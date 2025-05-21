import json
import traceback
import re
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext
from z3 import Optimize, Bool, Or, And, Not, If, Sum, sat, Implies

class SolverEngine:
    def __init__(self):
        self.cap_list = []
        self.step_vars = {}
        self.valid_mapping = {}
        self.solver = Optimize()

    def parse_req(self, s):
        s = s.strip()
        if s.startswith('>='): return float(s[2:]), None
        if s.startswith('<='): return None, float(s[2:])
        if '-' in s:
            low, high = map(float, s.split('-'))
            return low, high
        v = float(s)
        return v, v

    def load_data(self, cap_path, recipe_path):
        with open(cap_path, 'r', encoding='utf-8') as f:
            cap_data = json.load(f)
        with open(recipe_path, 'r', encoding='utf-8') as f:
            rec_data = json.load(f)
        self.build_capabilities(cap_data)
        self.rec_data = rec_data

    def build_capabilities(self, cap_data):
        self.cap_list.clear()
        for res, entries in cap_data.items():
            for e in entries:
                name = e.get('capability', [{}])[0].get('capability_name', '')
                if name.lower() in ['mixingofliquids', 'heatingofliquids']:
                    continue
                cid = f"{res}::{name}"
                gen = e.get('generalized_by', []) or []
                props = {}
                for p in e.get('properties', []):
                    pid = p.get('property_ID')
                    vmin = p.get('valueMin') if p.get('valueMin') is not None else p.get('value0')
                    vmax = p.get('valueMax') if p.get('valueMax') is not None else p.get('value1')
                    try:
                        lo = None if vmin is None else float(vmin)
                        hi = None if vmax is None else float(vmax)
                        if pid:
                            props[pid] = (lo, hi)
                    except:
                        continue
                self.cap_list.append({'id': cid, 'name': name, 'gen': gen, 'props': props})

    def build_constraints(self):
        self.solver = Optimize()
        self.step_vars.clear()
        self.valid_mapping.clear()
        invalid_mapping = {}

        # 记录步骤顺序及 base 名称
        step_ids = []
        step_bases = {}
        for step in self.rec_data.get('ProcessElements', []):
            sid = step.get('ID', '')
            base = re.sub(r'\d+$', '', sid).lower()
            step_ids.append(sid)
            step_bases[sid] = base

        # 为每一步创建布尔变量并添加“恰好一个能力”约束
        for step in self.rec_data.get('ProcessElements', []):
            sid = step.get('ID', '')
            step_key = ''.join(p.capitalize() for p in step_bases[sid].split('_'))
            params = {p['Key']: p['ValueString'] for p in step.get('Parameters', [])}

            valid, invalid = [], {}
            for cap in self.cap_list:
                cid = cap['id']
                if not (step_key.lower() in [g.lower() for g in cap['gen']] or cap['name'].lower() == step_key.lower()):
                    continue
                missing = [k for k in params if k not in cap['props']]
                if missing:
                    invalid[cid] = [f"Fehlender Parameter: {m}" for m in missing]
                    continue
                reasons = []
                for k, vstr in params.items():
                    lo, hi = self.parse_req(vstr)
                    c_lo, c_hi = cap['props'][k]
                    if lo is not None and c_hi is not None and c_hi < lo:
                        reasons.append(f"{k}: Max {c_hi} < gefordert {lo}")
                    if hi is not None and c_lo is not None and c_lo > hi:
                        reasons.append(f"{k}: Min {c_lo} > gefordert {hi}")
                if reasons:
                    invalid[cid] = reasons
                else:
                    valid.append(cid)

            self.valid_mapping[sid] = valid
            invalid_mapping[sid] = invalid

            vars_for = []
            for cid in valid:
                var = Bool(f"{sid}__{cid}")
                self.step_vars[(sid, cid)] = var
                vars_for.append(var)
            if not vars_for:
                self.solver.add(False)
            else:
                self.solver.add(Or(*vars_for))
                for i in range(len(vars_for)):
                    for j in range(i+1, len(vars_for)):
                        self.solver.add(Not(And(vars_for[i], vars_for[j])))

        # 绑定逻辑：对每个名为 dosing 的步骤
        for sid in step_ids:
            if step_bases[sid] == 'dosing':
                idx = step_ids.index(sid)
                if idx > 0:
                    prev = step_ids[idx - 1]
                    # 构建 prev 步骤和 dosing 步骤在同一 resource 的映射
                    for cap in self.cap_list:
                        cid = cap['id']
                        # dose 变量
                        dose_var = self.step_vars.get((sid, cid))
                        if dose_var is None:
                            continue
                        # 找到所有 prev 步骤在同一 resource 上的 var
                        res_prefix = cid.split('::')[0]
                        prev_vars = []
                        for prev_cid in self.valid_mapping.get(prev, []):
                            if prev_cid.split('::')[0] == res_prefix:
                                prev_vars.append(self.step_vars[(prev, prev_cid)])
                        # 强制：如果 dose_var 为真，则 prev 也必须在同一 resource 上的某个 var 为真
                        if prev_vars:
                            self.solver.add(Implies(dose_var, Or(*prev_vars)))
                        else:
                            # 如果 prev 在该 resource 上没有可用 var，则禁止 dose 选该 resource
                            self.solver.add(Not(dose_var))

        # 优化：最大化已覆盖步骤数
        all_vars = list(self.step_vars.values())
        if all_vars:
            self.solver.maximize(Sum([If(v,1,0) for v in all_vars]))

        return invalid_mapping

    def solve(self):
        res = self.solver.check()
        model = self.solver.model() if res == sat else None
        return res, model

class SMTGuiApp:
    def __init__(self, root):
        self.root = root
        self.engine = SolverEngine()
        self.root.title("SMT Z3 Löser - Optimale Abdeckung")
        self.root.geometry("900x700")

        frame_dateien = tk.Frame(root)
        frame_dateien.pack(fill=tk.X, padx=10, pady=5)
        tk.Button(frame_dateien, text="Fähigkeiten laden", command=self.load_cap).pack(side=tk.LEFT)
        self.cap_label = tk.Label(frame_dateien, text="Keine Datei"); self.cap_label.pack(side=tk.LEFT, padx=5)
        tk.Button(frame_dateien, text="Rezept laden", command=self.load_recipe).pack(side=tk.LEFT, padx=10)
        self.recipe_label = tk.Label(frame_dateien, text="Keine Datei"); self.recipe_label.pack(side=tk.LEFT, padx=5)

        frame_btn = tk.Frame(root); frame_btn.pack(pady=5)
        tk.Button(frame_btn, text="Lösen starten", command=self.run).pack(side=tk.LEFT, padx=5)
        tk.Button(frame_btn, text="Protokoll löschen", command=self.clear_log).pack(side=tk.LEFT, padx=5)

        self.output = scrolledtext.ScrolledText(root, wrap=tk.WORD, font=("Arial",10))
        self.output.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.cap_file = None
        self.recipe_file = None

    def load_cap(self):
        pf = filedialog.askopenfilename(filetypes=[('JSON Dateien','*.json')])
        if pf:
            self.cap_file = pf
            self.cap_label.config(text=pf.split('/')[-1])

    def load_recipe(self):
        pf = filedialog.askopenfilename(filetypes=[('JSON Dateien','*.json')])
        if pf:
            self.recipe_file = pf
            self.recipe_label.config(text=pf.split('/')[-1])

    def log(self,txt=""):
        self.output.insert(tk.END, txt+"\n")

    def clear_log(self):
        self.output.delete('1.0',tk.END)

    def run(self):
        self.clear_log()
        self.log("=== Optimale Abdeckung starten ===")
        if not self.cap_file or not self.recipe_file:
            messagebox.showwarning("Fehler","Bitte zuerst beide Dateien laden.")
            return
        try:
            self.engine.load_data(self.cap_file, self.recipe_file)
            invalid = self.engine.build_constraints()
            res, model = self.engine.solve()

            self.log(f"Ergebnis: {res}")
            for step in self.engine.rec_data['ProcessElements']:
                sid = step['ID']
                self.log(f"\nSchritt: {sid}")
                params = {p['Key']: p['ValueString'] for p in step['Parameters']}
                self.log("  Anforderungsparameter:")
                for k,v in params.items(): self.log(f"    - {k}: {v}")
                self.log("  Kandidatenfähigkeiten:")
                valid = self.engine.valid_mapping.get(sid, [])
                inval = invalid.get(sid,{})
                for cap in self.engine.cap_list:
                    cid = cap['id']
                    if cid in valid or cid in inval:
                        status = "gültig" if cid in valid else "ungültig"
                        self.log(f"    - {cid} ({status})")
                        if status=="gültig":
                            for k in params:
                                lo,hi = cap['props'][k]
                                self.log(f"      Eigenschaft {k}: Bereich [{lo},{hi}]")
                            sel = model.evaluate(self.engine.step_vars[(sid,cid)]) if res==sat else False
                            self.log("      Ausgewählt" if sel else "      Nicht ausgewählt")
                        else:
                            for reason in inval[cid]:
                                self.log(f"      Grund: {reason}")
        except Exception as e:
            self.log(f"Ausnahme: {e}")
            self.log(traceback.format_exc())

if __name__=='__main__':
    root=tk.Tk()
    app=SMTGuiApp(root)
    root.mainloop()