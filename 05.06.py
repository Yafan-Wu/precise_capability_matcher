import json
import traceback
import re
import tkinter as tk
from tkinter import filedialog, messagebox, scrolledtext
from z3 import Optimize, Bool, Or, And, Not, If, Sum, sat, Implies
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

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

        step_ids = []
        step_bases = {}
        for step in self.rec_data.get('ProcessElements', []):
            sid = step.get('ID', '')
            base = re.sub(r'\d+$', '', sid).lower()
            step_ids.append(sid)
            step_bases[sid] = base

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

        for sid in step_ids:
            if step_bases[sid] == 'dosing':
                idx = step_ids.index(sid)
                if idx > 0:
                    prev = step_ids[idx - 1]
                    for cap in self.cap_list:
                        cid = cap['id']
                        dose_var = self.step_vars.get((sid, cid))
                        if dose_var is None:
                            continue
                        res_prefix = cid.split('::')[0]
                        prev_vars = []
                        for prev_cid in self.valid_mapping.get(prev, []):
                            if prev_cid.split('::')[0] == res_prefix:
                                prev_vars.append(self.step_vars[(prev, prev_cid)])
                        if prev_vars:
                            self.solver.add(Implies(dose_var, Or(*prev_vars)))
                        else:
                            self.solver.add(Not(dose_var))

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
        tk.Button(frame_btn, text="Export Master Recipe", command=self.export_master_recipe).pack(side=tk.LEFT, padx=5)

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

    def log(self, txt=""):
        self.output.insert(tk.END, txt + "\n")

    def clear_log(self):
        self.output.delete('1.0', tk.END)

    def run(self):
        self.clear_log()
        self.log("=== Optimale Abdeckung starten ===")
        if not self.cap_file or not self.recipe_file:
            messagebox.showwarning("Fehler", "Bitte zuerst beide Dateien laden.")
            return
        try:
            self.engine.load_data(self.cap_file, self.recipe_file)
            invalid = self.engine.build_constraints()
            res, model = self.engine.solve()
            self.engine.model = model

            self.log(f"Ergebnis: {res}")
            for step in self.engine.rec_data['ProcessElements']:
                sid = step['ID']
                self.log(f"\nSchritt: {sid}")
                params = {p['Key']: p['ValueString'] for p in step['Parameters']}
                self.log("  Anforderungsparameter:")
                for k, v in params.items():
                    self.log(f"    - {k}: {v}")
                self.log("  Kandidatenfähigkeiten:")
                valid = self.engine.valid_mapping.get(sid, [])
                inval = invalid.get(sid, {})
                for cap in self.engine.cap_list:
                    cid = cap['id']
                    if cid in valid or cid in inval:
                        status = "gültig" if cid in valid else "ungültig"
                        self.log(f"    - {cid} ({status})")
                        if status == "gültig":
                            for k in params:
                                lo, hi = cap['props'][k]
                                self.log(f"      Eigenschaft {k}: Bereich [{lo},{hi}]")
                            sel = model.evaluate(self.engine.step_vars[(sid, cid)]) if res == sat else False
                            self.log("      Ausgewählt" if sel else "      Nicht ausgewählt")
                        else:
                            for reason in inval[cid]:
                                self.log(f"      Grund: {reason}")
        except Exception as e:
            self.log(f"Ausnahme: {e}")
            self.log(traceback.format_exc())

    def export_master_recipe(self):
        """Export a full-structure Master Recipe as B2MML XML with equipment binding and complete structure."""
        if not hasattr(self.engine, 'rec_data'):
            messagebox.showwarning("Fehler", "Bitte zuerst das Rezept laden.")
            return
        
        save_path = filedialog.asksaveasfilename(
            defaultextension=".xml",
            filetypes=[("XML Dateien","*.xml")],
            title="Master Recipe als XML speichern"
        )
        if not save_path:
            return

        NS = {"b2mml": "http://www.mesa.org/xml/B2MML"}
        ET.register_namespace("b2mml", NS["b2mml"])
        
        # Root element with proper namespace
        root = ET.Element(
            "b2mml:BatchInformation",
            {
                "xmlns:xsi": "http://www.w3.org/2001/XMLSchema-instance",
                "xsi:schemaLocation": "http://www.mesa.org/xml/B2MML Schema/AllSchemas.xsd",
                "xmlns:b2mml": NS["b2mml"]
            }
        )

        # ListHeader
        lh = ET.SubElement(root, "b2mml:ListHeader")
        ET.SubElement(lh, "b2mml:ID").text = "ListHeadID"
        ET.SubElement(lh, "b2mml:CreateDate").text = datetime.now(timezone.utc).astimezone().isoformat()

        # Global Description
        rd = self.engine.rec_data
        description_text = rd.get("Description", "")
        if not description_text:
            description_text = f"This Batch Information includes the Master Recipe \"{rd.get('ID', 'MasterRecipe')}\" to be executed"
        ET.SubElement(root, "b2mml:Description").text = description_text

        # MasterRecipe
        mr = ET.SubElement(root, "b2mml:MasterRecipe")
        ET.SubElement(mr, "b2mml:ID").text = rd.get("ID", "MasterRecipe")
        ET.SubElement(mr, "b2mml:Version").text = rd.get("Version", "1.0.0")
        ET.SubElement(mr, "b2mml:VersionDate").text = rd.get("VersionDate") or datetime.now(timezone.utc).astimezone().isoformat()
        ET.SubElement(mr, "b2mml:Description").text = rd.get("MasterRecipeDescription", rd.get("Description", "Master Recipe Description"))

        # Header
        hdr = ET.SubElement(mr, "b2mml:Header")
        ET.SubElement(hdr, "b2mml:ProductID").text = "StirredWater1"
        ET.SubElement(hdr, "b2mml:ProductName").text = "Stirred Water"

        # EquipmentRequirement
        eqr = ET.SubElement(mr, "b2mml:EquipmentRequirement")
        ET.SubElement(eqr, "b2mml:ID").text = "Equipment Requirement for the HCs"
        constraint = ET.SubElement(eqr, "b2mml:Constraint")
        ET.SubElement(constraint, "b2mml:ID").text = "Liquid constraint for the HC"
        ET.SubElement(constraint, "b2mml:Condition").text = "Material == H2O"
        ET.SubElement(eqr, "b2mml:Description").text = "Only water is allowed to used for the stirring process"

        # Formula
        formula = ET.SubElement(mr, "b2mml:Formula")
        param_counter = 1
        for step in rd.get("ProcessElements", []):
            for p in step.get("Parameters", []):
                parm = ET.SubElement(formula, "b2mml:Parameter")
                ET.SubElement(parm, "b2mml:ID").text = f"{param_counter:03d}:c90a9289-6b7d-4409-91f4-3c7fda23549a"
                ET.SubElement(parm, "b2mml:ParameterType").text = "ProcessParameter"
                ET.SubElement(parm, "b2mml:ParameterSubType").text = "ST"
                v = ET.SubElement(parm, "b2mml:Value")
                ET.SubElement(v, "b2mml:ValueString").text = p.get("ValueString", "0")
                ET.SubElement(v, "b2mml:DataInterpretation").text = "Constant"
                ET.SubElement(v, "b2mml:DataType").text = "duration"
                ET.SubElement(v, "b2mml:UnitOfMeasure").text = "second"
                param_counter += 1

        # ProcedureLogic
        proc = ET.SubElement(mr, "b2mml:ProcedureLogic")
        
        # Create a mapping from step IDs to equipment
        step_equipment_map = {}
        if hasattr(self.engine, 'model'):
            for (step_id, cap_id), var in self.engine.step_vars.items():
                if self.engine.model.evaluate(var):
                    equipment = cap_id.split("::")[0] + "Instance"
                    step_equipment_map[step_id] = equipment
        
        # Collect step IDs
        step_ids = [step['ID'] for step in rd.get("ProcessElements", [])]
        
        # Steps with equipment binding
        for step_id in step_ids:
            step_elem = ET.SubElement(proc, "b2mml:Step")
            ET.SubElement(step_elem, "b2mml:ID").text = step_id
            ET.SubElement(step_elem, "b2mml:RecipeElementID").text = step_id
            ET.SubElement(step_elem, "b2mml:Description").text = step_id
            
            # Add equipment binding if available
            if step_id in step_equipment_map:
                ET.SubElement(step_elem, "b2mml:ActualEquipmentID").text = step_equipment_map[step_id]

        # Transitions
        for i in range(1, len(step_ids)):
            trans = ET.SubElement(proc, "b2mml:Transition")
            ET.SubElement(trans, "b2mml:ID").text = f"T{i}"
            ET.SubElement(trans, "b2mml:Condition").text = f"Step {step_ids[i-1]} is Completed"

        # Links (Step to Transition and Transition to Step)
        link_counter = 1
        for i in range(len(step_ids)):
            # Step to Transition link
            if i < len(step_ids) - 1:
                link = ET.SubElement(proc, "b2mml:Link")
                ET.SubElement(link, "b2mml:ID").text = f"L{link_counter}"
                link_counter += 1
                
                fr = ET.SubElement(link, "b2mml:FromID")
                ET.SubElement(fr, "b2mml:FromIDValue").text = step_ids[i]
                ET.SubElement(fr, "b2mml:FromType").text = "Step"
                ET.SubElement(fr, "b2mml:IDScope").text = "External"
                
                to = ET.SubElement(link, "b2mml:ToID")
                ET.SubElement(to, "b2mml:ToIDValue").text = f"T{i+1}"
                ET.SubElement(to, "b2mml:ToType").text = "Transition"
                ET.SubElement(to, "b2mml:IDScope").text = "External"
                
                ET.SubElement(link, "b2mml:LinkType").text = "ControlLink"
                ET.SubElement(link, "b2mml:Depiction").text = "LineAndArrow"
                ET.SubElement(link, "b2mml:EvaluationOrder").text = "1"
                ET.SubElement(link, "b2mml:Description").text = "Step to Transition"
            
            # Transition to Step link
            if i > 0:
                link = ET.SubElement(proc, "b2mml:Link")
                ET.SubElement(link, "b2mml:ID").text = f"L{link_counter}"
                link_counter += 1
                
                fr = ET.SubElement(link, "b2mml:FromID")
                ET.SubElement(fr, "b2mml:FromIDValue").text = f"T{i}"
                ET.SubElement(fr, "b2mml:FromType").text = "Transition"
                ET.SubElement(fr, "b2mml:IDScope").text = "External"
                
                to = ET.SubElement(link, "b2mml:ToID")
                ET.SubElement(to, "b2mml:ToIDValue").text = step_ids[i]
                ET.SubElement(to, "b2mml:ToType").text = "Step"
                ET.SubElement(to, "b2mml:IDScope").text = "External"
                
                ET.SubElement(link, "b2mml:LinkType").text = "ControlLink"
                ET.SubElement(link, "b2mml:Depiction").text = "LineAndArrow"
                ET.SubElement(link, "b2mml:EvaluationOrder").text = "1"
                ET.SubElement(link, "b2mml:Description").text = "Transition to Step"

        # RecipeElements
        # Add Begin and End elements
        for elem_type, elem_id in [("Begin", "Init"), ("End", "End")]:
            re_el = ET.SubElement(mr, "b2mml:RecipeElement")
            ET.SubElement(re_el, "b2mml:ID").text = elem_id
            ET.SubElement(re_el, "b2mml:RecipeElementType").text = elem_type
        
        # Operation elements for each step
        for i, step_id in enumerate(step_ids):
            re_el = ET.SubElement(mr, "b2mml:RecipeElement")
            ET.SubElement(re_el, "b2mml:ID").text = f"Step_{i+1:03d}"
            ET.SubElement(re_el, "b2mml:Description").text = f"Operation for {step_id}"
            ET.SubElement(re_el, "b2mml:RecipeElementType").text = "Operation"
            
            # Assign equipment if solved
            if step_id in step_equipment_map:
                ET.SubElement(re_el, "b2mml:ActualEquipmentID").text = step_equipment_map[step_id]
            
            # Equipment requirement reference
            eq_req = ET.SubElement(re_el, "b2mml:EquipmentRequirement")
            ET.SubElement(eq_req, "b2mml:ID").text = "Equipment Requirement for the HCs"
            
            # Parameter reference
            param = ET.SubElement(re_el, "b2mml:Parameter")
            ET.SubElement(param, "b2mml:ID").text = f"{i+1:03d}:c90a9289-6b7d-4409-91f4-3c7fda23549a"
            ET.SubElement(param, "b2mml:ParameterType").text = "ProcessParameter"

        # EquipmentElements
        if hasattr(self.engine, 'model') and hasattr(self.engine, 'model'):
            # Get unique equipment
            equipment_set = set(step_equipment_map.values())
            
            for equip in equipment_set:
                ee = ET.SubElement(root, "b2mml:EquipmentElement")
                ET.SubElement(ee, "b2mml:ID").text = equip
                ET.SubElement(ee, "b2mml:EquipmentElementType").text = "Other"
                ET.SubElement(ee, "b2mml:EquipmentElementLevel").text = "EquipmentModule"
                
                # Add detailed procedural elements for each capability
                for (step_id, cap_id), var in self.engine.step_vars.items():
                    if self.engine.model.evaluate(var) and step_equipment_map.get(step_id) == equip:
                        cap_name = cap_id.split("::")[1]
                        epe = ET.SubElement(ee, "b2mml:EquipmentProceduralElement")
                        ET.SubElement(epe, "b2mml:ID").text = f"{equip}_{cap_name}"
                        ET.SubElement(epe, "b2mml:Description").text = f"{cap_name} for {equip}"
                        ET.SubElement(epe, "b2mml:EquipmentProceduralElementType").text = "Procedure"
                        
                        # Add parameters
                        param = ET.SubElement(epe, "b2mml:Parameter")
                        ET.SubElement(param, "b2mml:ID").text = f"param_{cap_name}"
                        ET.SubElement(param, "b2mml:Description").text = f"{cap_name} Parameter"
                        ET.SubElement(param, "b2mml:ParameterType").text = "ProcessParameter"
                        v = ET.SubElement(param, "b2mml:Value")
                        ET.SubElement(v, "b2mml:ValueString").text = "30"
                        ET.SubElement(v, "b2mml:DataInterpretation").text = "Constant"
                        ET.SubElement(v, "b2mml:DataType").text = "duration"
                        ET.SubElement(v, "b2mml:UnitOfMeasure").text = "second"
                
                # Add equipment connection
                conn = ET.SubElement(ee, "b2mml:EquipmentConnection")
                ET.SubElement(conn, "b2mml:ID").text = f"EquipmentConnection{equip}toNext"
                ET.SubElement(conn, "b2mml:ConnectionType").text = "MaterialMovement"
                ET.SubElement(conn, "b2mml:FromEquipmentID").text = equip
                ET.SubElement(conn, "b2mml:ToEquipmentID").text = "NextEquipment"

        # Format and save
        ET.indent(root, space="    ", level=0)
        tree = ET.ElementTree(root)
        tree.write(save_path, encoding="utf-8", xml_declaration=True)
        messagebox.showinfo("Erfolg", f"Master Recipe gespeichert:\n{save_path}")

if __name__=='__main__':
    root = tk.Tk()
    app = SMTGuiApp(root)
    root.mainloop()