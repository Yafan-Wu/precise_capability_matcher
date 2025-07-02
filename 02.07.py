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
        self.cap_list = []  # List of device capabilities
        self.step_vars = {}  # Step variables dictionary
        self.valid_mapping = {}  # Valid mapping
        self.solver = Optimize()  # Z3 optimizer
        self.step_ids = []  # List of step IDs
        # Define transport types and modes
        self.TRANSPORT_TYPES = ["dosing", "transporting", "conveying"]
        self.TRANSPORT_MODES = ["feed", "discharge", "transfer"]
        self.assigned_resources = {}  # Track assigned resources for each step
        self.semantic_hierarchy = {}  # Storage semantic type inheritance

    def parse_req(self, s):
        """Parse requirement string as a numeric range"""
        s = s.strip()
        if s.startswith('>='): return float(s[2:]), None
        if s.startswith('<='): return None, float(s[2:])
        if '-' in s:
            low, high = map(float, s.split('-'))
            return low, high
        v = float(s)
        return v, v

    def load_data(self, cap_path, recipe_path):
        """Load capability and recipe data"""
        with open(cap_path, 'r', encoding='utf-8') as f:
            cap_data = json.load(f)
        with open(recipe_path, 'r', encoding='utf-8') as f:
            rec_data = json.load(f)
        self.build_capabilities(cap_data)
        self.rec_data = rec_data
        # Collect step IDs
        self.step_ids = [step['ID'] for step in rec_data.get('ProcessElements', [])]
        
    def get_all_ancestor_types(self, semantic_type):
        """Recursively get all ancestor types (including itself)"""
        ancestors = set([semantic_type])
        to_process = [semantic_type]
        
        while to_process:
            current = to_process.pop()
            parents = self.semantic_hierarchy.get(current, [])
            for parent in parents:
                if parent not in ancestors:
                    ancestors.add(parent)
                    to_process.append(parent)
        return list(ancestors)

    def build_capabilities(self, cap_data):
        """Build capability list with semantic types and inheritance"""
        self.cap_list.clear()
        self.semantic_hierarchy = {}
        
        # First: Collect all semantic types and inheritance relationships
        for res, entries in cap_data.items():
            for e in entries:
                cap_info = e['capability'][0]
                semantic_id = cap_info.get('capability_ID', '')
                semantic_type = semantic_id.split('#')[-1] if '#' in semantic_id else cap_info['capability_name']
                generalized_by = e.get('generalized_by', []) or []
                
                # Record inheritance relationships
                self.semantic_hierarchy[semantic_type] = generalized_by
        
        # Second: Build a capability list containing all ancestor types
        for res, entries in cap_data.items():
            for e in entries:
                cap_info = e['capability'][0]
                name = cap_info['capability_name']
                semantic_id = cap_info.get('capability_ID', '')
                semantic_type = semantic_id.split('#')[-1] if '#' in semantic_id else name
                
                # Get all ancestor types (including self)
                all_semantic_types = self.get_all_ancestor_types(semantic_type)
                
                cid = f"{res}::{name}"
                props = {}
                for p in e.get('properties', []):
                    pid = p.get('property_ID')
                    vmin = p.get('valueMin') or p.get('value0') or None
                    vmax = p.get('valueMax') or p.get('value1') or None
                    try:
                        lo = None if vmin is None else float(vmin)
                        hi = None if vmax is None else float(vmax)
                        if pid:
                            props[pid] = (lo, hi)
                    except:
                        continue
                self.cap_list.append({
                    'id': cid, 
                    'name': name, 
                    'semantic_type': semantic_type,
                    'all_semantic_types': all_semantic_types,  # Contains all ancestor types
                    'props': props
                })

    def _handle_feed_mode(self, step_id, all_step_ids):
        """Handle feed mode: Previous steps must have the same device"""
        idx = all_step_ids.index(step_id)
        if idx == 0: return  # First step has no predecessor
        
        prev_step = all_step_ids[idx-1]
        for cap_id in self.valid_mapping.get(step_id, []):
            resource = cap_id.split("::")[0]
            transport_var = self.step_vars[(step_id, cap_id)]
            
            # Previous step must have capability with same resource
            prev_vars = []
            for prev_cid in self.valid_mapping.get(prev_step, []):
                if prev_cid.split("::")[0] == resource:
                    prev_vars.append(self.step_vars[(prev_step, prev_cid)])
            
            if prev_vars:
                self.solver.add(Implies(transport_var, Or(*prev_vars)))
            else:
                self.solver.add(Not(transport_var))  # Disable if no feasible predecessor

    def _handle_discharge_mode(self, step_id, all_step_ids):
        """Handle discharge mode: Subsequent steps must have the same device"""
        idx = all_step_ids.index(step_id)
        if idx == len(all_step_ids)-1: return  # Last step has no successor
        
        next_step = all_step_ids[idx+1]
        for cap_id in self.valid_mapping.get(step_id, []):
            resource = cap_id.split("::")[0]
            transport_var = self.step_vars[(step_id, cap_id)]
            
            # Next step must have capability with same resource
            next_vars = []
            for next_cid in self.valid_mapping.get(next_step, []):
                if next_cid.split("::")[0] == resource:
                    next_vars.append(self.step_vars[(next_step, next_cid)])
            
            if next_vars:
                self.solver.add(Implies(transport_var, Or(*next_vars)))
            else:
                self.solver.add(Not(transport_var))

    def _handle_transfer_mode(self, step_id, all_step_ids):
        """Handle transfer mode: Connecting different devices"""
        idx = all_step_ids.index(step_id)
        prev_step = all_step_ids[idx-1] if idx > 0 else None
        next_step = all_step_ids[idx+1] if idx < len(all_step_ids)-1 else None
        
        for cap_id in self.valid_mapping.get(step_id, []):
            transport_var = self.step_vars[(step_id, cap_id)]
            resource = cap_id.split("::")[0]
            
            # Source device: Previous step must have different resource
            if prev_step:
                prev_vars = []
                for prev_cid in self.valid_mapping.get(prev_step, []):
                    if prev_cid.split("::")[0] != resource:  # Different resource!
                        prev_vars.append(self.step_vars[(prev_step, prev_cid)])
                if prev_vars:
                    self.solver.add(Implies(transport_var, Or(*prev_vars)))
                else:
                    self.solver.add(Not(transport_var))
            
            # Target device: Next step must have different resource
            if next_step:
                next_vars = []
                for next_cid in self.valid_mapping.get(next_step, []):
                    if next_cid.split("::")[0] != resource:  # Different resource!
                        next_vars.append(self.step_vars[(next_step, next_cid)])
                if next_vars:
                    self.solver.add(Implies(transport_var, Or(*next_vars)))
                else:
                    self.solver.add(Not(transport_var))

    def determine_transport_mode(self, step, step_idx):
        """Determine transport mode for a step (Feed, Discharge, Transfer) based on device assignments"""
        sid = step['ID']
        
        # Only define transport modes for middle steps (not first or last)
        if step_idx == 0 or step_idx == len(self.step_ids) - 1:
            return None
            
        step_type = step.get('SemanticDescription', '').split('#')[-1].lower()
        
        # 1. Check if it's a transport step
        if step_type not in self.TRANSPORT_TYPES:
            return None  # Not a transport step
        
        # 2. Check if explicit mode parameter exists
        mode_param = next((p for p in step['Parameters'] if p['Key'].lower() == 'mode'), None)
        if mode_param:
            mode = mode_param['ValueString'].lower().strip()
            if mode in self.TRANSPORT_MODES:
                return mode
        
        # 3. Analyze step ID
        step_id_lower = sid.lower()
        if 'feed' in step_id_lower or 'inlet' in step_id_lower or 'input' in step_id_lower:
            return 'feed'
        if 'discharge' in step_id_lower or 'outlet' in step_id_lower or 'output' in step_id_lower:
            return 'discharge'
        if 'transfer' in step_id_lower or 'move' in step_id_lower or 'convey' in step_id_lower or 'dosing' in step_id_lower:
            return 'transfer'
        
        # 4. Analyze parameters
        param_keys = {p['Key'].lower() for p in step['Parameters']}
        if {'feedrate', 'inletflow', 'feed_flow'}.intersection(param_keys):
            return 'feed'
        if {'dischargerate', 'outlettarget', 'discharge_flow'}.intersection(param_keys):
            return 'discharge'
        if {'transferdistance', 'conveyorspeed', 'transfer_time'}.intersection(param_keys):
            return 'transfer'
        
        # 5. Material flow analysis based on device assignments
        if step_idx > 0 and step_idx < len(self.step_ids) - 1:
            prev_resource = self.assigned_resources.get(self.step_ids[step_idx-1], "").split("::")[0]
            next_resource = self.assigned_resources.get(self.step_ids[step_idx+1], "").split("::")[0]
            current_resource = self.assigned_resources.get(sid, "").split("::")[0]
            
            if current_resource and prev_resource and next_resource:
                if current_resource != prev_resource and current_resource == next_resource:
                    return 'feed'
                elif current_resource == prev_resource and current_resource != next_resource:
                    return 'discharge'
                elif current_resource != prev_resource and current_resource != next_resource:
                    return 'transfer'
        
        # 6. Default value
        return 'transfer'

    def build_constraints(self):
        """Build SMT constraints with semantic type matching"""
        self.solver = Optimize()
        self.step_vars.clear()
        self.valid_mapping.clear()
        invalid_mapping = {}

        # First determine transport mode for all steps
        for step_idx, step in enumerate(self.rec_data.get('ProcessElements', [])):
            sid = step.get('ID', '')
            # Only define transport modes for middle steps (not first or last)
            if step_idx > 0 and step_idx < len(self.step_ids) - 1:
                mode = self.determine_transport_mode(step, step_idx)
                step['_transport_mode'] = mode
            else:
                step['_transport_mode'] = None  # No transport mode for first/last steps

        for step in self.rec_data.get('ProcessElements', []):
            sid = step.get('ID', '')
            params = {p['Key']: p['ValueString'] for p in step.get('Parameters', [])}
            
            # Extract step semantic type
            step_semantic_desc = step.get('SemanticDescription', '')
            step_semantic = step_semantic_desc.split('#')[-1] if '#' in step_semantic_desc else step_semantic_desc

            valid, invalid = [], {}
            for cap in self.cap_list:
                cid = cap['id']
                
                # 1. Check semantic type matching (including inheritance relationships)
                step_semantic_lower = step_semantic.lower()
                cap_types_lower = [t.lower() for t in cap['all_semantic_types']]
                
                if step_semantic_lower not in cap_types_lower:
                    invalid[cid] = [f"Semantic type mismatch: need {step_semantic}, Actual capability type chain: {', '.join(cap['all_semantic_types'])}"]
                    continue
                
                # 2. Check if capability contains all required parameters
                missing = [k for k in params if k not in cap['props']]
                if missing:
                    invalid[cid] = [f"Missing parameters: {m}" for m in missing]
                    continue
                
                reasons = []
                # 3. Check parameter range constraints
                for k, vstr in params.items():
                    lo, hi = self.parse_req(vstr)
                    c_lo, c_hi = cap['props'][k]
                    if lo is not None and c_hi is not None and c_hi < lo:
                        reasons.append(f"{k}: max {c_hi} < demend {lo}")
                    if hi is not None and c_lo is not None and c_lo > hi:
                        reasons.append(f"{k}: min {c_lo} > demend {hi}")
                if reasons:
                    invalid[cid] = reasons
                else:
                    valid.append(cid)

            self.valid_mapping[sid] = valid
            invalid_mapping[sid] = invalid

            # Create variables and constraints for valid capabilities
            vars_for = []
            for cid in valid:
                var = Bool(f"{sid}__{cid}")
                self.step_vars[(sid, cid)] = var
                vars_for.append(var)
            if not vars_for:
                self.solver.add(False)  # No valid capabilities, add impossible constraint
            else:
                self.solver.add(Or(*vars_for))  # Select at least one capability
                # Mutual exclusion constraint: Only one capability per step
                for i in range(len(vars_for)):
                    for j in range(i+1, len(vars_for)):
                        self.solver.add(Not(And(vars_for[i], vars_for[j])))

        # Handle transport mode constraints
        for step_idx, step in enumerate(self.rec_data.get('ProcessElements', [])):
            sid = step.get('ID', '')
            step_type = step.get('SemanticDescription', '').split('#')[-1].lower()
            
            if step_type in self.TRANSPORT_TYPES and step['_transport_mode'] is not None:
                mode = step.get('_transport_mode', 'transfer')
                
                # Apply appropriate constraints based on mode
                if mode == "feed":
                    self._handle_feed_mode(sid, self.step_ids)
                elif mode == "discharge":
                    self._handle_discharge_mode(sid, self.step_ids)
                elif mode == "transfer":
                    self._handle_transfer_mode(sid, self.step_ids)

        # Maximize coverage: Select as many capabilities as possible
        all_vars = list(self.step_vars.values())
        if all_vars:
            self.solver.maximize(Sum([If(v,1,0) for v in all_vars]))

        return invalid_mapping

    def solve(self):
        """Solve the constraint system"""
        res = self.solver.check()
        model = self.solver.model() if res == sat else None
        
        # Record assigned resources
        if model:
            self.assigned_resources = {}
            for step_id in self.step_ids:
                for cap_id in self.valid_mapping.get(step_id, []):
                    var = self.step_vars.get((step_id, cap_id))
                    if model.evaluate(var):
                        self.assigned_resources[step_id] = cap_id
                        break
        
        return res, model

class SMTGuiApp:
    def __init__(self, root):
        self.root = root
        self.engine = SolverEngine()
        self.root.title("SMT Z3 Solver - Optimal Coverage")
        self.root.geometry("900x700")

        # File selection frame
        frame_files = tk.Frame(root)
        frame_files.pack(fill=tk.X, padx=10, pady=5)
        tk.Button(frame_files, text="Load Capabilities", command=self.load_cap).pack(side=tk.LEFT)
        self.cap_label = tk.Label(frame_files, text="No file selected")
        self.cap_label.pack(side=tk.LEFT, padx=5)
        tk.Button(frame_files, text="Load Recipe", command=self.load_recipe).pack(side=tk.LEFT, padx=10)
        self.recipe_label = tk.Label(frame_files, text="No file selected")
        self.recipe_label.pack(side=tk.LEFT, padx=5)

        # Button frame
        frame_btn = tk.Frame(root)
        frame_btn.pack(pady=5)
        tk.Button(frame_btn, text="Start Calculation", command=self.run).pack(side=tk.LEFT, padx=5)
        tk.Button(frame_btn, text="Clear Log", command=self.clear_log).pack(side=tk.LEFT, padx=5)
        tk.Button(frame_btn, text="Export Master Recipe", command=self.export_master_recipe).pack(side=tk.LEFT, padx=5)

        # Output text field
        self.output = scrolledtext.ScrolledText(root, wrap=tk.WORD, font=("Arial",10))
        self.output.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.cap_file = None
        self.recipe_file = None

    def load_cap(self):
        """Load capability file"""
        path = filedialog.askopenfilename(filetypes=[('JSON files','*.json')])
        if path:
            self.cap_file = path
            self.cap_label.config(text=path.split('/')[-1])

    def load_recipe(self):
        """Load recipe file"""
        path = filedialog.askopenfilename(filetypes=[('JSON files','*.json')])
        if path:
            self.recipe_file = path
            self.recipe_label.config(text=path.split('/')[-1])

    def log(self, txt=""):
        """Log message"""
        self.output.insert(tk.END, txt + "\n")

    def clear_log(self):
        """Clear log"""
        self.output.delete('1.0', tk.END)

    def run(self):
        """Start calculation process"""
        self.clear_log()
        self.log("=== Starting optimal coverage calculation ===")
        if not self.cap_file or not self.recipe_file:
            messagebox.showwarning("Error", "Please load both files first")
            return
        try:
            self.engine.load_data(self.cap_file, self.recipe_file)
            invalid = self.engine.build_constraints()
            res, model = self.engine.solve()
            self.engine.model = model

            self.log(f"Solution status: {res}")
            for step_idx, step in enumerate(self.engine.rec_data['ProcessElements']):
                sid = step['ID']
                self.log(f"\nStep {step_idx+1}: {sid}")
                
                # Extract and log semantic type
                semantic_desc = step.get('SemanticDescription', '')
                semantic_type = semantic_desc.split('#')[-1] if '#' in semantic_desc else semantic_desc
                self.log(f"  Semantic type: {semantic_type}")
                
                # Only show transport mode for middle steps
                if step_idx > 0 and step_idx < len(self.engine.rec_data['ProcessElements']) - 1:
                    if '_transport_mode' in step and step['_transport_mode'] is not None:
                        self.log(f"  Transport mode: {step['_transport_mode'].upper()}")
                    else:
                        self.log("  Transport mode: N/A (Non-transport step)")
                
                params = {p['Key']: p['ValueString'] for p in step['Parameters']}
                self.log("  Requirement parameters:")
                for k, v in params.items():
                    self.log(f"    - {k}: {v}")
                self.log("  Candidate capabilities:")
                valid = self.engine.valid_mapping.get(sid, [])
                inval = invalid.get(sid, {})
                for cap in self.engine.cap_list:
                    cid = cap['id']
                    if cid in valid or cid in inval:
                        status = "Valid" if cid in valid else "Invalid"
                        self.log(f"    - {cid} ({status})")
                        self.log(f"      Semantic type: {cap['semantic_type']}")
                        self.log(f"      All semantic types: {', '.join(cap['all_semantic_types'])}")
                        if status == "Valid":
                            for k in params:
                                lo, hi = cap['props'].get(k, (None, None))
                                if lo is not None or hi is not None:
                                    self.log(f"      Property {k}: Range [{lo},{hi}]")
                            if res == sat:
                                sel = model.evaluate(self.engine.step_vars.get((sid, cid), False))
                                self.log("      Selected" if sel else "      Not selected")
                        else:
                            for reason in inval.get(cid, []):
                                self.log(f"      Reason: {reason}")
        except Exception as e:
            self.log(f"Exception: {e}")
            self.log(traceback.format_exc())
            
    def infer_data_type_and_unit(self, param_key, value_str):
        """Infer data type and unit based on parameter name and value"""
        param_key_lower = param_key.lower()
        value_str_lower = value_str.lower()
        
        # Infer based on parameter name
        if 'temp' in param_key_lower:
            return "Temperature", "Celsius"
        elif 'pressure' in param_key_lower:
            return "Pressure", "Bar"
        elif 'time' in param_key_lower or 'duration' in param_key_lower:
            return "Duration", "Seconds"
        elif 'flow' in param_key_lower:
            return "FlowRate", "Milliliter/Second"
        elif 'volume' in param_key_lower:
            return "Volume", "Milliliter"
        elif 'speed' in param_key_lower:
            return "Speed", "Revolutions per Minute"
        elif 'weight' in param_key_lower or 'mass' in param_key_lower:
            return "Mass", "Grams"
        
        # Infer based on unit in value string
        if '°c' in value_str_lower or 'celsius' in value_str_lower:
            return "Temperature", "Celsius"
        elif 'bar' in value_str_lower:
            return "Pressure", "Bar"
        elif 's' in value_str_lower or 'sec' in value_str_lower:
            return "Duration", "Seconds"
        elif 'min' in value_str_lower:
            return "Duration", "Minutes"
        elif 'ml' in value_str_lower or 'milliliter' in value_str_lower:
            return "Volume", "Milliliter"
        elif 'l' in value_str_lower or 'liter' in value_str_lower:
            return "Volume", "Liters"
        elif 'g' in value_str_lower or 'gram' in value_str_lower:
            return "Mass", "Grams"
        elif 'kg' in value_str_lower or 'kilo' in value_str_lower:
            return "Mass", "Kilograms"
        elif 'rpm' in value_str_lower:
            return "Speed", "Revolutions per Minute"
        
        # Default
        return "Value", "Unit"

    def export_master_recipe(self):
        """Export B2MML XML master recipe (without Discharge/Feed/Transfer)"""
        if not hasattr(self.engine, 'rec_data'):
            messagebox.showwarning("Error", "Please load a recipe file first")
            return
        
        save_path = filedialog.asksaveasfilename(
            defaultextension=".xml",
            filetypes=[("XML files","*.xml")],
            title="Save Master Recipe as XML"
        )
        if not save_path:
            return

        NS = {"b2mml": "http://www.mesa.org/xml/B2MML"}
        ET.register_namespace("b2mml", NS["b2mml"])
        
        # Create root element
        root = ET.Element(
            "b2mml:BatchInformation",
            {
                "xmlns:xsi": "http://www.w3.org/2001/XMLSchema-instance",
                "xsi:schemaLocation": "http://www.mesa.org/xml/B2MML Schema/AllSchemas.xsd",
                "xmlns:b2mml": NS["b2mml"]
            }
        )

        # List header
        lh = ET.SubElement(root, "b2mml:ListHeader")
        ET.SubElement(lh, "b2mml:ID").text = "ListHeadID"
        ET.SubElement(lh, "b2mml:CreateDate").text = datetime.now(timezone.utc).astimezone().isoformat()

        # Global description
        rd = self.engine.rec_data
        description_text = rd.get("Description", "")
        if not description_text:
            description_text = f"This batch information contains the master recipe \"{rd.get('ID', 'MasterRecipe')}\" for execution"
        ET.SubElement(root, "b2mml:Description").text = description_text

        # Master recipe
        mr = ET.SubElement(root, "b2mml:MasterRecipe")
        ET.SubElement(mr, "b2mml:ID").text = rd.get("ID", "MasterRecipe")
        ET.SubElement(mr, "b2mml:Version").text = rd.get("Version", "1.0.0")
        ET.SubElement(mr, "b2mml:VersionDate").text = rd.get("VersionDate") or datetime.now(timezone.utc).astimezone().isoformat()
        ET.SubElement(mr, "b2mml:Description").text = rd.get("MasterRecipeDescription", rd.get("Description", "Master recipe description"))

        # Header information
        hdr = ET.SubElement(mr, "b2mml:Header")
        ET.SubElement(hdr, "b2mml:ProductID").text = "StirredWater1"
        ET.SubElement(hdr, "b2mml:ProductName").text = "Stirred Water"

        # Equipment requirement
        eqr = ET.SubElement(mr, "b2mml:EquipmentRequirement")
        ET.SubElement(eqr, "b2mml:ID").text = "HC Equipment Requirement"
        constraint = ET.SubElement(eqr, "b2mml:Constraint")
        ET.SubElement(constraint, "b2mml:ID").text = "HC Liquid Constraint"
        ET.SubElement(constraint, "b2mml:Condition").text = "Material == H2O"
        ET.SubElement(eqr, "b2mml:Description").text = "Water is the only allowed substance during stirring"

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
                
                # Use inference function to determine data type and unit
                data_type, unit = self.infer_data_type_and_unit(
                    p.get("Key", ""),
                    p.get("ValueString", "")
                )
                ET.SubElement(v, "b2mml:DataType").text = data_type
                ET.SubElement(v, "b2mml:UnitOfMeasure").text = unit
                param_counter += 1

        # Process logic
        proc = ET.SubElement(mr, "b2mml:ProcedureLogic")
        
        # Create step-to-equipment mapping
        step_equipment_map = {}
        if hasattr(self.engine, 'model'):
            for (step_id, cap_id), var in self.engine.step_vars.items():
                if self.engine.model.evaluate(var):
                    equipment = cap_id.split("::")[0] + "Instance"
                    step_equipment_map[step_id] = equipment
        
        # Collect step IDs
        step_ids = [step['ID'] for step in rd.get("ProcessElements", [])]
        
        # Steps with equipment assignment
        for step in rd.get("ProcessElements", []):
            step_id = step['ID']
            step_elem = ET.SubElement(proc, "b2mml:Step")
            ET.SubElement(step_elem, "b2mml:ID").text = step_id
            ET.SubElement(step_elem, "b2mml:RecipeElementID").text = step_id
            ET.SubElement(step_elem, "b2mml:Description").text = step_id
            
            # Add equipment assignment if available
            if step_id in step_equipment_map:
                ET.SubElement(step_elem, "b2mml:ActualEquipmentID").text = step_equipment_map[step_id]

        # Transition conditions
        for i in range(1, len(step_ids)):
            trans = ET.SubElement(proc, "b2mml:Transition")
            ET.SubElement(trans, "b2mml:ID").text = f"T{i}"
            ET.SubElement(trans, "b2mml:Condition").text = f"Step {step_ids[i-1]} completed"

        # Links (step-to-transition and transition-to-step)
        link_counter = 1
        for i in range(len(step_ids)):
            # Step-to-transition link
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
                ET.SubElement(link, "b2mml:Depiction").text = "Line and arrow"
                ET.SubElement(link, "b2mml:EvaluationOrder").text = "1"
                ET.SubElement(link, "b2mml:Description").text = "Step to transition"
            
            # Transition-to-step link
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
                ET.SubElement(link, "b2mml:Depiction").text = "Line and arrow"
                ET.SubElement(link, "b2mml:EvaluationOrder").text = "1"
                ET.SubElement(link, "b2mml:Description").text = "Transition to step"

        # Recipe elements
        # Add start and end elements
        for elem_type, elem_id in [("Start", "Init"), ("End", "End")]:
            re_el = ET.SubElement(mr, "b2mml:RecipeElement")
            ET.SubElement(re_el, "b2mml:ID").text = elem_id
            ET.SubElement(re_el, "b2mml:RecipeElementType").text = elem_type
        
        # Add operation elements for each step
        for i, step in enumerate(rd.get("ProcessElements", [])):
            step_id = step['ID']
            re_el = ET.SubElement(mr, "b2mml:RecipeElement")
            ET.SubElement(re_el, "b2mml:ID").text = f"Step_{i+1:03d}"
            
            # 使用统一的"Process"类型
            elem_type = "Process"
            desc = f"{step_id} operation"
            
            ET.SubElement(re_el, "b2mml:Description").text = desc
            ET.SubElement(re_el, "b2mml:RecipeElementType").text = elem_type
            
            # Equipment assignment if calculated
            if step_id in step_equipment_map:
                ET.SubElement(re_el, "b2mml:ActualEquipmentID").text = step_equipment_map[step_id]
            
            # Equipment requirement reference
            eq_req = ET.SubElement(re_el, "b2mml:EquipmentRequirement")
            ET.SubElement(eq_req, "b2mml:ID").text = "HC Equipment Requirement"
            
            # Parameter reference - associate recipe parameters with equipment capabilities
            for p in step.get("Parameters", []):
                param = ET.SubElement(re_el, "b2mml:Parameter")
                ET.SubElement(param, "b2mml:ID").text = p['Key']
                ET.SubElement(param, "b2mml:Description").text = f"{p['Key']} for {step_id}"
                ET.SubElement(param, "b2mml:ParameterType").text = "ProcessParameter"
                v = ET.SubElement(param, "b2mml:Value")
                ET.SubElement(v, "b2mml:ValueString").text = p.get("ValueString", "0")
                ET.SubElement(v, "b2mml:DataInterpretation").text = "Constant"
                
                # Use same inference function for consistency
                data_type, unit = self.infer_data_type_and_unit(p['Key'], p.get("ValueString", ""))
                ET.SubElement(v, "b2mml:DataType").text = data_type
                ET.SubElement(v, "b2mml:UnitOfMeasure").text = unit

        # Equipment elements
        if hasattr(self.engine, 'model') and hasattr(self.engine, 'model'):
            # Get unique equipment
            equipment_set = set(step_equipment_map.values())
            
            # Collect equipment connections based on material flow
            equipment_connections = {}
            if 'DirectedLinks' in rd:
                for link in rd['DirectedLinks']:
                    from_step = link['FromID']
                    to_step = link['ToID']
                    from_equip = step_equipment_map.get(from_step)
                    to_equip = step_equipment_map.get(to_step)
                    
                    if from_equip and to_equip and from_equip != to_equip:
                        if from_equip not in equipment_connections:
                            equipment_connections[from_equip] = set()
                        equipment_connections[from_equip].add(to_equip)
            
            for equip in equipment_set:
                ee = ET.SubElement(root, "b2mml:EquipmentElement")
                ET.SubElement(ee, "b2mml:ID").text = equip
                ET.SubElement(ee, "b2mml:EquipmentElementType").text = "Other"
                ET.SubElement(ee, "b2mml:EquipmentElementLevel").text = "EquipmentModule"
                
                # Add detailed procedural elements for each capability
                capabilities_added = set()
                for (step_id, cap_id), var in self.engine.step_vars.items():
                    if self.engine.model.evaluate(var) and step_equipment_map.get(step_id) == equip:
                        cap_name = cap_id.split("::")[1]
                        if cap_name not in capabilities_added:
                            capabilities_added.add(cap_name)
                            epe = ET.SubElement(ee, "b2mml:EquipmentProceduralElement")
                            ET.SubElement(epe, "b2mml:ID").text = f"{equip}_{cap_name}"
                            ET.SubElement(epe, "b2mml:Description").text = f"{equip} {cap_name}"
                            
                            # 使用统一的"Process"类型
                            epe_type = "Process"
                                
                            ET.SubElement(epe, "b2mml:EquipmentProceduralElementType").text = epe_type
                            
                            # Associate equipment parameters with recipe parameters
                            step = next((s for s in rd.get("ProcessElements", []) if s['ID'] == step_id), None)
                            if step:
                                for p in step.get("Parameters", []):
                                    param = ET.SubElement(epe, "b2mml:Parameter")
                                    ET.SubElement(param, "b2mml:ID").text = p['Key']
                                    ET.SubElement(param, "b2mml:Description").text = f"{cap_name} {p['Key']}"
                                    ET.SubElement(param, "b2mml:ParameterType").text = "ProcessParameter"
                                    v = ET.SubElement(param, "b2mml:Value")
                                    ET.SubElement(v, "b2mml:ValueString").text = p.get("ValueString", "0")
                                    ET.SubElement(v, "b2mml:DataInterpretation").text = "Constant"
                                    
                                    # Use same inference function for consistency
                                    data_type, unit = self.infer_data_type_and_unit(p['Key'], p.get("ValueString", ""))
                                    ET.SubElement(v, "b2mml:DataType").text = data_type
                                    ET.SubElement(v, "b2mml:UnitOfMeasure").text = unit
                
                # Add explicit equipment connections
                if equip in equipment_connections:
                    for target_equip in equipment_connections[equip]:
                        conn = ET.SubElement(ee, "b2mml:EquipmentConnection")
                        ET.SubElement(conn, "b2mml:ID").text = f"{equip}To{target_equip}"
                        ET.SubElement(conn, "b2mml:ConnectionType").text = "MaterialMovement"
                        ET.SubElement(conn, "b2mml:FromEquipmentID").text = equip
                        ET.SubElement(conn, "b2mml:ToEquipmentID").text = target_equip

        # Format and save
        ET.indent(root, space="    ", level=0)
        tree = ET.ElementTree(root)
        tree.write(save_path, encoding="utf-8", xml_declaration=True)
        messagebox.showinfo("Success", f"Master recipe saved at:\n{save_path}")

if __name__=='__main__':
    root = tk.Tk()
    app = SMTGuiApp(root)
    root.mainloop()