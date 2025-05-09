import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json, csv, re, math, traceback, logging

# Enable detailed logging for debugging
logging.basicConfig(level=logging.INFO, format='%(levelname)s: %(message)s')
logger = logging.getLogger('matcher')
DEBUG = True

# Improved operator regex for more strict numerical pattern matching
OPER_RE = re.compile(r'^(>=|<=|>|<|=)?\s*([0-9]+(?:\.[0-9]+)?)')

# Enhanced synonym dictionary with more precise term mappings
SYNONYMS = {
    'revolutionsperminute': ['revolutionsperminute', 'rpm', 'rotationalvelocity', 'rotation'],
    'settemperature': ['heatingtemperaturetoreachofthisprocessstep', 'temperature', 'temp'],
    'stirringtime': ['durationoftheprocessstepmixing', 'mixingduration', 'mixtime', 'stirtime'],
    'holdingtime': ['maxdurationoftheprocessstepheating', 'heatingduration', 'heattime', 'heatduration'],
    'volume': ['amountofdosing', 'litre', 'liter', 'amount', 'liquidvolume', 'dosingamount'],
    'cycleTime': ['cycle', 'frequency'],
    'dutyCycle': ['duty', 'pulseduty'],
    'heatPower': ['power', 'heatpower', 'powerheat'],
    'pulseTimeHigh': ['pulsehigh', 'highpulse', 'pulsehi'],
    'pulseTimeLow': ['pulselow', 'lowpulse', 'pulselo'],
}

# Create reverse synonym mapping for easier lookup
REVERSE_SYNONYMS = {}
for primary, synonyms in SYNONYMS.items():
    for syn in synonyms:
        REVERSE_SYNONYMS[syn] = primary

def norm(txt: str) -> str:
    """Normalize text by removing non-alphanumeric characters and converting to lowercase"""
    return re.sub(r'[^a-z0-9]', '', (txt or '').lower())

def parse_value(val_str: str):
    """Parse value string, supporting various comparison operators"""
    # Replace Unicode comparison symbols with standard symbols
    val_str = val_str.replace('≤', '<=').replace('≥', '>=')
    m = OPER_RE.match(val_str.strip())
    if not m: 
        # Try to parse directly as number
        try:
            return '=', float(val_str.strip())
        except:
            logger.warning(f"Cannot parse value: '{val_str}'")
            return '=', None
    op = m.group(1) or '='
    return op, float(m.group(2))

def to_float_safe(val):
    """Safely convert value to float"""
    if val is None:
        return None
    try: 
        return float(val)
    except: 
        logger.warning(f"Cannot convert to float: '{val}'")
        return None

def satisfies(op: str, target: float, vmin_raw, vmax_raw):
    """Check if target value satisfies given range and operator"""
    vmin = to_float_safe(vmin_raw)
    vmax = to_float_safe(vmax_raw)
    vmin = -math.inf if vmin is None else vmin
    vmax = math.inf if vmax is None else vmax
    
    # Log value comparison in debug mode
    if DEBUG:
        logger.info(f"Comparing: {vmin} <= {target} <= {vmax}, Operator: {op}")
    
    if op == '=':  return vmin <= target <= vmax
    if op == '>':  return target > vmin
    if op == '>=': return target >= vmin
    if op == '<':  return target < vmax
    if op == '<=': return target <= vmax
    return False

def find_property(param_key: str, properties):
    """Find matching property for parameter with improved synonym matching"""
    norm_key = norm(param_key)
    
    # Try to find primary keyword via reverse synonyms
    primary_key = norm_key
    for syn, primary in REVERSE_SYNONYMS.items():
        # Use exact or significant partial match for synonym detection
        if norm_key == norm(syn) or (len(norm_key) > 5 and len(norm(syn)) > 5 and 
                                    (norm_key in norm(syn) or norm(syn) in norm_key)):
            primary_key = primary
            logger.info(f"Mapped parameter '{param_key}' to primary key '{primary}'")
            break
            
    # Prepare candidate keywords
    candidates = [primary_key] + SYNONYMS.get(primary_key, [])
    
    # Check each property
    for pr in properties:
        pname = norm(pr.get('property_name'))
        
        # If exact match exists, return immediately
        if pname == norm_key:
            logger.info(f"Exact property match found: '{param_key}' --> '{pr.get('property_name')}'")
            return pr
            
        # Check synonyms with improved partial matching
        for key in candidates:
            k = norm(key)
            
            # Use exact match
            if pname == k:
                logger.info(f"Synonym exact match: '{param_key}' --> '{pr.get('property_name')}'")
                return pr
                
            # Use significant substring match (only if both strings are substantial)
            if len(k) > 5 and len(pname) > 5:
                # Check if one is a significant substring of the other (at least 70% match)
                if (k in pname and len(k) >= 0.7 * len(pname)) or \
                   (pname in k and len(pname) >= 0.7 * len(k)):
                    logger.info(f"Significant substring match: '{param_key}' --> '{pr.get('property_name')}'")
                    return pr
                
    # No match found
    logger.warning(f"No property match found for: '{param_key}'")
    return None

def semantic_ok(concept: str, entry: dict) -> bool:
    """Verify if semantic concept matches capability entry"""
    step = concept.lower()
    
    # Check direct capability match
    for cap in entry.get('capability', []):
        cap_id = cap.get('capability_ID', '').lower()
        cap_name = cap.get('capability_name', '').lower()
        
        # Exact match check
        if step == cap_id.split('#')[-1] or step == cap_name:
            logger.info(f"Exact semantic match: '{step}' and '{cap_name}'")
            return True
            
        # Significant partial match check
        if len(step) > 4 and (step in cap_id or step in cap_name):
            logger.info(f"Partial semantic match: '{step}' in '{cap_id}' or '{cap_name}'")
            return True
            
        # Check generalization relationships
        for g in entry.get('generalized_by', []):
            if step == g.lower():
                logger.info(f"Match via generalization: '{step}' and '{g}'")
                return True
    
    # No match found
    logger.warning(f"No semantic match for: '{concept}'")
    return False

class Matcher:
    def __init__(self, recipe: dict, caps: dict):
        self.recipe = recipe
        self.caps = caps
        self.rows = []
        self.debug_info = []  # Added to store detailed debug information

    def run(self):
        """Run matching process and return results"""
        for step in self.recipe.get('ProcessElements', []):
            sid = step.get('ID') or step.get('idShort') or '--'
            sem = step.get('SemanticDescription') or step.get('semanticId') or ''
            
            # Extract semantic concept
            if isinstance(sem, dict) and 'keys' in sem and len(sem['keys']) > 0:
                concept = sem['keys'][0]['value'].split('#')[-1]
            else:
                concept = str(sem).split('#')[-1]
                
            logger.info(f"\n===== Processing Step: '{sid}' (Concept: '{concept}') =====")

            # Extract parameters
            param_strs, param_map = [], {}
            for p in step.get('Parameters', []):
                desc = p.get('Description', '')
                op, val = parse_value(p.get('ValueString', ''))
                key = norm(desc)
                if val is not None:
                    param_map[key] = (op, val, desc)  # Store original description for better reporting
                unit = p.get('UnitOfMeasure', '').split('/')[-1]
                param_strs.append(f"{desc}:{p.get('ValueString')} {unit}")
            param_disp = '; '.join(param_strs)
            
            logger.info(f"Extracted parameters: {param_map}")

            # Try matching for each resource
            for res, entries in self.caps.items():
                logger.info(f"\n🔍 Trying to match step '{sid}' ({concept}) with resource {res}")
                matches = []  # Store all matching entries
                step_debug_info = []  # Debug info for this particular step-resource combination
                
                for e in entries:
                    # Check semantic match
                    if not semantic_ok(concept, e): 
                        step_debug_info.append(f"❌ Resource {res}: No semantic match for '{concept}'")
                        logger.info("  ❌ No semantic match")
                        continue
                        
                    props = e.get('properties', [])
                    ok = True
                    detailed_results = []
                    entry_debug_info = []  # Debug info for this particular entry
                    
                    # Check if each parameter matches
                    for pk, (op, val, orig_desc) in param_map.items():
                        prop = find_property(orig_desc, props)  # Use original description for better matching
                        if not prop:
                            entry_debug_info.append(f"❌ No matching property found for '{orig_desc}'")
                            detailed_results.append(f"  ❌ No matching property found for '{orig_desc}'")
                            ok = False
                            break
                            
                        vmin = prop.get('valueMin') or prop.get('value0')
                        vmax = prop.get('valueMax') or prop.get('value1')
                        
                        if not satisfies(op, val, vmin, vmax):
                            msg = f"{prop['property_name']} [{vmin}-{vmax}] does not satisfy {op} {val}"
                            entry_debug_info.append(f"❌ {msg}")
                            detailed_results.append(f"  ❌ {msg}")
                            ok = False
                            break
                        else:
                            msg = f"{prop['property_name']} [{vmin}-{vmax}] satisfies {op} {val}"
                            entry_debug_info.append(f"✅ {msg}")
                            detailed_results.append(f"  ✅ {msg}")
                    
                    # Print detailed results
                    for dr in detailed_results:
                        logger.info(dr)
                        
                    # Collect capability names for this entry
                    caps_names = [c.get('capability_name', '') for c in e.get('capability', [])]
                    caps_str = ', '.join(caps_names)
                    
                    if ok:
                        matches.append(e)  # Add to matches
                        logger.info(f"  ✅ Found matching capability entry: {caps_str}")
                        entry_debug_info.append(f"✅ Complete match found for capabilities: {caps_str}")
                        step_debug_info.append(f"✅ Resource {res}: Found match: {caps_str}")
                        step_debug_info.extend([f"  {detail}" for detail in entry_debug_info])
                    else:
                        logger.info(f"  ❌ No match for capabilities: {caps_str}")
                        entry_debug_info.append(f"❌ Match failed for capabilities: {caps_str}")
                        step_debug_info.append(f"❌ Resource {res}: Failed match: {caps_str}")
                        step_debug_info.extend([f"  {detail}" for detail in entry_debug_info])

                # Prepare result rows - one row per matching capability
                available = len(matches) > 0
                
                if available:
                    # Create separate rows for each matching capability
                    for match in matches:
                        caps_str = ', '.join(c.get('capability_name', '') for c in match.get('capability', []))
                        props_str = ', '.join(
                            f"{pr['property_name']}: {pr.get('valueMin') or pr.get('value0')}–{pr.get('valueMax') or pr.get('value1')}" 
                            for pr in match.get('properties', [])
                        )
                        realized = ', '.join(match.get('realized_by', []))
                        
                        # Add result row for this capability match
                        self.rows.append((
                            sid, param_disp, res, 'Yes', 
                            caps_str, props_str, realized
                        ))
                else:
                    # Add a single "No match" row
                    self.rows.append((
                        sid, param_disp, res, 'No', '', '', ''
                    ))
                    
                # Store debug info
                self.debug_info.append({
                    'step_id': sid,
                    'resource': res,
                    'available': available,
                    'details': step_debug_info
                })
                
        return self.rows

    def get_debug_report(self):
        """Generate a detailed debug report"""
        report = []
        report.append("===== DETAILED MATCHING DEBUG REPORT =====\n")
        
        for info in self.debug_info:
            report.append(f"Step: {info['step_id']} | Resource: {info['resource']} | Match: {'✅ Yes' if info['available'] else '❌ No'}")
            for detail in info['details']:
                report.append(f"  {detail}")
            report.append("")
            
        return '\n'.join(report)

class GUI:
    def __init__(self, root):
        self.root = root
        root.title('Enhanced Capability Matcher – (Multi-Capabilities)')
        self.recipe = self.caps = None
        self.matcher = None
        self.rows = []
        self._build()

    def _build(self):
        """Build GUI interface"""
        # Create top button bar
        bar = tk.Frame(self.root)
        bar.pack(pady=8)
        
        tk.Button(bar, text='Load Recipe', command=self.load_recipe).grid(row=0, column=0, padx=4)
        tk.Button(bar, text='Load Capabilities', command=self.load_caps).grid(row=0, column=1, padx=4)
        
        self.btn_match = tk.Button(bar, text='Match', state='disabled', command=self.do_match)
        self.btn_match.grid(row=0, column=2, padx=4)
        
        self.btn_export = tk.Button(bar, text='Export CSV', state='disabled', command=self.export)
        self.btn_export.grid(row=0, column=3, padx=4)

        self.btn_debug = tk.Button(bar, text='Debug Report', state='disabled', command=self.show_debug)
        self.btn_debug.grid(row=0, column=4, padx=4)

        # Create status bar
        self.status_var = tk.StringVar()
        self.status_var.set("Ready")
        status_bar = tk.Label(self.root, textvariable=self.status_var, bd=1, relief=tk.SUNKEN, anchor=tk.W)
        status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        # Create treeview
        cols = ('Step ID', 'Step Parameters', 'Resource', 'Available', 'Capability', 'Capability Properties', 'Implemented By')
        self.tree = ttk.Treeview(self.root, columns=cols, show='headings')
        
        for i, c in enumerate(cols):
            self.tree.heading(c, text=c)
            width = 300 if i == 1 else 180  # Make Step Parameters column wider
            self.tree.column(c, width=width, anchor='w')
            
        # Add scrollbars
        v_scrollbar = ttk.Scrollbar(self.root, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=v_scrollbar.set)
        
        h_scrollbar = ttk.Scrollbar(self.root, orient="horizontal", command=self.tree.xview)
        self.tree.configure(xscrollcommand=h_scrollbar.set)
        
        # Pack everything
        self.tree.pack(side=tk.LEFT, fill='both', expand=True, padx=6, pady=6)
        v_scrollbar.pack(side=tk.RIGHT, fill='y', pady=6)
        h_scrollbar.pack(side=tk.BOTTOM, fill='x', padx=6)

    def load_recipe(self):
        """Load recipe file"""
        p = filedialog.askopenfilename(filetypes=[('JSON files','*.json')])
        if p:
            try:
                self.recipe = json.load(open(p, encoding='utf-8'))
                self.status_var.set(f"Recipe loaded: {p}")
                messagebox.showinfo('Success','Recipe loaded')
            except Exception as e:
                self.status_var.set(f"Loading error: {str(e)}")
                messagebox.showerror('Error', str(e))
        self._update_btn()

    def load_caps(self):
        """Load capabilities file"""
        p = filedialog.askopenfilename(filetypes=[('JSON files','*.json')])
        if p:
            try:
                self.caps = json.load(open(p, encoding='utf-8'))
                self.status_var.set(f"Capabilities loaded: {p}")
                messagebox.showinfo('Success','Capabilities loaded')
            except Exception as e:
                self.status_var.set(f"Loading error: {str(e)}")
                messagebox.showerror('Error', str(e))
        self._update_btn()

    def _update_btn(self):
        """Update button states"""
        self.btn_match.config(state='normal' if (self.recipe and self.caps) else 'disabled')
        self.btn_export.config(state='disabled')
        self.btn_debug.config(state='disabled')

    def do_match(self):
        """Execute matching process"""
        try:
            self.status_var.set("Matching...")
            self.tree.delete(*self.tree.get_children())
            self.matcher = Matcher(self.recipe, self.caps)
            self.rows = self.matcher.run()
            
            # Display matching results
            for row in self.rows:
                self.tree.insert('', tk.END, values=row)
                
            self.btn_export.config(state='normal')
            self.btn_debug.config(state='normal')
            self.status_var.set(f"Matching completed, found {len(self.rows)} results")
            messagebox.showinfo('Complete','Matching completed')
        except Exception as e:
            traceback.print_exc()
            self.status_var.set(f"Matching error: {str(e)}")
            messagebox.showerror('Error', str(e))

    def export(self):
        """Export matching results to CSV file"""
        p = filedialog.asksaveasfilename(
            defaultextension='.csv',
            filetypes=[('CSV files','*.csv')]
        )
        if p:
            with open(p, 'w', newline='', encoding='utf-8') as f:
                w = csv.writer(f)
                w.writerow(['Step ID', 'Step Parameters', 'Resource', 'Available', 'Capability', 'Capability Properties', 'Implemented By'])
                w.writerows(self.rows)
            self.status_var.set(f"Exported to: {p}")
            messagebox.showinfo('Saved', f'Exported to {p}')

    def show_debug(self):
        """Show debug report in a new window"""
        if not self.matcher:
            return
            
        debug_window = tk.Toplevel(self.root)
        debug_window.title("Matching Debug Report")
        debug_window.geometry("800x600")
        
        text = tk.Text(debug_window, wrap=tk.WORD)
        text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Add scrollbar
        scrollbar = tk.Scrollbar(text, command=text.yview)
        text.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Insert debug report
        report = self.matcher.get_debug_report()
        text.insert(tk.END, report)
        text.config(state=tk.DISABLED)  # Make read-only

if __name__ == '__main__':
    root = tk.Tk()
    root.geometry("1200x600")  # Set initial window size
    app = GUI(root)
    root.mainloop()
