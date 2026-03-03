"""
Requirements:
- Python 3.8+
- tkinter (standard)
- matplotlib

"""
import tkinter as tk
from tkinter import ttk, messagebox, simpledialog
from dataclasses import dataclass, field
from typing import List, Tuple, Optional, Dict
import copy
import uuid
import math

# Matplotlib for Gantt charts
import matplotlib
matplotlib.use("TkAgg")
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import matplotlib.pyplot as plt

# ------------------------
# Data model
# ------------------------
@dataclass
class Proc:
    pid: str
    burst: int
    arrival: int = 0          # default 0 for algos without arrival
    priority: Optional[int] = None
    quantum: Optional[int] = None  # used only in RR if provided per-process
    insertion_index: int = 0

    # computed fields
    start: Optional[float] = None
    completion: Optional[float] = None
    waiting: Optional[float] = None
    turnaround: Optional[float] = None

# ------------------------
# Utility functions
# ------------------------
def center_window(win, width=None, height=None):
    win.update_idletasks()
    if width is None:
        width = win.winfo_reqwidth()
    if height is None:
        height = win.winfo_reqheight()
    x = (win.winfo_screenwidth() // 2) - (width // 2)
    y = (win.winfo_screenheight() // 2) - (height // 2)
    win.geometry(f"{width}x{height}+{x}+{y}")

def parse_int_or_none(s):
    try:
        return int(s)
    except:
        return None

# ------------------------
# Scheduling algorithms
# ------------------------

def schedule_fcfs(processes: List[Proc]) -> Tuple[List[Proc], List[Tuple[str,float,float]]]:
    # All processes assumed available at time 0; FCFS uses insertion order
    procs = [copy.deepcopy(p) for p in processes]
    procs.sort(key=lambda p: p.insertion_index)
    clock = 0.0
    gantt = []
    for p in procs:
        p.start = clock
        p.completion = clock + p.burst
        p.turnaround = p.completion - p.arrival
        p.waiting = p.start - p.arrival
        gantt.append((p.pid, p.start, p.completion))
        clock = p.completion
    return procs, gantt

def schedule_sjf_nonpreemptive(processes: List[Proc]) -> Tuple[List[Proc], List[Tuple[str,float,float]]]:
    # All available at t=0, pick by shortest burst then insertion index
    procs = [copy.deepcopy(p) for p in processes]
    remaining = sorted(procs, key=lambda p: (p.burst, p.insertion_index))
    clock = 0.0
    gantt = []
    for p in remaining:
        p.start = clock
        p.completion = clock + p.burst
        p.turnaround = p.completion - p.arrival
        p.waiting = p.start - p.arrival
        gantt.append((p.pid, p.start, p.completion))
        clock = p.completion
    # return procs in insertion order but with computed fields
    pidmap = {p.pid: p for p in remaining}
    ordered = [pidmap[p.pid] for p in processes]
    return ordered, gantt

def schedule_srtf(processes: List[Proc]) -> Tuple[List[Proc], List[Tuple[str,float,float]]]:
    # Standard SRTF uses arrival times
    procs = [copy.deepcopy(p) for p in processes]
    n = len(procs)
    # remaining times map
    rem = {p.pid: p.burst for p in procs}
    for p in procs:
        p.start = None
        p.completion = None
        p.waiting = None
        p.turnaround = None
    time = 0
    gantt = []
    last_pid = None
    completed = 0
    # We'll run until all completed
    # Use time-stepped simulation (unit time granularity)
    while completed < n:
        # select available process with min remaining >0
        available = [p for p in procs if p.arrival <= time and rem[p.pid] > 0]
        if available:
            # choose with min remaining; tie-breaker insertion_index
            cur = min(available, key=lambda p: (rem[p.pid], p.insertion_index))
            if last_pid != cur.pid:
                gantt.append([cur.pid, time, None])  # will fill end later
                last_pid = cur.pid
            # mark start if first time
            if cur.start is None:
                cur.start = time
            # execute 1 time unit
            rem[cur.pid] -= 1
            time += 1
            if rem[cur.pid] == 0:
                cur.completion = time
                cur.turnaround = cur.completion - cur.arrival
                cur.waiting = cur.turnaround - cur.burst
                completed += 1
                # close latest gantt segment end
                if gantt and gantt[-1][0] == cur.pid and gantt[-1][2] is None:
                    gantt[-1][2] = time
        else:
            # idle step (advance to next arrival if any)
            next_arrivals = [p.arrival for p in procs if p.arrival > time]
            if not next_arrivals:
                break
            next_time = min(next_arrivals)
            # record IDLE in gantt if want, but we will skip
            time = next_time
            last_pid = None
    # convert gantt sublists to tuples (pid,start,end)
    gantt_t = []
    for seg in gantt:
        pid, s, e = seg
        if e is None:
            e = s + 1
        gantt_t.append((pid, float(s), float(e)))
    # ensure we include missing computed fields for any processes not scheduled (edge)
    return procs, gantt_t

def schedule_priority_nonpreemptive(processes: List[Proc], lower_is_higher=True) -> Tuple[List[Proc], List[Tuple[str,float,float]]]:
    # No arrival times. Select by priority (lower number => higher priority by default).
    procs = [copy.deepcopy(p) for p in processes]
    # For processes without priority, assign large number
    for p in procs:
        if p.priority is None:
            p.priority = 999999
    # sort by priority then insertion index
    if lower_is_higher:
        order = sorted(procs, key=lambda p: (p.priority, p.insertion_index))
    else:
        order = sorted(procs, key=lambda p: (-p.priority, p.insertion_index))
    clock = 0.0
    gantt = []
    for p in order:
        p.start = clock
        p.completion = clock + p.burst
        p.turnaround = p.completion - p.arrival
        p.waiting = p.start - p.arrival
        gantt.append((p.pid, p.start, p.completion))
        clock = p.completion
    # return in insertion order with computed values
    pidmap = {p.pid: p for p in order}
    ordered = [pidmap[p.pid] for p in processes]
    return ordered, gantt

def schedule_round_robin(processes: List[Proc], global_quantum: int = 2) -> Tuple[List[Proc], List[Tuple[str,float,float]]]:
    # Default: arrival times 0 for all (as per spec). Allow per-process quantum override.
    procs = [copy.deepcopy(p) for p in processes]
    # remaining times
    rem = {p.pid: p.burst for p in procs}
    for p in procs:
        p.start = None
        p.completion = None
        p.waiting = None
        p.turnaround = None

    from collections import deque
    queue = deque()
    # initial order by insertion index
    procs_sorted = sorted(procs, key=lambda p: p.insertion_index)
    for p in procs_sorted:
        queue.append(p)
    time = 0.0
    gantt = []
    last_pid = None
    completed = 0
    n = len(procs_sorted)
    while queue:
        p = queue.popleft()
        if rem[p.pid] <= 0:
            continue
        # effective quantum: per-process if provided, else global
        q = p.quantum if (p.quantum and p.quantum > 0) else global_quantum
        if last_pid != p.pid:
            gantt.append([p.pid, time, None])
            last_pid = p.pid
        if p.start is None:
            p.start = time
        run = min(rem[p.pid], q)
        rem[p.pid] -= run
        time += run
        # close segment end for this run
        if gantt and gantt[-1][0] == p.pid and gantt[-1][2] is None:
            gantt[-1][2] = time
        # if process finished
        if rem[p.pid] <= 0:
            p.completion = time
            p.turnaround = p.completion - p.arrival
            p.waiting = p.turnaround - p.burst
            completed += 1
        else:
            # requeue at end
            queue.append(p)
    # convert gantt to tuples
    gantt_t = [(pid, float(s), float(e)) for (pid, s, e) in gantt]
    # return processes in insertion order with computed metrics
    pidmap = {p.pid: p for p in procs}
    ordered = [pidmap[p.pid] for p in processes]
    return ordered, gantt_t

# ------------------------
# GUI Base Class for Algorithm Windows
# ------------------------
class AlgoWindowBase:
    def __init__(self, parent, title: str, fields: List[Tuple[str,str]], algo_key: str):
        """
        fields: list of tuples (label, key) where key in {'pid','burst','arrival','priority','quantum'}
        algo_key: one of 'FCFS','SJF','SRTF','PRIORITY','RR'
        """
        self.parent = parent
        self.title = title
        self.fields = fields
        self.algo_key = algo_key
        self.win = tk.Toplevel(parent)
        self.win.title(f"{title} — {algo_key}")
        self.win.configure(bg="#EAF6FF")  # pastel blue background
        self.win.protocol("WM_DELETE_WINDOW", self.win.destroy)
        center_window(self.win, width=940, height=720)
        # process storage
        self.procs: List[Proc] = []
        self.counter = 0
        # font sizes (slightly bigger)
        self.hfont = ("Segoe UI Semibold", 14)
        self.lfont = ("Segoe UI", 12)
        self._build_ui()

    def _build_ui(self):
        header = tk.Label(self.win, text=f"{self.algo_key} Scheduler", font=self.hfont, bg="#EAF6FF")
        header.pack(pady=(10,4))

        # Input frame
        inp = ttk.Frame(self.win)
        inp.pack(fill="x", padx=12, pady=8)

        # dynamic entry fields stored in dict
        self.vars: Dict[str, tk.StringVar] = {}
        col = 0
        for label, key in self.fields:
            ttk.Label(inp, text=label + ":", font=self.lfont).grid(row=0, column=col*2, padx=6, pady=6, sticky="w")
            var = tk.StringVar()
            ent = ttk.Entry(inp, textvariable=var, width=16, font=self.lfont)
            ent.grid(row=0, column=col*2+1, padx=6, pady=6)
            self.vars[key] = var
            col += 1

        # Add / Edit / Delete / Clear
        btn_add = ttk.Button(inp, text="Add Process", command=self.add_process, width=14)
        btn_add.grid(row=0, column=col*2, padx=6, pady=6)
        btn_edit = ttk.Button(inp, text="Edit Selected", command=self.edit_selected)
        btn_edit.grid(row=0, column=col*2+1, padx=6, pady=6)
        btn_del = ttk.Button(inp, text="Delete Selected", command=self.delete_selected)
        btn_del.grid(row=0, column=col*2+2, padx=6, pady=6)

        # Treeview columns depend on algo
        cols = ["PID","Burst"]
        if any(k=="arrival" for _,k in self.fields):
            cols.append("Arrival")
        if any(k=="priority" for _,k in self.fields):
            cols.append("Priority")
        if any(k=="quantum" for _,k in self.fields):
            cols.append("Quantum")
        cols += ["Waiting","Turnaround"]
        # Treeview
        self.tree = ttk.Treeview(self.win, columns=cols, show="headings", height=9)
        for c in cols:
            self.tree.heading(c, text=c)
            # slightly wider columns for readability
            self.tree.column(c, width=100, anchor="center")
        self.tree.pack(fill="x", padx=12, pady=(6,4))

        # Buttons: Run, Clear All, Export CSV (optional)
        act = ttk.Frame(self.win)
        act.pack(fill="x", padx=12, pady=6)
        btn_run = ttk.Button(act, text="Run "+self.algo_key, command=self.run_algo, width=14)
        btn_run.pack(side="left", padx=6)
        btn_clear = ttk.Button(act, text="Clear All", command=self.clear_all)
        btn_clear.pack(side="left", padx=6)
        # Metrics labels
        metrics = ttk.Frame(self.win)
        metrics.pack(fill="x", padx=12, pady=6)
        self.avg_wait_lbl = ttk.Label(metrics, text="Avg Waiting Time: —", font=self.lfont)
        self.avg_turn_lbl = ttk.Label(metrics, text="Avg Turnaround Time: —", font=self.lfont)
        self.total_cpu_lbl = ttk.Label(metrics, text="Total CPU Time: —", font=self.lfont)
        self.avg_wait_lbl.grid(row=0, column=0, sticky="w", padx=6)
        self.avg_turn_lbl.grid(row=0, column=1, sticky="w", padx=6)
        self.total_cpu_lbl.grid(row=0, column=2, sticky="w", padx=6)

        # Gantt chart area
        chart_frame = ttk.LabelFrame(self.win, text="Gantt Chart", padding=8)
        chart_frame.pack(fill="both", expand=True, padx=12, pady=8)
        self.fig, self.ax = plt.subplots(figsize=(9,3))
        plt.subplots_adjust(left=0.12, right=0.95, top=0.88, bottom=0.12)
        self.canvas = FigureCanvasTkAgg(self.fig, master=chart_frame)
        self.canvas.get_tk_widget().pack(fill="both", expand=True)

    # -----------------
    # Process management
    # -----------------
    def _read_inputs(self) -> Optional[Dict]:
        vals = {}
        for key,var in self.vars.items():
            v = var.get().strip()
            if key == 'pid':
                if not v:
                    messagebox.showerror("Input error", "PID cannot be empty.")
                    return None
                vals['pid'] = v
            elif key == 'burst':
                try:
                    b = int(v)
                    if b <= 0:
                        raise ValueError()
                    vals['burst'] = b
                except:
                    messagebox.showerror("Input error", "Burst must be a positive integer.")
                    return None
            elif key == 'arrival':
                try:
                    a = int(v)
                    if a < 0:
                        raise ValueError()
                    vals['arrival'] = a
                except:
                    messagebox.showerror("Input error", "Arrival must be a non-negative integer.")
                    return None
            elif key == 'priority':
                try:
                    pr = int(v)
                    vals['priority'] = pr
                except:
                    messagebox.showerror("Input error", "Priority must be an integer.")
                    return None
            elif key == 'quantum':
                if v == "":
                    vals['quantum'] = None
                else:
                    try:
                        q = int(v)
                        if q <= 0:
                            raise ValueError()
                        vals['quantum'] = q
                    except:
                        messagebox.showerror("Input error", "Quantum must be a positive integer.")
                        return None
        return vals

    def add_process(self):
        vals = self._read_inputs()
        if vals is None:
            return
        pid = vals.get('pid')
        # ensure unique PID; append short suffix if duplicate
        existing = {p.pid for p in self.procs}
        if pid in existing:
            pid = f"{pid}_{str(uuid.uuid4())[:4]}"
        burst = vals.get('burst')
        arrival = vals.get('arrival', 0)
        priority = vals.get('priority', None)
        quantum = vals.get('quantum', None)
        p = Proc(pid=pid, burst=burst, arrival=arrival, priority=priority, quantum=quantum, insertion_index=self.counter)
        self.counter += 1
        self.procs.append(p)
        self._refresh_tree()
        # clear input fields
        for var in self.vars.values():
            var.set("")

    def edit_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showwarning("Edit process", "Select a process to edit.")
            return
        item = sel[0]
        vals = self.tree.item(item, "values")
        pid = vals[0]
        proc = next((p for p in self.procs if p.pid == pid), None)
        if not proc:
            messagebox.showerror("Error", "Process not found.")
            return
        # For simplicity, allow editing burst/arrival/priority/quantum via dialogs
        # Burst
        new_burst = simpledialog.askinteger("Edit Burst", f"New burst for {pid}:", initialvalue=proc.burst, minvalue=1)
        if new_burst is None:
            return
        proc.burst = new_burst
        if any(k=='arrival' for _,k in self.fields):
            new_arrival = simpledialog.askinteger("Edit Arrival", f"New arrival for {pid}:", initialvalue=proc.arrival, minvalue=0)
            if new_arrival is None:
                return
            proc.arrival = new_arrival
        if any(k=='priority' for _,k in self.fields):
            new_pr = simpledialog.askinteger("Edit Priority", f"New priority for {pid}:", initialvalue=(proc.priority if proc.priority is not None else 0))
            if new_pr is None:
                return
            proc.priority = new_pr
        if any(k=='quantum' for _,k in self.fields):
            new_q = simpledialog.askinteger("Edit Quantum (optional)", f"New quantum for {pid} (leave empty to use global):", initialvalue=(proc.quantum if proc.quantum else 0), minvalue=0)
            # if user enters 0 treat as None
            if new_q is None:
                pass
            else:
                proc.quantum = new_q if new_q>0 else None
        self._refresh_tree()

    def delete_selected(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showwarning("Delete process", "Select a process to delete.")
            return
        item = sel[0]
        vals = self.tree.item(item, "values")
        pid = vals[0]
        self.procs = [p for p in self.procs if p.pid != pid]
        self._refresh_tree()

    def clear_all(self):
        if messagebox.askyesno("Clear all", "Remove all processes?"):
            self.procs = []
            self._refresh_tree()
            self._clear_metrics()
            self._clear_gantt()

    def _refresh_tree(self):
        for r in self.tree.get_children():
            self.tree.delete(r)
        for p in self.procs:
            row = [p.pid, str(p.burst)]
            if any(k=='arrival' for _,k in self.fields):
                row.append(str(p.arrival))
            if any(k=='priority' for _,k in self.fields):
                row.append(str(p.priority) if p.priority is not None else "—")
            if any(k=='quantum' for _,k in self.fields):
                row.append(str(p.quantum) if p.quantum is not None else "—")
            row.append(f"{p.waiting:.2f}" if p.waiting is not None else "—")
            row.append(f"{p.turnaround:.2f}" if p.turnaround is not None else "—")
            self.tree.insert("", "end", values=tuple(row))

    # -----------------
    # Run scheduling
    # -----------------
    def run_algo(self):
        if not self.procs:
            messagebox.showwarning("Run", "No processes to schedule.")
            return
        # dispatch per algo_key
        if self.algo_key == 'FCFS':
            computed, gantt = schedule_fcfs(self.procs)
        elif self.algo_key == 'SJF':
            computed, gantt = schedule_sjf_nonpreemptive(self.procs)
        elif self.algo_key == 'SRTF':
            # ensure arrival fields present for all procs
            for p in self.procs:
                if p.arrival is None:
                    messagebox.showerror("Input error", "All processes must have arrival times for SRTF.")
                    return
            computed, gantt = schedule_srtf(self.procs)
        elif self.algo_key == 'PRIORITY':
            computed, gantt = schedule_priority_nonpreemptive(self.procs, lower_is_higher=True)
        elif self.algo_key == 'RR':
            # get global quantum if present among inputs (we add a field 'global_quantum' in vars if present)
            gq = None
            if 'global_quantum' in self.vars:
                v = self.vars['global_quantum'].get().strip()
                if v != "":
                    try:
                        gq = int(v)
                        if gq <= 0:
                            raise ValueError()
                    except:
                        messagebox.showerror("Input error", "Global quantum must be a positive integer.")
                        return
            if gq is None:
                gq = 2
            computed, gantt = schedule_round_robin(self.procs, global_quantum=gq)
        else:
            # default fallback to FCFS
            computed, gantt = schedule_fcfs(self.procs)

        # Update internal procs with computed metrics (match by pid)
        comp_map = {p.pid: p for p in computed}
        for p in self.procs:
            cp = comp_map.get(p.pid)
            if cp:
                p.start = cp.start
                p.completion = cp.completion
                p.waiting = cp.waiting
                p.turnaround = cp.turnaround
        self._refresh_tree()
        self._update_metrics()
        self._draw_gantt(gantt)

    # -----------------
    # Metrics & Gantt
    # -----------------
    def _update_metrics(self):
        if not self.procs:
            self._clear_metrics()
            return
        n = len(self.procs)
        wait_vals = [p.waiting for p in self.procs if p.waiting is not None]
        turn_vals = [p.turnaround for p in self.procs if p.turnaround is not None]
        avg_wait = sum(wait_vals)/len(wait_vals) if wait_vals else 0.0
        avg_turn = sum(turn_vals)/len(turn_vals) if turn_vals else 0.0
        total_cpu = sum(p.burst for p in self.procs)
        # per your spec: for Priority and RR some windows compute only avg waiting; but we display both numbers
        self.avg_wait_lbl.config(text=f"Avg Waiting Time: {avg_wait:.2f}")
        self.avg_turn_lbl.config(text=f"Avg Turnaround Time: {avg_turn:.2f}")
        self.total_cpu_lbl.config(text=f"Total CPU Time: {total_cpu:.2f}")

    def _clear_metrics(self):
        self.avg_wait_lbl.config(text="Avg Waiting Time: —")
        self.avg_turn_lbl.config(text="Avg Turnaround Time: —")
        self.total_cpu_lbl.config(text="Total CPU Time: —")

    def _clear_gantt(self):
        self.ax.clear()
        self.canvas.draw()

    def _draw_gantt(self, gantt: List[Tuple[str,float,float]]):
        self.ax.clear()
        if not gantt:
            self.canvas.draw()
            return
        # create lane per unique pid in order of appearance
        uniq = []
        for pid, s, e in gantt:
            if pid not in uniq:
                uniq.append(pid)
        uniq_rev = uniq[::-1]
        ypos = {pid: idx for idx, pid in enumerate(uniq_rev)}
        for pid, start, end in gantt:
            y = ypos[pid]
            self.ax.broken_barh([(start, end - start)], (y - 0.4, 0.8), facecolors='tab:blue')
            self.ax.text(start + (end-start)/2, y, pid, ha='center', va='center', color='white', fontsize=10)
        self.ax.set_yticks(list(ypos.values()))
        self.ax.set_yticklabels(list(uniq_rev))
        self.ax.set_xlabel("Time", fontsize=11)
        self.ax.grid(axis='x', linestyle='--', alpha=0.4)
        self.fig.tight_layout()
        self.canvas.draw()

# ------------------------
# Application main window
# ------------------------
class MainApp:
    def __init__(self, root):
        self.root = root
        root.title("CPU Scheduler — Multi-Window")
        root.configure(bg="#EAF6FF")  # pastel blue
        center_window(root, width=560, height=400)
        self._build_ui()

    def _build_ui(self):
        title = tk.Label(self.root, text="CPU Scheduler — Choose an Algorithm", font=("Segoe UI Semibold", 16), bg="#EAF6FF")
        title.pack(pady=(20,10))

        btn_frame = ttk.Frame(self.root)
        btn_frame.pack(pady=10)

        ttk.Button(btn_frame, text="FCFS (PID, Burst)", width=24, command=self.open_fcfs).grid(row=0, column=0, padx=10, pady=8)
        ttk.Button(btn_frame, text="SJF (PID, Burst)", width=24, command=self.open_sjf).grid(row=0, column=1, padx=10, pady=8)
        ttk.Button(btn_frame, text="SRTF (PID, Arrival, Burst)", width=24, command=self.open_srtf).grid(row=1, column=0, padx=10, pady=8)
        ttk.Button(btn_frame, text="Priority (PID, Burst, Priority)", width=24, command=self.open_priority).grid(row=1, column=1, padx=10, pady=8)
        ttk.Button(btn_frame, text="Round Robin (PID, Burst, Quantum)", width=50, command=self.open_rr).grid(row=2, column=0, columnspan=2, padx=10, pady=8)

        foot = tk.Label(self.root, text="Theme: Pastel Blue | Windows open centered | Fonts slightly larger", bg="#EAF6FF")
        foot.pack(pady=(10,0))

    def open_fcfs(self):
        # FCFS fields: pid, burst
        fields = [("PID","pid"), ("Burst","burst")]
        AlgoWindowBase(self.root, title="FCFS Scheduler", fields=fields, algo_key='FCFS')

    def open_sjf(self):
        fields = [("PID","pid"), ("Burst","burst")]
        AlgoWindowBase(self.root, title="SJF Scheduler", fields=fields, algo_key='SJF')

    def open_srtf(self):
        # SRTF needs arrival
        fields = [("PID","pid"), ("Arrival","arrival"), ("Burst","burst")]
        AlgoWindowBase(self.root, title="SRTF Scheduler", fields=fields, algo_key='SRTF')

    def open_priority(self):
        fields = [("PID","pid"), ("Burst","burst"), ("Priority","priority")]
        AlgoWindowBase(self.root, title="Priority Scheduler", fields=fields, algo_key='PRIORITY')

    def open_rr(self):
        # RR: allow global quantum input + per-process quantum in the table
        # we include a global quantum entry in the window inputs as well (key 'global_quantum')
        aw = AlgoWindowBase(self.root, title="Round Robin Scheduler", fields=[("PID","pid"), ("Burst","burst"), ("Quantum (optional)","quantum")], algo_key='RR')
        # add an extra field for global quantum on the created window
        # place it in the top input area to right
        top_inp_frame = aw.win.winfo_children()[1]  # matches how we built UI earlier (fragile but works)
        # create a small frame for global quantum
        gq_label = ttk.Label(top_inp_frame, text="Global Quantum:", font=("Segoe UI",12))
        gq_entry_var = tk.StringVar(value="2")
        gq_entry = ttk.Entry(top_inp_frame, textvariable=gq_entry_var, width=10, font=("Segoe UI",12))
        cols = len(aw.fields)
        gq_label.grid(row=0, column=cols*2+1, padx=6, pady=6)
        gq_entry.grid(row=0, column=cols*2+2, padx=6, pady=6)
        aw.vars['global_quantum'] = gq_entry_var
        # done

# ------------------------
# Run the application
# ------------------------
def main():
    root = tk.Tk()
    app = MainApp(root)
    root.mainloop()

if __name__ == "__main__":
    main()
