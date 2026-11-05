import Papers.PODC2013.ConstantBarriersMutex.Model

/-!
# Basic lemmas: views of store buffers, effects of steps
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-! ### Kinds of writes -/

/-- The write is to `lock`. -/
def W.isLock : W h → Bool | .lock _ => true | _ => false
/-- The write is to `promQ`. -/
def W.isPromQ : W h → Bool | .promQ _ => true | _ => false
/-- The write is to `exits`. -/
def W.isExits : W h → Bool | .exits _ => true | _ => false
/-- The write is to `inPromQ[q]`. -/
def W.isInPromQ (q : Proc h) : W h → Bool | .inPromQ q' _ => decide (q' = q) | _ => false
/-- The write is to `apply[q]`. -/
def W.isApply (q : Proc h) : W h → Bool | .apply q' _ => decide (q' = q) | _ => false
/-- The write is to `signal[q]`. -/
def W.isSignal (q : Proc h) : W h → Bool | .signal q' _ => decide (q' = q) | _ => false
/-- The write is to node `i`. -/
def W.isNode (i : ℕ) : W h → Bool | .node i' _ => decide (i' = i) | _ => false

@[simp] lemma Mem.view_nil (m : Mem h) : m.view [] = m := rfl
@[simp] lemma Mem.view_cons (m : Mem h) (w : W h) (b : List (W h)) :
    m.view (w :: b) = (m.write w).view b := rfl
@[simp] lemma Mem.view_append (m : Mem h) (b c : List (W h)) :
    m.view (b ++ c) = (m.view b).view c := by
  simp [Mem.view, List.foldl_append]

/-! ### Fields of a single write -/

@[simp] lemma write_lock (m : Mem h) (w : W h) :
    (m.write w).lock = match w with | .lock v => v | _ => m.lock := by cases w <;> rfl
@[simp] lemma write_promQ (m : Mem h) (w : W h) :
    (m.write w).promQ = match w with | .promQ l => l | _ => m.promQ := by cases w <;> rfl
@[simp] lemma write_exits (m : Mem h) (w : W h) :
    (m.write w).exits = match w with | .exits v => v | _ => m.exits := by cases w <;> rfl
lemma write_inPromQ (m : Mem h) (w : W h) (q : Proc h) :
    (m.write w).inPromQ q = match w with
      | .inPromQ q' b => if q' = q then b else m.inPromQ q | _ => m.inPromQ q := by
  cases w <;> simp [Mem.write, Function.update_apply, eq_comm]
lemma write_apply (m : Mem h) (w : W h) (q : Proc h) :
    (m.write w).apply q = match w with
      | .apply q' b => if q' = q then b else m.apply q | _ => m.apply q := by
  cases w <;> simp [Mem.write, Function.update_apply, eq_comm]
lemma write_signal (m : Mem h) (w : W h) (q : Proc h) :
    (m.write w).signal q = match w with
      | .signal q' b => if q' = q then b else m.signal q | _ => m.signal q := by
  cases w <;> simp [Mem.write, Function.update_apply, eq_comm]
lemma write_node (m : Mem h) (w : W h) (i : ℕ) :
    (m.write w).node i = match w with
      | .node i' v => if i' = i then some v else m.node i | _ => m.node i := by
  cases w <;> simp [Mem.write, Function.update_apply, eq_comm]

/-! ### Fields of a view, for buffers without writes to the field -/

lemma view_lock_of {m : Mem h} {b : List (W h)} (hb : ∀ w ∈ b, w.isLock = false) :
    (m.view b).lock = m.lock := by
  induction b generalizing m with
  | nil => rfl
  | cons w b ih =>
    simp only [Mem.view_cons]
    rw [ih (fun w' hw' => hb w' (by simp [hw']))]
    have := hb w (by simp); cases w <;> simp_all [W.isLock]

lemma view_promQ_of {m : Mem h} {b : List (W h)} (hb : ∀ w ∈ b, w.isPromQ = false) :
    (m.view b).promQ = m.promQ := by
  induction b generalizing m with
  | nil => rfl
  | cons w b ih =>
    simp only [Mem.view_cons]
    rw [ih (fun w' hw' => hb w' (by simp [hw']))]
    have := hb w (by simp); cases w <;> simp_all [W.isPromQ]

lemma view_exits_of {m : Mem h} {b : List (W h)} (hb : ∀ w ∈ b, w.isExits = false) :
    (m.view b).exits = m.exits := by
  induction b generalizing m with
  | nil => rfl
  | cons w b ih =>
    simp only [Mem.view_cons]
    rw [ih (fun w' hw' => hb w' (by simp [hw']))]
    have := hb w (by simp); cases w <;> simp_all [W.isExits]

lemma view_inPromQ_of {m : Mem h} {b : List (W h)} {q : Proc h}
    (hb : ∀ w ∈ b, w.isInPromQ q = false) : (m.view b).inPromQ q = m.inPromQ q := by
  induction b generalizing m with
  | nil => rfl
  | cons w b ih =>
    simp only [Mem.view_cons]
    rw [ih (fun w' hw' => hb w' (by simp [hw']))]
    have := hb w (by simp); cases w <;> simp_all [W.isInPromQ, write_inPromQ]

lemma view_apply_of {m : Mem h} {b : List (W h)} {q : Proc h}
    (hb : ∀ w ∈ b, w.isApply q = false) : (m.view b).apply q = m.apply q := by
  induction b generalizing m with
  | nil => rfl
  | cons w b ih =>
    simp only [Mem.view_cons]
    rw [ih (fun w' hw' => hb w' (by simp [hw']))]
    have := hb w (by simp); cases w <;> simp_all [W.isApply, write_apply]

lemma view_signal_of {m : Mem h} {b : List (W h)} {q : Proc h}
    (hb : ∀ w ∈ b, w.isSignal q = false) : (m.view b).signal q = m.signal q := by
  induction b generalizing m with
  | nil => rfl
  | cons w b ih =>
    simp only [Mem.view_cons]
    rw [ih (fun w' hw' => hb w' (by simp [hw']))]
    have := hb w (by simp); cases w <;> simp_all [W.isSignal, write_signal]

lemma view_node_of {m : Mem h} {b : List (W h)} {i : ℕ}
    (hb : ∀ w ∈ b, w.isNode i = false) : (m.view b).node i = m.node i := by
  induction b generalizing m with
  | nil => rfl
  | cons w b ih =>
    simp only [Mem.view_cons]
    rw [ih (fun w' hw' => hb w' (by simp [hw']))]
    have := hb w (by simp); cases w <;> simp_all [W.isNode, write_node]

/-! ### Effects of the configuration operations -/

section ops
variable (s : Cfg h) (p q : Proc h) (c : PC h) (w : W h)

@[simp] lemma goto_mem : (s.goto p c).mem = s.mem := rfl
@[simp] lemma goto_buf : (s.goto p c).buf = s.buf := rfl
@[simp] lemma goto_ent : (s.goto p c).ent = s.ent := rfl
@[simp] lemma goto_pc : (s.goto p c).pc = Function.update s.pc p c := rfl
@[simp] lemma issue_mem : (s.issue p w c).mem = s.mem := rfl
@[simp] lemma issue_buf : (s.issue p w c).buf = Function.update s.buf p (s.buf p ++ [w]) := rfl
@[simp] lemma issue_ent : (s.issue p w c).ent = s.ent := rfl
@[simp] lemma issue_pc : (s.issue p w c).pc = Function.update s.pc p c := rfl

lemma flush_of_cons {w : W h} {b : List (W h)} (hb : s.buf p = w :: b) :
    s.flush p = { s with mem := s.mem.write w, buf := Function.update s.buf p b } := by
  simp [Cfg.flush, hb]

lemma flush_of_nil (hb : s.buf p = []) : s.flush p = s := by simp [Cfg.flush, hb]

@[simp] lemma flush_pc : (s.flush p).pc = s.pc := by
  unfold Cfg.flush; split <;> rfl
@[simp] lemma flush_ent : (s.flush p).ent = s.ent := by
  unfold Cfg.flush; split <;> rfl

lemma barrier_pc : (s.barrier p c).pc = if s.buf p = [] then Function.update s.pc p c else s.pc := by
  unfold Cfg.barrier; split <;> simp
@[simp] lemma barrier_ent : (s.barrier p c).ent = s.ent := by
  unfold Cfg.barrier; split <;> simp

/-- A flush does not change any view. -/
lemma view_flush (r : Proc h) : (s.flush p).view r = if r = p then s.view r else
    (match s.buf p with | [] => s.mem | w :: _ => s.mem.write w).view (s.buf r) := by
  unfold Cfg.flush Cfg.view
  split <;> rename_i hb
  · simp [hb]
  · by_cases hr : r = p
    · subst hr; simp [hb]
    · simp [hr, hb]

end ops

lemma Cfg.view_self_flush (s : Cfg h) (p : Proc h) : (s.flush p).view p = s.view p := by
  rw [view_flush]; simp

end Podc.ConstantBarriersMutex
