import Papers.PODC2019.RecoverableHierarchy.Defs

/-!
# Figure 2: from conventional consensus to recoverable consensus with `≤ f` failures

Golab, *Recoverable Consensus in Shared Memory* (PODC 2019; arXiv 1804.10597), Section 4,
Figure 2, and its analysis in Appendix B (Lemmas 12–15, Theorem 16 = Theorem 2).

Objects (`Idx n f = (Fin n ⊕ Fin (f+1)) ⊕ Fin (f+1)`, typed with CSLib's `withRW`: read/write
registers `Rr` and consensus objects):
* `R z` (`.inl (.inl z)`): read/write register over `ℕ`, initially `0` (the paper's `R[1..n]`);
* `D k` (`.inl (.inr k)`): read/write register over `Option Bool`, initially `⊥ = none`;
* `C k` (`.inr k`): an atomic consensus object `consObj Bool` (the paper's
  conventional wait-free consensus algorithm `C[k]`, accessed once per process by Lemma 12, so it
  behaves as an atomic one-shot consensus object; initial value `none`).

Local states `Loc n f` = the process id and a program counter `PC n f` encoding the pseudo-code
faithfully, one shared-memory access per step (each program counter denotes the point *before* an
access; local computations are folded into the continuations):
* `rd16 k v` — line 16 of iteration `k` (`v` is the current proposal): read `R[i]`; if it equals
  `k` go to line 17, otherwise to iteration `k+1`. For `k > f` the `for` loop is exhausted: the
  process reached the end of the pseudo-code without returning (footnote 4); we model this as a
  stuck state that keeps reading `R[i]` and never outputs.
* `wr17 k v` — line 17: `R[i] := k+1`.
* `scan k j v` — lines 18–21: for `j < k` read `D[j]` and adopt its value if not `⊥` (lines
  19–20); for `j = k` propose `v` to `C[k]` (line 21) and get `d`.
* `wr22 k d v` — line 22: `D[k] := d`; then, if `k < f`, the check of lines 23–26, otherwise
  line 28.
* `chk k d v reset y` — lines 24–26 at the process `y ≠ i`: read `R[y]`; if it exceeds
  `R[i] = k+1` set `reset` (the paper's `d := ⊥`, line 26). The loop runs over all `y ≠ i` in
  increasing order without breaking. **Tiny deviation**: the paper re-reads `R[i]` at line 25;
  we compare with `k+1`, the value of `R[i]` known locally (only `p_i` writes `R[i]`, and it
  wrote `k+1` at line 17).
* after the check: if not `reset`, `done d` (line 28: return `d`, an output state); otherwise
  line 16 of iteration `k+1` (with the current proposal `v`).

`init i x = ⟨i, rd16 0 x⟩`: after a crash a process restarts the procedure from line 15 with its
own input as proposal.
-/

namespace Podc.RecoverableHierarchy.Fig2

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

/-- Object indices: registers `R z` (`.inl (.inl z)`), `D k` (`.inl (.inr k)`) and consensus
objects `C k` (`.inr k`). -/
abbrev Idx (n f : ℕ) := (Fin n ⊕ Fin (f + 1)) ⊕ Fin (f + 1)

/-- The read/write registers: `R z : ℕ` (initially `0`) and `D k : Option Bool`
(initially `⊥`). -/
abbrev Rr (n f : ℕ) : Fin n ⊕ Fin (f + 1) → ObjSpec :=
  Sum.elim (fun _ => register ℕ 0) (fun _ => register (Option Bool) none)

/-- The objects: the registers `Rr` and the consensus objects `C k`. -/
abbrev Obj (n f : ℕ) : Idx n f → ObjSpec := withRW (Rr n f) (consObj Bool)

/-- Program counters of Figure 2 (see the module docstring). -/
inductive PC (n f : ℕ) where
  /-- Line 16 of iteration `k` with proposal `v` (stuck for `k > f`). -/
  | rd16 (k : ℕ) (v : Bool)
  /-- Line 17 of iteration `k`. -/
  | wr17 (k : Fin (f + 1)) (v : Bool)
  /-- Lines 18–21 of iteration `k`, at loop index `j`. -/
  | scan (k : Fin (f + 1)) (j : ℕ) (v : Bool)
  /-- Line 22 of iteration `k` with decision `d`. -/
  | wr22 (k : Fin (f + 1)) (d v : Bool)
  /-- Lines 24–26 of iteration `k` at process `y`. -/
  | chk (k : Fin (f + 1)) (d v reset : Bool) (y : Fin n)
  /-- Line 28: return `d`. -/
  | done (d : Bool)

/-- Local states: the process and its program counter. -/
structure Loc (n f : ℕ) where
  /-- The process. -/
  id : Fin n
  /-- Its program counter. -/
  pc : PC n f

variable {n f : ℕ}

/-- Skip the own index `i` in the loop of line 24. -/
def skip (i : Fin n) (y : ℕ) : ℕ := if y = i.val then y + 1 else y

/-- Continue the loop of line 24 at index `y` (skipping `i`); after the loop, lines 27–28. -/
def goChk (i : Fin n) (k : Fin (f + 1)) (d v reset : Bool) (y : ℕ) : PC n f :=
  if h : skip i y < n then .chk k d v reset ⟨skip i y, h⟩
  else if reset then .rd16 (k.val + 1) v else .done d

lemma goChk_cases (i : Fin n) (k : Fin (f + 1)) (d v r : Bool) (y : ℕ) :
    (∃ h : skip i y < n, goChk i k d v r y = .chk k d v r ⟨skip i y, h⟩) ∨
    (¬ skip i y < n ∧ r = true ∧ goChk i k d v r y = .rd16 (k.val + 1) v) ∨
    (¬ skip i y < n ∧ r = false ∧ goChk i k d v r y = .done d) := by
  unfold goChk
  by_cases h : skip i y < n
  · exact Or.inl ⟨h, by simp [h]⟩
  · cases r <;> simp [h]

/-- The next action of a local state. -/
def act : Loc n f → Act (Obj n f) (Loc n f)
  | ⟨i, .rd16 k v⟩ => .access (.inl (.inl i)) RWOp.read (fun (r : ℕ) => ⟨i,
      if h : k < f + 1 then (if r = k then .wr17 ⟨k, h⟩ v else .rd16 (k + 1) v)
      else .rd16 k v⟩)
  | ⟨i, .wr17 k v⟩ => .access (.inl (.inl i)) (RWOp.write (k.val + 1)) (fun _ => ⟨i, .scan k 0 v⟩)
  | ⟨i, .scan k j v⟩ =>
      if h : j < k.val then
        .access (.inl (.inr ⟨j, lt_trans h k.isLt⟩)) RWOp.read
          (fun (r : Option Bool) => ⟨i, .scan k (j + 1) (r.getD v)⟩)
      else .access (.inr k) (v : Bool) (fun d => ⟨i, .wr22 k d v⟩)
  | ⟨i, .wr22 k d v⟩ => .access (.inl (.inr k)) (RWOp.write (some d))
      (fun _ => ⟨i, if k.val < f then goChk i k d v false 0 else .done d⟩)
  | ⟨i, .chk k d v reset y⟩ => .access (.inl (.inl y)) RWOp.read
      (fun (r : ℕ) => ⟨i, goChk i k d v (reset || decide (k.val + 1 < r)) (y.val + 1)⟩)
  | ⟨_, .done d⟩ => .out d

/-- **The algorithm of Figure 2** for `n` processes and at most `f` failures. -/
abbrev A (n f : ℕ) : Alg n (Obj n f) where
  L := Loc n f
  init i x := ⟨i, .rd16 0 x⟩
  act := act
  mem₀ := fun j => (Obj n f j).init

/-! ## Views of a configuration -/

/-- The value of `R[z]`. -/
def R (C : Cfg (A n f)) (z : Fin n) : ℕ := C.mem (.inl (.inl z))

/-- The value of `D[k]`. -/
def D (C : Cfg (A n f)) (k : Fin (f + 1)) : Option Bool := C.mem (.inl (.inr k))

/-- The value (decision) of the consensus object `C[k]`. -/
def Cv (C : Cfg (A n f)) (k : Fin (f + 1)) : Option Bool := C.mem (.inr k)

/-- The program counter of process `z`. -/
def pcOf (C : Cfg (A n f)) (z : Fin n) : PC n f := (C.loc z).pc

@[simp] lemma act_eq : (A n f).act = act := rfl

/-! ## Views after a memory update -/

section Views

variable (inp : Fin n → Bool) (loc : Fin n → (A n f).L) (mem : (j : Idx n f) → (Obj n f j).State)

@[simp] lemma R_upd_R (i z : Fin n) (x : ℕ) :
    R (⟨inp, loc, Function.update mem (.inl (.inl i)) x⟩ : Cfg (A n f)) z =
      if z = i then x else mem (.inl (.inl z)) := by
  by_cases h : z = i
  · subst h; simp only [R]; exact Function.update_self _ _ _
  · simp only [R, h]
    exact Function.update_of_ne
      (show (Sum.inl (Sum.inl z) : Idx n f) ≠ .inl (.inl i) by simpa using h) _ _

@[simp] lemma R_upd_D (k : Fin (f + 1)) (z : Fin n) (x : Option Bool) :
    R (⟨inp, loc, Function.update mem (.inl (.inr k)) x⟩ : Cfg (A n f)) z = mem (.inl (.inl z)) :=
  Function.update_of_ne (show (Sum.inl (Sum.inl z) : Idx n f) ≠ .inl (.inr k) by simp) x mem

@[simp] lemma R_upd_C (k : Fin (f + 1)) (z : Fin n) (x : Option Bool) :
    R (⟨inp, loc, Function.update mem (.inr k) x⟩ : Cfg (A n f)) z = mem (.inl (.inl z)) :=
  Function.update_of_ne (show (Sum.inl (Sum.inl z) : Idx n f) ≠ .inr k by simp) x mem

@[simp] lemma D_upd_R (i : Fin n) (k : Fin (f + 1)) (x : ℕ) :
    D (⟨inp, loc, Function.update mem (.inl (.inl i)) x⟩ : Cfg (A n f)) k = mem (.inl (.inr k)) :=
  Function.update_of_ne (show (Sum.inl (Sum.inr k) : Idx n f) ≠ .inl (.inl i) by simp) x mem

@[simp] lemma D_upd_D (k k' : Fin (f + 1)) (x : Option Bool) :
    D (⟨inp, loc, Function.update mem (.inl (.inr k')) x⟩ : Cfg (A n f)) k =
      if k = k' then x else mem (.inl (.inr k)) := by
  by_cases h : k = k'
  · subst h; simp only [D]; exact Function.update_self _ _ _
  · simp only [D, h]
    exact Function.update_of_ne (show (Sum.inl (Sum.inr k) : Idx n f) ≠ .inl (.inr k') by
      simpa using h) _ _

@[simp] lemma D_upd_C (k k' : Fin (f + 1)) (x : Option Bool) :
    D (⟨inp, loc, Function.update mem (.inr k') x⟩ : Cfg (A n f)) k = mem (.inl (.inr k)) :=
  Function.update_of_ne (show (Sum.inl (Sum.inr k) : Idx n f) ≠ .inr k' by simp) x mem

@[simp] lemma Cv_upd_R (i : Fin n) (k : Fin (f + 1)) (x : ℕ) :
    Cv (⟨inp, loc, Function.update mem (.inl (.inl i)) x⟩ : Cfg (A n f)) k = mem (.inr k) :=
  Function.update_of_ne (show (Sum.inr k : Idx n f) ≠ .inl (.inl i) by simp) x mem

@[simp] lemma Cv_upd_D (k k' : Fin (f + 1)) (x : Option Bool) :
    Cv (⟨inp, loc, Function.update mem (.inl (.inr k')) x⟩ : Cfg (A n f)) k = mem (.inr k) :=
  Function.update_of_ne (show (Sum.inr k : Idx n f) ≠ .inl (.inr k') by simp) x mem

@[simp] lemma Cv_upd_C (k k' : Fin (f + 1)) (x : Option Bool) :
    Cv (⟨inp, loc, Function.update mem (.inr k') x⟩ : Cfg (A n f)) k =
      if k = k' then x else mem (.inr k) := by
  by_cases h : k = k'
  · subst h; simp only [Cv]; exact Function.update_self _ _ _
  · simp only [Cv, h]
    exact Function.update_of_ne (show (Sum.inr k : Idx n f) ≠ .inr k' by
      simpa using h) _ _

/-- The views depend only on the memory. -/
@[simp] lemma R_loc (C : Cfg (A n f)) : R (⟨C.inp, loc, C.mem⟩ : Cfg (A n f)) = R C := rfl
@[simp] lemma D_loc (C : Cfg (A n f)) : D (⟨C.inp, loc, C.mem⟩ : Cfg (A n f)) = D C := rfl
@[simp] lemma Cv_loc (C : Cfg (A n f)) : Cv (⟨C.inp, loc, C.mem⟩ : Cfg (A n f)) = Cv C := rfl

end Views

/-! ## The steps of Figure 2 -/

section Steps

variable {C : Cfg (A n f)} {p i : Fin n}

/-- Line 16: read `R[i]`. -/
lemma stepP_rd16 {k : ℕ} {v : Bool} (h : C.loc p = ⟨i, .rd16 k v⟩) :
    C.stepP p = ⟨C.inp, Function.update C.loc p ⟨i,
      if hk : k < f + 1 then (if R C i = k then .wr17 ⟨k, hk⟩ v else .rd16 (k + 1) v)
      else .rd16 k v⟩, C.mem⟩ := by
  rw [stepP_of_access C (show (A n f).act (C.loc p) = _ by rw [h]; rfl)]
  simp only [Cfg.mk.injEq, true_and]
  exact ⟨rfl, Function.update_eq_self _ _⟩

/-- Line 17: `R[i] := k+1`. -/
lemma stepP_wr17 {k : Fin (f + 1)} {v : Bool} (h : C.loc p = ⟨i, .wr17 k v⟩) :
    C.stepP p = ⟨C.inp, Function.update C.loc p ⟨i, .scan k 0 v⟩,
      Function.update C.mem (.inl (.inl i)) (k.val + 1)⟩ := by
  rw [stepP_of_access C (show (A n f).act (C.loc p) = _ by rw [h]; rfl)]
  rfl

/-- Lines 19–20: read `D[j]`, adopt its value if not `⊥`. -/
lemma stepP_scan_lt {k : Fin (f + 1)} {j : ℕ} {v : Bool} (h : C.loc p = ⟨i, .scan k j v⟩)
    (hj : j < k.val) :
    C.stepP p = ⟨C.inp, Function.update C.loc p
      ⟨i, .scan k (j + 1) ((D C ⟨j, lt_trans hj k.isLt⟩).getD v)⟩, C.mem⟩ := by
  rw [stepP_of_access C (show (A n f).act (C.loc p) = _ by rw [h]; simp [act, hj]; rfl)]
  simp only [Cfg.mk.injEq, true_and]
  exact ⟨rfl, Function.update_eq_self _ _⟩

/-- Line 21: propose `v` to `C[k]`. -/
lemma stepP_scan_ge {k : Fin (f + 1)} {j : ℕ} {v : Bool} (h : C.loc p = ⟨i, .scan k j v⟩)
    (hj : ¬ j < k.val) :
    C.stepP p = ⟨C.inp, Function.update C.loc p ⟨i, .wr22 k ((Cv C k).getD v) v⟩,
      Function.update C.mem (.inr k) (some ((Cv C k).getD v))⟩ := by
  rw [stepP_of_access C (show (A n f).act (C.loc p) = _ by rw [h]; simp [act, hj]; rfl)]
  rfl

/-- Line 22: `D[k] := d`. -/
lemma stepP_wr22 {k : Fin (f + 1)} {d v : Bool} (h : C.loc p = ⟨i, .wr22 k d v⟩) :
    C.stepP p = ⟨C.inp, Function.update C.loc p
        ⟨i, if k.val < f then goChk i k d v false 0 else .done d⟩,
      Function.update C.mem (.inl (.inr k)) (some d)⟩ := by
  rw [stepP_of_access C (show (A n f).act (C.loc p) = _ by rw [h]; rfl)]
  rfl

/-- Line 25: read `R[y]`. -/
lemma stepP_chk {k : Fin (f + 1)} {d v reset : Bool} {y : Fin n}
    (h : C.loc p = ⟨i, .chk k d v reset y⟩) :
    C.stepP p = ⟨C.inp, Function.update C.loc p
      ⟨i, goChk i k d v (reset || decide (k.val + 1 < R C y)) (y.val + 1)⟩, C.mem⟩ := by
  rw [stepP_of_access C (show (A n f).act (C.loc p) = _ by rw [h]; rfl)]
  simp only [Cfg.mk.injEq, true_and]
  exact ⟨rfl, Function.update_eq_self _ _⟩

/-- Output states do not step. -/
lemma stepP_done {d : Bool} (h : C.loc p = ⟨i, .done d⟩) : C.stepP p = C :=
  stepP_of_out C (v := d) (by show act _ = _; rw [h]; rfl)

end Steps

lemma out_iff {C : Cfg (A n f)} {p : Fin n} {v : Bool} :
    C.Out p v ↔ (C.loc p).pc = .done v := by
  unfold Cfg.Out
  rcases C.loc p with ⟨i, pc⟩
  show act _ = _ ↔ _
  cases pc with
  | scan k j w => simp only [act]; split <;> simp
  | done d =>
    simp only [act, PC.done.injEq]
    exact ⟨fun h => by cases h; rfl, fun h => by subst h; exact rfl⟩
  | _ => simp [act]

end Podc.RecoverableHierarchy.Fig2
