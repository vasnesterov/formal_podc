import Papers.PODC2018.NestingSafeRecoverable.Alg2Lemmas

/-!
# Algorithm 2 of [ABH18]: one-step lemmas

The effect of each step of Algorithm 2 on a configuration, and the frame lemma `Inv.of_local`
for steps that do not change the shared memory.
-/

namespace Podc.NestingSafeRecoverable.Alg2

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] [Fintype P]

@[simp] lemma T_C_read (x : Cnt P V) :
    ((alg2 P V).T Obj.C).δ x CASOp.read = (x, .inl x) := rfl

@[simp] lemma T_C_cas (x c n : Cnt P V) :
    ((alg2 P V).T Obj.C).δ x (CASOp.cas c n) = if x = c then (n, .inr true) else (x, .inr false) :=
  rfl

@[simp] lemma T_R_read (q j : P) (x : Option V) :
    ((alg2 P V).T (Obj.R q j)).δ x RWOp.read = (x, x) := rfl

@[simp] lemma T_R_write (q j : P) (x w : Option V) :
    ((alg2 P V).T (Obj.R q j)).δ x (RWOp.write w) = (w, w) := rfl

/-- `Function.update` on the memory, with the (classical) decidability instance of the model. -/
lemma upd_ne {f : (i : (alg2 P V).ι) → ((alg2 P V).T i).State} {a a' : (alg2 P V).ι}
    (h : a ≠ a') (v : ((alg2 P V).T a').State) :
    @Function.update _ _ (fun _ _ => Classical.propDecidable _) f a' v a = f a :=
  @Function.update_of_ne _ _ (fun _ _ => Classical.propDecidable _) _ _ h v f

lemma upd_self {f : (i : (alg2 P V).ι) → ((alg2 P V).T i).State} (a : (alg2 P V).ι)
    (v : ((alg2 P V).T a).State) :
    @Function.update _ _ (fun _ _ => Classical.propDecidable _) f a v a = v :=
  @Function.update_self _ _ (fun _ _ => Classical.propDecidable _) a v f

section Events

variable {C : (alg2 P V).Cfg} {p : P} {old : Option V} {new : V}

lemma ev_c2 {v} (h : C.st p = some (.cas old new, .c2, v)) :
    C.ev (.step p) =
      { C with st := Function.update C.st p (some (.cas old new, .c3, .inl (memC C))) } := by
  rw [Alg.ev_step_access C h (i := Obj.C) (op := CASOp.read) (pc' := Loc.c3) (k := id) rfl]
  simp only [Alg.Cfg.mk.injEq, and_true]
  constructor <;> simp [alg2]
  exact @Function.update_eq_self _ _ (fun _ _ => Classical.propDecidable _) _ _

lemma ev_c3_ret {c : Cnt P V} (h : C.st p = some (.cas old new, .c3, .inl c)) (hc : c.2 ≠ old) :
    C.ev (.step p) =
      { C with st := Function.update C.st p none, hist := C.hist ++ [.res p (.inl false)] } := by
  obtain ⟨id, val⟩ := c
  exact Alg.ev_step_ret C h (by simp [alg2, act, hc])

open Classical in
lemma ev_c3_write {k : P} {val : Option V} (h : C.st p = some (.cas old new, .c3, .inl (some k, val)))
    (hc : val = old) :
    C.ev (.step p) =
      { C with mem := Function.update C.mem (.R k p) val,
               st := Function.update C.st p (some (.cas old new, .c7, .inl (some k, val))) } := by
  subst hc
  rw [Alg.ev_step_access C h (i := Obj.R k p) (op := RWOp.write val) (pc' := Loc.c7)
    (k := fun _ => .inl (some k, val)) (by simp [alg2, act])]
  rfl

lemma ev_c3_none {val : Option V} (h : C.st p = some (.cas old new, .c3, .inl (none, val)))
    (hc : val = old) :
    C.ev (.step p) =
      { C with st := Function.update C.st p (some (.cas old new, .c7, .inl (none, val))) } := by
  subst hc
  exact Alg.ev_step_internal C h (by simp [alg2, act])

open Classical in
lemma ev_c7_succ {c : Cnt P V} (h : C.st p = some (.cas old new, .c7, .inl c)) (hc : memC C = c) :
    C.ev (.step p) =
      { C with mem := Function.update C.mem .C (some p, some new),
               st := Function.update C.st p (some (.cas old new, .c8, .inr true)) } := by
  rw [Alg.ev_step_access C h (i := Obj.C) (op := CASOp.cas c (some p, some new)) (pc' := Loc.c8)
    (k := id) rfl]
  simp only [memC] at hc
  simp only [Alg.Cfg.mk.injEq, and_true]
  subst hc
  constructor <;> simp [alg2]

/-- The effect of the write of line 6, in terms of `memC`/`memR`. -/
lemma ev_c3_write_spec {k : P} {val : Option V}
    (h : C.st p = some (.cas old new, .c3, .inl (some k, val))) (hc : val = old) :
    memC (C.ev (.step p)) = memC C ∧
      (∀ a b, memR (C.ev (.step p)) a b = if a = k ∧ b = p then val else memR C a b) ∧
      (C.ev (.step p)).st = Function.update C.st p (some (.cas old new, .c7, .inl (some k, val))) ∧
      (C.ev (.step p)).hist = C.hist := by
  rw [ev_c3_write h hc]
  refine ⟨upd_ne (by intro h; cases h) _, fun a b => ?_, rfl, rfl⟩
  by_cases hab : a = k ∧ b = p
  · obtain ⟨rfl, rfl⟩ := hab
    rw [ite_eq_left ⟨rfl, rfl⟩]; exact upd_self _ _
  · rw [ite_eq_right hab]
    exact upd_ne (fun h => hab (by injection h with h1 h2; exact ⟨h1, h2⟩)) _

/-- The effect of a successful `cas` of line 7, in terms of `memC`/`memR`. -/
lemma ev_c7_succ_spec {c : Cnt P V} (h : C.st p = some (.cas old new, .c7, .inl c))
    (hc : memC C = c) :
    memC (C.ev (.step p)) = (some p, some new) ∧ memR (C.ev (.step p)) = memR C ∧
      (C.ev (.step p)).st = Function.update C.st p (some (.cas old new, .c8, .inr true)) ∧
      (C.ev (.step p)).hist = C.hist := by
  rw [ev_c7_succ h hc]
  refine ⟨upd_self _ _, ?_, rfl, rfl⟩
  funext a b
  exact upd_ne (by intro h; cases h) _

lemma ev_c7_fail {c : Cnt P V} (h : C.st p = some (.cas old new, .c7, .inl c)) (hc : memC C ≠ c) :
    C.ev (.step p) =
      { C with st := Function.update C.st p (some (.cas old new, .c8, .inr false)) } := by
  rw [Alg.ev_step_access C h (i := Obj.C) (op := CASOp.cas c (some p, some new)) (pc' := Loc.c8)
    (k := id) rfl]
  simp only [memC] at hc
  simp only [Alg.Cfg.mk.injEq, and_true]
  constructor <;> simp [alg2, hc]
  exact @Function.update_eq_self _ _ (fun _ _ => Classical.propDecidable _) _ _

lemma ev_c8 {b : Bool} (h : C.st p = some (.cas old new, .c8, .inr b)) :
    C.ev (.step p) =
      { C with st := Function.update C.st p none, hist := C.hist ++ [.res p (.inl b)] } :=
  Alg.ev_step_ret C h rfl

lemma ev_r13 {v} (h : C.st p = some (.cas old new, .r13, v)) :
    C.ev (.step p) =
      { C with st := Function.update C.st p (some (.cas old new, .r14, .inl (memC C))) } := by
  rw [Alg.ev_step_access C h (i := Obj.C) (op := CASOp.read) (pc' := Loc.r14) (k := id) rfl]
  simp only [Alg.Cfg.mk.injEq, and_true]
  constructor <;> simp [alg2]
  exact @Function.update_eq_self _ _ (fun _ _ => Classical.propDecidable _) _ _

lemma ev_r14_ret (h : C.st p = some (.cas old new, .r14, .inl (some p, some new))) :
    C.ev (.step p) =
      { C with st := Function.update C.st p none, hist := C.hist ++ [.res p (.inl true)] } :=
  Alg.ev_step_ret C h (by simp [alg2, act])

lemma ev_r14_go {v} (h : C.st p = some (.cas old new, .r14, v))
    (hv : v ≠ .inl (some p, some new)) :
    C.ev (.step p) = { C with st := Function.update C.st p (some (.cas old new, .rR 0, v)) } :=
  Alg.ev_step_internal C h (by simp only [alg2, act]; exact ite_eq_right hv)

lemma ev_rR_read {i : ℕ} {v} (h : C.st p = some (.cas old new, .rR i, v))
    (hi : i < (procs P).length) :
    C.ev (.step p) =
      { C with
        st := Function.update C.st p (some (.cas old new, .rT i, .inl (none, memR C p (procs P)[i])))
      } := by
  rw [Alg.ev_step_access C h (i := Obj.R p (procs P)[i]) (op := RWOp.read) (pc' := Loc.rT i)
    (k := fun r => .inl (none, r)) (by simp [alg2, act, hi])]
  simp only [Alg.Cfg.mk.injEq, and_true]
  constructor <;> simp [alg2]
  exact @Function.update_eq_self _ _ (fun _ _ => Classical.propDecidable _) _ _

lemma ev_rR_end {i : ℕ} {v} (h : C.st p = some (.cas old new, .rR i, v))
    (hi : ¬ i < (procs P).length) :
    C.ev (.step p) = { C with st := Function.update C.st p (some (.cas old new, .c2, v)) } :=
  Alg.ev_step_internal C h (by simp [alg2, act, hi])

lemma ev_rT_ret {i : ℕ} (h : C.st p = some (.cas old new, .rT i, .inl (none, some new))) :
    C.ev (.step p) =
      { C with st := Function.update C.st p none, hist := C.hist ++ [.res p (.inl true)] } :=
  Alg.ev_step_ret C h (by simp [alg2, act])

lemma ev_rT_go {i : ℕ} {v} (h : C.st p = some (.cas old new, .rT i, v))
    (hv : v ≠ .inl (none, some new)) :
    C.ev (.step p) =
      { C with st := Function.update C.st p (some (.cas old new, .rR (i + 1), v)) } :=
  Alg.ev_step_internal C h (by simp only [alg2, act]; exact ite_eq_right hv)

lemma ev_rd10 {v} (h : C.st p = some (.read, .rd10, v)) :
    C.ev (.step p) =
      { C with st := Function.update C.st p (some (.read, .rd11, .inl (memC C))) } := by
  rw [Alg.ev_step_access C h (i := Obj.C) (op := CASOp.read) (pc' := Loc.rd11) (k := id) rfl]
  simp only [Alg.Cfg.mk.injEq, and_true]
  constructor <;> simp [alg2]
  exact @Function.update_eq_self _ _ (fun _ _ => Classical.propDecidable _) _ _

lemma ev_rd11 {c : Cnt P V} (h : C.st p = some (.read, .rd11, .inl c)) :
    C.ev (.step p) =
      { C with st := Function.update C.st p none, hist := C.hist ++ [.res p (.inr c.2)] } := by
  obtain ⟨id, val⟩ := c
  exact Alg.ev_step_ret C h rfl

end Events

end Podc.NestingSafeRecoverable.Alg2
