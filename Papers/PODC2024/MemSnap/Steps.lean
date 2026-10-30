import Papers.PODC2024.MemSnap.Augmented

/-!
# MemSnap: effects of single steps

Explicit descriptions of the steps of Algorithm 1 (`tau_*`, `inv_eq`, `ret_eq`), stated through
the accessors `Cfg.X`, `Cfg.A`, `Cfg.B` and the local states.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemSnap

open Cslib.SharedMemory

variable {W : ObjSpec} {K : Type} [DecidableEq K] {v₀ : K → W.State}
variable {P : Type} [DecidableEq P] {σ : P}

section Mem

variable (m : (o : Obj K) → (base W K v₀ o).State)

@[simp] lemma upd_X_X (v : ℕ) : (Function.update m Obj.X v : (o : Obj K) → (base W K v₀ o).State) .X = v :=
  Function.update_self _ _ _
@[simp] lemma upd_X_A (v : ℕ) (j : K) :
    (Function.update m Obj.X v : (o : Obj K) → (base W K v₀ o).State) (.A j) = m (.A j) :=
  Function.update_of_ne (by simp) _ _
@[simp] lemma upd_X_B (v : ℕ) (j : K) :
    (Function.update m Obj.X v : (o : Obj K) → (base W K v₀ o).State) (.B j) = m (.B j) :=
  Function.update_of_ne (by simp) _ _
@[simp] lemma upd_A_X (i : K) (v : W.State) :
    (Function.update m (Obj.A i) v : (o : Obj K) → (base W K v₀ o).State) .X = m .X :=
  Function.update_of_ne (by simp) _ _
@[simp] lemma upd_A_B (i : K) (v : W.State) (j : K) :
    (Function.update m (Obj.A i) v : (o : Obj K) → (base W K v₀ o).State) (.B j) = m (.B j) :=
  Function.update_of_ne (by simp) _ _
lemma upd_A_A (i : K) (v : W.State) (j : K) :
    (Function.update m (Obj.A i) v : (o : Obj K) → (base W K v₀ o).State) (.A j) =
      if j = i then v else m (.A j) := by
  by_cases h : j = i
  · subst h; simp
  · simp only [h, ↓reduceIte]; exact Function.update_of_ne (by simpa using h) _ _
@[simp] lemma upd_B_X (i : K) (v : W.State × ℕ) :
    (Function.update m (Obj.B i) v : (o : Obj K) → (base W K v₀ o).State) .X = m .X :=
  Function.update_of_ne (by simp) _ _
@[simp] lemma upd_B_A (i : K) (v : W.State × ℕ) (j : K) :
    (Function.update m (Obj.B i) v : (o : Obj K) → (base W K v₀ o).State) (.A j) = m (.A j) :=
  Function.update_of_ne (by simp) _ _
lemma upd_B_B (i : K) (v : W.State × ℕ) (j : K) :
    (Function.update m (Obj.B i) v : (o : Obj K) → (base W K v₀ o).State) (.B j) =
      if j = i then v else m (.B j) := by
  by_cases h : j = i
  · subst h; simp
  · simp only [h, ↓reduceIte]; exact Function.update_of_ne (by simpa using h) _ _

end Mem

/-- A step of process `π` accessing a base object, in explicit form. -/
lemma tau_eq {C C' : Cfg W K v₀ P} {π : P} (h : (memSnap W K v₀ σ).step C (.tau π) = some C')
    {i : Obj K} {o : (base W K v₀ i).Op} {k : (base W K v₀ i).Resp → Loc W K}
    (hact : act W K v₀ (C.loc π) = .access i o k) :
    C' = { C with mem := Function.update C.mem i ((base W K v₀ i).δ (C.mem i) o).1,
                  loc := Function.update C.loc π (k ((base W K v₀ i).δ (C.mem i) o).2) } := by
  have hp := (Impl.step_tau h).1
  rw [Impl.step_tau_eq_some (I := memSnap W K v₀ σ) hp hact] at h
  exact (Option.some.inj h).symm

variable {C C' : Cfg W K v₀ P} {π : P}

lemma tau_c1 (h : (memSnap W K v₀ σ).step C (.tau π) = some C') (hl : C.loc π = .c1) :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧ C'.loc = Function.update C.loc π (.c1w C.X) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  exact ⟨rfl, Function.update_eq_self _ _, rfl⟩

lemma tau_c1w (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {x : ℕ} (hl : C.loc π = .c1w x) :
    C'.pend = C.pend ∧ C'.X = x + 1 ∧ (∀ j, C'.A j = C.A j) ∧ (∀ j, C'.B j = C.B j) ∧
      C'.loc = Function.update C.loc π .c2 := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  refine ⟨rfl, ?_, fun j => ?_, fun j => ?_, rfl⟩ <;> simp [Cfg.X, Cfg.A, Cfg.B]

lemma tau_f9 (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K} {u : Option W.Op}
    {k : Bool} (hl : C.loc π = .f9 i u k) :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧ C'.loc = Function.update C.loc π (.f10 i u k (C.B i)) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  exact ⟨rfl, Function.update_eq_self _ _, rfl⟩

lemma tau_f10 (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K} {u : Option W.Op}
    {k : Bool} {b : W.State × ℕ} (hl : C.loc π = .f10 i u k b) :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧ C'.loc = Function.update C.loc π
      (if b.2 = C.X then fcont i u else .f11 i u k b C.X) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  exact ⟨rfl, Function.update_eq_self _ _, rfl⟩

lemma tau_f11 (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K} {u : Option W.Op}
    {k : Bool} {b : W.State × ℕ} {x : ℕ} (hl : C.loc π = .f11 i u k b x) :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc π (.f12 i u k b x (C.A i)) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  exact ⟨rfl, Function.update_eq_self _ _, rfl⟩

lemma tau_f12_succ (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K}
    {u : Option W.Op} {k : Bool} {b : W.State × ℕ} {x : ℕ} {a : W.State}
    (hl : C.loc π = .f12 i u k b x a) (hb : C.B i = b) :
    C'.pend = C.pend ∧ C'.X = C.X ∧ (∀ j, C'.A j = C.A j) ∧
      (∀ j, C'.B j = if j = i then (a, x) else C.B j) ∧
      C'.loc = Function.update C.loc π (fcont i u) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  have hb' : C.mem (.B i) = b := hb
  refine ⟨rfl, by simp [Cfg.X], fun j => by simp [Cfg.A], fun j => ?_, ?_⟩
  · simp only [Cfg.B, upd_B_B]
    split_ifs with hj
    · simp_all
    · rfl
  · simp [hb', casOk]

lemma tau_f12_fail (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K}
    {u : Option W.Op} {k : Bool} {b : W.State × ℕ} {x : ℕ} {a : W.State}
    (hl : C.loc π = .f12 i u k b x a) (hb : C.B i ≠ b) :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧
      C'.loc = Function.update C.loc π (if k then fcont i u else .f9 i u true) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  have hb' : C.mem (.B i) ≠ b := hb
  refine ⟨rfl, ?_, ?_⟩
  · simp only [hb', ite_false]; exact Function.update_eq_self _ _
  · simp [hb', casOk]

lemma tau_o4 (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K} (hl : C.loc π = .o4 i) :
    C'.pend = C.pend ∧ C'.mem = C.mem ∧ C'.loc = Function.update C.loc π (.o5 (C.B i).1) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  exact ⟨rfl, Function.update_eq_self _ _, rfl⟩

lemma tau_u7 (h : (memSnap W K v₀ σ).step C (.tau π) = some C') {i : K} {o : W.Op}
    (hl : C.loc π = .u7 i o) :
    C'.pend = C.pend ∧ C'.X = C.X ∧ (∀ j, C'.A j = if j = i then (W.δ (C.A i) o).1 else C.A j) ∧
      (∀ j, C'.B j = C.B j) ∧ C'.loc = Function.update C.loc π (.u8 (W.δ (C.A i) o).2) := by
  have := tau_eq h (by rw [hl]; rfl); subst this
  refine ⟨rfl, by simp [Cfg.X], fun j => ?_, fun j => by simp [Cfg.B], rfl⟩
  simp only [Cfg.A, upd_A_A]

/-- Processes at a return statement (or idle) take no internal step. -/
lemma tau_ret_none (h : (memSnap W K v₀ σ).step C (.tau π) = some C') :
    C.loc π ≠ .idle ∧ C.loc π ≠ .c2 ∧ (∀ v, C.loc π ≠ .o5 v) ∧ (∀ r, C.loc π ≠ .u8 r) := by
  have hst := (Impl.step_tau h).2.2
  obtain ⟨i, o, k, hact, -⟩ := hst
  refine ⟨fun hl => ?_, fun hl => ?_, fun v hl => ?_, fun r hl => ?_⟩ <;>
    · change act W K v₀ (C.loc π) = _ at hact
      rw [hl] at hact; simp [act] at hact

lemma inv_eq (h : (memSnap W K v₀ σ).step C (.inv π o) = some C') :
    C.pend π = none ∧ Allowed W K σ π o ∧ C'.mem = C.mem ∧
      C'.pend = Function.update C.pend π (some o) ∧
      C'.loc = Function.update C.loc π (invoke W K o) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Impl.step_inv h
  exact ⟨h1, h2, h5, h3, h4⟩

lemma ret_eq {r : CResp W} (h : (memSnap W K v₀ σ).step C (.ret π r) = some C') :
    C.pend π ≠ none ∧ C'.mem = C.mem ∧ C'.pend = Function.update C.pend π none ∧
      C'.loc = Function.update C.loc π .idle ∧
      (C.loc π = .idle ∨ (C.loc π = .c2 ∧ r = .ack) ∨ (∃ v, C.loc π = .o5 v ∧ r = .obs v) ∨
        (∃ r', C.loc π = .u8 r' ∧ r = .upd r')) := by
  obtain ⟨h1, h2, h3, l, hact, h4⟩ := Impl.step_ret h
  change act W K v₀ (C.loc π) = _ at hact
  cases hl : C.loc π <;> rw [hl] at hact <;> simp [act] at hact <;>
    obtain ⟨rfl, rfl⟩ := hact <;> simp_all

end Podc.MemSnap
