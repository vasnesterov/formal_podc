import Papers.PODC2017.MemoryAnonymousCoordination.ConsensusCount

/-!
# Figure 2: the steps of the memory-anonymous execution

Inversion lemmas for the steps of `(alg n sel).unnamed π` (`tau_cases`, `ret_cases`,
`inv_cases`), forward solo-step lemmas, and the "virtual view" `mixed` of a process in the middle
of a collect (entries already read, then the current contents of the registers not yet read).
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Consensus

open Cslib.SharedMemory

variable {P V : Type} {m : ℕ} [DecidableEq V] [DecidableEq P] [Inhabited V]
  {n : ℕ} {sel : P → V → (Fin m → Option (P × V)) → Fin m} {π : P → Equiv.Perm (Fin m)}

/-- What a process in the middle of a collect (about to read local register `k`) would see if
the memory `M` did not change any more: entries read so far below `k`, current contents above. -/
def mixed (σ : Equiv.Perm (Fin m)) (k : Fin m) (view : Fin m → Option (P × V))
    (M : Fin m → Option (P × V)) (j : Fin m) : Option (P × V) :=
  if j < k then view j else M (σ j)

/-- Reading the next register does not change the virtual view. -/
lemma mixed_read (σ : Equiv.Perm (Fin m)) (k : Fin m) (view M : Fin m → Option (P × V))
    (h : k.val + 1 < m) :
    mixed σ ⟨k.val + 1, h⟩ (Function.update view k (M (σ k))) M = mixed σ k view M := by
  funext j
  simp only [mixed, Fin.lt_def, Function.update_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · have : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    by_cases hj : j.val < k.val
    · simp [hjk, hj, show j.val < k.val + 1 by omega]
    · simp [hj, show ¬ j.val < k.val + 1 by omega]

/-- After the last read, the view is the virtual view. -/
lemma mixed_last (σ : Equiv.Perm (Fin m)) (k : Fin m) (view M : Fin m → Option (P × V))
    (h : ¬ k.val + 1 < m) : Function.update view k (M (σ k)) = mixed σ k view M := by
  funext j
  simp only [mixed, Fin.lt_def, Function.update_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · have : j.val ≠ k.val := fun h => hjk (Fin.ext h)
    have : j.val < k.val := by have := j.isLt; omega
    simp [hjk, this]

lemma mixed_zero (σ : Equiv.Perm (Fin m)) (k : Fin m) (view M : Fin m → Option (P × V))
    (hk : k.val = 0) : mixed σ k view M = fun j => M (σ j) := by
  funext j; simp [mixed, Fin.lt_def, hk]

/-- A write to physical register `r` changes the virtual view at most at `σ⁻¹ r`, to the written
value. -/
lemma mixed_write (σ : Equiv.Perm (Fin m)) (k : Fin m) (view M : Fin m → Option (P × V))
    (r : Fin m) (e : Option (P × V)) (j : Fin m) :
    mixed σ k view (Function.update M r e) j = mixed σ k view M j ∨
      (mixed σ k view (Function.update M r e) j = e ∧ σ j = r) := by
  simp only [mixed, Function.update_apply]
  split_ifs <;> simp_all

variable (n sel π) in
/-- The algorithm under the numbering `π`. -/
noncomputable abbrev I : Impl (taskObj V V) (RegFamily (Fin m) (Option (P × V)) none) P
    (Loc P V m) := (alg n sel).unnamed π

lemma tau_cases {C C' : Cfg P V m} {p : P} (h : (I n sel π).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧
    ((∃ x k view, C.loc p = .collect x k view ∧ C'.mem = C.mem ∧
        C'.loc = Function.update C.loc p (afterRead n sel p x k view (C.mem (π p k)))) ∨
     (∃ x j b, C.loc p = .write x j b ∧
        C'.mem = Function.update C.mem (π p j) (some (p, x)) ∧
        C'.loc = Function.update C.loc p (afterWrite x b))) := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  refine ⟨hp, hpend, ?_⟩
  cases hl : C.loc p with
  | idle => simp [hl, Impl.unnamed, alg] at hact
  | done v => simp [hl, Impl.unnamed, alg] at hact
  | collect x k' view =>
    left
    simp only [hl, Impl.unnamed, alg, Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    subst ho; subst hk
    exact ⟨x, k', view, rfl, by rw [hmem]; simp, by rw [hloc]⟩
  | write x j b =>
    right
    simp only [hl, Impl.unnamed, alg, Action.access.injEq] at hact
    obtain ⟨rfl, ho, hk⟩ := hact
    subst ho; subst hk
    exact ⟨x, j, b, rfl, by rw [hmem], by rw [hloc]⟩

lemma ret_cases {C C' : Cfg P V m} {p : P} {r : V}
    (h : (I n sel π).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ (C.loc p = .done r ∨ C.loc p = .idle) ∧
    C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
    C'.loc = Function.update C.loc p .idle := by
  obtain ⟨hp, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  refine ⟨hp, ?_, hpend, hmem, ?_⟩
  · cases hl : C.loc p with
    | idle => exact Or.inr rfl
    | done v =>
      simp only [hl, Impl.unnamed, alg] at hact
      injection hact with h1 h2
      exact Or.inl (by rw [h1])
    | collect x k view => simp [hl, Impl.unnamed, alg] at hact
    | write x j b => simp [hl, Impl.unnamed, alg] at hact
  · rw [hloc]; congr 1
    cases hl : C.loc p with
    | idle => simp only [hl, Impl.unnamed, alg] at hact; injection hact with h1 h2; exact h2.symm
    | done v => simp only [hl, Impl.unnamed, alg] at hact; injection hact with h1 h2; exact h2.symm
    | collect x k view => simp [hl, Impl.unnamed, alg] at hact
    | write x j b => simp [hl, Impl.unnamed, alg] at hact

lemma inv_cases {C C' : Cfg P V m} {p : P} {o : V}
    (h : (I n sel π).step C (.inv p o) = some C') :
    C.pend p = none ∧ C'.pend = Function.update C.pend p (some o) ∧ C'.mem = C.mem ∧
    C'.loc = Function.update C.loc p (startCollect o) := by
  obtain ⟨hp, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  exact ⟨hp, hpend, hmem, hloc⟩

/-! ### Solo steps -/

lemma solo_collect {C : Cfg P V m} {p : P} (hp : C.pend p ≠ none) {x : V} {k : Fin m}
    {view : Fin m → Option (P × V)} (hl : C.loc p = .collect x k view) :
    (I n sel π).soloStep p C =
      { C with loc := Function.update C.loc p (afterRead n sel p x k view (C.mem (π p k))) } := by
  have hact : (I n sel π).act p (C.loc p) = .access (π p k) .read (afterRead n sel p x k view) := by
    rw [hl]; rfl
  have hnl : (I n sel π).nextLabel C p = .tau p := by simp [Impl.nextLabel, hact]
  simp only [Impl.soloStep, hp, ↓reduceIte, hnl, Impl.step_tau_eq_some hp hact]
  simp

lemma solo_write {C : Cfg P V m} {p : P} (hp : C.pend p ≠ none) {x : V} {j : Fin m} {b : Bool}
    (hl : C.loc p = .write x j b) :
    (I n sel π).soloStep p C =
      { C with mem := Function.update C.mem (π p j) (some (p, x)),
               loc := Function.update C.loc p (afterWrite x b) } := by
  have hact : (I n sel π).act p (C.loc p) =
      .access (π p j) (.write (some (p, x))) (fun _ => afterWrite x b) := by
    rw [hl]; rfl
  have hnl : (I n sel π).nextLabel C p = .tau p := by simp [Impl.nextLabel, hact]
  simp only [Impl.soloStep, hp, ↓reduceIte, hnl, Impl.step_tau_eq_some hp hact]
  simp

lemma solo_done {C : Cfg P V m} {p : P} (hp : C.pend p ≠ none) {v : V}
    (hl : C.loc p = .done v) : ((I n sel π).soloStep p C).pend p = none := by
  have hact : (I n sel π).act p (C.loc p) = .ret v .idle := by rw [hl]; rfl
  have hnl : (I n sel π).nextLabel C p = .ret p v := by simp [Impl.nextLabel, hact]
  simp only [Impl.soloStep, hp, ↓reduceIte, hnl, Impl.step_ret_eq_some hp hact]
  simp

end Podc.MemoryAnonymousCoordination.Consensus
