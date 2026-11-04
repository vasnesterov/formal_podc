import Papers.PODC2010.AsymmetricProgress.Theorems

/-!
# Degenerate case `n = 1` and tightness of the port bound

* `ownInput` — with a single process, "decide your own input" (no shared objects at all) is a
  wait-free consensus algorithm (`ownInput_live`). Hence Theorems 1 and 4 and Lemmas 3–9 of the
  paper are false for `n = 1` (`theorem1_false_one_process`, `lemma3_false_one_process`); our
  versions assume `2 ≤ n`.
* `atomicCons_live` — the hypothesis "at most `n − 1` ports" of Theorem 1 cannot be dropped: one
  `n`-port atomic consensus object (`advCons Finset.univ`, which answers everybody at once) gives
  a wait-free, hence `(n, X)`-live for every `X`, consensus algorithm. It also shows that the
  correctness notion `Live` is satisfiable.
-/

namespace Podc.AsymmetricProgress

set_option linter.unusedSectionVars false

/-- No shared objects. -/
abbrev noObj : Empty → BObj 1 := Empty.elim

/-- One process that decides its own input without accessing shared memory. -/
def ownInput : Alg 1 noObj where
  L := Bool
  init _ v := v
  act v := .out v
  mem₀ i := i.elim

lemma ownInput_out (C : Cfg ownInput) (p : Fin 1) : C.Out p (C.loc p) := rfl

lemma ownInput_run (C : Cfg ownInput) (σ : List (Fin 1)) : run C σ = C := by
  induction σ generalizing C with
  | nil => rfl
  | cons p σ ih => rw [run_cons, step_of_out (ownInput_out C p), ih]

/-- With one process, deciding the own input is a wait-free consensus algorithm. -/
theorem ownInput_live : Live ownInput Set.univ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro x σ p q v w hv hw
    have hpq : p = q := Subsingleton.elim p q
    subst hpq
    exact hv.unique hw
  · intro x σ p v hv
    refine ⟨p, ?_⟩
    rw [ownInput_run] at hv
    exact (hv.unique (ownInput_out _ p)).symm
  · intro p C _
    exact ⟨0, C.loc p, ownInput_out _ p⟩
  · intro p _ x e _
    exact ⟨0, _, ownInput_out _ p⟩

/-- Theorem 1 (and Theorem 4) fail for `n = 1`: an `(1,1)`-live consensus algorithm exists
using no objects at all (so all hypotheses on objects and ports hold vacuously). -/
theorem theorem1_false_one_process :
    ∃ (A : Alg 1 noObj) (Y : Empty → Set (Fin 1)),
      (∀ i, (noObj i).RWLike ∨ (Y i).ncard ≤ 1 - 1) ∧ RespectsPorts A Y ∧ Live A Set.univ :=
  ⟨ownInput, Empty.elim, fun i => i.elim, fun _ _ _ i => i.elim, ownInput_live⟩

/-- Lemma 3 fails for `n = 1`: no initial configuration of `ownInput` is bivalent. -/
theorem lemma3_false_one_process (x : Fin 1 → Bool) : ¬ Biv (initCfg ownInput x) := by
  rintro ⟨⟨σ, p, hp⟩, ⟨σ', q, hq⟩⟩
  rw [ownInput_run] at hp hq
  have hpq : p = q := Subsingleton.elim p q
  subst hpq
  have := hp.unique hq
  simp at this

/-- One `n`-port atomic consensus object (answering everybody at once) solves wait-free
consensus: the port bound `n − 1` in Theorem 1 is necessary, and `Live` is satisfiable. -/
theorem atomicCons_live (n : ℕ) : (advCons (Finset.univ : Finset (Fin n))).IsLive Set.univ := by
  have := advCons_isLive (Finset.univ : Finset (Fin n))
  simpa using this

end Podc.AsymmetricProgress
