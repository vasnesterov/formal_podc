import Papers.PODC2010.BroadcastUnreliableRadio.StrongSelectBound

/-!
# Strong select: non-vacuity and the gap in the proof of Theorem 10

* `roundRobin_stronglySelective`, `theorem10_roundRobin`: the hypotheses of `theorem10` are
  satisfiable for every network (all families round robin, `f = n`), and executions exist
  (`trivialExecution`).
* `paper_T_claim_fails`: with the paper's definition of `T` (the least round with
  `den(1, T) < ρ`, where `den(1, T)` counts the nodes receiving the message for the first time in
  rounds `1, …, T`, so the source is not counted), the first claim of the proof of Theorem 10,
  "every node receives the message by the end of round `T`", is false: on the directed path
  `0 → 1 → 2` with `smax = 1`, `f = 1` and `F_1` a round robin not starting with the source,
  nobody receives anything in round 1, so `den(1, 1) = 0 < ρ`, i.e. `T = 1`, but node `2` does not
  have the message after round 1.
-/

namespace Podc.BroadcastUnreliableRadio.StrongSelect

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Round robin (any family containing all singletons) is strongly selective for every `k`. -/
lemma stronglySelective_of_singletons {F : ℕ → Finset V} {ℓ : ℕ}
    (h : ∀ v, ∃ j < ℓ, F j = {v}) (k : ℕ) : StronglySelective F ℓ k := by
  intro Z _ z hz
  obtain ⟨j, hj, hFj⟩ := h z
  exact ⟨j, hj, by rw [hFj]; exact inter_singleton_of_mem hz⟩

/-- Round robin over an enumeration `e` of the nodes, padded with empty sets. -/
def roundRobin (e : V ≃ Fin (Fintype.card V)) (j : ℕ) : Finset V :=
  if h : j < Fintype.card V then {e.symm ⟨j, h⟩} else ∅

/-- Round robin is `(n, k)`-strongly selective for every `k` once it has `ℓ ≥ n` sets. -/
lemma roundRobin_stronglySelective (e : V ≃ Fin (Fintype.card V)) {ℓ : ℕ}
    (hℓ : Fintype.card V ≤ ℓ) (k : ℕ) : StronglySelective (roundRobin e) ℓ k :=
  stronglySelective_of_singletons
    (fun v => ⟨e v, lt_of_lt_of_le (e v).isLt hℓ, by simp [roundRobin]⟩) k

/-- Parameters with all families round robin and `f = n`. -/
noncomputable def rrParams (V : Type*) [Fintype V] (smax : ℕ) : Params V :=
  ⟨smax, Fintype.card V, fun _ => roundRobin (Fintype.equivFin V)⟩

/-- An execution in which every node gets the message in round 1 (shows that `Execution N A`
is inhabited for all `N`, `A`). -/
def trivialExecution (N : DualGraph V) (A : Params V) : Execution N A where
  inf t := if t = 0 then {N.src} else univ
  init := by simp
  mono t := by
    split_ifs <;> simp_all
  progress r hr _ _ w _ := by simp [show r ≠ 0 by omega]

/-- Non-vacuity of `theorem10`: its hypotheses hold for round robin families with `f = n`, in
every network and for every `smax ≥ 1`. -/
theorem theorem10_hyps_rr (N : DualGraph V) {smax : ℕ} (hs : 1 ≤ smax) :
    1 ≤ (rrParams V smax).smax ∧ 1 ≤ (rrParams V smax).f ∧
    (∀ s, 1 ≤ s → s < (rrParams V smax).smax →
      StronglySelective ((rrParams V smax).F s) ((rrParams V smax).ℓ s) (2 ^ s)) ∧
    StronglySelective ((rrParams V smax).F (rrParams V smax).smax)
      ((rrParams V smax).ℓ (rrParams V smax).smax) (Fintype.card V) := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨N.src⟩
  have hℓ : ∀ s, Fintype.card V ≤ (rrParams V smax).ℓ s := fun s =>
    Nat.le_mul_of_pos_left _ (by positivity)
  exact ⟨hs, hn, fun s _ _ => roundRobin_stronglySelective _ (hℓ s) _,
    roundRobin_stronglySelective _ (hℓ _) _⟩

/-! ## The paper's definition of `T` -/

/-- The directed path `0 → 1 → 2` (with `G' = G`) with source `0`. -/
def pathNet : DualGraph (Fin 3) where
  E u v := v.val = u.val + 1
  E' u v := v.val = u.val + 1
  le _ _ h := h
  src := 0
  reachable v := by
    fin_cases v
    · exact .refl
    · exact .single rfl
    · exact .tail (.single (b := 1) rfl) rfl

/-- `smax = 1`, `f = 1`, and `F_1 = ({1}, {2}, {0}, {1})` (round robin not starting with the
source `0`); `F_1` is a `(3, 3)`-strongly selective family. -/
def cexParams : Params (Fin 3) := ⟨1, 1, fun _ j => {Fin.ofNat 3 (j + 1)}⟩

lemma cex_round1 : cexParams.fam 1 = 1 ∧ cexParams.iter 1 = 0 ∧ cexParams.idx 1 = 0 := by
  decide

/-- The execution in which the source sends nothing in round 1 (it is not in `F_1[1]`), and the
adversary informs everybody in round 2. -/
def cexExecution : Execution pathNet cexParams where
  inf t := if t ≤ 1 then {0} else univ
  init := rfl
  mono t := by
    split_ifs <;> simp_all
  progress r hr u hu w _ := by
    by_cases h1 : r = 1
    · subst h1
      obtain ⟨⟨hp, -⟩, hF⟩ := (hu u).2 rfl
      obtain ⟨hf, hi, hx⟩ := cex_round1
      rw [hf, hi] at hp
      rw [hf, hx] at hF
      simp [cexParams] at hp hF
      simp only [hp] at hF
      exact absurd hF (by decide)
    · simp [show ¬ r ≤ 1 by omega]

/-- **The first claim of the proof of Theorem 10 fails for the paper's `T`.** In this execution
(`n = 3`, `s_max = f = 1`: an illustration below the paper's parameter range; the same first
round occurs for every `n`, `s_max` whenever `F_1[1]` misses the source), no node receives the message for the
first time in round 1, so `den(1, 1) = 0 < ρ` and the paper's `T` is `1`; but node `2` does not
have the message at the end of round `T = 1`. (Our `T`, which counts the source, is `> 1/ρ`.) -/
theorem paper_T_claim_fails :
    StronglySelective (cexParams.F cexParams.smax) (cexParams.ℓ cexParams.smax) 3 ∧
    (cexExecution.inf 1 \ cexExecution.inf 0).card * cexParams.D < 1 ∧
    (2 : Fin 3) ∉ cexExecution.inf 1 := by
  refine ⟨stronglySelective_of_singletons (fun v => ?_) 3, by decide, by decide⟩
  fin_cases v
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩

end Podc.BroadcastUnreliableRadio.StrongSelect
