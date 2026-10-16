import Papers.PODC2013.ByzantineVectorConsensus.LowerBounds
import Papers.PODC2013.ByzantineVectorConsensus.ExactAlgorithm
import Papers.PODC2013.ByzantineVectorConsensus.Iterative
import Papers.PODC2013.ByzantineVectorConsensus.RestrictedSync
import Papers.PODC2013.ByzantineVectorConsensus.Tverberg

/-!
# Byzantine Vector Consensus in Complete Graphs (Vaidya–Garg, PODC 2013): main results

* `exactBVC_sync_iff` — Theorems 1 and 3: for `n ≥ 2` processes and `d ≥ 1`, exact BVC is
  solvable in synchrony iff `n ≥ max(3t + 1, (d + 1) t + 1)`.
* `theorem_4` (`LowerBounds.lean`) — approximate BVC in the partially synchronous / asynchronous
  model needs `n ≥ (d + 2) t + 1`.
* `theorem_5` (`Iterative.lean`) — the Section 3.2 algorithm achieves approximate BVC for
  `n ≥ (d + 2) f + 1` on top of round exchanges with Properties 1–3 of AAD.
* `theorem_6_sync`, `theorem_6_async`, `theorem_6_sync_restricted` — sufficiency in Theorem 6;
  `theorem_6_sync_necessity_false` — the synchronous necessity claim of Theorem 6 fails as stated.
* `GammaOn_nonempty` (Helly) and `GammaOn_nonempty_of_tverberg` (Tverberg, `tverberg`) — Lemma 1;
  `gamma_empty_of_card_eq` — its tightness.

Sanity checks (this file): the trivial algorithm "decide your own input" solves exact BVC when
`n = 1` (so `n ≥ 2` is needed in Theorem 1), and solves approximate BVC for any `n` and `t` when
the input domain has width `≤ ε` (so `c > ε` is needed in Theorem 4); in particular the
specifications are satisfiable.
-/

open Cslib.Byzantine.PartialSync Finset

namespace ByzantineVectorConsensus

set_option linter.unusedSectionVars false

/-- **Theorems 1 and 3**: for `n ≥ 2` processes and dimension `d ≥ 1`, exact Byzantine vector
consensus is solvable in a synchronous system with at most `t` Byzantine processes iff
`n ≥ max(3t + 1, (d + 1) t + 1)`. -/
theorem exactBVC_sync_iff {P : Type} [Fintype P] [DecidableEq P] {d t δ : ℕ} (hd : 1 ≤ d)
    (hn : 2 ≤ Fintype.card P) :
    (bvcValidity P d).SolvableSync t δ ↔ 3 * t < Fintype.card P ∧ (d + 1) * t < Fintype.card P :=
  ⟨fun ⟨_, _, _, hA⟩ => theorem_1 hd hn hA, fun h => theorem_3 h.1 h.2⟩

variable {P : Type*} [Fintype P] [DecidableEq P] {d : ℕ}

/-- The trivial algorithm: decide the own input immediately. -/
def ownInput (P : Type*) (d : ℕ) : Algorithm P Unit (Vec d) (Vec d) (Vec d) where
  init _ v := v
  step _ s _ := s
  send _ _ _ := []
  decide _ s := some s

theorem ownInput_decides {R : Run P Unit (Vec d)} {p : P} {v : Vec d} :
    R.Decides (ownInput P d) p v ↔ v = R.inp p := by
  have hst : ∀ τ, R.st (ownInput P d) τ p = R.inp p := by
    intro τ
    induction τ with
    | zero => rfl
    | succ τ ih => rw [Run.st_succ]; exact ih
  simp only [Run.Decides]
  refine ⟨fun ⟨τ, h⟩ => ?_, fun h => ⟨0, ?_⟩⟩
  · have : (ownInput P d).decide p (R.st (ownInput P d) τ p) = some (R.inp p) := by
      rw [hst]; rfl
    rw [this, Option.some.injEq] at h
    exact h.symm
  · rw [hst, h]; rfl

theorem ownInput_valid {R : Run P Unit (Vec d)} {p : P} (hp : p ∉ R.faulty) :
    R.inp p ∈ bvcValidity P d R.inputConf :=
  subset_convexHull ℝ _ ⟨p, by simp [Run.inputConf, hp]⟩

/-- With a single process, exact BVC is trivially solvable for every `t` (the hypothesis
`n ≥ 2` of Theorem 1 cannot be dropped). -/
theorem ownInput_solves_of_card_one (h1 : Fintype.card P = 1) (t δ : ℕ) :
    SolvesConsensusSync t δ (ownInput P d) (bvcValidity P d) := by
  refine ⟨fun R _ _ _ p _ => ⟨_, ownInput_decides.2 rfl⟩,
    fun R _ _ _ p _ q _ v w hv hw => ?_, fun R _ _ _ p hp v hv => ?_⟩
  · obtain rfl : p = q := Fintype.card_le_one_iff.1 h1.le p q
    rw [ownInput_decides.1 hv, ownInput_decides.1 hw]
  · rw [ownInput_decides.1 hv]; exact ownInput_valid hp

/-- If all admissible inputs lie in a box of width `≤ ε`, deciding the own input solves
approximate BVC for every `n` and `t` (the hypothesis `c > ε` of Theorem 4 cannot be dropped). -/
theorem ownInput_solves_of_narrow {ν U ε : ℝ} (hUν : U - ν ≤ ε) (t δ : ℕ) :
    SolvesApproxBVC t δ ε {v : Vec d | ∀ l, ν ≤ v l ∧ v l ≤ U} (ownInput P d) := by
  refine ⟨fun R _ _ p _ => ⟨_, ownInput_decides.2 rfl⟩,
    fun R _ hK p hp q hq v w hv hw l => ?_, fun R _ _ p hp v hv => ?_⟩
  · rw [ownInput_decides.1 hv, ownInput_decides.1 hw]
    have h1 := hK p hp l
    have h2 := hK q hq l
    rw [abs_le]; constructor <;> linarith
  · rw [ownInput_decides.1 hv]; exact ownInput_valid hp

/-- The example of the introduction: coordinate-wise scalar validity does not imply vector
validity. With inputs `(2/3, 1/6, 1/6)`, `(1/6, 2/3, 1/6)`, `(1/6, 1/6, 2/3)` at the correct
processes, the vector `(1/6, 1/6, 1/6)` is coordinate-wise in the range of the inputs but not in
their convex hull (its coordinates do not sum to `1`). -/
theorem intro_example :
    let x : Fin 3 → Vec 3 := ![![2/3, 1/6, 1/6], ![1/6, 2/3, 1/6], ![1/6, 1/6, 2/3]]
    let z : Vec 3 := ![1/6, 1/6, 1/6]
    (∀ l, ∃ i j, x i l ≤ z l ∧ z l ≤ x j l) ∧ z ∉ convexHull ℝ (Set.range x) := by
  intro x z
  refine ⟨fun l => ?_, fun hz => ?_⟩
  · fin_cases l
    · exact ⟨1, 0, by norm_num [x, z]⟩
    · exact ⟨0, 1, by norm_num [x, z]⟩
    · exact ⟨0, 2, by norm_num [x, z]⟩
  · have hconv : Convex ℝ {w : Vec 3 | ∑ j, w j = 1} :=
      convex_hyperplane (f := fun w : Vec 3 => ∑ j, w j)
        ⟨fun _ _ => by simp [Finset.sum_add_distrib], fun _ _ => by simp [Finset.mul_sum]⟩ 1
    have hsub : Set.range x ⊆ {w : Vec 3 | ∑ j, w j = 1} := by
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [x, Fin.sum_univ_three] <;> norm_num
    have := convexHull_min hsub hconv hz
    simp [z, Fin.sum_univ_three] at this
    norm_num at this

end ByzantineVectorConsensus
