import Papers.PODC2013.ByzantineVectorConsensus.Spec

/-!
# Theorem 3: exact BVC in synchrony for `n ≥ max(3t + 1, (d + 1) t + 1)`

The paper's algorithm: (1) every process Byzantine-broadcasts its input, so that all correct
processes obtain the same multiset `S` of `n` vectors, containing the true input of every correct
process; (2) every process decides a deterministically chosen point of `Γ(S)`.

Step (1) is *interactive consistency* (IC), which CSLib provides for `n > 3t` in the synchronous
model (`icSolvableSync_of_three_t_lt`, Pease–Shostak–Lamport; implemented there by an exchange
round followed by vector consensus rather than by `n` parallel Byzantine broadcasts — the
specification is the same). `withGamma A` post-processes the decided vector `S` with `gammaPt`.
-/

open Cslib.Byzantine.PartialSync Finset Module

namespace ByzantineVectorConsensus

set_option linter.unusedSectionVars false

variable {P M S VI : Type*} [Fintype P] [DecidableEq P] {d t δ : ℕ}

/-- Step 2 of the exact BVC algorithm on top of an interactive-consistency algorithm `A`: decide
the chosen point `gammaPt t univ S` of `Γ(S)` when `A` decides the vector `S`. -/
noncomputable def withGamma (t : ℕ) (A : Algorithm P M S VI (P → Vec d)) :
    Algorithm P M S VI (Vec d) :=
  { A with decide := fun p s => (A.decide p s).map (gammaPt t univ) }

theorem withGamma_decides {A : Algorithm P M S VI (P → Vec d)} {R : Run P M VI} {p : P}
    {w : Vec d} : R.Decides (withGamma t A) p w ↔ ∃ V, R.Decides A p V ∧ gammaPt t univ V = w := by
  have hst : R.st (withGamma t A) = R.st A := R.st_congr (withGamma t A) rfl rfl rfl
  simp only [Run.Decides, hst]
  constructor
  · rintro ⟨τ, hτ⟩
    simp only [withGamma, Option.map_eq_some_iff] at hτ
    obtain ⟨V, hV, rfl⟩ := hτ
    exact ⟨V, ⟨τ, hV⟩, rfl⟩
  · rintro ⟨V, ⟨τ, hV⟩, rfl⟩
    exact ⟨τ, by simp only [withGamma, Option.map_eq_some_iff]; exact ⟨V, hV, rfl⟩⟩

/-- Correctness of the exact BVC algorithm (proof of **Theorem 3**): an interactive-consistency
algorithm followed by the choice of a point of `Γ` solves exact BVC in synchrony when
`n ≥ (d + 1) t + 1`. -/
theorem withGamma_solves {A : Algorithm P M S (Vec d) (P → Vec d)}
    (hA : SolvesConsensusSync t δ A (icValidity P (Vec d)))
    (hn : (d + 1) * t < Fintype.card P) :
    SolvesConsensusSync t δ (withGamma t A) (bvcValidity P d) := by
  refine ⟨fun R hR _ h0 p hp => ?_, fun R hR _ h0 p hp q hq v w hv hw => ?_,
    fun R hR _ h0 p hp w hw => ?_⟩
  · obtain ⟨V, hV⟩ := hA.termination R hR (R.authValid_none A) h0 p hp
    exact ⟨_, withGamma_decides.2 ⟨V, hV, rfl⟩⟩
  · obtain ⟨V, hV, rfl⟩ := withGamma_decides.1 hv
    obtain ⟨W, hW, rfl⟩ := withGamma_decides.1 hw
    rw [hA.agreement R hR (R.authValid_none A) h0 p hp q hq V W hV hW]
  · obtain ⟨V, hV, rfl⟩ := withGamma_decides.1 hw
    have hic := hA.validity R hR (R.authValid_none A) h0 p hp V hV
    -- the entries of correct processes are their inputs
    have hcorr : ∀ q ∉ R.faulty, V q = R.inp q := by
      intro q hq
      have := hic q (by simp [Run.inputConf, hq])
      simp only [Run.inputConf, hq, ite_false, Option.some.injEq] at this
      exact this.symm
    set T := univ.filter fun q => q ∉ R.faulty
    have hT : Fintype.card P - t ≤ T.card := by
      have h1 := card_filter_add_card_filter_not (s := (univ : Finset P)) (fun q => q ∈ R.faulty)
      have h2 : (univ.filter fun q => q ∈ R.faulty) = R.faulty := by ext; simp
      rw [h2, card_univ] at h1
      have := hR.card_faulty
      simp only [T]
      omega
    have hmem : gammaPt t univ V ∈ GammaOn t univ V :=
      gammaPt_mem V (by rw [finrank_fin_fun, card_univ]; exact hn)
    have := GammaOn_subset_convexHull (subset_univ T) (by rwa [card_univ]) hmem
    refine convexHull_mono ?_ this
    rintro _ ⟨q, hq, rfl⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, T] at hq
    exact ⟨q, by simp [Run.inputConf, hq, hcorr q hq]⟩

/-- **Theorem 3** of the paper: exact BVC is solvable in a synchronous system (without
signatures) if `n ≥ max(3t + 1, (d + 1) t + 1)`. -/
theorem theorem_3 {P : Type} [Fintype P] [DecidableEq P] (h3 : 3 * t < Fintype.card P)
    (hn : (d + 1) * t < Fintype.card P) : (bvcValidity P d).SolvableSync t δ := by
  obtain ⟨M, S, A, hA⟩ := icSolvableSync_of_three_t_lt (P := P) (VI := Vec d) (δ := δ) h3
  exact ⟨M, S, withGamma t A, withGamma_solves hA hn⟩

end ByzantineVectorConsensus
