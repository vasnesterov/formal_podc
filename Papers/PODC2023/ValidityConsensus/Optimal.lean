import Papers.PODC2023.ValidityConsensus.Universal
import Papers.PODC2023.ValidityConsensus.NonVacuity
import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Main

/-!
# The classification at optimal resilience, unconditionally

The verified vector-consensus protocol `Cslib.Byzantine.PartialSync.VC` (any `n > 3t`) discharges the
black-box hypothesis of §5.2:

* `vectorConsensusSolvable`, `vectorConsensusSolvableAuth`;
* **`solvable_iff_similarityCondition'`** (Theorems 3 + 5): for `n > 3t`, a validity property is
  solvable iff it satisfies `C_S` — no hypothesis left; and the authenticated analogue;
* `strongValidity_solvable_optimal`: binary consensus with strong validity is solvable for every
  `n > 3t` (the protocol is `Universal` on top of `VC`, deciding the majority of the vector), so
  Theorems 3 and 4 are non-vacuous at optimal resilience.
-/

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync
open Cslib.Byzantine.PartialSync.VC (cnt)

variable {P VI VO : Type} [Fintype P] [DecidableEq P] {t δ : ℕ}

/-- The paper's vector-consensus specification is the one of `Cslib.Byzantine.PartialSync`. -/
theorem SolvesVectorConsensus.of_podc {M S : Type} {A : Algorithm P M S VI (Config P VI)}
    (h : Cslib.Byzantine.PartialSync.SolvesVectorConsensus t δ A) : SolvesVectorConsensus t δ A :=
  ⟨h.termination, h.agreement, h.vectorValidity⟩

/-- **Vector consensus is solvable for `n > 3t`** (verified protocol `VC`). -/
theorem vectorConsensusSolvable (hn : 3 * t < Fintype.card P) :
    VectorConsensusSolvable P VI t δ :=
  ⟨_, _, _, SolvesVectorConsensus.of_podc
    (VC.solvesVectorConsensus hn (Binary.rotLeader_surj (by omega)) δ)⟩

/-- Vector consensus is solvable for `n > 3t` in the authenticated model (with no tokens). -/
theorem vectorConsensusSolvableAuth (hn : 3 * t < Fintype.card P) :
    VectorConsensusSolvableAuth P VI t δ := by
  obtain ⟨M, S, A, hA⟩ := vectorConsensusSolvable (VI := VI) (δ := δ) hn
  exact ⟨M, S, Empty, Auth.none P M, A, A.unforging_none,
    ⟨fun R hR _ => hA.termination R hR, fun R hR _ => hA.agreement R hR,
      fun R hR _ => hA.vectorValidity R hR⟩⟩

/-- **Classification for `n > 3t`, unconditional** (Theorems 3 and 5): a validity property is
solvable iff it satisfies the similarity condition. -/
theorem solvable_iff_similarityCondition' [Nonempty VI] {val : ValidityProperty P VI VO}
    (hn : 3 * t < Fintype.card P) : val.Solvable t δ ↔ SimilarityCondition t val :=
  solvable_iff_similarityCondition hn (vectorConsensusSolvable hn)

/-- **Classification for `n > 3t`, authenticated model, unconditional.** -/
theorem solvableAuth_iff_similarityCondition' [Nonempty VI] {val : ValidityProperty P VI VO}
    (hn : 3 * t < Fintype.card P) : val.SolvableAuth t δ ↔ SimilarityCondition t val :=
  solvableAuth_iff_similarityCondition hn (vectorConsensusSolvableAuth hn)

/-- **The full classification** (Theorems 1, 3, 5): for `0 < t < n`, a validity property is
solvable iff it is trivial (`n ≤ 3t`) or satisfies `C_S` (`n > 3t`). -/
theorem solvable_iff [Nonempty VI] {val : ValidityProperty P VI VO} (ht : 0 < t)
    (htn : t < Fintype.card P) :
    val.Solvable t δ ↔
      (Fintype.card P ≤ 3 * t ∧ val.Trivial t) ∨ (3 * t < Fintype.card P ∧ SimilarityCondition t val) := by
  rcases le_or_gt (Fintype.card P) (3 * t) with h | h
  · rw [solvable_iff_trivial ht htn h]; constructor
    · exact fun hv => Or.inl ⟨h, hv⟩
    · rintro (⟨-, hv⟩ | ⟨h', -⟩)
      · exact hv
      · omega
  · rw [solvable_iff_similarityCondition' h]; constructor
    · exact fun hv => Or.inr ⟨h, hv⟩
    · rintro (⟨h', -⟩ | ⟨-, hv⟩)
      · omega
      · exact hv

/-! ### Binary strong validity at optimal resilience -/

/-- Majority of a binary vector. -/
noncomputable def majority (c : Config P Bool) : Bool :=
  decide (cnt (fun q => c q = some false) < cnt (fun q => c q = some true))

/-- For `n > 3t`, the majority of an input configuration with `n - t` entries is admissible for
binary strong validity in every similar input configuration. -/
theorem majority_commonAdmissible (hn : 3 * t < Fintype.card P) (c : Config P Bool)
    (hc : IsInputConfigExact t c) :
    CommonAdmissible t (Binary.strongValidity (P := P)) c (majority c) := by
  intro c' hc' hsim v hv
  have hv' : ∀ q, c q ≠ none → c' q ≠ none → c q = some v := by
    intro q hq hq'
    rw [← hsim.2 q (by simp [Option.isSome_iff_ne_none, hq, hq']), hv q hq']
  unfold IsInputConfig at hc'
  unfold IsInputConfigExact at hc
  set A : Set P := {q | c q ≠ none}
  set B : Set P := {q | c' q ≠ none}
  have hA : A.ncard = Fintype.card P - t := by
    rw [← hc, ← Set.ncard_coe_finset]; congr 1; ext q
    simp [A, Option.isSome_iff_ne_none]
  have hB : Fintype.card P - t ≤ B.ncard := by
    have : B = ↑c'.procs := by ext q; simp [B, Option.isSome_iff_ne_none]
    rw [this, Set.ncard_coe_finset]; exact hc'
  have hU : (A ∪ B).ncard ≤ Fintype.card P := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  have hUI := Set.ncard_union_add_ncard_inter A B
  have hBc : Bᶜ.ncard = Fintype.card P - B.ncard := by
    rw [Set.ncard_compl, Nat.card_eq_fintype_card]
  -- `v` appears at least `n - 2t` times in `c`, the other value at most `t` times
  have hvc : (A ∩ B).ncard ≤ cnt (fun q => c q = some v) :=
    Set.ncard_le_ncard (fun q hq => hv' q hq.1 hq.2) (Set.toFinite _)
  have hnv : cnt (fun q => c q = some (!v)) ≤ Bᶜ.ncard := by
    refine Set.ncard_le_ncard (fun q hq => ?_) (Set.toFinite _)
    intro hq'
    have := hv' q (by simp [Set.mem_ofPred_eq.mp hq]) hq'
    rw [Set.mem_ofPred_eq.mp hq] at this; cases v <;> simp at this
  have hBle : B.ncard ≤ Fintype.card P := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  unfold majority
  cases v <;> simp at hvc hnv ⊢ <;> omega

/-- Binary strong validity satisfies the similarity condition when `n > 3t`
(`Λ` = majority). -/
theorem strongValidity_similarityCondition_optimal (hn : 3 * t < Fintype.card P) :
    SimilarityCondition t (Binary.strongValidity (P := P)) :=
  ⟨majority, majority_commonAdmissible hn⟩

/-- **Binary consensus with strong validity is solvable for every `n > 3t`**: the protocol is
`Universal` (majority of the decided vector) on top of the verified vector consensus `VC`. -/
theorem strongValidity_solvable_optimal (hn : 3 * t < Fintype.card P) :
    (Binary.strongValidity (P := P)).Solvable t δ :=
  solvable_of_similarityCondition hn (vectorConsensusSolvable hn)
    (strongValidity_similarityCondition_optimal hn)

/-- Explicit form: `Universal ∘ VC` with the majority map solves binary strong-validity consensus
for `n > 3t`. -/
theorem universal_vc_solves (hn : 3 * t < Fintype.card P) :
    SolvesConsensus t δ
      (universal ((VC.algo (VI := Bool) t (Binary.rotLeader (by omega))).compile (δ + 1)) majority)
      (Binary.strongValidity (P := P)) :=
  solvesConsensus_universal (by omega)
    (SolvesVectorConsensus.of_podc
      (VC.solvesVectorConsensus hn (Binary.rotLeader_surj (by omega)) δ))
    (majority_commonAdmissible hn)

/-- Theorem 4 at optimal resilience: for `n > 3t ≥ 3`, the explicit protocol has a valid
synchronous run with at least `⌈t/2⌉(⌈t/2⌉+1)` messages. -/
theorem optimal_message_lower_bound (ht : 0 < t) (hn : 3 * t < Fintype.card P) :
    ∃ R : Run P (ℕ × VC.Msg P Bool) Bool, R.Valid t δ ∧ R.gst = 0 ∧ ∃ N,
      ((t + 1) / 2) * ((t + 1) / 2 + 1) ≤ R.msgsUpTo
        (universal ((VC.algo (VI := Bool) t (Binary.rotLeader (by omega))).compile (δ + 1))
          majority) N :=
  message_lower_bound (universal_vc_solves hn) Binary.strongValidity_not_trivial ht (by omega)

end ValidityConsensus
