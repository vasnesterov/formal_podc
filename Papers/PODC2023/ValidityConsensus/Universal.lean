import Papers.PODC2023.ValidityConsensus.Similarity
import Cslib.Computability.Distributed.Byzantine.PartialSync.Map
import Cslib.Computability.Distributed.Byzantine.PartialSync.VC.Main

/-!
# On the Validity of Consensus — §5.2: `Universal` (Theorem 5) and the classification

* Vector consensus (§5.2.1) is taken as a black box: CSLib's `SolvesVectorConsensus` (its decided
  vectors are `IsInputConfigExact t`). Its existence is a *hypothesis* (the paper gives
  implementations in its Appendix B, relying on Quad / DBFT and reliable broadcast; these are not
  formalized here; `Optimal.lean` discharges it with CSLib's verified protocol `VC`).
* `universal A Λ` (Algorithm 2): run vector consensus `A`, decide `Λ vector` (the decision
  post-processing `A.mapDecide Λ` of `Cslib.Computability.Distributed.Byzantine.PartialSync.Map`).
* `solvesConsensus_universal` (Lemma 8 / Theorem 5): if `n > 2t` (the paper assumes `n > 3t`)
  and `Λ` witnesses `C_S`, then `universal A Λ` solves consensus with `val`, and it sends exactly
  the messages of `A` in every run (`Run.msgsUpTo_mapDecide`), so it inherits `A`'s message
  complexity.
* `solvable_iff_similarityCondition` (`n > 3t`, assuming vector consensus is solvable) and
  `solvable_iff_trivial` (`n ≤ 3t`): the full classification of solvable validity properties.
-/

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}

/-- Vector consensus (§5.2.1, CSLib's `SolvesVectorConsensus`: Termination, Agreement and Vector
Validity — a decided vector has exactly `n - t` process-proposal pairs, i.e. it is
`IsInputConfigExact t`, and the pair of each correct process is its actual proposal) is solvable
(with message and state types in `Type`). -/
def VectorConsensusSolvable (P VI : Type*) [Fintype P] [DecidableEq P] (t δ : ℕ) : Prop :=
  ∃ (M S : Type) (A : Algorithm P M S VI (Config P VI)), SolvesVectorConsensus t δ A

/-- **Algorithm 2 (`Universal`)**: decide `Λ vector` once vector consensus decides `vector`. -/
abbrev universal (A : Algorithm P M S VI (Config P VI)) (Λ : Config P VI → VO) :
    Algorithm P M S VI VO :=
  A.mapDecide Λ

variable {A : Algorithm P M S VI (Config P VI)} {Λ : Config P VI → VO}

/-- The decisions of vector consensus, as a validity property: a decided vector has exactly
`n - t` process-proposal pairs, and agrees with the input configuration where both are defined. -/
def vectorConsensusValidity (t : ℕ) : ValidityProperty P VI (Config P VI) :=
  fun c => {vec | IsInputConfigExact t vec ∧ ∀ q, c q ≠ none → vec q ≠ none → vec q = c q}

theorem mem_vectorConsensusValidity_inputConf {R : Run P M VI} {vec : Config P VI}
    (hex : IsInputConfigExact t vec)
    (hcorr : ∀ q ∉ R.faulty, vec q ≠ none → vec q = some (R.inp q)) :
    vec ∈ vectorConsensusValidity t R.inputConf := by
  refine ⟨hex, fun q hq hq' => ?_⟩
  have hqF : q ∉ R.faulty := fun h => hq (by simp [Run.inputConf, h])
  rw [hcorr q hqF hq']
  simp [Run.inputConf, hqF]

/-- Vector consensus solves consensus with the validity property `vectorConsensusValidity t`. -/
theorem solvesConsensus_vectorConsensusValidity (hA : SolvesVectorConsensus t δ A) :
    SolvesConsensus t δ A (vectorConsensusValidity t) where
  termination := hA.termination
  agreement := hA.agreement
  validity R hR p hp vec hvec :=
    mem_vectorConsensusValidity_inputConf (hA.vectorValidity R hR p hp vec hvec).1
      (hA.vectorValidity R hR p hp vec hvec).2

/-- The key step of Lemma 8: if `n > 2t`, a vector admissible for the input configuration `c`
has `n - t` entries and is similar to `c` (`|π(c)| + |π(vec)| ≥ 2(n - t) > n`), so `Λ vec` is
admissible for `c`. -/
theorem mem_of_vectorConsensusValidity {val : ValidityProperty P VI VO}
    (hn : 2 * t < Fintype.card P)
    (hΛ : ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c)) {c : Config P VI}
    (hc : IsInputConfig t c) {vec : Config P VI} (hvec : vec ∈ vectorConsensusValidity t c) :
    Λ vec ∈ val c := by
  obtain ⟨hvec, hcorr⟩ := hvec
  refine hΛ vec hvec _ hc ⟨?_, fun q hq => ?_⟩
  · rw [← card_pos]
    have h1 := card_union_add_card_inter c.procs vec.procs
    have h2 := card_le_univ (c.procs ∪ vec.procs)
    unfold IsInputConfig at hc
    unfold IsInputConfigExact at hvec
    omega
  · rw [mem_inter, Config.mem_procs_iff_ne_none, Config.mem_procs_iff_ne_none] at hq
    exact (hcorr q hq.1 hq.2).symm

/-- **Lemma 8 / Theorem 5.** If `n > 2t` and `Λ` witnesses the similarity condition, `Universal`
solves consensus with `val` on top of any vector consensus algorithm. -/
theorem solvesConsensus_universal {val : ValidityProperty P VI VO}
    (hn : 2 * t < Fintype.card P) (hA : SolvesVectorConsensus t δ A)
    (hΛ : ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c)) :
    SolvesConsensus t δ (universal A Λ) val :=
  (solvesConsensus_vectorConsensusValidity hA).mapDecide fun _ hc _ hvec =>
    mem_of_vectorConsensusValidity hn hΛ hc hvec

/-- **Theorem 5** (solvability form): with `n > 3t`, if vector consensus is solvable then every
validity property satisfying `C_S` is solvable. -/
theorem solvable_of_similarityCondition {val : ValidityProperty P VI VO}
    (hn : 3 * t < Fintype.card P) (hvc : VectorConsensusSolvable P VI t δ)
    (hS : SimilarityCondition t val) : val.Solvable t δ := by
  obtain ⟨M, S, A, hA⟩ := hvc
  obtain ⟨Λ, hΛ⟩ := hS
  exact ⟨M, S, universal A Λ, solvesConsensus_universal (by omega) hA hΛ⟩

/-- **Classification for `n > 3t`** (Theorems 3 and 5): assuming vector consensus is solvable,
a validity property is solvable iff it satisfies the similarity condition. -/
theorem solvable_iff_similarityCondition [Nonempty VI] {val : ValidityProperty P VI VO}
    (hn : 3 * t < Fintype.card P) (hvc : VectorConsensusSolvable P VI t δ) :
    val.Solvable t δ ↔ SimilarityCondition t val :=
  ⟨fun h => similarityCondition_of_solvable h (by omega),
    solvable_of_similarityCondition hn hvc⟩

/-! ### The authenticated (PKI) variant

The paper's `O(n²)` upper bound uses an authenticated vector consensus (Algorithm 1, built on
Quad). We take it as a black box `SolvesVectorConsensusAuth`; `Universal` preserves
unforgeability, so the classification and the message-complexity transfer hold verbatim. -/

/-- Vector consensus in the authenticated model `Au`. -/
structure SolvesVectorConsensusAuth (Au : Auth P M K) (t δ : ℕ)
    (A : Algorithm P M S VI (Config P VI)) : Prop where
  termination : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A →
    ∀ p ∉ R.faulty, ∃ vec, R.Decides A p vec
  agreement : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A →
    ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, R.Decides A p v → R.Decides A q w → v = w
  vectorValidity : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A → ∀ p ∉ R.faulty, ∀ vec,
    R.Decides A p vec → IsInputConfigExact t vec ∧
      ∀ q ∉ R.faulty, vec q ≠ none → vec q = some (R.inp q)

/-- Vector consensus is solvable with signatures. -/
def VectorConsensusSolvableAuth (P VI : Type*) [Fintype P] [DecidableEq P] (t δ : ℕ) : Prop :=
  ∃ (M S K : Type) (Au : Auth P M K) (A : Algorithm P M S VI (Config P VI)),
    A.Unforging Au ∧ SolvesVectorConsensusAuth Au t δ A

/-- Authenticated vector consensus solves consensus with the validity property
`vectorConsensusValidity t`. -/
theorem SolvesVectorConsensusAuth.solvesConsensusAuth {Au : Auth P M K}
    (hA : SolvesVectorConsensusAuth Au t δ A) :
    SolvesConsensusAuth Au t δ A (vectorConsensusValidity t) where
  termination := hA.termination
  agreement := hA.agreement
  validity R hR hRa p hp vec hvec :=
    mem_vectorConsensusValidity_inputConf (hA.vectorValidity R hR hRa p hp vec hvec).1
      (hA.vectorValidity R hR hRa p hp vec hvec).2

/-- **Lemma 8 / Theorem 5**, authenticated model. -/
theorem solvesConsensus_universal_auth {Au : Auth P M K} {val : ValidityProperty P VI VO}
    (hn : 2 * t < Fintype.card P) (hA : SolvesVectorConsensusAuth Au t δ A)
    (hΛ : ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c)) :
    SolvesConsensusAuth Au t δ (universal A Λ) val :=
  hA.solvesConsensusAuth.mapDecide fun _ hc _ hvec =>
    mem_of_vectorConsensusValidity hn hΛ hc hvec

/-- **Theorem 5** (authenticated, solvability form). -/
theorem solvableAuth_of_similarityCondition {val : ValidityProperty P VI VO}
    (hn : 3 * t < Fintype.card P) (hvc : VectorConsensusSolvableAuth P VI t δ)
    (hS : SimilarityCondition t val) : val.SolvableAuth t δ := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := hvc
  obtain ⟨Λ, hΛ⟩ := hS
  exact ⟨M, S, K, Au, universal A Λ, hU.mapDecide Λ,
    solvesConsensus_universal_auth (by omega) hA hΛ⟩

/-- **Classification for `n > 3t`**, authenticated model. -/
theorem solvableAuth_iff_similarityCondition [Nonempty VI] {val : ValidityProperty P VI VO}
    (hn : 3 * t < Fintype.card P) (hvc : VectorConsensusSolvableAuth P VI t δ) :
    val.SolvableAuth t δ ↔ SimilarityCondition t val :=
  ⟨fun h => similarityCondition_of_solvableAuth h (by omega),
    solvableAuth_of_similarityCondition hn hvc⟩

/-- The trivial algorithm: every process decides `v` immediately. -/
def constAlgorithm (P VI : Type*) {VO : Type*} (v : VO) : Algorithm P Unit Unit VI VO where
  init _ _ := ()
  step _ _ _ := ()
  send _ _ _ := []
  decide _ _ := some v

/-- An always-admissible value makes consensus trivially solvable (for any `n`, `t`). -/
theorem solvesConsensus_const {val : ValidityProperty P VI VO} {v : VO}
    (hv : ∀ c, IsInputConfig t c → v ∈ val c) :
    SolvesConsensus t δ (constAlgorithm P VI v) val where
  termination _ _ _ _ := ⟨v, 0, rfl⟩
  agreement _ _ _ _ _ _ _ _ := by
    rintro ⟨_, h₁⟩ ⟨_, h₂⟩
    simp only [constAlgorithm, Option.some.injEq] at h₁ h₂
    rw [← h₁, ← h₂]
  validity R hR _ _ w := by
    rintro ⟨_, h⟩
    simp only [constAlgorithm, Option.some.injEq] at h
    exact h ▸ hv _ (Run.isInputConfig_inputConf hR)

theorem solvable_of_trivial {val : ValidityProperty P VI VO} (h : val.Trivial t) :
    val.Solvable t δ := by
  obtain ⟨v, hv⟩ := h
  exact ⟨Unit, Unit, constAlgorithm P VI v, solvesConsensus_const hv⟩

theorem solvableAuth_of_trivial {val : ValidityProperty P VI VO} (h : val.Trivial t) :
    val.SolvableAuth t δ :=
  (solvable_of_trivial h).solvableAuth

/-- **Classification for `n ≤ 3t`**, authenticated model. -/
theorem solvableAuth_iff_trivial [Nonempty VI] {val : ValidityProperty P VI VO} (ht : 0 < t)
    (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    val.SolvableAuth t δ ↔ val.Trivial t :=
  ⟨fun h => trivial_of_solvableAuth h ht htn hn, solvableAuth_of_trivial⟩

/-- **Classification for `n ≤ 3t`** (Theorem 1 and the remark after Theorem 2): a validity
property is solvable iff it is trivial. -/
theorem solvable_iff_trivial [Nonempty VI] {val : ValidityProperty P VI VO} (ht : 0 < t)
    (htn : t < Fintype.card P) (hn : Fintype.card P ≤ 3 * t) :
    val.Solvable t δ ↔ val.Trivial t :=
  ⟨fun h => trivial_of_solvable h ht htn hn, solvable_of_trivial⟩

end ValidityConsensus
