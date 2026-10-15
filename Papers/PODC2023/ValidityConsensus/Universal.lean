import Papers.PODC2023.ValidityConsensus.Similarity

/-!
# On the Validity of Consensus — §5.2: `Universal` (Theorem 5) and the classification

* Vector consensus (§5.2.1) is taken as a black box: `SolvesVectorConsensus`. Its existence is a
  *hypothesis* (the paper gives implementations in its Appendix B, relying on Quad / DBFT and
  reliable broadcast; these are not formalized).
* `universal A Λ` (Algorithm 2): run vector consensus `A`, decide `Λ vector`.
* `solvesConsensus_universal` (Lemma 8 / Theorem 5): if `n > 2t` (the paper assumes `n > 3t`)
  and `Λ` witnesses `C_S`, then `universal A Λ` solves consensus with `val`, and it sends exactly
  the messages of `A` in every run (`msgsUpTo_universal`), so it inherits `A`'s message complexity.
* `solvable_iff_similarityCondition` (`n > 3t`, assuming vector consensus is solvable) and
  `solvable_iff_trivial` (`n ≤ 3t`): the full classification of solvable validity properties.
-/

namespace ValidityConsensus

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI VO K : Type*} [Fintype P] [DecidableEq P] {t δ : ℕ}

/-- **Vector consensus** (§5.2.1): Termination, Agreement and Vector Validity — a decided vector
has exactly `n - t` process-proposal pairs, and the pair of each correct process is its actual
proposal. -/
structure SolvesVectorConsensus (t δ : ℕ) (A : Algorithm P M S VI (Config P VI)) : Prop where
  termination : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∃ vec, R.Decides A p vec
  agreement : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w,
    R.Decides A p v → R.Decides A q w → v = w
  vectorValidity : ∀ R : Run P M VI, R.Valid t δ → ∀ p ∉ R.faulty, ∀ vec,
    R.Decides A p vec → IsInputConfigExact t vec ∧
      ∀ q ∉ R.faulty, vec q ≠ none → vec q = some (R.inp q)

/-- Vector consensus is solvable (with message and state types in `Type`). -/
def VectorConsensusSolvable (P VI : Type*) [Fintype P] [DecidableEq P] (t δ : ℕ) : Prop :=
  ∃ (M S : Type) (A : Algorithm P M S VI (Config P VI)), SolvesVectorConsensus t δ A

/-- **Algorithm 2 (`Universal`)**: decide `Λ vector` once vector consensus decides `vector`. -/
def universal (A : Algorithm P M S VI (Config P VI)) (Λ : Config P VI → VO) :
    Algorithm P M S VI VO where
  init := A.init
  step := A.step
  send := A.send
  decide p s := (A.decide p s).map Λ

variable {A : Algorithm P M S VI (Config P VI)} {Λ : Config P VI → VO}

omit [Fintype P] in
theorem st_universal (R : Run P M VI) : R.st (universal A Λ) = R.st A :=
  R.st_congr _ rfl rfl rfl

omit [Fintype P] in
theorem decides_universal {R : Run P M VI} {p : P} {v : VO} :
    R.Decides (universal A Λ) p v ↔ ∃ vec, R.Decides A p vec ∧ Λ vec = v := by
  simp only [Run.Decides, st_universal]
  simp only [universal, Option.map_eq_some_iff]
  constructor
  · rintro ⟨τ, vec, h, rfl⟩; exact ⟨vec, ⟨τ, h⟩, rfl⟩
  · rintro ⟨vec, ⟨τ, h⟩, rfl⟩; exact ⟨τ, vec, h, rfl⟩

/-- `Universal` sends exactly the messages of the underlying vector consensus. -/
theorem msgsUpTo_universal (R : Run P M VI) (N : ℕ) :
    R.msgsUpTo (universal A Λ) N = R.msgsUpTo A N := by
  simp only [Run.msgsUpTo, Run.msgsAt, R.out_congr (universal A Λ) (A' := A) rfl rfl rfl]

theorem msgComplexity_universal (R : Run P M VI) :
    R.msgComplexity (universal A Λ) = R.msgComplexity A := by
  simp only [Run.msgComplexity, msgsUpTo_universal]

/-- **Lemma 8 / Theorem 5.** If `n > 2t` and `Λ` witnesses the similarity condition, `Universal`
solves consensus with `val` on top of any vector consensus algorithm. -/
theorem solvesConsensus_universal {val : ValidityProperty P VI VO}
    (hn : 2 * t < Fintype.card P) (hA : SolvesVectorConsensus t δ A)
    (hΛ : ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c)) :
    SolvesConsensus t δ (universal A Λ) val where
  termination R hR p hp := by
    obtain ⟨vec, h⟩ := hA.termination R hR p hp
    exact ⟨Λ vec, decides_universal.mpr ⟨vec, h, rfl⟩⟩
  agreement R hR p hp q hq v w hv hw := by
    obtain ⟨vec, h, rfl⟩ := decides_universal.mp hv
    obtain ⟨vec', h', rfl⟩ := decides_universal.mp hw
    rw [hA.agreement R hR p hp q hq vec vec' h h']
  validity R hR p hp v hv := by
    obtain ⟨vec, h, rfl⟩ := decides_universal.mp hv
    obtain ⟨hvec, hcorr⟩ := hA.vectorValidity R hR p hp vec h
    refine hΛ vec hvec _ (Run.isInputConfig_inputConf hR) ⟨?_, ?_⟩
    · -- `|π(c*)| + |π(vec)| ≥ 2(n - t) > n`
      rw [← card_pos]
      have h1 := card_union_add_card_inter R.inputConf.procs vec.procs
      have h2 := card_le_univ (R.inputConf.procs ∪ vec.procs)
      have h3 := Run.isInputConfig_inputConf hR
      unfold IsInputConfig at h3
      unfold IsInputConfigExact at hvec
      omega
    · intro q hq
      rw [mem_inter, Run.mem_procs_inputConf, Config.mem_procs_iff_ne_none] at hq
      rw [hcorr q hq.1 hq.2]
      simp [Run.inputConf, hq.1]

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

omit [Fintype P] in
theorem out_universal (R : Run P M VI) : R.out (universal A Λ) = R.out A :=
  R.out_congr _ rfl rfl rfl

omit [Fintype P] in
theorem inbox_universal (R : Run P M VI) : R.inbox (universal A Λ) = R.inbox A := by
  funext p τ q
  simp only [Run.inbox, Run.inboxWith, Run.outWith, st_universal]
  rfl

omit [Fintype P] in
theorem authValid_universal {Au : Auth P M K} (R : Run P M VI) :
    R.AuthValid Au (universal A Λ) ↔ R.AuthValid Au A := by
  simp only [Run.AuthValid, Run.honestTokens, out_universal]

omit [Fintype P] in
theorem unforging_universal {Au : Auth P M K} (hU : A.Unforging Au) :
    (universal A Λ).Unforging Au := by
  intro R p τ q m hm x hx
  rw [st_universal] at hm
  have := hU R p τ q m hm x hx
  simpa only [Run.recvTokens, inbox_universal] using this

/-- **Lemma 8 / Theorem 5**, authenticated model. -/
theorem solvesConsensus_universal_auth {Au : Auth P M K} {val : ValidityProperty P VI VO}
    (hn : 2 * t < Fintype.card P) (hA : SolvesVectorConsensusAuth Au t δ A)
    (hΛ : ∀ c, IsInputConfigExact t c → CommonAdmissible t val c (Λ c)) :
    SolvesConsensusAuth Au t δ (universal A Λ) val := by
  -- reduce to the unauthenticated proof applied to the runs that respect unforgeability
  have key : ∀ R : Run P M VI, R.Valid t δ → R.AuthValid Au A →
      (∀ p ∉ R.faulty, ∃ v, R.Decides (universal A Λ) p v) ∧
      (∀ p ∉ R.faulty, ∀ q ∉ R.faulty, ∀ v w, R.Decides (universal A Λ) p v →
        R.Decides (universal A Λ) q w → v = w) ∧
      (∀ p ∉ R.faulty, ∀ v, R.Decides (universal A Λ) p v → v ∈ val R.inputConf) := by
    intro R hR hRa
    refine ⟨fun p hp => ?_, fun p hp q hq v w hv hw => ?_, fun p hp v hv => ?_⟩
    · obtain ⟨vec, h⟩ := hA.termination R hR hRa p hp
      exact ⟨Λ vec, decides_universal.mpr ⟨vec, h, rfl⟩⟩
    · obtain ⟨vec, h, rfl⟩ := decides_universal.mp hv
      obtain ⟨vec', h', rfl⟩ := decides_universal.mp hw
      rw [hA.agreement R hR hRa p hp q hq vec vec' h h']
    · obtain ⟨vec, h, rfl⟩ := decides_universal.mp hv
      obtain ⟨hvec, hcorr⟩ := hA.vectorValidity R hR hRa p hp vec h
      refine hΛ vec hvec _ (Run.isInputConfig_inputConf hR) ⟨?_, ?_⟩
      · rw [← card_pos]
        have h1 := card_union_add_card_inter R.inputConf.procs vec.procs
        have h2 := card_le_univ (R.inputConf.procs ∪ vec.procs)
        have h3 := Run.isInputConfig_inputConf hR
        unfold IsInputConfig at h3
        unfold IsInputConfigExact at hvec
        omega
      · intro q hq
        rw [mem_inter, Run.mem_procs_inputConf, Config.mem_procs_iff_ne_none] at hq
        rw [hcorr q hq.1 hq.2]
        simp [Run.inputConf, hq.1]
  exact ⟨fun R hR hRa => (key R hR ((authValid_universal R).mp hRa)).1,
    fun R hR hRa => (key R hR ((authValid_universal R).mp hRa)).2.1,
    fun R hR hRa => (key R hR ((authValid_universal R).mp hRa)).2.2⟩

/-- **Theorem 5** (authenticated, solvability form). -/
theorem solvableAuth_of_similarityCondition {val : ValidityProperty P VI VO}
    (hn : 3 * t < Fintype.card P) (hvc : VectorConsensusSolvableAuth P VI t δ)
    (hS : SimilarityCondition t val) : val.SolvableAuth t δ := by
  obtain ⟨M, S, K, Au, A, hU, hA⟩ := hvc
  obtain ⟨Λ, hΛ⟩ := hS
  exact ⟨M, S, K, Au, universal A Λ, unforging_universal hU,
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
