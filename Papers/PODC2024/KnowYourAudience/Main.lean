import Papers.PODC2024.KnowYourAudience.Positive

/-!
# Know your audience (Charron-Bost, Lambein-Monette, PODC 2024): main statements

Static networks (Section 4). The communication models are `CommModel.outPort` (output port
awareness), `CommModel.symmetric` (symmetric communications) and `CommModel.outdegree` (outdegree
awareness); `X` is any metric space (`δ` = its metric).

* Lemma 3.1 (Lifting lemma): `Cslib.AnonNet.Fibration.runFrom_comp`.
* Lemma 3.2: `Cslib.AnonNet.Fibration.eq_of_computesOn`.
* Lemma 3.3: `Cslib.AnonNet.Computes.perm_eq`, `multisetBased_of_computable`.
* Theorem 4.1, (i) ⇒ (ii): `theorem_4_1_i_imp_ii` — true.
* Theorem 4.1, (ii) ⇒ (i): **false** (`theorem_4_1_ii_imp_i_false`, `theorem_4_1_false`);
  corrected characterisations `theorem_4_1_corrected` and `theorem_4_1_corrected_symmetric`.
* Corollary 4.2: false as stated (`corollary_4_2_false`); corrected `corollary_4_2_corrected`,
  `corollary_4_2_corrected_symmetric`.
* Corollary 4.3: `corollary_4_3` — true.
* Corollary 4.4: `corollary_4_4` — true.
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet

universe u v

variable {I : Type u} [DecidableEq I] {X : Type v} [MetricSpace X]

/-- **Theorem 4.1, (i) ⇒ (ii).** In each of the three models, every frequency-based function is
`δ`-computable in the class of static strongly connected networks. -/
theorem theorem_4_1_i_imp_ii {m : CommModel}
    (hm : m = .outPort ∨ m = .symmetric ∨ m = .outdegree) {f : List I → X}
    (hf : FrequencyBased f) : Computable m staticSC (fun _ => True) f :=
  computable_of_frequencyBased (by rcases hm with rfl | rfl | rfl <;> decide) hf

/-- **Theorem 4.1, (ii) ⇒ (i), is false** in each of the three models: "is the network a single
agent?" is computable (with the discrete metric on `ℕ`) but not frequency-based. -/
theorem theorem_4_1_ii_imp_i_false [Nonempty I] (m : CommModel) :
    ∃ f : List I → ℕ, Computable m staticSC (fun _ => True) f ∧ ¬ FrequencyBased f :=
  ⟨isSingleton, isSingleton_computable m, isSingleton_not_frequencyBased⟩

/-- Theorem 4.1 as stated (for all `f`, (i) ⇔ (ii)) fails in each of the three models. -/
theorem theorem_4_1_false [Nonempty I] (m : CommModel) :
    ¬ ∀ f : List I → ℕ, FrequencyBased f ↔ Computable m staticSC (fun _ => True) f := by
  intro h
  obtain ⟨f, hc, hnf⟩ := theorem_4_1_ii_imp_i_false (I := I) m
  exact hnf ((h f).2 hc)

/-- With symmetric communications the failure is not limited to one-agent networks:
"is the network `K₂`?" is computable, and not frequency-based even on vectors of length `≥ 2`. -/
theorem theorem_4_1_false_symmetric_K2 [Nonempty I] :
    ∃ f : List I → ℕ, Computable .symmetric staticSC (fun _ => True) f ∧
      ¬ FrequencyBasedFrom 2 f :=
  ⟨isPair, isPair_computable, isPair_not_frequencyBasedFrom_two⟩

/-- **Theorem 4.1, corrected (outdegree awareness / output port awareness).** `f` is
`δ`-computable in the class of static strongly connected networks iff it is frequency-based on
vectors of length `≥ 2` (its values on vectors of length `1` are arbitrary). -/
theorem theorem_4_1_corrected {m : CommModel} (hm : m = .outPort ∨ m = .outdegree)
    (f : List I → X) :
    Computable m staticSC (fun _ => True) f ↔ FrequencyBasedFrom 2 f := by
  have h1 : m ≠ .symmetric := by rcases hm with rfl | rfl <;> decide
  have h2 : m ≠ .broadcast := by rcases hm with rfl | rfl <;> decide
  exact ⟨frequencyBasedFrom_two_of_computable h1, computable_of_frequencyBasedFrom_two h2⟩

/-- **Theorem 4.1, corrected (symmetric communications).** `f` is `δ`-computable in the class of
static strongly connected bidirectional networks iff it is symmetric and frequency-based on vectors
of length `≥ 3`. -/
theorem theorem_4_1_corrected_symmetric (f : List I → X) :
    Computable .symmetric staticSC (fun _ => True) f ↔
      FrequencyBasedFrom 3 f ∧ MultisetBased f :=
  ⟨fun h => ⟨frequencyBasedFrom_three_of_computable_symmetric h, multisetBased_of_computable h⟩,
    fun h => computable_of_frequencyBasedFrom_three_symmetric h.1 h.2⟩

/-- **Corollary 4.2 is false as stated**: `isSingleton` is computable in every class `C_{≤B}`. -/
theorem corollary_4_2_false [Nonempty I] (m : CommModel) :
    ¬ ∀ f : List I → ℕ, FrequencyBased f ↔ ∀ B, Computable m (sizeLE B) (fun _ => True) f := by
  intro h
  exact isSingleton_not_frequencyBased ((h isSingleton).2 fun B =>
    (isSingleton_computable m).mono fun _ _ hN => hN.1)

/-- **Corollary 4.2, (i) ⇒ (ii).** -/
theorem corollary_4_2_i_imp_ii {m : CommModel}
    (hm : m = .outPort ∨ m = .symmetric ∨ m = .outdegree) {f : List I → X}
    (hf : FrequencyBased f) (B : ℕ) : Computable m (sizeLE B) (fun _ => True) f :=
  computable_sizeLE_of_frequencyBased (by rcases hm with rfl | rfl | rfl <;> decide) hf B

/-- **Corollary 4.2, corrected (outdegree / output port awareness).** -/
theorem corollary_4_2_corrected {m : CommModel} (hm : m = .outPort ∨ m = .outdegree)
    (f : List I → X) :
    (∀ B, Computable m (sizeLE B) (fun _ => True) f) ↔ FrequencyBasedFrom 2 f := by
  have h1 : m ≠ .symmetric := by rcases hm with rfl | rfl <;> decide
  refine ⟨frequencyBasedFrom_two_of_computable_sizeLE h1, fun h B => ?_⟩
  exact ((theorem_4_1_corrected hm f).2 h).mono fun _ _ hN => hN.1

/-- **Corollary 4.2, corrected (symmetric communications).** -/
theorem corollary_4_2_corrected_symmetric (f : List I → X) :
    (∀ B, Computable .symmetric (sizeLE B) (fun _ => True) f) ↔
      FrequencyBasedFrom 3 f ∧ MultisetBased f := by
  refine ⟨fun h => ⟨frequencyBasedFrom_three_of_computable_sizeLE_symmetric h, ?_⟩,
    fun h B => ((theorem_4_1_corrected_symmetric f).2 h).mono fun _ _ hN => hN.1⟩
  -- multiset-based: Lemma 3.3 on rings of the right size
  intro l l' hperm
  obtain ⟨A, hA, hcomp⟩ := h l.length
  rcases Nat.eq_zero_or_pos l.length with h0 | hpos
  · rw [List.length_eq_zero_iff] at h0
    subst h0
    rw [List.nil_perm.1 hperm]
  have : NeZero l.length := ⟨by omega⟩
  exact (hcomp.perm_eq hA (sizeLE_isoClosed _) hpos ⟨ringNet_sc _, le_rfl⟩
    (ringNet_symmetric _) rfl hperm trivial trivial).symm

omit [DecidableEq I] in
/-- **Corollary 4.3.** When the size of the network is known, a function is `δ`-computable iff it
is multiset-based. -/
theorem corollary_4_3 {m : CommModel} (hm : m = .outPort ∨ m = .symmetric ∨ m = .outdegree)
    (f : List I → X) :
    (∀ k, Computable m (sizeEq k) (fun _ => True) f) ↔ MultisetBased f :=
  ⟨multisetBased_of_computable_sizeEq,
    fun h k => computable_sizeEq_of_multisetBased (by rcases hm with rfl | rfl | rfl <;> decide)
      h k⟩

/-- **Corollary 4.4.** With one leader (inputs `(value, isLeader)` with exactly one leader), a
function of the values is `δ`-computable iff it is multiset-based. -/
theorem corollary_4_4 {m : CommModel} (hm : m = .outPort ∨ m = .symmetric ∨ m = .outdegree)
    (f : List I → X) :
    Computable m staticSC OneLeader (fun l => f (l.map Prod.fst)) ↔ MultisetBased f :=
  ⟨multisetBased_of_computable_leader,
    computable_leader_of_multisetBased (by rcases hm with rfl | rfl | rfl <;> decide)⟩

end Podc.KnowYourAudience
