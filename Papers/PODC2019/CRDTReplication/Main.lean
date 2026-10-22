import Papers.PODC2019.CRDTReplication.History
import Papers.PODC2019.CRDTReplication.Linearizability
import Papers.PODC2019.CRDTReplication.Counterexample

/-!
# Main results

**Algorithm 2 as written** (`Variant.paper`), for every state-based CRDT and every quorum
system:
* Lemma 1, Corollary 1, Lemma 2, Lemma 4 and Theorems 1, 2, 5 hold (`paper_*`);
* Lemma 3, Theorem 3 (Consistency), Theorem 4 (Update Stability) and linearizability are false
  (`Cex.lemma3_false`, `Cex.theorem3_false`, `Cex.theorem4_false`, `Cex.not_linearizable`: the
  G-set, five processes, majority quorums).

**The repaired protocol** (`Variant.fixed`: an acceptor answers `VOTE((n, i), s')` only if, in
addition, its payload is `⊑ s'`) satisfies Theorems 1–5 and is linearizable (`fixed_*`), via the
paper's Section III-E argument (`linearizable_of_learnedHistory`, which is correct).
-/

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT} {QS : Finset (Finset P)}

lemma Variant.paper_cons (s t : D.S) : (Variant.paper (D := D)).cons s t = true → s = t := by
  simp [Variant.paper]

lemma Variant.fixed_cons (s t : D.S) : (Variant.fixed (D := D)).cons s t = true → s = t := by
  simp [Variant.fixed]

/-! ## Algorithm 2 as written -/

/-- **Lemma 1** for Algorithm 2. -/
theorem paper_lemma1 : Lemma1 (Variant.paper (D := D)) QS := lemma1

/-- **Corollary 1** for Algorithm 2. -/
theorem paper_corollary1 : Corollary1 (Variant.paper (D := D)) QS :=
  corollary1 Variant.paper_cons

/-- **Lemma 2** for Algorithm 2. -/
theorem paper_lemma2 : Lemma2 (Variant.paper (D := D)) QS := lemma2 Variant.paper_cons

/-- **Lemma 4** for Algorithm 2: two states learned by vote are comparable. -/
theorem paper_lemma4 (hQS : IsQuorumSystem QS) : Lemma4 (Variant.paper (D := D)) QS :=
  lemma4 Variant.paper_cons hQS

/-- **Theorem 1 (Validity)** for Algorithm 2. -/
theorem paper_theorem1 (hQS : IsQuorumSystem QS) (H : D.CausalHistory) :
    Theorem1 (Variant.paper (D := D)) QS H := theorem1 Variant.paper_cons hQS H

/-- **Theorem 2 (Stability)** for Algorithm 2. -/
theorem paper_theorem2 (hQS : IsQuorumSystem QS) : Theorem2 (Variant.paper (D := D)) QS :=
  theorem2 Variant.paper_cons hQS

/-- **Theorem 5 (Update Visibility)** for Algorithm 2. -/
theorem paper_theorem5 (hQS : IsQuorumSystem QS) (H : D.CausalHistory) :
    Theorem5 (Variant.paper (D := D)) QS H := theorem5 Variant.paper_cons hQS H

/-- **Lemma 3, Theorem 3, Theorem 4 and linearizability fail for Algorithm 2** (G-set over two
updates, five processes, majority quorums). -/
theorem paper_false :
    IsQuorumSystem Cex.QS5 ∧ ¬ Lemma3 (Variant.paper (D := Cex.G)) Cex.QS5 ∧
    ¬ Theorem3 (Variant.paper (D := Cex.G)) Cex.QS5 ∧
    ¬ Theorem4 (Variant.paper (D := Cex.G)) Cex.QS5 (gsetHistory (Fin 2)) ∧
    ¬ LinearizableClaim (Variant.paper (D := Cex.G)) Cex.QS5 ∧ ¬ Cex.alg5.Linearizable :=
  ⟨Cex.qs5_isQuorumSystem, Cex.lemma3_false, Cex.theorem3_false, Cex.theorem4_false,
    Cex.linearizableClaim_false, Cex.not_linearizable⟩

/-! ## The repaired protocol -/

/-- **Theorem 3 (Consistency)** for the repaired protocol. -/
theorem fixed_theorem3 (hQS : IsQuorumSystem QS) : Theorem3 (Variant.fixed (D := D)) QS :=
  theorem3_fixed Variant.fixed_cons rfl hQS

/-- **Lemma 3** for the repaired protocol. -/
theorem fixed_lemma3 (hQS : IsQuorumSystem QS) : Lemma3 (Variant.fixed (D := D)) QS :=
  lemma3_fixed Variant.fixed_cons rfl hQS

/-- **Theorem 4 (Update Stability)** for the repaired protocol. -/
theorem fixed_theorem4 (hQS : IsQuorumSystem QS) (H : D.CausalHistory) :
    Theorem4 (Variant.fixed (D := D)) QS H := theorem4_fixed Variant.fixed_cons rfl hQS H

/-- The histories of the repaired protocol satisfy the hypotheses of Section III-E. -/
theorem fixed_learnedHistory (hQS : IsQuorumSystem QS) (H : D.CausalHistory)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg Variant.fixed QS).Reach C h) (hu : UniqueUpd h) :
    LearnedHistory H h (learnedOf C) := by
  have hcons := Variant.fixed_cons (D := D)
  have hP := procInv_of_reach hcons hr
  have hlearn : ∀ x s, learnedOf C x = some s →
      Completed h x ∧ ∃ v, LearnedOK QS C.sent h x.1 x.2 s v := by
    intro x s hx
    simp only [learnedOf, Option.map_eq_some_iff] at hx
    obtain ⟨⟨s', v⟩, hx, rfl⟩ := hx
    exact ⟨(learned_ok hcons hr hx).1, v, (learned_ok hcons hr hx).2⟩
  refine ⟨hP.1, fun x s hx => ?_, fun x q r hx hr' => ?_, fun x u r hx hr' => ?_, hu,
    fun x s hx u hu' => ?_, fun x s hx u hu' y hy hp => ?_,
    fun x y s₁ s₂ hp h₁ h₂ => theorem2 hcons hQS C h hr x y s₁ s₂ hp h₁ h₂,
    fun x y s₁ s₂ h₁ h₂ => fixed_theorem3 hQS C h hr s₁ s₂ ⟨x, h₁⟩ ⟨y, h₂⟩,
    fun x y z u₁ u₂ s hp hx hy hz => fixed_theorem4 hQS H C h hr hu x y u₁ u₂ s hp hx hy ⟨z, hz⟩,
    fun x y u s hp hx hy => theorem5 hcons hQS H C h hr x y u s hp hx hy⟩
  · obtain ⟨hc, v, ⟨q, hq, -⟩, -⟩ := hlearn x s hx
    exact ⟨hc, q, hq⟩
  · have hc := Completed.of_respOf_eq_some hr'
    have hne := (hP.2 x.1).learned_some x.2 q hx hc
    obtain ⟨⟨s, v⟩, hsv⟩ := Option.ne_none_iff_exists'.1 hne
    obtain ⟨-, ⟨q', hq', hr''⟩, -⟩ := learned_ok hcons hr hsv
    rw [hx, Option.some.injEq] at hq'
    cases hq'
    rw [hr', Option.some.injEq] at hr''
    exact ⟨s, by simp [learnedOf, hsv], hr''⟩
  · exact (hP.2 x.1).resp_upd x.2 u r hx hr'
  · obtain ⟨y, hy, -⟩ := theorem1 hcons hQS H C h hr x s hx u hu'
    exact ⟨y, hy⟩
  · obtain ⟨y', hy', hny⟩ := theorem1 hcons hQS H C h hr x s hx u hu'
    have := hu y y' u hy hy'
    subst this
    exact hny hp

/-- **Linearizability** of the repaired protocol (histories with unique update identifiers), for
every state-based CRDT with a causal history and every quorum system. -/
theorem fixed_linearizable (hQS : IsQuorumSystem QS) (H : D.CausalHistory) :
    LinearizableClaim (Variant.fixed (D := D)) QS := by
  intro C h hr hu
  exact linearizable_of_learnedHistory H (fixed_learnedHistory hQS H hr hu)

/-- **Non-vacuity** for the repaired protocol: in the first 24 steps of the counterexample run
(which are also steps of the repaired protocol), query `B` learns `{u₁}`; and the full run is
*not* an execution of the repaired protocol (`p₂` refuses to vote). -/
theorem fixed_nonvacuous :
    (∃ C h, (alg (Variant.fixed (D := Cex.G)) Cex.QS5).Reach C h ∧
      (C.loc 1).learned 0 = some ({0}, false)) ∧
    (alg (Variant.fixed (D := Cex.G)) Cex.QS5).runFrom
      (alg (Variant.fixed (D := Cex.G)) Cex.QS5).initCfg Cex.run = none := by
  refine ⟨?_, by decide⟩
  obtain ⟨C, hC, hl⟩ : ∃ C, (alg (Variant.fixed (D := Cex.G)) Cex.QS5).runFrom
      (alg (Variant.fixed (D := Cex.G)) Cex.QS5).initCfg (Cex.run.take 24) =
        some (C, Cex.runHist.take 6) ∧ (C.loc 1).learned 0 = some ({0}, false) := by
    refine ⟨_, rfl, ?_⟩; rfl
  exact ⟨C, _, by simpa using Protocol.runFrom_reach Protocol.Reach.init hC, hl⟩

end Podc.CRDTReplication
