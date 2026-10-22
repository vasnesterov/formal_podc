import Papers.PODC2019.CRDTReplication.AccInv

/-!
# Lemma 1, Corollary 1, Lemma 2, Lemma 4; Theorem 3 for the repaired protocol

These hold for every variant whose line-13 test implies equality (in particular for Algorithm 2
as written, `Variant.paper`), except Theorem 3 and Lemma 3, which need the repaired `VOTE` handler
(`Variant.fixed`); for `Variant.paper` they are false (`Counterexample.lean`).
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-- Two sets containing quorums intersect. -/
lemma HasQuorum.inter (hQS : IsQuorumSystem QS) {A B : Finset P} (hA : HasQuorum QS A)
    (hB : HasQuorum QS B) : ∃ a, a ∈ A ∧ a ∈ B := by
  obtain ⟨Q₁, hQ₁, h₁⟩ := hA
  obtain ⟨Q₂, hQ₂, h₂⟩ := hB
  obtain ⟨a, ha⟩ := hQS Q₁ hQ₁ Q₂ hQ₂
  exact ⟨a, h₁ (Finset.mem_inter.1 ha).1, h₂ (Finset.mem_inter.1 ha).2⟩

/-- **Lemma 1.** The payload of every acceptor grows monotonically. -/
theorem lemma1 : Lemma1 V QS := by
  intro C h C' st ℓ hr hs a
  rcases reach_step_cases hr hs with ⟨hloc, -, -⟩ | ⟨p, l, out, htr, hloc, -⟩
  · rw [hloc]
  · rw [hloc]
    by_cases hap : a = p
    · subst hap; rw [Function.update_self]
      rcases trans_acc htr with ⟨_, hle, _⟩ | ⟨_, _, _, _, _, _, hle, _⟩ |
        ⟨_, _, _, _, _, _, _, _, hle, _⟩
      · exact hle
      · rw [hle]; exact le_sup_left
      · rw [hle]; exact le_sup_left
    · rw [Function.update_of_ne hap]

/-- A message sent in a step by acceptor `a` (`ACK`) carries a state above `a`'s payload before
the step. -/
lemma new_ack_ge {C C' : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    {st : Step P D.spec (Msg P D) Act} {ℓ : Option (Label P D.spec)}
    (hr : (alg V QS).Reach C h) (hs : (alg V QS).step C st = some (C', ℓ))
    {a p : P} {n : ℕ} {i : Rid P} {s : D.S} (hm : (a, p, Msg.ack n i s) ∈ C'.sent)
    (hnm : (a, p, Msg.ack n i s) ∉ C.sent) : (C.loc a).s ≤ s := by
  rcases reach_step_cases hr hs with ⟨-, hsent, -⟩ | ⟨q, l, out, htr, -, hsent⟩
  · rw [hsent] at hm; exact absurd hm hnm
  · rw [hsent] at hm
    rcases Multiset.mem_add.1 hm with hm | hm
    · exact absurd hm hnm
    · have hq : a = q := (mem_outMsgs.1 hm).1
      subst hq
      have hout := (mem_outMsgs.1 hm).2
      rcases trans_acc htr with ⟨_, _, _, hacc⟩ | ⟨_, _, _, _, _, _, _, _, _, hout'⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, hout'⟩
      · exact absurd trivial (hacc _ hout)
      · rw [hout'] at hout
        simp only [Multiset.mem_singleton, Prod.mk.injEq, Msg.ack.injEq] at hout
        rw [hout.2.2.2]; exact le_sup_left
      · rw [hout'] at hout; simp at hout

/-- **Corollary 1.** `ACK`s of the same acceptor carry increasing states. -/
theorem corollary1 (hcons : ∀ s t, V.cons s t = true → s = t) : Corollary1 V QS := by
  intro C h ss C' h' hr hrun a p p' n n' i i' s s' hm hm' hnm
  induction ss generalizing C h h' with
  | nil =>
    simp only [Protocol.runFrom, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, -⟩ := hrun; exact absurd hm' hnm
  | cons st ss ih =>
    simp only [Protocol.runFrom, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hrun
    obtain ⟨⟨C₁, ℓ⟩, hs, ⟨⟨C₂, h₂⟩, hrun', he⟩⟩ := hrun
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    have hr₁ : (alg V QS).Reach C₁ (h ++ ℓ.toList) := Protocol.Reach.step hr hs
    have hle : C.sent ≤ C₁.sent := by
      rcases reach_step_cases hr hs with ⟨-, hsent, -⟩ | ⟨q, l, out, -, -, hsent⟩
      · rw [hsent]
      · rw [hsent]; exact Multiset.le_add_right _ _
    by_cases h₁ : (a, p', Msg.ack n' i' s') ∈ C₁.sent
    · have := new_ack_ge hr hs h₁ hnm
      exact ((accInv_of_reach hcons hr a).ack_inv p n i s hm).2.2.trans this
    · exact ih C₁ _ _ hr₁ hrun' (Multiset.mem_of_le hle hm) h₁

/-- Every learned state is certified by a quorum (`LearnedOK`). -/
lemma learned_ok (hcons : ∀ s t, V.cons s t = true → s = t) {C : Config P (Loc P D) (Msg P D)}
    {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h) {x : OpId P} {s : D.S} {v : Bool}
    (hx : (C.loc x.1).learned x.2 = some (s, v)) :
    Completed h x ∧ LearnedOK QS C.sent h x.1 x.2 s v :=
  ((procInv_of_reach hcons hr).2 x.1).learned x.2 s v hx

/-- A learned state was sent as a snapshot (`ACK` with state `s` or `VOTED(s)`) by every member of
a quorum. -/
lemma learned_snap (hcons : ∀ s t, V.cons s t = true → s = t) {C : Config P (Loc P D) (Msg P D)}
    {h : List (Label P D.spec)} (hr : (alg V QS).Reach C h) {s : D.S} {v : Bool}
    (hs : LearnedBy C s v) : ∃ A, HasQuorum QS A ∧ ∀ a ∈ A, Snap C.sent a s := by
  obtain ⟨x, hx⟩ := hs
  obtain ⟨-, -, i, -, -, hv, hc⟩ := (learned_ok hcons hr hx)
  cases v with
  | true =>
    obtain ⟨n, -, A, hA, hAv⟩ := hv rfl
    exact ⟨A, hA, fun a ha => Or.inr ⟨_, n, i, hAv a ha⟩⟩
  | false =>
    obtain ⟨A, hA, hAc⟩ := hc rfl
    exact ⟨A, hA, fun a ha => (hAc a ha).elim fun n hn => Or.inl ⟨_, n, i, hn⟩⟩

lemma learned_iff {C : Config P (Loc P D) (Msg P D)} {s : D.S} :
    Learned C s ↔ ∃ v, LearnedBy C s v := by
  constructor
  · rintro ⟨x, hx⟩
    simp only [learnedOf, Option.map_eq_some_iff] at hx
    obtain ⟨⟨s', v⟩, h1, rfl⟩ := hx
    exact ⟨v, x, h1⟩
  · rintro ⟨v, x, hx⟩
    exact ⟨x, by simp [learnedOf, hx]⟩

/-- **Lemma 2.** If `s` is learned, there is a quorum of acceptors whose payloads are above `s`. -/
theorem lemma2 (hcons : ∀ s t, V.cons s t = true → s = t) : Lemma2 V QS := by
  intro C h hr s hs
  obtain ⟨v, hv⟩ := learned_iff.1 hs
  obtain ⟨A, ⟨Q, hQ, hQA⟩, hA⟩ := learned_snap hcons hr hv
  exact ⟨Q, hQ, fun a ha => (accInv_of_reach hcons hr a).snap_le (hA a (hQA ha))⟩

/-- **Lemma 4.** Two states learned by vote are comparable. This holds for Algorithm 2 as
written. -/
theorem lemma4 (hcons : ∀ s t, V.cons s t = true → s = t) (hQS : IsQuorumSystem QS) :
    Lemma4 V QS := by
  intro C h hr s₁ s₂ hs₁ hs₂
  have hA := accInv_of_reach hcons hr
  obtain ⟨x₁, hx₁⟩ := hs₁
  obtain ⟨x₂, hx₂⟩ := hs₂
  obtain ⟨-, -, i₁, hi₁, hk₁, hv₁, -⟩ := learned_ok hcons hr hx₁
  obtain ⟨-, -, i₂, hi₂, hk₂, hv₂, -⟩ := learned_ok hcons hr hx₂
  obtain ⟨n₁, ⟨A₁, hA₁, hA₁a⟩, ⟨B₁, hB₁, hB₁v⟩⟩ := hv₁ rfl
  obtain ⟨n₂, ⟨A₂, hA₂, hA₂a⟩, ⟨B₂, hB₂, hB₂v⟩⟩ := hv₂ rfl
  -- the acceptor-side statement: a `VOTED` for `(n, i)` and an `ACK` with a larger number
  have key : ∀ {n i s n' i' s'} {B A : Finset P}, HasQuorum QS B → HasQuorum QS A →
      (∀ a ∈ B, (a, i.1, Msg.voted n i s) ∈ C.sent) →
      (∀ a ∈ A, ∃ σ, (a, i'.1, Msg.ack n' i' σ) ∈ C.sent ∧ σ ≤ s') → n < n' → s ≤ s' := by
    intro n i s n' i' s' B A hB hA' hBv hAa hlt
    obtain ⟨a, haB, haA⟩ := hB.inter hQS hA'
    obtain ⟨σ, hσ, hσs⟩ := hAa a haA
    exact ((hA a).voted_ack _ _ _ _ _ _ _ _ (hBv a haB) hσ hlt).trans hσs
  rcases lt_trichotomy n₁ n₂ with hlt | rfl | hlt
  · exact Or.inl (key hB₁ hA₂ hB₁v hA₂a hlt)
  · obtain ⟨a, haB, haA⟩ := hB₁.inter hQS hA₂
    obtain ⟨-, -, σ', hσ'⟩ := (hA a).voted_inv _ _ _ _ (hB₁v a haB)
    obtain ⟨σ, hσ, -⟩ := hA₂a a haA
    have hi : i₁ = i₂ := (hA a).ack_uniq _ _ _ _ _ _ _ hσ' hσ
    have hx : x₁ = x₂ := Prod.ext (by rw [← hi₁, ← hi₂, hi]) (by rw [← hk₁, ← hk₂, hi])
    subst hx
    rw [hx₁, Option.some.injEq, Prod.mk.injEq] at hx₂
    exact Or.inl hx₂.1.le
  · exact Or.inr (key hB₂ hA₁ hB₂v hA₁a hlt)

/-- **Theorem 3 (Consistency)** for the repaired protocol: any two learned states are
comparable. -/
theorem theorem3_fixed (hcons : ∀ s t, V.cons s t = true → s = t) (hfix : V.fix = true)
    (hQS : IsQuorumSystem QS) : Theorem3 V QS := by
  intro C h hr s₁ s₂ hs₁ hs₂
  obtain ⟨v₁, hv₁⟩ := learned_iff.1 hs₁
  obtain ⟨v₂, hv₂⟩ := learned_iff.1 hs₂
  obtain ⟨A₁, hA₁, h₁⟩ := learned_snap hcons hr hv₁
  obtain ⟨A₂, hA₂, h₂⟩ := learned_snap hcons hr hv₂
  obtain ⟨a, ha₁, ha₂⟩ := hA₁.inter hQS hA₂
  exact (accInv_of_reach hcons hr a).snap hfix _ _ (h₁ a ha₁) (h₂ a ha₂)

/-- **Lemma 3** for the repaired protocol (a special case of Theorem 3). -/
theorem lemma3_fixed (hcons : ∀ s t, V.cons s t = true → s = t) (hfix : V.fix = true)
    (hQS : IsQuorumSystem QS) : Lemma3 V QS := fun C h hr s₁ s₂ hs₁ hs₂ =>
  theorem3_fixed hcons hfix hQS C h hr s₁ s₂ (learned_iff.2 ⟨false, hs₁⟩) hs₂

end Podc.CRDTReplication
