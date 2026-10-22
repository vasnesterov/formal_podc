import Papers.PODC2019.CRDTReplication.ProcStep

/-!
# Acceptor invariants

`AccInv` collects what an acceptor `a` guarantees about the messages it has sent (`ACK`, `VOTED`):

* `ack_inv`: an `ACK((n, i), σ)` goes to the proposer of `i`, with `n ≤ rnr` and `σ ⊑ s`
  (in particular: Lemma 1 + Corollary 1, the states in `ACK`s are below the current payload);
* `ack_uniq`: two `ACK`s of `a` with the same round number have the same round id;
* `rid_inv`: the current round `(rnr, rid)` was acknowledged;
* `voted_inv`, `voted_ack`: a `VOTED(s)` for round `(n, i)` comes after the `ACK` for `(n, i)`, and
  every `ACK` with a larger round number carries a state above `s` (the Paxos-style invariant
  behind Lemma 4);
* `snap` (repaired variant only): all states sent by `a` in `ACK`s and `VOTED`s are pairwise
  comparable — they are payloads that `a` held at some time.
-/

set_option linter.unusedSectionVars false

namespace Podc.CRDTReplication

open Cslib.SharedMemory Cslib.AsyncMP

variable {P : Type} [Fintype P] [DecidableEq P] {D : CRDT}
variable {V : Variant D} {QS : Finset (Finset P)}

/-- `σ` was sent by acceptor `a` in an `ACK` or a `VOTED` (a "snapshot" of its payload). -/
def Snap (sent : Multiset (P × P × Msg P D)) (a : P) (σ : D.S) : Prop :=
  (∃ p n i, (a, p, Msg.ack n i σ) ∈ sent) ∨ (∃ p n i, (a, p, Msg.voted n i σ) ∈ sent)

/-- The invariant of acceptor `a` with local state `L`. -/
structure AccInv (V : Variant D) (sent : Multiset (P × P × Msg P D)) (a : P) (L : Loc P D) :
    Prop where
  ack_inv : ∀ p n i σ, (a, p, Msg.ack n i σ) ∈ sent → i.1 = p ∧ n ≤ L.rnr ∧ σ ≤ L.s
  ack_uniq : ∀ p p' n i i' σ σ', (a, p, Msg.ack n i σ) ∈ sent → (a, p', Msg.ack n i' σ') ∈ sent →
    i = i'
  rid_inv : ∀ i, L.rid = some i → ∃ σ, (a, i.1, Msg.ack L.rnr i σ) ∈ sent
  voted_inv : ∀ p n i s, (a, p, Msg.voted n i s) ∈ sent →
    n ≤ L.rnr ∧ s ≤ L.s ∧ ∃ σ, (a, i.1, Msg.ack n i σ) ∈ sent
  voted_ack : ∀ p p' n₁ i₁ s₁ n i σ, (a, p, Msg.voted n₁ i₁ s₁) ∈ sent →
    (a, p', Msg.ack n i σ) ∈ sent → n₁ < n → s₁ ≤ σ
  snap : V.fix = true → ∀ σ σ', Snap sent a σ → Snap sent a σ' → Comparable σ σ'

lemma AccInv.snap_le {sent : Multiset (P × P × Msg P D)} {a : P} {L : Loc P D}
    (hA : AccInv V sent a L) {σ : D.S} (hσ : Snap sent a σ) : σ ≤ L.s := by
  rcases hσ with ⟨p, n, i, hm⟩ | ⟨p, n, i, hm⟩
  · exact (hA.ack_inv p n i σ hm).2.2
  · exact (hA.voted_inv p n i σ hm).2.1

/-- Messages of `a` in `sent + outMsgs p out` for `p ≠ a` were already in `sent`. -/
lemma mem_of_ne {sent : Multiset (P × P × Msg P D)} {p a : P} {out : Multiset (P × Msg P D)}
    (hpa : p ≠ a) {x : P × P × Msg P D} (hx : x ∈ sent + outMsgs p out) (hxa : x.1 = a) :
    x ∈ sent := by
  rcases Multiset.mem_add.1 hx with hx | hx
  · exact hx
  · exact absurd ((mem_outMsgs.1 hx).1.symm.trans hxa) hpa

/-- Steps of other processes preserve the invariant of `a`. -/
lemma AccInv.other {sent : Multiset (P × P × Msg P D)} {p a : P} {L : Loc P D}
    {out : Multiset (P × Msg P D)} (hA : AccInv V sent a L) (hpa : p ≠ a) :
    AccInv V (sent + outMsgs p out) a L := by
  have hm : ∀ {x : P × P × Msg P D}, x ∈ sent + outMsgs p out → x.1 = a → x ∈ sent :=
    fun hx hxa => mem_of_ne hpa hx hxa
  have hsnap : ∀ σ, Snap (sent + outMsgs p out) a σ → Snap sent a σ := by
    rintro σ (⟨p', n, i, h⟩ | ⟨p', n, i, h⟩)
    · exact Or.inl ⟨p', n, i, hm h rfl⟩
    · exact Or.inr ⟨p', n, i, hm h rfl⟩
  have hle : sent ≤ sent + outMsgs p out := Multiset.le_add_right _ _
  refine ⟨fun p' n i σ h => hA.ack_inv p' n i σ (hm h rfl),
    fun p₁ p₂ n i i' σ σ' h1 h2 => hA.ack_uniq p₁ p₂ n i i' σ σ' (hm h1 rfl) (hm h2 rfl),
    fun i hi => (hA.rid_inv i hi).imp fun σ hσ => Multiset.mem_of_le hle hσ,
    fun p' n i s h => ?_, fun p₁ p₂ n₁ i₁ s₁ n i σ h1 h2 => hA.voted_ack p₁ p₂ n₁ i₁ s₁ n i σ
      (hm h1 rfl) (hm h2 rfl),
    fun hf σ σ' h1 h2 => hA.snap hf σ σ' (hsnap σ h1) (hsnap σ' h2)⟩
  obtain ⟨h1, h2, σ, h3⟩ := hA.voted_inv p' n i s (hm h rfl)
  exact ⟨h1, h2, σ, Multiset.mem_of_le hle h3⟩

/-- Steps of `a` itself preserve its invariant. -/
lemma AccInv.self {sent : Multiset (P × P × Msg P D)} {a : P} {l₀ l : Loc P D}
    {out : Multiset (P × Msg P D)} {ℓ : Option (Label P D.spec)} (hA : AccInv V sent a l₀)
    (hprep : ∀ src i n σ, (src, a, Msg.prepare i n σ) ∈ sent → i.1 = src)
    (htr : Trans V QS sent a l₀ l out ℓ) : AccInv V (sent + outMsgs a out) a l := by
  have hle : sent ≤ sent + outMsgs a out := Multiset.le_add_right _ _
  rcases trans_acc htr with ⟨hrnr, hs, hrid, hout⟩ | ⟨src, i, n, s', hm, hlt, hs, hrnr, hrid, rfl⟩ |
    ⟨src, n, i, s', hm, hn, hi, hfix, hs, hrnr, hrid, rfl⟩
  · -- no acceptor message
    have hold : ∀ {x : P × P × Msg P D}, x ∈ sent + outMsgs a out → x.2.2.IsAcc → x ∈ sent := by
      intro x hx hacc
      rcases Multiset.mem_add.1 hx with hx | hx
      · exact hx
      · exact absurd hacc (hout _ (mem_outMsgs.1 hx).2)
    have hsnap : ∀ σ, Snap (sent + outMsgs a out) a σ → Snap sent a σ := by
      rintro σ (⟨p', n, i, h⟩ | ⟨p', n, i, h⟩)
      · exact Or.inl ⟨p', n, i, hold h trivial⟩
      · exact Or.inr ⟨p', n, i, hold h trivial⟩
    refine ⟨fun p n i σ h => ?_, fun p₁ p₂ n i i' σ σ' h1 h2 =>
        hA.ack_uniq p₁ p₂ n i i' σ σ' (hold h1 trivial) (hold h2 trivial), fun i hi => ?_,
      fun p n i s h => ?_, fun p₁ p₂ n₁ i₁ s₁ n i σ h1 h2 =>
        hA.voted_ack p₁ p₂ n₁ i₁ s₁ n i σ (hold h1 trivial) (hold h2 trivial),
      fun hf σ σ' h1 h2 => hA.snap hf σ σ' (hsnap σ h1) (hsnap σ' h2)⟩
    · obtain ⟨h1, h2, h3⟩ := hA.ack_inv p n i σ (hold h trivial)
      exact ⟨h1, hrnr ▸ h2, h3.trans hs⟩
    · rcases hrid with hrid | hrid
      · rw [hrid] at hi
        obtain ⟨σ, hσ⟩ := hA.rid_inv i hi
        exact ⟨σ, by rw [hrnr]; exact Multiset.mem_of_le hle hσ⟩
      · rw [hrid] at hi; cases hi
    · obtain ⟨h1, h2, σ, h3⟩ := hA.voted_inv p n i s (hold h trivial)
      exact ⟨hrnr ▸ h1, h2.trans hs, σ, Multiset.mem_of_le hle h3⟩
  · -- accepted `PREPARE`: a new `ACK`
    have hsrc : i.1 = src := hprep src i n s' hm
    set n' := n.getD (l₀.rnr + 1) with hn'
    have hnew : ∀ {x : P × P × Msg P D}, x ∈ sent + outMsgs a {(src, Msg.ack n' i (l₀.s ⊔ s'))} →
        x ∈ sent ∨ x = (a, src, Msg.ack n' i (l₀.s ⊔ s')) := by
      intro x hx
      rcases Multiset.mem_add.1 hx with hx | hx
      · exact Or.inl hx
      · right; simpa [outMsgs] using hx
    have hsnap : ∀ σ, Snap (sent + outMsgs a {(src, Msg.ack n' i (l₀.s ⊔ s'))}) a σ →
        Snap sent a σ ∨ σ = l₀.s ⊔ s' := by
      rintro σ (⟨p', n₀, i₀, h⟩ | ⟨p', n₀, i₀, h⟩)
      · rcases hnew h with h | h
        · exact Or.inl (Or.inl ⟨p', n₀, i₀, h⟩)
        · simp only [Prod.mk.injEq, Msg.ack.injEq] at h; exact Or.inr h.2.2.2.2
      · rcases hnew h with h | h
        · exact Or.inl (Or.inr ⟨p', n₀, i₀, h⟩)
        · simp at h
    refine ⟨fun p n₀ i₀ σ h => ?_, fun p₁ p₂ n₀ i₁ i₂ σ₁ σ₂ h1 h2 => ?_, fun i₀ hi₀ => ?_,
      fun p n₀ i₀ s₀ h => ?_, fun p₁ p₂ n₁ i₁ s₁ n₀ i₀ σ h1 h2 hlt' => ?_,
      fun hf σ σ' h1 h2 => ?_⟩
    · rcases hnew h with h | h
      · obtain ⟨h1, h2, h3⟩ := hA.ack_inv p n₀ i₀ σ h
        exact ⟨h1, by rw [hrnr]; omega, by rw [hs]; exact h3.trans le_sup_left⟩
      · simp only [Prod.mk.injEq, Msg.ack.injEq] at h
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨hsrc, by rw [hrnr], by rw [hs]⟩
    · rcases hnew h1 with h1 | h1 <;> rcases hnew h2 with h2 | h2
      · exact hA.ack_uniq p₁ p₂ n₀ i₁ i₂ σ₁ σ₂ h1 h2
      · simp only [Prod.mk.injEq, Msg.ack.injEq] at h2
        obtain ⟨-, -, rfl, -, -⟩ := h2
        have := (hA.ack_inv p₁ _ i₁ σ₁ h1).2.1; omega
      · simp only [Prod.mk.injEq, Msg.ack.injEq] at h1
        obtain ⟨-, -, rfl, -, -⟩ := h1
        have := (hA.ack_inv p₂ _ i₂ σ₂ h2).2.1; omega
      · simp only [Prod.mk.injEq, Msg.ack.injEq] at h1 h2
        rw [h1.2.2.2.1, h2.2.2.2.1]
    · rw [hrid, Option.some.injEq] at hi₀; subst hi₀
      refine ⟨l₀.s ⊔ s', Multiset.mem_add.2 (Or.inr ?_)⟩
      rw [hrnr, hsrc]; simp [outMsgs]
    · rcases hnew h with h | h
      · obtain ⟨h1, h2, σ, h3⟩ := hA.voted_inv p n₀ i₀ s₀ h
        exact ⟨by rw [hrnr]; omega, by rw [hs]; exact h2.trans le_sup_left, σ,
          Multiset.mem_of_le hle h3⟩
      · simp at h
    · rcases hnew h1 with h1 | h1
      · rcases hnew h2 with h2 | h2
        · exact hA.voted_ack p₁ p₂ n₁ i₁ s₁ n₀ i₀ σ h1 h2 hlt'
        · simp only [Prod.mk.injEq, Msg.ack.injEq] at h2
          obtain ⟨-, -, -, -, rfl⟩ := h2
          exact (hA.voted_inv p₁ n₁ i₁ s₁ h1).2.1.trans le_sup_left
      · simp at h1
    · have hle' : ∀ τ, Snap sent a τ → τ ≤ l₀.s ⊔ s' := fun τ hτ => (hA.snap_le hτ).trans le_sup_left
      rcases hsnap σ h1 with h1 | rfl <;> rcases hsnap σ' h2 with h2 | rfl
      · exact hA.snap hf σ σ' h1 h2
      · exact Or.inl (hle' σ h1)
      · exact Or.inr (hle' σ' h2)
      · exact Or.inl le_rfl
  · -- accepted `VOTE`: a new `VOTED`
    have hnew : ∀ {x : P × P × Msg P D}, x ∈ sent + outMsgs a {(src, Msg.voted n i s')} →
        x ∈ sent ∨ x = (a, src, Msg.voted n i s') := by
      intro x hx
      rcases Multiset.mem_add.1 hx with hx | hx
      · exact Or.inl hx
      · right; simpa [outMsgs] using hx
    refine ⟨fun p n₀ i₀ σ h => ?_, fun p₁ p₂ n₀ i₁ i₂ σ₁ σ₂ h1 h2 => ?_, fun i₀ hi₀ => ?_,
      fun p n₀ i₀ s₀ h => ?_, fun p₁ p₂ n₁ i₁ s₁ n₀ i₀ σ h1 h2 hlt' => ?_,
      fun hf σ σ' h1 h2 => ?_⟩
    · rcases hnew h with h | h
      · obtain ⟨h1, h2, h3⟩ := hA.ack_inv p n₀ i₀ σ h
        exact ⟨h1, hrnr ▸ h2, by rw [hs]; exact h3.trans le_sup_left⟩
      · simp at h
    · rcases hnew h1 with h1 | h1
      · rcases hnew h2 with h2 | h2
        · exact hA.ack_uniq p₁ p₂ n₀ i₁ i₂ σ₁ σ₂ h1 h2
        · simp at h2
      · simp at h1
    · rw [hrid] at hi₀
      obtain ⟨σ, hσ⟩ := hA.rid_inv i₀ hi₀
      exact ⟨σ, by rw [hrnr]; exact Multiset.mem_of_le hle hσ⟩
    · rcases hnew h with h | h
      · obtain ⟨h1, h2, σ, h3⟩ := hA.voted_inv p n₀ i₀ s₀ h
        exact ⟨hrnr ▸ h1, by rw [hs]; exact h2.trans le_sup_left, σ, Multiset.mem_of_le hle h3⟩
      · simp only [Prod.mk.injEq, Msg.voted.injEq] at h
        obtain ⟨-, -, rfl, rfl, rfl⟩ := h
        obtain ⟨σ, hσ⟩ := hA.rid_inv _ hi
        exact ⟨by rw [hrnr, hn], by rw [hs]; exact le_sup_right, σ, by
          have := Multiset.mem_of_le hle hσ; rwa [hn] at this⟩
    · rcases hnew h2 with h2' | h2'
      · rcases hnew h1 with h1' | h1'
        · exact hA.voted_ack p₁ p₂ n₁ i₁ s₁ n₀ i₀ σ h1' h2' hlt'
        · simp only [Prod.mk.injEq, Msg.voted.injEq] at h1'
          have := (hA.ack_inv p₂ n₀ i₀ σ h2').2.1; omega
      · simp at h2'
    · have hs' : l.s = s' := by rw [hs]; exact sup_eq_right.2 (hfix hf)
      have hsnap : ∀ τ, Snap (sent + outMsgs a {(src, Msg.voted n i s')}) a τ →
          Snap sent a τ ∨ τ = s' := by
        rintro τ (⟨p', n₀, i₀, h⟩ | ⟨p', n₀, i₀, h⟩)
        · rcases hnew h with h | h
          · exact Or.inl (Or.inl ⟨p', n₀, i₀, h⟩)
          · simp at h
        · rcases hnew h with h | h
          · exact Or.inl (Or.inr ⟨p', n₀, i₀, h⟩)
          · simp only [Prod.mk.injEq, Msg.voted.injEq] at h; exact Or.inr h.2.2.2.2
      have hle' : ∀ τ, Snap sent a τ → τ ≤ s' := fun τ hτ => (hA.snap_le hτ).trans (hfix hf)
      rcases hsnap σ h1 with h1' | rfl <;> rcases hsnap σ' h2 with h2' | rfl
      · exact hA.snap hf σ σ' h1' h2'
      · exact Or.inl (hle' σ h1')
      · exact Or.inr (hle' σ' h2')
      · exact Or.inl le_rfl

/-- The acceptor invariant holds for every acceptor in every reachable configuration. -/
theorem accInv_of_reach (hcons : ∀ s t, V.cons s t = true → s = t)
    {C : Config P (Loc P D) (Msg P D)} {h : List (Label P D.spec)}
    (hr : (alg V QS).Reach C h) : ∀ a, AccInv V C.sent a (C.loc a) := by
  induction hr with
  | init =>
    intro a
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Protocol.initCfg, alg, initLoc, Snap]
  | @step C₀ h₀ st C' ℓ hr hs ih =>
    have hP := (procInv_of_reach hcons hr).2
    rcases reach_step_cases hr hs with ⟨hloc, hsent, -⟩ | ⟨p, l, out, htr, hloc, hsent⟩
    · intro a; rw [hloc, hsent]; exact ih a
    · intro a
      rw [hloc, hsent]
      by_cases hpa : a = p
      · subst hpa
        rw [Function.update_self]
        exact (ih a).self (fun src i n σ hm => ((hP src).prep_id a i n σ hm).1.symm ▸ rfl) htr
      · rw [Function.update_of_ne hpa]
        exact (ih a).other (Ne.symm hpa)

end Podc.CRDTReplication
