import Mathlib

/-!
# Theorem 1: SRB implements the TrInc interface (Algorithm 2)

The implementation in the proof of Theorem 1: `Attest(c, m)` SRB-broadcasts `(c, m)`; a checker
`p` processes the messages of `q` in SRB order and *stores* `(k, c, m)` (the `k`-th message of `q`)
iff `C[q] < c`, where `C[q]` is the largest counter stored so far (initially `0`).
`CheckAttestation((k, c, m), q)` returns whether `(k, c, m)` is stored.

SRB delivers to every correct checker a prefix `L` of one common sequence `lq` (the log of `q`;
see `SRB.lean`), so the stored set at `p` is `accepted L`. We prove the properties of TrInc for
these stored sets:
* `accepted_prefix`: checkers agree — the stored lists of two correct checkers are prefixes of one
  another (consistency; "a Trinket does not produce two valid attestations …" holds globally);
* `accepted_counter_strictMono`: stored counters strictly increase, so no two valid attestations
  of `q` carry the same counter (non-equivocation);
* `accepted_sound`: a valid attestation `(k, c, m)` is the `k`-th message `q` broadcast (paper's
  property (2): `CheckAttestation(a, q)` is false unless `q` attested `a`; for correct `q`, SRB
  property 4);
* `accepted_complete`: if `q` is correct and attests with strictly increasing positive counters,
  every message of `q` delivered by `p` is valid at `p` (paper's property (1), with SRB property 1
  giving the eventual delivery);
* `accepted_prev`: the stored attestations form a chain: each one's predecessor in the stored list
  is the previous attestation (`prev` of Algorithm 2).
-/

namespace Podc.TrustedHW

namespace TrInc

variable {M : Type}

/-- The stored attestations `(k, c, m)` after processing `L`, starting at index `k₀` with stored
maximum `C`. -/
def acceptedFrom : ℕ → ℕ → List (ℕ × M) → List (ℕ × ℕ × M)
  | _, _, [] => []
  | C, k, (c, m) :: L =>
    if C < c then (k, c, m) :: acceptedFrom c (k + 1) L else acceptedFrom C (k + 1) L

/-- The stored attestations after processing the delivered prefix `L` (initially `C[q] = 0`). -/
def accepted (L : List (ℕ × M)) : List (ℕ × ℕ × M) := acceptedFrom 0 0 L

/-- The value of `C[q]` after processing `L`. -/
def maxFrom : ℕ → List (ℕ × M) → ℕ
  | C, [] => C
  | C, (c, _) :: L => maxFrom (max C c) L

lemma acceptedFrom_append (C k : ℕ) (L L' : List (ℕ × M)) :
    acceptedFrom C k (L ++ L') = acceptedFrom C k L ++ acceptedFrom (maxFrom C L) (k + L.length) L' := by
  induction L generalizing C k with
  | nil => simp [acceptedFrom, maxFrom]
  | cons a L ih =>
    obtain ⟨c, m⟩ := a
    simp only [List.cons_append, acceptedFrom, maxFrom, List.length_cons]
    split_ifs with h
    · rw [ih, max_eq_right h.le, show k + 1 + L.length = k + (L.length + 1) by omega]; rfl
    · rw [ih, max_eq_left (not_lt.1 h), show k + 1 + L.length = k + (L.length + 1) by omega]

/-- **Consistency**: delivering more never removes stored attestations, so the stored lists of
two correct checkers (prefixes of the same SRB log) are prefixes of one another. -/
theorem accepted_prefix {L L' lq : List (ℕ × M)} (h : L <+: lq) (h' : L' <+: lq) :
    accepted L <+: accepted L' ∨ accepted L' <+: accepted L := by
  have mono : ∀ {A B : List (ℕ × M)}, A <+: B → accepted A <+: accepted B := by
    intro A B hAB
    obtain ⟨T, rfl⟩ := hAB
    unfold accepted; rw [acceptedFrom_append]; exact List.prefix_append _ _
  rcases List.prefix_or_prefix_of_prefix h h' with h1 | h1
  · exact Or.inl (mono h1)
  · exact Or.inr (mono h1)

lemma acceptedFrom_lower {C k : ℕ} {L : List (ℕ × M)} {a : ℕ × ℕ × M}
    (ha : a ∈ acceptedFrom C k L) : C < a.2.1 ∧ k ≤ a.1 := by
  induction L generalizing C k with
  | nil => simp [acceptedFrom] at ha
  | cons b L ih =>
    obtain ⟨c, m⟩ := b
    simp only [acceptedFrom] at ha
    split_ifs at ha with h
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨h, le_rfl⟩
      · have := ih ha; exact ⟨h.trans this.1, by omega⟩
    · have := ih ha; exact ⟨this.1, by omega⟩

lemma acceptedFrom_pairwise (C k : ℕ) (L : List (ℕ × M)) :
    (acceptedFrom C k L).Pairwise (fun a b => a.2.1 < b.2.1 ∧ a.1 < b.1) := by
  induction L generalizing C k with
  | nil => simp [acceptedFrom]
  | cons b L ih =>
    obtain ⟨c, m⟩ := b
    simp only [acceptedFrom]
    split_ifs with h
    · refine List.Pairwise.cons (fun a ha => ?_) (ih _ _)
      have := acceptedFrom_lower ha; exact ⟨this.1, by simp at this ⊢; omega⟩
    · exact ih _ _

/-- **Non-equivocation**: stored counters (and indices) strictly increase along the stored list;
in particular two distinct valid attestations of `q` never share a counter. -/
theorem accepted_counter_strictMono (L : List (ℕ × M)) :
    (accepted L).Pairwise (fun a b => a.2.1 < b.2.1 ∧ a.1 < b.1) :=
  acceptedFrom_pairwise 0 0 L

/-- Two valid attestations (at the same or at different correct checkers) with the same counter
are equal. -/
theorem eq_of_counter_eq {L L' lq : List (ℕ × M)} (h : L <+: lq) (h' : L' <+: lq)
    {a b : ℕ × ℕ × M} (ha : a ∈ accepted L) (hb : b ∈ accepted L') (hc : a.2.1 = b.2.1) : a = b := by
  have key : ∀ {X : List (ℕ × ℕ × M)}, X.Pairwise (fun a b => a.2.1 < b.2.1 ∧ a.1 < b.1) →
      ∀ {a b}, a ∈ X → b ∈ X → a.2.1 = b.2.1 → a = b := by
    intro X hX
    induction X with
    | nil => intro a b ha; simp at ha
    | cons x X ih =>
      intro a b ha hb hc
      rw [List.pairwise_cons] at hX
      rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
      · rw [ha', hb']
      · subst ha'; have := (hX.1 b hb').1; omega
      · subst hb'; have := (hX.1 a ha').1; omega
      · exact ih hX.2 ha' hb' hc
  rcases accepted_prefix h h' with h1 | h1
  · exact key (accepted_counter_strictMono L') (h1.subset ha) hb hc
  · exact key (accepted_counter_strictMono L) ha (h1.subset hb) hc

lemma acceptedFrom_sound {C k : ℕ} {L : List (ℕ × M)} {a : ℕ × ℕ × M}
    (ha : a ∈ acceptedFrom C k L) : k ≤ a.1 ∧ L[a.1 - k]? = some a.2 := by
  induction L generalizing C k with
  | nil => simp [acceptedFrom] at ha
  | cons b L ih =>
    obtain ⟨c, m⟩ := b
    simp only [acceptedFrom] at ha
    have step : ∀ C', a ∈ acceptedFrom C' (k + 1) L →
        k ≤ a.1 ∧ ((c, m) :: L)[a.1 - k]? = some a.2 := by
      intro C' ha'
      obtain ⟨h1, h2⟩ := ih ha'
      obtain ⟨j, hj⟩ : ∃ j, a.1 - k = j + 1 := ⟨a.1 - (k + 1), by omega⟩
      refine ⟨by omega, ?_⟩
      rw [hj, List.getElem?_cons_succ, show j = a.1 - (k + 1) by omega]; exact h2
    split_ifs at ha with h
    · rcases List.mem_cons.1 ha with rfl | ha
      · simp
      · exact step _ ha
    · exact step _ ha

/-- **Soundness** (paper's property (2)): a valid attestation `(k, c, m)` of `q` is the `k`-th
message `q` SRB-broadcast. -/
theorem accepted_sound {L lq : List (ℕ × M)} (h : L <+: lq) {a : ℕ × ℕ × M}
    (ha : a ∈ accepted L) : lq[a.1]? = some a.2 := by
  obtain ⟨-, h2⟩ := acceptedFrom_sound ha
  simp only [Nat.sub_zero] at h2
  obtain ⟨t, rfl⟩ := h
  have : a.1 < L.length := by
    by_contra hh; rw [List.getElem?_eq_none (by omega)] at h2; cases h2
  rw [List.getElem?_append_left this, h2]

/-- **Completeness** (paper's property (1)): if the counters attested by `q` are positive and
strictly increasing (a correct `q` with the check of Algorithm 2), every delivered message of `q`
is a valid attestation. -/
theorem accepted_complete {L : List (ℕ × M)}
    (hinc : L.Pairwise (fun a b => a.1 < b.1)) (hpos : ∀ a ∈ L, 0 < a.1) :
    accepted L = L.zipIdx.map (fun x => (x.2, x.1.1, x.1.2)) := by
  suffices ∀ C k (L : List (ℕ × M)), L.Pairwise (fun a b => a.1 < b.1) → (∀ a ∈ L, C < a.1) →
      acceptedFrom C k L = (L.zipIdx k).map (fun x => (x.2, x.1.1, x.1.2)) from
    this 0 0 L hinc hpos
  intro C k L
  induction L generalizing C k with
  | nil => intros; simp [acceptedFrom]
  | cons b L ih =>
    intro hinc hpos
    obtain ⟨c, m⟩ := b
    rw [List.pairwise_cons] at hinc
    simp only [acceptedFrom, ite_eq_left (hpos _ List.mem_cons_self), List.zipIdx_cons, List.map_cons]
    rw [ih c (k + 1) hinc.2 (fun a ha => hinc.1 a ha)]

/-- The stored list is a chain: consecutive stored attestations have increasing counters, so the
`prev` field of Algorithm 2 (the previous stored counter) is determined consistently. -/
theorem accepted_prev (L : List (ℕ × M)) :
    (accepted L).IsChain (fun a b => a.2.1 < b.2.1) :=
  ((accepted_counter_strictMono L).imp (fun h => h.1)).isChain

/-- The implementation's `Attest` never returns `null`: if a correct `q` attests counter `2` and
then counter `1`, the second "attestation" `(1, 1, m)` is returned to `q` but is never valid at
any checker (Algorithm 2 requires `Attest` to return `null` here). -/
theorem attest_nonincreasing_invalid :
    accepted [(2, (7 : ℕ)), (1, 8)] = [(0, 2, 7)] := rfl

end TrInc

end Podc.TrustedHW
