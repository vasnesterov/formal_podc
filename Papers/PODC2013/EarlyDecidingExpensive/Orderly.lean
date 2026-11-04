import Papers.PODC2013.EarlyDecidingExpensive.Model

/-!
# The orderly-crash algorithm (Dolev–Lenzen, PODC 2013, Section 4, Theorem 4.5)

Nodes are `Fin n` (the paper's node `i` is our `i - 1`); messages are bits. With `t` the
resilience:

1. A node that receives a message containing `b` decides `b`.
2. A node `i ≤ t` (0-based) that has received nothing in rounds `1, …, i` decides its input at
   the beginning of round `i + 1` (i.e. after `i` rounds).
3. A node `i ≤ t` that decided after round `k - 1` (at the end of round `k - 1` or the beginning
   of round `k`) sends its value to all nodes `i + 1, …, n - 1`, in this order, in round `k`.

Orderly crashes are taken with respect to this order (`rank p k q = q`): a crashing node
delivers its messages to the nodes `q < m` for some `m`.
-/

namespace Podc.EarlyDecidingExpensive.Orderly

open Finset

variable {n : ℕ}

/-- The value of a message in an inbox (the first sender in the order of ids). -/
def firstVal (ib : Fin n → Option Bool) : Option Bool := (List.finRange n).findSome? ib

/-- Decision rule: own input if `i ≤ t` and nothing was received in the first `i` rounds,
otherwise the value of the first message received. -/
def dec (t : ℕ) (i : Fin n) (x : Bool) (h : History (Fin n) Bool) : Option Bool :=
  if i.val ≤ t ∧ i.val ≤ h.length ∧ ∀ ib ∈ h.take i.val, firstVal ib = none then some x
  else h.findSome? firstVal

/-- The algorithm of Section 4. -/
def alg (t : ℕ) : Algorithm (Fin n) Bool where
  send i x h q :=
    if i.val ≤ t ∧ i < q ∧ (h = [] ∨ dec t i x h.dropLast = none) then dec t i x h else none
  decide := dec t

/-- The order in which a node sends its messages: by increasing id. -/
def rank (_ : Fin n) (_ : ℕ) (q : Fin n) : ℕ := q.val

/-! ### First receipts -/

lemma firstVal_eq_none_iff {ib : Fin n → Option Bool} : firstVal ib = none ↔ ∀ p, ib p = none := by
  simp [firstVal, List.findSome?_eq_none_iff]

lemma exists_of_firstVal_eq_some {ib : Fin n → Option Bool} {v : Bool}
    (h : firstVal ib = some v) : ∃ p, ib p = some v := by
  obtain ⟨p, -, hp⟩ := List.exists_of_findSome?_eq_some h
  exact ⟨p, hp⟩

/-- The value of the first message received within the first `L` rounds. -/
def recv (A : Algorithm (Fin n) Bool) (E : Execution (Fin n) Bool) (L : ℕ) (q : Fin n) :
    Option Bool :=
  (hist A E L q).findSome? firstVal

section Recv

variable {A : Algorithm (Fin n) Bool} {E : Execution (Fin n) Bool}

@[simp] lemma recv_zero (q : Fin n) : recv A E 0 q = none := rfl

lemma recv_succ (L : ℕ) (q : Fin n) :
    recv A E (L + 1) q = (recv A E L q).or (firstVal fun p => msg A E (L + 1) p q) := by
  simp [recv, hist_succ, List.findSome?_append]

lemma recv_eq_none_iff {L : ℕ} {q : Fin n} :
    recv A E L q = none ↔ ∀ k, 1 ≤ k → k ≤ L → ∀ p, msg A E k p q = none := by
  induction L with
  | zero => simp only [recv_zero, true_iff]; intro k h1 h2; omega
  | succ L ih =>
    rw [recv_succ, Option.or_eq_none_iff, ih, firstVal_eq_none_iff]
    constructor
    · rintro ⟨h1, h2⟩ k hk1 hk2 p
      rcases Nat.lt_or_ge k (L + 1) with h | h
      · exact h1 k hk1 (by omega) p
      · obtain rfl : k = L + 1 := by omega
        exact h2 p
    · intro h
      exact ⟨fun k hk1 hk2 p => h k hk1 (by omega) p, fun p => h (L + 1) (by omega) le_rfl p⟩

lemma exists_of_recv_eq_some {L : ℕ} {q : Fin n} {v : Bool} (h : recv A E L q = some v) :
    ∃ k p, 1 ≤ k ∧ k ≤ L ∧ msg A E k p q = some v := by
  induction L with
  | zero => simp at h
  | succ L ih =>
    rw [recv_succ] at h
    cases hr : recv A E L q with
    | some w =>
      rw [hr] at h
      simp only [Option.some_or, Option.some_inj] at h
      subst h
      obtain ⟨k, p, h1, h2, h3⟩ := ih hr
      exact ⟨k, p, h1, by omega, h3⟩
    | none =>
      rw [hr] at h
      simp only [Option.none_or] at h
      obtain ⟨p, hp⟩ := exists_of_firstVal_eq_some h
      exact ⟨L + 1, p, by omega, le_rfl, hp⟩

lemma recv_mono {j L : ℕ} {q : Fin n} {v : Bool} (h : recv A E j q = some v) (hjL : j ≤ L) :
    recv A E L q = some v := by
  induction L, hjL using Nat.le_induction with
  | base => exact h
  | succ L _ ih => rw [recv_succ, ih]; rfl

lemma recv_isSome_of_msg {k : ℕ} {p q : Fin n} {v : Bool} (hk : 1 ≤ k)
    (h : msg A E k p q = some v) : ∃ w, recv A E k q = some w := by
  cases hr : recv A E k q with
  | some w => exact ⟨w, rfl⟩
  | none => rw [recv_eq_none_iff] at hr; simp [hr k hk le_rfl p] at h

end Recv

/-! ### The decision rule along an execution -/

section Status

variable {t : ℕ} {E : Execution (Fin n) Bool}

/-- `p` decides its own input: `p ≤ t` and it receives nothing in rounds `1, …, p`. -/
def Own (t : ℕ) (E : Execution (Fin n) Bool) (p : Fin n) : Prop :=
  p.val ≤ t ∧ recv (alg t) E p.val p = none

lemma status_eq (L : ℕ) (p : Fin n) : status (alg t) E L p =
    if p.val ≤ t ∧ p.val ≤ L ∧ recv (alg t) E p.val p = none then some (E.input p)
    else recv (alg t) E L p := by
  show dec t p (E.input p) (hist (alg t) E L p) = _
  unfold dec
  rw [length_hist]
  by_cases h : p.val ≤ t ∧ p.val ≤ L
  · have e : (∀ ib ∈ (hist (alg t) E L p).take p.val, firstVal ib = none) ↔
        recv (alg t) E p.val p = none := by
      rw [hist_take E h.2, recv, List.findSome?_eq_none_iff]
    by_cases hr : recv (alg t) E p.val p = none
    · rw [ite_eq_left ⟨h.1, h.2, e.2 hr⟩, ite_eq_left ⟨h.1, h.2, hr⟩]
    · rw [ite_eq_right (fun h' => hr (e.1 h'.2.2)), ite_eq_right (fun h' => hr h'.2.2)]; rfl
  · have h1 : ¬ (p.val ≤ t ∧ p.val ≤ L ∧ ∀ ib ∈ (hist (alg t) E L p).take p.val,
        firstVal ib = none) := fun h' => h ⟨h'.1, h'.2.1⟩
    have h2 : ¬ (p.val ≤ t ∧ p.val ≤ L ∧ recv (alg t) E p.val p = none) :=
      fun h' => h ⟨h'.1, h'.2.1⟩
    rw [ite_eq_right h1, ite_eq_right h2]
    rfl

lemma status_mono {L L' : ℕ} {p : Fin n} {b : Bool} (h : status (alg t) E L p = some b)
    (hL : L ≤ L') : status (alg t) E L' p = some b := by
  rw [status_eq] at h ⊢
  split_ifs at h with h1
  · rw [ite_eq_left ⟨h1.1, h1.2.1.trans hL, h1.2.2⟩]; exact h
  · rw [ite_eq_right]
    · exact recv_mono h hL
    · rintro ⟨h2, h3, h4⟩
      by_cases hpL : p.val ≤ L
      · exact h1 ⟨h2, hpL, h4⟩
      · rw [recv_mono h (by omega : L ≤ p.val)] at h4; simp at h4

lemma status_isSome_of_recv {L : ℕ} {p : Fin n} {w : Bool} (h : recv (alg t) E L p = some w) :
    ∃ b, status (alg t) E L p = some b := by
  rw [status_eq]; split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨w, h⟩

lemma status_isSome_of_msg {k : ℕ} {p q : Fin n} {v : Bool} (hk : 1 ≤ k)
    (h : msg (alg t) E k p q = some v) : ∃ b, status (alg t) E k q = some b := by
  obtain ⟨w, hw⟩ := recv_isSome_of_msg hk h
  exact status_isSome_of_recv hw

lemma status_self_isSome {p : Fin n} (hp : p.val ≤ t) : ∃ b, status (alg t) E p.val p = some b := by
  cases hr : recv (alg t) E p.val p with
  | none => exact ⟨E.input p, by rw [status_eq, ite_eq_left ⟨hp, le_rfl, hr⟩]⟩
  | some w => exact status_isSome_of_recv hr

lemma exists_decidesAt {L : ℕ} {p : Fin n} {b : Bool} (h : status (alg t) E L p = some b) :
    ∃ L' ≤ L, DecidesAt (alg t) E p L' b := by
  classical
  have hex : ∃ j, (status (alg t) E j p).isSome := ⟨L, by simp [h]⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (by simp [h]), ?_, fun j hj => ?_⟩
  · obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (Nat.find_spec hex)
    rw [hb', ← h, status_mono hb' (Nat.find_min' hex (by simp [h]))]
  · have := Nat.find_min hex hj
    simpa using this

lemma own_decidesAt {p : Fin n} (h : Own t E p) : DecidesAt (alg t) E p p.val (E.input p) := by
  refine ⟨by rw [status_eq, ite_eq_left ⟨h.1, le_rfl, h.2⟩], fun j hj => ?_⟩
  rw [status_eq, ite_eq_right (by omega), recv_eq_none_iff]
  intro k hk1 hk2 p'
  exact recv_eq_none_iff.1 h.2 k hk1 (by omega) p'

/-- A first decision is either an own decision (after `p` rounds) or the value of a message
received in the round of the decision. -/
lemma decidesAt_cases {L : ℕ} {p : Fin n} {v : Bool} (h : DecidesAt (alg t) E p L v) :
    (L = p.val ∧ Own t E p ∧ v = E.input p) ∨
      (1 ≤ L ∧ ∃ p', msg (alg t) E L p' p = some v) := by
  obtain ⟨h1, h2⟩ := h
  rw [status_eq] at h1
  split_ifs at h1 with hc
  · left
    refine ⟨?_, ⟨hc.1, hc.2.2⟩, (Option.some_injective _ h1).symm⟩
    by_contra hne
    have := h2 p.val (by omega)
    rw [status_eq, ite_eq_left ⟨hc.1, le_rfl, hc.2.2⟩] at this
    simp at this
  · right
    obtain ⟨k, p', hk1, hk2, hk⟩ := exists_of_recv_eq_some h1
    rcases Nat.lt_or_ge k L with hkL | hkL
    · obtain ⟨b, hb⟩ := status_isSome_of_msg hk1 hk
      simp [h2 k hkL] at hb
    · obtain rfl : k = L := by omega
      exact ⟨hk1, p', hk⟩

end Status

/-! ### Messages -/

section Messages

variable {t : ℕ} {E : Execution (Fin n) Bool}

lemma hist_dropLast (L : ℕ) (q : Fin n) :
    (hist (alg t) E L q).dropLast = hist (alg t) E (L - 1) q := by
  cases L with
  | zero => rfl
  | succ L => rw [hist_succ, List.dropLast_concat]; rfl

lemma hmsg_eq (L : ℕ) (p q : Fin n) : hmsg (alg t) E (L + 1) p q =
    if p.val ≤ t ∧ p < q ∧ (L = 0 ∨ status (alg t) E (L - 1) p = none)
    then status (alg t) E L p else none := by
  unfold hmsg
  simp only [Nat.add_sub_cancel]
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [ite_eq_right hpq]
    show (if _ then _ else _) = _
    rw [hist_dropLast]
    have h0 : hist (alg t) E L p = [] ↔ L = 0 := by
      rw [← List.length_eq_zero_iff, length_hist]
    simp only [h0]
    rfl

lemma hmsg_eq_some_iff {L : ℕ} {p q : Fin n} {v : Bool} :
    hmsg (alg t) E (L + 1) p q = some v ↔ p.val ≤ t ∧ p < q ∧ DecidesAt (alg t) E p L v := by
  rw [hmsg_eq]
  constructor
  · intro h
    split_ifs at h with hc
    refine ⟨hc.1, hc.2.1, h, fun j hj => ?_⟩
    cases hs : status (alg t) E j p with
    | none => rfl
    | some w =>
      rcases hc.2.2 with h0 | h0
      · omega
      · rw [status_mono hs (by omega : j ≤ L - 1)] at h0; simp at h0
  · rintro ⟨h1, h2, h3⟩
    have h4 : L = 0 ∨ status (alg t) E (L - 1) p = none := by
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h3.2 _ (by omega))
    rw [ite_eq_left ⟨h1, h2, h4⟩]
    exact h3.1

lemma hmsg_congr_right {k : ℕ} {p q q' : Fin n} (hq : p < q) (hq' : p < q') :
    hmsg (alg t) E k p q = hmsg (alg t) E k p q' := by
  simp [hmsg, alg, hq.ne, hq'.ne, hq, hq']

variable (hE : orderlyAdm (alg t) rank t E)
include hE

/-- In an orderly-crash execution, every message is either missing or the algorithm message. -/
lemma msg_cases (k : ℕ) (p q : Fin n) :
    msg (alg t) E k p q = none ∨ msg (alg t) E k p q = hmsg (alg t) E k p q := by
  by_cases hf : E.FaultyAt k p
  · obtain ⟨h1, m, h2⟩ := hE.2 p hf.1
    rcases Nat.lt_or_ge (E.fr p) k with hk | hk
    · exact Or.inl (h1 k q hk)
    · obtain hfr : E.fr p = k := le_antisymm hf.2 hk
      rw [← hfr, h2 q]
      split_ifs <;> simp
  · exact Or.inr (msg_of_not_faultyAt hf q)

/-- (F1): a message in round `k` is the value of a node `p ≤ t` that first decided after round
`k - 1`, sent to a node with a larger id. -/
lemma msg_eq_some {k : ℕ} {p q : Fin n} {v : Bool} (hk : 1 ≤ k)
    (h : msg (alg t) E k p q = some v) :
    p.val ≤ t ∧ p < q ∧ DecidesAt (alg t) E p (k - 1) v := by
  rcases msg_cases hE k p q with h' | h'
  · simp [h'] at h
  · rw [h', show k = (k - 1) + 1 by omega, hmsg_eq_some_iff] at h
    exact h

/-- (O): crashes are orderly with respect to the ids. -/
lemma msg_orderly {k : ℕ} {p q q' : Fin n} {v : Bool} (h : msg (alg t) E k p q = some v)
    (hpq' : p < q') (hq' : q' < q) : msg (alg t) E k p q' = some v := by
  by_cases hf : E.FaultyAt k p
  · obtain ⟨h1, m, h2⟩ := hE.2 p hf.1
    rcases Nat.lt_or_ge (E.fr p) k with hk | hk
    · simp [h1 k q hk] at h
    · obtain hfr : E.fr p = k := le_antisymm hf.2 hk
      rw [← hfr] at h ⊢
      rw [h2 q] at h
      rw [h2 q']
      split_ifs at h with hm
      · rw [ite_eq_left (lt_trans (show rank p (E.fr p) q' < rank p (E.fr p) q from hq') hm), ← h]
        exact hmsg_congr_right hpq' (hpq'.trans hq')
  · rw [msg_of_not_faultyAt hf] at h ⊢
    rw [← h]
    exact hmsg_congr_right hpq' (hpq'.trans hq')

/-- (T): a node `p` sends only in rounds `≤ p + 1`. -/
lemma msg_round_le {k : ℕ} {p q : Fin n} {v : Bool} (hk : 1 ≤ k)
    (h : msg (alg t) E k p q = some v) : k ≤ p.val + 1 := by
  induction k using Nat.strong_induction_on generalizing p q v with
  | _ k ih =>
    obtain ⟨-, -, hd⟩ := msg_eq_some hE hk h
    rcases decidesAt_cases hd with ⟨h1, -⟩ | ⟨h1, p', hp'⟩
    · omega
    · have h2 := ih (k - 1) (by omega) h1 hp'
      have h3 := (msg_eq_some hE h1 hp').2.1
      rw [Fin.lt_def] at h3
      omega

/-- Agreement and validity: all never-faulty nodes decide the input of the largest node that
decides its own input. -/
lemma exists_decision_value (q₀ : Fin n) :
    ∃ i₀ : Fin n, ∀ p ∉ E.F, ∀ L b, DecidesAt (alg t) E p L b → b = E.input i₀ := by
  classical
  have h0 : (⟨0, q₀.pos⟩ : Fin n) ∈ univ.filter (Own t E) := by
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨Nat.zero_le _, rfl⟩
  set i₀ := (univ.filter (Own t E)).max' ⟨_, h0⟩ with hi₀
  have hown : Own t E i₀ := by
    have := (univ.filter (Own t E)).max'_mem ⟨_, h0⟩
    simpa [← hi₀] using this
  have hmax : ∀ p, Own t E p → p ≤ i₀ := fun p hp =>
    (univ.filter (Own t E)).le_max' p (by simpa using hp)
  have hnone : ∀ k, 1 ≤ k → k ≤ i₀.val → ∀ p, msg (alg t) E k p i₀ = none :=
    recv_eq_none_iff.1 hown.2
  -- every message delivered to a node above `i₀` carries the input of `i₀`
  have hinv : ∀ k, 1 ≤ k → ∀ p q v, msg (alg t) E k p q = some v → i₀ < q → v = E.input i₀ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk p q v h hq
      obtain ⟨-, -, hd⟩ := msg_eq_some hE hk h
      rcases lt_trichotomy p i₀ with hp | rfl | hp
      · have h' := msg_orderly hE h hp hq
        have hk' := msg_round_le hE hk h'
        rw [Fin.lt_def] at hp
        simp [hnone k hk (by omega) p] at h'
      · exact ((own_decidesAt hown).unique hd).2.symm
      · rcases decidesAt_cases hd with ⟨-, ho, -⟩ | ⟨h1, p', hp'⟩
        · exact absurd (hmax p ho) (not_le.2 hp)
        · exact ih (k - 1) (by omega) h1 p' p v hp' hp
  have hge : ∀ p ∉ E.F, i₀ ≤ p := by
    intro p hp
    by_contra hlt
    rw [not_le] at hlt
    have hlt' := Fin.lt_def.1 hlt
    obtain ⟨w, hw⟩ := status_self_isSome (t := t) (E := E) (p := p) (by have := hown.1; omega)
    obtain ⟨L, hL, hd⟩ := exists_decidesAt hw
    have hm : hmsg (alg t) E (L + 1) p i₀ = some w :=
      hmsg_eq_some_iff.2 ⟨by have := hown.1; omega, hlt, hd⟩
    rw [← msg_of_not_faultyAt (Execution.not_faultyAt_of_not_mem hp)] at hm
    simp [hnone (L + 1) (by omega) (by omega) p] at hm
  refine ⟨i₀, fun p hp L b hd => ?_⟩
  rcases (hge p hp).lt_or_eq with hlt | rfl
  · rcases decidesAt_cases hd with ⟨-, ho, -⟩ | ⟨h1, p', hp'⟩
    · exact absurd (hmax p ho) (not_le.2 hlt)
    · exact hinv L h1 p' p b hp' hlt
  · exact ((own_decidesAt hown).unique hd).2.symm

/-- The smallest node `c` that is not faulty in round `f + 1` decides after `L ≤ f` rounds and
delivers its value to all larger nodes in round `L + 1`. -/
lemma exists_sender (q : Fin n) (hq : ¬ E.FaultyAt (E.F.card + 1) q) :
    ∃ c ≤ q, ∃ L ≤ E.F.card, ∃ w, DecidesAt (alg t) E c L w ∧
      ∀ q', c < q' → msg (alg t) E (L + 1) c q' = some w := by
  classical
  set S := univ.filter fun p => ¬ E.FaultyAt (E.F.card + 1) p
  have hqS : q ∈ S := by simpa [S] using hq
  set c := S.min' ⟨q, hqS⟩ with hc
  have hcS : ¬ E.FaultyAt (E.F.card + 1) c := by
    have := S.min'_mem ⟨q, hqS⟩
    simpa [S, ← hc] using this
  have hlow : Iio c ⊆ E.F := by
    intro p hp
    rw [mem_Iio] at hp
    by_contra hpF
    have : c ≤ p := S.min'_le p (by simpa [S] using Execution.not_faultyAt_of_not_mem hpF)
    exact absurd hp (not_lt.2 this)
  have hcf : c.val ≤ E.F.card := by
    have := card_le_card hlow
    rwa [Fin.card_Iio] at this
  obtain ⟨w, hw⟩ := status_self_isSome (t := t) (E := E) (p := c) (by have := hE.1; omega)
  obtain ⟨L, hL, hd⟩ := exists_decidesAt hw
  refine ⟨c, S.min'_le q hqS, L, by omega, w, hd, fun q' hq' => ?_⟩
  have hnf : ¬ E.FaultyAt (L + 1) c := fun h => hcS (h.mono (by omega))
  rw [msg_of_not_faultyAt hnf]
  exact hmsg_eq_some_iff.2 ⟨by have := hE.1; omega, hq', hd⟩

/-- A node sends in at most one round, to the nodes with larger ids, and only if its id is at
most `t`. -/
lemma sum_card_sentTo_le (R : ℕ) (p : Fin n) :
    ∑ k ∈ Icc 1 R, (sentTo (alg t) E k p).card ≤ if p.val ≤ t then n - 1 - p.val else 0 := by
  classical
  have hmem : ∀ k q, q ∈ sentTo (alg t) E k p → ∃ v, msg (alg t) E k p q = some v := by
    intro k q hq
    simpa [sentTo, Option.isSome_iff_exists] using hq
  by_cases hex : ∃ k₀ ∈ Icc 1 R, (sentTo (alg t) E k₀ p).Nonempty
  · obtain ⟨k₀, hk₀, q₀, hq₀⟩ := hex
    have hk₀1 : 1 ≤ k₀ := (mem_Icc.1 hk₀).1
    obtain ⟨v₀, hv₀⟩ := hmem _ _ hq₀
    obtain ⟨hpt, -, hd₀⟩ := msg_eq_some hE hk₀1 hv₀
    rw [sum_eq_single_of_mem k₀ hk₀, ite_eq_left hpt, ← Fin.card_Ioi]
    · apply card_le_card
      intro q hq
      obtain ⟨v, hv⟩ := hmem _ _ hq
      exact mem_Ioi.2 (msg_eq_some hE hk₀1 hv).2.1
    · intro k hk hne
      rw [card_eq_zero, ← not_nonempty_iff_eq_empty]
      rintro ⟨q, hq⟩
      obtain ⟨v, hv⟩ := hmem _ _ hq
      obtain ⟨-, -, hd⟩ := msg_eq_some hE (mem_Icc.1 hk).1 hv
      have := (hd.unique hd₀).1
      have := (mem_Icc.1 hk).1
      omega
  · push Not at hex
    rw [sum_eq_zero]
    · exact Nat.zero_le _
    · intro k hk
      simp [hex k hk]

lemma decidedBy_aux (q : Fin n) (hq : ¬ E.FaultyAt (E.F.card + 1) q) :
    ∃ b, DecidedBy (alg t) E q (E.F.card + 1) b := by
  obtain ⟨c, hcq, L, hL, w, hd, hsend⟩ := exists_sender hE q hq
  rcases hcq.lt_or_eq with hlt | rfl
  · obtain ⟨b, hb⟩ := status_isSome_of_msg (by omega) (hsend q hlt)
    obtain ⟨L', hL', hd'⟩ := exists_decidesAt hb
    exact ⟨b, L', by omega, hd'⟩
  · exact ⟨w, L, by omega, hd⟩

end Messages

lemma two_mul_sum_range_sub {N : ℕ} : ∀ m ≤ N,
    2 * ∑ i ∈ range m, (N - 1 - i) = m * (2 * N - m - 1)
  | 0, _ => by simp
  | m + 1, hm => by
    rw [sum_range_succ, mul_add, two_mul_sum_range_sub m (by omega)]
    obtain ⟨d, rfl⟩ : ∃ d, N = m + 1 + d := ⟨N - m - 1, by omega⟩
    rw [show 2 * (m + 1 + d) - m - 1 = m + 1 + 2 * d by omega,
      show m + 1 + d - 1 - m = d by omega, show 2 * (m + 1 + d) - (m + 1) - 1 = m + 2 * d by omega]
    ring

/-- Theorem 4.5 (resilience): the algorithm solves binary consensus against `t` orderly crashes. -/
theorem correct (t : ℕ) : Correct (alg (n := n) t) (orderlyAdm (alg t) rank t) where
  termination E hE p hp := by
    obtain ⟨b, hb⟩ := decidedBy_aux hE p (Execution.not_faultyAt_of_not_mem hp)
    exact ⟨b, hb.decides⟩
  agreement E hE p hp q hq b c := by
    rintro ⟨L, hL⟩ ⟨L', hL'⟩
    obtain ⟨i₀, hi₀⟩ := exists_decision_value hE p
    rw [hi₀ p hp L b hL, hi₀ q hq L' c hL']
  validity E hE p hp b := by
    rintro ⟨L, hL⟩
    obtain ⟨i₀, hi₀⟩ := exists_decision_value hE p
    exact ⟨i₀, (hi₀ p hp L b hL).symm⟩

/-- Theorem 4.5 (`(f+1)`-deciding, in the paper's strong form): in an orderly-crash execution
with `f` faults, every node that is not faulty in round `f + 1` has decided within `f + 1`
rounds. -/
theorem decidedBy (t : ℕ) (E : Execution (Fin n) Bool) (hE : orderlyAdm (alg t) rank t E)
    (q : Fin n) (hq : ¬ E.FaultyAt (E.F.card + 1) q) :
    ∃ b, DecidedBy (alg t) E q (E.F.card + 1) b :=
  decidedBy_aux hE q hq

/-- Theorem 4.5 (`(f+1)`-deciding, Definition 3.1). -/
theorem deciding (t : ℕ) : Deciding (alg (n := n) t) (orderlyAdm (alg t) rank t) (· + 1) := by
  intro f E hE hf q hq
  subst hf
  exact decidedBy t E hE q (Execution.not_faultyAt_of_not_mem hq)

/-- Theorem 4.5 (`(f+2)`-stopping): non-faulty nodes send no messages after round `f + 2`. -/
theorem stopping (t : ℕ) (E : Execution (Fin n) Bool) (hE : orderlyAdm (alg t) rank t E)
    (k : ℕ) (p q : Fin n) (hp : ¬ E.FaultyAt k p) (h : (msg (alg t) E k p q).isSome) :
    k ≤ E.F.card + 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · omega
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨-, -, hd⟩ := msg_eq_some hE hk hv
  by_cases hf : E.FaultyAt (E.F.card + 1) p
  · have : ¬ E.fr p ≤ k := fun h' => hp ⟨hf.1, h'⟩
    have := hf.2
    omega
  · obtain ⟨c, hcp, L, hL, w, hdc, hsend⟩ := exists_sender hE p hf
    rcases hcp.lt_or_eq with hlt | rfl
    · obtain ⟨b, hb⟩ := status_isSome_of_msg (by omega) (hsend p hlt)
      by_contra hcon
      have := hd.2 (L + 1) (by omega)
      rw [hb] at this
      simp at this
    · have := (hd.unique hdc).1
      omega

/-- Theorem 4.5 (message complexity): at most `(t + 1)(n - t/2 - 1)` messages are sent in any
orderly-crash execution, counting the messages of faulty nodes too. -/
theorem totalCount_le (t : ℕ) (ht : t < n) (E : Execution (Fin n) Bool)
    (hE : orderlyAdm (alg t) rank t E) (R : ℕ) :
    2 * totalCount (alg t) E R ≤ (t + 1) * (2 * n - t - 2) := by
  have h1 : totalCount (alg t) E R ≤ ∑ p : Fin n, if p.val ≤ t then n - 1 - p.val else 0 := by
    unfold totalCount roundCount
    rw [sum_comm]
    exact sum_le_sum fun p _ => sum_card_sentTo_le hE R p
  have h2 : (∑ p : Fin n, if p.val ≤ t then n - 1 - p.val else 0) =
      ∑ i ∈ range (t + 1), (n - 1 - i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ t then n - 1 - i else 0)]
    obtain ⟨d, hd⟩ : ∃ d, n = t + 1 + d := ⟨n - t - 1, by omega⟩
    rw [hd, sum_range_add, ← hd]
    rw [sum_eq_zero (s := range d) (fun i _ => ite_eq_right (by omega)), add_zero]
    exact sum_congr rfl fun i hi => ite_eq_left (by simp at hi; omega)
  have h3 := two_mul_sum_range_sub (N := n) (t + 1) (by omega)
  rw [h2] at h1
  have : 2 * n - (t + 1) - 1 = 2 * n - t - 2 := by omega
  rw [this] at h3
  omega

/-- Theorem 4.5: fewer than `n (t + 1)` messages. -/
theorem totalCount_lt (t : ℕ) (ht : t < n) (E : Execution (Fin n) Bool)
    (hE : orderlyAdm (alg t) rank t E) (R : ℕ) :
    totalCount (alg t) E R < n * (t + 1) := by
  have := totalCount_le t ht E hE R
  have h2 : (t + 1) * (2 * n - t - 2) < 2 * (n * (t + 1)) := by
    have : 2 * n - t - 2 < 2 * n := by omega
    calc (t + 1) * (2 * n - t - 2) < (t + 1) * (2 * n) := by
          exact Nat.mul_lt_mul_of_pos_left this (by omega)
      _ = 2 * (n * (t + 1)) := by ring
  omega

end Podc.EarlyDecidingExpensive.Orderly
