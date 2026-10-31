import Papers.PODC2012.GeneralizedLatticeAgreement.Basic

/-!
# The main inductive invariant of Algorithm 2

`Inv s` collects the facts used by the safety proofs (Section 5.1) and by the round lemmas
(Lemmas 5.7–5.11). It holds in every reachable state (`Reachable.inv`), for any initial buffers
(so for Algorithm 1 as well).
-/

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}

/-- The values carried by acknowledgements and rejections of acceptor `a`. -/
def respVals (s : State P A Ln L) (a : A) : Set L :=
  {v | ∃ p n, Msg.ack a p n v ∈ s.sent ∨ Msg.nack a p n v ∈ s.sent}

section

variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

/-- The main invariant. -/
structure Inv (s : State P A Ln L) : Prop where
  prop_range : ∀ {p n v}, Msg.proposal p n v ∈ s.sent → 1 ≤ n ∧ n ≤ (s.prop p).apn
  prop_exists : ∀ {p n}, 1 ≤ n → n ≤ (s.prop p).apn → ∃ v, Msg.proposal p n v ∈ s.sent
  prop_unique : ∀ {p n v v'}, Msg.proposal p n v ∈ s.sent → Msg.proposal p n v' ∈ s.sent →
    v = v'
  prop_le : ∀ {p n v}, Msg.proposal p n v ∈ s.sent → v ≤ (s.prop p).proposed
  prop_succ : ∀ {p n v v'}, Msg.proposal p n v ∈ s.sent → Msg.proposal p (n + 1) v' ∈ s.sent →
    v < v'
  cur_val : ∀ {p}, 1 ≤ (s.prop p).apn → (s.prop p).nacks (s.prop p).apn = ∅ →
    Msg.proposal p (s.prop p).apn (s.prop p).proposed ∈ s.sent
  ack_prop : ∀ {a p n v}, Msg.ack a p n v ∈ s.sent → Msg.proposal p n v ∈ s.sent
  nack_prop : ∀ {a p n ρ}, Msg.nack a p n ρ ∈ s.sent →
    ∃ v, Msg.proposal p n v ∈ s.sent ∧ v < ρ
  ack_done : ∀ {a p n v}, Msg.ack a p n v ∈ s.sent → (p, n) ∈ s.adone a
  nack_done : ∀ {a p n v}, Msg.nack a p n v ∈ s.sent → (p, n) ∈ s.adone a
  resp_excl : ∀ {a p n v v'}, Msg.ack a p n v ∈ s.sent → Msg.nack a p n v' ∈ s.sent → False
  resp_le_acc : ∀ {a v}, v ∈ respVals s a → v ≤ s.acc a
  resp_chain : ∀ {a u v}, u ∈ respVals s a → v ∈ respVals s a → u ≤ v ∨ v ≤ u
  acks_sent : ∀ {p n a}, a ∈ (s.prop p).acks n → ∃ v, Msg.ack a p n v ∈ s.sent
  nacks_sent : ∀ {p n a}, a ∈ (s.prop p).nacks n →
    ∃ ρ, Msg.nack a p n ρ ∈ s.sent ∧ ρ ≤ (s.prop p).proposed
  prev_quorum : ∀ {p n w}, 1 ≤ n → Msg.proposal p (n + 1) w ∈ s.sent →
    ∃ R : Finset A, quorum A ≤ R.card ∧
      ∀ a ∈ R, ∃ ρ, (Msg.ack a p n ρ ∈ s.sent ∨ Msg.nack a p n ρ ∈ s.sent) ∧ ρ ≤ w
  passive_quorum : ∀ {p}, (s.prop p).active = false → 1 ≤ (s.prop p).apn →
    quorum A ≤ ((s.prop p).acks (s.prop p).apn).card
  init_prop : ∀ {p m}, (p, m) ∈ s.initiated → ∃ v, Msg.proposal p m v ∈ s.sent
  init_quorum : ∀ {p m}, (p, m) ∈ s.initiated → 2 ≤ m →
    quorum A ≤ ((s.prop p).acks (m - 1)).card
  learn_sent : ∀ {l p n a}, a ∈ s.lacks l p n → ∃ v, Msg.ack a p n v ∈ s.sent
  learnt_chosen : ∀ l, s.learnt l = ⊥ ∨ Chosen s (s.learnt l)
  dec_quorum : ∀ {p n d c}, (p, n, d, c) ∈ s.decisions →
    1 ≤ n ∧ n ≤ (s.prop p).apn ∧ quorum A ≤ ((s.prop p).acks n).card
  dec_clean : ∀ {p n d}, (p, n, d, true) ∈ s.decisions → Msg.proposal p n d ∈ s.sent
  output_dec : ∀ p, (s.prop p).output = ⊥ ∨ ∃ n c, (p, n, (s.prop p).output, c) ∈ s.decisions

lemma inv_init (b : P → L) : Inv (initState (Ln := Ln) (A := A) b) where
  prop_range h := by simp [initState] at h
  prop_exists h1 h2 := by simp [initState] at h2; omega
  prop_unique h := by simp [initState] at h
  prop_le h := by simp [initState] at h
  prop_succ h := by simp [initState] at h
  cur_val h := by simp [initState] at h
  ack_prop h := by simp [initState] at h
  nack_prop h := by simp [initState] at h
  ack_done h := by simp [initState] at h
  nack_done h := by simp [initState] at h
  resp_excl h := by simp [initState] at h
  resp_le_acc h := by simp [initState, respVals] at h
  resp_chain h := by simp [initState, respVals] at h
  acks_sent h := by simp [initState] at h
  nacks_sent h := by simp [initState] at h
  prev_quorum _ h := by simp [initState] at h
  passive_quorum _ h := by simp [initState] at h
  init_prop h := by simp [initState] at h
  init_quorum h := by simp [initState] at h
  learn_sent h := by simp [initState] at h
  learnt_chosen _ := by simp [initState]
  dec_quorum h := by simp [initState] at h
  dec_clean h := by simp [initState] at h
  output_dec _ := by simp [initState]

variable {s : State P A Ln L}

namespace Inv

variable (h : Inv s)
include h

lemma one_le_of_mem_acks {p n a} (ha : a ∈ (s.prop p).acks n) : 1 ≤ n ∧ n ≤ (s.prop p).apn := by
  obtain ⟨v, hv⟩ := h.acks_sent ha
  exact h.prop_range (h.ack_prop hv)

lemma one_le_apn_of_quorum {p n} (hq : quorum A ≤ ((s.prop p).acks n).card) :
    1 ≤ n ∧ n ≤ (s.prop p).apn := by
  have : ((s.prop p).acks n).Nonempty := by
    rw [← Finset.card_pos]; unfold quorum at hq; omega
  obtain ⟨a, ha⟩ := this
  exact h.one_le_of_mem_acks ha

lemma acks_subset_ackers {p n v} (hv : Msg.proposal p n v ∈ s.sent) :
    (s.prop p).acks n ⊆ ackers s p n v := by
  intro a ha
  obtain ⟨v', hv'⟩ := h.acks_sent ha
  have := h.prop_unique hv (h.ack_prop hv')
  subst this
  simpa [ackers] using hv'

lemma chosen_of_quorum {p n v} (hv : Msg.proposal p n v ∈ s.sent)
    (hq : quorum A ≤ ((s.prop p).acks n).card) : Chosen s v :=
  ⟨p, n, hq.trans (Finset.card_le_card (h.acks_subset_ackers hv))⟩

lemma acks_nacks_disjoint (p n) : Disjoint ((s.prop p).acks n) ((s.prop p).nacks n) := by
  rw [Finset.disjoint_left]
  intro a ha hn
  obtain ⟨v, hv⟩ := h.acks_sent ha
  obtain ⟨ρ, hρ, -⟩ := h.nacks_sent hn
  exact h.resp_excl hv hρ

/-- Lemma 5.5: any two chosen values are comparable. -/
lemma chosen_comparable {u v : L} (hu : Chosen s u) (hv : Chosen s v) : u ≤ v ∨ v ≤ u := by
  obtain ⟨p, n, hu⟩ := hu
  obtain ⟨p', n', hv⟩ := hv
  obtain ⟨a, ha⟩ := quorum_inter hu hv
  simp only [Finset.mem_inter, ackers, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact h.resp_chain ⟨p, n, Or.inl ha.1⟩ ⟨p', n', Or.inl ha.2⟩

end Inv

/-- Chosen values stay chosen. -/
lemma Chosen.mono {s s' : State P A Ln L} (hs : s.sent ⊆ s'.sent) {v : L} (h : Chosen s v) :
    Chosen s' v := by
  obtain ⟨p, n, h⟩ := h
  refine ⟨p, n, h.trans (Finset.card_le_card ?_)⟩
  intro a; simp only [ackers, Finset.mem_filter, Finset.mem_univ, true_and]; exact fun x => hs x

end

end Podc.GeneralizedLatticeAgreement
