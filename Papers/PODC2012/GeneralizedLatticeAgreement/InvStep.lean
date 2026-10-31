import Papers.PODC2012.GeneralizedLatticeAgreement.Invariant

/-!
# Preservation of the invariant `Inv`
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.deprecated false

namespace Podc.GeneralizedLatticeAgreement

variable {P A Ln L : Type}
variable [SemilatticeSup L] [OrderBot L] [DecidableEq P] [DecidableEq A] [DecidableEq Ln]
  [DecidableEq L] [DecidableLE L] [Fintype P] [Fintype A]

variable {s : State P A Ln L}

namespace Inv

lemma propose (h : Inv s) {q : P} (he : Enabled s (.propose q)) :
    Inv (apply s (.propose q)) := by
  obtain ⟨hpas, hgt⟩ := he
  have hlt : (s.prop q).proposed < (s.prop q).proposed ⊔ (s.prop q).buffered := lt_of_le_not_ge le_sup_left hgt
  have hnew : ∀ {n v}, Msg.proposal q n v ∈ s.sent → n ≤ (s.prop q).apn := fun hm => (h.prop_range hm).2
  constructor
  · intro p n v hm
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · simp
    · have := h.prop_range hm
      split_ifs with hpq
      · subst p; simp; omega
      · exact this
  · -- prop_exists
    intro p n h1 h2
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at h2 ⊢
    split_ifs at h2 with hpq
    · subst p
      simp only at h2
      rcases Nat.lt_or_ge n ((s.prop q).apn + 1) with hn | hn
      · obtain ⟨v, hv⟩ := h.prop_exists (p := q) h1 (by omega)
        exact ⟨v, Or.inr hv⟩
      · exact ⟨_, Or.inl ⟨rfl, by omega, rfl⟩⟩
    · obtain ⟨v, hv⟩ := h.prop_exists h1 h2
      exact ⟨v, Or.inr hv⟩
  · -- prop_unique
    intro p n v v' hm hm'
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq] at hm hm'
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm <;> rcases hm' with ⟨hq, hn, rfl⟩ | hm'
    · rfl
    · have := hnew hm'; omega
    · subst p; have := hnew hm; omega
    · exact h.prop_unique hm hm'
  · -- prop_le
    intro p n v hm
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · simp
    · have := h.prop_le hm
      split_ifs with hpq
      · subst p; exact this.trans le_sup_left
      · exact this
  · -- prop_succ
    intro p n v v' hm hm'
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq] at hm hm'
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm <;> rcases hm' with ⟨hq, hn, rfl⟩ | hm'
    · omega
    · have := hnew hm'; omega
    · subst p
      have hn' : n = (s.prop q).apn := by omega
      subst hn'
      exact lt_of_le_of_lt (h.prop_le hm) hlt
    · exact h.prop_succ hm hm'
  · -- cur_val
    intro p h1 h2
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; simp
    · exact Or.inr (h.cur_val h1 h2)
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm ⊢
    exact Or.inr (h.ack_prop hm)
  · intro a p n ρ hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm ⊢
    obtain ⟨v, hv, hlt⟩ := h.nack_prop hm
    exact ⟨v, Or.inr hv, hlt⟩
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_adone] at hm ⊢
    exact h.ack_done hm
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_adone] at hm ⊢
    exact h.nack_done hm
  · intro a p n v v' hm hm'
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm hm'
    exact h.resp_excl hm hm'
  · intro a v hv
    simp only [respVals, apply, Finset.mem_insert, reduceCtorEq, false_or, Set.mem_ofPred_eq,
      State.updP_acc] at hv ⊢
    exact h.resp_le_acc hv
  · intro a u v hu hv
    simp only [respVals, apply, Finset.mem_insert, reduceCtorEq, false_or,
      Set.mem_ofPred_eq] at hu hv
    exact h.resp_chain hu hv
  · -- acks_sent
    intro p n a ha
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_prop] at ha ⊢
    split_ifs at ha with hpq
    · subst p
      simp only [Function.update_apply] at ha
      split_ifs at ha
      · simp at ha
      · exact h.acks_sent ha
    · exact h.acks_sent ha
  · -- nacks_sent
    intro p n a ha
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_prop] at ha ⊢
    split_ifs at ha ⊢ with hpq
    · subst p
      simp only [Function.update_apply] at ha
      split_ifs at ha
      · simp at ha
      · obtain ⟨ρ, hρ, hle⟩ := h.nacks_sent ha
        exact ⟨ρ, hρ, hle.trans le_sup_left⟩
    · exact h.nacks_sent ha
  · -- prev_quorum
    intro p n w h1 hm
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, reduceCtorEq, false_or] at hm ⊢
    rcases hm with ⟨hpq, hn, rfl⟩ | hm
    · subst p
      have hn' : n = (s.prop q).apn := by omega
      subst hn'
      refine ⟨(s.prop q).acks (s.prop q).apn, h.passive_quorum hpas h1, fun a ha => ?_⟩
      obtain ⟨v, hv⟩ := h.acks_sent ha
      exact ⟨v, Or.inl hv, (h.prop_le (h.ack_prop hv)).trans le_sup_left⟩
    · obtain ⟨R, hR, hR'⟩ := h.prev_quorum h1 hm
      exact ⟨R, hR, hR'⟩
  · -- passive_quorum
    intro p h1 h2
    simp only [apply, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    all_goals first | exact h.passive_quorum h1 h2 | simp at h1
  · -- init_prop
    intro p m hm
    simp only [apply, Finset.mem_insert, Prod.mk.injEq, Msg.proposal.injEq] at hm ⊢
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨_, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨v, hv⟩ := h.init_prop hm
      exact ⟨v, Or.inr hv⟩
  · -- init_quorum
    intro p m hm h2
    simp only [apply, Finset.mem_insert, Prod.mk.injEq, State.updP_prop] at hm ⊢
    rcases hm with ⟨rfl, rfl⟩ | hm
    · simp only [ite_true, Function.update_apply, Nat.add_sub_cancel]
      rw [if_neg (by omega)]
      exact h.passive_quorum hpas (by omega)
    · split_ifs with hpq
      · subst p
        obtain ⟨v, hv⟩ := h.init_prop hm
        have := hnew hv
        simp only [Function.update_apply]
        rw [if_neg (by omega)]
        exact h.init_quorum hm h2
      · exact h.init_quorum hm h2
  · intro l p n a ha
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_lacks] at ha ⊢
    exact h.learn_sent ha
  · intro l
    rcases h.learnt_chosen l with h0 | h0
    · left; simpa [apply] using h0
    · right
      have := h0.mono (sent_subset_apply s (.propose q))
      simpa [apply] using this
  · -- dec_quorum
    intro p n d c hm
    simp only [apply, State.updP_decisions, State.updP_prop] at hm ⊢
    obtain ⟨h1, h2, h3⟩ := h.dec_quorum hm
    split_ifs with hpq
    · subst p
      simp only [Function.update_apply]
      rw [if_neg (by omega)]
      exact ⟨h1, by omega, h3⟩
    · exact ⟨h1, h2, h3⟩
  · intro p n d hm
    simp only [apply, State.updP_decisions, Finset.mem_insert] at hm ⊢
    exact Or.inr (h.dec_clean hm)
  · intro p
    simp only [apply, State.updP_decisions, State.updP_prop]
    split_ifs with hpq
    · subst p; exact h.output_dec q
    · exact h.output_dec p

lemma refine (h : Inv s) {q : P} (he : Enabled s (.refine q)) :
    Inv (apply s (.refine q)) := by
  obtain ⟨hpos, hquo, hact⟩ := he
  have hnew : ∀ {n v}, Msg.proposal q n v ∈ s.sent → n ≤ (s.prop q).apn :=
    fun hm => (h.prop_range hm).2
  obtain ⟨a₀, ha₀⟩ := Finset.card_pos.1 hpos
  obtain ⟨ρ₀, hρ₀, hρ₀le⟩ := h.nacks_sent ha₀
  obtain ⟨v₀, hv₀, hv₀lt⟩ := h.nack_prop hρ₀
  have hk : 1 ≤ (s.prop q).apn := (h.prop_range hv₀).1
  have hlt : ∀ {v}, Msg.proposal q (s.prop q).apn v ∈ s.sent → v < (s.prop q).proposed := by
    intro v hv
    rw [h.prop_unique hv hv₀]
    exact lt_of_lt_of_le hv₀lt hρ₀le
  constructor
  · intro p n v hm
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · simp
    · have := h.prop_range hm
      split_ifs with hpq
      · subst p; simp; omega
      · exact this
  · -- prop_exists
    intro p n h1 h2
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at h2 ⊢
    split_ifs at h2 with hpq
    · subst p
      dsimp only at h2
      rcases Nat.lt_or_ge n ((s.prop q).apn + 1) with hn | hn
      · obtain ⟨v, hv⟩ := h.prop_exists (p := q) h1 (by omega)
        exact ⟨v, Or.inr hv⟩
      · exact ⟨_, Or.inl ⟨rfl, by omega, rfl⟩⟩
    · obtain ⟨v, hv⟩ := h.prop_exists h1 h2
      exact ⟨v, Or.inr hv⟩
  · -- prop_unique
    intro p n v v' hm hm'
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq] at hm hm'
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm <;> rcases hm' with ⟨hq, hn, rfl⟩ | hm'
    · rfl
    · have := hnew hm'; omega
    · subst p; have := hnew hm; omega
    · exact h.prop_unique hm hm'
  · -- prop_le
    intro p n v hm
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · simp
    · have := h.prop_le hm
      split_ifs with hpq
      · subst p; exact this
      · exact this
  · -- prop_succ
    intro p n v v' hm hm'
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq] at hm hm'
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm <;> rcases hm' with ⟨hq, hn, rfl⟩ | hm'
    · omega
    · have := hnew hm'; omega
    · subst p
      have hn' : n = (s.prop q).apn := by omega
      subst hn'
      exact hlt hm
    · exact h.prop_succ hm hm'
  · -- cur_val
    intro p h1 h2
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; simp
    · exact Or.inr (h.cur_val h1 h2)
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm ⊢
    exact Or.inr (h.ack_prop hm)
  · intro a p n ρ hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm ⊢
    obtain ⟨v, hv, hlt⟩ := h.nack_prop hm
    exact ⟨v, Or.inr hv, hlt⟩
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_adone] at hm ⊢
    exact h.ack_done hm
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_adone] at hm ⊢
    exact h.nack_done hm
  · intro a p n v v' hm hm'
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm hm'
    exact h.resp_excl hm hm'
  · intro a v hv
    simp only [respVals, apply, Finset.mem_insert, reduceCtorEq, false_or, Set.mem_ofPred_eq,
      State.updP_acc] at hv ⊢
    exact h.resp_le_acc hv
  · intro a u v hu hv
    simp only [respVals, apply, Finset.mem_insert, reduceCtorEq, false_or,
      Set.mem_ofPred_eq] at hu hv
    exact h.resp_chain hu hv
  · -- acks_sent
    intro p n a ha
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_prop] at ha ⊢
    split_ifs at ha with hpq
    · subst p
      simp only [Function.update_apply] at ha
      split_ifs at ha
      · simp at ha
      · exact h.acks_sent ha
    · exact h.acks_sent ha
  · -- nacks_sent
    intro p n a ha
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_prop] at ha ⊢
    split_ifs at ha ⊢ with hpq
    · subst p
      simp only [Function.update_apply] at ha
      split_ifs at ha
      · simp at ha
      · exact h.nacks_sent ha
    · exact h.nacks_sent ha
  · -- prev_quorum
    intro p n w h1 hm
    simp only [apply, Finset.mem_insert, Msg.proposal.injEq, reduceCtorEq, false_or] at hm ⊢
    rcases hm with ⟨hpq, hn, rfl⟩ | hm
    · subst p
      have hn' : n = (s.prop q).apn := by omega
      subst hn'
      refine ⟨(s.prop q).acks (s.prop q).apn ∪ (s.prop q).nacks (s.prop q).apn, ?_,
        fun a ha => ?_⟩
      · rw [Finset.card_union_of_disjoint (h.acks_nacks_disjoint _ _)]; exact hquo
      · rcases Finset.mem_union.1 ha with ha | ha
        · obtain ⟨v, hv⟩ := h.acks_sent ha
          exact ⟨v, Or.inl hv, h.prop_le (h.ack_prop hv)⟩
        · obtain ⟨ρ, hρ, hle⟩ := h.nacks_sent ha
          exact ⟨ρ, Or.inr hρ, hle⟩
    · exact h.prev_quorum h1 hm
  · -- passive_quorum
    intro p h1 h2
    simp only [apply, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; simp_all
    · exact h.passive_quorum h1 h2
  · -- init_prop
    intro p m hm
    simp only [apply, Finset.mem_insert, Prod.mk.injEq, Msg.proposal.injEq] at hm ⊢
    obtain ⟨v, hv⟩ := h.init_prop hm
    exact ⟨v, Or.inr hv⟩
  · -- init_quorum
    intro p m hm h2
    simp only [apply, State.updP_prop] at hm ⊢
    split_ifs with hpq
    · subst p
      obtain ⟨v, hv⟩ := h.init_prop hm
      have := hnew hv
      simp only [Function.update_apply]
      rw [if_neg (by omega)]
      exact h.init_quorum hm h2
    · exact h.init_quorum hm h2
  · intro l p n a ha
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, State.updP_lacks] at ha ⊢
    exact h.learn_sent ha
  · intro l
    rcases h.learnt_chosen l with h0 | h0
    · left; simpa [apply] using h0
    · right
      have := h0.mono (sent_subset_apply s (.refine q))
      simpa [apply] using this
  · -- dec_quorum
    intro p n d c hm
    simp only [apply, State.updP_decisions, State.updP_prop] at hm ⊢
    obtain ⟨h1, h2, h3⟩ := h.dec_quorum hm
    split_ifs with hpq
    · subst p
      simp only [Function.update_apply]
      rw [if_neg (by omega)]
      exact ⟨h1, by omega, h3⟩
    · exact ⟨h1, h2, h3⟩
  · intro p n d hm
    simp only [apply, State.updP_decisions, Finset.mem_insert] at hm ⊢
    exact Or.inr (h.dec_clean hm)
  · intro p
    simp only [apply, State.updP_decisions, State.updP_prop]
    split_ifs with hpq
    · subst p; exact h.output_dec q
    · exact h.output_dec p

/-- Transfer of the invariant to a state with the same proposals, acknowledgements, rejections,
acceptor states and proposal numbers, where proposers' `acks` and `proposedValue` can only grow
(the remaining fields have to be checked). -/
lemma frame (h : Inv s) {s' : State P A Ln L}
    (hpr : ∀ {p n v}, Msg.proposal p n v ∈ s'.sent ↔ Msg.proposal p n v ∈ s.sent)
    (hak : ∀ {a p n v}, Msg.ack a p n v ∈ s'.sent ↔ Msg.ack a p n v ∈ s.sent)
    (hnk : ∀ {a p n v}, Msg.nack a p n v ∈ s'.sent ↔ Msg.nack a p n v ∈ s.sent)
    (hapn : ∀ p, (s'.prop p).apn = (s.prop p).apn)
    (hacks : ∀ p n, (s.prop p).acks n ⊆ (s'.prop p).acks n)
    (hprop : ∀ p, (s.prop p).proposed ≤ (s'.prop p).proposed)
    (hacc : s'.acc = s.acc) (hadone : s'.adone = s.adone) (hinit : s'.initiated = s.initiated)
    (cur_val : ∀ {p}, 1 ≤ (s'.prop p).apn → (s'.prop p).nacks (s'.prop p).apn = ∅ →
      Msg.proposal p (s'.prop p).apn (s'.prop p).proposed ∈ s'.sent)
    (acks_sent : ∀ {p n a}, a ∈ (s'.prop p).acks n → ∃ v, Msg.ack a p n v ∈ s'.sent)
    (nacks_sent : ∀ {p n a}, a ∈ (s'.prop p).nacks n →
      ∃ ρ, Msg.nack a p n ρ ∈ s'.sent ∧ ρ ≤ (s'.prop p).proposed)
    (passive_quorum : ∀ {p}, (s'.prop p).active = false → 1 ≤ (s'.prop p).apn →
      quorum A ≤ ((s'.prop p).acks (s'.prop p).apn).card)
    (learn_sent : ∀ {l p n a}, a ∈ s'.lacks l p n → ∃ v, Msg.ack a p n v ∈ s'.sent)
    (learnt_chosen : ∀ l, s'.learnt l = ⊥ ∨ Chosen s' (s'.learnt l))
    (dec_quorum : ∀ {p n d c}, (p, n, d, c) ∈ s'.decisions →
      1 ≤ n ∧ n ≤ (s'.prop p).apn ∧ quorum A ≤ ((s'.prop p).acks n).card)
    (dec_clean : ∀ {p n d}, (p, n, d, true) ∈ s'.decisions → Msg.proposal p n d ∈ s'.sent)
    (output_dec : ∀ p, (s'.prop p).output = ⊥ ∨
      ∃ n c, (p, n, (s'.prop p).output, c) ∈ s'.decisions) : Inv s' := by
  have hrv : ∀ a, respVals s' a = respVals s a := by
    intro a; ext v; simp [respVals, hak, hnk]
  refine ⟨?_, ?_, ?_, ?_, ?_, cur_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, acks_sent, nacks_sent, ?_,
    passive_quorum, ?_, ?_, learn_sent, learnt_chosen, dec_quorum, dec_clean, output_dec⟩
  · intro p n v hm; rw [hapn]; exact h.prop_range (hpr.1 hm)
  · intro p n h1 h2; rw [hapn] at h2
    obtain ⟨v, hv⟩ := h.prop_exists h1 h2; exact ⟨v, hpr.2 hv⟩
  · intro p n v v' hm hm'; exact h.prop_unique (hpr.1 hm) (hpr.1 hm')
  · intro p n v hm; exact (h.prop_le (hpr.1 hm)).trans (hprop p)
  · intro p n v v' hm hm'; exact h.prop_succ (hpr.1 hm) (hpr.1 hm')
  · intro a p n v hm; exact hpr.2 (h.ack_prop (hak.1 hm))
  · intro a p n ρ hm
    obtain ⟨v, hv, hlt⟩ := h.nack_prop (hnk.1 hm); exact ⟨v, hpr.2 hv, hlt⟩
  · intro a p n v hm; rw [hadone]; exact h.ack_done (hak.1 hm)
  · intro a p n v hm; rw [hadone]; exact h.nack_done (hnk.1 hm)
  · intro a p n v v' hm hm'; exact h.resp_excl (hak.1 hm) (hnk.1 hm')
  · intro a v hv; rw [hrv] at hv; rw [hacc]; exact h.resp_le_acc hv
  · intro a u v hu hv; rw [hrv] at hu hv; exact h.resp_chain hu hv
  · intro p n w h1 hm
    obtain ⟨R, hR, hR'⟩ := h.prev_quorum h1 (hpr.1 hm)
    refine ⟨R, hR, fun a ha => ?_⟩
    obtain ⟨ρ, hρ, hle⟩ := hR' a ha
    exact ⟨ρ, hρ.imp hak.2 hnk.2, hle⟩
  · intro p m hm; rw [hinit] at hm
    obtain ⟨v, hv⟩ := h.init_prop hm; exact ⟨v, hpr.2 hv⟩
  · intro p m hm h2; rw [hinit] at hm
    exact (h.init_quorum hm h2).trans (Finset.card_le_card (hacks p _))

lemma decide (h : Inv s) {q : P} (he : Enabled s (.decide q)) :
    Inv (apply s (.decide q)) := by
  obtain ⟨hquo, hact⟩ := he
  have hk := h.one_le_apn_of_quorum hquo
  apply h.frame
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p n; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p h1 h2
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact h.cur_val h1 h2
    · exact h.cur_val h1 h2
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at ha ⊢
    split_ifs at ha with hpq
    · subst p; exact h.acks_sent ha
    · exact h.acks_sent ha
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at ha ⊢
    split_ifs at ha ⊢ with hpq
    · subst p; exact h.nacks_sent ha
    · exact h.nacks_sent ha
  · intro p h1 h2
    simp only [apply, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact hquo
    · exact h.passive_quorum h1 h2
  · intro l p n a ha; exact h.learn_sent (by simpa [apply] using ha)
  · intro l
    rcases h.learnt_chosen l with h0 | h0
    · left; simpa [apply] using h0
    · right; have := h0.mono (sent_subset_apply s (.decide q)); simpa [apply] using this
  · intro p n d c hm
    simp only [apply, State.updP_decisions, State.updP_prop, Finset.mem_insert,
      Prod.mk.injEq] at hm ⊢
    rcases hm with ⟨rfl, rfl, -, -⟩ | hm
    · simp only [ite_true]; exact ⟨hk.1, le_rfl, hquo⟩
    · obtain ⟨h1, h2, h3⟩ := h.dec_quorum hm
      split_ifs with hpq
      · subst p; exact ⟨h1, h2, h3⟩
      · exact ⟨h1, h2, h3⟩
  · intro p n d hm
    simp only [apply, State.updP_decisions, Finset.mem_insert, Prod.mk.injEq,
      State.updP_sent] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl, hc⟩ | hm
    · have : (s.prop p).nacks (s.prop p).apn = ∅ := by simpa using hc.symm
      exact h.cur_val hk.1 this
    · exact h.dec_clean hm
  · intro p
    simp only [apply, State.updP_decisions, State.updP_prop, Finset.mem_insert, Prod.mk.injEq]
    split_ifs with hpq
    · subst p
      right; exact ⟨(s.prop q).apn, _, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · rcases h.output_dec p with h0 | ⟨n, c, hn⟩
      · left; exact h0
      · right; exact ⟨n, c, Or.inr hn⟩

lemma receive (h : Inv s) {q : P} {v : L} : Inv (apply s (.receive q v)) := by
  apply h.frame
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p n; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p h1 h2
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact h.cur_val h1 h2
    · exact h.cur_val h1 h2
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at ha ⊢
    split_ifs at ha with hpq
    · subst p; exact h.acks_sent ha
    · exact h.acks_sent ha
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at ha ⊢
    split_ifs at ha ⊢ with hpq
    · subst p; exact h.nacks_sent ha
    · exact h.nacks_sent ha
  · intro p h1 h2
    simp only [apply, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact h.passive_quorum h1 h2
    · exact h.passive_quorum h1 h2
  · intro l p n a ha
    obtain ⟨w, hw⟩ := h.learn_sent (by simpa [apply] using ha)
    exact ⟨w, by simp [apply, hw]⟩
  · intro l
    rcases h.learnt_chosen l with h0 | h0
    · left; simpa [apply] using h0
    · right; exact (by simpa [apply] using h0.mono (sent_subset_apply s (.receive q v)))
  · intro p n d c hm
    simp only [apply, State.updP_decisions, State.updP_prop] at hm ⊢
    obtain ⟨h1, h2, h3⟩ := h.dec_quorum hm
    split_ifs with hpq
    · subst p; exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  · intro p n d hm
    simp only [apply, State.updP_decisions, Finset.mem_insert, reduceCtorEq, false_or] at hm ⊢
    exact h.dec_clean hm
  · intro p
    simp only [apply, State.updP_decisions, State.updP_prop]
    split_ifs with hpq
    · subst p; exact h.output_dec q
    · exact h.output_dec p

lemma buffer (h : Inv s) {q q' : P} {v : L} : Inv (apply s (.buffer q q' v)) := by
  apply h.frame
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p n; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p h1 h2
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact h.cur_val h1 h2
    · exact h.cur_val h1 h2
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at ha ⊢
    split_ifs at ha with hpq
    · subst p; exact h.acks_sent ha
    · exact h.acks_sent ha
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent, Finset.mem_insert, reduceCtorEq,
      false_or] at ha ⊢
    split_ifs at ha ⊢ with hpq
    · subst p; exact h.nacks_sent ha
    · exact h.nacks_sent ha
  · intro p h1 h2
    simp only [apply, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact h.passive_quorum h1 h2
    · exact h.passive_quorum h1 h2
  · intro l p n a ha; exact h.learn_sent (by simpa [apply] using ha)
  · intro l
    rcases h.learnt_chosen l with h0 | h0
    · left; simpa [apply] using h0
    · right; have := h0.mono (sent_subset_apply s (.buffer q q' v)); simpa [apply] using this
  · intro p n d c hm
    simp only [apply, State.updP_decisions, State.updP_prop] at hm ⊢
    obtain ⟨h1, h2, h3⟩ := h.dec_quorum hm
    split_ifs with hpq
    · subst p; exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  · intro p n d hm
    simp only [apply, State.updP_decisions, State.updP_sent] at hm ⊢
    exact h.dec_clean hm
  · intro p
    simp only [apply, State.updP_decisions, State.updP_prop]
    split_ifs with hpq
    · subst p; exact h.output_dec q
    · exact h.output_dec p

lemma processAck (h : Inv s) {q : P} {a₀ : A} {n₀ : ℕ} {v₀ : L}
    (he : Enabled s (.processAck q a₀ n₀ v₀)) : Inv (apply s (.processAck q a₀ n₀ v₀)) := by
  obtain ⟨hm₀, hn₀, -⟩ := he
  have hsub : ∀ p n, (s.prop p).acks n ⊆ ((apply s (.processAck q a₀ n₀ v₀)).prop p).acks n := by
    intro p n
    simp only [apply, State.updP_prop]
    split_ifs with hpq
    · subst p; simp only [Function.update_apply]; split_ifs with hn
      · subst hn; exact Finset.subset_insert _ _
      · exact le_rfl
    · exact le_rfl
  apply h.frame
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · exact hsub
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p h1 h2
    simp only [apply, State.updP_prop, State.updP_sent] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact h.cur_val h1 h2
    · exact h.cur_val h1 h2
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent] at ha ⊢
    split_ifs at ha with hpq
    · subst p
      simp only [Function.update_apply] at ha
      split_ifs at ha with hn
      · subst hn
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact ⟨v₀, hm₀⟩
        · exact h.acks_sent ha
      · exact h.acks_sent ha
    · exact h.acks_sent ha
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent] at ha ⊢
    split_ifs at ha ⊢ with hpq
    · subst p; exact h.nacks_sent ha
    · exact h.nacks_sent ha
  · intro p h1 h2
    have h1' : (s.prop p).active = false := by
      simp only [apply, State.updP_prop] at h1; split_ifs at h1 <;> simp_all
    have h2' : 1 ≤ (s.prop p).apn := by
      simp only [apply, State.updP_prop] at h2; split_ifs at h2 <;> simp_all
    have := (h.passive_quorum h1' h2').trans (Finset.card_le_card (hsub p (s.prop p).apn))
    simp only [apply, State.updP_prop] at this ⊢
    split_ifs at this ⊢ <;> simp_all
  · intro l p n a ha; exact h.learn_sent (by simpa [apply] using ha)
  · intro l
    rcases h.learnt_chosen l with h0 | h0
    · left; simpa [apply] using h0
    · right; have := h0.mono (sent_subset_apply s (.processAck q a₀ n₀ v₀))
      simpa [apply] using this
  · intro p n d c hm
    have hm' : (p, n, d, c) ∈ s.decisions := by simpa [apply] using hm
    obtain ⟨h1, h2, h3⟩ := h.dec_quorum hm'
    refine ⟨h1, ?_, h3.trans (Finset.card_le_card (hsub p n))⟩
    simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p n d hm
    simp only [apply, State.updP_decisions, State.updP_sent] at hm ⊢
    exact h.dec_clean hm
  · intro p
    simp only [apply, State.updP_decisions, State.updP_prop]
    split_ifs with hpq
    · subst p; exact h.output_dec q
    · exact h.output_dec p

lemma processNack (h : Inv s) {q : P} {a₀ : A} {n₀ : ℕ} {ρ₀ : L}
    (he : Enabled s (.processNack q a₀ n₀ ρ₀)) : Inv (apply s (.processNack q a₀ n₀ ρ₀)) := by
  obtain ⟨hm₀, hn₀, -⟩ := he
  apply h.frame
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p n; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · intro p; simp only [apply, State.updP_prop]; split_ifs <;> simp_all
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p h1 h2
    simp only [apply, State.updP_prop, State.updP_sent] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p
      simp only [hn₀, Function.update_self] at h2
      exact absurd h2 (Finset.insert_ne_empty _ _)
    · exact h.cur_val h1 h2
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent] at ha ⊢
    split_ifs at ha with hpq
    · subst p; exact h.acks_sent ha
    · exact h.acks_sent ha
  · intro p n a ha
    simp only [apply, State.updP_prop, State.updP_sent] at ha ⊢
    split_ifs at ha ⊢ with hpq
    · subst p
      simp only [Function.update_apply] at ha
      split_ifs at ha with hn
      · subst hn
        rcases Finset.mem_insert.1 ha with rfl | ha
        · exact ⟨ρ₀, hm₀, le_sup_right⟩
        · obtain ⟨ρ, hρ, hle⟩ := h.nacks_sent ha
          exact ⟨ρ, hρ, hle.trans le_sup_left⟩
      · obtain ⟨ρ, hρ, hle⟩ := h.nacks_sent ha
        exact ⟨ρ, hρ, hle.trans le_sup_left⟩
    · exact h.nacks_sent ha
  · intro p h1 h2
    simp only [apply, State.updP_prop] at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ with hpq
    · subst p; exact h.passive_quorum h1 h2
    · exact h.passive_quorum h1 h2
  · intro l p n a ha; exact h.learn_sent (by simpa [apply] using ha)
  · intro l
    rcases h.learnt_chosen l with h0 | h0
    · left; simpa [apply] using h0
    · right; have := h0.mono (sent_subset_apply s (.processNack q a₀ n₀ ρ₀))
      simpa [apply] using this
  · intro p n d c hm
    simp only [apply, State.updP_decisions, State.updP_prop] at hm ⊢
    obtain ⟨h1, h2, h3⟩ := h.dec_quorum hm
    split_ifs with hpq
    · subst p; exact ⟨h1, h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  · intro p n d hm
    simp only [apply, State.updP_decisions, State.updP_sent] at hm ⊢
    exact h.dec_clean hm
  · intro p
    simp only [apply, State.updP_decisions, State.updP_prop]
    split_ifs with hpq
    · subst p; exact h.output_dec q
    · exact h.output_dec p

/-- Transfer of the invariant across an acceptor step (the remaining fields have to be
checked). -/
lemma frameAcc (h : Inv s) {s' : State P A Ln L}
    (hpr : ∀ {p n v}, Msg.proposal p n v ∈ s'.sent ↔ Msg.proposal p n v ∈ s.sent)
    (hsub : s.sent ⊆ s'.sent) (hP : s'.prop = s.prop) (hinit : s'.initiated = s.initiated)
    (hdec : s'.decisions = s.decisions) (hlacks : s'.lacks = s.lacks)
    (hlearnt : s'.learnt = s.learnt)
    (ack_prop : ∀ {a p n v}, Msg.ack a p n v ∈ s'.sent → Msg.proposal p n v ∈ s'.sent)
    (nack_prop : ∀ {a p n ρ}, Msg.nack a p n ρ ∈ s'.sent →
      ∃ v, Msg.proposal p n v ∈ s'.sent ∧ v < ρ)
    (ack_done : ∀ {a p n v}, Msg.ack a p n v ∈ s'.sent → (p, n) ∈ s'.adone a)
    (nack_done : ∀ {a p n v}, Msg.nack a p n v ∈ s'.sent → (p, n) ∈ s'.adone a)
    (resp_excl : ∀ {a p n v v'}, Msg.ack a p n v ∈ s'.sent → Msg.nack a p n v' ∈ s'.sent →
      False)
    (resp_le_acc : ∀ {a v}, v ∈ respVals s' a → v ≤ s'.acc a)
    (resp_chain : ∀ {a u v}, u ∈ respVals s' a → v ∈ respVals s' a → u ≤ v ∨ v ≤ u) :
    Inv s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ack_prop, nack_prop, ack_done, nack_done, resp_excl,
    resp_le_acc, resp_chain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p n v hm; rw [hP]; exact h.prop_range (hpr.1 hm)
  · intro p n h1 h2; rw [hP] at h2
    obtain ⟨v, hv⟩ := h.prop_exists h1 h2; exact ⟨v, hpr.2 hv⟩
  · intro p n v v' hm hm'; exact h.prop_unique (hpr.1 hm) (hpr.1 hm')
  · intro p n v hm; rw [hP]; exact h.prop_le (hpr.1 hm)
  · intro p n v v' hm hm'; exact h.prop_succ (hpr.1 hm) (hpr.1 hm')
  · intro p h1 h2; rw [hP] at h1 h2 ⊢; exact hsub (h.cur_val h1 h2)
  · intro p n a ha; rw [hP] at ha
    obtain ⟨v, hv⟩ := h.acks_sent ha; exact ⟨v, hsub hv⟩
  · intro p n a ha; rw [hP] at ha ⊢
    obtain ⟨ρ, hρ, hle⟩ := h.nacks_sent ha; exact ⟨ρ, hsub hρ, hle⟩
  · intro p n w h1 hm
    obtain ⟨R, hR, hR'⟩ := h.prev_quorum h1 (hpr.1 hm)
    refine ⟨R, hR, fun a ha => ?_⟩
    obtain ⟨ρ, hρ, hle⟩ := hR' a ha
    exact ⟨ρ, hρ.imp (fun x => hsub x) (fun x => hsub x), hle⟩
  · intro p h1 h2; rw [hP] at h1 h2 ⊢; exact h.passive_quorum h1 h2
  · intro p m hm; rw [hinit] at hm
    obtain ⟨v, hv⟩ := h.init_prop hm; exact ⟨v, hpr.2 hv⟩
  · intro p m hm h2; rw [hinit] at hm; rw [hP]; exact h.init_quorum hm h2
  · intro l p n a ha; rw [hlacks] at ha
    obtain ⟨v, hv⟩ := h.learn_sent ha; exact ⟨v, hsub hv⟩
  · intro l; rw [hlearnt]
    exact (h.learnt_chosen l).imp id (fun hc => hc.mono hsub)
  · intro p n d c hm; rw [hdec] at hm; rw [hP]; exact h.dec_quorum hm
  · intro p n d hm; rw [hdec] at hm; exact hsub (h.dec_clean hm)
  · intro p; rw [hP, hdec]; exact h.output_dec p

lemma accept (h : Inv s) {a₀ : A} {q : P} {n₀ : ℕ} {v₀ : L}
    (he : Enabled s (.accept a₀ q n₀ v₀)) : Inv (apply s (.accept a₀ q n₀ v₀)) := by
  obtain ⟨hm₀, hd₀, hle₀⟩ := he
  have hrv : ∀ a v, v ∈ respVals (apply s (.accept a₀ q n₀ v₀)) a ↔
      v ∈ respVals s a ∨ (a = a₀ ∧ v = v₀) := by
    intro a v
    simp only [respVals, apply, Finset.mem_insert, Msg.ack.injEq, reduceCtorEq, false_or,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, n, (⟨rfl, rfl, rfl, rfl⟩ | h1) | h1⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨p, n, Or.inl h1⟩
      · exact Or.inl ⟨p, n, Or.inr h1⟩
    · rintro (⟨p, n, h1 | h1⟩ | ⟨rfl, rfl⟩)
      · exact ⟨p, n, Or.inl (Or.inr h1)⟩
      · exact ⟨p, n, Or.inr h1⟩
      · exact ⟨q, n₀, Or.inl (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
  apply h.frameAcc
  · simp [apply]
  · exact sent_subset_apply _ _
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, Msg.ack.injEq, reduceCtorEq, false_or] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
    · exact hm₀
    · exact h.ack_prop hm
  · intro a p n ρ hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm ⊢
    obtain ⟨v, hv, hlt⟩ := h.nack_prop hm
    exact ⟨v, hv, hlt⟩
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, Msg.ack.injEq, reduceCtorEq, false_or,
      Function.update_apply] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
    · simp
    · have := h.ack_done hm
      split_ifs <;> simp_all
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, Function.update_apply] at hm ⊢
    have := h.nack_done hm
    split_ifs <;> simp_all
  · intro a p n v v' hm hm'
    simp only [apply, Finset.mem_insert, Msg.ack.injEq, reduceCtorEq, false_or] at hm hm'
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
    · exact hd₀ (h.nack_done hm')
    · exact h.resp_excl hm hm'
  · intro a v hv
    rw [hrv] at hv
    simp only [apply, Function.update_apply]
    rcases hv with hv | ⟨rfl, rfl⟩
    · have := h.resp_le_acc hv
      split_ifs with ha
      · subst ha; exact this.trans hle₀
      · exact this
    · simp
  · intro a u v hu hv
    rw [hrv] at hu hv
    rcases hu with hu | ⟨rfl, rfl⟩ <;> rcases hv with hv | ⟨ha, rfl⟩
    · exact h.resp_chain hu hv
    · subst ha; exact Or.inl ((h.resp_le_acc hu).trans hle₀)
    · exact Or.inr ((h.resp_le_acc hv).trans hle₀)
    · exact Or.inl le_rfl

lemma reject (h : Inv s) {a₀ : A} {q : P} {n₀ : ℕ} {v₀ : L}
    (he : Enabled s (.reject a₀ q n₀ v₀)) : Inv (apply s (.reject a₀ q n₀ v₀)) := by
  obtain ⟨hm₀, hd₀, hle₀⟩ := he
  have hrv : ∀ a v, v ∈ respVals (apply s (.reject a₀ q n₀ v₀)) a ↔
      v ∈ respVals s a ∨ (a = a₀ ∧ v = s.acc a₀ ⊔ v₀) := by
    intro a v
    simp only [respVals, apply, Finset.mem_insert, Msg.nack.injEq, reduceCtorEq, false_or,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, n, h1 | ⟨rfl, rfl, rfl, rfl⟩ | h1⟩
      · exact Or.inl ⟨p, n, Or.inl h1⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨p, n, Or.inr h1⟩
    · rintro (⟨p, n, h1 | h1⟩ | ⟨rfl, rfl⟩)
      · exact ⟨p, n, Or.inl h1⟩
      · exact ⟨p, n, Or.inr (Or.inr h1)⟩
      · exact ⟨q, n₀, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)⟩
  apply h.frameAcc
  · simp [apply]
  · exact sent_subset_apply _ _
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or] at hm ⊢
    exact h.ack_prop hm
  · intro a p n ρ hm
    simp only [apply, Finset.mem_insert, Msg.nack.injEq, reduceCtorEq, false_or] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
    · refine ⟨v₀, hm₀, lt_of_le_of_ne le_sup_right fun heq => hle₀ ?_⟩
      rw [heq]; exact le_sup_left
    · exact h.nack_prop hm
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, reduceCtorEq, false_or, Function.update_apply] at hm ⊢
    have := h.ack_done hm
    split_ifs <;> simp_all
  · intro a p n v hm
    simp only [apply, Finset.mem_insert, Msg.nack.injEq, reduceCtorEq, false_or,
      Function.update_apply] at hm ⊢
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
    · simp
    · have := h.nack_done hm
      split_ifs <;> simp_all
  · intro a p n v v' hm hm'
    simp only [apply, Finset.mem_insert, Msg.nack.injEq, reduceCtorEq, false_or] at hm hm'
    rcases hm' with ⟨rfl, rfl, rfl, rfl⟩ | hm'
    · exact hd₀ (h.ack_done hm)
    · exact h.resp_excl hm hm'
  · intro a v hv
    rw [hrv] at hv
    simp only [apply, Function.update_apply]
    rcases hv with hv | ⟨rfl, rfl⟩
    · have := h.resp_le_acc hv
      split_ifs with ha
      · subst ha; exact this.trans le_sup_left
      · exact this
    · simp
  · intro a u v hu hv
    rw [hrv] at hu hv
    rcases hu with hu | ⟨rfl, rfl⟩ <;> rcases hv with hv | ⟨ha, rfl⟩
    · exact h.resp_chain hu hv
    · subst ha; exact Or.inl ((h.resp_le_acc hu).trans le_sup_left)
    · exact Or.inr ((h.resp_le_acc hv).trans le_sup_left)
    · exact Or.inl le_rfl

lemma learn (h : Inv s) {l₀ : Ln} {a₀ : A} {q : P} {n₀ : ℕ} {v₀ : L}
    (he : Enabled s (.learn l₀ a₀ q n₀ v₀)) : Inv (apply s (.learn l₀ a₀ q n₀ v₀)) := by
  obtain ⟨hm₀, -⟩ := he
  apply h.frame
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · simp [apply]
  · intro p h1 h2; exact h.cur_val h1 h2
  · intro p n a ha; exact h.acks_sent ha
  · intro p n a ha; exact h.nacks_sent ha
  · intro p h1 h2; exact h.passive_quorum h1 h2
  · intro l p n a ha
    have hla : (apply s (.learn l₀ a₀ q n₀ v₀)).lacks l p n = if l = l₀ ∧ p = q ∧ n = n₀ then
        insert a₀ (s.lacks l₀ q n₀) else s.lacks l p n := by
      simp only [apply, Function.update_apply]
      by_cases h1 : l = l₀ <;> by_cases h2 : p = q <;> by_cases h3 : n = n₀ <;> simp_all
    rw [hla] at ha
    show ∃ v, Msg.ack a p n v ∈ s.sent
    split_ifs at ha with h1
    · obtain ⟨rfl, rfl, rfl⟩ := h1
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨v₀, hm₀⟩
      · exact h.learn_sent ha
    · exact h.learn_sent ha
  · intro l
    have key : ∀ x, Chosen s x → Chosen (apply s (.learn l₀ a₀ q n₀ v₀)) x :=
      fun x hc => hc.mono (sent_subset_apply _ _)
    have hl' : (apply s (.learn l₀ a₀ q n₀ v₀)).learnt l = if l = l₀ then
        (if quorum A ≤ (insert a₀ (s.lacks l₀ q n₀)).card ∧ s.learnt l₀ ≤ v₀ ∧
          ¬ v₀ ≤ s.learnt l₀ then v₀ else s.learnt l₀) else s.learnt l := by
      simp only [apply, Function.update_apply]
    rw [hl']
    split_ifs with hl hc
    · subst hl
      right
      refine key _ ⟨q, n₀, hc.1.trans (Finset.card_le_card ?_)⟩
      intro a ha
      simp only [ackers, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hm₀
      · obtain ⟨v, hv⟩ := h.learn_sent ha
        have := h.prop_unique (h.ack_prop hv) (h.ack_prop hm₀)
        subst this; exact hv
    · subst hl; exact (h.learnt_chosen l).imp id (key _)
    · exact (h.learnt_chosen l).imp id (key _)
  · intro p n d c hm; exact h.dec_quorum hm
  · intro p n d hm; exact h.dec_clean hm
  · intro p; exact h.output_dec p

/-- Preservation of the invariant by every enabled step. -/
lemma step (h : Inv s) {act : Action P A Ln L} (he : Enabled s act) : Inv (apply s act) := by
  cases act with
  | receive => exact h.receive
  | buffer => exact h.buffer
  | propose => exact h.propose he
  | processAck => exact h.processAck he
  | processNack => exact h.processNack he
  | refine => exact h.refine he
  | decide => exact h.decide he
  | accept => exact h.accept he
  | reject => exact h.reject he
  | learn => exact h.learn he

end Inv

/-- The invariant holds in every reachable state. -/
theorem Reachable.inv {b : P → L} {s : State P A Ln L} (h : Reachable b s) : Inv s := by
  induction h with
  | init => exact inv_init b
  | step act _ he ih => exact ih.step he

end Podc.GeneralizedLatticeAgreement
