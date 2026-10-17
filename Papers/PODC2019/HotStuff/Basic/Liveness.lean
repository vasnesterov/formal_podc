import Papers.PODC2019.HotStuff.Basic.LiveCore
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Basic HotStuff: liveness (Theorem 4)

**Theorem 4.** After GST, if all correct replicas are in view `v` and are not interrupted by the
pacemaker for `T_f = 8 (δ + 1)` time units, and the leader of `v` is correct, then every correct
replica commits the leader's proposal of view `v` within `T_f`.

The bound counts eight message delays (new-view, prepare, vote, pre-commit, vote, commit, vote,
decide), each of at most `δ + 1` time units in the CSLib model (delivery within `δ`, one step to
process).
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {leader : ℕ → P}
variable {R : Run P (Msg P C) (Inp C)} {δ : ℕ}

/-! ### Phase bound -/

theorem phase_le_handlers {p : P} {s : RState P C} (h : s.phase ≤ 3) :
    (handlers f leader p s).phase ≤ 3 := by
  have h1 : (LQ f leader p 3 (LQ f leader p 2 (LQ f leader p 1 (L1 f leader p s)))).phase ≤ 3 := by
    simpa using h
  have hR1 : ∀ s : RState P C, s.phase ≤ 3 → (R1 f leader p s).phase ≤ 3 := fun s h => by
    unfold R1; split_ifs
    · dsimp only; split_ifs <;> simp [RState.send]
    · exact h
  have hR2 : ∀ s : RState P C, s.phase ≤ 3 → (R2 f leader p s).phase ≤ 3 := fun s h => by
    unfold R2; split_ifs
    · simp [RState.send]
    · exact h
  have hR3 : ∀ s : RState P C, s.phase ≤ 3 → (R3 f leader p s).phase ≤ 3 := fun s h => by
    unfold R3; split_ifs
    · simp [RState.send]
    · exact h
  have hR4 : ∀ s : RState P C, s.phase ≤ 3 → (R4 f leader s).phase ≤ 3 := fun s h => by
    unfold R4; split_ifs
    · simp
    · exact h
  exact hR4 _ (hR3 _ (hR2 _ (hR1 _ h1)))

theorem st_phase_le (τ : ℕ) (p : P) : (R.st (hotstuff f leader) τ p).phase ≤ 3 := by
  induction τ with
  | zero => show (RState.init leader (R.inp p)).phase ≤ 3; simp [RState.init]
  | succ τ ih =>
    rw [st_succ_eq, stepR_eq]
    have := phase_le_handlers (f := f) (leader := leader) (p := p)
      (s := recv (R.st (hotstuff f leader) τ p) (R.inbox (hotstuff f leader) p τ)) ih
    split_ifs
    · simp
    · exact this

/-! ### Stages of the leader of view `v` -/

/-- Leader stage `k`: the leader of `v` has proposed, and has formed the QCs of the phases
`1, …, k − 1` (prepare, pre-commit, commit) for its proposal. -/
def LS (R : Run P (Msg P C) (Inp C)) (f : ℕ) (leader : ℕ → P) (v k τ : ℕ) : Prop :=
  ∃ x j, (v, x, j) ∈ (R.st (hotstuff f leader) τ (leader v)).props ∧
    ∀ k', 1 ≤ k' → k' < k →
      ∃ c ∈ (R.st (hotstuff f leader) τ (leader v)).made, c.qc = ⟨lty k', v, x⟩

theorem LS.mono {v k τ τ' : ℕ} (h : LS R f leader v k τ) (hτ : τ ≤ τ') : LS R f leader v k τ' := by
  obtain ⟨x, j, hx, hc⟩ := h
  have hg := st_grow (f := f) (leader := leader) R hτ (leader v)
  refine ⟨x, j, hg.props hx, fun k' h1 h2 => ?_⟩
  obtain ⟨c, hc', e⟩ := hc k' h1 h2
  exact ⟨c, hg.made hc', e⟩

theorem LS.anti {v k k' τ : ℕ} (h : LS R f leader v k τ) (hk : k' ≤ k) : LS R f leader v k' τ := by
  obtain ⟨x, j, hx, hc⟩ := h
  exact ⟨x, j, hx, fun k'' h1 h2 => hc k'' h1 (by omega)⟩

theorem lty_eq_commit {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3) (h : lty k = .commit) : k = 3 := by
  interval_cases k <;> simp_all [lty]

theorem lty_eq_prepare {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3) (h : lty k = .prepare) : k = 1 := by
  interval_cases k <;> simp_all [lty]

theorem lty_eq_precommit {k : ℕ} (h1 : 1 ≤ k) (h3 : k ≤ 3) (h : lty k = .precommit) : k = 2 := by
  interval_cases k <;> simp_all [lty]

/-- Proposals of a leader are unique per view, across time. -/
theorem prop_uniq {v τ τ' : ℕ} {x x' : Node C} {j j' : QCm P C}
    (h : (v, x, j) ∈ (R.st (hotstuff f leader) τ (leader v)).props)
    (h' : (v, x', j') ∈ (R.st (hotstuff f leader) τ' (leader v)).props) : x = x' := by
  have g := st_grow (f := f) (leader := leader) R (le_max_left τ τ') (leader v)
  have g' := st_grow (f := f) (leader := leader) R (le_max_right τ τ') (leader v)
  exact ((st_LI (f := f) (leader := leader) R _ (leader v)).props_uniq v x j x' j' (g.props h) (g'.props h')).1

/-- A correct replica that decided in view `v` decided the leader's proposal, and the leader
has formed all its QCs. -/
theorem decided_LS4 (hℓ : leader v ∉ R.faulty) {r : P} {τ : ℕ} {y : Node C}
    (hy : (v, y) ∈ (R.st (hotstuff f leader) τ r).decs) :
    ∃ j, (v, y, j) ∈ (R.st (hotstuff f leader) τ (leader v)).props ∧
      ∀ k', 1 ≤ k' → k' < 4 →
        ∃ c ∈ (R.st (hotstuff f leader) τ (leader v)).made, c.qc = ⟨lty k', v, y⟩ := by
  obtain ⟨-, c, hcbuf, hty, hv, hn⟩ := (st_LI (f := f) (leader := leader) R τ r).decs_ok v y hy
  have hsent := genuine' hℓ hcbuf
  have hmade := (st_LI (f := f) (leader := leader) R τ (leader v)).sent_cert _ _ hsent
  obtain ⟨k, hk1, hk3, hlty, ⟨j, hj⟩, -, hearly, -⟩ := (st_LI (f := f) (leader := leader) R τ (leader v)).made_ok c hmade
  have hk : k = 3 := lty_eq_commit hk1 hk3 (hlty ▸ hty)
  subst hk
  rw [hv, hn] at hj hearly
  refine ⟨j, hj, fun k' h1 h2 => ?_⟩
  rcases Nat.lt_or_ge k' 3 with h | h
  · exact hearly k' h1 h
  · obtain rfl : k' = 3 := by omega
    refine ⟨c, hmade, ?_⟩
    obtain ⟨⟨t, w, n⟩, sg⟩ := c
    simp only at hty hv hn
    subst hty hv hn
    rfl

theorem LS4_of_decided (hℓ : leader v ∉ R.faulty) {r : P} {τ : ℕ} {y : Node C}
    (hy : (v, y) ∈ (R.st (hotstuff f leader) τ r).decs) : LS R f leader v 4 τ := by
  obtain ⟨j, hj, hc⟩ := decided_LS4 hℓ hy
  exact ⟨y, j, hj, hc⟩

/-- **Voting.** A correct replica in view `v` with phase `≥ k` has cast its `k`-th vote for the
proposal of the (correct) leader. -/
theorem voted_of_phase (hR : R.Valid f δ) (hA : R.AuthValid auth (hotstuff f leader))
    (h3 : 3 * f < Fintype.card P) {v : ℕ} (hℓ : leader v ∉ R.faulty) {r : P} (hr : r ∉ R.faulty)
    {τ τ' : ℕ} {x : Node C} {j : QCm P C}
    (hx : (v, x, j) ∈ (R.st (hotstuff f leader) τ' (leader v)).props)
    (hv : (R.st (hotstuff f leader) τ r).view = v) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hk : k ≤ (R.st (hotstuff f leader) τ r).phase) :
    (⟨lty k, v, x⟩ : QC C) ∈ (R.st (hotstuff f leader) τ r).votes := by
  have hI := st_LI (f := f) (leader := leader) R τ r
  interval_cases k
  · obtain ⟨x', j', l, hr1, hbuf, hg⟩ := hI.ph1 hk
    rw [hv] at hr1 hbuf hg
    have hp := (st_LI (f := f) (leader := leader) R τ (leader v)).sent_prep _ _ _ _ (genuine' hℓ hbuf)
    have hxx := prop_uniq hx hp
    subst hxx
    obtain ⟨hlv, hl⟩ := hI.r1_ok _ _ _ _ hr1
    obtain ⟨-, -, hxe, hjok, -⟩ := (st_LI (f := f) (leader := leader) R τ (leader v)).props_ok v x j' hp
    refine hg ⟨hjok, by rw [hxe]; exact List.suffix_cons _ _, ?_⟩
    exact safeNode_of_correct_leader hR hA h3 hℓ hp hr hlv hl
  · obtain ⟨c, hbuf, hty, hcv, hvote⟩ := hI.ph2 hk
    rw [hv] at hbuf hvote
    have hm := (st_LI (f := f) (leader := leader) R τ (leader v)).sent_cert _ _ (genuine' hℓ hbuf)
    obtain ⟨-, -, -, -, ⟨j', hj'⟩, -⟩ := (st_LI (f := f) (leader := leader) R τ (leader v)).made_ok c hm
    rw [hcv, hv] at hj'
    have := prop_uniq hx hj'
    rw [this]; exact hvote
  · obtain ⟨c, hbuf, hty, hcv, hvote⟩ := hI.ph3 hk
    rw [hv] at hbuf hvote
    have hm := (st_LI (f := f) (leader := leader) R τ (leader v)).sent_cert _ _ (genuine' hℓ hbuf)
    obtain ⟨-, -, -, -, ⟨j', hj'⟩, -⟩ := (st_LI (f := f) (leader := leader) R τ (leader v)).made_ok c hm
    rw [hcv, hv] at hj'
    have := prop_uniq hx hj'
    rw [this]; exact hvote

/-! ### Handler sequences -/

theorem handlers_eq (p : P) (s : RState P C) : handlers f leader p s =
    R4 f leader (R3 f leader p (R2 f leader p (R1 f leader p
      (LQ f leader p 3 (LQ f leader p 2 (LQ f leader p 1 (L1 f leader p s))))))) := rfl

theorem grow_after_R (p : P) (s : RState P C) :
    Grow s (R4 f leader (R3 f leader p (R2 f leader p (R1 f leader p s)))) :=
  (grow_R1 s).trans <| (grow_R2 _).trans <| (grow_R3 _).trans (grow_R4 _)

theorem grow_after_L1 (p : P) (s : RState P C) :
    Grow (L1 f leader p s) (handlers f leader p s) :=
  ((grow_LQ 1 _).trans ((grow_LQ 2 _).trans (grow_LQ 3 _))).trans (grow_after_R p _)

theorem leader_forms {p : P} {s : RState P C} {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3)
    (hl : s.lphase = k) (hp : p = leader s.view)
    (hc : Fintype.card P - f ≤ (voters s ⟨lty k, s.view, s.prop⟩).card) :
    ∃ c ∈ (handlers f leader p s).made, c.qc = ⟨lty k, s.view, s.prop⟩ := by
  rw [handlers_eq, L1_of_ne (by omega)]
  interval_cases k
  · obtain ⟨c, hc', e⟩ := LQ_fires (f := f) (leader := leader) hl hp hc
    exact ⟨c, (((grow_LQ 2 _).trans (grow_LQ 3 _)).trans (grow_after_R p _)).made hc', e⟩
  · rw [LQ_of_ne (k := 1) (by omega)]
    obtain ⟨c, hc', e⟩ := LQ_fires (f := f) (leader := leader) hl hp hc
    exact ⟨c, ((grow_LQ 3 _).trans (grow_after_R p _)).made hc', e⟩
  · rw [LQ_of_ne (k := 1) (by omega), LQ_of_ne (k := 2) (by omega)]
    obtain ⟨c, hc', e⟩ := LQ_fires (f := f) (leader := leader) hl hp hc
    exact ⟨c, (grow_after_R p _).made hc', e⟩

theorem HasCert.congr {ty : Phase} {s s' : RState P C} {c : QCm P C}
    (h : HasCert f leader ty s c) (hb : s'.buf = s.buf) (hv : s'.view = s.view) :
    HasCert f leader ty s' c := by
  unfold HasCert at *; rw [hb, hv]; exact h

/-- One step of a correct replica in view `v` that has received the leader's messages of the
stages `< k`: it reaches phase `k` (or decides). -/
theorem replica_step {v : ℕ} {r : P} {τ : ℕ} (hint : (R.inp r).1 τ = false)
    (hv : (R.st (hotstuff f leader) τ r).view = v) {k : ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hb1 : ∃ xj : Node C × QCm P C, (leader v, Msg.prepare v xj.1 xj.2) ∈
      (recv (R.st (hotstuff f leader) τ r) (R.inbox (hotstuff f leader) r τ)).buf)
    (hb : ∀ k', 2 ≤ k' → k' ≤ k → ∃ c, HasCert f leader (lty (k' - 1))
      (recv (R.st (hotstuff f leader) τ r) (R.inbox (hotstuff f leader) r τ)) c) :
    ((R.st (hotstuff f leader) (τ + 1) r).view = v ∧
        k ≤ (R.st (hotstuff f leader) (τ + 1) r).phase) ∨
      ∃ y, (v, y) ∈ (R.st (hotstuff f leader) (τ + 1) r).decs := by
  obtain ⟨s0, hs0⟩ : ∃ s, s = recv (R.st (hotstuff f leader) τ r)
      (R.inbox (hotstuff f leader) r τ) := ⟨_, rfl⟩
  rw [← hs0] at hb1 hb
  have e0 : s0.view = v := by rw [hs0]; exact hv
  obtain ⟨s1, hs1⟩ : ∃ s, s = LQ f leader r 3 (LQ f leader r 2 (LQ f leader r 1
      (L1 f leader r s0))) := ⟨_, rfl⟩
  have e1 : s1.view = v := by simp [hs1, e0]
  have e1b : s1.buf = s0.buf := by simp [hs1]
  obtain ⟨sA, hsA⟩ : ∃ s, s = R1 f leader r s1 := ⟨_, rfl⟩
  obtain ⟨sB, hsB⟩ : ∃ s, s = R2 f leader r sA := ⟨_, rfl⟩
  obtain ⟨sC, hsC⟩ : ∃ s, s = R3 f leader r sB := ⟨_, rfl⟩
  have hst : R.st (hotstuff f leader) (τ + 1) r = R4 f leader sC := by
    rw [st_succ_noint hint, hsC, hsB, hsA, hs1, hs0]; rfl
  have eA : sA.view = v ∧ sA.buf = s0.buf := by simp [hsA, e1, e1b]
  have eB : sB.view = v ∧ sB.buf = s0.buf := by simp [hsB, eA]
  have eC : sC.view = v ∧ sC.buf = s0.buf := by simp [hsC, eB]
  have hA : 1 ≤ sA.phase := by
    rw [hsA]
    rcases Nat.eq_zero_or_pos s1.phase with h0 | h0
    · exact R1_fires h0 (by rw [e1, e1b]; exact hb1)
    · exact h0.trans_le (R1_phase (f := f) (leader := leader) (p := r) s1)
  have hB : min k 2 ≤ sB.phase := by
    have hm := R2_phase (f := f) (leader := leader) (p := r) sA
    rw [← hsB] at hm
    by_cases hk : 2 ≤ k
    · rcases Nat.lt_or_ge sA.phase 2 with h | h
      · obtain ⟨c, hc⟩ := hb 2 le_rfl hk
        have := R2_fires (f := f) (leader := leader) (p := r) (s := sA) (by omega)
          ⟨c, hc.congr eA.2 (by rw [eA.1, e0])⟩
        rw [← hsB] at this
        omega
      · omega
    · omega
  have hC : min k 3 ≤ sC.phase := by
    have hm := R3_phase (f := f) (leader := leader) (p := r) sB
    rw [← hsC] at hm
    by_cases hk : 3 ≤ k
    · rcases Nat.lt_or_ge sB.phase 3 with h | h
      · obtain ⟨c, hc⟩ := hb 3 (by norm_num) hk
        have := R3_fires (f := f) (leader := leader) (p := r) (s := sB) (by omega)
          ⟨c, hc.congr eB.2 (by rw [eB.1, e0])⟩
        rw [← hsC] at this
        omega
      · omega
    · omega
  rw [hst]
  rcases R4_cases (f := f) (leader := leader) sC with h4 | ⟨-, y, hy⟩
  · rw [h4]
    by_cases hk : k ≤ 3
    · left; exact ⟨eC.1, by omega⟩
    · right
      have hle : sC.phase ≤ 3 := by
        have := st_phase_le (R := R) (f := f) (leader := leader) (τ + 1) r
        rwa [hst, h4] at this
      obtain ⟨c, hc⟩ := hb 4 (by norm_num) (by omega)
      obtain ⟨y, hy⟩ := R4_fires (f := f) (leader := leader) (s := sC) (by omega)
        ⟨c, hc.congr eC.2 (by rw [eC.1, e0])⟩
      rw [h4, eC.1] at hy
      exact ⟨y, hy⟩
  · right; rw [eC.1] at hy; exact ⟨y, hy⟩

theorem lty_inj {a b : ℕ} (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hb1 : 1 ≤ b) (hb3 : b ≤ 3)
    (h : lty a = lty b) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [lty]

/-! ### The synchronous view -/

section View

variable {v t₀ : ℕ}

theorem view_window
    (hview : ∀ p ∉ R.faulty, (R.st (hotstuff f leader) t₀ p).view = v)
    (hnv : ∀ p ∉ R.faulty, ∀ τ, t₀ ≤ τ → τ < t₀ + 8 * (δ + 1) → (R.inp p).1 τ = false)
    {r : P} (hr : r ∉ R.faulty) {τ : ℕ} (h1 : t₀ ≤ τ) (h2 : τ ≤ t₀ + 8 * (δ + 1)) :
    v ≤ (R.st (hotstuff f leader) τ r).view ∧
      (v < (R.st (hotstuff f leader) τ r).view →
        ∃ y, (v, y) ∈ (R.st (hotstuff f leader) τ r).decs) := by
  induction τ, h1 using Nat.le_induction with
  | base => rw [hview r hr]; exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
  | succ τ hτ ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hint := hnv r hr τ hτ (by omega)
    have hg : Grow (R.st (hotstuff f leader) τ r) (R.st (hotstuff f leader) (τ + 1) r) :=
      st_grow (f := f) (leader := leader) R (Nat.le_succ τ) r
    rw [st_succ_noint hint, handlers_eq] at hg ⊢
    obtain ⟨X, hX⟩ : ∃ X, X = R3 f leader r (R2 f leader r (R1 f leader r (LQ f leader r 3
        (LQ f leader r 2 (LQ f leader r 1 (L1 f leader r (recv (R.st (hotstuff f leader) τ r)
        (R.inbox (hotstuff f leader) r τ)))))))) := ⟨_, rfl⟩
    have hXv : X.view = (R.st (hotstuff f leader) τ r).view := by simp [hX, recv]
    rw [← hX] at hg ⊢
    rcases R4_cases (f := f) (leader := leader) X with h4 | ⟨h4v, y, hy⟩
    · rw [h4] at hg ⊢; rw [hXv]
      exact ⟨ih1, fun h => (ih2 h).imp fun y hy => hg.decs hy⟩
    · rw [h4v, hXv]
      refine ⟨by omega, fun _ => ?_⟩
      rcases eq_or_lt_of_le ih1 with e | e
      · rw [hXv, ← e] at hy; exact ⟨y, hy⟩
      · obtain ⟨y', hy'⟩ := ih2 e; exact ⟨y', hg.decs hy'⟩

/-- The leader's stage messages are in the buffer of every correct replica `δ` after they were
logged (after GST). -/
theorem stage_buf (hR : R.Valid f δ) (hgst : R.gst ≤ t₀) (hℓ : leader v ∉ R.faulty)
    {X τ k : ℕ} (hX : t₀ ≤ X) (hτ : X + δ ≤ τ) {x : Node C} {j : QCm P C}
    (hx : (v, x, j) ∈ (R.st (hotstuff f leader) X (leader v)).props)
    (hc : ∀ k', 1 ≤ k' → k' < k →
      ∃ c ∈ (R.st (hotstuff f leader) X (leader v)).made, c.qc = ⟨lty k', v, x⟩)
    {r : P} (hr : r ∉ R.faulty) (hv : (R.st (hotstuff f leader) τ r).view = v) :
    (∃ xj : Node C × QCm P C, (leader v, Msg.prepare v xj.1 xj.2) ∈
      (recv (R.st (hotstuff f leader) τ r) (R.inbox (hotstuff f leader) r τ)).buf) ∧
    ∀ k', 2 ≤ k' → k' ≤ k → ∃ c, HasCert f leader (lty (k' - 1))
      (recv (R.st (hotstuff f leader) τ r) (R.inbox (hotstuff f leader) r τ)) c := by
  have hdel : ∀ m, (r, m) ∈ (R.st (hotstuff f leader) X (leader v)).sent →
      (leader v, m) ∈ (recv (R.st (hotstuff f leader) τ r) (R.inbox (hotstuff f leader) r τ)).buf := by
    intro m hm
    obtain ⟨a, ha, hout⟩ := sent_out R hm
    exact deliver hR hℓ hr hout (by omega)
  refine ⟨⟨(x, j), hdel _ (((st_LI (f := f) (leader := leader) R X (leader v)).props_ok v x j hx).2.2.2.2.2.2 r)⟩,
    fun k' h2 hk => ?_⟩
  obtain ⟨c, hcm, hcq⟩ := hc (k' - 1) (by omega) (by omega)
  obtain ⟨-, -, -, -, -, hsent, -⟩ := (st_LI (f := f) (leader := leader) R X (leader v)).made_ok c hcm
  refine ⟨c, ?_, by rw [hcq], by rw [hcq]; simp [recv, hv], st_madeOk R X (leader v) c hcm⟩
  have : (recv (R.st (hotstuff f leader) τ r) (R.inbox (hotstuff f leader) r τ)).view = v := hv
  rw [this]; exact hdel _ (hsent r)

/-- A decision in view `v` by a correct replica is a decision on the leader's proposal `x`. -/
theorem committed_of_decs (hℓ : leader v ∉ R.faulty) {X τ : ℕ} {x : Node C} {j : QCm P C}
    (hx : (v, x, j) ∈ (R.st (hotstuff f leader) X (leader v)).props) {r : P} {y : Node C}
    (hy : (v, y) ∈ (R.st (hotstuff f leader) τ r).decs) :
    x ∈ (R.st (hotstuff f leader) τ r).committed := by
  obtain ⟨j', hj', -⟩ := decided_LS4 hℓ hy
  have := prop_uniq hx hj'
  subst this
  exact ((st_LI (f := f) (leader := leader) R τ r).decs_ok v x hy).1

/-- **Stage 1**: the leader proposes by `t₀ + δ + 1`. -/
theorem propose (hR : R.Valid f δ) (hgst : R.gst ≤ t₀) (hℓ : leader v ∉ R.faulty)
    (hview : ∀ p ∉ R.faulty, (R.st (hotstuff f leader) t₀ p).view = v)
    (hnv : ∀ p ∉ R.faulty, ∀ τ, t₀ ≤ τ → τ < t₀ + 8 * (δ + 1) → (R.inp p).1 τ = false) :
    LS R f leader v 1 (t₀ + δ + 1) := by
  by_cases hd : ∃ r ∉ R.faulty, ∃ y, (v, y) ∈ (R.st (hotstuff f leader) (t₀ + δ + 1) r).decs
  · obtain ⟨r, -, y, hy⟩ := hd
    exact (LS4_of_decided hℓ hy).anti (by norm_num)
  push Not at hd
  have hw := view_window hview hnv hℓ (τ := t₀ + δ) (by omega) (by omega)
  have hvℓ : (R.st (hotstuff f leader) (t₀ + δ) (leader v)).view = v := by
    rcases eq_or_lt_of_le hw.1 with e | e
    · exact e.symm
    · obtain ⟨y, hy⟩ := hw.2 e
      exact absurd ((st_grow (f := f) (leader := leader) R (Nat.le_succ _) _).decs hy)
        (hd _ hℓ y)
  have hI := st_LI (f := f) (leader := leader) R (t₀ + δ) (leader v)
  rcases Nat.eq_zero_or_pos (R.st (hotstuff f leader) (t₀ + δ) (leader v)).lphase with h0 | h0
  · -- the leader proposes in this step
    have hint := hnv _ hℓ (t₀ + δ) (by omega) (by omega)
    have hcard : Fintype.card P - f ≤ (nvSenders f (recv (R.st (hotstuff f leader) (t₀ + δ)
        (leader v)) (R.inbox (hotstuff f leader) (leader v) (t₀ + δ)))).card := by
      refine (Finset.card_sub_le_card_filter_notMem hR.card_faulty).trans
        (Finset.card_le_card fun q hq => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hIq := st_LI (f := f) (leader := leader) R t₀ q
      obtain ⟨jq, hjq⟩ := hIq.nv_cur
      rw [hview q hq] at hjq
      obtain ⟨-, hok, -⟩ := hIq.nv_sent _ _ _ hjq
      obtain ⟨a, ha, hout⟩ := sent_out R hjq
      have := deliver hR hq hℓ hout (τ := t₀ + δ) (by omega)
      simp only [nvSenders, Finset.mem_filter, Finset.mem_univ, true_and]
      have hv' : (recv (R.st (hotstuff f leader) (t₀ + δ) (leader v))
          (R.inbox (hotstuff f leader) (leader v) (t₀ + δ))).view = v := hvℓ
      rw [hv']
      exact ⟨jq, this, hok⟩
    obtain ⟨s0, hs0⟩ : ∃ s, s = recv (R.st (hotstuff f leader) (t₀ + δ) (leader v))
        (R.inbox (hotstuff f leader) (leader v) (t₀ + δ)) := ⟨_, rfl⟩
    have hs0v : s0.view = v := by rw [hs0]; exact hvℓ
    have hs0l : s0.lphase = 0 := by rw [hs0]; exact h0
    rw [← hs0] at hcard
    obtain ⟨-, x, j, hxj⟩ := L1_fires (f := f) (leader := leader) (p := leader v) (s := s0) hs0l
      (by rw [hs0v]) hcard
    refine ⟨x, j, ?_, fun k' h1 h2 => by omega⟩
    have hst : R.st (hotstuff f leader) (t₀ + δ + 1) (leader v) =
        handlers f leader (leader v) s0 := by rw [st_succ_noint hint, hs0]
    rw [hst]
    have := (grow_after_L1 (f := f) (leader := leader) (leader v) s0).props hxj
    rwa [hs0v] at this
  · have := hI.props_cur h0
    rw [hvℓ] at this
    exact LS.mono ⟨_, _, this, fun k' h1 h2 => by omega⟩ (Nat.le_succ _)

/-- **Stages 2–4**: from leader stage `k` at time `X`, the replicas vote within `δ + 1` and the
leader forms the next QC within another `δ + 1`. -/
theorem leader_step (hR : R.Valid f δ) (hA : R.AuthValid auth (hotstuff f leader))
    (h3 : 3 * f < Fintype.card P) (hgst : R.gst ≤ t₀) (hℓ : leader v ∉ R.faulty)
    (hview : ∀ p ∉ R.faulty, (R.st (hotstuff f leader) t₀ p).view = v)
    (hnv : ∀ p ∉ R.faulty, ∀ τ, t₀ ≤ τ → τ < t₀ + 8 * (δ + 1) → (R.inp p).1 τ = false)
    {k X : ℕ} (hk1 : 1 ≤ k) (hk3 : k ≤ 3) (hX : t₀ ≤ X) (hXT : X + 2 * δ + 1 < t₀ + 8 * (δ + 1))
    (hLS : LS R f leader v k X) : LS R f leader v (k + 1) (X + 2 * δ + 2) := by
  by_cases hd : ∃ r ∉ R.faulty, ∃ y, (v, y) ∈ (R.st (hotstuff f leader) (X + 2 * δ + 2) r).decs
  · obtain ⟨r, -, y, hy⟩ := hd
    exact (LS4_of_decided hℓ hy).anti (by omega)
  push Not at hd
  have hnd : ∀ r ∉ R.faulty, ∀ τ ≤ X + 2 * δ + 2, ∀ y,
      (v, y) ∉ (R.st (hotstuff f leader) τ r).decs := fun r hr τ hτ y hy =>
    hd r hr y ((st_grow (f := f) (leader := leader) R hτ r).decs hy)
  have hview_eq : ∀ r ∉ R.faulty, ∀ τ, t₀ ≤ τ → τ ≤ X + 2 * δ + 2 →
      (R.st (hotstuff f leader) τ r).view = v := by
    intro r hr τ h1 h2
    have hw := view_window hview hnv hr (τ := τ) h1 (by omega)
    rcases eq_or_lt_of_le hw.1 with e | e
    · exact e.symm
    · obtain ⟨y, hy⟩ := hw.2 e; exact absurd hy (hnd r hr τ h2 y)
  obtain ⟨x, j, hx, hc⟩ := hLS
  -- every correct replica casts its `k`-th vote by `X + δ + 1`
  have hvote : ∀ r ∉ R.faulty,
      (⟨lty k, v, x⟩ : QC C) ∈ (R.st (hotstuff f leader) (X + δ + 1) r).votes := by
    intro r hr
    have hv := hview_eq r hr (X + δ) (by omega) (by omega)
    obtain ⟨hb1, hb⟩ := stage_buf hR hgst hℓ hX le_rfl hx hc hr hv
    rcases replica_step (hnv r hr (X + δ) (by omega) (by omega)) hv hk1 (by omega) hb1 hb with
      ⟨hv', hph⟩ | ⟨y, hy⟩
    · exact voted_of_phase hR hA h3 hℓ hr hx hv' hk1 hk3 hph
    · exact absurd hy (hnd r hr _ (by omega) y)
  -- the leader receives them by step `X + 2δ + 1`
  set Z := X + 2 * δ + 1 with hZ
  have hvℓ := hview_eq _ hℓ Z (by omega) (by omega)
  obtain ⟨s0, hs0⟩ : ∃ s, s = recv (R.st (hotstuff f leader) Z (leader v))
      (R.inbox (hotstuff f leader) (leader v) Z) := ⟨_, rfl⟩
  have hbuf : ∀ r ∉ R.faulty, (r, Msg.vote r (⟨lty k, v, x⟩ : QC C)) ∈ s0.buf := by
    intro r hr
    have hs := (st_LI (f := f) (leader := leader) R _ r).votes_sent _ (hvote r hr)
    obtain ⟨a, ha, hout⟩ := sent_out R hs
    rw [hs0]; exact deliver hR hr hℓ hout (by omega)
  have hIℓ := st_LI (f := f) (leader := leader) R Z (leader v)
  have hxZ := (st_grow (f := f) (leader := leader) R (show X ≤ Z by omega) (leader v)).props hx
  have hcZ : ∀ k', 1 ≤ k' → k' < k → ∃ c ∈ (R.st (hotstuff f leader) Z (leader v)).made,
      c.qc = ⟨lty k', v, x⟩ := fun k' h1 h2 => by
    obtain ⟨c, hcm, e⟩ := hc k' h1 h2
    exact ⟨c, (st_grow (f := f) (leader := leader) R (show X ≤ Z by omega) (leader v)).made hcm, e⟩
  -- the leader's progress in view `v`
  have hl1 : 1 ≤ (R.st (hotstuff f leader) Z (leader v)).lphase :=
    hIℓ.props_lph x j (by rw [hvℓ]; exact hxZ)
  have hlk : k ≤ (R.st (hotstuff f leader) Z (leader v)).lphase := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · omega
    obtain ⟨c, hcm, e⟩ := hcZ (k - 1) (by omega) (by omega)
    obtain ⟨kc, hkc1, hkc3, hty, -, -, -, hcur⟩ := hIℓ.made_ok c hcm
    have : kc = k - 1 := lty_inj hkc1 hkc3 (by omega) (by omega) (by rw [← hty, e])
    have := hcur (by rw [e, hvℓ])
    omega
  have hprop : (R.st (hotstuff f leader) Z (leader v)).prop = x := by
    have := hIℓ.props_cur hl1
    rw [hvℓ] at this
    exact (hIℓ.props_uniq _ _ _ _ _ this hxZ).1
  have hfinal : ∃ c ∈ (R.st (hotstuff f leader) (Z + 1) (leader v)).made,
      c.qc = ⟨lty k, v, x⟩ := by
    rcases Nat.lt_or_ge k (R.st (hotstuff f leader) Z (leader v)).lphase with hlt | hge
    · obtain ⟨c, hcm, e⟩ := hIℓ.made_cur k hk1 hk3 hlt
      refine ⟨c, (st_grow (f := f) (leader := leader) R (Nat.le_succ Z) (leader v)).made hcm, ?_⟩
      rw [e, hvℓ, hprop]
    · have hint := hnv _ hℓ Z (by omega) (by omega)
      have hst : R.st (hotstuff f leader) (Z + 1) (leader v) = handlers f leader (leader v) s0 := by
        rw [st_succ_noint hint, hs0]
      have hs0v : s0.view = v := by rw [hs0]; exact hvℓ
      have hs0l : s0.lphase = k := by rw [hs0]; exact le_antisymm hge hlk
      have hs0p : s0.prop = x := by rw [hs0]; exact hprop
      have hcard : Fintype.card P - f ≤ (voters s0 ⟨lty k, s0.view, s0.prop⟩).card := by
        refine (Finset.card_sub_le_card_filter_notMem hR.card_faulty).trans
          (Finset.card_le_card fun q hq => ?_)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        simp only [voters, Finset.mem_filter, Finset.mem_univ, true_and, hs0v, hs0p]
        exact ⟨q, hbuf q hq⟩
      obtain ⟨c, hcm, e⟩ := leader_forms (f := f) (leader := leader) (p := leader v) hk1 hk3 hs0l
        (by rw [hs0v]) hcard
      rw [hst]
      exact ⟨c, hcm, by rw [e, hs0v, hs0p]⟩
  refine ⟨x, j, (st_grow (f := f) (leader := leader) R (Nat.le_succ Z) (leader v)).props hxZ,
    fun k' h1 h2 => ?_⟩
  rcases Nat.lt_or_ge k' k with h | h
  · obtain ⟨c, hcm, e⟩ := hcZ k' h1 h
    exact ⟨c, (st_grow (f := f) (leader := leader) R (Nat.le_succ Z) (leader v)).made hcm, e⟩
  · obtain rfl : k' = k := by omega
    exact hfinal

/-- **Final stage**: after the commit QC is formed, every correct replica decides within
`δ + 1`. -/
theorem decide_stage (hR : R.Valid f δ) (hgst : R.gst ≤ t₀) (hℓ : leader v ∉ R.faulty)
    (hview : ∀ p ∉ R.faulty, (R.st (hotstuff f leader) t₀ p).view = v)
    (hnv : ∀ p ∉ R.faulty, ∀ τ, t₀ ≤ τ → τ < t₀ + 8 * (δ + 1) → (R.inp p).1 τ = false)
    {X : ℕ} (hX : t₀ ≤ X) (hXT : X + δ < t₀ + 8 * (δ + 1)) {x : Node C} {j : QCm P C}
    (hx : (v, x, j) ∈ (R.st (hotstuff f leader) X (leader v)).props)
    (hc : ∀ k', 1 ≤ k' → k' < 4 →
      ∃ c ∈ (R.st (hotstuff f leader) X (leader v)).made, c.qc = ⟨lty k', v, x⟩)
    {r : P} (hr : r ∉ R.faulty) :
    x ∈ (R.st (hotstuff f leader) (X + δ + 1) r).committed := by
  have hw := view_window hview hnv hr (τ := X + δ) (by omega) (by omega)
  rcases eq_or_lt_of_le hw.1 with e | e
  · obtain ⟨hb1, hb⟩ := stage_buf hR hgst hℓ hX le_rfl hx hc hr e.symm
    rcases replica_step (hnv r hr (X + δ) (by omega) hXT) e.symm (by norm_num) le_rfl hb1 hb with
      ⟨-, hph⟩ | ⟨y, hy⟩
    · have := st_phase_le (R := R) (f := f) (leader := leader) (X + δ + 1) r; omega
    · exact committed_of_decs hℓ hx hy
  · obtain ⟨y, hy⟩ := hw.2 e
    exact committed_mono R (Nat.le_succ _) r (committed_of_decs hℓ hx hy)

end View

/-- **Theorem 4** (liveness). Let `R` be a run of Basic HotStuff in the partially synchronous
model (at most `f` Byzantine replicas, `3f < n`, unforgeable signatures, messages between correct
replicas delivered within `δ` after GST). Suppose that at some time `t₀ ≥ GST` all correct
replicas are in view `v`, the leader of `v` is correct, and the pacemaker does not interrupt any
correct replica during `[t₀, t₀ + T_f)` with `T_f = 8 (δ + 1)`. Then by `t₀ + T_f` every correct
replica has committed the leader's proposal of view `v`, a node `cmd :: highQC.node` carrying
the leader's new client command `cmd`. -/
theorem theorem_4 (hR : R.Valid f δ) (hA : R.AuthValid auth (hotstuff f leader))
    (h3 : 3 * f < Fintype.card P) {v t₀ : ℕ} (hgst : R.gst ≤ t₀) (hℓ : leader v ∉ R.faulty)
    (hview : ∀ p ∉ R.faulty, (R.st (hotstuff f leader) t₀ p).view = v)
    (hnv : ∀ p ∉ R.faulty, ∀ τ, t₀ ≤ τ → τ < t₀ + 8 * (δ + 1) → (R.inp p).1 τ = false) :
    ∃ x j, (v, x, j) ∈ (R.st (hotstuff f leader) (t₀ + 8 * (δ + 1)) (leader v)).props ∧
      x = (R.inp (leader v)).2 v :: j.qc.node ∧
      ∀ r ∉ R.faulty, x ∈ (R.st (hotstuff f leader) (t₀ + 8 * (δ + 1)) r).committed := by
  have s1 := propose hR hgst hℓ hview hnv
  have s2 := leader_step hR hA h3 hgst hℓ hview hnv (k := 1) le_rfl (by norm_num) (by omega)
    (by omega) s1
  have s3 := leader_step hR hA h3 hgst hℓ hview hnv (k := 2) (by norm_num) (by norm_num)
    (by omega) (by omega) s2
  have s4 := leader_step hR hA h3 hgst hℓ hview hnv (k := 3) (by norm_num) le_rfl
    (by omega) (by omega) s3
  obtain ⟨x, j, hx, hc⟩ := s4
  have hT : t₀ + 8 * (δ + 1) = t₀ + δ + 1 + 2 * δ + 2 + 2 * δ + 2 + 2 * δ + 2 + δ + 1 := by ring
  have hpx := (st_grow (f := f) (leader := leader) R (show t₀ + δ + 1 + 2 * δ + 2 + 2 * δ + 2 +
    2 * δ + 2 ≤ t₀ + 8 * (δ + 1) by omega) (leader v)).props hx
  refine ⟨x, j, hpx, ?_, fun r hr => ?_⟩
  · have := ((st_LI (f := f) (leader := leader) R _ (leader v)).props_ok v x j hpx).2.2.1
    rwa [st_inp] at this
  · rw [hT]
    exact decide_stage hR hgst hℓ hview hnv (by omega) (by omega) hx hc hr

end HotStuff.Basic
