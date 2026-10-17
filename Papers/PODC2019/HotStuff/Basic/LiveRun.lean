import Papers.PODC2019.HotStuff.Basic.LiveSteps

/-!
# Basic HotStuff implementation: facts about runs used by the liveness proof

Local invariants hold at all times, logs grow, logged messages were sent, messages between correct
replicas are delivered by `max τ gst + δ`, and messages from a correct sender are genuine.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {leader : ℕ → P}
variable (R : Run P (Msg P C) (Inp C))

theorem st_zero_eq (p : P) :
    R.st (hotstuff f leader) 0 p = RState.init leader (R.inp p) := rfl

theorem st_LI (τ : ℕ) (p : P) : LI f leader p (R.st (hotstuff f leader) τ p) := by
  induction τ with
  | zero => exact LI.init _
  | succ τ ih => rw [st_succ_eq]; exact ih.stepR _

theorem st_madeOk (τ : ℕ) (p : P) : MadeOk f (R.st (hotstuff f leader) τ p) := by
  induction τ with
  | zero =>
    intro c hc
    change c ∈ (∅ : Set (QCm P C)) at hc
    exact absurd hc (Set.notMem_empty c)
  | succ τ ih => rw [st_succ_eq]; exact madeOk_stepR ih _

theorem st_grow {σ τ : ℕ} (h : σ ≤ τ) (p : P) :
    Grow (R.st (hotstuff f leader) σ p) (R.st (hotstuff f leader) τ p) := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            exact Grow.refl _
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · rw [st_succ_eq] at *; exact (ih (by omega)).trans (grow_stepR _ _)
    · obtain rfl : σ = τ + 1 := by omega
      exact Grow.refl _

theorem sent_out {τ : ℕ} {p q : P} {m : Msg P C}
    (h : (q, m) ∈ (R.st (hotstuff f leader) τ p).sent) :
    ∃ a ≤ τ, m ∈ (R.st (hotstuff f leader) a p).out q := by
  induction τ with
  | zero =>
    simp only [st_zero_eq, RState.init, Set.mem_singleton_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, le_rfl, ?_⟩
    show _ ∈ (RState.init leader (R.inp p)).out _
    simp [RState.init, to1]
  | succ τ ih =>
    rw [st_succ_eq] at h
    rcases sentNew_stepR _ _ _ h with h | h
    · obtain ⟨a, ha, h'⟩ := ih h; exact ⟨a, by omega, h'⟩
    · exact ⟨τ + 1, le_rfl, by rw [st_succ_eq]; exact h⟩

theorem sent_of_out {a τ : ℕ} (h : a ≤ τ) {p q : P} {m : Msg P C}
    (hm : m ∈ (R.st (hotstuff f leader) a p).out q) :
    (q, m) ∈ (R.st (hotstuff f leader) τ p).sent :=
  (st_grow R h p).sent ((st_LI R a p).out_sent q m hm)

variable {R}

/-- Delivery after GST: a message sent by a correct replica at `a` to a correct replica is in the
receiver's buffer by step `max a gst + δ`. -/
theorem deliver {δ : ℕ} (hR : R.Valid f δ) {p q : P} (hp : p ∉ R.faulty) (hq : q ∉ R.faulty)
    {a : ℕ} {m : Msg P C} (hm : m ∈ (R.st (hotstuff f leader) a p).out q) {τ : ℕ}
    (hτ : max a R.gst + δ ≤ τ) :
    (p, m) ∈ (recv (R.st (hotstuff f leader) τ q) (R.inbox (hotstuff f leader) q τ)).buf := by
  rw [← (hstep_at R ∅ ∅ τ q).buf]
  exact hotstuff_logs.mem_log_of_valid R hR hp hq hm (by omega)

theorem buf_recv_sub {τ : ℕ} {q : P} {qm : P × Msg P C}
    (h : qm ∈ (R.st (hotstuff f leader) τ q).buf) :
    qm ∈ (recv (R.st (hotstuff f leader) τ q) (R.inbox (hotstuff f leader) q τ)).buf := by
  simp [recv, h]

theorem buf_succ {τ : ℕ} {q : P} {qm : P × Msg P C}
    (h : qm ∈ (recv (R.st (hotstuff f leader) τ q) (R.inbox (hotstuff f leader) q τ)).buf) :
    qm ∈ (R.st (hotstuff f leader) (τ + 1) q).buf := by
  rw [(hstep_at R ∅ ∅ τ q).buf]; exact h

/-- Messages from a correct sender in a buffer are genuine. -/
theorem genuine {p q : P} (hp : p ∉ R.faulty) {τ : ℕ} {m : Msg P C}
    (h : (p, m) ∈ (recv (R.st (hotstuff f leader) τ q) (R.inbox (hotstuff f leader) q τ)).buf) :
    (q, m) ∈ (R.st (hotstuff f leader) τ p).sent := by
  rw [← (hstep_at R ∅ ∅ τ q).buf] at h
  obtain ⟨σ, hσ, hm⟩ := hotstuff_logs.exists_mem_send_of_mem_log R hp h
  exact sent_of_out R (by omega) hm

theorem genuine' {p q : P} (hp : p ∉ R.faulty) {τ : ℕ} {m : Msg P C}
    (h : (p, m) ∈ (R.st (hotstuff f leader) τ q).buf) :
    (q, m) ∈ (R.st (hotstuff f leader) τ p).sent := genuine hp (buf_recv_sub h)

theorem st_succ_noint {τ : ℕ} {p : P} (h : (R.inp p).1 τ = false) :
    R.st (hotstuff f leader) (τ + 1) p = handlers f leader p
      (recv (R.st (hotstuff f leader) τ p) (R.inbox (hotstuff f leader) p τ)) := by
  rw [st_succ_eq, stepR_eq, st_inp, st_clock, h, if_neg Bool.false_ne_true]

end HotStuff.Basic
