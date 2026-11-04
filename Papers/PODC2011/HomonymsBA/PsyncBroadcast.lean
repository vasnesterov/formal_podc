import Papers.PODC2011.HomonymsBA.PsyncBasic

/-!
# Proposition 5: the authenticated broadcast (Proposition 6)

Proposition 6 of the paper, for the echo broadcast built into the algorithm:

* `unforgeable`: if a process has performed `Accept(m, i)` and no Byzantine process has
  identifier `i`, then some correct process with identifier `i` sent `⟨init m⟩` (performed
  `Broadcast(m)`) in an earlier round;
* `bcast_correct`: a broadcast by a correct process in a round `r ≥ gst` is accepted by every
  correct process two rounds later (i.e. within its superround);
* `relay`: if a correct process has accepted `(m, i)` at round `r ≥ gst`, every correct process
  has accepted it at round `r + 2`.
-/

namespace Podc.HomonymsBA.Psync

open Set

variable {P : Type} [Fintype P] {ℓ t : ℕ} {V : Type} {R : Run P ℓ V (Msg ℓ V)}

/-- What a broadcast `init` can be. -/
lemma init_eq_some {s : St ℓ V} {m : BMsg V} (h : (out t s).init = some m) :
    (s.rnd % 8 = 0 ∧ m = .propose (propSet s) (s.rnd / 8)) ∨
      (s.rnd % 8 = 4 ∧ ∃ v, voteChoice t s = some v ∧ m = .vote v (s.rnd / 8)) := by
  simp only [out] at h
  split_ifs at h with h0 h4
  · exact Or.inl ⟨h0, (Option.some.inj h).symm⟩
  · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Or.inr ⟨h4, v, hv, rfl⟩

lemma bcast_propose {r : ℕ} {q : P} {W : Set V} {ph : ℕ}
    (h : (out t (σ R t r q)).init = some (.propose W ph)) :
    r = 8 * ph ∧ W = propSet (σ R t (8 * ph) q) := by
  rcases init_eq_some h with ⟨h0, e⟩ | ⟨-, v, -, e⟩
  · simp only [rnd_σ, BMsg.propose.injEq] at h0 e
    have : r = 8 * ph := by omega
    subst this
    exact ⟨rfl, e.1⟩
  · cases e

lemma bcast_vote {r : ℕ} {q : P} {v : V} {ph : ℕ}
    (h : (out t (σ R t r q)).init = some (.vote v ph)) :
    r = 8 * ph + 4 ∧ voteChoice t (σ R t (8 * ph + 4) q) = some v := by
  rcases init_eq_some h with ⟨-, e⟩ | ⟨h4, w, hw, e⟩
  · cases e
  · simp only [rnd_σ, BMsg.vote.injEq] at h4 e
    obtain ⟨rfl, rfl⟩ := e
    have : r = 8 * (r / 8) + 4 := by omega
    refine ⟨this, ?_⟩
    rw [← this]
    exact hw

/-- Echoes received from an identifier without Byzantine process were echoed by a correct
process with that identifier in an earlier round. -/
lemma echoRcv_src (hR : R.Valid t) : ∀ (r : ℕ) (p : P) (j : Fin ℓ) (e : BMsg V × Fin ℓ),
    (j, e) ∈ (σ R t r p).echoRcv → BF R j →
      ∃ q, q ∉ R.byz ∧ R.id q = j ∧ ∃ r' < r, e ∈ (σ R t r' q).echoing := by
  intro r
  induction r with
  | zero => intro p j e h; simp [alg, initSt] at h
  | succ r ih =>
    intro p j e h hj
    rw [σ_succ] at h
    simp only [step, newEchoRcv, Set.mem_union, Set.mem_ofPred_eq] at h
    rcases h with h | ⟨m, hm, he⟩
    · obtain ⟨q, hq, hqj, r', hr', h'⟩ := ih p j e h hj
      exact ⟨q, hq, hqj, r', by omega, h'⟩
    · obtain ⟨q, hq, hqj, rfl⟩ := rcv_src hR hm hj
      exact ⟨q, hq, hqj, r, by omega, he⟩

/-- Echoes `(m, i)` of correct processes, for `i` without Byzantine process, come from a
broadcast of `m` by a correct process with identifier `i`. -/
lemma echoing_src (hR : R.Valid t) (h3 : 3 * t < ℓ) : ∀ (r : ℕ) (p : P) (e : BMsg V × Fin ℓ),
    e ∈ (σ R t r p).echoing → BF R e.2 →
      ∃ q, q ∉ R.byz ∧ R.id q = e.2 ∧ ∃ r' < r, (out t (σ R t r' q)).init = some e.1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro p e h he
  cases r with
  | zero => simp [alg, initSt] at h
  | succ r =>
    rw [σ_succ] at h
    simp only [step, Set.mem_union, Set.mem_ofPred_eq] at h
    rcases h with h | ⟨-, m, hm, hinit⟩ | h
    · obtain ⟨q, hq, hqj, r', hr', h'⟩ := ih r (by omega) p e h he
      exact ⟨q, hq, hqj, r', by omega, h'⟩
    · obtain ⟨q, hq, hqj, rfl⟩ := rcv_src hR hm he
      exact ⟨q, hq, hqj, r, by omega, hinit⟩
    · obtain ⟨j, hj, hbf⟩ := exists_BF hR (Q := fun j => (j, e) ∈ newEchoRcv (σ R t r p)
        (rcv R t r p)) (by omega)
      have hj' : (j, e) ∈ (σ R t (r + 1) p).echoRcv := by rw [σ_succ]; exact hj
      obtain ⟨q', -, -, r'', hr'', h''⟩ := echoRcv_src hR (r + 1) p j e hj' hbf
      obtain ⟨q, hq, hqj, r', hr', h'⟩ := ih r'' hr'' q' e h'' he
      exact ⟨q, hq, hqj, r', by omega, h'⟩

/-- **Unforgeability** (Proposition 6). -/
theorem unforgeable (hR : R.Valid t) (h3 : 3 * t < ℓ) {r : ℕ} {p : P} {m : BMsg V} {i : Fin ℓ}
    (hA : Acc t (σ R t r p).echoRcv m i) (hi : BF R i) :
    ∃ q, q ∉ R.byz ∧ R.id q = i ∧ ∃ r' < r, (out t (σ R t r' q)).init = some m := by
  obtain ⟨j, hj, hbf⟩ := exists_BF hR (Q := fun j => (j, (m, i)) ∈ (σ R t r p).echoRcv)
    (by unfold Acc at hA; omega)
  obtain ⟨q', -, -, r'', hr'', h''⟩ := echoRcv_src hR r p j (m, i) hj hbf
  obtain ⟨q, hq, hqj, r', hr', h'⟩ := echoing_src hR h3 r'' q' (m, i) h'' hi
  exact ⟨q, hq, hqj, r', by omega, h'⟩

/-- If all correct processes echo `(m, i)` in round `r ≥ gst`, all correct processes have
accepted `(m, i)` at the end of the round. -/
lemma acc_of_all_echo (hR : R.Valid t) {r : ℕ} {m : BMsg V} {i : Fin ℓ} (hr : R.gst ≤ r)
    (h : ∀ q, q ∉ R.byz → (m, i) ∈ (σ R t r q).echoing) :
    ∀ p, p ∉ R.byz → Acc t (σ R t (r + 1) p).echoRcv m i := by
  intro p hp
  refine (ncard_BF hR).trans (ncard_mono fun j hj => ?_)
  obtain ⟨q, hq, rfl⟩ := BF_correct hR hj
  rw [σ_succ]
  exact Or.inr ⟨_, rcv_of_gst hR hr hq hp, h q hq⟩

/-- **Correctness** (Proposition 6): a broadcast by a correct process in the first round `r` of a
superround with `r ≥ gst` is accepted by all correct processes at the end of the superround. -/
theorem bcast_correct (hR : R.Valid t) {r : ℕ} {q : P} {m : BMsg V} (hr : R.gst ≤ r)
    (he : r % 2 = 0) (hq : q ∉ R.byz) (hm : (out t (σ R t r q)).init = some m) :
    ∀ p, p ∉ R.byz → Acc t (σ R t (r + 2) p).echoRcv m (R.id q) := by
  refine acc_of_all_echo hR (by omega) fun p hp => ?_
  rw [σ_succ]
  simp only [step, Set.mem_union, Set.mem_ofPred_eq, rnd_σ]
  exact Or.inr (Or.inl ⟨he, _, rcv_of_gst hR hr hq hp, hm⟩)

/-- **Relay** (Proposition 6): what a correct process has accepted at round `r ≥ gst` is accepted
by all correct processes at round `r + 2`. -/
theorem relay (hR : R.Valid t) {r : ℕ} {p : P} {m : BMsg V} {i : Fin ℓ} (hr : R.gst ≤ r)
    (hA : Acc t (σ R t r p).echoRcv m i) :
    ∀ p', p' ∉ R.byz → Acc t (σ R t (r + 2) p').echoRcv m i := by
  refine acc_of_all_echo hR (by omega) fun p' hp' => ?_
  rw [σ_succ]
  simp only [step, Set.mem_union, Set.mem_ofPred_eq]
  refine Or.inr (Or.inr ((ncard_BF_and hR hA).trans (ncard_mono fun j ⟨hj, hbf⟩ => ?_)))
  obtain ⟨q, hq, rfl, r', hr', h'⟩ := echoRcv_src hR r p j (m, i) hj hbf
  exact Or.inr ⟨_, rcv_of_gst hR hr hq hp', echoing_mono hr'.le q h'⟩

end Podc.HomonymsBA.Psync
