import Papers.PODC2011.HomonymsBA.PsyncBroadcast

/-!
# Proposition 5: safety (agreement and validity)

* `vote_quorum` (Lemma 8): two quorums of accepted votes of the same phase have the same value;
* `lemma10` (Lemma 10): processes that acked `v` in phase `ph`, when `ℓ - t` identifiers sent an
  ack for `v`, keep a lock on `v` forever;
* `line22_agree` (Lemma 9 and the agreement part of the proof of Proposition 5): all decisions
  taken on line 22 are equal; `dec_inv`: every decision is a line-22 decision value;
* `agreement`, `validity`.
-/

namespace Podc.HomonymsBA.Psync

open Set

variable {P : Type} [Fintype P] {ℓ t : ℕ} {V : Type} {R : Run P ℓ V (Msg ℓ V)}

/-! ### Transitions of single fields -/

lemma locks_succ (r : ℕ) (p : P) :
    (σ R t (r + 1) p).locks = newLocks t (σ R t r p) (σ R t (r + 1) p).echoRcv := rfl

lemma ackVal_succ (r : ℕ) (p : P) : (σ R t (r + 1) p).ackVal =
    if r % 8 = 5 then ackChoice t (σ R t (r + 1) p).echoRcv (r / 8) else (σ R t r p).ackVal := by
  rw [σ_succ]; simp [step]

lemma lockReq_succ (r : ℕ) (p : P) : (σ R t (r + 1) p).lockReq =
    if r % 8 = 2 then lockSend t (σ R t r p) else (σ R t r p).lockReq := by
  rw [σ_succ]; simp [step]

lemma lockRcv_succ (r : ℕ) (p : P) : (σ R t (r + 1) p).lockRcv =
    if r % 8 = 2 then {v | ∃ j m, IsLeader j (r / 8) ∧ (j, m) ∈ rcv R t r p ∧ m.lock = some v}
    else (σ R t r p).lockRcv := by
  rw [σ_succ]; simp [step]

lemma dec_succ (r : ℕ) (p : P) :
    (σ R t (r + 1) p).dec = (σ R t r p).dec.or (decNew t (σ R t r p) (rcv R t r p)) := by
  rw [σ_succ]; rfl

lemma proper_succ (r : ℕ) (p : P) :
    (σ R t (r + 1) p).proper = (σ R t r p).proper ∪ {v | Rule1 t (rcv R t r p) v ∨
      Rule2 t (rcv R t r p)} := by
  rw [σ_succ]; rfl

lemma ackVal_spec (ph : ℕ) (p : P) :
    (σ R t (8 * ph + 6) p).ackVal = ackChoice t (σ R t (8 * ph + 6) p).echoRcv ph := by
  rw [show 8 * ph + 6 = (8 * ph + 5) + 1 from rfl, ackVal_succ, ite_eq_left (by omega)]
  congr 1
  omega

lemma lockReq_spec (ph : ℕ) (p : P) :
    (σ R t (8 * ph + 6) p).lockReq = lockSend t (σ R t (8 * ph + 2) p) := by
  have h : ∀ k ≤ 3, (σ R t (8 * ph + 3 + k) p).lockReq = lockSend t (σ R t (8 * ph + 2) p) := by
    intro k hk
    induction k with
    | zero =>
      rw [show 8 * ph + 3 + 0 = (8 * ph + 2) + 1 from rfl, lockReq_succ, ite_eq_left (by omega)]
    | succ k ih =>
      rw [show 8 * ph + 3 + (k + 1) = (8 * ph + 3 + k) + 1 by omega, lockReq_succ,
        ite_eq_right (by omega), ih (by omega)]
  exact h 3 le_rfl

lemma ackChoice_spec {E : Set (Fin ℓ × (BMsg V × Fin ℓ))} {ph : ℕ} {v : V}
    (h : ackChoice t E ph = some v) : AccVote t E v ph := by
  unfold ackChoice at h
  split_ifs at h with h'
  cases h
  exact h'.choose_spec

lemma lockSend_spec {s : St ℓ V} {v : V} (h : lockSend t s = some v) :
    IsLeader s.me (s.rnd / 8) ∧ AccProp t s.echoRcv (s.rnd / 8) v := by
  unfold lockSend at h
  split_ifs at h with h'
  cases h
  exact ⟨h'.1, h'.2.choose_spec⟩

lemma voteChoice_spec {s : St ℓ V} {v : V} (h : voteChoice t s = some v) :
    v ∈ s.lockRcv ∧ AccProp t s.echoRcv (s.rnd / 8) v := by
  unfold voteChoice at h
  split_ifs at h with h'
  cases h
  exact h'.choose_spec

lemma ack_sent {r : ℕ} {q : P} {v : V} (h : (out t (σ R t r q)).ack = some v) :
    r = 8 * (r / 8) + 6 ∧ AccVote t (σ R t r q).echoRcv v (r / 8) := by
  simp only [out, rnd_σ] at h
  split_ifs at h with h6
  have e : r = 8 * (r / 8) + 6 := by omega
  refine ⟨e, ?_⟩
  rw [e, ackVal_spec] at h
  rw [e]
  have := ackChoice_spec h
  simpa [show (8 * (r / 8) + 6) / 8 = r / 8 by omega] using this

/-- Locks of a process record a vote quorum it accepted when it locked. -/
lemma lock_inv : ∀ (r : ℕ) (p : P) (w : V) (x : ℕ), (w, x) ∈ (σ R t r p).locks →
    8 * x + 6 ≤ r ∧ ackChoice t (σ R t (8 * x + 6) p).echoRcv x = some w := by
  intro r
  induction r with
  | zero => intro p w x h; simp [alg, initSt] at h
  | succ r ih =>
    intro p w x h
    rw [locks_succ] at h
    simp only [newLocks, rnd_σ] at h
    split_ifs at h with h5 h7
    · split at h
      · next v hv =>
        rcases h with h | ⟨h, -⟩
        · simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have e : 8 * (r / 8) + 6 = r + 1 := by omega
          rw [e]
          exact ⟨le_rfl, hv⟩
        · have := ih p w x h
          exact ⟨by omega, this.2⟩
      · have := ih p w x h
        exact ⟨by omega, this.2⟩
    · have := ih p w x h.1
      exact ⟨by omega, this.2⟩
    · have := ih p w x h
      exact ⟨by omega, this.2⟩

lemma lock_accVote {r : ℕ} {p : P} {w : V} {x : ℕ} (h : (w, x) ∈ (σ R t r p).locks) :
    8 * x + 6 ≤ r ∧ AccVote t (σ R t (8 * x + 6) p).echoRcv w x :=
  ⟨(lock_inv r p w x h).1, ackChoice_spec (lock_inv r p w x h).2⟩

/-! ### Quorums -/

variable (hR : R.Valid t) (hℓ : Fintype.card P + 3 * t < 2 * ℓ)
include hR hℓ

/-- A process with a unique identifier that broadcast a vote for `v` in phase `ph`. -/
lemma vote_src_UCp {r : ℕ} {p s : P} {v : V} {ph : ℕ} (hs : UCp R s)
    (h : Acc t (σ R t r p).echoRcv (.vote v ph) (R.id s)) :
    voteChoice t (σ R t (8 * ph + 4) s) = some v := by
  obtain ⟨q, -, e, r', -, h'⟩ := unforgeable hR (three_t_lt hR hℓ) h hs.bf
  rw [hs.2 q e] at h'
  exact (bcast_vote h').2

/-- **Lemma 8** (in the form used): two quorums of accepted votes of the same phase (of any two
processes, at any times) carry the same value. -/
theorem vote_quorum {r r' : ℕ} {p p' : P} {v v' : V} {ph : ℕ}
    (h : AccVote t (σ R t r p).echoRcv v ph) (h' : AccVote t (σ R t r' p').echoRcv v' ph) :
    v = v' := by
  obtain ⟨s, hs, h1, h2⟩ := lemma7 hR hℓ h h'
  have e1 := vote_src_UCp hR hℓ hs h1
  have e2 := vote_src_UCp hR hℓ hs h2
  rw [e1] at e2
  exact Option.some.inj e2

/-- A process with a unique identifier that broadcast a proposal in phase `ph`. -/
lemma propose_src_UCp {r : ℕ} {p s : P} {W : Set V} {ph : ℕ} (hs : UCp R s)
    (h : Acc t (σ R t r p).echoRcv (.propose W ph) (R.id s)) :
    W = propSet (σ R t (8 * ph) s) := by
  obtain ⟨q, -, e, r', -, h'⟩ := unforgeable hR (three_t_lt hR hℓ) h hs.bf
  rw [hs.2 q e] at h'
  exact (bcast_propose h').2

/-- A vote accepted from `ℓ - t` identifiers was broadcast by a correct process in round
`8ph + 4`, which had accepted a proposal quorum for it. -/
lemma accVote_src {r : ℕ} {p : P} {w : V} {y : ℕ} (h : AccVote t (σ R t r p).echoRcv w y) :
    ∃ q, q ∉ R.byz ∧ 8 * y + 4 < r ∧ AccProp t (σ R t (8 * y + 4) q).echoRcv y w := by
  have h3 := three_t_lt hR hℓ
  obtain ⟨j, hj, hbf⟩ := exists_BF hR (Q := fun j => Acc t (σ R t r p).echoRcv (.vote w y) j)
    (by unfold AccVote at h; omega)
  obtain ⟨q, hq, -, r', hr', h'⟩ := unforgeable hR h3 hj hbf
  obtain ⟨e, hv⟩ := bcast_vote h'
  have := (voteChoice_spec hv).2
  simp only [rnd_σ, show (8 * y + 4) / 8 = y by omega] at this
  exact ⟨q, hq, by omega, this⟩

/-- **Lemma 10.** -/
theorem lemma10 {ph : ℕ} {v : V} {A : Fin ℓ → Prop} (hA : ℓ - t ≤ {j | A j}.ncard)
    (hAs : ∀ s, UCp R s → A (R.id s) → (σ R t (8 * ph + 6) s).ackVal = some v) :
    ∀ r, 8 * ph + 6 ≤ r → ∀ q, q ∉ R.byz → (σ R t (8 * ph + 6) q).ackVal = some v →
      ∃ x, ph ≤ x ∧ (v, x) ∈ (σ R t r q).locks := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro hr q hq hack
  rcases Nat.eq_or_lt_of_le hr with e | hlt
  · subst e
    refine ⟨ph, le_rfl, ?_⟩
    rw [ackVal_spec] at hack
    rw [show 8 * ph + 6 = (8 * ph + 5) + 1 from rfl, locks_succ]
    simp only [newLocks, rnd_σ, show (8 * ph + 5) % 8 = 5 by omega, ite_true,
      show (8 * ph + 5) / 8 = ph by omega]
    rw [show 8 * ph + 5 + 1 = 8 * ph + 6 from rfl, hack]
    exact Or.inl rfl
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨x, hx, hmem⟩ := ih r (by omega) (by omega) q hq hack
  rw [locks_succ]
  simp only [newLocks, rnd_σ]
  split_ifs with h5 h7
  · split
    · next w hw =>
      by_cases hwv : w = v
      · subst hwv
        exact ⟨r / 8, by omega, Or.inl rfl⟩
      · exact ⟨x, hx, Or.inr ⟨hmem, Ne.symm hwv⟩⟩
    · exact ⟨x, hx, hmem⟩
  · refine ⟨x, hx, hmem, ?_⟩
    rintro ⟨w, y, hwv, hxy, hvote⟩
    obtain ⟨q0, -, hy, hprop⟩ := accVote_src hR hℓ hvote
    obtain ⟨s, hs, hsA, W, hwW, hsW⟩ := lemma7 hR hℓ hA hprop
    rw [propose_src_UCp hR hℓ hs hsW] at hwW
    obtain ⟨x', -, hx'⟩ := ih (8 * y) (by omega) (by omega) s hs.1 (hAs s hs hsA)
    exact hwv (hwW.2 v x' hx').symm
  · exact ⟨x, hx, hmem⟩

/-! ### Decisions -/

omit hℓ in
/-- `p` decides `v` on line 22 in phase `ph`. -/
def Line22 (R : Run P ℓ V (Msg ℓ V)) (t : ℕ) (p : P) (ph : ℕ) (v : V) : Prop :=
  p ∉ R.byz ∧ (σ R t (8 * ph + 6) p).lockReq = some v ∧
    ℓ - t ≤ {j | ∃ m, (j, m) ∈ rcv R t (8 * ph + 6) p ∧ m.ack = some v}.ncard

/-- Every decision of a correct process is a value decided on line 22 by a correct process. -/
lemma dec_inv : ∀ (r : ℕ) (p : P) (v : V), p ∉ R.byz → (σ R t r p).dec = some v →
    ∃ p' ph, Line22 R t p' ph v := by
  have h3 := three_t_lt hR hℓ
  intro r
  induction r with
  | zero => intro p v _ h; simp [alg, initSt] at h
  | succ r ih =>
    intro p v hp h
    rw [dec_succ] at h
    cases hd : (σ R t r p).dec with
    | some w =>
      rw [hd, Option.some_or] at h
      obtain rfl := Option.some.inj h
      exact ih p w hp hd
    | none =>
      rw [hd, Option.none_or] at h
      unfold decNew at h
      split_ifs at h with h6 h7
      · cases h
        obtain ⟨hlr, hcnt⟩ := h6.2.2.choose_spec
        have e6 : r % 8 = 6 := by simpa using h6.1
        refine ⟨p, r / 8, hp, ?_, ?_⟩
        · rw [show 8 * (r / 8) + 6 = r by omega]; exact hlr
        · rw [show 8 * (r / 8) + 6 = r by omega]; exact hcnt
      · cases h
        have e7 : r % 8 = 7 := by simpa using h7.1
        obtain ⟨j, ⟨m, hm, hmd⟩, hbf⟩ := exists_BF hR
          (Q := fun j => ∃ m, (j, m) ∈ rcv R t r p ∧ m.dec = some h7.2.choose)
          (by have := h7.2.choose_spec; omega)
        obtain ⟨q, hq, -, rfl⟩ := rcv_src hR hm hbf
        simp only [out, rnd_σ, e7] at hmd
        exact ih q _ hq hmd

/-- A line-22 decision is backed by a vote quorum accepted by a correct process (which acked). -/
lemma line22_vote {p : P} {ph : ℕ} {v : V} (h : Line22 R t p ph v) :
    ∃ q, q ∉ R.byz ∧ AccVote t (σ R t (8 * ph + 6) q).echoRcv v ph := by
  have h3 := three_t_lt hR hℓ
  obtain ⟨j, ⟨m, hm, hma⟩, hbf⟩ := exists_BF hR
    (Q := fun j => ∃ m, (j, m) ∈ rcv R t (8 * ph + 6) p ∧ m.ack = some v)
    (by have := h.2.2; omega)
  obtain ⟨q, hq, -, rfl⟩ := rcv_src hR hm hbf
  obtain ⟨-, hacc⟩ := ack_sent hma
  rw [show (8 * ph + 6) / 8 = ph by omega] at hacc
  exact ⟨q, hq, hacc⟩

omit hR hℓ in
/-- The value decided on line 22 had been requested to be locked by the leader (line 10). -/
lemma line22_prop {p : P} {ph : ℕ} {v : V} (h : Line22 R t p ph v) :
    AccProp t (σ R t (8 * ph + 2) p).echoRcv ph v := by
  have := (lockSend_spec ((lockReq_spec ph p).symm.trans h.2.1)).2
  simpa [show (8 * ph + 2) / 8 = ph by omega] using this

/-- Agreement between line-22 decisions of different phases (proof of Proposition 5). -/
lemma line22_agree_lt {p₁ p : P} {ph₁ ph : ℕ} {v₁ v : V} (h₁ : Line22 R t p₁ ph₁ v₁)
    (h : Line22 R t p ph v) (hlt : ph₁ < ph) : v₁ = v := by
  have hAs : ∀ s, UCp R s →
      (fun j => ∃ m, (j, m) ∈ rcv R t (8 * ph₁ + 6) p₁ ∧ m.ack = some v₁) (R.id s) →
      (σ R t (8 * ph₁ + 6) s).ackVal = some v₁ := by
    rintro s hs ⟨m, hm, hma⟩
    rw [rcv_src_UCp hR hm hs] at hma
    simpa [out, show (8 * ph₁ + 6) % 8 = 6 by omega] using hma
  obtain ⟨s, hs, hsA, W, hvW, hsW⟩ := lemma7 hR hℓ h₁.2.2 (line22_prop h)
  obtain ⟨x, -, hx⟩ := lemma10 hR hℓ h₁.2.2 hAs (8 * ph) (by omega) s hs.1 (hAs s hs hsA)
  rw [propose_src_UCp hR hℓ hs hsW] at hvW
  exact hvW.2 v₁ x hx

/-- **Lemma 9** and agreement of all line-22 decisions. -/
theorem line22_agree {p₁ p₂ : P} {ph₁ ph₂ : ℕ} {v₁ v₂ : V} (h₁ : Line22 R t p₁ ph₁ v₁)
    (h₂ : Line22 R t p₂ ph₂ v₂) : v₁ = v₂ := by
  rcases lt_trichotomy ph₁ ph₂ with hlt | rfl | hlt
  · exact line22_agree_lt hR hℓ h₁ h₂ hlt
  · obtain ⟨q₁, -, a₁⟩ := line22_vote hR hℓ h₁
    obtain ⟨q₂, -, a₂⟩ := line22_vote hR hℓ h₂
    exact vote_quorum hR hℓ a₁ a₂
  · exact (line22_agree_lt hR hℓ h₂ h₁ hlt).symm

/-- **Agreement.** -/
theorem agreement {p q : P} {r r' : ℕ} {v w : V} (hp : p ∉ R.byz) (hq : q ∉ R.byz)
    (h₁ : (σ R t r p).dec = some v) (h₂ : (σ R t r' q).dec = some w) : v = w := by
  obtain ⟨p₁, ph₁, l₁⟩ := dec_inv hR hℓ r p v hp h₁
  obtain ⟨p₂, ph₂, l₂⟩ := dec_inv hR hℓ r' q w hq h₂
  exact line22_agree hR hℓ l₁ l₂

omit hℓ in
/-- If all correct processes have input `v₀`, their proper sets stay `{v₀}`. -/
lemma proper_valid {v₀ : V} (hv : ∀ p, p ∉ R.byz → R.inp p = v₀) :
    ∀ r, ∀ p, p ∉ R.byz → (σ R t r p).proper = {v₀} := by
  intro r
  induction r with
  | zero => intro p hp; simp [alg, initSt, hv p hp]
  | succ r ih =>
    intro p hp
    rw [proper_succ, ih p hp, Set.union_eq_left]
    rintro v (h1 | ⟨J, f, hJ, hf, hcnt⟩)
    · obtain ⟨j, ⟨m, hm, hvm⟩, hbf⟩ := exists_BF hR
        (Q := fun j => ∃ m, (j, m) ∈ rcv R t r p ∧ v ∈ m.proper) (by unfold Rule1 at h1; omega)
      obtain ⟨q, hq, -, rfl⟩ := rcv_src hR hm hbf
      simpa [out, ih q hq] using hvm
    · exfalso
      have h1 := ncard_le_BF hR (· ∈ J)
      have h2 : {j | j ∈ J ∧ BF R j}.ncard ≤ {j | j ∈ J ∧ v₀ ∈ f j}.ncard := by
        refine ncard_mono fun j ⟨hj, hbf⟩ => ⟨hj, ?_⟩
        obtain ⟨m, hm, hmf⟩ := hf j hj
        obtain ⟨q, hq, -, rfl⟩ := rcv_src hR hm hbf
        rw [← hmf]
        simp [out, ih q hq]
      have h3 := hcnt v₀
      simp only [Set.ofPred_mem_eq] at h1
      omega

/-- A line-22 decision is the common input, if there is one. -/
lemma line22_valid {v₀ : V} (hv : ∀ p, p ∉ R.byz → R.inp p = v₀) {p : P} {ph : ℕ} {v : V}
    (h : Line22 R t p ph v) : v = v₀ := by
  have h3 := three_t_lt hR hℓ
  have hp := line22_prop h
  obtain ⟨k, ⟨W, hvW, hacc⟩, hbf⟩ := exists_BF hR
    (Q := fun k => ∃ W, v ∈ W ∧ Acc t (σ R t (8 * ph + 2) p).echoRcv (.propose W ph) k)
    (by unfold AccProp at hp; omega)
  obtain ⟨q, hq, -, r', -, h'⟩ := unforgeable hR h3 hacc hbf
  rw [(bcast_propose h').2] at hvW
  have := hvW.1
  rwa [proper_valid hR hv _ q hq, Set.mem_singleton_iff] at this

/-- **Validity.** -/
theorem validity {v₀ : V} (hv : ∀ p, p ∉ R.byz → R.inp p = v₀) {p : P} {r : ℕ} {w : V}
    (hp : p ∉ R.byz) (h : (σ R t r p).dec = some w) : w = v₀ := by
  obtain ⟨p', ph, l⟩ := dec_inv hR hℓ r p w hp h
  exact line22_valid hR hℓ hv l

end Podc.HomonymsBA.Psync
