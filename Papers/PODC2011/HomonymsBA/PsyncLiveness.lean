import Papers.PODC2011.HomonymsBA.PsyncSafety

/-!
# Proposition 5: termination, and the theorem

* `lemma11` (Lemma 11): after `gst`, at the end of a phase all locks of correct processes carry
  the same value;
* `common_value` (Lemma 12, core): after `gst`, at the beginning of a phase some value belongs to
  the proposal set of every correct process;
* `leader_decides`: a correct leader that does not share its identifier decides in its phase
  (Lemma 12 and the termination part of the proof of Proposition 5);
* `termination`, `ba`, and **`prop5`**.
-/

namespace Podc.HomonymsBA.Psync

open Set

variable {P : Type} [Fintype P] {ℓ t : ℕ} {V : Type} {R : Run P ℓ V (Msg ℓ V)}

section

variable (hR : R.Valid t) (hℓ : Fintype.card P + 3 * t < 2 * ℓ)
include hR

/-- Relay of an accepted message to a later round. -/
lemma Acc_relay {r r' : ℕ} {p p' : P} {m : BMsg V} {i : Fin ℓ}
    (h : Acc t (σ R t r p).echoRcv m i) (hr : r ≤ r') (hg : R.gst ≤ r') (hp' : p' ∉ R.byz) :
    Acc t (σ R t (r' + 2) p').echoRcv m i :=
  relay hR hg (Acc_σ_mono hr h) p' hp'

lemma AccVote_relay {r r' : ℕ} {p p' : P} {w : V} {y : ℕ}
    (h : AccVote t (σ R t r p).echoRcv w y) (hr : r ≤ r') (hg : R.gst ≤ r') (hp' : p' ∉ R.byz) :
    AccVote t (σ R t (r' + 2) p').echoRcv w y :=
  h.trans (ncard_mono fun _ hj => Acc_relay hR hj hr hg hp')

lemma AccProp_relay {r r' : ℕ} {p p' : P} {v : V} {ph : ℕ}
    (h : AccProp t (σ R t r p).echoRcv ph v) (hr : r ≤ r') (hg : R.gst ≤ r') (hp' : p' ∉ R.byz) :
    AccProp t (σ R t (r' + 2) p').echoRcv ph v :=
  h.trans (ncard_mono fun _ ⟨W, hvW, hj⟩ => ⟨W, hvW, Acc_relay hR hj hr hg hp'⟩)

omit hR in
/-- Lines 27–30 at the end of phase `ph`. -/
lemma lock_kept {ph : ℕ} {p : P} {v w : V} {x y : ℕ}
    (h : (v, x) ∈ (σ R t (8 * ph + 8) p).locks) (hxy : x < y)
    (hw : AccVote t (σ R t (8 * ph + 8) p).echoRcv w y) : w = v := by
  rw [show 8 * ph + 8 = (8 * ph + 7) + 1 from rfl, locks_succ] at h
  simp only [newLocks, rnd_σ, show (8 * ph + 7) % 8 = 7 by omega] at h
  have h' := h.2
  by_contra hne
  exact h' ⟨w, y, hne, hxy, hw⟩

include hℓ

/-- **Lemma 11.** -/
theorem lemma11 {ph : ℕ} (hg : R.gst ≤ 8 * ph + 6) {p₁ p₂ : P} {v₁ v₂ : V} {x₁ x₂ : ℕ}
    (hp₁ : p₁ ∉ R.byz) (hp₂ : p₂ ∉ R.byz)
    (h₁ : (v₁, x₁) ∈ (σ R t (8 * ph + 8) p₁).locks)
    (h₂ : (v₂, x₂) ∈ (σ R t (8 * ph + 8) p₂).locks) : v₁ = v₂ := by
  obtain ⟨b₁, a₁⟩ := lock_accVote h₁
  obtain ⟨b₂, a₂⟩ := lock_accVote h₂
  rcases lt_trichotomy x₁ x₂ with hlt | rfl | hlt
  · exact (lock_kept h₁ hlt (AccVote_relay hR a₂ (by omega) hg hp₁)).symm
  · exact vote_quorum hR hℓ a₁ a₂
  · exact lock_kept h₂ hlt (AccVote_relay hR a₁ (by omega) hg hp₂)

omit hℓ in
/-- Proper sets after `gst`, first rule. -/
lemma proper_rule1 {r : ℕ} {v : V} (hg : R.gst ≤ r)
    (h : t + 1 ≤ {j | ∃ q, q ∉ R.byz ∧ R.id q = j ∧ v ∈ (σ R t r q).proper}.ncard) :
    ∀ p, p ∉ R.byz → v ∈ (σ R t (r + 1) p).proper := by
  intro p hp
  rw [proper_succ]
  refine Or.inr (Or.inl (h.trans (ncard_mono fun j ⟨q, hq, hqj, hv⟩ => ?_)))
  subst hqj
  exact ⟨_, rcv_of_gst hR hg hq hp, hv⟩

/-- Proper sets after `gst`, second rule. -/
lemma proper_rule2 {r : ℕ} (hg : R.gst ≤ r)
    (h : ∀ v, {j | ∃ q, q ∉ R.byz ∧ R.id q = j ∧ v ∈ (σ R t r q).proper}.ncard ≤ t) :
    ∀ p, p ∉ R.byz → ∀ v, v ∈ (σ R t (r + 1) p).proper := by
  classical
  intro p hp v
  rw [proper_succ]
  have h3 := three_t_lt hR hℓ
  let f : Fin ℓ → Set V := fun j =>
    if hj : ∃ q, q ∉ R.byz ∧ R.id q = j then (σ R t r hj.choose).proper else ∅
  refine Or.inr (Or.inr ⟨{j | BF R j}, f, by have := ncard_BF hR; omega, ?_, ?_⟩)
  · intro j hj
    have hc := BF_correct hR hj
    have hm := rcv_of_gst hR hg hc.choose_spec.1 hp
    rw [hc.choose_spec.2] at hm
    refine ⟨_, hm, ?_⟩
    simp only [f, dite_eq_left hc, out]
  · intro w
    refine le_trans (ncard_mono fun j ⟨hj, hw⟩ => ?_) (h w)
    have hc := BF_correct hR hj
    simp only [f, dite_eq_left hc] at hw
    exact ⟨_, hc.choose_spec.1, hc.choose_spec.2, hw⟩

/-- **Lemma 12** (core): after `gst`, at the beginning of a phase some value is in the proposal
set of every correct process. -/
theorem common_value {Q : ℕ} (hg : R.gst + 8 ≤ 8 * Q) :
    ∃ c, ∀ q, q ∉ R.byz → c ∈ propSet (σ R t (8 * Q) q) := by
  obtain ⟨ph, rfl⟩ : ∃ ph, Q = ph + 1 := ⟨Q - 1, by omega⟩
  have h3 := three_t_lt hR hℓ
  rw [show 8 * (ph + 1) = 8 * ph + 8 by ring]
  by_cases hA : ∃ q₀, q₀ ∉ R.byz ∧ ∃ w x, (w, x) ∈ (σ R t (8 * ph + 8) q₀).locks
  · -- Case 1 of Lemma 12: some correct process holds a lock
    obtain ⟨q₀, hq₀, w, x, hwx⟩ := hA
    refine ⟨w, fun q hq => ⟨?_, fun w' x' h' => lemma11 hR hℓ (by omega) hq hq₀ h' hwx⟩⟩
    obtain ⟨hx, hvote⟩ := lock_accVote hwx
    obtain ⟨q₁, -, -, hprop⟩ := accVote_src hR hℓ hvote
    have hcnt := ncard_BF_and hR hprop
    have key : t + 1 ≤ {j | ∃ q, q ∉ R.byz ∧ R.id q = j ∧
        w ∈ (σ R t (max (8 * x) R.gst) q).proper}.ncard := by
      refine le_trans (by omega) (hcnt.trans (ncard_mono fun k ⟨⟨W, hwW, hacc⟩, hbf⟩ => ?_))
      obtain ⟨q', hq', hq'k, r', -, h'⟩ := unforgeable hR h3 hacc hbf
      rw [(bcast_propose h').2] at hwW
      exact ⟨q', hq', hq'k, proper_mono (le_max_left _ _) q' hwW.1⟩
    exact proper_mono (by omega) q (proper_rule1 hR (le_max_right _ _) key q hq)
  · -- Case 2 of Lemma 12: no correct process holds a lock
    push Not at hA
    have hprop : ∀ q, q ∉ R.byz → ∀ c, c ∈ (σ R t (8 * ph + 8) q).proper →
        c ∈ propSet (σ R t (8 * ph + 8) q) :=
      fun q hq c hc => ⟨hc, fun w x h => absurd h (hA q hq w x)⟩
    by_cases hc : ∃ v, t + 1 ≤ {j | ∃ q, q ∉ R.byz ∧ R.id q = j ∧
        v ∈ (σ R t (8 * ph + 7) q).proper}.ncard
    · obtain ⟨v, hv⟩ := hc
      exact ⟨v, fun q hq => hprop q hq v (proper_rule1 hR (by omega) hv q hq)⟩
    · push Not at hc
      obtain ⟨p₀, -⟩ := hR.surj ⟨0, by omega⟩
      exact ⟨R.inp p₀, fun q hq => hprop q hq _
        (proper_rule2 hR hℓ (by omega) (fun v => Nat.le_of_lt_succ (hc v)) q hq _)⟩

/-- A correct leader that does not share its identifier decides in its phase, once phase
`Q - 1` is after `gst` (Lemma 12 and the termination proof of Proposition 5). -/
theorem leader_decides {Q : ℕ} (hg : R.gst + 8 ≤ 8 * Q) {s : P} (hs : UCp R s)
    (hl : IsLeader (R.id s) Q) : (σ R t (8 * Q + 7) s).dec ≠ none := by
  have h3 := three_t_lt hR hℓ
  obtain ⟨c, hc⟩ := common_value hR hℓ hg
  -- superround 1: proposals
  have hinit : ∀ q, (out t (σ R t (8 * Q) q)).init =
      some (.propose (propSet (σ R t (8 * Q) q)) Q) := by
    intro q
    simp [out, show (8 * Q) % 8 = 0 by omega, show 8 * Q / 8 = Q by omega]
  have hacc1 : ∀ p, p ∉ R.byz → AccProp t (σ R t (8 * Q + 2) p).echoRcv Q c := by
    intro p hp
    refine (ncard_BF hR).trans (ncard_mono fun j hj => ?_)
    obtain ⟨q, hq, rfl⟩ := BF_correct hR hj
    exact ⟨_, hc q hq, bcast_correct hR (by omega) (by omega) hq (hinit q) p hp⟩
  -- superround 2: the lock request of the leader
  have hls : ∃ v, lockSend t (σ R t (8 * Q + 2) s) = some v := by
    unfold lockSend
    rw [dite_eq_left]
    · exact ⟨_, rfl⟩
    · simp only [me_σ, rnd_σ, show (8 * Q + 2) / 8 = Q by omega]
      exact ⟨hl, c, hacc1 s hs.1⟩
  obtain ⟨v, hv⟩ := hls
  have hvs := (lockSend_spec hv).2
  simp only [rnd_σ, show (8 * Q + 2) / 8 = Q by omega] at hvs
  have hlr : ∀ q, q ∉ R.byz → ∀ w, w ∈ (σ R t (8 * Q + 4) q).lockRcv ↔ w = v := by
    intro q hq w
    rw [show 8 * Q + 4 = (8 * Q + 3) + 1 from rfl, lockRcv_succ, ite_eq_right (by omega),
      show 8 * Q + 3 = (8 * Q + 2) + 1 from rfl, lockRcv_succ, ite_eq_left (by omega),
      show (8 * Q + 2) / 8 = Q by omega]
    constructor
    · rintro ⟨j, m, hj, hm, hml⟩
      have e : j = R.id s := Fin.ext (hj.trans hl.symm)
      subst e
      rw [rcv_src_UCp hR hm hs] at hml
      simp only [out, rnd_σ, show (8 * Q + 2) % 8 = 2 by omega, ite_true, hv] at hml
      exact (Option.some.inj hml).symm
    · rintro rfl
      exact ⟨R.id s, _, hl, rcv_of_gst hR (by omega) hs.1 hq,
        by simp [out, show (8 * Q + 2) % 8 = 2 by omega, hv]⟩
  -- superround 3: votes
  have hvote : ∀ q, q ∉ R.byz → (out t (σ R t (8 * Q + 4) q)).init = some (.vote v Q) := by
    intro q hq
    have hpv : AccProp t (σ R t (8 * Q + 4) q).echoRcv Q v :=
      AccProp_relay hR hvs le_rfl (by omega) hq
    have hvc : voteChoice t (σ R t (8 * Q + 4) q) = some v := by
      have hex : ∃ w, w ∈ (σ R t (8 * Q + 4) q).lockRcv ∧
          AccProp t (σ R t (8 * Q + 4) q).echoRcv ((σ R t (8 * Q + 4) q).rnd / 8) w := by
        simp only [rnd_σ, show (8 * Q + 4) / 8 = Q by omega]
        exact ⟨v, (hlr q hq v).2 rfl, hpv⟩
      unfold voteChoice
      rw [dite_eq_left hex]
      congr 1
      exact (hlr q hq _).1 hex.choose_spec.1
    simp [out, show (8 * Q + 4) % 8 = 4 by omega, show (8 * Q + 4) / 8 = Q by omega, hvc]
  have hacc3 : ∀ p, p ∉ R.byz → AccVote t (σ R t (8 * Q + 6) p).echoRcv v Q := by
    intro p hp
    refine (ncard_BF hR).trans (ncard_mono fun j hj => ?_)
    obtain ⟨q, hq, rfl⟩ := BF_correct hR hj
    exact bcast_correct hR (by omega) (by omega) hq (hvote q hq) p hp
  -- superround 4: acks
  have hack : ∀ q, q ∉ R.byz → (σ R t (8 * Q + 6) q).ackVal = some v := by
    intro q hq
    rw [ackVal_spec]
    have hex : ∃ w, AccVote t (σ R t (8 * Q + 6) q).echoRcv w Q := ⟨v, hacc3 q hq⟩
    unfold ackChoice
    rw [dite_eq_left hex]
    congr 1
    exact vote_quorum hR hℓ (r := 8 * Q + 6) (p := q) hex.choose_spec (hacc3 q hq)
  have hd : decNew t (σ R t (8 * Q + 6) s) (rcv R t (8 * Q + 6) s) ≠ none := by
    unfold decNew
    rw [dite_eq_left]
    · simp
    · simp only [rnd_σ, me_σ, show (8 * Q + 6) % 8 = 6 by omega,
        show (8 * Q + 6) / 8 = Q by omega, true_and]
      refine ⟨hl, v, by rw [lockReq_spec, hv], (ncard_BF hR).trans (ncard_mono fun j hj => ?_)⟩
      obtain ⟨q, hq, rfl⟩ := BF_correct hR hj
      exact ⟨_, rcv_of_gst hR (by omega) hq hs.1,
        by simp [out, show (8 * Q + 6) % 8 = 6 by omega, hack q hq]⟩
  rw [show 8 * Q + 7 = (8 * Q + 6) + 1 from rfl, dec_succ]
  obtain ⟨d, hd'⟩ := Option.ne_none_iff_exists'.1 hd
  rw [hd', Option.or_some]
  simp

/-- **Termination.** -/
theorem termination {p : P} (hp : p ∉ R.byz) : ∃ r v, (σ R t r p).dec = some v := by
  have h3 := three_t_lt hR hℓ
  set K := R.gst + 1
  have hdec : ∀ s, UCp R s → ∃ v, (σ R t (8 * (ℓ * (K + 1)) + 7) s).dec = some v := by
    intro s hs
    have hi := (R.id s).isLt
    have hK : K ≤ ℓ * K := Nat.le_mul_of_pos_left K (by omega)
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (leader_decides hR hℓ
      (Q := ℓ * K + (R.id s).val) (by omega) hs
      (by unfold IsLeader; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]))
    refine ⟨v, dec_mono ?_ hv⟩
    have : ℓ * (K + 1) = ℓ * K + ℓ := by ring
    omega
  obtain ⟨j₀, s₀, hs₀, -⟩ : ∃ j, ∃ s, UCp R s ∧ R.id s = j := by
    have := ncard_UC hR hℓ
    obtain ⟨j, hj⟩ := (Set.ncard_pos (Set.toFinite _)).1
      (by omega : 0 < {j | ∃ s, UCp R s ∧ R.id s = j}.ncard)
    exact ⟨j, hj⟩
  obtain ⟨v, hv⟩ := hdec s₀ hs₀
  set r := 8 * (ℓ * (K + 1)) + 7
  have hK : R.gst ≤ r := by
    have : K ≤ ℓ * (K + 1) := le_trans (Nat.le_succ K) (Nat.le_mul_of_pos_left _ (by omega))
    omega
  have hd : decNew t (σ R t r p) (rcv R t r p) ≠ none := by
    have h7 : r % 8 = 7 := by omega
    have hcnt : t + 1 ≤ {j | ∃ m, (j, m) ∈ rcv R t r p ∧ m.dec = some v}.ncard := by
      refine le_trans (by omega) ((ncard_UC hR hℓ).trans (ncard_mono ?_))
      rintro j ⟨s, hs, rfl⟩
      obtain ⟨w, hw⟩ := hdec s hs
      have := agreement hR hℓ hs.1 hs₀.1 hw hv
      subst this
      exact ⟨_, rcv_of_gst hR hK hs.1 hp, by simp [out, h7, hw]⟩
    unfold decNew
    split_ifs with h6 h7'
    · simp
    · simp
    · exact absurd ⟨by simpa using h7, v, hcnt⟩ h7'
  refine ⟨r + 1, ?_⟩
  rw [dec_succ]
  obtain ⟨d, hd'⟩ := Option.ne_none_iff_exists'.1 hd
  rw [hd', Option.or_some]
  exact ⟨_, rfl⟩

/-- Byzantine agreement holds in every valid run of the algorithm. -/
theorem ba : R.BA (alg ℓ t V) where
  termination p hp := by
    obtain ⟨r, v, h⟩ := termination hR hℓ hp
    exact ⟨v, r, h⟩
  agreement p hp q hq v w := by
    rintro ⟨r, h₁⟩ ⟨r', h₂⟩
    exact agreement hR hℓ hp hq h₁ h₂
  validity v hv p hp w := by
    rintro ⟨r, h⟩
    exact validity hR hℓ hv hp h

end

/-- The algorithm of Figure 5 solves Byzantine agreement in the basic partially synchronous model
against unrestricted Byzantine processes whenever `2ℓ > n + 3t`. -/
theorem alg_solves {n ℓ t : ℕ} (hℓ : n + 3 * t < 2 * ℓ) (V : Type) :
    Solves .psync .unrestricted n t (alg ℓ t V) := by
  intro P _ _ hP R hR
  exact ba hR.1 (by rw [hP]; exact hℓ)

/-- **Proposition 5** of [Delporte-Gallet et al., PODC 2011]: partially synchronous Byzantine
agreement is solvable even with innumerate processes (and unrestricted Byzantine processes) if
`ℓ > (n + 3t)/2`. -/
theorem prop5 {n ℓ t : ℕ} (_hn : 3 * t < n) (hℓ : n + 3 * t < 2 * ℓ) (V : Type) :
    Solvable .psync .unrestricted .innumerate n ℓ t V :=
  ⟨Msg ℓ V, St ℓ V, alg ℓ t V, alg_innumerate t, alg_solves hℓ V⟩

end Podc.HomonymsBA.Psync
