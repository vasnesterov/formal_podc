import Papers.PODC2022.FullyDefective.Robbins.Invariant

/-!
# Lemma 11 of [CCGS22] (safety part): preservation of the invariant

Every step of Algorithm 3 preserves `Inv` (`Robbins/Invariant.lean`); hence `Inv` holds in every
reachable configuration (`Reach.inv`). Corollaries: Lemma 11(2) (single token holder) and
Lemma 11(3) (global consistency: every log is a prefix of the sequence of the payloads sent by the
successive token holders).
-/

set_option linter.unusedSectionVars false

namespace Podc.FullyDefective.RobbinsSim

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {R : RobbinsCycle G}

/-! ### Positions -/

lemma cast_succ_add (τ : ZMod R.L) (s : ℕ) : τ + ((s + 1 : ℕ) : ZMod R.L) = τ + s + 1 := by
  push_cast; ring

lemma firstOcc_of_cntF_zero {u : V} {a : ZMod R.L} {s : ℕ} (ha : R.C a ≠ u)
    (h0 : cntF R u a s = 0) (hu : R.C (a + s + 1) = u) : firstOcc R u a = a + s + 1 := by
  rw [firstOcc_of_ne ha, firstOcc_add_cntF h0, firstOcc_self hu]

lemma cntF_pos_of {x : V} {a : ZMod R.L} {s : ℕ} (hs : 0 < s) (hx : R.C (a + s) = x) :
    0 < cntF R x a s := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [cntF_succ]; rw [cast_succ_add] at hx; simp [hx]

lemma cntF_succ_of_ne {v : V} {a : ZMod R.L} {s : ℕ} (h : R.C (a + s + 1) ≠ v) :
    cntF R v a (s + 1) = cntF R v a s := by
  rw [cntF_succ]; simp [h]

lemma Phase.sent_le_one (ph : Phase V R.L) : ph.sent ≤ 1 := by cases ph <;> simp [Phase.sent]

lemma C_ne_of_mult {x u : V} {j : ZMod R.L} (h : 0 < mult R x u) (hx : R.C j = u) (hu : R.C (j + 1) = x) :
    False := by
  have := mult_eq_zero_of_pos h; rw [← hx, ← hu] at this
  exact absurd (mult_pos_of j) (by omega)

/-! ### Request pulses -/

section reqRead

variable (u x : V) (s : Node V R.L)

/-- The reaction to a pulse read as a `request` pulse (lines 1–7). -/
lemma react_req_cases (h : s.ph.isReq = true) :
    ((react R u s x).dst = none ∧ (react R u s x).s.tok = s.tok ∧ (react R u s x).s.ph.IsTok ∧
      (s.tok = true → (react R u s x).s.ph.isReq = true) ∧
      (react R u s x).s.log = s.log ∧ (react R u s x).s.q = s.q ∧ (react R u s x).s.o = s.o) ∨
    (s.tok = true ∧ (react R u s x).dst = some (R.C (s.o - 1)) ∧
      (react R u s x).s = { s with ph := .ready, tok := false }) := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph <;> simp only [Phase.isReq, Bool.false_eq_true] at h <;> simp only [react] <;>
  · rcases hd : (onReq R _ _ _).dst with _ | y
    · refine Or.inl ⟨rfl, onReq_tok _ _ _ hd, onReq_isTok _ _ _, fun ht => ?_, onReq_log _ _ _,
        onReq_q _ _ _, onReq_o _ _ _⟩
      unfold onReq at hd ⊢; split_ifs at hd ⊢
      · unfold release at hd; simp [ht] at hd
      · rfl
    · obtain ⟨h1, rfl, h3⟩ := onReq_dst _ _ _ hd
      exact Or.inr ⟨h1, rfl, h3⟩

end reqRead

/-- The `waits` condition for a pulse read as a `request` pulse: the channel is clockwise. -/
lemma mult_pos_of_req {c : Config V R.L} (hC : Common c) {u x : V} (hw : waits R u (c.node u) x)
    (hq : (c.node u).ph.isReq = true) : 0 < mult R x u := by
  revert hw hq
  rcases hph : (c.node u).ph with _ | need | _ | _ | _ | _ | _ <;>
    simp [waits, hph, Phase.isReq]
  intro h; exact lt_of_lt_of_le h (hC.needLe u need hph x)

/-! ### Initial configuration, `push`, `start` -/

theorem inv_init (τ₀ : ZMod R.L) {qs : V → List ℕ} (hqs : ∀ u, ∀ a ∈ qs u, 0 < a) :
    Inv (init R τ₀ qs) := by
  refine ⟨⟨fun x y => ?_, fun x y => ?_, fun u need h => ?_, fun u need h => ?_, hqs, fun u => rfl⟩,
    Or.inl ⟨?_, ?_, ?_⟩⟩
  · simp [init, rcv, snt, Config.wave, Phase.rIn, Phase.sent]
  · simp [init, rcv, snt, Phase.rIn, Phase.sent]
  · simp [init] at h
  · simp [init] at h
  · intro u; rfl
  · intro u; trivial
  · left; simp [init, Phase.isReq]

theorem inv_push {c : Config V R.L} (h : Inv c) (u : V) {a : ℕ} (ha : 0 < a) :
    Inv (next R c (.push u a)) := by
  obtain ⟨hC, hS⟩ := h
  set c' := next R c (.push u a)
  have hn : ∀ v, (c'.node v).ph = (c.node v).ph ∧ (c'.node v).tok = (c.node v).tok ∧
      (c'.node v).log = (c.node v).log ∧ (c'.node v).o = (c.node v).o := by
    intro v; by_cases hv : v = u <;> simp [c', next, Function.update_apply, hv]
  have hep : ∀ v, c'.ep v = c.ep v := fun v => by simp only [Config.ep, (hn v).2.2.1]
  have hrcv : ∀ y x, rcv R c' y x = rcv R c y x := fun y x => by simp only [rcv, hep, (hn y).1]
  have hsnt : ∀ x y, snt R c' x y = snt R c x y := fun x y => by simp only [snt, hep, (hn x).1]
  have hw : c'.wave = c.wave := rfl
  have hnode : ∀ v, c'.node v = { c.node v with q := (c'.node v).q } := by
    intro v; by_cases hv : v = u <;> simp [c', next, Function.update_apply, hv]
  refine ⟨⟨fun x y => ?_, fun x y => ?_, fun v need hv => ?_, fun v need hv => ?_, fun v b hb => ?_,
    fun v => by rw [(hn v).2.2.2]; exact hC.rot v⟩, ?_⟩
  · rw [hrcv, hsnt, hw]; exact hC.netEq x y
  · rw [hrcv, hsnt]; exact hC.reqLe x y
  · rw [(hn v).1] at hv; exact hC.needLe v need hv
  · rw [(hn v).1] at hv; exact hC.needPos v need hv
  · by_cases hv : v = u
    · subst hv; simp [c', next] at hb; rcases hb with hb | rfl
      · exact hC.posq _ _ hb
      · exact ha
    · simp [c', next, hv] at hb; exact hC.posq _ _ hb
  · have e : ∀ v, c'.node v = { c.node v with q := (c'.node v).q } := hnode
    rcases hS with H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩
    · refine Or.inl ⟨fun v => by rw [(hn v).2.2.1]; exact H.log v,
        fun v => by rw [(hn v).1]; exact H.isTok v, ?_⟩
      simp only [(hn _).1, (hn _).2.1, show c'.τ = c.τ from rfl, show c'.wv = c.wv from rfl]
      exact H.tok
    · refine Or.inr (Or.inl ⟨pre, d, s, H.ds_eq, H.s_lt, H.wv, by rw [(hn _).1]; exact H.hph,
        by rw [(hn _).2.1]; exact H.htok, by rw [(hn _).2.2.1]; exact H.hlog, fun v hv => ?_⟩)
      obtain ⟨h1, h2, h3⟩ := H.others v hv
      refine ⟨by rw [(hn v).2.1]; exact h1, by rw [(hn v).2.2.1]; exact h2, ?_⟩
      unfold DataNode at h3 ⊢; rw [(hn v).1]; exact h3
    · refine Or.inr (Or.inr ⟨pre, d, r, H.ds_eq, H.r_lt, H.wv, by rw [(hn _).1]; exact H.hph,
        by rw [(hn _).2.1]; exact H.htok, by rw [(hn _).2.2.1]; exact H.hlog, fun v hv => ?_⟩)
      obtain ⟨h1, h3⟩ := H.others v hv
      refine ⟨by rw [(hn v).2.1]; exact h1, ?_⟩
      unfold EndNode at h3 ⊢; rw [(hn v).1, (hn v).2.2.1]; exact h3

/-- The stages are preserved when one node changes its program point within the token phase. -/
lemma stage_ph_change {c c' : Config V R.L} {u : V} {ph' : Phase V R.L}
    (hS : TokStage c ∨ (∃ pre d s, DataStage c pre d s) ∨ ∃ pre d r, EndStage c pre d r)
    (hnode : ∀ v, v ≠ u → c'.node v = c.node v) (hu : c'.node u = { c.node u with ph := ph' })
    (hold : (c.node u).ph.isReq = true) (hnew : ph'.IsTok)
    (htok : (c.node u).tok = true → ph'.isReq = true) (hτ : c'.τ = c.τ) (hds : c'.ds = c.ds) (hwv : c'.wv = c.wv) :
    TokStage c' ∨ (∃ pre d s, DataStage c' pre d s) ∨ ∃ pre d r, EndStage c' pre d r := by
  have hlog : ∀ v, (c'.node v).log = (c.node v).log := fun v => by
    by_cases hv : v = u
    · subst hv; rw [hu]
    · rw [hnode v hv]
  have htk : ∀ v, (c'.node v).tok = (c.node v).tok := fun v => by
    by_cases hv : v = u
    · subst hv; rw [hu]
    · rw [hnode v hv]
  rcases hS with H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩
  · refine Or.inl ⟨fun v => by rw [hlog, hds]; exact H.log v, fun v => ?_, ?_⟩
    · by_cases hv : v = u
      · subst hv; rw [hu]; exact hnew
      · rw [hnode v hv]; exact H.isTok v
    · rw [hτ, hwv]
      rcases H.tok with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h5⟩
      · refine Or.inl ⟨by rw [htk]; exact h1, ?_, fun v hv => by rw [htk]; exact h3 v hv, h4⟩
        by_cases hv : R.C c.τ = u
        · rw [hv, hu]; exact htok (hv ▸ h1)
        · rw [hnode _ hv]; exact h2
      · refine Or.inr ⟨fun v => by rw [htk]; exact h1 v, h2, ?_⟩
        have hne : R.C c.τ ≠ u := by rintro hh; rw [hh] at h5; rw [h5] at hold; cases hold
        rw [hnode _ hne]; exact h5
  · have hT : u ≠ R.C c.τ := by rintro rfl; rw [H.hph] at hold; simp [Phase.isReq] at hold
    refine Or.inr (Or.inl ⟨pre, d, s, by rw [hds]; exact H.ds_eq, H.s_lt, by rw [hwv, hτ]; exact H.wv,
      by rw [hτ, hnode _ hT.symm]; exact H.hph, by rw [hτ, htk]; exact H.htok,
      by rw [hτ, hlog]; exact H.hlog, fun v hv => ?_⟩)
    rw [hτ] at hv ⊢
    obtain ⟨h1, h2, h3⟩ := H.others v hv
    refine ⟨by rw [htk]; exact h1, by rw [hlog]; exact h2, ?_⟩
    by_cases hvu : v = u
    · subst hvu; rw [hu]
      rcases h3 with ⟨h3, -⟩ | ⟨-, h3⟩
      · exact Or.inl ⟨h3, hnew⟩
      · rw [h3] at hold; simp [Phase.isReq] at hold
    · rw [hnode v hvu]; exact h3
  · have hT : u ≠ R.C c.τ := by rintro rfl; rw [H.hph] at hold; simp [Phase.isReq] at hold
    refine Or.inr (Or.inr ⟨pre, d, r, by rw [hds]; exact H.ds_eq, H.r_lt, by rw [hwv, hτ]; exact H.wv,
      by rw [hτ, hnode _ hT.symm]; exact H.hph, by rw [hτ, htk]; exact H.htok,
      by rw [hτ, hlog]; exact H.hlog, fun v hv => ?_⟩)
    rw [hτ] at hv ⊢
    obtain ⟨h1, h3⟩ := H.others v hv
    refine ⟨by rw [htk]; exact h1, ?_⟩
    by_cases hvu : v = u
    · subst hvu; rw [hu]
      rcases h3 with ⟨-, h3, -⟩ | ⟨-, -, h3, -⟩ | ⟨h3, -, h4⟩
      · rw [h3] at hold; simp [Phase.isReq] at hold
      · rw [h3] at hold; simp [Phase.isReq] at hold
      · exact Or.inr (Or.inr ⟨h3, hnew, h4⟩)
    · rw [hnode v hvu]; exact h3

theorem inv_start {c : Config V R.L} (h : Inv c) {u : V} (hen : Enabled R c (.start u)) :
    Inv (next R c (.start u)) := by
  obtain ⟨hC, hS⟩ := h
  obtain ⟨hidle, -⟩ := hen
  have hph : (c.node u).ph = .idle := by
    revert hidle; cases (c.node u).ph <;> simp [Phase.isIdle]
  set c' := next R c (.start u)
  have hnode : ∀ v, v ≠ u → c'.node v = c.node v := fun v hv => by simp [c', next, hv]
  have hu : c'.node u = { c.node u with ph := .waitReq fun y => mult R y u } := by simp [c', next]
  have hep : ∀ v, c'.ep v = c.ep v := fun v => by
    by_cases hv : v = u
    · subst hv; simp only [Config.ep, hu]
    · simp only [Config.ep, hnode v hv]
  have hrcv : ∀ y x, rcv R c' y x = rcv R c y x := fun y x => by
    by_cases hy : y = u
    · subst hy; simp [rcv, hu, hph, Phase.rIn, hep]
    · simp [rcv, hnode y hy, hep]
  have hsnt : ∀ x y, snt R c' x y = snt R c x y + if x = u then mult R u y else 0 := fun x y => by
    by_cases hx : x = u
    · subst hx; simp [snt, hu, hph, Phase.sent, hep]; ring
    · simp [snt, hnode x hx, hx, hep]
  refine ⟨⟨fun x y => ?_, fun x y => ?_, fun v need hv => ?_, fun v need hv => ?_, fun v b hb => ?_,
    fun v => ?_⟩,
    stage_ph_change hS hnode hu (by rw [hph]; rfl) trivial (fun _ => rfl) rfl rfl rfl⟩
  · rw [hrcv, hsnt]; have := hC.netEq x y
    have hn : c'.net x y = c.net x y + if x = u then mult R u y else 0 := rfl
    have hw : c'.wave x y = c.wave x y := rfl
    rw [hn, hw]; omega
  · rw [hrcv, hsnt]; have := hC.reqLe x y; omega
  · by_cases hvu : v = u
    · subst hvu; rw [hu] at hv; cases hv; exact fun _ => le_rfl
    · rw [hnode v hvu] at hv; exact hC.needLe v need hv
  · by_cases hvu : v = u
    · subst hvu; rw [hu] at hv; cases hv
      obtain ⟨j, hj⟩ := R.surj v
      exact ⟨R.C (j - 1), by rw [← hj]; exact mult_pos_of' j⟩
    · rw [hnode v hvu] at hv; exact hC.needPos v need hv
  · by_cases hvu : v = u
    · subst hvu; rw [hu] at hb; exact hC.posq v b hb
    · rw [hnode v hvu] at hb; exact hC.posq v b hb
  · by_cases hvu : v = u
    · subst hvu; rw [hu]; exact hC.rot v
    · rw [hnode v hvu]; exact hC.rot v

/-! ### Reading a pulse: generalities -/

lemma react_o {u x : V} {s : Node V R.L} (h : tokRecv R u s x = false) : (react R u s x).s.o = s.o := by
  rcases s with ⟨ph, tok, q, log, o⟩
  cases ph with
  | idle | waitReq _ => simp [react]
  | ready =>
    simp only [tokRecv, Phase.isReady, Bool.true_and, decide_eq_false_iff_not, not_lt,
      Nat.le_zero] at h
    simp [react, h]
  | _ => simp only [react] <;> (try split_ifs) <;> try rfl

lemma next_τ_of {c : Config V R.L} {u x : V} (h : tokRecv R u (c.node u) x = false) :
    (next R c (.recv u x)).τ = c.τ := by simp [next_recv_τ, h]

lemma next_ds_of {c : Config V R.L} {u x : V} (h : tokRecv R u (c.node u) x = false) :
    (next R c (.recv u x)).ds = c.ds := by simp [next_recv_ds, h]

lemma rot_of {c : Config V R.L} (hC : Common c) {u x : V} (h : tokRecv R u (c.node u) x = false) (v : V) :
    ((next R c (.recv u x)).node v).o = firstOcc R v (next R c (.recv u x)).τ := by
  rw [next_τ_of h, next_recv_node]; split_ifs with hv
  · subst hv; rw [react_o h]; exact hC.rot v
  · exact hC.rot v

lemma tokRecv_of_not_ready {u x : V} {s : Node V R.L} (h : s.ph.isReady = false) :
    tokRecv R u s x = false := by simp [tokRecv, h]

lemma prevOcc_firstOcc (u : V) (a : ZMod R.L) :
    prevOcc R (firstOcc R u a) = lastOcc R u (a - 1) := by
  rw [prevOcc_eq, C_firstOcc, lastOcc_firstOcc_sub_one]

lemma mult_pos_succ (j : ZMod R.L) {x y : V} (hx : R.C j = x) (hy : R.C (j + 1) = y) :
    0 < mult R x y := by rw [← hx, ← hy]; exact mult_pos_of j

/-! ### Request pulses never stand in for the token/data/end pulse -/

lemma DataStage.log_all {c : Config V R.L} {pre d s} (H : DataStage c pre d s) (v : V) :
    (c.node v).log = pre := by
  by_cases hv : v = R.C c.τ
  · rw [hv, H.hlog]
  · exact (H.others v hv).2.1

lemma req_ok {c : Config V R.L} (hC : Common c)
    (hS : TokStage c ∨ (∃ pre d s, DataStage c pre d s) ∨ ∃ pre d r, EndStage c pre d r)
    {u x : V} (hw : waits R u (c.node u) x) (hq : (c.node u).ph.isReq = true)
    (hwv : c.wv = some (x, u)) : rcv R c u x < snt R c x u := by
  have hm := mult_pos_of_req hC hw hq
  rcases hS with H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩
  · rcases H.tok with ⟨-, -, -, h⟩ | ⟨-, h, -⟩ <;> rw [hwv] at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact (C_ne_of_mult hm h.2.symm (by rw [sub_add_cancel]; exact h.1.symm)).elim
  · rw [H.wv] at hwv
    simp only [Option.some.injEq, Prod.mk.injEq] at hwv
    obtain ⟨hx, hu⟩ := hwv
    have huT : u ≠ R.C c.τ := by
      rintro rfl; have := H.hph; revert hq; rw [this]; simp [Phase.isReq]
    have hrIn : (c.node u).ph.rIn (mult R x u) x < mult R x u := by
      revert hw hq
      rcases hph : (c.node u).ph with _ | need | _ | _ | _ | _ | _ <;>
        simp [waits, hph, Phase.isReq, Phase.rIn]
      intro h; exact ⟨hm, h⟩
    have hsx : (c.node x).ph.sent = 1 := by
      by_cases hxT : x = R.C c.τ
      · rw [hxT, H.hph]; rfl
      · have hs0 : 0 < s := by
          rcases Nat.eq_zero_or_pos s with h0 | h0
          · subst h0; simp at hx; exact (hxT hx.symm).elim
          · exact h0
        rcases (H.others x hxT).2.2 with ⟨h0, -⟩ | ⟨-, h⟩
        · have := cntF_pos_of hs0 hx; omega
        · rw [h]; rfl
    simp only [rcv, snt, Config.ep, H.log_all, hsx]
    rw [mul_add, mul_one]; omega
  · rw [H.wv] at hwv
    simp only [Option.some.injEq, Prod.mk.injEq] at hwv
    exact (C_ne_of_mult hm hwv.2 hwv.1).elim

/-- Reading a `request` pulse. -/
theorem inv_recv_req {c : Config V R.L} (h : Inv c) {u x : V} (hen : Enabled R c (.recv u x))
    (hq : (c.node u).ph.isReq = true) : Inv (next R c (.recv u x)) := by
  obtain ⟨hC, hS⟩ := h
  have hready : (c.node u).ph.isReady = false := by
    revert hq; cases (c.node u).ph <;> simp [Phase.isReq, Phase.isReady]
  have htr := tokRecv_of_not_ready (R := R) (u := u) (x := x) hready
  have hτ := next_τ_of (c := c) htr
  have hds := next_ds_of (c := c) htr
  have hCm : ∀ (hdst : ∀ y, (react R u (c.node u) x).dst = some y → (c.node u).ph.isReq = true →
      c.wv = none), Common (next R c (.recv u x)) := fun hdst =>
    common_recv hC hen (fun h => by rw [hq] at h; cases h) (fun _ => req_ok hC hS hen.1 hq) hdst
      (rot_of hC htr)
  rcases react_req_cases u x (c.node u) hq with ⟨hd, htok, hIs, hholdreq, hlog, hqq, ho⟩ |
    ⟨htok, hd, hs⟩
  · refine ⟨hCm (fun y h => by rw [hd] at h; cases h), ?_⟩
    refine stage_ph_change (u := u) (ph' := (react R u (c.node u) x).s.ph) hS
      (fun v hv => next_recv_node_ne _ _ hv) ?_ hq hIs hholdreq hτ hds ?_
    · rw [next_recv_node_self]
      rcases e : react R u (c.node u) x with ⟨⟨ph, tk, qq, lg, oo⟩, rq, ds'⟩
      rw [e] at htok hlog hqq ho; simp_all
    · simp [next_recv_wv, hd, hq]
  · -- the token holder releases the token (lines 4–6): only in the token stage
    have hTS : TokStage c ∧ u = R.C c.τ ∧ c.wv = none := by
      rcases hS with H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩
      · rcases H.tok with ⟨h1, -, h3, h4⟩ | ⟨h1, -⟩
        · refine ⟨H, ?_, h4⟩; by_contra hne; rw [h3 u hne] at htok; cases htok
        · rw [h1 u] at htok; cases htok
      · by_cases hu : u = R.C c.τ
        · rw [hu, H.hph] at hq; simp [Phase.isReq] at hq
        · rw [(H.others u hu).1] at htok; cases htok
      · by_cases hu : u = R.C c.τ
        · rw [hu, H.hph] at hq; simp [Phase.isReq] at hq
        · rw [(H.others u hu).1] at htok; cases htok
    obtain ⟨H, hu, hwv0⟩ := hTS
    refine ⟨hCm (fun _ _ _ => hwv0), Or.inl ⟨fun v => ?_, fun v => ?_, Or.inr ⟨fun v => ?_, ?_⟩⟩⟩
    · rw [hds, next_recv_node]; split_ifs with hv
      · rw [hs]; subst hv; exact H.log v
      · exact H.log v
    · rw [next_recv_node]; split_ifs with hv
      · rw [hs]; trivial
      · exact H.isTok v
    · rw [next_recv_node]; split_ifs with hv
      · rw [hs]
      · rcases H.tok with ⟨-, -, h3, -⟩ | ⟨h1, -⟩
        · exact h3 v (by rw [← hu]; exact hv)
        · exact h1 v
    · refine ⟨by rw [next_recv_wv, hd, hτ, ← hu, hC.rot u, hu, firstOcc_self rfl], ?_⟩
      rw [hτ, ← hu, next_recv_node_self, hs]

/-! ### Reading the token pulse (token stage) -/

lemma ready_of_tok {s : Node V R.L} (h1 : s.ph.IsTok) (h2 : s.ph.isReq = false) : s.ph = .ready := by
  rcases s with ⟨ph, tok, q, log, o⟩; cases ph <;> simp_all [Phase.IsTok, Phase.isReq]

/-- Reading a non-request pulse in the token stage: the token pulse (lines 9–16). -/
theorem inv_recv_tok {c : Config V R.L} (hC : Common c) (H : TokStage c) {u x : V}
    (hen : Enabled R c (.recv u x)) (hq : (c.node u).ph.isReq = false) :
    Inv (next R c (.recv u x)) := by
  have hph := ready_of_tok (H.isTok u) hq
  have hwv : c.wv = some (x, u) := wave_of_read hC hen.2 (by rw [hph]; rfl)
    (Nat.mul_le_mul_left _ (by
      have := (c.node x).ph.sent_le_one; simp only [Config.ep, H.log]; omega))
  rcases H.tok with ⟨-, -, -, h⟩ | ⟨htk, h, -⟩
  · rw [hwv] at h; cases h
  rw [hwv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨hx, hu⟩ := h
  have hmux : 0 < mult R u x := mult_pos_succ (c.τ - 1) hu.symm (by rw [sub_add_cancel]; exact hx.symm)
  have htr : tokRecv R u (c.node u) x = true := by simp [tokRecv, hph, Phase.isReady, hmux]
  have hprev : prevOcc R (c.node u).o = c.τ - 1 := by
    rw [hC.rot u, prevOcc_firstOcc, lastOcc_self hu.symm]
  have hτ' : (next R c (.recv u x)).τ = c.τ - 1 := by rw [next_recv_τ, htr, ite_eq_left rfl, hprev]
  have hrotv : ∀ v, v ≠ u → firstOcc R v (c.τ - 1) = firstOcc R v c.τ := fun v hv => by
    rw [firstOcc_of_ne (by rw [← hu]; exact Ne.symm hv), sub_add_cancel]
  have hCm : Common (next R c (.recv u x)) := by
    refine common_recv hC hen (fun _ => hwv) (fun h => by rw [hq] at h; cases h)
      (fun _ _ h => by rw [hq] at h; cases h) (fun v => ?_)
    rw [hτ', next_recv_node]; split_ifs with hv
    · subst hv; rw [firstOcc_self hu.symm]
      simp only [react, hph, hmux, ite_true]; split <;> simp [hprev]
    · rw [hC.rot v, hrotv v hv]
  refine ⟨hCm, ?_⟩
  rcases hqq : (c.node u).q with _ | ⟨a, rest⟩
  · -- line 14: forward the token
    have hr : react R u (c.node u) x =
        ⟨{ c.node u with o := c.τ - 1 }, false, some (R.C (c.τ - 1 - 1))⟩ := by
      simp only [react, hph, hmux, ite_true, hqq, hprev]
    have hds : (next R c (.recv u x)).ds = c.ds := by rw [next_recv_ds, htr, ite_eq_left rfl, hqq]
    refine Or.inl ⟨fun v => ?_, fun v => ?_, Or.inr ⟨fun v => ?_, ?_⟩⟩
    · rw [hds, next_recv_node]; split_ifs with hv
      · rw [hr]; subst hv; exact H.log v
      · exact H.log v
    · rw [next_recv_node]; split_ifs with hv
      · rw [hr]; subst hv; exact H.isTok v
      · exact H.isTok v
    · rw [next_recv_node]; split_ifs with hv
      · rw [hr]; subst hv; exact htk v
      · exact htk v
    · refine ⟨by rw [next_recv_wv, hr, hτ', hu], ?_⟩
      rw [hτ', ← hu, next_recv_node_self, hr]; exact hph
  · -- lines 12, 19–23: take the token
    have hr : react R u (c.node u) x =
        ⟨{  ph := .hdata a 1 (nextOcc R (c.τ - 1))
            tok := true
            q := rest
            log := (c.node u).log
            o := c.τ - 1 }, false, some (R.C (c.τ - 1 + 1))⟩ := by
      simp only [react, hph, hmux, ite_true, hqq, hprev]
    have hds : (next R c (.recv u x)).ds = c.ds ++ [a] := by
      rw [next_recv_ds, htr, ite_eq_left rfl, hqq]
    have ha : 0 < a := hC.posq u a (by rw [hqq]; simp)
    have hT : R.C (next R c (.recv u x)).τ = u := by rw [hτ', hu]
    refine Or.inr (Or.inl ⟨c.ds, a, 0, hds, Nat.mul_pos ha (Nat.pos_of_neZero _), ?_, ?_, ?_, ?_,
      fun v hv => ?_⟩)
    · rw [next_recv_wv, hr, hτ', hu]; simp
    · rw [hT, next_recv_node_self, hr, hτ', nextOcc_eq, ← hu]; simp
    · rw [hT, next_recv_node_self, hr]
    · rw [hT, next_recv_node_self, hr]; exact H.log u
    · rw [hT] at hv
      rw [next_recv_node_ne _ _ hv]
      exact ⟨htk v, H.log v, Or.inl ⟨by simp [cntF], H.isTok v⟩⟩

/-! ### The data stage -/

lemma cast_L_sub_one : ((R.L - 1 : ℕ) : ZMod R.L) = -1 := by
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (NeZero.ne _)), ZMod.natCast_self]; simp

lemma add_cast_eq_self_iff {τ : ZMod R.L} {n : ℕ} : τ + (n : ZMod R.L) = τ ↔ R.L ∣ n := by
  rw [add_eq_left, ZMod.natCast_eq_zero_iff]

lemma Phase.rIn_full {ph : Phase V R.L} (m : ℕ) (x : V) (h1 : ph.isReq = false) (h2 : ∀ p, ph ≠ .fend p) :
    ph.rIn m x = m := by
  cases ph <;> simp_all [Phase.isReq, Phase.rIn]

lemma DataStage.advance {c c' : Config V R.L} {pre : List ℕ} {d s : ℕ} (H : DataStage c pre d s)
    {u : V} (hu : R.C (c.τ + (s : ZMod R.L) + 1) = u) (hτ : c'.τ = c.τ) (hds : c'.ds = c.ds)
    (hs : s + 1 < d * R.L) (hwv : c'.wv = some (u, R.C (c.τ + (s : ZMod R.L) + 1 + 1)))
    (hnode : ∀ v, v ≠ u → c'.node v = c.node v)
    (hT : u = R.C c.τ → (c'.node u).ph = .hdata d ((s + 1) / R.L + 1)
        (firstOcc R u (c.τ + (s : ZMod R.L) + 1 + 1)) ∧ (c'.node u).tok = true ∧ (c'.node u).log = pre)
    (hO : u ≠ R.C c.τ → (c'.node u).tok = false ∧ (c'.node u).log = pre ∧
      DataNode (c'.node u) (cntF R u c.τ (s + 1)) (firstOcc R u (c.τ + (s : ZMod R.L) + 1 + 1))) :
    DataStage c' pre d (s + 1) := by
  have hc : c.τ + ((s + 1 : ℕ) : ZMod R.L) = c.τ + s + 1 := cast_succ_add _ _
  refine ⟨by rw [hds]; exact H.ds_eq, hs, by rw [hwv, hτ, hc, hu], ?_, ?_, ?_, fun v hv => ?_⟩
  · rw [hτ, hc]
    by_cases huT : u = R.C c.τ
    · rw [← huT]; exact (hT huT).1
    · rw [hnode _ (Ne.symm huT), H.hph]
      have hne : R.C (c.τ + s + 1) ≠ R.C c.τ := by rw [hu]; exact huT
      have hdiv : (s + 1) / R.L = s / R.L := by
        have : ¬ R.L ∣ s + 1 := fun hd => hne (by rw [← hc, add_cast_eq_self_iff.2 hd])
        rw [Nat.succ_div]; simp [this]
      rw [hdiv, firstOcc_of_ne hne]
  · rw [hτ]
    by_cases huT : u = R.C c.τ
    · rw [← huT]; exact (hT huT).2.1
    · rw [hnode _ (Ne.symm huT)]; exact H.htok
  · rw [hτ]
    by_cases huT : u = R.C c.τ
    · rw [← huT]; exact (hT huT).2.2
    · rw [hnode _ (Ne.symm huT)]; exact H.hlog
  · rw [hτ] at hv ⊢; rw [hc]
    by_cases hvu : v = u
    · subst hvu; exact hO hv
    · rw [hnode v hvu]
      obtain ⟨h1, h2, h3⟩ := H.others v hv
      have hne : R.C (c.τ + s + 1) ≠ v := by rw [hu]; exact Ne.symm hvu
      refine ⟨h1, h2, ?_⟩
      rw [cntF_succ_of_ne hne, ← firstOcc_of_ne hne]; exact h3

/-- Reading a non-request pulse in the data stage: a data pulse (lines 8–9, 21–30, 32–36). -/
theorem inv_recv_data {c : Config V R.L} (hC : Common c) {pre : List ℕ} {d s : ℕ}
    (H : DataStage c pre d s) {u x : V} (hen : Enabled R c (.recv u x))
    (hq : (c.node u).ph.isReq = false) : Inv (next R c (.recv u x)) := by
  have hnofend : ∀ p, (c.node u).ph ≠ .fend p := by
    intro p hp
    by_cases huT : u = R.C c.τ
    · rw [huT, H.hph] at hp; cases hp
    · rcases (H.others u huT).2.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hp] at h
      · exact h
      · cases h
  have hwv : c.wv = some (x, u) := wave_of_read hC hen.2 (Phase.rIn_full _ _ hq hnofend)
    (Nat.mul_le_mul_left _ (by
      have := (c.node x).ph.sent_le_one; simp only [Config.ep, H.log_all]; omega))
  rw [H.wv] at hwv; simp only [Option.some.injEq, Prod.mk.injEq] at hwv
  obtain ⟨hx, hu⟩ := hwv
  have hmxu : 0 < mult R x u := mult_pos_succ (c.τ + (s : ZMod R.L)) hx hu
  have hmux : mult R u x = 0 := mult_eq_zero_of_pos hmxu
  have htr : tokRecv R u (c.node u) x = false := by simp [tokRecv, hmux]
  have hτ := next_τ_of (c := c) htr
  have hds := next_ds_of (c := c) htr
  have hCm : Common (next R c (.recv u x)) :=
    common_recv hC hen (fun _ => by rw [H.wv, hx, hu]) (fun h => by rw [hq] at h; cases h)
      (fun _ _ h => by rw [hq] at h; cases h) (rot_of hC htr)
  refine ⟨hCm, ?_⟩
  have hs1 : s + 1 < d * R.L ∨ u = R.C c.τ := by
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt H.s_lt) with h | h
    · exact Or.inl h
    · right; rw [← hu, ← cast_succ_add, show s + 1 = d * R.L from h,
        add_cast_eq_self_iff.2 (dvd_mul_left _ _)]
  have hnode : ∀ v, v ≠ u → (next R c (.recv u x)).node v = c.node v :=
    fun v hv => next_recv_node_ne _ _ hv
  by_cases huT : u = R.C c.τ
  · -- the token holder (lines 21–30)
    have hph := H.hph
    rw [← huT] at hph
    have hp : firstOcc R u (c.τ + s + 1) = c.τ + s + 1 := firstOcc_self hu
    have ho : (c.node u).o = c.τ := by rw [hC.rot u, huT, firstOcc_self rfl]
    rw [hp] at hph
    by_cases hpo : c.τ + s + 1 = c.τ
    · have hdvd : R.L ∣ s + 1 := add_cast_eq_self_iff.1 (by rw [cast_succ_add]; exact hpo)
      have hdiv : (s + 1) / R.L = s / R.L + 1 := by rw [Nat.succ_div]; simp [hdvd]
      have hsL : s + 1 = (s / R.L + 1) * R.L := by rw [← hdiv, Nat.div_mul_cancel hdvd]
      by_cases htd : s / R.L + 1 < d
      · -- the next data pulse
        have hr : react R u (c.node u) x = ⟨{ c.node u with
            ph := .hdata d (s / R.L + 1 + 1) (nextOcc R c.τ) }, false, some (R.C (c.τ + 1))⟩ := by
          simp only [react, hph, ho, hpo, ite_true, htd]
        refine Or.inr (Or.inl ⟨pre, d, s + 1, H.advance hu hτ hds ?_ ?_ hnode (fun _ => ?_)
          (fun h => (h huT).elim)⟩)
        · rw [hsL]; exact Nat.mul_lt_mul_of_pos_right htd (Nat.pos_of_neZero _)
        · rw [next_recv_wv, hr, hpo]
        · rw [next_recv_node_self, hr, hdiv, hpo, nextOcc_eq, ← huT]
          exact ⟨rfl, by rw [huT]; exact H.htok, by rw [huT]; exact H.hlog⟩
      · -- line 28: the `end` pulse
        have hr : react R u (c.node u) x = ⟨{ c.node u with
            ph := .hend d (prevOcc R c.τ) }, false, some (R.C (c.τ - 1))⟩ := by
          simp only [react, hph, ho, hpo, ite_true, htd, ite_false]
        have hsd : s + 1 = d * R.L := by
          have h1 : d ≤ s / R.L + 1 := not_lt.1 htd
          have h2 : (s / R.L + 1) * R.L ≤ d * R.L := by rw [← hsL]; exact H.s_lt
          have h3 := Nat.le_of_mul_le_mul_right h2 (Nat.pos_of_neZero _)
          rw [hsL, le_antisymm h3 h1]
        have hT' : R.C (next R c (.recv u x)).τ = u := by rw [hτ, huT]
        refine Or.inr (Or.inr ⟨pre, d, R.L - 1, by rw [hds]; exact H.ds_eq,
          Nat.sub_lt (Nat.pos_of_neZero _) one_pos, ?_, ?_, ?_, ?_,
          fun v hv => ?_⟩)
        · rw [next_recv_wv, hr, hτ, cast_L_sub_one]; simp [huT, ← sub_eq_add_neg]
        · rw [hT', next_recv_node_self, hr, hτ, cast_L_sub_one, prevOcc_eq, ← huT,
            ← sub_eq_add_neg]
        · rw [hT', next_recv_node_self, hr]; rw [huT]; exact H.htok
        · rw [hT', next_recv_node_self, hr]; rw [huT]; exact H.hlog
        · rw [hT'] at hv; rw [hτ, hnode v hv]
          obtain ⟨h1, h2, h3⟩ := H.others v (by rw [← huT]; exact hv)
          have hcnt : cntF R v c.τ s = d * occ R v := by
            have := cntF_mul (R := R) v c.τ d
            rw [← hsd, cntF_succ_of_ne (by rw [hpo, ← huT]; exact Ne.symm hv)] at this
            exact this
          have hpos : 0 < cntF R v c.τ s := by
            rw [hcnt]; exact Nat.mul_pos (by
              rcases Nat.eq_zero_or_pos d with h0 | h0
              · have := H.s_lt; rw [h0] at this; omega
              · exact h0) (occ_pos v)
          rcases h3 with ⟨h3, -⟩ | ⟨-, h3⟩
          · omega
          refine ⟨h1, Or.inl ⟨by have := dist_lt c.τ (lastOcc R v (c.τ - 1)); omega, ?_, h2⟩⟩
          rw [h3, hcnt, hpo]
    · -- forward the data pulse to the next occurrence (lines 23–24)
      have hr : react R u (c.node u) x = ⟨{ c.node u with
          ph := .hdata d (s / R.L + 1) (nextOcc R (c.τ + s + 1)) }, false,
          some (R.C (c.τ + s + 1 + 1))⟩ := by
        simp only [react, hph, ho, hpo, ite_false]
      have hdiv : (s + 1) / R.L = s / R.L := by
        have : ¬ R.L ∣ s + 1 := fun hd => hpo (by rw [← cast_succ_add, add_cast_eq_self_iff.2 hd])
        rw [Nat.succ_div]; simp [this]
      refine Or.inr (Or.inl ⟨pre, d, s + 1, H.advance hu hτ hds ?_ ?_ hnode (fun _ => ?_)
        (fun h => (h huT).elim)⟩)
      · rcases lt_or_eq_of_le (Nat.succ_le_of_lt H.s_lt) with h | h
        · exact h
        · exact absurd (by rw [← cast_succ_add, show s + 1 = d * R.L from h,
            add_cast_eq_self_iff.2 (dvd_mul_left _ _)]) hpo
      · rw [next_recv_wv, hr]
      · rw [next_recv_node_self, hr, hdiv, nextOcc_eq, hu]
        exact ⟨rfl, by rw [huT]; exact H.htok, by rw [huT]; exact H.hlog⟩
  · obtain ⟨htk, hlog, hdn⟩ := H.others u huT
    have hs1' : s + 1 < d * R.L := hs1.resolve_right huT
    have hτne : R.C c.τ ≠ u := Ne.symm huT
    rcases hdn with ⟨h0, hIs⟩ | ⟨hk, hph⟩
    · -- line 8: the first data pulse
      have hph := ready_of_tok hIs hq
      have ho : (c.node u).o = c.τ + s + 1 := by
        rw [hC.rot u, firstOcc_of_cntF_zero hτne h0 hu]
      have hr : react R u (c.node u) x = ⟨{ c.node u with ph := .fdata 1 (nextOcc R (c.node u).o) },
          false, some (R.C ((c.node u).o + 1))⟩ := by
        simp only [react, hph, hmux, lt_irrefl, ite_false]
      refine Or.inr (Or.inl ⟨pre, d, s + 1, H.advance hu hτ hds hs1' ?_ hnode
        (fun h => (huT h).elim) (fun _ => ?_)⟩)
      · rw [next_recv_wv, hr, ho]
      · rw [next_recv_node_self, hr]
        refine ⟨htk, hlog, Or.inr ⟨by rw [cntF_succ]; simp [hu], ?_⟩⟩
        rw [cntF_succ, h0, ho, nextOcc_eq, hu]; simp
    · -- lines 34–35
      have hp : firstOcc R u (c.τ + s + 1) = c.τ + s + 1 := firstOcc_self hu
      rw [hp] at hph
      have hr : react R u (c.node u) x = ⟨{ c.node u with
          ph := .fdata (cntF R u c.τ s + 1) (nextOcc R (c.τ + s + 1)) }, false,
          some (R.C (c.τ + s + 1 + 1))⟩ := by
        simp only [react, hph, hmux, lt_irrefl, and_false, ite_false]
      refine Or.inr (Or.inl ⟨pre, d, s + 1, H.advance hu hτ hds hs1' ?_ hnode
        (fun h => (huT h).elim) (fun _ => ?_)⟩)
      · rw [next_recv_wv, hr]
      · rw [next_recv_node_self, hr]
        refine ⟨htk, hlog, Or.inr ⟨by rw [cntF_succ]; omega, ?_⟩⟩
        rw [cntF_succ, nextOcc_eq, hu]; simp

/-! ### The end stage -/

lemma Phase.rIn_zero (ph : Phase V R.L) (x : V) : ph.rIn 0 x = 0 := by
  cases ph <;> simp [Phase.rIn]

lemma EndStage.ep_le {c : Config V R.L} {pre : List ℕ} {d r : ℕ} (H : EndStage c pre d r) (v : V) :
    c.ep v ≤ pre.length + 1 := by
  by_cases hv : v = R.C c.τ
  · rw [Config.ep, hv, H.hlog]; omega
  · rcases (H.others v hv).2 with ⟨-, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ <;> rw [Config.ep, h] <;> simp

lemma dist_cast_eq {a : ZMod R.L} {p : ZMod R.L} {n : ℕ} (hn : n < R.L) (h : dist a p = n) :
    p = a + n := by
  apply dist_inj (a := a); rw [h, dist_add_natCast _ hn]

/-- In the end stage, a non-request pulse can only be the `end` pulse. -/
lemma EndStage.read {c : Config V R.L} (hC : Common c) {pre : List ℕ} {d r : ℕ} (H : EndStage c pre d r)
    {u x : V} (hen : Enabled R c (.recv u x)) (hq : (c.node u).ph.isReq = false) :
    R.C (c.τ + r) = u ∧ R.C (c.τ + r + 1) = x := by
  obtain ⟨hw, hnet⟩ := hen
  have key : c.wv = some (x, u) → R.C (c.τ + r) = u ∧ R.C (c.τ + r + 1) = x := fun h => by
    rw [H.wv] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact ⟨h.2, h.1⟩
  by_cases hm : mult R x u = 0
  · exact key (wave_of_read hC hnet (by rw [hm, Phase.rIn_zero]) (by rw [hm]; simp))
  exfalso
  have hm' : 0 < mult R x u := Nat.pos_of_ne_zero hm
  have hmux : mult R u x = 0 := mult_eq_zero_of_pos hm'
  suffices c.wv = some (x, u) by
    obtain ⟨h1, h2⟩ := key this
    exact absurd (mult_pos_succ _ h1 h2) (by omega)
  have hTu : ∀ p, R.C p = u → x = R.C (p + 1) → False := fun p hp hx =>
    absurd (mult_pos_succ p hp hx.symm) (by omega)
  by_cases huT : u = R.C c.τ
  · have hph := H.hph; rw [← huT] at hph
    simp only [waits, hph] at hw; exact (hTu _ (by rw [huT]; exact C_lastOcc _ _) hw).elim
  obtain ⟨-, hN⟩ := H.others u huT
  rcases hN with ⟨hl, hph, hlog⟩ | ⟨-, -, hph, -⟩ | ⟨hr, hIs, hlog⟩
  · -- `u` in its data phase: the clockwise channel it waits on carries no request pulse of the
    -- next epoch, since its sender has not completed the epoch
    simp only [waits, hph, hmux, lt_irrefl, and_false, or_false] at hw
    refine wave_of_read hC hnet (by rw [hph]; rfl) (Nat.mul_le_mul_left _ ?_)
    simp only [Config.ep]; rw [hlog]
    by_cases hxT : x = R.C c.τ
    · rw [hxT, H.hlog, H.hph]; simp [Phase.sent]
    rcases (H.others x hxT).2 with ⟨-, -, h⟩ | ⟨-, -, h1, h⟩ | ⟨hr', -, -⟩
    · rw [h]; have := (c.node x).ph.sent_le_one; omega
    · rw [h, h1]; simp [Phase.sent]
    · exfalso
      have hoT : firstOcc R u c.τ ≠ c.τ := fun h => huT (by rw [← h, C_firstOcc])
      have h1 := dist_firstOcc_le (u := x) c.τ (p := firstOcc R u c.τ - 1) hw.symm
      have h2 := dist_sub_one hoT
      have h3 := dist_le_lastOcc (u := u) c.τ (p := firstOcc R u c.τ) (C_firstOcc _ _)
      have h4 : dist c.τ (firstOcc R u c.τ) ≠ 0 := fun h => hoT (dist_eq_zero.1 h)
      omega
  · simp only [waits, hph] at hw; exact (hTu _ (C_lastOcc _ _) hw).elim
  · have hph := ready_of_tok hIs hq
    refine wave_of_read hC hnet (by rw [hph]; rfl) (Nat.mul_le_mul_left _ ?_)
    have h1 := H.ep_le x; have h2 := (c.node x).ph.sent_le_one
    simp only [Config.ep] at h1 ⊢; rw [hlog]; simp; omega

lemma EndNode.step {c : Config V R.L} {s : Node V R.L} {v : V} {pre : List ℕ} {d r : ℕ}
    (hr : r + 1 < R.L) (hv : R.C (c.τ + r + 1) ≠ v) (h : EndNode s c.τ v pre d (r + 1)) :
    EndNode s c.τ v pre d r := by
  have hc : c.τ + ((r + 1 : ℕ) : ZMod R.L) = c.τ + r + 1 := cast_succ_add _ _
  have hne : ∀ p, R.C p = v → dist c.τ p ≠ r + 1 := fun p hp h' => by
    apply hv; rw [← hc, ← dist_cast_eq hr h', hp]
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨by have := hne (lastOcc R v (c.τ - 1)) (C_lastOcc v _); omega, h2, h3⟩
  · refine Or.inr (Or.inl ⟨by have := hne (firstOcc R v c.τ) (C_firstOcc v _); omega, by omega,
      ?_, h4⟩)
    rw [h3, hc, lastOcc_of_ne hv, add_sub_cancel_right]
  · exact Or.inr (Or.inr ⟨by omega, h2, h3⟩)

lemma EndStage.advance {c c' : Config V R.L} {pre : List ℕ} {d r : ℕ} (H : EndStage c pre d (r + 1))
    {u : V} (hu : R.C (c.τ + (r : ZMod R.L) + 1) = u) (hτ : c'.τ = c.τ) (hds : c'.ds = c.ds)
    (hwv : c'.wv = some (u, R.C (c.τ + (r : ZMod R.L))))
    (hnode : ∀ v, v ≠ u → c'.node v = c.node v)
    (hT : u = R.C c.τ → (c'.node u).ph = .hend d (lastOcc R u (c.τ + r)) ∧
      (c'.node u).tok = true ∧ (c'.node u).log = pre)
    (hO : u ≠ R.C c.τ → (c'.node u).tok = false ∧ EndNode (c'.node u) c.τ u pre d r) :
    EndStage c' pre d r := by
  have hc : c.τ + ((r + 1 : ℕ) : ZMod R.L) = c.τ + r + 1 := cast_succ_add _ _
  have hr := H.r_lt
  refine ⟨by rw [hds]; exact H.ds_eq, by omega, by rw [hwv, hτ, hu], ?_, ?_, ?_, fun v hv => ?_⟩
  · rw [hτ]
    by_cases huT : u = R.C c.τ
    · rw [← huT]; exact (hT huT).1
    · rw [hnode _ (Ne.symm huT), H.hph, hc, lastOcc_of_ne (by rw [hu]; exact huT),
        add_sub_cancel_right]
  · rw [hτ]
    by_cases huT : u = R.C c.τ
    · rw [← huT]; exact (hT huT).2.1
    · rw [hnode _ (Ne.symm huT)]; exact H.htok
  · rw [hτ]
    by_cases huT : u = R.C c.τ
    · rw [← huT]; exact (hT huT).2.2
    · rw [hnode _ (Ne.symm huT)]; exact H.hlog
  · rw [hτ] at hv ⊢
    by_cases hvu : v = u
    · subst hvu; exact hO hv
    · rw [hnode v hvu]
      obtain ⟨h1, h2⟩ := H.others v hv
      exact ⟨h1, EndNode.step hr (by rw [hu]; exact Ne.symm hvu) h2⟩

/-- Reading a non-request pulse in the end stage: the `end` pulse (lines 27–30, 37–44). -/
theorem inv_recv_end {c : Config V R.L} (hC : Common c) {pre : List ℕ} {d r : ℕ}
    (H : EndStage c pre d r) {u x : V} (hen : Enabled R c (.recv u x))
    (hq : (c.node u).ph.isReq = false) : Inv (next R c (.recv u x)) := by
  obtain ⟨hu, hx⟩ := H.read hC hen hq
  have hmux : 0 < mult R u x := mult_pos_succ _ hu hx
  have hwv : c.wv = some (x, u) := by rw [H.wv, hx, hu]
  have hready : (c.node u).ph.isReady = false := by
    by_cases huT : u = R.C c.τ
    · rw [huT, H.hph]; rfl
    rcases (H.others u huT).2 with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨h1, -, -⟩
    · rw [h]; rfl
    · rw [h]; rfl
    · exfalso
      have := dist_firstOcc_le (u := u) c.τ (p := c.τ + r) hu
      rw [dist_add_natCast _ H.r_lt] at this; omega
  have htr := tokRecv_of_not_ready (R := R) (u := u) (x := x) hready
  have hτ := next_τ_of (c := c) htr
  have hds := next_ds_of (c := c) htr
  have hCm : Common (next R c (.recv u x)) :=
    common_recv hC hen (fun _ => hwv) (fun h => by rw [hq] at h; cases h)
      (fun _ _ h => by rw [hq] at h; cases h) (rot_of hC htr)
  refine ⟨hCm, ?_⟩
  have hnode : ∀ v, v ≠ u → (next R c (.recv u x)).node v = c.node v :=
    fun v hv => next_recv_node_ne _ _ hv
  have hα : lastOcc R u (c.τ + r) = c.τ + r := lastOcc_self hu
  by_cases huT : u = R.C c.τ
  · -- the token holder (line 29)
    have hph := H.hph; rw [← huT, hα] at hph
    have ho : (c.node u).o = c.τ := by rw [hC.rot u, huT, firstOcc_self rfl]
    by_cases hr0 : c.τ + (r : ZMod R.L) = c.τ
    · -- its own `end` pulse is back: the epoch is complete
      have hr : react R u (c.node u) x = ⟨{ c.node u with ph := .idle, log := (c.node u).log ++ [d] },
          false, none⟩ := by
        simp only [react, hph, ho, hr0, ite_true]
      have hT' : R.C (next R c (.recv u x)).τ = u := by rw [hτ, huT]
      have hr0' : r = 0 := by
        have := dist_add_natCast c.τ H.r_lt; rw [hr0, dist_self] at this; omega
      subst hr0'
      have hlogs : ∀ v, ((next R c (.recv u x)).node v).log = c.ds := by
        intro v; rw [H.ds_eq]
        by_cases hvu : v = u
        · subst hvu; rw [next_recv_node_self, hr]; simp [huT, H.hlog]
        · rw [hnode v hvu]
          rcases (H.others v (by rw [← huT]; exact hvu)).2 with ⟨h1, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨-, -, h⟩
          · exfalso; have := dist_eq_zero.1 (Nat.le_zero.1 h1)
            exact hvu (by rw [← C_lastOcc v (c.τ - 1), this, ← huT])
          · exfalso; have := dist_eq_zero.1 (Nat.le_zero.1 h1)
            exact hvu (by rw [← C_firstOcc v c.τ, this, ← huT])
          · exact h
      refine Or.inl ⟨fun v => by rw [hlogs, hds], fun v => ?_, Or.inl ⟨?_, ?_, fun v hv => ?_, ?_⟩⟩
      · by_cases hvu : v = u
        · subst hvu; rw [next_recv_node_self, hr]; trivial
        · rw [hnode v hvu]
          rcases (H.others v (by rw [← huT]; exact hvu)).2 with ⟨h1, -, -⟩ | ⟨h1, -, -, -⟩ | ⟨-, h, -⟩
          · exfalso; have := dist_eq_zero.1 (Nat.le_zero.1 h1)
            exact hvu (by rw [← C_lastOcc v (c.τ - 1), this, ← huT])
          · exfalso; have := dist_eq_zero.1 (Nat.le_zero.1 h1)
            exact hvu (by rw [← C_firstOcc v c.τ, this, ← huT])
          · exact h
      · rw [hT', next_recv_node_self, hr]; rw [huT]; exact H.htok
      · rw [hT', next_recv_node_self, hr]; rfl
      · rw [hT'] at hv; rw [hnode v hv]; exact (H.others v (by rw [← huT]; exact hv)).1
      · rw [next_recv_wv, hr]; simp [hq]
    · -- forward its `end` pulse (line 28)
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by
        rcases Nat.eq_zero_or_pos r with h | h
        · subst h; simp at hr0
        · omega⟩
      rw [cast_succ_add] at hph hr0 hu
      have hr : react R u (c.node u) x = ⟨{ c.node u with
          ph := .hend d (prevOcc R (c.τ + r' + 1)) }, false, some (R.C (c.τ + r' + 1 - 1))⟩ := by
        simp only [react, hph, ho, hr0, ite_false]
      refine Or.inr (Or.inr ⟨pre, d, r', H.advance hu hτ hds ?_ hnode (fun _ => ?_)
        (fun h => (h huT).elim)⟩)
      · rw [next_recv_wv, hr, add_sub_cancel_right]
      · rw [next_recv_node_self, hr, prevOcc_eq, hu, add_sub_cancel_right]
        exact ⟨rfl, by rw [huT]; exact H.htok, by rw [huT]; exact H.hlog⟩
  · obtain ⟨htk, hN⟩ := H.others u huT
    have hr0 : c.τ + (r : ZMod R.L) ≠ c.τ := fun h => huT (by rw [← hu, h])
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; simp at hr0
      · omega⟩
    have hrL := H.r_lt
    have hdα : dist c.τ (c.τ + ((r' + 1 : ℕ) : ZMod R.L)) = r' + 1 := dist_add_natCast _ hrL
    rw [cast_succ_add] at hu hdα hα
    have hoα : dist c.τ (firstOcc R u c.τ) ≤ r' + 1 := by
      rw [← hdα]; exact dist_firstOcc_le _ hu
    -- the new state of `u` after processing the `end` pulse at occurrence `α = τ + r' + 1`
    have hnew : ∀ (k : ℕ), r' + 1 ≤ dist c.τ (lastOcc R u (c.τ - 1)) →
        (∀ s : Node V R.L, s.ph = (if c.τ + r' + 1 = firstOcc R u c.τ then .idle else
          .fend (prevOcc R (c.τ + r' + 1))) → s.log = pre ++ [d] → EndNode s c.τ u pre d r') := by
      intro _ hlast s hs hlog
      by_cases hαo : c.τ + r' + 1 = firstOcc R u c.τ
      · rw [ite_eq_left hαo] at hs
        refine Or.inr (Or.inr ⟨by rw [← hαo, hdα]; omega, by rw [hs]; trivial, hlog⟩)
      · rw [ite_eq_right hαo] at hs
        refine Or.inr (Or.inl ⟨?_, by omega, by rw [hs, prevOcc_eq, hu, add_sub_cancel_right], hlog⟩)
        have : dist c.τ (firstOcc R u c.τ) ≠ r' + 1 := fun h => hαo (by
          rw [dist_cast_eq hrL h]; push_cast; ring)
        omega
    rcases hN with ⟨hl, hph, hlog⟩ | ⟨h1, h2, hph, hlog⟩ | ⟨hr, -, -⟩
    · -- line 37: the `end` pulse in the data phase; decode (lines 38–40)
      have hl' : lastOcc R u (c.τ - 1) = c.τ + r' + 1 := by
        apply dist_inj (a := c.τ); have := dist_le_lastOcc c.τ hu; omega
      have hpo : prevOcc R (c.node u).o = c.τ + r' + 1 := by
        rw [hC.rot u, prevOcc_firstOcc, hl']
      have ho : (c.node u).o = firstOcc R u c.τ := hC.rot u
      have hr : react R u (c.node u) x = ⟨{ c.node u with
          ph := if c.τ + r' + 1 = firstOcc R u c.τ then .idle else .fend (prevOcc R (c.τ + r' + 1))
          log := (c.node u).log ++ [d * occ R u / occ R u] }, false,
          some (R.C (c.τ + r' + 1 - 1))⟩ := by
        simp only [react, hph, ho, hmux, and_self, ite_true]; rw [← ho, hpo]
      refine Or.inr (Or.inr ⟨pre, d, r', H.advance hu hτ hds ?_ hnode (fun h => (huT h).elim)
        (fun _ => ⟨by rw [next_recv_node_self, hr]; exact htk, ?_⟩)⟩)
      · rw [next_recv_wv, hr, add_sub_cancel_right]
      · rw [next_recv_node_self, hr]
        exact hnew 0 (by rw [hl', hdα]) _ rfl (by
          simp [hlog, Nat.mul_div_cancel _ (occ_pos u)])
    · -- lines 42–43
      have hp : lastOcc R u (c.τ + ((r' + 1 : ℕ) : ZMod R.L)) = c.τ + r' + 1 := by
        rw [cast_succ_add]; exact hα
      rw [hp] at hph
      have ho : (c.node u).o = firstOcc R u c.τ := hC.rot u
      have hr : react R u (c.node u) x = ⟨{ c.node u with
          ph := if c.τ + r' + 1 = firstOcc R u c.τ then .idle else .fend (prevOcc R (c.τ + r' + 1)) },
          false, some (R.C (c.τ + r' + 1 - 1))⟩ := by
        simp only [react, hph, ho]
      refine Or.inr (Or.inr ⟨pre, d, r', H.advance hu hτ hds ?_ hnode (fun h => (huT h).elim)
        (fun _ => ⟨by rw [next_recv_node_self, hr]; exact htk, ?_⟩)⟩)
      · rw [next_recv_wv, hr, add_sub_cancel_right]
      · rw [next_recv_node_self, hr]
        exact hnew 0 (by omega) _ rfl hlog
    · exfalso; omega

/-! ### The invariant -/

theorem inv_recv {c : Config V R.L} (h : Inv c) {u x : V} (hen : Enabled R c (.recv u x)) :
    Inv (next R c (.recv u x)) := by
  by_cases hq : (c.node u).ph.isReq = true
  · exact inv_recv_req h hen hq
  · simp only [Bool.not_eq_true] at hq
    obtain ⟨hC, H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩⟩ := h
    · exact inv_recv_tok hC H hen hq
    · exact inv_recv_data hC H hen hq
    · exact inv_recv_end hC H hen hq

theorem inv_step {c : Config V R.L} (h : Inv c) {l : Label V} (hen : Enabled R c l) :
    Inv (next R c l) := by
  cases l with
  | push u a => exact inv_push h u hen
  | start u => exact inv_start h hen
  | recv u x => exact inv_recv h hen

/-- **Lemma 11 of [CCGS22] (safety part).** The invariant holds in every reachable configuration
of Algorithm 3. -/
theorem Reach.inv {τ₀ : ZMod R.L} {qs : V → List ℕ} (hqs : ∀ u, ∀ a ∈ qs u, 0 < a)
    {c : Config V R.L} (h : Reach R τ₀ qs c) : Inv c := by
  induction h with
  | refl => exact inv_init τ₀ hqs
  | tail _ hs ih => obtain ⟨l, hen, rfl⟩ := hs; exact inv_step ih hen

/-- **Lemma 11(2) of [CCGS22], single token holder.** At most one node has
`isTokenHolder = True`; it is the node at the token position `τ`. -/
theorem Inv.tok_unique {c : Config V R.L} (h : Inv c) {u : V} (hu : (c.node u).tok = true) :
    u = R.C c.τ := by
  by_contra hne
  rcases h.2 with H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩
  · rcases H.tok with ⟨-, -, h3, -⟩ | ⟨h1, -⟩
    · rw [h3 u hne] at hu; cases hu
    · rw [h1 u] at hu; cases hu
  · rw [(H.others u hne).1] at hu; cases hu
  · rw [(H.others u hne).1] at hu; cases hu

/-- Every node's log is the list of payloads of the epochs it completed. -/
theorem Inv.log_eq {c : Config V R.L} (h : Inv c) (u : V) :
    (c.node u).log = c.ds.take (c.node u).log.length := by
  rcases h.2 with H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩
  · rw [H.log u]; simp
  · rw [H.log_all u, H.ds_eq]; simp
  · rw [H.ds_eq]
    by_cases hu : u = R.C c.τ
    · rw [hu, H.hlog]; simp
    · rcases (H.others u hu).2 with ⟨-, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> simp

/-- **Lemma 11(3) of [CCGS22], global consistency.** Every node has decoded exactly the payloads
of the epochs it completed, which are the payloads dequeued by the successive token holders
(`ds`): its log is a prefix of `ds`. -/
theorem Inv.log_prefix {c : Config V R.L} (h : Inv c) (u : V) : (c.node u).log <+: c.ds := by
  rw [h.log_eq u]; exact List.take_prefix _ _

/-- **Challenge 1 of [CCGS22], Section 4.** Every node's occurrence `0` is its first occurrence
at or after the token position: the token always lies in segment `0` of every node. -/
theorem Inv.rot {c : Config V R.L} (h : Inv c) (u : V) : (c.node u).o = firstOcc R u c.τ :=
  h.1.rot u

end Podc.FullyDefective.RobbinsSim
