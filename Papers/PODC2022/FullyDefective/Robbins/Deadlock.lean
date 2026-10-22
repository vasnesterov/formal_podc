import Papers.PODC2022.FullyDefective.Robbins.Preservation

/-!
# Algorithm 3 of [CCGS22] never deadlocks

If no step of the network layer (`start` or `recv`) is enabled in a reachable configuration of
Algorithm 3, then all queues are empty, no pulse is in transit, every node is at line 1 and has
decoded the payloads of all epochs (`deadlock_free`). This is the safety half of the progress
statement Lemma 11(1): the algorithm can only stop in a quiescent configuration. (Fairness/progress
proper — every enabled step is eventually taken — is not modelled.)
-/

set_option linter.unusedSectionVars false

namespace Podc.FullyDefective.RobbinsSim

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {R : RobbinsCycle G}

/-- No step of the network layer is enabled (`push` steps belong to the environment). -/
def Stuck (c : Config V R.L) : Prop := ∀ l : Label V, (∀ u a, l ≠ .push u a) → ¬ Enabled R c l

lemma Stuck.recv {c : Config V R.L} (h : Stuck c) {u x : V} (hw : waits R u (c.node u) x) :
    c.net x u = 0 := by
  by_contra h'
  exact h (.recv u x) (by intro _ _ h; cases h) ⟨hw, Nat.pos_of_ne_zero h'⟩

lemma Stuck.start {c : Config V R.L} (h : Stuck c) {u : V} (hu : (c.node u).ph.isIdle = true) :
    (c.node u).q = [] := by
  by_contra h'
  exact h (.start u) (by intro _ _ h; cases h) ⟨hu, h'⟩

/-- The token/data/end pulse in transit is really in transit. -/
lemma net_pos_of_wv {c : Config V R.L} (hC : Common c) {x u : V} (h : c.wv = some (x, u)) :
    0 < c.net x u := by
  have h1 := hC.netEq x u; have h2 := hC.reqLe x u
  simp only [Config.wave, h, ite_true] at h1; omega

/-- In the token and data stages, the nodes that broadcast their `request` pulses form a set
closed under the links of the cycle, hence everybody has broadcast its `request` pulses as soon as
one node has; then nobody waits at line 3. -/
lemma all_started {c : Config V R.L} (hC : Common c) (hs : Stuck c) {K : ℕ}
    (hep : ∀ v, c.ep v = K) (hfend : ∀ v p, (c.node v).ph ≠ .fend p) {v₀ : V}
    (h₀ : (c.node v₀).ph.isIdle = false) :
    (∀ v, (c.node v).ph.isIdle = false) ∧ ∀ v need, (c.node v).ph ≠ .waitReq need := by
  have hsent : ∀ v, (c.node v).ph.isIdle = false → (c.node v).ph.sent = 1 := by
    intro v hv; have := hfend v; revert hv this
    cases (c.node v).ph <;> simp [Phase.isIdle, Phase.sent]
  have step : ∀ j : ZMod R.L, (c.node (R.C j)).ph.isIdle = false →
      (c.node (R.C (j + 1))).ph.isIdle = false := by
    intro j hj
    by_contra hj'
    simp only [Bool.not_eq_false] at hj'
    have hid : (c.node (R.C (j + 1))).ph = .idle := by
      revert hj'; cases (c.node (R.C (j + 1))).ph <;> simp [Phase.isIdle]
    have hm := mult_pos_of j
    have h1 := hC.netEq (R.C j) (R.C (j + 1))
    simp only [rcv, snt, hep, hid, Phase.rIn, hsent _ hj] at h1
    have h2 := hs.recv (u := R.C (j + 1)) (x := R.C j) (by rw [waits, hid]; exact hm)
    rw [h2, mul_add, mul_one] at h1; omega
  have hall : ∀ v, (c.node v).ph.isIdle = false := by
    obtain ⟨j₀, rfl⟩ := R.surj v₀
    have : ∀ n : ℕ, (c.node (R.C (j₀ + n))).ph.isIdle = false := by
      intro n; induction n with
      | zero => simpa using h₀
      | succ n ih => rw [Nat.cast_succ, ← add_assoc]; exact step _ ih
    intro v; obtain ⟨j, rfl⟩ := R.surj v
    simpa using this (j - j₀).val
  refine ⟨hall, fun v need hv => ?_⟩
  obtain ⟨y, hy⟩ := hC.needPos v need hv
  have hle := hC.needLe v need hv y
  have h1 := hC.netEq y v
  simp only [rcv, snt, hep, hv, Phase.rIn, hsent _ (hall y)] at h1
  have h2 := hs.recv (u := v) (x := y) (by rw [waits, hv]; exact hy)
  rw [h2, mul_add, mul_one] at h1; omega

/-- **Algorithm 3 never deadlocks.** In a reachable configuration where no step of the network
layer is enabled, every node is at line 1 with an empty queue and has decoded all the payloads
sent so far, and no pulse is in transit. -/
theorem Inv.deadlock_free {c : Config V R.L} (h : Inv c) (hs : Stuck c) :
    (∀ u, (c.node u).ph = .idle ∧ (c.node u).q = [] ∧ (c.node u).log = c.ds) ∧
      ∀ x y, c.net x y = 0 := by
  obtain ⟨hC, H | ⟨pre, d, s, H⟩ | ⟨pre, d, r, H⟩⟩ := h
  · have hep : ∀ v, c.ep v = c.ds.length := fun v => by simp [Config.ep, H.log v]
    have hfend : ∀ v p, (c.node v).ph ≠ .fend p := fun v p hp => by
      have := H.isTok v; rw [hp] at this; exact this
    by_cases hidle : ∀ v, (c.node v).ph.isIdle = true
    · have hid : ∀ v, (c.node v).ph = .idle := fun v => by
        have := hidle v; revert this; cases (c.node v).ph <;> simp [Phase.isIdle]
      have hwv : c.wv = none := by
        rcases H.tok with ⟨-, -, -, h⟩ | ⟨-, -, h⟩
        · exact h
        · rw [hid] at h; cases h
      refine ⟨fun u => ⟨hid u, hs.start (hidle u), H.log u⟩, fun x y => ?_⟩
      have h1 := hC.netEq x y
      simp only [rcv, snt, hep, hid, Phase.rIn, Phase.sent, Config.wave, hwv] at h1
      simpa using h1
    · push Not at hidle
      obtain ⟨v₀, h₀⟩ := hidle
      obtain ⟨hall, hnw⟩ := all_started hC hs hep hfend (by simpa using h₀)
      have hready : ∀ v, (c.node v).ph = .ready := fun v => by
        have h1 := H.isTok v; have h2 := hall v; have h3 := hnw v; revert h1 h2 h3
        cases (c.node v).ph <;> simp [Phase.IsTok, Phase.isIdle]
      exfalso
      rcases H.tok with ⟨-, h2, -, -⟩ | ⟨-, h, -⟩
      · rw [hready] at h2; cases h2
      · have := hs.recv (u := R.C (c.τ - 1)) (x := R.C c.τ) (by
          rw [waits, hready]; right
          exact mult_pos_succ (c.τ - 1) rfl (by rw [sub_add_cancel]))
        have := net_pos_of_wv hC h; omega
  · exfalso
    have hep : ∀ v, c.ep v = pre.length := fun v => by simp [Config.ep, H.log_all v]
    have hfend : ∀ v p, (c.node v).ph ≠ .fend p := fun v p hp => by
      by_cases hv : v = R.C c.τ
      · rw [hv, H.hph] at hp; cases hp
      · rcases (H.others v hv).2.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hp] at h
        · exact h
        · cases h
    obtain ⟨-, hnw⟩ := all_started hC hs hep hfend (v₀ := R.C c.τ) (by rw [H.hph]; rfl)
    have hpos := net_pos_of_wv hC H.wv
    set u := R.C (c.τ + s + 1)
    have hp : firstOcc R u (c.τ + s + 1) = c.τ + s + 1 := firstOcc_self rfl
    suffices waits R u (c.node u) (R.C (c.τ + s)) by have := hs.recv this; omega
    by_cases huT : u = R.C c.τ
    · have := H.hph; rw [← huT, hp] at this; simp only [waits, this, add_sub_cancel_right]
    · rcases (H.others u huT).2.2 with ⟨-, hIs⟩ | ⟨-, hph⟩
      · have hm : 0 < mult R (R.C (c.τ + s)) u := mult_pos_of _
        have := hnw u; revert hIs this
        rw [waits]; cases (c.node u).ph <;> simp [Phase.IsTok, hm]
      · rw [hp] at hph; simp only [waits, hph, add_sub_cancel_right, true_or]
  · exfalso
    have hpos := net_pos_of_wv hC H.wv
    set u := R.C (c.τ + r)
    have hl : lastOcc R u (c.τ + r) = c.τ + r := lastOcc_self rfl
    suffices waits R u (c.node u) (R.C (c.τ + r + 1)) by have := hs.recv this; omega
    by_cases huT : u = R.C c.τ
    · have := H.hph; rw [← huT, hl] at this; rw [waits, this]
    · rcases (H.others u huT).2 with ⟨-, hph, -⟩ | ⟨-, -, hph, -⟩ | ⟨h1, -, -⟩
      · rw [waits, hph]; right; exact ⟨(hC.rot u).symm, mult_pos_of _⟩
      · rw [hl] at hph; rw [waits, hph]
      · have := dist_firstOcc_le (u := u) c.τ (p := c.τ + r) rfl
        rw [dist_add_natCast _ H.r_lt] at this; omega

/-- **Deadlock-freedom of Algorithm 3**, for reachable configurations. -/
theorem Reach.deadlock_free {τ₀ : ZMod R.L} {qs : V → List ℕ} (hqs : ∀ u, ∀ a ∈ qs u, 0 < a)
    {c : Config V R.L} (h : Reach R τ₀ qs c) (hs : Stuck c) :
    (∀ u, (c.node u).ph = .idle ∧ (c.node u).q = [] ∧ (c.node u).log = c.ds) ∧
      ∀ x y, c.net x y = 0 :=
  (h.inv hqs).deadlock_free hs

end Podc.FullyDefective.RobbinsSim
