import Mathlib

/-!
# Stability of simple discrete-time queues

Two single-server discrete-time queues, modelled with Mathlib's `PMF`:

* `slot a s`: in each slot a packet arrives with probability `a` and, independently, the link has a
  transmission opportunity with probability `s`; it then sends one packet if its queue (after the
  arrival) is nonempty. `slot_stable`: the queue is stable (bounded expected length) if `a < s`.
* the TDMA frame `slot a 0` followed by `slot a 1` (a slot without and a slot with a sure transmission
  opportunity). `tdma_stable`: stable if `a < 1/2`.

The proof is a Foster–Lyapunov argument with the exponential Lyapunov function `V j = z ^ j`, `z > 1`
(`stable_of_drift`): a geometric drift `E[V(Q') | Q = j] ≤ ρ V j` for `j ≥ 1`, `ρ < 1`, bounds
`E[V(Q_t)]` uniformly in `t`, and `j ≤ z ^ j / (z - 1)` bounds the expected queue length.
-/

open scoped ENNReal NNReal

namespace Podc.WirelessPacketScheduling.Queue

/-- A biased coin: `true` with probability `p` (same as the deprecated `PMF.bernoulli`). -/
noncomputable def coin (p : ℝ≥0) (h : p ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun b => ((cond b p (1 - p) : ℝ≥0) : ℝ≥0∞)) (by
    simp only [Fintype.univ_bool, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
      Finset.sum_insert, Bool.cond_true, Finset.sum_singleton, Bool.cond_false]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le h, ENNReal.coe_one])

/-- One time slot of a queue: a packet arrives with probability `a`; independently, with probability
`s` the link has a transmission opportunity and then sends one packet if its queue (after the
arrival) is nonempty. -/
noncomputable def slot (a s : ℝ≥0) (ha : a ≤ 1) (hs : s ≤ 1) (q : ℕ) : PMF ℕ :=
  (coin a ha).bind fun A => (coin s hs).bind fun S =>
    PMF.pure (if S && decide (0 < q + A.toNat) then q + A.toNat - 1 else q + A.toNat)

/-- Law of the queue length after `t` steps of the kernel `K`, started empty. -/
noncomputable def law (K : ℕ → PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | t + 1 => (law K t).bind K

/-- Expected queue length. -/
noncomputable def meanQ (p : PMF ℕ) : ℝ≥0∞ := ∑' j, p j * j

/-- Stability: the expected queue length is bounded uniformly in time. -/
def Stable (K : ℕ → PMF ℕ) : Prop := ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ t, meanQ (law K t) ≤ B

/-- Expectation of a nonnegative function under a `PMF`. -/
noncomputable def ev {α : Type*} (p : PMF α) (V : α → ℝ≥0∞) : ℝ≥0∞ := ∑' k, p k * V k

lemma ev_pure {α : Type*} (x : α) (V : α → ℝ≥0∞) : ev (PMF.pure x) V = V x := by
  classical
  simp [ev, PMF.pure_apply]

lemma ev_bind {α β : Type*} (p : PMF α) (f : α → PMF β) (V : β → ℝ≥0∞) :
    ev (p.bind f) V = ev p fun x => ev (f x) V := by
  simp only [ev, PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

lemma ev_coin (p : ℝ≥0) (h : p ≤ 1) (g : Bool → ℝ≥0∞) :
    ev (coin p h) g = (1 - p : ℝ≥0) * g false + p * g true := by
  simp [ev, coin, add_comm]

/-- Expected value of `W` after one slot started at `q`. -/
lemma ev_slot (a s : ℝ≥0) (ha : a ≤ 1) (hs : s ≤ 1) (q : ℕ) (W : ℕ → ℝ≥0∞) :
    ev (slot a s ha hs q) W = (1 - a : ℝ≥0) * ((1 - s : ℝ≥0) * W q + s * W (q - 1)) +
      a * ((1 - s : ℝ≥0) * W (q + 1) + s * W q) := by
  rcases q with _ | q <;> simp [slot, ev_bind, ev_coin, ev_pure]

-- CSLib candidate
/-- Foster–Lyapunov criterion with `V j = z ^ j`: a geometric drift for nonempty queues implies
stability. -/
theorem stable_of_drift (K : ℕ → PMF ℕ) (z ρ : ℝ≥0) (hz : 1 < z) (hρ : ρ < 1)
    (hdrift : ∀ m, ev (K (m + 1)) (fun k => (z : ℝ≥0∞) ^ k) ≤ ρ * (z : ℝ≥0∞) ^ (m + 1))
    (h0 : ev (K 0) (fun k => (z : ℝ≥0∞) ^ k) ≠ ⊤) : Stable K := by
  set V : ℕ → ℝ≥0∞ := fun k => (z : ℝ≥0∞) ^ k with hV
  set C := ev (K 0) V
  have hd : ∀ j, ev (K j) V ≤ ρ * V j + C := fun j => by
    rcases j with _ | m
    · exact le_add_self
    · exact (hdrift m).trans le_self_add
  -- one-step bound on `M t = E[V(Q_t)]`
  have hstep : ∀ t, ev (law K (t + 1)) V ≤ ρ * ev (law K t) V + C := fun t => by
    calc ev (law K (t + 1)) V = ∑' j, law K t j * ev (K j) V := by
          show ev ((law K t).bind K) V = _; rw [ev_bind]; rfl
      _ ≤ ∑' j, law K t j * (ρ * V j + C) := by gcongr with j; exact hd j
      _ = ρ * ev (law K t) V + C := by
        simp only [mul_add, ENNReal.tsum_add, ev, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          ← ENNReal.tsum_mul_left]
        congr 1; congr 1; ext j; ring
  have h1ρ : (1 : ℝ≥0∞) - ρ ≠ 0 := by
    exact (tsub_pos_of_lt (by exact_mod_cast hρ)).ne'
  set X := C / (1 - ρ)
  have hX : X ≠ ⊤ := ENNReal.div_ne_top h0 h1ρ
  have hXeq : ρ * X + C = X := by
    conv_lhs => rw [← ENNReal.mul_div_cancel h1ρ (by simp) (b := C)]
    rw [← add_mul, add_tsub_cancel_of_le (by exact_mod_cast hρ.le), one_mul]
  have hM : ∀ t, ev (law K t) V ≤ 1 + X := fun t => by
    induction t with
    | zero => simp [law, ev_pure, hV]
    | succ t ih =>
      calc _ ≤ ρ * ev (law K t) V + C := hstep t
        _ ≤ ρ * (1 + X) + C := by gcongr
        _ = ρ + X := by rw [mul_add, mul_one, add_assoc, hXeq]
        _ ≤ 1 + X := by gcongr; exact_mod_cast hρ.le
  -- `j ≤ c * z ^ j` with `c = (z - 1)⁻¹`
  set c : ℝ≥0 := (z - 1)⁻¹
  have hj : ∀ j : ℕ, (j : ℝ≥0∞) ≤ c * V j := fun j => by
    have hz' : (0 : ℝ) < (z : ℝ) - 1 := by have : (1 : ℝ) < z := hz; linarith
    have hb := one_add_mul_le_pow (a := (z : ℝ) - 1) (by linarith) j
    have : (j : ℝ≥0) ≤ c * z ^ j := by
      rw [← NNReal.coe_le_coe]
      simp only [c, NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow,
        NNReal.coe_sub hz.le, NNReal.coe_one]
      rw [inv_mul_eq_div, le_div_iff₀ hz']
      simp only [add_sub_cancel] at hb
      linarith
    simpa [hV] using (ENNReal.coe_le_coe.mpr this)
  refine ⟨c * (1 + X), ENNReal.mul_ne_top (by simp) (by simpa using hX), fun t => ?_⟩
  calc meanQ (law K t) ≤ ∑' j, law K t j * (c * V j) := by
        unfold meanQ; gcongr with j; exact hj j
    _ = c * ev (law K t) V := by
        rw [ev, ← ENNReal.tsum_mul_left]; congr 1; ext j; ring
    _ ≤ c * (1 + X) := by gcongr; exact hM t

/-- Expected `z ^ (Q')` after one slot from a nonempty queue. -/
lemma ev_slot_succ (a s : ℝ≥0) (ha : a ≤ 1) (hs : s ≤ 1) (z : ℝ≥0) (m : ℕ) :
    ev (slot a s ha hs (m + 1)) (fun k => (z : ℝ≥0∞) ^ k) =
      ((z ^ m * ((1 - a) * ((1 - s) * z + s) + a * ((1 - s) * z ^ 2 + s * z)) : ℝ≥0) : ℝ≥0∞) := by
  rw [ev_slot]
  simp only [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_pow, Nat.add_sub_cancel]
  ring

lemma drift_eq (z ψ : ℝ≥0) (hz0 : z ≠ 0) (m : ℕ) :
    ((z ^ m * ψ : ℝ≥0) : ℝ≥0∞) = ((ψ / z : ℝ≥0) : ℝ≥0∞) * (z : ℝ≥0∞) ^ (m + 1) := by
  rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_inj]
  field_simp
  ring

/-- **Stability of a Bernoulli queue.** With i.i.d. Bernoulli(`a`) arrivals and i.i.d.
Bernoulli(`s`) transmission opportunities, the queue is stable whenever `a < s`. -/
theorem slot_stable (a s : ℝ≥0) (ha : a ≤ 1) (hs : s ≤ 1) (h : a < s) :
    Stable (slot a s ha hs) := by
  set z : ℝ≥0 := 1 + (s - a)
  set ψ : ℝ≥0 := (1 - a) * ((1 - s) * z + s) + a * ((1 - s) * z ^ 2 + s * z)
  have hz : 1 < z := lt_add_of_pos_right _ (tsub_pos_of_lt h)
  have hz0 : z ≠ 0 := (zero_lt_one.trans hz).ne'
  have hψ : ψ < z := by
    rw [← NNReal.coe_lt_coe]
    simp only [ψ, z, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_one,
      NNReal.coe_sub ha, NNReal.coe_sub hs, NNReal.coe_sub h.le]
    have h' : (a : ℝ) < s := h
    have ha0 : (0 : ℝ) ≤ a := a.2
    have hs1 : (s : ℝ) ≤ 1 := hs
    nlinarith [mul_pos (sub_pos.2 h') (sub_pos.2 h'), mul_nonneg ha0 (sub_nonneg.2 hs1),
      mul_pos (mul_pos (sub_pos.2 h') (sub_pos.2 h')) (sub_pos.2 (h'.trans_le hs1))]
  refine stable_of_drift _ z (ψ / z) hz ((div_lt_one (pos_iff_ne_zero.2 hz0)).2 hψ)
    (fun m => ?_) ?_
  · rw [ev_slot_succ]; exact (drift_eq z ψ hz0 m).le
  · rw [ev_slot]; finiteness

/-- **Stability of the TDMA frame.** A frame consisting of a slot without and a slot with a sure
transmission opportunity (Bernoulli(`a`) arrivals in each slot) is stable whenever `a < 1/2`. -/
theorem tdma_stable (a : ℝ≥0) (h : a < 1 / 2) :
    Stable (fun q => (slot a 0 (h.le.trans (by norm_num)) zero_le_one q).bind
      (slot a 1 (h.le.trans (by norm_num)) le_rfl)) := by
  have ha : a ≤ 1 := h.le.trans (by norm_num)
  set z : ℝ≥0 := 2 - 2 * a
  set ψ : ℝ≥0 := ((1 - a) + a * z) ^ 2
  have h2a : 2 * a ≤ 2 := by
    have : 2 * a < 2 * (1 / 2) := by gcongr
    norm_num at this; exact this.le.trans one_le_two
  have hz : 1 < z := by
    rw [← NNReal.coe_lt_coe]
    simp only [z, NNReal.coe_sub h2a, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one]
    have : (a : ℝ) < 1 / 2 := h
    linarith
  have hz0 : z ≠ 0 := (zero_lt_one.trans hz).ne'
  have hψ : ψ < z := by
    rw [← NNReal.coe_lt_coe]
    simp only [ψ, z, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_one,
      NNReal.coe_sub ha, NNReal.coe_sub h2a, NNReal.coe_ofNat]
    have h' : (a : ℝ) < 1 / 2 := h
    have ha0 : (0 : ℝ) ≤ a := a.2
    have h1 : (0 : ℝ) < 1 - a := by linarith
    have h2 : (0 : ℝ) < (1 - 2 * a) ^ 2 := pow_pos (by linarith) 2
    nlinarith [mul_pos (mul_pos h1 h2) (by linarith : (0 : ℝ) < 1 + a)]
  refine stable_of_drift _ z (ψ / z) hz ((div_lt_one (pos_iff_ne_zero.2 hz0)).2 hψ)
    (fun m => ?_) ?_
  · rw [ev_bind, ev_slot]
    simp only [ev_slot, ENNReal.coe_zero, ENNReal.coe_one, tsub_zero, tsub_self, zero_mul,
      one_mul, add_zero, zero_add, Nat.add_sub_cancel]
    calc _ = ((z ^ m * ψ : ℝ≥0) : ℝ≥0∞) := by
          simp only [ψ, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_add]; ring
      _ ≤ _ := (drift_eq z ψ hz0 m).le
  · rw [ev_bind, ev_slot]; simp only [ev_slot]; finiteness

end Podc.WirelessPacketScheduling.Queue
