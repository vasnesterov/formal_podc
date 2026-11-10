import Papers.PODC2010.KShotRadioBroadcast.Lines

/-!
# Algorithm *Oblivious k-Shot* and Lemma 4.1 (Section 4 of the paper)

Nodes are `Fin n` (0-based labels, `n ≤ p²`; label `i` is the point `⟨i div p, i mod p⟩`).
The algorithm interleaves
* *Line-Transmit*: stages `a = 0, …, p` (cyclically), each made of the `p` steps
  `b = 0, …, p - 1` with transmission set `L_{a,b}`;
* *Round-Robin*: slots `0, …, p² - 1` (cyclically), slot `m` with transmission set `{m}`
  (empty if `m ≥ n`),

as follows: one Line-Transmit step, then `K = ⌈p / (k - 2)⌉` Round-Robin steps, and so on.
Step `t ≥ 1` is a Line-Transmit step iff `(t - 1) mod (K + 1) = 0`; a *stage* is a block of
`S = p (K + 1)` consecutive steps (stage `g` = steps `g S + 1, …, (g + 1) S`), during which
Line-Transmit runs through all lines of direction `g mod (p + 1)`.

Main results: Lemma 4.1 (`lemma_4_1`, with a time bound in `exists_lone_transmission`) and the
three schedule properties used by the progress argument (`lineRR_appears`,
`lineRR_common_le_one`).
-/

namespace Podc.KShotRadioBroadcast

open Finset

/-- The Line-Transmit transmission set `L_{a,b}` (restricted to the existing labels). -/
def lineSet (n p a b : ℕ) : Finset (Fin n) := univ.filter fun v => OnLine p a b v.val

/-- The Round-Robin transmission set of the `m`-th Round-Robin step: the node with label
`m mod p²` (empty if there is no such node). -/
def rrSet (n p m : ℕ) : Finset (Fin n) := univ.filter fun v => v.val = m % (p * p)

/-- The schedule obtained by multiplexing one Line-Transmit step with `K` Round-Robin steps. -/
def lineRRSchedule (n p K : ℕ) : Schedule (Fin n) := fun t =>
  if (t - 1) % (K + 1) = 0 then
    lineSet n p ((t - 1) / (K + 1) / p % (p + 1)) ((t - 1) / (K + 1) % p)
  else rrSet n p ((t - 1) / (K + 1) * K + ((t - 1) % (K + 1) - 1))

/-- `K = ⌈p / (k - 2)⌉`, the number of Round-Robin steps after each Line-Transmit step. -/
def numRR (p k : ℕ) : ℕ := (p + k - 3) / (k - 2)

/-- Algorithm *Oblivious k-Shot* (Algorithm 3 of the paper), for `n` nodes and the prime `p`. -/
def obliviousKShot (n p k : ℕ) : Schedule (Fin n) := lineRRSchedule n p (numRR p k)

theorem one_le_numRR {p k : ℕ} (hp : 0 < p) (hk : 3 ≤ k) : 1 ≤ numRR p k := by
  unfold numRR
  rw [Nat.le_div_iff_mul_le (by omega)]; omega

theorem le_mul_numRR {p k : ℕ} (hk : 3 ≤ k) : p ≤ (k - 2) * numRR p k := by
  unfold numRR
  have h1 := Nat.div_add_mod (p + k - 3) (k - 2)
  have h2 := Nat.mod_lt (p + k - 3) (show 0 < k - 2 by omega)
  omega

theorem numRR_le {p k : ℕ} (hk : 3 ≤ k) : numRR p k ≤ p := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  unfold numRR
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  rw [show j + 3 - 2 = j + 1 by omega, show p + (j + 3) - 3 = p + j by omega]
  have : p ≤ (j + 1) * p := Nat.le_mul_of_pos_left p (by omega)
  omega

section schedule

variable {n p K : ℕ}

theorem rrSet_eq_singleton {m : ℕ} {v : Fin n} (hv : v.val = m % (p * p)) :
    rrSet n p m = {v} := by
  ext u
  simp only [rrSet, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro h; exact Fin.ext (h.trans hv.symm)
  · rintro rfl; exact hv

theorem eq_of_mem_rrSet {m : ℕ} {u v : Fin n} (hu : u ∈ rrSet n p m) (hv : v ∈ rrSet n p m) :
    u = v := by
  simp only [rrSet, mem_filter, mem_univ, true_and] at hu hv
  exact Fin.ext (hu.trans hv.symm)

theorem lineRR_of_line {t : ℕ} (h : (t - 1) % (K + 1) = 0) :
    lineRRSchedule n p K t =
      lineSet n p ((t - 1) / (K + 1) / p % (p + 1)) ((t - 1) / (K + 1) % p) := by
  simp [lineRRSchedule, h]

theorem lineRR_of_rr {t : ℕ} (h : (t - 1) % (K + 1) ≠ 0) :
    lineRRSchedule n p K t = rrSet n p ((t - 1) / (K + 1) * K + ((t - 1) % (K + 1) - 1)) := by
  simp [lineRRSchedule, h]

/-- At a Round-Robin step, a node that appears transmits alone. -/
theorem lineRR_eq_singleton_of_rr {t : ℕ} {v : Fin n} (h : (t - 1) % (K + 1) ≠ 0)
    (hv : v ∈ lineRRSchedule n p K t) : lineRRSchedule n p K t = {v} := by
  rw [lineRR_of_rr h] at hv ⊢
  have := hv
  simp only [rrSet, mem_filter, mem_univ, true_and] at this
  exact rrSet_eq_singleton this

/-- The stage of step `t` is `(t - 1) / (K + 1) / p`. -/
theorem stage_eq (t : ℕ) : (t - 1) / (p * (K + 1)) = (t - 1) / (K + 1) / p := by
  rw [Nat.div_div_eq_div_mul, mul_comm]

/-- Two Line-Transmit steps with the same Line-Transmit index are equal. -/
theorem eq_of_line_index {t t' : ℕ} (ht : 0 < t) (ht' : 0 < t') (h : (t - 1) % (K + 1) = 0)
    (h' : (t' - 1) % (K + 1) = 0) (hq : (t - 1) / (K + 1) = (t' - 1) / (K + 1)) : t = t' := by
  have e1 := Nat.div_add_mod (t - 1) (K + 1)
  have e2 := Nat.div_add_mod (t' - 1) (K + 1)
  rw [h, hq] at e1; rw [h'] at e2
  omega

/-- A node appears in at most one Line-Transmit step of each stage. -/
theorem line_step_unique_in_stage (hp : 0 < p) {t t' : ℕ} {v : Fin n} (ht : 0 < t) (ht' : 0 < t')
    (h : (t - 1) % (K + 1) = 0) (h' : (t' - 1) % (K + 1) = 0)
    (hG : (t - 1) / (K + 1) / p = (t' - 1) / (K + 1) / p)
    (hv : v ∈ lineRRSchedule n p K t) (hv' : v ∈ lineRRSchedule n p K t') : t = t' := by
  rw [lineRR_of_line h] at hv; rw [lineRR_of_line h'] at hv'
  simp only [lineSet, mem_filter, mem_univ, true_and] at hv hv'
  rw [hG] at hv
  have hb := onLine_unique (Nat.mod_lt _ hp) (Nat.mod_lt _ hp) hv hv'
  apply eq_of_line_index ht ht' h h'
  rw [← Nat.div_add_mod ((t - 1) / (K + 1)) p, ← Nat.div_add_mod ((t' - 1) / (K + 1)) p, hG, hb]

/-- Every node appears (in a Line-Transmit step) in every stage. -/
theorem lineRR_appears (hp : 0 < p) (G : ℕ) (v : Fin n) :
    ∃ t, G * (p * (K + 1)) < t ∧ t ≤ (G + 1) * (p * (K + 1)) ∧ v ∈ lineRRSchedule n p K t := by
  set b := lineOffset p (G % (p + 1)) v.val with hb
  have hbp : b < p := lineOffset_lt hp _ _
  refine ⟨(G * p + b) * (K + 1) + 1, ?_, ?_, ?_⟩
  · have : G * (p * (K + 1)) = G * p * (K + 1) := by ring
    rw [this]; have := Nat.mul_le_mul_right (K + 1) (Nat.le_add_right (G * p) b); omega
  · have : (G + 1) * (p * (K + 1)) = (G * p + p) * (K + 1) := by ring
    rw [this]
    have := Nat.mul_le_mul_right (K + 1) (show G * p + b + 1 ≤ G * p + p by omega)
    rw [add_mul (G * p + b) 1, one_mul] at this
    omega
  · have h1 : ((G * p + b) * (K + 1) + 1 - 1) = (G * p + b) * (K + 1) := by omega
    rw [lineRR_of_line (by rw [h1]; exact Nat.mul_mod_left _ _), h1,
      Nat.mul_div_cancel _ (Nat.succ_pos K)]
    have h2 : (G * p + b) / p = G := by
      rw [mul_comm G p, Nat.mul_add_div hp, Nat.div_eq_of_lt hbp, add_zero]
    have h3 : (G * p + b) % p = b := by
      rw [mul_comm G p, Nat.mul_add_mod, Nat.mod_eq_of_lt hbp]
    rw [h2, h3]
    simp only [lineSet, mem_filter, mem_univ, true_and]
    exact onLine_lineOffset hp _ _

/-- Two distinct nodes appear together in at most one step of any window of `p + 1`
consecutive stages. -/
theorem lineRR_common_le_one (hp : p.Prime) (hn : n ≤ p * p) {t t' : ℕ} {u v : Fin n}
    (ht : 0 < t) (htt : t < t')
    (hstage : (t' - 1) / (p * (K + 1)) ≤ (t - 1) / (p * (K + 1)) + p)
    (hu : u ∈ lineRRSchedule n p K t) (hv : v ∈ lineRRSchedule n p K t)
    (hu' : u ∈ lineRRSchedule n p K t') (hv' : v ∈ lineRRSchedule n p K t') : u = v := by
  have hp0 := hp.pos
  by_cases hj : (t - 1) % (K + 1) = 0
  · by_cases hj' : (t' - 1) % (K + 1) = 0
    · rw [stage_eq, stage_eq] at hstage
      set G := (t - 1) / (K + 1) / p with hG
      set G' := (t' - 1) / (K + 1) / p with hG'
      have hGG : G ≤ G' := Nat.div_le_div_right (Nat.div_le_div_right (by omega))
      rcases Nat.eq_or_lt_of_le hGG with heq | hlt
      · exact absurd (line_step_unique_in_stage hp0 ht (by omega) hj hj' heq hu hu')
          (Nat.ne_of_lt htt)
      · have hdir : G % (p + 1) ≠ G' % (p + 1) := by
          intro hmod
          have h1 : (G' - G) % (p + 1) = 0 := Nat.sub_mod_eq_zero_of_mod_eq hmod.symm
          have h2 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h1)
          omega
        rw [lineRR_of_line hj] at hu hv; rw [lineRR_of_line hj'] at hu' hv'
        simp only [lineSet, mem_filter, mem_univ, true_and] at hu hv hu' hv'
        exact Fin.ext (eq_of_onLine_two_dirs hp (Nat.lt_succ_iff.1 (Nat.mod_lt _ (by omega)))
          (Nat.lt_succ_iff.1 (Nat.mod_lt _ (by omega))) hdir (by omega) (by omega) hu hv hu' hv')
    · rw [lineRR_of_rr hj'] at hu' hv'
      exact eq_of_mem_rrSet hu' hv'
  · rw [lineRR_of_rr hj] at hu hv
    exact eq_of_mem_rrSet hu hv

/-- Every residue modulo `N > 0` occurs among `N` consecutive numbers. -/
theorem exists_mod_eq {N : ℕ} (hN : 0 < N) (A x : ℕ) (hx : x < N) :
    ∃ m, A ≤ m ∧ m < A + N ∧ m % N = x := by
  refine ⟨A + (x + N - A % N) % N, by omega, by have := Nat.mod_lt (x + N - A % N) hN; omega, ?_⟩
  rw [Nat.add_mod_mod]
  have h1 := Nat.div_add_mod A N
  have h2 := Nat.mod_lt A hN
  have : A + (x + N - A % N) = x + N * (A / N + 1) := by
    rw [Nat.mul_add, mul_one]; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

/-- **Lemma 4.1 (validity), with a time bound.** Let `c` be such that `c K ≥ p` and `c + 2 ≤ k`.
A node `v` that received the message at step `r` transmits alone (transmission set `{v}`) at one
of its `k` transmission steps, and this happens at the latest at the end of stage `r / S + c`
(where `S = p (K + 1)` is the length of a stage). -/
theorem exists_lone_transmission (hpos : 0 < p) (hn : n ≤ p * p) (hK : 1 ≤ K) {k c : ℕ}
    (hc : p ≤ c * K) (hck : c + 2 ≤ k) (v : Fin n) (r : ℕ) :
    ∃ t, TransmitsAt (lineRRSchedule n p K) k r v t ∧ lineRRSchedule n p K t = {v} ∧
      t ≤ (r / (p * (K + 1)) + c + 1) * (p * (K + 1)) := by
  classical
  set σ := lineRRSchedule n p K with hσ
  set S := p * (K + 1) with hS
  have hS0 : 0 < S := Nat.mul_pos hpos (Nat.succ_pos K)
  set g := r / S with hg
  have hrg : r < (g + 1) * S := by
    have := Nat.lt_div_mul_add (a := r) hS0
    rw [hg]; nlinarith
  -- a Round-Robin step of `v` in stages `g + 1, …, g + c`
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_mod_eq (Nat.mul_pos hpos hpos) ((g + 1) * p * K) v.val
    (lt_of_lt_of_le v.isLt hn)
  have hmK1 : (g + 1) * p ≤ m / K := by
    rw [Nat.le_div_iff_mul_le (by omega)]; exact hm1
  have hmK2 : m / K < (g + c + 1) * p := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : (g + c + 1) * p * K = (g + 1) * p * K + p * (c * K) := by ring
    have := Nat.mul_le_mul_left p hc
    nlinarith
  set ts := m / K * (K + 1) + m % K + 2 with hts
  have hmodK := Nat.mod_lt m (show 0 < K by omega)
  have ets : ts - 1 = m / K * (K + 1) + (m % K + 1) := by omega
  have ets1 : (ts - 1) % (K + 1) = m % K + 1 := by
    rw [ets, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have ets2 : (ts - 1) / (K + 1) = m / K := by
    rw [ets, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.succ_pos K), Nat.div_eq_of_lt (by omega),
      zero_add]
  have hσts : σ ts = {v} := by
    rw [hσ, lineRR_of_rr (by omega), ets1, ets2, Nat.add_sub_cancel]
    apply rrSet_eq_singleton
    rw [Nat.div_add_mod' m K, hm3]
  have hrts : r < ts := by
    have : (g + 1) * S ≤ m / K * (K + 1) := by
      rw [hS, show (g + 1) * (p * (K + 1)) = (g + 1) * p * (K + 1) by ring]
      exact Nat.mul_le_mul_right _ hmK1
    omega
  have htsle : ts ≤ (g + c + 1) * S := by
    rw [hS, show (g + c + 1) * (p * (K + 1)) = (g + c + 1) * p * (K + 1) by ring]
    have := Nat.mul_le_mul_right (K + 1) (show m / K + 1 ≤ (g + c + 1) * p by omega)
    rw [add_mul (m / K) 1, one_mul] at this
    omega
  -- the first lone appearance of `v` after `r`
  have hex : ∃ t, r < t ∧ σ t = {v} := ⟨ts, hrts, hσts⟩
  set t0 := Nat.find hex with ht0
  obtain ⟨hrt0, hσt0⟩ := Nat.find_spec hex
  have ht0ts : t0 ≤ ts := Nat.find_min' hex ⟨hrts, hσts⟩
  refine ⟨t0, ⟨hrt0, by rw [hσt0]; exact mem_singleton_self v, ?_⟩, hσt0, ht0ts.trans htsle⟩
  -- the appearances of `v` between `r` and `t0` are Line-Transmit steps in distinct stages
  -- among `g, …, g + c`
  have hlinestep : ∀ t ∈ (Ioo r t0).filter (fun t => v ∈ σ t), (t - 1) % (K + 1) = 0 := by
    intro t ht
    rw [mem_filter, mem_Ioo] at ht
    by_contra hj
    exact Nat.find_min hex ht.1.2 ⟨ht.1.1, lineRR_eq_singleton_of_rr hj ht.2⟩
  have hmaps : ∀ t ∈ (Ioo r t0).filter (fun t => v ∈ σ t), (t - 1) / S ∈ Icc g (g + c) := by
    intro t ht
    rw [mem_filter, mem_Ioo] at ht
    rw [mem_Icc]
    constructor
    · rw [Nat.le_div_iff_mul_le hS0]
      have : g * S ≤ r := Nat.div_mul_le_self r S
      omega
    · rw [Nat.div_le_iff_le_mul_add_pred hS0]
      have : (g + c + 1) * S = S * (g + c) + S := by ring
      omega
  have hinj : Set.InjOn (fun t => (t - 1) / S) ((Ioo r t0).filter (fun t => v ∈ σ t)) := by
    intro t ht t' ht' heq
    have hl := hlinestep t ht
    have hl' := hlinestep t' ht'
    rw [coe_filter] at ht ht'
    simp only [mem_Ioo, Set.mem_ofPred_eq] at ht ht'
    simp only [hS, stage_eq] at heq
    exact line_step_unique_in_stage hpos (by omega) (by omega) hl hl' heq ht.2 ht'.2
  have := card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Icc] at this
  unfold count
  omega

end schedule

/-- **Lemma 4.1 (validity).** In *Oblivious k-Shot* (`k ≥ 3`, `p > 0`, `n ≤ p²`), every node,
whenever it receives the message (at step `r`), transmits at least once alone: one of its `k`
transmission steps has transmission set `{v}`. -/
theorem lemma_4_1 {n p k : ℕ} (hp : 0 < p) (hn : n ≤ p * p) (hk : 3 ≤ k) (v : Fin n) (r : ℕ) :
    ∃ t, TransmitsAt (obliviousKShot n p k) k r v t ∧ obliviousKShot n p k t = {v} := by
  obtain ⟨t, h1, h2, -⟩ := exists_lone_transmission hp hn (one_le_numRR hp hk)
    (k := k) (c := k - 2) (le_mul_numRR hk) (by omega) v r
  exact ⟨t, h1, h2⟩

end Podc.KShotRadioBroadcast
