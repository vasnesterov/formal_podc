import Papers.PODC2012.LineTreeScheduling.Composite

/-!
# Line networks with windows (Section 7): Theorems 7.1 and 7.2

Timeslots are natural numbers; a resource `q` offers bandwidth `1` on every timeslot. A demand `a`
has a window `[rt a, dl a]`, a processing time `ρ a ≥ 1`, a profit, a height and a set `acc a` of
accessible resources. Its demand instances are the pairs `(q, s)` with `q ∈ acc a` and
`rt a ≤ s`, `s + ρ a - 1 ≤ dl a`; such an instance occupies the timeslots `[s, s + ρ a - 1]` of
resource `q`.

The improved layered decomposition of Section 7: instances are grouped by length,
`grp d = ⌊log₂ (len(d) / L_min)⌋`, and `π(d) = {s(d), mid(d), e(d)}` (`lineLayered`, critical set
size `Δ = 3`, length `⌊log₂(L_max/L_min)⌋ + 1`). Plugging it into the unit-height algorithm with
`ξ = 8/9` gives `theorem_7_1` (`(1-ε) Opt ≤ 4 p(S)`), into the algorithm for arbitrary heights
`theorem_7_2` (`(1-ε) Opt ≤ 23 p(S)`).
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

/-- The key interval fact behind the line-network decomposition: if two overlapping intervals
`[s₁, e₁]`, `[s₂, e₂]` satisfy `len₁ ≤ 2 len₂ + 1`, then `[s₂, e₂]` contains the start, the
midpoint `⌊(s₁+e₁)/2⌋` or the end of `[s₁, e₁]`. -/
lemma interval_hits {s₁ e₁ s₂ e₂ x : ℕ} (h₁ : s₁ ≤ x ∧ x ≤ e₁) (h₂ : s₂ ≤ x ∧ x ≤ e₂)
    (hlen : e₁ - s₁ + 1 ≤ 2 * (e₂ - s₂ + 1) + 1) :
    (s₂ ≤ s₁ ∧ s₁ ≤ e₂) ∨ (s₂ ≤ (s₁ + e₁) / 2 ∧ (s₁ + e₁) / 2 ≤ e₂) ∨ (s₂ ≤ e₁ ∧ e₁ ≤ e₂) := by
  omega

variable {A Q : Type*} [DecidableEq A] [DecidableEq Q]

/-- Input of the scheduling problem on line networks with windows (Section 7). The timeline
consists of the timeslots `0, …, n-1`. -/
structure LineInput (A Q : Type*) where
  /-- Number of timeslots. -/
  n : ℕ
  /-- Release time. -/
  rt : A → ℕ
  /-- Deadline. -/
  dl : A → ℕ
  /-- Processing time. -/
  ρ : A → ℕ
  /-- Accessible resources. -/
  acc : A → Finset Q
  /-- Profit. -/
  profit : A → ℝ
  /-- Height (bandwidth requirement). -/
  height : A → ℝ
  /-- Windows lie within the timeline. -/
  dl_lt : ∀ a, dl a < n

namespace LineInput

variable (P : LineInput A Q) [Fintype Q]

/-- Demand instances: a demand, an accessible resource, and a start time with the execution
interval `[s, s + ρ - 1]` inside the window. -/
def Inst' : Type _ :=
  {x : A × Q × Fin P.n // x.2.1 ∈ P.acc x.1 ∧ P.rt x.1 ≤ x.2.2 ∧ (x.2.2 : ℕ) + P.ρ x.1 ≤ P.dl x.1 + 1}

instance [Fintype A] : Fintype P.Inst' := by unfold Inst'; infer_instance
instance : DecidableEq P.Inst' := by unfold Inst'; infer_instance

/-- The demand of an instance. -/
def dem (d : P.Inst') : A := d.1.1
/-- The resource of an instance. -/
def res (d : P.Inst') : Q := d.1.2.1
/-- The start time `s(d)`. -/
def st (d : P.Inst') : ℕ := d.1.2.2
/-- The end time `e(d) = s(d) + ρ - 1`. -/
def en (d : P.Inst') : ℕ := P.st d + P.ρ (P.dem d) - 1

lemma en_lt (d : P.Inst') : P.en d < P.n := by
  have h1 := d.2.2.2
  have h2 := P.dl_lt d.1.1
  have h3 : (d.1.2.2 : ℕ) < P.n := d.1.2.2.2
  unfold en st dem; omega

/-- The abstract instance: an instance uses the timeslots `[s(d), e(d)]` of its resource; edges
are pairs (resource, timeslot). -/
def toInst : Inst A P.Inst' (Q × Fin P.n) where
  dem := P.dem
  path d := Finset.univ.filter fun e : Q × Fin P.n =>
    e.1 = P.res d ∧ P.st d ≤ e.2 ∧ (e.2 : ℕ) ≤ P.en d
  profit d := P.profit (P.dem d)

lemma mem_path {d : P.Inst'} {e : Q × Fin P.n} :
    e ∈ P.toInst.path d ↔ e.1 = P.res d ∧ P.st d ≤ e.2 ∧ (e.2 : ℕ) ≤ P.en d := by
  simp [toInst]

/-- The critical edges `π(d) = {s(d), mid(d), e(d)}` (with `mid(d) = ⌊(s(d)+e(d))/2⌋`) on the
resource of `d`. -/
def critL (d : P.Inst') : Finset (Q × Fin P.n) :=
  Finset.univ.filter fun e : Q × Fin P.n => e.1 = P.res d ∧
    ((e.2 : ℕ) = P.st d ∨ (e.2 : ℕ) = (P.st d + P.en d) / 2 ∨ (e.2 : ℕ) = P.en d)

lemma card_critL (d : P.Inst') : (P.critL d).card ≤ 3 := by
  have : (P.critL d).card ≤ ({P.st d, (P.st d + P.en d) / 2, P.en d} : Finset ℕ).card := by
    refine Finset.card_le_card_of_injOn (fun e => (e.2 : ℕ)) (fun e he => ?_) (fun e₁ h₁ e₂ h₂ h => ?_)
    · simp only [critL, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      exact he.2
    · simp only [critL, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h₁ h₂
      exact Prod.ext (h₁.1.trans h₂.1.symm) (Fin.ext h)
  exact this.trans Finset.card_le_three

/-- **The layered decomposition of Section 7** (implicit in Panconesi–Sozio): groups by length,
critical set size `3`, length `⌊log₂(L_max/L_min)⌋ + 1`, for processing times
`1 ≤ L_min ≤ ρ ≤ L_max`. -/
def lineLayered {Lmin Lmax : ℕ} (hLmin : 0 < Lmin) (hρmin : ∀ a, Lmin ≤ P.ρ a)
    (hρmax : ∀ a, P.ρ a ≤ Lmax) : P.toInst.Layered 3 (Nat.log 2 (Lmax / Lmin) + 1) where
  grp d := Nat.log 2 (P.ρ (P.dem d) / Lmin)
  crit := P.critL
  grp_lt d := Nat.lt_succ_of_le (Nat.log_mono_right (Nat.div_le_div_right (hρmax _)))
  crit_subset d := by
    have h1 : 1 ≤ P.ρ (P.dem d) := hLmin.trans_le (hρmin _)
    have h2 : P.st d ≤ P.en d := by unfold en; omega
    intro e he
    simp only [critL, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨he1, he2⟩ := he
    rw [mem_path]
    refine ⟨he1, ?_, ?_⟩ <;> omega
  card_crit d := P.card_critL d
  prop d₁ d₂ hg hov := by
    obtain ⟨⟨q, x⟩, hx⟩ := hov
    rw [Finset.mem_inter, mem_path, mem_path] at hx
    obtain ⟨⟨hq₁, hx₁⟩, ⟨hq₂, hx₂⟩⟩ := hx
    set ρ₁ := P.ρ (P.dem d₁)
    set ρ₂ := P.ρ (P.dem d₂)
    have h1 : 1 ≤ ρ₁ := hLmin.trans_le (hρmin _)
    have h2 : 1 ≤ ρ₂ := hLmin.trans_le (hρmin _)
    -- lengths within a factor two: `ρ₁ < 2 ρ₂`
    have hlen : ρ₁ < 2 * ρ₂ := by
      have hq2 : ρ₂ / Lmin ≠ 0 := (Nat.div_pos (hρmin _) hLmin).ne'
      have a1 : ρ₁ / Lmin < 2 ^ (Nat.log 2 (ρ₁ / Lmin) + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) _
      have a2 : 2 ^ Nat.log 2 (ρ₂ / Lmin) ≤ ρ₂ / Lmin := Nat.pow_log_le_self 2 hq2
      have a3 : 2 ^ (Nat.log 2 (ρ₁ / Lmin) + 1) ≤ 2 ^ (Nat.log 2 (ρ₂ / Lmin) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_succ hg)
      have a4 : ρ₁ / Lmin + 1 ≤ 2 * (ρ₂ / Lmin) := by rw [pow_succ] at a3; omega
      have a5 : ρ₁ < ρ₁ / Lmin * Lmin + Lmin := Nat.lt_div_mul_add hLmin
      have a6 : ρ₂ / Lmin * Lmin ≤ ρ₂ := Nat.div_mul_le_self _ _
      have a7 : (ρ₁ / Lmin + 1) * Lmin ≤ 2 * (ρ₂ / Lmin) * Lmin := Nat.mul_le_mul_right _ a4
      nlinarith
    have he₁ : P.en d₁ = P.st d₁ + ρ₁ - 1 := rfl
    have he₂ : P.en d₂ = P.st d₂ + ρ₂ - 1 := rfl
    have hhit := interval_hits (s₁ := P.st d₁) (e₁ := P.en d₁) (s₂ := P.st d₂) (e₂ := P.en d₂)
      hx₁ hx₂ (by omega)
    have hq : P.res d₁ = P.res d₂ := hq₁.symm.trans hq₂
    have hlt := P.en_lt d₁
    have hse : P.st d₁ ≤ P.en d₁ := by omega
    have pick : ∀ t : ℕ, (ht : t < P.n) → (t = P.st d₁ ∨ t = (P.st d₁ + P.en d₁) / 2 ∨
        t = P.en d₁) → P.st d₂ ≤ t → t ≤ P.en d₂ →
        (P.critL d₁ ∩ P.toInst.path d₂).Nonempty := fun t ht h3 h4 h5 =>
      ⟨(P.res d₁, ⟨t, ht⟩), Finset.mem_inter.2 ⟨by simp [critL, h3], (mem_path P).2 ⟨hq, h4, h5⟩⟩⟩
    rcases hhit with h | h | h
    · exact pick _ (by omega) (Or.inl rfl) h.1 h.2
    · exact pick _ (by omega) (Or.inr (Or.inl rfl)) h.1 h.2
    · exact pick _ hlt (Or.inr (Or.inr rfl)) h.1 h.2

variable [Fintype A]

/-- **Theorem 7.1** (unit-height line networks with windows). For `ε < 1`, `ξ = 8/9`, `b` stages
with `(8/9)^b ≤ ε`, `K` steps per stage with `p_max < 2^K p_min` and any MIS oracle, the algorithm
runs `ℓ b K` steps with `ℓ = ⌊log₂(L_max/L_min)⌋ + 1` and outputs a feasible solution `S` with
`(1-ε) · p(Opt) ≤ 4 · p(S)` (i.e. ratio `4/(1-ε)`, which is `4 + ε'` for `ε = ε'/(4+ε')`).
The bound holds even against the LP optimum. -/
theorem theorem_7_1 {Lmin Lmax : ℕ} (hLmin : 0 < Lmin) (hρmin : ∀ a, Lmin ≤ P.ρ a)
    (hρmax : ∀ a, P.ρ a ≤ Lmax) {pmin pmax : ℝ} (hpmin0 : 0 < pmin)
    (hpmin : ∀ a, pmin ≤ P.profit a) (hpmax : ∀ a, P.profit a ≤ pmax) {ε : ℝ}
    {b K : ℕ} (hb : (8 / 9 : ℝ) ^ b ≤ ε) (hK : pmax < 2 ^ K * pmin)
    {mis : ℕ → Finset P.Inst' → Finset P.Inst'} (hmis : ∀ t U, P.toInst.IsMIS U (mis t U)) :
    let L := P.lineLayered hLmin hρmin hρmax
    let S := P.toInst.solU (P.toInst.algI (unitRule L.crit) ⟨L.grp, b, K, ξUnit 3⟩ mis)
      ((Nat.log 2 (Lmax / Lmin) + 1) * b * K)
    P.toInst.IsIndep S ∧
      ∀ O, P.toInst.IsIndep O → (1 - ε) * P.toInst.profitOf O ≤ 4 * P.toInst.profitOf S := by
  intro L S
  have hb' : ξUnit 3 ^ b ≤ ε := by rw [ξUnit_three]; exact hb
  refine ⟨(Inst.unit_alg L hpmin0 (fun d => hpmin (P.dem d)) (fun d => hpmax (P.dem d)) hb' hK hmis
    (x := 0) ⟨fun _ => le_rfl, fun e => by simp, fun a => by simp⟩).1, fun O hO => ?_⟩
  have := (Inst.unit_alg L hpmin0 (fun d => hpmin (P.dem d)) (fun d => hpmax (P.dem d)) hb' hK hmis
    (Inst.IsIndep.isLPFeasible _ hO)).2
  rw [Inst.lpValue_ind] at this
  norm_num at this
  rw [div_mul_eq_mul_div, div_le_iff₀ (by norm_num)] at this
  linarith

/-- **Theorem 7.2** (line networks with windows, arbitrary heights `h_min ≤ h ≤ 1`,
`h_min ≤ 1/2`). Running the unit algorithm (`ξ = 8/9`, `bw` stages) on the wide instances and the
narrow algorithm (`ξ = 10/(10 + h_min)`, `bn` stages) on the narrow ones and combining, the output
`S` is feasible and `(1-ε) · p(Opt) ≤ 23 · p(S)` (ratio `(4 + 19)/(1-ε)`). -/
theorem theorem_7_2 {Lmin Lmax : ℕ} (hLmin : 0 < Lmin) (hρmin : ∀ a, Lmin ≤ P.ρ a)
    (hρmax : ∀ a, P.ρ a ≤ Lmax) {hmin : ℝ} (hmin0 : 0 < hmin) (hmin12 : hmin ≤ 1 / 2)
    (hhmin : ∀ a, hmin ≤ P.height a) (hh1 : ∀ a, P.height a ≤ 1) {pmin pmax : ℝ}
    (hpmin0 : 0 < pmin) (hpmin : ∀ a, pmin ≤ P.profit a) (hpmax : ∀ a, P.profit a ≤ pmax)
    {ε : ℝ} (hε1 : ε < 1) {bw bn K : ℕ} (hbw : (8 / 9 : ℝ) ^ bw ≤ ε)
    (hbn : (10 / (10 + hmin)) ^ bn ≤ ε) (hK : pmax < 2 ^ K * pmin)
    (misW misN) (hmisW : ∀ t U, (P.toInst.restrict (Inst.Wide (fun d => P.height (P.dem d)))).IsMIS U
      (misW t U))
    (hmisN : ∀ t U, (P.toInst.restrict (Inst.Narrow (fun d => P.height (P.dem d)))).IsMIS U
      (misN t U)) :
    let S := P.toInst.arbSol (P.lineLayered hLmin hρmin hρmax) (fun d => P.height (P.dem d)) hmin
      bw bn K P.res misW misN
    P.toInst.IsHFeasible (fun d => P.height (P.dem d)) S ∧
      ∀ O, P.toInst.IsHFeasible (fun d => P.height (P.dem d)) O →
        (1 - ε) * P.toInst.profitOf O ≤ 23 * P.toInst.profitOf S := by
  intro S
  have hbw' : ξUnit 3 ^ bw ≤ ε := by rw [ξUnit_three]; exact hbw
  have hbn' : ξNarrow 3 hmin ^ bn ≤ ε := by unfold ξNarrow; norm_num; exact hbn
  have := Inst.arbitrary_alg (P.lineLayered hLmin hρmin hρmax) hmin0 hmin12 (fun d => hhmin _)
    (fun d => hh1 _) (fun d₁ d₂ h => by simp only [toInst] at h; rw [h]) P.res
    (fun d₁ d₂ hov => by
      obtain ⟨e, he⟩ := hov
      rw [Finset.mem_inter, mem_path, mem_path] at he
      exact he.1.1.symm.trans he.2.1)
    hpmin0 (fun d => hpmin (P.dem d)) (fun d => hpmax (P.dem d)) hε1 hbw' hbn' hK hmisW hmisN
  refine ⟨this.1, fun O hO => ?_⟩
  have := this.2 O hO
  norm_num at this
  exact this

end LineInput

end Podc.LineTreeScheduling
