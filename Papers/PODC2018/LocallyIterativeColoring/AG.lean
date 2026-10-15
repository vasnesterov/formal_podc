import Cslib.Computability.Distributed.Local.LocallyIterative
import Mathlib

/-!
# The Additive-Group (AG) algorithm (Section 3.1 of [BEG18])

[BEG18] L. Barenboim, M. Elkin, U. Goldenberg. *Locally-Iterative Distributed (Δ+1)-Coloring below
Szegedy–Vishwanathan Barrier, and Applications to Self-Stabilization and to Restricted-Bandwidth
Models.* PODC 2018; arXiv:1712.00285v2.

Colours are pairs `⟨a, b⟩` over an additive group `R` (in the paper `R = GF(q)`, `q` prime). In
every round a vertex `v` with colour `⟨a, b⟩`
* *conflicts* if some neighbour has the same second coordinate `b`; then its new colour is
  `⟨a, b + a⟩`;
* otherwise its new colour is `⟨0, b⟩` (*final*).

## Main results

* `ag_isProper` (**Lemma 3.2**): proper colourings stay proper, over any additive group.
* `run_of_working`, `run_of_final`: the trajectory of a vertex is `⟨a, b + t•a⟩` while it is working
  and constant once it is final.
* `ag_final` (**Lemmas 3.3, 3.4 + Corollary 3.5**, generalized): over `ZMod q`, `q` prime, if all
  degrees are `≤ Δ` and `Δ (m + 1) < m q`, every vertex is final after `m q` rounds.
  `ag_final_of_two_mul_lt` is the paper's case `m = 1`, `2Δ < q`: final after `q` rounds.
-/

namespace BEG18

open Cslib.LocallyIterative Finset

variable {V R : Type*} {G : SimpleGraph V}

section Group

variable [AddCommGroup R]

open Classical in
/-- One step of the AG algorithm (Algorithm 1 of [BEG18], lines 4–10): a vertex with colour `x`
whose neighbours have the set of colours `N`. -/
noncomputable def agStep (x : R × R) (N : Set (R × R)) : R × R :=
  if ∃ y ∈ N, y.2 = x.2 then (x.1, x.2 + x.1) else (0, x.2)

/-- The AG algorithm (Algorithm 1 of [BEG18]); it is round-independent. -/
noncomputable def ag : Algorithm (R × R) := Algorithm.ofStep agStep

variable (G) in
/-- Vertex `v` *conflicts* under colouring `c` (Definition 3.1 of [BEG18]): some neighbour has the
same second coordinate. -/
def Conflict (c : V → R × R) (v : V) : Prop := ∃ u, G.Adj v u ∧ (c u).2 = (c v).2

open Classical in
theorem agStep_nbrColors (c : V → R × R) (v : V) :
    agStep (c v) (nbrColors G c v) =
      if Conflict G c v then ((c v).1, (c v).2 + (c v).1) else (0, (c v).2) := by
  classical
  simp only [agStep, Conflict, mem_nbrColors]
  congr 1
  apply propext
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, h⟩; exact ⟨u, hu, h⟩
  · rintro ⟨u, hu, h⟩; exact ⟨_, ⟨u, hu, rfl⟩, h⟩

open Classical in
theorem ag_run_succ (c₀ : V → R × R) (t : ℕ) (v : V) :
    (ag : Algorithm (R × R)).run G c₀ (t + 1) v =
      if Conflict G (ag.run G c₀ t) v then
        ((ag.run G c₀ t v).1, (ag.run G c₀ t v).2 + (ag.run G c₀ t v).1)
      else (0, (ag.run G c₀ t v).2) := by
  rw [Algorithm.run_succ_apply]
  exact agStep_nbrColors _ v

/-- One AG round preserves properness (the induction step of Lemma 3.2 of [BEG18]). -/
theorem agStep_ne {c : V → R × R} {u v : V} (huv : G.Adj u v) (hne : c u ≠ c v) :
    agStep (c u) (nbrColors G c u) ≠ agStep (c v) (nbrColors G c v) := by
  classical
  simp only [agStep_nbrColors]
  split_ifs with hu hv hv
  · -- both conflict: `a = a'` and `b + a = b' + a'` force equal colours
    intro h
    simp only [Prod.mk.injEq] at h
    apply hne
    ext
    · exact h.1
    · have := h.2; rw [h.1] at this; exact add_right_cancel this
  · intro h
    simp only [Prod.mk.injEq] at h
    -- `u` (a neighbour of `v`) has second coordinate `b_v`, so `v` conflicts
    apply hv ⟨u, huv.symm, ?_⟩
    have h2 := h.2; rw [h.1, add_zero] at h2; exact h2
  · intro h
    simp only [Prod.mk.injEq] at h
    apply hu ⟨v, huv, ?_⟩
    have h2 := h.2; rw [← h.1, add_zero] at h2; exact h2.symm
  · intro h
    simp only [Prod.mk.injEq] at h
    exact hu ⟨v, huv, h.2.symm⟩

theorem isProper_agStep {c : V → R × R} (hc : IsProper G c) :
    IsProper G fun v => agStep (c v) (nbrColors G c v) := fun _ _ huv => agStep_ne huv (hc huv)

theorem agStep_of_fst_eq_zero (x : R × R) (N : Set (R × R)) (hx : x.1 = 0) : agStep x N = x := by
  classical
  unfold agStep; split_ifs <;> ext <;> simp [hx]

/-- **Lemma 3.2 of [BEG18].** Starting from a proper colouring, every colouring produced by the AG
algorithm is proper (over any additive commutative group). -/
theorem ag_isProper {c₀ : V → R × R} (h₀ : IsProper G c₀) (t : ℕ) :
    IsProper G ((ag : Algorithm (R × R)).run G c₀ t) := by
  induction t with
  | zero => exact h₀
  | succ t ih =>
    rw [Algorithm.run_succ]
    exact isProper_agStep ih

/-! ### Trajectories

The running-time analysis only uses three properties of a run `c : ℕ → V → R × R`, collected in
`IsAGRun`: a vertex working in round `t + 1` was conflicting in round `t` and made the AG move; final
vertices stay final; a final vertex with a working neighbour keeps its colour. Besides AG itself
(`isAGRun_ag`), this covers AG combined with recolourings of final vertices whose neighbours are all
final (`Uniform.lean`). -/

variable (G) in
/-- The properties of an AG run used in the analysis of Lemmas 3.3, 3.4 and Corollary 3.5. -/
structure IsAGRun (c : ℕ → V → R × R) : Prop where
  working : ∀ t v, (c (t + 1) v).1 ≠ 0 →
    Conflict G (c t) v ∧ c (t + 1) v = ((c t v).1, (c t v).2 + (c t v).1)
  final : ∀ t v, (c t v).1 = 0 → (c (t + 1) v).1 = 0
  stable : ∀ t u w, (c t u).1 = 0 → G.Adj u w → (c t w).1 ≠ 0 → c (t + 1) u = c t u

namespace IsAGRun

variable {c : ℕ → V → R × R} (hc : IsAGRun G c)
include hc

theorem working_mono {s t : ℕ} {v : V} (hst : s ≤ t) (h : (c t v).1 ≠ 0) : (c s v).1 ≠ 0 := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact ih fun h0 => h (hc.final t v h0)

/-- A vertex that is working in round `t + 1` was working and conflicting in round `t`. -/
theorem conflict_of_working {t : ℕ} {v : V} (h : (c (t + 1) v).1 ≠ 0) :
    Conflict G (c t) v ∧ (c t v).1 ≠ 0 ∧ c (t + 1) v = ((c t v).1, (c t v).2 + (c t v).1) :=
  ⟨(hc.working t v h).1, hc.working_mono (Nat.le_succ t) h, (hc.working t v h).2⟩

/-- While working, a vertex with initial colour `⟨a, b⟩` has colour `⟨a, b + t • a⟩`. -/
theorem eq_of_working {t : ℕ} {v : V} (h : (c t v).1 ≠ 0) :
    c t v = ((c 0 v).1, (c 0 v).2 + t • (c 0 v).1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨-, hw, heq⟩ := hc.conflict_of_working h
    rw [heq, ih hw, succ_nsmul]
    ext <;> simp [add_assoc]

/-- A final vertex `u` that has a neighbour `w` working up to round `T` keeps its colour up to
round `T`. -/
theorem eq_of_final {s t : ℕ} {u w : V} (h : (c s u).1 = 0) (hst : s ≤ t) (huw : G.Adj u w)
    (hw : (c t w).1 ≠ 0) : c t u = c s u := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    have ih := ih (hc.working_mono (Nat.le_succ t) hw)
    rw [hc.stable t u w (ih ▸ h) huw (hc.working_mono (Nat.le_succ t) hw), ih]

end IsAGRun

variable (c₀ : V → R × R)

/-- A final vertex (first coordinate `0`) keeps its colour (footnote 1 on p. 6 of [BEG18]). -/
theorem ag_run_succ_of_final {t : ℕ} {v : V} (h : ((ag : Algorithm (R × R)).run G c₀ t v).1 = 0) :
    (ag : Algorithm (R × R)).run G c₀ (t + 1) v = ag.run G c₀ t v := by
  rw [ag_run_succ]
  split_ifs <;> ext <;> simp [h]

theorem ag_run_of_final {s t : ℕ} {v : V} (h : ((ag : Algorithm (R × R)).run G c₀ s v).1 = 0)
    (hst : s ≤ t) : (ag : Algorithm (R × R)).run G c₀ t v = ag.run G c₀ s v := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t _ ih => rw [ag_run_succ_of_final c₀ (ih ▸ h), ih]

/-- Runs of AG satisfy `IsAGRun`. -/
theorem isAGRun_ag : IsAGRun G ((ag : Algorithm (R × R)).run G c₀) where
  working t v h := by
    rw [ag_run_succ] at h ⊢
    split_ifs at h ⊢ with hc
    · exact ⟨hc, rfl⟩
    · exact absurd rfl h
  final t v h := by rw [ag_run_succ_of_final c₀ h]; exact h
  stable t u _ h _ _ := ag_run_succ_of_final c₀ h

/-- While working, a vertex with initial colour `⟨a, b⟩` has colour `⟨a, b + t • a⟩`. -/
theorem ag_run_of_working {t : ℕ} {v : V} (h : ((ag : Algorithm (R × R)).run G c₀ t v).1 ≠ 0) :
    (ag : Algorithm (R × R)).run G c₀ t v = ((c₀ v).1, (c₀ v).2 + t • (c₀ v).1) :=
  (isAGRun_ag c₀).eq_of_working h

end Group

/-! ### Counting conflicts over `ZMod q` -/

section Count

variable {q : ℕ} [NeZero q]

/-- Numbers in `[lo, hi)` in one residue class mod `q`: at most `⌈(hi - lo) / q⌉` of them. -/
theorem card_filter_natCast_eq_le (x : ZMod q) (lo hi : ℕ) :
    #{t ∈ Ico lo hi | ((t : ℕ) : ZMod q) = x} ≤ (hi - lo + q - 1) / q := by
  have hq : 0 < q := Nat.pos_of_neZero q
  calc #{t ∈ Ico lo hi | ((t : ℕ) : ZMod q) = x}
      ≤ #(range ((hi - lo + q - 1) / q)) := by
        apply card_le_card_of_injOn (fun t => (t - lo) / q)
        · intro t ht
          simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at ht
          simp only [coe_range, Set.mem_Iio]
          apply Nat.div_lt_of_lt_mul
          have : (hi - lo + q - 1) / q * q + q > hi - lo + q - 1 := by
            have := Nat.lt_div_mul_add (a := hi - lo + q - 1) hq; omega
          rw [Nat.mul_comm]; omega
        · intro t₁ h₁ t₂ h₂ he
          simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at h₁ h₂
          have hmod : (t₁ - lo) % q = (t₂ - lo) % q := by
            have : ((t₁ - lo : ℕ) : ZMod q) = ((t₂ - lo : ℕ) : ZMod q) := by
              rw [Nat.cast_sub h₁.1.1, Nat.cast_sub h₂.1.1, h₁.2, h₂.2]
            exact (ZMod.natCast_eq_natCast_iff' _ _ q).1 this
          have e1 := Nat.mod_add_div (t₁ - lo) q
          have e2 := Nat.mod_add_div (t₂ - lo) q
          simp only at he
          rw [hmod, he] at e1
          omega
    _ = _ := card_range _

/-- Solutions of `t * k = e` (`k ≠ 0` or `e ≠ 0`) in `[lo, hi)`: at most `⌈(hi - lo) / q⌉`
(`q` prime). This is the "`d + x c ≡ b` has exactly one solution" fact of Lemmas 3.3–3.4. -/
theorem card_filter_mul_eq_le [Fact q.Prime] {k e : ZMod q} (hke : k ≠ 0 ∨ e ≠ 0) (lo hi : ℕ) :
    #{t ∈ Ico lo hi | ((t : ℕ) : ZMod q) * k = e} ≤ (hi - lo + q - 1) / q := by
  by_cases hk : k = 0
  · have he : e ≠ 0 := hke.resolve_left (not_not.2 hk)
    simp [hk, he.symm]
  · calc #{t ∈ Ico lo hi | ((t : ℕ) : ZMod q) * k = e} = #{t ∈ Ico lo hi | ((t : ℕ) : ZMod q) = e * k⁻¹} := by
          congr 1; apply filter_congr; intro t _
          constructor
          · intro h; rw [← h, mul_assoc, mul_inv_cancel₀ hk, mul_one]
          · intro h; rw [h, mul_assoc, inv_mul_cancel₀ hk, mul_one]
      _ ≤ _ := card_filter_natCast_eq_le _ _ _

theorem ceil_add_ceil_le (q s T m : ℕ) (hq : 0 < q) (hs : s ≤ T) (hT : T = m * q) :
    (s - 0 + q - 1) / q + (T - s + q - 1) / q ≤ m + 1 := by
  have h := Nat.div_add_div_le_add_div (x := s - 0 + q - 1) (y := T - s + q - 1) (z := q)
  have h1 : (s - 0 + q - 1) + (T - s + q - 1) < (m + 2) * q := by
    rw [add_mul, ← hT]; omega
  have h2 := (Nat.div_lt_iff_lt_mul hq).2 h1
  omega

end Count

section Main

variable {q : ℕ} [Fact q.Prime] [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- The number of rounds `t < T` in which `v`, working throughout `[0, T]`, conflicts with the
neighbour `u` is at most `m + 1` when `T = m q` (Lemmas 3.3 and 3.4 of [BEG18], generalized
from `T ≤ q` to `T = m q`: at most one conflict per period while both are working, at most one per
period once `u` is final). -/
theorem IsAGRun.card_conflicts_le {c : ℕ → V → ZMod q × ZMod q} (hc : IsAGRun G c)
    (h₀ : IsProper G (c 0)) {m T : ℕ} (hT : T = m * q) {u v : V} (huv : G.Adj v u)
    (hv : (c T v).1 ≠ 0) :
    #{t ∈ range T | (c t u).2 = (c t v).2} ≤ m + 1 := by
  classical
  have hq : 0 < q := (Fact.out : q.Prime).pos
  -- trajectory of `v`
  have hvt : ∀ t ≤ T, c t v = ((c 0 v).1, (c 0 v).2 + t • (c 0 v).1) := fun t ht =>
    hc.eq_of_working (hc.working_mono ht hv)
  have ha : (c 0 v).1 ≠ 0 := hc.working_mono (Nat.zero_le T) hv
  -- the first time `u` is final (or `T`)
  let s : ℕ := if h : ∃ s, s < T ∧ (c s u).1 = 0 then Nat.find h else T
  have hsT : s ≤ T := by
    simp only [s]; split_ifs with h
    · exact (Nat.find_spec h).1.le
    · exact le_rfl
  have hwork : ∀ t < s, (c t u).1 ≠ 0 := by
    intro t hts h
    simp only [s] at hts; split_ifs at hts with hex
    · exact Nat.find_min hex hts ⟨by have := (Nat.find_spec hex).1; omega, h⟩
    · exact hex ⟨t, hts, h⟩
  have hfin : s < T → ∀ t, s ≤ t → t ≤ T → c t u = c s u := by
    intro hs t hst htT
    simp only [s] at hs hst ⊢; split_ifs at hs hst ⊢ with hex
    · exact hc.eq_of_final (Nat.find_spec hex).2 hst huv.symm (hc.working_mono htT hv)
    · omega
  -- split the conflict rounds at `s`
  have hsplit : {t ∈ range T | (c t u).2 = (c t v).2} ⊆
      {t ∈ Ico 0 s | ((t : ℕ) : ZMod q) * ((c 0 u).1 - (c 0 v).1) = (c 0 v).2 - (c 0 u).2} ∪
      {t ∈ Ico s T | ((t : ℕ) : ZMod q) * (c 0 v).1 = (c s u).2 - (c 0 v).2} := by
    intro t ht
    simp only [mem_filter, mem_range] at ht
    rw [hvt t ht.1.le] at ht
    simp only [mem_union, mem_filter, mem_Ico, Nat.zero_le, true_and]
    by_cases hts : t < s
    · left
      refine ⟨hts, ?_⟩
      have := ht.2; rw [hc.eq_of_working (hwork t hts)] at this
      simp only [nsmul_eq_mul] at this
      linear_combination this
    · right
      have hs : s < T := by omega
      refine ⟨⟨by omega, ht.1⟩, ?_⟩
      have := ht.2; rw [hfin hs t (by omega) ht.1.le] at this
      simp only [nsmul_eq_mul] at this
      linear_combination -this
  calc _ ≤ #({t ∈ Ico 0 s | ((t : ℕ) : ZMod q) * ((c 0 u).1 - (c 0 v).1) = (c 0 v).2 - (c 0 u).2} ∪
          {t ∈ Ico s T | ((t : ℕ) : ZMod q) * (c 0 v).1 = (c s u).2 - (c 0 v).2}) :=
        card_le_card hsplit
    _ ≤ _ := card_union_le _ _
    _ ≤ (s - 0 + q - 1) / q + (T - s + q - 1) / q := by
        gcongr
        · apply card_filter_mul_eq_le
          by_contra hcon
          push Not at hcon
          apply h₀ huv.symm
          ext
          · exact sub_eq_zero.1 hcon.1
          · exact (sub_eq_zero.1 hcon.2).symm
        · exact card_filter_mul_eq_le (Or.inl ha) _ _
    _ ≤ m + 1 := ceil_add_ceil_le q s T m hq hsT hT

/-- Running time of any `IsAGRun` (see `ag_final`). -/
theorem IsAGRun.allFinal {c : ℕ → V → ZMod q × ZMod q} (hc : IsAGRun G c) (h₀ : IsProper G (c 0))
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {m : ℕ} (hm : Δ * (m + 1) < m * q) (v : V) :
    (c (m * q) v).1 = 0 := by
  classical
  by_contra hv
  set T := m * q
  -- every round `t < T` is a conflict round of `v`
  have hcover : range T ⊆ (G.neighborFinset v).biUnion fun u =>
      {t ∈ range T | (c t u).2 = (c t v).2} := by
    intro t ht
    have ht' := mem_range.1 ht
    obtain ⟨⟨u, hu, he⟩, -, -⟩ := hc.conflict_of_working (hc.working_mono (show t + 1 ≤ T by omega) hv)
    exact mem_biUnion.2 ⟨u, (G.mem_neighborFinset v u).2 hu, mem_filter.2 ⟨ht, he⟩⟩
  have := card_le_card hcover
  rw [card_range] at this
  have h2 := this.trans card_biUnion_le
  have h3 : ∑ u ∈ G.neighborFinset v, #{t ∈ range T | (c t u).2 = (c t v).2}
      ≤ ∑ _u ∈ G.neighborFinset v, (m + 1) :=
    sum_le_sum fun u hu => hc.card_conflicts_le h₀ rfl ((G.mem_neighborFinset v u).1 hu) hv
  rw [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at h3
  have h4 : G.degree v * (m + 1) ≤ Δ * (m + 1) := Nat.mul_le_mul_right _ (hΔ v)
  omega

/-- **Corollary 3.5 of [BEG18] (generalized), via Lemmas 3.3–3.4.** Over `GF(q)` (`q` prime), on a
graph of maximum degree `≤ Δ`, starting from a proper colouring, if `Δ (m + 1) < m q` then after
`m q` rounds every vertex is final (first coordinate `0`). -/
theorem ag_final {c₀ : V → ZMod q × ZMod q} (h₀ : IsProper G c₀) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {m : ℕ} (hm : Δ * (m + 1) < m * q) (v : V) :
    ((ag : Algorithm (ZMod q × ZMod q)).run G c₀ (m * q) v).1 = 0 :=
  (isAGRun_ag c₀).allFinal h₀ hΔ hm v

/-- **Corollary 3.5 of [BEG18]** (the paper's parameters): if `2Δ < q` then after `q` rounds every
vertex is final, i.e. its colour is `⟨0, b⟩`. -/
theorem ag_final_of_two_mul_lt {c₀ : V → ZMod q × ZMod q} (h₀ : IsProper G c₀) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (hq : 2 * Δ < q) (v : V) :
    ((ag : Algorithm (ZMod q × ZMod q)).run G c₀ q v).1 = 0 := by
  have := ag_final h₀ hΔ (m := 1) (by omega) v
  rwa [one_mul] at this

/-- Corrected version of the claim in Section 1.2 of [BEG18] (`q = Δ + 1`): for any prime `q > Δ`,
every vertex is final after `(Δ + 1) q` rounds (`= (Δ + 1)²` rounds for `q = Δ + 1`). The claimed
`2q + 1` rounds do not suffice, see `Counterexamples.lean`. -/
theorem ag_final_of_lt {c₀ : V → ZMod q × ZMod q} (h₀ : IsProper G c₀) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (hq : Δ < q) (v : V) :
    ((ag : Algorithm (ZMod q × ZMod q)).run G c₀ ((Δ + 1) * q) v).1 = 0 :=
  ag_final h₀ hΔ (by nlinarith) v

omit [G.LocallyFinite] in
/-- After the final round the colouring stays the same. -/
theorem ag_run_stable {c₀ : V → ZMod q × ZMod q} {T : ℕ}
    (hT : ∀ v, ((ag : Algorithm (ZMod q × ZMod q)).run G c₀ T v).1 = 0) {t : ℕ} (ht : T ≤ t) :
    (ag : Algorithm (ZMod q × ZMod q)).run G c₀ t = ag.run G c₀ T :=
  funext fun v => ag_run_of_final c₀ (hT v) ht

end Main

end BEG18
