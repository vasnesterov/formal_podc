import Papers.PODC2010.TruncatedGaleShapley.Invariants

/-!
# Analysis of the truncated Gale–Shapley algorithm (§5, Lemmas 1–6)

Edge weights `w : Sym2 V → ℝ` *respect the preferences* (`RespectsPrefs`) if they are nonnegative
and whenever a node prefers `x` over `y`, `w {v,x} ≥ w {v,y}` (§5.2; the paper uses positive
integers, `w ≡ 1` for Theorem 1).

* `nodeW s w v = w {v, p(v)}` (`0` if unmatched); `blueW s w = w_i(B)`, the weight of the matching.
* `pot s w r = f_i(r)`: `w {r, b}` for the head `b` of `C(r)` if `r` is unmatched, else `0`;
  `potR s w = f_i(R)`.
* `lostW s w = w(L_i)`, the weight of the lost edges `{r, b}`, `b ∉ C(r)`.

Main results: `lemma_1` … `lemma_6`. Lemma 6 as stated in the paper (`i ≥ 1 + (Δ-1)/γ`) fails for
`Δ = 1`, `i = 1` (`lemma_6_false_at_one` in `Counterexample.lean`); we prove it for `i ≥ 2`.
-/

namespace Podc.TruncatedGaleShapley

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Bicoloured

variable (I : Bicoloured V)

/-- Edge weights respect the preferences (§5.2): nonnegative, and `v` prefers `x` over `y` ⇒
`w {v, x} ≥ w {v, y}`. -/
structure RespectsPrefs (w : Sym2 V → ℝ) : Prop where
  nonneg : ∀ e, 0 ≤ w e
  mono : ∀ {v x y}, x ∈ I.N v → y ∈ I.N v → I.rank v x < I.rank v y → w s(v, y) ≤ w s(v, x)

/-- The constant weight `1` respects every preference order. -/
lemma respectsPrefs_one : I.RespectsPrefs (fun _ => 1) := ⟨fun _ => zero_le_one, fun _ _ _ => le_rfl⟩

/-- Red nodes. -/
def reds : Finset V := univ.filter fun v => I.red v = true

/-- Blue nodes. -/
def blues : Finset V := univ.filter fun v => I.red v = false

/-- The weight `w {v, p(v)}` of the matching edge at `v` (`0` if `v` is unmatched). -/
def nodeW (s : State V) (w : Sym2 V → ℝ) (v : V) : ℝ :=
  match s.p v with
  | none => 0
  | some u => w s(v, u)

/-- `w_i(B)`: the total blue weight (= the weight of the matching, `blueW_eq_sum_matchingEdges`). -/
def blueW (s : State V) (w : Sym2 V → ℝ) : ℝ := ∑ b ∈ I.blues, nodeW s w b

/-- The potential `f_i(r)` of a red node. -/
noncomputable def pot (s : State V) (w : Sym2 V → ℝ) (r : V) : ℝ :=
  match s.p r, I.best r (s.C r) with
  | none, some b => w s(r, b)
  | _, _ => 0

/-- `f_i(R)`, the total potential. -/
noncomputable def potR (s : State V) (w : Sym2 V → ℝ) : ℝ := ∑ r ∈ I.reds, I.pot s w r

/-- The weight of the lost edges at the red node `r`. -/
def lostAt (s : State V) (w : Sym2 V → ℝ) (r : V) : ℝ := ∑ b ∈ I.N r \ s.C r, w s(r, b)

/-- `w(L_i)`, the weight of all lost edges. -/
def lostW (s : State V) (w : Sym2 V → ℝ) : ℝ := ∑ r ∈ I.reds, I.lostAt s w r

@[simp] lemma mem_reds {v : V} : v ∈ I.reds ↔ I.red v = true := by simp [reds]
@[simp] lemma mem_blues {v : V} : v ∈ I.blues ↔ I.red v = false := by simp [blues]

variable {I}

lemma nodeW_nonneg {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) (s : State V) (v : V) :
    0 ≤ nodeW s w v := by
  unfold nodeW; split <;> simp [hw.nonneg]

lemma pot_nonneg {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) (s : State V) (r : V) :
    0 ≤ I.pot s w r := by
  unfold pot; split <;> simp [hw.nonneg]

lemma potR_nonneg {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) (s : State V) : 0 ≤ I.potR s w :=
  sum_nonneg fun r _ => pot_nonneg hw s r

lemma blueW_nonneg {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) (s : State V) : 0 ≤ I.blueW s w :=
  sum_nonneg fun b _ => nodeW_nonneg hw s b

lemma pot_of_matched {s : State V} {w : Sym2 V → ℝ} {r b : V} (h : s.p r = some b) :
    I.pot s w r = 0 := by
  simp [pot, h]

lemma pot_of_unmatched {s : State V} {w : Sym2 V → ℝ} {r : V} (h : s.p r = none) :
    I.pot s w r = match I.best r (s.C r) with | none => 0 | some b => w s(r, b) := by
  unfold pot; rw [h]; cases I.best r (s.C r) <;> rfl

/-- In the losing case: the potential after losing the head `b` is at most `w {r, b}`. -/
lemma pot_le_of_erase {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {C : Finset V} {r b : V}
    (hC : C ⊆ I.N r) (hb : I.best r C = some b) :
    (match I.best r (C.erase b) with | none => 0 | some x => w s(r, x)) ≤ w s(r, b) := by
  split
  · exact hw.nonneg _
  · rename_i x hx
    obtain ⟨hxC, -⟩ := I.best_spec hx
    have hxb := ne_of_mem_erase hxC
    have hle := (I.best_spec hb).2 x (mem_of_mem_erase hxC)
    have hlt : I.rank r b < I.rank r x := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exact absurd (I.rank_inj (hC (mem_of_mem_erase hxC)) (hC (I.best_mem hb)) h.symm) hxb
    exact hw.mono (hC (I.best_mem hb)) (hC (mem_of_mem_erase hxC)) hlt

/-! ### Lemma 1 -/

/-- **Lemma 1.** At the end of every round `i`, an edge `{r, b}` (`r` red) is unstable only if `b`
is still in `C_i(r)` and `r` is unmatched. -/
theorem lemma_1 (i : ℕ) {r b : V} (hr : I.red r = true)
    (h : I.IsUnstable (I.run i).p r b) : b ∈ (I.run i).C r ∧ (I.run i).p r = none := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [run_zero, hr, h.1]
  have hs := I.inv_run hi
  obtain ⟨hbN, hr', hb'⟩ := h
  refine ⟨?_, ?_⟩
  · by_contra hbC
    obtain ⟨r₀, h₀, hlt⟩ := hs.lost r b hr hbN hbC
    rw [h₀] at hb'
    exact absurd hb' (not_lt.2 hlt.le)
  · rcases hp : (I.run i).p r with _ | b₂
    · rfl
    · exfalso
      rw [hp] at hr'
      have hbest := (hs.red_matched r b₂ hr hp).2
      by_cases hbC : b ∈ (I.run i).C r
      · exact absurd ((I.best_spec hbest).2 b hbC) (not_le.2 hr')
      · obtain ⟨r₀, h₀, hlt⟩ := hs.lost r b hr hbN hbC
        rw [h₀] at hb'
        exact absurd hb' (not_lt.2 hlt.le)

/-! ### Lemma 2 -/

lemma lostAt_round {s : State V} (hs : I.Inv s) {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {r : V}
    (hr : I.red r = true) :
    I.lostAt s w r ≤ I.lostAt (I.round s) w r ∧
      I.pot (I.round s) w r ≤ I.lostAt (I.round s) w r - I.lostAt s w r := by
  rcases hs.red_outcome hr with ⟨hC, hp, -, ⟨b, hb, -⟩ | ⟨hpn, -, hCe⟩⟩ |
      ⟨b, -, -, -, hC, hp, -⟩ | ⟨b, hbest, -, -, hC, hp, -⟩
  · simp [lostAt, hC, pot_of_matched (hp.trans hb)]
  · have : I.pot (I.round s) w r = 0 := by
      rw [pot_of_unmatched (hp.trans hpn), hC, hCe, (I.best_eq_none.2 rfl)]
    simp [lostAt, hC, this]
  · simp [lostAt, hC, pot_of_matched hp]
  · have hbC := I.best_mem hbest
    have hsub := hs.C_sub r hr
    have hdiff : I.N r \ (s.C r).erase b = insert b (I.N r \ s.C r) := by
      ext x; by_cases hx : x = b
      · subst hx; simp [hsub hbC]
      · simp [hx]
    have hlost : I.lostAt (I.round s) w r = w s(r, b) + I.lostAt s w r := by
      rw [lostAt, hC, hdiff, sum_insert (by simp [hbC])]; rfl
    refine ⟨by rw [hlost]; linarith [hw.nonneg s(r, b)], ?_⟩
    rw [hlost, pot_of_unmatched hp, hC, add_sub_cancel_right]
    exact pot_le_of_erase hw hsub hbest

lemma lostW_round_le {s : State V} (hs : I.Inv s) {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) :
    I.lostW s w ≤ I.lostW (I.round s) w :=
  sum_le_sum fun _ hr => (lostAt_round hs hw (I.mem_reds.1 hr)).1

lemma potR_round_le_lostW {s : State V} (hs : I.Inv s) {w : Sym2 V → ℝ}
    (hw : I.RespectsPrefs w) :
    I.potR (I.round s) w ≤ I.lostW (I.round s) w - I.lostW s w := by
  rw [potR, lostW, lostW, ← sum_sub_distrib]
  exact sum_le_sum fun r hr => (lostAt_round hs hw (I.mem_reds.1 hr)).2

/-- **Lemma 2.** For `i ≥ 2`, `f_i(R) ≤ w(L_i) - w(L_{i-1})`. -/
theorem lemma_2 {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {i : ℕ} (hi : 2 ≤ i) :
    I.potR (I.run i) w ≤ I.lostW (I.run i) w - I.lostW (I.run (i - 1)) w := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [run_succ, Nat.add_sub_cancel]
  exact potR_round_le_lostW (I.inv_run (by omega)) hw

/-! ### Lemma 3 -/

lemma potR_round_le_potR {s : State V} (hs : I.Inv s) {w : Sym2 V → ℝ}
    (hw : I.RespectsPrefs w) : I.potR (I.round s) w ≤ I.potR s w := by
  classical
  let Brk : V → Prop := fun r => ∃ b, s.p r = some b ∧ (I.blueTurn s).p b ≠ some r
  let Acc : V → Prop := fun r => s.p r = none ∧ ∃ b, s.c r = some b ∧ (I.blueTurn s).p b = some r
  let φ : V → V := fun r => ((I.blueTurn s).p ((s.p r).getD r)).getD r
  have key : ∀ r ∈ I.reds, I.pot (I.round s) w r + (if Acc r then I.pot s w r else 0) ≤
      I.pot s w r + (if Brk r then nodeW s w r else 0) := by
    intro r hr
    have hr := I.mem_reds.1 hr
    have h0 := pot_nonneg hw s r
    have h1 := nodeW_nonneg hw s r
    rcases hs.red_outcome hr with ⟨hC, hp, -, ⟨b, hb, hbt⟩ | ⟨hpn, hcn, hCe⟩⟩ |
        ⟨b, hpn, hcb, hacc, hC, hp, -⟩ | ⟨b, hbest, hcb, hbt, hC, hp, -⟩
    · have hA : ¬ Acc r := fun h => by have := h.1; rw [hb] at this; cases this
      rw [pot_of_matched (hp.trans hb), ite_eq_right hA]
      split_ifs <;> linarith
    · have hA : ¬ Acc r := fun h => by obtain ⟨-, b, hb, -⟩ := h; rw [hcn] at hb; cases hb
      have : I.pot (I.round s) w r = 0 := by
        rw [pot_of_unmatched (hp.trans hpn), hC, hCe, I.best_eq_none.2 rfl]
      rw [this, ite_eq_right hA]
      split_ifs <;> linarith
    · have hA : Acc r := ⟨hpn, b, hcb, hacc⟩
      rw [pot_of_matched hp, ite_eq_left hA]
      split_ifs <;> linarith
    · have hpot' : I.pot (I.round s) w r ≤ w s(r, b) := by
        rw [pot_of_unmatched hp, hC]; exact pot_le_of_erase hw (hs.C_sub r hr) hbest
      by_cases hpr : s.p r = none
      · have hA : ¬ Acc r := fun h => by
          obtain ⟨-, b', hb', hb't⟩ := h
          have : s.c r = some b := by rw [hs.red_unmatched r hr hpr, hbest]
          rw [this] at hb'; cases hb'; exact hbt hb't
        have hpot : I.pot s w r = w s(r, b) := by rw [pot_of_unmatched hpr, hbest]
        rw [ite_eq_right hA]
        split_ifs <;> linarith
      · obtain ⟨b₀, hpr⟩ := Option.ne_none_iff_exists'.1 hpr
        have hbb : b₀ = b := by
          rcases hcb with hcb | hcb
          · rw [hs.c_eq_none hr hpr] at hcb; cases hcb
          · rw [hpr] at hcb; cases hcb; rfl
        subst hbb
        have hA : ¬ Acc r := fun h => by have := h.1; rw [hpr] at this; cases this
        have hB : Brk r := ⟨b₀, hpr, hbt⟩
        rw [ite_eq_right hA, ite_eq_left hB, pot_of_matched hpr]
        have : nodeW s w r = w s(r, b₀) := by simp [nodeW, hpr]
        linarith
  have hmaps : ∀ r ∈ I.reds.filter Brk, φ r ∈ I.reds.filter Acc ∧
      (∃ b, s.p r = some b ∧ s.c (φ r) = some b) ∧ nodeW s w r ≤ I.pot s w (φ r) := by
    intro r hr
    obtain ⟨hr, b, hpb, hbt⟩ := mem_filter.1 hr
    have hr := I.mem_reds.1 hr
    have hbN := hs.p_mem r b hpb
    have hbb := blue_of_mem_red hbN hr
    obtain ⟨q, hq, hqr⟩ := hs.blue_of_mem_Q hbb (Or.inr (hs.p_symm r b hpb))
    have hφ : φ r = q := by simp only [φ, hpb, Option.getD_some, hq]
    have hqr' : I.rank b q < I.rank b r := hqr.resolve_left (by rintro rfl; exact hbt hq)
    have hqN := hs.blueTurn_p_mem hbb hq
    have hqred := red_of_mem_blue hqN hbb
    have hcq : s.c q = some b := by
      rcases hs.blue_choice hbb hq with h | h
      · exact h
      · have := hs.p_symm q b h
        rw [hs.p_symm r b hpb] at this; cases this; exact absurd hq hbt
    have hpq : s.p q = none := by
      rcases hpq : s.p q with _ | x
      · rfl
      · rw [hs.c_eq_none hqred hpq] at hcq; cases hcq
    rw [hφ]
    refine ⟨mem_filter.2 ⟨I.mem_reds.2 hqred, hpq, b, hcq, hq⟩, ⟨b, hpb, hcq⟩, ?_⟩
    have hbest : I.best q (s.C q) = some b := by rw [← hs.red_unmatched q hqred hpq, hcq]
    rw [pot_of_unmatched hpq, hbest]
    simp only [nodeW, hpb]
    have := hw.mono hqN (I.symm hbN) hqr'
    rwa [Sym2.eq_swap, Sym2.eq_swap (a := b)] at this
  have hinj : Set.InjOn φ (I.reds.filter Brk) := by
    intro r hr r' hr' h
    obtain ⟨-, ⟨b, hpb, hcb⟩, -⟩ := hmaps r hr
    obtain ⟨-, ⟨b', hpb', hcb'⟩, -⟩ := hmaps r' hr'
    rw [h, hcb'] at hcb; cases hcb
    have h1 := hs.p_symm r b hpb
    have h2 := hs.p_symm r' b hpb'
    rw [h1] at h2; cases h2; rfl
  have hsum := sum_le_sum key
  rw [sum_add_distrib, sum_add_distrib, ← sum_filter, ← sum_filter] at hsum
  have h2 : ∑ r ∈ I.reds.filter Brk, nodeW s w r ≤ ∑ r ∈ I.reds.filter Acc, I.pot s w r :=
    calc ∑ r ∈ I.reds.filter Brk, nodeW s w r
        ≤ ∑ r ∈ I.reds.filter Brk, I.pot s w (φ r) := sum_le_sum fun r hr => (hmaps r hr).2.2
      _ = ∑ q ∈ (I.reds.filter Brk).image φ, I.pot s w q := (sum_image hinj).symm
      _ ≤ ∑ q ∈ I.reds.filter Acc, I.pot s w q :=
        sum_le_sum_of_subset_of_nonneg (image_subset_iff.2 fun r hr => (hmaps r hr).1)
          fun _ _ _ => pot_nonneg hw s _
  rw [potR, potR]
  linarith

/-- **Lemma 3.** For `i ≥ 2`, `f_i(R) ≤ f_{i-1}(R)`. -/
theorem lemma_3 {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {i : ℕ} (hi : 2 ≤ i) :
    I.potR (I.run i) w ≤ I.potR (I.run (i - 1)) w := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [run_succ, Nat.add_sub_cancel]
  exact potR_round_le_potR (I.inv_run (by omega)) hw

/-! ### Lemma 4 -/

lemma lostW_run_one (w : Sym2 V → ℝ) : I.lostW (I.run 1) w = 0 := by
  refine sum_eq_zero fun r hr => ?_
  simp [lostAt, run_one_C, I.mem_reds.1 hr]

/-- **Lemma 4.** `w(L_i) ≥ (i - 1) f_i(R)` (the paper states it for `i ≥ 2`; it also holds for
`i = 1`). -/
theorem lemma_4 {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {i : ℕ} (hi : 1 ≤ i) :
    ((i : ℝ) - 1) * I.potR (I.run i) w ≤ I.lostW (I.run i) w := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [lostW_run_one]
    · have h2 := lemma_2 hw (i := i + 1) (by omega)
      have h3 := lemma_3 hw (i := i + 1) (by omega)
      rw [Nat.add_sub_cancel] at h2 h3
      have ih := ih hpos
      have hi1 : (0 : ℝ) ≤ (i : ℝ) - 1 := by
        have : (1 : ℝ) ≤ i := by exact_mod_cast hpos
        linarith
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left h3 hi1]

/-! ### Lemma 5 -/

/-- Lost edges counted at their blue endpoints. -/
lemma lostW_eq_sum_blues (s : State V) (w : Sym2 V → ℝ) :
    I.lostW s w = ∑ b ∈ I.blues, ∑ r ∈ (I.N b).filter (fun r => b ∉ s.C r), w s(r, b) := by
  unfold lostW lostAt
  refine sum_comm' fun r b => ?_
  simp only [mem_reds, mem_sdiff, mem_filter, mem_blues]
  constructor
  · rintro ⟨hr, hb, hbC⟩
    exact ⟨⟨I.symm hb, hbC⟩, blue_of_mem_red hb hr⟩
  · rintro ⟨⟨hr, hbC⟩, hb⟩
    exact ⟨red_of_mem_blue hr hb, I.symm hr, hbC⟩

/-- **Lemma 5.** For `i ≥ 1` (paper: `i ≥ 2`), if all degrees are at most `Δ`,
`w(L_i) ≤ (Δ - 1) w_i(B)`. -/
theorem lemma_5 {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {Δ : ℕ} (hΔ : ∀ v, (I.N v).card ≤ Δ)
    {i : ℕ} (hi : 1 ≤ i) : I.lostW (I.run i) w ≤ ((Δ - 1 : ℕ) : ℝ) * I.blueW (I.run i) w := by
  have hs := I.inv_run hi
  set s := I.run i
  rw [lostW_eq_sum_blues, blueW, mul_sum]
  refine sum_le_sum fun b hb => ?_
  have hb := I.mem_blues.1 hb
  set L := (I.N b).filter (fun r => b ∉ s.C r)
  rcases L.eq_empty_or_nonempty with hL | ⟨r₁, hr₁⟩
  · rw [hL, sum_empty]; exact mul_nonneg (Nat.cast_nonneg _) (nodeW_nonneg hw s b)
  obtain ⟨hr₁N, hr₁C⟩ := mem_filter.1 hr₁
  obtain ⟨r₀, h₀, -⟩ := hs.lost r₁ b (red_of_mem_blue hr₁N hb) (I.symm hr₁N) hr₁C
  have hnode : nodeW s w b = w s(b, r₀) := by simp [nodeW, h₀]
  have hle : ∀ r ∈ L, w s(r, b) ≤ nodeW s w b := by
    intro r hr
    obtain ⟨hrN, hrC⟩ := mem_filter.1 hr
    obtain ⟨r₀', h₀', hlt⟩ := hs.lost r b (red_of_mem_blue hrN hb) (I.symm hrN) hrC
    rw [h₀] at h₀'; cases h₀'
    rw [hnode, Sym2.eq_swap]
    exact hw.mono (hs.p_mem b r₀ h₀) hrN hlt
  have hcard : L.card ≤ Δ - 1 := by
    have hr₀N := hs.p_mem b r₀ h₀
    have hsub : L ⊆ (I.N b).erase r₀ := by
      intro r hr
      obtain ⟨hrN, hrC⟩ := mem_filter.1 hr
      refine mem_erase.2 ⟨?_, hrN⟩
      rintro rfl
      have := (hs.red_matched r b (red_of_mem_blue hrN hb) (hs.p_symm b r h₀)).2
      exact hrC (I.best_mem this)
    have := card_le_card hsub
    rw [card_erase_of_mem hr₀N] at this
    have := hΔ b
    omega
  calc ∑ r ∈ L, w s(r, b) ≤ L.card • nodeW s w b := sum_le_card_nsmul _ _ _ hle
    _ = (L.card : ℝ) * nodeW s w b := nsmul_eq_mul _ _
    _ ≤ ((Δ - 1 : ℕ) : ℝ) * nodeW s w b :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (nodeW_nonneg hw s b)

/-! ### Lemma 6 -/

/-- **Lemma 6** (with the missing hypothesis `i ≥ 2`). For `γ > 0` and `i ≥ 1 + (Δ - 1)/γ`,
`f_i(R) ≤ γ w_i(B)`. -/
theorem lemma_6 {w : Sym2 V → ℝ} (hw : I.RespectsPrefs w) {Δ : ℕ} (hΔ : ∀ v, (I.N v).card ≤ Δ)
    {γ : ℝ} (hγ : 0 < γ) {i : ℕ} (hi2 : 2 ≤ i) (hi : 1 + ((Δ - 1 : ℕ) : ℝ) / γ ≤ i) :
    I.potR (I.run i) w ≤ γ * I.blueW (I.run i) w := by
  have h4 := lemma_4 hw (i := i) (by omega)
  have h5 := lemma_5 hw hΔ (i := i) (by omega)
  have hW := blueW_nonneg hw (I.run i)
  have hf := potR_nonneg hw (I.run i)
  have hi1 : (1 : ℝ) ≤ (i : ℝ) - 1 := by
    have : (2 : ℝ) ≤ i := by exact_mod_cast hi2
    linarith
  have hΔγ : ((Δ - 1 : ℕ) : ℝ) ≤ γ * ((i : ℝ) - 1) := by
    have := (div_le_iff₀ hγ).1 (by linarith : ((Δ - 1 : ℕ) : ℝ) / γ ≤ (i : ℝ) - 1)
    linarith
  have h6 := mul_le_mul_of_nonneg_right hΔγ hW
  have h7 : ((i : ℝ) - 1) * I.potR (I.run i) w ≤ ((i : ℝ) - 1) * (γ * I.blueW (I.run i) w) := by
    nlinarith
  exact le_of_mul_le_mul_left h7 (by linarith)

end Bicoloured

end Podc.TruncatedGaleShapley
