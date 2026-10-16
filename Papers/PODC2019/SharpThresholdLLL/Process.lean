import Papers.PODC2019.SharpThresholdLLL.Basic
import Papers.PODC2019.SharpThresholdLLL.Representable

/-!
# The sequential variable-fixing process (Theorems 1.1 and 1.3, Lemma 3.2)

The bookkeeping of Section 3.1. Every ordered pair `(t, u)` of adjacent events (an edge `{t,u}`
of the dependency graph, seen from `t`) carries a value `φ t u`. Property `P*`
(Definition 3.1, `PStar`) says that
1. `φ t u ≥ 0` and `φ t u + φ u t ≤ 2` on every edge, and
2. `Pr[E_v | fixed variables] ≤ p · ∏_{u ∈ N(v)} φ v u` for every event `v`.

A step of the process (`Step`) fixes one unfixed variable `X_j` to a value of positive
probability. It changes `φ` only on the edges inside the hyperedge `evs j` of `X_j`. It must
re-establish `P*` *locally*, for the events of `evs j` and the edges among them. Every
condition in `Step` involves only `X_j`, its events, and their incident edges. This is the
locality claimed by the paper.

* `step_pstar`: a step preserves `P*` globally.
* `exists_step` (Lemma 3.2, generalised): if `P*` holds, then **every** unfixed variable `X_j`
  can be fixed by a step, provided the hyperedge `evs j` has the *fixing property*
  `FixingProperty`. The fixing property is the averaging statement of Lemma 3.9. We prove it
  for hyperedges of size `≤ 3` (`fixingProperty_of_card_le_three`).
* `process_correct`: from the all-ones initial state, every reachable state has a step for
  every unfixed variable, and every reachable state with all variables fixed avoids all bad
  events, provided `Pr[E_v] ≤ p` and `p · 2^d < 1`. Since this holds for *every* reachable state
  and *every* unfixed variable, the order may be chosen by an adaptive adversary.
* `theorem_1_1` (rank `≤ 2`) and `theorem_1_3` (rank `≤ 3`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace SharpThresholdLLL

/-! ## Representability on a hyperedge -/

section RepOn

variable {V : Type} [DecidableEq V]

/-- `s` (restricted to the hyperedge `T`) is *representable on `T`*: there are values `ψ t u`
on the ordered pairs of distinct elements of `T` with `ψ ≥ 0` and `ψ t u + ψ u t ≤ 2`, such that
`s t ≤ ∏_{u ∈ T, u ≠ t} ψ t u` for each `t ∈ T`. For `|T| = 3` this is Definition 3.3
(`repOn_three_iff`). -/
def RepOn (T : Finset V) (s : V → ℝ) : Prop :=
  ∃ ψ : V → V → ℝ, (∀ t ∈ T, ∀ u ∈ T, t ≠ u → 0 ≤ ψ t u ∧ ψ t u + ψ u t ≤ 2) ∧
    ∀ t ∈ T, s t ≤ ∏ u ∈ T.erase t, ψ t u

/-- The *fixing property* of a hyperedge `T`. Let a distribution `w` with positive weights on
the values `Ω` of a variable be given. If the `w`-average of nonnegative vectors `s y` is
dominated on `T` by a vector `a` representable on `T`, then some `s y` is representable on `T`.
For `|T| = 3` this is Lemma 3.9 in contrapositive form, and it follows from `S_rep` being
incurved. The paper conjectures it for all sizes (Conjecture 1.5). -/
def FixingProperty (T : Finset V) : Prop :=
  ∀ (β : Type) (Ω : Finset β) (w : β → ℝ) (s : β → V → ℝ) (a : V → ℝ),
    (∀ y ∈ Ω, 0 < w y) → ∑ y ∈ Ω, w y = 1 → (∀ y ∈ Ω, ∀ t ∈ T, 0 ≤ s y t) →
    (∀ t ∈ T, ∑ y ∈ Ω, w y * s y t ≤ a t) → RepOn T a → ∃ y ∈ Ω, RepOn T (s y)

lemma repOn_empty (s : V → ℝ) : RepOn ∅ s := ⟨fun _ _ => 0, by simp, by simp⟩

lemma repOn_singleton_iff (t : V) (s : V → ℝ) : RepOn {t} s ↔ s t ≤ 1 := by
  constructor
  · rintro ⟨ψ, -, h⟩; simpa using h t (mem_singleton_self t)
  · intro h; exact ⟨fun _ _ => 0, by simp, by simpa using h⟩

lemma repOn_pair_iff {t u : V} (htu : t ≠ u) (s : V → ℝ) (hs : 0 ≤ s t ∧ 0 ≤ s u) :
    RepOn {t, u} s ↔ s t + s u ≤ 2 := by
  have e1 : ({t, u} : Finset V).erase t = {u} := by
    rw [erase_insert (by simpa using htu)]
  have e2 : ({t, u} : Finset V).erase u = {t} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact h2
      · exact absurd h2 h1
    · rintro rfl; exact ⟨htu, Or.inl rfl⟩
  constructor
  · rintro ⟨ψ, hψ, h⟩
    have h1 := h t (by simp); have h2 := h u (by simp)
    rw [e1, prod_singleton] at h1; rw [e2, prod_singleton] at h2
    have := (hψ t (by simp) u (by simp) htu).2
    linarith
  · intro h
    refine ⟨fun x _ => if x = t then s t else s u, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy] at hxy ⊢
      · exact absurd rfl hxy
      · simp only [Ne.symm htu, ↓reduceIte]; exact ⟨hs.1, h⟩
      · simp only [Ne.symm htu, ↓reduceIte]; exact ⟨hs.2, by linarith⟩
      · exact absurd rfl hxy
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [e1, prod_singleton]; simp
      · rw [e2, prod_singleton]; simp [Ne.symm htu]

lemma repOn_three_iff {t₁ t₂ t₃ : V} (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃)
    (s : V → ℝ) : RepOn {t₁, t₂, t₃} s ↔ RepLe (s t₁) (s t₂) (s t₃) := by
  have e1 : ({t₁, t₂, t₃} : Finset V).erase t₁ = {t₂, t₃} := by
    rw [erase_insert]; simp [h12, h13]
  have e2 : ({t₁, t₂, t₃} : Finset V).erase t₂ = {t₁, t₃} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, h | h | h⟩
      · exact Or.inl h
      · exact absurd h hx
      · exact Or.inr h
    · rintro (rfl | rfl)
      · exact ⟨h12, Or.inl rfl⟩
      · exact ⟨Ne.symm h23, Or.inr (Or.inr rfl)⟩
  have e3 : ({t₁, t₂, t₃} : Finset V).erase t₃ = {t₁, t₂} := by
    ext x; simp only [mem_erase, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hx, h | h | h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hx
    · rintro (rfl | rfl)
      · exact ⟨h13, Or.inl rfl⟩
      · exact ⟨h23, Or.inr (Or.inl rfl)⟩
  constructor
  · rintro ⟨ψ, hψ, h⟩
    have m1 : t₁ ∈ ({t₁, t₂, t₃} : Finset V) := by simp
    have m2 : t₂ ∈ ({t₁, t₂, t₃} : Finset V) := by simp
    have m3 : t₃ ∈ ({t₁, t₂, t₃} : Finset V) := by simp
    have p12 := hψ t₁ m1 t₂ m2 h12
    have p21 := hψ t₂ m2 t₁ m1 (Ne.symm h12)
    have p13 := hψ t₁ m1 t₃ m3 h13
    have p31 := hψ t₃ m3 t₁ m1 (Ne.symm h13)
    have p23 := hψ t₂ m2 t₃ m3 h23
    have p32 := hψ t₃ m3 t₂ m2 (Ne.symm h23)
    have s1 := h t₁ m1
    have s2 := h t₂ m2
    have s3 := h t₃ m3
    rw [e1, prod_pair h23] at s1
    rw [e2, prod_pair h13] at s2
    rw [e3, prod_pair h12] at s3
    refine ⟨ψ t₁ t₂, ψ t₁ t₃, ψ t₂ t₃, ⟨p12.1, by linarith⟩, ⟨p13.1, by linarith⟩,
      ⟨p23.1, by linarith⟩, s1, ?_, ?_⟩
    · calc s t₂ ≤ ψ t₂ t₁ * ψ t₂ t₃ := s2
        _ ≤ (2 - ψ t₁ t₂) * ψ t₂ t₃ := mul_le_mul_of_nonneg_right (by linarith) p23.1
    · calc s t₃ ≤ ψ t₃ t₁ * ψ t₃ t₂ := s3
        _ ≤ (2 - ψ t₁ t₃) * (2 - ψ t₂ t₃) :=
          mul_le_mul (by linarith) (by linarith) p32.1 (by linarith)
  · rintro ⟨X, Y, Z, hX, hY, hZ, h1, h2, h3⟩
    let ψ : V → V → ℝ := fun x y =>
      if x = t₁ then (if y = t₂ then X else Y)
      else if x = t₂ then (if y = t₁ then 2 - X else Z)
      else (if y = t₁ then 2 - Y else 2 - Z)
    have q12 : ψ t₁ t₂ = X := by simp [ψ]
    have q13 : ψ t₁ t₃ = Y := by simp [ψ, Ne.symm h23]
    have q21 : ψ t₂ t₁ = 2 - X := by simp [ψ, Ne.symm h12]
    have q23 : ψ t₂ t₃ = Z := by simp [ψ, Ne.symm h12, Ne.symm h13]
    have q31 : ψ t₃ t₁ = 2 - Y := by simp [ψ, Ne.symm h13, Ne.symm h23]
    have q32 : ψ t₃ t₂ = 2 - Z := by simp [ψ, Ne.symm h13, Ne.symm h23, Ne.symm h12]
    refine ⟨ψ, ?_, ?_⟩
    · intro x hx y hy hxy
      simp only [mem_insert, mem_singleton] at hx hy
      obtain ⟨hX0, hX2⟩ := hX; obtain ⟨hY0, hY2⟩ := hY; obtain ⟨hZ0, hZ2⟩ := hZ
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
        first
        | exact absurd rfl hxy
        | (simp only [q12, q13, q21, q23, q31, q32]; constructor <;> linarith)
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · rw [e1, prod_pair h23, q12, q13]; exact h1
      · rw [e2, prod_pair h13, q21, q23]; exact h2
      · rw [e3, prod_pair h12, q31, q32]; exact h3

/-- Averaging for a linear constraint: if `Σ w y * F y ≤ c` with `w` a positive probability
distribution on `Ω`, then some `F y ≤ c`. -/
lemma exists_le_of_avg_le {β : Type} {Ω : Finset β} {w F : β → ℝ} {c : ℝ}
    (hw : ∀ y ∈ Ω, 0 < w y) (hsum : ∑ y ∈ Ω, w y = 1) (h : ∑ y ∈ Ω, w y * F y ≤ c) :
    ∃ y ∈ Ω, F y ≤ c := by
  have hne : Ω.Nonempty := by
    by_contra h'; rw [not_nonempty_iff_eq_empty] at h'; simp [h'] at hsum
  have : ∑ y ∈ Ω, w y * F y ≤ ∑ y ∈ Ω, w y * c := by rwa [← sum_mul, hsum, one_mul]
  obtain ⟨y, hy, hle⟩ := exists_le_of_sum_le hne this
  exact ⟨y, hy, le_of_mul_le_mul_left hle (hw y hy)⟩

/-- **The fixing property for hyperedges of size at most 3.** Size `≤ 2` is linearity of
expectation (the argument of Section 2). Size `3` is Lemma 3.9 together with Lemma 3.7. -/
theorem fixingProperty_of_card_le_three (T : Finset V) (hT : T.card ≤ 3) :
    FixingProperty T := by
  intro β Ω w s a hw hsum hs havg hrep
  have hne : Ω.Nonempty := by
    by_contra h'; rw [not_nonempty_iff_eq_empty] at h'; simp [h'] at hsum
  have ha0 : ∀ t ∈ T, 0 ≤ a t := fun t ht =>
    (sum_nonneg fun y hy => mul_nonneg (hw y hy).le (hs y hy t ht)).trans (havg t ht)
  interval_cases hc : T.card
  · rw [card_eq_zero] at hc; subst hc
    obtain ⟨y, hy⟩ := hne
    exact ⟨y, hy, repOn_empty _⟩
  · obtain ⟨t, rfl⟩ := card_eq_one.1 hc
    rw [repOn_singleton_iff] at hrep
    obtain ⟨y, hy, hle⟩ := exists_le_of_avg_le hw hsum ((havg t (by simp)).trans hrep)
    exact ⟨y, hy, (repOn_singleton_iff t _).2 hle⟩
  · obtain ⟨t, u, htu, rfl⟩ := card_eq_two.1 hc
    rw [repOn_pair_iff htu a ⟨ha0 t (by simp), ha0 u (by simp)⟩] at hrep
    have : ∑ y ∈ Ω, w y * (s y t + s y u) ≤ 2 := by
      simp only [mul_add, sum_add_distrib]
      linarith [havg t (by simp), havg u (by simp)]
    obtain ⟨y, hy, hle⟩ := exists_le_of_avg_le hw hsum this
    exact ⟨y, hy, (repOn_pair_iff htu _ ⟨hs y hy t (by simp), hs y hy u (by simp)⟩).2 hle⟩
  · obtain ⟨t₁, t₂, t₃, h12, h13, h23, rfl⟩ := card_eq_three.1 hc
    rw [repOn_three_iff h12 h13 h23] at hrep
    have m1 : t₁ ∈ ({t₁, t₂, t₃} : Finset V) := by simp
    have m2 : t₂ ∈ ({t₁, t₂, t₃} : Finset V) := by simp
    have m3 : t₃ ∈ ({t₁, t₂, t₃} : Finset V) := by simp
    have h4 := hval_le_four_of_repLe (ha0 t₁ m1) (ha0 t₂ m2) (ha0 t₃ m3) hrep
    obtain ⟨y, hy, hle⟩ := exists_hval_le_four Ω w (fun y => s y t₁) (fun y => s y t₂)
      (fun y => s y t₃) hw hsum (fun y hy => hs y hy t₁ m1) (fun y hy => hs y hy t₂ m2)
      (fun y hy => hs y hy t₃ m3) (havg t₁ m1) (havg t₂ m2) (havg t₃ m3) h4
    refine ⟨y, hy, (repOn_three_iff h12 h13 h23 _).2 ?_⟩
    have := (representable_iff (a := s y t₁) (b := s y t₂) (c := s y t₃)).2
      ⟨hs y hy t₁ m1, hs y hy t₂ m2, hs y hy t₃ m3, hle⟩
    exact repLe_of_representable this

end RepOn

/-! ## The process -/

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)] {V : Type} [Fintype V] [DecidableEq V]

/-- A state of the process: the partial assignment and the bookkeeping values `φ`. -/
structure State (ι : Type) (α : ι → Type) (V : Type) where
  σ : ∀ i, Option (α i)
  φ : V → V → ℝ

namespace Instance

variable (I : Instance ι α V)

/-- **Definition 3.1 (property `P*`).** -/
def PStar (p : ℝ) (s : State ι α V) : Prop :=
  (∀ u v, v ∈ I.dep u → 0 ≤ s.φ u v ∧ s.φ u v + s.φ v u ≤ 2) ∧
    ∀ v, I.condProb s.σ v ≤ p * ∏ u ∈ I.dep v, s.φ v u

/-- The initial state: nothing fixed, all bookkeeping values `1`. -/
def init : State ι α V := ⟨Instance.empty, fun _ _ => 1⟩

/-- One step of the process: fix the unfixed variable `X_j` to a value `a` with
`Pr[X_j = a] > 0`, and update `φ` on the edges inside the hyperedge `evs j` only, so that
`P*` holds again at the events of `evs j`. -/
def Step (p : ℝ) (j : ι) (s s' : State ι α V) : Prop :=
  s.σ j = none ∧ (∃ a, 0 < I.prob j a ∧ s'.σ = Function.update s.σ j (some a)) ∧
    (∀ u v, ¬ (u ∈ I.evs j ∧ v ∈ I.evs j) → s'.φ u v = s.φ u v) ∧
    (∀ u ∈ I.evs j, ∀ v ∈ I.evs j, u ≠ v → 0 ≤ s'.φ u v ∧ s'.φ u v + s'.φ v u ≤ 2) ∧
    ∀ t ∈ I.evs j, I.condProb s'.σ t ≤ p * ∏ u ∈ I.dep t, s'.φ t u

/-- States reachable from `init` by steps (fixing variables in any order). -/
def Reachable (p : ℝ) : State ι α V → Prop :=
  Relation.ReflTransGen (fun s s' => ∃ j, I.Step p j s s') (init : State ι α V)

lemma init_pstar {p : ℝ} (hp : ∀ v, I.pr v ≤ p) : I.PStar p (init : State ι α V) := by
  refine ⟨fun u v _ => ⟨by simp [init], by simp [init]; norm_num⟩, fun v => ?_⟩
  simpa [init, pr] using hp v

/-- A step preserves `P*` (the conditions outside the hyperedge are untouched). -/
theorem step_pstar {p : ℝ} {j : ι} {s s' : State ι α V} (hs : I.PStar p s)
    (hstep : I.Step p j s s') : I.PStar p s' := by
  obtain ⟨hj, ⟨a, -, hσ⟩, hframe, hpair, hloc⟩ := hstep
  refine ⟨fun u v huv => ?_, fun v => ?_⟩
  · by_cases h : u ∈ I.evs j ∧ v ∈ I.evs j
    · exact hpair u h.1 v h.2 (fun e => I.not_mem_dep_self u (e ▸ huv))
    · rw [hframe u v h, hframe v u (fun h' => h ⟨h'.2, h'.1⟩)]
      exact hs.1 u v huv
  · by_cases hv : v ∈ I.evs j
    · exact hloc v hv
    · have hjv : j ∉ I.vbl v := fun h => hv (I.mem_evs.2 h)
      rw [hσ, I.condProb_fix_of_not_mem s.σ hj hjv a]
      have : ∏ u ∈ I.dep v, s'.φ v u = ∏ u ∈ I.dep v, s.φ v u :=
        prod_congr rfl fun u _ => hframe v u (fun h => hv h.1)
      rw [this]; exact hs.2 v

/-- In a state satisfying `P*` with all variables fixed to `x`, no bad event occurs, provided
`#N(v) ≤ d` and `p · 2^d < 1`. -/
theorem not_bad_of_pstar {p : ℝ} {d : ℕ} {s : State ι α V} (hs : I.PStar p s)
    (x : ∀ i, α i) (hx : ∀ i, s.σ i = some (x i)) (hd : ∀ v, (I.dep v).card ≤ d)
    (hpd : p * 2 ^ d < 1) (v : V) : ¬ I.bad v x := by
  classical
  intro hbad
  have h1 := hs.2 v
  rw [I.condProb_total s.σ x hx v] at h1; simp only [hbad, ↓reduceIte] at h1
  have hφ : ∀ u ∈ I.dep v, 0 ≤ s.φ v u ∧ s.φ v u ≤ 2 := by
    intro u hu
    have a := hs.1 v u hu
    have b := hs.1 u v (I.dep_symm.1 hu)
    exact ⟨a.1, by linarith [b.1]⟩
  have hprod0 : 0 ≤ ∏ u ∈ I.dep v, s.φ v u := prod_nonneg fun u hu => (hφ u hu).1
  have hprod : ∏ u ∈ I.dep v, s.φ v u ≤ 2 ^ d := by
    calc ∏ u ∈ I.dep v, s.φ v u ≤ ∏ _u ∈ I.dep v, (2 : ℝ) :=
          prod_le_prod₀ (fun u hu => (hφ u hu).1) (fun u hu => (hφ u hu).2)
      _ = 2 ^ (I.dep v).card := by rw [prod_const]
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (hd v)
  rcases le_or_gt 0 p with hp | hp
  · have : p * ∏ u ∈ I.dep v, s.φ v u ≤ p * 2 ^ d := mul_le_mul_of_nonneg_left hprod hp
    linarith
  · have : p * ∏ u ∈ I.dep v, s.φ v u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp.le hprod0
    linarith

/-- **Lemma 3.2 (Variable Fixing Lemma), generalised to any hyperedge with the fixing
property.** If `P*` holds and `X_j` is unfixed, there is a step fixing `X_j`. -/
theorem exists_step {p : ℝ} {j : ι} {s : State ι α V} (hs : I.PStar p s) (hj : s.σ j = none)
    (hfix : FixingProperty (I.evs j)) (hp0 : ∀ _ : V, 0 ≤ p) : ∃ s', I.Step p j s s' := by
  classical
  set T := I.evs j with hT
  set Ω : Finset (α j) := univ.filter fun b => 0 < I.prob j b
  have hΩsum : ∀ F : α j → ℝ, ∑ b ∈ Ω, I.prob j b * F b = ∑ b, I.prob j b * F b := by
    intro F
    apply sum_subset (filter_subset _ _)
    intro b _ hb
    simp only [mem_filter, mem_univ, true_and, not_lt] at hb
    rw [le_antisymm hb (I.prob_nonneg j b), zero_mul]
  have hw : ∀ b ∈ Ω, 0 < I.prob j b := fun b hb => (mem_filter.1 hb).2
  have hwsum : ∑ b ∈ Ω, I.prob j b = 1 := by
    have := hΩsum (fun _ => 1); simp only [mul_one] at this; rw [this, I.prob_sum]
  -- notation
  let Pt : V → ℝ := fun t => I.condProb s.σ t
  let r : α j → V → ℝ := fun b t => I.condProb (Function.update s.σ j (some b)) t
  let a : V → ℝ := fun t => ∏ u ∈ T.erase t, s.φ t u
  let K : V → ℝ := fun t => p * ∏ u ∈ I.dep t \ T.erase t, s.φ t u
  let sv : α j → V → ℝ := fun b t => if Pt t = 0 then 0 else a t * r b t / Pt t
  have hsub : ∀ t ∈ T, T.erase t ⊆ I.dep t := by
    intro t ht u hu
    obtain ⟨hut, hu⟩ := mem_erase.1 hu
    exact I.mem_dep_of_mem_evs hu ht hut
  have hφ0 : ∀ t u, u ∈ I.dep t → 0 ≤ s.φ t u := fun t u h => (hs.1 t u h).1
  have ha0 : ∀ t ∈ T, 0 ≤ a t := fun t ht =>
    prod_nonneg fun u hu => hφ0 t u (hsub t ht hu)
  have hK0 : ∀ t ∈ T, 0 ≤ K t := fun t _ =>
    mul_nonneg (hp0 t) (prod_nonneg fun u hu => hφ0 t u (mem_sdiff.1 hu).1)
  have hPK : ∀ t ∈ T, Pt t ≤ K t * a t := by
    intro t ht
    have := hs.2 t
    rw [← prod_sdiff (hsub t ht), ← mul_assoc] at this
    exact this
  have hr0 : ∀ b t, 0 ≤ r b t := fun b t => I.condProb_nonneg _ t
  have hPt0 : ∀ t, 0 ≤ Pt t := fun t => I.condProb_nonneg _ t
  have htotal : ∀ t, ∑ b ∈ Ω, I.prob j b * r b t = Pt t := fun t => by
    rw [hΩsum]; exact I.sum_condProb_fix s.σ hj t
  have hsv0 : ∀ b, ∀ t ∈ T, 0 ≤ sv b t := by
    intro b t ht
    simp only [sv]; split
    · exact le_rfl
    · exact div_nonneg (mul_nonneg (ha0 t ht) (hr0 b t)) (hPt0 t)
  -- the average of `sv` is dominated by `a`
  have havg : ∀ t ∈ T, ∑ b ∈ Ω, I.prob j b * sv b t ≤ a t := by
    intro t ht
    by_cases hP : Pt t = 0
    · simp only [sv, hP, ↓reduceIte, mul_zero, sum_const_zero]; exact ha0 t ht
    · simp only [sv, hP, ↓reduceIte]
      have : ∑ b ∈ Ω, I.prob j b * (a t * r b t / Pt t) =
          a t / Pt t * ∑ b ∈ Ω, I.prob j b * r b t := by
        rw [mul_sum]; apply sum_congr rfl; intro b _; ring
      rw [this, htotal t, div_mul_cancel₀ _ hP]
  -- the current bookkeeping is representable on `T`
  have hrepa : RepOn T a := by
    refine ⟨s.φ, fun t ht u hu htu => hs.1 t u (I.mem_dep_of_mem_evs hu ht (Ne.symm htu)),
      fun t _ => le_rfl⟩
  obtain ⟨b, hb, ψ, hψ, hψs⟩ := hfix (α j) Ω (fun b => I.prob j b) sv a hw hwsum
    (fun b _ t ht => hsv0 b t ht) havg hrepa
  -- the new state
  let s' : State ι α V := ⟨Function.update s.σ j (some b),
    fun u v => if u ∈ T ∧ v ∈ T then ψ u v else s.φ u v⟩
  refine ⟨s', hj, ⟨b, hw b hb, rfl⟩, fun u v huv => by simp only [s', show ¬(u ∈ T ∧ v ∈ T) from huv, ↓reduceIte], ?_, ?_⟩
  · intro u hu v hv huv
    have hu' : u ∈ T := hu
    have hv' : v ∈ T := hv
    simp only [s', hu', hv', and_self, ↓reduceIte]
    exact hψ u hu v hv huv
  · intro t ht
    have ht' : t ∈ T := ht
    -- `r b t ≤ K t * sv b t`
    have h1 : r b t ≤ K t * sv b t := by
      by_cases hP : Pt t = 0
      · have hz := (sum_eq_zero_iff_of_nonneg (fun b hb => mul_nonneg (hw b hb).le
          (hr0 b t))).1 ((htotal t).trans hP) b hb
        rcases mul_eq_zero.1 hz with h | h
        · exact absurd h (hw b hb).ne'
        · simp only [sv, hP, ↓reduceIte, mul_zero]; exact h.le
      · have hPpos : 0 < Pt t := lt_of_le_of_ne (hPt0 t) (Ne.symm hP)
        simp only [sv, hP, ↓reduceIte]
        rw [mul_div_assoc', ← mul_assoc, le_div_iff₀ hPpos]
        calc r b t * Pt t ≤ r b t * (K t * a t) := mul_le_mul_of_nonneg_left (hPK t ht) (hr0 b t)
          _ = K t * a t * r b t := by ring
    have h2 : K t * sv b t ≤ K t * ∏ u ∈ T.erase t, ψ t u :=
      mul_le_mul_of_nonneg_left (hψs t ht) (hK0 t ht)
    have h3 : p * ∏ u ∈ I.dep t, s'.φ t u = K t * ∏ u ∈ T.erase t, ψ t u := by
      rw [← prod_sdiff (hsub t ht), ← mul_assoc]
      congr 1
      · simp only [K]; congr 1
        apply prod_congr rfl
        intro u hu
        obtain ⟨hu1, hu2⟩ := mem_sdiff.1 hu
        have huT : u ∉ T := by
          intro huT
          exact hu2 (mem_erase.2 ⟨fun e => I.not_mem_dep_self t (e ▸ hu1), huT⟩)
        simp [s', huT]
      · apply prod_congr rfl
        intro u hu
        simp [s', ht', (mem_erase.1 hu).2]
    show r b t ≤ _
    rw [h3]; exact h1.trans h2

/-- **Lemma 3.2 (Variable Fixing Lemma)** for rank `≤ 3`: if `(G, φ)` satisfies `P*` and `X_j`
is not fixed, then `X_j` can be fixed to a value, and `φ` changed only on the edges inside the
hyperedge of `X_j`, such that `P*` still holds. -/
theorem variable_fixing_lemma {p : ℝ} {j : ι} {s : State ι α V} (hs : I.PStar p s)
    (hj : s.σ j = none) (hrank : (I.evs j).card ≤ 3) (hp0 : 0 ≤ p) :
    ∃ s', I.Step p j s s' ∧ I.PStar p s' := by
  obtain ⟨s', h⟩ := I.exists_step hs hj (fixingProperty_of_card_le_three _ hrank) fun _ => hp0
  exact ⟨s', h, I.step_pstar hs h⟩

/-- **The general theorem.** Suppose every hyperedge has the fixing property, `Pr[E_v] ≤ p`,
every event has at most `d` neighbours, and `p · 2^d < 1`. Then:
1. in every state reachable by the process, **every** unfixed variable can be fixed by a step
   (so the variable order may be chosen by an adaptive adversary);
2. every reachable state in which all variables are fixed avoids all bad events. -/
theorem process_correct {p : ℝ} {d : ℕ} (hfix : ∀ j, FixingProperty (I.evs j))
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1) :
    (∀ s, I.Reachable p s → ∀ j, s.σ j = none → ∃ s', I.Step p j s s') ∧
      (∀ s, I.Reachable p s → ∀ x : ∀ i, α i, (∀ i, s.σ i = some (x i)) →
        ∀ v, ¬ I.bad v x) := by
  have hp0 : ∀ _ : V, 0 ≤ p := fun v => (I.condProb_nonneg _ v).trans (hp v)
  have hinv : ∀ s, I.Reachable p s → I.PStar p s := by
    intro s hs
    induction hs with
    | refl => exact I.init_pstar hp
    | tail _ hstep ih => obtain ⟨j, hj⟩ := hstep; exact I.step_pstar ih hj
  exact ⟨fun s hs j hj => I.exists_step (hinv s hs) hj (hfix j) hp0,
    fun s hs x hx v => I.not_bad_of_pstar (hinv s hs) x hx hd hpd v⟩

/-- Number of unfixed variables. -/
def numUnfixed (σ : ∀ i, Option (α i)) : ℕ := (univ.filter fun i => σ i = none).card

/-- Every run can be completed: from any reachable state, steps lead to a reachable state with
all variables fixed (in at most `numUnfixed` steps, each fixing a new variable). -/
theorem exists_complete {p : ℝ} (hstep : ∀ s, I.Reachable p s → ∀ j, s.σ j = none →
    ∃ s', I.Step p j s s') :
    ∀ s, I.Reachable p s → ∃ s', I.Reachable p s' ∧ ∀ i, s'.σ i ≠ none := by
  intro s hs
  generalize hn : numUnfixed s.σ = n
  induction n generalizing s with
  | zero =>
    refine ⟨s, hs, fun i hi => ?_⟩
    have : i ∈ univ.filter fun i => s.σ i = none := by simp [hi]
    rw [numUnfixed, card_eq_zero] at hn
    simp [hn] at this
  | succ n ih =>
    have : (univ.filter fun i => s.σ i = none).Nonempty := by
      rw [← card_pos]; rw [numUnfixed] at hn; omega
    obtain ⟨j, hj⟩ := this
    have hj' : s.σ j = none := (mem_filter.1 hj).2
    obtain ⟨s', hst⟩ := hstep s hs j hj'
    have hs' : I.Reachable p s' := Relation.ReflTransGen.tail hs ⟨j, hst⟩
    apply ih s' hs'
    obtain ⟨-, ⟨a, -, hσ⟩, -⟩ := hst
    have : (univ.filter fun i => s'.σ i = none) = (univ.filter fun i => s.σ i = none).erase j := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_erase, hσ]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [numUnfixed, this, card_erase_of_mem hj]
    rw [numUnfixed] at hn; omega

/-- The process yields an assignment avoiding all bad events (the LLL conclusion). -/
theorem exists_good_assignment {p : ℝ} {d : ℕ} (hfix : ∀ j, FixingProperty (I.evs j))
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1) :
    ∃ x : ∀ i, α i, ∀ v, ¬ I.bad v x := by
  obtain ⟨h1, h2⟩ := I.process_correct hfix hp hd hpd
  obtain ⟨s, hs, hall⟩ := I.exists_complete h1 init Relation.ReflTransGen.refl
  let x : ∀ i, α i := fun i => (s.σ i).get (Option.ne_none_iff_isSome.1 (hall i))
  exact ⟨x, h2 s hs x (fun i => by simp [x])⟩

/-- **Theorem 1.1.** Rank `≤ 2` (every variable affects at most two events) and `p < 2^{-d}`:
the sequential, local, deterministic process works for any (adaptive) order of the variables
and yields an assignment avoiding all bad events. Unlike the paper, several variables may be
shared by the same pair of events (the paper merges them first). -/
theorem theorem_1_1 {p : ℝ} {d : ℕ} (hrank : ∀ j, (I.evs j).card ≤ 2)
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1) :
    (∀ s, I.Reachable p s → ∀ j, s.σ j = none → ∃ s', I.Step p j s s') ∧
      (∀ s, I.Reachable p s → ∀ x : ∀ i, α i, (∀ i, s.σ i = some (x i)) →
        ∀ v, ¬ I.bad v x) ∧
      ∃ x : ∀ i, α i, ∀ v, ¬ I.bad v x := by
  have hfix : ∀ j, FixingProperty (I.evs j) := fun j =>
    fixingProperty_of_card_le_three _ ((hrank j).trans (by norm_num))
  exact ⟨(I.process_correct hfix hp hd hpd).1, (I.process_correct hfix hp hd hpd).2,
    I.exists_good_assignment hfix hp hd hpd⟩

/-- **Theorem 1.3.** Rank `≤ 3` (every variable affects at most three events) and
`p · 2^d < 1`: the sequential, local, deterministic process works for any (adaptive) order of
the variables and yields an assignment avoiding all bad events. -/
theorem theorem_1_3 {p : ℝ} {d : ℕ} (hrank : ∀ j, (I.evs j).card ≤ 3)
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1) :
    (∀ s, I.Reachable p s → ∀ j, s.σ j = none → ∃ s', I.Step p j s s') ∧
      (∀ s, I.Reachable p s → ∀ x : ∀ i, α i, (∀ i, s.σ i = some (x i)) →
        ∀ v, ¬ I.bad v x) ∧
      ∃ x : ∀ i, α i, ∀ v, ¬ I.bad v x := by
  have hfix : ∀ j, FixingProperty (I.evs j) := fun j => fixingProperty_of_card_le_three _ (hrank j)
  exact ⟨(I.process_correct hfix hp hd hpd).1, (I.process_correct hfix hp hd hpd).2,
    I.exists_good_assignment hfix hp hd hpd⟩

/-! ## The rule of Section 2 -/

/-- The increase factor `Inc(t, b) = Pr[E_t | θ, X_j = b] / Pr[E_t | θ]` (`0` if the
denominator vanishes). -/
noncomputable def Inc (σ : ∀ i, Option (α i)) (j : ι) (b : α j) (t : V) : ℝ :=
  if I.condProb σ t = 0 then 0
  else I.condProb (Function.update σ j (some b)) t / I.condProb σ t

/-- **The claim in the proof of Theorem 1.1.** For an unfixed variable `X_j` and two events
`u, v`, some value `b` of positive probability has `Inc(u, b) + Inc(v, b) ≤ 2`. -/
theorem exists_inc_add_inc_le_two (σ : ∀ i, Option (α i)) {j : ι} (hj : σ j = none)
    (u v : V) : ∃ b, 0 < I.prob j b ∧ I.Inc σ j b u + I.Inc σ j b v ≤ 2 := by
  classical
  set Ω : Finset (α j) := univ.filter fun b => 0 < I.prob j b
  have hΩsum : ∀ F : α j → ℝ, ∑ b ∈ Ω, I.prob j b * F b = ∑ b, I.prob j b * F b := by
    intro F
    apply sum_subset (filter_subset _ _)
    intro b _ hb
    simp only [mem_filter, mem_univ, true_and, not_lt] at hb
    rw [le_antisymm hb (I.prob_nonneg j b), zero_mul]
  have hw : ∀ b ∈ Ω, 0 < I.prob j b := fun b hb => (mem_filter.1 hb).2
  have hwsum : ∑ b ∈ Ω, I.prob j b = 1 := by
    have := hΩsum (fun _ => 1); simp only [mul_one] at this; rw [this, I.prob_sum]
  have havg : ∀ t, ∑ b ∈ Ω, I.prob j b * I.Inc σ j b t ≤ 1 := by
    intro t
    rw [hΩsum]
    unfold Inc
    by_cases hP : I.condProb σ t = 0
    · simp [hP]
    · simp only [hP, ↓reduceIte]
      have : ∑ b, I.prob j b * (I.condProb (Function.update σ j (some b)) t / I.condProb σ t) =
          (∑ b, I.prob j b * I.condProb (Function.update σ j (some b)) t) / I.condProb σ t := by
        rw [sum_div]; apply sum_congr rfl; intro b _; ring
      rw [this, I.sum_condProb_fix σ hj t, div_self hP]
  have : ∑ b ∈ Ω, I.prob j b * (I.Inc σ j b u + I.Inc σ j b v) ≤ 2 := by
    simp only [mul_add, sum_add_distrib]; linarith [havg u, havg v]
  obtain ⟨b, hb, hle⟩ := exists_le_of_avg_le hw hwsum this
  exact ⟨b, hw b hb, hle⟩

end Instance

end SharpThresholdLLL
