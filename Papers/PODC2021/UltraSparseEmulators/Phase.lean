import Papers.PODC2021.UltraSparseEmulators.Algorithm

/-!
# Invariants of one phase of Algorithm 1

Elkin, Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021 (arXiv:2106.01036v1).

`PInv δ d C E₀ s` collects the invariants of a phase with threshold `δ`, degree `d`, centers `C`,
started with emulator edges `E₀`:

* the bookkeeping behind Lemmas 2.1 and 2.4: `d · #T ≤ #J` (every supercluster absorbed at least
  `deg_i` clusters) and `|E| ≤ |E₀| + d · #U + #J` (the charging scheme of Section 2.2.1:
  an unpopular center is charged with `< deg_i` edges, a joining center with one edge);
* the structure behind Lemmas 2.5 and 2.7: joined centers are linked to their supercluster center
  by an emulator edge of length `≤ 2δ`; an unclustered center is linked to every center of `C`
  within distance `δ` (`U_edge`); and the separation invariant used in Case 2 of Lemma 2.7: no
  center still in `S_i` is within `δ` of a center that formed or joined a supercluster (`sep`).
-/

namespace Podc.UltraSparseEmulators

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {δ d : ℝ}

/-! ### The three cases of a step -/

lemma step_of_ne {s : St V} {r : V} (h : s.stat r ≠ .S) : step G δ d s r = s := by
  simp [step, h]

lemma step_of_lt {s : St V} {r : V} (h : s.stat r = .S) (hg : ((gam G δ s r).card : ℝ) < d) :
    step G δ d s r =
      ⟨Function.update s.stat r .U, s.par, s.E ∪ (gam G δ s r).image fun x => s(r, x)⟩ := by
  simp [step, h, hg]

lemma step_of_le {s : St V} {r : V} (h : s.stat r = .S) (hg : ¬ ((gam G δ s r).card : ℝ) < d) :
    step G δ d s r =
      ⟨fun x => if x = r then .T else if x ∈ gam G δ s r then .J
          else if s.stat x = .S ∧ Near G (2 * δ) r x then .N else s.stat x,
       fun x => if x = r ∨ x ∈ gam G δ s r ∨ (s.stat x = .S ∧ Near G (2 * δ) r x) then r
          else s.par x,
       s.E ∪ (gam G δ s r).image fun x => s(r, x)⟩ := by
  simp only [step, h, ite_true, hg, ite_false]

lemma mem_gam {s : St V} {r x : V} :
    x ∈ gam G δ s r ↔ x ≠ r ∧ (s.stat x = .S ∨ s.stat x = .N) ∧ Near G δ r x := by
  simp [gam]

/-! ### The invariant -/

/-- The invariants of a phase (see the module docstring). -/
structure PInv (G : SimpleGraph V) (δ d : ℝ) (C : Finset V) (E₀ : Finset (Sym2 V)) (s : St V) :
    Prop where
  out_iff : ∀ x, s.stat x = .out ↔ x ∉ C
  sub : E₀ ⊆ s.E
  reach : ∀ a b, s(a, b) ∈ s.E → s(a, b) ∉ E₀ → G.Reachable a b
  J_par : ∀ x, s.stat x = .J →
    s.stat (s.par x) = .T ∧ Near G (2 * δ) (s.par x) x ∧ s(s.par x, x) ∈ s.E
  N_par : ∀ x, s.stat x = .N → s.stat (s.par x) = .T ∧ Near G (2 * δ) (s.par x) x
  T_par : ∀ x, s.stat x = .T → s.par x = x
  U_edge : ∀ u x, s.stat u = .U → x ∈ C → x ≠ u → Near G δ u x → s(u, x) ∈ s.E
  sep : ∀ x y, (s.stat x = .J ∨ s.stat x = .T) → s.stat y = .S → ¬ Near G δ x y
  cntT : d * s.cnt .T ≤ s.cnt .J
  cntE : (s.E.card : ℝ) ≤ E₀.card + d * s.cnt .U + s.cnt .J
  noT : (C.card : ℝ) ≤ d → ∀ x, s.stat x ≠ .T

lemma pinv_init (C : Finset V) (E₀ : Finset (Sym2 V)) : PInv G δ d C E₀ (init C E₀) := by
  have hst : ∀ x, (init C E₀).stat x = .S ∨ (init C E₀).stat x = .out := fun x => by
    simp only [init]; split_ifs <;> simp
  have hc : ∀ t, t ≠ Tag.S → t ≠ Tag.out → (init C E₀).cnt t = 0 := by
    intro t ht ht'
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun x _ => ?_)
    rcases hst x with h | h <;> rw [h] <;> intro h' <;> simp_all
  have hno : ∀ x t, (init C E₀).stat x = t → t ≠ Tag.S → t ≠ Tag.out → False := by
    intro x t hx ht ht'; rcases hst x with h | h <;> rw [h] at hx <;> simp_all
  refine ⟨?_, subset_refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; simp only [init]; split_ifs <;> simp_all
  · intro a b h h'; exact absurd h h'
  · intro x hx; exact (hno x _ hx (by decide) (by decide)).elim
  · intro x hx; exact (hno x _ hx (by decide) (by decide)).elim
  · intro x hx; exact (hno x _ hx (by decide) (by decide)).elim
  · intro u x hx; exact (hno u _ hx (by decide) (by decide)).elim
  · intro x y hx
    rcases hx with hx | hx <;> exact (hno x _ hx (by decide) (by decide)).elim
  · simp [hc Tag.T (by decide) (by decide), hc Tag.J (by decide) (by decide)]
  · rw [hc Tag.U (by decide) (by decide), hc Tag.J (by decide) (by decide)]; simp [init]
  · intro _ x hx; exact hno x _ hx (by decide) (by decide)

lemma PInv.mem_of_stat {C : Finset V} {E₀ : Finset (Sym2 V)} {s : St V}
    (hs : PInv G δ d C E₀ s) {x : V} {t : Tag} (hx : s.stat x = t) (ht : t ≠ .out) : x ∈ C := by
  by_contra hc
  have := (hs.out_iff x).2 hc
  rw [hx] at this; exact ht this

omit [Fintype V] in
lemma reach_of_mem_image {r a b : V} {Γ : Finset V} (hΓ : ∀ x ∈ Γ, G.Reachable r x)
    (h : s(a, b) ∈ Γ.image fun x => s(r, x)) : G.Reachable a b := by
  obtain ⟨x, hx, he⟩ := mem_image.1 h
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hΓ _ hx
  · exact (hΓ _ hx).symm

omit [Fintype V] in
lemma card_union_image_le (E : Finset (Sym2 V)) (Γ : Finset V) (f : V → Sym2 V) :
    ((E ∪ Γ.image f).card : ℝ) ≤ E.card + Γ.card := by
  have := (card_union_le E (Γ.image f)).trans (Nat.add_le_add_left (card_image_le) _)
  exact_mod_cast this

/-- An unpopular step preserves the invariant. -/
lemma pinv_step_lt {C : Finset V} {E₀ : Finset (Sym2 V)} {s : St V} {r : V}
    (hs : PInv G δ d C E₀ s) (h : s.stat r = .S) (hg : ((gam G δ s r).card : ℝ) < d) :
    PInv G δ d C E₀ (step G δ d s r) := by
  rw [step_of_lt h hg]
  have hrC : r ∈ C := hs.mem_of_stat h (by decide)
  have hupd : ∀ x, Function.update s.stat r Tag.U x = if x = r then Tag.U else s.stat x :=
    fun x => Function.update_apply _ _ _ _
  have hne : ∀ t, t ≠ Tag.U → t ≠ Tag.S →
      (univ.filter fun x => Function.update s.stat r Tag.U x = t) =
        univ.filter fun x => s.stat x = t := by
    intro t ht ht'; ext x; by_cases hx : x = r
    · subst hx; simp [hupd, h, Ne.symm ht, Ne.symm ht']
    · simp [hupd, hx]
  have hU : (univ.filter fun x => Function.update s.stat r Tag.U x = .U) =
      insert r (univ.filter fun x => s.stat x = .U) := by
    ext x; by_cases hx : x = r <;> simp [hupd, hx]
  have hcU : (St.cnt ⟨Function.update s.stat r .U, s.par,
      s.E ∪ (gam G δ s r).image fun x => s(r, x)⟩ Tag.U) = s.cnt .U + 1 := by
    simp only [St.cnt]; rw [hU, card_insert_of_notMem (by simp [h])]
  have hcJ : (St.cnt ⟨Function.update s.stat r .U, s.par,
      s.E ∪ (gam G δ s r).image fun x => s(r, x)⟩ Tag.J) = s.cnt .J := by
    simp only [St.cnt]; rw [hne _ (by decide) (by decide)]
  have hcT : (St.cnt ⟨Function.update s.stat r .U, s.par,
      s.E ∪ (gam G δ s r).image fun x => s(r, x)⟩ Tag.T) = s.cnt .T := by
    simp only [St.cnt]; rw [hne _ (by decide) (by decide)]
  have hpar : ∀ x, s.stat x = .T → x ≠ r := fun x hx e => by rw [e, h] at hx; cases hx
  refine ⟨?_, hs.sub.trans subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; by_cases hx : x = r
    · subst hx; simp [hrC]
    · simp only [hupd, hx, ite_false]; exact hs.out_iff x
  · intro a b hab hn
    rcases mem_union.1 hab with h1 | h1
    · exact hs.reach a b h1 hn
    · exact reach_of_mem_image (fun x hx => (mem_gam.1 hx).2.2.1) h1
  · intro x hx
    have hxr : x ≠ r := fun e => by subst e; simp at hx
    simp only [hupd, hxr, ite_false] at hx
    obtain ⟨h1, h2, h3⟩ := hs.J_par x hx
    refine ⟨by simp only [hupd, hpar _ h1, ite_false]; exact h1, h2, mem_union_left _ h3⟩
  · intro x hx
    have hxr : x ≠ r := fun e => by subst e; simp at hx
    simp only [hupd, hxr, ite_false] at hx
    obtain ⟨h1, h2⟩ := hs.N_par x hx
    exact ⟨by simp only [hupd, hpar _ h1, ite_false]; exact h1, h2⟩
  · intro x hx
    have hxr : x ≠ r := fun e => by subst e; simp at hx
    simp only [hupd, hxr, ite_false] at hx
    exact hs.T_par x hx
  · intro u x hu hxC hxu hn
    by_cases hur : u = r
    · subst hur
      rcases hsx : s.stat x with _ | _ | _ | _ | _ | _
      · exact mem_union_right _ (mem_image.2 ⟨x, mem_gam.2 ⟨hxu, Or.inl hsx, hn⟩, rfl⟩)
      · exact mem_union_right _ (mem_image.2 ⟨x, mem_gam.2 ⟨hxu, Or.inr hsx, hn⟩, rfl⟩)
      · have := hs.U_edge x u hsx hrC (Ne.symm hxu) hn.symm
        exact mem_union_left _ (by rw [Sym2.eq_swap]; exact this)
      · exact absurd hn.symm (hs.sep x u (Or.inr hsx) h)
      · exact absurd hn.symm (hs.sep x u (Or.inl hsx) h)
      · exact absurd hxC ((hs.out_iff x).1 hsx)
    · simp only [hupd, hur, ite_false] at hu
      exact mem_union_left _ (hs.U_edge u x hu hxC hxu hn)
  · intro x y hx hy
    have hxr : x ≠ r := fun e => by subst e; simp at hx
    have hyr : y ≠ r := fun e => by subst e; simp at hy
    simp only [hupd, hxr, hyr, ite_false] at hx hy
    exact hs.sep x y hx hy
  · rw [hcT, hcJ]; exact hs.cntT
  · rw [hcU, hcJ]
    have := card_union_image_le s.E (gam G δ s r) (fun x => s(r, x))
    simp only at this ⊢
    push_cast
    linarith [hs.cntE]
  · intro hC x hx
    have hxr : x ≠ r := fun e => by subst e; simp at hx
    simp only [hupd, hxr, ite_false] at hx
    exact hs.noT hC x hx

/-- A popular step preserves the invariant. -/
lemma pinv_step_le (hδ : 0 ≤ δ) {C : Finset V} {E₀ : Finset (Sym2 V)} {s : St V} {r : V}
    (hs : PInv G δ d C E₀ s) (h : s.stat r = .S) (hg : ¬ ((gam G δ s r).card : ℝ) < d) :
    PInv G δ d C E₀ (step G δ d s r) := by
  rw [step_of_le h hg]
  set Γ := gam G δ s r with hΓdef
  have hrC : r ∈ C := hs.mem_of_stat h (by decide)
  have hΓ : ∀ x ∈ Γ, x ≠ r ∧ (s.stat x = .S ∨ s.stat x = .N) ∧ Near G δ r x :=
    fun x hx => mem_gam.1 hx
  have hrΓ : r ∉ Γ := fun hr => (hΓ r hr).1 rfl
  have hnotΓ : ∀ x, s.stat x ≠ .S → s.stat x ≠ .N → x ∉ Γ := fun x h1 h2 hx => by
    rcases (hΓ x hx).2.1 with h3 | h3 <;> contradiction
  set st' : V → Tag := fun x => if x = r then .T else if x ∈ Γ then .J
    else if s.stat x = .S ∧ Near G (2 * δ) r x then .N else s.stat x with hst'
  set pr : V → V := fun x => if x = r ∨ x ∈ Γ ∨ (s.stat x = .S ∧ Near G (2 * δ) r x) then r
    else s.par x with hpr
  -- `st'` on vertices that were neither in `S_i` nor in `N_i`
  have hst_old : ∀ x, s.stat x ≠ .S → s.stat x ≠ .N → st' x = s.stat x := by
    intro x h1 h2
    have hxr : x ≠ r := fun e => h1 (e ▸ h)
    simp [hst', hxr, hnotΓ x h1 h2, h1]
  have hpar_old : ∀ x, s.stat x ≠ .S → s.stat x ≠ .N → pr x = s.par x := by
    intro x h1 h2
    have hxr : x ≠ r := fun e => h1 (e ▸ h)
    simp [hpr, hxr, hnotΓ x h1 h2, h1]
  have hTr : ∀ x, s.stat x = .T → x ≠ r := fun x hx e => by rw [e, h] at hx; cases hx
  -- counting
  have hfT : (univ.filter fun x => st' x = .T) = insert r (univ.filter fun x => s.stat x = .T) := by
    ext x
    by_cases hxr : x = r
    · subst hxr; simp [hst']
    · by_cases hxΓ : x ∈ Γ
      · have := (hΓ x hxΓ).2.1
        simp only [mem_filter, mem_univ, true_and, mem_insert, hxr, false_or, hst',
          hxΓ, ↓reduceIte]
        constructor <;> intro h' <;> [cases h'; (rcases this with h3 | h3 <;> rw [h3] at h' <;> cases h')]
      · by_cases hmv : s.stat x = .S ∧ Near G (2 * δ) r x
        · simp [hst', hxr, hxΓ, hmv]
        · simp [hst', hxr, hxΓ, hmv]
  have hfJ : (univ.filter fun x => st' x = .J) = (univ.filter fun x => s.stat x = .J) ∪ Γ := by
    ext x
    by_cases hxr : x = r
    · subst hxr; simp [hst', hrΓ, h]
    · by_cases hxΓ : x ∈ Γ
      · simp [hst', hxr, hxΓ]
      · by_cases hmv : s.stat x = .S ∧ Near G (2 * δ) r x
        · simp [hst', hxr, hxΓ, hmv]
        · simp [hst', hxr, hxΓ, hmv]
  have hfU : (univ.filter fun x => st' x = .U) = univ.filter fun x => s.stat x = .U := by
    ext x
    by_cases hxr : x = r
    · subst hxr; simp [hst', h]
    · by_cases hxΓ : x ∈ Γ
      · have := (hΓ x hxΓ).2.1
        simp only [mem_filter, mem_univ, true_and, hst', hxr, hxΓ, ↓reduceIte]
        constructor <;> intro h' <;> [cases h'; (rcases this with h3 | h3 <;> rw [h3] at h' <;> cases h')]
      · by_cases hmv : s.stat x = .S ∧ Near G (2 * δ) r x
        · simp [hst', hxr, hxΓ, hmv]
        · simp [hst', hxr, hxΓ, hmv]
  have hdisj : Disjoint (univ.filter fun x => s.stat x = .J) Γ := by
    rw [Finset.disjoint_left]; intro x hx hxΓ
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases (hΓ x hxΓ).2.1 with h3 | h3 <;> rw [h3] at hx <;> cases hx
  have hcT : (St.cnt ⟨st', pr, s.E ∪ Γ.image fun x => s(r, x)⟩ Tag.T) = s.cnt .T + 1 := by
    simp only [St.cnt]; rw [hfT, card_insert_of_notMem (by simp [h])]
  have hcJ : (St.cnt ⟨st', pr, s.E ∪ Γ.image fun x => s(r, x)⟩ Tag.J) = s.cnt .J + Γ.card := by
    simp only [St.cnt]; rw [hfJ, card_union_of_disjoint hdisj]
  have hcU : (St.cnt ⟨st', pr, s.E ∪ Γ.image fun x => s(r, x)⟩ Tag.U) = s.cnt .U := by
    simp only [St.cnt]; rw [hfU]
  have hd : d ≤ Γ.card := le_of_not_gt hg
  refine ⟨?_, hs.sub.trans subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- out_iff
    intro x
    by_cases hxr : x = r
    · subst hxr; simp [hst', hrC]
    · by_cases hxΓ : x ∈ Γ
      · have hxC : x ∈ C := by
          rcases (hΓ x hxΓ).2.1 with h3 | h3 <;> exact hs.mem_of_stat h3 (by decide)
        simp [hst', hxr, hxΓ, hxC]
      · by_cases hmv : s.stat x = .S ∧ Near G (2 * δ) r x
        · have hxC : x ∈ C := hs.mem_of_stat hmv.1 (by decide)
          simp [hst', hxr, hxΓ, hmv, hxC]
        · simp only [hst', hxr, hxΓ, hmv, ↓reduceIte]; exact hs.out_iff x
  · intro a b hab hn
    rcases mem_union.1 hab with h1 | h1
    · exact hs.reach a b h1 hn
    · exact reach_of_mem_image (fun x hx => (hΓ x hx).2.2.1) h1
  · -- J_par
    intro x hx
    simp only at hx ⊢
    by_cases hxr : x = r
    · subst hxr; simp [hst'] at hx
    by_cases hxΓ : x ∈ Γ
    · have hpx : pr x = r := by simp [hpr, hxΓ]
      rw [hpx]
      refine ⟨by simp [hst'], ?_, mem_union_right _ (mem_image.2 ⟨x, hxΓ, rfl⟩)⟩
      have := (hΓ x hxΓ).2.2
      exact ⟨this.1, by linarith [this.2]⟩
    by_cases hmv : s.stat x = .S ∧ Near G (2 * δ) r x
    · simp [hst', hxr, hxΓ, hmv] at hx
    simp only [hst', hxr, hxΓ, hmv, ↓reduceIte] at hx
    have h1 : s.stat x ≠ .S := by rw [hx]; decide
    have h2 : s.stat x ≠ .N := by rw [hx]; decide
    rw [hpar_old x h1 h2]
    obtain ⟨h3, h4, h5⟩ := hs.J_par x hx
    refine ⟨?_, h4, mem_union_left _ h5⟩
    rw [hst_old _ (by rw [h3]; decide) (by rw [h3]; decide)]; exact h3
  · -- N_par
    intro x hx
    simp only at hx ⊢
    by_cases hxr : x = r
    · subst hxr; simp [hst'] at hx
    by_cases hxΓ : x ∈ Γ
    · simp [hst', hxr, hxΓ] at hx
    by_cases hmv : s.stat x = .S ∧ Near G (2 * δ) r x
    · have hpx : pr x = r := by simp [hpr, hmv]
      rw [hpx]
      exact ⟨by simp [hst'], hmv.2⟩
    simp only [hst', hxr, hxΓ, hmv, ↓reduceIte] at hx
    have h1 : s.stat x ≠ .S := by rw [hx]; decide
    have hpx : pr x = s.par x := by simp [hpr, hxr, hxΓ, h1]
    rw [hpx]
    obtain ⟨h3, h4⟩ := hs.N_par x hx
    refine ⟨?_, h4⟩
    rw [hst_old _ (by rw [h3]; decide) (by rw [h3]; decide)]; exact h3
  · -- T_par
    intro x hx
    simp only at hx ⊢
    by_cases hxr : x = r
    · simp [hpr, hxr]
    by_cases hxΓ : x ∈ Γ
    · simp [hst', hxr, hxΓ] at hx
    by_cases hmv : s.stat x = .S ∧ Near G (2 * δ) r x
    · simp [hst', hxr, hxΓ, hmv] at hx
    simp only [hst', hxr, hxΓ, hmv, ↓reduceIte] at hx
    rw [hpar_old x (by rw [hx]; decide) (by rw [hx]; decide)]
    exact hs.T_par x hx
  · -- U_edge
    intro u x hu hxC hxu hn
    simp only at hu ⊢
    by_cases hur : u = r
    · subst hur; simp [hst'] at hu
    by_cases huΓ : u ∈ Γ
    · simp [hst', hur, huΓ] at hu
    by_cases hmv : s.stat u = .S ∧ Near G (2 * δ) r u
    · simp [hst', hur, huΓ, hmv] at hu
    simp only [hst', hur, huΓ, hmv, ↓reduceIte] at hu
    exact mem_union_left _ (hs.U_edge u x hu hxC hxu hn)
  · -- sep
    intro x y hx hy
    simp only at hx hy
    by_cases hyr : y = r
    · subst hyr; simp [hst'] at hy
    by_cases hyΓ : y ∈ Γ
    · simp [hst', hyr, hyΓ] at hy
    by_cases hmv : s.stat y = .S ∧ Near G (2 * δ) r y
    · simp [hst', hyr, hyΓ, hmv] at hy
    simp only [hst', hyr, hyΓ, hmv, ↓reduceIte] at hy
    have hfar : ¬ Near G (2 * δ) r y := fun hn => hmv ⟨hy, hn⟩
    intro hxy
    by_cases hxr : x = r
    · subst hxr
      exact hyΓ (mem_gam.2 ⟨hyr, Or.inl hy, hxy⟩)
    by_cases hxΓ : x ∈ Γ
    · exact hfar (by have := ((hΓ x hxΓ).2.2).trans hxy; rwa [← two_mul] at this)
    have hxmv : ¬ (s.stat x = .S ∧ Near G (2 * δ) r x) := by
      rintro ⟨h3, -⟩
      rcases hx with hx | hx <;> simp [hst', hxr, hxΓ, h3] at hx <;> split_ifs at hx
    simp only [hst', hxr, hxΓ, hxmv, ↓reduceIte] at hx
    exact hs.sep x y hx hy hxy
  · rw [hcT, hcJ]; push_cast; linarith [hs.cntT]
  · rw [hcU, hcJ]
    have := card_union_image_le s.E Γ (fun x => s(r, x))
    push_cast
    linarith [hs.cntE]
  · intro hC
    exfalso
    have hsub : Γ ⊆ C.erase r := by
      intro x hx
      rcases (hΓ x hx).2.1 with h3 | h3 <;>
        exact mem_erase.2 ⟨(hΓ x hx).1, hs.mem_of_stat h3 (by decide)⟩
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hrC] at h1
    have h2 : (Γ.card : ℝ) ≤ (C.card : ℝ) - 1 := by
      have : 1 ≤ C.card := card_pos.2 ⟨r, hrC⟩
      have : Γ.card + 1 ≤ C.card := by omega
      have : (Γ.card : ℝ) + 1 ≤ C.card := by exact_mod_cast this
      linarith
    linarith

lemma pinv_step (hδ : 0 ≤ δ) {C : Finset V} {E₀ : Finset (Sym2 V)} {s : St V} (r : V)
    (hs : PInv G δ d C E₀ s) : PInv G δ d C E₀ (step G δ d s r) := by
  by_cases h : s.stat r = .S
  · by_cases hg : ((gam G δ s r).card : ℝ) < d
    · exact pinv_step_lt hs h hg
    · exact pinv_step_le hδ hs h hg
  · rw [step_of_ne h]; exact hs

lemma pinv_foldl (hδ : 0 ≤ δ) {C : Finset V} {E₀ : Finset (Sym2 V)} (L : List V) :
    ∀ {s : St V}, PInv G δ d C E₀ s → PInv G δ d C E₀ (L.foldl (step G δ d) s) := by
  induction L with
  | nil => intro s hs; exact hs
  | cons r L ih => intro s hs; exact ih (pinv_step hδ r hs)

/-! ### Every center is eventually removed from `S_i` -/

lemma step_stat_ne_S {s : St V} {r x : V} (hx : s.stat x ≠ .S) :
    (step G δ d s r).stat x ≠ .S := by
  by_cases h : s.stat r = .S
  · by_cases hg : ((gam G δ s r).card : ℝ) < d
    · rw [step_of_lt h hg]; simp only [Function.update_apply]; split_ifs <;> simp_all
    · rw [step_of_le h hg]; simp only; split_ifs <;> simp_all
  · rw [step_of_ne h]; exact hx

lemma step_stat_self {s : St V} {r : V} : (step G δ d s r).stat r ≠ .S := by
  by_cases h : s.stat r = .S
  · by_cases hg : ((gam G δ s r).card : ℝ) < d
    · rw [step_of_lt h hg]; simp
    · rw [step_of_le h hg]; simp
  · rw [step_of_ne h]; exact h

lemma foldl_stat_ne_S (L : List V) :
    ∀ {s : St V} {x : V}, s.stat x ≠ .S → (L.foldl (step G δ d) s).stat x ≠ .S := by
  induction L with
  | nil => intro s x hx; exact hx
  | cons r L ih => intro s x hx; exact ih (step_stat_ne_S hx)

lemma foldl_stat_of_mem (L : List V) :
    ∀ {s : St V} {x : V}, x ∈ L → (L.foldl (step G δ d) s).stat x ≠ .S := by
  induction L with
  | nil => intro s x hx; simp at hx
  | cons r L ih =>
    intro s x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact foldl_stat_ne_S L step_stat_self
    · exact ih hx

/-! ### End of a phase -/

/-- `finish` preserves the invariant once `S_i = ∅`. -/
lemma pinv_finish {C : Finset V} {E₀ : Finset (Sym2 V)} {s : St V} (hs : PInv G δ d C E₀ s)
    (hS : ∀ x, s.stat x ≠ .S) : PInv G δ d C E₀ (finish s) := by
  have hst : ∀ x, (finish s).stat x = if s.stat x = .N then .J else s.stat x := fun _ => rfl
  have hne : ∀ t, t ≠ Tag.J → t ≠ Tag.N →
      (univ.filter fun x => (finish s).stat x = t) = univ.filter fun x => s.stat x = t := by
    intro t h1 h2; ext x; simp only [mem_filter, mem_univ, true_and, hst]
    split_ifs with h <;> simp_all [eq_comm]
  have hJ : (univ.filter fun x => (finish s).stat x = .J) =
      (univ.filter fun x => s.stat x = .J) ∪ univ.filter fun x => s.stat x = .N := by
    ext x; simp only [mem_filter, mem_univ, true_and, mem_union, hst]
    split_ifs with h <;> simp [h]
  have hdisj : Disjoint (univ.filter fun x => s.stat x = .J) (univ.filter fun x => s.stat x = .N) := by
    rw [Finset.disjoint_left]; intro x h1 h2; simp only [mem_filter] at h1 h2; rw [h1.2] at h2
    exact absurd h2.2 (by decide)
  have hcJ : (finish s).cnt .J = s.cnt .J + s.cnt .N := by
    simp only [St.cnt]; rw [hJ, card_union_of_disjoint hdisj]
  have hcT : (finish s).cnt .T = s.cnt .T := by simp only [St.cnt]; rw [hne _ (by decide) (by decide)]
  have hcU : (finish s).cnt .U = s.cnt .U := by simp only [St.cnt]; rw [hne _ (by decide) (by decide)]
  have hold : ∀ x, s.stat x ≠ .N → (finish s).stat x = s.stat x := fun x h => by simp [hst, h]
  refine ⟨?_, hs.sub.trans subset_union_left, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; rw [hst]; split_ifs with h
    · simp only [false_iff, not_not]; exact hs.mem_of_stat h (by decide)
    · exact hs.out_iff x
  · intro a b hab hn
    rcases mem_union.1 hab with h1 | h1
    · exact hs.reach a b h1 hn
    · obtain ⟨x, hx, he⟩ := mem_image.1 h1
      have := (hs.N_par x (by simpa using hx)).2.1
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact this.symm
  · intro x hx
    rw [hst] at hx
    split_ifs at hx with h
    · obtain ⟨h1, h2⟩ := hs.N_par x h
      refine ⟨by show (finish s).stat (s.par x) = .T; rw [hold _ (by rw [h1]; decide)]; exact h1,
        h2, ?_⟩
      exact mem_union_right _ (mem_image.2 ⟨x, by simp [h], rfl⟩)
    · obtain ⟨h1, h2, h3⟩ := hs.J_par x hx
      exact ⟨by show (finish s).stat (s.par x) = .T; rw [hold _ (by rw [h1]; decide)]; exact h1,
        h2, mem_union_left _ h3⟩
  · intro x hx; rw [hst] at hx; split_ifs at hx <;> simp_all
  · intro x hx
    by_cases h : s.stat x = .N
    · simp [hst, h] at hx
    · rw [hold x h] at hx; exact hs.T_par x hx
  · intro u x hu hxC hxu hn
    by_cases h : s.stat u = .N
    · simp [hst, h] at hu
    · rw [hold u h] at hu; exact mem_union_left _ (hs.U_edge u x hu hxC hxu hn)
  · intro x y _ hy
    by_cases h : s.stat y = .N
    · simp [hst, h] at hy
    · rw [hold y h] at hy; exact absurd hy (hS y)
  · rw [hcT, hcJ]; push_cast; linarith [hs.cntT, (Nat.cast_nonneg (s.cnt .N) : (0 : ℝ) ≤ _)]
  · rw [hcU, hcJ]
    have := card_union_image_le s.E (univ.filter fun x => s.stat x = .N) (fun x => s(s.par x, x))
    simp only [finish]
    push_cast
    have h2 : ((univ.filter fun x => s.stat x = .N).card : ℝ) = s.cnt .N := rfl
    linarith [hs.cntE]
  · intro hC x hx
    by_cases h : s.stat x = .N
    · simp [hst, h] at hx
    · rw [hold x h] at hx; exact hs.noT hC x hx

/-- The outcome of a phase in which every center is considered (`∀ x, x ∈ L`): the invariant
holds, `S_i = N_i = ∅`. -/
theorem phase_spec (hδ : 0 ≤ δ) (C : Finset V) (E₀ : Finset (Sym2 V)) {L : List V}
    (hL : ∀ x, x ∈ L) :
    PInv G δ d C E₀ (phase G δ d C E₀ L) ∧ ∀ x, (phase G δ d C E₀ L).stat x ≠ .S ∧
      (phase G δ d C E₀ L).stat x ≠ .N := by
  have h1 := pinv_foldl (G := G) (δ := δ) (d := d) hδ L (pinv_init C E₀)
  have h2 : ∀ x, (L.foldl (step G δ d) (init C E₀)).stat x ≠ .S := fun x => foldl_stat_of_mem L (hL x)
  refine ⟨pinv_finish h1 h2, fun x => ?_⟩
  simp only [phase, finish]
  split_ifs with h
  · exact ⟨by decide, by decide⟩
  · exact ⟨h2 x, h⟩

/-- At the end of a phase, every center is in `U_i`, is a new supercluster center, or joined a
supercluster: `|C| = #U + #T + #J`. -/
lemma card_eq_of_end {C : Finset V} {E₀ : Finset (Sym2 V)} {s : St V} (hs : PInv G δ d C E₀ s)
    (hend : ∀ x, s.stat x ≠ .S ∧ s.stat x ≠ .N) :
    C.card = s.cnt .U + s.cnt .T + s.cnt .J := by
  have hC : C = ((univ.filter fun x => s.stat x = .U) ∪ univ.filter fun x => s.stat x = .T) ∪
      univ.filter fun x => s.stat x = .J := by
    ext x
    simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      have h1 := hend x
      have h2 : s.stat x ≠ .out := fun h => (hs.out_iff x).1 h hx
      rcases hsx : s.stat x <;> simp_all
    · rintro ((h | h) | h) <;> exact hs.mem_of_stat h (by decide)
  rw [hC, card_union_of_disjoint, card_union_of_disjoint] <;>
    · try rw [Finset.disjoint_union_left]
      try constructor
      all_goals
        rw [Finset.disjoint_left]; intro x h1 h2; simp only [mem_filter] at h1 h2
        rw [h1.2] at h2; exact absurd h2.2 (by decide)

end Podc.UltraSparseEmulators
