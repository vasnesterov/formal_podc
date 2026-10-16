import Mathlib
import Cslib.Computability.Distributed.ColourSystem.Algorithm

/-!
# Templates, realisations and extensions (§3.2–3.5 of Hirvonen–Suomela)

An `h`-template `(T, τ)` is an `h`-regular colour system `T` with a forbidden colour
`τ(t) ∉ C(T, t)` at each node. Its **realisation** (§3.5) adds at each node `t` a half-loop of every
free colour `c ∉ C(T,t) + τ(t)` and unfolds: the view of `t` in this graph is the `d`-regular
(`d = k - 1`) colour system `real T t` in which every node mapped to `t` sees the same thing
(Corollary 10). We define the template output `out A T t := A (real T t) e` directly as the output
of the root of the view from `t`; by Lemma 8 / Corollary 10 this is the output of every node of the
realisation that is mapped to `t` (`out_eq_apply`).

A 1-colour picker `P` chooses one free colour `P t` at each node; the **extension** `T.extend P`
(§3.3) unfolds the half-loops `P t` only, keeping `τ`. Its realisation coincides with the
realisation of `T` (Corollary 11, `real_extend`), so `out A (T.extend P) x = out A T (pos x)`
(`Good.out_extend`).
-/

namespace Papers.PODC2012.MaximalMatching

open Cslib.ColourSystem FreeCox Pointwise

variable {k : ℕ}

/-- A template: a set `T ⊆ G_k` (the carrier) with a forbidden colour `τ t` at each node (the
values outside `T` are irrelevant). -/
@[ext] structure Template (k : ℕ) where
  carrier : Set (FreeCox k)
  forb : FreeCox k → Fin k

namespace Template

instance : SMul (FreeCox k) (Template k) :=
  ⟨fun u T => ⟨u • T.carrier, fun x => T.forb (u⁻¹ * x)⟩⟩

@[simp] theorem smul_carrier (u : FreeCox k) (T : Template k) : (u • T).carrier = u • T.carrier :=
  rfl

@[simp] theorem smul_forb (u : FreeCox k) (T : Template k) (x : FreeCox k) :
    (u • T).forb x = T.forb (u⁻¹ * x) := rfl

instance : MulAction (FreeCox k) (Template k) where
  one_smul T := by ext x <;> simp
  mul_smul u v T := by
    ext x
    · simp [mul_smul]
    · simp [mul_assoc]

/-- `(T, τ)` is an `h`-template (§3.2). -/
def IsTemplate (h : ℕ) (T : Template k) : Prop :=
  IsColourSystem T.carrier ∧ IsRegular T.carrier h ∧ ∀ t ∈ T.carrier, T.forb t ∉ colours T.carrier t

/-- Colour `c` is free at `t`: `c ∉ C(T, t) + τ(t)`. -/
def Free (T : Template k) (t : FreeCox k) (c : Fin k) : Prop :=
  t * gen c ∉ T.carrier ∧ c ≠ T.forb t

/-- The graph whose view is the realisation: tree edges of `T` plus half-loops of all colours
`≠ τ(t)` (which, by priority of tree edges, are exactly the free colours). -/
noncomputable def realGraph (T : Template k) : ColouredGraph k (FreeCox k) :=
  tGraph T.carrier fun s => {c | c ≠ T.forb s}

/-- The realisation of `T` seen from `t` (`t̄`-translate of the realisation of §3.5, viewed from a
node `v` with `p(v) = t`). -/
def real (T : Template k) (t : FreeCox k) : Set (FreeCox k) := T.realGraph.view t

/-- `A(T, τ, t)`: the output of the algorithm at (any node of the realisation mapped to) `t`. -/
def out (A : Algorithm k) (T : Template k) (t : FreeCox k) : Option (Fin k) := A (T.real t) 1

/-- `t` is matched along an edge of `T` (in the realisation's output). -/
def Matched (A : Algorithm k) (T : Template k) (t : FreeCox k) : Prop :=
  ∃ c ∈ colours T.carrier t, T.out A t = some c

/-- `h`-compatibility (§3.7): (C1) `S[h] = T[h]` and (C2) `σ[h-1] = τ[h-1]`. -/
def Compatible (h : ℕ) (S T : Template k) : Prop :=
  ball S.carrier h = ball T.carrier h ∧ ∀ s ∈ S.carrier, len s + 1 ≤ h → S.forb s = T.forb s

/-- An `h`-critical pair (§3.7): (C1)–(C4). -/
def IsCritical (A : Algorithm k) (h : ℕ) (S T : Template k) : Prop :=
  IsTemplate h S ∧ IsTemplate h T ∧ Compatible h S T ∧ ¬ T.Matched A 1 ∧
    ∀ s ∈ S.carrier, S.Matched A s

/-! ### Basic properties -/

theorem IsTemplate.isColourSystem {h : ℕ} {T : Template k} (hT : IsTemplate h T) :
    IsColourSystem T.carrier := hT.1

theorem IsTemplate.card_colours {h : ℕ} {T : Template k} (hT : IsTemplate h T) {t : FreeCox k}
    (ht : t ∈ T.carrier) : (colours T.carrier t).card = h := hT.2.1 t ht

theorem IsTemplate.forb_not_mem {h : ℕ} {T : Template k} (hT : IsTemplate h T) {t : FreeCox k}
    (ht : t ∈ T.carrier) : t * gen (T.forb t) ∉ T.carrier := by
  have := hT.2.2 t ht; rwa [mem_colours] at this

theorem IsTemplate.smul {h : ℕ} {T : Template k} (hT : IsTemplate h T) {u : FreeCox k}
    (hu : u ∈ T.carrier) : IsTemplate h (u⁻¹ • T) := by
  refine ⟨hT.1.inv_smul hu, isRegular_inv_smul hT.2.1 u, fun t ht => ?_⟩
  rw [smul_carrier, mem_inv_smul] at ht
  simp only [smul_carrier, smul_forb, inv_inv, colours_inv_smul]
  exact hT.2.2 _ ht

/-- If `h < k - 1`, every node of an `h`-template has a free colour. -/
theorem IsTemplate.exists_free {h : ℕ} {T : Template k} (hT : IsTemplate h T) (hh : h + 1 < k)
    {t : FreeCox k} (ht : t ∈ T.carrier) : ∃ c, T.Free t c := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ : Finset (Fin k)) ⊆ insert (T.forb t) (colours T.carrier t) := by
    intro c _
    rw [Finset.mem_insert, mem_colours]
    by_contra hc
    push Not at hc
    exact hne c ⟨hc.2, hc.1⟩ |>.elim
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_insert_le (T.forb t) (colours T.carrier t)
  rw [hT.card_colours ht] at this
  omega

/-! ### The realisation -/

section real

variable {h : ℕ} {T : Template k}

theorem realGraph_step (t : FreeCox k) (c : Fin k) :
    T.realGraph.step t c = (tGraph T.carrier fun s => {c | c ≠ T.forb s}).step t c := rfl

theorem isColourSystem_real (T : Template k) (t : FreeCox k) : IsColourSystem (T.real t) :=
  T.realGraph.isColourSystem_view t

theorem realGraph_walk_mem {t b x : FreeCox k} (ht : t ∈ T.carrier)
    (hb : T.realGraph.walk t x = some b) : b ∈ T.carrier :=
  tGraph_walk_mem ht hb

theorem realGraph_step_isSome (hT : IsTemplate h T) {b : FreeCox k} (hb : b ∈ T.carrier)
    (c : Fin k) : (T.realGraph.step b c).isSome ↔ c ≠ T.forb b := by
  rw [realGraph, tGraph_step_isSome]
  simp only [ne_eq, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, h1 | h1⟩
    · rintro rfl; exact hT.forb_not_mem hb h1
    · exact h1
  · intro h1; exact ⟨hb, Or.inr h1⟩

theorem colours_real (hT : IsTemplate h T) {t b x : FreeCox k} (ht : t ∈ T.carrier)
    (hb : T.realGraph.walk t x = some b) (c : Fin k) :
    c ∈ colours (T.real t) x ↔ c ≠ T.forb b := by
  rw [real, T.realGraph.colours_view hb, realGraph_step_isSome hT (realGraph_walk_mem ht hb)]

theorem colours_real_one (hT : IsTemplate h T) {t : FreeCox k} (ht : t ∈ T.carrier) (c : Fin k) :
    c ∈ colours (T.real t) 1 ↔ c ≠ T.forb t :=
  colours_real hT ht (T.realGraph.walk_one t) c

/-- Realisations are `d`-regular with `d = k - 1` (Lemma 7 applied to the realisation). -/
theorem isRegular_real (hT : IsTemplate h T) {t : FreeCox k} (ht : t ∈ T.carrier) :
    IsRegular (T.real t) (k - 1) := by
  classical
  intro x hx
  obtain ⟨b, hb⟩ := T.realGraph.mem_view.1 hx
  have : colours (T.real t) x = Finset.univ.erase (T.forb b) := by
    ext c; rw [colours_real hT ht hb]; simp
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

theorem real_inv_smul {t b x : FreeCox k} (hb : T.realGraph.walk t x = some b) :
    x⁻¹ • T.real t = T.real b :=
  T.realGraph.view_inv_smul hb

/-- Translating a template does not change its realisations. -/
theorem real_smul (u t : FreeCox k) : (u • T).real (u * t) = T.real t := by
  unfold real realGraph
  have := view_tGraph_smul (T := T.carrier) (L := fun s => {c | c ≠ T.forb s}) u t
  simpa using this

theorem out_smul (A : Algorithm k) (u t : FreeCox k) : (u • T).out A (u * t) = T.out A t := by
  simp only [out, real_smul]

theorem out_inv_smul (A : Algorithm k) (u t : FreeCox k) : (u⁻¹ • T).out A t = T.out A (u * t) := by
  rw [← out_smul A u, smul_inv_smul]

theorem colours_smul_carrier (u t : FreeCox k) :
    colours (u⁻¹ • T).carrier t = colours T.carrier (u * t) := by
  rw [smul_carrier, colours_inv_smul]

theorem matched_inv_smul (A : Algorithm k) (u t : FreeCox k) :
    (u⁻¹ • T).Matched A t ↔ T.Matched A (u * t) := by
  simp only [Matched, colours_smul_carrier, out_inv_smul]

/-- For an `h`-template with `h + 1 = k` there are no free colours. -/
theorem IsTemplate.not_free (hT : IsTemplate h T) (hh : h + 1 = k) {t : FreeCox k}
    (ht : t ∈ T.carrier) (c : Fin k) : ¬ T.Free t c := by
  classical
  rintro ⟨h1, h2⟩
  have hc : c ∉ insert (T.forb t) (colours T.carrier t) := by
    simp [mem_colours, h1, h2]
  have := Finset.card_le_card (Finset.subset_univ (insert c (insert (T.forb t) (colours T.carrier t))))
  rw [Finset.card_insert_of_notMem hc, Finset.card_insert_of_notMem (hT.2.2 t ht),
    hT.card_colours ht, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- For an `h`-template with `h + 1 = k` the realisation is `T` itself. -/
theorem real_eq_of_full (hT : IsTemplate h T) (hh : h + 1 = k) {t : FreeCox k}
    (ht : t ∈ T.carrier) : T.real t = t⁻¹ • T.carrier := by
  have hstep : ∀ b c, T.realGraph.step b c = (tGraph T.carrier fun _ => ∅).step b c := by
    intro b c
    by_cases hb : b ∈ T.carrier
    · by_cases hbc : b * gen c ∈ T.carrier
      · rw [realGraph, tGraph_step_of_mem hb hbc, tGraph_step_of_mem hb hbc]
      · have : c = T.forb b := by
          by_contra hne; exact hT.not_free hh hb c ⟨hbc, hne⟩
        rw [realGraph, tGraph_step_of_not_mem hb hbc (by simp [this]),
          tGraph_step_of_not_mem hb hbc (by simp)]
    · simp [realGraph, tGraph, hb]
  rw [real, ← view_tGraph_empty hT.1 ht]
  exact (tGraph T.carrier fun _ => ∅).view_map T.realGraph id (fun b c => by simp [hstep]) t

end real

/-! ### Extensions (§3.3–3.4) -/

section ext

variable {h : ℕ} {T : Template k} {P : FreeCox k → Fin k}

/-- `P` is a 1-colour picker for `T`: it picks a free colour at every node. -/
def IsPicker (T : Template k) (P : FreeCox k → Fin k) : Prop := ∀ t ∈ T.carrier, T.Free t (P t)

/-- The graph of the `P`-extension: tree edges of `T` plus a half-loop of colour `P t` at `t`
(Remark 1 of the paper). -/
noncomputable def extGraph (T : Template k) (P : FreeCox k → Fin k) : ColouredGraph k (FreeCox k) :=
  tGraph T.carrier fun s => {P s}

/-- The projection `p : X → T` of the extension. -/
noncomputable def pos (T : Template k) (P : FreeCox k → Fin k) (x : FreeCox k) : FreeCox k :=
  ((T.extGraph P).walk 1 x).getD 1

/-- The `P`-extension `ext(T, τ, P) = (X, ξ)` with `ξ = τ ∘ p`. -/
noncomputable def extend (T : Template k) (P : FreeCox k → Fin k) : Template k :=
  ⟨(T.extGraph P).view 1, fun x => T.forb (T.pos P x)⟩

theorem extend_forb (x : FreeCox k) : (T.extend P).forb x = T.forb (T.pos P x) := rfl

theorem walk_extend {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) :
    (T.extGraph P).walk 1 x = some (T.pos P x) := by
  obtain ⟨b, hb⟩ := (T.extGraph P).mem_view.1 hx
  simp [pos, hb]

theorem mem_extend_of_walk {x b : FreeCox k} (hb : (T.extGraph P).walk 1 x = some b) :
    x ∈ (T.extend P).carrier ∧ T.pos P x = b :=
  ⟨(T.extGraph P).mem_view.2 ⟨b, hb⟩, by simp [pos, hb]⟩

theorem one_mem_extend : (1 : FreeCox k) ∈ (T.extend P).carrier := (T.extGraph P).one_mem_view 1

@[simp] theorem pos_one : T.pos P 1 = 1 := rfl

theorem isColourSystem_extend : IsColourSystem (T.extend P).carrier :=
  (T.extGraph P).isColourSystem_view 1

theorem pos_mem (hT : IsColourSystem T.carrier) {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) :
    T.pos P x ∈ T.carrier :=
  tGraph_walk_mem hT.one_mem (walk_extend hx)

theorem len_pos_le {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) : len (T.pos P x) ≤ len x := by
  have := tGraph_len_walk_le (walk_extend hx); simpa using this

theorem colours_extend (hT : IsColourSystem T.carrier) {x : FreeCox k}
    (hx : x ∈ (T.extend P).carrier) (c : Fin k) :
    c ∈ colours (T.extend P).carrier x ↔ T.pos P x * gen c ∈ T.carrier ∨ c = P (T.pos P x) := by
  rw [extend, (T.extGraph P).colours_view (walk_extend hx), extGraph, tGraph_step_isSome]
  simp [pos_mem hT hx]

theorem walk_extend_mul_gen {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) (c : Fin k) :
    (T.extGraph P).walk 1 (x * gen c) = (T.extGraph P).step (T.pos P x) c :=
  (T.extGraph P).walk_mul_gen (walk_extend hx) c

theorem pos_mul_gen_of_mem (hT : IsColourSystem T.carrier) {x : FreeCox k}
    (hx : x ∈ (T.extend P).carrier) {c : Fin k} (hc : T.pos P x * gen c ∈ T.carrier) :
    x * gen c ∈ (T.extend P).carrier ∧ T.pos P (x * gen c) = T.pos P x * gen c := by
  apply mem_extend_of_walk
  rw [walk_extend_mul_gen hx, extGraph, tGraph_step_of_mem (pos_mem hT hx) hc]

theorem pos_mul_gen_of_loop (hT : IsColourSystem T.carrier) (hP : IsPicker T P)
    {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) :
    x * gen (P (T.pos P x)) ∈ (T.extend P).carrier ∧ T.pos P (x * gen (P (T.pos P x))) = T.pos P x := by
  apply mem_extend_of_walk
  rw [walk_extend_mul_gen hx, extGraph,
    tGraph_step_of_loop (pos_mem hT hx) (hP _ (pos_mem hT hx)).1 rfl]

/-- Lemma 7: the extension of an `h`-template by a 1-colour picker is an `(h+1)`-template, with
`C(X, x) = C(T, p(x)) + P(p(x))`. -/
theorem isTemplate_extend (hT : IsTemplate h T) (hP : IsPicker T P) : IsTemplate (h + 1) (T.extend P) := by
  classical
  refine ⟨isColourSystem_extend, fun x hx => ?_, fun x hx => ?_⟩
  · have hpos := pos_mem hT.1 hx
    have : colours (T.extend P).carrier x = insert (P (T.pos P x)) (colours T.carrier (T.pos P x)) := by
      ext c
      rw [colours_extend hT.1 hx, Finset.mem_insert, mem_colours]
      tauto
    rw [this, Finset.card_insert_of_notMem, hT.card_colours hpos]
    rw [mem_colours]; exact (hP _ hpos).1
  · have hpos := pos_mem hT.1 hx
    rw [colours_extend hT.1 hx, extend_forb]
    rintro (h1 | h1)
    · exact hT.forb_not_mem hpos h1
    · exact (hP _ hpos).2 h1.symm

/-- Corollary 11: an extension has the same realisations as the template. -/
theorem real_extend (hT : IsTemplate h T) (hP : IsPicker T P) {x : FreeCox k}
    (hx : x ∈ (T.extend P).carrier) : (T.extend P).real x = T.real (T.pos P x) := by
  have hX := isTemplate_extend hT hP
  refine ((T.extend P).realGraph.view_map_of_reachable T.realGraph (T.pos P) x ?_).symm
  intro y b hb c
  have hbX : b ∈ (T.extend P).carrier := realGraph_walk_mem hx hb
  have hs := pos_mem hT.1 hbX
  by_cases h1 : T.pos P b * gen c ∈ T.carrier
  · obtain ⟨h2, h3⟩ := pos_mul_gen_of_mem hT.1 hbX h1
    rw [realGraph, realGraph, tGraph_step_of_mem hs h1, tGraph_step_of_mem hbX h2, Option.map_some,
      h3]
  · by_cases h2 : c = P (T.pos P b)
    · obtain ⟨h3, h4⟩ := pos_mul_gen_of_loop hT.1 hP hbX
      rw [← h2] at h3 h4
      rw [realGraph, realGraph, tGraph_step_of_mem hbX h3, Option.map_some, h4,
        tGraph_step_of_loop hs h1]
      simp only [Set.mem_ofPred_eq]
      rw [h2]; exact ((hP _ hs).2)
    · have h3 : b * gen c ∉ (T.extend P).carrier := by
        intro h3
        have := (colours_extend hT.1 hbX c).1 (mem_colours.2 h3)
        tauto
      rw [realGraph, realGraph]
      by_cases h4 : c = T.forb (T.pos P b)
      · rw [tGraph_step_of_not_mem hs h1 (by simpa using h4),
          tGraph_step_of_not_mem hbX h3 (by simpa [extend_forb] using h4), Option.map_none]
      · rw [tGraph_step_of_loop hs h1 (by simpa using h4),
          tGraph_step_of_loop hbX h3 (by simpa [extend_forb] using h4), Option.map_some]

/-- Lemma 8 (symmetry of extensions): the extension seen from `x` only depends on `p(x)`. -/
theorem walk_extend_mul {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) (y : FreeCox k) :
    (T.extGraph P).walk 1 (x * y) = (T.extGraph P).walk (T.pos P x) y :=
  (T.extGraph P).walk_mul (walk_extend hx) y

theorem extend_symm {x : FreeCox k} (hx : x ∈ (T.extend P).carrier) (hp : T.pos P x = 1) :
    x • (T.extend P) = T.extend P := by
  have hw : ∀ y, (T.extGraph P).walk 1 (x⁻¹ * y) = (T.extGraph P).walk 1 y := by
    intro y
    have hx' : (T.extGraph P).walk 1 x⁻¹ = some 1 := by
      have := (T.extGraph P).walk_inv (walk_extend hx); rwa [hp] at this
    rw [(T.extGraph P).walk_mul hx']
  ext y
  · rw [smul_carrier, mem_smul]
    simp only [extend, ColouredGraph.view, Set.mem_ofPred_eq, hw]
  · simp only [smul_forb, extend_forb, pos, hw]

end ext

end Template

end Papers.PODC2012.MaximalMatching
