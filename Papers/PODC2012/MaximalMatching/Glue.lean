import Papers.PODC2012.MaximalMatching.Outputs

/-!
# Gluing two templates along the edge `{e, χ}` (§3.9 of Hirvonen–Suomela)

`glue χ K L` takes the part `K₁ = prune(K, χ)` of `K` on the `e`-side of the edge `{e, χ}` and the
part `L₁ = χ prune(χ̄L, χ)` of `L` on the `χ`-side; the forbidden colours are inherited. We prove
that the result is again a template (observation (a)) and the compatibility observations (d) and
(e) (`compatible_glue_left`, `compatible_glue_right`).
-/

namespace Papers.PODC2012.MaximalMatching

open Cslib.ColourSystem FreeCox Pointwise Template

variable {k : ℕ}

open Classical in
/-- `X = K₁ ∪ L₁` with `ξ = κ` on `K₁` and `ξ = λ` on `L₁`. -/
noncomputable def glue (χ : Fin k) (K L : Template k) : Template k :=
  ⟨{x | if startsWith χ x then x ∈ L.carrier else x ∈ K.carrier},
    fun x => if startsWith χ x then L.forb x else K.forb x⟩

section

variable {χ : Fin k} {K L : Template k}

theorem mem_glue_of_not {x : FreeCox k} (hx : ¬ startsWith χ x) :
    x ∈ (glue χ K L).carrier ↔ x ∈ K.carrier := by
  simp [glue, hx]

theorem mem_glue_of_starts {x : FreeCox k} (hx : startsWith χ x) :
    x ∈ (glue χ K L).carrier ↔ x ∈ L.carrier := by
  simp [glue, hx]

theorem glue_forb_of_not {x : FreeCox k} (hx : ¬ startsWith χ x) :
    (glue χ K L).forb x = K.forb x := by
  simp [glue, hx]

theorem glue_forb_of_starts {x : FreeCox k} (hx : startsWith χ x) :
    (glue χ K L).forb x = L.forb x := by
  simp [glue, hx]

variable (hK : IsColourSystem K.carrier) (hL : IsColourSystem L.carrier)
  (hχK : gen χ ∈ K.carrier) (hχL : gen χ ∈ L.carrier)
include hK hL hχK hχL

theorem isColourSystem_glue : IsColourSystem (glue χ K L).carrier := by
  refine ⟨(mem_glue_of_not (not_startsWith_one χ)).2 hK.one_mem, fun x hx c hc => ?_⟩
  by_cases hs : startsWith χ (x * gen c) ↔ startsWith χ x
  · by_cases hx' : startsWith χ x
    · rw [mem_glue_of_starts hx'] at hx
      rw [mem_glue_of_starts (hs.2 hx')]
      exact hL.mul_gen_mem hx hc
    · rw [mem_glue_of_not hx'] at hx
      rw [mem_glue_of_not (fun h => hx' (hs.1 h))]
      exact hK.mul_gen_mem hx hc
  · obtain ⟨rfl, h1 | rfl⟩ := startsWith_mul_gen (c := χ) (c' := c) (x := x) (by tauto)
    · subst h1; simp at hc
    · rw [gen_mul_gen]
      exact (mem_glue_of_not (not_startsWith_one _)).2 hK.one_mem

omit hK hL in
theorem colours_glue_of_not {x : FreeCox k} (hx : ¬ startsWith χ x) :
    colours (glue χ K L).carrier x = colours K.carrier x := by
  ext c
  rw [mem_colours, mem_colours]
  by_cases hs : startsWith χ (x * gen c)
  · obtain ⟨rfl, h1 | rfl⟩ := startsWith_mul_gen (c := χ) (c' := c) (x := x) (by tauto)
    · subst h1
      rw [one_mul, mem_glue_of_starts (startsWith_gen.2 rfl)]
      exact ⟨fun _ => hχK, fun _ => hχL⟩
    · exact absurd (startsWith_gen.2 rfl) hx
  · exact mem_glue_of_not hs

theorem colours_glue_of_starts {x : FreeCox k} (hx : startsWith χ x) :
    colours (glue χ K L).carrier x = colours L.carrier x := by
  ext c
  rw [mem_colours, mem_colours]
  by_cases hs : startsWith χ (x * gen c)
  · exact mem_glue_of_starts hs
  · obtain ⟨rfl, h1 | rfl⟩ := startsWith_mul_gen (c := χ) (c' := c) (x := x) (by tauto)
    · subst h1; exact absurd hx (not_startsWith_one _)
    · rw [gen_mul_gen, mem_glue_of_not (not_startsWith_one _)]
      exact ⟨fun _ => hL.one_mem, fun _ => hK.one_mem⟩

/-- Observation (a) of §3.9: `(X, ξ)` is an `(h+1)`-template. -/
theorem isTemplate_glue {h : ℕ} (tK : IsTemplate h K) (tL : IsTemplate h L) :
    IsTemplate h (glue χ K L) := by
  refine ⟨isColourSystem_glue hK hL hχK hχL, fun x hx => ?_, fun x hx => ?_⟩
  · by_cases hs : startsWith χ x
    · rw [colours_glue_of_starts hK hL hχK hχL hs]
      exact tL.card_colours ((mem_glue_of_starts hs).1 hx)
    · rw [colours_glue_of_not hχK hχL hs]
      exact tK.card_colours ((mem_glue_of_not hs).1 hx)
  · by_cases hs : startsWith χ x
    · rw [colours_glue_of_starts hK hL hχK hχL hs, glue_forb_of_starts hs]
      exact tL.2.2 x ((mem_glue_of_starts hs).1 hx)
    · rw [colours_glue_of_not hχK hχL hs, glue_forb_of_not hs]
      exact tK.2.2 x ((mem_glue_of_not hs).1 hx)

end

/-! ### Compatibility of the glued template (observations (d), (e)) -/

section compat

variable {χ : Fin k} {K L : Template k} {h : ℕ}

/-- `χ`-symmetry of a template (`χ̄K = K`, `χ̄κ = κ`). -/
def SymmAt (χ : Fin k) (K : Template k) : Prop := gen χ • K = K

theorem SymmAt.mem_iff (hs : SymmAt χ K) (x : FreeCox k) :
    gen χ * x ∈ K.carrier ↔ x ∈ K.carrier := by
  conv_rhs => rw [← hs]
  rw [smul_carrier, mem_smul, inv_gen]

theorem SymmAt.forb_eq (hs : SymmAt χ K) (x : FreeCox k) : K.forb (gen χ * x) = K.forb x := by
  conv_rhs => rw [← hs]
  rw [smul_forb, inv_gen]

/-- If `x` starts with `χ`, write `x = χ w` with `|w| = |x| - 1`. -/
theorem len_gen_mul_of_startsWith {x : FreeCox k} (hx : startsWith χ x) :
    len (gen χ * x) + 1 = len x := by
  have := le_len_gen_mul x χ
  unfold startsWith at hx
  omega

/-- Observation (d): for `y ∈ K₁`, `(ȳX, ȳξ)` and `(ȳK, ȳκ)` are `(h+1)`-compatible. -/
theorem compatible_glue_left (hc : Compatible h K L) (sK : SymmAt χ K) (sL : SymmAt χ L)
    {y : FreeCox k} (hy : ¬ startsWith χ y) :
    Compatible (h + 1) (y⁻¹ • K) (y⁻¹ • glue χ K L) := by
  -- for `z` with `yz` starting with `χ`: `|z| = |y| + |yz|`
  have key : ∀ z, startsWith χ (y * z) → len z = len y + len (y * z) := by
    intro z hz
    have := len_inv_mul_of_startsWith hz hy
    rwa [inv_mul_cancel_left] at this
  constructor
  · ext z
    simp only [mem_ball, smul_carrier, mem_inv_smul]
    refine and_congr_left fun hz => ?_
    by_cases hs : startsWith χ (y * z)
    · rw [mem_glue_of_starts hs]
      have h1 := key z hs
      have h2 := len_gen_mul_of_startsWith hs
      rw [← sK.mem_iff, ← sL.mem_iff]
      exact mem_iff_of_ball_eq hc.1 (by omega)
    · rw [mem_glue_of_not hs]
  · intro s hs hs1
    rw [smul_carrier, mem_inv_smul] at hs
    simp only [smul_forb, inv_inv]
    by_cases hst : startsWith χ (y * s)
    · rw [glue_forb_of_starts hst, ← sK.forb_eq, ← sL.forb_eq (y * s)]
      have h1 := key s hst
      have h2 := len_gen_mul_of_startsWith hst
      exact hc.2 _ ((sK.mem_iff _).2 hs) (by omega)
    · rw [glue_forb_of_not hst]

/-- Observation (e): for `y ∈ L₁`, `(ȳX, ȳξ)` and `(ȳL, ȳλ)` are `(h+1)`-compatible. -/
theorem compatible_glue_right (hc : Compatible h K L) {y : FreeCox k} (hy : startsWith χ y) :
    Compatible (h + 1) (y⁻¹ • L) (y⁻¹ • glue χ K L) := by
  have key : ∀ z, ¬ startsWith χ (y * z) → len z = len (y * z) + len y := by
    intro z hz
    have := len_inv_mul_of_startsWith hy hz
    rwa [mul_inv_rev, inv_mul_cancel_right, len_inv] at this
  have hy1 : 1 ≤ len y := by
    by_contra h0
    rw [Nat.not_le, Nat.lt_one_iff, len_eq_zero] at h0
    subst h0; exact not_startsWith_one χ hy
  constructor
  · ext z
    simp only [mem_ball, smul_carrier, mem_inv_smul]
    refine and_congr_left fun hz => ?_
    by_cases hs : startsWith χ (y * z)
    · rw [mem_glue_of_starts hs]
    · rw [mem_glue_of_not hs]
      have h1 := key z hs
      exact (mem_iff_of_ball_eq hc.1 (by omega)).symm
  · intro s hs hs1
    rw [smul_carrier, mem_inv_smul] at hs
    simp only [smul_forb, inv_inv]
    by_cases hst : startsWith χ (y * s)
    · rw [glue_forb_of_starts hst]
    · rw [glue_forb_of_not hst]
      have h1 := key s hst
      exact (hc.2 _ ((mem_iff_of_ball_eq hc.1 (by omega)).2 hs) (by omega)).symm

end compat

end Papers.PODC2012.MaximalMatching
