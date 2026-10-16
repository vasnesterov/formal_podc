import Papers.PODC2012.MaximalMatching.Templates

/-!
# Outputs of an algorithm on templates (Corollaries 10–11, Lemma 12)

Standing assumptions of Theorem 6 (`Good A r`): `A` has running time `r` and finds a maximal
matching in every `d`-regular colour system, `d = k - 1`. Under these assumptions the template
outputs `out A T t` satisfy (M1)–(M3) "up to half-loops", and Lemma 12 holds.
-/

namespace Papers.PODC2012.MaximalMatching

open Cslib.ColourSystem FreeCox Pointwise Template

variable {k : ℕ}

/-- The standing assumptions of Theorem 6: `A` has running time `r` and finds a maximal matching
in every `(k-1)`-regular `k`-colour system. -/
structure Good (A : Algorithm k) (r : ℕ) : Prop where
  time : HasRunningTime A r
  mm : ∀ V, IsColourSystem V → IsRegular V (k - 1) → FindsMaximalMatching A V

namespace Good

variable {A : Algorithm k} {r h : ℕ} (hA : Good A r) {T : Template k} {t : FreeCox k}
include hA

theorem findsMM (hT : IsTemplate h T) (ht : t ∈ T.carrier) : FindsMaximalMatching A (T.real t) :=
  hA.mm _ (isColourSystem_real T t) (isRegular_real hT ht)

/-- Corollary 10: every node of the realisation mapped to `b` outputs `A(T, τ, b)`. -/
theorem apply_real {x b : FreeCox k} (hb : T.realGraph.walk t x = some b) :
    A (T.real t) x = T.out A b := by
  rw [hA.time.apply_eq (isColourSystem_real T t) (T.realGraph.mem_view.2 ⟨b, hb⟩),
    real_inv_smul hb]
  rfl

theorem out_ne_forb (hT : IsTemplate h T) (ht : t ∈ T.carrier) {c : Fin k}
    (h : T.out A t = some c) : c ≠ T.forb t := by
  have := ((hA.findsMM hT ht) 1 (T.realGraph.one_mem_view t)).1 c h
  rwa [colours_real_one hT ht] at this

/-- (M2) for templates. -/
theorem out_mul_gen (hT : IsTemplate h T) (ht : t ∈ T.carrier) {c : Fin k}
    (h : T.out A t = some c) (hc : t * gen c ∈ T.carrier) : T.out A (t * gen c) = some c := by
  have := ((hA.findsMM hT ht) 1 (T.realGraph.one_mem_view t)).2.1 c h
  rwa [one_mul, hA.apply_real (b := t * gen c)
    (by rw [ColouredGraph.walk_gen, realGraph, tGraph_step_of_mem ht hc])] at this

theorem out_ne_none_of_free (hT : IsTemplate h T) (ht : t ∈ T.carrier) {c : Fin k}
    (hc : T.Free t c) : T.out A t ≠ none := by
  intro hnone
  have := ((hA.findsMM hT ht) 1 (T.realGraph.one_mem_view t)).2.2 hnone c
    ((colours_real_one hT ht c).2 hc.2)
  rw [one_mul, hA.apply_real (b := t)
    (by rw [ColouredGraph.walk_gen, realGraph, tGraph_step_of_loop ht hc.1 hc.2])] at this
  exact this hnone

/-- Lemma 12: if `h < d`, every node of an `h`-template is matched (possibly along a half-loop). -/
theorem out_ne_none (hT : IsTemplate h T) (hh : h + 1 < k) (ht : t ∈ T.carrier) :
    T.out A t ≠ none := by
  obtain ⟨c, hc⟩ := hT.exists_free hh ht
  exact hA.out_ne_none_of_free hT ht hc

theorem out_cases (hT : IsTemplate h T) (ht : t ∈ T.carrier) {c : Fin k}
    (h : T.out A t = some c) : c ∈ colours T.carrier t ∨ T.Free t c := by
  by_cases hc : t * gen c ∈ T.carrier
  · exact Or.inl (mem_colours.2 hc)
  · exact Or.inr ⟨hc, hA.out_ne_forb hT ht h⟩

/-- Template outputs only depend on the radius-`(r+1)` neighbourhood in the template and the
forbidden colours in the radius-`r` neighbourhood. -/
theorem out_eq_of_agree {T' : Template k} {t' : FreeCox k} (ht : t ∈ T.carrier)
    (hball : ∀ z, len z ≤ r + 1 → (t * z ∈ T.carrier ↔ t' * z ∈ T'.carrier))
    (hforb : ∀ z, len z ≤ r → t * z ∈ T.carrier → T.forb (t * z) = T'.forb (t' * z)) :
    T.out A t = T'.out A t' := by
  have e1 := out_inv_smul (T := T) A t 1
  have e2 := out_inv_smul (T := T') A t' 1
  rw [mul_one] at e1 e2
  rw [← e1, ← e2, out, out]
  apply hA.time.apply_one_eq (isColourSystem_real _ _) (isColourSystem_real _ _)
  apply ColouredGraph.ball_view_eq_of_agree
  intro x b hx hb c
  have h1 : (1 : FreeCox k) ∈ (t⁻¹ • T).carrier := by
    rw [smul_carrier, mem_inv_smul, mul_one]; exact ht
  have hbT : b ∈ (t⁻¹ • T).carrier := realGraph_walk_mem h1 hb
  have hlen : len b ≤ len x := by
    have := tGraph_len_walk_le hb; simpa using this
  have hbT' : b ∈ (t'⁻¹ • T').carrier := by
    rw [smul_carrier, mem_inv_smul] at hbT ⊢
    exact (hball b (by omega)).1 hbT
  apply tGraph_step_congr
  · exact ⟨fun _ => hbT', fun _ => hbT⟩
  · simp only [smul_carrier, mem_inv_smul]
    exact hball _ (by have := len_mul_gen_le b c; omega)
  · simp only [smul_forb, inv_inv, Set.mem_ofPred_eq]
    rw [smul_carrier, mem_inv_smul] at hbT
    rw [hforb b (by omega) hbT]

end Good

end Papers.PODC2012.MaximalMatching
