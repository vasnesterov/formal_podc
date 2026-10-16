import Papers.PODC2020.NonEquivocation.Model

/-!
# Algorithm 1 and Theorem 4.2 (`t ≤ 1`)

Madsen–Debois, PODC 2020, Section 4.1. Algorithm 1 (`WNE_{t=1}`), for `p` and source `q`:

1. if `p = q`, return `p`'s private value;
2. if `q` sent `p` a value in round 1, return it;
3. if some `r` reports in round 2 that `q` sent it a value `≠ ⟨⊥⟩`, return that value;
4. otherwise return `⟨⊥⟩`.

In line 5, `r` must range over processes other than `p` and `q`: with the paper's convention
`σ_p(p|p|q) = σ_p(p|q) = ⊥ ≠ ⟨⊥⟩`, the choice `r = p` (or `r = q`) would make line 6 return
`⊥ ∉ V`. We read it this way (`alg1`). `theorem_4_2`: with 2 rounds and at most one faulty
process, `alg1` solves interactive consistency under weak non-equivocation — for every `n` (the
paper assumes `n > 1`, which is not needed).
-/

namespace NonEquivocation

open Classical

variable {P V : Type*} [Fintype P] [OmitVal V]

/-- **Algorithm 1**. -/
noncomputable def alg1 : Alg P V := fun p τ q =>
  if p = q then rep (τ [])
  else if (τ [q]).isSome then rep (τ [q])
  else if h : ∃ r, r ≠ p ∧ r ≠ q ∧ τ [r, q] ≠ some omitted then rep (τ [h.choose, q])
  else omitted

/-- **Theorem 4.2**: in the weak non-equivocation fault model, interactive consistency is solvable
(by Algorithm 1, in two rounds) if `t ≤ 1`. -/
theorem theorem_4_2 {t : ℕ} (ht : t ≤ 1) : SolvesIC wne 2 t (alg1 (P := P) (V := V)) := by
  intro F σ hF hm hpriv
  have hnf := hm.1
  have val : ∀ p q, p ∉ F → q ∉ F → σ [q] = some (alg1 p (view 2 σ p) q) := by
    intro p q hp hq
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hpriv q hq)
    by_cases hpq : p = q
    · subst hpq; simp [alg1, view, ha]
    · have := hnf q (Finset.mem_univ _) hq p (Finset.mem_univ _) [] (by simp)
        (seq_pair.2 hpq) (by simp)
      simp [alg1, hpq, view, this, ha]
  refine ⟨val, fun p p' q hp hp' => ?_⟩
  by_cases hq : q ∉ F
  · have h1 := val p q hp hq
    rw [val p' q hp' hq] at h1
    exact (Option.some.inj h1).symm
  push Not at hq
  -- `q` is the only faulty process
  have honly : ∀ r, r ≠ q → r ∉ F := by
    intro r hrq hr
    have : ({r, q} : Finset P) ⊆ F := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rw [Finset.card_pair hrq] at this
    omega
  -- the values sent by `q` in round 1 agree
  have wne1 : ∀ r r' a b, r ≠ q → r' ≠ q → σ [r, q] = some a → σ [r', q] = some b → a = b := by
    intro r r' a b hr hr' ha hb
    have := hm.2 q (Finset.mem_univ _) r (Finset.mem_univ _) r' (Finset.mem_univ _) [] (by simp)
      (seq_pair.2 hr) (seq_pair.2 hr') (by simp) (by simp [ha]) (by simp [hb])
    rw [ha, hb] at this
    exact Option.some.inj this
  -- the common outcome
  let T : V := if h : ∃ b r, r ≠ q ∧ σ [r, q] = some b then h.choose else omitted
  have relay : ∀ x r, x ≠ r → r ≠ q → σ [x, r, q] = some (rep (σ [r, q])) := fun x r hxr hrq =>
    hnf r (Finset.mem_univ _) (honly r hrq) x (Finset.mem_univ _) [q] (by simp)
      (by simp [Seq, hxr, hrq]) (by simp)
  have key : ∀ x, x ≠ q → alg1 x (view 2 σ x) q = T := by
    intro x hxq
    have v1 : view 2 σ x [q] = σ [x, q] := view_of_le (by simp)
    have v2 : ∀ r, view 2 σ x [r, q] = σ [x, r, q] := fun r => view_of_le (by simp)
    simp only [alg1, hxq, ↓reduceIte, v1, v2]
    cases hx : σ [x, q] with
    | some a =>
      simp only [Option.isSome_some, ↓reduceIte, rep_some, T]
      have hex : ∃ b r, r ≠ q ∧ σ [r, q] = some b := ⟨a, x, hxq, hx⟩
      simp only [hex, ↓reduceDIte]
      obtain ⟨r, hr, hb⟩ := hex.choose_spec
      exact wne1 x r _ _ hxq hr hx hb
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      split_ifs with hc
      · obtain ⟨hr1, hr2, hr3⟩ := hc.choose_spec
        rw [relay x _ (Ne.symm hr1) hr2] at hr3 ⊢
        simp only [rep_some]
        cases hb : σ [hc.choose, q] with
        | none => rw [hb] at hr3; simp at hr3
        | some b =>
          simp only [rep_some, T]
          have hex : ∃ b r, r ≠ q ∧ σ [r, q] = some b := ⟨b, _, hr2, hb⟩
          simp only [hex, ↓reduceDIte]
          obtain ⟨r, hr, hb'⟩ := hex.choose_spec
          exact wne1 _ r _ _ hr2 hr hb hb'
      · simp only [T]
        split_ifs with hex
        · obtain ⟨r, hr, hb⟩ := hex.choose_spec
          by_contra hne
          have hrx : r ≠ x := fun h => by rw [h, hx] at hb; simp at hb
          exact hc ⟨r, hrx, hr, by rw [relay x r (Ne.symm hrx) hr, hb]; simpa using Ne.symm hne⟩
        · rfl
  rw [key p (fun h => hp (h ▸ hq)), key p' (fun h => hp' (h ▸ hq))]

end NonEquivocation
