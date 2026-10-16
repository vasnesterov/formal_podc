import Papers.PODC2019.AutomaticSpeedup.SuperweakDefs

/-!
# The trit description of `Π'_{1/2}` for superweak `k`-colouring (Brandt, PODC 2019, §5.1)

"An Equivalent Description": the problem `Π'_{1/2} = (superweak k).edgeStepMax` maps to the trit
problem `tritHalf k` via `toTrit`, in the direction needed for the speedup lemma (Lemma 4):

* `edgeAllMax_superweak`: every maximal edge pair `{Y, Z}` (Property 5) is *trit-shaped*: in every
  colour `c`, `{p | (c, p) ∈ Y}` is `{⊸}`, `{⊸, •}` or `{→, ⊸, •}` (`TritShaped`), and the
  colour-`c` parts of `Y` and `Z` are `({→, ⊸, •}, {⊸})`, `({⊸, •}, {⊸, •})` or `({⊸}, {→, ⊸, •})`;
  hence `{toTrit Y, toTrit Z}` sums to `22…2` (`toTrit_mem_g`).
  The paper's listing of `g'_{1/2}` only mentions the first two cases per colour; the third
  (swapped) case is also maximal and occurs (in a colour-dependent way) — the trit description,
  which is symmetric, handles it.
* `toTrit_mem_h`: if some choice from `Y_0, …, Y_{d-1}` is a good superweak node configuration
  (Property 2), the trit sequences form a node configuration of `tritHalf k`. Trit-shapedness is
  not needed for this direction.
* `ViewSystem.solvesE_toTrit`: an edge-view algorithm for `Π'_{1/2}` composed with `toTrit` solves
  `tritHalf k`.
-/

namespace AutomaticSpeedup

open Problem

variable {k Δ : ℕ}

/-- Edge configurations of superweak colouring. -/
theorem superweak_g_iff {a b : Fin k × Ptr} :
    ({a, b} : Multiset (Fin k × Ptr)) ∈ (superweak k).g Δ ↔
      a.1 ≠ b.1 ∨ (a.2 = .none ∧ b.2 = .none) ∨ a.2 = .accept ∨ b.2 = .accept := by
  constructor
  · rintro ⟨a', b', he, h⟩
    rcases pair_eq_pair_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · rcases h with h | h | h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
  · intro h; exact ⟨a, b, rfl, h⟩

/-- Pointer compatibility on an edge whose endpoints have the same colour. -/
def PtrOk (p q : Ptr) : Prop := (p = .none ∧ q = .none) ∨ p = .accept ∨ q = .accept

theorem superweak_g_same {c : Fin k} {p q : Ptr} :
    ({(c, p), (c, q)} : Multiset (Fin k × Ptr)) ∈ (superweak k).g Δ ↔ PtrOk p q := by
  rw [superweak_g_iff]; simp [PtrOk]

theorem superweak_g_of_ne {a b : Fin k × Ptr} (h : a.1 ≠ b.1) :
    ({a, b} : Multiset (Fin k × Ptr)) ∈ (superweak k).g Δ :=
  superweak_g_iff.2 (Or.inl h)

/-- A `Π'_{1/2}` label is *trit-shaped* if in every colour `c` its colour-`c` part is `{⊸}`,
`{⊸, •}` or `{→, ⊸, •}`, i.e. it contains `(c, ⊸)`, and `(c, •)` whenever it contains `(c, →)`.
On trit-shaped labels `toTrit` is injective (the paper's bijection). -/
def TritShaped (Y : Set (Fin k × Ptr)) : Prop :=
  ∀ c, (c, Ptr.accept) ∈ Y ∧ ((c, Ptr.demand) ∈ Y → (c, Ptr.none) ∈ Y)

theorem toTrit_apply (Y : Set (Fin k × Ptr)) (c : Fin k) [Decidable ((c, Ptr.demand) ∈ Y)]
    [Decidable ((c, Ptr.none) ∈ Y)] :
    toTrit Y c = if (c, Ptr.demand) ∈ Y then 2 else if (c, Ptr.none) ∈ Y then 1 else 0 := by
  unfold toTrit; congr

/-- Membership facts for a maximal edge pair in one colour. -/
private theorem edgeAllMax_facts {Y Z : Set (Fin k × Ptr)} (h : (superweak k).EdgeAllMax Δ Y Z)
    (c : Fin k) :
    (∀ p q, (c, p) ∈ Y → (c, q) ∈ Z → PtrOk p q) ∧
      (∀ p, (c, p) ∉ Y → ∃ q, (c, q) ∈ Z ∧ ¬ PtrOk p q) := by
  refine ⟨fun p q hp hq => superweak_g_same.1 (h.1.2.2 _ hp _ hq), fun p hp => ?_⟩
  by_contra hne
  push Not at hne
  apply h.2.1 (insert (c, p) Y) (Set.ssubset_insert hp)
  refine ⟨fun _ _ => trivial, fun _ _ => trivial, fun y hy z hz => ?_⟩
  rcases hy with rfl | hy
  · obtain ⟨z1, z2⟩ := z
    by_cases hc : c = z1
    · subst hc; exact superweak_g_same.2 (hne z2 hz)
    · exact superweak_g_of_ne hc
  · exact h.1.2.2 y hy z hz

theorem PtrOk.accept_left (q : Ptr) : PtrOk .accept q := Or.inr (Or.inl rfl)

theorem not_ptrOk_demand_demand : ¬ PtrOk .demand .demand := by simp [PtrOk]
theorem not_ptrOk_demand_none : ¬ PtrOk .demand .none := by simp [PtrOk]
theorem not_ptrOk_none_demand : ¬ PtrOk .none .demand := by simp [PtrOk]

private theorem not_ptrOk_none {q : Ptr} (h : ¬ PtrOk .none q) : q = .demand := by
  cases q <;> simp_all [PtrOk]

private theorem not_ptrOk_demand {q : Ptr} (h : ¬ PtrOk .demand q) : q = .demand ∨ q = .none := by
  cases q <;> simp_all [PtrOk]

/-- **"An Equivalent Description" (edges).** Both labels of a maximal edge pair of `Π'_{1/2}`
(Property 5) are trit-shaped, and their trit sequences sum to `22…2` position-wise. -/
theorem edgeAllMax_superweak {Y Z : Set (Fin k × Ptr)} (h : (superweak k).EdgeAllMax Δ Y Z) :
    TritShaped Y ∧ TritShaped Z ∧ ∀ c, (toTrit Y c).val + (toTrit Z c).val = 2 := by
  classical
  have hY := edgeAllMax_facts h
  have hZ := edgeAllMax_facts h.symm
  have shape : ∀ {Y Z : Set (Fin k × Ptr)},
      (∀ c, (∀ p q, (c, p) ∈ Y → (c, q) ∈ Z → PtrOk p q) ∧
        (∀ p, (c, p) ∉ Y → ∃ q, (c, q) ∈ Z ∧ ¬ PtrOk p q)) → TritShaped Y := by
    intro Y Z hY c
    refine ⟨?_, fun hd => ?_⟩
    · by_contra ha
      obtain ⟨q, -, hq⟩ := (hY c).2 _ ha
      exact hq (PtrOk.accept_left q)
    · by_contra hn
      obtain ⟨q, hq, hq'⟩ := (hY c).2 _ hn
      rw [not_ptrOk_none hq'] at hq
      exact not_ptrOk_demand_demand ((hY c).1 _ _ hd hq)
  refine ⟨shape hY, shape hZ, fun c => ?_⟩
  obtain ⟨E1, M1⟩ := hY c
  obtain ⟨E2, M2⟩ := hZ c
  rw [toTrit_apply, toTrit_apply]
  by_cases dY : (c, Ptr.demand) ∈ Y
  · have ndZ : (c, Ptr.demand) ∉ Z := fun hz => not_ptrOk_demand_demand (E1 _ _ dY hz)
    have nnZ : (c, Ptr.none) ∉ Z := fun hz => not_ptrOk_demand_none (E1 _ _ dY hz)
    simp [dY, ndZ, nnZ]
  · by_cases nY : (c, Ptr.none) ∈ Y
    · have ndZ : (c, Ptr.demand) ∉ Z := fun hz => not_ptrOk_none_demand (E1 _ _ nY hz)
      have nZ : (c, Ptr.none) ∈ Z := by
        obtain ⟨q, hq, hq'⟩ := M1 _ dY
        rcases not_ptrOk_demand hq' with rfl | rfl
        · exact absurd hq ndZ
        · exact hq
      simp [dY, nY, ndZ, nZ]
    · have dZ : (c, Ptr.demand) ∈ Z := by
        obtain ⟨q, hq, hq'⟩ := M1 _ nY
        rwa [not_ptrOk_none hq'] at hq
      simp [dY, nY, dZ]

/-- `{toTrit Y, toTrit Z}` is an edge configuration of `tritHalf k` for every maximal edge pair. -/
theorem toTrit_mem_g {Y Z : Set (Fin k × Ptr)} (h : (superweak k).EdgeAllMax Δ Y Z) :
    ({toTrit Y, toTrit Z} : Multiset (Trit k)) ∈ (tritHalf k).g Δ :=
  ⟨_, _, rfl, (edgeAllMax_superweak h).2.2⟩

theorem card_filter_range_le {d : ℕ} {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ i < d, P i → Q i) :
    Multiset.card ((Multiset.range d).filter P) ≤ Multiset.card ((Multiset.range d).filter Q) := by
  have e : (Multiset.range d).filter P = (Multiset.range d).filter fun i => P i ∧ Q i :=
    Multiset.filter_congr fun i hi =>
      ⟨fun hp => ⟨hp, h i (Multiset.mem_range.1 hi) hp⟩, And.left⟩
  rw [e]
  exact Multiset.card_le_card (Multiset.monotone_filter_right _ fun _ => And.right)

/-- **"An Equivalent Description" (nodes).** If one can choose one label from each of
`Y 0, …, Y (d-1)` forming a good superweak node configuration (Property 2), then the trit
sequences of the `Y i` form a node configuration of `tritHalf k`. -/
theorem toTrit_mem_h {d : ℕ} {Y : ℕ → Set (Fin k × Ptr)}
    (h : (superweak k).NodeEx Δ ((Multiset.range d).map Y)) :
    (Multiset.range d).map (toTrit ∘ Y) ∈ (tritHalf k).h Δ := by
  classical
  rcases isEmpty_or_nonempty (Fin k × Ptr) with hL | hL
  · exfalso
    obtain ⟨-, -, m', -, hm'⟩ := h
    have hm0 : m' = 0 := Multiset.eq_zero_of_forall_notMem fun a => isEmptyElim a
    subst hm0
    simp [superweak] at hm'
  obtain ⟨-, -, y, hy, hm⟩ := nodeEx_map_range.1 h
  obtain ⟨hcard, ⟨c, hc⟩, hcnt⟩ := hm
  simp only [Multiset.card_map, Multiset.card_range] at hcard
  have hc' : ∀ i < d, y i = (c, (y i).2) := by
    intro i hi
    have := hc (y i) (Multiset.mem_map.2 ⟨i, Multiset.mem_range.2 hi, rfl⟩)
    exact Prod.ext this rfl
  refine ⟨by simpa using hcard, c, ?_⟩
  simp only [countAt, Multiset.filter_map, Multiset.card_map] at hcnt ⊢
  have h0 : Multiset.card ((Multiset.range d).filter ((fun a : Trit k => a c = 0) ∘ toTrit ∘ Y)) ≤
      Multiset.card ((Multiset.range d).filter ((fun x : Fin k × Ptr => x.2 = Ptr.accept) ∘ y)) := by
    refine card_filter_range_le fun i hi hP => ?_
    simp only [Function.comp_apply] at hP ⊢
    rw [toTrit_apply] at hP
    have hyi := hy i hi
    rw [hc' i hi] at hyi
    generalize (y i).2 = p at hyi ⊢
    split_ifs at hP with h1 h2
    · exact absurd hP (by decide)
    · exact absurd hP (by decide)
    · cases p
      · exact absurd hyi h1
      · rfl
      · exact absurd hyi h2
  have h2 : Multiset.card ((Multiset.range d).filter ((fun x : Fin k × Ptr => x.2 = Ptr.demand) ∘ y)) ≤
      Multiset.card ((Multiset.range d).filter ((fun a : Trit k => a c = 2) ∘ toTrit ∘ Y)) := by
    refine card_filter_range_le fun i hi hP => ?_
    simp only [Function.comp_apply] at hP ⊢
    rw [toTrit_apply]
    have hyi := hy i hi
    rw [hc' i hi, hP] at hyi
    simp [hyi]
  have := min_le_left (k + 1) (Multiset.card ((Multiset.range d).filter
    ((fun x : Fin k × Ptr => x.2 = Ptr.demand) ∘ y)))
  have := min_le_right (k + 1) (Multiset.card ((Multiset.range d).filter
    ((fun x : Fin k × Ptr => x.2 = Ptr.demand) ∘ y)))
  omega

namespace ViewSystem

variable {S : ViewSystem}

/-- An edge-view algorithm solving `Π'_{1/2}` (for superweak `k`-colouring), composed with
`toTrit`, solves the trit description `tritHalf k`. -/
theorem solvesE_toTrit {B : S.EV → Set (Fin k × Ptr)}
    (hB : S.SolvesE (superweak k).edgeStepMax Δ B) : S.SolvesE (tritHalf k) Δ (toTrit ∘ B) := by
  intro G
  refine ⟨fun _ _ _ => trivial, fun v i hi => ?_, fun v => ?_⟩
  · exact toTrit_mem_g (edgeStepMax_g_iff.1 ((hB G).2.1 v i hi))
  · exact toTrit_mem_h (Y := fun i => B (S.ev G v i)) ((hB G).2.2 v)

end ViewSystem

end AutomaticSpeedup
