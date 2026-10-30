import Papers.PODC2016.PowerLawLabeling.Defs

/-!
# Counting lower bound (Moon) and induced subgraphs

* `HasAdjLabeling.of_embedding`: a labeling scheme for a family into which every graph of another
  family embeds as an induced subgraph gives a scheme for that family with the same label size.
* `moon`: any adjacency labeling scheme for all graphs on `m` vertices has labels of at least
  `⌊(m-1)/2⌋` bits (counting: `2^{m(m-1)/2} ≤ (2^{ℓ+1}-1)^m`).
-/

namespace Podc.PowerLawLabeling

-- CSLib candidate (adjacency labeling basics)
/-- Induced subgraphs inherit labeling schemes. -/
theorem HasAdjLabeling.of_embedding {m n : ℕ} {F₁ : SimpleGraph (Fin m) → Prop}
    {F₂ : SimpleGraph (Fin n) → Prop} {X : ℝ} (h : HasAdjLabeling n F₂ X)
    (hemb : ∀ H, F₁ H → ∃ G, F₂ G ∧ Nonempty (H ↪g G)) : HasAdjLabeling m F₁ X := by
  obtain ⟨D, hD⟩ := h
  refine ⟨D, fun H hH => ?_⟩
  obtain ⟨G, hG, ⟨e⟩⟩ := hemb H hH
  obtain ⟨lab, hlen, hadj⟩ := hD G hG
  refine ⟨lab ∘ e, fun v => hlen (e v), fun u v huv => ?_⟩
  rw [← e.map_adj_iff]
  exact hadj (e u) (e v) (e.injective.ne huv)

namespace Moon

/-- Binary encoding of a bit list as a natural number with a leading `1`. -/
def encList : List Bool → ℕ
  | [] => 1
  | b :: l => 2 * encList l + b.toNat

lemma one_le_encList (l : List Bool) : 1 ≤ encList l := by
  induction l with
  | nil => simp [encList]
  | cons b l ih => simp only [encList]; omega

lemma encList_lt (l : List Bool) : encList l < 2 ^ (l.length + 1) := by
  induction l with
  | nil => simp [encList]
  | cons b l ih =>
    simp only [encList, List.length_cons, pow_succ] at ih ⊢
    cases b <;> simp <;> omega

lemma encList_injective : Function.Injective encList := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil => rfl
    | cons b l =>
      have := one_le_encList l
      simp only [encList] at h
      cases b <;> simp at h <;> omega
  | cons b l ih =>
    intro l₂ h
    cases l₂ with
    | nil =>
      have := one_le_encList l
      simp only [encList] at h
      cases b <;> simp at h; omega
    | cons b' l' =>
      simp only [encList] at h
      have hb : b = b' := by cases b <;> cases b' <;> first | rfl | (simp at h; omega)
      subst hb
      have : encList l = encList l' := by cases b <;> simp at h <;> omega
      rw [ih this]

/-- The graph on `Fin m` whose edges are the 2-sets in `T`. -/
def graphOf {m : ℕ} (T : Finset (Finset (Fin m))) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun a b => ({a, b} : Finset (Fin m)) ∈ T

lemma graphOf_adj {m : ℕ} (T : Finset (Finset (Fin m))) (a b : Fin m) :
    (graphOf T).Adj a b ↔ a ≠ b ∧ ({a, b} : Finset (Fin m)) ∈ T := by
  simp [graphOf, Finset.pair_comm]

end Moon

open Moon in

-- CSLib candidate (adjacency labeling basics)
/-- Moon's counting lower bound: labels for all graphs on `m` vertices need `⌊(m-1)/2⌋` bits. -/
theorem moon {m : ℕ} {X : ℝ} (hm : 1 ≤ m) (h : HasAdjLabeling m (fun _ => True) X) :
    (((m - 1) / 2 : ℕ) : ℝ) ≤ X := by
  obtain ⟨D, hD⟩ := h
  choose lab hlen hadj using fun G => hD G trivial
  have hX : 0 ≤ X := le_trans (Nat.cast_nonneg _) (hlen ⊥ ⟨0, hm⟩)
  set ℓ := ⌊X⌋₊
  have hlen' : ∀ G v, (lab G v).length ≤ ℓ := fun G v => Nat.le_floor (hlen G v)
  let Φ : Finset (Finset (Fin m)) → Fin m → ℕ := fun T v => encList (lab (graphOf T) v)
  have hmaps : ∀ T ∈ (Finset.univ.powersetCard 2).powerset,
      Φ T ∈ Fintype.piFinset (fun _ : Fin m => Finset.Ico 1 (2 ^ (ℓ + 1))) := by
    intro T _
    simp only [Fintype.mem_piFinset, Finset.mem_Ico]
    intro v
    refine ⟨one_le_encList _, lt_of_lt_of_le (encList_lt _)
      (Nat.pow_le_pow_right (by norm_num) (by have := hlen' (graphOf T) v; omega))⟩
  have hinj : Set.InjOn Φ (((Finset.univ : Finset (Fin m)).powersetCard 2).powerset :
      Set (Finset (Finset (Fin m)))) := by
    intro T₁ h₁ T₂ h₂ hΦ
    have hl : lab (graphOf T₁) = lab (graphOf T₂) :=
      funext fun v => encList_injective (congrFun hΦ v)
    have key : ∀ a b : Fin m, a ≠ b →
        (({a, b} : Finset _) ∈ T₁ ↔ ({a, b} : Finset _) ∈ T₂) := by
      intro a b hab
      have h1 := hadj (graphOf T₁) a b hab
      have h2 := hadj (graphOf T₂) a b hab
      rw [hl, ← h2] at h1
      simpa [graphOf_adj, hab] using h1
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at h₁ h₂
    ext s
    constructor
    · intro hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 (h₁ hs)).2
      exact (key a b hab).1 hs
    · intro hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (Finset.mem_powersetCard.1 (h₂ hs)).2
      exact (key a b hab).2 hs
  have hcard := Finset.card_le_card_of_injOn Φ hmaps hinj
  rw [Finset.card_powerset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Fintype.card_piFinset, Finset.prod_const, Nat.card_Ico, Finset.card_univ,
    Fintype.card_fin] at hcard
  have h2 : (2 ^ (ℓ + 1) - 1) ^ m < (2 ^ (ℓ + 1)) ^ m :=
    Nat.pow_lt_pow_left (by have := Nat.one_le_two_pow (n := ℓ + 1); omega) (by omega)
  rw [← pow_mul] at h2
  have h3 : m.choose 2 < (ℓ + 1) * m :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt hcard h2)
  rw [Nat.choose_two_right] at h3
  have h4 : (m - 1) / 2 ≤ ℓ := by
    by_contra hc
    push Not at hc
    have h5 : 2 * (ℓ + 1) ≤ m - 1 := by omega
    have h6 : m * (2 * (ℓ + 1)) ≤ m * (m - 1) := Nat.mul_le_mul_left m h5
    have : (ℓ + 1) * m ≤ m * (m - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; nlinarith
    omega
  calc (((m - 1) / 2 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast h4
    _ ≤ X := Nat.floor_le hX

end Podc.PowerLawLabeling
