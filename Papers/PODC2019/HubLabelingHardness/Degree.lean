import Papers.PODC2019.HubLabelingHardness.Basic

/-!
# Degree and size of `G_{b,ℓ}` (Theorem 2.1 (i), (ii) of Kosowski–Uznański–Viennot, PODC 2019)

Every vertex of `G_{b,ℓ}` has degree at most `3` (and degree `3` is attained), and
`G_{b,ℓ}` has `2^{bℓ} · 2^{Θ(b + log ℓ)}` vertices.

Degree bound: for every vertex `a` we give three sets `nb₁ a, nb₂ a, nb₃ a`, each with at most one
element, whose union contains all neighbours of `a`.
-/

namespace Podc.HubLabelingHardness

open SimpleGraph GV

variable {b ℓ : ℕ}

/-! ## Degree -/

/-- First neighbour slot: the "parent" side (in-root / parent / predecessor). -/
def nb₁ : GV b ℓ → Set (GV b ℓ)
  | main i j => {c | ∃ i' : Fin (2 * ℓ), i'.succ = i ∧ c = tin i' j (root b)}
  | tin i j n => {c | (n = root b ∧ c = main i.succ j) ∨
      ∃ n' : Fin (2 * side b - 1), (n.val = 2 * n'.val + 1 ∨ n.val = 2 * n'.val + 2) ∧ c = tin i j n'}
  | tout i j n => {c | (n = root b ∧ c = main i.castSucc j) ∨
      ∃ n' : Fin (2 * side b - 1), (n.val = 2 * n'.val + 1 ∨ n.val = 2 * n'.val + 2) ∧ c = tout i j n'}
  | mid i j t p => {c | (p.val = 0 ∧ c = tout i j (leaf t)) ∨
      ∃ p' : Fin (plen b ℓ i j t - 1), p.val = p'.val + 1 ∧ c = mid i j t p'}

/-- Second neighbour slot: out-root / first child or path vertex / successor. -/
def nb₂ : GV b ℓ → Set (GV b ℓ)
  | main i j => {c | ∃ i' : Fin (2 * ℓ), i'.castSucc = i ∧ c = tout i' j (root b)}
  | tin i j n => {c | (∃ m : Fin (2 * side b - 1), m.val = 2 * n.val + 1 ∧ c = tin i j m) ∨
      ∃ (j' : Vec b ℓ) (t : Fin (side b)) (p : Fin (plen b ℓ i j' t - 1)),
        p.val + 2 = plen b ℓ i j' t ∧ j = Function.update j' (cc i) t ∧ n = leaf (j' (cc i)) ∧
          c = mid i j' t p}
  | tout i j n => {c | (∃ m : Fin (2 * side b - 1), m.val = 2 * n.val + 1 ∧ c = tout i j m) ∨
      ∃ (t : Fin (side b)) (p : Fin (plen b ℓ i j t - 1)), p.val = 0 ∧ n = leaf t ∧ c = mid i j t p}
  | mid i j t p => {c | (∃ q : Fin (plen b ℓ i j t - 1), q.val = p.val + 1 ∧ c = mid i j t q) ∨
      (p.val + 2 = plen b ℓ i j t ∧ c = tin i (Function.update j (cc i) t) (leaf (j (cc i))))}

/-- Third neighbour slot: second child of a tree node. -/
def nb₃ : GV b ℓ → Set (GV b ℓ)
  | main _ _ => ∅
  | tin i j n => {c | ∃ m : Fin (2 * side b - 1), m.val = 2 * n.val + 2 ∧ c = tin i j m}
  | tout i j n => {c | ∃ m : Fin (2 * side b - 1), m.val = 2 * n.val + 2 ∧ c = tout i j m}
  | mid _ _ _ _ => ∅

/-- All neighbour slots. -/
def nbs (a : GV b ℓ) : Set (GV b ℓ) := nb₁ a ∪ nb₂ a ∪ nb₃ a

lemma E_mem_nbs {a c : GV b ℓ} (h : E b ℓ a c) : c ∈ nbs a ∧ a ∈ nbs c := by
  cases h with
  | inRoot i j =>
    exact ⟨Or.inl (Or.inl ⟨i, rfl, rfl⟩), Or.inl (Or.inl (Or.inl ⟨rfl, rfl⟩))⟩
  | outRoot i j =>
    exact ⟨Or.inl (Or.inr ⟨i, rfl, rfl⟩), Or.inl (Or.inl (Or.inl ⟨rfl, rfl⟩))⟩
  | inChild i j n m h =>
    refine ⟨?_, Or.inl (Or.inl (Or.inr ⟨n, h, rfl⟩))⟩
    rcases h with h | h
    · exact Or.inl (Or.inr (Or.inl ⟨m, h, rfl⟩))
    · exact Or.inr ⟨m, h, rfl⟩
  | outChild i j n m h =>
    refine ⟨?_, Or.inl (Or.inl (Or.inr ⟨n, h, rfl⟩))⟩
    rcases h with h | h
    · exact Or.inl (Or.inr (Or.inl ⟨m, h, rfl⟩))
    · exact Or.inr ⟨m, h, rfl⟩
  | pathStart i j t p hp =>
    exact ⟨Or.inl (Or.inr (Or.inr ⟨t, p, hp, rfl, rfl⟩)), Or.inl (Or.inl (Or.inl ⟨hp, rfl⟩))⟩
  | pathStep i j t p q h =>
    exact ⟨Or.inl (Or.inr (Or.inl ⟨q, h, rfl⟩)), Or.inl (Or.inl (Or.inr ⟨p, h, rfl⟩))⟩
  | pathEnd i j t p hp =>
    exact ⟨Or.inl (Or.inr (Or.inr ⟨hp, rfl⟩)),
      Or.inl (Or.inr (Or.inr ⟨j, t, p, hp, rfl, rfl, rfl⟩))⟩

lemma neighborSet_subset (a : GV b ℓ) : (G b ℓ).neighborSet a ⊆ nbs a := by
  intro c hc
  rcases (G_adj.mp hc).2 with h | h
  · exact (E_mem_nbs h).1
  · exact (E_mem_nbs h).2

lemma leaf_val (t : Fin (side b)) : (leaf t).val = side b - 1 + t.val := rfl

lemma leaf_injective : Function.Injective (leaf (b := b)) := by
  intro t t' h
  have := congrArg Fin.val h
  simp only [leaf_val] at this
  exact Fin.ext (by omega)

/-- The in-leaf at the end of a path determines the path's lower endpoint and target value. -/
lemma pathEnd_unique {i : Fin (2 * ℓ)} {j₁ j₂ : Vec b ℓ} {t₁ t₂ : Fin (side b)}
    (h1 : Function.update j₁ (cc i) t₁ = Function.update j₂ (cc i) t₂)
    (h2 : leaf (j₁ (cc i)) = leaf (j₂ (cc i))) : j₁ = j₂ ∧ t₁ = t₂ := by
  have hc : j₁ (cc i) = j₂ (cc i) := leaf_injective h2
  refine ⟨funext fun k => ?_, ?_⟩
  · by_cases hk : k = cc i
    · subst hk; exact hc
    · have := congrFun h1 k
      simpa [Function.update_of_ne hk] using this
  · have := congrFun h1 (cc i)
    simpa using this

lemma subsingleton_nb₁ (a : GV b ℓ) : (nb₁ a).Subsingleton := by
  cases a with
  | main i j =>
    rintro _ ⟨i₁, h₁, rfl⟩ _ ⟨i₂, h₂, rfl⟩
    rw [Fin.succ_injective _ (h₁.trans h₂.symm)]
  | tin i j n =>
    rintro _ (⟨hn, rfl⟩ | ⟨n₁, h₁, rfl⟩) _ (⟨hn', rfl⟩ | ⟨n₂, h₂, rfl⟩)
    · rfl
    · subst hn; simp [root] at h₂
    · subst hn'; simp [root] at h₁
    · have : n₁ = n₂ := Fin.ext (by omega)
      rw [this]
  | tout i j n =>
    rintro _ (⟨hn, rfl⟩ | ⟨n₁, h₁, rfl⟩) _ (⟨hn', rfl⟩ | ⟨n₂, h₂, rfl⟩)
    · rfl
    · subst hn; simp [root] at h₂
    · subst hn'; simp [root] at h₁
    · have : n₁ = n₂ := Fin.ext (by omega)
      rw [this]
  | mid i j t p =>
    rintro _ (⟨hp, rfl⟩ | ⟨p₁, h₁, rfl⟩) _ (⟨hp', rfl⟩ | ⟨p₂, h₂, rfl⟩)
    · rfl
    · omega
    · omega
    · have : p₁ = p₂ := Fin.ext (by omega)
      rw [this]

lemma subsingleton_nb₂ (a : GV b ℓ) : (nb₂ a).Subsingleton := by
  cases a with
  | main i j =>
    rintro _ ⟨i₁, h₁, rfl⟩ _ ⟨i₂, h₂, rfl⟩
    rw [Fin.castSucc_injective _ (h₁.trans h₂.symm)]
  | tin i j n =>
    rintro _ (⟨m₁, h₁, rfl⟩ | ⟨j₁, t₁, p₁, hp₁, hj₁, hn₁, rfl⟩) _
      (⟨m₂, h₂, rfl⟩ | ⟨j₂, t₂, p₂, hp₂, hj₂, hn₂, rfl⟩)
    · have : m₁ = m₂ := Fin.ext (by omega)
      rw [this]
    · have := m₁.2; have := congrArg Fin.val hn₂; simp only [leaf_val] at this; omega
    · have := m₂.2; have := congrArg Fin.val hn₁; simp only [leaf_val] at this; omega
    · obtain ⟨rfl, rfl⟩ := pathEnd_unique (hj₁.symm.trans hj₂) (hn₁.symm.trans hn₂)
      have : p₁ = p₂ := Fin.ext (by omega)
      rw [this]
  | tout i j n =>
    rintro _ (⟨m₁, h₁, rfl⟩ | ⟨t₁, p₁, hp₁, hn₁, rfl⟩) _ (⟨m₂, h₂, rfl⟩ | ⟨t₂, p₂, hp₂, hn₂, rfl⟩)
    · have : m₁ = m₂ := Fin.ext (by omega)
      rw [this]
    · have := m₁.2; have := congrArg Fin.val hn₂; simp only [leaf_val] at this; omega
    · have := m₂.2; have := congrArg Fin.val hn₁; simp only [leaf_val] at this; omega
    · obtain rfl := leaf_injective (hn₁.symm.trans hn₂)
      have : p₁ = p₂ := Fin.ext (by omega)
      rw [this]
  | mid i j t p =>
    rintro _ (⟨q₁, h₁, rfl⟩ | ⟨hp, rfl⟩) _ (⟨q₂, h₂, rfl⟩ | ⟨hp', rfl⟩)
    · have : q₁ = q₂ := Fin.ext (by omega)
      rw [this]
    · have := q₁.2; omega
    · have := q₂.2; omega
    · rfl

lemma subsingleton_nb₃ (a : GV b ℓ) : (nb₃ a).Subsingleton := by
  cases a with
  | main i j => exact Set.subsingleton_empty
  | tin i j n =>
    rintro _ ⟨m₁, h₁, rfl⟩ _ ⟨m₂, h₂, rfl⟩
    have : m₁ = m₂ := Fin.ext (by omega)
    rw [this]
  | tout i j n =>
    rintro _ ⟨m₁, h₁, rfl⟩ _ ⟨m₂, h₂, rfl⟩
    have : m₁ = m₂ := Fin.ext (by omega)
    rw [this]
  | mid i j t p => exact Set.subsingleton_empty

/-- Theorem 2.1 (ii), upper half: every vertex of `G_{b,ℓ}` has degree at most `3`. -/
theorem ncard_neighborSet_le (v : GV b ℓ) : ((G b ℓ).neighborSet v).ncard ≤ 3 := by
  calc ((G b ℓ).neighborSet v).ncard ≤ (nbs v).ncard :=
        Set.ncard_le_ncard (neighborSet_subset v) (Set.toFinite _)
    _ ≤ (nb₁ v ∪ nb₂ v).ncard + (nb₃ v).ncard := Set.ncard_union_le _ _
    _ ≤ (nb₁ v).ncard + (nb₂ v).ncard + (nb₃ v).ncard := by
        gcongr; exact Set.ncard_union_le _ _
    _ ≤ 1 + 1 + 1 := by
        gcongr
        · exact Set.ncard_le_one_iff_subsingleton.mpr (subsingleton_nb₁ v)
        · exact Set.ncard_le_one_iff_subsingleton.mpr (subsingleton_nb₂ v)
        · exact Set.ncard_le_one_iff_subsingleton.mpr (subsingleton_nb₃ v)

lemma two_le_side (hb : 1 ≤ b) : 2 ≤ side b := by
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb

/-- Theorem 2.1 (ii), lower half: degree `3` is attained (by the root of an out-tree, adjacent to
its main vertex and its two children). -/
theorem exists_ncard_neighborSet_eq (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) :
    ∃ v : GV b ℓ, ((G b ℓ).neighborSet v).ncard = 3 := by
  have hs := two_le_side hb
  let i : Fin (2 * ℓ) := ⟨0, by omega⟩
  let j : Vec b ℓ := fun _ => ⟨0, by omega⟩
  let n1 : Fin (2 * side b - 1) := ⟨1, by omega⟩
  let n2 : Fin (2 * side b - 1) := ⟨2, by omega⟩
  refine ⟨tout i j (root b), le_antisymm (ncard_neighborSet_le _) ?_⟩
  have hsub : ({main i.castSucc j, tout i j n1, tout i j n2} : Set (GV b ℓ)) ⊆
      (G b ℓ).neighborSet (tout i j (root b)) := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl
    · exact G_adj.mpr ⟨by simp, Or.inr (E.outRoot i j)⟩
    · refine G_adj.mpr ⟨by simp [n1, root, Fin.ext_iff], Or.inl (E.outChild i j _ _ ?_)⟩
      simp [n1, root]
    · refine G_adj.mpr ⟨by simp [n2, root, Fin.ext_iff], Or.inl (E.outChild i j _ _ ?_)⟩
      simp [n2, root]
  have h3 : ({main i.castSucc j, tout i j n1, tout i j n2} : Set (GV b ℓ)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨_, _, _, by simp, by simp, by simp [n1, n2, Fin.ext_iff], rfl⟩
  rw [← h3]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

/-- Theorem 2.1 (ii): `G_{b,ℓ}` has maximum degree exactly `3` (for `b, ℓ ≥ 1`). -/
theorem maxDegree_eq (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) [DecidableRel (G b ℓ).Adj] :
    (G b ℓ).maxDegree = 3 := by
  apply le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro v
    rw [← SimpleGraph.ncard_neighborSet]
    exact ncard_neighborSet_le v
  · obtain ⟨v, hv⟩ := exists_ncard_neighborSet_eq hb hℓ
    rw [← hv, SimpleGraph.ncard_neighborSet]
    exact SimpleGraph.degree_le_maxDegree _ _

/-! ## Number of vertices -/

lemma card_eq : Fintype.card (GV b ℓ) = (2 * ℓ + 1) * side b ^ ℓ +
    2 * (2 * ℓ * side b ^ ℓ * (2 * side b - 1)) +
    ∑ e : Fin (2 * ℓ) × Vec b ℓ × Fin (side b), (plen b ℓ e.1 e.2.1 e.2.2 - 1) := by
  rw [Fintype.card_congr GV.equivCode]
  simp [Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod]
  ring

lemma sqd_le {s : ℕ} {a c : ℕ} (ha : a < s) (hc : c < s) : sqd a c ≤ (s - 1) ^ 2 := by
  unfold sqd
  apply Nat.pow_le_pow_left
  omega

lemma plen_le (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) :
    plen b ℓ i j t ≤ bigA b ℓ + (side b - 1) ^ 2 := by
  have := sqd_le (j (cc i)).2 t.2
  unfold plen; omega

lemma plen_sub_one_le (hℓ : 1 ≤ ℓ) (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) :
    plen b ℓ i j t - 1 ≤ 4 * ℓ * side b ^ 2 := by
  have h1 := plen_le i j t
  have h2 : (side b - 1) ^ 2 ≤ side b ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  have h3 : side b ^ 2 ≤ ℓ * side b ^ 2 := Nat.le_mul_of_pos_left _ hℓ
  simp only [bigA] at h1
  have h4 : 4 * ℓ * side b ^ 2 = 3 * ℓ * side b ^ 2 + ℓ * side b ^ 2 := by ring
  omega

lemma two_le_plen (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) (i : Fin (2 * ℓ)) (j : Vec b ℓ) (t : Fin (side b)) :
    2 ≤ plen b ℓ i j t := by
  have h1 : b + 1 ≤ side b := Nat.lt_two_pow_self
  have h2 : (b + 1) ^ 2 ≤ side b ^ 2 := Nat.pow_le_pow_left h1 2
  have h3 : side b ^ 2 ≤ ℓ * side b ^ 2 := Nat.le_mul_of_pos_left _ hℓ
  have h4 : 2 * b + 4 ≤ 3 * ℓ * side b ^ 2 := by nlinarith
  unfold plen bigA
  omega

/-- Theorem 2.1 (i), upper bound: `|V(G_{b,ℓ})| ≤ 16 ℓ² s^{ℓ+3} = 2^{bℓ} · 2^{O(b + log ℓ)}`. -/
theorem card_le (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) :
    Fintype.card (GV b ℓ) ≤ 16 * ℓ ^ 2 * side b ^ (ℓ + 3) := by
  have hs := two_le_side hb
  have hsum : ∑ e : Fin (2 * ℓ) × Vec b ℓ × Fin (side b), (plen b ℓ e.1 e.2.1 e.2.2 - 1) ≤
      (2 * ℓ * side b ^ ℓ * side b) * (4 * ℓ * side b ^ 2) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin (2 * ℓ) × Vec b ℓ × Fin (side b)))
      (fun e => plen b ℓ e.1 e.2.1 e.2.2 - 1) (4 * ℓ * side b ^ 2)
      (fun e _ => plen_sub_one_le hℓ e.1 e.2.1 e.2.2)
    simpa [Fintype.card_prod, mul_assoc] using this
  rw [card_eq]
  set X := side b ^ ℓ
  set s := side b
  have hX : 1 ≤ X := Nat.one_le_pow _ _ (by omega)
  have e : s ^ (ℓ + 3) = X * s ^ 3 := by rw [pow_add]
  rw [e]
  have h2s : 2 * s - 1 ≤ 2 * s := Nat.sub_le _ _
  have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
  calc (2 * ℓ + 1) * X + 2 * (2 * ℓ * X * (2 * s - 1)) + _
      ≤ 3 * ℓ * X + 2 * (2 * ℓ * X * (2 * s)) + (2 * ℓ * X * s) * (4 * ℓ * s ^ 2) := by
        gcongr; omega
    _ ≤ 16 * ℓ ^ 2 * (X * s ^ 3) := by
        have h4 : 4 * s ≤ s ^ 3 := by
          have h : 4 ≤ s ^ 2 := by nlinarith
          calc 4 * s ≤ s ^ 2 * s := Nat.mul_le_mul_right _ h
            _ = s ^ 3 := by ring
        have hA : 4 * s * (ℓ ^ 2 * X) ≤ s ^ 3 * (ℓ ^ 2 * X) := Nat.mul_le_mul_right _ h4
        have hB : ℓ * X * s ≤ ℓ ^ 2 * X * s := by gcongr
        have hC : ℓ * X ≤ ℓ * X * s := Nat.le_mul_of_pos_right _ (by omega)
        nlinarith

/-- Theorem 2.1 (i), lower bound: `|V(G_{b,ℓ})| ≥ 2ℓ s^{ℓ+1} = 2^{bℓ} · 2^{Ω(b + log ℓ)}`
(already the internal path vertices adjacent to the out-trees are that many). -/
theorem card_ge (hb : 1 ≤ b) (hℓ : 1 ≤ ℓ) :
    2 * ℓ * side b ^ (ℓ + 1) ≤ Fintype.card (GV b ℓ) := by
  have hsum : (2 * ℓ * side b ^ ℓ * side b) * 1 ≤
      ∑ e : Fin (2 * ℓ) × Vec b ℓ × Fin (side b), (plen b ℓ e.1 e.2.1 e.2.2 - 1) := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin (2 * ℓ) × Vec b ℓ × Fin (side b)))
      (fun e => plen b ℓ e.1 e.2.1 e.2.2 - 1) 1
      (fun e _ => by have := two_le_plen hb hℓ e.1 e.2.1 e.2.2; omega)
    simpa [Fintype.card_prod, mul_assoc] using this
  rw [card_eq, pow_succ]
  generalize ∑ e : Fin (2 * ℓ) × Vec b ℓ × Fin (side b), (plen b ℓ e.1 e.2.1 e.2.2 - 1) = S at hsum ⊢
  have : 2 * ℓ * (side b ^ ℓ * side b) = 2 * ℓ * side b ^ ℓ * side b * 1 := by ring
  omega

end Podc.HubLabelingHardness
