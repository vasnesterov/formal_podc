import Mathlib

/-!
# The MVC lower-bound graphs `G_{x,y}` of Censor-Hillel, Khoury, Paz (DISC 2017)

These graphs (Figure 1 of Bar-Yehuda, Censor-Hillel, Maus, Pai, Pemmaraju, *Distributed
Approximation on Power Graphs*, PODC 2020, and Section 5 of [CKP17]) are the starting point of the
`G²`-vertex-cover lower bounds (Theorems 20 and 22).

`k = 2 ^ L`; a row index `i ∈ [k]` is a bit string `i : Fin L → Bool`.

* Rows: `row s ℓ i` is `a^i_1` (`s = false`, `ℓ = false`), `a^i_2` (`s = false`, `ℓ = true`),
  `b^i_1`, `b^i_2` (`s = true`). The rows with fixed `(s, ℓ)` form a clique of size `k`.
* Bit gadgets: `bit s ℓ h b` is `t^h_S` (`b = true`) or `f^h_S` (`b = false`) for `S = A_ℓ`
  (`s = false`) or `S = B_ℓ` (`s = true`). For fixed `(ℓ, h)` the four vertices form the 4-cycle
  `t_A – f_A – t_B – f_B – t_A`, i.e. `bit s ℓ h b ~ bit s' ℓ h b'` iff `b ≠ b'`. (The paper does
  not spell out the order of the cycle; this choice makes `{t_A, t_B}` and `{f_A, f_B}` the two
  independent pairs, which is what the argument of [CKP17] needs.)
* `row s ℓ i ~ bit s ℓ h (i h)`: `a^i` is joined to `t^h` if bit `h` of `i` is `1`, else to `f^h`.
* Input edges: `a^i_1 – a^j_2` iff `x(i, j) = 0`, `b^i_1 – b^j_2` iff `y(i, j) = 0`.

`n = 4k + 8 log k` (`card_GV`). Main result (`ckp17`): `G_{x,y}` has a vertex cover of size
`W = 4(k - 1) + 4 log k` iff `x` and `y` intersect.
-/

namespace Podc.PowerGraphApproximation.LowerBound

open Finset SimpleGraph

/-- A row index: a `log k`-bit string. -/
abbrev Idx (L : ℕ) := Fin L → Bool

/-- Vertices of `G_{x,y}`. `s = false` is Alice's side (`A`), `ℓ = false` the first layer
(`A₁`, `B₁`). In `bit s ℓ h b`, `b = true` is `t^h`, `b = false` is `f^h`. -/
inductive GV (L : ℕ) where
  | row (s ℓ : Bool) (i : Idx L)
  | bit (s ℓ : Bool) (h : Fin L) (b : Bool)
  deriving DecidableEq, Fintype

variable {L : ℕ}

/-- The input matrix of side `s` (`x` for Alice, `y` for Bob). -/
def mat (x y : Idx L × Idx L → Bool) (s : Bool) : Idx L × Idx L → Bool := if s then y else x

/-- Adjacency of `G_{x,y}`. -/
def GAdj (x y : Idx L × Idx L → Bool) : GV L → GV L → Prop
  | .row s ℓ i, .row s' ℓ' i' => s = s' ∧ ((ℓ = ℓ' ∧ i ≠ i') ∨
      (ℓ = false ∧ ℓ' = true ∧ mat x y s (i, i') = false) ∨
      (ℓ = true ∧ ℓ' = false ∧ mat x y s (i', i) = false))
  | .row s ℓ i, .bit s' ℓ' h b => s = s' ∧ ℓ = ℓ' ∧ i h = b
  | .bit s ℓ h b, .row s' ℓ' i => s = s' ∧ ℓ = ℓ' ∧ i h = b
  | .bit _ ℓ h b, .bit _ ℓ' h' b' => ℓ = ℓ' ∧ h = h' ∧ b ≠ b'

instance (x y : Idx L × Idx L → Bool) : DecidableRel (GAdj x y) := fun a b =>
  match a, b with
  | .row s ℓ i, .row s' ℓ' i' => inferInstanceAs (Decidable (s = s' ∧ ((ℓ = ℓ' ∧ i ≠ i') ∨
      (ℓ = false ∧ ℓ' = true ∧ mat x y s (i, i') = false) ∨
      (ℓ = true ∧ ℓ' = false ∧ mat x y s (i', i) = false))))
  | .row s ℓ i, .bit s' ℓ' h b => inferInstanceAs (Decidable (s = s' ∧ ℓ = ℓ' ∧ i h = b))
  | .bit s ℓ h b, .row s' ℓ' i => inferInstanceAs (Decidable (s = s' ∧ ℓ = ℓ' ∧ i h = b))
  | .bit _ ℓ h b, .bit _ ℓ' h' b' => inferInstanceAs (Decidable (ℓ = ℓ' ∧ h = h' ∧ b ≠ b'))

/-- The lower-bound graph `G_{x,y}` of [CKP17] (Figure 1). -/
def G (x y : Idx L × Idx L → Bool) : SimpleGraph (GV L) where
  Adj := GAdj x y
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only [GAdj] at h ⊢ <;> grind⟩
  loopless := ⟨fun a h => by cases a <;> simp only [GAdj] at h <;> grind⟩

instance (x y : Idx L × Idx L → Bool) : DecidableRel (G x y).Adj :=
  inferInstanceAs (DecidableRel (GAdj x y))

section Adj

variable {x y : Idx L × Idx L → Bool}

@[simp] lemma G_row_row {s ℓ s' ℓ' : Bool} {i i' : Idx L} :
    (G x y).Adj (.row s ℓ i) (.row s' ℓ' i') ↔ s = s' ∧ ((ℓ = ℓ' ∧ i ≠ i') ∨
      (ℓ = false ∧ ℓ' = true ∧ mat x y s (i, i') = false) ∨
      (ℓ = true ∧ ℓ' = false ∧ mat x y s (i', i) = false)) := Iff.rfl

@[simp] lemma G_row_bit {s ℓ s' ℓ' b : Bool} {i : Idx L} {h : Fin L} :
    (G x y).Adj (.row s ℓ i) (.bit s' ℓ' h b) ↔ s = s' ∧ ℓ = ℓ' ∧ i h = b := Iff.rfl

@[simp] lemma G_bit_row {s ℓ s' ℓ' b : Bool} {i : Idx L} {h : Fin L} :
    (G x y).Adj (.bit s ℓ h b) (.row s' ℓ' i) ↔ s = s' ∧ ℓ = ℓ' ∧ i h = b := Iff.rfl

@[simp] lemma G_bit_bit {s ℓ s' ℓ' b b' : Bool} {h h' : Fin L} :
    (G x y).Adj (.bit s ℓ h b) (.bit s' ℓ' h' b') ↔ ℓ = ℓ' ∧ h = h' ∧ b ≠ b' := Iff.rfl

end Adj

/-- `n = 4k + 8 log k`. -/
lemma card_GV : Fintype.card (GV L) = 4 * 2 ^ L + 8 * L := by
  let e : GV L ≃ (Bool × Bool × Idx L) ⊕ (Bool × Bool × Fin L × Bool) :=
    { toFun := fun v => match v with
        | .row s ℓ i => .inl (s, ℓ, i)
        | .bit s ℓ h b => .inr (s, ℓ, h, b)
      invFun := fun p => match p with
        | .inl (s, ℓ, i) => .row s ℓ i
        | .inr (s, ℓ, h, b) => .bit s ℓ h b
      left_inv := fun v => by cases v <;> rfl
      right_inv := fun p => by rcases p with ⟨s, ℓ, i⟩ | ⟨s, ℓ, h, b⟩ <;> rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_sum, Fintype.card_prod]
  ring

/-! ### Independent sets of `G_{x,y}` -/

/-- The "group" of a vertex: the clique `(s, ℓ)` of a row, the bit gadget `(ℓ, h)` of a gadget
vertex. -/
def grp : GV L → (Bool × Bool) ⊕ (Bool × Fin L)
  | .row s ℓ _ => .inl (s, ℓ)
  | .bit _ ℓ h _ => .inr (ℓ, h)

/-- Capacity of a group: an independent set meets a clique at most once and a bit gadget (a
4-cycle) at most twice. -/
def cap : (Bool × Bool) ⊕ (Bool × Fin L) → ℕ
  | .inl _ => 1
  | .inr _ => 2

lemma sum_cap : ∑ g : (Bool × Bool) ⊕ (Bool × Fin L), (cap g : ℕ) = 4 + 4 * L := by
  simp [cap, Fintype.sum_sum_type, Finset.card_univ, Fintype.card_prod]
  ring

lemma grp_eq_inl {v : GV L} {s ℓ : Bool} : grp v = .inl (s, ℓ) ↔ ∃ i, v = .row s ℓ i := by
  cases v <;> simp [grp, eq_comm, and_comm]

lemma grp_eq_inr {v : GV L} {ℓ : Bool} {h : Fin L} :
    grp v = .inr (ℓ, h) ↔ ∃ s b, v = .bit s ℓ h b := by
  cases v <;> simp [grp, eq_comm, and_comm]

section Indep

variable {x y : Idx L × Idx L → Bool} {S : Finset (GV L)}

lemma fiber_le (hS : (G x y).IsIndepSet ↑S) (g : (Bool × Bool) ⊕ (Bool × Fin L)) :
    (S.filter fun v => grp v = g).card ≤ cap g := by
  rcases g with ⟨s, ℓ⟩ | ⟨ℓ, h⟩
  · refine Finset.card_le_one.2 fun a ha b hb => ?_
    simp only [Finset.mem_filter] at ha hb
    obtain ⟨i, rfl⟩ := grp_eq_inl.1 ha.2
    obtain ⟨i', rfl⟩ := grp_eq_inl.1 hb.2
    by_contra hab
    have hi : i ≠ i' := fun h => hab (by rw [h])
    exact hS ha.1 hb.1 hab (by simp [hi])
  · by_cases hne : (S.filter fun v => grp v = .inr (ℓ, h)).Nonempty
    · obtain ⟨a, ha⟩ := hne
      simp only [Finset.mem_filter] at ha
      obtain ⟨s0, β, rfl⟩ := grp_eq_inr.1 ha.2
      calc _ ≤ ({.bit false ℓ h β, .bit true ℓ h β} : Finset (GV L)).card := by
            refine Finset.card_le_card fun b hb => ?_
            simp only [Finset.mem_filter] at hb
            obtain ⟨s1, β1, rfl⟩ := grp_eq_inr.1 hb.2
            have hβ : β1 = β := by
              by_contra hβ
              exact hS hb.1 ha.1 (by simp [hβ]) (by simp [hβ])
            subst hβ
            cases s1 <;> simp
        _ ≤ 2 := Finset.card_le_two
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp

/-- An independent set of `G_{x,y}` has at most `4 + 4 log k` vertices. -/
lemma card_indep_le (hS : (G x y).IsIndepSet ↑S) : S.card ≤ 4 + 4 * L := by
  rw [Finset.card_eq_sum_card_fiberwise (f := grp) (t := univ) (by simp), ← sum_cap]
  exact Finset.sum_le_sum fun g _ => fiber_le hS g

/-- An independent set of `G_{x,y}` of size `4 + 4 log k` forces `x` and `y` to intersect. -/
lemma intersect_of_indep (hS : (G x y).IsIndepSet ↑S) (hcard : 4 + 4 * L ≤ S.card) :
    ∃ p, x p = true ∧ y p = true := by
  have hfib : ∀ g, (S.filter fun v => grp v = g).card = cap g := by
    have hsum : ∑ g : (Bool × Bool) ⊕ (Bool × Fin L), (S.filter fun v => grp v = g).card =
        ∑ g : (Bool × Bool) ⊕ (Bool × Fin L), cap g := by
      apply le_antisymm (Finset.sum_le_sum fun g _ => fiber_le hS g)
      rw [sum_cap, ← Finset.card_eq_sum_card_fiberwise (by simp)]
      exact hcard
    intro g
    exact (Finset.sum_eq_sum_iff_of_le (fun g _ => fiber_le hS g)).1 hsum g (mem_univ _)
  -- one row per clique
  have hrow : ∀ s ℓ, ∃ i, GV.row s ℓ i ∈ S := by
    intro s ℓ
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (hfib (.inl (s, ℓ)))
    have : a ∈ S.filter fun v => grp v = .inl (s, ℓ) := by rw [ha]; simp
    simp only [Finset.mem_filter] at this
    obtain ⟨i, rfl⟩ := grp_eq_inl.1 this.2
    exact ⟨i, this.1⟩
  -- two vertices with the same bit per gadget
  have hbit : ∀ ℓ h, ∃ β, GV.bit false ℓ h β ∈ S ∧ GV.bit true ℓ h β ∈ S := by
    intro ℓ h
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.1 (hfib (.inr (ℓ, h)))
    have ha : a ∈ S.filter fun v => grp v = .inr (ℓ, h) := by rw [he]; simp
    have hb : b ∈ S.filter fun v => grp v = .inr (ℓ, h) := by rw [he]; simp
    simp only [Finset.mem_filter] at ha hb
    obtain ⟨s1, β1, rfl⟩ := grp_eq_inr.1 ha.2
    obtain ⟨s2, β2, rfl⟩ := grp_eq_inr.1 hb.2
    have hβ : β1 = β2 := by
      by_contra hβ
      exact hS ha.1 hb.1 hab (by simp [hβ])
    subst hβ
    have hs : s1 ≠ s2 := fun h => hab (by rw [h])
    cases s1 <;> cases s2 <;> simp at hs
    · exact ⟨β1, ha.1, hb.1⟩
    · exact ⟨β1, hb.1, ha.1⟩
  choose r hr using hrow
  choose β hβ using hbit
  -- the row chosen in clique `(s, ℓ)` is the complement of the gadget bits of layer `ℓ`
  have hrβ : ∀ s ℓ h, r s ℓ h = !β ℓ h := by
    intro s ℓ h
    have h1 : GV.bit s ℓ h (β ℓ h) ∈ S := by cases s; exact (hβ ℓ h).1; exact (hβ ℓ h).2
    by_contra hne
    have : r s ℓ h = β ℓ h := by cases hr' : r s ℓ h <;> cases hb : β ℓ h <;> simp_all
    exact hS (hr s ℓ) h1 (by simp) (by simp [this])
  have hrr : ∀ ℓ, r false ℓ = r true ℓ := fun ℓ => funext fun h => by rw [hrβ, hrβ]
  refine ⟨(r false false, r false true), ?_, ?_⟩
  · by_contra hx
    exact hS (hr false false) (hr false true) (by simp)
      (by simp [mat, (by simpa using hx : x (r false false, r false true) = false)])
  · by_contra hy
    rw [hrr false, hrr true] at hy
    exact hS (hr true false) (hr true true) (by simp)
      (by simp [mat, (by simpa using hy : y (r true false, r true true) = false)])

end Indep

/-- The independent set of size `4 + 4 log k` built from a common element `(i, j)`: rows
`a^i_1, b^i_1, a^j_2, b^j_2` and, in every gadget, the two vertices of the complementary bit. -/
def indepOf (i j : Idx L) : Finset (GV L) :=
  (univ : Finset (Bool × Bool)).image (fun p => .row p.1 p.2 (if p.2 then j else i)) ∪
  (univ : Finset (Bool × Bool × Fin L)).image
    (fun p => .bit p.1 p.2.1 p.2.2 (!(if p.2.1 then j else i) p.2.2))

lemma card_indepOf (i j : Idx L) : (indepOf i j).card = 4 + 4 * L := by
  rw [indepOf, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective]
  · simp [Finset.card_univ, Fintype.card_prod]; ring
  · rintro ⟨s, ℓ, h⟩ ⟨s', ℓ', h'⟩ he
    simp only [GV.bit.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    rfl
  · rintro ⟨s, ℓ⟩ ⟨s', ℓ'⟩ he
    simp only [GV.row.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    rfl
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨_, -, rfl⟩ := ha
    obtain ⟨_, -, hb⟩ := hb
    simp at hb

lemma indepOf_indep {x y : Idx L × Idx L → Bool} {i j : Idx L} (hx : x (i, j) = true)
    (hy : y (i, j) = true) : (G x y).IsIndepSet ↑(indepOf i j) := by
  intro a ha b hb hab hadj
  simp only [indepOf, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
    Finset.mem_coe, Finset.mem_univ, true_and] at ha hb
  rcases ha with ⟨⟨s, ℓ⟩, rfl⟩ | ⟨⟨s, ℓ, h⟩, rfl⟩ <;>
    rcases hb with ⟨⟨s', ℓ'⟩, rfl⟩ | ⟨⟨s', ℓ', h'⟩, rfl⟩
  · cases s <;> cases s' <;> cases ℓ <;> cases ℓ' <;> simp_all [mat]
  · cases ℓ <;> simp at hadj <;> grind
  · cases ℓ' <;> simp at hadj <;> grind
  · cases ℓ <;> cases ℓ' <;> simp at hadj <;> grind

/-- **Lemma of [CKP17]** (used as Theorem 19's instance in the proofs of Theorems 20 and 22):
`G_{x,y}` has a vertex cover of size at most `W = 4(k - 1) + 4 log k` iff `x` and `y`
intersect, i.e. `DISJ_{k²}(x, y) = FALSE`. -/
theorem ckp17 (x y : Idx L × Idx L → Bool) :
    (∃ C : Finset (GV L), (G x y).IsVertexCover ↑C ∧ C.card ≤ 4 * (2 ^ L - 1) + 4 * L) ↔
      ∃ p, x p = true ∧ y p = true := by
  have hk : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  constructor
  · rintro ⟨C, hC, hcard⟩
    have hS : (G x y).IsIndepSet ↑Cᶜ := by
      rw [← isVertexCover_compl, Finset.coe_compl, compl_compl]; exact hC
    refine intersect_of_indep hS ?_
    rw [Finset.card_compl, card_GV]
    omega
  · rintro ⟨⟨i, j⟩, hx, hy⟩
    refine ⟨(indepOf i j)ᶜ, ?_, ?_⟩
    · rw [Finset.coe_compl, isVertexCover_compl]; exact indepOf_indep hx hy
    · rw [Finset.card_compl, card_GV, card_indepOf]
      omega

end Podc.PowerGraphApproximation.LowerBound
