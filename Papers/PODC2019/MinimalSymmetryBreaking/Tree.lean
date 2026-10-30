import Papers.PODC2019.MinimalSymmetryBreaking.Field

/-!
# The consistently oriented `2k`-regular tree

The infinite `Δ`-regular tree with a consistent orientation of its `k = Δ/2` dimensions
(Section 5 of the paper: directions `U, D, L, R` for `Δ = 4`) is the Cayley graph of the free
group on `k` generators: node `v` has the neighbours `v * dir (d, true) = v * gᵈ` (the positive
direction of dimension `d`) and `v * dir (d, false) = v * gᵈ⁻¹`. Distances are word lengths:
`dist(v, w) = ‖v⁻¹ w‖`. The radius-`r` view of `v` of a field `x` is `shift v x = (h ↦ x (v * h))`
restricted to the ball of radius `r` around the origin; so an algorithm is a function of the field
around the origin, and translation invariance is built in.

The geometric facts used by the speedup lemmas are about balls around two adjacent nodes:
`ball_inter_ball_subset` (a node at distance `≤ r+1` from both endpoints of an edge is at distance
`≤ r` from one of them) and `disjoint_diff` / `disjoint_diff_ball` (the parts of the balls of the
neighbours of `v` outside the ball of `v` are pairwise disjoint, and disjoint from the ball of
radius `r + 1` around the remaining neighbour).
-/

-- CSLib candidate
namespace Podc.MinimalSymmetryBreaking

open Finset Function FreeGroup
open scoped Classical

noncomputable section

/-- The consistently oriented `2k`-regular tree: the free group on `k` generators. -/
abbrev Tree (k : ℕ) := FreeGroup (Fin k)

variable {k : ℕ} {Ω : Type*}

/-- The neighbour of the origin in direction `p = (d, b)`: `gᵈ` if `b`, `gᵈ⁻¹` otherwise. -/
def dir (p : Fin k × Bool) : Tree k := FreeGroup.mk [p]

/-- The field seen from node `v`. -/
def shift (v : Tree k) (x : Tree k → Ω) : Tree k → Ω := fun h => x (v * h)

/-- The ball of radius `r` around `v`. -/
def ball (v : Tree k) (r : ℕ) : Set (Tree k) := {w | (v⁻¹ * w).norm ≤ r}

lemma shift_eq_comp (v : Tree k) (x : Tree k → Ω) : shift v x = x ∘ Equiv.mulLeft v := rfl

@[simp] lemma shift_one (x : Tree k → Ω) : shift 1 x = x := by
  funext h; simp [shift]

lemma shift_shift (u v : Tree k) (x : Tree k → Ω) : shift v (shift u x) = shift (u * v) x := by
  funext h; simp [shift, mul_assoc]

lemma dir_inv (p : Fin k × Bool) : (dir p)⁻¹ = dir (p.1, !p.2) := by
  simp [dir, FreeGroup.inv_mk, FreeGroup.invRev]

@[simp] lemma norm_dir (p : Fin k × Bool) : (dir p).norm = 1 := by
  simp [dir, FreeGroup.norm, FreeGroup.toWord_mk, FreeGroup.reduce]

lemma dir_injective : Injective (dir (k := k)) := by
  intro p q h
  have := congrArg FreeGroup.toWord h
  simpa [dir, FreeGroup.toWord_mk, FreeGroup.reduce] using this

/-- Left multiplication by a generator changes the word length by exactly one. -/
lemma norm_dir_mul (p : Fin k × Bool) (h : Tree k) :
    (dir p * h).norm = if h.toWord.head? = some (p.1, !p.2) then h.norm - 1 else h.norm + 1 := by
  unfold dir FreeGroup.norm
  obtain ⟨a, b⟩ := p
  rw [FreeGroup.toWord_mk_mul_eq]
  split_ifs <;> simp

lemma norm_dir_mul_cases (p : Fin k × Bool) (h : Tree k) :
    (dir p * h).norm + 1 = h.norm ∨ (dir p * h).norm = h.norm + 1 := by
  rw [norm_dir_mul]
  split_ifs with hh
  · left
    have : h.toWord ≠ [] := by intro h0; simp [h0] at hh
    have : 0 < h.norm := by
      unfold FreeGroup.norm; exact List.length_pos_of_ne_nil this
    omega
  · right; rfl

/-- If left multiplication by `dir p⁻¹` shortens `h`, then the reduced word of `h` starts with
the letter `p`. -/
lemma head_of_norm_lt (p : Fin k × Bool) (h : Tree k) (hlt : ((dir p)⁻¹ * h).norm < h.norm) :
    h.toWord.head? = some p := by
  rw [dir_inv, norm_dir_mul] at hlt
  split_ifs at hlt with hh
  · simpa using hh
  · omega

lemma norm_inv_dir_mul_of_head_ne (p : Fin k × Bool) (h : Tree k) (hh : h.toWord.head? ≠ some p) :
    ((dir p)⁻¹ * h).norm = h.norm + 1 := by
  rw [dir_inv, norm_dir_mul]
  simp only [Bool.not_not]
  rw [if_neg (by simpa using hh)]

/-! ### Balls -/

lemma mem_ball {v w : Tree k} {r : ℕ} : w ∈ ball v r ↔ (v⁻¹ * w).norm ≤ r := Iff.rfl

lemma ball_mono {v : Tree k} {r s : ℕ} (h : r ≤ s) : ball v r ⊆ ball v s :=
  fun _ hw => le_trans hw h

lemma mem_ball_self (v : Tree k) (r : ℕ) : v ∈ ball v r := by simp [mem_ball]

lemma preimage_mul_ball (g v : Tree k) (r : ℕ) :
    (fun w => g * w) ⁻¹' ball v r = ball (g⁻¹ * v) r := by
  ext w; simp [mem_ball, mul_assoc]

lemma preimage_inv_mul_ball (g v : Tree k) (r : ℕ) :
    (fun w => g⁻¹ * w) ⁻¹' ball v r = ball (g * v) r := by
  rw [preimage_mul_ball, inv_inv]

/-- The ball around a neighbour is contained in the ball of radius one more. -/
lemma ball_dir_subset (v : Tree k) (p : Fin k × Bool) (r : ℕ) :
    ball (v * dir p) r ⊆ ball v (r + 1) := by
  intro w hw
  rw [mem_ball] at hw ⊢
  have : v⁻¹ * w = dir p * ((v * dir p)⁻¹ * w) := by group
  rw [this]
  rcases norm_dir_mul_cases p ((v * dir p)⁻¹ * w) with h | h <;> omega

lemma ball_subset_ball_dir (v : Tree k) (p : Fin k × Bool) (r : ℕ) :
    ball v r ⊆ ball (v * dir p) (r + 1) := by
  have := ball_dir_subset (v * dir p) (p.1, !p.2) r
  rwa [← dir_inv, mul_inv_cancel_right] at this

/-- A node at distance `≤ r + 1` from both endpoints of an edge is at distance `≤ r` from one of
them (trees are bipartite). -/
lemma ball_inter_ball_subset (v : Tree k) (p : Fin k × Bool) (r : ℕ) :
    ball v (r + 1) ∩ ball (v * dir p) (r + 1) ⊆ ball v r ∪ ball (v * dir p) r := by
  rintro w ⟨h1, h2⟩
  rw [mem_ball] at h1 h2
  have : v⁻¹ * w = dir p * ((v * dir p)⁻¹ * w) := by group
  rw [this] at h1
  rcases norm_dir_mul_cases p ((v * dir p)⁻¹ * w) with h | h
  · left; rw [mem_ball, this]; omega
  · right; rw [mem_ball]; omega

/-- A node in the ball around the neighbour `v * dir p` but not in the ball around `v` lies
"behind" that neighbour: the reduced word of `v⁻¹ w` starts with `p`. -/
lemma head_of_mem_diff {v w : Tree k} {p : Fin k × Bool} {r : ℕ}
    (h1 : w ∈ ball (v * dir p) r) (h2 : w ∉ ball v r) :
    (v⁻¹ * w).toWord.head? = some p ∧ (v⁻¹ * w).norm = r + 1 := by
  rw [mem_ball] at h1 h2
  have e : (v * dir p)⁻¹ * w = (dir p)⁻¹ * (v⁻¹ * w) := by group
  rw [e] at h1
  push_neg at h2
  refine ⟨head_of_norm_lt p _ (by omega), ?_⟩
  have := norm_dir_mul_cases p ((dir p)⁻¹ * (v⁻¹ * w))
  rw [mul_inv_cancel_left] at this
  omega

/-- The parts of the balls around distinct neighbours of `v` outside the ball around `v` are
disjoint. -/
lemma disjoint_diff (v : Tree k) {p q : Fin k × Bool} (hpq : p ≠ q) (r : ℕ) :
    Disjoint (ball (v * dir p) r \ ball v r) (ball (v * dir q) r \ ball v r) := by
  rw [Set.disjoint_left]
  rintro w ⟨h1, h2⟩ ⟨h3, -⟩
  have a := (head_of_mem_diff h1 h2).1
  have b := (head_of_mem_diff h3 h2).1
  rw [a] at b
  exact hpq (Option.some.inj b)

/-- The part of the ball around the neighbour `v * dir p` outside the ball around `v` is disjoint
from the ball of radius `r + 1` around any other neighbour `v * dir q`. -/
lemma disjoint_diff_ball (v : Tree k) {p q : Fin k × Bool} (hpq : p ≠ q) (r : ℕ) :
    Disjoint (ball (v * dir p) r \ ball v r) (ball (v * dir q) (r + 1)) := by
  rw [Set.disjoint_left]
  rintro w ⟨h1, h2⟩ h3
  obtain ⟨a, hn⟩ := head_of_mem_diff h1 h2
  rw [mem_ball] at h3
  have e : (v * dir q)⁻¹ * w = (dir q)⁻¹ * (v⁻¹ * w) := by group
  rw [e, norm_inv_dir_mul_of_head_ne q _ (by rw [a]; simpa using hpq)] at h3
  omega

/-! ### Finite balls -/

lemma ball_finite (r : ℕ) : (ball (1 : Tree k) r).Finite := by
  have : ball (1 : Tree k) r ⊆ FreeGroup.mk '' {L : List (Fin k × Bool) | L.length ≤ r} := by
    intro w hw
    refine ⟨w.toWord, ?_, FreeGroup.mk_toWord⟩
    simpa [mem_ball, FreeGroup.norm] using hw
  exact ((List.finite_length_le (Fin k × Bool) r).image _).subset this

/-- The ball of radius `r` around the origin, as a finite set. -/
def Ball (r : ℕ) : Finset (Tree k) := (ball_finite r).toFinset

@[simp] lemma mem_Ball {w : Tree k} {r : ℕ} : w ∈ Ball r ↔ w.norm ≤ r := by
  simp [Ball, mem_ball]

lemma coe_Ball (r : ℕ) : ((Ball r : Finset (Tree k)) : Set (Tree k)) = ball 1 r := by
  ext w; simp [mem_ball]

lemma ball_subset_Ball {v : Tree k} {r N : ℕ} (h : v.norm + r ≤ N) :
    ball v r ⊆ (Ball N : Finset (Tree k)) := by
  intro w hw
  rw [mem_ball] at hw
  rw [Finset.mem_coe, mem_Ball]
  have : w = v * (v⁻¹ * w) := by group
  rw [this]
  exact (FreeGroup.norm_mul_le _ _).trans (by omega)

lemma Ball_mono {r s : ℕ} (h : r ≤ s) : (Ball r : Finset (Tree k)) ⊆ Ball s := by
  intro w; simp only [mem_Ball]; omega

lemma mem_map_mulLeft {v w : Tree k} {F : Finset (Tree k)} :
    w ∈ F.map (Equiv.mulLeft v).toEmbedding ↔ v⁻¹ * w ∈ F := by
  rw [Finset.mem_map_equiv]; rfl

lemma mem_map_mulLeft_symm {v w : Tree k} {F : Finset (Tree k)} :
    w ∈ F.map (Equiv.mulLeft v).symm.toEmbedding ↔ v * w ∈ F := by
  rw [Finset.mem_map_equiv]; simp

/-! ### Locality under shifts -/

/-- A function of the ball of radius `r` around the origin, evaluated on the field seen from `v`,
depends on the ball of radius `r` around `v`. -/
lemma dependsOn_shift {β : Type*} {g : (Tree k → Ω) → β} {S : Set (Tree k)} (hg : DependsOn g S)
    (v : Tree k) : DependsOn (fun x => g (shift v x)) ((fun w => v⁻¹ * w) ⁻¹' S) := by
  intro x x' hxx'
  apply hg
  intro h hh
  simp only [shift]
  apply hxx'
  simpa using hh

lemma dependsOn_shift_ball {β : Type*} {g : (Tree k → Ω) → β} {u : Tree k} {r : ℕ}
    (hg : DependsOn g (ball u r)) (v : Tree k) :
    DependsOn (fun x => g (shift v x)) (ball (v * u) r) := by
  have := dependsOn_shift hg v
  rwa [preimage_inv_mul_ball] at this

/-! ### Probabilities under shifts -/

variable [Fintype Ω] [Inhabited Ω] {μ : FinDist Ω}

lemma ind_dependsOn {E : (Tree k → Ω) → Prop} {S : Set (Tree k)} (hE : DependsOn E S) :
    DependsOn (ind E) S := by
  intro x x' h; simp only [ind, hE h]

/-- Probabilities are invariant under shifts. -/
lemma prob_shift {E : (Tree k → Ω) → Prop} {D : Set (Tree k)} (hE : DependsOn E D) {v : Tree k}
    {M N : ℕ} (hDN : D ⊆ ball 1 N) (hDM : ∀ w ∈ D, (v * w).norm ≤ M) :
    prob μ (Ball M) (fun x => E (shift v x)) = prob μ (Ball N) E := by
  rw [show (fun x => E (shift v x)) = fun x => E (x ∘ Equiv.mulLeft v) from rfl,
    prob_comp_equiv]
  unfold prob
  apply expect_congr_support
  apply (ind_dependsOn hE).mono
  intro w hw
  simp only [coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_map_mulLeft_symm, mem_Ball]
  refine ⟨hDM w hw, ?_⟩
  have := hDN hw; simpa [mem_ball] using this

/-- Conditional probabilities under shifts. -/
lemma cond_shift {E : (Tree k → Ω) → Prop} {D : Set (Tree k)} (hE : DependsOn E D) {v : Tree k}
    {N : ℕ} (hDN : D ⊆ ball 1 N) (hDM : ∀ w ∈ D, (v * w).norm ≤ N) (S : Set (Tree k))
    (x : Tree k → Ω) :
    cond μ (Ball N) S E (shift v x) =
      cond μ (Ball N) ((fun w => v⁻¹ * w) ⁻¹' S) (fun z => E (shift v z)) x := by
  unfold cond
  rw [shift_eq_comp, condE_comp_equiv]
  have hS : (Equiv.mulLeft v).symm ⁻¹' S = (fun w => v⁻¹ * w) ⁻¹' S := by
    ext w; simp [Equiv.mulLeft_symm]
  rw [hS]
  unfold condE
  apply expect_congr_support
  intro z z' hzz'
  simp only
  have : ∀ y : Tree k → Ω, ind E (y ∘ Equiv.mulLeft v) = ind (fun z => E (shift v z)) y := by
    intro y; rfl
  rw [this, this]
  apply ind_dependsOn (dependsOn_shift hE v)
  intro w hw
  simp only [Set.mem_preimage] at hw
  by_cases hwS : w ∈ (fun w => v⁻¹ * w) ⁻¹' S
  · simp [Set.piecewise, hwS]
  · simp only [Set.piecewise, hwS, if_false]
    apply hzz'
    simp only [coe_inter, Set.mem_inter_iff, Finset.mem_coe, mem_map_mulLeft, mem_Ball]
    have h1 := hDN hw
    have h2 := hDM _ hw
    simp only [mem_ball, inv_one, one_mul] at h1
    simp only [mul_inv_cancel_left] at h2
    exact ⟨h1, h2⟩

end

end Podc.MinimalSymmetryBreaking
