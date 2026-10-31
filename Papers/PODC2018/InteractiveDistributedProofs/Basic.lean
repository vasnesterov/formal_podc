import Mathlib

/-!
# Graph symmetry and the adjacency-row sums (Section 2.3, Observation 1, Lemma 3.1)

Kol, Oshman, Saxena. *Interactive Distributed Proofs.* PODC 2018.

The network is a finite simple graph `G` on a vertex type `V`. As in the paper, the
neighbourhood `N(v)` contains `v` itself (`cnbhd G v`). For a vertex `w` and a set `S`,
`rowMat R w S` is the `V × V` matrix `[w, S]` over a semiring `R` whose row `w` is the
characteristic vector of `S` and whose other rows are zero. The paper's two matrices are

* `adjSum R G = ∑_v [v, N(v)]` (the adjacency matrix with self-loops), and
* `permSum R G ρ = ∑_v [ρ(v), ρ(N(v))]` (the `ρ`-permuted one, for any map `ρ : V → V`).

## Main results

* `observation_1`: a permutation `ρ` is an automorphism iff `N(ρ v) = ρ(N v)` for all `v`.
* `lemma_3_1`: if `adjSum = permSum ρ` (over any nontrivial semiring, e.g. `ZMod p`), then `ρ` is an
  automorphism (in particular a permutation).
* `permSum_eq_adjSum`: the converse, used for completeness.
* `sym_iff_nontrivial_aut`: `Sym` agrees with Mathlib's graph automorphism group being nontrivial.
-/

open Finset

namespace Podc.InteractiveDistributedProofs

variable {V : Type*} [Fintype V] [DecidableEq V]

section Neighbourhood

open Classical in
/-- The closed neighbourhood `N(v)` of the paper (it contains `v`). -/
noncomputable def cnbhd (G : SimpleGraph V) (v : V) : Finset V :=
  univ.filter fun u => u = v ∨ G.Adj v u

variable {G : SimpleGraph V}

theorem mem_cnbhd {u v : V} : u ∈ cnbhd G v ↔ u = v ∨ G.Adj v u := by
  classical
  simp [cnbhd]

theorem self_mem_cnbhd (v : V) : v ∈ cnbhd G v := mem_cnbhd.2 (Or.inl rfl)

theorem mem_cnbhd_comm {u v : V} : u ∈ cnbhd G v ↔ v ∈ cnbhd G u := by
  simp only [mem_cnbhd]
  constructor <;> rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr h.symm
  · exact Or.inl h.symm
  · exact Or.inr h.symm

end Neighbourhood

section Symmetry

/-- A permutation `ρ : V → V` is an automorphism of `G` if `{u, v} ∈ E ↔ {ρ u, ρ v} ∈ E`
(Section 2.3). -/
def IsAut (G : SimpleGraph V) (ρ : V → V) : Prop :=
  Function.Bijective ρ ∧ ∀ u v, G.Adj (ρ u) (ρ v) ↔ G.Adj u v

/-- Definition 3: the language `Sym` of graphs with a non-trivial automorphism. -/
def Sym (G : SimpleGraph V) : Prop :=
  ∃ ρ : V → V, IsAut G ρ ∧ ρ ≠ id

/-- `Sym` is Mathlib's "the automorphism group `G ≃g G` is nontrivial". -/
theorem sym_iff_nontrivial_aut (G : SimpleGraph V) : Sym G ↔ Nontrivial (G ≃g G) := by
  constructor
  · rintro ⟨ρ, ⟨hb, hadj⟩, hne⟩
    let φ : G ≃g G := ⟨Equiv.ofBijective ρ hb, fun {a b} => hadj a b⟩
    refine ⟨⟨φ, 1, fun h => hne ?_⟩⟩
    funext v
    exact congrArg (fun ψ : G ≃g G => ψ v) h
  · rintro ⟨φ, ψ, hne⟩
    by_contra hS
    apply hne
    have key : ∀ χ : G ≃g G, χ = 1 := by
      intro χ
      by_contra hχ
      apply hS
      refine ⟨χ, ⟨χ.bijective, fun u v => χ.map_adj_iff⟩, fun h => hχ ?_⟩
      ext v
      exact congrFun h v
    rw [key φ, key ψ]

end Symmetry

section Matrices

variable (R : Type*) [Semiring R]

/-- The matrix `[w, S]`: row `w` is the characteristic vector of `S`, all other rows are `0`. -/
def rowMat (w : V) (S : Finset V) : V × V → R :=
  fun q => if q.1 = w ∧ q.2 ∈ S then 1 else 0

/-- `∑_v [v, N(v)]`: the adjacency matrix of `G` with self-loops. -/
noncomputable def adjSum (G : SimpleGraph V) : V × V → R :=
  ∑ v, rowMat R v (cnbhd G v)

/-- `∑_v [ρ(v), ρ(N(v))]` for an arbitrary map `ρ : V → V`. -/
noncomputable def permSum (G : SimpleGraph V) (ρ : V → V) : V × V → R :=
  ∑ v, rowMat R (ρ v) ((cnbhd G v).image ρ)

variable {R}
variable {G : SimpleGraph V}

theorem adjSum_apply (x y : V) :
    adjSum R G (x, y) = if y ∈ cnbhd G x then 1 else 0 := by
  simp only [adjSum, Finset.sum_apply, rowMat]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem permSum_apply_of_injective {ρ : V → V} (hρ : Function.Injective ρ) (u y : V) :
    permSum R G ρ (ρ u, y) = if y ∈ (cnbhd G u).image ρ then 1 else 0 := by
  simp only [permSum, Finset.sum_apply, rowMat]
  rw [Finset.sum_eq_single u]
  · simp
  · intro b _ hb
    have : ¬ ρ u = ρ b := fun h => hb (hρ h).symm
    simp [this]
  · simp

theorem permSum_apply_of_notMem_range {ρ : V → V} {x : V} (hx : ∀ v, ρ v ≠ x) (y : V) :
    permSum R G ρ (x, y) = 0 := by
  simp only [permSum, Finset.sum_apply, rowMat]
  refine Finset.sum_eq_zero fun v _ => ?_
  simp [Ne.symm (hx v)]

/-- **Observation 1.** A permutation `ρ` is an automorphism of `G` iff `N(ρ v) = ρ(N v)` for every
`v`. -/
theorem observation_1 {ρ : V → V} (hρ : Function.Bijective ρ) :
    IsAut G ρ ↔ ∀ v, cnbhd G (ρ v) = (cnbhd G v).image ρ := by
  constructor
  · rintro ⟨-, hadj⟩ v
    ext w
    obtain ⟨w', rfl⟩ := hρ.2 w
    simp only [mem_cnbhd, Finset.mem_image]
    constructor
    · rintro (h | h)
      · exact ⟨v, Or.inl rfl, (hρ.1 h).symm ▸ rfl⟩
      · exact ⟨w', Or.inr ((hadj v w').1 h), rfl⟩
    · rintro ⟨x, hx | hx, hxw⟩
      · subst hx; exact Or.inl hxw.symm
      · have := hρ.1 hxw; subst this; exact Or.inr ((hadj v x).2 hx)
  · intro h
    refine ⟨hρ, fun u v => ?_⟩
    have hmem := congrArg (ρ v ∈ ·) (h u)
    simp only [mem_cnbhd, Finset.mem_image, eq_iff_iff] at hmem
    have hinj := hρ.1
    constructor
    · intro hA
      have : ρ v = ρ u ∨ G.Adj (ρ u) (ρ v) := Or.inr hA
      obtain ⟨x, hx, hxv⟩ := hmem.1 this
      have := hinj hxv; subst this
      rcases hx with hx | hx
      · subst hx; exact absurd hA (G.irrefl)
      · exact hx
    · intro hA
      rcases hmem.2 ⟨v, Or.inr hA, rfl⟩ with h' | h'
      · exact absurd (hinj h' ▸ hA) (G.irrefl)
      · exact h'

/-- Converse of Lemma 3.1: for an automorphism the two sums coincide. -/
theorem permSum_eq_adjSum {ρ : V → V} (hρ : IsAut G ρ) : permSum R G ρ = adjSum R G := by
  have h := (observation_1 hρ.1).1 hρ
  simp only [permSum, adjSum, ← h]
  exact Function.Bijective.sum_comp hρ.1 (fun w => rowMat R w (cnbhd G w))

variable [Nontrivial R]

/-- **Lemma 3.1.** Let `ρ : V → V` be any map with `∑_v [v, N(v)] = ∑_v [ρ(v), ρ(N(v))]`
(sums in a nontrivial semiring, e.g. `ZMod p`). Then `ρ` is an automorphism of `G`. -/
theorem lemma_3_1 {ρ : V → V} (h : adjSum R G = permSum R G ρ) : IsAut G ρ := by
  -- `ρ` is surjective: a vertex outside the range has a zero row on the right but not on the left
  have hsurj : Function.Surjective ρ := by
    intro x
    by_contra hx
    push Not at hx
    have h1 := congrFun h (x, x)
    rw [adjSum_apply, permSum_apply_of_notMem_range hx] at h1
    simp [self_mem_cnbhd] at h1
  have hbij : Function.Bijective ρ := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  refine (observation_1 hbij).2 fun u => ?_
  ext y
  have h1 := congrFun h (ρ u, y)
  rw [adjSum_apply, permSum_apply_of_injective hbij.1] at h1
  by_cases h2 : y ∈ cnbhd G (ρ u) <;> by_cases h3 : y ∈ (cnbhd G u).image ρ <;>
    simp_all

/-- The adjacency sum is never zero (its diagonal is all ones). -/
theorem adjSum_ne_zero [Nonempty V] : adjSum R G ≠ 0 := by
  intro h
  obtain ⟨v⟩ := ‹Nonempty V›
  have := congrFun h (v, v)
  rw [adjSum_apply] at this
  simp [self_mem_cnbhd] at this

/-- For a non-symmetric graph and a non-identity map `ρ`, the two sums differ (this is how Lemma 3.1
is used in the soundness proofs). -/
theorem adjSum_ne_permSum {ρ : V → V} (hG : ¬ Sym G) (hρ : ρ ≠ id) :
    adjSum R G ≠ permSum R G ρ :=
  fun h => hG ⟨ρ, lemma_3_1 h, hρ⟩

end Matrices

end Podc.InteractiveDistributedProofs
