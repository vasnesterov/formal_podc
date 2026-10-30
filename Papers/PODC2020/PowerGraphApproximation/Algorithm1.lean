import Podc.Foundations.Combinatorics.SimpleGraph.Power

/-!
# Algorithm 1: the `(1 + ε)`-approximation for `G²`-MVC (combinatorial core of Theorem 1)

[BCMPP20] R. Bar-Yehuda, K. Censor-Hillel, Y. Maus, S. Pai, S. V. Pemmaraju,
*Distributed Approximation on Power Graphs*, PODC 2020 (arXiv 2006.03746), Section 3.1.

We formalize the *sequential semantics* of Algorithm 1 with `ε = 1/l` (the paper reduces to this
case by `ε' = 1/⌈1/ε⌉`): Phase I repeatedly picks a centre `c ∈ C` with more than `l`
`G`-neighbours in `R`, moves `N(c) ∩ R` to the cover `S = V \ R` and removes `c` from `C`; Phase
II adds an optimal vertex cover `R*` of `G²[U]`, `U = V \ S`. The CONGEST implementation (BFS
pipelining, symmetry breaking by IDs) is not formalized; we prove the facts its round analysis
rests on.

* `lemma_3`: `G²[U]` is determined by the set `F` of `G`-edges touching `U`.
* `lemma_4`: `S ∪ R*` is a vertex cover of `G²`.
* `lemma_5`: `l |S| ≤ (l + 1) |O|` for every vertex cover `O` of `G²[S]`.
* `theorem_1_approx`: `l |S ∪ R*| ≤ (l + 1) |OPT|` (approximation factor `1 + ε`).
* `card_nbrs_U_le` (key fact of Lemma 2): after Phase I every vertex has at most `l`
  `G`-neighbours in `U`, so `|F| ≤ l n`.
* `phase1_length`: Phase I has at most `n/(l+1) ≤ ε n` iterations.
-/

namespace Podc.PowerGraphApproximation.Algorithm1

open SimpleGraph Finset Relation
open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (l : ℕ)

/-- `G`-neighbours of `c` inside `R`. -/
noncomputable def gnbrs (R : Finset V) (c : V) : Finset V := R.filter fun v => G.Adj c v

/-- State of Phase I: the possible centres `C` and the vertices `R` not in the cover. -/
structure State (V : Type*) where
  C : Finset V
  R : Finset V

/-- Initially `C = R = V`. -/
def init : State V := ⟨univ, univ⟩

/-- One iteration of the while loop (lines 4–7). -/
inductive Step : State V → State V → Prop
  | pick {s : State V} {c : V} (hc : c ∈ s.C) (hbig : l < (gnbrs G s.R c).card) :
      Step s ⟨s.C.erase c, s.R \ gnbrs G s.R c⟩

/-- Phase I has ended: no centre has more than `l` neighbours in `R`. -/
def Final (s : State V) : Prop := ∀ c ∈ s.C, (gnbrs G s.R c).card ≤ l

/-- `O` covers all edges of `G²[X]`. -/
def CoversIn (X O : Finset V) : Prop :=
  ∀ u ∈ X, ∀ v ∈ X, (G.power 2).Adj u v → u ∈ O ∨ v ∈ O

variable {G l}

lemma mem_gnbrs {R : Finset V} {c v : V} : v ∈ gnbrs G R c ↔ v ∈ R ∧ G.Adj c v := by
  simp [gnbrs]

/-- Invariant: processed centres have no neighbour left in `R`; the charging bound of Lemma 5
holds for the current cover `S = V \ R`. -/
structure Inv (G : SimpleGraph V) (l : ℕ) (s : State V) : Prop where
  processed : ∀ c ∉ s.C, gnbrs G s.R c = ∅
  charge : ∀ O : Finset V, CoversIn G (univ \ s.R) O →
    l * (univ \ s.R).card ≤ (l + 1) * (O ∩ (univ \ s.R)).card

lemma inv_init : Inv G l (init : State V) where
  processed := by simp [init]
  charge := by simp [init]

lemma inv_step {s t : State V} (hI : Inv G l s) (h : Step G l s t) : Inv G l t := by
  cases h with
  | @pick c hc hbig =>
  set N := gnbrs G s.R c
  have hNR : N ⊆ s.R := filter_subset _ _
  have hS' : univ \ (s.R \ N) = (univ \ s.R) ∪ N := by
    ext v; simp only [mem_sdiff, mem_univ, true_and, mem_union, not_and, not_not]
    constructor
    · intro h; by_cases hv : v ∈ s.R
      · exact Or.inr (h hv)
      · exact Or.inl hv
    · rintro (h | h) h'
      · exact absurd h' h
      · exact h
  have hdisj : Disjoint (univ \ s.R) N := by
    rw [Finset.disjoint_left]; intro v hv hvN; exact (mem_sdiff.1 hv).2 (hNR hvN)
  refine ⟨?_, ?_⟩
  · intro c' hc'
    by_cases hcc : c' = c
    · subst hcc
      ext v; simp only [N, mem_gnbrs, mem_sdiff, notMem_empty, iff_false, not_and]
      intro hv hadj; exact hv.2 hv.1 hadj
    · have : c' ∉ s.C := fun h => hc' (mem_erase.2 ⟨hcc, h⟩)
      have h0 := hI.processed c' this
      ext v
      simp only [mem_gnbrs, mem_sdiff, notMem_empty, iff_false, not_and]
      intro hv hadj
      have : v ∈ gnbrs G s.R c' := mem_gnbrs.2 ⟨hv.1, hadj⟩
      rw [h0] at this; simp at this
  · intro O hO
    rw [hS']
    have hO1 : CoversIn G (univ \ s.R) O := fun u hu v hv huv =>
      hO u (by rw [hS']; exact mem_union_left _ hu) v (by rw [hS']; exact mem_union_left _ hv) huv
    have h1 := hI.charge O hO1
    -- `N` is a clique of `G²` (common neighbour `c`), so `O` contains all but one of it
    have hclique : N.card ≤ (O ∩ N).card + 1 := by
      by_contra hlt
      rw [not_le] at hlt
      have : 2 ≤ (N \ O).card := by
        have := card_sdiff_add_card_inter N O
        rw [inter_comm] at this
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 this
      rw [mem_sdiff] at ha hb
      have hadj : (G.power 2).Adj a b :=
        power_two_adj_of_adj_adj (mem_gnbrs.1 ha.1).2.symm (mem_gnbrs.1 hb.1).2 hab
      rcases hO a (by rw [hS']; exact mem_union_right _ ha.1) b
        (by rw [hS']; exact mem_union_right _ hb.1) hadj with h | h
      · exact ha.2 h
      · exact hb.2 h
    rw [card_union_of_disjoint hdisj, inter_union_distrib_left,
      card_union_of_disjoint (disjoint_of_subset_left inter_subset_right
        (disjoint_of_subset_right inter_subset_right hdisj))]
    have : l + 1 ≤ N.card := hbig
    nlinarith

theorem inv_of_reach {s : State V} (h : ReflTransGen (Step G l) init s) : Inv G l s := by
  induction h with
  | refl => exact inv_init
  | tail _ hst ih => exact inv_step ih hst

/-- **Lemma 5 of [BCMPP20]** (with `ε = 1/l`): after Phase I, `|S| ≤ (1 + ε)|O|`, i.e.
`l |S| ≤ (l + 1) |O|`, for every vertex cover `O` of `G²[S]`, `S = V \ R`. -/
theorem lemma_5 {s : State V} (h : ReflTransGen (Step G l) init s) (O : Finset V)
    (hO : CoversIn G (univ \ s.R) O) :
    l * (univ \ s.R).card ≤ (l + 1) * O.card :=
  ((inv_of_reach h).charge O hO).trans (Nat.mul_le_mul_left _ (card_le_card inter_subset_left))

/-- **Lemma 2 of [BCMPP20]**, key fact: after Phase I every vertex has at most `l = 1/ε`
`G`-neighbours in `U = R`. Hence `|F| ≤ l · n`. -/
theorem card_nbrs_U_le {s : State V} (h : ReflTransGen (Step G l) init s) (hf : Final G l s)
    (v : V) : (gnbrs G s.R v).card ≤ l := by
  by_cases hv : v ∈ s.C
  · exact hf v hv
  · simp [(inv_of_reach h).processed v hv]

/-- **Lemma 3 of [BCMPP20].** For `u, v ∈ U`, adjacency in `G²[U]` is determined by the set `F`
of `G`-edges with an endpoint in `U`: `u ~ v` iff `u ≠ v` and `{u, v} ∈ F` or `u, v` have a common
neighbour `w` with `{u, w}, {w, v} ∈ F`. -/
theorem lemma_3 (U : Finset V) {u v : V} (hu : u ∈ U) (hv : v ∈ U) :
    let F : V → V → Prop := fun a b => G.Adj a b ∧ (a ∈ U ∨ b ∈ U)
    (G.power 2).Adj u v ↔ u ≠ v ∧ (F u v ∨ ∃ w, F u w ∧ F w v) := by
  intro F
  rw [power_two_adj]
  simp only [F]
  constructor
  · rintro ⟨hne, h | ⟨w, h1, h2⟩⟩
    · exact ⟨hne, Or.inl ⟨h, Or.inl hu⟩⟩
    · exact ⟨hne, Or.inr ⟨w, ⟨h1, Or.inl hu⟩, ⟨h2, Or.inr hv⟩⟩⟩
  · rintro ⟨hne, h | ⟨w, h1, h2⟩⟩
    · exact ⟨hne, Or.inl h.1⟩
    · exact ⟨hne, Or.inr ⟨w, h1.1, h2.1⟩⟩

/-- **Lemma 4 of [BCMPP20].** If `R*` covers `G²[U]`, `U = R` after Phase I, then `S ∪ R*` is a
vertex cover of `G²`. -/
theorem lemma_4 (s : State V) {Rs : Finset V} (hRs : CoversIn G s.R Rs) :
    (G.power 2).IsVertexCover (((univ \ s.R) ∪ Rs : Finset V) : Set V) := by
  intro u v huv
  simp only [coe_union, coe_sdiff, coe_univ, Set.mem_union, Set.mem_sdiff, Set.mem_univ,
    true_and, mem_coe]
  by_cases hu : u ∈ s.R
  · by_cases hv : v ∈ s.R
    · rcases hRs u hu v hv huv with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl hv)
  · exact Or.inl (Or.inl hu)

/-- **Theorem 1 of [BCMPP20]**, approximation factor (with `ε = 1/l`): for an optimal vertex
cover `R*` of `G²[U]` (optimal among covers inside `U`), `|S ∪ R*| ≤ (1 + ε) |OPT|` for every
vertex cover `OPT` of `G²`. -/
theorem theorem_1_approx {s : State V} (h : ReflTransGen (Step G l) init s) {Rs : Finset V}
    (hopt : ∀ D ⊆ s.R, CoversIn G s.R D → Rs.card ≤ D.card) (OPT : Finset V)
    (hOPT : (G.power 2).IsVertexCover (OPT : Set V)) :
    l * ((univ \ s.R) ∪ Rs).card ≤ (l + 1) * OPT.card := by
  have hS := (inv_of_reach h).charge OPT (fun u _ v _ huv => hOPT huv)
  have hU : Rs.card ≤ (OPT ∩ s.R).card :=
    hopt _ inter_subset_right (fun u hu v hv huv => by
      rcases hOPT huv with h | h
      · exact Or.inl (mem_inter.2 ⟨h, hu⟩)
      · exact Or.inr (mem_inter.2 ⟨h, hv⟩))
  have hsplit : (OPT ∩ (univ \ s.R)).card + (OPT ∩ s.R).card = OPT.card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext v; by_cases hv : v ∈ s.R <;> simp [hv]
    · rw [Finset.disjoint_left]; intro v h1 h2
      exact (mem_sdiff.1 (mem_inter.1 h1).2).2 (mem_inter.1 h2).2
  have := card_union_le (univ \ s.R) Rs
  nlinarith

/-- Phase I takes at most `n / (l + 1)` iterations (`≤ ε n`): every iteration moves more than
`l` vertices out of `R`. -/
theorem phase1_length (f : ℕ → State V) (m : ℕ) (h0 : f 0 = init)
    (hf : ∀ i < m, Step G l (f i) (f (i + 1))) : m * (l + 1) ≤ Fintype.card V := by
  have : ∀ i ≤ m, (f i).R.card + i * (l + 1) ≤ Fintype.card V := by
    intro i hi
    induction i with
    | zero => simp [h0, init]
    | succ i ih =>
      have ih := ih (by omega)
      have hs := hf i (by omega)
      cases hs' : f (i + 1) with
      | mk C' R' =>
      rw [hs'] at hs
      cases hs with
      | @pick c hc hbig =>
      have := card_sdiff_add_card_inter (f i).R (gnbrs G (f i).R c)
      have hsub : (f i).R ∩ gnbrs G (f i).R c = gnbrs G (f i).R c :=
        inter_eq_right.2 (filter_subset _ _)
      rw [hsub] at this
      simp only
      nlinarith
  have := this m le_rfl
  omega

/-- Phase I always terminates in a final state. -/
theorem exists_final : ∃ s, ReflTransGen (Step G l) init s ∧ Final G l s := by
  suffices H : ∀ k, ∀ s, ReflTransGen (Step G l) init s → s.R.card + s.C.card ≤ k →
      ∃ t, ReflTransGen (Step G l) init t ∧ Final G l t from H _ init .refl le_rfl
  intro k
  induction k with
  | zero =>
    intro s hs hk
    refine ⟨s, hs, fun c hc => ?_⟩
    have : s.C.card = 0 := by omega
    simp [card_eq_zero.1 this] at hc
  | succ k ih =>
    intro s hs hk
    by_cases hf : Final G l s
    · exact ⟨s, hs, hf⟩
    simp only [Final, not_forall, not_le] at hf
    obtain ⟨c, hc, hbig⟩ := hf
    have hst := Step.pick (G := G) (l := l) hc hbig
    refine ih _ (hs.tail hst) ?_
    have h1 := card_erase_of_mem hc
    have h2 : (s.R \ gnbrs G s.R c).card ≤ s.R.card := card_le_card sdiff_subset
    have h3 : 0 < s.C.card := card_pos.2 ⟨c, hc⟩
    simp only
    omega

end Podc.PowerGraphApproximation.Algorithm1
