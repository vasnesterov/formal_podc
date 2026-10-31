import Papers.PODC2015.RandomizedPLS.Compile
import Papers.PODC2015.RandomizedPLS.LowerBound
import Cslib.Foundations.Combinatorics.SimpleGraph.WalkParity
import Cslib.Foundations.Combinatorics.SimpleGraph.Arboricity

/-!
# Acyclicity: upper bounds (Section 5.1)

Theorem 5.1 states that the randomized verification complexity of MST on connected graphs is
`Θ(log log n)`; the lower bound is proved for the simpler predicate *acyclicity*, and the upper
bound combines Theorem 3.1 with the `O(log² n)` MST scheme of Korman–Kutten–Peleg (not formalized).
We formalize the acyclicity version of both bounds.

* `acyclicPLS`: the classical deterministic PLS for acyclicity on connected graphs, with labels of
  `⌊log₂ n⌋ + 1` bits (distance to a root, in binary). The verifier checks that the neighbours'
  numbers differ from its own and that at most one of them is smaller; soundness is CSLib's
  `isAcyclic_of_rank` (it does not even need connectivity).
* `acyclic_rpls`: compiled by Theorem 3.1, a one-sided edge-independent RPLS with certificates of
  `2 log₂(⌊log₂ n⌋ + 1) + 6 = O(log log n)` bits.
-/

namespace Podc.RandomizedPLS

open Classical SimpleGraph

variable {S : Type}

/-- Connected configurations (`F_con`). -/
def Fcon (c : Config S) : Prop := c.Connected

/-- A refutation of `(F, P)` by a configuration with distinct states (identities) is also a
refutation of `(F', P)` for every family `F'` containing the members of `F` with distinct states.
Used to state the lower bounds of Section 5 for every family between "connected, with distinct
identities" (the paper's model) and arbitrary configurations. -/
lemma Refuted.mono {F F' P : Config S → Prop}
    (hFF : ∀ c, F c → Function.Injective c.state → F' c) {c' : Config S}
    (hinj : Function.Injective c'.state) (h : Refuted F P c') : Refuted F' P c' := by
  rcases h with ⟨hF, hP⟩ | ⟨U, hU, hF, hP⟩
  · exact Or.inl ⟨hFF _ hF hinj, hP⟩
  · exact Or.inr ⟨U, hU, hFF _ hF (hinj.comp Subtype.val_injective), hP⟩

/-- The acyclicity predicate. -/
def Acyclic (c : Config S) : Prop := c.graph.IsAcyclic

namespace Acyc

/-- The verifier: decode the own number `d` and the neighbours' numbers; all differ from `d`, at
most one is smaller. -/
noncomputable def ver : Verifier S := fun _ x ls =>
  decide ((∀ y ∈ ls, decN y ≠ decN x) ∧ ((ls.map decN).filter (· < decN x)).length ≤ 1)

/-- The prover: the distance to an arbitrary root, in binary. -/
noncomputable def prover (c : Config S) (v : c.V) : List Bool :=
  if h : Nonempty c.V then encN (c.graph.dist (Classical.choice h) v) else []

lemma graph_adj_iff (c : Config S) {u v : c.V} : c.graph.Adj u v ↔ v ∈ c.nbrs u := Iff.rfl

lemma eq_of_mem_filter_length_le_one {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {p : α → Bool} (h : (l.filter p).length ≤ 1) {a b : α} (ha : a ∈ l.filter p)
    (hb : b ∈ l.filter p) : a = b := by
  by_contra hab
  have h2 : ({a, b} : Finset α) ⊆ (l.filter p).toFinset := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.2 ha
    · exact List.mem_toFinset.2 hb
  have := Finset.card_le_card h2
  rw [Finset.card_pair hab, List.toFinset_card_of_nodup (hl.filter p)] at this
  omega

/-- Soundness: an accepted configuration is acyclic. -/
lemma acyclic_of_accepts (c : Config S) (ℓ : c.V → List Bool) (h : Accepts ver c ℓ) :
    Acyclic c := by
  have h' : ∀ v, (∀ w ∈ c.nbrs v, decN (ℓ w) ≠ decN (ℓ v)) ∧
      (((c.nbrs v).map ℓ |>.map decN).filter (· < decN (ℓ v))).length ≤ 1 := by
    intro v
    have := h v
    simp only [ver, decide_eq_true_eq, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at this
    exact this
  refine isAcyclic_of_rank (fun v => decN (ℓ v)) (fun u v huv => (h' u).1 v huv |>.symm) ?_
  intro v u u' hu hu' hlt hlt'
  have hlen := (h' v).2
  rw [List.map_map, List.filter_map, List.length_map] at hlen
  refine eq_of_mem_filter_length_le_one (c.nodup v) (p := fun w => decide (decN (ℓ w) < decN (ℓ v)))
    ?_ (List.mem_filter.2 ⟨hu, by simpa using hlt⟩) (List.mem_filter.2 ⟨hu', by simpa using hlt'⟩)
  simpa [Function.comp_def] using hlen

/-- Adjacent vertices of a forest have distinct distances from any vertex. -/
lemma dist_ne_of_adj {V : Type*} {G : SimpleGraph V} (hG : G.IsAcyclic) {s u v : V}
    (hu : G.Reachable s u) (h : G.Adj u v) : G.dist s u ≠ G.dist s v := by
  intro he
  have hv : G.Reachable s v := hu.trans h.reachable
  have h1 := mem_walkSet_succ_of_adj hu.mem_walkSet_dist h
  have h2 := hv.mem_walkSet_dist
  have := mod_two_eq_of_colorable hG.colorable_two h1 h2
  omega

lemma dist_lt_card {V : Type*} [Fintype V] {G : SimpleGraph V} {s v : V} (h : G.Reachable s v) :
    G.dist s v < Fintype.card V := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  rw [← hp]
  exact (p.isPath_of_length_eq_dist hp).length_lt

/-- Completeness: a connected acyclic configuration is accepted with the prover's labels. -/
lemma accepts_prover (c : Config S) (hc : Fcon c) (ha : Acyclic c) :
    Accepts ver c (prover c) := by
  haveI hne : Nonempty c.V := hc.nonempty
  set s := Classical.choice hne
  have hp : ∀ v, prover c v = encN (c.graph.dist s v) := fun v => by
    simp [prover, hne, s]
  intro v
  simp only [ver, decide_eq_true_eq, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, hp, decN_encN]
  refine ⟨fun w hw => (dist_ne_of_adj ha (hc.preconnected s v) hw).symm, ?_⟩
  simp only [List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup ((c.nodup v).filter _)]
  refine Finset.card_le_one.2 fun a ha' b hb' => ?_
  simp only [List.mem_toFinset, List.mem_filter, Function.comp_apply, hp, decN_encN,
    decide_eq_true_eq] at ha' hb'
  have hra := hc.preconnected s a
  have hrb := hc.preconnected s b
  have hda : c.graph.dist s a + 1 = c.graph.dist s v := by
    have := (hra).dist_le_dist_add_one_of_adj (G := c.graph) (c.symm _ _ ha'.1); omega
  have hdb : c.graph.dist s b + 1 = c.graph.dist s v := by
    have := (hrb).dist_le_dist_add_one_of_adj (G := c.graph) (c.symm _ _ hb'.1); omega
  exact ha.eq_of_dist_add_one (c.symm _ _ ha'.1) (c.symm _ _ hb'.1) hra hrb hda hdb

/-- The deterministic PLS for acyclicity on connected configurations. -/
theorem acyclicPLS : IsPLS (ver (S := S)) prover Fcon Acyclic :=
  ⟨fun c hF hP => accepts_prover c hF hP, fun c _ hP ℓ hacc => hP (acyclic_of_accepts c ℓ hacc)⟩

/-- Its labels have `⌊log₂ n⌋ + 1` bits. -/
theorem acyclicPLS_labelBound :
    LabelBound (prover (S := S)) Fcon Acyclic (fun c => Nat.log 2 (Fintype.card c.V) + 1) := by
  intro c hF _ v
  haveI hne : Nonempty c.V := hF.nonempty
  simp only [prover, hne, dite_true]
  refine (length_encN _).trans (Nat.add_le_add_right (Nat.log_mono_right ?_) 1)
  exact (dist_lt_card (hF.preconnected _ v)).le

end Acyc

/-- **Theorem 5.1 of [BFP15], upper bound (acyclicity version).** Acyclicity on connected
configurations has a one-sided (hence also two-sided), edge-independent RPLS with certificates of
`2 log₂(⌊log₂ n⌋ + 1) + 6 = O(log log n)` bits. -/
theorem thm_5_1_upper :
    ∃ (e : EIScheme S (List (List Bool))) (prover : ∀ c : Config S, c.V → List (List Bool)),
      IsRPLS e.toRScheme prover Fcon Acyclic 1 (2 / 3) ∧
      CertBound e.toRScheme prover Fcon Acyclic
        (fun c => 2 * Nat.log 2 (Nat.log 2 (Fintype.card c.V) + 1) + 6) :=
  ⟨_, _, theorem_3_1 Acyc.acyclicPLS Acyc.acyclicPLS_labelBound⟩

end Podc.RandomizedPLS
