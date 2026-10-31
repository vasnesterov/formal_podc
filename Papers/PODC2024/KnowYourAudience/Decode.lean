import Papers.PODC2024.KnowYourAudience.Views
import Papers.PODC2024.KnowYourAudience.Kernel

/-!
# Decoding the input frequencies from a view (Section 4.2)

From its view, an agent extracts the set `S` of the depth-`(s+1)` views of all agents (the vertices
of the minimum base, once colour refinement has stabilised), the numbers `edgeCount s c c'` of
edges from the class `c` into an agent of the class `c'` (the multiplicities `d_{c,c'}` of the
base), and the class outdegrees `b c`. It solves the homogeneous system of eq. (1),
`b_c y_c = ∑_{c'} d_{c,c'} y_{c'}`, in positive integers (`solve`), and outputs the multiset with
each class value repeated `y_c` times.

* `isSol_card`: the fibre cardinalities form a positive solution (eq. (1)).
* `solve_correct`: every positive solution is proportional to the fibre cardinalities (rank one,
  `exists_eq_mul_of_irreducible`), so the decoded multiset has the frequencies of the input.
* `classes_eq`: with enough lookahead the extracted set of classes is the set of all views.
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset Filter

open scoped Classical

universe u

variable {I : Type u}

/-- Number of edges from (agents of) class `c` into an agent of class `c'`. -/
noncomputable def edgeCount (s : ℕ) (c c' : Msg I (s + 1)) : ℕ :=
  (Msg.kids s c').count (Msg.trunc s c)

/-- `y` is a positive solution of eq. (1) on the classes `S`. -/
def IsSol (s : ℕ) (b : Msg I (s + 1) → ℕ) (S : Finset (Msg I (s + 1)))
    (y : Msg I (s + 1) → ℕ) : Prop :=
  (∀ c ∈ S, 0 < y c) ∧ ∀ c ∈ S, b c * y c = ∑ c' ∈ S, edgeCount s c c' * y c'

/-- Solve eq. (1) and output the multiset in which the value of class `c` occurs `y_c` times. -/
noncomputable def solve (s : ℕ) (b : Msg I (s + 1) → ℕ) (S : Finset (Msg I (s + 1))) :
    Option (Multiset I) :=
  if h : ∃ y, IsSol s b S y then
    some (∑ c ∈ S, (Classical.choose h c) • ({Msg.val (s + 1) c} : Multiset I))
  else none

/-- The classes seen in a multiset `R` of depth-`(s+1+K)` views, with lookahead `K`. -/
noncomputable def classes (s K : ℕ) (R : Multiset (Msg I (s + 1 + K))) : Finset (Msg I (s + 1)) :=
  R.toFinset.biUnion (desc (s + 1) K)

variable {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) (x : V → I) (dd : ℕ → ℕ)

lemma classes_eq (s K : ℕ) (hK : ∀ j i : V, ReachLE N K j i) (i : V) :
    classes s K ((N.inN i).val.map (msg N x dd (s + 1 + K))) = univ.image (msg N x dd (s + 1)) := by
  ext m
  simp only [classes, Finset.mem_biUnion, Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨k, _, rfl⟩, hm⟩
    rw [desc_msg] at hm
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hm
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨_, ⟨i, N.self_mem_inN i, rfl⟩, ?_⟩
    rw [desc_msg]
    exact Finset.mem_image.2 ⟨j, by simpa using hK j i, rfl⟩

/-- The fibre of the class `c`. -/
noncomputable def fibre (s : ℕ) (c : Msg I (s + 1)) : Finset V :=
  univ.filter fun j => msg N x dd (s + 1) j = c

lemma edgeCount_msg (s : ℕ) (hst : ∀ j k : V, msg N x dd (s + 1) j = msg N x dd (s + 1) k ↔
      msg N x dd s j = msg N x dd s k) (j₀ k : V) :
    edgeCount s (msg N x dd (s + 1) j₀) (msg N x dd (s + 1) k) =
      ((N.inN k).filter fun j => msg N x dd (s + 1) j = msg N x dd (s + 1) j₀).card := by
  simp only [edgeCount, kids_msg, trunc_msg, Multiset.count_map]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro j _
  rw [hst, eq_comm]

/-- **Eq. (1)**: the fibre cardinalities solve the system. -/
theorem isSol_card (s : ℕ) (b : Msg I (s + 1) → ℕ)
    (hb : ∀ j, b (msg N x dd (s + 1) j) = N.outdeg j)
    (hst : ∀ j k : V, msg N x dd (s + 1) j = msg N x dd (s + 1) k ↔
      msg N x dd s j = msg N x dd s k) :
    IsSol s b (univ.image (msg N x dd (s + 1))) (fun c => (fibre N x dd s c).card) := by
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.card_pos.2 ⟨j, by simp [fibre]⟩
  · intro c hc
    obtain ⟨j₀, -, rfl⟩ := Finset.mem_image.1 hc
    set c := msg N x dd (s + 1) j₀ with hc_def
    -- left-hand side: total outdegree of the fibre
    have h1 : b c * (fibre N x dd s c).card = ∑ j ∈ fibre N x dd s c, (N.out j).card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [← hj, hb]; rfl
    -- double counting of the edges leaving the fibre
    have h2 : ∑ j ∈ fibre N x dd s c, (N.out j).card =
        ∑ k, ((N.inN k).filter fun j => msg N x dd (s + 1) j = c).card := by
      have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := fibre N x dd s c) (t := (univ : Finset V)) (r := fun j k => k ∈ N.out j)
      convert this using 2 with j _ k _
      · congr 1; ext k; simp [Finset.bipartiteAbove]
      · congr 1; ext j; simp [Finset.bipartiteBelow, fibre, and_comm]
    -- right-hand side, fibrewise
    have h3 : ∑ c' ∈ univ.image (msg N x dd (s + 1)), edgeCount s c c' * (fibre N x dd s c').card =
        ∑ k, edgeCount s c (msg N x dd (s + 1) k) := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := (univ : Finset V))
        (t := univ.image (msg N x dd (s + 1))) (g := msg N x dd (s + 1))
        (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k))]
      apply Finset.sum_congr rfl
      intro c' _
      rw [Finset.sum_congr rfl (g := fun _ => edgeCount s c c') (fun k hk => by
        rw [(Finset.mem_filter.1 hk).2])]
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
      rfl
    rw [h1, h2, h3]
    apply Finset.sum_congr rfl
    intro k _
    rw [hc_def, edgeCount_msg N x dd s hst]

/-- Classes are connected by edges as soon as the agents are. -/
lemma classes_connected (s : ℕ) (hsc : N.StronglyConnected) :
    ∀ c ∈ univ.image (msg N x dd (s + 1)), ∀ c' ∈ univ.image (msg N x dd (s + 1)),
      Relation.ReflTransGen (fun a a' => a ∈ univ.image (msg N x dd (s + 1)) ∧
        a' ∈ univ.image (msg N x dd (s + 1)) ∧ 0 < edgeCount s a a') c c' := by
  intro c hc c' hc'
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 hc'
  refine Relation.ReflTransGen.lift (msg N x dd (s + 1)) (fun k k' hkk' => ?_) _ _ (hsc j j')
  refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
    Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  simp only [edgeCount, kids_msg, trunc_msg]
  rw [Multiset.count_pos, Multiset.mem_map]
  exact ⟨k, by simpa [Network.Adj] using hkk', rfl⟩

/-- Counting the occurrences of `a` in a multiset of the form `∑ c, y c • {val c}`. -/
lemma count_sum_nsmul {s : ℕ} (S : Finset (Msg I (s + 1))) (y : Msg I (s + 1) → ℕ) (a : I) :
    (∑ c ∈ S, y c • ({Msg.val (s + 1) c} : Multiset I)).count a =
      ∑ c ∈ S, if Msg.val (s + 1) c = a then y c else 0 := by
  rw [Multiset.count_sum']
  apply Finset.sum_congr rfl
  intro c _
  rw [Multiset.count_nsmul, Multiset.count_singleton]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

lemma card_sum_nsmul {s : ℕ} (S : Finset (Msg I (s + 1))) (y : Msg I (s + 1) → ℕ) :
    Multiset.card (∑ c ∈ S, y c • ({Msg.val (s + 1) c} : Multiset I)) = ∑ c ∈ S, y c := by
  simp [Multiset.card_sum]

/-- The input counts, fibrewise. -/
lemma card_filter_eq_sum (s : ℕ) (a : I) :
    (univ.filter fun j => x j = a).card = ∑ c ∈ univ.image (msg N x dd (s + 1)),
      if Msg.val (s + 1) c = a then (fibre N x dd s c).card else 0 := by
  rw [Finset.card_eq_sum_card_fiberwise (f := msg N x dd (s + 1))
    (t := univ.image (msg N x dd (s + 1)))
    (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k))]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨j₀, -, rfl⟩ := Finset.mem_image.1 hc
  rw [val_msg]
  split_ifs with h
  · congr 1; ext j
    simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro hj; rw [← h, ← val_msg N x dd (s + 1) j, hj, val_msg]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    intro hj'
    apply h
    rw [← hj, ← val_msg N x dd (s + 1) j, hj', val_msg]

lemma card_eq_sum_fibre (s : ℕ) :
    Fintype.card V = ∑ c ∈ univ.image (msg N x dd (s + 1)), (fibre N x dd s c).card := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := msg N x dd (s + 1))
    (t := univ.image (msg N x dd (s + 1)))
    (fun k _ => Finset.mem_image_of_mem _ (Finset.mem_univ k))]
  rfl

/-- **Correctness of the decoding.** Once colour refinement is stable at depth `s`, solving eq. (1)
on the classes yields a nonempty multiset with the input frequencies. -/
theorem solve_correct [Nonempty V] (hsc : N.StronglyConnected) (s : ℕ) (b : Msg I (s + 1) → ℕ)
    (hb : ∀ j, b (msg N x dd (s + 1) j) = N.outdeg j)
    (hst : ∀ j k : V, msg N x dd (s + 1) j = msg N x dd (s + 1) k ↔
      msg N x dd s j = msg N x dd s k) :
    ∃ u, solve s b (univ.image (msg N x dd (s + 1))) = some u ∧ u ≠ 0 ∧
      ∀ a, u.count a * Fintype.card V =
        (univ.filter fun j => x j = a).card * Multiset.card u := by
  set S := univ.image (msg N x dd (s + 1)) with hS
  have hex : ∃ y, IsSol s b S y := ⟨_, isSol_card N x dd s b hb hst⟩
  set y := Classical.choose hex with hy_def
  have hy : IsSol s b S y := Classical.choose_spec hex
  refine ⟨∑ c ∈ S, y c • ({Msg.val (s + 1) c} : Multiset I), by simp [solve, hex, y], ?_, ?_⟩
  · intro h0
    have := congrArg Multiset.card h0
    rw [card_sum_nsmul, Multiset.card_zero, Finset.sum_eq_zero_iff] at this
    obtain ⟨j⟩ := ‹Nonempty V›
    have hm : msg N x dd (s + 1) j ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ j)
    exact (hy.1 _ hm).ne' (this _ hm)
  · -- rank one
    have hz := isSol_card N x dd s b hb hst
    obtain ⟨r, hr⟩ := exists_eq_mul_of_irreducible S (edgeCount s) b (fun c => (y c : ℚ))
      (fun c => ((fibre N x dd s c).card : ℚ))
      (fun c hc => by exact_mod_cast hy.2 c hc) (fun c hc => by exact_mod_cast hz.2 c hc)
      (fun c hc => by exact_mod_cast hz.1 c hc) (classes_connected N x dd s hsc)
    intro a
    rw [count_sum_nsmul, card_sum_nsmul, card_filter_eq_sum N x dd s a, card_eq_sum_fibre N x dd s]
    have key : ∀ (w : Msg I (s + 1) → ℕ), (∀ c ∈ S, (y c : ℚ) = r * w c) →
        ((∑ c ∈ S, if Msg.val (s + 1) c = a then y c else 0 : ℕ) : ℚ) =
          r * ((∑ c ∈ S, if Msg.val (s + 1) c = a then w c else 0 : ℕ) : ℚ) ∧
        ((∑ c ∈ S, y c : ℕ) : ℚ) = r * ((∑ c ∈ S, w c : ℕ) : ℚ) := by
      intro w hw
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      refine ⟨Finset.sum_congr rfl fun c hc => ?_, Finset.sum_congr rfl fun c hc => hw c hc⟩
      split_ifs <;> simp [hw c hc]
    obtain ⟨k1, k2⟩ := key _ hr
    have : ((∑ c ∈ S, if Msg.val (s + 1) c = a then y c else 0 : ℕ) : ℚ) *
        ((∑ c ∈ S, (fibre N x dd s c).card : ℕ) : ℚ) =
        ((∑ c ∈ S, if Msg.val (s + 1) c = a then (fibre N x dd s c).card else 0 : ℕ) : ℚ) *
        ((∑ c ∈ S, y c : ℕ) : ℚ) := by
      rw [k1, k2]; ring
    exact_mod_cast this

end Podc.KnowYourAudience
