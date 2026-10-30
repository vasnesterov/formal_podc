import Papers.PODC2021.MISTreeLowerBounds.Model

/-!
# Round elimination (forward direction of Theorem 3)

Theorem 3 of the paper (Brandt's round elimination theorem, [13, Theorem 4.3]) says that if `Π`
can be solved in `T ≥ 1` rounds on (high-girth) `Δ`-regular graphs, then `R̄(R(Π))` can be solved
in `T - 1` rounds. We prove this in the model of `Model.lean`: the infinite `Δ`-regular tree with
a `Δ`-edge colouring (port numbers = colours) and an arbitrary edge orientation as input
(`Problem.SolvableIn.Rbar_R`, `Problem.SolvableIn.Rbar_R_sub`).

Since the tree is infinite and the orientation is completely free, no independence assumption is
needed: the views of the two endpoints of an edge, and the views of the branches of a node, can be
glued freely.

## Proof

Let `A` be a `(t+1)`-round algorithm solving `Π`, and look at the root `1` and its edge
`e_c = {1, gen c}` of colour `c`.
1. *Edge step.* Let `K_c` (`edgeBall t c`) be the nodes within distance `t` of `e_c`. The set
   `rawSet` of outputs `A J c` over all inputs `J` agreeing with `I` on `K_c` is the set of labels
   the root might output on `e_c`, knowing only the `t`-neighbourhood of `e_c`. Every label of
   `rawSet I c` is edge-compatible with every label of `rawSet (I.shift (gen c)) c` (the set of
   the other endpoint): the two inputs can be glued along `e_c` (`glue`). Extending the pair to
   a maximal one (`maxPair`), with the orientation of `e_c` breaking the symmetry, gives the
   half-edge labels `halfLabel I c`, which form an edge configuration of `R(Π)` along every edge.
2. *Node step.* The set `nodeSet I c` of the possible `halfLabel J c` over all inputs `J` with
   the same radius-`t` view as `I` depends only on that view. Every choice of one label in each
   `nodeSet I c` is realized by a single input obtained by gluing the branches of the root
   (`branchGlue`), so it is a node configuration of `R(Π)`: `nodeSet I` satisfies the universal
   node condition of `R̄(R(Π))`. Extending it to a maximal configuration (`maxNode`) gives a
   `t`-round algorithm for `R̄(R(Π))`.
-/

-- CSLib candidate (round elimination on the oriented Δ-edge-coloured Δ-regular tree)
namespace Podc.MISTreeLowerBounds

open Cslib.ColourSystem FreeCox

variable {Δ : ℕ} {Λ : Type*}

namespace RoundElim

/-! ### Tree facts -/

theorem orientation_ext {I J : Orientation Δ} (h : ∀ v c, I.dir v c = J.dir v c) : I = J := by
  cases I; cases J; congr; funext v c; exact h v c

theorem shift_gen_shift_gen (I : Orientation Δ) (c : Fin Δ) :
    (I.shift (gen c)).shift (gen c) = I := by
  simp

/-- The nodes within distance `t` of the edge `{1, gen c}`. -/
def edgeBall (t : ℕ) (c : Fin Δ) : Set (FreeCox Δ) := {w | len w ≤ t ∨ len (gen c * w) ≤ t}

theorem one_mem_edgeBall (t : ℕ) (c : Fin Δ) : (1 : FreeCox Δ) ∈ edgeBall t c :=
  Or.inl (by simp)

theorem gen_mem_edgeBall (t : ℕ) (c : Fin Δ) : gen c ∈ edgeBall t c :=
  Or.inr (by simp)

theorem ball_subset_edgeBall (t : ℕ) (c : Fin Δ) : {w : FreeCox Δ | len w ≤ t} ⊆ edgeBall t c :=
  fun _ h => Or.inl h

theorem image_edgeBall (t : ℕ) (c : Fin Δ) : (gen c * ·) '' edgeBall t c = edgeBall t c := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases hv with h | h
    · right; simpa [← mul_assoc] using h
    · left; exact h
  · intro hw
    refine ⟨gen c * w, ?_, by simp [← mul_assoc]⟩
    rcases hw with h | h
    · right; simpa [← mul_assoc] using h
    · left; exact h

theorem agreeOnSet_edgeBall_shift {t : ℕ} {c : Fin Δ} {I J : Orientation Δ}
    (h : AgreeOnSet (edgeBall t c) I J) :
    AgreeOnSet (edgeBall t c) (I.shift (gen c)) (J.shift (gen c)) := by
  rw [agreeOnSet_shift, image_edgeBall]; exact h

/-! ### Gluing two inputs along the edge `{1, gen c}` -/

/-- The orientation that equals `K` on the darts leaving nodes of the branch `c` (the nodes whose
reduced word starts with `c`) and `J` elsewhere; the only edge between the two sides is
`{1, gen c}`, so it suffices that `J` and `K` agree on it. -/
def glue (c : Fin Δ) (J K : Orientation Δ) (h : J.dir 1 c = K.dir 1 c) : Orientation Δ where
  dir v d := if startsWith c v then K.dir v d else J.dir v d
  anti v d := by
    by_cases hv : startsWith c (v * gen d) ↔ startsWith c v
    · by_cases h1 : startsWith c v
      · simp only [hv.2 h1, h1, ite_true, K.anti]
      · simp only [mt hv.1 h1, h1, ite_false, J.anti]
    · obtain ⟨rfl, rfl | rfl⟩ := startsWith_mul_gen (c := c) (c' := d) (x := v) (by tauto)
      · have := K.anti 1 d
        simp_all
      · have h2 := J.anti (gen d) d
        have h3 := K.anti 1 d
        simp_all

theorem len_gen_mul_ne (c : Fin Δ) (v : FreeCox Δ) : len (gen c * v) ≠ len v := by
  have h := len_mul_gen_ne v⁻¹ c
  rw [← len_inv (gen c * v), mul_inv_rev, inv_gen]
  simpa using h

/-- Left multiplication by `gen c` swaps the branch `c` and its complement. -/
theorem startsWith_gen_mul_iff (c : Fin Δ) (v : FreeCox Δ) :
    startsWith c (gen c * v) ↔ ¬ startsWith c v := by
  unfold startsWith
  rw [← mul_assoc, gen_mul_gen, one_mul]
  have := len_gen_mul_ne c v
  omega

/-- If `J` and `K` agree on the nodes within distance `t` of `{1, gen c}`, then the glued input
has the same radius-`(t+1)` view at the root as `J`. -/
theorem glue_agree {t : ℕ} {c : Fin Δ} {J K : Orientation Δ} (h : J.dir 1 c = K.dir 1 c)
    (hJK : AgreeOnSet (edgeBall t c) J K) : AgreeOn (t + 1) (glue c J K h) J := by
  intro v d (hv : len v ≤ t + 1) (hvd : len (v * gen d) ≤ t + 1)
  show (if startsWith c v then K.dir v d else J.dir v d) = J.dir v d
  split_ifs with h1
  · refine (hJK v d (Or.inr (by unfold startsWith at h1; omega)) ?_).symm
    by_cases h2 : startsWith c (v * gen d)
    · exact Or.inr (by unfold startsWith at h2; omega)
    · obtain ⟨rfl, rfl | rfl⟩ := startsWith_mul_gen (c := c) (c' := d) (x := v) (by tauto)
      · simp at h1
      · exact Or.inl (by simp)
  · rfl

theorem glue_shift_aux {c : Fin Δ} {J K : Orientation Δ} (h : J.dir 1 c = K.dir 1 c) :
    (K.shift (gen c)).dir 1 c = (J.shift (gen c)).dir 1 c := by
  have h1 := J.anti 1 c
  have h2 := K.anti 1 c
  simp only [one_mul] at h1 h2
  simp [h1, h2, h]

/-- Seen from `gen c`, the glued input is the glued input with the roles of `J`, `K` swapped. -/
theorem glue_shift {c : Fin Δ} {J K : Orientation Δ} (h : J.dir 1 c = K.dir 1 c) :
    (glue c J K h).shift (gen c) =
      glue c (K.shift (gen c)) (J.shift (gen c)) (glue_shift_aux h) := by
  refine orientation_ext fun v d => ?_
  show (if startsWith c (gen c * v) then K.dir (gen c * v) d else J.dir (gen c * v) d) =
    (if startsWith c v then J.dir (gen c * v) d else K.dir (gen c * v) d)
  by_cases hs : startsWith c v <;> simp [startsWith_gen_mul_iff, hs]

theorem glue_shift_agree {t : ℕ} {c : Fin Δ} {J K : Orientation Δ} (h : J.dir 1 c = K.dir 1 c)
    (hJK : AgreeOnSet (edgeBall t c) J K) :
    AgreeOn (t + 1) ((glue c J K h).shift (gen c)) (K.shift (gen c)) := by
  rw [glue_shift]
  exact glue_agree _ (agreeOnSet_edgeBall_shift hJK).symm

/-! ### Gluing inputs branch by branch at the root -/

/-- The branch of the dart `(v, d)`: the first letter of `v`, or `d` for the darts of the root. -/
def branch (v : FreeCox Δ) (d : Fin Δ) : Fin Δ := v.1.getLast?.getD d

theorem branch_eq_of_startsWith {c d : Fin Δ} {v : FreeCox Δ} (h : startsWith c v) :
    branch v d = c := by
  rw [startsWith_iff] at h
  simp [branch, h]

/-- Both darts of an edge lie in the same branch. -/
theorem branch_mul_gen (v : FreeCox Δ) (d : Fin Δ) : branch (v * gen d) d = branch v d := by
  by_cases h : ∀ b, startsWith b (v * gen d) ↔ startsWith b v
  · have : (v * gen d).1.getLast? = v.1.getLast? :=
      Option.ext fun b => by simpa [startsWith_iff] using h b
    simp [branch, this]
  · obtain ⟨b, hb⟩ := not_forall.1 h
    obtain ⟨rfl, rfl | rfl⟩ := startsWith_mul_gen (c := b) (c' := d) (x := v) (by tauto)
    · simp [branch]
    · simp [branch]

/-- The input equal to `J b` on (the darts of) branch `b`, for every `b`. -/
def branchGlue (J : Fin Δ → Orientation Δ) : Orientation Δ where
  dir v d := (J (branch v d)).dir v d
  anti v d := by rw [branch_mul_gen]; exact (J _).anti v d

/-- If all `J b` have the same radius-`t` view as `I`, then the branch-glued input agrees with
`J c` within distance `t` of the edge `{1, gen c}`. -/
theorem branchGlue_agree {t : ℕ} {I : Orientation Δ} {J : Fin Δ → Orientation Δ}
    (hJ : ∀ b, AgreeOn t (J b) I) (c : Fin Δ) :
    AgreeOnSet (edgeBall t c) (branchGlue J) (J c) := by
  intro v d hv hvd
  show (J (branch v d)).dir v d = (J c).dir v d
  by_cases hb : branch v d = c
  · rw [hb]
  · have key : ∀ w, branch w d = branch v d → w ∈ edgeBall t c → len w ≤ t := by
      intro w hw hwK
      have : ¬ startsWith c w := fun hs => hb (hw ▸ branch_eq_of_startsWith hs)
      unfold startsWith at this
      rcases hwK with h | h <;> omega
    have h1 := key v rfl hv
    have h2 := key (v * gen d) (branch_mul_gen v d) hvd
    rw [hJ (branch v d) v d h1 h2, hJ c v d h1 h2]

/-! ### The edge step -/

variable [Finite Λ] {P : Problem Δ Λ} {A : Orientation Δ → Fin Δ → Λ} {t : ℕ}

/-- The labels the root might output on its edge of colour `c` given the input on the nodes within
distance `t` of that edge. -/
noncomputable def rawSet (A : Orientation Δ → Fin Δ → Λ) (t : ℕ) (I : Orientation Δ)
    (c : Fin Δ) : Finset Λ :=
  (Set.toFinite {a | ∃ J, AgreeOnSet (edgeBall t c) J I ∧ A J c = a}).toFinset

theorem mem_rawSet {I : Orientation Δ} {c : Fin Δ} {a : Λ} :
    a ∈ rawSet A t I c ↔ ∃ J, AgreeOnSet (edgeBall t c) J I ∧ A J c = a := by
  rw [rawSet, Set.Finite.mem_toFinset]; rfl

theorem self_mem_rawSet (I : Orientation Δ) (c : Fin Δ) : A I c ∈ rawSet A t I c :=
  mem_rawSet.2 ⟨I, fun _ _ _ _ => rfl, rfl⟩

theorem rawSet_congr {I I' : Orientation Δ} {c : Fin Δ} (h : AgreeOnSet (edgeBall t c) I I') :
    rawSet A t I c = rawSet A t I' c := by
  ext a
  simp only [mem_rawSet]
  constructor <;> rintro ⟨J, hJ, rfl⟩
  exacts [⟨J, hJ.trans h, rfl⟩, ⟨J, hJ.trans h.symm, rfl⟩]

/-- Every label the root might output on `{1, gen c}` is compatible with every label the other
endpoint might output on it (gluing argument). -/
theorem edgeAll_rawSet (hA : IsLocal (t + 1) A) (hS : P.Solves A) (I : Orientation Δ)
    (c : Fin Δ) : P.EdgeAll (rawSet A t I c) (rawSet A t (I.shift (gen c)) c) := by
  refine ⟨⟨_, self_mem_rawSet I c⟩, ⟨_, self_mem_rawSet _ c⟩, ?_⟩
  intro a ha a' ha'
  obtain ⟨J, hJ, rfl⟩ := mem_rawSet.1 ha
  obtain ⟨J', hJ', rfl⟩ := mem_rawSet.1 ha'
  have hJ'' : AgreeOnSet (edgeBall t c) (J'.shift (gen c)) I := by
    have := agreeOnSet_edgeBall_shift hJ'; rwa [shift_gen_shift_gen] at this
  have hJJ : AgreeOnSet (edgeBall t c) J (J'.shift (gen c)) := hJ.trans hJ''.symm
  have h1 : J.dir 1 c = (J'.shift (gen c)).dir 1 c :=
    hJJ 1 c (one_mem_edgeBall t c) (by rw [one_mul]; exact gen_mem_edgeBall t c)
  have e1 : A (glue c J _ h1) c = A J c := by rw [hA _ J (glue_agree h1 hJJ)]
  have e2 : A ((glue c J _ h1).shift (gen c)) c = A J' c := by
    have := glue_shift_agree h1 hJJ
    rw [shift_gen_shift_gen] at this
    rw [hA _ _ this]
  have := ((solves_iff.1 hS) (glue c J _ h1)).2 c
  rwa [e1, e2] at this

open Classical in
/-- A fixed maximal extension of a pair `(U, W)` (meaningful when `P.EdgeAll U W`). -/
noncomputable def maxPair (P : Problem Δ Λ) (U W : Finset Λ) : Finset Λ × Finset Λ :=
  if h : ∃ p : Finset Λ × Finset Λ, U ⊆ p.1 ∧ W ⊆ p.2 ∧ P.edgeMax p.1 p.2 then h.choose
  else (U, W)

theorem maxPair_spec {U W : Finset Λ} (h : P.EdgeAll U W) :
    U ⊆ (maxPair P U W).1 ∧ W ⊆ (maxPair P U W).2 ∧
      P.edgeMax (maxPair P U W).1 (maxPair P U W).2 := by
  have hex : ∃ p : Finset Λ × Finset Λ, U ⊆ p.1 ∧ W ⊆ p.2 ∧ P.edgeMax p.1 p.2 := by
    obtain ⟨A', B', h1, h2, h3⟩ := h.exists_edgeMax
    exact ⟨(A', B'), h1, h2, h3⟩
  unfold maxPair
  split_ifs
  exact hex.choose_spec

/-- The `R(Π)` half-edge label of the root on its edge of colour `c`: the pair of possible label
sets of the two endpoints, extended to a maximal pair; the orientation of the edge decides which
endpoint takes which component, so both endpoints use the same maximal pair. It depends only on
the input within distance `t` of the edge. -/
noncomputable def halfLabel (P : Problem Δ Λ) (A : Orientation Δ → Fin Δ → Λ) (t : ℕ)
    (I : Orientation Δ) (c : Fin Δ) : Finset Λ :=
  if I.dir 1 c then (maxPair P (rawSet A t I c) (rawSet A t (I.shift (gen c)) c)).1
  else (maxPair P (rawSet A t (I.shift (gen c)) c) (rawSet A t I c)).2

theorem halfLabel_congr {I I' : Orientation Δ} {c : Fin Δ} (h : AgreeOnSet (edgeBall t c) I I') :
    halfLabel P A t I c = halfLabel P A t I' c := by
  have h1 : I.dir 1 c = I'.dir 1 c :=
    h 1 c (one_mem_edgeBall t c) (by rw [one_mul]; exact gen_mem_edgeBall t c)
  rw [halfLabel, halfLabel, h1, rawSet_congr h, rawSet_congr (agreeOnSet_edgeBall_shift h)]

theorem dir_shift_gen (I : Orientation Δ) (c : Fin Δ) :
    (I.shift (gen c)).dir 1 c = !I.dir 1 c := by
  have := I.anti 1 c
  simpa using this

theorem subset_halfLabel (hA : IsLocal (t + 1) A) (hS : P.Solves A) (I : Orientation Δ)
    (c : Fin Δ) : rawSet A t I c ⊆ halfLabel P A t I c := by
  have h2 := edgeAll_rawSet hA hS (I.shift (gen c)) c
  rw [shift_gen_shift_gen] at h2
  cases h : I.dir 1 c
  · simpa [halfLabel, h] using (maxPair_spec h2).2.1
  · simpa [halfLabel, h] using (maxPair_spec (edgeAll_rawSet hA hS I c)).1

theorem self_mem_halfLabel (hA : IsLocal (t + 1) A) (hS : P.Solves A) (I : Orientation Δ)
    (c : Fin Δ) : A I c ∈ halfLabel P A t I c :=
  subset_halfLabel hA hS I c (self_mem_rawSet I c)

/-- The half-edge labels of the two endpoints of every edge form an edge configuration of
`R(Π)`. -/
theorem edgeMax_halfLabel (hA : IsLocal (t + 1) A) (hS : P.Solves A) (I : Orientation Δ)
    (c : Fin Δ) : P.edgeMax (halfLabel P A t I c) (halfLabel P A t (I.shift (gen c)) c) := by
  have h1 := edgeAll_rawSet hA hS I c
  have h2 := edgeAll_rawSet hA hS (I.shift (gen c)) c
  rw [shift_gen_shift_gen] at h2
  have hd := dir_shift_gen I c
  cases h : I.dir 1 c
  · rw [h] at hd
    simp only [halfLabel, h, hd, shift_gen_shift_gen, Bool.false_eq_true, ite_false]
    exact (maxPair_spec h2).2.2.symm
  · rw [h] at hd
    simp only [halfLabel, h, hd, shift_gen_shift_gen, ite_true]
    exact (maxPair_spec h1).2.2

theorem halfLabel_mem_alphR (hA : IsLocal (t + 1) A) (hS : P.Solves A) (I : Orientation Δ)
    (c : Fin Δ) : halfLabel P A t I c ∈ P.alphR :=
  ⟨_, edgeMax_halfLabel hA hS I c⟩

/-! ### The node step -/

/-- The `R(Π)` labels the root might output on its edge of colour `c`, given its radius-`t`
view. -/
noncomputable def nodeSet (P : Problem Δ Λ) (A : Orientation Δ → Fin Δ → Λ) (t : ℕ)
    (I : Orientation Δ) (c : Fin Δ) : Finset (Finset Λ) :=
  (Set.toFinite {S | ∃ J, AgreeOn t J I ∧ halfLabel P A t J c = S}).toFinset

theorem mem_nodeSet {I : Orientation Δ} {c : Fin Δ} {S : Finset Λ} :
    S ∈ nodeSet P A t I c ↔ ∃ J, AgreeOn t J I ∧ halfLabel P A t J c = S := by
  rw [nodeSet, Set.Finite.mem_toFinset]; rfl

theorem self_mem_nodeSet (I : Orientation Δ) (c : Fin Δ) :
    halfLabel P A t I c ∈ nodeSet P A t I c :=
  mem_nodeSet.2 ⟨I, fun _ _ _ _ => rfl, rfl⟩

theorem nodeSet_congr {I I' : Orientation Δ} (h : AgreeOn t I I') :
    nodeSet P A t I = nodeSet P A t I' := by
  funext c
  ext S
  simp only [mem_nodeSet]
  constructor <;> rintro ⟨J, hJ, rfl⟩
  exacts [⟨J, AgreeOnSet.trans hJ h, rfl⟩, ⟨J, AgreeOnSet.trans hJ h.symm, rfl⟩]

/-- Every choice of one label of each `nodeSet I c` is a node configuration of `R(Π)` (gluing the
branches of the root). -/
theorem nodeAll_nodeSet (hA : IsLocal (t + 1) A) (hS : P.Solves A) (I : Orientation Δ) :
    P.R.NodeAll (nodeSet P A t I) := by
  refine ⟨fun c => ⟨_, self_mem_nodeSet I c⟩, fun y hy => ?_⟩
  choose J hJ hJy using fun c => mem_nodeSet.1 (hy c)
  have hL : ∀ c, halfLabel P A t (branchGlue J) c = y c :=
    fun c => (halfLabel_congr (branchGlue_agree hJ c)).trans (hJy c)
  refine ⟨fun c => hL c ▸ halfLabel_mem_alphR hA hS _ c, A (branchGlue J),
    fun c => hL c ▸ self_mem_halfLabel hA hS _ c, ((solves_iff.1 hS) (branchGlue J)).1⟩

open Classical in
/-- A fixed maximal extension of a node configuration (meaningful when `Q.NodeAll Y`). -/
noncomputable def maxNode {Λ' : Type*} (Q : Problem Δ Λ') (Y : Fin Δ → Finset Λ') :
    Fin Δ → Finset Λ' :=
  if h : ∃ Y', (∀ i, Y i ⊆ Y' i) ∧ Q.nodeMax Y' then h.choose else Y

theorem maxNode_spec {Λ' : Type*} [Finite Λ'] {Q : Problem Δ Λ'} {Y : Fin Δ → Finset Λ'}
    (h : Q.NodeAll Y) : (∀ i, Y i ⊆ maxNode Q Y i) ∧ Q.nodeMax (maxNode Q Y) := by
  have hex := h.exists_nodeMax
  unfold maxNode
  split_ifs
  exact hex.choose_spec

end RoundElim

open RoundElim

/-- **Round elimination**, forward direction of Theorem 3 of the paper ([13, Theorem 4.3]): if `Π`
can be solved in `t + 1` rounds, then `R̄(R(Π))` can be solved in `t` rounds (deterministic PN
model on the `Δ`-edge-coloured `Δ`-regular tree with an edge orientation as input). -/
theorem Problem.SolvableIn.Rbar_R [Finite Λ] {P : Problem Δ Λ} {t : ℕ} (h : P.SolvableIn (t + 1)) :
    P.R.Rbar.SolvableIn t := by
  obtain ⟨A, hA, hS⟩ := h
  refine ⟨fun I => maxNode P.R (nodeSet P A t I), fun I J hIJ => by simp only [nodeSet_congr hIJ],
    solves_iff.2 fun I => ?_⟩
  have hm := maxNode_spec (nodeAll_nodeSet hA hS I)
  refine ⟨hm.2, fun c => ?_⟩
  have hm' := maxNode_spec (nodeAll_nodeSet hA hS (I.shift (gen c)))
  exact ⟨⟨_, hm.2, c, rfl⟩, ⟨_, hm'.2, c, rfl⟩, _, hm.1 c (self_mem_nodeSet I c), _,
    hm'.1 c (self_mem_nodeSet _ c), edgeMax_halfLabel hA hS I c⟩

/-- Theorem 3 of the paper, as stated there: a `T`-round algorithm for `Π` (`T ≥ 1`) gives a
`(T - 1)`-round algorithm for `R̄(R(Π))`. (For `T = 0` the statement holds trivially as well.) -/
theorem Problem.SolvableIn.Rbar_R_sub [Finite Λ] {P : Problem Δ Λ} {t : ℕ} (h : P.SolvableIn t) :
    P.R.Rbar.SolvableIn (t - 1) :=
  (h.mono (Nat.le_succ_of_pred_le le_rfl)).Rbar_R

end Podc.MISTreeLowerBounds
