import Papers.PODC2015.CrashConsensusDigraph.Necessity

/-!
# Fixed iterative algorithms in anonymous networks: Theorem 5

Section 3 and Appendix B. An *iterative algorithm* keeps one value per node; in iteration `t`
every node sends its value on all outgoing edges and applies a transition function to the
collection `Rᵢ[t]` of its own value and the values received. It is *fixed* (Definition 5) if
every node uses the same transition function `Z*` in every iteration. In an anonymous network
`Z*` can only depend on the *multiset* of values (the paper counts 0's and 1's). We study binary
consensus, so `Z : Multiset Bool → Bool`.

* `iterState G Z adv inp t u` — the value of `u` after `t` iterations under the crash pattern
  `adv` (same crash model as `SyncModel.lean`).
* The paper never says when an iterative algorithm *outputs*. Its proof of Theorem 5 shows
  executions where two fault-free nodes disagree *forever*, and argues that `Z` must map
  all-0 / all-1 collections to 0 / 1 "otherwise either validity or agreement is violated". This
  is sound for the **eventual** reading (`SolvesEventually`: from some iteration on, the values
  of fault-free nodes agree and are inputs), for which we prove **Theorem 5** (`theorem5`) with the
  paper's graph (`pGraph f`: a source `s`, a clique of `f + 1` nodes, a leaf `l`), for every `f`
  (the paper's argument crashes a clique node, so it does not apply to `f = 0` as written; there
  the graph is the path `s → c → l` and the same case analysis works without crashes).
* For the **fixed-iteration** reading (`SolvesAt … T`: the output is the value after iteration
  `T`, as for Algorithm Min-Max), the paper's counterexample is not one: see
  `IterativeCounterexample.lean`.
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus

variable {V : Type*} [DecidableEq V] [Fintype V]

open Classical in
/-- The in-neighbours whose iteration-`t` message reaches `w`. -/
noncomputable def recvSet (G : Digraph V) (adv : Adversary V) (t : ℕ) (w : V) : Finset V :=
  univ.filter fun u => u ≠ w ∧ Delivers G adv t u w

/-- Values of a fixed iterative algorithm with transition function `Z` (Definition 5): the new
value of `w` is `Z` applied to the multiset of its own value and the values received. -/
noncomputable def iterState (G : Digraph V) (Z : Multiset Bool → Bool) (adv : Adversary V)
    (inp : V → Bool) : ℕ → V → Bool
  | 0, u => inp u
  | t + 1, w => Z (iterState G Z adv inp t w ::ₘ (recvSet G adv t w).val.map (iterState G Z adv inp t))

/-- Fixed iterative binary consensus, **eventual** reading: from some iteration on, the values
of the fault-free nodes agree and are inputs. -/
def SolvesEventually (G : Digraph V) (f : ℕ) (Z : Multiset Bool → Bool) : Prop :=
  ∀ adv : Adversary V, adv.Admissible f → ∀ inp : V → Bool, ∃ T₀, ∀ T ≥ T₀, ∀ u w,
    adv.crash u = none → adv.crash w = none →
      iterState G Z adv inp T u = iterState G Z adv inp T w ∧ ∃ v, inp v = iterState G Z adv inp T u

/-- Fixed iterative binary consensus, **fixed-iteration** reading: the output is the value after
iteration `T`. -/
def SolvesAt (G : Digraph V) (f : ℕ) (Z : Multiset Bool → Bool) (T : ℕ) : Prop :=
  ∀ adv : Adversary V, adv.Admissible f → ∀ inp : V → Bool, ∀ u w,
    adv.crash u = none → adv.crash w = none →
      iterState G Z adv inp T u = iterState G Z adv inp T w ∧ ∃ v, inp v = iterState G Z adv inp T u

/-! ## The graph of Appendix B -/

/-- Nodes of the graph of Appendix B: the source `s`, clique nodes `cl i` (`i ≤ f`), the leaf. -/
inductive PNode (f : ℕ) where
  | src
  | cl (i : Fin (f + 1))
  | leaf
  deriving DecidableEq, Fintype

namespace PNode

variable {f : ℕ}

/-- The edges: `s → cl i`, `cl i → cl j` (`i ≠ j`), `cl i → l`. -/
def Adj : PNode f → PNode f → Prop
  | src, cl _ => True
  | cl i, cl j => i ≠ j
  | cl _, leaf => True
  | _, _ => False

end PNode

/-- The graph of Appendix B. -/
def pGraph (f : ℕ) : Digraph (PNode f) where
  Adj := PNode.Adj

open PNode

theorem pGraph_adj_src {f : ℕ} (i : Fin (f + 1)) : (pGraph f).Adj src (cl i) := trivial
theorem pGraph_adj_cl {f : ℕ} {i j : Fin (f + 1)} (h : i ≠ j) : (pGraph f).Adj (cl i) (cl j) := h
theorem pGraph_adj_leaf {f : ℕ} (i : Fin (f + 1)) : (pGraph f).Adj (cl i) leaf := trivial

theorem exists_cl_notMem {f : ℕ} {F : Finset (PNode f)} (hF : F.card ≤ f) : ∃ i, cl i ∉ F := by
  by_contra h
  push Not at h
  have := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin (f + 1)))) cl
    (fun i _ => h i) (fun i _ j _ hij => PNode.cl.inj hij)
  simp at this
  omega

/-- The graph of Appendix B satisfies `f` CT node connectivity. -/
theorem pGraph_ctConn (f : ℕ) : CTConn (pGraph f) f := by
  intro F hF _
  obtain ⟨c, hc⟩ := exists_cl_notMem hF
  by_cases hs : src ∈ F
  · refine ⟨cl c, hc, fun v hv => ?_⟩
    cases v with
    | src => exact absurd hs hv
    | cl j =>
      by_cases hj : j = c
      · subst hj; exact Reaches.refl hc
      · exact (Reaches.refl hc).tail (pGraph_adj_cl (Ne.symm hj)) hv
    | leaf => exact (Reaches.refl hc).tail (pGraph_adj_leaf c) hv
  · refine ⟨src, hs, fun v hv => ?_⟩
    cases v with
    | src => exact Reaches.refl hs
    | cl j => exact (Reaches.refl hs).tail (pGraph_adj_src j) hv
    | leaf => exact ((Reaches.refl hs).tail (pGraph_adj_src c) hc).tail (pGraph_adj_leaf c) hv

/-! ## The executions of Appendix B -/

section Exec

variable {f : ℕ}

/-- In the executions of the proof, one clique node (`cl 0`) crashes before the start when
`f ≥ 1`; nobody crashes when `f = 0`. -/
def crashSet (f : ℕ) : Finset (PNode f) := if 1 ≤ f then {cl 0} else ∅

theorem crashSet_card (f : ℕ) : (crashSet f).card ≤ f := by
  unfold crashSet; split_ifs <;> simp_all

/-- The clique nodes that do not crash. -/
def CC (f : ℕ) (i : Fin (f + 1)) : Prop := ¬ (1 ≤ f ∧ i = 0)

instance (f : ℕ) (i : Fin (f + 1)) : Decidable (CC f i) := by unfold CC; infer_instance

theorem cl_mem_crashSet {i : Fin (f + 1)} : cl i ∈ crashSet f ↔ ¬ CC f i := by
  unfold crashSet CC; split_ifs with h <;> simp [h]

theorem src_notMem_crashSet : (src : PNode f) ∉ crashSet f := by
  unfold crashSet; split_ifs <;> simp

theorem leaf_notMem_crashSet : (leaf : PNode f) ∉ crashSet f := by
  unfold crashSet; split_ifs <;> simp

/-- The observed fault-free clique node. -/
def cStar (f : ℕ) : Fin (f + 1) := Fin.last f

theorem cc_cStar : CC f (cStar f) := by
  unfold CC cStar
  rintro ⟨h1, h2⟩
  have := congrArg Fin.val h2
  simp at this
  omega

abbrev advB (f : ℕ) : Adversary (PNode f) := crashAtStart (crashSet f)

theorem delivers_advB {t : ℕ} {u w : PNode f} :
    Delivers (pGraph f) (advB f) t u w ↔ (pGraph f).Adj u w ∧ u ∉ crashSet f := by
  constructor
  · intro h; exact ⟨h.adj, notMem_of_delivers_crashAtStart h⟩
  · rintro ⟨e, hu⟩
    exact ⟨e, fun c hc => by simp [crashAtStart, hu] at hc⟩

theorem recvSet_src (t : ℕ) : recvSet (pGraph f) (advB f) t src = ∅ := by
  ext u
  simp only [recvSet, mem_filter, mem_univ, true_and, delivers_advB, notMem_empty, iff_false]
  rintro ⟨-, e, -⟩
  cases u <;> exact e

/-- The fault-free clique nodes other than `i`. -/
def others (f : ℕ) (i : Fin (f + 1)) : Finset (Fin (f + 1)) := univ.filter fun j => j ≠ i ∧ CC f j

/-- `cl` as an embedding. -/
def clEmb : Fin (f + 1) ↪ PNode f := ⟨cl, fun _ _ h => cl.inj h⟩

@[simp] theorem clEmb_apply (i : Fin (f + 1)) : clEmb i = cl i := rfl

theorem pGraph_adj {u w : PNode f} : (pGraph f).Adj u w ↔ PNode.Adj u w := Iff.rfl

theorem recvSet_cl (t : ℕ) (i : Fin (f + 1)) :
    recvSet (pGraph f) (advB f) t (cl i) = insert src ((others f i).map clEmb) := by
  ext u
  simp only [recvSet, mem_filter, mem_univ, true_and, delivers_advB, pGraph_adj]
  cases u with
  | src => simp [PNode.Adj, src_notMem_crashSet]
  | cl j =>
    simp only [PNode.Adj, others, cl_mem_crashSet, not_not, mem_insert, reduceCtorEq, false_or,
      mem_map, mem_filter, mem_univ, true_and, clEmb_apply, cl.injEq, exists_eq_right, ne_eq]
    constructor
    · rintro ⟨-, e, hc⟩; exact ⟨e, hc⟩
    · rintro ⟨e, hc⟩; exact ⟨fun h => e h, e, hc⟩
  | leaf => simp [PNode.Adj]

theorem recvSet_leaf (t : ℕ) :
    recvSet (pGraph f) (advB f) t leaf = (univ.filter (CC f)).map clEmb := by
  ext u
  simp only [recvSet, mem_filter, mem_univ, true_and, delivers_advB, pGraph_adj]
  cases u with
  | src => simp [PNode.Adj]
  | cl j => simp [PNode.Adj, cl_mem_crashSet]
  | leaf => simp [PNode.Adj]

theorem card_others {i : Fin (f + 1)} (hi : CC f i) : (others f i).card = f - 1 := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · have : others 0 i = ∅ := by
      ext j; simp only [others, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
      intro h; exact absurd (Fin.ext (by have := j.isLt; have := i.isLt; omega)) h
    simp [this]
  · have hi0 : i ≠ 0 := fun h => hi ⟨hf, h⟩
    have : others f i = (univ.erase i).erase 0 := by
      ext j
      simp only [others, mem_filter, mem_univ, true_and, mem_erase, and_true]
      unfold CC
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 ⟨hf, h⟩, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 h.2⟩
    rw [this, card_erase_of_mem (by simp [Ne.symm hi0]), card_erase_of_mem (mem_univ _)]
    simp

theorem card_cc (hf : 1 ≤ f) : (univ.filter (CC f)).card = f := by
  have : univ.filter (CC f) = univ.erase 0 := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]; unfold CC
    exact ⟨fun h h0 => h ⟨hf, h0⟩, fun h h' => h h'.2⟩
  rw [this, card_erase_of_mem (mem_univ _)]
  simp

variable {Z : Multiset Bool → Bool} {inp : PNode f → Bool}

local notation "x" => iterState (pGraph f) Z (advB f) inp

theorem iter_src (t : ℕ) : x (t + 1) src = Z {x t src} := by
  show Z (_ ::ₘ _) = _
  rw [recvSet_src]; rfl

/-- One iteration at a fault-free clique node, when the source holds `a` and all fault-free
clique nodes hold `b`. -/
theorem iter_cl {t : ℕ} {a b : Bool} (ha : x t src = a) (hb : ∀ j, CC f j → x t (cl j) = b)
    {i : Fin (f + 1)} (hi : CC f i) : x (t + 1) (cl i) = Z (b ::ₘ a ::ₘ Multiset.replicate (f - 1) b) := by
  show Z (_ ::ₘ _) = _
  rw [recvSet_cl, hb i hi, insert_val_of_notMem (by simp), Multiset.map_cons, ha, map_val,
    Multiset.map_map]
  congr 3
  apply Multiset.eq_replicate.mpr
  refine ⟨by simp [card_others hi], fun y hy => ?_⟩
  obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hy
  exact hb j (mem_filter.mp (Finset.mem_val.mp hj)).2.2

/-- One iteration at the leaf (`f ≥ 1`), when all fault-free clique nodes hold `b`. -/
theorem iter_leaf (hf : 1 ≤ f) {t : ℕ} {b : Bool} (hb : ∀ j, CC f j → x t (cl j) = b) :
    x (t + 1) leaf = Z (x t leaf ::ₘ Multiset.replicate f b) := by
  show Z (_ ::ₘ _) = _
  rw [recvSet_leaf, map_val, Multiset.map_map]
  congr 2
  apply Multiset.eq_replicate.mpr
  refine ⟨by rw [Multiset.card_map, Finset.card_val]; exact card_cc hf, fun y hy => ?_⟩
  obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.mp hy
  exact hb j (mem_filter.mp (Finset.mem_val.mp hj)).2

/-- If the source holds `a` and the fault-free clique nodes hold `b`, and these are fixed points
of the respective updates, they keep these values forever. -/
theorem iter_const {a b : Bool} (ha0 : inp src = a) (hb0 : ∀ j, inp (cl j) = b)
    (hZa : Z {a} = a) (hZb : Z (b ::ₘ a ::ₘ Multiset.replicate (f - 1) b) = b) :
    ∀ t, x t src = a ∧ ∀ j, CC f j → x t (cl j) = b := by
  intro t
  induction t with
  | zero => exact ⟨ha0, fun j _ => hb0 j⟩
  | succ t ih =>
    refine ⟨by rw [iter_src, ih.1, hZa], fun j hj => ?_⟩
    rw [iter_cl ih.1 ih.2 hj, hZb]

theorem advB_admissible : (advB f).Admissible f := crashAtStart_admissible (crashSet_card f)

theorem advB_src_correct : (advB f).crash src = none := crashAtStart_correct src_notMem_crashSet

theorem advB_cl_correct {i : Fin (f + 1)} (hi : CC f i) : (advB f).crash (cl i) = none :=
  crashAtStart_correct (by rw [cl_mem_crashSet]; exact not_not.mpr hi)

theorem advB_leaf_correct : (advB f).crash leaf = none := crashAtStart_correct leaf_notMem_crashSet

end Exec

/-- **Theorem 5** (Appendix B), eventual reading: for every `f`, the graph of Appendix B
satisfies `f` CT node connectivity, but no fixed iterative algorithm (in an anonymous network)
solves binary crash consensus on it. -/
theorem theorem5 (f : ℕ) :
    CTConn (pGraph f) f ∧ ∀ Z : Multiset Bool → Bool, ¬ SolvesEventually (pGraph f) f Z := by
  refine ⟨pGraph_ctConn f, fun Z hZ => ?_⟩
  -- a fault-free node holding a value different from another one forever contradicts agreement
  have contra : ∀ (inp : PNode f → Bool) (u w : PNode f), (advB f).crash u = none →
      (advB f).crash w = none → (∀ t, iterState (pGraph f) Z (advB f) inp t u ≠
        iterState (pGraph f) Z (advB f) inp t w) → False := by
    intro inp u w hu hw hne
    obtain ⟨T₀, hT⟩ := hZ (advB f) advB_admissible inp
    exact hne T₀ (hT T₀ le_rfl u w hu hw).1
  -- validity: with constant inputs `a`, fault-free nodes eventually hold `a`
  have valid : ∀ (a : Bool) (u : PNode f), (advB f).crash u = none →
      ∃ T₀, ∀ T ≥ T₀, iterState (pGraph f) Z (advB f) (fun _ => a) T u = a := by
    intro a u hu
    obtain ⟨T₀, hT⟩ := hZ (advB f) advB_admissible (fun _ => a)
    refine ⟨T₀, fun T hT' => ?_⟩
    obtain ⟨-, v, hv⟩ := hT T hT' u u hu hu
    exact hv.symm
  -- forced values: `Z {a} = a`
  have hZs : ∀ a, Z {a} = a := by
    intro a
    obtain ⟨T₀, hT⟩ := valid a src advB_src_correct
    have h1 := hT (T₀ + 1) (by omega)
    rw [iter_src, hT T₀ le_rfl] at h1
    exact h1
  -- forced values: `Z (a ::ₘ a ::ₘ a^(f - 1)) = a`
  have hZc : ∀ a, Z (a ::ₘ a ::ₘ Multiset.replicate (f - 1) a) = a := by
    intro a
    obtain ⟨T₀, hT⟩ := valid a (cl (cStar f)) (advB_cl_correct cc_cStar)
    have hsrc : ∀ t, iterState (pGraph f) Z (advB f) (fun _ => a) t src = a := by
      intro t; induction t with
      | zero => rfl
      | succ t ih' => rw [iter_src, ih', hZs]
    -- all fault-free clique nodes hold the same value at every time
    have hsym : ∀ t, ∃ y, ∀ j, CC f j → iterState (pGraph f) Z (advB f) (fun _ => a) t (cl j) = y := by
      intro t
      induction t with
      | zero => exact ⟨a, fun _ _ => rfl⟩
      | succ t ih =>
        obtain ⟨y, hy⟩ := ih
        exact ⟨_, fun j hj => iter_cl (hsrc t) hy hj⟩
    obtain ⟨y, hy⟩ := hsym T₀
    have hya : y = a := (hy _ cc_cStar).symm.trans (hT T₀ le_rfl)
    have := iter_cl (hsrc T₀) hy (cc_cStar (f := f))
    rw [hT (T₀ + 1) (by omega), hya] at this
    exact this.symm
  -- the three cases of Appendix B
  by_cases h1 : Z (false ::ₘ true ::ₘ Multiset.replicate (f - 1) false) = false
  · -- `Z(R) = 0`: source `1`, everybody else `0`
    set inp : PNode f → Bool := fun v => match v with | src => true | _ => false
    have hc := iter_const (inp := inp) (Z := Z) (a := true) (b := false) rfl (fun _ => rfl)
      (hZs true) h1
    exact contra inp src (cl (cStar f)) advB_src_correct (advB_cl_correct cc_cStar) fun t => by
      rw [(hc t).1, (hc t).2 _ cc_cStar]; simp
  by_cases h2 : Z (true ::ₘ false ::ₘ Multiset.replicate (f - 1) true) = false
  · -- `Z(R) = 1`, `Z(R') = 0`: leaf `0`, everybody else `1` (needs `f ≥ 1`)
    have hf : 1 ≤ f := by
      by_contra hf
      obtain rfl : f = 0 := by omega
      simp only [zero_tsub, Multiset.replicate_zero] at h1 h2
      rw [Multiset.cons_swap] at h2
      exact h1 h2
    set inp : PNode f → Bool := fun v => match v with | leaf => false | _ => true
    have hc := iter_const (inp := inp) (Z := Z) (a := true) (b := true) rfl (fun _ => rfl)
      (hZs true) (hZc true)
    have hR' : false ::ₘ Multiset.replicate f true =
        true ::ₘ false ::ₘ Multiset.replicate (f - 1) true := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [Multiset.cons_swap, Multiset.replicate_succ]; simp
    have hleaf : ∀ t, iterState (pGraph f) Z (advB f) inp t leaf = false := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih => rw [iter_leaf hf (hc t).2, ih, hR', h2]
    exact contra inp src leaf advB_src_correct advB_leaf_correct fun t => by
      rw [(hc t).1, hleaf t]; simp
  · -- `Z(R) = 1`, `Z(R') = 1`: source `0`, everybody else `1`
    simp only [Bool.not_eq_false] at h2
    set inp : PNode f → Bool := fun v => match v with | src => false | _ => true
    have hc := iter_const (inp := inp) (Z := Z) (a := false) (b := true) rfl (fun _ => rfl)
      (hZs false) h2
    exact contra inp src (cl (cStar f)) advB_src_correct (advB_cl_correct cc_cStar) fun t => by
      rw [(hc t).1, (hc t).2 _ cc_cStar]; simp

end CrashConsensusDigraph
