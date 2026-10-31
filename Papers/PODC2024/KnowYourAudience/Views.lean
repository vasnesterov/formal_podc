import Podc.Computability.Distributed.AnonymousNetworks.Basic
import Cslib.Foundations.Data.Nat.Descent

-- CSLib candidate (paper-local for now)

/-!
# Views (colour refinement) in a static anonymous network

The first step of the positive results of Section 4 is the construction, by every agent, of its
*view* of the network (the in-tree of walks ending at it), from which the minimum base is
extracted [Boldi–Vigna]. We use depth-indexed views:

* `Msg I t`: a depth-`t` view: a tag (the sender's outdegree, or `0` in the simple broadcast
  model), an input value, and (for `t > 0`) the multiset of depth-`(t-1)` views of the
  in-neighbours.
* `msg N x dd t j`: the depth-`t` view of agent `j` in network `N` with inputs `x`
  (tag `dd (outdeg j)`).
* `Msg.trunc`: truncation; `trunc_msg`: views of depth `t + 1` determine views of depth `t`.
* `eventually_stable`: the partition of the agents by their depth-`t` views stabilises
  (colour refinement on a finite set).
* `desc p K m`: the depth-`p` views of the nodes of a view at distance `≤ K` from the root;
  `desc_msg`: these are the views of the agents from which the root is reachable in `≤ K` steps.
-/

namespace Podc.KnowYourAudience

open Cslib.AnonNet Finset Filter

universe u

/-- Depth-`t` views. -/
def Msg (I : Type u) : ℕ → Type u
  | 0 => ℕ × I
  | t + 1 => ℕ × I × Multiset (Msg I t)

variable {I : Type u}

namespace Msg

/-- The tag of the root. -/
def tag : (t : ℕ) → Msg I t → ℕ
  | 0, m => m.1
  | _ + 1, m => m.1

/-- The input value of the root. -/
def val : (t : ℕ) → Msg I t → I
  | 0, m => m.2
  | _ + 1, m => m.2.1

/-- The views of the in-neighbours of the root. -/
def kids (t : ℕ) (m : Msg I (t + 1)) : Multiset (Msg I t) := m.2.2

/-- Truncation of a depth-`(t+1)` view to depth `t`. -/
def trunc : (t : ℕ) → Msg I (t + 1) → Msg I t
  | 0, m => (m.1, m.2.1)
  | t + 1, m => (m.1, m.2.1, m.2.2.map (trunc t))

end Msg

variable {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) (x : V → I) (dd : ℕ → ℕ)

/-- The depth-`t` view of agent `j`. -/
def msg : (t : ℕ) → V → Msg I t
  | 0, j => (dd (N.outdeg j), x j)
  | t + 1, j => (dd (N.outdeg j), x j, (N.inN j).val.map (msg t))

@[simp] lemma kids_msg (t : ℕ) (j : V) :
    Msg.kids t (msg N x dd (t + 1) j) = (N.inN j).val.map (msg N x dd t) := rfl

@[simp] lemma tag_msg (t : ℕ) (j : V) : Msg.tag t (msg N x dd t j) = dd (N.outdeg j) := by
  cases t <;> rfl

@[simp] lemma val_msg (t : ℕ) (j : V) : Msg.val t (msg N x dd t j) = x j := by
  cases t <;> rfl

@[simp] lemma trunc_msg (t : ℕ) (j : V) :
    Msg.trunc t (msg N x dd (t + 1) j) = msg N x dd t j := by
  induction t generalizing j with
  | zero => rfl
  | succ t ih =>
    show (_, _, ((N.inN j).val.map (msg N x dd (t + 1))).map (Msg.trunc t)) = _
    rw [Multiset.map_map]
    have : (Msg.trunc t ∘ msg N x dd (t + 1)) = msg N x dd t := funext ih
    rw [this]; rfl

lemma msg_eq_of_msg_succ_eq {t : ℕ} {j k : V} (h : msg N x dd (t + 1) j = msg N x dd (t + 1) k) :
    msg N x dd t j = msg N x dd t k := by
  rw [← trunc_msg, h, trunc_msg]

open scoped Classical in
/-- The number of distinct depth-`t` views. -/
noncomputable def numClasses (t : ℕ) : ℕ := (univ.image (msg N x dd t)).card

open scoped Classical in
lemma image_msg_eq (t : ℕ) :
    univ.image (msg N x dd t) = (univ.image (msg N x dd (t + 1))).image (Msg.trunc t) := by
  rw [Finset.image_image]
  congr 1
  funext j; simp

/-- **Colour refinement stabilises**: from some depth on, views of depth `t + 1` separate exactly
the same agents as views of depth `t`. -/
theorem eventually_stable :
    ∀ᶠ t in atTop, ∀ j k : V, msg N x dd (t + 1) j = msg N x dd (t + 1) k ↔
      msg N x dd t j = msg N x dd t k := by
  classical
  have hmono : ∀ t ≥ 0, numClasses N x dd t ≤ numClasses N x dd (t + 1) := by
    intro t _
    unfold numClasses
    rw [image_msg_eq]
    exact Finset.card_image_le
  have hbdd : ∀ t ≥ 0, numClasses N x dd t ≤ Fintype.card V := by
    intro t _
    unfold numClasses
    exact (Finset.card_image_le).trans (by simp)
  obtain ⟨T, -, hT⟩ := Nat.eventually_const_of_le_succ hbdd hmono
  rw [eventually_atTop]
  refine ⟨T, fun t ht j k => ⟨msg_eq_of_msg_succ_eq N x dd, fun h => ?_⟩⟩
  have heq : numClasses N x dd t = numClasses N x dd (t + 1) := by
    rw [hT t ht, hT (t + 1) (by omega)]
  unfold numClasses at heq
  rw [image_msg_eq] at heq
  have hinj : Set.InjOn (Msg.trunc t) (↑(univ.image (msg N x dd (t + 1))) : Set (Msg I (t + 1))) :=
    Finset.card_image_iff.1 heq
  apply hinj (by simp) (by simp)
  simpa using h

/-! ### Descendants of a view -/

/-- `j` reaches `i` by a walk of length at most `K`. -/
def ReachLE : ℕ → V → V → Prop
  | 0, j, i => j = i
  | K + 1, j, i => ReachLE K j i ∨ ∃ k ∈ N.inN i, ReachLE K j k

lemma reachLE_succ {K : ℕ} {j i : V} :
    ReachLE N (K + 1) j i ↔ ReachLE N K j i ∨ ∃ k ∈ N.inN i, ReachLE N K j k := Iff.rfl

lemma ReachLE.mono {K : ℕ} {j i : V} (h : ReachLE N K j i) : ∀ d, ReachLE N (K + d) j i := by
  intro d
  induction d with
  | zero => exact h
  | succ d ih => exact Or.inl ih

lemma exists_reachLE {j i : V} (h : Relation.ReflTransGen N.Adj j i) : ∃ K, ReachLE N K j i := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨K, hK⟩ := ih
    exact ⟨K + 1, Or.inr ⟨_, (N.mem_inN).2 hbc, hK⟩⟩

/-- In a strongly connected network, eventually every agent reaches every agent in `≤ K` steps. -/
lemma eventually_reachLE (hsc : N.StronglyConnected) :
    ∀ᶠ K in atTop, ∀ j i : V, ReachLE N K j i := by
  have : ∀ p : V × V, ∀ᶠ K in atTop, ReachLE N K p.1 p.2 := by
    rintro ⟨j, i⟩
    obtain ⟨K, hK⟩ := exists_reachLE N (hsc j i)
    rw [eventually_atTop]
    exact ⟨K, fun K' hK' => by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK'
      exact ReachLE.mono N hK d⟩
  have := Filter.eventually_all.2 this
  exact this.mono fun K hK j i => hK (j, i)

open scoped Classical in
/-- The depth-`p` truncations of the subviews of a depth-`(p + K)` view at distance `≤ K`. -/
noncomputable def desc (p : ℕ) : (K : ℕ) → Msg I (p + K) → Finset (Msg I p)
  | 0, m => {m}
  | K + 1, m => desc p K (Msg.trunc (p + K) m) ∪ (Msg.kids (p + K) m).toFinset.biUnion (desc p K)

open scoped Classical in
lemma desc_msg (p K : ℕ) (i : V) :
    desc p K (msg N x dd (p + K) i) =
      (univ.filter fun j => ReachLE N K j i).image (msg N x dd p) := by
  induction K generalizing i with
  | zero =>
    ext m; simp [desc, ReachLE, eq_comm]
  | succ K ih =>
    show desc p K (Msg.trunc (p + K) (msg N x dd (p + K + 1) i)) ∪
      (Msg.kids (p + K) (msg N x dd (p + K + 1) i)).toFinset.biUnion (desc p K) = _
    rw [trunc_msg, kids_msg, ih]
    ext m
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val]
    simp only [reachLE_succ]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨_, ⟨k, hk, rfl⟩, hm⟩)
      · exact ⟨j, Or.inl hj, rfl⟩
      · rw [ih] at hm
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        obtain ⟨j, hj, rfl⟩ := hm
        exact ⟨j, Or.inr ⟨k, hk, hj⟩, rfl⟩
    · rintro ⟨j, hj | ⟨k, hk, hjk⟩, rfl⟩
      · exact Or.inl ⟨j, hj, rfl⟩
      · refine Or.inr ⟨_, ⟨k, hk, rfl⟩, ?_⟩
        rw [ih]
        exact Finset.mem_image.2 ⟨j, by simpa using hjk, rfl⟩

end Podc.KnowYourAudience
