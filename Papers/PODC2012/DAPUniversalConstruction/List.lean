import Papers.PODC2012.DAPUniversalConstruction.Model

/-!
# The singly-linked list of Section 3 / Appendix A

The unsorted singly-linked list of integers with operations `Append(v)` and `Search(v)`
(Figures 5 and 6 of the paper). Its abstract state is the list of keys, in order. Its data items
are the static pointers `L.start` and `L.end` and the nodes; the `k`-th node (from `0`) is the
node created by the `(k+1)`-st `Append`.

Data sets, read off the code of Figure 6:
* `Append(v)` from a list with `m` nodes: `CreateDI` of the new node `node m`, `ReadDI(L.end)`,
  `WriteDI(e → next)` on the last node `node (m-1)` (or `WriteDI(L.start)` if the list is empty),
  `WriteDI(L.end)`;
* `Search(v)`: `ReadDI(L.start)`, then the nodes from the first one up to the first node with key
  `v` (all nodes if there is none).

We check the paper's claims that `Append` is value oblivious and `Search` is not.
-/

namespace Podc.DAPUniversalConstruction

open Cslib.SharedMemory

/-- Operations of the list. -/
inductive LOp where
  | append (v : ℤ)
  | search (v : ℤ)
  deriving DecidableEq

/-- Sequential specification of the list: states are the lists of keys. `Append` returns a
dummy `true`; `Search(v)` returns whether `v` is in the list. -/
abbrev listSpec : ObjSpec where
  State := List ℤ
  Op := LOp
  Resp := Bool
  init := []
  δ := fun s o => match o with
    | .append v => (s ++ [v], true)
    | .search v => (s, decide (v ∈ s))

/-- Data items of the list. -/
inductive DItem where
  /-- The pointer `L.start` to the first node. -/
  | start
  /-- The pointer `L.end` to the last node. -/
  | last
  /-- The `k`-th node (from `0`). -/
  | node (k : ℕ)
  deriving DecidableEq

/-- Data sets of the list operations, as accessed by the code of Figure 6. -/
def listDataSet : List ℤ → LOp → Set DItem
  | s, .append _ => {DItem.last, DItem.node s.length} ∪
      (if s = [] then {DItem.start} else {DItem.node (s.length - 1)})
  | s, .search v => insert DItem.start {x | ∃ k, x = DItem.node k ∧ k < s.length ∧ k ≤ s.idxOf v}

/-- The list data structure. -/
def listDS : SeqDS := ⟨listSpec, DItem, listDataSet⟩

lemma runOps_append_map (s : List ℤ) (vs : List ℤ) :
    listSpec.runOps s (vs.map LOp.append) = s ++ vs := by
  induction vs generalizing s with
  | nil => rw [List.map_nil, ObjSpec.runOps_nil, List.append_nil]
  | cons v vs ih => rw [List.map_cons, ObjSpec.runOps_cons, ih]; simp

lemma length_runOps_append (s : List ℤ) (f : ℕ → ℤ) (n : ℕ) :
    (listSpec.runOps s ((List.range n).map (LOp.append ∘ f))).length = s.length + n := by
  rw [← List.map_map, List.map_map, show (List.range n).map (LOp.append ∘ f) =
    ((List.range n).map f).map LOp.append by simp, runOps_append_map]
  simp

/-- `Append` is value oblivious (Section 3). -/
theorem append_valueOblivious : listDS.ValueOblivious LOp.append := by
  intro os f g n
  simp only [listDS, listDataSet]
  have hf := length_runOps_append (listSpec.runOps listSpec.init os) f n
  have hg := length_runOps_append (listSpec.runOps listSpec.init os) g n
  simp only [hf, hg, ← List.length_eq_zero_iff]

/-- `Search` is not value oblivious (Section 3): `Search(1)` and `Search(2)` on the list `[1, 2]`
access different data items. -/
theorem search_not_valueOblivious : ¬ listDS.ValueOblivious LOp.search := by
  intro h
  have := h [.append 1, .append 2] (fun _ => 1) (fun _ => 2) 0
  have e : listSpec.runOps (listSpec.runOps listSpec.init [.append 1, .append 2])
      ((List.range 0).map (LOp.search ∘ fun _ => (1 : ℤ))) = [1, 2] := rfl
  have e' : listSpec.runOps (listSpec.runOps listSpec.init [.append 1, .append 2])
      ((List.range 0).map (LOp.search ∘ fun _ => (2 : ℤ))) = [1, 2] := rfl
  simp only [listDS] at this
  rw [e, e'] at this
  simp only [listDataSet] at this
  have hmem : DItem.node 1 ∈ insert DItem.start {x | ∃ k, x = DItem.node k ∧
      k < ([1, 2] : List ℤ).length ∧ k ≤ ([1, 2] : List ℤ).idxOf 2} :=
    Or.inr ⟨1, rfl, by decide, by decide⟩
  rw [← this] at hmem
  rcases hmem with h1 | ⟨k, hk, -, hk'⟩
  · cases h1
  · cases hk; revert hk'; decide

end Podc.DAPUniversalConstruction
