import Mathlib

/-!
# Algorithm 2 (S-SP) of [HW12] and counterexamples to Theorem 5

Holzer–Wattenhofer, *Optimal Distributed All Pairs Shortest Paths and Applications*, PODC 2012
([HW12]), Section 6.1. Algorithm 2 grows the BFS trees `T_u`, `u ∈ S`, simultaneously; on every
edge the smaller ID has priority. **Theorem 5** claims that after `|S| + D'` time slots
(`D' = 2 · ecc(1)`) every node `v` knows `δ_v[u] = d(u, v)` for all `u ∈ S`.

## The model

Synchronous message passing (CONGEST), no failures, deterministic. Vertices are `Fin n`, the ID of
vertex `v` is `v` itself (the paper's ID `k` is our vertex `k - 1`). A network is given by the
neighbour lists `nbrs v = [v₁, …, v_{d(v)}]` in the order of the paper's neighbour indices `i`.

## The algorithm (lines 13–29), faithfully

* `NodeState`: the local variables `L`, `L₁, …, L_{d(v)}` (as lists) and `δ` (`none` = `∞`).
  `parent` (line 23) is not modelled: it does not influence `L`, `Lᵢ`, `δ`.
* `init` (lines 1–6): `L = Lᵢ = {v}` and `δ[v] = 0` if `v ∈ S`, else `L = Lᵢ = ∅`, `δ ≡ ∞`.
  Lines 7–12 only compute the number of rounds `D' = 2 · ecc(1)`; it is a parameter here.
* `minId` (lines 14–16): `lᵢ = min Lᵢ`, or `∞` if `Lᵢ = ∅`.
* `NodeState.out` / `msgTo` (line 17): node `w` sends `(l_j, δ[l_j] + 1)` to its `j`-th neighbour.
* `process` (lines 19–27), for one neighbour index `i`:
  if `rᵢ < lᵢ` then (if `rᵢ ∉ L` then `δ[rᵢ] := δ_{rᵢ}`, `L := L ∪ {rᵢ}`,
  `L_j := L_j ∪ {rᵢ}` for all `j ≠ i`), else `Lᵢ := Lᵢ \ {lᵢ}`.
  In particular (literally as in the pseudocode) a received ID `rᵢ < lᵢ` that is already in `L`
  is ignored, and a received ID `rᵢ ≥ lᵢ` is dropped (the sender keeps it in its own list).
* `loop` (line 18): the indices `i = 1, …, d(v)` are processed in this order, so if a new ID
  arrives from several neighbours in the same slot, the one with the lowest index wins (as the
  paper says right before Theorem 5). `TieRule.minDelta` is a repaired variant in which `δ[r]`
  is the minimum of all values received for `r` in that slot.
* `run rule nbrs S t`: the global state after `t` synchronous time slots; the algorithm outputs
  `run rule nbrs S (|S| + D')`.

## Results

* `delta_stable`: once set, `δ_v[u]` never changes (so wrong values are final).
* (A) `triangle_wrong`: triangle, `S = {1, 3}`: node 1 ends with `δ[3] = 2`, but `d(1, 3) = 1`.
* (B) `exB_wrong`: nodes `1..4`, edges `1-3, 1-4, 3-4, 2-4`, `S = {2, 3, 4}`: node 3 ends with
  `δ[4] = 2` although `3` and `4` are adjacent — for **every** numbering of the neighbours and
  for **both** tie rules; the executions are tie-free (`exB_tieFree`), so the error is not a
  tie-breaking artefact. (`exB0_wrong`: the counterexample of the task description, edges
  `1-2, 1-3, 1-4, 2-3`, `S = V`, which works for the min-δ rule but only for some orderings.)
* (C) `exC_late`: `K₄` on `1..4` plus a pendant `5` at `1`, `S = {1,2,3,4}`: after
  `|S| + D' = 4 + 2 = 6` slots node `5` still has `δ[4] = ∞`.
* `theorem5_false`: Theorem 5 (correctness after `|S| + D'` slots) is false for both tie rules;
  `not_eventuallyCorrect`: the algorithm is not even correct after arbitrarily many slots.
-/

namespace Podc.OptimalAPSP.Alg2

variable {n : ℕ}

/-! ### The algorithm -/

/-- `r < l` on IDs extended by `∞` (`none`). -/
def idLt : Option (Fin n) → Option (Fin n) → Bool
  | some a, some b => decide (a.val < b.val)
  | some _, none => true
  | none, _ => false

/-- Line 15: `min Lᵢ`, or `∞` (`none`) if `Lᵢ = ∅`. -/
def minId : List (Fin n) → Option (Fin n)
  | [] => none
  | a :: l =>
    match minId l with
    | none => some a
    | some b => if a.val ≤ b.val then some a else some b

/-- `min` on `ℕ ∪ {∞}` (`none = ∞`). -/
def minInf : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- The local state of a node: `L`, the lists `L₁, …, L_{d(v)}` (one per neighbour, in index
order) and the array `δ` (`none = ∞`). -/
structure NodeState (n : ℕ) where
  /-- The set `L` of IDs whose BFS has reached the node. -/
  L : List (Fin n)
  /-- `Ls[i]` is the list `L_{i+1}` for the `(i+1)`-st neighbour. -/
  Ls : List (List (Fin n))
  /-- The distance array `δ` (`none = ∞`). -/
  δ : Fin n → Option ℕ

/-- A message `(l, δ[l] + 1)` (both components may be `∞ = none`). -/
abbrev Msg (n : ℕ) := Option (Fin n) × Option ℕ

/-- Line 17: the message `(l_j, δ[l_j] + 1)` a node sends to its neighbour with (0-based)
index `j`. -/
def NodeState.out (s : NodeState n) (j : ℕ) : Msg n :=
  let l := minId (s.Ls.getD j [])
  (l, (l.bind s.δ).map (· + 1))

/-- How the value `δ[r]` is chosen when a new ID `r` arrives in a slot. -/
inductive TieRule
  /-- As in the paper: the value received from the lowest neighbour index. -/
  | firstIndex
  /-- Repaired variant: the minimum of all values received for `r` in this slot. -/
  | minDelta

/-- The value assigned to `δ[r]` by line 21, given the value `d` received from the processed
neighbour, the own messages `ls` and the received messages `ms` of this slot. -/
def bestδ : TieRule → List (Option (Fin n)) → List (Msg n) → Fin n → Option ℕ → Option ℕ
  | .firstIndex, _, _, _, d => d
  | .minDelta, ls, ms, r, d =>
    ((ls.zip ms).filter fun p => p.2.1 = some r ∧ idLt p.2.1 p.1 = true).foldl
      (fun acc p => minInf acc p.2.2) d

/-- Lines 19–27 for the neighbour with (0-based) index `i`, own value `l = lᵢ` and received
message `m = (rᵢ, δ_{rᵢ})`. -/
def process (best : Fin n → Option ℕ → Option ℕ) (s : NodeState n) (i : ℕ)
    (l : Option (Fin n)) (m : Msg n) : NodeState n :=
  if idLt m.1 l then
    match m.1 with
    | some r =>
      if r ∈ s.L then s
      else
        { L := s.L.insert r
          Ls := s.Ls.mapIdx fun j Lj => if j = i then Lj else Lj.insert r
          δ := Function.update s.δ r (best r m.2) }
    | none => s
  else
    { s with Ls := s.Ls.mapIdx fun j Lj => if j = i then Lj.filter (fun x => some x ≠ l) else Lj }

/-- Line 18: process the neighbour indices `i = 0, 1, …` in this order. -/
def loop (best : Fin n → Option ℕ → Option ℕ) :
    NodeState n → ℕ → List (Option (Fin n)) → List (Msg n) → NodeState n
  | s, i, l :: ls, m :: ms => loop best (process best s i l m) (i + 1) ls ms
  | s, _, _, _ => s

/-- The message that `w` sends to its neighbour `v` in the current slot. -/
def msgTo (nbrs : Fin n → List (Fin n)) (st : Fin n → NodeState n) (w v : Fin n) : Msg n :=
  (st w).out ((nbrs w).idxOf v)

/-- The own values `l₁, …, l_{d(v)}` of a node (lines 14–16). -/
def NodeState.ls (s : NodeState n) : List (Option (Fin n)) := s.Ls.map minId

/-- The messages `(r₁, δ_{r₁}), …` received by `v` in the current slot. -/
def received (nbrs : Fin n → List (Fin n)) (st : Fin n → NodeState n) (v : Fin n) :
    List (Msg n) :=
  (nbrs v).map fun w => msgTo nbrs st w v

/-- One time slot (one iteration of the loop of line 13) at node `v`. -/
def localStep (rule : TieRule) (nbrs : Fin n → List (Fin n)) (st : Fin n → NodeState n)
    (v : Fin n) : NodeState n :=
  let ls := (st v).ls
  let ms := received nbrs st v
  loop (bestδ rule ls ms) (st v) 0 ls ms

/-- Lines 1–6: the initial state. -/
def init (nbrs : Fin n → List (Fin n)) (S : Finset (Fin n)) (v : Fin n) : NodeState n :=
  let L := if v ∈ S then [v] else []
  { L := L
    Ls := (nbrs v).map fun _ => L
    δ := fun u => if v ∈ S ∧ u = v then some 0 else none }

/-- The global state after `t` synchronous time slots. -/
def run (rule : TieRule) (nbrs : Fin n → List (Fin n)) (S : Finset (Fin n)) :
    ℕ → Fin n → NodeState n
  | 0 => init nbrs S
  | t + 1 => localStep rule nbrs (run rule nbrs S t)

/-- The value of `δ_v[u]` after `t` slots (`none = ∞`). -/
def deltaAt (rule : TieRule) (nbrs : Fin n → List (Fin n)) (S : Finset (Fin n)) (t : ℕ)
    (v u : Fin n) : Option ℕ :=
  (run rule nbrs S t v).δ u

/-- The output of Algorithm 2 with `D'` given: `δ_v[u]` after `|S| + D'` slots. -/
def output (rule : TieRule) (nbrs : Fin n → List (Fin n)) (S : Finset (Fin n)) (D' : ℕ)
    (v u : Fin n) : Option ℕ :=
  deltaAt rule nbrs S (S.card + D') v u

/-! ### Networks and their graphs -/

/-- A network: neighbour lists (in the order of the neighbour indices) of a simple graph. -/
structure Network (n : ℕ) where
  /-- The neighbours `v₁, …, v_{d(v)}` of `v`, in index order. -/
  nbrs : Fin n → List (Fin n)
  symm : ∀ u v, v ∈ nbrs u → u ∈ nbrs v
  loopless : ∀ v, v ∉ nbrs v
  nodup : ∀ v, (nbrs v).Nodup

/-- The underlying simple graph of a network. -/
def Network.graph (N : Network n) : SimpleGraph (Fin n) where
  Adj u v := v ∈ N.nbrs u
  symm := ⟨N.symm⟩
  loopless := ⟨N.loopless⟩

instance (N : Network n) : DecidableRel N.graph.Adj := fun u v =>
  inferInstanceAs (Decidable (v ∈ N.nbrs u))

/-- Two networks with the same graph differ only by the numbering of the neighbours. -/
theorem Network.perm_of_graph_eq {N N' : Network n} (h : N.graph = N'.graph) (v : Fin n) :
    (N.nbrs v).Perm (N'.nbrs v) := by
  rw [List.perm_ext_iff_of_nodup (N.nodup v) (N'.nodup v)]
  intro w
  change N.graph.Adj v w ↔ N'.graph.Adj v w
  rw [h]

/-! ### Once set, `δ` never changes -/

/-- The invariant: a known distance belongs to an ID in `L`. -/
def Inv (s : NodeState n) : Prop := ∀ u, s.δ u ≠ none → u ∈ s.L

theorem process_inv {best} {s : NodeState n} (hs : Inv s) (i l m) :
    Inv (process best s i l m) ∧ ∀ u k, s.δ u = some k → (process best s i l m).δ u = some k := by
  unfold process
  split
  · split
    · rename_i r _
      split
      · exact ⟨hs, fun _ _ h => h⟩
      · rename_i hr
        refine ⟨fun u hu => ?_, fun u k hk => ?_⟩
        · simp only [List.mem_insert_iff]
          by_cases hur : u = r
          · exact Or.inl hur
          · right; apply hs; simpa [Function.update_of_ne hur] using hu
        · have hur : u ≠ r := by rintro rfl; exact hr (hs _ (by simp [hk]))
          simpa [Function.update_of_ne hur] using hk
    · exact ⟨hs, fun _ _ h => h⟩
  · exact ⟨hs, fun _ _ h => h⟩

theorem loop_inv {best} : ∀ (s : NodeState n) (i : ℕ) ls ms, Inv s →
    Inv (loop best s i ls ms) ∧ ∀ u k, s.δ u = some k → (loop best s i ls ms).δ u = some k
  | s, i, l :: ls, m :: ms, hs => by
    obtain ⟨h1, h2⟩ := process_inv (best := best) hs i l m
    obtain ⟨h3, h4⟩ := loop_inv _ (i + 1) ls ms h1
    exact ⟨h3, fun u k hk => h4 u k (h2 u k hk)⟩
  | s, _, [], _, hs => ⟨hs, fun _ _ h => h⟩
  | s, _, _ :: _, [], hs => ⟨hs, fun _ _ h => h⟩

theorem run_inv (rule nbrs S) : ∀ t (v : Fin n), Inv (run rule nbrs S t v)
  | 0, v => by
    intro u hu
    simp only [run, init, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false, not_not] at hu ⊢
    simp [hu.1, hu.2]
  | t + 1, v => (loop_inv _ _ _ _ (run_inv rule nbrs S t v)).1

/-- Once `δ_v[u]` has been set (line 21), it never changes again. -/
theorem delta_stable (rule : TieRule) (nbrs : Fin n → List (Fin n)) (S : Finset (Fin n))
    {t t' : ℕ} (htt' : t ≤ t') {v u : Fin n} {k : ℕ} (h : deltaAt rule nbrs S t v u = some k) :
    deltaAt rule nbrs S t' v u = some k := by
  induction htt' with
  | refl => exact h
  | step _ ih => exact (loop_inv _ _ _ _ (run_inv rule nbrs S _ v)).2 u k ih

/-! ### Ties -/

/-- The new IDs delivered successfully to `v` in the slot following state `st` (one entry per
delivering neighbour). -/
def newDeliveries (nbrs : Fin n → List (Fin n)) (st : Fin n → NodeState n) (v : Fin n) :
    List (Fin n) :=
  ((st v).ls.zip (received nbrs st v)).filterMap fun p =>
    match p.2.1 with
    | some r => if idLt (some r) p.1 ∧ r ∉ (st v).L then some r else none
    | none => none

/-- No node receives the same new ID from two neighbours in the same slot during the first
`T` slots; then the tie rule (and the processing order of line 18) is never consulted. -/
def TieFree (rule : TieRule) (nbrs : Fin n → List (Fin n)) (S : Finset (Fin n)) (T : ℕ) :
    Prop :=
  ∀ t < T, ∀ v, (newDeliveries nbrs (run rule nbrs S t) v).Nodup

instance (rule : TieRule) (nbrs : Fin n → List (Fin n)) (S : Finset (Fin n)) (T : ℕ) :
    Decidable (TieFree rule nbrs S T) := by
  unfold TieFree; infer_instance

/-! ### Counterexample (A): the triangle -/

/-- The triangle on the IDs `1, 2, 3` (our vertices `0, 1, 2`), neighbours by increasing ID. -/
def triangle : Network 3 where
  nbrs := ![[1, 2], [0, 2], [0, 1]]
  symm := by decide
  loopless := by decide
  nodup := by decide

/-- `D' = 2 · ecc(1) = 2` for the triangle. -/
theorem triangle_eccent : triangle.graph.eccent 0 = 1 := by
  rw [SimpleGraph.eccent_eq_one_iff]; decide

/-- Counterexample (A) to Theorem 5. Triangle, `S = {1, 3}` (vertices `{0, 2}`): from slot 2 on
(in particular at the end, after `|S| + D' = 4` slots) node `1` has `δ[3] = 2`, although
`d(1, 3) = 1`: in slot 2 the ID `3` reaches node `1` both directly (value 1) and via node `2`
(value 2), and the lower neighbour index (node 2) wins. -/
theorem triangle_wrong :
    triangle.graph.dist 0 2 = 1 ∧ ({0, 2} : Finset (Fin 3)).card + 2 = 4 ∧
    ∀ t ≥ 2, deltaAt .firstIndex triangle.nbrs {0, 2} t 0 2 = some 2 := by
  refine ⟨SimpleGraph.dist_eq_one_iff_adj.2 (by decide), by decide, fun t ht => ?_⟩
  exact delta_stable _ _ _ ht (by decide +kernel)

/-! ### Counterexample (B): robust, tie-free -/

/-- IDs `1..4` (vertices `0..3`), edges `1-3, 1-4, 3-4, 2-4`: a triangle `{1,3,4}` with a pendant
`2` at `4`; neighbours by increasing ID. -/
def exB : Network 4 where
  nbrs := ![[2, 3], [3], [0, 3], [0, 1, 2]]
  symm := by decide
  loopless := by decide
  nodup := by decide

/-- A network from a list of neighbour lists (used to enumerate all numberings). -/
def nbrsOf (ls : List (List (Fin n))) (v : Fin n) : List (Fin n) := ls.getD v.val []

/-- `D' = 2 · ecc(1) = 4` for `exB`. -/
theorem exB_eccent : exB.graph.eccent 0 = 2 := by
  apply le_antisymm
  · rw [SimpleGraph.eccent_le_iff]
    intro v
    fin_cases v
    · simp
    · have h : exB.graph.Adj 0 3 ∧ exB.graph.Adj 3 1 := by decide
      exact (SimpleGraph.edist_le (h.1.toWalk.concat h.2)).trans (by simp)
    · exact (SimpleGraph.edist_eq_one_iff_adj.2 (by decide)).le.trans (by norm_num)
    · exact (SimpleGraph.edist_eq_one_iff_adj.2 (by decide)).le.trans (by norm_num)
  · refine le_trans ?_ (SimpleGraph.edist_le_eccent (v := 1))
    have h0 : exB.graph.edist 0 1 ≠ 0 := by rw [Ne, SimpleGraph.edist_eq_zero_iff]; decide
    have h1 : exB.graph.edist 0 1 ≠ 1 := by rw [Ne, SimpleGraph.edist_eq_one_iff_adj]; decide
    generalize exB.graph.edist 0 1 = x at h0 h1 ⊢
    induction x using ENat.recTopCoe with
    | top => simp
    | coe k => norm_cast at h0 h1 ⊢; omega

/-- All runs of `exB` (every numbering of the neighbours, both tie rules) during the
`|S| + D' = 3 + 4 = 7` slots: tie-free, and node `3` (vertex 2) has `δ[4] = 2` after slot 2. -/
theorem exB_check : ∀ l0 ∈ (exB.nbrs 0).permutations', ∀ l1 ∈ (exB.nbrs 1).permutations',
    ∀ l2 ∈ (exB.nbrs 2).permutations', ∀ l3 ∈ (exB.nbrs 3).permutations',
    ∀ rule ∈ [TieRule.firstIndex, TieRule.minDelta],
      TieFree rule (nbrsOf [l0, l1, l2, l3]) {1, 2, 3} 7 ∧
      deltaAt rule (nbrsOf [l0, l1, l2, l3]) {1, 2, 3} 2 2 3 = some 2 := by
  decide +kernel

/-- Counterexample (B) to Theorem 5, robust version. Network `exB` (triangle `{1,3,4}` plus a
pendant `2` at `4`), `S = {2, 3, 4}` (vertices `{1, 2, 3}`), `D' = 2 · ecc(1) = 4`. For **every**
numbering of the neighbours (every network `N` with the same graph) and **both** tie rules, the
execution is tie-free during the `|S| + D' = 7` slots, and from slot 2 on node `3` has
`δ[4] = 2`, although `3` and `4` are adjacent. In slot 1 the ID `4` is blocked on the edge
`4 → 3` by the smaller ID `3` travelling `3 → 4`; in slot 2 it arrives at `3` via node `1`. -/
theorem exB_wrong (N : Network 4) (hN : N.graph = exB.graph) (rule : TieRule) :
    N.graph.dist 2 3 = 1 ∧ N.graph.eccent 0 = 2 ∧ ({1, 2, 3} : Finset (Fin 4)).card + 2 * 2 = 7 ∧
    TieFree rule N.nbrs {1, 2, 3} 7 ∧
    ∀ t ≥ 2, deltaAt rule N.nbrs {1, 2, 3} t 2 3 = some 2 := by
  have hn : N.nbrs = nbrsOf [N.nbrs 0, N.nbrs 1, N.nbrs 2, N.nbrs 3] := by
    funext v; fin_cases v <;> rfl
  have hp : ∀ i, N.nbrs i ∈ (exB.nbrs i).permutations' := fun i =>
    List.mem_permutations'.2 (Network.perm_of_graph_eq hN i)
  have key := exB_check _ (hp 0) _ (hp 1) _ (hp 2) _ (hp 3) rule (by cases rule <;> simp)
  rw [← hn] at key
  refine ⟨?_, hN ▸ exB_eccent, by decide, key.1, fun t ht => delta_stable _ _ _ ht key.2⟩
  rw [hN]; exact SimpleGraph.dist_eq_one_iff_adj.2 (by decide)

/-- The counterexample of the task description: IDs `1..4` (vertices `0..3`), edges
`1-2, 1-3, 1-4, 2-3`, neighbours by increasing ID. -/
def exB0 : Network 4 where
  nbrs := ![[1, 2, 3], [0, 2], [0, 1], [0]]
  symm := by decide
  loopless := by decide
  nodup := by decide

/-- On `exB0` with `S = V` (`D' = 2`, `|S| + D' = 6`) and the neighbours numbered by increasing
ID, node `3` (vertex 2) ends with `δ[4] = 3` although `d(3, 4) = 2`, for both tie rules: the ID `4`
first reaches node `3` only along the path `4, 1, 2, 3`. (For other numberings this instance can
be correct; see `exB_wrong` for a robust counterexample.) -/
theorem exB0_wrong (rule : TieRule) :
    exB0.graph.dist 2 3 = 2 ∧ exB0.graph.eccent 0 = 1 ∧
    ∀ t ≥ 4, deltaAt rule exB0.nbrs Finset.univ t 2 3 = some 3 := by
  refine ⟨?_, (SimpleGraph.eccent_eq_one_iff _).2 (by decide), fun t ht => ?_⟩
  · apply le_antisymm
    · have h : exB0.graph.Adj 2 0 ∧ exB0.graph.Adj 0 3 := by decide
      exact (SimpleGraph.dist_le (h.1.toWalk.concat h.2)).trans (by simp)
    · have hr : exB0.graph.Reachable 2 3 := (by decide : exB0.graph.Adj 2 0).reachable.trans
        (by decide : exB0.graph.Adj 0 3).reachable
      have h0 : exB0.graph.dist 2 3 ≠ 0 := by
        rw [Ne, hr.dist_eq_zero_iff]; decide
      have h1 : exB0.graph.dist 2 3 ≠ 1 := by
        rw [Ne, SimpleGraph.dist_eq_one_iff_adj]; decide
      omega
  · cases rule
    · exact delta_stable _ _ _ ht (by decide +kernel)
    · exact delta_stable _ _ _ ht (by decide +kernel)

/-! ### Counterexample (C): the running time `|S| + D'` -/

/-- `K₄` on the IDs `1..4` (vertices `0..3`) plus a pendant `5` (vertex 4) at `1`, neighbours by
increasing ID. -/
def exC : Network 5 where
  nbrs := ![[1, 2, 3, 4], [0, 2, 3], [0, 1, 3], [0, 1, 2], [0]]
  symm := by decide
  loopless := by decide
  nodup := by decide

/-- Counterexample (C): on `exC` with `S = {1, 2, 3, 4}` we have `D' = 2 · ecc(1) = 2`, but after
the `|S| + D' = 6` slots of Algorithm 2 node `5` still has `δ[4] = ∞` (with the paper's tie rule).
The ID `4` only arrives in slot 7, and then with the wrong value `4` (`d(5, 4) = 2`). -/
theorem exC_late :
    exC.graph.eccent 0 = 1 ∧
    output .firstIndex exC.nbrs {0, 1, 2, 3} (2 * 1) 4 3 = none ∧
    deltaAt .firstIndex exC.nbrs {0, 1, 2, 3} 7 4 3 = some 4 ∧ exC.graph.dist 4 3 = 2 := by
  refine ⟨(SimpleGraph.eccent_eq_one_iff _).2 (by decide), by decide +kernel, by decide +kernel, ?_⟩
  apply le_antisymm
  · have h : exC.graph.Adj 4 0 ∧ exC.graph.Adj 0 3 := by decide
    exact (SimpleGraph.dist_le (h.1.toWalk.concat h.2)).trans (by simp)
  · have hr : exC.graph.Reachable 4 3 := (by decide : exC.graph.Adj 4 0).reachable.trans
      (by decide : exC.graph.Adj 0 3).reachable
    have h0 : exC.graph.dist 4 3 ≠ 0 := by
      rw [Ne, hr.dist_eq_zero_iff]; decide
    have h1 : exC.graph.dist 4 3 ≠ 1 := by
      rw [Ne, SimpleGraph.dist_eq_one_iff_adj]; decide
    omega

/-! ### Theorem 5 is false -/

/-- **Theorem 5 of [HW12]** (correctness part), as implemented by Algorithm 2 with tie rule
`rule`: on every connected network, after `|S| + D'` slots with `D' = 2 · ecc(1)`, every node `v`
has `δ_v[u] = d(u, v)` for every `u ∈ S`. (The ID `1` is our vertex `0`.) -/
def Theorem5 (rule : TieRule) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (N : Network n) (S : Finset (Fin n)), N.graph.Connected →
    ∀ u ∈ S, ∀ v, output rule N.nbrs S (2 * (N.graph.eccent ⟨0, hn⟩).toNat) v u =
      some (N.graph.dist u v)

/-- The weakest form of correctness: for every connected network and every `S` the values `δ`
are eventually (after sufficiently many slots) the correct distances. -/
def EventuallyCorrect (rule : TieRule) : Prop :=
  ∀ (n : ℕ) (N : Network n) (S : Finset (Fin n)), N.graph.Connected →
    ∃ T, ∀ t ≥ T, ∀ u ∈ S, ∀ v, deltaAt rule N.nbrs S t v u = some (N.graph.dist u v)

theorem triangle_connected : triangle.graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · rfl
  · exact (by decide : triangle.graph.Adj 0 1).reachable
  · exact (by decide : triangle.graph.Adj 0 2).reachable

theorem exB_connected : exB.graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨3, fun v => ?_⟩
  fin_cases v
  · exact (by decide : exB.graph.Adj 3 0).reachable
  · exact (by decide : exB.graph.Adj 3 1).reachable
  · exact (by decide : exB.graph.Adj 3 2).reachable
  · rfl

/-- Algorithm 2 is not even eventually correct, for either tie rule and every numbering of
the neighbours of `exB` (`exB_wrong`). -/
theorem not_eventuallyCorrect (rule : TieRule) : ¬ EventuallyCorrect rule := by
  intro h
  obtain ⟨T, hT⟩ := h 4 exB {1, 2, 3} exB_connected
  have h1 := hT (max T 2) (le_max_left _ _) 3 (by decide) 2
  have h2 := (exB_wrong exB rfl rule).2.2.2.2 (max T 2) (le_max_right _ _)
  rw [h2, SimpleGraph.dist_comm, (exB_wrong exB rfl rule).1] at h1
  simp at h1

/-- **Theorem 5 of [HW12] is false** (correctness part): already on the triangle with
`S = {1, 3}` node `1` computes `δ[3] = 2 ≠ 1 = d(1, 3)` (`triangle_wrong`); and even the
repaired tie rule `minDelta` fails (`exB_wrong`, for every numbering of the neighbours). -/
theorem theorem5_false : ¬ Theorem5 .firstIndex ∧ ¬ Theorem5 .minDelta := by
  constructor
  · intro h
    have h1 := h 3 (by decide) triangle {0, 2} triangle_connected 2 (by decide) 0
    have he : triangle.graph.eccent ⟨0, by decide⟩ = 1 := triangle_eccent
    rw [he] at h1
    have h2 := (triangle_wrong).2.2 4 (by decide)
    rw [SimpleGraph.dist_comm, triangle_wrong.1] at h1
    simp only [output] at h1
    rw [show ({0, 2} : Finset (Fin 3)).card + 2 * (1 : ℕ∞).toNat = 4 by decide, h2] at h1
    simp at h1
  · intro h
    have h1 := h 4 (by decide) exB {1, 2, 3} exB_connected 3 (by decide) 2
    have he : exB.graph.eccent ⟨0, by decide⟩ = 2 := exB_eccent
    rw [he] at h1
    have h2 := (exB_wrong exB rfl .minDelta).2.2.2.2 7 (by decide)
    rw [SimpleGraph.dist_comm, (exB_wrong exB rfl .minDelta).1] at h1
    simp only [output] at h1
    rw [show ({1, 2, 3} : Finset (Fin 4)).card + 2 * (2 : ℕ∞).toNat = 7 by decide, h2] at h1
    simp at h1

end Podc.OptimalAPSP.Alg2
