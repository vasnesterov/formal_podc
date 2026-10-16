import Papers.PODC2021.AllYouNeedIsDAG.Dag

/-!
# DAG-Rider: the ordering layer (Algorithm 3)

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021, Section 5.

The ordering layer of a process is a deterministic function of the local DAGs it holds at the
moments `wave_ready(w)` is signalled (`w = 1, 2, …`; the spurious initial call `wave_ready(0)`
of Algorithm 2 never commits anything and is omitted). A *snapshot sequence* `D : ℕ → Finset (Vtx P)`
gives, for every wave `w`, the local DAG `DAG_i` when wave `w` became ready.

* `wround w k = 4(w-1) + k` is the `k`-th round of wave `w`.
* `leader coin D w` is `get_wave_vertex_leader(w)`: the vertex of round `wround w 1` of the
  coin-chosen process `coin w` (global perfect coin: one value per wave), if it is in `D`.
* `commitCount C D v w` counts the vertices of `D` of round `wround w 4` with a strong path to `v`
  (commit rule: `≥ 2f + 1`, line 36).
* `chain` is the loop of lines 39–43, `deliverAll` is `order_vertices` (lines 51–57), where the
  "some deterministic order" is an arbitrary function `sortV : Finset (Vtx P) → List (Vtx P)`
  listing each finite set without repetitions (`SortSpec`).
* `waveReady` is the handler `upon wave_ready(w)` and `orun D W` the state after waves `1..W`.
-/

namespace DagRider

open Finset

variable {P : Type*} {B : Type*}

/-- `round(w, k) = 4(w - 1) + k`. -/
def wround (w k : ℕ) : ℕ := 4 * (w - 1) + k

/-- The leader vertex of wave `w` (if the process has it): `get_wave_vertex_leader(w)`. -/
def leader [DecidableEq P] (coin : ℕ → P) (D : Finset (Vtx P)) (w : ℕ) : Option (Vtx P) :=
  if (wround w 1, coin w) ∈ D then some (wround w 1, coin w) else none

/-- `|{v' ∈ DAG[round(w, 4)] : strong_path(v', v)}|` (line 36). -/
def commitCount [DecidableEq P] (C : Content P B) (D : Finset (Vtx P)) (v : Vtx P) (w : ℕ) : ℕ :=
  (D.filter (fun u => u.1 = wround w 4 ∧ SPath C u v)).card

/-- The waves `w - 1, w - 2, …, d + 1` (the loop of line 39). -/
def wavesDown (w d : ℕ) : List ℕ := (List.range (w - 1 - d)).map (fun k => w - 1 - k)

/-- Lines 39–43: the leaders pushed onto the stack after `v`, in push order. -/
def chain [DecidableEq P] (C : Content P B) (coin : ℕ → P) (D : Finset (Vtx P)) :
    Vtx P → List ℕ → List (Vtx P)
  | _, [] => []
  | cur, w :: ws =>
    match leader coin D w with
    | some v => if SPath C cur v then v :: chain C coin D v ws else chain C coin D cur ws
    | none => chain C coin D cur ws

/-- A "deterministic order": any function listing each finite set exactly once. -/
def SortSpec (sortV : Finset (Vtx P) → List (Vtx P)) : Prop :=
  ∀ s, (sortV s).Nodup ∧ ∀ x, x ∈ sortV s ↔ x ∈ s

/-- Lines 53–57 for one popped leader `v`: deliver its not yet delivered causal history. -/
noncomputable def deliverOne (C : Content P B) (sortV : Finset (Vtx P) → List (Vtx P))
    (D : Finset (Vtx P)) (L : List (Vtx P)) (v : Vtx P) : List (Vtx P) := by
  classical exact L ++ sortV ((hist C D v).filter (fun u => u ∉ L))

/-- `order_vertices`: process the popped leaders in order. -/
noncomputable def deliverAll (C : Content P B) (sortV : Finset (Vtx P) → List (Vtx P))
    (D : Finset (Vtx P)) (L : List (Vtx P)) (ls : List (Vtx P)) : List (Vtx P) :=
  ls.foldl (deliverOne C sortV D) L

/-- The local variables of Algorithm 3 (`deliveredVertices` is the set of `delivered`). -/
structure OState (P : Type*) where
  /-- `decidedWave`. -/
  decided : ℕ
  /-- The sequence of `a_deliver` outputs (as vertex identifiers). -/
  delivered : List (Vtx P)

/-- `upon wave_ready(w)` (lines 34–45). -/
noncomputable def waveReady [DecidableEq P] (f : ℕ) (C : Content P B) (coin : ℕ → P)
    (sortV : Finset (Vtx P) → List (Vtx P)) (D : Finset (Vtx P)) (w : ℕ) (s : OState P) :
    OState P :=
  match leader coin D w with
  | none => s
  | some v =>
    if 2 * f + 1 ≤ commitCount C D v w then
      { decided := w
        delivered :=
          deliverAll C sortV D s.delivered (v :: chain C coin D v (wavesDown w s.decided)).reverse }
    else s

/-- The state of the ordering layer after waves `1, …, W`, given the snapshots `D w`. -/
noncomputable def orun [DecidableEq P] (f : ℕ) (C : Content P B) (coin : ℕ → P)
    (sortV : Finset (Vtx P) → List (Vtx P)) (D : ℕ → Finset (Vtx P)) : ℕ → OState P
  | 0 => ⟨0, []⟩
  | W + 1 => waveReady f C coin sortV (D (W + 1)) (W + 1) (orun f C coin sortV D W)

end DagRider
