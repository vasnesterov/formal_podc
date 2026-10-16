import Papers.PODC2021.AllYouNeedIsDAG.Ordering

/-!
# DAG-Rider: the DAG construction layer (Algorithm 2) as an asynchronous execution

Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*, PODC 2021, Sections 2 and 4.

**Model.** `n = 3f + 1` processes `P`, a set `byz` of at most `f` Byzantine processes (static: the
adversary's choice is part of the run). Reliable broadcast is abstract: a run gives for every
process `p` and every step `t` the finite set `dl p t` of vertex identifiers `(r, k)` that `p`
`r_deliver`s just before its `t`-th step. Non-equivocation (the consequence of RBC Agreement +
Integrity) is built in: the contents of all delivered vertices are given by one global
`Content` `R.C`. The remaining RBC guarantees are hypotheses of `Run.Valid`:

* *Validity*: a vertex broadcast by a correct process is eventually delivered to every correct one;
* *Agreement*: a vertex delivered to a correct process is eventually delivered to every correct one;
* *Authenticity*: a correct process delivers `(r, q)` with `q` correct only if `q` broadcast it,
  and then the delivered contents are the ones `q` computed (`createdOK`).

Correct processes run Algorithm 2: every step is one iteration of the `while True` loop
(buffer the delivered vertices that pass the check of line 25, add buffered vertices of round
`≤ r` whose predecessors are present (lines 6–9), and advance the round if `DAG[r]` has
`2f + 1` vertices (line 10)). When advancing to round `r + 1` the process broadcasts its vertex
`(r + 1, p)`: block `blk p (r + 1)` (the `(r+1)`-th `a_bcast` block), strong edges to all of
`DAG[r]` and weak edges such that it has a path to every vertex of `DAG` of round `≤ r - 1`
(`set_weak_edges` produces such a set; we allow any). `DAG[0]` is the hard-coded set of
`2f + 1` genesis vertices `G0` (only their sources matter); the local `dag` stores rounds `≥ 1`.
-/

namespace DagRider

open Finset

variable {P : Type*} {B : Type*} [DecidableEq P]

/-- Local state of Algorithm 2 for a correct process. -/
structure LState (P : Type*) where
  /-- The current round `r`. -/
  rnd : ℕ
  /-- `⋃_{r ≥ 1} DAG[r]`. -/
  dag : Finset (Vtx P)
  /-- `buffer`. -/
  buf : Finset (Vtx P)

/-- Line 7 (with `DAG[0]` the genesis vertices): all predecessors of `v` are present. -/
def PredsIn (G0 : Finset P) (C : Content P B) (dag : Finset (Vtx P)) (v : Vtx P) : Prop :=
  (∀ s ∈ C.strong v, if v.1 = 1 then s ∈ G0 else (v.1 - 1, s) ∈ dag) ∧
    ∀ u ∈ C.weak v, (u.1 = 0 ∧ u.2 ∈ G0) ∨ u ∈ dag

/-- One iteration of the main loop of Algorithm 2, after the vertices `new` were delivered. -/
noncomputable def lstep (f : ℕ) (G0 : Finset P) (C : Content P B) (s : LState P)
    (new : Finset (Vtx P)) : LState P := by
  classical exact
    let buf1 := s.buf ∪ new.filter (fun v => 2 * f + 1 ≤ (C.strong v).card)
    let add := buf1.filter (fun v => 1 ≤ v.1 ∧ v.1 ≤ s.rnd ∧ PredsIn G0 C s.dag v)
    let dag1 := s.dag ∪ add
    if s.rnd = 0 ∨ 2 * f + 1 ≤ (layer dag1 s.rnd).card then ⟨s.rnd + 1, dag1, buf1 \ add⟩
    else ⟨s.rnd, dag1, buf1 \ add⟩

/-- A run: the adversary's choices. -/
structure Run (P : Type*) (B : Type*) where
  /-- Contents of all broadcast vertices (non-equivocation). -/
  C : Content P B
  /-- Byzantine processes. -/
  byz : Finset P
  /-- `dl p t`: vertices `r_deliver`ed by `p` before its step `t`. -/
  dl : P → ℕ → Finset (Vtx P)

/-- The local state of process `p` after `t` steps (meaningful for correct `p`). -/
noncomputable def Run.st (f : ℕ) (G0 : Finset P) (R : Run P B) (p : P) : ℕ → LState P
  | 0 => ⟨0, ∅, ∅⟩
  | t + 1 => lstep f G0 R.C (R.st f G0 p t) (R.dl p t)

/-- The vertex `(r + 1, p)` created by a correct process when it advances from round `r` with
local DAG `D` has the contents prescribed by Algorithm 2 (lines 16–21, 27–31). -/
def CreatedOK (G0 : Finset P) (blk : P → ℕ → B) (C : Content P B) (p : P) (r : ℕ)
    (D : Finset (Vtx P)) : Prop :=
  C.block (r + 1, p) = blk p (r + 1) ∧
  C.strong (r + 1, p) = (if r = 0 then G0 else (layer D r).image Prod.snd) ∧
  C.weak (r + 1, p) ⊆ D ∧
  ∀ u ∈ D, u.1 + 2 ≤ r + 1 → Path C (r + 1, p) u

/-- Validity of a run of DAG-Rider's DAG layer (`n = 3f + 1`, `≤ f` Byzantine, RBC properties). -/
structure Run.Valid [Fintype P] (f : ℕ) (G0 : Finset P) (blk : P → ℕ → B) (R : Run P B) : Prop where
  card : Fintype.card P = 3 * f + 1
  card_G0 : G0.card = 2 * f + 1
  card_byz : R.byz.card ≤ f
  /-- Correct processes broadcast the vertices computed by Algorithm 2. -/
  created : ∀ p, p ∉ R.byz → ∀ t, (R.st f G0 p (t + 1)).rnd = (R.st f G0 p t).rnd + 1 →
    CreatedOK G0 blk R.C p (R.st f G0 p t).rnd (R.st f G0 p (t + 1)).dag
  /-- RBC authenticity: a vertex of a correct source is delivered only if it was broadcast. -/
  auth : ∀ p, p ∉ R.byz → ∀ q, q ∉ R.byz → ∀ t, ∀ v ∈ R.dl p t, v.2 = q →
    1 ≤ v.1 ∧ ∃ t', v.1 ≤ (R.st f G0 q t').rnd
  /-- RBC validity. -/
  rbcValidity : ∀ p, p ∉ R.byz → ∀ q, q ∉ R.byz → ∀ t r, 1 ≤ r → r ≤ (R.st f G0 q t).rnd →
    ∃ t', (r, q) ∈ R.dl p t'
  /-- RBC agreement. -/
  rbcAgreement : ∀ p, p ∉ R.byz → ∀ q, q ∉ R.byz → ∀ t, ∀ v ∈ R.dl p t, ∃ t', v ∈ R.dl q t'

/-- The local DAG of `p` at the moment `wave_ready(w)` is signalled (the step at which `p`
advances from round `4w` to `4w + 1`), or `∅` if `p` never completes wave `w`. -/
noncomputable def Run.snap (f : ℕ) (G0 : Finset P) (R : Run P B) (p : P) (w : ℕ) :
    Finset (Vtx P) := by
  classical exact
    if h : ∃ t, 4 * w < (R.st f G0 p t).rnd then (R.st f G0 p (Nat.find h)).dag else ∅

/-- Number of waves `w ≥ 1` completed by `p` after `t` steps. -/
noncomputable def Run.wavesDone (f : ℕ) (G0 : Finset P) (R : Run P B) (p : P) (t : ℕ) : ℕ :=
  ((R.st f G0 p t).rnd - 1) / 4

/-- The `a_deliver` outputs of `p` after `t` steps. -/
noncomputable def Run.delivered (f : ℕ) (G0 : Finset P) (coin : ℕ → P)
    (sortV : Finset (Vtx P) → List (Vtx P)) (R : Run P B) (p : P) (t : ℕ) : List (Vtx P) :=
  (orun f R.C coin sortV (R.snap f G0 p) (R.wavesDone f G0 p t)).delivered

end DagRider
