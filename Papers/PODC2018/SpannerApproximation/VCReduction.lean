import Papers.PODC2018.SpannerApproximation.VertexCover
import Cslib.Computability.Distributed.Congest.LowerBound
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# From distributed weighted 2-spanners to distributed vertex cover (Lemma 3.2 of [CD18])

Model: CSLib's deterministic synchronous CONGEST model `Cslib.Congest.Algorithm V I σ B`
(vertex names are the IDs, `B`-bit messages per edge, direction and round, no failures).

* **Spanner algorithms** run on `G_S` (vertex type `V × Fin 3`). The input of node `a` is the list
  of its incident edges with their weights, `inpS G a : V × Fin 3 → Option ℕ`. The output is given
  by a selector `pick : V' → σ → V' → V' → Bool`: node `x` in state `s` outputs the edge `{a, b}`
  iff `pick x s a b` (either orientation; only incident edges count). The output spanner is the
  union of the nodes' outputs, `spannerOut`.
* **MVC algorithms** run on `G`; node input = its neighbourhood `V → Bool`; output
  `out v s = true` iff `v` is in the cover.

`mvcAlg A pick T` simulates `A` on `G_S`: node `v` of `G` simulates `v₁, v₂, v₃`; the (at most
three) `G_S`-messages that travel from copies of `v` to copies of a neighbour `u` in one round are
bundled into one message of `3B` bits. After `T` simulated rounds, one extra round tells every
neighbour `u` whether a copy of `v` picked the cross edge between `v` and `u`; then `v` decides
whether `v ∈ C_H` (Claim 3.1). The extra round is needed: whether the cross edge `{v₁, u₂}` is in
the union of the outputs may depend on the output of `u₂`, which `v` does not know
(see `localRule_counterexample`).

Main results:
* `lemma_3_2`: `A_MVC = mvcAlg A pick T` uses `3B`-bit messages and `T + 1` rounds;
* `lemma_3_2_congest`: `slow 3 (mvcAlg A pick T)` uses `B`-bit messages and `3(T + 1)` rounds
  (`slow k` is a generic CONGEST slowdown splitting `kB`-bit messages over `k` rounds);
* `localRule_counterexample`: `C_H` cannot be computed from the nodes' own outputs only.
-/

namespace Podc.SpannerApproximation

open Cslib.Congest

section SpannerOutput

variable {W σ : Type*}

/-- The spanner output by the nodes: the union of the edges output by the nodes, restricted to the
edges of `Gs`; node `x` (in state `st x`) outputs its incident edge `{x, y}` iff
`pick x (st x) x y` or `pick x (st x) y x`. -/
def spannerOut (Gs : SimpleGraph W) (pick : W → σ → W → W → Bool) (st : W → σ) :
    SimpleGraph W where
  Adj a b := Gs.Adj a b ∧ (pick a (st a) a b = true ∨ pick a (st a) b a = true ∨
    pick b (st b) a b = true ∨ pick b (st b) b a = true)
  symm := ⟨fun _ _ h => ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => Gs.irrefl h.1⟩

instance (Gs : SimpleGraph W) [DecidableRel Gs.Adj] (pick : W → σ → W → W → Bool) (st : W → σ) :
    DecidableRel (spannerOut Gs pick st).Adj := fun _ _ => by unfold spannerOut; infer_instance

lemma spannerOut_le (Gs : SimpleGraph W) (pick : W → σ → W → W → Bool) (st : W → σ) :
    spannerOut Gs pick st ≤ Gs := fun _ _ h => h.1

end SpannerOutput

variable {V : Type*} [LinearOrder V]

/-! ### Inputs -/

/-- Input of the MVC algorithm at `v`: its neighbourhood. -/
def nbrInput (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : V → Bool :=
  fun u => decide (G.Adj v u)

/-- Input of the spanner algorithm at node `a` of `G_S`: its incident edges with their weights. -/
def inpS (G : SimpleGraph V) [DecidableRel G.Adj] (a : V × Fin 3) : V × Fin 3 → Option ℕ :=
  fun b => if (GS G).Adj a b then some (wtPair a b) else none

/-- Node `v` computes the `G_S`-input of its copy `vᵢ` from its own neighbourhood `nb`. -/
def localInpS (v : V) (nb : V → Bool) (i : Fin 3) : V × Fin 3 → Option ℕ :=
  fun b => if SAdj (fun _ y => nb y = true) (v, i) b then some (wtPair (v, i) b) else none

lemma localInpS_eq (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (i : Fin 3) :
    localInpS v (nbrInput G v) i = inpS G (v, i) := by
  funext b
  simp [localInpS, inpS, GS_adj, SAdj, nbrInput]

/-! ### The three `G_S`-edges of a `G`-edge -/

/-- The `k`-th `G_S`-edge between copies of `v` and copies of `u ≠ v`, as (copy of `v`, copy of
`u`): `{v₁,u₁}`, `{v₂,u₂}` and the cross edge. -/
def src (v u : V) : Fin 3 → Fin 3 × Fin 3
  | 0 => (0, 0)
  | 1 => (1, 1)
  | 2 => if v < u then (0, 1) else (1, 0)

/-- The index `k` of the `G_S`-edge `{wᵢ, uⱼ}` (if it is one of the three). -/
def idx (w u : V) (i j : Fin 3) : Option (Fin 3) :=
  if i = 0 ∧ j = 0 then some 0 else if i = 1 ∧ j = 1 then some 1
  else if src w u 2 = (i, j) then some 2 else none

lemma src_idx {w u : V} {i j : Fin 3} {k : Fin 3} (h : idx w u i j = some k) :
    src w u k = (i, j) := by
  unfold idx at h
  split_ifs at h with h1 h2 h3 <;> simp only [Option.some.injEq] at h <;> subst h
  · simp [src, h1.1, h1.2]
  · simp [src, h2.1, h2.2]
  · exact h3

lemma GS_adj_iff_idx {G : SimpleGraph V} {w u : V} (h : w ≠ u) {i j : Fin 3} :
    (GS G).Adj (w, i) (u, j) ↔ G.Adj w u ∧ (idx w u i j).isSome := by
  rw [GS_adj_of_ne h]
  refine and_congr_right fun _ => ?_
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have : ¬ u < w := not_lt.mpr hlt.le
    simp only [idx, src, hlt, this, ite_true, false_and, or_false, true_and]
    revert i j; decide
  · have : ¬ w < u := not_lt.mpr hlt.le
    simp only [idx, src, hlt, this, ite_false, false_and, true_and]
    revert i j; decide

/-! ### The simulation -/

/-- State of the MVC algorithm at `v`: round counter, own neighbourhood, simulated states of the
copies `v₁, v₂, v₃`, and the output bit. -/
structure SimState (V σ : Type*) where
  /-- Number of rounds done. -/
  round : ℕ
  /-- The neighbourhood of `v` (its input). -/
  nbr : V → Bool
  /-- Simulated states of `v₁, v₂, v₃`. -/
  sim : Fin 3 → σ
  /-- Output: `v ∈ C_H`. -/
  inC : Bool

variable {σ : Type*} {B : ℕ}

/-- Node `x` in state `s` outputs the edge `{a, b}` (either orientation). -/
def picks (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (x : V × Fin 3) (s : σ)
    (a b : V × Fin 3) : Bool :=
  pick x s a b || pick x s b a

/-- Whether the copy of `v` incident to the cross edge between `v` and `u` outputs it. -/
def crossPicked (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (v u : V)
    (sim : Fin 3 → σ) : Bool :=
  picks pick (v, (src v u 2).1) (sim (src v u 2).1) (v, (src v u 2).1) (u, (src v u 2).2)

/-- The bundled `3B`-bit message from `v` to `u`: the messages of the copies of `v` along the
three `G_S`-edges between `v` and `u`. -/
def bundle (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B) (v u : V) (sim : Fin 3 → σ) :
    Msg (3 * B) := fun n =>
  let p := finProdFinEquiv.symm n
  A.send (v, (src v u p.1).1) (sim (src v u p.1).1) (u, (src v u p.1).2) p.2

/-- The `k`-th `B`-bit chunk of a bundled message. -/
def chunk (k : Fin 3) (m : Msg (3 * B)) : Msg B := fun b => m (finProdFinEquiv (k, b))

lemma chunk_bundle (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B) (v u : V)
    (sim : Fin 3 → σ) (k : Fin 3) :
    chunk k (bundle A v u sim) =
      A.send (v, (src v u k).1) (sim (src v u k).1) (u, (src v u k).2) := by
  funext b
  simp [chunk, bundle]

/-- The first bit of a message (`false` if `B = 0`). -/
def firstBit (m : Msg (3 * B)) : Bool := if h : 0 < 3 * B then m ⟨0, h⟩ else false

/-- The messages received by the simulated copy `vⱼ`, reconstructed by `v` from its own
simulated states (triangle edges) and the bundled messages received from its neighbours. -/
def simRecv (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B) (v : V) (sim : Fin 3 → σ)
    (recv : V → Option (Msg (3 * B))) (j : Fin 3) : V × Fin 3 → Option (Msg B) := fun x =>
  if x.1 = v then (if x.2 ≠ j then some (A.send (v, x.2) (sim x.2) (v, j)) else none)
  else (recv x.1).bind fun m => (idx x.1 v x.2 j).map fun k => chunk k m

/-- Bit sent by `v` to `u`: in the first `T` rounds the bundled `A`-messages, then whether a copy
of `v` output the cross edge between `v` and `u`. -/
def mvcSend (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B)
    (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (T : ℕ) (v : V) (st : SimState V σ)
    (u : V) : Msg (3 * B) :=
  if st.round < T then bundle A v u st.sim else fun _ => crossPicked pick v u st.sim

/-- The decision `v ∈ C_H` after the last round: `{v₁, v₂}` was output by `v₁` or `v₂`, or the
cross edge between `v` and some neighbour `u` was output by the copy of `v` or (as reported in
the last round) by the copy of `u`. -/
def decideC [Fintype V] (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (v : V)
    (st : SimState V σ) (recv : V → Option (Msg (3 * B))) : Bool :=
  picks pick (v, 0) (st.sim 0) (v, 0) (v, 1) || picks pick (v, 1) (st.sim 1) (v, 0) (v, 1) ||
    decide (∃ u, st.nbr u = true ∧
      (crossPicked pick v u st.sim || ((recv u).map firstBit).getD false) = true)

/-- State update of `A_MVC`. -/
def mvcStep [Fintype V] (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B)
    (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (T : ℕ) (v : V) (st : SimState V σ)
    (recv : V → Option (Msg (3 * B))) : SimState V σ :=
  if st.round < T then
    { st with round := st.round + 1,
              sim := fun j => A.step (v, j) (st.sim j) (simRecv A v st.sim recv j) }
  else if st.round = T then
    { st with round := T + 1, inC := decideC pick v st recv }
  else st

/-- The MVC algorithm `A_MVC` of Lemma 3.2: `T` simulated rounds of `A` on `G_S`, then one round
in which `v` learns which cross edges at its copies were output by its neighbours, and computes
`v ∈ C_H`. -/
def mvcAlg [Fintype V] (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B)
    (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (T : ℕ) :
    Algorithm V (V → Bool) (SimState V σ) (3 * B) where
  init v nb := ⟨0, nb, fun i => A.init (v, i) (localInpS v nb i), false⟩
  send := mvcSend A pick T
  step := mvcStep A pick T
  out _ st := st.inC

lemma run_succ_eq {W I τ : Type*} {b : ℕ} (A' : Algorithm W I τ b) (G' : SimpleGraph W)
    [DecidableRel G'.Adj] (inp : W → I) (t : ℕ) (v : W) :
    A'.run G' inp (t + 1) v = A'.step v (A'.run G' inp t v)
      (fun w => if G'.Adj w v then some (A'.send w (A'.run G' inp t w) v) else none) := rfl

section
variable [Fintype V] (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B)
  (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (T : ℕ)

@[simp] lemma mvcAlg_step : (mvcAlg A pick T).step = mvcStep A pick T := rfl
@[simp] lemma mvcAlg_send : (mvcAlg A pick T).send = mvcSend A pick T := rfl
@[simp] lemma mvcAlg_out (v : V) (st : SimState V σ) : (mvcAlg A pick T).out v st = st.inC := rfl
@[simp] lemma mvcAlg_init (v : V) (nb : V → Bool) :
    (mvcAlg A pick T).init v nb = ⟨0, nb, fun i => A.init (v, i) (localInpS v nb i), false⟩ := rfl

end

variable [Fintype V] (A : Algorithm (V × Fin 3) (V × Fin 3 → Option ℕ) σ B)
  (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool) (T : ℕ)
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Simulation invariant: after `t ≤ T` rounds, `v` holds the states of `v₁, v₂, v₃` after `t`
rounds of `A` on `G_S`. -/
theorem mvcAlg_run_of_le : ∀ t ≤ T, ∀ v,
    ((mvcAlg A pick T).run G (nbrInput G) t v).round = t ∧
    ((mvcAlg A pick T).run G (nbrInput G) t v).nbr = nbrInput G v ∧
    ∀ i, ((mvcAlg A pick T).run G (nbrInput G) t v).sim i = A.run (GS G) (inpS G) t (v, i)
  | 0, _, v => by
    simp [Algorithm.run, localInpS_eq]
  | t + 1, ht, v => by
    have ih := mvcAlg_run_of_le t (by omega)
    obtain ⟨h1, h2, h3⟩ := ih v
    have hlt : ((mvcAlg A pick T).run G (nbrInput G) t v).round < T := by omega
    rw [run_succ_eq, mvcAlg_step, mvcStep, ite_eq_left hlt]
    refine ⟨by rw [h1], h2, fun j => ?_⟩
    simp only [h3, run_succ_eq, mvcAlg_send]
    congr 1
    funext ⟨w, i⟩
    simp only [simRecv]
    by_cases hw : w = v
    · subst hw
      simp only [ite_true, GS_adj_same, h3]
    · simp only [hw, ite_false, GS_adj_iff_idx hw]
      by_cases hG : G.Adj w v
      · have hlt' : ((mvcAlg A pick T).run G (nbrInput G) t w).round < T := by
          rw [(ih w).1]; omega
        simp only [hG, ite_true, Option.bind_some, true_and]
        cases hk : idx w v i j with
        | none => simp
        | some k =>
          have hs := src_idx hk
          simp only [Option.map_some, Option.isSome_some, ite_true, Option.some.injEq]
          rw [mvcSend, ite_eq_left hlt', chunk_bundle, hs, (ih w).2.2]
      · simp [hG]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Local characterisation of `C_H` for the union-of-outputs spanner `H`: `v ∈ C_H` iff one of
`v₁, v₂` output `{v₁, v₂}`, or for some neighbour `u` the cross edge between `v` and `u` was output
by the copy of `v` or by the copy of `u` on it. -/
lemma mem_CH_spannerOut_iff (st : V × Fin 3 → σ) (v : V) :
    v ∈ CH (spannerOut (GS G) pick st) ↔
      (picks pick (v, 0) (st (v, 0)) (v, 0) (v, 1) = true ∨
        picks pick (v, 1) (st (v, 1)) (v, 0) (v, 1) = true) ∨
      ∃ u, G.Adj v u ∧ (crossPicked pick v u (fun i => st (v, i)) = true ∨
        crossPicked pick u v (fun i => st (u, i)) = true) := by
  simp only [CH, Set.mem_ofPred_eq, spannerOut, picks, crossPicked, Bool.or_eq_true]
  constructor
  · rintro ⟨u, h | h⟩
    · by_cases hu : u = v
      · subst hu
        left; simp only [GS_adj_same] at h; tauto
      · right
        have hvu : v ≠ u := Ne.symm hu
        have h1 := (GS_adj_of_ne hvu).mp h.1
        have hlt : v < u := by rcases h1.2 with h' | h' | h' | h' <;> (simp at h'; try exact h')
        refine ⟨u, h1.1, ?_⟩
        simp only [src, hlt, ite_true, not_lt.mpr hlt.le, ite_false]
        tauto
    · by_cases hu : u = v
      · subst hu
        left; simp only [GS_adj_same] at h; tauto
      · right
        have h1 := (GS_adj_of_ne hu).mp h.1
        have hlt : u < v := by rcases h1.2 with h' | h' | h' | h' <;> (simp at h'; try exact h')
        refine ⟨u, h1.1.symm, ?_⟩
        simp only [src, hlt, ite_true, not_lt.mpr hlt.le, ite_false]
        tauto
  · rintro (h | ⟨u, hG, h⟩)
    · exact ⟨v, Or.inl ⟨GS_adj_same.mpr (by decide), by tauto⟩⟩
    · have hvu : v ≠ u := G.ne_of_adj hG
      rcases lt_or_gt_of_ne hvu with hlt | hlt
      · simp only [src, hlt, ite_true, not_lt.mpr hlt.le, ite_false] at h
        exact ⟨u, Or.inl ⟨(GS_adj_of_ne hvu).mpr ⟨hG, by simp [hlt]⟩, by tauto⟩⟩
      · simp only [src, hlt, ite_true, not_lt.mpr hlt.le, ite_false] at h
        exact ⟨u, Or.inr ⟨(GS_adj_of_ne (Ne.symm hvu)).mpr ⟨hG.symm, by simp [hlt]⟩, by tauto⟩⟩

/-- After `T + 1` rounds, `v` outputs `true` iff `v ∈ C_H`, where `H` is the spanner output by `A`
on `G_S` after `T` rounds. -/
theorem mvcAlg_inC (hB : 0 < B) (v : V) :
    ((mvcAlg A pick T).run G (nbrInput G) (T + 1) v).inC = true ↔
      v ∈ CH (spannerOut (GS G) pick (A.run (GS G) (inpS G) T)) := by
  have hrun := mvcAlg_run_of_le A pick T G T le_rfl
  obtain ⟨h1, h2, h3⟩ := hrun v
  rw [run_succ_eq, mvcAlg_step, mvcStep, ite_eq_right (by omega), ite_eq_left h1]
  simp only [decideC]
  have hsim : ((mvcAlg A pick T).run G (nbrInput G) T v).sim =
      fun i => A.run (GS G) (inpS G) T (v, i) := funext h3
  simp only [Bool.or_eq_true, decide_eq_true_eq, mem_CH_spannerOut_iff, h2, h3, hsim, nbrInput]
  refine or_congr Iff.rfl (exists_congr fun u => and_congr_right fun hG => or_congr_right ?_)
  have hu := hrun u
  have hu' : ¬ ((mvcAlg A pick T).run G (nbrInput G) T u).round < T := by omega
  have h3B : 0 < 3 * B := by omega
  have hsimu : ((mvcAlg A pick T).run G (nbrInput G) T u).sim =
      fun i => A.run (GS G) (inpS G) T (u, i) := funext hu.2.2
  simp only [G.adj_symm hG, ite_true, mvcAlg_send, mvcSend, hu', ite_false, Option.map_some,
    Option.getD_some, firstBit, h3B, dite_true, hsimu]

/-- **Lemma 3.2 of [CD18]** (with `3B`-bit messages and `T + 1` rounds). Let `A` be a
deterministic CONGEST algorithm on `G_S` (vertex set `V × Fin 3`, `B`-bit messages, `B > 0`)
which, for every graph `G` in the class `P`, outputs after `T` rounds an `α`-approximate
minimum-cost 2-spanner of `G_S` (as the union of the nodes' outputs). Then `A_MVC = mvcAlg A pick T`
is a CONGEST algorithm on `G` with `3B`-bit messages which, for every `G` in `P`, outputs after
`T + 1` rounds an `α`-approximate minimum vertex cover of `G`. -/
theorem lemma_3_2 (hB : 0 < B) (α : ℝ) (P : SimpleGraph V → Prop)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], P G →
      IsApproxMinSpanner wt α (GS G) (spannerOut (GS G) pick (A.run (GS G) (inpS G) T)))
    (hP : P G) :
    IsApproxMinVC α G
      {v | (mvcAlg A pick T).out v ((mvcAlg A pick T).run G (nbrInput G) (T + 1) v) = true} := by
  have : {v | (mvcAlg A pick T).out v ((mvcAlg A pick T).run G (nbrInput G) (T + 1) v) = true} =
      CH (spannerOut (GS G) pick (A.run (GS G) (inpS G) T)) := by
    ext v
    simp [mvcAlg_inC A pick T G hB]
  rw [this]
  exact approx_transfer (hA G hP)

/-! ### Splitting `kB`-bit messages into `k` rounds of `B`-bit messages -/

section Slow

-- CSLib candidate: generic slowdown of a CONGEST algorithm (Cslib.Congest).

variable {U I τ : Type*} {k b : ℕ}

/-- State of the slowed-down algorithm: the simulated state, the sub-round within the current
block of `k` rounds, and the `b`-bit chunks received so far in this block. -/
structure SlowState (U τ : Type*) (k b : ℕ) where
  /-- The simulated state. -/
  inner : τ
  /-- Sub-round within the current block (`< k`). -/
  phase : ℕ
  /-- Chunks received in the current block, per neighbour. -/
  buf : U → Fin k → Msg b

/-- The `c`-th `b`-bit chunk of a `k·b`-bit message. -/
def chunkK (c : Fin k) (m : Msg (k * b)) : Msg b := fun i => m (finProdFinEquiv (c, i))

/-- Sending in the slowed-down algorithm: the current chunk of the simulated message. -/
def slowSend (k : ℕ) [NeZero k] (A' : Algorithm U I τ (k * b)) (v : U) (st : SlowState U τ k b)
    (w : U) : Msg b :=
  chunkK ⟨st.phase % k, Nat.mod_lt _ (NeZero.pos k)⟩ (A'.send v st.inner w)

/-- State update of the slowed-down algorithm: store the received chunk; at the end of a block,
reassemble the messages and take the simulated step. -/
def slowStep (k : ℕ) (A' : Algorithm U I τ (k * b)) (v : U) (st : SlowState U τ k b)
    (recv : U → Option (Msg b)) : SlowState U τ k b :=
  let buf' : U → Fin k → Msg b := fun w c =>
    if c.val = st.phase then (recv w).getD (fun _ => false) else st.buf w c
  if st.phase + 1 < k then ⟨st.inner, st.phase + 1, buf'⟩
  else ⟨A'.step v st.inner
      (fun w => (recv w).map fun _ => fun n => buf' w (finProdFinEquiv.symm n).1
        (finProdFinEquiv.symm n).2), 0, fun _ _ _ => false⟩

/-- Simulate a CONGEST algorithm with `k·b`-bit messages by one with `b`-bit messages: every
round becomes a block of `k` rounds; in sub-round `c` the `c`-th chunk of each message is sent,
and at the end of the block the simulated step is taken. -/
def slow (k : ℕ) [NeZero k] (A' : Algorithm U I τ (k * b)) :
    Algorithm U I (SlowState U τ k b) b where
  init v i := ⟨A'.init v i, 0, fun _ _ _ => false⟩
  send := slowSend k A'
  step := slowStep k A'
  out v st := A'.out v st.inner

section
variable [NeZero k] (A' : Algorithm U I τ (k * b))
@[simp] lemma slow_send : (slow k A').send = slowSend k A' := rfl
@[simp] lemma slow_step : (slow k A').step = slowStep k A' := rfl
@[simp] lemma slow_out' (v : U) (st : SlowState U τ k b) : (slow k A').out v st = A'.out v st.inner :=
  rfl
@[simp] lemma slow_init (v : U) (i : I) :
    (slow k A').init v i = ⟨A'.init v i, 0, fun _ _ _ => false⟩ := rfl
end

variable [NeZero k] (A' : Algorithm U I τ (k * b)) (G' : SimpleGraph U) [DecidableRel G'.Adj]
  (inp : U → I)

/-- Invariant of `slow` after `k·t + j` rounds (`j < k`). -/
def SlowSpec (t j : ℕ) (v : U) : Prop :=
  ((slow k A').run G' inp (k * t + j) v).inner = A'.run G' inp t v ∧
  ((slow k A').run G' inp (k * t + j) v).phase = j ∧
  ∀ w, G'.Adj w v → ∀ c : Fin k, c.val < j →
    ((slow k A').run G' inp (k * t + j) v).buf w c = chunkK c (A'.send w (A'.run G' inp t w) v)

lemma slowSpec_succ {t j : ℕ} (hj : j + 1 < k) (h : ∀ v, SlowSpec A' G' inp t j v) (v : U) :
    SlowSpec A' G' inp t (j + 1) v := by
  obtain ⟨h1, h2, h3⟩ := h v
  unfold SlowSpec
  rw [← Nat.add_assoc, run_succ_eq, slow_step, slowStep]
  simp only [h2, hj, ite_true]
  refine ⟨h1, by simp, fun w hw c hc => ?_⟩
  simp only [hw, ite_true, Option.getD_some, slow_send, slowSend]
  split_ifs with hcj
  · obtain ⟨hw1, hw2, -⟩ := h w
    have : (⟨((slow k A').run G' inp (k * t + j) w).phase % k, Nat.mod_lt _ (NeZero.pos k)⟩ :
        Fin k) = c := by
      ext; simp only [hw2, hcj, Nat.mod_eq_of_lt (by omega : j < k)]
    rw [this, hw1]
  · exact h3 w hw c (by omega)

lemma slowSpec_block {t : ℕ} (h : ∀ v, SlowSpec A' G' inp t (k - 1) v) (v : U) :
    SlowSpec A' G' inp (t + 1) 0 v := by
  have hk := NeZero.pos k
  obtain ⟨h1, h2, h3⟩ := h v
  unfold SlowSpec
  have he : k * (t + 1) + 0 = k * t + (k - 1) + 1 := by rw [Nat.mul_succ]; omega
  rw [he, run_succ_eq, slow_step, slowStep]
  simp only [h2]
  rw [ite_eq_right (show ¬ (k - 1 + 1 < k) by omega)]
  refine ⟨?_, rfl, fun w _ c hc => absurd hc (Nat.not_lt_zero _)⟩
  rw [h1, run_succ_eq]
  dsimp only
  congr 1
  funext w
  by_cases hw : G'.Adj w v
  · simp only [hw, ite_true, Option.map_some, Option.getD_some, Option.some.injEq, slow_send,
      slowSend]
    funext n
    obtain ⟨hw1, hw2, -⟩ := h w
    split_ifs with hc
    · have : (⟨((slow k A').run G' inp (k * t + (k - 1)) w).phase % k,
          Nat.mod_lt _ (NeZero.pos k)⟩ : Fin k) = (finProdFinEquiv.symm n).1 := by
        ext; simp only [hw2, hc, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
      rw [this, hw1, chunkK, Prod.mk.eta, Equiv.apply_symm_apply]
    · rw [h3 w hw _ (by have := (finProdFinEquiv.symm n).1.isLt; omega), chunkK, Prod.mk.eta,
        Equiv.apply_symm_apply]
  · simp [hw]

/-- The slowed-down algorithm after `k·t` rounds holds the state of the original after `t`
rounds. -/
theorem slow_run (t : ℕ) (v : U) :
    ((slow k A').run G' inp (k * t) v).inner = A'.run G' inp t v := by
  have hk := NeZero.pos k
  have key : ∀ t, ∀ v, SlowSpec A' G' inp t 0 v := by
    intro t
    induction t with
    | zero => intro v; simp [SlowSpec, Algorithm.run]
    | succ t ih =>
      have hall : ∀ j, j < k → ∀ v, SlowSpec A' G' inp t j v := by
        intro j
        induction j with
        | zero => exact fun _ => ih
        | succ j ihj => exact fun hj => slowSpec_succ A' G' inp hj (ihj (by omega))
      exact slowSpec_block A' G' inp (hall (k - 1) (by omega))
  exact (key t v).1

/-- Outputs of the slowed-down algorithm after `k·t` rounds. -/
theorem slow_out (t : ℕ) (v : U) :
    (slow k A').out v ((slow k A').run G' inp (k * t) v) = A'.out v (A'.run G' inp t v) := by
  rw [slow_out', slow_run]

end Slow

/-- **Lemma 3.2 of [CD18]** (with `B`-bit messages and `3(T + 1)` rounds). Under the hypotheses
of `lemma_3_2`, the algorithm `slow 3 (mvcAlg A pick T)` with `B`-bit messages outputs, for every
`G` in `P`, an `α`-approximate minimum vertex cover of `G` after `3 (T + 1)` rounds. -/
theorem lemma_3_2_congest (hB : 0 < B) (α : ℝ) (P : SimpleGraph V → Prop)
    (hA : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], P G →
      IsApproxMinSpanner wt α (GS G) (spannerOut (GS G) pick (A.run (GS G) (inpS G) T)))
    (hP : P G) :
    IsApproxMinVC α G {v | (slow 3 (mvcAlg A pick T)).out v
      ((slow 3 (mvcAlg A pick T)).run G (nbrInput G) (3 * (T + 1)) v) = true} := by
  simp only [slow_out]
  exact lemma_3_2 A pick T G hB α P hA hP

/-! ### The extra round is needed

The paper says that, after the simulation, `C_H` is computed "without any communication". With
the output convention of the paper (every node outputs some of its incident edges, the spanner is
the union), node `v` does not know whether the cross edge `{v₁, u₂}` was output by `u₂`. The
natural communication-free variant — `v` evaluates the rule of `C_H` on the edges output by its
own copies (`ownCH`) — fails: on the triangle, the optimal 2-spanner `Hex` (all weight-0 edges and
the cross edge `{0₁, 2₂}`) can be output with the cross edge chosen by `0₁` (`pickA`) or by `2₂`
(`pickC`); `ownCH` is `{0}` resp. `{2}`, neither of which is a vertex cover. -/

/-- `C_H` evaluated by `v` on the edges output by its own copies only. -/
def ownCH (G : SimpleGraph V) (pick : V × Fin 3 → σ → V × Fin 3 → V × Fin 3 → Bool)
    (st : V × Fin 3 → σ) : Set V :=
  {v | ∃ u, ((GS G).Adj (v, 0) (u, 1) ∧ picks pick (v, 0) (st (v, 0)) (v, 0) (u, 1) = true) ∨
    ((GS G).Adj (u, 0) (v, 1) ∧ picks pick (v, 1) (st (v, 1)) (u, 0) (v, 1) = true)}

/-- The triangle. -/
abbrev K3 : SimpleGraph (Fin 3) := ⊤

/-- An optimal 2-spanner of `G_S` for the triangle: all weight-0 edges and the cross edge
`{0₁, 2₂}`. -/
def Hex : SimpleGraph (Fin 3 × Fin 3) where
  Adj x y := (GS K3).Adj x y ∧ (wtPair x y = 0 ∨ s(x, y) = s(((0 : Fin 3), (0 : Fin 3)), (2, 1)))
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [wtPair_comm, Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun x h => (GS K3).irrefl h.1⟩

instance : DecidableRel Hex.Adj := fun x y => by unfold Hex; infer_instance

/-- Selector: every node outputs its weight-0 edges, `0₁` also outputs `{0₁, 2₂}`. -/
def pickA : Fin 3 × Fin 3 → Unit → Fin 3 × Fin 3 → Fin 3 × Fin 3 → Bool := fun x _ a b =>
  decide (x = a ∧ (wtPair a b = 0 ∨ (a = (0, 0) ∧ b = (2, 1))))

/-- Selector: every node outputs its weight-0 edges, `2₂` also outputs `{0₁, 2₂}`. -/
def pickC : Fin 3 × Fin 3 → Unit → Fin 3 × Fin 3 → Fin 3 × Fin 3 → Bool := fun x _ a b =>
  decide (x = a ∧ (wtPair a b = 0 ∨ (a = (2, 1) ∧ b = (0, 0))))

lemma cost_Hex : cost Hex = 2 := by
  rw [cost, wcost_eq]
  decide +kernel

lemma isApproxMinSpanner_Hex : IsApproxMinSpanner wt 1 (GS K3) Hex := by
  have hsp : IsTwoSpanner (GS K3) Hex := ⟨fun _ _ h => h.1, by decide⟩
  refine ⟨hsp, fun H' hH' => ?_⟩
  have h1 : minSpannerCost K3 ≤ cost H' := iInf₂_le H' hH'
  rw [claim_3_1, SimpleGraph.vertexCoverNum_top] at h1
  have h0 : ENat.card (Fin 3) - 1 = 2 := by
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]; rfl
  rw [h0] at h1
  have h3 : 2 ≤ cost H' := by exact_mod_cast h1
  show (cost Hex : ℝ) ≤ 1 * cost H'
  rw [cost_Hex, one_mul]
  exact_mod_cast h3

/-- Counterexample to computing `C_H` "without any communication" (see above). Both selectors
output the same optimal 2-spanner `Hex`, but the sets computed from the nodes' own outputs are
`{0}` and `{2}`, which are not vertex covers of the triangle. -/
theorem localRule_counterexample :
    spannerOut (GS K3) pickA (fun _ => ()) = Hex ∧ spannerOut (GS K3) pickC (fun _ => ()) = Hex ∧
    IsApproxMinSpanner wt 1 (GS K3) Hex ∧
    ownCH K3 pickA (fun _ => ()) = {0} ∧ ownCH K3 pickC (fun _ => ()) = {2} ∧
    ¬ K3.IsVertexCover {0} ∧ ¬ K3.IsVertexCover {2} := by
  refine ⟨?_, ?_, isApproxMinSpanner_Hex, ?_, ?_, ?_, ?_⟩
  · ext x y; revert x y; decide
  · ext x y; revert x y; decide
  · ext v; simp only [ownCH, Set.mem_ofPred_eq, Set.mem_singleton_iff]; revert v; decide
  · ext v; simp only [ownCH, Set.mem_ofPred_eq, Set.mem_singleton_iff]; revert v; decide
  · intro h; have := @h 1 2 (by decide); simp at this
  · intro h; have := @h 0 1 (by decide); simp at this

end Podc.SpannerApproximation
