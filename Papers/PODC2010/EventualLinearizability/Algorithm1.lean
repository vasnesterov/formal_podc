import Papers.PODC2010.EventualLinearizability.Theorem1
import Papers.PODC2010.EventualLinearizability.Layer

/-!
# Algorithm 1 is not weakly consistent over Eventual Consensus

Algorithm 1 of the paper (the sufficiency part of Theorem 3): on `invoke(o)`, a process sets
`curr ← o` and submits `o` to the consistency layer; on `deliver(H)`, if `curr ∈ H` it completes
`curr` with the result of executing `H` up to and including `curr`.

We model Algorithm 1 for an arbitrary deterministic object (`alg1`): a run is a list of
low-level input events (high-level invocations and layer deliveries, one per time unit,
the `k`-th event at time `k + 1`); operations are identified by the order of their
invocations; `alg1` produces the high-level history, and `layerOf` the consistency-layer run
(`S(i, t)` = last sequence delivered to `p_i` by time `t`, submission = invocation).

**Counterexample** (`algorithm1_not_weaklyConsistent`). Swap register, initially `0`:

```
1  p1 invokes x = swap(1)       (submitted)
2  p0 invokes o' = read         (submitted)
3  deliver [x] to p1            x returns 0
4  deliver [x, o'] to p0        o' returns 1
5  p0 invokes o = read          (submitted)
6  deliver [o, x, o'] to p0     o returns 0     (set stability allows reordering)
7  deliver [o, x, o'] to p1
8  deliver [o, x, o'] to p2
```

The layer run satisfies Eventual Consensus (stable from time 7 on, common prefix
`[o, x, o']` from time 8 on, all processes correct). The high-level history is not weakly
consistent: `τ(p0, o')` must contain `x` (the only `swap(1)`), so `τ(p0, o)` contains `x`
before `o`, and `o` must return `1`, not `0`. The paper's claim "Weak consistency directly
derives from the set stability and nontriviality properties" (proof of Lemma 6) overlooks that
set stability allows operations observed earlier to be reordered *after* the new operation.
-/

namespace Podc.EventualLinearizability

open Cslib.SharedMemory.HerlihyWing

/-! ### Algorithm 1 -/

/-- Low-level input events: a high-level invocation, or a delivery of the consistency layer
(operations are identified by the index of their invocation in the run). -/
inductive Input (P Op : Type) where
  | invoke (i : P) (op : Op)
  | deliver (i : P) (s : List ℕ)

section Alg

variable {P Op Res State : Type} [DecidableEq P]

/-- The configuration of Algorithm 1: the current operation of each process, the operations
invoked so far (operation `n` is the `n`-th entry), and the high-level history so far. -/
structure Alg1Cfg (P Op Res : Type) where
  curr : P → Option ℕ
  ops : List (P × Op)
  hist : History P Unit Op Res

/-- `execute(o, H)`: the result of `o` when the sequence `s` is executed up to and including
`o`. -/
def execute (δ : State → Op → State × Res) (q₀ : State) (opOf : ℕ → Op) (c : ℕ)
    (s : List ℕ) : Res :=
  (δ ((s.takeWhile (· ≠ c)).foldl (fun q n => (δ q (opOf n)).1) q₀) (opOf c)).2

/-- One step of Algorithm 1. -/
def alg1Step (δ : State → Op → State × Res) (q₀ : State) [Inhabited Op]
    (C : Alg1Cfg P Op Res) : Input P Op → Alg1Cfg P Op Res
  | .invoke i op =>
    { curr := Function.update C.curr i (some C.ops.length)
      ops := C.ops ++ [(i, op)]
      hist := C.hist ++ [.inv i () op] }
  | .deliver i s =>
    match C.curr i with
    | some c =>
      if c ∈ s then
        { C with
          curr := Function.update C.curr i none
          hist := C.hist ++
            [.res i () (execute δ q₀ (fun n => ((C.ops[n]?).map Prod.snd).getD default) c s)] }
      else C
    | none => C

/-- The configuration after running Algorithm 1 on a list of inputs. -/
def alg1 (δ : State → Op → State × Res) (q₀ : State) [Inhabited Op] (tr : List (Input P Op)) :
    Alg1Cfg P Op Res :=
  tr.foldl (alg1Step δ q₀) ⟨fun _ => none, [], []⟩

/-- The consistency-layer run of a list of inputs (the `k`-th input happens at time `k + 1`):
`S(i, t)` is the last sequence delivered to `p_i` among the first `t` inputs, and operation `n`
is submitted by its invoker at the time of its invocation. -/
def layerOf (tr : List (Input P Op)) (correct : Set P) : LayerRun P ℕ where
  S i t := ((tr.take t).filterMap fun
    | .deliver j s => if j = i then some s else none
    | .invoke .. => none).getLastD []
  sub n := ((tr.zipIdx 1).filterMap fun
    | (.invoke j _, k) => some (j, k)
    | (.deliver .., _) => none)[n]?
  correct := correct

end Alg

/-! ### The counterexample -/

instance : Inhabited SwapOp := ⟨.read⟩

/-- The run of the counterexample. -/
def tr₁ : List (Input (Fin 3) SwapOp) :=
  [.invoke 1 (.swap 1), .invoke 0 .read, .deliver 1 [0], .deliver 0 [0, 1], .invoke 0 .read,
   .deliver 0 [2, 0, 1], .deliver 1 [2, 0, 1], .deliver 2 [2, 0, 1]]

/-- Its layer run (all processes correct). -/
def R₁ : LayerRun (Fin 3) ℕ := layerOf tr₁ Set.univ

/-- The high-level history produced by Algorithm 1. -/
def Halg : History (Fin 3) Unit SwapOp ℕ := (alg1 swapδ 0 tr₁).hist

lemma Halg_eq : Halg = [.inv 1 () (.swap 1), .inv 0 () .read, .res 1 () 0, .res 0 () 1,
    .inv 0 () .read, .res 0 () 0] := by decide

/-! #### The layer run satisfies Eventual Consensus -/

lemma R₁_S_eq (i : Fin 3) (t : ℕ) : R₁.S i t = R₁.S i (min t 8) := by
  simp only [R₁, layerOf]
  congr 2
  rcases le_total t 8 with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_of_length_le (by simp [tr₁]; omega),
      List.take_of_length_le (by simp [tr₁])]

lemma R₁_sub (n : ℕ) : R₁.sub n = [((1 : Fin 3), 1), (0, 2), (0, 5)][n]? := by
  simp only [R₁, layerOf]; congr 1

/-- The common prefixes. -/
def P₁ (t : ℕ) : List ℕ := if 8 ≤ t then [2, 0, 1] else []

lemma R₁_eventualConsensus : R₁.EventualConsensus ∧ R₁.StableFrom 7 := by
  have hS := R₁_S_eq
  have hstab : R₁.StableFrom 7 := by
    intro i t' t'' h1 h2
    rw [hS i t', hS i t'']
    have : ∀ i : Fin 3, ∀ a ∈ List.range 9, ∀ b ∈ List.range 9, 7 ≤ a → a ≤ b →
        R₁.S i a <+: R₁.S i b := by decide
    exact this i _ (by simp) _ (by simp) (by omega) (by omega)
  refine ⟨⟨⟨fun i => by decide +revert, ?_, ?_, P₁, ?_, ?_, ?_⟩, 7, hstab⟩, hstab⟩
  · intro i t
    rw [hS i t]
    have : ∀ i : Fin 3, ∀ a ∈ List.range 9, (∀ o ∈ R₁.S i a, ∃ p ∈ [((1 : Fin 3), 1), (0, 2), (0, 5)][o]?,
        p.2 ≤ a) ∧ (R₁.S i a).Nodup := by decide
    obtain ⟨h1, h2⟩ := this i (min t 8) (by simp)
    refine ⟨fun o ho => ?_, h2⟩
    obtain ⟨⟨j, t'⟩, hp, hle⟩ := h1 o ho
    exact ⟨j, t', by rw [R₁_sub]; simpa using hp, by simp at hle; omega⟩
  · intro i t t' h o ho
    rw [hS] at ho ⊢
    have : ∀ i : Fin 3, ∀ a ∈ List.range 9, ∀ b ∈ List.range 9, a ≤ b → ∀ o ∈ R₁.S i a,
        o ∈ R₁.S i b := by decide
    exact this i _ (by simp) _ (by simp) (by omega) o ho
  · intro i _ t t' h
    rw [hS i t']
    simp only [P₁]
    split_ifs with h8
    · have : ∀ i : Fin 3, [2, 0, 1] <+: R₁.S i 8 := by decide
      rw [min_eq_right (by omega)]; exact this i
    · exact List.nil_prefix
  · intro t t' h
    simp only [P₁]
    split_ifs <;> first | exact List.prefix_refl _ | exact List.nil_prefix | omega
  · intro o j t' ho _
    rw [R₁_sub] at ho
    refine ⟨max t' 8, le_max_left _ _, ?_⟩
    simp only [P₁, le_max_right, ↓reduceIte]
    rcases o with _ | _ | _ | o <;> simp_all

/-! #### The high-level history is not weakly consistent -/

def ax : OpId (Fin 3) Unit := ⟨1, (), 0⟩
def ao' : OpId (Fin 3) Unit := ⟨0, (), 0⟩
def ao : OpId (Fin 3) Unit := ⟨0, (), 1⟩

/-- All operations of `Halg`. -/
def V : List (OpId (Fin 3) Unit) := [ax, ao', ao]

lemma invoked_Halg {a : OpId (Fin 3) Unit} (h : Invoked Halg a) : a ∈ V := by
  rcases a with ⟨p, x, k⟩
  have hlen : (opsOf Halg p x).length ≤ 6 :=
    (List.length_filterMap_le _ _).trans (by rw [Halg_eq]; simp)
  have hk : k < 7 := by simp only [Invoked] at h; omega
  have : ∀ p : Fin 3, ∀ k < 7, Invoked Halg ⟨p, (), k⟩ → (⟨p, (), k⟩ : OpId (Fin 3) Unit) ∈ V := by
    rw [Halg_eq]; decide
  exact this p k hk h

/-- The operation of an identity in `Halg`. -/
def opV (a : OpId (Fin 3) Unit) : SwapOp := (opOf Halg a).getD .read

lemma eq_fill_of_isSeqOf_alg {L : IdSeq (Fin 3) Unit SwapOp ℕ} (hL : IsSeqOf swapSpec Halg L) :
    L = fillWith opV 0 L.ids ∧ L.ids ⊆ V := by
  have hof : ∀ ae ∈ L, ae.2.p = ae.1.p ∧ ae.2.o = opV ae.1 ∧ ae.1 ∈ V := by
    intro ae hae
    obtain ⟨h1, -, h3⟩ := hL.ofHist ae hae
    exact ⟨h1, by simp [opV, h3], invoked_Halg (Invoked.of_opOf h3)⟩
  refine ⟨eq_fillWith (fun ae hae => ⟨(hof ae hae).1, (hof ae hae).2.1⟩)
    (legal_swap_iff.1 hL.legal), ?_⟩
  intro a ha
  obtain ⟨ae, hae, rfl⟩ := List.mem_map.1 ha
  exact (hof ae hae).2.2

set_option maxRecDepth 100000 in
lemma alg_core : ∀ π ∈ V.sublists.flatMap List.permutations',
    ((fillWith opV 0 π).getLast?.map (fun ae => (ae.1, ae.2.r)) = some (ao', 1) → ax ∈ π) ∧
    ((fillWith opV 0 π).getLast?.map (fun ae => (ae.1, ae.2.r)) = some (ao, 0) → ax ∉ π) := by
  decide +kernel

lemma not_weaklyConsistent_Halg : ¬ WeaklyConsistent swapSpec Halg := by
  rintro ⟨τ, hτ⟩
  obtain ⟨hs1, ⟨e1, hl1, hr1⟩, -, -⟩ := hτ ao' (by rw [Halg_eq]; decide)
  obtain ⟨hs2, ⟨e2, hl2, hr2⟩, -, hiii⟩ := hτ ao (by rw [Halg_eq]; decide)
  obtain ⟨hf1, hsub1⟩ := eq_fill_of_isSeqOf_alg hs1
  obtain ⟨hf2, hsub2⟩ := eq_fill_of_isSeqOf_alg hs2
  have hr1' : e1.r = 1 := by
    rw [(by rw [Halg_eq]; decide : resOf Halg ao' = some 1)] at hr1
    exact (Option.some.inj hr1).symm
  have hr2' : e2.r = 0 := by
    rw [(by rw [Halg_eq]; decide : resOf Halg ao = some 0)] at hr2
    exact (Option.some.inj hr2).symm
  have hx : ax ∈ (τ ao').ids := by
    refine (alg_core _ (mem_sublists_permutations hs1.nodup hsub1)).1 ?_
    rw [← hf1, hl1]; simp [hr1']
  have hprec : Precedes Halg ao' ao := by rw [Halg_eq]; decide
  have hx' := hiii ao' rfl hprec ax hx
  refine (alg_core _ (mem_sublists_permutations hs2.nodup hsub2)).2 ?_ hx'
  rw [← hf2, hl2]; simp [hr2']

/-- **Algorithm 1 is not weakly consistent over an Eventual Consensus layer.** In the run
`tr₁`, the consistency layer satisfies Eventual Consensus (all processes correct, stable from
time 7), but the history produced by Algorithm 1 is not weakly consistent; hence Algorithm 1
is not an eventually linearizable implementation, contrary to the sufficiency part of
Theorem 3 (Lemma 6). -/
theorem algorithm1_not_weaklyConsistent :
    R₁.EventualConsensus ∧ R₁.correct = Set.univ ∧
      ¬ WeaklyConsistent swapSpec (alg1 swapδ 0 tr₁).hist :=
  ⟨R₁_eventualConsensus.1, rfl, not_weaklyConsistent_Halg⟩

end Podc.EventualLinearizability
