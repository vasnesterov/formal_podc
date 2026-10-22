import Papers.PODC2019.CRDTReplication.Statements
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases

/-!
# A counterexample execution of Algorithm 2

Algorithm 2 as written (`Variant.paper`) for the G-set over two updates `u₁ = 0`, `u₂ = 1`,
five processes `p₀, …, p₄` (each a proposer and an acceptor) and majority quorums (`QS5`). The
execution `run` (asynchronous, no crashes; some messages are still in transit at the end):

1. Query `C` at `p₂` sends an incremental `PREPARE`; it reaches `p₀, p₁, p₃, p₄`, which move to
   round `(1, C)`. (`C` never returns; it only advances the round numbers.)
2. Query `A` at `p₀` sends an incremental `PREPARE`; it reaches `p₀, p₁`, which move to round
   `(2, A)` and answer `ACK((2, A), ∅)` (these ACKs stay in transit for now).
3. Update `u₁` at `p₄`: `MERGE({u₁})` reaches `p₀, p₁, p₂`; `u₁` completes.
4. Query `B` at `p₁` sends an incremental `PREPARE`; `p₀, p₁` move to round `(3, B)`, `p₂` to
   `(1, B)`; all three answer with state `{u₁}`, so `B` learns `{u₁}` **by consistent quorum**
   and returns `{u₁}`.
5. Update `u₂` is invoked at `p₃` (only applied locally; its `MERGE`s stay in transit).
6. `A`'s `PREPARE` reaches `p₂, p₃, p₄`, which move to round `(2, A)`. `A` now receives the old
   `ACK((2, A), ∅)` from `p₀, p₁` and `ACK((2, A), {u₂})` from `p₃`: a quorum, all in round
   `(2, A)` but with different states, so `A` sends `VOTE((2, A), {u₂})`.
7. `p₂, p₃, p₄` are still in round `(2, A)` and answer `VOTED` (although `p₂` and `p₄` hold
   `u₁ ∉ {u₂}`), so `A` learns `{u₂}` **by vote** and returns `{u₂}`.

Hence the learned states `{u₁}` (by consistent quorum) and `{u₂}` are incomparable
(`lemma3_false`, `theorem3_false`); `u₁` precedes `u₂` in real time but the learned `{u₂}` does
not contain `u₁` (`theorem4_false`); and the history (`B` returns `{u₁}` after `u₁` completed,
`A` returns `{u₂}` after `u₂` was invoked, which is after `u₁` completed) has no linearization
(`runHist_not_linearizable`, `not_linearizable`, `linearizableClaim_false`).
-/

namespace Podc.CRDTReplication.Cex

open Cslib.SharedMemory Cslib.AsyncMP Podc.CRDTReplication

/-- The G-set over two update identifiers `0` (`u₁`) and `1` (`u₂`). -/
abbrev G := gset (Fin 2)

/-- Majority quorums of five processes. -/
def QS5 : Finset (Finset (Fin 5)) := Finset.univ.powerset.filter fun Q => Q.card = 3

/-- Algorithm 2 for the G-set, five processes, majority quorums. -/
abbrev alg5 := alg (P := Fin 5) (D := G) Variant.paper QS5

/-- Steps of `alg5`. -/
abbrev St := Step (Fin 5) G.spec (Msg (Fin 5) G) Act

/-- Attempt id of query `A` (first operation of `p₀`). -/
def iA : Rid (Fin 5) := (0, 0, 0)
/-- Attempt id of query `B` (first operation of `p₁`). -/
def iB : Rid (Fin 5) := (1, 0, 0)
/-- Attempt id of query `C` (first operation of `p₂`). -/
def iC : Rid (Fin 5) := (2, 0, 0)

/-- The empty G-set state. -/
def e : Finset (Fin 2) := ∅

/-- The counterexample execution (see the module docstring). -/
def run : List St :=
  [ -- query C at p₂: its PREPARE reaches p₀, p₁, p₃, p₄
    .inv 2 (.qry ()),
    .recv 2 0 (.prepare iC none e), .recv 2 1 (.prepare iC none e),
    .recv 2 3 (.prepare iC none e), .recv 2 4 (.prepare iC none e),
    -- query A at p₀: its PREPARE reaches p₀, p₁
    .inv 0 (.qry ()),
    .recv 0 0 (.prepare iA none e), .recv 0 1 (.prepare iA none e),
    -- update u₁ at p₄, merged at p₀, p₁, p₂; completes
    .inv 4 (.upd 0),
    .recv 4 0 (.merge 0 {0}), .recv 4 1 (.merge 0 {0}), .recv 4 2 (.merge 0 {0}),
    .recv 0 4 (.merged 0), .recv 1 4 (.merged 0), .recv 2 4 (.merged 0),
    .internal 4 .advance,
    -- query B at p₁ learns {u₁} by consistent quorum {p₀, p₁, p₂}
    .inv 1 (.qry ()),
    .recv 1 0 (.prepare iB none e), .recv 1 1 (.prepare iB none e),
    .recv 1 2 (.prepare iB none e),
    .recv 0 1 (.ack 3 iB {0}), .recv 1 1 (.ack 3 iB {0}), .recv 2 1 (.ack 1 iB {0}),
    .internal 1 .advance,
    -- update u₂ at p₃ (its MERGE messages stay in transit)
    .inv 3 (.upd 1),
    -- A's PREPARE reaches p₂, p₃, p₄
    .recv 0 2 (.prepare iA none e), .recv 0 3 (.prepare iA none e),
    .recv 0 4 (.prepare iA none e),
    -- A receives ACKs from p₀, p₁, p₃ (all in round (2, iA)) and proposes {u₂}
    .recv 0 0 (.ack 2 iA e), .recv 1 0 (.ack 2 iA e), .recv 3 0 (.ack 2 iA {1}),
    .internal 0 .advance,
    -- p₂, p₃, p₄ are still in round (2, iA) and vote
    .recv 0 2 (.vote 2 iA {1}), .recv 0 3 (.vote 2 iA {1}), .recv 0 4 (.vote 2 iA {1}),
    .recv 2 0 (.voted 2 iA {1}), .recv 3 0 (.voted 2 iA {1}), .recv 4 0 (.voted 2 iA {1}),
    .internal 0 .advance ]

/-- The history of `run`: `C` (pending), `A` (returns `{u₂}`), `u₁ = (4, 0)` (completes),
`B = (1, 0)` (returns `{u₁}`), `u₂ = (3, 0)` (pending). -/
def runHist : List (Label (Fin 5) G.spec) :=
  [.inv 2 (.qry ()), .inv 0 (.qry ()), .inv 4 (.upd 0), .ret 4 .done, .inv 1 (.qry ()),
   .ret 1 (.val {0}), .inv 3 (.upd 1), .ret 0 (.val {1})]

set_option maxRecDepth 100000 in
/-- `run` is an execution of `alg5` with history `runHist`; `B` learned `{u₁}` by consistent
quorum and `A` learned `{u₂}` by vote. -/
theorem run_spec : ∃ C, alg5.runFrom alg5.initCfg run = some (C, runHist) ∧
    (C.loc 1).learned 0 = some ({0}, false) ∧ (C.loc 0).learned 0 = some ({1}, true) :=
  by refine ⟨_, rfl, ?_, ?_⟩ <;> rfl

/-- Majority quorums of five processes form a quorum system. -/
theorem qs5_isQuorumSystem : IsQuorumSystem QS5 := by
  unfold IsQuorumSystem QS5; decide

/-- The final configuration of `run` is reachable with history `runHist`; in it, query `B`
(operation `(1, 0)`) learned `{u₁}` by consistent quorum and query `A` (operation `(0, 0)`)
learned `{u₂}` by vote. -/
theorem run_reach : ∃ C, alg5.Reach C runHist ∧ (C.loc 1).learned 0 = some ({0}, false) ∧
    (C.loc 0).learned 0 = some ({1}, true) := by
  obtain ⟨C, hrun, h1, h0⟩ := run_spec
  exact ⟨C, by simpa using Protocol.runFrom_reach Protocol.Reach.init hrun, h1, h0⟩

/-- `{u₁}` and `{u₂}` are incomparable. -/
lemma not_comparable : ¬ Comparable ({0} : Finset (Fin 2)) {1} := by
  unfold Comparable; decide

/-- **Lemma 3 is false**: `{u₁}` (learned by consistent quorum) and `{u₂}` are incomparable. -/
theorem lemma3_false : ¬ Lemma3 (Variant.paper (D := G)) QS5 := by
  intro h
  obtain ⟨C, hC, h1, h0⟩ := run_reach
  exact not_comparable (h C _ hC _ _ ⟨(1, 0), h1⟩ ⟨(0, 0), by simp [learnedOf, h0]⟩)

/-- **Theorem 3 (Consistency) is false**: two incomparable states are learned. -/
theorem theorem3_false : ¬ Theorem3 (Variant.paper (D := G)) QS5 := by
  intro h
  obtain ⟨C, hC, h1, h0⟩ := run_reach
  exact not_comparable
    (h C _ hC _ _ ⟨(1, 0), by simp [learnedOf, h1]⟩ ⟨(0, 0), by simp [learnedOf, h0]⟩)

/-- The operations invoked by each process in `runHist`. -/
lemma opsOf_runHist (p : Fin 5) : opsOf runHist p =
    if p = 3 then [.upd 1] else if p = 4 then [.upd 0] else [.qry ()] := by
  fin_cases p <;> rfl

/-- The update operations of `runHist`: `u₁` is `(4, 0)` and `u₂` is `(3, 0)`. -/
lemma opOf_runHist_upd {y : OpId (Fin 5)} {u : Fin 2}
    (h : opOf runHist y = some (.upd u)) : (y = (4, 0) ∧ u = 0) ∨ (y = (3, 0) ∧ u = 1) := by
  obtain ⟨p, k⟩ := y
  simp only [opOf, opsOf_runHist] at h
  fin_cases p <;> rcases k with _ | k <;> cases h <;> simp

/-- Update identifiers are unique in `runHist`. -/
lemma uniqueUpd_runHist : UniqueUpd (D := G) runHist := by
  intro x y u hx hy
  rcases opOf_runHist_upd hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases opOf_runHist_upd hy with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp_all

/-- `u₁` completes before `u₂` is invoked. -/
lemma precedes_runHist : Precedes runHist (4, 0) (3, 0) :=
  ⟨[.inv 2 (.qry ()), .inv 0 (.qry ()), .inv 4 (.upd 0), .ret 4 .done],
    [.inv 1 (.qry ()), .ret 1 (.val {0}), .inv 3 (.upd 1), .ret 0 (.val {1})], rfl,
    by unfold Completed; decide, by unfold Invoked; decide⟩

/-- **Theorem 4 (Update Stability) is false**: `u₁` precedes `u₂`, but the learned state `{u₂}`
does not include `u₁`. -/
theorem theorem4_false : ¬ Theorem4 (Variant.paper (D := G)) QS5 (gsetHistory (Fin 2)) := by
  intro h
  obtain ⟨C, hC, -, h0⟩ := run_reach
  have := h C _ hC uniqueUpd_runHist (4, 0) (3, 0) 0 1 {1} precedes_runHist rfl rfl
    ⟨(0, 0), by simp [learnedOf, h0]⟩ (by simp [gsetHistory])
  simp [gsetHistory] at this

/-! ## The history `runHist` is not linearizable -/


/-- In the G-set, the state `r` reached from `q` by a list of commands contains `u` iff `q`
does or `u` is one of the update commands. -/
lemma gset_mem_runOps {U : Type} [DecidableEq U] (q : Finset U)
    (os : List (CRDT.Cmd (gset U))) (u : U) (r : Finset U)
    (hr : (gset U).spec.runOps q os = r) : u ∈ r ↔ u ∈ q ∨ CRDT.Cmd.upd u ∈ os := by
  induction os generalizing q with
  | nil => subst hr; simp only [List.not_mem_nil, or_false]; exact Iff.rfl
  | cons o os ih =>
    cases o with
    | upd v =>
      rw [ih (insert v q) hr]
      simp only [List.mem_cons, Finset.mem_insert, CRDT.Cmd.upd.injEq]
      tauto
    | qry _ =>
      rw [ih q hr]
      simp

/-- In a sequential G-set history, a query at `x` returns exactly the set of the update
commands placed before `x`. -/
lemma gset_respIn_qry {U K : Type} [DecidableEq U] [DecidableEq K]
    {L : List (K × (gset U).spec.Op)} {x : K} {r : Finset U}
    (h : (gset U).spec.respIn (gset U).spec.init L x = some (.val r))
    (hx : ∀ o, (x, o) ∈ L → o = .qry ()) :
    ∃ L₁ L₂, L = L₁ ++ (x, .qry ()) :: L₂ ∧ ∀ u, u ∈ r ↔ CRDT.Cmd.upd u ∈ L₁.map Prod.snd := by
  obtain ⟨L₁, L₂, o, hs, hr⟩ := ObjSpec.exists_split_of_respIn_eq_some h
  have ho : o = .qry () := hx o (hs ▸ List.mem_append_right _ List.mem_cons_self)
  subst ho
  refine ⟨L₁, L₂, hs, fun u => ?_⟩
  have hr' : (gset U).spec.runOps (∅ : Finset U) (L₁.map Prod.snd) = r := CRDT.Res.val.inj hr
  exact (gset_mem_runOps ∅ _ u r hr').trans (by simp only [Finset.notMem_empty, false_or])

/-- If `[a, b]` is a sublist of `l₁ ++ l₂` (without duplicates) and `b ∈ l₁`, then `a ∈ l₁`. -/
lemma mem_left_of_sublist_pair {α : Type} {a b : α} {l₁ l₂ : List α}
    (h : [a, b].Sublist (l₁ ++ l₂)) (hb : b ∈ l₁) (hnd : (l₁ ++ l₂).Nodup) : a ∈ l₁ := by
  obtain ⟨r₁, r₂, he, h1, h2⟩ := List.sublist_append_iff.1 h
  rcases r₁ with _ | ⟨c, _ | ⟨d, r₁⟩⟩
  · simp only [List.nil_append] at he
    subst he
    exact absurd (h2.subset (by simp)) (List.disjoint_of_nodup_append hnd hb)
  · simp only [List.singleton_append, List.cons.injEq] at he
    exact he.1 ▸ h1.subset (by simp)
  · simp only [List.cons_append, List.cons.injEq] at he
    exact he.1 ▸ h1.subset (by simp)

/-- The history `runHist` has no linearization: `A` returns `{u₂}`, so `u₂` precedes `A` in any
linearization; by real time `u₁` precedes `u₂`, hence `A`, so `A` would have to return a set
containing `u₁`. -/
theorem runHist_not_linearizable : ¬ ∃ L, IsLinearization runHist L := by
  rintro ⟨L, hL⟩
  obtain ⟨L₁, L₂, hs, hr⟩ := gset_respIn_qry
    (hL.respIn_eq (x := (0, 0)) (r := .val {1}) rfl) (fun o ho => by
      have := hL.op_eq _ ho
      exact Option.some.inj (this.symm.trans rfl))
  -- `u₂ = (3, 0)` is placed before `A` ...
  obtain ⟨⟨y, o⟩, hy, ho⟩ := List.mem_map.1 ((hr 1).1 (by simp))
  simp only at ho
  subst ho
  have hy3 : y = (3, 0) := by
    rcases opOf_runHist_upd (hL.op_eq _ (by rw [hs]; exact List.mem_append_left _ hy)) with
      h | h <;> simp_all
  subst hy3
  -- ... hence so is `u₁ = (4, 0)` ...
  have hmap : L.map Prod.fst = L₁.map Prod.fst ++ ((0, 0) :: L₂.map Prod.fst) := by
    rw [hs, List.map_append, List.map_cons]
  have h4 : ((4, 0) : OpId (Fin 5)) ∈ L₁.map Prod.fst := by
    have hsub := hL.realtime _ _ precedes_runHist (by rw [hmap]; simp [List.mem_map.2 ⟨_, hy, rfl⟩])
    rw [hmap] at hsub
    exact mem_left_of_sublist_pair hsub (List.mem_map.2 ⟨_, hy, rfl⟩) (hmap ▸ hL.nodup)
  obtain ⟨⟨z, o'⟩, hz, hzo⟩ := List.mem_map.1 h4
  simp only at hzo
  subst hzo
  have ho' : o' = .upd 0 := by
    have := hL.op_eq _ (by rw [hs]; exact List.mem_append_left _ hz)
    exact (Option.some.inj (this.symm.trans rfl))
  subst ho'
  -- ... so `A`'s response contains `u₁`.
  have := (hr 0).2 (List.mem_map.2 ⟨_, hz, rfl⟩)
  simp at this

/-- **Algorithm 2 is not linearizable** (for the G-set over two updates, five processes and
majority quorums). -/
theorem not_linearizable : ¬ alg5.Linearizable := by
  intro h
  obtain ⟨C, hC, -⟩ := run_reach
  exact runHist_not_linearizable (h C _ hC)

/-- **The main claim of Section III-E is false**: the history `runHist` has unique update
identifiers and no linearization. -/
theorem linearizableClaim_false : ¬ LinearizableClaim (Variant.paper (D := G)) QS5 := by
  intro h
  obtain ⟨C, hC, -⟩ := run_reach
  exact runHist_not_linearizable (h C _ hC uniqueUpd_runHist)

end Podc.CRDTReplication.Cex
