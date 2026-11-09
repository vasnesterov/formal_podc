/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Protocol
import Papers.PODC2019.ReconfigurableCommit.LemmaA3

/-!
# Theorem 4.1 fails if line 56 of Figure 1 is read without a check

Line 56 of Figure 1 reads `when received NEW_CONFIG(new_epoch, M)`. By the paper's convention
(state variables in message patterns are matched, cf. lines 45, 51 and the "checks in lines 141
and 148" of App. C) this only accepts the message epoch `new_epoch`, and the execution below is
blocked at the late `NEW_CONFIG(1)`. If the pattern is read as a binder (`NEW_CONFIG(e, M)`, as
line 58's `e` suggests), the handler has no precondition. A late `NEW_CONFIG(1)` can
therefore reach a process that has meanwhile become the leader of epoch `2`: it moves *back* to
epoch `1` (contradicting "epoch[s] never decreases" and Invariant 3, whose proof cites "the checks
in lines 56 and 62") and revives the abandoned configuration of epoch `1`, while epoch `3`
(introduced from epoch `2`) is active as well. Two conflicting transactions then commit, one in
each configuration.

The execution uses one shard, four processes `a b c d` (`0 1 2 3`) and FIFO delivery only:

* initial configuration (epoch 0): `{a, b}`, leader `a`;
* `c` reconfigures: probes `{a, b}`, both reply, `c` installs epoch 1 = `{a, b}` (leader `a`) and
  sends `NEW_CONFIG(1)` to `a`, which is delayed;
* `d` reconfigures: probes `{a, b}` with `PROBE(2)`; `a` replies (its `PROBE(2)` to `b` is
  delayed); `d` installs epoch 2 = `{a, c}` (`c` fresh), `a` becomes leader of 2, `c` its follower;
* the delayed `NEW_CONFIG(1)` reaches `a`: `a` becomes leader of epoch 1 again and initializes `b`;
* `d` reconfigures again: probes `{a, c}` with `PROBE(3)`; `c` replies; `d` installs epoch 3 =
  `{c, d}` (`d` fresh), `c` leads it, `d` follows;
* `b` certifies `t₁` (leader `a`, epoch 1, follower `b`), `d` certifies `t₂` (leader `c`, epoch 3,
  follower `d`); both commit although they conflict (both read `x` and overwrite it).
-/

namespace Podc.ReconfigurableCommit

namespace Line56

/-- One shard, payloads `Bool`: `true` reads object `x` at version 0 and writes version 1, `false`
is the empty payload `ε`. Serializability: `l` commits after `L` unless `l` read `x` and some
`x ∈ L` wrote it. -/
def σ : Sharding (Fin 2) Bool Unit where
  shards _ := {()}
  proj l _ := l
  eps := false

/-- Shard-local functions: `fₛ = gₛ`, a conflict iff both payloads are `true`. -/
def fs (_ : Unit) : Finset Bool → Bool → Dec :=
  LemmaA3Counterexample.ofPred fun x l => x = false ∨ l = false

/-- The global certification function (`= fₛ`, one shard). -/
def f : Finset Bool → Bool → Dec := fs ()

theorem matching : Matching σ f fs fs where
  distrib_f := LemmaA3Counterexample.ofPred_distributive _
  distrib_fs _ := LemmaA3Counterexample.ofPred_distributive _
  distrib_gs _ := LemmaA3Counterexample.ofPred_distributive _
  fs_eps _ _ := LemmaA3Counterexample.ofPred_eq_commit.2 fun _ _ => Or.inr rfl
  match_f l L := by
    simp only [f, σ, Finset.image_id']
    exact ⟨fun h _ => h, fun h => h ()⟩
  g_imp_f _ _ _ h := h
  comm _ l l' h := LemmaA3Counterexample.ofPred_eq_commit.2 fun x hx => by
    rw [Finset.mem_singleton] at hx
    subst hx
    have := LemmaA3Counterexample.ofPred_eq_commit.1 h l (Finset.mem_singleton_self l)
    tauto

theorem epsNeutral : EpsNeutral σ fs :=
  fun _ _ => LemmaA3Counterexample.ofPred_eq_commit.2 fun x hx => Or.inl (by simpa [σ] using hx)

/-- The protocol of Figure 1 with line 56 read as a binder (no check), initial configuration `{a, b}` with
leader `a`. -/
def Pa : Params (Fin 2) Bool Unit (Fin 4) where
  σ := σ
  fs := fs
  gs := fs
  home _ := ()
  init _ := ⟨{0, 1}, 0⟩
  fixNewConfig := false

theorem validInit : ValidInit Pa := fun s => by cases s; decide

/-- The execution described in the module docstring (`a b c d = 0 1 2 3`). -/
def acts : List (Action (Fin 2) Bool Unit (Fin 4)) :=
  [ .reconfigure 2 (),        -- c probes epoch 0 for epoch 1
    .deliver 2 0 0,           -- a: PROBE(1)
    .deliver 2 1 0,           -- b: PROBE(1)
    .deliver 0 2 0,           -- c: PROBE_ACK from a
    .deliver 1 2 0,           -- c: PROBE_ACK from b
    .probeDone 2 0 {0, 1},    -- c installs epoch 1 = {a, b}; NEW_CONFIG(1) to a (delayed)
    .reconfigure 3 (),        -- d probes epoch 1 for epoch 2
    .deliver 3 0 0,           -- a: PROBE(2)  (PROBE(2) to b stays in transit)
    .deliver 0 3 0,           -- d: PROBE_ACK from a
    .probeDone 3 0 {0, 2},    -- d installs epoch 2 = {a, c}
    .deliver 3 0 0,           -- a: NEW_CONFIG(2): leader of epoch 2
    .deliver 0 2 0,           -- c: NEW_STATE(2): follower of epoch 2
    .deliver 2 0 0,           -- a: the late NEW_CONFIG(1): leader of epoch 1 again
    .deliver 0 1 0,           -- b: NEW_STATE(1): follower of epoch 1
    .reconfigure 3 (),        -- d probes epoch 2 for epoch 3
    .deliver 3 2 0,           -- c: PROBE(3)
    .deliver 2 3 0,           -- d: PROBE_ACK from c
    .probeDone 3 2 {2, 3},    -- d installs epoch 3 = {c, d}
    .deliver 3 2 0,           -- c: NEW_CONFIG(3): leader of epoch 3
    .deliver 2 3 0,           -- d: NEW_STATE(3): follower of epoch 3
    .certify 1 0 true,        -- b certifies t₁
    .deliver 1 0 0,           -- a (epoch 1) prepares t₁ at slot 1, vote commit
    .deliver 0 1 0,           -- b: PREPARE_ACK, sends ACCEPT to b
    .deliver 1 1 0,           -- b: ACCEPT
    .deliver 1 1 0,           -- b: ACCEPT_ACK
    .decide 1 0 (fun _ => 1) (fun _ => .commit),   -- t₁ commits
    .certify 3 1 true,        -- d certifies t₂
    .deliver 3 2 0,           -- c (epoch 3) prepares t₂ at slot 1, vote commit
    .deliver 2 3 0,           -- d: PREPARE_ACK, sends ACCEPT to d
    .deliver 3 3 0,           -- d: ACCEPT
    .deliver 3 3 0,           -- d: ACCEPT_ACK
    .decide 3 1 (fun _ => 1) (fun _ => .commit) ]  -- t₂ commits

/-- The resulting history. -/
def hist : History (Fin 2) Bool :=
  [.certify 0 true, .decide 0 .commit, .certify 1 true, .decide 1 .commit]

theorem acts_fifo : ∀ a ∈ acts, a.IsFIFO := by simp [acts, Action.IsFIFO]

theorem run_hist : (run Pa (initState Pa) acts).map State.hist = some hist := by decide

/-- After step 11 process `a` is at epoch 2; after step 13 it is back at epoch 1. -/
theorem epoch_decreases :
    (run Pa (initState Pa) (acts.take 11)).map (fun st => (st.loc 0).epoch ()) = some 2 ∧
    (run Pa (initState Pa) (acts.take 13)).map (fun st => (st.loc 0).epoch ()) = some 1 := by
  decide

/-- With the check `e ≥ new_epoch` at line 56 the late `NEW_CONFIG(1)` is not accepted. -/
theorem fixed_blocks :
    run { Pa with fixNewConfig := true } (initState { Pa with fixNewConfig := true })
      (acts.take 13) = none := by
  decide

theorem not_correct : ¬ Correct f hist := by
  rintro ⟨ord, -, hmem, hrt, hlegal⟩
  have h1 : (0 : Fin 2) ∈ ord := (hmem 0).2 (by simp [Committed, hist])
  have h2 : (1 : Fin 2) ∈ ord := (hmem 1).2 (by simp [Committed, hist])
  have hlt := hrt 0 1 h1 h2 ⟨⟨1, by simp [hist]⟩, ⟨2, by simp [hist]⟩, by decide,
    ⟨.commit, rfl⟩, ⟨true, rfl⟩⟩
  have hi := List.idxOf_lt_length_of_mem h2
  have hget : ord[ord.idxOf (1 : Fin 2)] = 1 := List.getElem_idxOf hi
  have := hlegal ⟨ord.idxOf (1 : Fin 2), hi⟩ true (by simp [hget, hist])
  have hpay : true ∈ payloadsOf hist (ord.take (ord.idxOf (1 : Fin 2))) := by
    refine mem_payloadsOf.2 ⟨0, ?_, by simp [hist]⟩
    rw [List.mem_take_iff_getElem]
    exact ⟨ord.idxOf (0 : Fin 2), by simp [hlt, List.idxOf_lt_length_of_mem h1],
      List.getElem_idxOf (List.idxOf_lt_length_of_mem h1)⟩
  have := LemmaA3Counterexample.ofPred_eq_commit.1 (show fs () _ true = _ from this) _ hpay
  simp at this

end Line56

open Line56 in
/-- **Theorem 4.1 of [Bravo–Gotsman 2019] is false if line 56 of Figure 1 is read without a
check** (the message pattern `NEW_CONFIG(new_epoch, M)` read as a binder rather than as a match
on the current `new_epoch`). With valid initial configurations, shard-local functions matching `f` (conditions (1), (3)–(5)
and `fₛ({ε}, l) = commit`) and FIFO delivery, a reachable state has a history in which two
conflicting transactions both commit: it is not correct w.r.t. `f`. The cause is the absent
check of the message epoch against `new_epoch` in the `NEW_CONFIG` handler (line 56), see `Line56.epoch_decreases`
and `Line56.fixed_blocks`. -/
theorem theorem_4_1_false_printed :
    ValidInit Pa ∧ Matching σ f fs fs ∧ EpsNeutral σ fs ∧ Pa.fixNewConfig = false ∧
    (∀ a ∈ acts, a.IsFIFO) ∧
    ∃ st, run Pa (initState Pa) acts = some st ∧ Reachable Pa st ∧ ¬ Correct f st.hist := by
  refine ⟨validInit, matching, epsNeutral, rfl, acts_fifo, ?_⟩
  obtain ⟨st, hst, hh⟩ := Option.map_eq_some_iff.1 run_hist
  exact ⟨st, hst, reachable_of_run Pa Relation.ReflTransGen.refl hst, hh ▸ not_correct⟩

end Podc.ReconfigurableCommit

namespace Podc.ReconfigurableCommit

/-!
### Theorem 4.1 also needs `fₛ({ε}, l) = commit`

Two shards, each with its own transaction; the shard-local functions of
`LemmaA3Counterexample` satisfy (1), (3)–(5) but `fₛ({ε}, l) = abort` for `l ≠ ε`. The
*corrected* protocol (`fixNewConfig = true`) commits both transactions in a failure-free run, but
the global `f` defined by (3) forbids committing the second after the first.
-/

namespace Eps

open LemmaA3Counterexample

/-- Shard `false` = processes `{0, 1}` (leader `0`), shard `true` = `{2, 3}` (leader `2`). -/
def Pa : Params Bool (Option Bool) Bool (Fin 4) where
  σ := LemmaA3Counterexample.σ
  fs := LemmaA3Counterexample.fs
  gs := LemmaA3Counterexample.gs
  home p := decide (2 ≤ p.val)
  init s := if s then ⟨{2, 3}, 2⟩ else ⟨{0, 1}, 0⟩
  fixNewConfig := true

theorem validInit : ValidInit Pa := fun s => by cases s <;> decide

/-- `1` certifies `t₁ = false` at shard `false`, then `3` certifies `t₂ = true` at shard
`true`. -/
def acts : List (Action Bool (Option Bool) Bool (Fin 4)) :=
  [ .certify 1 false (some false), .deliver 1 0 0, .deliver 0 1 0, .deliver 1 1 0,
    .deliver 1 1 0, .decide 1 false (fun _ => 1) (fun _ => .commit),
    .certify 3 true (some true), .deliver 3 2 0, .deliver 2 3 0, .deliver 3 3 0,
    .deliver 3 3 0, .decide 3 true (fun _ => 1) (fun _ => .commit) ]

theorem acts_fifo : ∀ a ∈ acts, a.IsFIFO := by simp [acts, Action.IsFIFO]

theorem run_hist : (run Pa (initState Pa) acts).map State.hist =
    some LemmaA3Counterexample.hist := by decide

end Eps

open Eps in
/-- **Theorem 4.1 of [Bravo–Gotsman 2019] is false as stated even for the corrected protocol**:
conditions (1), (3)–(5) do not suffice; the missing hypothesis is `EpsNeutral`
(`fₛ({ε}, l) = commit`), which makes it true (`theorem_4_1`). -/
theorem theorem_4_1_false_eps :
    ValidInit Pa ∧ Matching LemmaA3Counterexample.σ LemmaA3Counterexample.f
      LemmaA3Counterexample.fs LemmaA3Counterexample.gs ∧ Pa.fixNewConfig = true ∧
    (∀ a ∈ acts, a.IsFIFO) ∧
    ∃ st, Reachable Pa st ∧ ¬ Correct LemmaA3Counterexample.f st.hist := by
  refine ⟨validInit, LemmaA3Counterexample.matching, rfl, acts_fifo, ?_⟩
  obtain ⟨st, hst, hh⟩ := Option.map_eq_some_iff.1 run_hist
  exact ⟨st, reachable_of_run Pa Relation.ReflTransGen.refl hst,
    hh ▸ LemmaA3Counterexample.not_correct⟩

/-!
### Single-member configurations (`f = 0`)

With a configuration without followers, the wait of line 26 ("received `ACCEPT_ACK` from every
`p_j ∈ members[s] \ leader[s]`") is vacuous for any `kₛ, dₛ`: a coordinator may decide `commit`
before any shard has seen the transaction. This is why our model requires `|M| ≥ 2`
(`ValidInit`, `probeDone`).
-/

namespace Single

open Line56 in
/-- One shard, initial configuration `{0}` (no follower). -/
def Pa : Params (Fin 2) Bool Unit (Fin 4) :=
  { Line56.Pa with init := fun _ => ⟨{0}, 0⟩, fixNewConfig := true }

/-- Certify both conflicting transactions at `0` and decide `commit` immediately. -/
def acts : List (Action (Fin 2) Bool Unit (Fin 4)) :=
  [ .certify 0 0 true, .decide 0 0 (fun _ => 1) (fun _ => .commit),
    .certify 0 1 true, .decide 0 1 (fun _ => 1) (fun _ => .commit) ]

theorem run_hist : (run Pa (initState Pa) acts).map State.hist = some Line56.hist := by decide

/-- With a single-member configuration (`f = 0`) the protocol of Figure 1 commits two conflicting
transactions without preparing them. -/
theorem single_member_unsafe :
    ∃ st, Reachable Pa st ∧ ¬ Correct Line56.f st.hist := by
  obtain ⟨st, hst, hh⟩ := Option.map_eq_some_iff.1 run_hist
  exact ⟨st, reachable_of_run Pa Relation.ReflTransGen.refl hst, hh ▸ Line56.not_correct⟩

end Single

end Podc.ReconfigurableCommit

namespace Podc.ReconfigurableCommit

/-!
### Invariant 8 is false

Invariant 8 (Figure 5) claims `new_epoch ≥ epoch[s₀]` at every process. A fresh process added to a
new configuration never received `PROBE`, and the `NEW_STATE` handler (lines 61–66) does not
update `new_epoch`; so after joining epoch `1` it has `new_epoch = 0 < 1 = epoch[s₀]`, also in the
corrected protocol. (The invariant is not needed: our proof uses `new_epoch ≤ epoch[s₀]` for leaders and
followers instead, `Inv.loc_newEpoch`.)
-/

namespace Inv8

/-- The corrected protocol on the instance of `Line56`. -/
def Pa : Params (Fin 2) Bool Unit (Fin 4) := { Line56.Pa with fixNewConfig := true }

/-- `c` installs epoch 1 = `{a, d}` with `d` fresh; `d` receives `NEW_STATE(1)`. -/
def acts : List (Action (Fin 2) Bool Unit (Fin 4)) :=
  [ .reconfigure 2 (), .deliver 2 0 0, .deliver 0 2 0, .probeDone 2 0 {0, 3}, .deliver 2 0 0,
    .deliver 0 3 0 ]

theorem run_epochs : (run Pa (initState Pa) acts).map
    (fun st => ((st.loc 3).newEpoch, (st.loc 3).epoch ())) = some (0, 1) := by decide

/-- Invariant 8 of [Bravo–Gotsman 2019] fails in a reachable state of the corrected protocol. -/
theorem invariant_8_false : ∃ st, Reachable Pa st ∧ (st.loc 3).newEpoch < (st.loc 3).epoch () := by
  obtain ⟨st, hst, hh⟩ := Option.map_eq_some_iff.1 run_epochs
  simp only [Prod.mk.injEq] at hh
  exact ⟨st, reachable_of_run Pa Relation.ReflTransGen.refl hst, by omega⟩

end Inv8

end Podc.ReconfigurableCommit
