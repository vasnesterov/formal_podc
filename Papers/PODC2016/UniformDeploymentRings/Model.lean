import Papers.PODC2016.UniformDeploymentRings.Defs

/-!
# Mobile agents with tokens in an asynchronous unidirectional ring (Section 2.1)

-- CSLib candidate: Cslib/Computability/Distributed/MobileAgents/TokenRing.lean

The model of [Shibata et al., PODC 2016], Section 2.1.

* The ring has nodes `ZMod n`; agents move from `v` to `v + 1` only.
* A node holds a number of tokens (`Local.tok`), the list of agents *staying* at it
  (`Local.stay`) and the FIFO queue of agents *in transit* towards it (`Local.queue`, its incoming
  buffer).
* Agents are anonymous deterministic state machines (`Algorithm`). In one **atomic action**
  (`Local.act`) an agent at node `v` — either staying there or at the head of the incoming queue —
  receives all its messages, observes the number of tokens at `v` and the states of the other
  agents staying at `v`, computes, may release a token, may broadcast one message to the other
  agents staying at `v` (appended to their mailboxes), and then stays at `v` or leaves to the tail
  of the queue of `v + 1`. A halted agent (`Algorithm.halted`) never acts again.
  Agents carry an identifier `id` used only for the schedule; the algorithm never sees it.
  Observing the states of co-located agents is more than the paper grants (it only allows
  messages and seeing whether other agents are present), which only strengthens impossibility
  results and is not used by our algorithms beyond counting the agents.
* A **schedule** is a sequence of agents `σ : ℕ → ι`; at time `t` agent `σ t` takes an atomic
  action if it can (it is staying somewhere or at the head of a queue), otherwise nothing happens
  (`step`, `exec`). It is **fair** if every agent appears infinitely often (`Fair`).
* Initially (`initConfig`) no node has a token, all agents are in the initial state and each
  agent is in the incoming buffer of its home node, so it acts at its home before any other agent
  (the paper's assumption in Section 2.1).
* `SolvesTD A n k home`: the uniform deployment problem with termination detection
  (Definition 1): in every fair execution all agents eventually halt, and whenever all agents are
  halted, no agent is in transit and the deployment is uniform.
-/

namespace Podc.UniformDeploymentRings

/-- The outcome of the local computation of an atomic action. -/
structure Action (S M : Type) where
  /-- new state -/
  state : S
  /-- release a token at the current node -/
  release : Bool
  /-- message broadcast to the other agents staying at the current node -/
  msg : Option M
  /-- leave towards the next node (otherwise stay) -/
  move : Bool

/-- A deterministic anonymous mobile-agent algorithm. `act s msgs tok others` is the local
computation of an agent in state `s` that received the messages `msgs`, at a node holding `tok`
tokens where the other staying agents are in the states `others`. -/
structure Algorithm where
  /-- agent states -/
  S : Type
  /-- messages -/
  M : Type
  /-- the initial state -/
  init : S
  /-- the halt states -/
  halted : S → Bool
  /-- the local computation -/
  act : S → List M → ℕ → List S → Action S M

variable (A : Algorithm) {n : ℕ} {ι ι' : Type}

/-- An agent: identifier (for the scheduler only), state and pending messages. -/
@[ext] structure Agent (A : Algorithm) (ι : Type) where
  /-- identifier, invisible to the algorithm -/
  id : ι
  /-- current state -/
  st : A.S
  /-- received, not yet consumed messages -/
  mail : List A.M

/-- Relabel the identifier of an agent. -/
def Agent.map (f : ι → ι') (x : Agent A ι) : Agent A ι' := ⟨f x.id, x.st, x.mail⟩

/-- The local configuration of a node: tokens, staying agents, incoming FIFO queue. -/
@[ext] structure Local (A : Algorithm) (ι : Type) where
  /-- number of tokens on the node -/
  tok : ℕ
  /-- agents staying at the node -/
  stay : List (Agent A ι)
  /-- agents in transit towards the node (head first) -/
  queue : List (Agent A ι)

/-- Relabel the identifiers in a local configuration. -/
def Local.map (f : ι → ι') (L : Local A ι) : Local A ι' :=
  ⟨L.tok, L.stay.map (Agent.map A f), L.queue.map (Agent.map A f)⟩

/-- Who acts: the head of the incoming queue, or the `i`-th staying agent. -/
inductive Slot
  | head
  | stay (i : ℕ)
  deriving DecidableEq

/-- The agent at a slot, if any. -/
def Local.actor (L : Local A ι) : Slot → Option (Agent A ι)
  | .head => L.queue.head?
  | .stay i => L.stay[i]?

/-- The staying agents other than the actor. -/
def Local.others (L : Local A ι) : Slot → List (Agent A ι)
  | .head => L.stay
  | .stay i => L.stay.eraseIdx i

/-- The incoming queue without the actor. -/
def Local.rest (L : Local A ι) : Slot → List (Agent A ι)
  | .head => L.queue.tail
  | .stay _ => L.queue

/-- Deliver message `m` (if any) to the agents `l`. -/
def deliver (m : Option A.M) (l : List (Agent A ι)) : List (Agent A ι) :=
  match m with
  | none => l
  | some m => l.map fun y => { y with mail := y.mail ++ [m] }

/-- The new local configuration of the node and the leaving agent (if any) when the agent `x` at
slot `s` computes the outcome `o`. -/
def Local.result (L : Local A ι) (s : Slot) (x : Agent A ι) (o : Action A.S A.M) :
    Local A ι × Option (Agent A ι) :=
  (⟨L.tok + (if o.release then 1 else 0),
    if o.move then deliver A o.msg (L.others A s)
    else deliver A o.msg (L.others A s) ++ [⟨x.id, o.state, []⟩], L.rest A s⟩,
   if o.move then some ⟨x.id, o.state, []⟩ else none)

/-- The atomic action of the agent at slot `s`: the new local configuration of the node and the
agent leaving it (if any). `none` if there is no such agent or it is halted. -/
def Local.act (L : Local A ι) (s : Slot) : Option (Local A ι × Option (Agent A ι)) :=
  match L.actor A s with
  | none => none
  | some x =>
    if A.halted x.st then none else
    some (L.result A s x (A.act x.st x.mail L.tok ((L.others A s).map Agent.st)))

/-- Append an arriving agent (if any) to the incoming queue. -/
def Local.push (L : Local A ι) : Option (Agent A ι) → Local A ι
  | none => L
  | some x => { L with queue := L.queue ++ [x] }

/-- Global configurations. -/
abbrev Config (A : Algorithm) (n : ℕ) (ι : Type) := ZMod n → Local A ι

/-- The atomic action of the agent at slot `s` of node `v`. -/
def stepAt (C : Config A n ι) (v : ZMod n) (s : Slot) : Config A n ι := fun w =>
  match (C v).act A s with
  | none => C w
  | some r =>
    let base := if w = v then r.1 else C w
    if w = v + 1 then base.push A r.2 else base

open Classical in
/-- One step of the schedule: agent `a` takes an atomic action if it can. -/
noncomputable def step (C : Config A n ι) (a : ι) : Config A n ι :=
  if h : ∃ p : ZMod n × Slot, ((C p.1).actor A p.2).map Agent.id = some a then
    stepAt A C h.choose.1 h.choose.2
  else C

/-- The execution from `C₀` under the schedule `σ`. -/
noncomputable def exec (C₀ : Config A n ι) (σ : ℕ → ι) : ℕ → Config A n ι
  | 0 => C₀
  | t + 1 => step A (exec C₀ σ t) (σ t)

/-- A schedule is fair if every agent appears in it infinitely often. -/
def Fair (σ : ℕ → ι) : Prop := ∀ a N, ∃ t, N ≤ t ∧ σ t = a

/-- The initial configuration: no tokens, every agent in the initial state, in the incoming buffer
of its home node. -/
def initConfig (k : ℕ) (home : Fin k → ZMod n) : Config A n (Fin k) := fun v =>
  ⟨0, [], ((List.finRange k).filter fun a => home a = v).map fun a => ⟨a, A.init, []⟩⟩

/-- All agents are in the halt state. -/
def AllHalted (C : Config A n ι) : Prop :=
  ∀ v, ∀ x ∈ (C v).stay ++ (C v).queue, A.halted x.st = true

/-- No agent is in transit. -/
def QueuesEmpty (C : Config A n ι) : Prop := ∀ v, (C v).queue = []

/-- The number of agents staying at each node. -/
def occ (C : Config A n ι) (v : ZMod n) : ℕ := ((C v).stay).length

/-- Definition 1: `A` solves the uniform deployment problem with termination detection in the
ring of `n` nodes with `k` agents placed initially at `home`. -/
def SolvesTD (A : Algorithm) (n k : ℕ) (home : Fin k → ZMod n) : Prop :=
  ∀ σ : ℕ → Fin k, Fair σ →
    (∃ t, AllHalted A (exec A (initConfig A k home) σ t)) ∧
    ∀ t, AllHalted A (exec A (initConfig A k home) σ t) →
      QueuesEmpty A (exec A (initConfig A k home) σ t) ∧
      IsUniform n k (occ A (exec A (initConfig A k home) σ t))

/-! ### Basic lemmas -/

section Lemmas

variable {A}

theorem stepAt_of_act_none {C : Config A n ι} {v : ZMod n} {s : Slot}
    (h : (C v).act A s = none) : stepAt A C v s = C := by
  funext w; simp [stepAt, h]

theorem stepAt_apply_of_ne {C : Config A n ι} {v w : ZMod n} {s : Slot} (h1 : w ≠ v)
    (h2 : w ≠ v + 1) : stepAt A C v s w = C w := by
  unfold stepAt; split <;> simp [h1, h2]

theorem stepAt_apply_self {C : Config A n ι} {v : ZMod n} {s : Slot} {r}
    (h : (C v).act A s = some r) (hv : v ≠ v + 1) : stepAt A C v s v = r.1 := by
  simp [stepAt, h, hv]

theorem stepAt_apply_succ {C : Config A n ι} {v : ZMod n} {s : Slot} {r}
    (h : (C v).act A s = some r) (hv : v + 1 ≠ v) :
    stepAt A C v s (v + 1) = (C (v + 1)).push A r.2 := by
  simp [stepAt, h, hv]

/-! #### Relabelling identifiers commutes with the semantics -/

@[simp] theorem Agent.map_st (f : ι → ι') (x : Agent A ι) : (x.map A f).st = x.st := rfl
@[simp] theorem Agent.map_mail (f : ι → ι') (x : Agent A ι) : (x.map A f).mail = x.mail := rfl
@[simp] theorem Agent.map_id (f : ι → ι') (x : Agent A ι) : (x.map A f).id = f x.id := rfl

theorem Local.actor_map (f : ι → ι') (L : Local A ι) (s : Slot) :
    (L.map A f).actor A s = (L.actor A s).map (Agent.map A f) := by
  cases s <;> simp [Local.actor, Local.map, List.head?_map]

theorem Local.others_map (f : ι → ι') (L : Local A ι) (s : Slot) :
    (L.map A f).others A s = (L.others A s).map (Agent.map A f) := by
  cases s <;> simp [Local.others, Local.map, List.eraseIdx_map]

theorem Local.rest_map (f : ι → ι') (L : Local A ι) (s : Slot) :
    (L.map A f).rest A s = (L.rest A s).map (Agent.map A f) := by
  cases s <;> simp [Local.rest, Local.map, List.map_tail]

theorem deliver_map (f : ι → ι') (m : Option A.M) (l : List (Agent A ι)) :
    deliver A m (l.map (Agent.map A f)) = (deliver A m l).map (Agent.map A f) := by
  cases m <;> simp [deliver, Agent.map]

theorem Local.result_map (f : ι → ι') (L : Local A ι) (s : Slot) (x : Agent A ι)
    (o : Action A.S A.M) :
    (L.map A f).result A s (x.map A f) o =
      ((L.result A s x o).1.map A f, (L.result A s x o).2.map (Agent.map A f)) := by
  rcases o with ⟨_, _, _, mv⟩
  have ho := Local.others_map f L s
  have hr := Local.rest_map f L s
  simp only [Local.map] at ho hr
  cases mv <;> simp [Local.result, Local.map, Agent.map, ho, hr, ← deliver_map]

theorem Local.act_map (f : ι → ι') (L : Local A ι) (s : Slot) :
    (L.map A f).act A s =
      ((L.act A s).map fun r => (r.1.map A f, r.2.map (Agent.map A f))) := by
  unfold Local.act
  rw [Local.actor_map]
  rcases hx : L.actor A s with _ | x
  · simp
  · by_cases hh : A.halted x.st
    · simp [hh]
    · have h2 : (Agent.st ∘ Agent.map A f) = (Agent.st : Agent A ι → A.S) := rfl
      simp only [Option.map_some, Agent.map_st, hh, Bool.false_eq_true, ite_false,
        Agent.map_mail, Local.others_map, List.map_map, h2, Local.result_map]
      rfl

theorem Local.push_map (f : ι → ι') (L : Local A ι) (x : Option (Agent A ι)) :
    (L.map A f).push A (x.map (Agent.map A f)) = (L.push A x).map A f := by
  cases x <;> simp [Local.push, Local.map]

/-- Two local configurations are *alike* if they agree up to the identifiers of the agents. -/
def Local.Alike (L : Local A ι) (L' : Local A ι') : Prop :=
  L.map A (fun _ => ()) = L'.map A (fun _ => ())

theorem Local.Alike.act {L : Local A ι} {L' : Local A ι'} (h : L.Alike L') (s : Slot) :
    ((L.act A s).map fun r => (r.1.map A (fun _ => ()), r.2.map (Agent.map A fun _ => ()))) =
    ((L'.act A s).map fun r => (r.1.map A (fun _ => ()), r.2.map (Agent.map A fun _ => ()))) := by
  unfold Local.Alike at h
  rw [← Local.act_map, ← Local.act_map, h]

/-! #### Halted agents -/

theorem Local.act_eq_none_of_halted {L : Local A ι} {s : Slot} {x : Agent A ι}
    (hx : L.actor A s = some x) (hh : A.halted x.st = true) : L.act A s = none := by
  simp [Local.act, hx, hh]

theorem Local.actor_mem {L : Local A ι} {s : Slot} {x : Agent A ι} (hx : L.actor A s = some x) :
    x ∈ L.stay ++ L.queue := by
  cases s with
  | head =>
    simp only [Local.actor] at hx
    exact List.mem_append_right _ (List.mem_of_mem_head? hx)
  | stay i =>
    simp only [Local.actor] at hx
    exact List.mem_append_left _ (List.mem_of_getElem? hx)

theorem stepAt_of_allHalted {C : Config A n ι} (h : AllHalted A C) (v : ZMod n) (s : Slot) :
    stepAt A C v s = C := by
  apply stepAt_of_act_none
  rcases hx : (C v).actor A s with _ | x
  · simp [Local.act, hx]
  · exact Local.act_eq_none_of_halted hx (h v x (Local.actor_mem hx))

theorem step_of_allHalted {C : Config A n ι} (h : AllHalted A C) (a : ι) : step A C a = C := by
  unfold step; split <;> simp [stepAt_of_allHalted h]

theorem exec_of_allHalted {C₀ : Config A n ι} {σ : ℕ → ι} {t : ℕ}
    (h : AllHalted A (exec A C₀ σ t)) : ∀ m, exec A C₀ σ (t + m) = exec A C₀ σ t
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, exec, exec_of_allHalted h m, step_of_allHalted h]

/-- Node `w` holds a halted staying agent. -/
def HaltedAt (C : Config A n ι) (w : ZMod n) : Prop := ∃ x ∈ (C w).stay, A.halted x.st = true

theorem mem_deliver {m : Option A.M} {l : List (Agent A ι)} {x : Agent A ι} (hx : x ∈ l) :
    ∃ y ∈ deliver A m l, y.st = x.st := by
  cases m with
  | none => exact ⟨x, hx, rfl⟩
  | some m => exact ⟨{ x with mail := x.mail ++ [m] }, List.mem_map.2 ⟨x, hx, rfl⟩, rfl⟩

theorem Local.haltedStay_result {L : Local A ι} {s : Slot} {y : Agent A ι}
    (hy : L.actor A s = some y) (hny : A.halted y.st = false) {o : Action A.S A.M}
    {x : Agent A ι} (hx : x ∈ L.stay) (hh : A.halted x.st = true) :
    ∃ z ∈ (L.result A s y o).1.stay, A.halted z.st = true := by
  have hmem : x ∈ L.others A s := by
    cases s with
    | head => exact hx
    | stay i =>
      simp only [Local.actor] at hy
      simp only [Local.others]
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hy
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hij : j ≠ i := by rintro rfl; simp [hh] at hny
      exact List.mem_eraseIdx_iff_getElem.2 ⟨j, hj, hij, rfl⟩
  obtain ⟨z, hz, hzst⟩ := mem_deliver (m := o.msg) hmem
  refine ⟨z, ?_, hzst ▸ hh⟩
  simp only [Local.result]
  split <;> simp [hz]

theorem HaltedAt.stepAt {C : Config A n ι} {w : ZMod n} (h : HaltedAt C w) (v : ZMod n)
    (s : Slot) : HaltedAt (stepAt A C v s) w := by
  obtain ⟨x, hx, hh⟩ := h
  unfold Podc.UniformDeploymentRings.stepAt
  rcases hr : (C v).act A s with _ | r
  · exact ⟨x, hx, hh⟩
  · simp only
    have key : ∃ z ∈ (if w = v then r.1 else C w).stay, A.halted z.st = true := by
      split_ifs with hwv
      · subst hwv
        unfold Local.act at hr
        rcases hy : (C w).actor A s with _ | y
        · simp [hy] at hr
        · simp only [hy] at hr
          by_cases hny : A.halted y.st
          · simp [hny] at hr
          · simp only [hny, Bool.false_eq_true, ite_false, Option.some.injEq] at hr
            rw [← hr]
            exact Local.haltedStay_result hy (by simpa using hny) hx hh
      · exact ⟨x, hx, hh⟩
    show ∃ z ∈ (if w = v + 1 then _ else _ : Local A ι).stay, _
    generalize (if w = v then r.1 else C w) = B at key ⊢
    by_cases h1 : w = v + 1
    · simp only [h1, ↓reduceIte]
      obtain ⟨z, hz, hzh⟩ := key
      refine ⟨z, ?_, hzh⟩
      cases r.2 <;> simpa [Local.push] using hz
    · simp only [h1, ↓reduceIte]; exact key

theorem HaltedAt.step {C : Config A n ι} {w : ZMod n} (h : HaltedAt C w) (a : ι) :
    HaltedAt (step A C a) w := by
  unfold Podc.UniformDeploymentRings.step; split
  · exact h.stepAt _ _
  · exact h

theorem HaltedAt.exec {C₀ : Config A n ι} {σ : ℕ → ι} {t : ℕ} {w : ZMod n}
    (h : HaltedAt (exec A C₀ σ t) w) : ∀ m, HaltedAt (exec A C₀ σ (t + m)) w
  | 0 => h
  | m + 1 => by rw [← Nat.add_assoc, Podc.UniformDeploymentRings.exec]; exact (h.exec m).step _

/-! #### Identifiers are never duplicated -/

/-- The identifiers of the agents at a node (staying or in its incoming queue). -/
def Local.ids (L : Local A ι) : Multiset ι :=
  ((L.stay.map Agent.id : List ι) : Multiset ι) + ((L.queue.map Agent.id : List ι) : Multiset ι)

/-- The identifiers of all agents. -/
def allIds [NeZero n] (C : Config A n ι) : Multiset ι := ∑ v, (C v).ids

/-- Identifiers of an optional agent. -/
def optIds : Option (Agent A ι) → Multiset ι
  | none => 0
  | some x => {x.id}

theorem Local.ids_push (L : Local A ι) (o : Option (Agent A ι)) :
    (L.push A o).ids = L.ids + optIds o := by
  cases o <;> simp [Local.push, Local.ids, optIds, ← Multiset.coe_add, add_assoc]

theorem map_id_deliver (m : Option A.M) (l : List (Agent A ι)) :
    (deliver A m l).map Agent.id = l.map Agent.id := by
  cases m <;> simp [deliver, Function.comp_def]

theorem Local.ids_act {L : Local A ι} {s : Slot} {r} (h : L.act A s = some r) :
    r.1.ids + optIds r.2 = L.ids := by
  unfold Local.act at h
  rcases hx : L.actor A s with _ | x
  · simp [hx] at h
  · simp only [hx] at h
    by_cases hh : A.halted x.st
    · simp [hh] at h
    · simp only [hh, Bool.false_eq_true, ite_false, Option.some.injEq] at h
      subst h
      -- the actor `x` and the others make up the node
      have key : ((L.others A s).map Agent.id : Multiset ι) + ((L.rest A s).map Agent.id) +
          {x.id} = L.ids := by
        cases s with
        | head =>
          simp only [Local.actor] at hx
          obtain ⟨q, hq⟩ : ∃ q, L.queue = x :: q := by
            cases hL : L.queue with
            | nil => simp [hL] at hx
            | cons y q => simp [hL] at hx; exact ⟨q, by rw [hx]⟩
          simp only [Local.others, Local.rest, Local.ids, hq, List.map_cons, List.tail_cons,
            ← Multiset.cons_coe, ← Multiset.singleton_add]
          abel
        | stay i =>
          simp only [Local.actor] at hx
          obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
          have hp := (List.getElem_cons_eraseIdx_perm hi).map Agent.id
          have hp' : (((L.stay.eraseIdx i).map Agent.id : List ι) : Multiset ι) + {L.stay[i].id} =
              ((L.stay.map Agent.id : List ι) : Multiset ι) := by
            simp only [List.map_cons] at hp
            rw [← Multiset.coe_eq_coe.2 hp, ← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]
          simp only [Local.others, Local.rest, Local.ids]
          rw [← hp']; abel
      rw [← key]
      generalize A.act x.st x.mail L.tok ((L.others A s).map Agent.st) = o
      rcases o with ⟨_, _, _, mv⟩
      cases mv <;> simp [Local.result, Local.ids, optIds, map_id_deliver, ← Multiset.coe_add]
      all_goals abel

theorem allIds_stepAt [NeZero n] (C : Config A n ι) (v : ZMod n) (s : Slot) :
    allIds (stepAt A C v s) = allIds C := by
  rcases hr : (C v).act A s with _ | r
  · rw [stepAt_of_act_none hr]
  · have hpt : ∀ w, (stepAt A C v s w).ids =
        (Function.update (fun w => (C w).ids) v r.1.ids w) + if w = v + 1 then optIds r.2 else 0 := by
      intro w
      have hb : (if w = v then r.1 else C w).ids = Function.update (fun w => (C w).ids) v r.1.ids w := by
        by_cases h : w = v
        · subst h; simp
        · simp [h]
      rw [← hb]
      simp only [stepAt, hr]
      generalize (if w = v then r.1 else C w) = B
      by_cases h1 : w = v + 1 <;> simp [h1, Local.ids_push]
    unfold allIds
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_update_of_mem (Finset.mem_univ v), add_assoc, add_comm _ (optIds r.2),
      ← add_assoc, Local.ids_act hr, ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    simp [Finset.sdiff_singleton_eq_erase]

theorem allIds_step [NeZero n] (C : Config A n ι) (a : ι) : allIds (step A C a) = allIds C := by
  unfold step; split
  · exact allIds_stepAt _ _ _
  · rfl

theorem allIds_exec [NeZero n] (C₀ : Config A n ι) (σ : ℕ → ι) :
    ∀ t, allIds (exec A C₀ σ t) = allIds C₀
  | 0 => rfl
  | t + 1 => by rw [exec, allIds_step, allIds_exec C₀ σ t]

theorem Local.ids_nodup_of_allIds [NeZero n] {C : Config A n ι} (h : (allIds C).Nodup) (v : ZMod n) :
    (C v).ids.Nodup := by
  refine Multiset.nodup_of_le ?_ h
  unfold allIds
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  exact le_add_right le_rfl

theorem actor_unique [NeZero n] {C : Config A n ι} (h : (allIds C).Nodup) {v v' : ZMod n}
    {s s' : Slot} {x x' : Agent A ι} (hx : (C v).actor A s = some x)
    (hx' : (C v').actor A s' = some x') (hid : x.id = x'.id) : v = v' ∧ s = s' := by
  have mem : ∀ {v s} {x : Agent A ι}, (C v).actor A s = some x → x.id ∈ (C v).ids := by
    intro v s x hx
    have := Local.actor_mem hx
    simp only [Local.ids, Multiset.mem_add, Multiset.mem_coe, List.mem_map]
    rcases List.mem_append.1 this with h | h
    · exact Or.inl ⟨x, h, rfl⟩
    · exact Or.inr ⟨x, h, rfl⟩
  by_cases hvv : v = v'
  · subst hvv
    refine ⟨rfl, ?_⟩
    have hnd := Local.ids_nodup_of_allIds h v
    simp only [Local.ids, Multiset.coe_add, Multiset.coe_nodup] at hnd
    -- positions in the list `stay.map id ++ queue.map id`
    have pos : ∀ {s} {x : Agent A ι}, (C v).actor A s = some x →
        ∃ j, ∃ hj : j < ((C v).stay.map Agent.id ++ (C v).queue.map Agent.id).length,
          ((C v).stay.map Agent.id ++ (C v).queue.map Agent.id)[j] = x.id ∧
          (s = .head → j = (C v).stay.length) ∧ (∀ i, s = .stay i → j = i) := by
      intro s x hx
      cases s with
      | head =>
        simp only [Local.actor] at hx
        obtain ⟨y, q, hq⟩ : ∃ y q, (C v).queue = y :: q := by
          cases hL : (C v).queue with
          | nil => simp [hL] at hx
          | cons y q => exact ⟨y, q, rfl⟩
        rw [hq] at hx; simp at hx; subst hx
        refine ⟨(C v).stay.length, by simp [hq], ?_, fun _ => rfl, fun i h => by cases h⟩
        rw [List.getElem_append_right (by simp)]; simp [hq]
      | stay i =>
        simp only [Local.actor] at hx
        obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hx
        refine ⟨i, ?_, ?_, ?_, ?_⟩
        · simp; omega
        · rw [List.getElem_append_left (by simpa using hi)]; simp
        · intro h; cases h
        · intro i' h; cases h; rfl
    obtain ⟨j, hj, hjx, hj1, hj2⟩ := pos hx
    obtain ⟨j', hj', hjx', hj1', hj2'⟩ := pos hx'
    have : j = j' := (List.Nodup.getElem_inj_iff hnd).1 (hjx.trans (hid.trans hjx'.symm))
    subst this
    cases s with
    | head =>
      cases s' with
      | head => rfl
      | stay i' =>
        have := hj2' i' rfl
        simp only [Local.actor] at hx'
        have := (List.getElem?_eq_some_iff.1 hx').1
        have := hj1 rfl
        omega
    | stay i =>
      cases s' with
      | head =>
        have := hj2 i rfl
        simp only [Local.actor] at hx
        have := (List.getElem?_eq_some_iff.1 hx).1
        have := hj1' rfl
        omega
      | stay i' => rw [← hj2 i rfl, hj2' i' rfl]
  · exfalso
    have hsum : (C v).ids + (C v').ids ≤ allIds C := by
      unfold allIds
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hvv, Finset.mem_univ v'⟩)]
      rw [← add_assoc]; exact le_add_right le_rfl
    have hnd := Multiset.nodup_of_le hsum h
    exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 (mem hx) (hid ▸ mem hx')

theorem step_eq_stepAt [NeZero n] {C : Config A n ι} (h : (allIds C).Nodup) {v : ZMod n}
    {s : Slot} {x : Agent A ι} (hx : (C v).actor A s = some x) :
    step A C x.id = stepAt A C v s := by
  have he : ∃ p : ZMod n × Slot, ((C p.1).actor A p.2).map Agent.id = some x.id :=
    ⟨(v, s), by simp [hx]⟩
  unfold step
  simp only [he, ↓reduceDIte]
  obtain ⟨y, hy, hyid⟩ := Option.map_eq_some_iff.1 he.choose_spec
  obtain ⟨h1, h2⟩ := actor_unique h hy hx hyid
  rw [h1, h2]

theorem allIds_foldl [NeZero n] (C₀ : Config A n ι) (l : List ι) :
    allIds (l.foldl (step A) C₀) = allIds C₀ := by
  induction l generalizing C₀ with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, allIds_step]

theorem exec_eq_foldl (C₀ : Config A n ι) (σ : ℕ → ι) (l : List ι)
    (hσ : ∀ i (h : i < l.length), σ i = l[i]) :
    ∀ t ≤ l.length, exec A C₀ σ t = (l.take t).foldl (step A) C₀
  | 0, _ => rfl
  | t + 1, ht => by
    rw [exec, exec_eq_foldl C₀ σ l hσ t (by omega), List.take_add_one, List.foldl_append,
      List.getElem?_eq_getElem (by omega), hσ t (by omega)]
    rfl

theorem allIds_initConfig_nodup [NeZero n] {k : ℕ} (home : Fin k → ZMod n) :
    (allIds (initConfig A k home)).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  unfold allIds
  rw [Multiset.count_sum']
  have : ∀ v, Multiset.count a (initConfig A k home v).ids = if home a = v then 1 else 0 := by
    intro v
    simp only [initConfig, Local.ids, List.map_nil, Multiset.coe_nil, zero_add, List.map_map,
      Multiset.coe_count]
    have hf : (Agent.id ∘ fun a : Fin k => (⟨a, A.init, []⟩ : Agent A (Fin k))) = id := rfl
    rw [hf, List.map_id]
    by_cases h : home a = v
    · rw [List.count_filter (by simp [h])]
      simp [h, List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange a)]
    · simp only [h, ↓reduceIte]
      exact List.count_eq_zero.2 (by simp [h])
  simp [this]

theorem filter_finRange_eq_singleton {k : ℕ} (p : Fin k → Bool) (a₀ : Fin k)
    (h : ∀ a, p a = true ↔ a = a₀) : (List.finRange k).filter p = [a₀] := by
  have hall : ∀ b ∈ (List.finRange k).filter p, b = a₀ := fun b hb =>
    (h b).1 (List.mem_filter.1 hb).2
  have hmem : a₀ ∈ (List.finRange k).filter p :=
    List.mem_filter.2 ⟨List.mem_finRange a₀, (h a₀).2 rfl⟩
  have hnd : ((List.finRange k).filter p).Nodup := (List.nodup_finRange k).filter p
  generalize (List.finRange k).filter p = L at hall hmem hnd
  match L, hall, hmem, hnd with
  | [], _, hmem, _ => simp at hmem
  | b :: t, hall, _, hnd =>
    have hb : b = a₀ := hall b (by simp)
    subst hb
    cases t with
    | nil => rfl
    | cons c t =>
      have hc : c = b := hall c (by simp)
      subst hc
      simp at hnd

end Lemmas

end Podc.UniformDeploymentRings
