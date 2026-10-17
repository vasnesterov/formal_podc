import Papers.PODC2011.KCoreDecomposition.Algorithm
import Cslib.Foundations.Data.Nat.Descent

/-!
# Asynchronous execution of Algorithm 1: Theorems 2 (Safety) and 3 (Liveness)

Montresor, De Pellegrini, Miorandi, *Distributed k-Core Decomposition*, PODC 2011
(arXiv 1103.5320v2), §3.1 and §4.1.

## Model (one host = one node)

* **Global state** `GState`: the local states `st : V → NodeState V` of Algorithm 1 and the
  multiset `net` of messages in transit, each a triple `(sender, receiver, value)`. Channels are
  reliable but have arbitrary delays and may reorder messages (no FIFO assumption); no crashes.
* **Initial state** `initGState`: every node is in `initState` (`core = d(u)`, `est = +∞`,
  `changed = false`) and the initialization broadcast `⟨u, d(u)⟩` to all neighbours is in transit.
* **Actions** (`Action`, semantics `perform`):
  - `deliver m`: if `m ∈ net`, one copy of `m` is removed and the receiver runs the handler
    `on receive ⟨sender, value⟩` (`receive` from `Algorithm.lean`). A `deliver m` with `m ∉ net`
    is a **no-op** (so schedules need not be state-dependent).
  - `tick u`: the periodic block `repeat every δ`: if `changed`, send `⟨u, core⟩` to all neighbours
    and reset `changed`; otherwise a no-op. The round duration `δ` plays no role in the proofs:
    a tick is an arbitrary point at which the node's periodic block runs.
* **Executions** `Async.run G act`: the sequence of global states produced by an arbitrary
  schedule `act : ℕ → Action V` (the interleaving of all events, chosen by an adversary).
* **Fairness** `Fair G act`: every node ticks infinitely often, and every message in transit at time
  `t` is delivered at some time `t' ≥ t` (i.e. `deliver m` is performed while `m` is in transit;
  identical copies are indistinguishable).

## Results

* `Async.theorem_2` (**Safety**): in *every* execution, `core(u) ≥ k(u)` at all times. Also
  `coreness_le_est`, `coreness_le_of_mem_net` (all estimates and in-transit values are safe) and
  `core_anti` (`core` never increases).
* `Async.theorem_3` (**Liveness**): in every *fair* execution there is a time after which
  `core(u) = k(u)` for all `u`.
* `Async.exists_fair`: fair schedules exist (any schedule in which every action occurs infinitely
  often is fair, `fair_of_frequently`), so Theorem 3 is not vacuous.

## Proof

Both theorems follow from one inductive invariant `Inv` of all reachable states:
`core ≤ d`, `core ≥ k` (safety), `core_v ≤ est_u[v]` and `core_v ≤ value` of every message from `v`,
`computeIndex(est_u, u, core_u) = core_u` (every node's `core` is a fixpoint of its own
estimates), and, for every edge `(v, u)`:
`est_u[v] = core_v`, or a message `⟨v, core_v⟩` to `u` is in transit, or `changed_v`.

Liveness then avoids the paper's induction on the coreness: cores are non-increasing, hence
eventually constant (`c∞`); after one more tick of every node all `changed` flags stay `false`;
by fairness every edge then gets `est_u[v] = c∞(v)` forever; the fixpoint invariant gives
`step G c∞ = c∞`, and `eq_coreness_of_step_eq` (with safety) gives `c∞ = k`.

## Remarks on the paper's proofs

* The paper never states the fairness assumptions Theorem 3 needs (reliable eventual delivery,
  every node runs its periodic block infinitely often); without them liveness fails trivially.
  No FIFO assumption is needed (est only ever takes minima).
* The liveness proof (induction on `k(u)` with cycle arguments) silently relies on the fact that
  a node's `core` is always a fixpoint of `computeIndex` on its current estimates (the `fix`
  invariant), i.e. that once the final estimates have arrived, `u` has already lowered its `core`
  accordingly. This holds because `computeIndex` is rerun after every decrease of an estimate.
-/

open Finset Filter

set_option linter.unusedSectionVars false

namespace KCoreDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Two facts about the handler `receive` -/

theorem receive_est_apply (u : V) (s : NodeState V) (v : V) (k : ℕ) (w : V) :
    (receive G u s (v, k)).est w = if w = v then min (s.est v) (k : ℕ∞) else s.est w := by
  have key : (receive G u s (v, k)).est =
      if (k : ℕ∞) < s.est v then Function.update s.est v (k : ℕ∞) else s.est := by
    unfold receive; split_ifs <;> rfl
  rw [key]
  by_cases h1 : (k : ℕ∞) < s.est v <;> by_cases hw : w = v
  · subst hw; simp [h1, min_eq_right h1.le]
  · simp [h1, hw]
  · subst hw; simp [h1, min_eq_left (not_lt.1 h1)]
  · simp [h1, hw]

/-- `receive` preserves the property that `core` is a fixpoint of `computeIndex` on the current
estimates. -/
theorem receive_fix (u : V) (s : NodeState V) (m : V × ℕ)
    (h : computeIndex G s.est u s.core = s.core) :
    computeIndex G (receive G u s m).est u (receive G u s m).core = (receive G u s m).core := by
  unfold receive
  split_ifs with h1 h2
  · exact computeIndex_idem _ _ _
  · exact le_antisymm (computeIndex_le _ _ _) (not_lt.1 h2)
  · exact h

namespace Async

/-! ### The model -/

/-- A message in transit: `(sender, receiver, value)`. -/
abbrev Msg (V : Type*) := V × V × ℕ

/-- Global state of the asynchronous system. -/
structure GState (V : Type*) where
  /-- local states of the nodes -/
  st : V → NodeState V
  /-- messages in transit -/
  net : Multiset (Msg V)

/-- The atomic events of an execution. -/
inductive Action (V : Type*)
  /-- delivery of (one copy of) a message in transit -/
  | deliver (m : Msg V)
  /-- node `u` executes its periodic block `repeat every δ` -/
  | tick (u : V)

/-- `send ⟨u, k⟩ to neighborV(u)`. -/
def bcast (u : V) (k : ℕ) : Multiset (Msg V) :=
  (G.neighborFinset u).val.map fun w => (u, w, k)

variable {G} in
theorem mem_bcast {u : V} {k : ℕ} {m : Msg V} :
    m ∈ bcast G u k ↔ m.1 = u ∧ G.Adj u m.2.1 ∧ m.2.2 = k := by
  rcases m with ⟨a, b, c⟩
  simp only [bcast, Multiset.mem_map, Finset.mem_val, SimpleGraph.mem_neighborFinset,
    Prod.mk.injEq]
  constructor
  · rintro ⟨w, hw, rfl, rfl, rfl⟩; exact ⟨rfl, hw, rfl⟩
  · rintro ⟨rfl, hw, rfl⟩; exact ⟨b, hw, rfl, rfl, rfl⟩

/-- Initial global state: `on initialization` has been executed by every node, and its broadcast
`⟨u, d(u)⟩` is in transit. -/
def initGState : GState V :=
  ⟨initState G, ∑ u, bcast G u (G.degree u)⟩

/-- Effect of one action. A `deliver m` with `m` not in transit is a no-op. -/
noncomputable def perform : Action V → GState V → GState V
  | .deliver m, s =>
    if m ∈ s.net then
      ⟨Function.update s.st m.2.1 (receive G m.2.1 (s.st m.2.1) (m.1, m.2.2)), s.net.erase m⟩
    else s
  | .tick u, s =>
    if (s.st u).changed then
      ⟨Function.update s.st u { s.st u with changed := false }, s.net + bcast G u (s.st u).core⟩
    else s

/-- The execution produced by the schedule `act`. -/
noncomputable def run (act : ℕ → Action V) : ℕ → GState V
  | 0 => initGState G
  | t + 1 => perform G (act t) (run act t)

@[simp] theorem run_zero (act : ℕ → Action V) : run G act 0 = initGState G := rfl

theorem run_succ (act : ℕ → Action V) (t : ℕ) :
    run G act (t + 1) = perform G (act t) (run G act t) := rfl

/-- Fairness: every node ticks infinitely often, and every message in transit is eventually
delivered. -/
def Fair (act : ℕ → Action V) : Prop :=
  (∀ u t, ∃ t' ≥ t, act t' = .tick u) ∧
    ∀ m t, m ∈ (run G act t).net → ∃ t' ≥ t, act t' = .deliver m ∧ m ∈ (run G act t').net

/-! ### Basic properties of one action -/

variable {G}

theorem perform_core_le (a : Action V) (s : GState V) (u : V) :
    ((perform G a s).st u).core ≤ (s.st u).core := by
  cases a with
  | deliver m =>
    simp only [perform]; split_ifs
    · simp only [Function.update_apply]; split_ifs with h
      · subst h; exact receive_core_le _ _ _
      · exact le_rfl
    · exact le_rfl
  | tick w =>
    simp only [perform]; split_ifs
    · simp only [Function.update_apply]; split_ifs with h
      · subst h; exact le_rfl
      · exact le_rfl
    · exact le_rfl

theorem perform_est_le (a : Action V) (s : GState V) (u v : V) :
    ((perform G a s).st u).est v ≤ (s.st u).est v := by
  cases a with
  | deliver m =>
    simp only [perform]; split_ifs
    · simp only [Function.update_apply]; split_ifs with h
      · subst h; exact receive_est_le _ _ _ _
      · exact le_rfl
    · exact le_rfl
  | tick w =>
    simp only [perform]; split_ifs
    · simp only [Function.update_apply]; split_ifs with h
      · subst h; exact le_rfl
      · exact le_rfl
    · exact le_rfl

/-- `changed` is only set when `core` decreases. -/
theorem perform_changed (a : Action V) (s : GState V) (u : V)
    (h : ((perform G a s).st u).changed = true) :
    (s.st u).changed = true ∨ ((perform G a s).st u).core < (s.st u).core := by
  cases a with
  | deliver m =>
    simp only [perform] at h ⊢; split_ifs at h ⊢
    · simp only [Function.update_apply] at h ⊢; split_ifs at h ⊢ with hu
      · subst hu; exact (receive_changed _ _ _).1 h
      · exact Or.inl h
    · exact Or.inl h
  | tick w =>
    simp only [perform] at h ⊢; split_ifs at h ⊢
    · simp only [Function.update_apply] at h ⊢
      split_ifs at h ⊢ with hu
      exact Or.inl h
    · exact Or.inl h

theorem perform_tick_changed (s : GState V) (u : V) :
    ((perform G (.tick u) s).st u).changed = false := by
  simp only [perform]; split_ifs with h
  · simp
  · simpa using h

theorem perform_deliver_est {s : GState V} {m : Msg V} (hm : m ∈ s.net) :
    ((perform G (.deliver m) s).st m.2.1).est m.1 ≤ m.2.2 := by
  simp only [perform, hm, ↓reduceIte, Function.update_self, receive_est_apply]
  exact min_le_right _ _

theorem mem_perform_net {s : GState V} {m : Msg V} (hm : m ∈ s.net) {a : Action V}
    (ha : a ≠ .deliver m) : m ∈ (perform G a s).net := by
  cases a with
  | deliver m' =>
    have : m ≠ m' := fun h => ha (h ▸ rfl)
    simp only [perform]; split_ifs
    · exact (Multiset.mem_erase_of_ne this).2 hm
    · exact hm
  | tick w =>
    simp only [perform]; split_ifs
    · exact Multiset.mem_add.2 (Or.inl hm)
    · exact hm

/-! ### The invariant -/

variable (G) in
/-- Inductive invariant of all reachable global states. -/
structure Inv (s : GState V) : Prop where
  core_le_degree : ∀ u, (s.st u).core ≤ G.degree u
  coreness_le_core : ∀ u, coreness G u ≤ (s.st u).core
  core_le_est : ∀ u v, ((s.st v).core : ℕ∞) ≤ (s.st u).est v
  core_le_net : ∀ m ∈ s.net, (s.st m.1).core ≤ m.2.2
  fix : ∀ u, computeIndex G (s.st u).est u (s.st u).core = (s.st u).core
  edge : ∀ u v, G.Adj u v →
    (s.st u).est v = (s.st v).core ∨ (v, u, (s.st v).core) ∈ s.net ∨ (s.st v).changed = true

theorem hIndex_top (u : V) : hIndex G (fun _ => ⊤) u = G.degree u := by
  refine le_antisymm (hIndex_le_degree _ _) (le_hIndex_iff.2 ?_)
  simp [nbrCount]

variable (G) in
theorem inv_init : Inv G (initGState G) where
  core_le_degree _ := le_rfl
  coreness_le_core u := coreness_le_degree u
  core_le_est _ _ := le_top
  core_le_net m hm := by
    obtain ⟨u, -, hu⟩ := Multiset.mem_sum.1 hm
    obtain ⟨rfl, -, h⟩ := mem_bcast.1 hu
    exact h.ge
  fix u := by
    change computeIndex G (fun _ => ⊤) u (G.degree u) = G.degree u
    rw [computeIndex_eq, hIndex_top]; split_ifs <;> omega
  edge u v h := Or.inr (Or.inl (Multiset.mem_sum.2 ⟨v, mem_univ _, mem_bcast.2 ⟨rfl, h.symm, rfl⟩⟩))

theorem Inv.coreness_le_est {s : GState V} (hs : Inv G s) (u v : V) :
    (coreness G v : ℕ∞) ≤ (s.st u).est v :=
  le_trans (by exact_mod_cast hs.coreness_le_core v) (hs.core_le_est u v)

theorem Inv.coreness_le_net {s : GState V} (hs : Inv G s) {m : Msg V} (hm : m ∈ s.net) :
    coreness G m.1 ≤ m.2.2 :=
  (hs.coreness_le_core _).trans (hs.core_le_net m hm)

/-- Estimates after a `receive` stay above any lower bound valid for the old estimates and the
received value. -/
theorem le_receive_est {a : V → ℕ∞} {u : V} {s : NodeState V} {v : V} {k : ℕ}
    (hs : ∀ w, a w ≤ s.est w) (hk : a v ≤ k) (w : V) : a w ≤ (receive G u s (v, k)).est w := by
  rw [receive_est_apply]
  split_ifs with h
  · subst h; exact le_min (hs w) hk
  · exact hs w

theorem inv_deliver {s : GState V} (hs : Inv G s) (m : Msg V) :
    Inv G (perform G (.deliver m) s) := by
  by_cases hm : m ∈ s.net
  swap
  · simpa [perform, hm] using hs
  rcases m with ⟨x, y, k⟩
  have hk : (s.st x).core ≤ k := hs.core_le_net _ hm
  set r := receive G y (s.st y) (x, k) with hr
  have hst : ∀ w, (perform G (.deliver (x, y, k)) s).st w = if w = y then r else s.st w := by
    intro w; simp only [perform, hm, ↓reduceIte, Function.update_apply]; rfl
  have hnet : (perform G (.deliver (x, y, k)) s).net = s.net.erase (x, y, k) := by
    simp only [perform, hm, ↓reduceIte]
  have hcore : ∀ w, ((perform G (.deliver (x, y, k)) s).st w).core ≤ (s.st w).core :=
    perform_core_le _ _
  have hrest : ∀ w, ((s.st w).core : ℕ∞) ≤ r.est w :=
    le_receive_est (fun w => hs.core_le_est y w) (by exact_mod_cast hk)
  constructor
  · intro u; exact (hcore u).trans (hs.core_le_degree u)
  · intro u
    rw [hst]; split_ifs with hu
    · subst hu
      rcases receive_cases (G := G) u (s.st u) (x, k) with h | h <;> rw [← hr] at h
      · rw [h]; exact hs.coreness_le_core u
      · rw [h]
        refine coreness_le_computeIndex (hs.coreness_le_core u) fun v _ => ?_
        exact le_receive_est (fun w => hs.coreness_le_est u w)
          (by exact_mod_cast hs.coreness_le_net hm) v
    · exact hs.coreness_le_core u
  · intro u v
    refine le_trans (by exact_mod_cast hcore v : ((perform G (.deliver (x, y, k)) s).st v).core ≤ ((s.st v).core : ℕ∞)) ?_
    rw [hst u]; split_ifs with hu
    · subst hu; exact hrest v
    · exact hs.core_le_est u v
  · intro m' hm'
    rw [hnet] at hm'
    exact (hcore _).trans (hs.core_le_net m' (Multiset.mem_of_mem_erase hm'))
  · intro u
    rw [hst]; split_ifs with hu
    · subst hu; exact receive_fix G u _ _ (hs.fix u)
    · exact hs.fix u
  · intro u v huv
    have hvu : v ≠ u := huv.ne.symm
    set s' := perform G (.deliver (x, y, k)) s
    have hle : ((s'.st v).core : ℕ∞) ≤ (s'.st u).est v :=
      le_trans (by exact_mod_cast hcore v : ((s'.st v).core : ℕ∞) ≤ (s.st v).core) (by
        rw [hst u]; split_ifs with hu
        · subst hu; exact hrest v
        · exact hs.core_le_est u v)
    rcases lt_or_eq_of_le (hcore v) with hlt | heq
    · -- `core_v` dropped: `changed_v` was set
      refine Or.inr (Or.inr ?_)
      have : v = y := by
        by_contra hv
        simp only [hst v, hv, ↓reduceIte] at hlt
        exact lt_irrefl _ hlt
      subst this
      simp only [hst v, ↓reduceIte] at hlt ⊢
      exact (receive_changed _ _ _).2 (Or.inr hlt)
    · rw [heq]
      rcases hs.edge u v huv with h | h | h
      · refine Or.inl (le_antisymm ?_ (heq ▸ hle))
        rw [← h]; exact perform_est_le _ _ _ _
      · by_cases hmm : (v, u, (s.st v).core) = (x, y, k)
        · simp only [Prod.mk.injEq] at hmm
          obtain ⟨rfl, rfl, hk'⟩ := hmm
          refine Or.inl (le_antisymm ?_ (heq ▸ hle))
          have := perform_deliver_est (G := G) hm
          simpa [hk'] using this
        · exact Or.inr (Or.inl (by rw [hnet]; exact (Multiset.mem_erase_of_ne hmm).2 h))
      · refine Or.inr (Or.inr ?_)
        rw [hst v]; split_ifs with hv
        · subst hv; exact (receive_changed _ _ _).2 (Or.inl h)
        · exact h

theorem inv_tick {s : GState V} (hs : Inv G s) (w : V) : Inv G (perform G (.tick w) s) := by
  by_cases hw : (s.st w).changed = true
  swap
  · simpa [perform, hw] using hs
  have hcore : ∀ u, ((perform G (.tick w) s).st u).core = (s.st u).core := by
    intro u; simp only [perform, hw, ↓reduceIte, Function.update_apply]; split_ifs with h
    · subst h; rfl
    · rfl
  have hest : ∀ u, ((perform G (.tick w) s).st u).est = (s.st u).est := by
    intro u; simp only [perform, hw, ↓reduceIte, Function.update_apply]; split_ifs with h
    · subst h; rfl
    · rfl
  have hch : ∀ u, u ≠ w → ((perform G (.tick w) s).st u).changed = (s.st u).changed := by
    intro u hu; simp only [perform, hw, ↓reduceIte, Function.update_apply, hu, ↓reduceIte]
  have hnet : (perform G (.tick w) s).net = s.net + bcast G w (s.st w).core := by
    simp only [perform, hw, ↓reduceIte]
  constructor
  · intro u; rw [hcore]; exact hs.core_le_degree u
  · intro u; rw [hcore]; exact hs.coreness_le_core u
  · intro u v; rw [hcore, hest]; exact hs.core_le_est u v
  · intro m hm
    rw [hcore]
    rw [hnet, Multiset.mem_add] at hm
    rcases hm with hm | hm
    · exact hs.core_le_net m hm
    · obtain ⟨h1, -, h2⟩ := mem_bcast.1 hm
      rw [h1, h2]
  · intro u; rw [hcore, hest]; exact hs.fix u
  · intro u v huv
    rw [hcore, hest, hnet]
    by_cases hv : v = w
    · subst hv
      exact Or.inr (Or.inl (Multiset.mem_add.2 (Or.inr (mem_bcast.2 ⟨rfl, huv.symm, rfl⟩))))
    · rw [hch v hv]
      rcases hs.edge u v huv with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Multiset.mem_add.2 (Or.inl h)))
      · exact Or.inr (Or.inr h)

theorem Inv.perform {s : GState V} (hs : Inv G s) (a : Action V) : Inv G (perform G a s) := by
  cases a with
  | deliver m => exact inv_deliver hs m
  | tick w => exact inv_tick hs w

variable (G) in
theorem inv_run (act : ℕ → Action V) : ∀ t, Inv G (run G act t)
  | 0 => inv_init G
  | t + 1 => (inv_run act t).perform (act t)

/-! ### Theorem 2 (Safety) -/

/-- **Theorem 2 (Safety)** of the paper, asynchronous version: in every execution (no fairness
needed), at all times the variable `core` of every node `u` is at least `k(u)`. -/
theorem theorem_2 (act : ℕ → Action V) (t : ℕ) (u : V) :
    coreness G u ≤ ((run G act t).st u).core :=
  (inv_run G act t).coreness_le_core u

/-- All estimates `est_u[v]` are always at least `k(v)`. -/
theorem coreness_le_est (act : ℕ → Action V) (t : ℕ) (u v : V) :
    (coreness G v : ℕ∞) ≤ ((run G act t).st u).est v :=
  (inv_run G act t).coreness_le_est u v

/-- Every message in transit from `v` carries a value at least `k(v)`. -/
theorem coreness_le_of_mem_net (act : ℕ → Action V) (t : ℕ) {m : Msg V}
    (hm : m ∈ (run G act t).net) : coreness G m.1 ≤ m.2.2 :=
  (inv_run G act t).coreness_le_net hm

/-- The variable `core` never increases. -/
theorem core_anti (act : ℕ → Action V) (u : V) :
    Antitone fun t => ((run G act t).st u).core :=
  antitone_nat_of_succ_le fun t => perform_core_le (act t) _ u

theorem est_anti (act : ℕ → Action V) (u v : V) :
    Antitone fun t => ((run G act t).st u).est v :=
  antitone_nat_of_succ_le fun t => perform_est_le (act t) _ u v

/-! ### Theorem 3 (Liveness) -/

/-- **Theorem 3 (Liveness)** of the paper, asynchronous version: in every fair execution there is a
time after which the variable `core` of every node `u` is equal to `k(u)`. -/
theorem theorem_3 (act : ℕ → Action V) (hfair : Fair G act) :
    ∃ T, ∀ t ≥ T, ∀ u, ((run G act t).st u).core = coreness G u := by
  classical
  have hinv := inv_run G act
  -- the cores are eventually constant, equal to `c`
  have hstab : ∀ u, ∃ T, ∀ t ≥ T, ((run G act t).st u).core = ((run G act T).st u).core :=
    fun u => (Nat.eventually_const_of_succ_le (N := 0) fun t _ =>
      core_anti act u t.le_succ).imp fun _ h => h.2
  choose Tu hTu using hstab
  set c : V → ℕ := fun u => ((run G act (Tu u)).st u).core with hc_def
  have hc : ∀ᶠ t in atTop, ∀ u, ((run G act t).st u).core = c u :=
    eventually_all.2 fun u => eventually_atTop.2 ⟨Tu u, hTu u⟩
  obtain ⟨T0, hT0⟩ := eventually_atTop.1 hc
  -- all `changed` flags are eventually `false`
  have hch : ∀ u, ∀ᶠ t in atTop, ((run G act t).st u).changed = false := by
    intro u
    obtain ⟨t1, ht1, hact⟩ := hfair.1 u T0
    refine eventually_atTop.2 ⟨t1 + 1, fun t ht => ?_⟩
    induction t, ht using Nat.le_induction with
    | base => rw [run_succ, hact]; exact perform_tick_changed _ u
    | succ t ht ih =>
      cases h : ((run G act (t + 1)).st u).changed
      · rfl
      · rw [run_succ] at h
        rcases perform_changed _ _ u h with h' | h'
        · rw [ih] at h'; exact absurd h' (by simp)
        · rw [← run_succ, hT0 (t + 1) (by omega) u, hT0 t (by omega) u] at h'
          exact absurd h' (lt_irrefl _)
  -- every estimate on an edge is eventually exact
  have hest : ∀ u v, ∀ᶠ t in atTop, G.Adj u v → ((run G act t).st u).est v = c v := by
    intro u v
    by_cases huv : G.Adj u v
    swap
    · exact Eventually.of_forall fun _ h => absurd h huv
    obtain ⟨T1, hT1⟩ := eventually_atTop.1 ((hch v).and (eventually_ge_atTop T0))
    have : ∃ t2 ≥ T0, ((run G act t2).st u).est v ≤ c v := by
      obtain ⟨hchf, hT1T0⟩ := hT1 T1 le_rfl
      rcases (hinv T1).edge u v huv with h | h | h
      · exact ⟨T1, hT1T0, by rw [h, hT0 T1 hT1T0 v]⟩
      · rw [hT0 T1 hT1T0 v] at h
        obtain ⟨t2, ht2, hact, hmem⟩ := hfair.2 _ T1 h
        refine ⟨t2 + 1, by omega, ?_⟩
        rw [run_succ, hact]; exact perform_deliver_est hmem
      · rw [hchf] at h; exact absurd h (by simp)
    obtain ⟨t2, ht2, hle⟩ := this
    refine eventually_atTop.2 ⟨t2, fun t ht _ => le_antisymm ((est_anti act u v ht).trans hle) ?_⟩
    rw [← hT0 t (ht2.trans ht) v]; exact (hinv t).core_le_est u v
  -- at a time where both hold, `c` is a fixpoint of the synchronous step, hence the coreness
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (hc.and (eventually_all.2 fun u => eventually_all.2 fun v => hest u v))
  obtain ⟨h1, h2⟩ := hT T le_rfl
  have hfix : step G c = c := by
    funext u
    have hf := (hinv T).fix u
    rw [h1 u, computeIndex_congr (e' := toE c) (fun v hv => h2 u v hv)] at hf
    exact hf
  have hcc : c = coreness G :=
    eq_coreness_of_step_eq (fun v => by rw [← h1 v]; exact (hinv T).coreness_le_core v)
      (fun v => by rw [← h1 v]; exact (hinv T).core_le_degree v) hfix
  exact ⟨T, fun t ht u => by rw [(hT t ht).1 u, hcc]⟩

/-! ### Fair schedules exist -/

/-- A schedule in which every action occurs infinitely often is fair (a message in transit stays
in transit until the next `deliver` of it). -/
theorem fair_of_frequently (act : ℕ → Action V) (h : ∀ a t, ∃ t' ≥ t, act t' = a) :
    Fair G act := by
  classical
  refine ⟨fun u t => h _ t, fun m t hm => ?_⟩
  have hex : ∃ k, act (t + k) = .deliver m := by
    obtain ⟨t', ht', ha⟩ := h (.deliver m) t
    exact ⟨t' - t, by rw [Nat.add_sub_cancel' ht']; exact ha⟩
  have hmem : ∀ j ≤ Nat.find hex, m ∈ (run G act (t + j)).net := by
    intro j hj
    induction j with
    | zero => exact hm
    | succ j ih =>
      rw [← Nat.add_assoc, run_succ]
      exact mem_perform_net (ih (by omega)) (Nat.find_min hex (by omega))
  exact ⟨t + Nat.find hex, Nat.le_add_right _ _, Nat.find_spec hex, hmem _ le_rfl⟩

instance : Countable (Action V) := by
  refine Function.Injective.countable (f := fun a : Action V => match a with
    | .deliver m => (Sum.inl m : Msg V ⊕ V)
    | .tick u => Sum.inr u) ?_
  intro a b hab
  cases a <;> cases b <;> simp_all

variable (G) in
/-- Non-vacuity of Theorem 3: fair schedules exist (for a non-empty set of nodes). -/
theorem exists_fair [Nonempty V] : ∃ act : ℕ → Action V, Fair G act := by
  have : Nonempty (Action V) := ⟨.tick (Classical.arbitrary V)⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat (Action V)
  refine ⟨fun t => f (Nat.unpair t).1, fair_of_frequently _ fun a t => ?_⟩
  obtain ⟨n, rfl⟩ := hf a
  exact ⟨Nat.pair n t, Nat.right_le_pair n t, by simp⟩

end Async

end KCoreDecomposition
