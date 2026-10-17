import Papers.PODC2011.KCoreDecomposition.Trajectory

/-!
# One host, multiple nodes (§3.2, Algorithms 3 and 4) in synchronous rounds

Montresor, De Pellegrini, Miorandi, *Distributed k-Core Decomposition*, PODC 2011
(arXiv 1103.5320v2), §3.2. The paper proves safety and liveness only for the one-to-one version
and says (§4) that "the results can be easily extended to the one-to-many case". Here we do this
extension for the synchronous round model of §4.2, and prove in addition that the one-to-many
version is never slower (in rounds) than the one-to-one version.

## Model

* A finite set of hosts `H` and an assignment `h : V → H`; host `x` is responsible for
  `own h x = {u | h u = x}` (the paper's `V(x)`).
* Host state `HostState` (Algorithm 3): `est : V → ℕ∞` (`⊤` = `+∞`; one entry per node, entries of
  nodes that are neither own nodes nor neighbours of own nodes are never read) and
  `changed : V → Bool`.
* `improveEstimate G L s` is Algorithm 4: passes over the list `L` of own nodes (an **arbitrary
  order**, duplicates allowed) doing `k ← computeIndex(est, u, est[u]); if k < est[u] then
  est[u] ← k, changed[u] ← true`, repeated until a pass changes nothing. It is defined by
  well-founded recursion (the measure `pot` decreases at each pass that changes something);
  `improvePass_improveEstimate`: the last pass changes nothing (termination of the `while` loop).
* `improveEstimate_isGreatest`: the result is the **greatest** vector below the input that is
  quiescent on `L` (`Quiescent`: no own node can improve its estimate). Hence it does not depend on
  the order of `L` (`improveEstimate_congr`) and processing messages one at a time with an
  `improveEstimate` after each one (as in Algorithm 3) gives the same state as processing them all
  and calling `improveEstimate` once (`receiveSeq_improveEstimate`).
* Messages are sets `S` of pairs `(v, k)`; receiving `S` performs
  `foreach (v, k) ∈ S: if k < est[v] then est[v] ← k`, i.e. `est[v] ← min(est[v], min_{(v,k)∈S} k)`
  (`receive`).
* Synchronous rounds (`run G h ord r` is the global state at the end of round `r + 1`):
  - round 1: `est[v] = d(v)` for own `v`, `+∞` otherwise; `improveEstimate`; send all own estimates
    (`allMsg`); reset `changed`;
  - round `r + 2`: receive all sets sent in round `r + 1` by the **other** hosts (broadcast policy
    of Algorithm 3; only the senders' own nodes appear in them), `improveEstimate`, send
    `S = {(u, est[u]) : u own, changed[u]}` (`changedMsg`; `S = ∅` means nothing is sent), reset
    `changed`. All messages of a round are processed and then `improveEstimate` is called once;
    `run_succ_host_eq_receiveSeq` shows this is the same as Algorithm 3's per-message handler, for
    every order of the messages.
  - The pass order of host `x` is `ord x`, any list whose members are exactly the own nodes
    (`hord`); `run_congr_ord`: the run does not depend on it.
  No failures, reliable channels. Algorithm 5 (point-to-point policy) is not modelled; as printed
  it sends all boundary estimates to every neighbour host in every round, without testing
  `changed[u]` and without resetting it, so it never becomes silent.

The run is a total deterministic function of `(G, h, ord)`, so the theorems below are about actual
executions and are not vacuous.

## Results

* `safety` (Theorem 2): every entry of `est` at every host in every round is `≥ k(v)`;
  `safety_sent`: so is every value in every message; `ownEst_ne_top`: own estimates are finite.
* `ownEst_le_traj` (speed comparison): the estimate of `u` at its host at the end of round `s + 1`
  is `≤ traj G s u`, the estimate of the one-to-one algorithm at the end of round `s + 1`
  (`Run.run_spec`). Hence `liveness`: from round `stab G + 1` on (the round at which the one-to-one
  version is correct), every host knows the exact coreness of its own nodes.
* `est_eq_coreness`, `sent_eq_empty`, `theorem_3_multiHost` (Theorem 3): from round `stab G + 2` on
  every entry of every host is the coreness and no host sends anything.
-/

open Finset

set_option linter.unusedSectionVars false

namespace KCoreDecomposition

namespace MultiHost

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Host state and Algorithm 4 -/

/-- The variables of a host in Algorithm 3. -/
@[ext] structure HostState (V : Type*) where
  /-- `est[v]`: the most up-to-date estimate of the coreness of `v` (`⊤` = `+∞`) -/
  est : V → ℕ∞
  /-- `changed[v]`: the estimate of the own node `v` changed since the last broadcast -/
  changed : V → Bool

/-- `computeIndex(est, u, est[u])`, the value computed in the loop body of Algorithm 4. -/
noncomputable def newEst (e : V → ℕ∞) (u : V) : ℕ := computeIndex G e u (e u).toNat

/-- The body of the `foreach` loop of Algorithm 4, for node `u`:
`k ← computeIndex(est, u, est[u]); if k < est[u] then est[u] ← k; changed[u] ← true`. -/
noncomputable def updateNode (s : HostState V) (u : V) : HostState V :=
  if (newEst G s.est u : ℕ∞) < s.est u then
    ⟨Function.update s.est u (newEst G s.est u), Function.update s.changed u true⟩
  else s

/-- One pass of the `while` loop of Algorithm 4 over the own nodes, in the order `L`. -/
noncomputable def improvePass (L : List V) (s : HostState V) : HostState V :=
  L.foldl (updateNode G) s

/-- The vector `p` is quiescent on `L`: no node of `L` can lower its estimate. -/
def Quiescent (L : List V) (p : V → ℕ∞) : Prop := ∀ u ∈ L, p u ≤ newEst G p u

/-- Termination measure for Algorithm 4. -/
def potTerm (x : ℕ∞) : ℕ := x.toNat + if x = ⊤ then 1 else 0

/-- Termination measure for Algorithm 4: it decreases at every pass that changes something. -/
def pot (e : V → ℕ∞) : ℕ := ∑ v, potTerm (e v)

theorem newEst_le_toNat (e : V → ℕ∞) (u : V) : newEst G e u ≤ (e u).toNat :=
  computeIndex_le _ _ _

theorem potTerm_lt {k : ℕ} {x : ℕ∞} (hk : k ≤ x.toNat) (hlt : (k : ℕ∞) < x) :
    potTerm (k : ℕ∞) < potTerm x := by
  induction x using ENat.recTopCoe with
  | top => simp only [ENat.toNat_top, nonpos_iff_eq_zero] at hk; subst hk; simp [potTerm]
  | coe n => simp only [potTerm, ENat.toNat_natCast, ENat.natCast_ne_top, ↓reduceIte,
      Nat.cast_lt, add_zero] at hk hlt ⊢; omega

theorem updateNode_eq_or_lt (s : HostState V) (u : V) :
    updateNode G s u = s ∨ pot (updateNode G s u).est < pot s.est := by
  unfold updateNode
  split_ifs with hlt
  · right
    show ∑ v, potTerm (Function.update s.est u (newEst G s.est u : ℕ∞) v) < ∑ v, potTerm (s.est v)
    have key := potTerm_lt (newEst_le_toNat G s.est u) hlt
    apply Finset.sum_lt_sum
    · intro v _
      rcases eq_or_ne v u with rfl | hne
      · rw [Function.update_self]; exact key.le
      · rw [Function.update_of_ne hne]
    · exact ⟨u, mem_univ _, by rw [Function.update_self]; exact key⟩
  · left; rfl

theorem updateNode_est_le (s : HostState V) (u v : V) : (updateNode G s u).est v ≤ s.est v := by
  unfold updateNode
  split_ifs with hlt
  · rcases eq_or_ne v u with rfl | hne
    · simpa using hlt.le
    · simp [Function.update_of_ne hne]
  · exact le_rfl

theorem updateNode_est_of_ne (s : HostState V) {u v : V} (hne : v ≠ u) :
    (updateNode G s u).est v = s.est v := by
  unfold updateNode; split_ifs <;> simp [Function.update_of_ne hne]

theorem updateNode_changed (s : HostState V) (u v : V) :
    (updateNode G s u).changed v =
      (s.changed v || decide ((updateNode G s u).est v ≠ s.est v)) := by
  unfold updateNode
  split_ifs with hlt
  · rcases eq_or_ne v u with rfl | hne
    · simp [hlt.ne]
    · simp [Function.update_of_ne hne]
  · simp

theorem updateNode_eq_self_iff (s : HostState V) (u : V) :
    updateNode G s u = s ↔ s.est u ≤ newEst G s.est u := by
  unfold updateNode
  split_ifs with hlt
  · refine iff_of_false (fun h => ?_) (not_le.2 hlt)
    have := congrArg (fun t : HostState V => t.est u) h
    simp only [Function.update_self] at this
    exact hlt.ne this
  · exact iff_of_true rfl (not_lt.1 hlt)

theorem updateNode_eq_of_est_eq (s : HostState V) (u : V) (h : (updateNode G s u).est = s.est) :
    updateNode G s u = s := by
  by_contra hne
  have hlt := not_le.1 ((updateNode_eq_self_iff G s u).not.1 hne)
  have := congrFun h u
  unfold updateNode at this
  simp only [hlt, ↓reduceIte, Function.update_self] at this
  exact hlt.ne this

theorem updateNode_max {p : V → ℕ∞} {s : HostState V} {u : V} (hp : ∀ v, p v ≤ s.est v)
    (hfin : s.est u ≠ ⊤) (hq : p u ≤ newEst G p u) (v : V) : p v ≤ (updateNode G s u).est v := by
  unfold updateNode
  split_ifs with hlt
  · rcases eq_or_ne v u with rfl | hne
    · simp only [Function.update_self]
      exact hq.trans (Nat.cast_le.2
        (computeIndex_mono (fun w _ => hp w) (ENat.toNat_le_toNat (hp _) hfin)))
    · simp only [Function.update_of_ne hne]; exact hp v
  · exact hp v

/-- Bookkeeping of the `changed` flags along two successive decreases. -/
theorem changed_trans {c : Bool} {a b d : ℕ∞} (hab : a ≤ b) (hbd : b ≤ d) :
    ((c || decide (b ≠ d)) || decide (a ≠ b)) = (c || decide (a ≠ d)) := by
  by_cases h : b = d
  · subst h; simp
  · have : a ≠ d := fun h' => h (le_antisymm hbd (h'.symm.le.trans hab))
    simp [h, this]

/-! #### One pass -/

@[simp] theorem improvePass_nil (s : HostState V) : improvePass G [] s = s := rfl

@[simp] theorem improvePass_cons (u : V) (L : List V) (s : HostState V) :
    improvePass G (u :: L) s = improvePass G L (updateNode G s u) := rfl

theorem improvePass_eq_or_lt (L : List V) (s : HostState V) :
    improvePass G L s = s ∨ pot (improvePass G L s).est < pot s.est := by
  induction L generalizing s with
  | nil => exact Or.inl rfl
  | cons u L ih =>
    rw [improvePass_cons]
    rcases updateNode_eq_or_lt G s u with h | h
    · rw [h]; exact ih s
    · rcases ih (updateNode G s u) with h' | h'
      · right; rw [h']; exact h
      · exact Or.inr (h'.trans h)

theorem improvePass_est_le (L : List V) (s : HostState V) (v : V) :
    (improvePass G L s).est v ≤ s.est v := by
  induction L generalizing s with
  | nil => exact le_rfl
  | cons u L ih => exact (ih _).trans (updateNode_est_le G s u v)

theorem improvePass_est_of_not_mem {L : List V} {v : V} (hv : v ∉ L) (s : HostState V) :
    (improvePass G L s).est v = s.est v := by
  induction L generalizing s with
  | nil => rfl
  | cons u L ih =>
    rw [List.mem_cons, not_or] at hv
    rw [improvePass_cons, ih hv.2, updateNode_est_of_ne G s hv.1]

theorem improvePass_max {p : V → ℕ∞} (L : List V) (hq : Quiescent G L p) (s : HostState V)
    (hp : ∀ v, p v ≤ s.est v) (hfin : ∀ u ∈ L, s.est u ≠ ⊤) (v : V) :
    p v ≤ (improvePass G L s).est v := by
  induction L generalizing s with
  | nil => exact hp v
  | cons u L ih =>
    exact ih (fun w hw => hq w (List.mem_cons_of_mem _ hw)) _
      (updateNode_max G hp (hfin u (by simp)) (hq u (by simp)))
      (fun w hw => ne_top_of_le_ne_top (hfin w (List.mem_cons_of_mem _ hw))
        (updateNode_est_le G s u w))

theorem improvePass_changed (L : List V) (s : HostState V) (v : V) :
    (improvePass G L s).changed v =
      (s.changed v || decide ((improvePass G L s).est v ≠ s.est v)) := by
  induction L generalizing s with
  | nil => simp
  | cons u L ih =>
    rw [improvePass_cons, ih, updateNode_changed]
    exact changed_trans (improvePass_est_le G L _ v) (updateNode_est_le G s u v)

theorem improvePass_quiescent (L : List V) (s : HostState V) (h : improvePass G L s = s) :
    Quiescent G L s.est := by
  induction L generalizing s with
  | nil => intro u hu; simp at hu
  | cons u L ih =>
    rw [improvePass_cons] at h
    have hs : updateNode G s u = s := by
      apply updateNode_eq_of_est_eq
      funext v
      refine le_antisymm (updateNode_est_le G s u v) ?_
      calc s.est v = (improvePass G L (updateNode G s u)).est v := by rw [h]
        _ ≤ _ := improvePass_est_le G L _ v
    rw [hs] at h
    intro w hw
    rcases List.mem_cons.1 hw with hw' | hw'
    · rw [hw']; exact (updateNode_eq_self_iff G s u).1 hs
    · exact ih s h w hw'

theorem improvePass_of_quiescent (L : List V) (s : HostState V) (h : Quiescent G L s.est) :
    improvePass G L s = s := by
  induction L with
  | nil => rfl
  | cons u L ih =>
    rw [improvePass_cons, (updateNode_eq_self_iff G s u).2 (h u (by simp))]
    exact ih fun w hw => h w (by simp [hw])

/-! #### Algorithm 4: `improveEstimate` -/

open Classical in
/-- **Algorithm 4**, `improveEstimate`: repeat passes over the own nodes `L` (`again ← true` iff a
pass changed something, i.e. iff the state changed) until a pass changes nothing. Terminates
because `pot` decreases at every changing pass. -/
noncomputable def improveEstimate (L : List V) (s : HostState V) : HostState V :=
  if _h : improvePass G L s = s then s else improveEstimate L (improvePass G L s)
termination_by pot s.est
decreasing_by exact (improvePass_eq_or_lt G L s).resolve_left _h

theorem improveEstimate_of_eq {L : List V} {s : HostState V} (h : improvePass G L s = s) :
    improveEstimate G L s = s := by
  rw [improveEstimate]; simp [h]

theorem improveEstimate_of_ne {L : List V} {s : HostState V} (h : improvePass G L s ≠ s) :
    improveEstimate G L s = improveEstimate G L (improvePass G L s) := by
  rw [improveEstimate]; simp [h]

/-- Induction principle following the loop of Algorithm 4. -/
theorem improveEstimate_induction (L : List V) {motive : HostState V → Prop}
    (base : ∀ s, improvePass G L s = s → motive s)
    (step : ∀ s, improvePass G L s ≠ s → motive (improvePass G L s) → motive s)
    (s : HostState V) : motive s := by
  induction hn : pot s.est using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases h : improvePass G L s = s
    · exact base s h
    · exact step s h (ih _ (hn ▸ (improvePass_eq_or_lt G L s).resolve_left h) _ rfl)

/-- **Termination of Algorithm 4**: the loop stops at a state where a further pass changes
nothing. -/
theorem improvePass_improveEstimate (L : List V) (s : HostState V) :
    improvePass G L (improveEstimate G L s) = improveEstimate G L s := by
  refine improveEstimate_induction G L (motive := fun s =>
    improvePass G L (improveEstimate G L s) = improveEstimate G L s) ?_ ?_ s
  · intro s h; rw [improveEstimate_of_eq G h, h]
  · intro s h ih; rw [improveEstimate_of_ne G h]; exact ih

theorem improveEstimate_quiescent (L : List V) (s : HostState V) :
    Quiescent G L (improveEstimate G L s).est :=
  improvePass_quiescent G L _ (improvePass_improveEstimate G L s)

theorem improveEstimate_est_le (L : List V) (s : HostState V) (v : V) :
    (improveEstimate G L s).est v ≤ s.est v := by
  refine improveEstimate_induction G L
    (motive := fun s => (improveEstimate G L s).est v ≤ s.est v) ?_ ?_ s
  · intro s h; rw [improveEstimate_of_eq G h]
  · intro s h ih; rw [improveEstimate_of_ne G h]; exact ih.trans (improvePass_est_le G L s v)

theorem improveEstimate_est_of_not_mem {L : List V} {v : V} (hv : v ∉ L) (s : HostState V) :
    (improveEstimate G L s).est v = s.est v := by
  refine improveEstimate_induction G L
    (motive := fun s => (improveEstimate G L s).est v = s.est v) ?_ ?_ s
  · intro s h; rw [improveEstimate_of_eq G h]
  · intro s h ih; rw [improveEstimate_of_ne G h, ih, improvePass_est_of_not_mem G hv]

theorem improveEstimate_max {L : List V} {p : V → ℕ∞} (hq : Quiescent G L p) (s : HostState V)
    (hp : ∀ v, p v ≤ s.est v) (hfin : ∀ u ∈ L, s.est u ≠ ⊤) (v : V) :
    p v ≤ (improveEstimate G L s).est v := by
  refine improveEstimate_induction G L (motive := fun s => (∀ v, p v ≤ s.est v) →
    (∀ u ∈ L, s.est u ≠ ⊤) → p v ≤ (improveEstimate G L s).est v) ?_ ?_ s hp hfin
  · intro s h hp _; rw [improveEstimate_of_eq G h]; exact hp v
  · intro s h ih hp hfin
    rw [improveEstimate_of_ne G h]
    exact ih (improvePass_max G L hq s hp hfin)
      (fun u hu => ne_top_of_le_ne_top (hfin u hu) (improvePass_est_le G L s u))

theorem improveEstimate_changed (L : List V) (s : HostState V) (v : V) :
    (improveEstimate G L s).changed v =
      (s.changed v || decide ((improveEstimate G L s).est v ≠ s.est v)) := by
  refine improveEstimate_induction G L (motive := fun s => (improveEstimate G L s).changed v =
      (s.changed v || decide ((improveEstimate G L s).est v ≠ s.est v))) ?_ ?_ s
  · intro s h; rw [improveEstimate_of_eq G h]; simp
  · intro s h ih
    rw [improveEstimate_of_ne G h, ih, improvePass_changed]
    exact changed_trans (improveEstimate_est_le G L _ v) (improvePass_est_le G L s v)

theorem improveEstimate_est_ne_top (L : List V) {s : HostState V} {v : V} (h : s.est v ≠ ⊤) :
    (improveEstimate G L s).est v ≠ ⊤ :=
  ne_top_of_le_ne_top h (improveEstimate_est_le G L s v)

/-- **Characterization of Algorithm 4.** If the own estimates are finite, `improveEstimate`
returns the greatest vector below its input that is quiescent on the own nodes (in particular the
result does not depend on the order of the passes). -/
theorem improveEstimate_isGreatest (L : List V) (s : HostState V) (hfin : ∀ u ∈ L, s.est u ≠ ⊤) :
    IsGreatest {p : V → ℕ∞ | p ≤ s.est ∧ Quiescent G L p} (improveEstimate G L s).est :=
  ⟨⟨fun v => improveEstimate_est_le G L s v, improveEstimate_quiescent G L s⟩,
    fun _ hp v => improveEstimate_max G hp.2 s hp.1 hfin v⟩

theorem improveEstimate_of_quiescent {L : List V} {s : HostState V} (h : Quiescent G L s.est) :
    improveEstimate G L s = s :=
  improveEstimate_of_eq G (improvePass_of_quiescent G L s h)

theorem quiescent_congr {L L' : List V} (h : ∀ u, u ∈ L ↔ u ∈ L') {p : V → ℕ∞} :
    Quiescent G L p ↔ Quiescent G L' p := by
  simp [Quiescent, h]

/-- The result of Algorithm 4 does not depend on the order in which the own nodes are visited. -/
theorem improveEstimate_congr {L L' : List V} (h : ∀ u, u ∈ L ↔ u ∈ L') (s : HostState V)
    (hfin : ∀ u ∈ L, s.est u ≠ ⊤) : improveEstimate G L s = improveEstimate G L' s := by
  have hfin' : ∀ u ∈ L', s.est u ≠ ⊤ := fun u hu => hfin u ((h u).2 hu)
  have hest : (improveEstimate G L s).est = (improveEstimate G L' s).est := funext fun v =>
    le_antisymm
      (improveEstimate_max G ((quiescent_congr G h).1 (improveEstimate_quiescent G L s)) s
        (improveEstimate_est_le G L s) hfin' v)
      (improveEstimate_max G ((quiescent_congr G h).2 (improveEstimate_quiescent G L' s)) s
        (improveEstimate_est_le G L' s) hfin v)
  exact HostState.ext hest (funext fun v => by
    rw [improveEstimate_changed, improveEstimate_changed, hest])

/-- The true corenesses are quiescent (Theorem 1). -/
theorem quiescent_coreness (L : List V) : Quiescent G L (fun v => (coreness G v : ℕ∞)) := by
  intro u _
  have h := congrFun (step_coreness (G := G)) u
  simp only [newEst, ENat.toNat_natCast]
  exact Nat.cast_le.2 h.symm.le

/-! ### Messages -/

/-- The value that the set `S` of pairs carries for `v` (`⊤` if `v` does not occur). -/
noncomputable def msgVal (S : Finset (V × ℕ∞)) (v : V) : ℕ∞ := (S.filter fun p => p.1 = v).inf Prod.snd

/-- `on receive ⟨S⟩: foreach (v, k) ∈ S do if k < est[v] then est[v] ← k` (Algorithm 3). -/
noncomputable def receive (S : Finset (V × ℕ∞)) (s : HostState V) : HostState V :=
  ⟨fun v => min (s.est v) (msgVal S v), s.changed⟩

theorem msgVal_union (S T : Finset (V × ℕ∞)) (v : V) :
    msgVal (S ∪ T) v = min (msgVal S v) (msgVal T v) := by
  simp [msgVal, filter_union, inf_union]

theorem receive_empty (s : HostState V) : receive ∅ s = s :=
  HostState.ext (funext fun v => by simp [receive, msgVal]) rfl

theorem receive_receive (S T : Finset (V × ℕ∞)) (s : HostState V) :
    receive T (receive S s) = receive (S ∪ T) s :=
  HostState.ext (funext fun v => by simp [receive, msgVal_union, min_assoc]) rfl

theorem msgVal_eq_top {S : Finset (V × ℕ∞)} {v : V} (hS : ∀ p ∈ S, p.1 ≠ v) : msgVal S v = ⊤ := by
  rw [msgVal, Finset.inf_eq_top_iff]
  intro p hp
  exact absurd (mem_filter.1 hp).2 (hS p (mem_filter.1 hp).1)

theorem msgVal_image (A : Finset V) (e : V → ℕ∞) (v : V) :
    msgVal (A.image fun u => (u, e u)) v = if v ∈ A then e v else ⊤ := by
  split_ifs with hv
  · unfold msgVal
    refine le_antisymm (Finset.inf_le (f := Prod.snd) (b := (v, e v)) (by simp [hv]))
      (Finset.le_inf fun p hp => ?_)
    simp only [mem_filter, mem_image] at hp
    obtain ⟨⟨u, _, rfl⟩, rfl⟩ := hp
    exact le_rfl
  · refine msgVal_eq_top fun p hp hpv => ?_
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hp
    simp only at hpv
    subst hpv
    exact hv hu

/-- Processing messages one at a time, calling `improveEstimate` after each one, as the handler
`on receive` of Algorithm 3 does. -/
noncomputable def receiveSeq (L : List V) : List (Finset (V × ℕ∞)) → HostState V → HostState V
  | [], s => s
  | S :: ms, s => receiveSeq L ms (improveEstimate G L (receive S s))

/-- Receiving a message after `improveEstimate` and improving again is the same as receiving it
first and improving once (for messages that do not concern own nodes). -/
theorem improveEstimate_receive_improveEstimate {L : List V} {S : Finset (V × ℕ∞)}
    {s : HostState V} (hfin : ∀ u ∈ L, s.est u ≠ ⊤) (hS : ∀ u ∈ L, msgVal S u = ⊤) :
    improveEstimate G L (receive S (improveEstimate G L s)) =
      improveEstimate G L (receive S s) := by
  have hfinA : ∀ u ∈ L, (receive S (improveEstimate G L s)).est u ≠ ⊤ := fun u hu =>
    ne_top_of_le_ne_top (improveEstimate_est_ne_top G L (hfin u hu)) (min_le_left _ _)
  have hfinB : ∀ u ∈ L, (receive S s).est u ≠ ⊤ := fun u hu =>
    ne_top_of_le_ne_top (hfin u hu) (min_le_left _ _)
  have hAB : ∀ v, (improveEstimate G L (receive S (improveEstimate G L s))).est v ≤
      (improveEstimate G L (receive S s)).est v :=
    improveEstimate_max G (improveEstimate_quiescent G L _) _
      (fun v => (improveEstimate_est_le G L _ v).trans
        (min_le_min_right _ (improveEstimate_est_le G L s v))) hfinB
  have hBI : ∀ v, (improveEstimate G L (receive S s)).est v ≤ (improveEstimate G L s).est v :=
    improveEstimate_max G (improveEstimate_quiescent G L _) s
      (fun w => (improveEstimate_est_le G L (receive S s) w).trans (min_le_left _ _)) hfin
  have hBA : ∀ v, (improveEstimate G L (receive S s)).est v ≤
      (improveEstimate G L (receive S (improveEstimate G L s))).est v :=
    improveEstimate_max G (improveEstimate_quiescent G L _) _ (fun v =>
      le_min (hBI v) ((improveEstimate_est_le G L (receive S s) v).trans (min_le_right _ _))) hfinA
  have hest : (improveEstimate G L (receive S (improveEstimate G L s))).est =
      (improveEstimate G L (receive S s)).est := funext fun v => le_antisymm (hAB v) (hBA v)
  refine HostState.ext hest (funext fun v => ?_)
  rw [improveEstimate_changed G L _ v, improveEstimate_changed G L _ v, hest]
  simp only [receive]
  rw [improveEstimate_changed G L s v]
  by_cases hv : v ∈ L
  · simp only [hS v hv, le_top, min_eq_left]
    exact changed_trans (hBI v) (improveEstimate_est_le G L s v)
  · simp only [improveEstimate_est_of_not_mem G hv s, ne_eq, not_true_eq_false, decide_false,
      Bool.or_false]
    all_goals (try congr 1)

/-- **Per-message processing (Algorithm 3) = batch processing.** -/
theorem receiveSeq_improveEstimate (L : List V) :
    ∀ (ms : List (Finset (V × ℕ∞))) (s : HostState V), (∀ u ∈ L, s.est u ≠ ⊤) →
      (∀ S ∈ ms, ∀ u ∈ L, msgVal S u = ⊤) →
      receiveSeq G L ms (improveEstimate G L s) =
        improveEstimate G L (receive (ms.foldr (· ∪ ·) ∅) s)
  | [], s, _, _ => by simp [receiveSeq, receive_empty]
  | S :: ms, s, hfin, hms => by
    rw [receiveSeq, improveEstimate_receive_improveEstimate G hfin (hms S (by simp)),
      receiveSeq_improveEstimate L ms _
        (fun u hu => ne_top_of_le_ne_top (hfin u hu) (min_le_left _ _))
        (fun T hT => hms T (by simp [hT])),
      receive_receive, List.foldr_cons]

/-! ### Synchronous rounds -/

variable {H : Type*} [Fintype H] [DecidableEq H] (h : V → H) (ord : H → List V)

/-- `V(x)`: the nodes host `x` is responsible for. -/
def own (x : H) : Finset V := univ.filter fun v => h v = x

/-- Initialization of Algorithm 3: `est[v] = d(v)` for own nodes, `+∞` otherwise. -/
def initState (x : H) : HostState V :=
  ⟨fun v => if h v = x then (G.degree v : ℕ∞) else ⊤, fun _ => false⟩

/-- Round 1 message: `S = {(u, est[u]) : u ∈ V(x)}`. -/
def allMsg (x : H) (s : HostState V) : Finset (V × ℕ∞) := (own h x).image fun u => (u, s.est u)

/-- Periodic message: `S = {(u, est[u]) : u ∈ V(x), changed[u]}`. -/
def changedMsg (x : H) (s : HostState V) : Finset (V × ℕ∞) :=
  ((own h x).filter fun u => s.changed u = true).image fun u => (u, s.est u)

/-- `foreach u ∈ V(x) do changed[u] ← false`. -/
def resetChanged (s : HostState V) : HostState V := ⟨s.est, fun _ => false⟩

/-- Global state at the end of a round. -/
structure GlobalState (H V : Type*) where
  /-- local states of the hosts -/
  host : H → HostState V
  /-- the set sent by each host in this round (`∅` = nothing sent) -/
  sent : H → Finset (V × ℕ∞)

/-- All the pairs host `x` receives in the next round (from all other hosts). -/
def inbox (g : GlobalState H V) (x : H) : Finset (V × ℕ∞) :=
  (univ.filter fun y => y ≠ x).biUnion g.sent

/-- Host `x` in round `r + 2`, before resetting `changed`: receive, then `improveEstimate`. -/
noncomputable def roundHost (g : GlobalState H V) (x : H) : HostState V :=
  improveEstimate G (ord x) (receive (inbox g x) (g.host x))

/-- The synchronous run: `run G h ord r` is the global state at the end of round `r + 1`. -/
noncomputable def run : ℕ → GlobalState H V
  | 0 => ⟨fun x => resetChanged (improveEstimate G (ord x) (initState G h x)),
          fun x => allMsg h x (improveEstimate G (ord x) (initState G h x))⟩
  | r + 1 => ⟨fun x => resetChanged (roundHost G ord (run r) x),
              fun x => changedMsg h x (roundHost G ord (run r) x)⟩

/-- The estimate of `v` at its own host at the end of round `r + 1`. -/
noncomputable def ownEst (r : ℕ) (v : V) : ℕ∞ := ((run G h ord r).host (h v)).est v

variable {G h ord}

theorem msgVal_biUnion (T : Finset H) (f : H → Finset (V × ℕ∞)) (v : V) :
    msgVal (T.biUnion f) v = T.inf fun y => msgVal (f y) v := by
  simp only [msgVal, filter_biUnion, inf_biUnion]

theorem msgVal_inbox (g : GlobalState H V) (hg : ∀ y, ∀ p ∈ g.sent y, h p.1 = y) (x : H) (v : V) :
    msgVal (inbox g x) v = if h v = x then ⊤ else msgVal (g.sent (h v)) v := by
  rw [inbox, msgVal_biUnion]
  have htop : ∀ y, y ≠ h v → msgVal (g.sent y) v = ⊤ := fun y hy =>
    msgVal_eq_top fun p hp hpv => hy (by rw [← hg y p hp, hpv])
  split_ifs with hx
  · exact (Finset.inf_eq_top_iff _ _).2 fun y hy => htop y (by rw [hx]; exact (mem_filter.1 hy).2)
  · refine le_antisymm (Finset.inf_le (mem_filter.2 ⟨mem_univ _, hx⟩))
      (Finset.le_inf fun y _ => ?_)
    by_cases hy : y = h v
    · subst hy; exact le_rfl
    · rw [htop y hy]; exact le_top

theorem sent_mem (r : ℕ) (x : H) : ∀ p ∈ (run G h ord r).sent x, h p.1 = x := by
  cases r with
  | zero =>
    intro p hp
    simp only [run, allMsg, mem_image] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    simpa [own] using hu
  | succ r =>
    intro p hp
    simp only [run, changedMsg, mem_image, mem_filter] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    simpa [own] using hu.1

theorem host_changed (r : ℕ) (x : H) : ((run G h ord r).host x).changed = fun _ => false := by
  cases r <;> rfl

theorem not_mem_ord (hord : ∀ x u, u ∈ ord x ↔ h u = x) {x : H} {v : V} (hv : h v ≠ x) :
    v ∉ ord x := fun hm => hv ((hord x v).1 hm)

theorem receive_inbox_eq {r : ℕ}
    (hinv : ∀ x v, h v ≠ x →
      min (((run G h ord r).host x).est v) (msgVal ((run G h ord r).sent (h v)) v) =
        ownEst G h ord r v) (x : H) :
    receive (inbox (run G h ord r) x) ((run G h ord r).host x) =
      ⟨ownEst G h ord r, fun _ => false⟩ := by
  refine HostState.ext (funext fun v => ?_) (host_changed r x)
  simp only [receive]
  rw [msgVal_inbox _ (sent_mem r) x v]
  split_ifs with hv
  · subst hv; simp [ownEst]
  · exact hinv x v hv

/-- **Knowledge invariant.** At the end of every round, for a node `v` of another host, what
host `x` knows about `v`, combined with what the owner of `v` has just sent, is the owner's current
estimate of `v`. -/
theorem knowledge (hord : ∀ x u, u ∈ ord x ↔ h u = x) :
    ∀ r x v, h v ≠ x →
      min (((run G h ord r).host x).est v) (msgVal ((run G h ord r).sent (h v)) v) =
        ownEst G h ord r v
  | 0, x, v, hv => by
    simp only [run, ownEst, resetChanged, allMsg]
    rw [msgVal_image, improveEstimate_est_of_not_mem G (not_mem_ord hord hv)]
    simp [initState, hv, own]
  | r + 1, x, v, hv => by
    have hrec := receive_inbox_eq (knowledge hord r)
    simp only [run, ownEst, resetChanged, changedMsg, roundHost, hrec]
    rw [msgVal_image, improveEstimate_est_of_not_mem G (not_mem_ord hord hv)]
    have hle := improveEstimate_est_le G (ord (h v)) ⟨ownEst G h ord r, fun _ => false⟩ v
    have hch := improveEstimate_changed G (ord (h v)) ⟨ownEst G h ord r, fun _ => false⟩ v
    simp only at hle hch ⊢
    split_ifs with hmem
    · exact min_eq_right hle
    · have hc : (improveEstimate G (ord (h v)) ⟨ownEst G h ord r, fun _ => false⟩).changed v =
          false := by simpa [own] using hmem
      rw [hch] at hc
      simp only [Bool.false_or, decide_eq_false_iff_not, not_not] at hc
      rw [hc]; simp

/-- After receiving in round `r + 2`, every host knows exactly the estimates `ownEst r` of all
nodes. -/
theorem receive_inbox (hord : ∀ x u, u ∈ ord x ↔ h u = x) (r : ℕ) (x : H) :
    receive (inbox (run G h ord r) x) ((run G h ord r).host x) =
      ⟨ownEst G h ord r, fun _ => false⟩ :=
  receive_inbox_eq (knowledge hord r) x

theorem run_succ_host (hord : ∀ x u, u ∈ ord x ↔ h u = x) (r : ℕ) (x : H) :
    (run G h ord (r + 1)).host x =
      resetChanged (improveEstimate G (ord x) ⟨ownEst G h ord r, fun _ => false⟩) := by
  simp only [run, roundHost, receive_inbox hord r x]

theorem run_succ_sent (hord : ∀ x u, u ∈ ord x ↔ h u = x) (r : ℕ) (x : H) :
    (run G h ord (r + 1)).sent x =
      changedMsg h x (improveEstimate G (ord x) ⟨ownEst G h ord r, fun _ => false⟩) := by
  simp only [run, roundHost, receive_inbox hord r x]

theorem ownEst_succ (hord : ∀ x u, u ∈ ord x ↔ h u = x) (r : ℕ) (v : V) :
    ownEst G h ord (r + 1) v =
      (improveEstimate G (ord (h v)) ⟨ownEst G h ord r, fun _ => false⟩).est v := by
  rw [ownEst, run_succ_host hord]; rfl

/-- **Speed comparison with the one-to-one algorithm.** At the end of round `s + 1`, the estimate
of `u` at its host is at most `traj G s u`, the estimate of `u` in the one-to-one algorithm at
the end of round `s + 1` (`run_spec` in `Run.lean`). -/
theorem ownEst_le_traj (hord : ∀ x u, u ∈ ord x ↔ h u = x) :
    ∀ (s : ℕ) (v : V), ownEst G h ord s v ≤ (traj G s v : ℕ∞)
  | 0, v => by
    simp only [ownEst, run, resetChanged]
    exact (improveEstimate_est_le G _ _ v).trans (by simp [initState])
  | s + 1, u => by
    rw [ownEst_succ hord]
    have hBle : ∀ v, (improveEstimate G (ord (h u)) ⟨ownEst G h ord s, fun _ => false⟩).est v ≤
        (traj G s v : ℕ∞) := fun v =>
      (improveEstimate_est_le G _ _ v).trans (ownEst_le_traj hord s v)
    have hq := improveEstimate_quiescent G (ord (h u)) ⟨ownEst G h ord s, fun _ => false⟩ u
      ((hord _ _).2 rfl)
    refine hq.trans (Nat.cast_le.2 ?_)
    rw [traj_succ_apply]
    exact computeIndex_mono (fun v _ => hBle v) (ENat.toNat_le_of_le_natCast (hBle u))

theorem ownEst_ne_top (hord : ∀ x u, u ∈ ord x ↔ h u = x) (r : ℕ) (v : V) :
    ownEst G h ord r v ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (ownEst_le_traj (G := G) hord r v)

/-- **Theorem 2 (Safety), one-to-many version.** Every entry of `est` at every host, at the end of
every round, is at least the coreness. -/
theorem safety (hord : ∀ x u, u ∈ ord x ↔ h u = x) :
    ∀ (r : ℕ) (x : H) (v : V), (coreness G v : ℕ∞) ≤ ((run G h ord r).host x).est v
  | 0, x, v => by
    simp only [run, resetChanged]
    refine improveEstimate_max G (quiescent_coreness G _) _ (fun w => ?_) (fun u hu => ?_) v
    · simp only [initState]
      split_ifs
      · exact_mod_cast coreness_le_degree w
      · exact le_top
    · simp [initState, (hord x u).1 hu]
  | r + 1, x, v => by
    rw [run_succ_host hord]
    exact improveEstimate_max G (quiescent_coreness G _) _ (fun w => safety hord r (h w) w)
      (fun u _ => ownEst_ne_top (G := G) hord r u) v

/-- Safety of the messages: every value sent is at least the coreness of its node. -/
theorem safety_sent (hord : ∀ x u, u ∈ ord x ↔ h u = x) (r : ℕ) (x : H) :
    ∀ p ∈ (run G h ord r).sent x, (coreness G p.1 : ℕ∞) ≤ p.2 := by
  cases r with
  | zero =>
    intro p hp
    simp only [run, allMsg, mem_image] at hp
    obtain ⟨u, _, rfl⟩ := hp
    have := safety (G := G) hord 0 x u
    simpa [run, resetChanged] using this
  | succ r =>
    intro p hp
    rw [run_succ_sent hord] at hp
    simp only [changedMsg, mem_image] at hp
    obtain ⟨u, _, rfl⟩ := hp
    have := safety (G := G) hord (r + 1) x u
    simpa [run_succ_host hord, resetChanged] using this

theorem ownEst_eq_coreness (hord : ∀ x u, u ∈ ord x ↔ h u = x) {r : ℕ} (hr : stab G ≤ r)
    (v : V) : ownEst G h ord r v = coreness G v :=
  le_antisymm ((ownEst_le_traj (G := G) hord r v).trans_eq (by rw [traj_eq_coreness_of_le hr]))
    (safety (G := G) hord r (h v) v)

/-- **Liveness, own nodes.** From the end of round `stab G + 1` on (the round at which the
one-to-one algorithm is correct), every host knows the exact coreness of each of its own nodes:
the one-to-many algorithm is never slower than the one-to-one algorithm. -/
theorem liveness (hord : ∀ x u, u ∈ ord x ↔ h u = x) {r : ℕ} (hr : stab G ≤ r) (u : V) :
    ((run G h ord r).host (h u)).est u = coreness G u :=
  ownEst_eq_coreness (G := G) hord hr u

/-- From the end of round `stab G + 2` on, every entry at every host is the coreness. -/
theorem est_eq_coreness (hord : ∀ x u, u ∈ ord x ↔ h u = x) {r : ℕ} (hr : stab G < r) (x : H)
    (v : V) : ((run G h ord r).host x).est v = coreness G v := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  refine le_antisymm ?_ (safety (G := G) hord _ x v)
  rw [run_succ_host hord]
  exact (improveEstimate_est_le G _ _ v).trans_eq (ownEst_eq_coreness (G := G) hord (by omega) v)

/-- From round `stab G + 2` on, no host sends anything. -/
theorem sent_eq_empty (hord : ∀ x u, u ∈ ord x ↔ h u = x) {r : ℕ} (hr : stab G < r) (x : H) :
    (run G h ord r).sent x = ∅ := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  rw [run_succ_sent hord, changedMsg, image_eq_empty, filter_eq_empty_iff]
  intro u _
  have h1 : (improveEstimate G (ord x) ⟨ownEst G h ord r, fun _ => false⟩).est u =
      coreness G u := by
    have := est_eq_coreness (G := G) hord hr x u
    rwa [run_succ_host hord] at this
  have h2 := ownEst_eq_coreness (G := G) hord (r := r) (by omega) u
  rw [improveEstimate_changed]
  simp [h1, h2]

/-- **Theorem 3 (Liveness), one-to-many version.** There is a round after which every host knows
the exact coreness of every node and no messages are sent any more. -/
theorem theorem_3_multiHost (hord : ∀ x u, u ∈ ord x ↔ h u = x) :
    ∃ R, ∀ r ≥ R, (∀ x v, ((run G h ord r).host x).est v = coreness G v) ∧
      ∀ x, (run G h ord r).sent x = ∅ :=
  ⟨stab G + 1, fun _ hr =>
    ⟨est_eq_coreness (G := G) hord (by omega), sent_eq_empty (G := G) hord (by omega)⟩⟩

/-! ### Faithfulness: per-message processing and the pass order do not matter -/

theorem host_quiescent (r : ℕ) (x : H) : Quiescent G (ord x) ((run G h ord r).host x).est := by
  cases r <;> exact improveEstimate_quiescent G _ _

theorem foldr_union_map (l : List H) (f : H → Finset (V × ℕ∞)) :
    (l.map f).foldr (· ∪ ·) ∅ = l.toFinset.biUnion f := by
  induction l with
  | nil => simp
  | cons y l ih => simp [ih, Finset.biUnion_insert]

/-- **Algorithm 3's per-message handler.** Processing the messages of round `r + 1` one at a time,
in any order `l` of the sending hosts, with an `improveEstimate` after each one, yields the same
state as the batch processing used in `run`. -/
theorem run_succ_host_eq_receiveSeq (hord : ∀ x u, u ∈ ord x ↔ h u = x) (r : ℕ) (x : H)
    (l : List H) (hl : ∀ y, y ∈ l ↔ y ≠ x) :
    (run G h ord (r + 1)).host x =
      resetChanged (receiveSeq G (ord x) (l.map (run G h ord r).sent) ((run G h ord r).host x)) := by
  have hfin : ∀ u ∈ ord x, ((run G h ord r).host x).est u ≠ ⊤ := by
    intro u hu
    have := ownEst_ne_top (G := G) hord r u
    rwa [ownEst, (hord x u).1 hu] at this
  have hms : ∀ S ∈ l.map (run G h ord r).sent, ∀ u ∈ ord x, msgVal S u = ⊤ := by
    intro S hS u hu
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hS
    refine msgVal_eq_top fun p hp hpu => (hl y).1 hy ?_
    rw [← sent_mem r y p hp, hpu, (hord x u).1 hu]
  have := receiveSeq_improveEstimate G (ord x) _ _ hfin hms
  rw [improveEstimate_of_quiescent G (host_quiescent r x)] at this
  rw [this, foldr_union_map]
  have hl' : l.toFinset = univ.filter fun y => y ≠ x := by ext y; simp [hl]
  rw [hl']
  rfl

/-- The run does not depend on the order in which hosts visit their own nodes in Algorithm 4. -/
theorem run_congr_ord {ord' : H → List V} (hord : ∀ x u, u ∈ ord x ↔ h u = x)
    (hord' : ∀ x u, u ∈ ord' x ↔ h u = x) : ∀ r, run G h ord r = run G h ord' r
  | 0 => by
    have hR : ∀ x, improveEstimate G (ord x) (initState G h x) =
        improveEstimate G (ord' x) (initState G h x) := fun x =>
      improveEstimate_congr G (fun u => by rw [hord, hord']) _
        (fun u hu => by simp [initState, (hord x u).1 hu])
    simp only [run, hR]
  | r + 1 => by
    have hR : ∀ x, roundHost G ord (run G h ord r) x = roundHost G ord' (run G h ord r) x :=
      fun x => improveEstimate_congr G (fun u => by rw [hord, hord']) _ (fun u _ => by
        rw [receive_inbox hord]; exact ownEst_ne_top (G := G) hord r u)
    simp only [run]
    rw [← run_congr_ord hord hord' r]
    simp only [hR]

end MultiHost

end KCoreDecomposition
