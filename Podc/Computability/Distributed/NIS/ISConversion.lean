import Podc.Computability.Distributed.NIS.Model

-- CSLib candidate: Cslib/Computability/Distributed/NIS/ISConversion.lean (staged by Papers/PODC2021/ExtensionBasedReductions)
/-!
# From NIS protocols to IS protocols (Borowsky–Gafni)

Brusse–Ellen, *Reductions and Extension-Based Proofs*, PODC 2021, Section 7 cites the fact
(Borowsky–Gafni) that a task solvable in the NIS model is solvable in the IS model. We prove it for
the full-information model of `Model.lean` (`exists_isIS_of_solves`).

Construction. Let `δ` solve `T` (wait-free).
1. *Uniform bound* (König): since there are finitely many processes and inputs, there is `N` with
   `α.length ≤ N` for every schedule `α` of `δ` from an initial configuration
   (`exists_bound_of_waitFree`).
2. *Simulation map* `sim δ : St P X → St P X`: from a state of the IS execution it computes the state
   the process would have in the NIS protocol `δ` if every process stopped as soon as its simulated
   state is terminated. It drops from each simulated scan the components written by processes whose
   simulated state was already terminated, and freezes once the simulated process has decided.
3. The IS protocol `isProt δ t` (`t = N + 1`) decides exactly after the `t`-th scan, outputting the
   `δ`-decision of the simulated state.

Correctness: every (not necessarily valid) schedule `α` from `C` induces a valid `δ`-schedule
`ind δ C α` (dropping steps of simulated-terminated processes) whose final configuration is the
`sim`-image of `C α` (`simC_exec`). As `ind` has length `≤ N`, after `t > N` rounds every simulated
state is terminated, so final IS configurations are mapped to final `δ`-configurations with the same
outputs. Wait-freedom: every process takes at most `2t` steps.
-/

namespace Cslib.NIS

open St

variable {P X Y : Type}

namespace ISConv

/-! ## Basic facts on states -/

lemma rounds_le_depth : ∀ s : St P X, s.rounds ≤ s.depth
  | init _ _ => le_rfl
  | upd s => by simp only [St.rounds, St.depth]; have := rounds_le_depth s; omega
  | scan s _ => by simp only [St.rounds, St.depth]; have := rounds_le_depth s; omega

/-! ## The simulation map -/

section Sim
variable (δ : Protocol P X Y)

mutual
/-- The simulated NIS state of a process whose IS state is the argument. -/
def sim : St P X → St P X
  | init i x => init i x
  | upd s => if decided δ (sim s) = none then upd (sim s) else sim s
  | scan s v => if decided δ (sim s) = none then scan (sim s) (fun j => simO (v j)) else sim s
/-- The simulated content of a snapshot component: the simulated state of the writer, unless its
simulated state was already terminated when it wrote (then it did not write in the simulation). -/
def simO : Option (St P X) → Option (St P X)
  | none => none
  | some w => if decided δ (sim w) = none then some (sim w) else none
end

variable {δ}

@[simp] lemma sim_init (i : P) (x : X) : sim δ (init i x) = init i x := by simp only [sim]

lemma sim_upd (s : St P X) :
    sim δ (upd s) = if decided δ (sim δ s) = none then upd (sim δ s) else sim δ s := by
  simp only [sim]

lemma sim_scan (s : St P X) v : sim δ (scan s v) =
    if decided δ (sim δ s) = none then scan (sim δ s) (fun j => simO δ (v j)) else sim δ s := by
  simp only [sim]

@[simp] lemma simO_none : simO δ (none : Option (St P X)) = none := by simp only [simO]

lemma simO_some (w : St P X) :
    simO δ (some w) = if decided δ (sim δ w) = none then some (sim δ w) else none := by
  simp only [simO]

/-- If the simulated state of `upd s` is not terminated, it is `upd (sim s)`. -/
lemma sim_upd_of_active {s : St P X} (h : decided δ (sim δ (upd s)) = none) :
    decided δ (sim δ s) = none ∧ sim δ (upd s) = upd (sim δ s) := by
  rw [sim_upd] at h ⊢
  by_cases hs : decided δ (sim δ s) = none
  · simp [hs]
  · simp [hs] at h

lemma sim_scan_of_active {s : St P X} {v} (h : decided δ (sim δ (scan s v)) = none) :
    decided δ (sim δ s) = none ∧ sim δ (scan s v) = scan (sim δ s) (fun j => simO δ (v j)) := by
  rw [sim_scan] at h ⊢
  by_cases hs : decided δ (sim δ s) = none
  · simp [hs]
  · simp [hs] at h

lemma hist_sim_scan (s : St P X) v : (sim δ (scan s v)).hist = (sim δ s).hist := by
  rw [sim_scan]; split_ifs <;> rfl

/-- Active simulated states have as many rounds as the simulating state. -/
lemma rounds_sim : ∀ {c : St P X}, decided δ (sim δ c) = none → (sim δ c).rounds = c.rounds
  | init _ _, _ => by simp
  | upd s, h => by
    obtain ⟨h1, h2⟩ := sim_upd_of_active h
    rw [h2]; simp only [St.rounds]; exact rounds_sim h1
  | scan s v, h => by
    obtain ⟨h1, h2⟩ := sim_scan_of_active h
    rw [h2]; simp only [St.rounds]; rw [rounds_sim h1]

lemma hist_sim_of_active : ∀ {c : St P X}, decided δ (sim δ c) = none →
    (sim δ c).hist = c.hist.map (sim δ) ∧ ∀ w ∈ c.hist, decided δ (sim δ w) = none
  | init _ _, _ => by simp [St.hist]
  | upd s, h => by
    obtain ⟨h1, h2⟩ := sim_upd_of_active h
    obtain ⟨ih1, ih2⟩ := hist_sim_of_active h1
    rw [h2]; simp only [St.hist, ih1, List.map_append, List.map_cons, List.map_nil, true_and,
      List.mem_append, List.mem_singleton]
    rintro w (hw | rfl)
    · exact ih2 w hw
    · exact h1
  | scan s v, h => by
    obtain ⟨h1, h2⟩ := sim_scan_of_active h
    rw [h2]; exact hist_sim_of_active h1

lemma simO_getElem?_of_active {L : List (St P X)} (hL : ∀ w ∈ L, decided δ (sim δ w) = none)
    (r : ℕ) : simO δ L[r]? = (L.map (sim δ))[r]? := by
  rw [List.getElem?_map]
  cases h : L[r]? with
  | none => simp
  | some w =>
    have := hL w (List.mem_of_getElem? h)
    simp [simO_some, this]

/-- The simulated snapshot component equals the snapshot component of the simulated states. -/
lemma hist_sim : ∀ (c : St P X) (r : ℕ), (sim δ c).hist[r]? = simO δ c.hist[r]?
  | init _ _, r => by simp [St.hist]
  | upd s, r => by
    by_cases hs : decided δ (sim δ s) = none
    · have hu : sim δ (upd s) = upd (sim δ s) := by rw [sim_upd]; simp only [hs, ↓reduceIte]
      have hact : decided δ (sim δ (upd s)) = none := by rw [hu]; rfl
      obtain ⟨h1, h2⟩ := hist_sim_of_active hact
      rw [h1, simO_getElem?_of_active h2]
    · have hu : sim δ (upd s) = sim δ s := by rw [sim_upd]; simp only [hs, ↓reduceIte]
      rw [hu, hist_sim s r]
      simp only [St.hist]
      by_cases hr : r < s.hist.length
      · rw [List.getElem?_append_left hr]
      · push Not at hr
        rw [List.getElem?_eq_none hr, List.getElem?_append_right hr]
        cases h : r - s.hist.length with
        | zero => simp [simO_some, hs]
        | succ k => simp
  | scan s v, r => by
    rw [hist_sim_scan]; exact hist_sim s r

/-- The simulated configuration. -/
def simC (δ : Protocol P X Y) (C : Config P X) : Config P X := fun j => sim δ (C j)

@[simp] lemma simC_initC (x : P → X) : simC δ (initC x) = initC x := by
  funext j; simp [simC, initC]

/-- One IS step of an active simulated process is one NIS step of the simulation. -/
lemma sim_stepState_of_active (C : Config P X) (q : P) (h : decided δ (sim δ (C q)) = none) :
    sim δ (stepState C q) = stepState (simC δ C) q := by
  cases hc : C q with
  | init i x =>
    have e1 : stepState C q = upd (init i x) := by simp [stepState, hc]
    have e2 : stepState (simC δ C) q = upd (init i x) := by simp [stepState, simC, hc]
    rw [e1, e2, sim_upd]; simp
  | upd s =>
    rw [hc] at h
    obtain ⟨h1, h2⟩ := sim_upd_of_active h
    have e1 : stepState C q = scan (upd s) (fun j => (C j).hist[s.rounds]?) := by
      simp [stepState, hc]
    have e2 : stepState (simC δ C) q =
        scan (upd (sim δ s)) (fun j => (sim δ (C j)).hist[(sim δ s).rounds]?) := by
      simp [stepState, simC, hc, h2]
    rw [e1, e2, sim_scan, h2, rounds_sim h1]
    simp only [show decided δ (upd (sim δ s)) = none from rfl, ↓reduceIte]
    congr 1; funext j; rw [hist_sim]
  | scan s v =>
    rw [hc] at h
    obtain ⟨h1, h2⟩ := sim_scan_of_active h
    have e1 : stepState C q = upd (scan s v) := by simp [stepState, hc]
    have e2 : stepState (simC δ C) q = upd (sim δ (scan s v)) := by
      simp [stepState, simC, hc, h2]
    rw [e1, e2, sim_upd]
    simp only [h, ↓reduceIte]

variable [DecidableEq P]

lemma sim_stepState_of_not_active (C : Config P X) (q : P) (h : decided δ (sim δ (C q)) ≠ none) :
    sim δ (stepState C q) = sim δ (C q) := by
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩
  · have h' : ¬ decided δ (sim δ (upd s)) = none := by rw [← h1]; exact h
    rw [h2, sim_scan, h1]; simp only [h', ↓reduceIte]
  · rw [h2, sim_upd]; simp only [h, ↓reduceIte]

lemma simC_step (C : Config P X) (q : P) :
    simC δ (step C q) =
      if decided δ (sim δ (C q)) = none then step (simC δ C) q else simC δ C := by
  funext j
  split_ifs with h
  · by_cases hj : j = q
    · subst hj; simp [simC, sim_stepState_of_active C j h]
    · simp [simC, step_ne _ hj]
  · by_cases hj : j = q
    · subst hj; simp [simC, sim_stepState_of_not_active C j h]
    · simp [simC, step_ne _ hj]

/-- The `δ`-schedule induced by an IS schedule: steps of simulated-terminated processes are
dropped. -/
def ind (δ : Protocol P X Y) : Config P X → List P → List P
  | _, [] => []
  | C, q :: α =>
    (if decided δ (sim δ (C q)) = none then [q] else []) ++ ind δ (step C q) α

lemma simC_exec (C : Config P X) (α : List P) :
    simC δ (exec C α) = exec (simC δ C) (ind δ C α) ∧ IsSched δ (simC δ C) (ind δ C α) := by
  induction α generalizing C with
  | nil => simp [ind]
  | cons q α ih =>
    obtain ⟨ih1, ih2⟩ := ih (step C q)
    simp only [exec_cons, ind]
    rw [simC_step] at ih1 ih2
    split_ifs with h
    · simp only [h, ↓reduceIte] at ih1 ih2
      refine ⟨ih1, ?_⟩
      simp only [List.singleton_append, isSched_cons]
      exact ⟨h, ih2⟩
    · simp only [h, ↓reduceIte] at ih1 ih2
      exact ⟨ih1, by simpa using ih2⟩

end Sim

/-! ## Uniform bound on schedule lengths (König) -/

section Bound
variable [DecidableEq P] {δ : Protocol P X Y}

lemma exists_bound_of_waitFree_aux [Fintype P] (hw : WaitFree δ) (x : P → X) :
    ∃ N, ∀ α, IsSched δ (initC x) α → α.length ≤ N := by
  by_contra hne
  push Not at hne
  -- `γ` has arbitrarily long valid extensions
  let good : List P → Prop := fun γ =>
    ∀ N, ∃ β, IsSched δ (initC x) (γ ++ β) ∧ N ≤ β.length
  have g0 : good [] := fun N => by
    obtain ⟨α, h1, h2⟩ := hne N; exact ⟨α, by simpa using h1, h2.le⟩
  have gsched : ∀ γ, good γ → IsSched δ (initC x) γ := fun γ hg => by
    obtain ⟨β, hβ, -⟩ := hg 0; exact ((isSched_append _ _ _).1 hβ).1
  have gstep : ∀ γ, good γ → ∃ q, good (γ ++ [q]) := fun γ hg => by
    by_contra hn
    push Not at hn
    simp only [good, not_forall, not_exists, not_and, not_le] at hn
    choose Nq hNq using hn
    obtain ⟨β, hβ, hlen⟩ := hg (Finset.univ.sup Nq + 1)
    cases β with
    | nil => simp at hlen
    | cons q β =>
      have := hNq q β (by simpa using hβ)
      have hle : Nq q ≤ Finset.univ.sup Nq := Finset.le_sup (Finset.mem_univ q)
      simp only [List.length_cons] at hlen; omega
  choose nxt hnxt using gstep
  let g : ℕ → {γ : List P // good γ} := fun k =>
    Nat.rec ⟨[], g0⟩ (fun _ γ => ⟨γ.1 ++ [nxt γ.1 γ.2], hnxt γ.1 γ.2⟩) k
  let f : ℕ → P := fun k => nxt (g k).1 (g k).2
  have hf : ∀ k, (List.range k).map f = (g k).1 := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [List.range_succ, List.map_append, ih]; rfl
  exact hw x ⟨f, fun k => by rw [hf]; exact gsched _ (g k).2⟩

/-- König's lemma for wait-free protocols: a uniform bound on the lengths of schedules from initial
configurations. -/
lemma exists_bound_of_waitFree [Fintype P] [Finite X] (hw : WaitFree δ) :
    ∃ N, ∀ x α, IsSched δ (initC x) α → α.length ≤ N := by
  choose Nx hNx using exists_bound_of_waitFree_aux hw
  obtain ⟨N, hN⟩ := (Set.finite_range Nx).bddAbove
  exact ⟨N, fun x α hα => (hNx x α hα).trans (hN ⟨x, rfl⟩)⟩

end Bound

/-! ## The IS protocol -/

/-- The IS protocol: decide exactly after the `t`-th scan, with the `δ`-decision of the simulated
state. -/
def isProt [Inhabited Y] (δ : Protocol P X Y) (t : ℕ) : Protocol P X Y := fun c =>
  if c.IsScan ∧ c.rounds = t then some ((decided δ (sim δ c)).getD default) else none

section IS
variable [Inhabited Y] {δ : Protocol P X Y} {t : ℕ}

lemma decided_isProt (c : St P X) : decided (isProt δ t) c = isProt δ t c := by
  cases c <;> simp [isProt, St.IsScan]

lemma isIS_isProt : IsIS (isProt δ t) t := fun s v => by
  simp [isProt, St.IsScan]

/-- Shape invariant of the states along an IS execution. -/
def Inv (t : ℕ) (c : St P X) : Prop :=
  (∃ s, c = upd s ∧ c.depth = 2 * c.rounds + 1 ∧ c.rounds < t) ∨
  ((∀ s, c ≠ upd s) ∧ c.depth = 2 * c.rounds ∧ c.rounds ≤ t)

lemma Inv.depth_le {c : St P X} (h : Inv t c) : c.depth ≤ 2 * t := by
  rcases h with ⟨_, _, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega

lemma inv_stepState (ht : 0 < t) {C : Config P X} {q : P} (hI : Inv t (C q))
    (ha : Active (isProt δ t) C q) : Inv t (stepState C q) := by
  unfold Active at ha; rw [decided_isProt] at ha
  cases hc : C q with
  | init i x =>
    have e1 : stepState C q = upd (init i x) := by simp [stepState, hc]
    rw [e1]; left; exact ⟨_, rfl, by simp [St.depth, St.rounds], by simp [St.rounds]; omega⟩
  | upd s =>
    have e1 : stepState C q = scan (upd s) (fun j => (C j).hist[s.rounds]?) := by
      simp [stepState, hc]
    rw [hc] at hI
    rw [e1]; right
    rcases hI with ⟨_, _, h1, h2⟩ | ⟨h0, -, -⟩
    · refine ⟨(fun _ h => by cases h), ?_, ?_⟩ <;> simp only [St.depth, St.rounds] at * <;> omega
    · exact absurd rfl (h0 s)
  | scan s v =>
    have e1 : stepState C q = upd (scan s v) := by simp [stepState, hc]
    rw [hc] at hI ha
    rw [e1]; left
    rcases hI with ⟨_, h, -, -⟩ | ⟨-, h1, h2⟩
    · cases h
    · have : (scan s v).rounds ≠ t := fun h => by simp [isProt, St.IsScan, h] at ha
      exact ⟨_, rfl, by simp only [St.depth, St.rounds] at *; omega,
        by simp only [St.rounds] at *; omega⟩

variable [DecidableEq P]

lemma inv_exec (ht : 0 < t) {C : Config P X} (hI : ∀ j, Inv t (C j)) {α : List P}
    (hα : IsSched (isProt δ t) C α) : ∀ j, Inv t (exec C α j) := by
  induction α generalizing C with
  | nil => exact hI
  | cons q α ih =>
    obtain ⟨hq, hα⟩ := hα
    refine ih (fun j => ?_) hα
    by_cases hj : j = q
    · subst hj; rw [step_self]; exact inv_stepState ht (hI j) hq
    · rw [step_ne _ hj]; exact hI j

lemma waitFree_isProt [Fintype P] (ht : 0 < t) : WaitFree (isProt δ t) := by
  rintro x ⟨f, hf⟩
  have hα := hf (Fintype.card P * (2 * t) + 1)
  have hI := inv_exec ht (C := initC x) (fun j => Or.inr ⟨fun _ h => by simp [initC] at h,
    by simp [initC, St.depth, St.rounds], by simp [initC, St.rounds]⟩) hα
  have hm := measure_exec (initC x) ((List.range (Fintype.card P * (2 * t) + 1)).map f)
  have h0 : totalDepth (initC x : Config P X) = 0 := by simp [totalDepth, initC, St.depth]
  have hle : totalDepth (exec (initC x) ((List.range (Fintype.card P * (2 * t) + 1)).map f)) ≤
      Fintype.card P * (2 * t) := by
    unfold totalDepth
    calc _ ≤ ∑ _j : P, 2 * t := Finset.sum_le_sum fun j _ => (hI j).depth_le
      _ = _ := by simp
  simp [h0] at hm; omega

end IS

end ISConv

open ISConv in
/-- Borowsky–Gafni (cited in Section 7 of Brusse–Ellen, PODC 2021): if a task is solvable (wait-free)
in the NIS model, then it is solvable in the IS model, by a protocol in which every process terminates
exactly after its `t`-th scan. -/
theorem exists_isIS_of_solves [DecidableEq P] [Fintype P] [Finite X] [Inhabited Y]
    {δ : Protocol P X Y} {T : Task P X Y} (h : Solves δ T) :
    ∃ (δ' : Protocol P X Y) (t : ℕ), 0 < t ∧ IsIS δ' t ∧ Solves δ' T := by
  obtain ⟨N, hN⟩ := exists_bound_of_waitFree h.1
  refine ⟨isProt δ (N + 1), N + 1, Nat.succ_pos _, isIS_isProt, waitFree_isProt (Nat.succ_pos _),
    fun x hx α _ hfin => ?_⟩
  set C := exec (initC x) α
  obtain ⟨h1, h2⟩ := simC_exec (δ := δ) (initC x) α
  rw [simC_initC] at h1 h2
  set β := ind δ (initC x) α
  have hβ := hN x β h2
  -- every process has terminated in the IS run, hence in the simulation
  have hterm : ∀ q, (C q).IsScan ∧ (C q).rounds = N + 1 ∧ decided δ (sim δ (C q)) ≠ none := by
    intro q
    have hq := hfin q
    simp only [Active, decided_isProt, isProt] at hq
    split_ifs at hq with hc
    · refine ⟨hc.1, hc.2, fun hd => ?_⟩
      have hr := rounds_sim hd
      have hle := rounds_le_depth (sim δ (C q))
      have hd' : (sim δ (C q)).depth = β.count q := by
        have := congrFun h1 q
        simp only [simC] at this
        rw [this, depth_exec]; simp [initC, St.depth]
      have := List.count_le_length (a := q) (l := β)
      omega
    · exact absurd rfl hq
  have hfinδ : Final δ (exec (initC x) β) := fun q hq => by
    rw [Active, ← h1] at hq; exact (hterm q).2.2 hq
  obtain ⟨y, hy, hyq⟩ := h.2 x hx β h2 hfinδ
  refine ⟨y, hy, fun q => ?_⟩
  have hyq' := hyq q
  rw [outs, ← h1] at hyq'
  have hyq'' : decided δ (sim δ (C q)) = some (y q) := hyq'
  have hc : (C q).IsScan ∧ (C q).rounds = N + 1 := ⟨(hterm q).1, (hterm q).2.1⟩
  simp only [outs, decided_isProt, isProt, hc, and_self, ↓reduceIte, hyq'', Option.getD_some]

end Cslib.NIS
