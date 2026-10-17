import Papers.PODC2016.VertexCoverLocalRatio.Paper
import Cslib.Computability.Distributed.Local.Identifiers
import Cslib.Computability.Distributed.Local.OnlineLocalLocality

/-!
# Algorithm 1 in the synchronous LOCAL model (Theorem 3.1)

We implement Algorithm 1 in CSLib's synchronous locally-iterative model
(`Cslib.LocallyIterative.Algorithm`): in every round each node replaces its state by a function of
the round number, its own state and the *set* of states of its neighbours. States carry the node's
identifier, so a node can address an amount to a particular neighbour (field `out`) and pick out
the amount addressed to itself.

Local input of `v`: its identifier, its weight `w(v)` and its degree `d(v)`. Global knowledge: only
`ε` (through `θ = a = ε'`) and the processing order of line 17; no knowledge of `n` or `Δ`.

One iteration of Algorithm 1 takes three rounds (`t ≡ 0, 1, 2 mod 3`):
* `respond` (lines 10–21): every running node sees `vault(u)/d_i(u)` of its running neighbours
  (their requests) and fixes its answers `budget_i(v,·)` (field `out`);
* `deduct` (lines 13–14, 22–23, 26): every running node collects the answers addressed to it, updates
  `w_{i+1}(v)` and decides whether it returns `InCover` (field `cv`);
* `notify` (lines 27–33): a node with `cv` returns `InCover`; the others drop the neighbours that
  returned `InCover` and return `NotInCover` if none is left.

A node that has returned never changes its state again (`dist_frozen`).

Main results: `run_dist` (the run simulates `alg1`), `theorem_3_1` (correctness, termination,
per-vertex round bounds `3·(34+2E)/ε` for `d(v) ≤ 16` and `3(2+3E)·log d/(ε log log d)` for
`d(v) > 16`, for `0 < ε ≤ E`).
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph Cslib.LocallyIterative

/-- Local state of a node. -/
structure NState (V : Type*) where
  /-- identifier -/
  id : V
  /-- initial weight `w_0(v)` (local input) -/
  w0 : ℝ
  /-- current weight `w_i(v)` -/
  w : ℝ
  /-- status (running / returned `InCover` / returned `NotInCover`) -/
  st : Status
  /-- `d_i(v)`, the number of running neighbours -/
  dg : ℕ
  /-- answers `budget_i(v,u)` to the requests of the neighbours (addressed by identifier) -/
  out : V → ℝ
  /-- `v` returns `InCover` at the end of the current iteration -/
  cv : Prop

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
/-- Identifiers of the running neighbours. -/
noncomputable def runIds (N : Set (NState V)) : Finset V :=
  univ.filter fun u => ∃ x ∈ N, x.id = u ∧ x.st = .active

section
variable (θ a : ℝ) (R : Rule V)

open scoped Classical in
/-- The requests of the running neighbours, as seen by a node. -/
noncomputable def locReq (s : NState V) (N : Set (NState V)) (u : V) : ℝ :=
  if u ∈ runIds N then a * (pickId NState.id s N u).w0 / (pickId NState.id s N u).dg else 0

/-- The answers computed in round `3i`. -/
noncomputable def locOut (s : NState V) (N : Set (NState V)) : V → ℝ :=
  R s.id s.w0 (s.w - a * s.w0) (locReq a s N) (runIds N)

/-- Round `3i`: answer the requests of the running neighbours. -/
noncomputable def respond (s : NState V) (N : Set (NState V)) : NState V :=
  { s with out := locOut a R s N }

/-- The new weight computed in round `3i+1`. -/
noncomputable def locW (s : NState V) (N : Set (NState V)) : ℝ :=
  s.w - (∑ u ∈ runIds N, (pickId NState.id s N u).out s.id) - (∑ u ∈ runIds N, s.out u)

/-- Round `3i+1`: deduct the amounts exchanged and decide whether to return `InCover`. -/
noncomputable def deduct (s : NState V) (N : Set (NState V)) : NState V :=
  { s with w := locW s N, cv := locW s N ≤ θ * s.w0 }

open scoped Classical in
/-- Round `3i+2`: return `InCover`, or drop the neighbours that return `InCover` and return
`NotInCover` if none is left. -/
noncomputable def notify (s : NState V) (N : Set (NState V)) : NState V :=
  if s.cv then { s with st := .inCover }
  else if univ.filter (fun u => ∃ x ∈ N, x.id = u ∧ x.st = .active ∧ ¬ x.cv) = ∅ then
    { s with st := .notInCover }
  else { s with dg := (univ.filter fun u => ∃ x ∈ N, x.id = u ∧ x.st = .active ∧ ¬ x.cv).card }

/-- The distributed algorithm (with vault factor `a`, threshold `θ` and response rule `R`). -/
noncomputable def dist : Algorithm (NState V) :=
  ⟨fun t s N =>
    if s.st = .active then
      if t % 3 = 0 then respond a R s N else if t % 3 = 1 then deduct θ s N else notify s N
    else s⟩

end

/-- Initial configuration: identifier, weight and degree. -/
def c0 (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) : V → NState V :=
  fun v => ⟨v, w v, w v, .active, G.degree v, fun _ => 0, False⟩

/-! ### Reading the neighbourhood -/

section nbr
variable {G : SimpleGraph V} [DecidableRel G.Adj] {c : V → NState V}

theorem runIds_eq (hc : ∀ u, (c u).id = u) (v : V) :
    runIds (nbrColors G c v) = (G.neighborFinset v).filter fun u => (c u).st = .active := by
  ext u
  simp only [runIds, mem_filter, mem_univ, true_and, mem_neighborFinset]
  exact exists_mem_nbrColors_id NState.id hc

end nbr

/-! ### Simulation of the global iteration -/

section sim
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ a σ : ℝ} {R : Rule V} {w0 : V → ℝ}

variable (G w0) in
/-- The configuration encodes the global state `s` at an iteration boundary. -/
structure Sim (s : GState V) (c : V → NState V) : Prop where
  id : ∀ v, (c v).id = v
  w0 : ∀ v, (c v).w0 = w0 v
  w : ∀ v, (c v).w = s.w v
  st : ∀ v, (c v).st = s.st v
  dg : ∀ v, s.st v = .active → (c v).dg = dg G s v

theorem newW_active_eq {s : GState V} {v : V} (hv : s.st v = .active) :
    newW G a R w0 s v = s.w v - recv G a R w0 s v - given G a R w0 s v := by
  simp [newW, hv]

theorem runIds_sim {s : GState V} {c : V → NState V} (hs : Sim G w0 s c) (v : V) :
    runIds (nbrColors G c v) = actN G s v := by
  rw [runIds_eq hs.id]; ext u; simp [actN, hs.st]

/-- Membership in `mem_actN_step`: when `v` keeps running, its running neighbours after the
iteration are those that were running and did not return `InCover`. -/
theorem mem_actN_step_iff {s : GState V} {v u : V} (hv : (step G θ a R w0 s).st v = .active) :
    u ∈ actN G (step G θ a R w0 s) v ↔ u ∈ actN G s v ∧ ¬ cov G θ a R w0 s u := by
  obtain ⟨hv0, hvn, -⟩ := step_active_iff.1 hv
  simp only [mem_actN]
  constructor
  · rintro ⟨hadj, hu⟩
    obtain ⟨hu0, hun, -⟩ := step_active_iff.1 hu
    exact ⟨⟨hadj, hu0⟩, fun hc => hun hc.2⟩
  · rintro ⟨⟨hadj, hu0⟩, hnc⟩
    exact ⟨hadj, step_active_iff.2 ⟨hu0, fun hle => hnc ⟨hu0, hle⟩, v,
      mem_actN.2 ⟨hadj.symm, hv0⟩, fun hc => hvn hc.2⟩⟩

/-- Round `3i`. -/
theorem respond_sim {s : GState V} {c : V → NState V} (hs : Sim G w0 s c) (v : V) :
    respond a R (c v) (nbrColors G c v) = { c v with out := bud G a R w0 s v } := by
  classical
  have hrun := runIds_sim hs v
  simp only [respond]
  congr 1
  funext u
  rw [locOut, bud, hrun, hs.id, hs.w0, hs.w, bank]
  congr 1
  funext x
  simp only [reqAt, locReq, hrun]
  by_cases hx : x ∈ actN G s v
  · have hx' := mem_actN.1 hx
    rw [if_pos hx, if_pos hx, pickId_nbrColors NState.id hs.id _ hx'.1, hs.w0, hs.dg x hx'.2]; rfl
  · rw [if_neg hx, if_neg hx]

/-- Round `3i+1`. -/
theorem deduct_sim {s : GState V} {c : V → NState V} (hs : Sim G w0 s c)
    (hout : ∀ v, s.st v = .active → (c v).out = bud G a R w0 s v) {v : V}
    (hv : s.st v = .active) :
    deduct θ (c v) (nbrColors G c v) =
      { c v with w := newW G a R w0 s v, cv := cov G θ a R w0 s v } := by
  have hrun := runIds_sim hs v
  have hrecv : ∑ u ∈ runIds (nbrColors G c v),
      (pickId NState.id (c v) (nbrColors G c v) u).out (c v).id =
      recv G a R w0 s v := by
    rw [hrun, recv]
    refine sum_congr rfl fun u hu => ?_
    have hu' := mem_actN.1 hu
    rw [pickId_nbrColors NState.id hs.id _ hu'.1, hout u hu'.2, hs.id]
  have hgiven : ∑ u ∈ runIds (nbrColors G c v), (c v).out u = given G a R w0 s v := by
    rw [hrun, given, hout v hv]
  have hw : locW (c v) (nbrColors G c v) = newW G a R w0 s v := by
    rw [locW, hrecv, hgiven, hs.w, newW_active_eq hv]
  simp only [deduct, hw, hs.w0]
  congr 1
  exact propext ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩

/-- Round `3i+2`. -/
theorem notify_step {s : GState V} {c : V → NState V} (hid : ∀ u, (c u).id = u)
    (hst : ∀ u, (c u).st = s.st u)
    (hcv : ∀ v, s.st v = .active → ((c v).cv ↔ cov G θ a R w0 s v)) {v : V}
    (hv : s.st v = .active) :
    let c' := notify (c v) (nbrColors G c v)
    c'.id = (c v).id ∧ c'.w0 = (c v).w0 ∧ c'.w = (c v).w ∧
      c'.st = (step G θ a R w0 s).st v ∧
      ((step G θ a R w0 s).st v = .active → c'.dg = dg G (step G θ a R w0 s) v) := by
  classical
  have hS : (univ.filter fun u => ∃ x ∈ nbrColors G c v, x.id = u ∧ x.st = .active ∧ ¬ x.cv) =
      (actN G s v).filter fun u => ¬ cov G θ a R w0 s u := by
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_actN]
    rw [exists_mem_nbrColors_id NState.id hid (P := fun x => x.st = .active ∧ ¬ x.cv), hst]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, fun hc => h3 ((hcv u h2).2 hc)⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, fun hc => h3 ((hcv u h2).1 hc)⟩
  by_cases hc : (c v).cv
  · have hcov := (hcv v hv).1 hc
    have hst : (step G θ a R w0 s).st v = .inCover := (step_inCover_iff hv).2 hcov.2
    simp only [notify, if_pos hc, hst, true_and]
    exact fun h => by cases h
  · have hncov : ¬ newW G a R w0 s v ≤ θ * w0 v := fun h => hc ((hcv v hv).2 ⟨hv, h⟩)
    by_cases he : (actN G s v).filter (fun u => ¬ cov G θ a R w0 s u) = ∅
    · have hall : ∀ u ∈ actN G s v, cov G θ a R w0 s u := by
        intro u hu; by_contra hn
        have : u ∈ (actN G s v).filter (fun u => ¬ cov G θ a R w0 s u) := mem_filter.2 ⟨hu, hn⟩
        rw [he] at this; simp at this
      have hst : (step G θ a R w0 s).st v = .notInCover :=
        (step_notInCover_iff hv).2 ⟨hncov, hall⟩
      simp only [notify, if_neg hc, hS, if_pos he, hst, true_and]
      exact fun h => by cases h
    · have hex : ∃ u ∈ actN G s v, ¬ cov G θ a R w0 s u := by
        by_contra hn; push Not at hn
        exact he (filter_eq_empty_iff.2 fun u hu => not_not.2 (hn u hu))
      have hstep : (step G θ a R w0 s).st v = .active := step_active_iff.2 ⟨hv, hncov, hex⟩
      simp only [notify, if_neg hc, hS, if_neg he]
      refine ⟨trivial, trivial, trivial, ?_, fun _ => ?_⟩
      · show (c v).st = _
        rw [hst, hstep, hv]
      · show _ = dg G (step G θ a R w0 s) v
        rw [dg]
        congr 1
        ext u
        rw [mem_filter, mem_actN_step_iff hstep]

end sim

/-! ### The run -/

section run
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ a σ : ℝ} {R : Rule V} {w0 : V → ℝ}

theorem dist_step_of_ne {t : ℕ} {s : NState V} {N : Set (NState V)} (h : s.st ≠ .active) :
    (dist θ a R).step t s N = s := by
  simp only [dist]; rw [if_neg h]

theorem dist_step_of_active {t : ℕ} {s : NState V} {N : Set (NState V)} (h : s.st = .active) :
    (dist θ a R).step t s N =
      if t % 3 = 0 then respond a R s N else if t % 3 = 1 then deduct θ s N else notify s N := by
  simp only [dist]; rw [if_pos h]

/-- One iteration = three rounds. -/
theorem iter_sim {s : GState V} {c : V → NState V} (hs : Sim G w0 s c) {t : ℕ} (ht : t % 3 = 0) :
    let A := dist θ a R
    let c1 := fun v => A.step t (c v) (nbrColors G c v)
    let c2 := fun v => A.step (t + 1) (c1 v) (nbrColors G c1 v)
    let c3 := fun v => A.step (t + 2) (c2 v) (nbrColors G c2 v)
    (∀ v, (c1 v).st = s.st v) ∧ (∀ v, (c2 v).st = s.st v) ∧
      Sim G w0 (step G θ a R w0 s) c3 := by
  intro A c1 c2 c3
  have ht1 : (t + 1) % 3 = 1 := by omega
  have ht2 : (t + 2) % 3 ≠ 0 ∧ (t + 2) % 3 ≠ 1 := by omega
  -- round 1
  have hc1 : ∀ v, c1 v = if s.st v = .active then { c v with out := bud G a R w0 s v } else c v := by
    intro v
    by_cases hv : s.st v = .active
    · rw [if_pos hv]
      show A.step t (c v) (nbrColors G c v) = _
      rw [dist_step_of_active (by rw [hs.st]; exact hv), if_pos ht]
      exact respond_sim hs v
    · rw [if_neg hv]
      exact dist_step_of_ne (by rw [hs.st]; exact hv)
  have hs1 : Sim G w0 s c1 := by
    refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v hv => ?_⟩ <;> rw [hc1 v] <;>
      split_ifs <;> first | exact hs.id v | exact hs.w0 v | exact hs.w v | exact hs.st v |
        exact hs.dg v hv
  have hout1 : ∀ v, s.st v = .active → (c1 v).out = bud G a R w0 s v := by
    intro v hv; rw [hc1 v, if_pos hv]
  -- round 2
  have hc2 : ∀ v, c2 v = if s.st v = .active then
      { c1 v with w := newW G a R w0 s v, cv := cov G θ a R w0 s v } else c1 v := by
    intro v
    by_cases hv : s.st v = .active
    · rw [if_pos hv]
      show A.step (t + 1) (c1 v) (nbrColors G c1 v) = _
      rw [dist_step_of_active (by rw [hs1.st]; exact hv), if_neg (by omega), if_pos ht1]
      exact deduct_sim hs1 hout1 hv
    · rw [if_neg hv]
      exact dist_step_of_ne (by rw [hs1.st]; exact hv)
  have hid2 : ∀ v, (c2 v).id = v := by
    intro v; rw [hc2 v]; split_ifs <;> simp [hs1.id]
  have hst2 : ∀ v, (c2 v).st = s.st v := by
    intro v; rw [hc2 v]; split_ifs <;> simp [hs1.st]
  have hw2 : ∀ v, (c2 v).w = newW G a R w0 s v := by
    intro v; rw [hc2 v]; split_ifs with hv
    · rfl
    · simp [hs1.w, newW, hv]
  have hcv2 : ∀ v, s.st v = .active → ((c2 v).cv ↔ cov G θ a R w0 s v) := by
    intro v hv; rw [hc2 v, if_pos hv]
  refine ⟨hs1.st, hst2, ?_⟩
  -- round 3
  have hc3 : ∀ v, c3 v = if s.st v = .active then notify (c2 v) (nbrColors G c2 v) else c2 v := by
    intro v
    by_cases hv : s.st v = .active
    · rw [if_pos hv]
      show A.step (t + 2) (c2 v) (nbrColors G c2 v) = _
      rw [dist_step_of_active (by rw [hst2]; exact hv), if_neg ht2.1, if_neg ht2.2]
    · rw [if_neg hv]
      exact dist_step_of_ne (by rw [hst2]; exact hv)
  have hw0_2 : ∀ v, (c2 v).w0 = w0 v := by
    intro v; rw [hc2 v]; split_ifs <;> simp [hs1.w0]
  constructor
  · intro v; rw [hc3 v]; split_ifs with hv
    · rw [(notify_step hid2 hst2 hcv2 hv).1, hid2]
    · exact hid2 v
  · intro v; rw [hc3 v]; split_ifs with hv
    · rw [(notify_step hid2 hst2 hcv2 hv).2.1, hw0_2]
    · exact hw0_2 v
  · intro v; rw [hc3 v, step_w]; split_ifs with hv
    · rw [(notify_step hid2 hst2 hcv2 hv).2.2.1, hw2]
    · exact hw2 v
  · intro v; rw [hc3 v]; split_ifs with hv
    · exact (notify_step hid2 hst2 hcv2 hv).2.2.2.1
    · rw [hst2, step_st_of_ne hv]
  · intro v hv'; rw [hc3 v]; split_ifs with hv
    · exact (notify_step hid2 hst2 hcv2 hv).2.2.2.2 hv'
    · exact absurd (active_of_step hv') hv

variable (G θ a R w0) in
/-- The configuration of the distributed algorithm after `t` rounds. -/
noncomputable abbrev cfg (t : ℕ) : V → NState V := (dist θ a R).run G (c0 G w0) t

/-- **Simulation**: after `3i` rounds the configuration encodes the global state at the beginning
of iteration `i`; in the two intermediate rounds the statuses are unchanged. -/
theorem run_dist (i : ℕ) :
    Sim G w0 (run G θ a R w0 i) (cfg G θ a R w0 (3 * i)) ∧
      (∀ v, (cfg G θ a R w0 (3 * i + 1) v).st = (run G θ a R w0 i).st v) ∧
      (∀ v, (cfg G θ a R w0 (3 * i + 2) v).st = (run G θ a R w0 i).st v) := by
  have key : ∀ i, Sim G w0 (run G θ a R w0 i) (cfg G θ a R w0 (3 * i)) := by
    intro i
    induction i with
    | zero =>
      refine ⟨fun v => rfl, fun v => rfl, fun v => rfl, fun v => rfl, fun v _ => ?_⟩
      exact (dg_init v).symm
    | succ i ih =>
      have h := (iter_sim (θ := θ) (a := a) (R := R) ih (t := 3 * i) (by omega)).2.2
      rw [run_succ, show 3 * (i + 1) = 3 * i + 2 + 1 by ring]
      exact h
  refine ⟨key i, fun v => ?_, fun v => ?_⟩
  · exact (iter_sim (θ := θ) (a := a) (R := R) (key i) (t := 3 * i) (by omega)).1 v
  · exact (iter_sim (θ := θ) (a := a) (R := R) (key i) (t := 3 * i) (by omega)).2.1 v

/-- The status of `v` after `t` rounds is its status at the beginning of iteration `⌊t/3⌋`. -/
theorem cfg_st (t : ℕ) (v : V) :
    (cfg G θ a R w0 t v).st = (run G θ a R w0 (t / 3)).st v := by
  obtain ⟨h0, h1, h2⟩ := run_dist (G := G) (θ := θ) (a := a) (R := R) (w0 := w0) (t / 3)
  have : t = 3 * (t / 3) ∨ t = 3 * (t / 3) + 1 ∨ t = 3 * (t / 3) + 2 := by omega
  rcases this with ht | ht | ht
  · conv_lhs => rw [ht]
    exact h0.st v
  · conv_lhs => rw [ht]
    exact h1 v
  · conv_lhs => rw [ht]
    exact h2 v

/-- A node that has returned never changes its state again. -/
theorem dist_frozen {t : ℕ} {v : V} (hv : (cfg G θ a R w0 t v).st ≠ .active) (k : ℕ) :
    cfg G θ a R w0 (t + k) v = cfg G θ a R w0 t v :=
  Nat.eq_of_le_of_stable (x := fun t => cfg G θ a R w0 t v) (P := fun s => s.st ≠ .active)
    (fun _ h => dist_step_of_ne h) hv (Nat.le_add_right t k)

end run

/-- The distributed algorithm is a LOCAL algorithm: the state of a node after `t` rounds only
depends on the graph and the initial states (identifiers, weights, degrees) within distance `t`. -/
theorem dist_isLocal (θ a : ℝ) (R : Rule V) (t : ℕ) :
    Cslib.Local.IsLocal t fun G (s₀ : V → NState V) v => (dist θ a R).run G s₀ t v :=
  Algorithm.run_isLocal _ _

end VertexCoverLocalRatio
