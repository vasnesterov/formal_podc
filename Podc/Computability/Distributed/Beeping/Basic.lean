/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/Beeping/Basic.lean
import Mathlib
import Cslib.Computability.Distributed.SelfStabilization.StoneAge

/-!
# The synchronous beeping model (BEEP)

The beeping model of Cornejo–Kuhn, in the form of Dufoulon–Burman–Beauquier (DISC 2018, Section 2.2):
an execution proceeds in synchronous rounds, all nodes starting at the same time. In each round
every node either *beeps* or *listens*; a beep is transmitted to all neighbours. A node that beeped
learns nothing in this round; a node that listened learns one bit: whether **at least one**
neighbour beeped (no collision detection, no sender identity, no multiplicity). Then every node
performs a local computation.

* `Algorithm σ`: a deterministic beeping algorithm with local states `σ`: `beeps : σ → Bool` (beep or
  listen in this round), `onBeep : σ → σ` (local computation after beeping) and
  `onListen : σ → Bool → σ` (after listening, given the heard bit). Per-node inputs (identifiers, …)
  are encoded in the initial configuration `init : V → σ`, so non-anonymous algorithms are covered.
* `hears G A C v`: some neighbour of `v` beeps in configuration `C`; `step`, `run` (synchronous
  start: `run G A init 0 = init`).
* `toStoneAge` / `run_eq_stoneAge`: a beeping algorithm is a stone-age algorithm
  (`Cslib.StoneAge`) under the synchronous schedule.
* Multi-slot design pattern (Cornejo–Kuhn; Section 3.1.2 of Dufoulon et al.): if in a window of `M`
  rounds every node `u` beeps exactly in its slot `m u`, then the set of slots in which `v` listens
  and hears a beep is exactly `{m u | u ∼ v} \ {m v}` (`heardSlots_eq`).
-/

namespace Cslib.Beeping

variable {V σ : Type*}

/-- A deterministic algorithm in the beeping model with local states `σ`. -/
structure Algorithm (σ : Type*) where
  /-- Whether a node in this state beeps (`true`) or listens (`false`) in the current round. -/
  beeps : σ → Bool
  /-- Local computation of a node that beeped: it learns nothing from its neighbours. -/
  onBeep : σ → σ
  /-- Local computation of a node that listened, given whether at least one neighbour beeped. -/
  onListen : σ → Bool → σ

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Algorithm σ)

/-- In configuration `C`, at least one neighbour of `v` beeps. -/
def hears (C : V → σ) (v : V) : Bool := decide (∃ u, G.Adj v u ∧ A.beeps (C u) = true)

theorem hears_eq_true {C : V → σ} {v : V} :
    hears G A C v = true ↔ ∃ u, G.Adj v u ∧ A.beeps (C u) = true := by
  simp [hears]

/-- One synchronous round. -/
def step (C : V → σ) : V → σ :=
  fun v => if A.beeps (C v) then A.onBeep (C v) else A.onListen (C v) (hears G A C v)

/-- The synchronous execution from the initial configuration `init` (synchronous start):
`run G A init t` is the configuration at the end of round `t`. -/
def run (init : V → σ) : ℕ → V → σ
  | 0 => init
  | t + 1 => step G A (run init t)

@[simp] theorem run_zero (init : V → σ) : run G A init 0 = init := rfl

theorem run_succ (init : V → σ) (t : ℕ) : run G A init (t + 1) = step G A (run G A init t) := rfl

theorem run_succ_of_beeps {init : V → σ} {t : ℕ} {v : V} (h : A.beeps (run G A init t v) = true) :
    run G A init (t + 1) v = A.onBeep (run G A init t v) := by
  simp [run_succ, step, h]

theorem run_succ_of_listens {init : V → σ} {t : ℕ} {v : V}
    (h : A.beeps (run G A init t v) = false) :
    run G A init (t + 1) v = A.onListen (run G A init t v) (hears G A (run G A init t) v) := by
  simp [run_succ, step, h]

/-! ### Bridge to the stone-age model -/

/-- A beeping algorithm as a stone-age algorithm: the transition only depends on the own state and on
whether some state of the closed neighbourhood beeps (for a listening node, some neighbour). -/
noncomputable def Algorithm.toStoneAge : Cslib.StoneAge.Algorithm σ := by
  classical
  exact ⟨fun q S => if A.beeps q then A.onBeep q else A.onListen q (decide (∃ q' ∈ S, A.beeps q'))⟩

/-- The beeping execution is the stone-age execution of `toStoneAge` under the synchronous
schedule. -/
theorem run_eq_stoneAge (init : V → σ) (t : ℕ) :
    run G A init t = Cslib.StoneAge.run G A.toStoneAge init Cslib.StoneAge.sync t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext v
    rw [run_succ, Cslib.StoneAge.run, ← ih]
    simp only [step, Cslib.StoneAge.step, Cslib.StoneAge.sync, Set.mem_univ, ite_true, Algorithm.toStoneAge]
    split_ifs with hb
    · rfl
    · congr 1
      simp only [hears, Cslib.StoneAge.mem_signal, decide_eq_decide]
      constructor
      · rintro ⟨u, hu, hb'⟩; exact ⟨_, ⟨u, Or.inr hu, rfl⟩, hb'⟩
      · rintro ⟨_, ⟨u, rfl | hu, rfl⟩, hb'⟩
        · simp_all
        · exact ⟨u, hu, hb'⟩

/-! ### The multi-slot design pattern -/

/-- The slots `r < M` of the window of rounds `t, …, t + M - 1` in which `v` listens and hears a
beep. -/
def heardSlots (C : ℕ → V → σ) (t M : ℕ) (v : V) : Finset ℕ :=
  (Finset.range M).filter fun r => A.beeps (C (t + r) v) = false ∧ hears G A (C (t + r)) v = true

/-- **Multi-slot design pattern** (Section 3.1.2 of Dufoulon–Burman–Beauquier, after Cornejo–Kuhn):
if in the window of rounds `t, …, t + M - 1` every node `u` beeps exactly in its slot `m u < M`, then
the slots in which `v` hears a beep are exactly the slots of its neighbours other than its own:
`{m u | u ∼ v} \ {m v}`. In particular `v` learns nothing about the multiplicity or the identity of the
senders, nor whether some neighbour shares its own slot. -/
theorem heardSlots_eq [DecidableEq V] (C : ℕ → V → σ) (t M : ℕ) (m : V → ℕ) (hm : ∀ u, m u < M)
    (hslot : ∀ u r, r < M → (A.beeps (C (t + r) u) = true ↔ r = m u)) (v : V) :
    heardSlots G A C t M v = ((Finset.univ.filter (G.Adj v)).image m).erase (m v) := by
  ext r
  simp only [heardSlots, Finset.mem_filter, Finset.mem_range, Finset.mem_erase, Finset.mem_image,
    Finset.mem_univ, true_and, hears_eq_true]
  constructor
  · rintro ⟨hr, hb, u, hu, hbu⟩
    refine ⟨fun h => ?_, u, hu, ((hslot u r hr).1 hbu).symm⟩
    have := (hslot v r hr).2 h
    rw [hb] at this
    exact Bool.false_ne_true this
  · rintro ⟨hne, u, hu, rfl⟩
    refine ⟨hm u, ?_, u, hu, (hslot u _ (hm u)).2 rfl⟩
    cases h : A.beeps (C (t + m u) v)
    · rfl
    · exact absurd ((hslot v _ (hm u)).1 h) hne

/-- The multi-slot design pattern for the execution `run G A init`. -/
theorem heardSlots_run_eq [DecidableEq V] (init : V → σ) (t M : ℕ) (m : V → ℕ)
    (hm : ∀ u, m u < M)
    (hslot : ∀ u r, r < M → (A.beeps (run G A init (t + r) u) = true ↔ r = m u)) (v : V) :
    heardSlots G A (run G A init) t M v = ((Finset.univ.filter (G.Adj v)).image m).erase (m v) :=
  heardSlots_eq G A _ t M m hm hslot v

end Cslib.Beeping
