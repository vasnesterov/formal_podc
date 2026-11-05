import Mathlib

-- CSLib candidate: IIS executions with crashes and strongly correct processes.

/-!
# The iterated immediate snapshot (IIS) model and strongly correct processes

Raynal, Stainer, *Increasing the Power of the Iterated Immediate Snapshot Model with Failure
Detectors* (PODC 2012 brief announcement; full version IRISA PI 1991, 2012), Sections 2.4 and 2.6.

* `ISRound P`: one round of the IIS model — the set `part` of processes that invoke
  `IS[r].write_snapshot()` and the views they obtain, satisfying self-inclusion, containment and
  immediacy (Section 2.4).
* `Schedule P`: an infinite sequence of rounds; participation is non-increasing (a process that
  skips a round has crashed). Rounds are numbered from `0` (the paper starts at `1`).
* `Schedule.Correct i`: `i` executes every round.
* `Schedule.SCk k` and `Schedule.SC` (Section 2.6): `SC₀` = processes whose writes are seen by all
  correct processes in infinitely many rounds, `SC_{k+1}` = processes seen in infinitely many
  rounds by some process of `SC_k`, `SC = ⋃ₖ SC_k`.

Basic facts: `SC ⊆ Correct` (`Schedule.correct_of_mem_SC`), the chain is increasing
(`Schedule.SCk_mono`), `SC₀ ≠ ∅` as soon as some process is correct (`Schedule.SCk_zero_nonempty`),
after some round the views of strongly correct processes contain only strongly correct processes
(`Schedule.eventually_view_SC`), and information of a strongly correct process reaches every correct
process (`Schedule.propagate`).
-/

namespace Podc.IteratedSnapshotFD

/-- One round of an IIS execution: participants and the views returned by the one-shot immediate
snapshot object of the round (Section 2.4). `view i` is meaningful only for `i ∈ part`. -/
structure ISRound (P : Type) where
  /-- Processes that invoke `write_snapshot()` in this round. -/
  part : Finset P
  /-- The view (set of processes whose pair is returned) of each participant. -/
  view : P → Finset P
  view_sub : ∀ i ∈ part, view i ⊆ part
  /-- Self-inclusion. -/
  self_mem : ∀ i ∈ part, i ∈ view i
  /-- Containment. -/
  contain : ∀ i ∈ part, ∀ j ∈ part, view i ⊆ view j ∨ view j ⊆ view i
  /-- Immediacy. -/
  immed : ∀ i ∈ part, ∀ j ∈ part, i ∈ view j → view i ⊆ view j

/-- An infinite IIS schedule: round `r` uses the immediate snapshot object `IS[r]`. A process that
does not take part in round `r` has crashed and takes part in no later round. -/
structure Schedule (P : Type) where
  /-- Round `r`. -/
  rd : ℕ → ISRound P
  mono : ∀ r, (rd (r + 1)).part ⊆ (rd r).part

namespace Schedule

variable {P : Type} (σ : Schedule P)

/-- A correct process executes all rounds. -/
def Correct (i : P) : Prop := ∀ r, i ∈ (σ.rd r).part

/-- `i` is seen by `j` in round `r` (both participate). -/
def Sees (r : ℕ) (j i : P) : Prop := j ∈ (σ.rd r).part ∧ i ∈ (σ.rd r).view j

/-- The sets `SC_k` of Section 2.6. For `SC₀` we also require that `i` writes in the round; this
only matters when no process is correct (then the paper's `SC₀` would be all processes). -/
def SCk : ℕ → Set P
  | 0 => {i | ∀ R, ∃ r ≥ R, i ∈ (σ.rd r).part ∧ ∀ j, σ.Correct j → σ.Sees r j i}
  | k + 1 => {i | ∀ R, ∃ r ≥ R, ∃ j ∈ SCk k, σ.Sees r j i}

theorem mem_SCk_zero {i : P} :
    i ∈ σ.SCk 0 ↔ ∀ R, ∃ r ≥ R, i ∈ (σ.rd r).part ∧ ∀ j, σ.Correct j → σ.Sees r j i := Iff.rfl

theorem mem_SCk_succ {k : ℕ} {i : P} :
    i ∈ σ.SCk (k + 1) ↔ ∀ R, ∃ r ≥ R, ∃ j ∈ σ.SCk k, σ.Sees r j i := Iff.rfl

/-- The strongly correct processes `SC = SC_K` (the union of the increasing chain `SC_k`). -/
def SC : Set P := {i | ∃ k, i ∈ σ.SCk k}

theorem part_anti {r r' : ℕ} (h : r ≤ r') : (σ.rd r').part ⊆ (σ.rd r).part := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (σ.mono _).trans ih

/-- A process that participates in infinitely many rounds is correct. -/
theorem correct_of_frequently {i : P} (h : ∀ R, ∃ r ≥ R, i ∈ (σ.rd r).part) : σ.Correct i := by
  intro r
  obtain ⟨r', hr', hi⟩ := h r
  exact σ.part_anti hr' hi

theorem part_of_sees {r : ℕ} {j i : P} (h : σ.Sees r j i) : i ∈ (σ.rd r).part :=
  (σ.rd r).view_sub j h.1 h.2

theorem correct_of_mem_SCk {k : ℕ} {i : P} (h : i ∈ σ.SCk k) : σ.Correct i := by
  cases k with
  | zero =>
    exact σ.correct_of_frequently fun R => by
      obtain ⟨r, hr, hi, -⟩ := (σ.mem_SCk_zero.1 h) R; exact ⟨r, hr, hi⟩
  | succ k =>
    exact σ.correct_of_frequently fun R => by
      obtain ⟨r, hr, j, -, hji⟩ := (σ.mem_SCk_succ.1 h) R; exact ⟨r, hr, σ.part_of_sees hji⟩

/-- Strongly correct processes are correct. -/
theorem correct_of_mem_SC {i : P} (h : i ∈ σ.SC) : σ.Correct i := by
  obtain ⟨k, hk⟩ := h; exact σ.correct_of_mem_SCk hk

theorem sees_self {i : P} (hi : σ.Correct i) (r : ℕ) : σ.Sees r i i :=
  ⟨hi r, (σ.rd r).self_mem i (hi r)⟩

/-- `SC_k ⊆ SC_{k+1}` (self-inclusion). -/
theorem SCk_succ_sub (k : ℕ) : σ.SCk k ⊆ σ.SCk (k + 1) := by
  intro i hi
  refine σ.mem_SCk_succ.2 fun R => ?_
  exact ⟨R, le_rfl, i, hi, σ.sees_self (σ.correct_of_mem_SCk hi) R⟩

theorem SCk_mono {k k' : ℕ} (h : k ≤ k') : σ.SCk k ⊆ σ.SCk k' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (σ.SCk_succ_sub _)

/-- A process seen infinitely often by a strongly correct process is strongly correct. -/
theorem mem_SC_of_frequently_seen {i j : P} (hj : j ∈ σ.SC)
    (h : ∀ R, ∃ r ≥ R, σ.Sees r j i) : i ∈ σ.SC := by
  obtain ⟨k, hk⟩ := hj
  exact ⟨k + 1, σ.mem_SCk_succ.2 fun R => by obtain ⟨r, hr, h⟩ := h R; exact ⟨r, hr, j, hk, h⟩⟩

/-- Pigeonhole on rounds: if at every round `r ≥ R₀` some element `f r` of a finite type satisfies
a property, then some element satisfies it infinitely often. -/
theorem exists_frequently {α : Type} [Finite α] {Q : ℕ → α → Prop} (R₀ : ℕ)
    (h : ∀ r ≥ R₀, ∃ a, Q r a) : ∃ a, ∀ R, ∃ r ≥ R, Q r a := by
  classical
  have := Fintype.ofFinite α
  by_contra hc
  push Not at hc
  choose B hB using hc
  let M := max R₀ (Finset.univ.sup B)
  obtain ⟨a, ha⟩ := h M (le_max_left _ _)
  exact hB a M (le_trans (Finset.le_sup (f := B) (Finset.mem_univ a)) (le_max_right _ _)) ha

/-- If some process is correct, `SC₀ ≠ ∅` (Section 2.6). -/
theorem SCk_zero_nonempty [Finite P] {c : P} (hc : σ.Correct c) : (σ.SCk 0).Nonempty := by
  classical
  -- In each round, the smallest view among the correct processes is seen by all of them.
  have key : ∀ r, ∃ i, i ∈ (σ.rd r).part ∧ ∀ j, σ.Correct j → σ.Sees r j i := by
    intro r
    have := Fintype.ofFinite P
    let C : Finset P := Finset.univ.filter σ.Correct
    have hCne : C.Nonempty := ⟨c, by simp [C, hc]⟩
    obtain ⟨m, hm, hmin⟩ := C.exists_min_image (fun j => ((σ.rd r).view j).card) hCne
    have hmc : σ.Correct m := by simpa [C] using hm
    refine ⟨m, hmc r, fun j hj => ⟨hj r, ?_⟩⟩
    rcases (σ.rd r).contain m (hmc r) j (hj r) with h | h
    · exact h ((σ.rd r).self_mem m (hmc r))
    · have hjC : j ∈ C := by simp [C, hj]
      have hcard := hmin j hjC
      have : (σ.rd r).view j = (σ.rd r).view m := Finset.eq_of_subset_of_card_le h hcard
      rw [this]; exact (σ.rd r).self_mem m (hmc r)
  obtain ⟨i, hi⟩ := exists_frequently (Q := fun r i => i ∈ (σ.rd r).part ∧
    ∀ j, σ.Correct j → σ.Sees r j i) 0 (fun r _ => key r)
  exact ⟨i, σ.mem_SCk_zero.2 hi⟩

theorem SC_nonempty [Finite P] {c : P} (hc : σ.Correct c) : σ.SC.Nonempty := by
  obtain ⟨i, hi⟩ := σ.SCk_zero_nonempty hc
  exact ⟨i, 0, hi⟩

/-- After some round, a strongly correct process sees only strongly correct processes (weakly
correct and faulty processes are invisible to it), Section 3.2. -/
theorem eventually_view_SC [Finite P] :
    ∃ R, ∀ r ≥ R, ∀ j ∈ σ.SC, j ∈ (σ.rd r).part → ∀ i ∈ (σ.rd r).view j, i ∈ σ.SC := by
  classical
  have := Fintype.ofFinite P
  have key : ∀ i j : P, ∃ R, ∀ r ≥ R, j ∈ σ.SC → i ∉ σ.SC → ¬ σ.Sees r j i := by
    intro i j
    by_cases hj : j ∈ σ.SC
    · by_cases hi : i ∈ σ.SC
      · exact ⟨0, fun _ _ _ h => absurd hi h⟩
      · by_contra hc
        push Not at hc
        exact hi (σ.mem_SC_of_frequently_seen hj fun R => by
          obtain ⟨r, hr, -, -, h⟩ := hc R; exact ⟨r, hr, h⟩)
    · exact ⟨0, fun _ _ h => absurd h hj⟩
  choose B hB using key
  refine ⟨Finset.univ.sup fun i => Finset.univ.sup fun j => B i j, fun r hr j hj hjp i hi => ?_⟩
  by_contra hiSC
  refine hB i j r ?_ hj hiSC ⟨hjp, hi⟩
  exact le_trans (le_trans (Finset.le_sup (f := fun j => B i j) (Finset.mem_univ j))
    (Finset.le_sup (f := fun i => Finset.univ.sup fun j => B i j) (Finset.mem_univ i))) hr

/-- **Propagation along `SC`.** Let `Good r i` be a property of process `i` at (the beginning of)
round `r` that, once true for a correct process, stays true, and that is passed on to every
correct process that sees, in some round `r`, a process for which it holds at `r`. If it holds
for a strongly correct process, it eventually holds for every correct process. -/
theorem propagate (Good : ℕ → P → Prop)
    (hstay : ∀ r i, σ.Correct i → Good r i → Good (r + 1) i)
    (hpass : ∀ r i j, σ.Correct j → σ.Sees r j i → Good r i → Good (r + 1) j)
    {i : P} (hi : i ∈ σ.SC) {r₀ : ℕ} (h0 : Good r₀ i) :
    ∀ j, σ.Correct j → ∃ r, Good r j := by
  have stay : ∀ i, σ.Correct i → ∀ r r', r ≤ r' → Good r i → Good r' i := by
    intro i hi r r' hrr' h
    induction hrr' with
    | refl => exact h
    | step _ ih => exact hstay _ _ hi ih
  obtain ⟨k, hk⟩ := hi
  induction k generalizing i r₀ with
  | zero =>
    intro j hj
    obtain ⟨r, hr, -, hall⟩ := (σ.mem_SCk_zero.1 hk) r₀
    exact ⟨r + 1, hpass r i j hj (hall j hj) (stay i (σ.correct_of_mem_SCk hk) _ _ hr h0)⟩
  | succ k ih =>
    obtain ⟨r, hr, j', hj', hsee⟩ := (σ.mem_SCk_succ.1 hk) r₀
    exact ih (hpass r i j' (σ.correct_of_mem_SCk hj') hsee
      (stay i (σ.correct_of_mem_SCk hk) _ _ hr h0)) hj'

end Schedule

end Podc.IteratedSnapshotFD
