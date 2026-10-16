import Podc.SyncCrash.Model

/-!
# Silence (Goren–Moses, PODC 2018): atomic commitment in `γ_f`

Definitions shared by the whole formalization: decisions, the atomic-commitment (AC)
specification of §2.1, nice runs, message-chain sets `S_j^r(t)`.

The model `γ_f` (synchronous rounds, crash failures, deterministic history-based protocols,
knowledge) is `Podc.SyncCrash` (`Podc/SyncCrash/Model.lean`).
-/

namespace Papers.PODC2018.Silence

open Podc.SyncCrash Classical

/-- The two AC actions. -/
inductive Decision
  | commit
  | abort
  deriving DecidableEq, Repr

/-- AC protocols: binary inputs (votes), decisions `commit` / `abort`. -/
abbrev ACProtocol (P M : Type*) := Cslib.Byzantine.LockStep.Protocol P Bool M Decision

variable {P M : Type*}

/-- The four AC conditions (§2.1) for one run.
* Decision: every correct process eventually decides;
* Agreement: all processes that decide (also faulty ones) make the same decision;
* Commit Validity: commit only if all initial values are `1`;
* Abort Validity: abort only if some initial value is `0` or some process fails. -/
structure ACRun (alg : ACProtocol P M) (r : Run P Bool) : Prop where
  decision : ∀ i, ¬ r.Faulty i → ∃ m d, DecidesAt alg r i m d
  agreement : ∀ i m d i' m' d', DecidesAt alg r i m d → DecidesAt alg r i' m' d' → d = d'
  commit_validity : ∀ i m, DecidesAt alg r i m .commit → ∀ j, r.input j = true
  abort_validity : ∀ i m, DecidesAt alg r i m .abort → (∃ j, r.input j = false) ∨ ∃ j, r.Faulty j

/-- `alg` solves AC in `γ_f`: every admissible run satisfies the AC conditions. -/
def SolvesAC [Fintype P] (alg : ACProtocol P M) (f : ℕ) : Prop :=
  ∀ r : Run P Bool, r.Admissible f → ACRun alg r

/-- The nice run: all initial values are `1` and nobody fails. (For a deterministic protocol it is
unique.) -/
def nice : Run P Bool := ⟨fun _ => true, fun _ => none, fun _ => ∅⟩

lemma nice_admissible [Fintype P] (f : ℕ) : (nice : Run P Bool).Admissible f := by
  refine ⟨?_, by simp [nice]⟩
  have : (nice : Run P Bool).faulty = ∅ := by ext; simp [nice, Run.Faulty]
  simp [this]

lemma nice_not_faulty (p : P) : ¬ (nice : Run P Bool).Faulty p := by simp [nice, Run.Faulty]

lemma nice_alive (p : P) (m : ℕ) : (nice : Run P Bool).Alive p m :=
  Run.alive_of_not_faulty (nice_not_faulty p) m

/-- `S_j^r(t)`: the processes reached by a message chain from `(j, 0)` by time `t`. -/
noncomputable def S {O : Type*} (alg : Cslib.Byzantine.LockStep.Protocol P Bool M O) [Fintype P] (r : Run P Bool) (j : P) (t : ℕ) :
    Finset P :=
  Finset.univ.filter (fun z => Chain alg r j 0 z t)

@[simp] lemma mem_S {O : Type*} {alg : Cslib.Byzantine.LockStep.Protocol P Bool M O} [Fintype P] {r : Run P Bool} {j z : P} {t : ℕ} :
    z ∈ S alg r j t ↔ Chain alg r j 0 z t := by simp [S]

/-- In the nice run, every process decides, and it commits (Abort Validity). -/
lemma nice_decides_commit [Fintype P] {alg : ACProtocol P M} {f : ℕ} (hAC : SolvesAC alg f)
    (i : P) {m : ℕ} {d : Decision} (h : DecidesAt alg nice i m d) : d = .commit := by
  cases d with
  | commit => rfl
  | abort =>
    rcases (hAC nice (nice_admissible f)).abort_validity i m h with ⟨j, hj⟩ | ⟨j, hj⟩
    · simp [nice] at hj
    · exact absurd hj (nice_not_faulty j)

lemma nice_exists_commit [Fintype P] {alg : ACProtocol P M} {f : ℕ} (hAC : SolvesAC alg f)
    (i : P) : ∃ m, DecidesAt alg nice i m .commit := by
  obtain ⟨m, d, h⟩ := (hAC nice (nice_admissible f)).decision i (nice_not_faulty i)
  exact ⟨m, nice_decides_commit hAC i h ▸ h⟩

end Papers.PODC2018.Silence
