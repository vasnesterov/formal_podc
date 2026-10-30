import Mathlib

/-!
# Distributed computing with adaptive heuristics: the model (Section 3)

Jaggard, Schapira, Wright, *Distributed Computing with Adaptive Heuristics* (PODC 2011 title:
*Distributed computing with rules of thumb*), arXiv 0910.1585v2, Section 3.

There are finitely many computational nodes `i : ι`, node `i` has action space `A i`. A *history*
`h ∈ H_w` (`w ≥ 1`) is a nonempty sequence of action profiles; we store it as the current profile
`h.cur` and the earlier profiles `h.past`, **most recent first**, so `h.time = w` is the number of
recorded time steps. A (deterministic) *reaction function* of node `i` is a sequence of functions
`f(i,t) : H_{t-1} → A i`; here `F.f i t h` (only applied to histories with `h.time = t - 1`).

A schedule `σ : ℕ → Finset ι` activates the nonempty set `σ t` at time step `t`. The
`(s⁰, σ)`-dynamics starts with the history `s⁰ ∈ H_w` at time `w + 1`; at time `t` the nodes in
`σ t` simultaneously apply `f(i,t)` to the history so far, the other nodes keep their action.

## Main definitions

* `System.step`, `System.run`: the dynamics.
* `IsSchedule`, `Fair`: nonempty activation sets; every node activated infinitely often.
* `ConvergesTo`, `Convergent`, `IsStableState`: convergence of the dynamics, convergent systems
  (all initial states, all fair schedules), stable states (limits of fair dynamics).
* `SelfIndependent`, `HasRecall`, `Stationary`: restrictions 2–4 of Section 3.
-/

-- CSLib candidate (with the rest of the adaptive-heuristics model of this folder).
namespace Podc.RulesOfThumb

open Filter

universe u v

variable {ι : Type u} {A : ι → Type v}

/-- An action profile `a ∈ A = ×ᵢ Aᵢ`. -/
abbrev Profile (A : ι → Type v) := (i : ι) → A i

/-- A nonempty history of interaction (an element of `H_w`, `w ≥ 1`): the most recent action
profile `cur` and the earlier profiles `past`, most recent first. -/
structure Hist (A : ι → Type v) where
  /-- The most recent action profile. -/
  cur : Profile A
  /-- The earlier action profiles, most recent first. -/
  past : List (Profile A)

namespace Hist

/-- All recorded profiles, most recent first. -/
def toList (h : Hist A) : List (Profile A) := h.cur :: h.past

/-- The number `w` of recorded time steps (`h ∈ H_w`). -/
def time (h : Hist A) : ℕ := h.past.length + 1

@[simp] lemma length_toList (h : Hist A) : h.toList.length = h.time := rfl

lemma time_pos (h : Hist A) : 0 < h.time := Nat.succ_pos _

end Hist

/-- An interaction system with deterministic reaction functions: `f i t h` is the action that node
`i` chooses when it is activated at time step `t`, after the history `h` (with `h.time = t - 1`). -/
structure System (A : ι → Type v) where
  /-- The reaction function `f(i,t)` of node `i` at time step `t`. -/
  f : (i : ι) → ℕ → Hist A → A i

namespace System

variable [DecidableEq ι] (F : System A)

/-- One time step: the nodes in `T` react to the history `h` (at time step `h.time + 1`). -/
def step (h : Hist A) (T : Finset ι) : Hist A :=
  ⟨fun i => if i ∈ T then F.f i (h.time + 1) h else h.cur i, h.toList⟩

/-- The `(s⁰, σ)`-dynamics: `F.run s0 σ m` is the history after `m` time steps; the step at
absolute time `t` activates `σ t`. -/
def run (s0 : Hist A) (σ : ℕ → Finset ι) : ℕ → Hist A
  | 0 => s0
  | m + 1 => F.step (run s0 σ m) (σ ((run s0 σ m).time + 1))

@[simp] lemma run_zero (s0 : Hist A) (σ : ℕ → Finset ι) : F.run s0 σ 0 = s0 := rfl

lemma run_succ (s0 : Hist A) (σ : ℕ → Finset ι) (m : ℕ) :
    F.run s0 σ (m + 1) = F.step (F.run s0 σ m) (σ ((F.run s0 σ m).time + 1)) := rfl

@[simp] lemma step_time (h : Hist A) (T : Finset ι) : (F.step h T).time = h.time + 1 := rfl

@[simp] lemma step_toList (h : Hist A) (T : Finset ι) :
    (F.step h T).toList = (F.step h T).cur :: h.toList := rfl

lemma step_cur_of_mem {h : Hist A} {T : Finset ι} {i : ι} (hi : i ∈ T) :
    (F.step h T).cur i = F.f i (h.time + 1) h := by simp [step, hi]

lemma step_cur_of_not_mem {h : Hist A} {T : Finset ι} {i : ι} (hi : i ∉ T) :
    (F.step h T).cur i = h.cur i := by simp [step, hi]

@[simp] lemma run_time (s0 : Hist A) (σ : ℕ → Finset ι) (m : ℕ) :
    (F.run s0 σ m).time = s0.time + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [run_succ, step_time, ih]; rfl

/-- Running `m + j` steps is running `j` steps from the history after `m` steps (the schedule is
indexed by absolute time). -/
lemma run_add (s0 : Hist A) (σ : ℕ → Finset ι) (m j : ℕ) :
    F.run s0 σ (m + j) = F.run (F.run s0 σ m) σ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [← add_assoc, run_succ, ih, run_succ]

/-- The dynamics only depends on the schedule at the times it uses. -/
lemma run_congr {s0 : Hist A} {σ τ : ℕ → Finset ι} {m : ℕ}
    (h : ∀ t, s0.time < t → t ≤ s0.time + m → σ t = τ t) : F.run s0 σ m = F.run s0 τ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [run_succ, run_succ, ih (fun t h1 h2 => h t h1 (by omega)), run_time,
      h _ (by omega) (by omega)]

end System

/-- A schedule: every time step activates a nonempty set of nodes. -/
def IsSchedule (σ : ℕ → Finset ι) : Prop := ∀ t, (σ t).Nonempty

/-- A fair schedule activates every node infinitely often. -/
def Fair (σ : ℕ → Finset ι) : Prop := ∀ i, ∃ᶠ t in atTop, i ∈ σ t

namespace System

variable [DecidableEq ι] (F : System A)

/-- The `(s⁰, σ)`-dynamics converges to the action profile `a`. -/
def ConvergesTo (s0 : Hist A) (σ : ℕ → Finset ι) (a : Profile A) : Prop :=
  ∀ᶠ m in atTop, (F.run s0 σ m).cur = a

/-- The system is *convergent*: for every initial state and every fair schedule the dynamics
converges. -/
def Convergent : Prop :=
  ∀ (s0 : Hist A) (σ : ℕ → Finset ι), IsSchedule σ → Fair σ → ∃ a, F.ConvergesTo s0 σ a

/-- `a` is a *stable state*: some fair dynamics converges to `a`. -/
def IsStableState (a : Profile A) : Prop :=
  ∃ (s0 : Hist A) (σ : ℕ → Finset ι), IsSchedule σ ∧ Fair σ ∧ F.ConvergesTo s0 σ a

end System

/-- Two histories of the same length that agree on the actions of all nodes other than `i`. -/
def OthersEq (i : ι) (h h' : Hist A) : Prop :=
  List.Forall₂ (fun a b : Profile A => ∀ j, j ≠ i → a j = b j) h.toList h'.toList

namespace System

variable (F : System A)

/-- *Self-independence*: node `i`'s own past and present actions do not affect its reaction. -/
def SelfIndependent : Prop :=
  ∀ i (h h' : Hist A), OthersEq i h h' → F.f i (h.time + 1) h = F.f i (h'.time + 1) h'

/-- *`k`-recall* of node `i`: on histories with at least `k` entries, its reaction at each time
step only depends on the `k` most recent action profiles. -/
def HasRecall (i : ι) (k : ℕ) : Prop :=
  ∀ h h' : Hist A, h.time = h'.time → k ≤ h.time → h.toList.take k = h'.toList.take k →
    F.f i (h.time + 1) h = F.f i (h.time + 1) h'

/-- A *stationary `k`-recall* reaction function: one function `g` of the `k` most recent action
profiles, used at all time steps. -/
def Stationary (i : ι) (k : ℕ) : Prop :=
  ∃ g : List (Profile A) → A i, ∀ h : Hist A, k ≤ h.time → F.f i (h.time + 1) h = g (h.toList.take k)

/-- *Historyless*: stationary `1`-recall, i.e. a function of the most recent action profile. -/
def Historyless (i : ι) : Prop := F.Stationary i 1

lemma Stationary.hasRecall {F : System A} {i : ι} {k : ℕ} (h : F.Stationary i k) :
    F.HasRecall i k := by
  obtain ⟨g, hg⟩ := h
  intro h h' ht hk htake
  rw [hg h hk, ht, hg h' (ht ▸ hk), htake]

lemma HasRecall.mono {F : System A} {i : ι} {k l : ℕ} (h : F.HasRecall i k) (hkl : k ≤ l) :
    F.HasRecall i l := by
  intro h1 h2 ht hl htake
  have e : ∀ x : List (Profile A), x.take k = (x.take l).take k := fun x => by
    rw [List.take_take, min_eq_left hkl]
  exact h h1 h2 ht (hkl.trans hl) (by rw [e, htake, ← e])

lemma Stationary.mono {F : System A} {i : ι} {k l : ℕ} (h : F.Stationary i k) (hkl : k ≤ l) :
    F.Stationary i l := by
  obtain ⟨g, hg⟩ := h
  refine ⟨fun x => g (x.take k), fun h hl => ?_⟩
  simp only [hg h (hkl.trans hl), List.take_take, min_eq_left hkl]

end System

end Podc.RulesOfThumb
