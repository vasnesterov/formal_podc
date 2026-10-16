import Cslib.Computability.Distributed.DynamicNetworks.HeardOf
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Card

/-!
# Dynamic graphs, the nine DG classes, and stabilizing leader election

Altisen, Devismes, Durand, Johnen, Petit, *On Implementing Stabilizing Leader Election with Weak
Assumptions on Network Dynamics* (PODC 2021; journal version HAL hal-03346225), Section 2.

## Conventions

* Processes are identified with their identifiers: `ι` is the identifier domain `IDSET`, and a
  system is a finite set `V : Finset ι` of processes (`id(p) = p`).
* A dynamic graph is `G : ℕ → Graph ι` (CSLib `Cslib.HeardOf.Graph`, `G t p q` = edge `p → q`).
  Rounds are **0-indexed**: `G t` is the paper's `G_{t+1}` and `exec A G γ t` is the paper's
  configuration `γ_{t+1}`. `IsDG V G`: all edges of `G` are between distinct vertices of `V`.
* Journeys: `Reach G p a b q` holds iff `p = q` or there is a journey from `p` to `q` all of whose
  edges are taken in rounds `t ∈ [a, b)` (at strictly increasing times).
  The temporal distance `tdist G i p q` is the paper's `d̂_{G_{i▷}}(p, q)` (`tdist_le_iff`).
* Algorithms are deterministic full-information round algorithms (CSLib `Cslib.HeardOf.StepFn`):
  each process broadcasts its whole state; the receiver also learns who sent what. Each process has
  its own code (`step p`) and output `lid p : σ → ι`. This is at least as strong as the paper's
  local broadcast of (part of) the state, so impossibility results transfer.
* An algorithm is designed for a fixed number `n` of processes (well-formedness: the code of a
  process may depend on its identifier, `n`, and class parameters such as `Δ`, but not on `V`).
-/

namespace StabilizingLEDynamic

open Cslib.HeardOf

variable {ι σ : Type*}

/-- A dynamic graph: `G t p q` means that there is an edge `p → q` in round `t` (0-indexed). -/
abbrev DG (ι : Type*) := ℕ → Graph ι

/-- `G` is a dynamic graph with vertex set `V`: loopless, and all edges inside `V`. -/
def IsDG (V : Finset ι) (G : DG ι) : Prop := ∀ t p q, G t p q → p ∈ V ∧ q ∈ V ∧ p ≠ q

/-! ### Journeys and temporal distance -/

-- CSLib candidate: `Reach`, `TReach`, `tdist`, `tdist_le_iff`, `Reach.shift_iff` (next to
-- `Cslib.DynNet`), and the timeliness classes below.

/-- `Reach G p a b q`: `p = q`, or there is a journey from `p` to `q` whose edges are all taken in
rounds of `[a, b)`, at strictly increasing times. -/
inductive Reach (G : DG ι) : ι → ℕ → ℕ → ι → Prop
  | refl (p : ι) (a b : ℕ) : Reach G p a b p
  | step {p r q : ι} {a b t : ℕ} : a ≤ t → t < b → G t p r → Reach G r (t + 1) b q →
      Reach G p a b q

/-- `p ⇝ q` in the suffix `G_{i▷}` (`p = q` or there is a journey from `p` to `q` starting at
round `i` or later). -/
def TReach (G : DG ι) (i : ℕ) (p q : ι) : Prop := ∃ b, Reach G p i b q

/-- The temporal distance `d̂_{G_{i▷}}(p, q)`: the least `k` such that a journey from `p` to `q`
starting at round `i` or later arrives by round `i + k - 1` (`0` iff `p = q`; `⊤` if no journey). -/
noncomputable def tdist (G : DG ι) (i : ℕ) (p q : ι) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k | Reach G p i (i + k) q})

namespace Reach

variable {G : DG ι}

theorem mono_right {p q : ι} {a b b' : ℕ} (h : Reach G p a b q) (hb : b ≤ b') :
    Reach G p a b' q := by
  induction h with
  | refl p a b => exact .refl p a b'
  | step hat htb hG _ ih => exact .step hat (by omega) hG (ih hb)

theorem mono_left {p q : ι} {a a' b : ℕ} (h : Reach G p a b q) (ha : a' ≤ a) :
    Reach G p a' b q := by
  cases h with
  | refl => exact .refl _ _ _
  | step hat htb hG h => exact .step (by omega) htb hG h

theorem trans {p r q : ι} {a b c : ℕ} (h₁ : Reach G p a b r) (h₂ : Reach G r b c q)
    (hab : a ≤ b) (hbc : b ≤ c) : Reach G p a c q := by
  induction h₁ with
  | refl p a b => exact h₂.mono_left hab
  | step hat htb hG _ ih => exact .step hat (by omega) hG (ih h₂ (by omega) hbc)

theorem single {p q : ι} {t : ℕ} (h : G t p q) : Reach G p t (t + 1) q :=
  .step le_rfl (by omega) h (.refl _ _ _)

/-- Journeys in a shifted dynamic graph. -/
theorem shift_iff {i : ℕ} {p q : ι} {a b : ℕ} :
    Reach (shift i G) p a b q ↔ Reach G p (i + a) (i + b) q := by
  constructor
  · intro h
    induction h with
    | refl p a b => exact .refl _ _ _
    | step hat htb hG _ ih =>
      exact .step (by omega) (by omega) hG (by rw [← Nat.add_assoc] at ih; exact ih)
  · intro h
    generalize ha : i + a = a' at h
    generalize hb : i + b = b' at h
    induction h generalizing a with
    | refl p a b => exact .refl _ _ _
    | @step p r q a'' b'' t hat htb hG _ ih =>
      obtain ⟨t', rfl⟩ : ∃ t', t = i + t' := ⟨t - i, by omega⟩
      exact .step (a := a) (t := t') (by omega) (by omega) hG (ih (by omega) hb)

end Reach

theorem tdist_le_iff {G : DG ι} {i : ℕ} {p q : ι} {Δ : ℕ} :
    tdist G i p q ≤ Δ ↔ Reach G p i (i + Δ) q := by
  constructor
  · intro h
    have hne : ((fun k : ℕ => (k : ℕ∞)) '' {k | Reach G p i (i + k) q}).Nonempty := by
      by_contra hc
      rw [Set.not_nonempty_iff_eq_empty] at hc
      simp only [tdist, hc, sInf_empty, top_le_iff, ENat.coe_ne_top] at h
    obtain ⟨k, hk, hkeq⟩ := csInf_mem hne
    have : (k : ℕ∞) ≤ Δ := by unfold tdist at h; rw [← hkeq] at h; exact h
    exact Reach.mono_right hk (by have := ENat.coe_le_coe.mp this; omega)
  · intro h
    exact sInf_le ⟨Δ, h, rfl⟩

theorem tdist_eq_zero_iff {G : DG ι} {i : ℕ} {p q : ι} : tdist G i p q = 0 ↔ p = q := by
  rw [← nonpos_iff_eq_zero, show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, tdist_le_iff]
  constructor
  · intro h
    cases h with
    | refl => rfl
    | step hat htb => omega
  · rintro rfl; exact .refl _ _ _

theorem tdist_lt_top_iff {G : DG ι} {i : ℕ} {p q : ι} : tdist G i p q < ⊤ ↔ TReach G i p q := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp h.ne
    have : tdist G i p q ≤ k := hk ▸ le_rfl
    exact ⟨_, tdist_le_iff.mp this⟩
  · rintro ⟨b, hb⟩
    have : tdist G i p q ≤ (b - i : ℕ) := tdist_le_iff.mpr (hb.mono_right (by omega))
    exact lt_of_le_of_lt this (ENat.coe_lt_top _)

/-! ### The nine classes (Table 1) -/

/-- Timeliness of the connection from one vertex to another. -/
inductive Timeliness
  /-- recurrent: `p ⇝ q` in every suffix `G_{i▷}` -/
  | recur
  /-- quasi-timely: infinitely often `d̂_{G_{j▷}}(p, q) ≤ Δ` -/
  | quasi
  /-- timely ("bounded"): always `d̂_{G_{i▷}}(p, q) ≤ Δ` -/
  | bounded
  deriving DecidableEq

/-- Which vertices are required to be (timely) sources/sinks. -/
inductive Kind
  /-- at least one source (`J_{1,*}`) -/
  | src
  /-- at least one sink (`J_{*,1}`) -/
  | snk
  /-- every vertex is a source (`J_{*,*}`) -/
  | all
  deriving DecidableEq

/-- The connection condition from `p` to `q` for each timeliness. -/
def Conn (τ : Timeliness) (Δ : ℕ) (G : DG ι) (p q : ι) : Prop :=
  match τ with
  | .recur => ∀ i, TReach G i p q
  | .quasi => ∀ i, ∃ j ≥ i, tdist G j p q ≤ Δ
  | .bounded => ∀ i, tdist G i p q ≤ Δ

/-- The class `J_{k}^{τ}(Δ)` of dynamic graphs with vertex set `V` (Table 1). -/
def J (k : Kind) (τ : Timeliness) (Δ : ℕ) (V : Finset ι) : Set (DG ι) :=
  {G | IsDG V G ∧
    match k with
    | .src => ∃ s ∈ V, ∀ p ∈ V, Conn τ Δ G s p
    | .snk => ∃ s ∈ V, ∀ p ∈ V, Conn τ Δ G p s
    | .all => ∀ p ∈ V, ∀ q ∈ V, Conn τ Δ G p q}

/-- `J_{1,*}`: at least one temporal source. -/
abbrev J1s (V : Finset ι) : Set (DG ι) := J .src .recur 0 V
/-- `J^Q_{1,*}(Δ)`: at least one quasi-timely source. -/
abbrev J1sQ (Δ : ℕ) (V : Finset ι) : Set (DG ι) := J .src .quasi Δ V
/-- `J^B_{1,*}(Δ)`: at least one timely source. -/
abbrev J1sB (Δ : ℕ) (V : Finset ι) : Set (DG ι) := J .src .bounded Δ V
/-- `J_{*,1}`: at least one temporal sink. -/
abbrev Js1 (V : Finset ι) : Set (DG ι) := J .snk .recur 0 V
/-- `J^Q_{*,1}(Δ)`: at least one quasi-timely sink. -/
abbrev Js1Q (Δ : ℕ) (V : Finset ι) : Set (DG ι) := J .snk .quasi Δ V
/-- `J^B_{*,1}(Δ)`: at least one timely sink. -/
abbrev Js1B (Δ : ℕ) (V : Finset ι) : Set (DG ι) := J .snk .bounded Δ V
/-- `J_{*,*}`: every vertex is a temporal source. -/
abbrev Jss (V : Finset ι) : Set (DG ι) := J .all .recur 0 V
/-- `J^Q_{*,*}(Δ)`: every vertex is a quasi-timely source. -/
abbrev JssQ (Δ : ℕ) (V : Finset ι) : Set (DG ι) := J .all .quasi Δ V
/-- `J^B_{*,*}(Δ)`: every vertex is a timely source. -/
abbrev JssB (Δ : ℕ) (V : Finset ι) : Set (DG ι) := J .all .bounded Δ V

/-- The recurrent classes do not depend on `Δ`. -/
theorem J_rec_eq (k : Kind) (Δ Δ' : ℕ) (V : Finset ι) : J k .recur Δ V = J k .recur Δ' V := rfl

theorem conn_shift {τ : Timeliness} {Δ : ℕ} {G : DG ι} {p q : ι} (h : Conn τ Δ G p q) (i : ℕ) :
    Conn τ Δ (shift i G) p q := by
  have hd : ∀ j, tdist (shift i G) j p q ≤ Δ ↔ tdist G (i + j) p q ≤ Δ := by
    intro j; rw [tdist_le_iff, tdist_le_iff, Reach.shift_iff, Nat.add_assoc]
  cases τ with
  | recur =>
    intro j
    obtain ⟨b, hb⟩ := h (i + j)
    exact ⟨b - i, Reach.shift_iff.mpr (hb.mono_right (by omega))⟩
  | quasi =>
    intro j
    obtain ⟨j', hj', hd'⟩ := h (i + j)
    exact ⟨j' - i, by omega, (hd _).mpr (by rwa [show i + (j' - i) = j' by omega])⟩
  | bounded => intro j; exact (hd j).mpr (h (i + j))

/-- All nine classes are recurring (suffix-closed). -/
theorem J_shift {k : Kind} {τ : Timeliness} {Δ : ℕ} {V : Finset ι} {G : DG ι}
    (hG : G ∈ J k τ Δ V) (i : ℕ) : shift i G ∈ J k τ Δ V := by
  obtain ⟨hdg, h⟩ := hG
  refine ⟨fun t p q hpq => hdg (i + t) p q hpq, ?_⟩
  cases k with
  | src => obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs, fun p hp => conn_shift (h p hp) i⟩
  | snk => obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs, fun p hp => conn_shift (h p hp) i⟩
  | all => exact fun p hp q hq => conn_shift (h p hp q hq) i

/-! ### Algorithms, executions, and stabilization -/

/-- A deterministic (full-information) distributed algorithm for a fixed number of processes:
the code `step p` of each process `p` and its output `lid p` (the identifier of its leader). -/
structure Algorithm (ι σ : Type*) where
  /-- One synchronous round: process `p` maps the received states (`none` = not heard; its own
  state is always received) to its new state. -/
  step : StepFn ι σ
  /-- The output variable `lid(p)`, as a function of the local state. -/
  lid : ι → σ → ι

/-- The execution of `A` in the dynamic graph `G` from the configuration `γ`: `exec A G γ t` is
the configuration at the beginning of round `t` (0-indexed). -/
noncomputable def exec (A : Algorithm ι σ) (G : DG ι) (γ : ι → σ) : ℕ → ι → σ :=
  conf A.step γ G

theorem exec_add (A : Algorithm ι σ) (G : DG ι) (γ : ι → σ) (i t : ℕ) :
    exec A G γ (i + t) = exec A (shift i G) (exec A G γ i) t :=
  conf_add γ G i t

/-- The leader election specification `SP_LE` on a sequence of configurations: some process
`ℓ ∈ V` is the leader of every process of `V` in every configuration. -/
def SPLE (A : Algorithm ι σ) (V : Finset ι) (e : ℕ → ι → σ) : Prop :=
  ∃ ℓ ∈ V, ∀ i, ∀ q ∈ V, A.lid q (e i q) = ℓ

/-- A class of dynamic graphs, for each vertex set. -/
abbrev DGClass (ι : Type*) := Finset ι → Set (DG ι)

/-- **Definition 2** (pseudo-stabilization), for systems of `n` processes: every execution from
every configuration in every dynamic graph of the class has a suffix satisfying `SP_LE`. -/
def PseudoStab (A : Algorithm ι σ) (C : DGClass ι) (n : ℕ) : Prop :=
  ∀ V : Finset ι, V.card = n → ∀ G ∈ C V, ∀ γ : ι → σ, ∃ i, SPLE A V (fun t => exec A G γ (i + t))

/-- **Definition 1** (self-stabilization), for systems of `n` processes: for every vertex set
there is a set `L` of legitimate configurations that every execution reaches (convergence) and from
which every execution satisfies `SP_LE` (correctness). -/
def SelfStab (A : Algorithm ι σ) (C : DGClass ι) (n : ℕ) : Prop :=
  ∀ V : Finset ι, V.card = n → ∃ L : Set (ι → σ),
    (∀ G ∈ C V, ∀ γ : ι → σ, ∃ i, exec A G γ i ∈ L) ∧
    (∀ G ∈ C V, ∀ γ ∈ L, SPLE A V (exec A G γ))

/-- The pseudo-stabilization phase of every execution in the class has length at most `T`, i.e.
`SP_LE` holds from configuration `γ_{T+1}` (0-indexed: `exec … T`) on. -/
def PseudoStabWithin (A : Algorithm ι σ) (C : DGClass ι) (n T : ℕ) : Prop :=
  ∀ V : Finset ι, V.card = n → ∀ G ∈ C V, ∀ γ : ι → σ, SPLE A V (fun t => exec A G γ (T + t))

theorem PseudoStabWithin.pseudoStab {A : Algorithm ι σ} {C : DGClass ι} {n T : ℕ}
    (h : PseudoStabWithin A C n T) : PseudoStab A C n :=
  fun V hV G hG γ => ⟨T, h V hV G hG γ⟩

theorem PseudoStab.mono {A : Algorithm ι σ} {C C' : DGClass ι} {n : ℕ}
    (h : PseudoStab A C n) (hC : ∀ V, C' V ⊆ C V) : PseudoStab A C' n :=
  fun V hV G hG => h V hV G (hC V hG)

theorem SelfStab.mono {A : Algorithm ι σ} {C C' : DGClass ι} {n : ℕ}
    (h : SelfStab A C n) (hC : ∀ V, C' V ⊆ C V) : SelfStab A C' n := by
  intro V hV
  obtain ⟨L, h1, h2⟩ := h V hV
  exact ⟨L, fun G hG => h1 G (hC V hG), fun G hG => h2 G (hC V hG)⟩

/-- **Remark 1**: on a recurring class, self-stabilization implies pseudo-stabilization. -/
theorem SelfStab.pseudoStab {A : Algorithm ι σ} {C : DGClass ι} {n : ℕ}
    (hrec : ∀ V, ∀ G ∈ C V, ∀ i, shift i G ∈ C V) (h : SelfStab A C n) : PseudoStab A C n := by
  intro V hV G hG γ
  obtain ⟨L, hconv, hcorr⟩ := h V hV
  obtain ⟨i, hi⟩ := hconv G hG γ
  refine ⟨i, ?_⟩
  have := hcorr (shift i G) (hrec V G hG i) _ hi
  simpa only [exec_add] using this

theorem SPLE.shift {A : Algorithm ι σ} {V : Finset ι} {e : ℕ → ι → σ} (h : SPLE A V e) (i : ℕ) :
    SPLE A V (fun t => e (i + t)) := by
  obtain ⟨ℓ, hℓ, h⟩ := h
  exact ⟨ℓ, hℓ, fun t => h (i + t)⟩

end StabilizingLEDynamic
