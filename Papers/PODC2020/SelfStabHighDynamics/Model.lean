import Papers.PODC2021.StabilizingLEDynamic.Model

/-!
# Model: algorithms for every set of processes, self-stabilization, closure, size-ambiguity

Altisen, Devismes, Durand, Johnen, Petit, *Self-stabilizing Systems in Spite of High Dynamics*
(PODC 2020 brief announcement; full version: Theoretical Computer Science 2023,
HAL hal-04109662), Sections 2–3.

We reuse the dynamic-graph model of `Papers/PODC2021/StabilizingLEDynamic/Model.lean` (same
authors, same classes):

* processes are identified with their identifiers (`ι` = `IDSET`, `id(p) = p`), a system is a
  finite set `V : Finset ι`;
* a TVG is a dynamic graph `G : ℕ → Graph ι` with `IsDG V G` (edges between distinct processes of
  `V`); rounds are **0-indexed**: `G t` is the snapshot of the paper's Round `t + 1`, and
  `exec A G γ t` is the paper's `γ_t` (the configuration at the end of Round `t`, i.e. at the
  beginning of Round `t + 1`);
* `TC_B(Δ) = JssB Δ V`, `TC_Q(Δ) = JssQ Δ V`, `TC_R = Jss V` (temporal distance `tdist`, a journey
  of temporal length `≤ Δ` from time `i` uses the rounds `i, …, i + Δ - 1`);
* algorithms are deterministic full-information round algorithms (`Cslib.HeardOf.StepFn`): each
  process receives the whole state of each current in-neighbour, which is at least as strong as
  the paper's `SEND` of part of the state.

New here (Section 3): an algorithm `SAlg` is defined for **every** set of processes `V`. The code
of a process `p` (`step p`, `lid p`) does not depend on `V`; knowledge about the system (such as
`n`) is an input stored in the local state, so it is captured by the sets of possible local states
`S V p` (the paper's `S_A^V(p)`), exactly as in the paper's discussion before Definition 3.
Configurations of `A` for `V` are the `γ` with `γ p ∈ S V p` for `p ∈ V` (the states of processes
outside `V` are irrelevant).

Since all classes considered are recurring (`StabilizingLEDynamic.J_shift`), Definitions 1 and 2
are stated in the simplified form of Remarks 1 and 2 (executions from time `0` of every graph of
the class).
-/

namespace Podc.SelfStabHighDynamics

open Cslib.HeardOf
open StabilizingLEDynamic (DG IsDG Algorithm SPLE DGClass JssB JssQ Jss)

variable {ι σ : Type*}

-- CSLib candidate
/-- A deterministic distributed algorithm defined for every set of processes: the code of each
process (independent of the system) and, for every system `V`, the nonempty set `S V p` of
possible local states of `p` (the paper's `S_A^V(p)`). -/
structure SAlg (ι σ : Type*) extends Algorithm ι σ where
  /-- The possible local states of `p` in the system `V`. -/
  S : Finset ι → ι → Set σ
  /-- Every process has a possible local state. -/
  S_nonempty : ∀ V p, p ∈ V → (S V p).Nonempty

namespace SAlg

variable (A : SAlg ι σ)

/-- The execution of `A` in `G` from `γ` (`exec G γ t` = configuration at the end of Round `t`). -/
noncomputable abbrev exec (G : DG ι) (γ : ι → σ) : ℕ → ι → σ :=
  StabilizingLEDynamic.exec A.toAlgorithm G γ

/-- The configurations of `A` for `V` (`C_A^V`). -/
def Cfg (V : Finset ι) : Set (ι → σ) := {γ | ∀ p ∈ V, γ p ∈ A.S V p}

theorem cfg_nonempty (V : Finset ι) : (A.Cfg V).Nonempty := by
  classical
  refine ⟨fun p => if h : p ∈ V then (A.S_nonempty V p h).some else
    (A.S_nonempty {p} p (Finset.mem_singleton_self p)).some, fun p hp => ?_⟩
  simp only [dif_pos hp]
  exact (A.S_nonempty V p hp).some_mem

end SAlg

/-- A specification: a predicate on the sequences of configurations of a system `V`. -/
abbrev Spec (ι σ : Type*) := Finset ι → (ℕ → ι → σ) → Prop

/-- The leader election specification `SP_LE` (Section 3.2). -/
def spLE (A : SAlg ι σ) : Spec ι σ := fun V e => SPLE A.toAlgorithm V e

/-- **Definition 4.** A recurring specification: satisfied by every suffix of a sequence that
satisfies it. -/
def Recurring (SP : Spec ι σ) : Prop := ∀ V e, SP V e → ∀ i, SP V (fun t => e (i + t))

theorem recurring_spLE (A : SAlg ι σ) : Recurring (spLE A) :=
  fun _ _ h i => StabilizingLEDynamic.SPLE.shift h i

variable (A : SAlg ι σ) (C : DGClass ι) (SP : Spec ι σ)

/-- `L` is a set of legitimate configurations of `A` for `V` (Definition 1, in the form of
Remark 1): `L ⊆ C_A^V`, every execution from a configuration of `A` for `V` in every graph of the
class reaches `L` (convergence), and every execution from `L` satisfies `SP` (correctness). -/
def IsLegit (V : Finset ι) (L : Set (ι → σ)) : Prop :=
  L ⊆ A.Cfg V ∧
  (∀ G ∈ C V, ∀ γ ∈ A.Cfg V, ∃ i, A.exec G γ i ∈ L) ∧
  (∀ G ∈ C V, ∀ γ ∈ L, SP V (A.exec G γ))

/-- **Definition 1** (self-stabilization on a recurring class, Remark 1): for every (nonempty)
set of processes `V` there is a set of legitimate configurations. -/
def SelfStab : Prop := ∀ V : Finset ι, V.Nonempty → ∃ L, IsLegit A C SP V L

/-- **Definition 2** (closure on a recurring class, Remark 2). -/
def Closed (V : Finset ι) (L : Set (ι → σ)) : Prop :=
  ∀ G ∈ C V, ∀ γ ∈ L, ∀ i, A.exec G γ i ∈ L

/-- **Definition 6** (pseudo-stabilization): every execution has a suffix satisfying `SP`. -/
def PseudoStab : Prop :=
  ∀ V : Finset ι, V.Nonempty → ∀ G ∈ C V, ∀ γ ∈ A.Cfg V, ∃ i, SP V (fun t => A.exec G γ (i + t))

/-- **Definition 3** (size-ambiguity): `A` is `(k, V)`-ambiguous if `0 < k < |V|` and every
process of every `k`-subset `U` of `V` has the same possible local states in the systems `U` and
`V`. -/
def Ambiguous (k : ℕ) (V : Finset ι) : Prop :=
  0 < k ∧ k < V.card ∧ ∀ U ⊆ V, U.card = k → ∀ p ∈ U, A.S U p = A.S V p

/-- `A` is size-ambiguous if it is `(k, V)`-ambiguous for some `k` and `V`. -/
def SizeAmbiguous : Prop := ∃ k V, Ambiguous A k V

variable {A C SP}

theorem IsLegit.mono {C' : DGClass ι} {V : Finset ι} {L : Set (ι → σ)} (h : IsLegit A C SP V L)
    (hC : C' V ⊆ C V) : IsLegit A C' SP V L :=
  ⟨h.1, fun G hG => h.2.1 G (hC hG), fun G hG => h.2.2 G (hC hG)⟩

theorem SelfStab.mono {C' : DGClass ι} (h : SelfStab A C SP) (hC : ∀ V, C' V ⊆ C V) :
    SelfStab A C' SP := fun V hV =>
  let ⟨L, hL⟩ := h V hV
  ⟨L, hL.mono (hC V)⟩

/-- **Remark 7.** Self-stabilization implies pseudo-stabilization (on a recurring class). -/
theorem SelfStab.pseudoStab (hrec : ∀ V, ∀ G ∈ C V, ∀ i, shift i G ∈ C V)
    (h : SelfStab A C SP) : PseudoStab A C SP := by
  intro V hV G hG γ hγ
  obtain ⟨L, -, hconv, hcorr⟩ := h V hV
  obtain ⟨i, hi⟩ := hconv G hG γ hγ
  refine ⟨i, ?_⟩
  have := hcorr (shift i G) (hrec V G hG i) _ hi
  simpa [SAlg.exec, StabilizingLEDynamic.exec_add] using this

/-! ### Received messages

Helpers for message-passing algorithms in the full-information model: the set of items (for
instance identifier/timestamp pairs) that `me` receives from processes other than itself, as a
finite set (it is finite in every execution in a graph with a finite vertex set; `∅` is a junk
value otherwise). -/

/-- The items `x ∈ f s` sent by the processes `q ≠ me` whose state `s` is received. -/
def rset {β : Type*} (f : σ → Set β) (me : ι) (m : ι → Option σ) : Set β :=
  {x | ∃ q, q ≠ me ∧ ∃ s, m q = some s ∧ x ∈ f s}

open Classical in
/-- The received items as a finite set. -/
noncomputable def rfin {β : Type*} (f : σ → Set β) (me : ι) (m : ι → Option σ) : Finset β :=
  if h : (rset f me m).Finite then h.toFinset else ∅

/-- In a round of a dynamic graph with vertex set `V`, process `p` receives exactly the items of
its current in-neighbours. -/
theorem mem_rfin_msgs {β : Type*} {f : σ → Set β} (hf : ∀ s, (f s).Finite) {V : Finset ι}
    {G : DG ι} (hG : IsDG V G) (t : ℕ) (C : ι → σ) (p : ι) (x : β) :
    x ∈ rfin f p (msgs (G t) C p) ↔ ∃ q, G t q p ∧ x ∈ f (C q) := by
  classical
  have hset : rset f p (msgs (G t) C p) = {x | ∃ q, G t q p ∧ x ∈ f (C q)} := by
    ext x
    simp only [rset, msgs, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hq, s, hs, hx⟩
      by_cases h : Hears (G t) p q
      · rw [if_pos h] at hs; cases hs
        exact ⟨q, h.resolve_left hq, hx⟩
      · rw [if_neg h] at hs; cases hs
    · rintro ⟨q, hq, hx⟩
      exact ⟨q, (hG t q p hq).2.2, _, by rw [if_pos (show Hears (G t) p q from Or.inr hq)], hx⟩
  have hfin : (rset f p (msgs (G t) C p)).Finite := by
    rw [hset]
    refine (V.finite_toSet.biUnion fun q _ => hf (C q)).subset ?_
    rintro y ⟨q, hq, hy⟩
    exact Set.mem_biUnion (hG t q p hq).1 hy
  simp only [rfin, dif_pos hfin, Set.Finite.mem_toFinset]
  rw [hset]; rfl

/-- Own state is always received. -/
theorem msgs_self (G : Graph ι) (C : ι → σ) (p : ι) : msgs G C p p = some (C p) := by
  classical
  simp [msgs, hears_self]

/-! ### Identifier/timestamp lists (Algorithms 2 and 3) -/

/-- The local state of Algorithms 2 and 3: the input `n`, the list `members` of pairs
`⟨id, t⟩` (a FIFO queue in Algorithm 2, a map in Algorithm 3), and the output `lid`. -/
structure MSt (ι : Type*) where
  /-- The input `n` (number of processes). -/
  n : ℕ
  /-- The variable `members(p)`. -/
  mem : List (ι × ℕ)
  /-- The output `lid(p)`. -/
  lid : ι

/-- The identifiers of a list of pairs. -/
def keys (l : List (ι × ℕ)) : List ι := l.map Prod.fst

/-- `min (d, ids of l)`; used as `min {id : ⟨id, _⟩ ∈ members(p)}` (line 8 of Algorithms 2
and 3), where `d = id(p)` is always one of the identifiers. -/
def minKey [LinearOrder ι] (l : List (ι × ℕ)) (d : ι) : ι := l.foldl (fun a x => min a x.1) d

end Podc.SelfStabHighDynamics
