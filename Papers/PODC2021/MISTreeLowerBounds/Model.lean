import Papers.PODC2021.MISTreeLowerBounds.Problem
import Cslib.Computability.Distributed.ColourSystem.FreeCoxeter

/-!
# The port-numbering model on the `Δ`-edge-coloured `Δ`-regular tree

The paper proves its lower bound in the deterministic port-numbering (PN) model on `Δ`-regular trees,
with two inputs (§2.1, §2.3):
* a `Δ`-edge colouring, each node knowing the colours of its incident edges, and
* an *edge port numbering* (each edge has the numbers `1, 2` at its endpoints), i.e. an orientation
  of the edges.

We work on the infinite `Δ`-regular tree, realized as the Cayley graph of the free Coxeter group
`FreeCox Δ = ⟨1, …, Δ | 1², …, Δ²⟩` (CSLib): nodes are group elements, the neighbour of `v` along
the edge of colour `c` is `v * gen c`. Port numbers equal colours (as in the graph family of
Lemmas 12 and 15; since the colours are known, arbitrary port numbers carry no extra information).
The only free input is the orientation (`Orientation`), given as a direction bit on each dart,
antisymmetric along each edge.

A `t`-round algorithm is a function of the radius-`t` view (as in the paper, §2.1: "a function that
maps `T`-radius neighborhoods into outputs"). The radius-`t` view of the root `1` consists of the
inputs on all edges having both endpoints within distance `t` (`AgreeOn t`); the view of `v` is
the view of the root in the translated input `I.shift v`. In particular a 0-round algorithm sees no
orientation at all: this is the convention used in the proof of Lemma 12 ("they do not even see
the port numbering of the edges, that is, their orientation").

`Solves P A`: the algorithm `A` (output = one label per incident edge, indexed by colour) solves
`P` on every input: at every node the configuration is in `P.node` and along every edge of colour
`c` the two labels form an edge configuration.
-/

-- CSLib candidate (round elimination on the oriented Δ-edge-coloured Δ-regular tree)
namespace Podc.MISTreeLowerBounds

open Cslib.ColourSystem FreeCox

variable {Δ : ℕ}

/-- An orientation of the edges of the tree (the paper's edge port numbering): `dir v c = true`
iff the edge `{v, v * gen c}` is oriented away from `v`. -/
structure Orientation (Δ : ℕ) where
  /-- The direction bit of the dart from `v` along colour `c`. -/
  dir : FreeCox Δ → Fin Δ → Bool
  anti : ∀ v c, dir (v * gen c) c = !dir v c

namespace Orientation

/-- The input seen from `u`: re-root the tree at `u` (left translation by `u`). -/
def shift (I : Orientation Δ) (u : FreeCox Δ) : Orientation Δ where
  dir v c := I.dir (u * v) c
  anti v c := by simp only [← mul_assoc, I.anti]

@[simp] theorem shift_dir (I : Orientation Δ) (u v : FreeCox Δ) (c : Fin Δ) :
    (I.shift u).dir v c = I.dir (u * v) c := rfl

@[simp] theorem shift_one (I : Orientation Δ) : I.shift 1 = I := by
  cases I; simp [shift]

@[simp] theorem shift_shift (I : Orientation Δ) (u v : FreeCox Δ) :
    (I.shift u).shift v = I.shift (u * v) := by
  simp [shift, mul_assoc]

/-- Some orientation exists (orient every edge away from the root). -/
instance : Inhabited (Orientation Δ) :=
  ⟨⟨fun v c => decide (len v < len (v * gen c)), fun v c => by
    have h1 := len_mul_gen_ne v c
    simp only [mul_gen_mul_gen]
    by_cases h : len v < len (v * gen c)
    · simp [h, le_of_lt h]
    · have : len (v * gen c) < len v := by omega
      simp [h, this]⟩⟩

end Orientation

/-- `I` and `J` agree on the set of nodes `S`: on every edge with both endpoints in `S`. -/
def AgreeOnSet (S : Set (FreeCox Δ)) (I J : Orientation Δ) : Prop :=
  ∀ v c, v ∈ S → v * gen c ∈ S → I.dir v c = J.dir v c

/-- `I` and `J` have the same radius-`t` view at the root. -/
def AgreeOn (t : ℕ) (I J : Orientation Δ) : Prop :=
  AgreeOnSet {v | len v ≤ t} I J

/-- `A` is a `t`-round algorithm: its output at the root depends only on the radius-`t` view. -/
def IsLocal {β : Type*} (t : ℕ) (A : Orientation Δ → β) : Prop :=
  ∀ I J, AgreeOn t I J → A I = A J

/-- The algorithm `A` (the output at the root; at node `v` it outputs `A (I.shift v)`) solves `P`
on the oriented `Δ`-edge-coloured `Δ`-regular tree. -/
def Problem.Solves {Λ : Type*} (P : Problem Δ Λ) (A : Orientation Δ → Fin Δ → Λ) : Prop :=
  ∀ (I : Orientation Δ) (v : FreeCox Δ), A (I.shift v) ∈ P.node ∧
    ∀ c, P.edge (A (I.shift v) c) (A (I.shift (v * gen c)) c)

/-- `P` can be solved in `t` rounds (deterministic PN model, `Δ`-edge colouring and edge
orientation given). -/
def Problem.SolvableIn {Λ : Type*} (P : Problem Δ Λ) (t : ℕ) : Prop :=
  ∃ A : Orientation Δ → Fin Δ → Λ, IsLocal t A ∧ P.Solves A

theorem solves_iff {Λ : Type*} {P : Problem Δ Λ} {A : Orientation Δ → Fin Δ → Λ} :
    P.Solves A ↔ ∀ I : Orientation Δ, A I ∈ P.node ∧ ∀ c, P.edge (A I c) (A (I.shift (gen c)) c) := by
  constructor
  · intro h I
    simpa using h I 1
  · intro h I v
    simpa using h (I.shift v)

theorem AgreeOnSet.mono {S T : Set (FreeCox Δ)} {I J : Orientation Δ} (h : AgreeOnSet T I J)
    (hST : S ⊆ T) : AgreeOnSet S I J :=
  fun v c hv hvc => h v c (hST hv) (hST hvc)

theorem AgreeOnSet.symm {S : Set (FreeCox Δ)} {I J : Orientation Δ} (h : AgreeOnSet S I J) :
    AgreeOnSet S J I :=
  fun v c hv hvc => (h v c hv hvc).symm

theorem AgreeOnSet.trans {S : Set (FreeCox Δ)} {I J K : Orientation Δ} (h : AgreeOnSet S I J)
    (h' : AgreeOnSet S J K) : AgreeOnSet S I K :=
  fun v c hv hvc => (h v c hv hvc).trans (h' v c hv hvc)

theorem agreeOnSet_shift {S : Set (FreeCox Δ)} {I J : Orientation Δ} {u : FreeCox Δ} :
    AgreeOnSet S (I.shift u) (J.shift u) ↔ AgreeOnSet ((u * ·) '' S) I J := by
  constructor
  · rintro h _ c ⟨v, hv, rfl⟩ ⟨w, hw, hw'⟩
    have : w = v * gen c := by
      have := congrArg (u⁻¹ * ·) hw'
      simpa [← mul_assoc] using this
    subst this
    exact h v c hv hw
  · intro h v c hv hvc
    exact h (u * v) c ⟨v, hv, rfl⟩ ⟨v * gen c, hvc, by simp [mul_assoc]⟩

theorem IsLocal.mono {β : Type*} {t t' : ℕ} {A : Orientation Δ → β} (h : IsLocal t A)
    (htt' : t ≤ t') : IsLocal t' A :=
  fun I J hIJ => h I J (hIJ.mono fun v (hv : len v ≤ t) => le_trans hv htt')

theorem Problem.SolvableIn.mono {Λ : Type*} {P : Problem Δ Λ} {t t' : ℕ} (h : P.SolvableIn t)
    (htt' : t ≤ t') : P.SolvableIn t' := by
  obtain ⟨A, hA, hs⟩ := h
  exact ⟨A, hA.mono htt', hs⟩

/-- A 0-round reduction transfers solvability in `t` rounds. -/
theorem Problem.SolvableIn.of_reduction {Λ Λ' : Type*} {P : Problem Δ Λ} {P' : Problem Δ Λ'} {t : ℕ}
    (h : P.SolvableIn t) (hr : ZeroRoundReduction P P') : P'.SolvableIn t := by
  obtain ⟨A, hA, hs⟩ := h
  obtain ⟨f, hf1, hf2⟩ := hr
  refine ⟨fun I => f (A I), fun I J h => by simp only [hA I J h], fun I v => ?_⟩
  obtain ⟨h1, h2⟩ := hs I v
  refine ⟨hf1 _ h1, fun c => hf2 _ h1 _ (hs I (v * gen c)).1 c (h2 c)⟩

/-- A 0-round algorithm sees nothing: it outputs the same configuration everywhere. -/
theorem IsLocal.zero_eq {β : Type*} {A : Orientation Δ → β} (h : IsLocal 0 A) (I J : Orientation Δ) :
    A I = A J := by
  refine h I J fun v c hv hvc => ?_
  have h1 : len v = 0 := Nat.le_zero.1 hv
  have h2 : len (v * gen c) = 0 := Nat.le_zero.1 hvc
  have := len_mul_gen_ne v c
  omega

/-- Characterization of 0-round solvability: some single configuration `σ ∈ P.node` has every
label edge-compatible with itself (in the graphs of the model the edge of colour `c` carries the
labels of the half-edges of colour `c` of both endpoints). -/
theorem solvableIn_zero_iff {Λ : Type*} {P : Problem Δ Λ} :
    P.SolvableIn 0 ↔ ∃ σ ∈ P.node, ∀ c, P.edge (σ c) (σ c) := by
  constructor
  · rintro ⟨A, hA, hs⟩
    let I : Orientation Δ := default
    obtain ⟨h1, h2⟩ := hs I 1
    refine ⟨A (I.shift 1), h1, fun c => ?_⟩
    have := h2 c
    rwa [hA.zero_eq (I.shift (1 * gen c)) (I.shift 1)] at this
  · rintro ⟨σ, hσ, hc⟩
    exact ⟨fun _ => σ, fun _ _ _ => rfl, fun _ _ => ⟨hσ, hc⟩⟩

end Podc.MISTreeLowerBounds
