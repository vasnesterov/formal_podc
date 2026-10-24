import Papers.PODC2010.ArbdefectiveColoring.PartialOrientation

/-!
# Procedure Legal-Coloring (Algorithm 2), generic form (Lemma 4.2(1), correctness of Theorem 4.3)

The procedure refines a decomposition of `G` into subgraphs `I` times: in every iteration it runs
Procedure Arbdefective-Coloring with `p` colours on all current subgraphs in parallel, and gives the
`j`-th part of the `i`-th subgraph the index `i·p + j` (line 9). Afterwards all subgraphs are
coloured legally in parallel, with disjoint palettes (lines 17–20).

We keep the subgraph index of `v` as a label `lab i G v < p^i`; the current subgraphs are the
classes of `classGraph G (lab i G)`. The parameters are bundled in `LCParams`: for an arboricity
bound `α`, the H-partition uses degree parameter `A α` and `L α` rounds, the defective colouring
black box `D α` (a `d α`-defective colouring with colours `< K α` in `R α` rounds), and the final
legal colouring black box `B α`. The arboricity bounds follow line 15:
`α_{i+1} = d α_i + ⌊A α_i / p⌋` (Corollary 3.6).

* `lab_spec` (**Lemma 4.2(1)**): after `i` iterations, every subgraph has arboricity `≤ α_i`, and
  there are at most `p^i` subgraphs.
* `legalColoring_correct` (correctness part of **Theorem 4.3**): the result is a legal colouring
  with fewer than `p^I · (A α_I + 1)` colours.
* `legalColoringProc_isLocal`: the round complexity is the sum of the round complexities of the
  `I` invocations of Arbdefective-Coloring and of the final legal colouring.
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- Parameters of Procedure Legal-Coloring, as functions of the current arboricity bound `α`. -/
structure LCParams (V : Type*) [Fintype V] where
  /-- The number of colours of each arbdefective colouring (`k = t = p`). -/
  p : ℕ
  /-- H-partition degree parameter (`⌊(2+ε)α⌋` in the paper). -/
  A : ℕ → ℕ
  /-- H-partition rounds (`O(log n)`). -/
  L : ℕ → ℕ
  /-- Defect of the defective colourings of the H-sets (`⌊α/t⌋` in the paper). -/
  d : ℕ → ℕ
  /-- Number of colours of the defective colourings (`O(t²)`). -/
  K : ℕ → ℕ
  /-- Rounds of the defective colourings (`O(log* n)`). -/
  R : ℕ → ℕ
  /-- The defective colouring algorithms (Lemma 2.1). -/
  D : ∀ α, DefectiveAlg V (A α) (d α) (K α) (R α)
  /-- Number of colours of the legal colourings of the H-sets in the final step. -/
  KB : ℕ → ℕ
  /-- Rounds of the legal colourings of the H-sets in the final step. -/
  RB : ℕ → ℕ
  /-- The legal colouring algorithms used in the final step (Lemma 2.2(1)). -/
  B : ∀ α, DefectiveAlg V (A α) 0 (KB α) (RB α)

namespace LCParams

variable (P : LCParams V)

/-- The new arboricity bound after one iteration (line 15). -/
def next (α : ℕ) : ℕ := P.d α + P.A α / P.p

/-- The arboricity bounds `α_i` (`α_0 = a`). -/
def bound (a : ℕ) : ℕ → ℕ
  | 0 => a
  | i + 1 => P.next (bound a i)

/-- Rounds of one invocation of Arbdefective-Coloring with bound `α`. -/
def arbRounds (α : ℕ) : ℕ := P.L α * P.K α - 1 + (1 + (P.R α + P.L α))

/-- Rounds of the final legal colouring with bound `α`. -/
def legRounds (α : ℕ) : ℕ := P.L α * P.KB α - 1 + (1 + (P.RB α + P.L α))

/-- The subgraph index after `i` iterations. -/
noncomputable def lab (a : ℕ) : ℕ → SimpleGraph V → V → ℕ
  | 0 => fun _ _ => 0
  | i + 1 => fun G v => lab a i G v * P.p +
      arbCol P.p (P.A (P.bound a i)) (P.L (P.bound a i)) (P.K (P.bound a i))
        (P.D (P.bound a i)).col (classGraph G (lab a i G)) v

/-- **Procedure Legal-Coloring** with `I` iterations of the while-loop, for a graph of arboricity
`≤ a`: the final colour of `v` is `(index of its subgraph) · (A α_I + 1) + (its colour in the legal
colouring of its subgraph)` (line 19). -/
noncomputable def proc (a I : ℕ) (G : SimpleGraph V) (v : V) : ℕ :=
  P.lab a I G v * (P.A (P.bound a I) + 1) +
    legalCol (P.A (P.bound a I)) (P.L (P.bound a I)) (P.KB (P.bound a I)) (P.B (P.bound a I)).col
      (classGraph G (P.lab a I G)) v

/-- The total number of rounds of the while-loop. -/
def loopRounds (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => P.arbRounds (P.bound a i) + loopRounds a i

/-- The labels after `i` iterations are computed in `loopRounds a i` rounds. -/
theorem lab_isLocal (a : ℕ) (i : ℕ) : IsLocalG (P.loopRounds a i) (P.lab a i) := by
  induction i with
  | zero => intro _ _ _ _ _ _; rfl
  | succ i ih =>
    have hstep : IsLocal (V := V) (P.arbRounds (P.bound a i)) (fun G (y : V → ℕ) v => y v * P.p +
        arbCol P.p (P.A (P.bound a i)) (P.L (P.bound a i)) (P.K (P.bound a i))
          (P.D (P.bound a i)).col (classGraph G (id ∘ y)) v) := by
      have h1 := IsLocal.prod ((isLocal_self (V := V) fun _ (b : ℕ) => b).mono (Nat.zero_le
        (P.arbRounds (P.bound a i))))
        ((arbCol_isLocal P.p (P.A (P.bound a i)) (P.L (P.bound a i)) (P.K (P.bound a i))
          (P.D (P.bound a i)).isLocal).classGraph (α := ℕ) id)
      exact IsLocal.map h1 (fun q => q.1 * P.p + q.2)
    have := hstep.comp ih
    simpa [IsLocalG, lab, loopRounds] using this

/-- **Round complexity of Procedure Legal-Coloring**: the `I` iterations of the while-loop plus the
final legal colouring. -/
theorem proc_isLocal (a I : ℕ) :
    IsLocalG (P.legRounds (P.bound a I) + P.loopRounds a I) (P.proc a I) := by
  have hstep : IsLocal (V := V) (P.legRounds (P.bound a I)) (fun G (y : V → ℕ) v =>
      y v * (P.A (P.bound a I) + 1) +
        legalCol (P.A (P.bound a I)) (P.L (P.bound a I)) (P.KB (P.bound a I))
          (P.B (P.bound a I)).col (classGraph G (id ∘ y)) v) := by
    have h1 := IsLocal.prod ((isLocal_self (V := V) fun _ (b : ℕ) => b).mono (Nat.zero_le
      (P.legRounds (P.bound a I))))
      ((legalCol_isLocal (P.A (P.bound a I)) (P.L (P.bound a I)) (P.KB (P.bound a I))
        (P.B (P.bound a I)).isLocal).classGraph (α := ℕ) id)
    exact IsLocal.map h1 (fun q => q.1 * (P.A (P.bound a I) + 1) + q.2)
  have := hstep.comp (P.lab_isLocal a I)
  simpa [IsLocalG, proc] using this

/-- `x * p + y` with `y < p` determines `x` and `y`. -/
lemma mul_add_inj {p x x' y y' : ℕ} (hy : y < p) (hy' : y' < p) :
    x * p + y = x' * p + y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    have h1 : (x * p + y) / p = (x' * p + y') / p := by rw [h]
    have h2 : (x * p + y) % p = (x' * p + y') % p := by rw [h]
    have hp : 0 < p := (Nat.zero_le _).trans_lt hy
    rw [mul_comm x, mul_comm x', Nat.mul_add_div hp, Nat.mul_add_div hp, Nat.div_eq_of_lt hy, Nat.div_eq_of_lt hy'] at h1
    rw [mul_comm x, mul_comm x', Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hy'] at h2
    exact ⟨by simpa using h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The termination condition of the H-partition for every bound `α` (`L α = O(log n)`). -/
def HRoundsOK : Prop :=
  ∀ α, Fintype.card V * (2 * α) ^ P.L α < (P.A α + 1) ^ P.L α

/-- **Lemma 4.2(1)**: after `i` iterations of the while-loop, every subgraph in the collection
(every class of `lab i`) has arboricity at most `α_i`; the subgraph indices are `< p^i`. -/
theorem lab_spec (hP : P.HRoundsOK) (hp : 0 < P.p) {G : SimpleGraph V} {a : ℕ}
    (hG : G.ArboricityLE a) (i : ℕ) :
    (classGraph G (P.lab a i G)).ArboricityLE (P.bound a i) ∧ ∀ v, P.lab a i G v < P.p ^ i := by
  induction i with
  | zero =>
    refine ⟨?_, fun v => by simp [lab]⟩
    have : classGraph G (P.lab a 0 G) = G := by ext u v; simp [lab]
    rw [this]; exact hG
  | succ i ih =>
    obtain ⟨harb, hlt⟩ := ih
    set H := classGraph G (P.lab a i G)
    obtain ⟨harb', hlt'⟩ := arbdefectiveColoring_spec (k := P.p) harb.hasOutDegLE (hP _)
      (P.D (P.bound a i)) hp
    set c := arbCol P.p (P.A (P.bound a i)) (P.L (P.bound a i)) (P.K (P.bound a i))
      (P.D (P.bound a i)).col H
    have hlab : ∀ v, P.lab a (i + 1) G v = P.lab a i G v * P.p + c v := fun v => rfl
    refine ⟨?_, fun v => ?_⟩
    · have : classGraph G (P.lab a (i + 1) G) = classGraph H c := by
        ext u v
        simp only [classGraph_adj, H, hlab, mul_add_inj (hlt' u) (hlt' v), and_assoc]
      rw [this]
      exact harb'
    · rw [hlab, pow_succ]
      have := hlt v
      have := hlt' v
      calc P.lab a i G v * P.p + c v < P.lab a i G v * P.p + P.p := by omega
        _ = (P.lab a i G v + 1) * P.p := by ring
        _ ≤ P.p ^ i * P.p := Nat.mul_le_mul_right _ (by omega)

/-- **Theorem 4.3, correctness part.** For a graph of arboricity `≤ a`, Procedure Legal-Coloring
with `I` iterations computes a legal colouring with colours `< p^I · (⌊(2+ε)α_I⌋ + 1)`, where
`⌊(2+ε)α_I⌋ = A α_I` (the palettes of line 19). -/
theorem proc_correct (hP : P.HRoundsOK) (hp : 0 < P.p) {G : SimpleGraph V} {a : ℕ}
    (hG : G.ArboricityLE a) (I : ℕ) :
    IsLegal G (P.proc a I G) ∧ ∀ v, P.proc a I G v < P.p ^ I * (P.A (P.bound a I) + 1) := by
  obtain ⟨harb, hlt⟩ := P.lab_spec hP hp hG I
  set H := classGraph G (P.lab a I G)
  obtain ⟨hleg, hle⟩ := legalColoring_spec harb.hasOutDegLE (hP _) (P.B (P.bound a I))
  set ψ := legalCol (P.A (P.bound a I)) (P.L (P.bound a I)) (P.KB (P.bound a I))
    (P.B (P.bound a I)).col H
  have hproc : ∀ v, P.proc a I G v = P.lab a I G v * (P.A (P.bound a I) + 1) + ψ v :=
    fun v => rfl
  refine ⟨fun u v huv heq => ?_, fun v => ?_⟩
  · rw [hproc, hproc, mul_add_inj (Nat.lt_succ_of_le (hle u)) (Nat.lt_succ_of_le (hle v))] at heq
    exact hleg ⟨huv, heq.1⟩ heq.2
  · rw [hproc]
    have := hlt v
    have := hle v
    calc P.lab a I G v * (P.A (P.bound a I) + 1) + ψ v
        < P.lab a I G v * (P.A (P.bound a I) + 1) + (P.A (P.bound a I) + 1) := by omega
      _ = (P.lab a I G v + 1) * (P.A (P.bound a I) + 1) := by ring
      _ ≤ P.p ^ I * (P.A (P.bound a I) + 1) := Nat.mul_le_mul_right _ (by omega)

end LCParams

end Podc.ArbdefectiveColoring
