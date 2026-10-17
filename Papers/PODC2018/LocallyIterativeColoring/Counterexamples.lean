import Papers.PODC2018.LocallyIterativeColoring.AG

/-!
# Counterexamples to two claims of [BEG18]

## 1. The `2p + 1`-round claim of Section 1.2

Section 1.2 of [BEG18] (arXiv v2) says: start from a proper `(Δ+1)²`-colouring with `Δ + 1 = p`
prime, run AG over `GF(p)`; "when all vertices run this simple iterative step for
`2p + 1 = 2(Δ + 1) + 1` rounds, the ultimate coloring `ψ` is a proper `(Δ + 1)`-coloring".
Section 3 itself (correctly) assumes `q > 2Δ`.

`intro_claim_false`: a tree on 16 vertices with maximum degree `Δ = 4`, `p = 5`, and a proper
colouring with values in `GF(5)²`; after `2p + 1 = 11` rounds vertex `0` is still working (colour
`⟨1, 1⟩`) and six distinct colours are in use (`> Δ + 1 = 5`). (It finalizes after 13 rounds;
`ag_final_of_lt` gives the correct general bound `(Δ + 1) p` rounds.)

## 2. The 3-dimensional AG algorithm of Section 7 does not terminate

Algorithm 7 (3AG(p)) of [BEG18] on colours `⟨c, b, a⟩ ∈ Z_p³`: a vertex with `c ≠ 0` finalizes
`c` (to `⟨0, b, a⟩`) iff no neighbour has the same `b`; otherwise it moves to `⟨c, b + c, a⟩`.
Two adjacent vertices with colours `⟨1, 0, 0⟩` and `⟨1, 0, 1⟩` (a proper colouring) keep equal
second coordinates forever, so `c` never becomes `0`: `threeAG_never_finalizes`. This refutes the
termination claim ("Within the first `3Δ + 1` rounds, each vertex will have `c_v = 0`") and
Corollaries 7.2, 7.3 for every `p ≥ 2` (in particular for `p ≥ 3Δ + 1 = 4` and `p ≥ 2Δ + 2`). The
flaw: unlike in the 2-dimensional case, a proper colouring may contain adjacent vertices with the
same `⟨c, b⟩` (differing only in `a`), and these conflict in every round.
-/

namespace BEG18

open Cslib.LocallyIterative

/-! ### 1. The `2p + 1` claim -/

namespace IntroCounterexample

/-- The edges of the tree. -/
def edges : List (Fin 16 × Fin 16) :=
  [(0, 1), (0, 2), (2, 3), (2, 4), (4, 5), (0, 6), (6, 7), (6, 8), (8, 9), (8, 10), (6, 11),
    (11, 12), (11, 13), (0, 14), (14, 15)]

/-- A tree on 16 vertices with maximum degree 4. -/
def T : SimpleGraph (Fin 16) where
  Adj u v := (u, v) ∈ edges ∨ (v, u) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel T.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem degree_le : ∀ v, T.degree v ≤ 4 := by decide

/-- The initial colouring `⟨a, b⟩ ∈ GF(5)²`. -/
def c₀ : Fin 16 → ZMod 5 × ZMod 5 :=
  ![(1, 0), (0, 0), (2, 1), (4, 1), (4, 4), (0, 4), (2, 3), (0, 0), (1, 3), (0, 0), (0, 4), (4, 2),
    (0, 1), (3, 2), (2, 4), (0, 4)]

theorem c₀_isProper : IsProper T c₀ := by
  unfold IsProper; decide

/-- A computable copy of one AG round on `T`. -/
def simStep (c : Fin 16 → ZMod 5 × ZMod 5) : Fin 16 → ZMod 5 × ZMod 5 := fun v =>
  if ∃ u, T.Adj v u ∧ (c u).2 = (c v).2 then ((c v).1, (c v).2 + (c v).1) else (0, (c v).2)

theorem run_eq (t : ℕ) : (ag : Algorithm (ZMod 5 × ZMod 5)).run T c₀ t = simStep^[t] c₀ := by
  rw [ag, Algorithm.run_ofStep]
  congr 1
  funext c v
  rw [agStep_nbrColors]
  unfold simStep Conflict
  congr

theorem round_11 : simStep^[11] c₀ 0 = (1, 1) := by decide +kernel

theorem six_colours : (Finset.univ.image (simStep^[11] c₀)).card = 6 := by decide +kernel

/-- **The claim of Section 1.2 of [BEG18] is false**: maximum degree `Δ = 4`, `p = Δ + 1 = 5`,
a proper colouring with values in `GF(p)²` (a `(Δ+1)²`-colouring); after `2p + 1 = 11` rounds of
AG a vertex is not final and the colouring uses `6 > Δ + 1` colours. -/
theorem intro_claim_false :
    (∀ v, T.degree v ≤ 4) ∧ IsProper T c₀ ∧
      ((ag : Algorithm (ZMod 5 × ZMod 5)).run T c₀ (2 * 5 + 1) 0).1 ≠ 0 ∧
      (Finset.univ.image ((ag : Algorithm (ZMod 5 × ZMod 5)).run T c₀ (2 * 5 + 1))).card = 6 := by
  refine ⟨degree_le, c₀_isProper, ?_, ?_⟩
  · rw [run_eq, round_11]; decide
  · rw [run_eq]; exact six_colours

end IntroCounterexample

/-! ### 2. Non-termination of 3AG (Section 7) -/

section ThreeAG

variable {R : Type*} [AddCommGroup R]

open Classical in
/-- One step of Algorithm 7 (3AG(p)) of [BEG18] on colours `⟨c, b, a⟩`. -/
noncomputable def threeAGStep (x : R × R × R) (N : Set (R × R × R)) : R × R × R :=
  if x.1 ≠ 0 then
    (if ∀ y ∈ N, y.2.1 ≠ x.2.1 then (0, x.2.1, x.2.2) else (x.1, x.2.1 + x.1, x.2.2))
  else
    (if ∀ y ∈ N, y.2.2 ≠ x.2.2 then (0, 0, x.2.2) else (0, x.2.1, x.2.2 + x.2.1))

/-- Algorithm 7 (3AG(p)) of [BEG18]. -/
noncomputable def threeAG : Algorithm (R × R × R) := Algorithm.ofStep threeAGStep

/-- The initial colouring of `K₂`: `⟨1, 0, 0⟩` and `⟨1, 0, 1⟩`. -/
def k2Colouring (R : Type*) [AddCommGroup R] [One R] : Fin 2 → R × R × R := ![(1, 0, 0), (1, 0, 1)]

variable {p : ℕ} [Fact (1 < p)]

theorem k2Colouring_isProper : IsProper (⊤ : SimpleGraph (Fin 2)) (k2Colouring (ZMod p)) := by
  intro u v huv h
  have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
  fin_cases u <;> fin_cases v <;> simp_all [k2Colouring]

/-- **Algorithm 7 (3AG) of [BEG18] never terminates on `K₂`**: from the proper colouring
`⟨1,0,0⟩, ⟨1,0,1⟩` (over `Z_p`, any `p ≥ 2`), in every round both vertices have first coordinate
`c = 1 ≠ 0`; so 3AG never reaches a `p`-colouring, contrary to Corollaries 7.2 and 7.3. -/
theorem threeAG_never_finalizes (t : ℕ) :
    (threeAG : Algorithm (ZMod p × ZMod p × ZMod p)).run ⊤ (k2Colouring (ZMod p)) t =
      ![(1, (t : ZMod p), 0), (1, (t : ZMod p), 1)] := by
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  induction t with
  | zero => funext v; fin_cases v <;> simp [k2Colouring]
  | succ t ih =>
    funext v
    rw [Algorithm.run_succ_apply, ih]
    have hN : ∀ w : Fin 2, ∃ y ∈ nbrColors ⊤ (![(1, (t : ZMod p), 0), (1, (t : ZMod p), 1)] :
        Fin 2 → ZMod p × ZMod p × ZMod p) w, y.2.1 = (t : ZMod p) := by
      intro w
      refine ⟨_, mem_nbrColors_of_adj _ (show (⊤ : SimpleGraph (Fin 2)).Adj w (1 - w) from ?_), ?_⟩
      · fin_cases w <;> decide
      · fin_cases w <;> rfl
    obtain ⟨y, hy, hy2⟩ := hN v
    show threeAGStep _ _ = _
    unfold threeAGStep
    have h1 : ((![(1, (t : ZMod p), 0), (1, (t : ZMod p), 1)] :
        Fin 2 → ZMod p × ZMod p × ZMod p) v).1 ≠ 0 := by fin_cases v <;> exact h10
    have h2 : ((![(1, (t : ZMod p), 0), (1, (t : ZMod p), 1)] :
        Fin 2 → ZMod p × ZMod p × ZMod p) v).2.1 = t := by fin_cases v <;> rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1),
      ite_eq_right_of_eq_false _ _ (eq_false fun h => h y hy (hy2.trans h2.symm)), h2]
    fin_cases v <;> simp [Nat.cast_succ]

end ThreeAG

end BEG18
