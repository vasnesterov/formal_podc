import Papers.PODC2018.InteractiveDistributedProofs.Model

/-!
# Setting of the lower bound (Section 3.4): dumbbell graphs, simple protocols, `𝓜_A`, `μ_A`

* `𝓕` is a family of graphs on `Fin k` (the paper's `{1, …, n}`); the paper requires all of them to be
  asymmetric and pairwise non-isomorphic (`FamilyOK`).
* `dumbbell FA FB vA` is the paper's `G(F_A, F_B)`: copies of `F_A` on `V_A = {a i}` and of `F_B` on
  `V_B = {b i}`, bridge nodes `x_A, x_B`, and the path `v_A – x_A – x_B – v_B` with `v_A = a vA`,
  `v_B = b vA` (corresponding vertices, as needed for `G(F, F)` to be symmetric).
* `IsSimple` is Definition 6: the bridge nodes accept iff a predicate of their view of the challenges
  and of their own response holds and both bridge nodes got the same response.
* `MA` is `𝓜_A(F, r)`: the responses `m` to `x_A` that extend to a response making all of
  `V_A ∪ {x_A}` accept on `G(F, F)`; `μA F` is its law under uniform challenges, and `l1` the
  `ℓ₁` distance of two such laws.
-/

open Finset Cslib.Probability

namespace Podc.InteractiveDistributedProofs.LowerBound

/-- Vertices of a dumbbell graph built from two graphs on `Fin k`. -/
inductive DVert (k : ℕ)
  | a (i : Fin k)
  | b (i : Fin k)
  | xA
  | xB
  deriving DecidableEq, Fintype

open DVert

/-- Adjacency of the dumbbell graph `G(F_A, F_B)` (bridge attached at `v_A = a vA`, `v_B = b vA`). -/
def dAdj {k : ℕ} (FA FB : SimpleGraph (Fin k)) (vA : Fin k) : DVert k → DVert k → Prop
  | a i, a j => FA.Adj i j
  | b i, b j => FB.Adj i j
  | a i, xA => i = vA
  | xA, a i => i = vA
  | xA, xB => True
  | xB, xA => True
  | b i, xB => i = vA
  | xB, b i => i = vA
  | _, _ => False

/-- The dumbbell graph `G(F_A, F_B)`. -/
def dumbbell {k : ℕ} (FA FB : SimpleGraph (Fin k)) (vA : Fin k) : SimpleGraph (DVert k) where
  Adj := dAdj FA FB vA
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp_all [dAdj, SimpleGraph.adj_comm]⟩
  loopless := by
    constructor
    intro x h
    cases x <;> simp_all [dAdj]

instance {k : ℕ} (FA FB : SimpleGraph (Fin k)) [DecidableRel FA.Adj] [DecidableRel FB.Adj]
    (vA : Fin k) : DecidableRel (dumbbell FA FB vA).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [dumbbell, dAdj] <;> infer_instance

/-- The paper's requirements on `𝓕`: all graphs asymmetric, no two distinct ones isomorphic. -/
def FamilyOK {k : ℕ} (𝓕 : Finset (SimpleGraph (Fin k))) : Prop :=
  (∀ F ∈ 𝓕, ¬ Sym F) ∧ ∀ F ∈ 𝓕, ∀ F' ∈ 𝓕, F ≠ F' → IsEmpty (F ≃g F')

/-- The class `𝒢` of dumbbells built from `𝓕`. -/
def InClass {k : ℕ} (𝓕 : Finset (SimpleGraph (Fin k))) (vA : Fin k)
    (G : SimpleGraph (DVert k)) : Prop :=
  ∃ FA ∈ 𝓕, ∃ FB ∈ 𝓕, G = dumbbell FA FB vA

variable {k : ℕ} {R M : Type*}

/-- **Definition 6** (simple protocols): on every graph of the class, every challenge vector and every
response vector, `x_A` accepts iff `f_A(R_{N(x_A)}, M_{x_A})` and `M_{x_A} = M_{x_B}`; similarly for
`x_B`. (The challenges a bridge node sees are given as its local view.) -/
def IsSimple (pr : AMProtocol (DVert k) R M) (𝓕 : Finset (SimpleGraph (Fin k))) (vA : Fin k)
    (fA fB : (DVert k → Option R) → M → Prop) : Prop :=
  ∀ G, InClass 𝓕 vA G → ∀ (c : DVert k → R) (Mr : DVert k → M),
    (pr.out xA (mask G xA fun u => (c u, Mr u)) ↔ fA (mask G xA c) (Mr xA) ∧ Mr xA = Mr xB) ∧
    (pr.out xB (mask G xB fun u => (c u, Mr u)) ↔ fB (mask G xB c) (Mr xB) ∧ Mr xB = Mr xA)

/-- `𝓜_A(F, r)`: responses `m` to `x_A` extendable to a response `M` with `M x_A = m` such that every
node of `V_A` accepts on `G(F, F)` and `f_A(r, m)` holds. -/
def MA (pr : AMProtocol (DVert k) R M) (vA : Fin k) (fA : (DVert k → Option R) → M → Prop)
    (F : SimpleGraph (Fin k)) (c : DVert k → R) : Set M :=
  {m | ∃ Mr : DVert k → M, Mr xA = m ∧
    (∀ i, pr.out (a i) (mask (dumbbell F F vA) (a i) fun u => (c u, Mr u))) ∧
    fA (mask (dumbbell F F vA) xA c) m}

/-- `𝓜_B(F, r)`, symmetrically. -/
def MB (pr : AMProtocol (DVert k) R M) (vA : Fin k) (fB : (DVert k → Option R) → M → Prop)
    (F : SimpleGraph (Fin k)) (c : DVert k → R) : Set M :=
  {m | ∃ Mr : DVert k → M, Mr xB = m ∧
    (∀ i, pr.out (b i) (mask (dumbbell F F vA) (b i) fun u => (c u, Mr u))) ∧
    fB (mask (dumbbell F F vA) xB c) m}

variable [Fintype R]

/-- `μ_A(F)`: the law of the random set `𝓜_A(F, r)` for uniform challenges `r`. -/
noncomputable def μA (pr : AMProtocol (DVert k) R M) (vA : Fin k)
    (fA : (DVert k → Option R) → M → Prop) (F : SimpleGraph (Fin k)) (S : Set M) : ℝ :=
  uprob fun c : DVert k → R => MA pr vA fA F c = S

/-- `ℓ₁` distance of two laws on `Set M`. -/
noncomputable def l1 [Fintype M] (μ η : Set M → ℝ) : ℝ := by
  classical
  exact ∑ S : Set M, |μ S - η S|

/-- The claim of **Lemma 3.11** for a protocol `pr` (with bridge predicates `fA`, `fB`) and a family
`𝓕`: distinct graphs of `𝓕` have `ℓ₁`-far laws `μ_A`. -/
def Lemma311Claim [Fintype M] (pr : AMProtocol (DVert k) R M) (𝓕 : Finset (SimpleGraph (Fin k)))
    (vA : Fin k) (fA : (DVert k → Option R) → M → Prop) : Prop :=
  ∀ F₁ ∈ 𝓕, ∀ F₂ ∈ 𝓕, F₁ ≠ F₂ → 2 / 3 ≤ l1 (μA pr vA fA F₁) (μA pr vA fA F₂)

end Podc.InteractiveDistributedProofs.LowerBound
