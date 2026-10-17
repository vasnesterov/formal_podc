import Papers.PODC2026.LocalComputable.ComputableEquiv
import Mathlib.Tactic.TFAE

/-!
# Table 1: six models, three classes

Combining Theorem 5.3 (`exists_computable_of_promise`) and Theorem 5.4 (`exists_boundFree`):
for a computable locality bound `T`, a computable validity check and a finite output alphabet,

* class II: uncomputable-LOCAL without information on `n`, uncomputable-LOCAL with a bound
  `n ≤ N`, and computable-LOCAL with a bound `n ≤ N` solve the same problems with locality `T`
  (`classII_iff`);
* class III: with the promise `n ≤ N ≤ f(n)`, uncomputable and computable LOCAL coincide
  (`classIII_iff`);
* the trivial inclusions I ≤ II (`classI_le_classII`) and II ≤ III (`classII_le_classIII`).

The strictness I < II is the separation of Section 4 (not formalized; see `README.md`).
-/

namespace LocalComputable

open Computable

variable {Net View Out : Type*}

namespace Model

variable (M : Model Net View)

/-- Computable-LOCAL (with a bound): the algorithm family is a computable function of
`(N, view, radius)`. -/
def IsComputableFam (A : ℕ → Alg View Out) [Primcodable View] [Primcodable Out] : Prop :=
  Computable fun p : ℕ × View × ℕ => A p.1 p.2.1 p.2.2

/-- Computable-LOCAL (no information): the algorithm is a computable function of
`(view, radius)`. -/
def IsComputableAlg (A : Alg View Out) [Primcodable View] [Primcodable Out] : Prop :=
  Computable₂ A

/-- I ≤ II: a computable algorithm without information on `n` is a computable algorithm that
ignores the bound. -/
theorem classI_le_classII [Primcodable View] [Primcodable Out] {P : M.Problem Out}
    {T : ℕ → ℕ} {A : Alg View Out} (hc : IsComputableAlg A) (hA : M.Solves P A T) :
    ∃ B : ℕ → Alg View Out, IsComputableFam B ∧ M.SolvesWith M.UpperBound P B T :=
  ⟨fun _ => A, hc.comp (fst.comp snd) (snd.comp snd), fun _ G _ => hA G⟩

/-- II ≤ III: the promise `n ≤ N ≤ f(n)` is stronger than `n ≤ N`. -/
theorem classII_le_classIII {P : M.Problem Out} {T : ℕ → ℕ} {f : ℕ → ℕ∞}
    {A : ℕ → Alg View Out} (hA : M.SolvesWith M.UpperBound P A T) :
    M.SolvesWith (M.Sandwich f) P A T :=
  fun N G h => hA N G h.1

variable [DecidableEq View] [Primcodable Net] [Primcodable View] [Primcodable Out]

/-- **Table 1, class II.** For computable `T`, computable views and validity check, networks of
size `≤ N` computably listable, and a finite output alphabet, the following are equivalent:
(1) uncomputable-LOCAL without information on `n` solves `P` with locality `T`;
(2) uncomputable-LOCAL with an upper bound `N ≥ n` does;
(3) computable-LOCAL with an upper bound `N ≥ n` does. -/
theorem classII_iff [Finite Out]
    (hsize : Computable M.size) (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    {T : ℕ → ℕ} (hT : Computable T)
    (nets : ℕ → List Net) (hnets : Computable nets) (hnetsG : ∀ N G, G ∈ nets N ↔ M.size G ≤ N)
    {P : M.Problem Out} (check : Net → List Out → Bool) (hcheck : Computable₂ check)
    (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab) :
    [(∃ A : Alg View Out, M.Solves P A T),
      (∃ A : ℕ → Alg View Out, M.SolvesWith M.UpperBound P A T),
      (∃ A : ℕ → Alg View Out, IsComputableFam A ∧ M.SolvesWith M.UpperBound P A T)].TFAE := by
  tfae_have 1 ↔ 2 := (M.solvable_upperBound_iff P T).symm
  tfae_have 2 → 3 := fun ⟨A, hA⟩ =>
    M.exists_computable_of_promise hsize hview hT nets hnets (fun N G => (hnetsG N G).symm) check
      hcheck hP A hA
  tfae_have 3 → 2 := fun ⟨A, _, hA⟩ => ⟨A, hA⟩
  tfae_finish

/-- **Table 1, class III** (= Theorem 5.3). With the promise `n ≤ N ≤ f(n)` for a computable
`f`, uncomputable-LOCAL and computable-LOCAL solve the same problems with locality `T`. -/
theorem classIII_iff
    (hsize : Computable M.size) (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    {T : ℕ → ℕ} (hT : Computable T) {f : ℕ → ℕ∞} (hf : Computable fun n => enatToOption (f n))
    (nets : ℕ → List Net) (hnets : Computable nets) (hnetsG : ∀ N G, G ∈ nets N ↔ M.size G ≤ N)
    {P : M.Problem Out} (check : Net → List Out → Bool) (hcheck : Computable₂ check)
    (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab) :
    (∃ A : ℕ → Alg View Out, M.SolvesWith (M.Sandwich f) P A T) ↔
      ∃ A : ℕ → Alg View Out, IsComputableFam A ∧ M.SolvesWith (M.Sandwich f) P A T := by
  constructor
  · rintro ⟨A, hA⟩
    exact M.sandwich_computable hsize hview hT hf nets hnets hnetsG check hcheck hP A hA
  · rintro ⟨A, -, hA⟩
    exact ⟨A, hA⟩

end Model

end LocalComputable
