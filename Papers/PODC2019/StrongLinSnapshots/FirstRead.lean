import Papers.PODC2019.StrongLinSnapshots.ABADefs
import Cslib.Computability.Distributed.SharedMemory.Sequential

/-!
# The first `DRead` of a process: the paper's literal specification is not met

Section 3 of the paper specifies: `DRead_q()` returns `(x, a)` where "`a` is true if and only if
`q` performed an earlier `DRead_q()` operation, and a `DWrite_p` was performed by some process
`p` since `q`'s last `DRead_q()`". So the *first* `DRead` of every process must return
`a = false`.

Algorithm 2 (and Algorithm 1) do not do this: in the sequential execution
`DWrite_p(x); DRead_p()` the read finds `A[p] = ⊥ ≠ (p, s)` in its first iteration, sets
`changed`, and returns `(x, true)`. Hence Algorithm 2 is not even linearizable with respect to the
literal specification (`not_linearizable_literal`); it is correct for the specification in which
the flag reports writes since the last `DRead_q()` *or since the beginning* (`abaObj`, used for
Theorem 1). The counterexample works for every number of processes `n ≥ 1`, every value domain
and every choice of fresh sequence numbers.
-/

namespace Podc.StrongLinSnapshots

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

variable {n : ℕ} {V : Type}

/-- The paper's literal specification: the state records the value, the "write since the last
`DRead_q`" flags and the "`q` has read before" flags; `DRead_q` returns
`(x, hasRead q && dirty q)`. -/
def litδ (s : V × (Fin n → Bool) × (Fin n → Bool)) :
    ABAOp (Fin n) V → (V × (Fin n → Bool) × (Fin n → Bool)) × (V × Bool)
  | .dread q => ((s.1, Function.update s.2.1 q false, Function.update s.2.2 q true),
      (s.1, s.2.2 q && s.2.1 q))
  | .dwrite x => ((x, fun _ => true, s.2.2), (x, true))

/-- The literal specification as an object. -/
abbrev litObj (n : ℕ) (V : Type) (v₀ : V) : ObjSpec :=
  abaSpec (n := n) (V := V) (V × (Fin n → Bool) × (Fin n → Bool)) (v₀, fun _ => false, fun _ => false)
    litδ

/-- Algorithm 2 viewed as an implementation of the literal specification. -/
abbrev implLit [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) :
    Impl (litObj n V v₀) (B n V v₀) (Fin n) (Loc n V) :=
  implG v₀ pick _ _ litδ

/-- The sequential execution `DWrite_p(x) → (x, true); DRead_p() → (x, true)` (two and eight
internal steps). -/
def badHist (p : Fin n) (x : V) : List (Fin n × ABAOp (Fin n) V × (V × Bool) × ℕ) :=
  [(p, .dwrite x, (x, true), 2), (p, .dread p, (x, true), 8)]

/-- The sequential execution is an execution of Algorithm 2 (for any specification with the
same interface). -/
lemma valid_badHist [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) (p : Fin n) (x : V)
    (S : Type) (s₀ : S) (δ : S → ABAOp (Fin n) V → S × (V × Bool)) :
    (implG v₀ pick S s₀ δ).Valid (seqExec (A := abaSpec S s₀ δ) (badHist p x)) := by
  unfold Impl.Valid
  simp [seqExec, segLabels, badHist, Impl.run, Impl.runFrom, Impl.step, implG, actG,
    Impl.initCfg, allowedOp, Function.update_self, Function.update_of_ne]

/-- **The first `DRead` violates the literal specification**: Algorithm 2 is not linearizable
with respect to the specification as stated in Section 3 of the paper (for every `n ≥ 1`). -/
theorem not_linearizable_literal [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n)
    (p : Fin n) (x : V) : ¬ (implLit v₀ pick).Linearizable := by
  refine (implLit v₀ pick).not_linearizable_of_seqExec (valid_badHist v₀ pick p x _ _ _) ?_
  simp [badHist, LegalFrom, litδ]

end Podc.StrongLinSnapshots
