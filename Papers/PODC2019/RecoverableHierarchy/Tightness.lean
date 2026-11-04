import Papers.PODC2019.RecoverableHierarchy.Fig2Prog
import Papers.PODC2019.RecoverableHierarchy.Fig2Generic

/-!
# Exact tightness for generic constructions (Theorem 6 + Theorem 16)

For generic constructions of recoverable consensus from atomic consensus objects and registers
tolerating at most `f` independent failures, the number of consensus objects needed is exactly
`f + 1`:

* Figure 2 (`Fig2.A n f`) uses `f + 1` consensus objects, is generic (`Fig2.fig2_generic`) and
  solves `n`-process recoverable consensus with at most `f` failures (`Fig2.theorem16`);
* no generic algorithm with at most `f` consensus objects does, even when only two processes
  participate (`theorem6`).

The paper states the two bounds separately (Θ(f)); combined they are tight up to the constant.
-/

namespace Podc.RecoverableHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

/-- Genericity on all executions implies genericity on any set of executions. -/
lemma Generic.mono {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}
    {isC : ι → Prop} {Adm Adm' : List (Ev n) → Prop} (h : Generic A isC Adm)
    (hAdm : ∀ γ, Adm' γ → Adm γ) : Generic A isC Adm' :=
  fun x α β γ p i hi hadm hp => h x α β γ p i hi (hAdm _ hadm) hp

/-- **Exact tightness.** For `n ≥ 2` and every `f`: there is a generic algorithm with `f + 1`
atomic consensus objects (and registers) solving `n`-process recoverable consensus (CSLib's strong
specification) in all executions with at most `f` failures, and no generic algorithm with `f`
or fewer consensus objects (and read/write-like objects) satisfies even the paper's weaker
specification on the executions with at most `f` failures and two participants. -/
theorem generic_consensus_objects_tight {n : ℕ} (hn : 2 ≤ n) (f : ℕ) :
    (Generic (Fig2.A n f) (fun i => ∃ k, i = Sum.inr k) (fun _ => True) ∧
      Solves (Fig2.A n f) (AtMost f)) ∧
    ∀ {ιR ιS V : Type} [DecidableEq ιR] [DecidableEq ιS] [Fintype ιS] {R : ιR → ObjSpec},
      (∀ j, (R j).RWLike) → Fintype.card ιS ≤ f →
      ∀ A : Alg n (withRW (ιS := ιS) R (consObj V)),
        Generic A (fun i => ∃ j, i = Sum.inr j) (AtMostTwo f) → ¬ SolvesP A (AtMostTwo f) :=
  ⟨⟨Fig2.fig2_generic, Fig2.theorem16 n f⟩,
    fun hR hf A hgen => theorem6 hR hn f hf A hgen⟩

/-- Sanity check of Theorem 6 against Figure 2: Figure 2 with `f + 1` objects is consistent with
Theorem 6 (it satisfies the hypotheses of Theorem 6 except the object count). -/
example {n : ℕ} (f : ℕ) : SolvesP (Fig2.A n f) (AtMostTwo f) :=
  let h := Fig2.theorem16P n f
  ⟨fun x γ hγ => h.agree x γ hγ.1, fun x γ hγ => h.valid x γ hγ.1,
    fun x e p N hadm => h.prog x e p N (fun t => (hadm t).1)⟩

end Podc.RecoverableHierarchy
