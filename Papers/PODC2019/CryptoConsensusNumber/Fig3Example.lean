import Papers.PODC2019.CryptoConsensusNumber.Fig3WF

/-!
# Figure 3: non-vacuity

A concrete instance: two processes owning one shared account (`k = 2`), initial balance `5`.
The hypothesis `KShared μ k` holds, and transfers by owners as well as reads are allowed, so
the two theorems apply to executions in which both processes concurrently transfer from the
shared account.
-/

namespace CryptoCons.Fig3

/-- Both processes own the single account. -/
def μ₂ : Unit → Finset (Fin 2) := fun _ => Finset.univ

lemma kShared_μ₂ : KShared μ₂ 2 := by intro a; simp [μ₂]

example : (impl μ₂ (fun _ => 5) 2).Linearizable := fig3_linearizable kShared_μ₂

example : (impl μ₂ (fun _ => 5) 2).WaitFree := fig3_waitFree kShared_μ₂

/-- Both owners may invoke transfers from the shared account (under their own identity). -/
example (q : Fin 2) : (impl μ₂ (fun _ => 5) 2).allowed q (ATOp.transfer q () () 3) := rfl

example (q : Fin 2) : (impl μ₂ (fun _ => 5) 2).allowed q (ATOp.read ()) := trivial

example (q : Fin 2) : q ∈ μ₂ () := by simp [μ₂]

end CryptoCons.Fig3
