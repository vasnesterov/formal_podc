import Papers.PODC2021.TrustedHardwareUnidirectional.EchoProof
import Papers.PODC2021.TrustedHardwareUnidirectional.SRBFair

/-!
# The Claim of Section 4.1 is false

"Sequenced reliable broadcast cannot implement unidirectionality in a system with `n > 2f` and
`f > 1`, under asynchrony and in the absence of additional assumptions."

`Claim_4_1` states it in the SRB model of `SRB.lean`: no protocol, whatever its message and state
types, implements unidirectional rounds over SRB when `n > 2f` and `f > 1`. The echo protocol
(`Echo.echoProtocol`) implements them for every `n > 2f`, so the claim fails, e.g. for `n = 5`,
`f = 2` (`claim_4_1_false`).
-/

namespace Podc.TrustedHW

/-- **Claim of Section 4.1** of Ben-David–Nayak, as stated in the paper. -/
def Claim_4_1 : Prop :=
  ∀ (P V M S : Type) [Fintype P] [DecidableEq P] (f : ℕ), 2 * f < Fintype.card P → 1 < f →
    ∀ A : SRBProtocol P V M S, ¬ A.Implements f

/-- SRB implements unidirectional rounds whenever `n > 2f`. -/
theorem srb_implements_unidirectional (P V : Type) [Fintype P] [DecidableEq P] {f : ℕ}
    (hf : 2 * f < Fintype.card P) :
    ∃ (M S : Type) (A : SRBProtocol P V M S), A.Implements f :=
  ⟨_, _, Echo.echoProtocol P V f, Echo.echoProtocol_implements hf⟩

/-- **The Claim of Section 4.1 is false**: with `n = 5`, `f = 2` the echo protocol implements
unidirectional rounds over SRB. -/
theorem claim_4_1_false : ¬ Claim_4_1 := fun h =>
  h (Fin 5) Bool _ _ 2 (by simp) (by norm_num) (Echo.echoProtocol (Fin 5) Bool 2)
    (Echo.echoProtocol_implements (by simp))

/-- Non-vacuity: for the echo protocol with `n = 5`, `f = 2`, two Byzantine processes and any
clients, a fair execution exists, and in it every correct process completes every round. -/
theorem echo_fair_exec_exists (cl : Fin 5 → Client (Fin 5) Bool) :
    let A := Echo.echoProtocol (Fin 5) Bool 2
    let F : Finset (Fin 5) := {3, 4}
    (A.system F cl).IsExec (A.rrExec F cl) ∧ SRBProtocol.Fair F (A.rrExec F cl) ∧
      ∀ p, p ∉ F → ∀ r, ∃ t, r < ((A.system F cl).rounds (A.rrExec F cl t) p).length := by
  intro A F
  refine ⟨A.rrExec_isExec F cl, A.rrExec_fair F cl, fun p hp r => ?_⟩
  exact (Echo.echoProtocol_implements (by simp) F (by decide) cl).live _ (A.rrExec_isExec F cl)
    (A.rrExec_fair F cl) p hp r

end Podc.TrustedHW
