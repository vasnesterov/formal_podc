import Papers.PODC2021.FastByzantineConsensus.ImplSafety
import Papers.PODC2021.FastByzantineConsensus.ImplLivenessAux

/-!
# The concrete protocol: termination

After GST, the first view `v` (of length `L ≥ 6δ + 12`) that starts after GST and has a correct
leader completes: votes → leader's `CertAck` → verifiers' `CertAck`s → proposal → acks → commit
certificate → `Commit`s → slow-path decision at every correct process (gossip delivers every token
known to a correct process at time `τ ≥ gst` to every correct process by `τ + δ + 1`).
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus.Impl

open Cslib.Byzantine.PartialSync FastByzantineConsensus.Protocol Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {pr : Params P} {L δ : ℕ}

/-- **Termination**, for views of length `L ≥ 6δ + 12` and a leader map in which every process
leads infinitely many views. -/
theorem algo_termination (hL : 6 * δ + 12 ≤ L)
    (hlead : ∀ v₀ q, ∃ v ≥ v₀, pr.leader v = q) (ht : 1 ≤ pr.t) (htf : pr.t ≤ pr.f)
    (hn : 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P) (R : Run P (Tok P V) V)
    (hR : R.Valid pr.f δ) (hRa : R.AuthValid auth (algo pr L)) :
    ∀ p ∉ R.faulty, ∃ v, R.Decides (algo pr L) p v :=
  termination_of hL hlead ht hn hR hRa
    (fun τ => Inv.of_reachable (reachable_absState (by omega) R hRa τ))

end FastByzantineConsensus.Impl
