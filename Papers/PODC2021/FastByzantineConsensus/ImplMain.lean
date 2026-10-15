import Papers.PODC2021.FastByzantineConsensus.ImplLiveness
import Papers.PODC2021.FastByzantineConsensus.ImplTwoStep
import Papers.PODC2021.FastByzantineConsensus.LowerBound
import Cslib.Computability.Distributed.Byzantine.PartialSync.BinaryConsensus

/-!
# Tightness: `3f + 2t − 1` processes are necessary and sufficient

* `algo_fastConsensus`: the protocol is an `f`-resilient `t`-two-step consensus protocol for
  `n ≥ 3f + 2t − 1`, `1 ≤ t ≤ f`, `δ ≥ 2`.
* `tight_bound`: for `1 ≤ t ≤ f` and `δ ≥ 2`, an `f`-resilient `t`-two-step consensus protocol (with
  signatures) exists for `n` processes iff `n ≥ 3f + 2t − 1` (for `n ≥ 2`).
-/

set_option linter.unusedSectionVars false

namespace FastByzantineConsensus.Impl

open Cslib.Byzantine.PartialSync FastByzantineConsensus.Protocol Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
variable {pr : Params P} {L δ : ℕ}

/-- **The protocol is an `f`-resilient `t`-two-step consensus protocol** for
`n ≥ 3f + 2t − 1`, `1 ≤ t ≤ f`, `δ ≥ 2` (views of length `L ≥ 6δ + 12`, every process leads
infinitely many views). -/
theorem algo_fastConsensus (hδ : 2 ≤ δ) (hL : 6 * δ + 12 ≤ L)
    (hlead : ∀ v₀ q, ∃ v ≥ v₀, pr.leader v = q) (ht : 1 ≤ pr.t) (htf : pr.t ≤ pr.f)
    (hn : 3 * pr.f + 2 * pr.t - 1 ≤ Fintype.card P) :
    FastConsensus (algo (V := V) pr L) auth pr.f pr.t δ :=
  ⟨⟨fun R hR hRa => algo_termination hL hlead ht htf hn R hR hRa,
    fun R hR hRa => algo_agreement (by omega) ht htf hn R hR hRa,
    fun R _ hRa => algo_validity (by omega) (by omega) R hRa⟩,
   algo_twoStep hδ (by omega) htf hn⟩

/-- **Tight bound** (Theorems 4.5 and 3.6/A.4 together, in the authenticated partially synchronous
model): for `1 ≤ t ≤ f`, `δ ≥ 2` and at least two values, an `f`-resilient `t`-two-step consensus
protocol exists for `n ≥ 2` processes iff `n ≥ 3f + 2t − 1`. -/
theorem tight_bound {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V] {f t δ : ℕ}
    (ht : 1 ≤ t) (htf : t ≤ f) (hδ : 2 ≤ δ) (h2 : 2 ≤ Fintype.card P) {a b : V} (hab : a ≠ b) :
    (∃ (M S K : Type) (Au : Auth P M K) (A : Algorithm P M S V V),
      A.Unforging Au ∧ FastConsensus A Au f t δ) ↔ 3 * f + 2 * t - 1 ≤ Fintype.card P := by
  constructor
  · rintro ⟨M, S, K, Au, A, hU, hA⟩
    by_contra h
    exact no_fastConsensus_of_le hU (by omega) htf h2 (by omega) hab hA
  · intro hn
    let pr : Params P := ⟨f, t, Cslib.Byzantine.PartialSync.Binary.rotLeader (by omega)⟩
    exact ⟨Tok P V, LState P V, Tok P V, auth, algo pr (6 * δ + 12), algo_unforging,
      algo_fastConsensus (pr := pr) hδ le_rfl
        (fun v₀ q => Cslib.Byzantine.PartialSync.Binary.rotLeader_surj (by omega) q v₀) ht htf hn⟩

end FastByzantineConsensus.Impl
