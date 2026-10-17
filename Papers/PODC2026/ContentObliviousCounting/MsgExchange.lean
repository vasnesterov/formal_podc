import Papers.PODC2026.ContentObliviousCounting.SimulationGeneric
import Papers.PODC2026.ContentObliviousCounting.MinFindingGeneric
import Papers.PODC2026.ContentObliviousCounting.ComputeOR
import Papers.PODC2026.ContentObliviousCounting.BitSending

/-!
# Theorems 22, 14 and 5 for the concrete Algorithms 7–9

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260).

The generic results (`MsgExchangeGeneric.lean`, `SimulationGeneric.lean`, `MinFindingGeneric.lean`)
assume round procedures satisfying Theorems 17 and 21. Here they are instantiated with the
formalized `ComputeOR` (Algorithm 9), `CCWBitSending/CCWBitRelay` (Algorithms 7–8) and their
mirror images `CWBitSending/CWBitRelay`.

Setting: oriented ring `ZMod n` (any `n ≥ 1`), exactly one leader `ℓ`, and — for the message
exchange and the simulation — the leader is active (as in Theorem 14). `vnext act v` /
`vprev act v` is the next active process clockwise / counter-clockwise.
-/

namespace Podc.ContentOblivious.Concrete

open Cslib.ContentOblivious MsgExchange Finset

variable {n : ℕ} [NeZero n] {lead act : ZMod n → Bool} {ℓ : ZMod n}

/-- Theorems 17 and 21 give the hypotheses of the generic message exchange. -/
theorem roundSpec (hℓ : ∀ v, lead v = true ↔ v = ℓ) (hlact : act ℓ = true) :
    RoundSpec ComputeOR.proc BitSending.cwProc BitSending.proc lead act
      (vnext act) (vprev act) where
  or_init a := by rcases a with ⟨_ | _, _ | _⟩ <;> rfl
  cw_init a := by rcases a with ⟨_ | _, _ | _, _ | _ | _⟩ <;> rfl
  ccw_init a := by rcases a with ⟨_ | _, _ | _, _ | _ | _⟩ <;> rfl
  or_comp b := ComputeOR.composable (x := fun v => (lead v, b v)) hℓ
  or_ret b := ComputeOR.returns (x := fun v => (lead v, b v)) hℓ
  or_bound b _ hc := ComputeOR.totalSent_le (x := fun v => (lead v, b v)) hℓ hc
  cw_comp bit := BitSending.cw_composable (x := fun v => (lead v, act v, bit v)) hℓ ⟨ℓ, hlact⟩
    hlact
  cw_ret bit := BitSending.cw_returns (x := fun v => (lead v, act v, bit v)) hℓ ⟨ℓ, hlact⟩
  cw_bound bit _ hc := BitSending.cw_totalSent_le (x := fun v => (lead v, act v, bit v)) hℓ
    ⟨ℓ, hlact⟩ hc
  ccw_comp bit := BitSending.composable (x := fun v => (lead v, act v, bit v)) hℓ ⟨ℓ, hlact⟩
    hlact
  ccw_ret bit := BitSending.returns (x := fun v => (lead v, act v, bit v)) hℓ ⟨ℓ, hlact⟩
  ccw_bound bit _ hc := BitSending.totalSent_le (x := fun v => (lead v, act v, bit v)) hℓ
    ⟨ℓ, hlact⟩ hc

/-- The message-exchange program (Algorithms 5–6) built from Algorithms 7–9. -/
abbrev msgExchange : Proc Input St := prog ComputeOR.proc BitSending.cwProc BitSending.proc

/-- **Theorem 22.** On an oriented ring with a unique leader that is active, Algorithms 5 (active
processes) and 6 (relays) are quiescently terminating; every active process receives exactly the
message sent to it by its clockwise neighbour (`rcvdcw`) and by its counter-clockwise neighbour
(`rcvdccw`) on the virtual ring of the active processes; at most `15·n·L + 3·n` pulses are sent
(`L`: longest message); and the exchange is composable. -/
theorem theorem_22 (hℓ : ∀ v, lead v = true ↔ v = ℓ) (hlact : act ℓ = true)
    (mcw mccw : ZMod n → List Bool) :
    (∀ c, msgExchange.Reach (oriented n) (inputs lead act mcw mccw) c →
      msgExchange.Final (oriented n) c →
      msgExchange.Quiescent (oriented n) c ∧ ∀ v, (c.st v).2 = none ∧
        (act v = true → (c.st v).1.rcw.filterMap id = mccw (vnext act v) ∧
          (c.st v).1.rccw.filterMap id = mcw (vprev act v))) ∧
    (∀ c, msgExchange.Reach (oriented n) (inputs lead act mcw mccw) c →
      totalSent c ≤ 15 * n * maxLen act mcw mccw + 3 * n) ∧
    msgExchange.Composable (oriented n) (inputs lead act mcw mccw) :=
  theorem_22_of_rounds (roundSpec hℓ hlact) (act_vnext hlact) (act_vprev hlact)

/-- **Theorem 14.** On an oriented ring with a unique, active leader, the content-oblivious
simulation of `T` rounds of a synchronous algorithm `A` on the virtual ring of the active
processes is correct (every active process ends in the state of the synchronous execution),
quiescently terminating and composable, and round `k` costs at most `15·n·b_k + 3·n` pulses,
`b_k` = the longest message of round `k` (i.e. `O(b_k)` pulses per process). -/
theorem theorem_14 {S : Type} [Encodable S] [Inhabited S] (A : Simulation.SyncAlg S)
    (hℓ : ∀ v, lead v = true ↔ v = ℓ) (hlact : act ℓ = true) (s0 : ZMod n → S) (T : ℕ) :
    (∀ c, (Simulation.simProg ComputeOR.proc BitSending.cwProc BitSending.proc A).Reach
        (oriented n) (fun v => (lead v, act v, s0 v, T)) c →
      (Simulation.simProg ComputeOR.proc BitSending.cwProc BitSending.proc A).Final
        (oriented n) c →
      (Simulation.simProg ComputeOR.proc BitSending.cwProc BitSending.proc A).Quiescent
        (oriented n) c ∧ ∀ v, act v = true →
        (c.st v).1.s = A.run (vnext act) (vprev act) s0 T v) ∧
    (∀ c, (Simulation.simProg ComputeOR.proc BitSending.cwProc BitSending.proc A).Reach
        (oriented n) (fun v => (lead v, act v, s0 v, T)) c →
      totalSent c ≤ ∑ k ∈ range T,
        (15 * n * Simulation.lenAt A act (vnext act) (vprev act) s0 k
          + 3 * n)) ∧
    (Simulation.simProg ComputeOR.proc BitSending.cwProc BitSending.proc A).Composable
      (oriented n) (fun v => (lead v, act v, s0 v, T)) :=
  Simulation.theorem_14_of_rounds (roundSpec hℓ hlact) (act_vnext hlact) (act_vprev hlact)

/-- ComputeOR satisfies the hypotheses of the generic minimum finding. -/
theorem orSpec (hℓ : ∀ v, lead v = true ↔ v = ℓ) : MinFinding.ORSpec ComputeOR.proc lead where
  init a := by rcases a with ⟨_ | _, _ | _⟩ <;> rfl
  comp b := ComputeOR.composable (x := fun v => (lead v, b v)) hℓ
  ret b := ComputeOR.returns (x := fun v => (lead v, b v)) hℓ
  bound b _ hc := ComputeOR.totalSent_le (x := fun v => (lead v, b v)) hℓ hc

/-- **Theorem 5.** In an anonymous oriented ring with a unique leader where every process `v`
holds `x v ∈ ℕ`, Algorithm 10 (with the loop bound fixed, see `MinFindingGeneric.lean`) run by the
participants `a0` (at least one; all processes when computing the global minimum) on the binary
representations is quiescently terminating, every process outputs `xmin = min {x v | a0 v}`,
exactly the participants holding `xmin` stay active, and at most `6·n·|xmin|` pulses are sent,
`|xmin| = ⌊log₂ xmin⌋ + 1`. -/
theorem theorem_5 (hℓ : ∀ v, lead v = true ↔ v = ℓ) (a0 : ZMod n → Bool)
    (hex : ∃ v, a0 v = true) (x : ZMod n → ℕ) :
    ∃ xmin, (∃ w, a0 w = true ∧ x w = xmin) ∧ (∀ v, a0 v = true → xmin ≤ x v) ∧
    (∀ c, (MinFinding.prog ComputeOR.proc).Reach (oriented n)
        (fun v => (lead v, a0 v, MinFinding.enc (x v))) c →
      (MinFinding.prog ComputeOR.proc).Final (oriented n) c →
      (MinFinding.prog ComputeOR.proc).Quiescent (oriented n) c ∧ ∀ v,
        (c.st v).2 = none ∧ MinFinding.val (c.st v).1.minBits = xmin ∧
        ((c.st v).1.active = true ↔ a0 v = true ∧ x v = xmin)) ∧
    (∀ c, (MinFinding.prog ComputeOR.proc).Reach (oriented n)
        (fun v => (lead v, a0 v, MinFinding.enc (x v))) c →
      totalSent c ≤ 6 * n * (Nat.log 2 xmin + 1)) :=
  MinFinding.theorem_5 (a0 := a0) (hex := hex) (orSpec hℓ) x

end Podc.ContentOblivious.Concrete
