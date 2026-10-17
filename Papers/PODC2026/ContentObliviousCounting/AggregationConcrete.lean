import Papers.PODC2026.ContentObliviousCounting.Aggregation
import Papers.PODC2026.ContentObliviousCounting.MsgExchange

/-!
# Theorem 1 and Corollary 2 for the concrete Algorithms 7–9

The aggregation algorithm (`Aggregation.lean`) is proved for any round procedures satisfying
`RoundSpecAll` (Theorems 17 and 21 on every virtual ring containing the leader). Here this
hypothesis is discharged with the formalized ComputeOR (Algorithm 9) and bit-sending rounds
(Algorithms 7–8 and their mirrors), so Theorem 1 and Corollary 2 hold unconditionally.
-/

namespace Podc.ContentOblivious.Aggregation

open Cslib.ContentOblivious Finset

variable {n : ℕ} [NeZero n]

/-- Theorems 17 and 21 give `RoundSpecAll` for the concrete round procedures. -/
theorem roundSpecAll {lead : ZMod n → Bool} {ℓ : ZMod n} (hℓ : ∀ v, lead v = true ↔ v = ℓ) :
    RoundSpecAll ComputeOR.proc BitSending.cwProc BitSending.proc lead ℓ := by
  intro act hact
  exact Concrete.roundSpec hℓ hact

/-- **Theorem 1** (efficient aggregation), for the concrete content-oblivious algorithms: see
`theorem1` for the statement; here the round procedures are Algorithms 7–9. -/
theorem theorem1_concrete {U Y : Type} [Encodable U] [Inhabited U] (f : Multiset U → Y)
    (op : Y → Y → Y) (enc : Y → List Bool) (dec : List Bool → Y) {x : ZMod n → ℕ × Bool × U}
    {ℓ : ZMod n}
    (hid : Function.Injective fun v => (x v).1) (hlead : ∀ v, (x v).2.1 = true ↔ v = ℓ)
    (hdec : ∀ y, dec (enc y) = y)
    (hself : ∀ X₁ X₂, X₁ ≠ 0 → X₂ ≠ 0 → f (X₁ + X₂) = op (f X₁) (f X₂))
    {lam β : ℕ} (hlam : ∀ v, Nat.size (x v).1 ≤ lam)
    (hβ : ∀ S : Finset (ZMod n), S.Nonempty →
      (enc (f (S.val.map fun u => (x u).2.2))).length ≤ β) :
    (∀ c, (aggAlg f op enc dec ComputeOR.proc BitSending.cwProc BitSending.proc).Reach
        (oriented n) x c →
      (aggAlg f op enc dec ComputeOR.proc BitSending.cwProc BitSending.proc).Final
        (oriented n) c →
      (aggAlg f op enc dec ComputeOR.proc BitSending.cwProc BitSending.proc).Quiescent
        (oriented n) c ∧
        ∀ v, (c.st v).1.out = enc (f (univ.val.map fun u => (x u).2.2)) ∧
          dec (c.st v).1.out = f (univ.val.map fun u => (x u).2.2)) ∧
    (∀ c, (aggAlg f op enc dec ComputeOR.proc BitSending.cwProc BitSending.proc).Reach
        (oriented n) x c →
      totalSent c ≤ 3 * n * (lam + 2 * Nat.log 2 n + 2 * β + 3) +
        Nat.log 2 n * (78 * n * lam + 15 * n * β + 180 * n)) ∧
    (aggAlg f op enc dec ComputeOR.proc BitSending.cwProc BitSending.proc).Composable
      (oriented n) x :=
  theorem1 (roundSpecAll hlead) hid hlead hdec hself hlam hβ

/-- **Corollary 2** (efficient counting), for the concrete algorithms: on an oriented ring with
distinct IDs of at most `C·(⌊log₂ n⌋ + 1)` bits and a unique leader, the counting algorithm is
quiescently terminating, every process outputs `n`, and every execution sends at most
`(81·C + 216)·n·(⌊log₂ n⌋ + 1)²` pulses. -/
theorem corollary2_concrete {x : ZMod n → ℕ × Bool × Unit} {ℓ : ZMod n}
    (hid : Function.Injective fun v => (x v).1) (hlead : ∀ v, (x v).2.1 = true ↔ v = ℓ)
    {C : ℕ} (hlam : ∀ v, Nat.size (x v).1 ≤ C * (Nat.log 2 n + 1)) :
    (∀ c, (countAlg ComputeOR.proc BitSending.cwProc BitSending.proc).Reach (oriented n) x c →
      (countAlg ComputeOR.proc BitSending.cwProc BitSending.proc).Final (oriented n) c →
      (countAlg ComputeOR.proc BitSending.cwProc BitSending.proc).Quiescent (oriented n) c ∧
        ∀ v, natDec (c.st v).1.out = n) ∧
    (∀ c, (countAlg ComputeOR.proc BitSending.cwProc BitSending.proc).Reach (oriented n) x c →
      totalSent c ≤ (81 * C + 216) * n * (Nat.log 2 n + 1) ^ 2) := by
  refine ⟨(corollary2 (roundSpecAll hlead) hid hlead hlam).1, fun c hc => ?_⟩
  exact corollary2_bigO (roundSpecAll hlead) hid hlead hlam c hc

end Podc.ContentOblivious.Aggregation
