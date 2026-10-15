import Papers.PODC2021.LinearizabilityTypo.Examples
import Papers.PODC2021.LinearizabilityTypo.Alternative
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Locality
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Bridge

/-!
# Linearizability: A Typo (Sela, Herlihy, Petrank; PODC 2021) — main results

Statements of the paper's results, with the paper's numbering. The general theory is in
`Cslib/Computability/Distributed/SharedMemory/HerlihyWing/`; the concrete counterexamples are in `Examples.lean` and
`Alternative.lean`.

* Definitions 2.2, 4.1, 7.1: `Cslib.SharedMemory.HerlihyWing.LinearizableHW`, `Cslib.SharedMemory.HerlihyWing.Linearizable`,
  `Cslib.SharedMemory.HerlihyWing.LinearizableLP`.
* Section 3: the original definition is neither local nor nonblocking.
* Theorems 5.1, 5.2: the amended definition is local and nonblocking.
* Claim 1: linearization points ⟺ amended definition (and not the original one).
* Section 8: amended ⊊ original; alternative interpretation (Section 6) ⊊ amended.
* CSLib: `Cslib.SharedMemory.IsLinearization` is the *amended* definition.
-/

namespace Podc2021.LinearizabilityTypo

open Cslib.SharedMemory.HerlihyWing Proc

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-- **Section 3.2.** Linearizability as defined with the typo (Definition 2.2) is not local:
the history `H` of Figure 3 is not linearizable although both object subhistories are. -/
theorem sec3_2_not_local :
    ∃ (spec : SeqSpec Proc Reg2 RegOp RegRes) (H : History Proc Reg2 RegOp RegRes),
      WellFormed H ∧ (∀ o, LinearizableHW spec (restrictX H o)) ∧ ¬ LinearizableHW spec H :=
  not_local_HW

/-- **Section 3.3.** Linearizability as defined with the typo (Definition 2.2) is not
nonblocking: in `H1` (Figure 1) the pending write is total, yet no response to it yields a
linearizable history. -/
theorem sec3_3_not_nonblocking :
    ∃ (H : History Proc Unit RegOp RegRes) (p : Proc) (x : Unit) (o : RegOp),
      LinearizableHW regSpec H ∧ PendingInv H p x o ∧ Total regSpec p x o ∧
        ∀ r, ¬ LinearizableHW regSpec (H ++ [.res p x r]) :=
  not_nonblocking_HW

/-- **Theorem 5.1** (locality of amended linearizability). -/
theorem theorem5_1 {spec : SeqSpec P X Op Res} {H : History P X Op Res} (hH : WellFormed H)
    (hnil : ∀ x, [] ∈ spec x) :
    Linearizable spec H ↔ ∀ x, Linearizable spec (restrictX H x) :=
  locality hH hnil

/-- **Theorem 5.2** (amended linearizability is nonblocking). -/
theorem theorem5_2 {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    (h : Linearizable spec H) {p : P} {x : X} {o : Op} (hpend : PendingInv H p x o)
    (htot : Total spec p x o) : ∃ r, Linearizable spec (H ++ [.res p x r]) :=
  h.nonblocking hpend htot

/-- **Claim 1.** Definition 7.1 (linearization points) is equivalent to Definition 4.1. -/
theorem claim_1 {spec : SeqSpec P X Op Res} {H : History P X Op Res} :
    LinearizableLP spec H ↔ Linearizable spec H := claim1

/-- **Section 7.** Definition 7.1 is not equivalent to the original Definition 2.2: `H1` is
linearizable by Definition 2.2 but not by Definition 7.1. -/
theorem sec7_not_equiv_original :
    LinearizableHW regSpec H1 ∧ ¬ LinearizableLP regSpec H1 :=
  ⟨H1_linearizableHW, fun h => H1_not_linearizable (claim1.1 h)⟩

/-- **Section 8.** The amended definition is strictly stronger than the original one. -/
theorem sec8_amended_lt_original :
    (∀ (spec : SeqSpec P X Op Res) (H : History P X Op Res),
      Linearizable spec H → LinearizableHW spec H) ∧
    (LinearizableHW regSpec H1 ∧ ¬ Linearizable regSpec H1) ∧
    (LinearizableHW queueSpec H2 ∧ ¬ Linearizable queueSpec H2) :=
  ⟨fun _ _ h => h.linearizableHW, ⟨H1_linearizableHW, H1_not_linearizable⟩,
    ⟨H2_linearizableHW, H2_not_linearizable⟩⟩

/-- **Sections 6 and 8.** The alternative interpretation (pending invocations as operations,
original L2) is strictly stronger than the amended definition: `H_s` (Figure 5). -/
theorem sec6_alternative_too_strong :
    (∀ (spec : SeqSpec P X Op Res) (H : History P X Op Res),
      Sec6.LinearizableAlt spec H → Linearizable spec H) ∧
    (Linearizable Sec6.stackSpec Sec6.Hs ∧ ¬ Sec6.LinearizableAlt Sec6.stackSpec Sec6.Hs) :=
  ⟨fun _ _ h => h.linearizable, Sec6.Hs_linearizable, Sec6.Hs_not_linearizableAlt⟩

/-! ## CSLib's linearizability -/

open Cslib.SharedMemory (ObjSpec Label) in
/-- The register (initially `0`) as a CSLib object. -/
def regObj : Cslib.SharedMemory.ObjSpec where
  State := ℕ
  Op := RegOp
  Resp := RegRes
  init := 0
  δ := regδ

/-- **CSLib implements the amended definition, not the one with the typo.** For every
well-formed single-object history, `Cslib.SharedMemory.IsLinearization` holds iff the history is
linearizable by Definition 4.1 (`linearizable_iff_cslib`). In particular CSLib rejects `H1`
(Figure 1), which the original Definition 2.2 accepts. -/
theorem cslib_rejects_H1 :
    WellFormed H1 ∧ LinearizableHW regSpec H1 ∧
      ¬ ∃ L, Cslib.SharedMemory.IsLinearization (ofHist (A := regObj) H1) L := by
  have hwf : WellFormed H1 := readWrite_wellFormed (by decide)
  refine ⟨hwf, H1_linearizableHW, fun h => H1_not_linearizable ?_⟩
  exact (linearizable_iff_cslib (A := regObj) H1 hwf).2 h

end Podc2021.LinearizabilityTypo
