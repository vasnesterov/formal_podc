import Papers.PODC2017.SeeingIsBelieving.ParallelSI

/-!
# The hierarchy of state-based commit tests

On a fixed execution `e`, the commit tests of Table 1 are ordered:
`CT_SER ⇒ CT_SI ⇒ CT_PSI ⇒ CT_RC ⇒ CT_RU` (for all transactions at once; the step
`CT_SI ⇒ CT_PSI` is the "Adya SI ⊆ PSI/PL-2+" level of Figure 4). The strictness of the first
step (write skew) is in `Examples.lean`.
-/

namespace Podc.SeeingIsBelieving

open Relation

variable {K ι : Type*} [DecidableEq K] [DecidableEq ι] {H : TxnSet K ι}

namespace Execution

variable (e : Execution H)

lemma ctSI_of_ctSer {T : ι} (hT : T ∈ H.committed) (h : e.CTSer T) : e.CTSI T :=
  ⟨e.idx T, (e.idx_lt_length hT).le, h, fun _ _ => rfl⟩

lemma ctPSI_of_ctSI (he : ∀ T ∈ H.committed, e.CTSI T) {T : ι} (hT : T ∈ H.committed) :
    e.CTPSI T := by
  classical
  have hex : ∀ T ∈ H.committed, ∃ j ≤ e.idx T, e.Complete T j ∧ e.NoConf T j := by
    intro T hT
    obtain ⟨i, -, hc, hn⟩ := he T hT
    by_cases hi : i ≤ e.idx T
    · exact ⟨i, hi, hc, hn⟩
    · exact ⟨e.idx T, le_rfl, fun m hm => absurd (hc m hm).1 hi, fun k _ => rfl⟩
  choose snap hsnap_le hcomp hnoconf using hex
  -- every `▶` edge `X ▶ Y` has `X` before the snapshot of `Y`
  have hd : ∀ X Y (hY : Y ∈ H.committed), e.DPrec X Y → e.idx X < snap Y hY := by
    rintro X Y hY ⟨hX, -, ⟨m, hm, hfirst⟩ | ⟨hlt, k, hwY, hwX⟩⟩
    · have := hfirst.2 _ (hcomp Y hY m hm); omega
    · by_contra hc
      exact e.state_ne_of_writer hX hwX (by omega) hlt (hnoconf Y hY k hwY)
  have hpath : ∀ X Y, TransGen e.DPrec X Y → ∃ hY : Y ∈ H.committed, e.idx X < snap Y hY := by
    intro X Y h
    induction h with
    | single h => exact ⟨h.2.1, hd _ _ h.2.1 h⟩
    | tail _ h ih =>
      obtain ⟨hb, hXb⟩ := ih
      have := hsnap_le _ hb
      have := hd _ _ h.2.1 h
      exact ⟨h.2.1, by omega⟩
  refine ⟨fun m hm => ⟨_, hcomp T hT m hm⟩, fun T' hT'T m hm _ i hi => ?_⟩
  obtain ⟨hT₁, hlt⟩ := hpath T' T hT'T
  have := hi.2 _ (hcomp T hT₁ m hm)
  omega

lemma ctRC_of_ctPSI {T : ι} (h : e.CTPSI T) : e.CTRC T := h.1

end Execution

/-- Figure 4 / Table 1 hierarchy at the level of sets of transactions:
serializable ⇒ snapshot isolation ⇒ PSI ⇒ read committed. -/
theorem satisfies_hierarchy :
    (H.Satisfies Execution.CTSer → H.Satisfies Execution.CTSI) ∧
    (H.Satisfies Execution.CTSI → H.Satisfies Execution.CTPSI) ∧
    (H.Satisfies Execution.CTPSI → H.Satisfies Execution.CTRC) :=
  ⟨fun ⟨e, he⟩ => ⟨e, fun T hT => e.ctSI_of_ctSer hT (he T hT)⟩,
   fun ⟨e, he⟩ => ⟨e, fun _ hT => e.ctPSI_of_ctSI he hT⟩,
   fun ⟨e, he⟩ => ⟨e, fun T hT => e.ctRC_of_ctPSI (he T hT)⟩⟩

end Podc.SeeingIsBelieving
