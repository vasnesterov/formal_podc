import Papers.PODC2017.SeeingIsBelieving.Lemmas

/-!
# Theorem 1: serializability

`∃ e : ∀ T ∈ 𝒯 : CT_SER(T, e) ≡ ¬G1 ∧ ¬G2` (Adya's PL-3), where the right-hand side is read as
"for some version order" (the version order is not observable by clients; see `differencies.md`).
-/

namespace Podc.SeeingIsBelieving

open Relation

variable {K ι : Type*} [DecidableEq K] [DecidableEq ι] {H : TxnSet K ι}

namespace Execution

variable (e : Execution H)

/-- Under `CT_SER`, every edge of `DSG(H)` (with the version order of `e`) goes forward in `e`. -/
lemma dsg_idx_of_ctSer (he : ∀ T ∈ H.committed, e.CTSer T) {X Y : ι} (h : e.vo.DSG X Y) :
    e.idx X < e.idx Y := by
  rcases h with (h | ⟨hX, hY, hne, k, -, hmem⟩) | ⟨hX, hne, k, v, hmem, hN⟩
  · exact e.vo_ww_idx h
  · obtain ⟨m, hm, hm'⟩ := exists_getElem?_of_mem hmem
    exact (e.lt_of_readState_ne hm' hne (he Y hY m hm)).2
  · obtain ⟨m, hm, hm'⟩ := exists_getElem?_of_mem hmem
    obtain ⟨hYc, -⟩ := e.vo.isNextAfter_committed hN
    rcases ((e.readState_read hm').1 (he X hX m hm)).2 with hs | ⟨rfl, -⟩
    · have := e.le_idx_of_isNextAfter hs hN
      have hne' : e.idx X ≠ e.idx Y := fun h => hne (e.idx_inj hX hYc h)
      omega
    · exact hN.1.2.2.2.2

end Execution

/-- **Theorem 1** of [Crooks, Pu, Alvisi, Clement, PODC 2017]. A set of transactions satisfies
the state-based definition of serializability (`∃ e, ∀ T, CT_SER(T, e)`) iff it has a version
order for which Adya's phenomena G1 and G2 are excluded (PL-3). -/
theorem theorem1 (hwf : H.WellFormed) :
    H.Satisfies Execution.CTSer ↔ ∃ vo : VersionOrder H, ¬ vo.G1 ∧ ¬ vo.G2 := by
  constructor
  · rintro ⟨e, he⟩
    have hedge := fun X Y (h : e.vo.DSG X Y) => e.dsg_idx_of_ctSer he h
    refine ⟨e.vo, ?_, ?_⟩
    · rintro (hG | ⟨X, hX⟩)
      · exact e.not_G1a (fun T hT m hm => ⟨_, he T hT m hm⟩) hG
      · have := lt_of_transGen e.idx (fun a b h => hedge a b (Or.inl h)) hX
        omega
    · rintro ⟨X, Y, hXY, hYX⟩
      have h1 := hedge X Y (Or.inr hXY)
      have h2 := le_of_reflTransGen e.idx hedge hYX
      omega
  · rintro ⟨vo, hG1, hG2⟩
    have hdsg : ∀ a b, vo.DSG a b → a ∈ H.committed ∧ b ∈ H.committed := by
      rintro a b (h | ⟨ha, -, k, v, -, h⟩)
      · exact vo.dep_committed h
      · exact ⟨ha, (vo.isNextAfter_committed h).1⟩
    have hacyc : ∀ a, ¬ TransGen (H.committed.restrictRel vo.DSG) a a := by
      intro a ha
      rw [transGen_restrict_of hdsg] at ha
      rcases transGen_or_split ha with h | ⟨x, y, hxy, hax, hya⟩
      · exact hG1 (Or.inr ⟨a, h⟩)
      · exact hG2 ⟨x, y, hxy, hya.trans hax⟩
    obtain ⟨e, he⟩ := Execution.exists_of_acyclic vo.DSG hacyc
    have hedge : ∀ a b, vo.DSG a b → e.idx a < e.idx b := fun a b h =>
      he a b (hdsg a b h).1 (hdsg a b h).2 h
    have hvo : ∀ k Z V, vo.lt k Z V → e.idx Z < e.idx V := fun k Z V h =>
      lt_of_transGen e.idx (fun a b h => hedge a b (Or.inl (Or.inl h))) (vo.transGen_ww_of_lt h)
    refine ⟨e, fun T hT m hm => ?_⟩
    have hm' : (H.ops T)[m]? = some (H.ops T)[m] := List.getElem?_eq_getElem hm
    have hmem : (H.ops T)[m] ∈ H.ops T := List.getElem_mem hm
    generalize (H.ops T)[m] = o at hm' hmem
    cases o with
    | write k => exact (e.readState_write hm').2 le_rfl
    | read k v =>
      refine (e.readState_read hm').2 ⟨le_rfl, ?_⟩
      by_cases hint : v = some T ∧ Op.write k ∈ (H.ops T).take m
      · exact Or.inr hint
      left
      refine e.state_eq_of_no_next vo (hvo k) ?_ ?_
      · rintro V rfl
        by_cases hVT : V = T
        · subst hVT; exact absurd ⟨rfl, hwf.read_own V hT m k hm'⟩ hint
        have hwV := hwf.read_other T hT k V hmem hVT
        have hVc : V ∈ H.committed := by
          by_contra hc; exact hG1 (Or.inl ⟨T, hT, k, V, hmem, hc⟩)
        exact ⟨hVc, hwV, hedge V T (Or.inl (Or.inr ⟨hVc, hT, hVT, k, hwV, hmem⟩))⟩
      · intro N Z hN hNZ hZ hwZ hZT
        have hNZ' := le_of_reflTransGen e.idx (fun a b h => hedge a b (Or.inl (Or.inl h))) hNZ
        by_cases hNT : N = T
        · subst hNT; omega
        · have := hedge T N (Or.inr ⟨hT, Ne.symm hNT, k, v, hmem, hN⟩)
          omega

end Podc.SeeingIsBelieving
