import Papers.PODC2017.SeeingIsBelieving.Serializability

/-!
# Theorems 3 and 4: read committed and read uncommitted

* Theorem 3: `∃ e : ∀ T ∈ 𝒯 : CT_RC(T, e) ≡ ¬G1` (Adya's PL-2).
* Theorem 4: `∃ e : ∀ T ∈ 𝒯 : CT_RU(T, e) ≡ ¬G0` (Adya's PL-1): both sides always hold.

As for Theorems 1 and 2, Adya's side is read as "for some version order".
-/

namespace Podc.SeeingIsBelieving

open Relation

variable {K ι : Type*} [DecidableEq K] [DecidableEq ι] {H : TxnSet K ι}

namespace Execution

variable (e : Execution H)

/-- If every operation has a read state, dependency edges go forward in `e`. -/
lemma dep_idx_of_preRead (hpre : ∀ T ∈ H.committed, e.PreRead T) {X Y : ι} (h : e.vo.Dep X Y) :
    e.idx X < e.idx Y := by
  rcases h with h | ⟨hX, hY, hne, k, -, hmem⟩
  · exact e.vo_ww_idx h
  · obtain ⟨m, hm, hm'⟩ := exists_getElem?_of_mem hmem
    obtain ⟨i, hi⟩ := hpre Y hY m hm
    have := e.lt_of_readState_ne hm' hne hi
    have := hi.1
    omega

lemma not_G1_of_preRead (hpre : ∀ T ∈ H.committed, e.PreRead T) : ¬ e.vo.G1 := by
  rintro (hG | ⟨X, hX⟩)
  · exact e.not_G1a hpre hG
  · have := lt_of_transGen e.idx (fun a b h => e.dep_idx_of_preRead hpre h) hX
    exact lt_irrefl _ this

/-- `PREREAD` holds in any execution in which every committed transaction comes after the
writers of the values it reads (under well-formedness and without aborted reads). -/
lemma preRead_of_wr (hwf : H.WellFormed) (hG1a : ¬ H.G1a)
    (hwr : ∀ X Y, H.WR X Y → e.idx X < e.idx Y) {T : ι} (hT : T ∈ H.committed) :
    e.PreRead T := by
  intro m hm
  have hm' : (H.ops T)[m]? = some (H.ops T)[m] := List.getElem?_eq_getElem hm
  have hmem : (H.ops T)[m] ∈ H.ops T := List.getElem_mem hm
  generalize (H.ops T)[m] = o at hm' hmem
  cases o with
  | write k => exact ⟨0, (e.readState_write hm').2 (Nat.zero_le _)⟩
  | read k v =>
    cases v with
    | none => exact ⟨0, (e.readState_read hm').2 ⟨Nat.zero_le _, Or.inl rfl⟩⟩
    | some V =>
      by_cases hVT : V = T
      · subst hVT
        exact ⟨0, (e.readState_read hm').2
          ⟨Nat.zero_le _, Or.inr ⟨rfl, hwf.read_own V hT m k hm'⟩⟩⟩
      have hwV := hwf.read_other T hT k V hmem hVT
      have hVc : V ∈ H.committed := by
        by_contra hc; exact hG1a ⟨T, hT, k, V, hmem, hc⟩
      have := hwr V T ⟨hVc, hT, hVT, k, hwV, hmem⟩
      exact ⟨e.idx V + 1, (e.readState_read hm').2 ⟨by omega, Or.inl (e.state_idx_succ hVc hwV)⟩⟩

end Execution

/-- An execution in which the dependency edges of `vo` go forward (when `¬G1c`). -/
lemma VersionOrder.exists_execution_of_not_G1c (vo : VersionOrder H) (h : ¬ vo.G1c) :
    ∃ e : Execution H, ∀ a b, vo.Dep a b → e.idx a < e.idx b := by
  have hacyc : ∀ a, ¬ TransGen (H.committed.restrictRel vo.Dep) a a := by
    intro a ha
    rw [transGen_restrict_of (fun a b h => vo.dep_committed h)] at ha
    exact h ⟨a, ha⟩
  obtain ⟨e, he⟩ := Execution.exists_of_acyclic vo.Dep hacyc
  exact ⟨e, fun a b h => he a b (vo.dep_committed h).1 (vo.dep_committed h).2 h⟩

/-- **Theorem 3** of [Crooks, Pu, Alvisi, Clement, PODC 2017]. A set of transactions satisfies
the state-based definition of read committed (`∃ e, ∀ T, CT_RC(T, e)`) iff it has a version
order for which Adya's phenomenon G1 is excluded (PL-2). -/
theorem theorem3 (hwf : H.WellFormed) :
    H.Satisfies Execution.CTRC ↔ ∃ vo : VersionOrder H, ¬ vo.G1 := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e.vo, e.not_G1_of_preRead he⟩
  · rintro ⟨vo, hG1⟩
    obtain ⟨e, he⟩ := vo.exists_execution_of_not_G1c (fun h => hG1 (Or.inr h))
    exact ⟨e, fun T hT => e.preRead_of_wr hwf (fun h => hG1 (Or.inl h))
      (fun X Y h => he X Y (Or.inr h)) hT⟩

omit [DecidableEq K] [DecidableEq ι] in
/-- Every set of transactions has an execution. -/
lemma TxnSet.nonempty_execution (H : TxnSet K ι) : Nonempty (Execution H) :=
  ⟨⟨H.committed.toList, H.committed.nodup_toList, fun _ => Finset.mem_toList⟩⟩

/-- **Theorem 4** of [Crooks, Pu, Alvisi, Clement, PODC 2017]. Read uncommitted: both sides
always hold (the state-based test is `True`; the version order of any execution has no write
cycle). -/
theorem theorem4 : H.Satisfies Execution.CTRU ↔ ∃ vo : VersionOrder H, ¬ vo.G0 := by
  obtain ⟨e⟩ := H.nonempty_execution
  refine iff_of_true ⟨e, fun _ _ => trivial⟩ ⟨e.vo, ?_⟩
  rintro ⟨X, hX⟩
  exact lt_irrefl _ (lt_of_transGen e.idx (fun a b h => e.vo_ww_idx h) hX)

end Podc.SeeingIsBelieving
