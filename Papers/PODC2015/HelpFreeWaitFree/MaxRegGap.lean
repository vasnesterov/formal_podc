import Papers.PODC2015.HelpFreeWaitFree.MaxRegister

/-!
# A gap in the proof of Theorem 4.11 (Claim 4.7.1, second case)

In the proof of Claim 4.7.1, the paper argues (second case for line 4): after `W₃ = WriteMax(3)`
completed without being decided before the pending `R₁ = ReadMax`, "`R₁` cannot possibly return
any value `≥ 3` … But if `R₁` cannot possibly return a value `≥ 3`, then `R₁` is decided before
`W₃`." The last inference is not valid: whether a *pending* operation is decided before another
one depends on the linearization function, which may leave a pending read out of the
linearization (Definition of linearization in Section 4.3) until it returns, even though its
response is already determined.

We show this on the max register of Figure 4.5 with the linearization function `lin'`: the
linearization points of Section 4.8.2, except that a `ReadMax` is only included once it has
returned (`isLinFun_lin'`). In the history `gapHist` (process `0` invokes `ReadMax` and reads `0`;
process `1` then runs `WriteMax(3)` to completion), every extension in which `R₁ = (0, 0)` returns
gives it the response `0` (`gap_resp`), yet `R₁` is not decided before `W₃ = (1, 0)`
(`gap_not_decided`). (`lin'` is also help-free by the reasoning of Claim 4.8.1, since a read is
inserted when it returns, at its read step; we do not formalize this, it is not needed to refute
the inference.)

The general fact behind `lin'` (`isLinearization_filter`): dropping pending read-only operations
from a linearization yields a linearization.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

section Filter

variable {P : Type} [DecidableEq P] {A : ObjSpec}

lemma seqOK_filter {α : List (Label P A)} (keep : OpId P × A.Op → Bool)
    (hro : ∀ e, keep e = false → A.ReadOnly e.2 ∧ ¬ Completed α e.1) :
    ∀ {q : A.State} {S : List (OpId P × A.Op)}, SeqOK α q S → SeqOK α q (S.filter keep)
  | _, [], _ => trivial
  | q, (x, o) :: S, ⟨h1, h2⟩ => by
    by_cases hk : keep (x, o) = true
    · rw [List.filter_cons_of_pos hk]; exact ⟨h1, seqOK_filter keep hro h2⟩
    · rw [List.filter_cons_of_neg hk]
      obtain ⟨hr, -⟩ := hro (x, o) (by simpa using hk)
      have := seqOK_filter keep hro h2
      rwa [hr q] at this

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Linearization.lean
/-- Dropping pending read-only operations from a linearization yields a linearization. -/
lemma isLinearization_filter {α : List (Label P A)} {S : List (OpId P × A.Op)}
    (hS : IsLinearization α S) (keep : OpId P × A.Op → Bool)
    (hro : ∀ e, keep e = false → A.ReadOnly e.2 ∧ ¬ Completed α e.1) :
    IsLinearization α (S.filter keep) where
  nodup := ((List.filter_sublist).map Prod.fst).nodup hS.nodup
  op_eq y hy := hS.op_eq y (List.mem_of_mem_filter hy)
  complete a ha := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (hS.complete a ha)
    refine List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, ?_⟩, rfl⟩
    by_contra hk
    exact (hro e (by simpa using hk)).2 ha
  realtime a b hab hb := by
    obtain ⟨l', hl', he⟩ := List.sublist_map_iff.1 (hS.realtime a b hab
      (List.Sublist.map _ List.filter_sublist |>.subset hb))
    obtain ⟨ea, eb, rfl⟩ : ∃ ea eb, l' = [ea, eb] := by
      match l', he with
      | [ea, eb], _ => exact ⟨ea, eb, rfl⟩
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at he
    obtain ⟨rfl, rfl⟩ := he
    have hea : ea ∈ S := hl'.subset (by simp)
    have heb : eb ∈ S := hl'.subset (by simp)
    have hka : keep ea = true := by
      by_contra hk; exact (hro ea (by simpa using hk)).2 hab.completed
    have hkb : keep eb = true := by
      obtain ⟨e, he, he1⟩ := List.mem_map.1 hb
      have := List.inj_on_of_nodup_map hS.nodup (List.mem_of_mem_filter he) heb he1
      rw [← this]; exact (List.mem_filter.1 he).2
    have : List.Sublist [ea, eb] (S.filter keep) := by
      have := hl'.filter keep
      rwa [List.filter_cons_of_pos hka, List.filter_cons_of_pos hkb, List.filter_nil] at this
    exact this.map Prod.fst
  seq := seqOK_filter keep hro hS.seq

end Filter

namespace MaxRegister

variable {P : Type} [DecidableEq P]

/-- Linearization points of Section 4.8.2, but a `ReadMax` enters the linearization only when it
returns. -/
noncomputable def lin' (h : List (Label P maxRegObj)) : List (OpId P × MaxOp) := by
  classical
  exact (lin h).filter (fun e => decide (Completed h e.1 ∨ e.2 ≠ .readMax))

theorem isLinFun_lin' : (impl P).IsLinFun lin' := by
  intro α hα
  classical
  refine isLinearization_filter (isLinFun_lin α hα) _ (fun e he => ?_)
  simp only [decide_eq_false_iff_not, not_or, not_not] at he
  refine ⟨?_, he.1⟩
  rw [he.2]; intro q; rfl

/-! ### The history of the gap -/

/-- `R₁` (process `0`) invokes `ReadMax` and reads `0`; then `W₃` (process `1`) runs
`WriteMax(3)` to completion. -/
def gapHist : List (Label (Fin 2) maxRegObj) :=
  [.inv 0 .readMax, .tau 0, .inv 1 (.writeMax 3), .tau 1, .tau 1, .ret 1 0]

instance : ∀ (p : Fin 2) (o : maxRegObj.Op), Decidable ((impl (Fin 2)).allowed p o) :=
  fun _ _ => (inferInstance : Decidable True)

theorem run_gapHist : ∃ C : Cfg (Fin 2), (impl (Fin 2)).run gapHist = some C ∧
    C.loc 0 = .rDone 0 ∧ C.pend 0 = some .readMax := by
  rw [Impl.run_eq_crun]
  simp [Impl.crun, Impl.crunFrom, Impl.cstep, gapHist, impl, Impl.initCfg, val]

/-- `R₁` is not decided before `W₃` (with respect to `lin'`): `lin'` contains the completed `W₃`
but not the pending `R₁`. -/
theorem gap_not_decided :
    ¬ DecidedBefore (impl (Fin 2)) lin' gapHist ((0 : Fin 2), 0) ((1 : Fin 2), 0) := by
  intro hd
  obtain ⟨C, hC, -, -⟩ := run_gapHist
  have hv : (impl (Fin 2)).Valid (gapHist ++ []) := ⟨C, by simpa using hC⟩
  have hlin := isLinFun_lin' (gapHist ++ []) hv
  apply hd [] hv
  refine ⟨hlin.complete _ (by simp [Completed, gapHist, respsOf]), Or.inl ?_⟩
  intro hm
  obtain ⟨e, he, he1⟩ := List.mem_map.1 hm
  have hop := hlin.op_eq e he
  rw [he1] at hop
  have hk := (List.mem_filter.1 he).2
  simp only [decide_eq_true_eq] at hk
  rcases hk with hk | hk
  · rw [he1] at hk; simp [Completed, gapHist, respsOf] at hk
  · apply hk
    simp [opOf, gapHist, opsOf] at hop
    exact hop.symm

lemma resp_first {s : List (Label (Fin 2) maxRegObj)} :
    ∀ {C C' : Cfg (Fin 2)}, C.loc 0 = .rDone 0 → C.pend 0 ≠ none →
      (impl (Fin 2)).runFrom C s = some C' → ∀ r, (respsOf s 0).head? = some r → r = 0 := by
  induction s with
  | nil => intro _ _ _ _ _ r hr; simp at hr
  | cons ℓ s ih =>
    intro C C' hl hp hrun r hr
    simp only [Impl.runFrom_cons] at hrun
    cases hs : (impl (Fin 2)).step C ℓ with
    | none => simp [hs] at hrun
    | some C₁ =>
      simp only [hs, Option.bind_some] at hrun
      by_cases hq : ℓ.proc = 0
      · cases ℓ with
        | inv q o =>
          simp only [Label.proc] at hq; subst hq
          exact absurd (Impl.step_inv hs).1 hp
        | tau q =>
          simp only [Label.proc] at hq; subst hq
          obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau hs
          rw [hl] at hact; simp [impl] at hact
        | ret q r' =>
          simp only [Label.proc] at hq; subst hq
          obtain ⟨-, -, -, l, hact, -⟩ := Impl.step_ret hs
          rw [hl] at hact; simp only [impl, Action.ret.injEq] at hact
          simp only [respsOf_cons, Label.retOf_ret, ↓reduceIte, Option.toList_some,
            List.singleton_append, List.head?_cons, Option.some.injEq] at hr
          rw [← hr, hact.1]
      · have h1 := Impl.step_other hs hq
        rw [respsOf_cons, Label.retOf_eq_none_of_proc_ne hq] at hr
        exact ih (by rw [h1.1]; exact hl) (by rw [h1.2]; exact hp) hrun r (by simpa using hr)

/-- Every extension of `gapHist` in which `R₁` returns gives it the response `0`: its result is
already determined. -/
theorem gap_resp {s : List (Label (Fin 2) maxRegObj)} (hv : (impl (Fin 2)).Valid (gapHist ++ s))
    {r : ℕ} (hr : respOf (gapHist ++ s) ((0 : Fin 2), 0) = some r) : r = 0 := by
  obtain ⟨C, hC, hl, hp⟩ := run_gapHist
  obtain ⟨C', hC'⟩ := hv
  rw [Impl.run_append_of_eq _ hC] at hC'
  apply resp_first hl (by rw [hp]; simp) hC' r
  have : respsOf gapHist (0 : Fin 2) = [] := by simp [gapHist, respsOf]
  simp only [respOf, respsOf_append, this, List.nil_append] at hr
  rw [List.head?_eq_getElem?]; exact hr

/-- **The inference of Claim 4.7.1 (second case) fails**: in the history `gapHist`, the pending
`R₁` returns `0 < 3` in every extension, but it is not decided before the completed `W₃ =
WriteMax(3)` with respect to the linearization function `lin'`. -/
theorem claim_4_7_1_inference_fails :
    (impl (Fin 2)).IsLinFun lin' ∧
    (∀ s, (impl (Fin 2)).Valid (gapHist ++ s) → ∀ r,
      respOf (gapHist ++ s) ((0 : Fin 2), 0) = some r → r < 3) ∧
    ¬ DecidedBefore (impl (Fin 2)) lin' gapHist ((0 : Fin 2), 0) ((1 : Fin 2), 0) :=
  ⟨isLinFun_lin', fun _ hv r hr => by rw [gap_resp hv hr]; norm_num, gap_not_decided⟩

end MaxRegister

end Podc.HelpFreeWaitFree
