import Papers.PODC2015.EventualConsistencyLimits.Acts

/-!
# Reads in states that have heard everything

If replica `R` has received every message sent by the other replicas in `α` and nobody has a
message pending, then `R`'s state is final for the quiescent completion of `α`: a read of `o` at
`R` must return what late reads return, i.e. the maximal writes to `o`. When all writes to `o`
are by a single replica this is the value of the last one (`final_read`). This is the form in
which the paper's Theorem 12 uses eventual consistency.
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*} [DecidableEq ι]

namespace Store

variable {D : Store ι Obj V M St}

lemma getElem_append_deliverAll_do [Fintype ι] {R : ι} {α : List (ι × Ev Obj V M)} {a : ℕ}
    (ha : a < (α ++ deliverAll R α).length) {i : ι} {d : DoEv Obj V}
    (h : (α ++ deliverAll R α)[a] = (i, .do_ d)) : ∃ h : a < α.length, α[a] = (i, .do_ d) := by
  rw [List.getElem_append] at h
  split_ifs at h with h1
  · exact ⟨h1, h⟩
  · exfalso
    have hmem : (i, Ev.do_ d) ∈ deliverAll R α := h ▸ List.getElem_mem _
    obtain ⟨-, m, hm, -⟩ := mem_deliverAll hmem
    cases hm

/-- Delivering every message to every other replica quiesces an execution in which nobody has a
message pending and `R` has received everything. -/
lemma quiescent_deliverAll [Fintype ι] (hOD : D.OpDriven) (hRecv : D.RecvEnabled) {R : ι}
    {α : List (ι × Ev Obj V M)} (hα : D.IsExec α)
    (hnp : ∀ i σi, D.state i α = some σi → ¬ D.Pending i σi)
    (hrcv : ∀ j m, (j, .send m) ∈ α → j ≠ R → (R, .recv m) ∈ α) :
    D.IsExec (α ++ deliverAll R α) ∧ D.Quiescent (α ++ deliverAll R α) ∧
      D.state R (α ++ deliverAll R α) = D.state R α := by
  have hδmem : ∀ x ∈ deliverAll R α, ∃ m, x.2 = .recv m ∧ ∃ j, j ≠ x.1 ∧ (j, .send m) ∈ α :=
    fun x hx => (mem_deliverAll hx).2
  refine ⟨hα.append_recvs hRecv hδmem, ⟨fun i σi h => not_pending_append_recvs hOD
    (fun x hx => let ⟨m, hm, _⟩ := hδmem x hx; ⟨m, hm⟩) (hnp i) σi h, ?_⟩,
    state_append_of_not_mem _ _ _ deliverAll_ne⟩
  intro j m hj i hij
  have hjα : (j, Ev.send m) ∈ α := by
    rcases List.mem_append.1 hj with hj | hj
    · exact hj
    · obtain ⟨m', hm', -⟩ := hδmem _ hj; cases hm'
  by_cases hiR : i = R
  · subst hiR; exact List.mem_append_left _ (hrcv j m hjα (Ne.symm hij))
  · exact List.mem_append_right _ (recv_mem_deliverAll hjα hij hiR)

/-- A read at a replica that has heard everything (and nobody has a message pending) returns the
last write to `o`, when all writes to `o` are by one replica `q`. -/
theorem final_read [Fintype ι] {P : AE ι Obj V → Prop} (hEC : D.EventuallyConsistent P)
    (hOD : D.OpDriven) (hRecv : D.RecvEnabled) {α : List (ι × Ev Obj V M)} (hα : D.IsExec α)
    {R : ι} {o : Obj} {r : Resp V} {σ : St} (hσ : D.state R α = some σ)
    (hr : D.step R σ (rd o r) = some σ)
    (hnp : ∀ i σi, D.state i α = some σi → ¬ D.Pending i σi)
    (hrcv : ∀ j m, (j, .send m) ∈ α → j ≠ R → (R, .recv m) ∈ α)
    {q : ι} {p₀ : ℕ} (hp₀ : p₀ < α.length) {v₀ : V} {r₀ : Resp V}
    (hlast : α[p₀] = (q, .do_ ⟨o, .write v₀, r₀⟩))
    (hwr : ∀ p (hp : p < α.length) i v r', α[p] = (i, .do_ ⟨o, .write v, r'⟩) → i = q ∧ p ≤ p₀) :
    r = .vals {v₀} := by
  obtain ⟨hE, hq, hst⟩ := quiescent_deliverAll hOD hRecv hα hnp hrcv
  rw [← hst] at hσ
  obtain ⟨A, hOn, hWF, hC, -, hwA, p₁, -, -, -, d₁, -, -, -, v₁, -, c₁, -⟩ :=
    exists_late_ae hEC hE hq hσ hr hσ hr
  rw [AE.Correct.read' (hA := hC) d₁ v₁, c₁]
  congr 1
  have hp₀' : p₀ < (α ++ deliverAll R α).length := by simp; omega
  have hs₀ : ext2 (α ++ deliverAll R α) R (rd o r) R (rd o r) p₀ = (q, .do_ ⟨o, .write v₀, r₀⟩) := by
    rw [ext2_lt hp₀', List.getElem_append_left hp₀]; exact hlast
  obtain ⟨dp, rp, ep⟩ := hOn.at hs₀
  -- every write to `o` is by `q`, at a position `≤ p₀`
  have loc : ∀ a, A.dom a → (A.ev a).obj = o → A.IsWrite a →
      A.rep a = q ∧ a ≤ p₀ := by
    rintro a hda hoa ⟨u, hu⟩
    have hlt := hwA a hda ⟨u, hu⟩
    obtain ⟨i, d, hsd, hri, hev⟩ := hOn.of_dom hda
    rw [ext2_lt hlt] at hsd
    obtain ⟨h1, h2⟩ := getElem_append_deliverAll_do hlt hsd
    rw [hev] at hu hoa
    obtain ⟨o', op', r'⟩ := d
    simp only at hu hoa
    subst hu hoa
    obtain ⟨rfl, hle⟩ := hwr a h1 i u r' h2
    exact ⟨hri, hle⟩
  have hp₀W : p₀ ∈ {a | A.dom a ∧ (A.ev a).obj = o ∧ A.IsWrite a} :=
    ⟨dp, by rw [ep], v₀, by rw [ep]⟩
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, ⟨hda, hoa, hwa⟩, hav, hmax⟩
    obtain ⟨hra, hle⟩ := loc a hda hoa hwa
    rcases hle.lt_or_eq with hlt | rfl
    · exact absurd (hWF.vis_sess (hOn.2.2 _ _ hda dp (by rw [hra, rp]) hlt) (by rw [hra, rp]))
        (hmax _ hp₀W)
    · rw [ep] at hav; cases hav; rfl
  · rintro rfl
    refine ⟨p₀, hp₀W, by rw [ep], fun b ⟨hdb, hob, hwb⟩ hvb => ?_⟩
    obtain ⟨hrb, hle⟩ := loc b hdb hob hwb
    rcases hle.lt_or_eq with hlt | rfl
    · exact hWF.ord_irrefl _ (hWF.ord_trans (hWF.vis_ord hvb)
        (hOn.2.2 _ _ hdb dp (by rw [hrb, rp]) hlt))
    · exact hWF.ord_irrefl _ (hWF.vis_ord hvb)

/-- `final_read` with the last write given by a decomposition of the execution. -/
theorem final_read' [Fintype ι] {P : AE ι Obj V → Prop} (hEC : D.EventuallyConsistent P)
    (hOD : D.OpDriven) (hRecv : D.RecvEnabled) {α₁ α₂ : List (ι × Ev Obj V M)} {q : ι} {o : Obj}
    {v₀ : V} {r₀ : Resp V} (hα : D.IsExec (α₁ ++ (q, .do_ ⟨o, .write v₀, r₀⟩) :: α₂))
    {R : ι} {r : Resp V} {σ : St}
    (hσ : D.state R (α₁ ++ (q, .do_ ⟨o, .write v₀, r₀⟩) :: α₂) = some σ)
    (hr : D.step R σ (rd o r) = some σ)
    (hnp : ∀ i σi, D.state i (α₁ ++ (q, .do_ ⟨o, .write v₀, r₀⟩) :: α₂) = some σi →
      ¬ D.Pending i σi)
    (hrcv : ∀ j m, (j, .send m) ∈ α₁ ++ (q, .do_ ⟨o, .write v₀, r₀⟩) :: α₂ → j ≠ R →
      (R, .recv m) ∈ α₁ ++ (q, .do_ ⟨o, .write v₀, r₀⟩) :: α₂)
    (hall : ∀ z ∈ α₁ ++ (q, .do_ ⟨o, .write v₀, r₀⟩) :: α₂, ∀ v r', z.2 = .do_ ⟨o, .write v, r'⟩ →
      z.1 = q)
    (h₂ : ∀ z ∈ α₂, ∀ v r', z ≠ (q, .do_ ⟨o, .write v, r'⟩)) :
    r = .vals {v₀} := by
  refine final_read hEC hOD hRecv hα hσ hr hnp hrcv (q := q) (p₀ := α₁.length) (v₀ := v₀)
    (r₀ := r₀) (by simp) (by simp) ?_
  intro p hp i v r' he
  have hz := hall _ (he ▸ List.getElem_mem hp) v r' rfl
  simp only at hz
  subst hz
  refine ⟨rfl, ?_⟩
  by_contra hlt
  push_neg at hlt
  rw [List.getElem_append_right (by omega)] at he
  obtain ⟨k, hk⟩ : ∃ k, p - α₁.length = k + 1 := ⟨p - α₁.length - 1, by omega⟩
  simp only [hk, List.getElem_cons_succ] at he
  exact h₂ _ (he ▸ List.getElem_mem _) v r' rfl

end Store

end Podc.EventualConsistencyLimits
