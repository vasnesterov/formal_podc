import Papers.PODC2015.EventualConsistencyLimits.Late

/-!
# Definition 14 as written is unsatisfiable

Definition 14 of [AEM15] calls a data store eventually consistent if, for every infinite
execution `α`, **every** abstract execution that `α` complies with is eventually consistent.
Compliance (Definition 9) only fixes the per-replica sequences of operations, not visibility. So
the abstract execution whose visibility is just the per-replica order complies with `α` as well.
If two replicas read the same MVR forever and nothing is written, this abstract execution is
correct and causally consistent, but not eventually consistent.

`literalEC_false`: no data store with two replicas, available invisible reads, op-driven messages
and correct finite executions satisfies Definition 14 literally, even if "every abstract execution"
is restricted to correct, causally consistent ones. We therefore use the evident intent ("some
correct abstract execution that `α` complies with is eventually consistent",
`Store.EventuallyConsistent`).
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*} [DecidableEq ι]

namespace Store

/-- Definition 14 read literally (restricted to correct, causally consistent abstract
executions, which only makes it weaker). -/
def LiteralEC (D : Store ι Obj V M St) : Prop :=
  ∀ s, D.IsInfExec s → D.SuffConnected s →
    ∀ A : AE ι Obj V, A.On (fun p => some (s p)) → A.WF → A.CC → A.EC

variable {D : Store ι Obj V M St}

/-- A read with no write before it returns `∅` in a store with correct finite executions. -/
lemma read_init_empty (hCC : D.CausallyConsistent) {R : ι} {o : Obj} {r : Resp V} {σ : St}
    (h : D.step R (D.init R) (rd o r) = some σ) : r = .vals ∅ := by
  have hE : D.IsExec [(R, rd o r)] := .snoc (α := []) .nil rfl h (fun m h => by cases h)
  obtain ⟨A, hOn, hWF, hC, -⟩ := hCC _ hE
  have h0 : A.dom 0 ∧ A.rep 0 = R ∧ A.ev 0 = ⟨o, .read, r⟩ :=
    ⟨(hOn.1 0).2 ⟨R, _, rfl⟩, hOn.2.1 0 R _ rfl⟩
  rw [AE.Correct.read' (hA := hC) h0.1 h0.2.2]
  congr 1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro a ha
  obtain ⟨i, d, hd⟩ := (hOn.1 a).1 (hWF.vis_dom ha.1).1
  have ha0 : a = 0 := by
    rcases a with _ | a
    · rfl
    · simp [seqL] at hd
  subst ha0
  obtain ⟨u, hu⟩ := ha.2.2
  rw [h0.2.2] at hu
  cases hu

/-- **Definition 14, read literally, is unsatisfiable.** -/
theorem literalEC_false (hCC : D.CausallyConsistent) (hIR : D.InvisibleReads)
    (hOD : D.OpDriven) (hAv : D.Available) {R R' : ι} (hRR' : R ≠ R') (o : Obj) :
    ¬ D.LiteralEC := by
  intro hL
  obtain ⟨r₁, σ₁, h₁⟩ := hAv R (D.init R) o .read
  obtain ⟨r₂, σ₂, h₂⟩ := hAv R' (D.init R') o .read
  have e₁ := hIR _ _ _ _ _ h₁
  have e₂ := hIR _ _ _ _ _ h₂
  subst e₁ e₂
  have hr₁ := read_init_empty hCC h₁
  have hr₂ := read_init_empty hCC h₂
  subst hr₁ hr₂
  set s := ext2 ([] : List (ι × Ev Obj V M)) R (rd o (.vals ∅)) R' (rd o (.vals ∅))
  have hinf : D.IsInfExec s :=
    isInfExec_ext2 .nil rfl h₁ rfl h₂ (fun m h => by cases h) (fun m h => by cases h)
  have hq : D.Quiescent ([] : List (ι × Ev Obj V M)) :=
    ⟨fun i σ h => by cases h; exact hOD.1 i, fun j m h => by simp at h⟩
  have hsc : D.SuffConnected s :=
    suffConnected_ext2 hq rfl h₁ rfl h₂ (fun m h => by cases h) (fun m h => by cases h)
  have hs : ∀ p, s p = (if p % 2 = 0 then R else R', rd o (.vals ∅)) := by
    intro p
    simp only [s, ext2, List.length_nil, not_lt_zero', dite_false, Nat.sub_zero]
    split_ifs <;> rfl
  -- the abstract execution whose visibility is the per-replica order
  let A : AE ι Obj V :=
    { dom := fun _ => True
      rep := fun p => (s p).1
      ev := fun _ => ⟨o, .read, .vals ∅⟩
      ord := fun p q => p < q
      vis := fun p q => p < q ∧ (s p).1 = (s q).1 }
  have hWF : A.WF :=
    { ord_dom := fun _ => ⟨trivial, trivial⟩
      ord_irrefl := fun a => lt_irrefl a
      ord_trans := fun h h' => lt_trans h h'
      ord_total := fun _ _ h => lt_or_gt_of_ne h
      ord_fin := fun b => Set.finite_lt_nat b
      vis_ord := fun h => h.1
      vis_sess := fun h h' => ⟨h, h'⟩
      vis_mono := fun h h' h'' => ⟨lt_trans h.1 h', h.2.trans h''⟩ }
  have hOn : A.On fun p => some (s p) := by
    refine ⟨fun p => ⟨fun _ => ⟨_, ⟨o, .read, .vals ∅⟩, by simp only [hs p]; rfl⟩, fun _ => trivial⟩, fun p i d h => ?_,
      fun p q _ _ _ h => h⟩
    simp only [hs p, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    cases h2
    exact ⟨by simp [A, hs p, h1], rfl⟩
  have hCCA : A.CC := by
    refine ⟨fun e _ => ?_, fun a b c h h' => ⟨lt_trans h.1 h'.1, h.2.trans h'.2⟩⟩
    show Resp.vals ∅ = A.mvr e
    rw [AE.mvr_of_read rfl]
    congr 1
    ext v
    simp only [Set.mem_empty_iff_false, false_iff]
    rintro ⟨a, ha, -⟩
    obtain ⟨u, hu⟩ := ha.2.2
    cases hu
  have hEC := hL s hinf hsc A hOn hWF hCCA 0 trivial
  apply Set.infinite_of_not_bddAbove _ hEC
  rintro ⟨B, hB⟩
  have hmem : 2 * B + 1 ∈ {e' | A.dom e' ∧ (A.ev e').obj = (A.ev 0).obj ∧ ¬ A.vis 0 e'} := by
    refine ⟨trivial, rfl, fun h => ?_⟩
    have := h.2
    simp only [A, hs] at this
    rw [if_pos (by norm_num), if_neg (by omega)] at this
    exact hRR' this
  have := hB hmem
  omega

end Store

end Podc.EventualConsistencyLimits
