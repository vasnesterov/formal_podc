import Papers.PODC2020.StoreCollectChurn.SnapshotOps

/-!
# Sequential histories of the snapshot specification, and sorted lists
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P]

/-- In a list sorted by `R`, two members `a ≠ b` with `¬ R b a` appear in the order `a, b`. -/
lemma sublist_of_pairwise {α : Type} {R : α → α → Prop} :
    ∀ {l : List α} {a b : α}, l.Pairwise R → a ∈ l → b ∈ l → ¬ R b a → a ≠ b → [a, b].Sublist l
  | [], _, _, _, ha, _, _, _ => by simp at ha
  | x :: l, a, b, hl, ha, hb, hba, hab => by
    rw [List.pairwise_cons] at hl
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact List.Sublist.cons₂ _ (List.singleton_sublist.2 hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd (hl.1 a ha') hba
      · exact List.Sublist.cons _ (sublist_of_pairwise hl.2 ha' hb' hba hab)

/-- `SeqOK` from the responses at every position. -/
lemma seqOK_of_forall {A : ObjSpec} {α : List (Label P A)} :
    ∀ (q : A.State) (L : List (OpId P × A.Op)),
      (∀ i (hi : i < L.length), ∀ r, respOf α L[i].1 = some r →
        (A.δ (A.runOps q ((L.take i).map Prod.snd)) L[i].2).2 = r) → SeqOK α q L
  | _, [], _ => trivial
  | q, (x, o) :: L, h => by
    refine ⟨fun r hr => h 0 (by simp) r hr, ?_⟩
    apply seqOK_of_forall
    intro i hi r hr
    have := h (i + 1) (by simp; omega) r (by simpa using hr)
    simpa using this

/-- The value of an update of `r`. -/
def updVal (r : P) : SnapOp P V → Option V
  | .update r' v => if r' = r then some v else none
  | .scan => none

lemma runOps_snap (ops : List (SnapOp P V)) (r : P) :
    (snapSpec P V).runOps (snapSpec P V).init ops r = (ops.filterMap (updVal r)).getLast? := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops o ih =>
    rw [ObjSpec.runOps_append, List.filterMap_append, ObjSpec.runOps_cons, ObjSpec.runOps_nil]
    rcases o with _ | ⟨r', v⟩
    · show (snapSpec P V).runOps (snapSpec P V).init ops r = _
      rw [ih]; simp [updVal]
    · by_cases hr : r' = r
      · subst hr
        show Function.update ((snapSpec P V).runOps (snapSpec P V).init ops) r' (some v) r' = _
        simp [updVal]
      · show Function.update ((snapSpec P V).runOps (snapSpec P V).init ops) r' (some v) r = _
        rw [Function.update_of_ne (Ne.symm hr), ih]
        simp [updVal, hr]

/-- The last value of a filter-map along a list sorted by a key: the entry of largest key. -/
lemma getLast?_filterMap_of_max {α β γ : Type} [LinearOrder γ] (key : α → γ) (f : α → Option β)
    {l : List α} (hl : l.Pairwise (fun a b => key a < key b)) {e : α} {v : β} (he : e ∈ l)
    (hf : f e = some v) (hmax : ∀ e' ∈ l, f e' ≠ none → key e' ≤ key e) :
    (l.filterMap f).getLast? = some v := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem he
  have h2 : l₂.filterMap f = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro e' he'
    by_contra hne
    have h1 := hmax e' (by simp [he']) hne
    have h3 : key e < key e' := by
      rw [List.pairwise_append] at hl
      exact (List.pairwise_cons.1 hl.2.1).1 e' he'
    exact absurd h1 (not_le.2 h3)
  simp [List.filterMap_append, hf, h2]

lemma getLast?_filterMap_eq_none {α β : Type} (f : α → Option β) {l : List α}
    (h : ∀ e ∈ l, f e = none) : (l.filterMap f).getLast? = none := by
  rw [List.filterMap_eq_nil_iff.2 h]; rfl

end Podc.StoreCollectChurn.Snap
