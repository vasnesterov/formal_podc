import Papers.PODC2024.HistoryIndependent.Avoidance

/-!
# The class `C_t` and Theorem 17 / Corollary 18

Definition 13, Theorem 17 and Corollary 18 of Attiya, Bender, Farach-Colton, Oshman, Schiller,
*History-Independent Concurrent Objects*, PODC 2024.
-/

namespace Cslib.SharedMemory

open List

/-- **Definition 13** (the class `C_t`). The state space is partitioned into `t` nonempty classes
(`cls` is surjective), a read-only operation `oread` distinguishes states of different classes,
and for any two distinct states `q ≠ q'` the operation `ochange q q'` moves the object from `q`
to `q'`. (The operations `ochange q q'` are part of the data so that access disciplines, e.g.
single-writer registers, can be expressed.) -/
structure ClassC (A : ObjSpec) (t : ℕ) where
  /-- The partition of the state space into `t` classes. -/
  cls : A.State → Fin t
  cls_surj : Function.Surjective cls
  /-- The distinguishing read-only operation. -/
  oread : A.Op
  oread_ro : A.ReadOnly oread
  oread_sep : ∀ q q', cls q ≠ cls q' → (A.δ q oread).2 ≠ (A.δ q' oread).2
  /-- The operation moving from `q` to `q'`. -/
  ochange : A.State → A.State → A.Op
  ochange_spec : ∀ q q', q ≠ q' → (A.δ q (ochange q q')).1 = q'

namespace ClassC

variable {A : ObjSpec} {t : ℕ} (K : ClassC A t)

/-- A representative state of each class. -/
noncomputable def rep (i : Fin t) : A.State := (K.cls_surj i).choose

lemma cls_rep (i : Fin t) : K.cls (K.rep i) = i := (K.cls_surj i).choose_spec

open Classical in
/-- The avoidance data of an object in `C_t`: representatives of the classes, single-operation
paths `ochange`. -/
noncomputable def avoidData : AvoidData A t where
  oread := K.oread
  oread_ro := K.oread_ro
  rep := K.rep
  resp_inj := by
    intro i j hij
    by_contra hne
    exact K.oread_sep (K.rep i) (K.rep j) (by rw [K.cls_rep, K.cls_rep]; exact hne) hij
  path i j := [K.ochange (K.rep i) (K.rep j)]
  path_end i j hij := by
    have : K.rep i ≠ K.rep j := fun h => hij (by rw [← K.cls_rep i, h, K.cls_rep])
    simp [K.ochange_spec _ _ this]
  path_mid i j hij m hm := by
    have : K.rep i ≠ K.rep j := fun h => hij (by rw [← K.cls_rep i, h, K.cls_rep])
    simp only [length_singleton] at hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
    · left; simp
    · right; simp [K.ochange_spec _ _ this]
  start j := if A.init = K.rep j then [] else [K.ochange A.init (K.rep j)]
  start_end j := by
    split_ifs with h
    · simpa using h
    · simp [K.ochange_spec _ _ h]

end ClassC

/-- **Theorem 17.** For any object in the class `C_t` (`t ≥ 2`), there is no wait-free,
state-quiescent history-independent implementation from base objects with fewer than `t`
states. Formally: in any implementation where some process `r` may invoke `oread` and another
process `c` may invoke all the `ochange` operations, if every base object has fewer than `t`
states, the implementation is not both wait-free and state-quiescent HI. -/
theorem thm17 {A : ObjSpec} {t : ℕ} (ht : 2 ≤ t) (K : ClassC A t) {ι : Type} [DecidableEq ι]
    {B : ι → ObjSpec} {P L : Type} [DecidableEq P] (I : Impl A B P L) (c r : P) (hcr : c ≠ r)
    (hr : I.allowed r K.oread) (hc : ∀ q q', I.allowed c (K.ochange q q'))
    (hB : ∀ j, Finite (B j).State ∧ Nat.card (B j).State < t) :
    ¬ (I.WaitFree ∧ I.StateQuiescentHI) :=
  not_waitFree_stateQuiescentHI K.avoidData I c r ht hcr hr
    (fun i j o ho => by simp [ClassC.avoidData] at ho; subst ho; exact hc _ _)
    (fun j o ho => by
      classical
      simp only [ClassC.avoidData] at ho; split_ifs at ho
      · simp at ho
      · simp at ho; subst ho; exact hc _ _) hB

/-! ## Multi-valued registers -/

/-- A `t`-valued register (values `Fin t`, initial value `v₀`) is in `C_t`: classes are the
values, `oread` is `read`, `ochange q q'` is `write q'`. -/
def registerClassC (t : ℕ) (v₀ : Fin t) : ClassC (register (Fin t) v₀) t where
  cls := id
  cls_surj := Function.surjective_id
  oread := .read
  oread_ro := fun _ => rfl
  oread_sep _ _ h := h
  ochange _ q' := .write q'
  ochange_spec _ _ _ := rfl

/-- **Corollary 18.** There is no wait-free state-quiescent HI implementation of a `t`-valued
register, `t ≥ 3`, from binary registers — even a single-writer single-reader one (any
implementation in which a writer `w` may write and a different reader `r` may read). -/
theorem cor18 {t : ℕ} (ht : 3 ≤ t) (v₀ : Fin t) {ι : Type} [DecidableEq ι] {P L : Type}
    [DecidableEq P] (b₀ : ι → Bool) (I : Impl (register (Fin t) v₀) (fun i => binaryRegister (b₀ i)) P L)
    (w r : P) (hwr : w ≠ r) (hr : I.allowed r .read) (hw : ∀ v, I.allowed w (.write v)) :
    ¬ (I.WaitFree ∧ I.StateQuiescentHI) :=
  thm17 (by omega) (registerClassC t v₀) I w r hwr hr (fun _ q' => hw q')
    (fun _ => ⟨inferInstanceAs (Finite Bool), by simp; omega⟩)

end Cslib.SharedMemory
