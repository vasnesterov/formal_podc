import Papers.PODC2016.WeakCrashFailures.Fig1Model

/-!
# Fig. 1: the inductive invariant

The invariant `Inv x C` consists of a local invariant `LI` per process (by program counter) and
global facts. The core of agreement (Lemmas 3 and 4 of the paper) is the notion of a *tag*
(`Tag`): every value ever decided or written into `decision` is `val x t` for a tag `t` with
`TagFact C t`, where
* `Tag.ex y` stands for "the maximum of the inputs of all processes but `y`" (lines 7 and 20):
  `y`'s state is smaller than everybody else's, and `y` is frozen: it has terminated, or it is
  *doomed* (`DoomedR C 3 y`: all other processes have `state = 3`, and `y` has not yet scanned
  in round 3 in a way that would let it write `3`);
* `Tag.all` stands for "the maximum of all inputs" (line 25): every state is `3`.
Two tags satisfying `TagFact` in the same configuration are equal (`TagFact.unique`, `n ≥ 2`),
which gives agreement.
-/

namespace Podc.WeakCrashFailures.Fig1

open Finset

variable {n : ℕ}

/-- Number of processes with index `< j` other than `y`. -/
def cntLt (j : ℕ) (y : Fin n) : ℕ := (univ.filter fun k : Fin n => k.val < j ∧ k ≠ y).card

/-- Number of processes with `state ≥ r`. -/
def cntGE (C : Cfg n) (r : ℕ) : ℕ := (univ.filter fun k : Fin n => r ≤ C.st k).card

/-- The indices `< j`. -/
def ltSet (j : ℕ) : Finset (Fin n) := univ.filter fun k : Fin n => k.val < j

/-- `y` has not yet passed (or is about to fail) the line-7 test of round `r`: it is in an earlier
round, or in the scan of round `r` having counted exactly the other processes read so far. -/
def PreRpc (r : ℕ) (y : Fin n) : PC → Prop
  | .start => True
  | .scan r' j cnt _ => r' < r ∨ (r' = r ∧ cnt = cntLt j y)
  | .scanIn r' j cnt _ => r' < r ∨ (r' = r ∧ cnt = cntLt (j + 1) y)
  | .wait r' _ _ _ => r' < r
  | .done _ => True
  | _ => False

/-- `y` is doomed in round `r`: all other processes have `state ≥ r`, `y`'s state is `< r`, and
`y` is before (or within, counting everybody else) the scan of round `r`. Such a process never
writes `r` into its state register: it decides in line 7 of round `r` at the latest. -/
def DoomedR (C : Cfg n) (r : ℕ) (y : Fin n) : Prop :=
  (∀ k, k ≠ y → r ≤ C.st k) ∧ C.st y < r ∧ PreRpc r y (C.pc y)

/-- Tags of decision values. -/
inductive Tag (n : ℕ)
  | ex (y : Fin n)
  | all

/-- The value of a tag. -/
def val (x : Fin n → ℕ) : Tag n → ℕ
  | .ex y => (univ.erase y).sup x
  | .all => univ.sup x

/-- The facts justifying a tag. -/
def TagFact (C : Cfg n) : Tag n → Prop
  | .ex y => (∀ k, k ≠ y → C.st y < C.st k) ∧ ((∃ v, C.pc y = .done v) ∨ DoomedR C 3 y)
  | .all => ∀ k, C.st k = 3

/-- The local invariant of process `i` with program counter `c`. -/
def LIpc (x : Fin n → ℕ) (C : Cfg n) (i : Fin n) : PC → Prop
  | .start => C.st i = 0
  | .scan r j cnt mx => 1 ≤ r ∧ r ≤ 3 ∧ j ≤ n ∧ C.st i + 1 = r ∧
      (r = 2 → n - 1 ≤ cntGE C 1) ∧
      ∃ S : Finset (Fin n), (∀ k ∈ S, k.val < j ∧ r ≤ C.st k) ∧ S.card = cnt ∧ mx = S.sup x
  | .scanIn r j cnt mx => 1 ≤ r ∧ r ≤ 3 ∧ ∃ h : j < n, C.st i + 1 = r ∧
      (r = 2 → n - 1 ≤ cntGE C 1) ∧ r ≤ C.st ⟨j, h⟩ ∧
      ∃ S : Finset (Fin n), (∀ k ∈ S, k.val < j ∧ r ≤ C.st k) ∧ S.card + 1 = cnt ∧ mx = S.sup x
  | .wait r j cnt mx => 1 ≤ r ∧ r ≤ 3 ∧ j ≤ n ∧ C.st i = r ∧
      (∃ S : Finset (Fin n), (∀ k ∈ S, k.val < j ∧ r ≤ C.st k) ∧ S.card = cnt) ∧
      ∃ T : Finset (Fin n), mx = T.sup x
  | .chk j cnt mx => j ≤ n ∧ C.st i = 3 ∧
      (∃ S3 : Finset (Fin n), S3.card = n - 1 ∧ ∀ k ∈ S3, C.st k = 3) ∧
      ∃ Cn : Finset (Fin n), (∀ k ∈ Cn, k.val < j ∧ 2 ≤ C.st k) ∧ Cn.card = cnt ∧
        mx = Cn.sup x ∧ ∀ k : Fin n, k.val < j → k ∉ Cn → DoomedR C 3 k
  | .chkIn j cnt mx => C.st i = 3 ∧ ∃ h : j < n, 2 ≤ C.st ⟨j, h⟩ ∧
      (∃ S3 : Finset (Fin n), S3.card = n - 1 ∧ ∀ k ∈ S3, C.st k = 3) ∧
      ∃ Cn : Finset (Fin n), (∀ k ∈ Cn, k.val < j ∧ 2 ≤ C.st k) ∧ Cn.card + 1 = cnt ∧
        mx = Cn.sup x ∧ ∀ k : Fin n, k.val < j → k ∉ Cn → DoomedR C 3 k
  | .fin j mx => j ≤ n ∧ C.st i = 3 ∧ (∀ k, 2 ≤ C.st k) ∧ (∀ k : Fin n, k.val < j → C.st k = 3) ∧
      ∃ T : Finset (Fin n), mx = (T ∪ ltSet j).sup x
  | .finDec j mx b => C.st i = 3 ∧ (∀ k, 2 ≤ C.st k) ∧ ∃ h : j < n,
      (∀ k : Fin n, k.val < j → C.st k = 3) ∧ (b = true → C.st ⟨j, h⟩ = 3) ∧
      ∃ T : Finset (Fin n), mx = (T ∪ ltSet j).sup x
  | .finIn j mx => C.st i = 3 ∧ (∀ k, 2 ≤ C.st k) ∧ ∃ h : j < n,
      (∀ k : Fin n, k.val < j → C.st k = 3) ∧ C.st ⟨j, h⟩ = 3 ∧
      ∃ T : Finset (Fin n), mx = (T ∪ ltSet j).sup x
  | .done v => C.dec.isSome ∧ ∃ t, TagFact C t ∧ v = val x t

/-- The invariant. -/
structure Inv (x : Fin n → ℕ) (C : Cfg n) : Prop where
  li : ∀ i, LIpc x C i (C.pc i)
  le3 : ∀ k, C.st k ≤ 3
  inr : ∀ k, C.pc k ≠ .start → C.inr k = x k
  g3 : ∀ k, 2 ≤ C.st k → n - 1 ≤ cntGE C 1
  dec : ∀ v, C.dec = some v → ∃ t, TagFact C t ∧ v = val x t

/-! ### Counting lemmas -/

@[simp] lemma cntLt_zero (y : Fin n) : cntLt 0 y = 0 := by simp [cntLt]

lemma cntLt_succ (j : ℕ) (y : Fin n) :
    cntLt (j + 1) y = cntLt j y + if h : j < n then (if (⟨j, h⟩ : Fin n) ≠ y then 1 else 0)
      else 0 := by
  unfold cntLt
  split_ifs with h h'
  · have : (univ.filter fun k : Fin n => k.val < j + 1 ∧ k ≠ y) =
        insert ⟨j, h⟩ (univ.filter fun k : Fin n => k.val < j ∧ k ≠ y) := by
      ext k; simp only [mem_filter, mem_univ, true_and, mem_insert]
      constructor
      · rintro ⟨hk, hky⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
        · exact Or.inr ⟨hk, hky⟩
        · exact Or.inl (Fin.ext hk)
      · rintro (rfl | ⟨hk, hky⟩)
        · exact ⟨Nat.lt_succ_self j, h'⟩
        · exact ⟨Nat.lt_succ_of_lt hk, hky⟩
    rw [this, card_insert_of_notMem (by simp)]
  · have hy : (⟨j, h⟩ : Fin n) = y := by simpa using h'
    simp only [add_zero]
    congr 1
    ext k; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hk, hky⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · exact ⟨hk, hky⟩
      · exact absurd (hy ▸ Fin.ext hk) hky
    · rintro ⟨hk, hky⟩; exact ⟨Nat.lt_succ_of_lt hk, hky⟩
  · simp only [add_zero]
    congr 1
    ext k; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hk, hky⟩
      exact ⟨lt_of_lt_of_le k.isLt (Nat.le_of_not_lt h), hky⟩
    · rintro ⟨hk, hky⟩; exact ⟨Nat.lt_succ_of_lt hk, hky⟩

lemma cntLt_of_le {j : ℕ} (hj : n ≤ j) (y : Fin n) : cntLt j y = n - 1 := by
  unfold cntLt
  have : (univ.filter fun k : Fin n => k.val < j ∧ k ≠ y) = univ.erase y := by
    ext k; simp [lt_of_lt_of_le k.isLt hj]
  rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

lemma ltSet_succ {j : ℕ} (h : j < n) : (ltSet (j + 1) : Finset (Fin n)) = insert ⟨j, h⟩ (ltSet j) := by
  ext k; simp only [ltSet, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact Or.inr hk
    · exact Or.inl (Fin.ext hk)
  · rintro (rfl | hk)
    · exact Nat.lt_succ_self j
    · exact Nat.lt_succ_of_lt hk

lemma ltSet_of_le {j : ℕ} (h : n ≤ j) : (ltSet j : Finset (Fin n)) = univ := by
  ext k; simp [ltSet, lt_of_lt_of_le k.isLt h]

lemma cntGE_mono {C C' : Cfg n} (h : ∀ k, C.st k ≤ C'.st k) (r : ℕ) : cntGE C r ≤ cntGE C' r := by
  unfold cntGE
  exact card_le_card (fun k hk => by
    simp only [mem_filter, mem_univ, true_and] at hk ⊢; exact le_trans hk (h k))

/-- A set of `n - 1` processes not containing `y` is everybody but `y`. -/
lemma eq_erase_of_card {S : Finset (Fin n)} {y : Fin n} (hy : y ∉ S) (hS : n - 1 ≤ S.card) :
    S = univ.erase y := by
  apply eq_of_subset_of_card_le
  · intro k hk; simp only [mem_erase, mem_univ, and_true]; rintro rfl; exact hy hk
  · rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]; exact hS

lemma eq_univ_of_card {S : Finset (Fin n)} (hS : n ≤ S.card) : S = univ := by
  apply eq_of_subset_of_card_le (subset_univ _)
  rw [card_univ, Fintype.card_fin]; exact hS

/-! ### Tags -/

/-- Two justified tags are equal (`n ≥ 2`). -/
lemma TagFact.unique (hn : 2 ≤ n) {C : Cfg n} {t t' : Tag n} (h : TagFact C t)
    (h' : TagFact C t') : t = t' := by
  have hex : ∀ y : Fin n, ∃ k, k ≠ y := fun y => by
    by_cases hy : y.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h => hy (by simp [Fin.ext_iff] at h; omega)⟩
  cases t with
  | ex y =>
    cases t' with
    | ex y' =>
      by_contra hne
      have hyy : y ≠ y' := fun e => hne (by rw [e])
      have h1 := h.1 y' (Ne.symm hyy)
      have h2 := h'.1 y hyy
      omega
    | all =>
      obtain ⟨k, hk⟩ := hex y
      have := h.1 k hk
      have h1 := h' y; have h2 := h' k
      omega
  | all =>
    cases t' with
    | ex y =>
      obtain ⟨k, hk⟩ := hex y
      have := h'.1 k hk
      have h1 := h y; have h2 := h k
      omega
    | all => rfl

end Podc.WeakCrashFailures.Fig1
