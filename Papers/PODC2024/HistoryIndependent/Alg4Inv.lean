import Papers.PODC2024.HistoryIndependent.Alg4State
import Mathlib.Data.List.GetD

/-!
# Algorithm 4: the invariant

`Inv v₀ s` is an invariant of the abstract state (with ghost variables) of Algorithm 4,
preserved by every enabled step (`inv_sstep`). It formalizes, as forward invariants:

* the shape of `A` during a `Write` (`memA`, `tagA`), and the values of writes (`lastv`, `pendv`);
* the flag protocol (Lemmas 35, 36): every `1` in `B` is either "covered" by the reader (it will
  be cleared by the pending `Read` in Line 8) or belongs to the writer's window between Lines 13
  and 15 (`bprot`);
* Lemma 11 (`b11`): a `1` in `B` seen by a `Read` was written by a `Write` that had not returned
  when the `Read` was invoked;
* Lemma 34 / Lemma 10 (`h1`–`h4`, `l10`): if both `TryRead`s fail, some `Write` invoked after
  Line 1 executed Line 16 and left a `1` in `B` which stays there until the `Read` scans `B`;
* the reads-from candidate `rf` of the pending `Read` (`rf`, `rfB`) and the floor `fl` given by
  the last completed `Read` (`fl1`–`fl5`), which yield the conditions of the reads-from criterion
  (no read from the future, no overwritten value, no new-old inversion).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

namespace Alg4

variable {K : ℕ} [NeZero K]

/-! ### Auxiliary predicates on program counters -/

/-- The reader is in a `TryRead` or in Lines 5-6. -/
def RPC.active : RPC K → Prop
  | .up .. | .down .. | .bscan .. => True
  | _ => False

/-- Expected value of `flag[1]`. -/
def RPC.f1v : RPC K → Bool
  | .up .. | .down .. | .bscan .. | .setF2 _ | .clr .. | .resF1 _ => true
  | _ => false

/-- Expected value of `flag[2]`. -/
def RPC.f2v : RPC K → Bool
  | .clr .. | .resF1 _ | .resF2 _ => true
  | _ => false

/-- The reader's current `val` (`none` before the first assignment). -/
def RPC.val? : RPC K → Option (Fin K)
  | .down val _ => some val
  | .bscan _ val | .setF2 val | .clr _ val | .resF1 val | .resF2 val | .done val => val
  | _ => none

/-- The reader is at Line 7 or later. -/
def RPC.late : RPC K → Prop
  | .setF2 _ | .clr .. | .resF1 _ | .resF2 _ | .done _ => True
  | _ => False

/-- The reader is at Line 9 or later (done clearing `B`). -/
def RPC.fin : RPC K → Prop
  | .resF1 _ | .resF2 _ | .done _ => True
  | _ => False

/-- The reader will clear `B[x]` before returning. -/
def RPC.cov (x : Fin K) : RPC K → Prop
  | .up .. | .down .. | .bscan .. | .setF2 _ => True
  | .clr j _ => j ≤ x
  | _ => False

/-- The reader states possible while the writer is at the second read of Line 14 with
`B[x] = 1` written in Line 13. -/
def RPC.s1 (x : Fin K) : RPC K → Prop
  | .resF1 _ | .resF2 _ => False
  | .clr j _ => j ≤ x
  | _ => True

/-- Lower bound of the cells already scanned downwards. -/
def RPC.dlow (x : Fin K) : RPC K → Prop
  | .down _ j => j < x
  | _ => True

/-- The value of the pending `Write`. -/
def WPC.val? : WPC K → Option (Fin K)
  | .idle => none
  | .scanB v _ | .rdF1 v | .setB v | .rdF2 v | .rdF1' v | .clrB v | .setA v | .down v _
  | .up v _ | .done v => some v

/-- The value written to `A` in Line 16, after Line 16. -/
def WPC.newv : WPC K → Option (Fin K)
  | .down v _ | .up v _ | .done v => some v
  | _ => none

/-- The cells holding the previous value's `1` (not yet cleared). -/
def WPC.old (last x : Fin K) : WPC K → Prop
  | .down v j => x = last ∧ (x ≤ j ∨ v < x)
  | .up _ j => x = last ∧ j ≤ x
  | .done _ => False
  | _ => x = last

/-- Well-formedness of the loop indices. -/
def WPC.wf : WPC K → Prop
  | .down v j => j < v
  | .up v j => v < j
  | _ => True

/-- The writer is not between Lines 12 and 15. -/
def WPC.noWin : WPC K → Prop
  | .rdF1 _ | .setB _ | .rdF2 _ | .rdF1' _ | .clrB _ => False
  | _ => True

/-- The writer is at Line 14 (first read) or Line 15. -/
def WPC.win : WPC K → Prop
  | .rdF2 _ | .clrB _ => True
  | _ => False

/-- The writer is at Line 14 (second read). -/
def WPC.win' : WPC K → Prop
  | .rdF1' _ => True
  | _ => False

variable (v₀ : Fin K)

/-- **The invariant.** -/
structure Inv (s : St K) : Prop where
  -- the writer and `A`
  wf : s.wpc.wf
  pendv : ∀ v, s.wpc.val? = some v → v = s.vals v₀ s.n ∧ 1 ≤ s.n
  lastv : s.last = s.vals v₀ s.c
  memA : ∀ x, s.A x = true ↔ (s.wpc.newv = some x ∨ s.wpc.old s.last x)
  tagA : ∀ x, s.A x = true → s.tagA x = if s.wpc.newv = some x then s.n else s.c
  -- flags
  f1 : s.f1 = s.rpc.f1v
  f2 : s.f2 = s.rpc.f2v
  -- `B`
  scan : ∀ v j, s.wpc = .scanB v j → ∀ x, x < j → s.Bm x = false
  scan' : ∀ v, s.wpc = .rdF1 v ∨ s.wpc = .setB v → ∀ x, s.Bm x = false
  bprot : ∀ x, s.Bm x = true → s.rpc.cov x ∨
    (x = s.last ∧ s.tagB x = s.n ∧ (s.wpc.win ∨ (s.wpc.win' ∧ s.rpc.s1 x)))
  bval : ∀ x, s.Bm x = true → 1 ≤ s.tagB x ∧ s.tagB x ≤ s.n ∧ x = s.vals v₀ (s.tagB x - 1)
  -- Lemma 11
  b11 : s.rpc ≠ .idle → ∀ x, s.Bm x = true → s.lo < s.tagB x
  lo : s.rpc ≠ .idle → s.lo ≤ s.c
  -- Lemma 10 (with the weak form of Lemma 34)
  h1 : s.rpc.active → s.sN1 < s.nA → ∃ x, s.Bm x = true ∧ s.wpc.noWin ∧
    (∀ v j, s.wpc = .scanB v j → j ≤ x) ∧ (∀ j, s.rpc = .bscan j none → j ≤ x)
  h2 : s.rpc.active → s.sN1 < s.n →
    (∀ v, s.wpc = .rdF2 v ∨ s.wpc = .rdF1' v → s.Bm s.last = true) ∧
    (∀ v, s.wpc ≠ .clrB v) ∧ (∀ v, s.wpc = .setA v → ∃ x, s.Bm x = true)
  h3 : ∀ b j, s.rpc = .up b j → s.nA = s.sT → j ≤ s.vals v₀ s.nA
  h4 : ∀ j, s.rpc = .up false j → s.sN1 ≤ s.sT + 1 ∧ s.sT ≤ s.nA
  h4' : ∀ j, s.rpc = .up true j → s.sN1 ≤ s.sT ∧ s.sT ≤ s.nA
  h4'' : ∀ j, s.rpc = .bscan j none → s.sN1 < s.nA
  l10 : s.rpc.late → s.rpc.val?.isSome
  rwf : ∀ val j, s.rpc = .down val j → j < val
  -- the reads-from candidate of the pending `Read`
  rf : ∀ v, s.rpc.val? = some v → v = s.vals v₀ s.rf ∧ s.rf ≤ s.nA ∧ s.lo ≤ s.rf ∧
    s.fl ≤ s.rf ∧ (s.rf ≤ s.c ∨ (s.n = s.rf ∧ s.wpc.postA ∧
      ∀ x, x < v → s.rpc.dlow x → s.A x = true → s.rf ≤ s.tagA x))
  rfB : ∀ j val, s.rpc = .clr j val → ∀ x, x < j → s.Bm x = true → s.rf < s.tagB x
  rfB' : s.rpc.fin → ∀ x, s.Bm x = true → s.rf < s.tagB x
  -- the floor: reads-from value of the last completed `Read`
  fl1 : s.fl ≤ s.nA
  fl2 : ∀ x, s.Bm x = true → s.fl < s.tagB x
  fl3 : s.fl ≤ s.c ∨
    (s.n = s.fl ∧ s.wpc.postA ∧ ∀ x, x < s.vals v₀ s.fl → s.A x = true → s.fl ≤ s.tagA x)
  fl4 : ∀ b j, s.rpc = .up b j → s.fl ≤ s.c ∨ j ≤ s.vals v₀ s.fl
  fl5 : ∀ val j, s.rpc = .down val j → s.fl ≤ s.c ∨ val ≤ s.vals v₀ s.fl
  -- completed reads
  pis1 : ∀ p ∈ s.pis, p ≤ s.fl
  pis2 : s.pis.Pairwise (· ≤ ·)

lemma inv_init : Inv v₀ (St.init v₀) where
  wf := trivial
  pendv v h := by simp [St.init, WPC.val?] at h
  lastv := rfl
  memA x := by simp [St.init, WPC.newv, WPC.old]
  tagA x _ := by simp [St.init, WPC.newv, St.c, St.n]
  f1 := rfl
  f2 := rfl
  scan v j h := by simp [St.init] at h
  scan' v h := by simp [St.init] at h
  bprot x h := by simp [St.init] at h
  bval x h := by simp [St.init] at h
  b11 h := by simp [St.init] at h
  lo h := by simp [St.init] at h
  h1 h := by simp [St.init, RPC.active] at h
  h2 h := by simp [St.init, RPC.active] at h
  h3 b j h := by simp [St.init] at h
  h4 j h := by simp [St.init] at h
  h4' j h := by simp [St.init] at h
  h4'' j h := by simp [St.init] at h
  l10 h := by simp [St.init, RPC.late] at h
  rwf val j h := by simp [St.init] at h
  rf v h := by simp [St.init, RPC.val?] at h
  rfB j val h := by simp [St.init] at h
  rfB' h := by simp [St.init, RPC.fin] at h
  fl1 := Nat.zero_le _
  fl2 x h := by simp [St.init] at h
  fl3 := Or.inl (Nat.zero_le _)
  fl4 b j h := by simp [St.init] at h
  fl5 val j h := by simp [St.init] at h
  pis1 p h := by simp [St.init] at h
  pis2 := List.Pairwise.nil

/-! ### Basic facts -/

namespace St

lemma c_le_nA (s : St K) : s.c ≤ s.nA := by
  unfold St.c St.nA; split_ifs with h1 h2 <;> simp_all [WPC.preA]

lemma nA_le_n (s : St K) : s.nA ≤ s.n := by
  unfold St.nA; split_ifs <;> omega

lemma n_le_c (s : St K) : s.n ≤ s.c + 1 := by
  unfold St.c; split_ifs <;> omega

lemma vals_append (s : St K) (v : Fin K) {m : ℕ} (hm : m ≤ s.n) :
    St.vals v₀ { s with wv := s.wv ++ [v] } m = s.vals v₀ m := by
  simp only [St.vals]
  rw [← List.cons_append, List.getD_append _ _ _ _ (by simp only [St.n] at hm; simp; omega)]

lemma vals_append_last (s : St K) (v : Fin K) :
    St.vals v₀ { s with wv := s.wv ++ [v] } (s.n + 1) = v := by
  simp [St.vals, St.n]

end St

lemma WPC.old_eq {w : WPC K} {last x : Fin K} (h : w.old last x) : x = last := by
  cases w <;> simp_all [WPC.old]

lemma WPC.newv_eq {w : WPC K} {x : Fin K} (h : w.newv = some x) :
    w.postA ∧ w.val? = some x := by
  cases w <;> simp_all [WPC.newv, WPC.postA, WPC.val?]

namespace Inv

variable {v₀} {s : St K} (hI : Inv v₀ s)
include hI

/-- Ones in `A`: tags are between `c` and `nA`, and the value of the tag is the index. -/
lemma A_one {x : Fin K} (hx : s.A x = true) :
    s.c ≤ s.tagA x ∧ s.tagA x ≤ s.nA ∧ s.vals v₀ (s.tagA x) = x := by
  have ht := hI.tagA x hx
  by_cases h : s.wpc.newv = some x
  · obtain ⟨hp, hv⟩ := WPC.newv_eq h
    simp only [h, ↓reduceIte] at ht
    have hn : s.nA = s.n := by simp [St.nA]; cases hw : s.wpc <;> simp_all [WPC.postA, WPC.preA]
    refine ⟨ht ▸ (s.c_le_nA.trans_eq hn), by omega, ?_⟩
    rw [ht]; exact ((hI.pendv x hv).1).symm
  · have h' := WPC.old_eq (((hI.memA x).1 hx).resolve_left h)
    simp only [h, ↓reduceIte] at ht
    refine ⟨ht.ge, ht ▸ s.c_le_nA, ?_⟩
    rw [ht, ← hI.lastv, h']

/-- The cell of the current value holds `1`. -/
lemma A_cur : s.A (s.vals v₀ s.nA) = true := by
  rw [hI.memA]
  cases hw : s.wpc with
  | idle => right; simp [WPC.old, St.nA, St.c, hw, WPC.preA, hI.lastv] at *
  | down v j =>
    left; have := (hI.pendv v (by simp [hw, WPC.val?])).1
    simp [WPC.newv, St.nA, hw, WPC.preA, this]
  | up v j =>
    left; have := (hI.pendv v (by simp [hw, WPC.val?])).1
    simp [WPC.newv, St.nA, hw, WPC.preA, this]
  | done v =>
    left; have := (hI.pendv v (by simp [hw, WPC.val?])).1
    simp [WPC.newv, St.nA, hw, WPC.preA, this]
  | _ => right; simp [WPC.old, St.nA, St.c, hw, WPC.preA, hI.lastv]

lemma postA_newv (hp : s.wpc.postA) : s.wpc.newv = some (s.vals v₀ s.n) := by
  cases hw : s.wpc <;> simp_all [WPC.postA, WPC.newv] <;>
    exact (hI.pendv _ (by simp [hw, WPC.val?])).1

lemma postA_nA (hp : s.wpc.postA) : s.nA = s.n := by
  cases hw : s.wpc <;> simp_all [WPC.postA, St.nA, WPC.preA]

lemma pend_n (hw : s.wpc ≠ .idle) : 1 ≤ s.n := by
  obtain ⟨v, hv⟩ : ∃ v, s.wpc.val? = some v := by
    cases h : s.wpc <;> simp_all [WPC.val?]
  exact (hI.pendv v hv).2

lemma pend_c (hw : s.wpc ≠ .idle) : s.c + 1 = s.n := by
  have := hI.pend_n hw; simp [St.c, hw]; omega

/-- The reads-from candidate after reading `A[j] = 1`. -/
lemma rf_A {j : Fin K} (hA : s.A j = true) (hfl : s.fl ≤ s.c ∨ j ≤ s.vals v₀ s.fl)
    (hr : s.rpc ≠ .idle) :
    j = s.vals v₀ (s.tagA j) ∧ s.tagA j ≤ s.nA ∧ s.lo ≤ s.tagA j ∧ s.fl ≤ s.tagA j ∧
      (s.tagA j ≤ s.c ∨ (s.n = s.tagA j ∧ s.wpc.postA)) := by
  obtain ⟨h1, h2, h3⟩ := hI.A_one hA
  have ht := hI.tagA j hA
  refine ⟨h3.symm, h2, (hI.lo hr).trans h1, ?_, ?_⟩
  · rcases hI.fl3 with h | ⟨hn, hp, hlow⟩
    · exact h.trans h1
    · rcases hfl with h | h
      · exact h.trans h1
      · rcases lt_or_eq_of_le h with h | h
        · exact hlow j h hA
        · rw [h, ← hn] at ht ⊢
          rw [hI.postA_newv hp] at ht
          simp at ht; omega
  · by_cases hv : s.wpc.newv = some j
    · simp only [hv, ↓reduceIte] at ht
      exact Or.inr ⟨ht.symm, (WPC.newv_eq hv).1⟩
    · simp only [hv, ↓reduceIte] at ht
      exact Or.inl ht.le

end Inv

lemma WPC.afterSetA_spec (v : Fin K) :
    (0 < v.val ∧ ∃ h : v.val - 1 < K, WPC.afterSetA v = .down v ⟨v.val - 1, h⟩) ∨
    (v.val = 0 ∧ ∃ h : 1 < K, WPC.afterSetA v = .up v ⟨1, h⟩) ∨
    (v.val = 0 ∧ K = 1 ∧ WPC.afterSetA v = .done v) := by
  unfold WPC.afterSetA WPC.upFrom
  by_cases h : v.val = 0
  · by_cases h' : 1 < K
    · exact Or.inr (Or.inl ⟨h, h', by simp [h, h']⟩)
    · have := v.isLt
      exact Or.inr (Or.inr ⟨h, by omega, by simp [h, h']⟩)
  · exact Or.inl ⟨by omega, by omega, by simp [h]⟩

lemma WPC.downNext_spec (v j : Fin K) :
    (0 < j.val ∧ ∃ h : j.val - 1 < K, WPC.downNext v j = .down v ⟨j.val - 1, h⟩) ∨
    (j.val = 0 ∧ ∃ h : v.val + 1 < K, WPC.downNext v j = .up v ⟨v.val + 1, h⟩) ∨
    (j.val = 0 ∧ v.val + 1 = K ∧ WPC.downNext v j = .done v) := by
  unfold WPC.downNext WPC.upFrom
  by_cases h : j.val = 0
  · by_cases h' : v.val + 1 < K
    · exact Or.inr (Or.inl ⟨h, h', by simp [h, h']⟩)
    · have := v.isLt
      exact Or.inr (Or.inr ⟨h, by omega, by simp [h, h']⟩)
  · exact Or.inl ⟨by omega, by omega, by simp [h]⟩

lemma WPC.upNext_spec (v j : Fin K) :
    (∃ h : j.val + 1 < K, WPC.upNext v j = .up v ⟨j.val + 1, h⟩) ∨
    (j.val + 1 = K ∧ WPC.upNext v j = .done v) := by
  unfold WPC.upNext WPC.upFrom
  by_cases h : j.val + 1 < K
  · exact Or.inl ⟨h, by simp [h]⟩
  · have := j.isLt
    exact Or.inr ⟨by omega, by simp [h]⟩

lemma RPC.found_spec (j : Fin K) :
    (j.val = 0 ∧ RPC.found j = .setF2 (some j)) ∨
      (∃ h : j.val - 1 < K, 0 < j.val ∧ RPC.found j = .down j ⟨j.val - 1, h⟩) := by
  unfold RPC.found
  by_cases h : j.val = 0
  · exact Or.inl ⟨h, by simp [h]⟩
  · exact Or.inr ⟨by omega, by omega, by simp [h]⟩

lemma RPC.downNext_spec (val j : Fin K) (b : Bool) :
    (j.val = 0 ∧ RPC.downNext val j b = .setF2 (some (if b then j else val))) ∨
      (∃ h : j.val - 1 < K, 0 < j.val ∧
        RPC.downNext val j b = .down (if b then j else val) ⟨j.val - 1, h⟩) := by
  unfold RPC.downNext
  by_cases h : j.val = 0
  · exact Or.inl ⟨h, by simp [h]⟩
  · exact Or.inr ⟨by omega, by omega, by simp [h]⟩

lemma RPC.bscanNext_spec (j : Fin K) (val : Option (Fin K)) (b : Bool) :
    (j.val + 1 = K ∧ RPC.bscanNext j val b = .setF2 (if b then some j else val)) ∨
      (∃ h : j.val + 1 < K,
        RPC.bscanNext j val b = .bscan ⟨j.val + 1, h⟩ (if b then some j else val)) := by
  unfold RPC.bscanNext
  by_cases h : j.val + 1 < K
  · exact Or.inr ⟨h, by simp [h]⟩
  · exact Or.inl ⟨by omega, by simp [h]⟩

lemma RPC.clrNext_spec (j : Fin K) (val : Option (Fin K)) :
    (j.val + 1 = K ∧ RPC.clrNext j val = .resF1 val) ∨
      (∃ h : j.val + 1 < K, RPC.clrNext j val = .clr ⟨j.val + 1, h⟩ val) := by
  unfold RPC.clrNext
  by_cases h : j.val + 1 < K
  · exact Or.inr ⟨h, by simp [h]⟩
  · exact Or.inl ⟨by omega, by simp [h]⟩

end Alg4

end Cslib.SharedMemory
