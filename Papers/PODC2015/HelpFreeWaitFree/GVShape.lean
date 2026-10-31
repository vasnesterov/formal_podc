import Papers.PODC2015.HelpFreeWaitFree.GVDefs
import Papers.PODC2015.HelpFreeWaitFree.Shape

/-!
# The shape of a linearization in the proof of Theorem 4.8

Combinatorial core of the result arguments of Section 4.6 of [CPT15]. In the setting of the proof
(process `p₁` runs `op`, `p₂` runs the modifiers `M`, `p₃` runs the views `V`), consider a
sequential history `S` (a linearization) and the view `x = (p₃, l)`. Suppose that the entries of `S`
up to `x` are `op₁ = (p₁, 0)`, modifiers `(p₂, k)` with `k ≤ i` and views `(p₃, k)` with `k ≤ l`
(with their operations), the first `i` modifiers and the views before `x` come before `x`, and
both sequences are in program order. Then the prefix of `S` up to `x` is a history of
`gvSet i (l+1) o m` (Definition 4.6.16), where `o`, resp. `m`, says whether `op₁`, resp.
`(p₂, i)`, precedes `x` in `S` (`gv_shape`), and its last result is the response of `x` if `S` is
legal (`gv_lastResult`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- The tag of an instance in the proof of Theorem 4.8: instances of `p₁` are `op`, instances of
`p₂` are modifiers, all others are views. -/
def gvTagOf (p₁ p₂ : P) (y : OpId P) : GVTag :=
  if y.1 = p₁ then .op else if y.1 = p₂ then .mod y.2 else .view y.2

lemma lastResult_append_singleton (os : List A.Op) (o : A.Op) :
    lastResult A (os ++ [o]) = some (A.δ (A.runOps A.init os) o).2 := by
  simp [lastResult]

/-- Legality of a sequential history, read at one entry. -/
lemma seqOK_resp {α : List (Label P A)} {y : OpId P} {o : A.Op} {r : A.Resp}
    {S₂ : List (OpId P × A.Op)} : ∀ {q : A.State} (S₁ : List (OpId P × A.Op)),
    SeqOK α q (S₁ ++ (y, o) :: S₂) → respOf α y = some r →
    (A.δ (A.runOps q (S₁.map Prod.snd)) o).2 = r
  | _, [], h, hr => h.1 _ hr
  | _, (_, _) :: S₁, h, hr => by simpa using seqOK_resp S₁ h.2 hr

lemma getElem_pos_fst {S : List (OpId P × A.Op)} {x : OpId P} (h : pos S x < S.length) : (S[pos S x]'h).1 = x := by
  have h' : pos S x < (S.map Prod.fst).length := by simpa using h
  have e1 := List.getElem_idxOf h'
  have e2 : (S.map Prod.fst)[pos S x]'h' = (S[pos S x]'h).1 := List.getElem_map ..
  exact e2.symm.trans e1

/-- The last result of the prefix of a legal sequential history ending at the entry `k` is the
response of that entry. -/
theorem gv_lastResult {α : List (Label P A)} {S : List (OpId P × A.Op)} (p₁ p₂ : P)
    (op : A.Op) (M V : ℕ → A.Op) (hseq : SeqOK α A.init S) {k : ℕ} (hk : k < S.length)
    (hop : ∀ e ∈ S.take (k + 1), e.2 = (gvTagOf p₁ p₂ e.1).toOp op M V) {r : A.Resp}
    (hr : respOf α (S[k]'hk).1 = some r) :
    lastResult A (((S.take (k + 1)).map (gvTagOf p₁ p₂ ∘ Prod.fst)).map (GVTag.toOp op M V)) =
      some r := by
  have h1 : ((S.take (k + 1)).map (gvTagOf p₁ p₂ ∘ Prod.fst)).map (GVTag.toOp op M V) =
      (S.take (k + 1)).map Prod.snd := by
    rw [List.map_map]
    exact List.map_congr_left (fun e he => (hop e he).symm)
  have h2 : S.take (k + 1) = S.take k ++ [S[k]'hk] := List.take_succ_eq_append_getElem hk
  rw [h1, h2, List.map_append, List.map_singleton, lastResult_append_singleton]
  congr 1
  have hsplit : S = S.take k ++ ((S[k]'hk).1, (S[k]'hk).2) :: S.drop (k + 1) := by
    simp [List.getElem_cons_drop]
  rw [hsplit] at hseq
  exact seqOK_resp _ hseq hr

/-- **Shape of a linearization** (core of the result arguments of Section 4.6). -/
theorem gv_shape (S : List (OpId P × A.Op)) (p₁ p₂ p₃ : P) (op : A.Op) (M V : ℕ → A.Op)
    (i l : ℕ) (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (hnd : (S.map Prod.fst).Nodup)
    (hx : ((p₃, l) : OpId P) ∈ S.map Prod.fst)
    (hknown : ∀ e ∈ S, pos S e.1 ≤ pos S (p₃, l) →
      e.1 = (p₁, 0) ∨ (e.1.1 = p₂ ∧ e.1.2 ≤ i) ∨ (e.1.1 = p₃ ∧ e.1.2 ≤ l))
    (hop : ∀ e ∈ S, pos S e.1 ≤ pos S (p₃, l) → e.2 = (gvTagOf p₁ p₂ e.1).toOp op M V)
    (hM : ∀ k < i, pos S (p₂, k) < pos S (p₃, l))
    (hV : ∀ k < l, pos S (p₃, k) < pos S (p₃, l))
    (hMM : ∀ k k', k < k' → k' ≤ i → ((p₂, k') : OpId P) ∈ S.map Prod.fst →
      pos S (p₂, k) < pos S (p₂, k'))
    (hVV : ∀ k k', k < k' → k' ≤ l → pos S (p₃, k) < pos S (p₃, k')) :
    (S.take (pos S (p₃, l) + 1)).map (gvTagOf p₁ p₂ ∘ Prod.fst) ∈
      gvSet i (l + 1) (decide (pos S (p₁, 0) < pos S (p₃, l)))
        (decide (pos S (p₂, i) < pos S (p₃, l))) := by
  classical
  set x : OpId P := (p₃, l) with hxdef
  set n := pos S x with hn
  set S' := S.take (n + 1) with hS'
  have hnlen : n < S.length := pos_lt_length_iff.2 hx
  have hmemS' : ∀ {e}, e ∈ S' ↔ e ∈ S ∧ pos S e.1 ≤ n := by
    intro e; rw [hS', mem_take_iff hnd, Nat.lt_succ_iff]
  have hsub : S'.Sublist S := List.take_sublist _ _
  -- an instance before `x` has an entry in `S'`
  have hentry : ∀ y : OpId P, pos S y ≤ n → ∃ e ∈ S', e.1 = y := by
    intro y hy
    have hy' : y ∈ S.map Prod.fst := pos_lt_length_iff.1 (lt_of_le_of_lt hy hnlen)
    obtain ⟨e, he, rfl⟩ := exists_entry hy'
    exact ⟨e, hmemS'.2 ⟨he, hy⟩, rfl⟩
  have hmem_lt : ∀ y : OpId P, pos S y < n → y ∈ S.map Prod.fst := fun y hy =>
    pos_lt_length_iff.1 (lt_trans hy hnlen)
  have hkn : ∀ e ∈ S', e.1 = (p₁, 0) ∨ (e.1.1 = p₂ ∧ e.1.2 ≤ i) ∨ (e.1.1 = p₃ ∧ e.1.2 ≤ l) :=
    fun e he => hknown e (hmemS'.1 he).1 (hmemS'.1 he).2
  have hop' : ∀ e ∈ S', e.2 = (gvTagOf p₁ p₂ e.1).toOp op M V :=
    fun e he => hop e (hmemS'.1 he).1 (hmemS'.1 he).2
  -- tags
  have tag1 : ∀ k, gvTagOf p₁ p₂ ((p₁, k) : OpId P) = .op := fun k => by simp [gvTagOf]
  have tag2 : ∀ k, gvTagOf p₁ p₂ ((p₂, k) : OpId P) = .mod k := fun k => by
    simp [gvTagOf, Ne.symm h12]
  have tag3 : ∀ k, gvTagOf p₁ p₂ ((p₃, k) : OpId P) = .view k := fun k => by
    simp [gvTagOf, Ne.symm h13, Ne.symm h23]
  -- the three filters
  have fMod : ∀ e : OpId P × A.Op, (gvTagOf p₁ p₂ e.1).isMod = decide (e.1.1 = p₂) := by
    intro e
    by_cases h1 : e.1.1 = p₁
    · simp [gvTagOf, h1, h12]
    · by_cases h2 : e.1.1 = p₂ <;> simp [gvTagOf, h1, h2, Ne.symm h12]
  have fOp : ∀ e : OpId P × A.Op, (gvTagOf p₁ p₂ e.1).isOp = decide (e.1.1 = p₁) := by
    intro e
    by_cases h1 : e.1.1 = p₁
    · simp [gvTagOf, h1]
    · by_cases h2 : e.1.1 = p₂ <;> simp [gvTagOf, h1, h2, Ne.symm h12]
  have fView : ∀ e ∈ S', (gvTagOf p₁ p₂ e.1).isView = decide (e.1.1 = p₃) := by
    intro e he
    rcases hkn e he with h | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h, tag1]; simp [h13]
    · obtain ⟨⟨q, k⟩, o⟩ := e; simp only at h; subst h; rw [tag2]; simp [h23]
    · obtain ⟨⟨q, k⟩, o⟩ := e; simp only at h; subst h; rw [tag3]; simp
  -- modifiers
  have hModL : S'.filter (fun e => decide (e.1.1 = p₂)) =
      (List.range (i + (decide (pos S (p₂, i) < n)).toNat)).map
        (fun k => (((p₂, k) : OpId P), M k)) := by
    apply eq_range_of_sublist hnd (List.filter_sublist.trans hsub) p₂ _ M
    · intro e he; simpa using (List.mem_filter.1 he).2
    · intro e he
      have he2 : e.1.1 = p₂ := by simpa using (List.mem_filter.1 he).2
      have he' := (List.mem_filter.1 he).1
      rcases hkn e he' with h | ⟨-, h⟩ | ⟨h, -⟩
      · rw [h] at he2; exact absurd he2 h12
      · rcases h.lt_or_eq with h | h
        · have := Nat.zero_le (decide (pos S (p₂, i) < n)).toNat; omega
        · have he1 : e.1 = (p₂, i) := Prod.ext he2 h
          have hP : pos S (p₂, i) < n := by
            rw [← he1]
            refine lt_of_le_of_ne (hmemS'.1 he').2 (fun e' => ?_)
            have := List.idxOf_inj (pos_lt_length_iff.1 (e' ▸ hnlen)) |>.1 e'
            rw [he1] at this; exact h23 (Prod.ext_iff.1 this).1
          simp [hP]; omega
      · rw [h] at he2; exact absurd he2 h23.symm
    · intro k hk
      have hpos : pos S (p₂, k) < n := by
        rcases Nat.lt_or_ge k i with h | h
        · exact hM k h
        · by_cases hP : pos S (p₂, i) < n
          · simp [hP] at hk
            rw [show k = i by omega]; exact hP
          · simp [hP] at hk; omega
      obtain ⟨e, he, he1⟩ := hentry _ hpos.le
      exact ⟨e, List.mem_filter.2 ⟨he, by simp [he1]⟩, he1⟩
    · intro k k' hkk hk'
      by_cases hP : pos S (p₂, i) < n
      · simp [hP] at hk'
        apply hMM k k' hkk (by omega)
        rcases Nat.lt_or_ge k' i with h | h
        · exact hmem_lt _ (hM k' h)
        · rw [show k' = i by omega]; exact hmem_lt _ hP
      · simp [hP] at hk'
        exact hMM k k' hkk hk'.le (hmem_lt _ (hM k' hk'))
    · intro e he
      have he2 : e.1.1 = p₂ := by simpa using (List.mem_filter.1 he).2
      rw [hop' e (List.mem_filter.1 he).1]
      obtain ⟨⟨q, k⟩, o⟩ := e; simp only at he2; subst he2; rw [tag2]; rfl
  -- views
  have hViewL : S'.filter (fun e => decide (e.1.1 = p₃)) =
      (List.range (l + 1)).map (fun k => (((p₃, k) : OpId P), V k)) := by
    apply eq_range_of_sublist hnd (List.filter_sublist.trans hsub) p₃ (l + 1) V
    · intro e he; simpa using (List.mem_filter.1 he).2
    · intro e he
      have he3 : e.1.1 = p₃ := by simpa using (List.mem_filter.1 he).2
      rcases hkn e (List.mem_filter.1 he).1 with h | ⟨h, -⟩ | ⟨-, h⟩
      · rw [h] at he3; exact absurd he3 h13
      · rw [h] at he3; exact absurd he3 h23
      · omega
    · intro k hk
      have hpos : pos S (p₃, k) ≤ n := by
        rcases Nat.lt_or_ge k l with h | h
        · exact (hV k h).le
        · have : k = l := by omega
          rw [this]
      obtain ⟨e, he, he1⟩ := hentry _ hpos
      exact ⟨e, List.mem_filter.2 ⟨he, by simp [he1]⟩, he1⟩
    · intro k k' hkk hk'; exact hVV k k' hkk (by omega)
    · intro e he
      have he3 : e.1.1 = p₃ := by simpa using (List.mem_filter.1 he).2
      rw [hop' e (List.mem_filter.1 he).1]
      obtain ⟨⟨q, k⟩, o⟩ := e; simp only at he3; subst he3; rw [tag3]; rfl
  -- `op₁`
  have hOpL : S'.filter (fun e => decide (e.1.1 = p₁)) =
      (List.range (decide (pos S (p₁, 0) < n)).toNat).map (fun k => (((p₁, k) : OpId P), op)) := by
    apply eq_range_of_sublist hnd (List.filter_sublist.trans hsub) p₁ _ (fun _ => op)
    · intro e he; simpa using (List.mem_filter.1 he).2
    · intro e he
      have he1 : e.1.1 = p₁ := by simpa using (List.mem_filter.1 he).2
      have he' := (List.mem_filter.1 he).1
      rcases hkn e he' with h | ⟨h, -⟩ | ⟨h, -⟩
      · have hP : pos S (p₁, 0) < n := by
          rw [← h]
          refine lt_of_le_of_ne (hmemS'.1 he').2 (fun e' => ?_)
          have := List.idxOf_inj (pos_lt_length_iff.1 (e' ▸ hnlen)) |>.1 e'
          rw [h] at this; exact h13 (Prod.ext_iff.1 this).1
        rw [h]; simp [hP]
      · rw [h] at he1; exact absurd he1.symm h12
      · rw [h] at he1; exact absurd he1.symm h13
    · intro k hk
      by_cases hP : pos S (p₁, 0) < n
      · simp [hP] at hk
        obtain ⟨e, he, he1⟩ := hentry _ hP.le
        exact ⟨e, List.mem_filter.2 ⟨he, by simp [he1]⟩, by rw [he1, hk]⟩
      · simp [hP] at hk
    · intro k k' hkk hk'
      by_cases hP : pos S (p₁, 0) < n <;> simp [hP] at hk'; omega
    · intro e he
      have he1 : e.1.1 = p₁ := by simpa using (List.mem_filter.1 he).2
      rw [hop' e (List.mem_filter.1 he).1]
      obtain ⟨⟨q, k⟩, o⟩ := e; simp only at he1; subst he1; rw [tag1]; rfl
  have hlast : (S[n]'hnlen).1 = x := getElem_pos_fst hnlen
  refine ⟨?_, ?_, ?_, l, ?_⟩
  · rw [List.filter_map, List.filter_congr (fun e _ => by simpa using fMod e), hModL]
    simp [List.map_map, Function.comp_def, tag2]
  · rw [List.filter_map, List.filter_congr (fun e he => by simpa using fView e he), hViewL]
    simp [List.map_map, Function.comp_def, tag3]
  · rw [List.filter_map, List.filter_congr (fun e _ => by simpa using fOp e), hOpL]
    by_cases hP : pos S (p₁, 0) < n <;> simp [hP, tag1]
  · rw [List.getLast?_map, hS', List.getLast?_take]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.getElem?_eq_getElem hnlen,
      Option.some_or, Option.map_some, Function.comp_apply, hlast, hxdef, tag3]

end Podc.HelpFreeWaitFree
