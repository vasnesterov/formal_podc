import Papers.PODC2023.DuraCAS.AGlob

/-!
# Extending the keyed linearization

`lgood_append` (an entry linearized at the current step), `lgood_insert_fcas` (a `CAS` that
returns `false` at line 11, inserted retroactively after its witness step, Definition A.43.2) and
`lgood_insert_hh` (a hitchhiking write, inserted retroactively just before the installing write
moved at its witness step, Definition A.42.3).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem lgood_append {init : K → V} {L : List (GE K V)} {clk : ℕ} (hL : LGood init L clk)
    (x : GE K V) (hkey : x.key = 4 * clk + 1) (hid : x.id ∉ L.map GE.id)
    (hrsp : (seqStep (curSt init L) x.k x.op).2 = x.rsp) : LGood init (L ++ [x]) (clk + 1) := by
  have hlt := hL.key_lt
  refine ⟨kSorted_append_one hL.sorted (fun a ha => by have := hlt a ha; omega), ?_, ?_,
    respOK_append_one hL.resp hrsp, ?_, ?_⟩
  · rw [List.map_append, List.nodup_append]
    exact ⟨hL.nodup, by simp, by simp; intro a ha he; exact hid (he ▸ List.mem_map_of_mem ha)⟩
  · intro e he
    rcases List.mem_append.1 he with he | he
    · have := hlt e he; omega
    · simp at he; subst he; omega
  · intro e he h0
    rcases List.mem_append.1 he with he | he
    · obtain ⟨hw, y, hy, hy'⟩ := hL.rank0 e he h0
      exact ⟨hw, y, List.mem_append_left _ hy, hy'⟩
    · simp at he; subst he; omega
  · intro e he e' he' hk h1
    rcases List.mem_append.1 he with h2 | h2 <;> rcases List.mem_append.1 he' with h3 | h3
    · exact hL.rank1 e h2 e' h3 hk h1
    · simp at h3; subst h3; have := hlt e h2; omega
    · simp at h2; subst h2; have := hlt e' h3; omega
    · simp at h2 h3; rw [h2, h3]

theorem stAt_append_lt {init : K → V} {L : List (GE K V)} {clk : ℕ} (x : GE K V)
    (hkey : x.key = 4 * clk + 1) (t : ℕ) (ht : t < clk) :
    stAt init (L ++ [x]) t = stAt init L t :=
  stAt_append_one init L x t (by omega)

theorem nodup_insert_id {A B : List (GE K V)} {x : GE K V} (h : ((A ++ B).map GE.id).Nodup)
    (hx : x.id ∉ (A ++ B).map GE.id) : ((A ++ x :: B).map GE.id).Nodup := by
  have : ((A ++ x :: B).map GE.id).Perm (x.id :: (A ++ B).map GE.id) := by
    simp only [List.map_append, List.map_cons]
    exact List.perm_middle
  exact this.nodup_iff.2 (List.nodup_cons.2 ⟨hx, h⟩)

/-- Common part of the two retroactive insertions. -/
theorem lgood_insert {init : K → V} {A B : List (GE K V)} {clk : ℕ} {x : GE K V}
    (hL : LGood init (A ++ B) clk) (hA : ∀ a ∈ A, a.key ≤ x.key) (hB : ∀ b ∈ B, x.key ≤ b.key)
    (hkey : x.key < 4 * clk) (hk1 : x.key % 4 ≠ 1) (hid : x.id ∉ (A ++ B).map GE.id)
    (hrsp : (seqStep (runSeq init (A.map GE.ent)) x.k x.op).2 = x.rsp)
    (hb : Benign (runSeq init (A.map GE.ent)) x B)
    (h0 : x.key % 4 = 0 → x.op.IsWrite ∧ ∃ y ∈ A ++ B, y.key = x.key + 1 ∧ y.k = x.k ∧
      y.op.IsWrite) :
    LGood init (A ++ x :: B) (clk + 1) := by
  have hmem : ∀ e, e ∈ A ++ x :: B ↔ e ∈ A ++ B ∨ e = x := by
    intro e; simp only [List.mem_append, List.mem_cons]; tauto
  refine ⟨kSorted_insert hL.sorted hA hB, nodup_insert_id hL.nodup hid, ?_,
    respOK_insert hL.resp hrsp hb, ?_, ?_⟩
  · intro e he
    rcases (hmem e).1 he with he | rfl
    · have := hL.key_lt e he; omega
    · omega
  · intro e he hz
    rcases (hmem e).1 he with he | rfl
    · obtain ⟨hw, y, hy, hy'⟩ := hL.rank0 e he hz
      exact ⟨hw, y, (hmem y).2 (Or.inl hy), hy'⟩
    · obtain ⟨hw, y, hy, hy'⟩ := h0 hz
      exact ⟨hw, y, (hmem y).2 (Or.inl hy), hy'⟩
  · intro e he e' he' hk h1
    rcases (hmem e).1 he with he | rfl <;> rcases (hmem e').1 he' with he' | rfl
    · exact hL.rank1 e he e' he' hk h1
    · exact absurd (hk ▸ h1) hk1
    · exact absurd h1 hk1
    · rfl

/-- Insertion of a `CAS` returning `false`, after all entries of steps `≤ t`. -/
theorem lgood_insert_fcas {init : K → V} {L : List (GE K V)} {clk t : ℕ} (hL : LGood init L clk)
    (ht : t < clk) (x : GE K V) (hkey : x.key = 4 * t + 3) {old new : V}
    (hop : x.op = .cas old new) (hs : stAt init L t x.k ≠ old) (hrsp : x.rsp = .ok false)
    (hid : x.id ∉ L.map GE.id) :
    ∃ L', LGood init L' (clk + 1) ∧ (∀ e ∈ L, e ∈ L') ∧ (∀ e ∈ L', e ∈ L ∨ e = x) ∧ x ∈ L' ∧
      curSt init L' = curSt init L ∧ ∀ t', stAt init L' t' = stAt init L t' := by
  obtain ⟨A, B, rfl, hA, hB⟩ := kSorted_split_le L hL.sorted (4 * t + 3)
  have hAs : runSeq init (A.map GE.ent) = stAt init (A ++ B) t := by
    simp only [stAt, List.filter_append]
    rw [List.filter_eq_self.2 (by simpa using hA), List.filter_eq_nil_iff.2
      (fun b hb => by simp; have := hB b hb; omega)]
    simp
  have hno : (seqStep (runSeq init (A.map GE.ent)) x.k x.op) =
      (runSeq init (A.map GE.ent), .ok false) := by
    rw [hop, hAs]; simp [seqStep, hs]
  refine ⟨A ++ x :: B, lgood_insert hL (fun a ha => by rw [hkey]; exact hA a ha)
      (fun b hb => by rw [hkey]; exact (hB b hb).le) (by omega) (by omega) hid
      (by rw [hno, hrsp]) (Or.inl (by rw [hno])) (fun h => by omega), ?_, ?_, by simp, ?_, ?_⟩
  · intro e he; simp only [List.mem_append, List.mem_cons] at he ⊢; tauto
  · intro e he; simp only [List.mem_append, List.mem_cons] at he ⊢; tauto
  · exact curSt_insert (Or.inl (by rw [hno]))
  · intro t'
    exact stAt_insert (fun a ha => by rw [hkey]; exact hA a ha)
      (fun b hb => by rw [hkey]; exact (hB b hb).le) (Or.inl (by rw [hno])) t'

/-- Insertion of a hitchhiking write just before the writes of step `t` (rank `0`). -/
theorem lgood_insert_hh {init : K → V} {L : List (GE K V)} {clk t : ℕ} (hL : LGood init L clk)
    (ht : t < clk) (x : GE K V) (hkey : x.key = 4 * t) (hw : x.op.IsWrite)
    (hy : ∃ y ∈ L, y.key = 4 * t + 1 ∧ y.k = x.k ∧ y.op.IsWrite) (hrsp : x.rsp = .ok true)
    (hid : x.id ∉ L.map GE.id) :
    ∃ L', LGood init L' (clk + 1) ∧ (∀ e ∈ L, e ∈ L') ∧ (∀ e ∈ L', e ∈ L ∨ e = x) ∧ x ∈ L' ∧
      curSt init L' = curSt init L ∧ ∀ t', stAt init L' t' = stAt init L t' := by
  obtain ⟨y, hyL, hyk, hyx, hyw⟩ := hy
  obtain ⟨A, B, rfl, hA, hB⟩ := kSorted_split_lt L hL.sorted (4 * t)
  have hyB : y ∈ B := by
    rcases List.mem_append.1 hyL with h | h
    · have := hA y h; omega
    · exact h
  obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
    cases B with
    | nil => simp at hyB
    | cons b B' => exact ⟨b, B', rfl⟩
  have hbL : b ∈ A ++ b :: B' := by simp
  have hbk : b.key ≤ 4 * t + 1 := by
    rcases List.mem_cons.1 hyB with h | h
    · rw [← h, hyk]
    · have hs := hL.sorted
      unfold KSorted at hs
      rw [List.pairwise_append] at hs
      have := (List.pairwise_cons.1 hs.2.1).1 y h; omega
  have hbk' : 4 * t ≤ b.key := hB b (by simp)
  have hbw : b.op.IsWrite ∧ b.k = x.k := by
    rcases (show b.key = 4 * t ∨ b.key = 4 * t + 1 by omega) with h | h
    · obtain ⟨hw', y', hy', hy'k, hy'b, -⟩ := hL.rank0 b hbL (by omega)
      have := hL.rank1 y' hy' y hyL (by omega) (by omega)
      subst this
      exact ⟨hw', by rw [← hy'b, hyx]⟩
    · have := hL.rank1 b hbL y hyL (by omega) (by omega)
      subst this; exact ⟨hyw, hyx⟩
  have hben : Benign (runSeq init (A.map GE.ent)) x (b :: B') :=
    Or.inr ⟨hw, b, B', rfl, hbw.1, hbw.2⟩
  have hr : (seqStep (runSeq init (A.map GE.ent)) x.k x.op).2 = x.rsp := by
    obtain ⟨u, hu⟩ := hw.eq; rw [hu, hrsp]; simp [seqStep]
  refine ⟨A ++ x :: b :: B', lgood_insert hL (fun a ha => by rw [hkey]; exact (hA a ha).le)
      (fun c hc => by rw [hkey]; exact hB c hc) (by omega) (by omega) hid hr hben
      (fun _ => ⟨hw, y, hyL, by omega, hyx, hyw⟩), ?_, ?_, by simp, curSt_insert hben, ?_⟩
  · intro e he; simp only [List.mem_append, List.mem_cons] at he ⊢; tauto
  · intro e he; simp only [List.mem_append, List.mem_cons] at he ⊢; tauto
  · intro t'
    exact stAt_insert (fun a ha => by rw [hkey]; exact (hA a ha).le)
      (fun c hc => by rw [hkey]; exact hB c hc)
      (Or.inr ⟨hw, by omega, b, B', rfl, hbw.1, hbw.2, by omega⟩) t'

end Podc.DuraCAS
