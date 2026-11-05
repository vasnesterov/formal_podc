import Papers.PODC2023.DuraCAS.Spec

/-!
# Keyed linearization lists (helper for the A-level proof)

The linearization of the A-level proof is built incrementally as a list of *keyed entries*
`GE` sorted by key. A key `4 t + r` encodes the step `t` at which the entry takes effect and a
rank `r` inside that step: `0` hitchhiking writes (inserted retroactively just before the
installing write moved at step `t`), `1` the operation linearized at step `t` itself, `3` failing
`CAS`es (inserted retroactively after step `t`); `2` is the rank of history events.

This file proves the list facts: state/response bookkeeping (`RespOK`), the state `stAt L t`
after step `t`, and invariance of both under *benign* insertions (a no-op entry, or a write
immediately overwritten by another write on the same object).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {K V : Type} [DecidableEq K] [DecidableEq V]

variable (K V) in
/-- A keyed entry of the ghost linearization: key, operation `(id, k, op)`, response. -/
structure GE where
  key : ℕ
  id : ℕ
  k : K
  op : Op V
  rsp : Resp V
  deriving DecidableEq

/-- The operation of an entry. -/
def GE.ent (e : GE K V) : ℕ × K × Op V := (e.id, e.k, e.op)

/-- The operation is a `WRITE`. -/
def Op.IsWrite : Op V → Prop
  | .write _ => True
  | _ => False

/-- Every entry of the list returns, in the sequential run from `σ`, its recorded response. -/
def RespOK (σ : K → V) : List (GE K V) → Prop
  | [] => True
  | e :: L => (seqStep σ e.k e.op).2 = e.rsp ∧ RespOK (seqStep σ e.k e.op).1 L

/-- Keys are non-decreasing. -/
def KSorted (L : List (GE K V)) : Prop := L.Pairwise (fun a b => a.key ≤ b.key)

/-- The state of the sequential run after step `t` (entries with key `≤ 4 t + 3`). -/
def stAt (init : K → V) (L : List (GE K V)) (t : ℕ) : K → V :=
  runSeq init ((L.filter (fun e => e.key ≤ 4 * t + 3)).map GE.ent)

/-- The current state of the sequential run. -/
def curSt (init : K → V) (L : List (GE K V)) : K → V := runSeq init (L.map GE.ent)

theorem runSeq_append (σ : K → V) (A B : List (ℕ × K × Op V)) :
    runSeq σ (A ++ B) = runSeq (runSeq σ A) B := by
  induction A generalizing σ with
  | nil => rfl
  | cons e A ih => simp only [List.cons_append, runSeq, ih]

@[simp] theorem runSeq_nil (σ : K → V) : runSeq σ [] = σ := rfl

@[simp] theorem runSeq_cons (σ : K → V) (e : ℕ × K × Op V) (L : List (ℕ × K × Op V)) :
    runSeq σ (e :: L) = runSeq (seqStep σ e.2.1 e.2.2).1 L := rfl

theorem RespOK_append (σ : K → V) (A B : List (GE K V)) :
    RespOK σ (A ++ B) ↔ RespOK σ A ∧ RespOK (runSeq σ (A.map GE.ent)) B := by
  induction A generalizing σ with
  | nil => simp [RespOK]
  | cons e A ih =>
    simp only [List.cons_append, RespOK, ih, List.map_cons, runSeq_cons, GE.ent]
    tauto

/-- A write overwritten by a write on the same object. -/
theorem seqStep_write_write (σ : K → V) (k : K) (u w : V) :
    (seqStep (seqStep σ k (.write u)).1 k (.write w)).1 = (seqStep σ k (.write w)).1 := by
  simp [seqStep]

theorem seqStep_write_rsp (σ σ' : K → V) (k : K) (u : V) :
    (seqStep σ k (.write u)).2 = (seqStep σ' k (.write u)).2 := by
  simp [seqStep]

/-- Benign insertion of `x` in front of `B`, in state `σ`. -/
def Benign (σ : K → V) (x : GE K V) (B : List (GE K V)) : Prop :=
  (seqStep σ x.k x.op).1 = σ ∨
    (x.op.IsWrite ∧ ∃ y B', B = y :: B' ∧ y.op.IsWrite ∧ y.k = x.k)

theorem Op.IsWrite.eq {op : Op V} (h : op.IsWrite) : ∃ u, op = .write u := by
  cases op <;> simp_all [Op.IsWrite]

theorem benign_runSeq (σ : K → V) (x : GE K V) (B : List (GE K V)) (h : Benign σ x B) :
    runSeq (seqStep σ x.k x.op).1 (B.map GE.ent) = runSeq σ (B.map GE.ent) := by
  rcases h with h | ⟨hx, y, B', rfl, hy, hk⟩
  · rw [h]
  · obtain ⟨u, hu⟩ := hx.eq
    obtain ⟨w, hw⟩ := hy.eq
    simp only [List.map_cons, runSeq_cons, GE.ent, hu, hw, hk]
    rw [seqStep_write_write]

theorem benign_respOK (σ : K → V) (x : GE K V) (B : List (GE K V)) (h : Benign σ x B)
    (hB : RespOK σ B) : RespOK (seqStep σ x.k x.op).1 B := by
  rcases h with h | ⟨hx, y, B', rfl, hy, hk⟩
  · rw [h]; exact hB
  · obtain ⟨u, hu⟩ := hx.eq
    obtain ⟨w, hw⟩ := hy.eq
    simp only [RespOK] at hB ⊢
    rw [hu]; rw [hw, hk] at hB
    refine ⟨?_, ?_⟩
    · rw [← hB.1, hw, hk]; simp [seqStep]
    · rw [hw, hk, seqStep_write_write]; exact hB.2

/-- Benign insertion preserves `RespOK`. -/
theorem respOK_insert {σ : K → V} {A B : List (GE K V)} {x : GE K V}
    (hL : RespOK σ (A ++ B)) (hx : (seqStep (runSeq σ (A.map GE.ent)) x.k x.op).2 = x.rsp)
    (hb : Benign (runSeq σ (A.map GE.ent)) x B) : RespOK σ (A ++ x :: B) := by
  rw [RespOK_append] at hL ⊢
  exact ⟨hL.1, hx, benign_respOK _ _ _ hb hL.2⟩

/-- Benign insertion preserves the final state. -/
theorem curSt_insert {init : K → V} {A B : List (GE K V)} {x : GE K V}
    (hb : Benign (runSeq init (A.map GE.ent)) x B) :
    curSt init (A ++ x :: B) = curSt init (A ++ B) := by
  simp only [curSt, List.map_append, List.map_cons, runSeq_append, runSeq_cons]
  exact benign_runSeq _ _ _ hb

theorem respOK_append_one {σ : K → V} {L : List (GE K V)} {x : GE K V} (hL : RespOK σ L)
    (hx : (seqStep (runSeq σ (L.map GE.ent)) x.k x.op).2 = x.rsp) : RespOK σ (L ++ [x]) := by
  rw [RespOK_append]
  exact ⟨hL, hx, trivial⟩

theorem curSt_append_one (init : K → V) (L : List (GE K V)) (x : GE K V) :
    curSt init (L ++ [x]) = (seqStep (curSt init L) x.k x.op).1 := by
  simp [curSt, runSeq_append, GE.ent]

/-- Appending an entry with a later key does not change `stAt` of earlier steps. -/
theorem stAt_append_one (init : K → V) (L : List (GE K V)) (x : GE K V) (t : ℕ)
    (h : 4 * t + 3 < x.key) : stAt init (L ++ [x]) t = stAt init L t := by
  simp only [stAt, List.filter_append, List.filter_cons]
  rw [if_neg (by simpa using h)]
  simp

theorem stAt_eq_curSt (init : K → V) (L : List (GE K V)) (t : ℕ)
    (h : ∀ e ∈ L, e.key ≤ 4 * t + 3) : stAt init L t = curSt init L := by
  simp only [stAt, curSt]
  rw [List.filter_eq_self.2 (by simpa using h)]

/-- Benign insertion at a sorted position preserves `stAt`, provided that in the overwriting
case the key of `x` is `0 mod 4` and the next entry has key `≤ key x + 1`. -/
theorem stAt_insert {init : K → V} {A B : List (GE K V)} {x : GE K V}
    (hA : ∀ a ∈ A, a.key ≤ x.key) (hB : ∀ b ∈ B, x.key ≤ b.key)
    (hb : (seqStep (runSeq init (A.map GE.ent)) x.k x.op).1 = runSeq init (A.map GE.ent) ∨
      (x.op.IsWrite ∧ x.key % 4 = 0 ∧ ∃ y B', B = y :: B' ∧ y.op.IsWrite ∧ y.k = x.k ∧
        y.key ≤ x.key + 1)) (t : ℕ) :
    stAt init (A ++ x :: B) t = stAt init (A ++ B) t := by
  simp only [stAt, List.filter_append, List.filter_cons]
  by_cases hx : x.key ≤ 4 * t + 3
  · rw [if_pos (by simpa using hx)]
    rw [List.filter_eq_self.2 (by intro a ha; simpa using (hA a ha).trans hx)]
    simp only [List.map_append, List.map_cons, runSeq_append, runSeq_cons]
    apply benign_runSeq
    rcases hb with hb | ⟨hw, h4, y, B', rfl, hy, hk, hyk⟩
    · exact Or.inl hb
    · right
      refine ⟨hw, y, B'.filter (fun e => e.key ≤ 4 * t + 3), ?_, hy, hk⟩
      rw [List.filter_cons, if_pos (by simp; omega)]
  · rw [if_neg (by simpa using hx)]

theorem kSorted_insert {A B : List (GE K V)} {x : GE K V} (hL : KSorted (A ++ B))
    (hA : ∀ a ∈ A, a.key ≤ x.key) (hB : ∀ b ∈ B, x.key ≤ b.key) : KSorted (A ++ x :: B) := by
  unfold KSorted at *
  rw [List.pairwise_append] at hL ⊢
  refine ⟨hL.1, List.pairwise_cons.2 ⟨hB, hL.2.1⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hA a ha
  · exact hL.2.2 a ha b hb

theorem kSorted_append_one {L : List (GE K V)} {x : GE K V} (hL : KSorted L)
    (h : ∀ a ∈ L, a.key ≤ x.key) : KSorted (L ++ [x]) := by
  unfold KSorted at *
  rw [List.pairwise_append]
  exact ⟨hL, by simp, fun a ha b hb => by simp at hb; subst hb; exact h a ha⟩

/-- Split a sorted list at a key threshold (`≤ c` / `> c`). -/
theorem kSorted_split_le (L : List (GE K V)) (hL : KSorted L) (c : ℕ) :
    ∃ A B, L = A ++ B ∧ (∀ a ∈ A, a.key ≤ c) ∧ (∀ b ∈ B, c < b.key) := by
  induction L with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons e L ih =>
    have hL' : KSorted L := (List.pairwise_cons.1 hL).2
    by_cases he : e.key ≤ c
    · obtain ⟨A, B, rfl, hA, hB⟩ := ih hL'
      exact ⟨e :: A, B, rfl, by simp; exact ⟨he, hA⟩, hB⟩
    · refine ⟨[], e :: L, rfl, by simp, ?_⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · have := (List.pairwise_cons.1 hL).1 b hb; omega

/-- Split a sorted list at a key threshold (`< c` / `≥ c`). -/
theorem kSorted_split_lt (L : List (GE K V)) (hL : KSorted L) (c : ℕ) :
    ∃ A B, L = A ++ B ∧ (∀ a ∈ A, a.key < c) ∧ (∀ b ∈ B, c ≤ b.key) := by
  induction L with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons e L ih =>
    have hL' : KSorted L := (List.pairwise_cons.1 hL).2
    by_cases he : e.key < c
    · obtain ⟨A, B, rfl, hA, hB⟩ := ih hL'
      exact ⟨e :: A, B, rfl, by simp; exact ⟨he, hA⟩, hB⟩
    · refine ⟨[], e :: L, rfl, by simp, ?_⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · have := (List.pairwise_cons.1 hL).1 b hb; omega

/-- In a key-sorted list, an entry with a smaller key comes first. -/
theorem kSorted_sublist {L : List (GE K V)} (hL : KSorted L) {a b : GE K V} (ha : a ∈ L)
    (hb : b ∈ L) (hab : a.key < b.key) : [a, b].Sublist L := by
  induction L with
  | nil => simp at ha
  | cons e L ih =>
    have hL' : KSorted L := (List.pairwise_cons.1 hL).2
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · omega
      · exact List.Sublist.cons_cons _ (List.singleton_sublist.2 hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · have := (List.pairwise_cons.1 hL).1 a ha'; omega
      · exact List.Sublist.cons _ (ih hL' ha' hb')

/-- `RespOK` gives the response at every split of the projected list. -/
theorem respOK_split {σ : K → V} {L : List (GE K V)} (hL : RespOK σ L) :
    ∀ L₁ e L₂, L.map GE.ent = L₁ ++ e :: L₂ →
      ∃ g ∈ L, g.ent = e ∧ (seqStep (runSeq σ L₁) e.2.1 e.2.2).2 = g.rsp := by
  induction L generalizing σ with
  | nil => intro L₁ e L₂ h; simp at h
  | cons g L ih =>
    intro L₁ e L₂ h
    cases L₁ with
    | nil =>
      simp only [List.map_cons, List.nil_append, List.cons.injEq] at h
      refine ⟨g, List.mem_cons_self, h.1, ?_⟩
      rw [← h.1]; exact hL.1
    | cons f L₁ =>
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      obtain ⟨g', hg', h1, h2⟩ := ih hL.2 L₁ e L₂ h.2
      refine ⟨g', List.mem_cons_of_mem _ hg', h1, ?_⟩
      rw [← h.1]
      simpa [GE.ent] using h2

end Podc.DuraCAS
