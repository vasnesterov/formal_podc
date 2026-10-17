import Papers.PODC2025.StrangerFreeTasks.Alg1SafetyBasic
import Podc.Foundations.Data.Fin.Cyclic

/-!
# Algorithm 1 for `k = 1`: local steps and static invariants

Preparation for the proof that Algorithm 1 is wait-free for `k = 1`
(`Alg1WaitFreeK1.lean`). With `k = 1` there are two registers `A[0]`, `A[1]`, every collect
has two reads, and a process writes `A[0], A[1], A[0], …` (its write index is its sequence
number modulo 2).

* explicit local states after the reads of a collect (`afterCol1_j0`, …);
* `SInvK1`: static invariants of every reachable configuration (writer in seen set, parity of
  sequence numbers per register, registers are never re-initialized, …), `sInvK1_of_run`;
* simple step facts: `done` is absorbing, sequence numbers are monotone.
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P : Type} [DecidableEq P]

/-! ### `Fin 2` and the local steps for `k = 1` -/

lemma fin2_cases_k1 (j : Fin (1 + 1)) : j = 0 ∨ j = 1 := by
  revert j; decide

lemma fin2_le_one (j : Fin (1 + 1)) : j ≤ 1 := by
  revert j; decide

lemma fin2_val_add_one (i : Fin (1 + 1)) : (i + 1).val = (i.val + 1) % 2 := by
  revert i; decide

section Local

variable (l : Loc P 1) (v : Triple P)

lemma afterCol1_j0 (h : l.j = 0) : afterCol1 1 l v =
    { l with collect := Function.update l.collect 0 v, seen := l.seen ∪ v.seen, j := 1 } := by
  simp [afterCol1, h]

lemma afterCol1_j1 (h : l.j = 1) : afterCol1 1 l v =
    { l with collect := Function.update l.collect 1 v, seen := l.seen ∪ v.seen,
             phase := .col2, j := 0, snap := true } := by
  simp [afterCol1, h]

lemma afterCol2_j0 (h : l.j = 0) : afterCol2 1 l v =
    { l with snap := l.snap && decide (v = l.collect 0),
             seen := l.seen ∪ (l.collect 0).seen, j := 1 } := by
  simp [afterCol2, h]

lemma afterCol2_j1 (h : l.j = 1) : afterCol2 1 l v =
    decision 1 { l with snap := l.snap && decide (v = l.collect 1),
                        seen := l.seen ∪ (l.collect 1).seen } := by
  simp [afterCol2, h]

@[simp] lemma decision_i : (decision 1 l).i = l.i := by
  unfold decision; split_ifs <;> rfl

lemma decision_cases_k1 :
    (decision 1 l).phase = .done ∨
      ((decision 1 l).phase = .wr ∧ l.seen.card ≤ 1 ∧
        ¬ (l.snap = true ∧ ∀ r, l.seen = (l.collect r).seen)) := by
  unfold decision; split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, not_lt.1 h1, h2⟩

lemma decision_done (h : 1 < l.seen.card ∨ (l.snap = true ∧ ∀ r, l.seen = (l.collect r).seen)) :
    (decision 1 l).phase = .done := by
  rcases decision_cases_k1 l with h' | ⟨-, h1, h2⟩
  · exact h'
  · rcases h with h | h
    · omega
    · exact absurd h h2

@[simp] lemma afterCol2_i : (afterCol2 1 l v).i = l.i := by
  unfold afterCol2; split_ifs <;> simp

lemma afterCol2_wr_card (hl : l.phase = .col2) (h : (afterCol2 1 l v).phase = .wr) :
    (afterCol2 1 l v).seen.card ≤ 1 := by
  revert h; unfold afterCol2; split_ifs with h1
  · intro h
    rcases decision_cases_k1 (P := P) { l with
        snap := l.snap && decide (v = l.collect l.j),
        seen := l.seen ∪ (l.collect l.j).seen } with h' | h'
    · rw [h'] at h; cases h
    · rw [decision_seen]; exact h'.2.1
  · simp [hl]

end Local

/-! ### Static invariants -/

/-- Static invariants of reachable configurations of Algorithm 1 with `k = 1`. -/
structure SInvK1 (C : Cfg P 1) : Prop where
  mem_self : ∀ r w, (C.mem r).id = some w → w ∈ (C.mem r).seen
  col_self : ∀ x r w, ((C.loc x).collect r).id = some w → w ∈ ((C.loc x).collect r).seen
  mem_par : ∀ r w, (C.mem r).id = some w → (C.mem r).seq % 2 = r.val
  col_par : ∀ x r w, ((C.loc x).collect r).id = some w → ((C.loc x).collect r).seq % 2 = r.val
  i_par : ∀ x, (C.loc x).i.val = (C.loc x).seq % 2
  idle_seq : ∀ x, (C.loc x).phase = .idle → (C.loc x).seq = 0
  wr_card : ∀ x, (C.loc x).phase = .wr → (C.loc x).seen.card ≤ 1
  col_sub : ∀ x r, ((C.loc x).collect r).seen ⊆ (C.loc x).seen
  mem0 : ∀ x, 1 ≤ (C.loc x).seq → (C.mem 0).id ≠ none
  mem1 : ∀ x, 2 ≤ (C.loc x).seq → (C.mem 1).id ≠ none

lemma sInvK1_init : SInvK1 ((alg1 (P := P) 1).initCfg) where
  mem_self r w h := by simp [Impl.initCfg, alg1, Triple.init] at h
  col_self x r w h := by simp [Impl.initCfg, alg1, locInit, Triple.init] at h
  mem_par r w h := by simp [Impl.initCfg, alg1, Triple.init] at h
  col_par x r w h := by simp [Impl.initCfg, alg1, locInit, Triple.init] at h
  i_par x := rfl
  idle_seq x _ := rfl
  wr_card x h := by simp [Impl.initCfg, alg1, locInit] at h
  col_sub x r := by simp [Impl.initCfg, alg1, locInit, Triple.init]
  mem0 x h := by simp [Impl.initCfg, alg1, locInit] at h
  mem1 x h := by simp [Impl.initCfg, alg1, locInit] at h

/-- `SInvK1` after a step that replaces the local state of `p` by `l'` and the memory by `M'`. -/
lemma SInvK1.of_local {C C' : Cfg P 1} {p : P} {l' : Loc P 1} {M' : Fin (1 + 1) → Triple P}
    (hS : SInvK1 C) (hloc : C'.loc = Function.update C.loc p l') (hmem : C'.mem = M')
    (m_self : ∀ r w, (M' r).id = some w → w ∈ (M' r).seen)
    (m_par : ∀ r w, (M' r).id = some w → (M' r).seq % 2 = r.val)
    (c_self : ∀ r w, (l'.collect r).id = some w → w ∈ (l'.collect r).seen)
    (c_par : ∀ r w, (l'.collect r).id = some w → (l'.collect r).seq % 2 = r.val)
    (i_par : l'.i.val = l'.seq % 2) (idle_seq : l'.phase = .idle → l'.seq = 0)
    (wr_card : l'.phase = .wr → l'.seen.card ≤ 1) (col_sub : ∀ r, (l'.collect r).seen ⊆ l'.seen)
    (m0 : ∀ r, (C.mem r).id ≠ none → (M' r).id ≠ none)
    (m0' : 1 ≤ l'.seq → (M' 0).id ≠ none) (m1' : 2 ≤ l'.seq → (M' 1).id ≠ none) :
    SInvK1 C' := by
  have hl : ∀ q, C'.loc q = if q = p then l' else C.loc q := fun q => by
    rw [hloc, Function.update_apply]
  subst hmem
  refine ⟨m_self, ?_, m_par, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x r w; rw [hl]; split_ifs
    · exact c_self r w
    · exact hS.col_self x r w
  · intro x r w; rw [hl]; split_ifs
    · exact c_par r w
    · exact hS.col_par x r w
  · intro x; rw [hl]; split_ifs
    · exact i_par
    · exact hS.i_par x
  · intro x; rw [hl]; split_ifs
    · exact idle_seq
    · exact hS.idle_seq x
  · intro x; rw [hl]; split_ifs
    · exact wr_card
    · exact hS.wr_card x
  · intro x r; rw [hl]; split_ifs
    · exact col_sub r
    · exact hS.col_sub x r
  · intro x; rw [hl]; split_ifs
    · exact m0'
    · exact fun h => m0 0 (hS.mem0 x h)
  · intro x; rw [hl]; split_ifs
    · exact m1'
    · exact fun h => m0 1 (hS.mem1 x h)

lemma SInvK1.step {α : List (Label P (laObj P))} {C C' : Cfg P 1} {ℓ : Label P (laObj P)}
    (hB : BInv α C) (hS : SInvK1 C) (h : (alg1 1).step C ℓ = some C') : SInvK1 C' := by
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, h3, h4⟩ := step_inv_alg1 h
    have e : ∀ q, (C.loc q).phase = .idle → (C.loc q).seen.card ≤ 1 := fun q hq => by
      rw [hB.idle_seen q hq]; simp
    refine hS.of_local h3 h4 hS.mem_self hS.mem_par ?_ ?_ ?_ ?_ ?_ ?_ (fun r h => h) ?_ ?_
    all_goals split_ifs with hh
    all_goals first
      | exact hS.col_self p | exact hS.col_par p | exact hS.i_par p | exact hS.col_sub p
      | exact hS.mem0 p | exact hS.mem1 p | skip
    · simp
    · exact hS.idle_seq p
    · intro _; exact e p hh
    · exact hS.wr_card p
  | ret p o =>
    obtain ⟨-, -, h3, h4, -⟩ := step_ret_alg1 h
    have : C'.loc = Function.update C.loc p (C.loc p) := by rw [h4, Function.update_eq_self]
    exact hS.of_local this h3 hS.mem_self hS.mem_par (hS.col_self p) (hS.col_par p) (hS.i_par p)
      (hS.idle_seq p) (hS.wr_card p) (hS.col_sub p) (fun r h => h) (hS.mem0 p) (hS.mem1 p)
  | tau p =>
    obtain ⟨-, -, h3⟩ := step_tau_alg1 h
    rcases h3 with ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩
    · -- write
      have hpar := hS.i_par p
      refine hS.of_local hl hm ?_ ?_ (hS.col_self p) (hS.col_par p) ?_ (by simp) (by simp)
        (hS.col_sub p) ?_ ?_ ?_
      · intro r w; rw [Function.update_apply]; split_ifs
        · simp only [Option.some.injEq]; rintro rfl; exact hB.self _
        · exact hS.mem_self r w
      · intro r w; rw [Function.update_apply]; split_ifs with hr
        · subst hr; intro _; exact hpar.symm
        · exact hS.mem_par r w
      · simp only [wrNext]; rw [fin2_val_add_one, hpar]; omega
      · intro r hr; rw [Function.update_apply]; split_ifs <;> simp [hr]
      · intro h1; rw [Function.update_apply]; split_ifs with hr
        · simp
        · simp only [wrNext_seq] at h1
          rcases Nat.eq_zero_or_pos (C.loc p).seq with h0 | h0
          · exfalso; apply hr; apply Fin.ext; rw [hpar, h0]; rfl
          · exact hS.mem0 p h0
      · intro h1; rw [Function.update_apply]; split_ifs with hr
        · simp
        · simp only [wrNext_seq] at h1
          by_cases h0 : (C.loc p).seq = 1
          · exfalso; apply hr; apply Fin.ext; rw [hpar, h0]; rfl
          · exact hS.mem1 p (by omega)
    · -- first collect
      have hpar := hS.i_par p
      have hsub := hS.col_sub p
      rcases fin2_cases_k1 (C.loc p).j with hj | hj
      · rw [afterCol1_j0 _ _ hj, hj] at hl
        refine hS.of_local hl hm hS.mem_self hS.mem_par ?_ ?_ hpar (by simp [hph]) (by simp [hph]) ?_
          (fun r h => h) (hS.mem0 p) (hS.mem1 p)
        · intro r w; simp only [Function.update_apply]; split_ifs with hr
          · exact hS.mem_self 0 w
          · exact hS.col_self p r w
        · intro r w; simp only [Function.update_apply]; split_ifs with hr
          · subst hr; exact hS.mem_par 0 w
          · exact hS.col_par p r w
        · intro r; simp only [Function.update_apply]; split_ifs with hr
          · exact Finset.subset_union_right
          · exact (hsub r).trans Finset.subset_union_left
      · rw [afterCol1_j1 _ _ hj, hj] at hl
        refine hS.of_local hl hm hS.mem_self hS.mem_par ?_ ?_ hpar (by simp) (by simp) ?_
          (fun r h => h) (hS.mem0 p) (hS.mem1 p)
        · intro r w; simp only [Function.update_apply]; split_ifs with hr
          · exact hS.mem_self 1 w
          · exact hS.col_self p r w
        · intro r w; simp only [Function.update_apply]; split_ifs with hr
          · subst hr; exact hS.mem_par 1 w
          · exact hS.col_par p r w
        · intro r; simp only [Function.update_apply]; split_ifs with hr
          · exact Finset.subset_union_right
          · exact (hsub r).trans Finset.subset_union_left
    · -- second collect
      have hsub := hS.col_sub p
      have hph2 := afterCol2_phase (C.loc p) (C.mem (C.loc p).j) hph
      refine hS.of_local hl hm hS.mem_self hS.mem_par (by simpa using hS.col_self p)
        (by simpa using hS.col_par p) (by simpa [afterCol2_i] using hS.i_par p) ?_ ?_ ?_
        (fun r h => h) (by simpa using hS.mem0 p) (by simpa using hS.mem1 p)
      · intro h'; rcases hph2 with h'' | h'' | ⟨h'', -⟩ <;> rw [h''] at h' <;> cases h'
      · exact afterCol2_wr_card _ _ hph
      · intro r; simp only [afterCol2_collect, afterCol2_seen]
        exact (hsub r).trans Finset.subset_union_left

theorem sInvK1_of_run {α : List (Label P (laObj P))} {C : Cfg P 1}
    (h : (alg1 1).run α = some C) : SInvK1 C :=
  Impl.run_induction (I := alg1 1) (Q := fun _ C => SInvK1 C) sInvK1_init
    (fun _ _ _ _ hα hS hs => hS.step (bInv_of_run hα) hs) h

/-! ### Simple step facts -/

section StepFacts

variable {C C' : Cfg P 1} {ℓ : Label P (laObj P)}

lemma step_tau_phase {x : P} (h : (alg1 1).step C (.tau x) = some C') :
    (C.loc x).phase = .wr ∨ (C.loc x).phase = .col1 ∨ (C.loc x).phase = .col2 := by
  obtain ⟨-, -, h3⟩ := step_tau_alg1 h
  rcases h3 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- A process in phase `done` never changes its local state. -/
lemma step_loc_done {x : P} (h : (alg1 1).step C ℓ = some C') (hd : (C.loc x).phase = .done) :
    C'.loc x = C.loc x := by
  by_cases hx : ℓ.proc = x
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hx; subst hx
      obtain ⟨-, -, h3, -⟩ := step_inv_alg1 h
      rw [h3, Function.update_self, hd]; rfl
    | ret q o =>
      obtain ⟨-, -, -, h4, -⟩ := step_ret_alg1 h
      rw [h4]
    | tau q =>
      simp only [Label.proc] at hx; subst hx
      rcases step_tau_phase h with h' | h' | h' <;> rw [h'] at hd <;> cases hd
  · exact (Impl.step_other h hx).1

lemma step_seq_le (h : (alg1 1).step C ℓ = some C') (x : P) :
    (C.loc x).seq ≤ (C'.loc x).seq := by
  by_cases hx : ℓ.proc = x
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hx; subst hx
      obtain ⟨-, -, h3, -⟩ := step_inv_alg1 h
      rw [h3, Function.update_self]; split_ifs <;> simp
    | ret q o =>
      obtain ⟨-, -, -, h4, -⟩ := step_ret_alg1 h
      rw [h4]
    | tau q =>
      simp only [Label.proc] at hx; subst hx
      obtain ⟨-, -, h3⟩ := step_tau_alg1 h
      rcases h3 with ⟨-, -, hl⟩ | ⟨-, -, hl⟩ | ⟨-, -, hl⟩ <;> rw [hl] <;> simp
  · rw [(Impl.step_other h hx).1]

lemma step_write_seq {x : P} (h : (alg1 1).step C (.tau x) = some C')
    (hph : (C.loc x).phase = .wr) : (C'.loc x).seq = (C.loc x).seq + 1 := by
  obtain ⟨-, -, h3⟩ := step_tau_alg1 h
  rcases h3 with ⟨-, -, hl⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · rw [hl]; simp
  · rw [hph] at h'; cases h'
  · rw [hph] at h'; cases h'

/-- Memory only changes by writes. -/
lemma step_mem (h : (alg1 1).step C ℓ = some C') :
    C'.mem = C.mem ∨ ∃ y, ℓ = .tau y ∧ (C.loc y).phase = .wr ∧
      C'.mem = Function.update C.mem (C.loc y).i ⟨some y, (C.loc y).seq, (C.loc y).seen⟩ := by
  cases ℓ with
  | inv q o => exact Or.inl (step_inv_alg1 h).2.2.2
  | ret q o => exact Or.inl (step_ret_alg1 h).2.2.1
  | tau q =>
    obtain ⟨-, -, h3⟩ := step_tau_alg1 h
    rcases h3 with ⟨hph, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩
    · exact Or.inr ⟨q, rfl, hph, hm⟩
    · exact Or.inl hm
    · exact Or.inl hm

lemma step_mem_id (h : (alg1 1).step C ℓ = some C') (r : Fin (1 + 1))
    (hr : (C.mem r).id ≠ none) : (C'.mem r).id ≠ none := by
  rcases step_mem h with hm | ⟨y, -, -, hm⟩
  · rwa [hm]
  · rw [hm, Function.update_apply]; split_ifs
    · simp
    · exact hr

/-- The five kinds of internal steps of a process for `k = 1`. -/
lemma step_tau_k1 {x : P} (h : (alg1 1).step C (.tau x) = some C') :
    ((C.loc x).phase = .wr ∧
      C'.mem = Function.update C.mem (C.loc x).i ⟨some x, (C.loc x).seq, (C.loc x).seen⟩ ∧
      C'.loc x = wrNext 1 (C.loc x)) ∨
    ((C.loc x).phase = .col1 ∧ (C.loc x).j = 0 ∧ C'.mem = C.mem ∧
      C'.loc x = { C.loc x with collect := Function.update (C.loc x).collect 0 (C.mem 0),
                                seen := (C.loc x).seen ∪ (C.mem 0).seen, j := 1 }) ∨
    ((C.loc x).phase = .col1 ∧ (C.loc x).j = 1 ∧ C'.mem = C.mem ∧
      C'.loc x = { C.loc x with collect := Function.update (C.loc x).collect 1 (C.mem 1),
                                seen := (C.loc x).seen ∪ (C.mem 1).seen,
                                phase := .col2, j := 0, snap := true }) ∨
    ((C.loc x).phase = .col2 ∧ (C.loc x).j = 0 ∧ C'.mem = C.mem ∧
      C'.loc x = { C.loc x with snap := (C.loc x).snap && decide (C.mem 0 = (C.loc x).collect 0),
                                seen := (C.loc x).seen ∪ ((C.loc x).collect 0).seen, j := 1 }) ∨
    ((C.loc x).phase = .col2 ∧ (C.loc x).j = 1 ∧ C'.mem = C.mem ∧
      C'.loc x = decision 1 { C.loc x with
        snap := (C.loc x).snap && decide (C.mem 1 = (C.loc x).collect 1),
        seen := (C.loc x).seen ∪ ((C.loc x).collect 1).seen, j := 1 }) := by
  obtain ⟨-, -, h3⟩ := step_tau_alg1 h
  rcases h3 with ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩ | ⟨hph, hm, hl⟩
  · exact Or.inl ⟨hph, hm, by rw [hl, Function.update_self]⟩
  · rcases fin2_cases_k1 (C.loc x).j with hj | hj
    · refine Or.inr (Or.inl ⟨hph, hj, hm, ?_⟩)
      rw [hl, Function.update_self, afterCol1_j0 _ _ hj, hj]
    · refine Or.inr (Or.inr (Or.inl ⟨hph, hj, hm, ?_⟩))
      rw [hl, Function.update_self, afterCol1_j1 _ _ hj, hj]
  · rcases fin2_cases_k1 (C.loc x).j with hj | hj
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hph, hj, hm, ?_⟩)))
      rw [hl, Function.update_self, afterCol2_j0 _ _ hj, hj]
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hph, hj, hm, ?_⟩)))
      rw [hl, Function.update_self, afterCol2_j1 _ _ hj, hj]

end StepFacts

end Cslib.SharedMemory.StrangerFree
