import Papers.PODC2026.GeneralizedCAS.Trace

/-!
# Algorithm 1: basic facts of Appendix B.1, in temporal form

* `done_of_completed`: a completed operation is done (Lemma B.1.19);
* `done_of_ann_cell`: if a process reads a cell different from `(t', Null)` for the operation
  `(t', o', ptr')` it read from `A`, that operation is done (used on lines 10–15);
* `A_eq_ann`: the contents of `A` are determined by the timestamp (Observation B.1.10);
* `Trace.done_after_l7`: after line 7 for an operation, it is done (Lemma B.1.21);
* `Trace.done_of_S_change`: when `S` changes, its old operation is done (Lemma B.1.22);
* `Trace.S_ne_of_change`: `S` never takes a value twice (Lemma B.1.25 / Proposition B.1.24).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]
variable {cellInit : ℕ → CellVal T.Resp}

section state

variable {C : Cfg T P} {G : Ghost T P}

/-- **Lemma B.1.19**: a completed operation is done. -/
lemma done_of_completed (hI : CInv C G) {τ : ℕ} {q : P} {k : ℕ} {o : T.Op}
    (h : G.ts τ = some (q, k, o)) (hk : k < G.k q) : Done C G τ := by
  right; refine ⟨q, k, o, h, Or.inl hk, fun he => ?_⟩
  obtain ⟨c1, c2, c3⟩ := hI.cell τ q k o h (Or.inl hk)
  rw [he] at c1 c2 c3
  rcases c3 rfl with c | ⟨r, c, -⟩
  · exact absurd c.2.1 hk.ne
  · cases c

/-- Done, unfolded: the cell of the owner no longer holds `(τ, Null)`. -/
lemma Done.cell_ne {τ : ℕ} (hd : Done C G τ) (hτ : τ ≠ 0) {q : P} {k : ℕ} {o : T.Op}
    (h : G.ts τ = some (q, k, o)) : C.M.cell (C.loc q).me ≠ ⟨τ, .null⟩ := by
  obtain ⟨q', k', o', h1, -, h3⟩ := hd.resolve_left hτ
  rw [h] at h1; simp only [Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1; exact h3

/-- If a process that read `(t', o', ptr')` from `A` finds the cell at `ptr'` different from
`(t', Null)`, the operation with timestamp `t'` is done. -/
lemma done_of_ann_cell (hI : CInv C G) {q : P} (hq : C.pend q ≠ none)
    (hann : (C.loc q).pc.HasAnn) (hc : C.M.cell (C.loc q).ann.ptr ≠ ⟨(C.loc q).ann.time, .null⟩) :
    Done C G (C.loc q).ann.time := by
  by_cases h0 : (C.loc q).ann.time = 0
  · exact Or.inl h0
  obtain ⟨q', k, o, h1, h2, -, h4⟩ := hI.ann_pos q hq hann h0
  exact Or.inr ⟨q', k, o, h1, h2, by rw [← h4]; exact hc⟩

/-- **Observation B.1.10**: the contents of `A` are determined by their timestamp. -/
lemma A_eq_ann (hI : CInv C G) {q : P} (hq : C.pend q ≠ none) (hann : (C.loc q).pc.HasAnn)
    (h : C.M.A.time = (C.loc q).ann.time) : C.M.A = (C.loc q).ann := by
  by_cases h0 : C.M.A.time = 0
  · rw [hI.A_zero h0, hI.ann_zero q hq hann (h ▸ h0)]
  · obtain ⟨q₁, k₁, o₁, a1, -, a3, a4⟩ := hI.A_pos h0
    obtain ⟨q₂, k₂, o₂, b1, -, b3, b4⟩ := hI.ann_pos q hq hann (h ▸ h0)
    rw [← h, a1] at b1; simp only [Option.some.injEq, Prod.mk.injEq] at b1
    obtain ⟨rfl, rfl, rfl⟩ := b1
    exact AVal.ext h (a3.trans b3.symm) (a4.trans b4.symm)

/-- A current operation is done iff the own cell no longer holds `(t, Null)`. -/
lemma done_cur_iff (hI : CInv C G) {q : P} {o : T.Op} (ho : C.pend q = some o)
    (h3 : (C.loc q).pc.Past3) (h4 : (C.loc q).pc ≠ .l4) :
    Done C G (C.loc q).t ↔ C.M.cell (C.loc q).me ≠ ⟨(C.loc q).t, .null⟩ := by
  have hcur := hI.cur q o ho h3
  have ht0 : (C.loc q).t ≠ 0 := by
    intro h; have := (hI.ts_range (C.loc q).t).1 (by simp [hcur]); omega
  constructor
  · intro hd; exact hd.cell_ne ht0 hcur
  · intro hc; exact Or.inr ⟨q, G.k q, o, hcur, Or.inr h4, hc⟩

end state

namespace Trace

variable (tr : Trace T P cellInit)

/-- **Lemma B.1.21**: after an execution of line 7 for an operation, it is done. -/
theorem done_after_l7 {m : ℕ} (hm : m < tr.N) {q : P} (hl : tr.lbl m = .tau q)
    (hpc : ((tr.C m).loc q).pc = .l7) :
    Done (tr.C (m + 1)) (tr.G (m + 1)) ((tr.C m).loc q).snap.time := by
  have hI := tr.inv hm.le
  obtain ⟨hp, -, -, hM, hloc⟩ := tr.step_tau hm hl
  by_cases h0 : ((tr.C m).loc q).snap.time = 0
  · exact Or.inl h0
  obtain ⟨q', k, o, h1, h2, h3, r, h4, -⟩ := hI.snap_pos q hp (by simp [hpc, PC.HasSnap]) h0
  refine Or.inr ⟨q', k, o, tr.ts_mono (Nat.le_succ m) hm h1, ?_, ?_⟩
  · -- written stays written
    unfold WrittenAt at h2 ⊢
    rw [tr.stepG m hm, hl, hloc]
    have hk : (augStep (tr.C m) (.tau q) (tr.G m)).k = (tr.G m).k := by
      simp only [augStep]; split <;> (try split_ifs) <;> (try split) <;> rfl
    rw [hk]
    rcases eq_or_ne q' q with rfl | hq
    · simp [effect, hpc]
    · simp only [Function.update_of_ne hq]; exact h2
  · have hme : ((tr.C (m + 1)).loc q').me = ((tr.C m).loc q').me := by
      rw [hloc]; by_cases hq : q' = q
      · subst hq; simp [effect, hpc, Loc.me]
      · simp [Function.update_of_ne hq]
    rw [hme, hM]
    simp only [effect, hpc]
    rw [← h3, Function.update_self]
    unfold cellCAS; split_ifs with hc
    · simp [h4]
    · exact hc

/-- **Lemma B.1.22**: when `S` changes, the operation it held is done. -/
theorem done_of_S_change {m : ℕ} (hm : m < tr.N) (h : (tr.C (m + 1)).M.S ≠ (tr.C m).M.S) :
    Done (tr.C m) (tr.G m) (tr.C m).M.S.time := by
  obtain ⟨q, hl, hpc, hS, -⟩ := tr.S_change hm h
  obtain ⟨hp, -⟩ := tr.step_tau hm hl
  have := (tr.inv hm.le).copied q hp (by simp [hpc, PC.Copied]) hS
  rw [hS]; exact this

/-- The linearization only grows. -/
theorem lin_step {m : ℕ} (hm : m < tr.N) : ∃ X, (tr.G (m + 1)).lin = (tr.G m).lin ++ X := by
  rw [tr.stepG m hm]
  cases tr.lbl m with
  | inv p o => exact ⟨[], by simp [augStep]⟩
  | ret p r => exact ⟨[], by simp [augStep]⟩
  | tau p =>
    simp only [augStep]
    split <;> (try split_ifs) <;> (try split) <;> first | exact ⟨_, rfl⟩ | exact ⟨[], by simp⟩

theorem lin_prefix {n m : ℕ} (hnm : n ≤ m) (hm : m ≤ tr.N) :
    ∃ X, (tr.G m).lin = (tr.G n).lin ++ X := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ m _ ih =>
    obtain ⟨X, hX⟩ := ih (by omega)
    obtain ⟨Y, hY⟩ := tr.lin_step (m := m) (by omega)
    exact ⟨X ++ Y, by rw [hY, hX, List.append_assoc]⟩

/-- A change of `S` appends an operation to the linearization. -/
theorem lin_of_S_change {m : ℕ} (hm : m < tr.N) (h : (tr.C (m + 1)).M.S ≠ (tr.C m).M.S) :
    ∃ x, (tr.G (m + 1)).lin = (tr.G m).lin ++ [x] := by
  obtain ⟨q, hl, hpc, hS, -⟩ := tr.S_change hm h
  obtain ⟨hp, -⟩ := tr.step_tau hm hl
  obtain ⟨q', o', hts, -, -⟩ := (tr.inv hm.le).l13 q hp hpc hS
  rw [tr.stepG m hm, hl]
  exact ⟨((q', (tr.G m).k q'), o'), by simp [augStep, hpc, hS, hts]⟩

/-- The value of `S` determines the linearization (given that it only grows). -/
theorem lin_eq_of_S_eq {a b : ℕ} (hab : a ≤ b) (hb : b ≤ tr.N)
    (h : (tr.C a).M.S = (tr.C b).M.S) : (tr.G a).lin = (tr.G b).lin := by
  obtain ⟨X, hX⟩ := tr.lin_prefix hab hb
  have hIa := tr.inv (hab.trans hb)
  have hIb := tr.inv hb
  by_cases h0 : (tr.C a).M.S.time = 0
  · rw [(hIa.S_zero h0).1, (hIb.S_zero (h ▸ h0)).1]
  obtain ⟨q, k, o, h1, -, h3, -⟩ := hIa.S_pos h0
  obtain ⟨q', k', o', h1', -, h3', -⟩ := hIb.S_pos (h ▸ h0)
  rw [← h, tr.ts_mono hab hb h1] at h1'
  simp only [Option.some.injEq, Prod.mk.injEq] at h1'
  obtain ⟨rfl, rfl, rfl⟩ := h1'
  rw [hX]
  rcases List.eq_nil_or_concat X with hx | ⟨L, y, rfl⟩
  · rw [hx, List.append_nil]
  · exfalso
    simp only [List.concat_eq_append] at hX
    rw [hX, ← List.append_assoc, List.getLast?_concat] at h3'
    cases h3'
    have hnd := hIb.lin_nodup
    rw [hX, ← List.append_assoc, List.map_append, List.map_append] at hnd
    have hmem : ((q, k), o) ∈ (tr.G a).lin := List.mem_of_getLast? h3
    have := List.nodup_append.1 hnd
    exact this.2.2 _ (List.mem_append_left _ (List.mem_map_of_mem hmem)) _ (by simp) rfl

/-- **`S` never takes the same value twice** (Lemma B.1.25 / Proposition B.1.24). -/
theorem S_ne_of_change {a e b : ℕ} (hae : a ≤ e) (heb : e < b) (hb : b ≤ tr.N)
    (h : (tr.C (e + 1)).M.S ≠ (tr.C e).M.S) : (tr.C a).M.S ≠ (tr.C b).M.S := by
  intro hS
  have h1 := tr.lin_eq_of_S_eq (hae.trans heb.le) hb hS
  obtain ⟨X, hX⟩ := tr.lin_prefix hae (by omega)
  obtain ⟨x, hx⟩ := tr.lin_of_S_change (by omega) h
  obtain ⟨Y, hY⟩ := tr.lin_prefix (show e + 1 ≤ b by omega) hb
  have := congrArg List.length (h1.trans (hY.trans (by rw [hx, hX])))
  simp at this

end Trace

end Podc.GeneralizedCAS
