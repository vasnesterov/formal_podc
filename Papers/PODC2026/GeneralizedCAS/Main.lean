import Papers.PODC2026.GeneralizedCAS.Linearizable
import Papers.PODC2026.GeneralizedCAS.Counting

/-!
# Hadzilacos–Thiessen–Toueg (PODC 2026): Theorems 4 and 5 for Algorithm 1

* `step_bound` — **Theorem 5**: an operation of `p` takes at most `105 c + 44` memory steps
  (plus its invocation and response), where `c` is the point contention when `p` executes line 3.
* `waitFree` — wait-freedom (part of Theorem 4).
* `space_bound` — the space complexity part of Theorem 4.
* `theorem4` — Algorithm 1 is a linearizable, wait-free universal construction.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]
variable {cellInit : ℕ → CellVal T.Resp}

namespace Trace

variable (tr : Trace T P cellInit)

/-- Only finitely many processes have a pending operation at any time. -/
theorem pend_finite {n : ℕ} (hn : n ≤ tr.N) : {q | (tr.C n).pend q ≠ none}.Finite := by
  induction n with
  | zero => rw [tr.zeroC]; simp [Impl.initCfg]
  | succ n ih =>
    refine ((ih (by omega)).union (Set.finite_singleton (tr.lbl n).proc)).subset ?_
    intro q hq
    by_cases hp : (tr.lbl n).proc = q
    · exact Or.inr hp.symm
    · left; have := (tr.step_other (by omega) hp).2.1; simp only [Set.mem_setOf_eq] at hq ⊢
      rwa [this] at hq

/-- The point contention at time `n` (Definition 1): the number of pending operations. -/
noncomputable def contention (n : ℕ) : ℕ := {q | (tr.C n).pend q ≠ none}.ncard

end Trace

namespace OpStart

variable {tr : Trace T P cellInit} {p : P} {n3 : ℕ} (h : OpStart tr p n3)
include h

/-- `|S(o)| ≤ c`: the operations of `S(o)` are pending at time `n3` (Theorem B.2.15). -/
theorem card_SO_le : h.SO.card ≤ tr.contention n3 := by
  classical
  have hI := tr.inv h.lt.le
  have hfin := tr.pend_finite h.lt.le
  obtain ⟨f, hfs, hfn⟩ : ∃ f : ℕ → P,
      (∀ τ, (∃ q o, (tr.G n3).ts τ = some (q, (tr.G n3).k q, o)) →
        ∃ o, (tr.G n3).ts τ = some (f τ, (tr.G n3).k (f τ), o)) ∧
      (∀ τ, (¬ ∃ q o, (tr.G n3).ts τ = some (q, (tr.G n3).k q, o)) → f τ = p) :=
    ⟨fun τ => if hτ : ∃ q o, (tr.G n3).ts τ = some (q, (tr.G n3).k q, o) then hτ.choose else p,
      fun τ hτ => by simp only [dif_pos hτ]; exact hτ.choose_spec,
      fun τ hτ => by simp only [dif_neg hτ]⟩
  rw [Trace.contention, Set.ncard_eq_toFinset_card _ hfin]
  refine Finset.card_le_card_of_injOn f (fun τ hτ => ?_) (fun τ hτ τ' hτ' he => ?_)
  · simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_cases hx : ∃ q o, (tr.G n3).ts τ = some (q, (tr.G n3).k q, o)
    · obtain ⟨o, ho⟩ := hfs τ hx; rw [(hI.ts_cur _ _ _ ho).1]; simp
    · rw [hfn τ hx]; exact h.pend_n3
  · -- injectivity
    have hm : ∀ {σ}, σ ∈ (h.SO : Set ℕ) → σ ≠ h.t →
        ∃ o, (tr.G n3).ts σ = some (f σ, (tr.G n3).k (f σ), o) := by
      intro σ hσ hne
      simp only [Finset.mem_coe, OpStart.SO, Finset.mem_filter] at hσ
      exact hfs σ (hσ.2.resolve_left hne)
    have hpt : f h.t = p := by
      have : ¬ ∃ q o, (tr.G n3).ts h.t = some (q, (tr.G n3).k q, o) := by
        rintro ⟨q, o, hx⟩
        have := (hI.ts_range h.t).1 (by simp [hx]); simp [OpStart.t] at this
      exact hfn _ this
    have hnotp : ∀ {σ o}, (tr.G n3).ts σ = some (p, (tr.G n3).k p, o) → False := by
      intro σ o hx; have := (hI.ts_cur σ p o hx).2.1; rw [h.pc] at this; exact this
    by_cases e1 : τ = h.t <;> by_cases e2 : τ' = h.t
    · rw [e1, e2]
    · obtain ⟨o', ho'⟩ := hm hτ' e2
      rw [e1, hpt] at he; rw [← he] at ho'; exact (hnotp ho').elim
    · obtain ⟨o, ho⟩ := hm hτ e1
      rw [e2, hpt] at he; rw [he] at ho; exact (hnotp ho).elim
    · obtain ⟨o, ho⟩ := hm hτ e1
      obtain ⟨o', ho'⟩ := hm hτ' e2
      rw [he] at ho
      exact hI.ts_cur_inj ho ho'

end OpStart


namespace Trace

variable (tr : Trace T P cellInit)

open Classical in
/-- One step of the step counter of `p` while its operation continues. -/
theorem ns_step {p : P} {i : ℕ} (hi : i < tr.N) (hp : (tr.C i).pend p ≠ none)
    (hk : (tr.G (i + 1)).k p = (tr.G i).k p) :
    (tr.C (i + 1)).pend p ≠ none ∧
    (tr.G (i + 1)).ns p = (tr.G i).ns p + (if tr.lbl i = .tau p then 1 else 0) := by
  classical
  by_cases hq : (tr.lbl i).proc = p
  · have hs := tr.stepC i hi
    cases hl : tr.lbl i with
    | inv q o =>
      rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
      exact absurd (step_inv_eff cellInit hs).1 hp
    | ret q r =>
      rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
      exfalso
      have : (tr.G (i + 1)).k q = (tr.G i).k q + 1 := by rw [tr.stepG i hi, hl]; simp [augStep]
      omega
    | tau q =>
      rw [hl] at hq; simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, hpend, -, -⟩ := tr.step_tau hi hl
      refine ⟨by rw [hpend]; exact hp, ?_⟩
      rw [tr.stepG i hi, hl]; simp only [augStep, if_true]
      split <;> (try split_ifs) <;> (try split) <;> simp
  · obtain ⟨-, e2, -, -, e5, -⟩ := tr.step_other hi hq
    have : ¬ tr.lbl i = .tau p := fun h => hq (by rw [h]; rfl)
    rw [e2, e5]; simp [this, hp]

open Classical in
theorem ns_count {p : P} {a m : ℕ} (ham : a ≤ m) (hm : m ≤ tr.N) (hp : (tr.C a).pend p ≠ none)
    (hk : (tr.G m).k p = (tr.G a).k p) :
    (tr.G m).ns p = (tr.G a).ns p + ((Finset.Ico a m).filter (fun i => tr.lbl i = Label.tau p)).card ∧
      (tr.C m).pend p ≠ none := by
  classical
  induction m, ham using Nat.le_induction with
  | base => simp [hp]
  | succ m ham ih =>
    have hkm : (tr.G m).k p = (tr.G a).k p :=
      le_antisymm (hk ▸ tr.k_mono (Nat.le_succ m) hm) (tr.k_mono ham (by omega))
    obtain ⟨i1, i2⟩ := ih (by omega) hkm
    obtain ⟨j1, j2⟩ := tr.ns_step (i := m) (by omega) i2 (by rw [hk, hkm])
    refine ⟨?_, j1⟩
    rw [j2, i1, Nat.Ico_succ_right_eq_insert_Ico ham, Finset.filter_insert]
    split_ifs with hl <;> simp [Finset.card_insert_of_notMem]; omega

end Trace

open Classical in
/-- **Theorem 5** (Theorem B.2.15). Suppose process `p` executes line 3 of an operation `o` at
time `n3`, and let `c` be the point contention at that time. Then during every interval
`[a, m)` inside `o`, `p` takes at most `105 c + 44` memory steps; so `o` consists of at most
`105 c + 46` steps of `p` (counting its invocation and its response). -/
theorem step_bound {tr : Trace T P cellInit} {p : P} {n3 : ℕ} (h : OpStart tr p n3) {a m : ℕ}
    (ham : a ≤ m) (hm : h.InOp m) (ha : (tr.C a).pend p ≠ none) (hka : (tr.G a).k p = h.k0) :
    ((Finset.Ico a m).filter (fun i => tr.lbl i = Label.tau p)).card ≤ 105 * tr.contention n3 + 44 := by
  classical
  obtain ⟨hc, -⟩ := tr.ns_count ham hm.2.1 ha (by rw [hm.2.2, hka])
  have h1 := ((tr.inv2 hm.2.1).ns p (h.inOp hm).1).le
  have h2 := h.it_le hm
  have h3 := h.card_SO_le
  have : ((Finset.Ico a m).filter (fun i => tr.lbl i = Label.tau p)).card ≤ (tr.G m).ns p := by
    rw [hc]; omega
  omega


/-- If a predicate holds at most `B` times on every interval `[a, M)`, it eventually fails. -/
theorem eventually_not_of_count {Q : ℕ → Prop} [DecidablePred Q] {a B : ℕ}
    (h : ∀ M, a ≤ M → ((Finset.Ico a M).filter Q).card ≤ B) : ∃ N0, ∀ m ≥ N0, ¬ Q m := by
  by_contra hc
  push_neg at hc
  have hinf : {m | a ≤ m ∧ Q m}.Infinite := by
    refine Set.infinite_of_not_bddAbove fun ⟨b, hb⟩ => ?_
    obtain ⟨m, hm, hq⟩ := hc (max a b + 1)
    have := hb ⟨by omega, hq⟩; omega
  obtain ⟨t, ht, hcard⟩ := hinf.exists_subset_card_eq (B + 1)
  have hsub : t ⊆ (Finset.Ico a (t.sup id + 1)).filter Q := by
    intro x hx
    have := ht hx
    simp only [Set.mem_setOf_eq] at this
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨this.1, Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)⟩, this.2⟩
  have := (Finset.card_le_card hsub).trans (h _ (by
    rcases t.eq_empty_or_nonempty with he | ⟨x, hx⟩
    · rw [he] at hcard; simp at hcard
    · have := (ht hx).1; have := Finset.le_sup (f := id) hx; simp at this; omega))
  omega

variable (cellInit) in
/-- The ghost variables along an infinite execution. -/
noncomputable def ghostSeq (e : (alg T P cellInit).InfExec) : ℕ → Ghost T P
  | 0 => ginit T P
  | n + 1 => augStep (e.cfg n) (e.lbl n) (ghostSeq e n)

/-- The prefix of length `M` of an infinite execution, as a trace. -/
noncomputable def traceOf (e : (alg T P cellInit).InfExec) (M : ℕ) : Trace T P cellInit where
  N := M
  C := e.cfg
  G := ghostSeq cellInit e
  lbl := e.lbl
  zeroC := e.cfg_zero
  zeroG := rfl
  stepC n _ := e.step_eq n
  stepG n _ := rfl

open Classical in
/-- **Wait-freedom** (Theorem 4): an operation that stays pending forever takes only finitely many
steps. (Theorem 5 bounds their number by `105 c + 44`.) -/
theorem waitFree : (alg T P cellInit).WaitFree := by
  intro e p n hpend
  -- `k` is constant from time `n` on
  have hk : ∀ m ≥ n, (ghostSeq cellInit e m).k p = (ghostSeq cellInit e n).k p := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [← ih]
      show (augStep (e.cfg m) (e.lbl m) (ghostSeq cellInit e m)).k p = _
      cases hl : e.lbl m with
      | inv q o => rfl
      | ret q r =>
        by_cases hq : q = p
        · subst hq
          have := (step_ret_eff cellInit (hl ▸ e.step_eq m)).2.2.1
          exact absurd (by rw [this]; simp) (hpend (m + 1) (by omega))
        · simp [augStep, Function.update_of_ne (Ne.symm hq)]
      | tau q => simp only [augStep]; split <;> (try split_ifs) <;> (try split) <;> rfl
  suffices ∃ a B, ∀ M, a ≤ M → ((Finset.Ico a M).filter (fun i => e.lbl i = .tau p)).card ≤ B by
    obtain ⟨a, B, hB⟩ := this
    exact eventually_not_of_count hB
  by_cases h3 : ∃ m0 ≥ n, ((e.cfg m0).loc p).pc.Past3
  · obtain ⟨m0, hm0, hpast⟩ := h3
    have hl3 := (traceOf e (m0 + 1)).l3Time (n := m0) (by simp [traceOf]) p (hpend m0 hm0) hpast
    obtain ⟨b1, b2, b3, b4⟩ := hl3
    simp only [traceOf] at b1 b2 b3 b4
    set n3 := (ghostSeq cellInit e m0).lt p .l3 with hn3
    have hstart : ∀ M, m0 < M → OpStart (traceOf e M) p n3 :=
      fun M hM => ⟨by simp only [traceOf]; omega, b2, b3⟩
    refine ⟨m0, 105 * (traceOf e (m0 + 1)).contention n3 + 44, fun M hM => ?_⟩
    rcases eq_or_lt_of_le hM with rfl | hM'
    · simp
    have hs := hstart M hM'
    have hin : hs.InOp M := ⟨by omega, by simp [traceOf],
      by show (ghostSeq cellInit e M).k p = (ghostSeq cellInit e n3).k p
         rw [hk M (by omega), b4, hk m0 hm0]⟩
    have := step_bound hs hM hin (hpend m0 hm0)
      (by show (ghostSeq cellInit e m0).k p = (ghostSeq cellInit e n3).k p; rw [b4])
    convert this using 1
    · congr 1
    · simp [traceOf, Trace.contention]
  · push_neg at h3
    refine ⟨n, 1, fun M hM => ?_⟩
    have tr := traceOf e M
    obtain ⟨hc, -⟩ := (traceOf e M).ns_count hM (by simp [traceOf]) (hpend n le_rfl)
      (by show (ghostSeq cellInit e M).k p = _; exact hk M hM)
    have hns := (Trace.inv2 (traceOf e M) (n := M) (by simp [traceOf])).ns p (hpend M hM)
    have hpc := h3 M hM
    simp only [traceOf] at hc hns
    have : (ghostSeq cellInit e M).ns p ≤ 1 := by
      revert hns hpc; cases ((e.cfg M).loc p).pc <;> simp [PC.Past3, PC.NsOK] <;> omega
    rw [hc] at this
    refine le_trans (le_of_eq ?_) (le_trans (Nat.le_add_left _ _) this)
    congr 1


theorem Trace.k_eq_of_noret (tr : Trace T P cellInit) {p : P} {lo m : ℕ} (hlo : lo ≤ m)
    (hm : m ≤ tr.N) (hnr : ∀ i r, lo ≤ i → i < m → tr.lbl i ≠ .ret p r) :
    ∀ i, lo ≤ i → i ≤ m → (tr.G i).k p = (tr.G lo).k p := by
  intro i h1 h2
  induction i, h1 using Nat.le_induction with
  | base => rfl
  | succ i hi ih =>
    rw [← ih (by omega), tr.stepG i (by omega)]
    have := hnr i
    cases hl : tr.lbl i with
    | inv q o => rfl
    | ret q r =>
      have hq : q ≠ p := fun e => this r hi (by omega) (by rw [hl, e])
      simp [augStep, Function.update_of_ne hq.symm]
    | tau q => simp only [augStep]; split <;> (try split_ifs) <;> (try split) <;> rfl

open Classical in
/-- **Theorem 5.** Suppose process `p` executes line 3 of an operation `o` at time `n3`, and let
`c` be the point contention at that time. Then in every interval `[a, m)` during `o` (`p` is
pending at `a`, and does not return before `m`), `p` takes at most `105 c + 44` memory steps.
Hence `o` consists of at most `105 c + 46` steps of `p` (with its invocation and response). By
`exists_trace`, this applies to every finite execution of Algorithm 1. -/
theorem theorem5 {tr : Trace T P cellInit} {p : P} {n3 a m : ℕ} (h : OpStart tr p n3)
    (ham : a ≤ m) (h3m : n3 < m) (hm : m ≤ tr.N) (ha : (tr.C a).pend p ≠ none)
    (hnr : ∀ i r, min a n3 ≤ i → i < m → tr.lbl i ≠ .ret p r) :
    ((Finset.Ico a m).filter (fun i => tr.lbl i = Label.tau p)).card ≤
      105 * tr.contention n3 + 44 := by
  have hk := tr.k_eq_of_noret (by omega) hm hnr
  refine step_bound h ham ⟨h3m, hm, ?_⟩ ha ?_
  · show (tr.G m).k p = (tr.G n3).k p
    rw [hk m (by omega) le_rfl, hk n3 (by omega) (by omega)]
  · show (tr.G a).k p = (tr.G n3).k p
    rw [hk a (by omega) ham, hk n3 (by omega) (by omega)]

/-! ### Finite executions as traces -/

theorem arun_take_isSome {α : List (Label P T)} {C : Cfg T P}
    (h : (alg T P cellInit).run α = some C) (n : ℕ) : (arun cellInit (α.take n)).isSome := by
  obtain ⟨G, hG⟩ := exists_arun cellInit h
  rw [← List.take_append_drop n α, arun, arunFrom_append] at hG
  cases hx : arunFrom cellInit ((alg T P cellInit).initCfg, ginit T P) (α.take n) with
  | none => rw [hx] at hG; simp at hG
  | some x => simp [arun, hx]

/-- Every finite execution of Algorithm 1 is a trace (`d` is an arbitrary default label, used
beyond the end of the execution). -/
theorem exists_trace {α : List (Label P T)} {C : Cfg T P}
    (h : (alg T P cellInit).run α = some C) (d : Label P T) :
    ∃ tr : Trace T P cellInit, tr.N = α.length ∧ (∀ i (hi : i < α.length), tr.lbl i = α[i]) ∧
      tr.C α.length = C ∧ ∀ n ≤ α.length, (alg T P cellInit).run (α.take n) = some (tr.C n) := by
  classical
  let X : ℕ → Cfg T P × Ghost T P := fun n => (arun cellInit (α.take n)).getD
    ((alg T P cellInit).initCfg, ginit T P)
  have hX : ∀ n, arun cellInit (α.take n) = some (X n) := fun n => by
    have := arun_take_isSome h n
    cases hx : arun cellInit (α.take n) with
    | none => rw [hx] at this; simp at this
    | some x => simp [X, hx]
  refine ⟨⟨α.length, fun n => (X n).1, fun n => (X n).2, fun n => α.getD n d, ?_, ?_, ?_, ?_⟩,
    rfl, fun i hi => by simp [List.getD_eq_getElem?_getD, hi], ?_, ?_⟩
  · have := hX 0; simp only [List.take_zero, arun, arunFrom, Option.some.injEq] at this
    rw [← this]
  · have := hX 0; simp only [List.take_zero, arun, arunFrom, Option.some.injEq] at this
    rw [← this]
  · intro n hn
    have h1 := hX (n + 1)
    rw [List.take_succ, List.getElem?_eq_getElem hn, Option.toList_some, arun_concat, hX n] at h1
    simp only [Option.bind_some] at h1
    cases hs : (alg T P cellInit).step (X n).1 α[n] with
    | none => rw [hs] at h1; simp at h1
    | some C' =>
      rw [hs] at h1; simp only [Option.map_some, Option.some.injEq] at h1
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
      rw [hs, ← h1]
  · intro n hn
    have h1 := hX (n + 1)
    rw [List.take_succ, List.getElem?_eq_getElem hn, Option.toList_some, arun_concat, hX n] at h1
    simp only [Option.bind_some] at h1
    cases hs : (alg T P cellInit).step (X n).1 α[n] with
    | none => rw [hs] at h1; simp at h1
    | some C' =>
      rw [hs] at h1; simp only [Option.map_some, Option.some.injEq] at h1
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
      rw [← h1]
  · show (X α.length).1 = C
    have h2 := hX α.length
    rw [List.take_length] at h2
    have := arun_fst cellInit h2
    rw [h] at this
    exact (Option.some.inj this).symm
  · intro n hn; exact arun_fst cellInit (hX n)


/-! ### Space complexity -/

/-- The space complexity (Definition 3): the statically allocated base objects `C`, `A`, `S` and
the dummy cell, plus the cells allocated by the memory manager. -/
def space (C : Cfg T P) : ℕ := 4 + C.M.mm

theorem cells_owned {α : List (Label P T)} {C : Cfg T P} {G : Ghost T P}
    (h : arun cellInit α = some (C, G)) :
    ∀ j < C.M.mm, ∃ q ∈ α.map Label.proc, (C.loc q).ptr = some (j : Ptr) := by
  refine (arun_induction cellInit
    (Q := fun α C G => CInv C G ∧ ∀ j < C.M.mm, ∃ q ∈ α.map Label.proc, (C.loc q).ptr = some (j : Ptr))
    ⟨cinv_init cellInit, fun j hj => by simp [Impl.initCfg, alg, Cfg.M, view] at hj⟩
    (fun α C G ℓ C' _ ⟨hI, hJ⟩ hs => ⟨hI.step cellInit hs, ?_⟩) h).2
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, hmem, hloc⟩ := step_inv_eff cellInit hs
    have hM : Cfg.M C' = C.M := by simp [Cfg.M, hmem]
    intro j hj; rw [hM] at hj; obtain ⟨q, hq, hptr⟩ := hJ j hj
    refine ⟨q, by simp [hq], ?_⟩
    rw [hloc]; by_cases hqp : q = p
    · subst hqp; simpa [Loc.invoke] using hptr
    · rw [Function.update_of_ne hqp]; exact hptr
  | ret p r =>
    obtain ⟨-, -, -, hmem, hloc⟩ := step_ret_eff cellInit hs
    have hM : Cfg.M C' = C.M := by simp [Cfg.M, hmem]
    intro j hj; rw [hM] at hj; obtain ⟨q, hq, hptr⟩ := hJ j hj
    refine ⟨q, by simp [hq], ?_⟩
    rw [hloc]; by_cases hqp : q = p
    · subst hqp; simpa using hptr
    · rw [Function.update_of_ne hqp]; exact hptr
  | tau p =>
    obtain ⟨hp, hmem, -, hM, hloc⟩ := step_tau_eff cellInit hs
    intro j hj
    by_cases hpc : (C.loc p).pc = .l2
    · have hnone : (C.loc p).ptr = none := (hI.pc_ptr p hp).1 hpc
      rw [hM] at hj; simp only [effect, hpc] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨q, hq, hptr⟩ := hJ j hj
        have hqp : q ≠ p := by rintro rfl; rw [hnone] at hptr; cases hptr
        refine ⟨q, by simp [hq], ?_⟩
        rw [hloc, Function.update_of_ne hqp]; exact hptr
      · refine ⟨p, by simp [Label.proc], ?_⟩
        rw [hloc]; simp [effect, hpc]
    · have hmm : (Cfg.M C').mm = C.M.mm := by
        rw [hM]; cases hc : (C.loc p).pc <;> simp [effect, hc] at hpc ⊢ <;>
          (try (unfold pc5; split_ifs <;> (try split) <;> rfl)) <;> (try (split_ifs <;> rfl))
      rw [hmm] at hj
      obtain ⟨q, hq, hptr⟩ := hJ j hj
      refine ⟨q, by simp [hq], ?_⟩
      rw [hloc]; by_cases hqp : q = p
      · subst hqp; rw [Function.update_self]
        rw [← hptr]
        cases hc : (C.loc q).pc <;> simp [effect, hc] at hpc ⊢
        all_goals first
          | (rcases pc5_cases (C.loc q) C.M with h5 | h5 | ⟨r, h5⟩ <;> simp [h5])
          | (split_ifs <;> rfl)
          | exact absurd hc (hmem _)
      · rw [Function.update_of_ne hqp]; exact hptr

/-- **Theorem 4 (space complexity)**: at any time, the space used is at most `4` plus the number
of processes that have participated (taken a step) so far. -/
theorem space_bound {α : List (Label P T)} {C : Cfg T P} (h : (alg T P cellInit).run α = some C) :
    space C ≤ 4 + (α.map Label.proc).toFinset.card := by
  classical
  obtain ⟨G, hG⟩ := exists_arun cellInit h
  have hI := arun_inv cellInit hG
  have hown := cells_owned hG
  choose f hf1 hf2 using hown
  have : C.M.mm ≤ (α.map Label.proc).toFinset.card := by
    rcases Nat.eq_zero_or_pos C.M.mm with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    have := Finset.card_le_card_of_injOn (s := Finset.range C.M.mm)
      (t := (α.map Label.proc).toFinset) (fun j => if hj : j < C.M.mm then f j hj else
        f 0 h0) ?_ ?_
    · simpa using this
    · intro j hj; simp only [Finset.coe_range, Set.mem_Iio] at hj
      simp only [dif_pos hj, List.coe_toFinset, Set.mem_setOf_eq]; exact hf1 j hj
    · intro j hj j' hj' he
      simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
      simp only [dif_pos hj, dif_pos hj'] at he
      have h1 := hf2 j hj; have h2 := hf2 j' hj'
      rw [he, h2] at h1
      exact_mod_cast (Option.some.inj h1).symm
  unfold space; omega

/-- **Theorem 4**: Algorithm 1 is a linearizable, wait-free universal construction for the
infinite-arrival model (any set of processes `P`, any sequential specification `T`); its space
complexity at any time is at most `4` plus the number of processes that have participated. -/
theorem theorem4 :
    (alg T P cellInit).Linearizable ∧ (alg T P cellInit).WaitFree ∧
      ∀ α C, (alg T P cellInit).run α = some C →
        space C ≤ 4 + (α.map Label.proc).toFinset.card :=
  ⟨linearizable cellInit, waitFree, fun _ _ h => space_bound h⟩

end Podc.GeneralizedCAS
