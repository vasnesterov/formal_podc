import Papers.PODC2015.SetAgreementSpace.Lemma3
import Cslib.Foundations.Data.Nat.Descent

/-!
# Liveness of the corrected Figure 3: `m`-obstruction-freedom (Section 4.1)

The original algorithm of Figure 3 (`fig3 false`) is not obstruction-free (`Counterexample.lean`):
the proof of Lemma 5 (Case 2) assumes that adopting a value (lines 11–13) changes `pref`. With the
extra guard of `fig3 true` (adopt only if the value of the first duplicated pair differs from
`pref`, otherwise advance `i`, line 14) the paper's argument goes through, and we prove

* `fig3Fixed_mObstructionFree`: `fig3 true n m r` is `m`-obstruction-free on one-shot executions,
  for **all** `n`, `m` and `r ≥ 1` (the size `r = n + 2m - k` of the paper is only needed for
  safety).

The proof follows Section 4.1. Let `e` be an infinite one-shot execution and `S` the set of
processes taking infinitely many steps, `|S| ≤ m`, `S ≠ ∅`. From some time `T₀` on only processes
of `S` step, each of them is pending forever (one-shot: after its response a process can never
step again) and therefore never decides (`Liveness.Setting`, `Liveness.exists_setting`).

* `Liveness.lemma5` (**Lemma 5**): some process of `S` advances (line 14) infinitely often.
  Otherwise, after a time `μ`, every `q ∈ S` keeps its position `i_q`; the components `NM` not of
  the form `i_q` are constant. A pair written after `μ` cannot also lie in `NM` (its writer would
  see it at another position at its next scan and advance — Case 1 of the paper); components of
  `M` hold pairwise different pairs. Hence the first duplicated pair lies in `NM` and its value
  `w` is constant (`Liveness.dupVal_congr`). Every scan adopts, so some process adopts `w`, and at
  its next scan the corrected guard (`dupVal ≠ pref`) fails: it advances. (The paper's Case 2
  instead claims that adoption always changes `pref`, which is false for `fig3 false`.)
* `Liveness.cor6` (**Corollary 6**): the advancing process updates every component again and
  again, so eventually every component holds a pair of a process of `S`.
* By **Lemma 3** (`lemma3`, `Lemma3.lean`) such a memory contains at most `|S| ≤ m` distinct
  pairs and no `⊥`, so the next scan satisfies line 9 (`Liveness.decideCond_of_run`) and the
  scanner decides — a contradiction (`Liveness.false_of_infSteppers`).

In fact the proof shows more: every infinite one-shot execution has more than `m` processes
taking infinitely many steps (the hypothesis that a given process is pending forever is not
used).
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

variable {V : Type} [DecidableEq V] [Inhabited V] {n m r : ℕ} [NeZero r]

namespace Liveness

set_option linter.unusedSectionVars false

/-! ### Single steps -/

section Steps

variable {fix : Bool} {C C' : Cfg V n r} {q : Fin n}

lemma step_upd (hp : C.pend q ≠ none) (hpc : (C.loc q).pc = .upd) :
    (fig3 fix n m r).step C (.tau q) = some
      { C with mem := Function.update C.mem ()
                 (Function.update (C.mem ()) (C.loc q).i (some ((C.loc q).pref, q))),
               loc := Function.update C.loc q { C.loc q with pc := .scan } } := by
  have hact : (fig3 fix n m r).act q (C.loc q) =
      .access () (.update (C.loc q).i ((C.loc q).pref, q)) (fun _ => { C.loc q with pc := .scan }) := by
    simp only [fig3, hpc]
  rw [Impl.step_tau_eq_some hp hact]

lemma step_scan (hp : C.pend q ≠ none) (hpc : (C.loc q).pc = .scan) :
    (fig3 fix n m r).step C (.tau q) = some
      { C with loc := Function.update C.loc q (afterScan fix m q (C.loc q) (C.mem ())) } := by
  have hact : (fig3 fix n m r).act q (C.loc q) =
      .access () .scan (fun s => afterScan fix m q (C.loc q) s) := by
    simp only [fig3, hpc]
  rw [Impl.step_tau_eq_some hp hact]
  have hm : Function.update C.mem () ((Mem V n r ()).δ (C.mem ()) SnapOpOpt.scan).1 = C.mem := by
    funext u; cases u; simp
  simp only [hm]

/-- Inversion of an internal step: it is an update or a scan. -/
lemma step_tau_cases (h : (fig3 fix n m r).step C (.tau q) = some C') :
    ((C.loc q).pc = .upd ∧
      C'.mem () = Function.update (C.mem ()) (C.loc q).i (some ((C.loc q).pref, q)) ∧
      C'.loc = Function.update C.loc q { C.loc q with pc := .scan }) ∨
    ((C.loc q).pc = .scan ∧ C'.mem () = C.mem () ∧
      C'.loc = Function.update C.loc q (afterScan fix m q (C.loc q) (C.mem ()))) := by
  have hp := (Impl.step_tau h).1
  cases hpc : (C.loc q).pc with
  | upd =>
    rw [step_upd hp hpc] at h; cases h
    exact Or.inl ⟨rfl, by simp, rfl⟩
  | scan =>
    rw [step_scan hp hpc] at h; cases h
    exact Or.inr ⟨rfl, rfl, rfl⟩
  | idle =>
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
    simp [fig3, hpc] at hact
  | ret =>
    obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
    simp [fig3, hpc] at hact

lemma afterScan_pc_of_not_decide {l : Loc V r} {s : Fin r → Cell V n}
    (hd : ¬ DecideCond m s) : (afterScan fix m q l s).pc = .upd := by
  unfold afterScan; split_ifs <;> rfl

lemma afterScan_of_adopt {l : Loc V r} {s : Fin r → Cell V n}
    (hd : ¬ DecideCond m s) (ha : AdoptCond fix s l.i l.pref q) :
    afterScan fix m q l s = { l with pc := .upd, pref := (dupVal s).getD l.pref } := by
  simp [afterScan, hd, ha]

lemma afterScan_of_not_adopt {l : Loc V r} {s : Fin r → Cell V n}
    (hd : ¬ DecideCond m s) (ha : ¬ AdoptCond fix s l.i l.pref q) :
    afterScan fix m q l s = { l with pc := .upd, i := l.i + 1 } := by
  simp [afterScan, hd, ha]

end Steps

/-! ### Steps along an infinite execution -/

section Exec

variable {fix : Bool} {e : (fig3 (V := V) fix n m r).InfExec} {q : Fin n}

/-- Internal step of `q` at time `t` that is an update. -/
lemma exec_upd {t : ℕ} {q : Fin n} (hl : e.lbl t = .tau q) (hpc : ((e.cfg t).loc q).pc = .upd) :
    (e.cfg (t + 1)).mem () = Function.update ((e.cfg t).mem ()) ((e.cfg t).loc q).i
      (some (((e.cfg t).loc q).pref, q)) ∧
    (e.cfg (t + 1)).loc q = { (e.cfg t).loc q with pc := .scan } := by
  have h := e.step_eq t
  rw [hl] at h
  rcases step_tau_cases h with ⟨-, h1, h2⟩ | ⟨h0, -⟩
  · exact ⟨h1, by rw [h2]; simp⟩
  · rw [hpc] at h0; cases h0

/-- Internal step of `q` at time `t` that is a scan. -/
lemma exec_scan {t : ℕ} {q : Fin n} (hl : e.lbl t = .tau q) (hpc : ((e.cfg t).loc q).pc = .scan) :
    (e.cfg (t + 1)).mem () = (e.cfg t).mem () ∧
    (e.cfg (t + 1)).loc q = afterScan fix m q ((e.cfg t).loc q) ((e.cfg t).mem ()) := by
  have h := e.step_eq t
  rw [hl] at h
  rcases step_tau_cases h with ⟨h0, -⟩ | ⟨-, h1, h2⟩
  · rw [hpc] at h0; cases h0
  · exact ⟨h1, by rw [h2]; simp⟩

/-- An internal step is an update or a scan. -/
lemma exec_tau_pc {t : ℕ} {q : Fin n} (hl : e.lbl t = .tau q) :
    ((e.cfg t).loc q).pc = .upd ∨ ((e.cfg t).loc q).pc = .scan := by
  have h := e.step_eq t
  rw [hl] at h
  rcases step_tau_cases h with ⟨h0, -⟩ | ⟨h0, -⟩
  · exact Or.inl h0
  · exact Or.inr h0

/-- The memory changes only by updates. -/
lemma exec_mem (t : ℕ) :
    (e.cfg (t + 1)).mem () = (e.cfg t).mem () ∨ ∃ q, e.lbl t = .tau q ∧
      ((e.cfg t).loc q).pc = .upd ∧ (e.cfg (t + 1)).mem () = Function.update ((e.cfg t).mem ())
        ((e.cfg t).loc q).i (some (((e.cfg t).loc q).pref, q)) := by
  have h := e.step_eq t
  cases hl : e.lbl t with
  | inv q o => rw [hl] at h; left; rw [(Impl.step_inv h).2.2.2.2]
  | ret q o => rw [hl] at h; left; rw [(Impl.step_ret h).2.2.1]
  | tau q =>
    rcases exec_tau_pc hl with hpc | hpc
    · exact Or.inr ⟨q, rfl, hpc, (exec_upd hl hpc).1⟩
    · exact Or.inl (exec_scan hl hpc).1

/-- The first step of `q` at or after `t`, if `q` steps infinitely often; the local state and
pending operation of `q` are unchanged until then. -/
lemma exists_next (hq : q ∈ e.infSteppers) (t : ℕ) :
    ∃ t' ≥ t, (e.lbl t').proc = q ∧ (e.cfg t').loc q = (e.cfg t).loc q ∧
      (e.cfg t').pend q = (e.cfg t).pend q := by
  classical
  have hex : ∃ k, (e.lbl (t + k)).proc = q := by
    obtain ⟨t₁, ht₁, h⟩ := hq t
    exact ⟨t₁ - t, by rw [Nat.add_sub_cancel' ht₁]; exact h⟩
  have hc := e.cfg_add_of_proc_ne fun j hj => Nat.find_min hex hj
  exact ⟨t + Nat.find hex, by omega, Nat.find_spec hex, hc.1, hc.2⟩

/-- A step of `q` that is not an invocation happens while `q` is pending. -/
lemma pend_of_proc {t : ℕ} {q : Fin n} (hl : (e.lbl t).proc = q) (hni : ∀ o, e.lbl t ≠ .inv q o) :
    (e.cfg t).pend q ≠ none := by
  have h := e.step_eq t
  cases hlt : e.lbl t with
  | inv q' o => rw [hlt] at hl hni; simp only [Label.proc] at hl; subst hl; exact absurd rfl (hni o)
  | ret q' o => rw [hlt] at h hl; simp only [Label.proc] at hl; subst hl; exact (Impl.step_ret h).1
  | tau q' => rw [hlt] at h hl; simp only [Label.proc] at hl; subst hl; exact (Impl.step_tau h).1

/-- An invocation of `q` between `t₀` (where `q` is idle) and a later step `t` of `q`. -/
lemma exists_inv_of_proc {t₀ t : ℕ} {q : Fin n} (h0 : (e.cfg t₀).pend q = none) (ht : t₀ ≤ t)
    (hl : (e.lbl t).proc = q) : ∃ b, t₀ ≤ b ∧ b ≤ t ∧ ∃ o, e.lbl b = .inv q o := by
  by_cases hi : ∃ o, e.lbl t = .inv q o
  · exact ⟨t, ht, le_rfl, hi⟩
  · push Not at hi
    obtain ⟨b, h1, h2, o, ho⟩ := e.exists_inv_between ht h0 (pend_of_proc hl hi)
    exact ⟨b, h1, h2.le, o, ho⟩

lemma two_le_opsOf {a b : ℕ} {q : Fin n} {o o' : V} (hab : a < b) (ha : e.lbl a = .inv q o)
    (hb : e.lbl b = .inv q o') : 2 ≤ (opsOf (e.pre (b + 1)) q).length := by
  have h1 := e.opsOf_pre_mono q (show a + 1 ≤ b by omega)
  rw [e.pre_succ, opsOf_concat, ha] at h1
  rw [e.pre_succ, opsOf_concat, hb]
  simp [Label.invOf] at h1 ⊢
  omega

/-- What a process that steps infinitely often does from some time on in a one-shot execution: it
is pending forever and all its steps are internal. -/
def StableAt (e : (fig3 (V := V) fix n m r).InfExec) (q : Fin n) (t : ℕ) : Prop :=
  (e.cfg t).pend q ≠ none ∧ ((e.lbl t).proc = q → e.lbl t = .tau q)

lemma exists_stable (hOS : ∀ t, OneShot (e.pre t)) (hq : q ∈ e.infSteppers) :
    ∃ T, ∀ t ≥ T, StableAt e q t := by
  have hpend : ∃ T, ∀ t ≥ T, (e.cfg t).pend q ≠ none := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, -, h₁⟩ := hq 0
    have hz : (e.cfg 0).pend q = none := by rw [e.cfg_zero]; rfl
    obtain ⟨a, -, ha, o, hao⟩ := exists_inv_of_proc hz (Nat.zero_le _) h₁
    obtain ⟨t₂, ht₂, h₂⟩ := hcon (t₁ + 1)
    obtain ⟨t₃, ht₃, h₃⟩ := hq t₂
    obtain ⟨b, hb, -, o', hbo⟩ := exists_inv_of_proc h₂ ht₃ h₃
    have := two_le_opsOf (show a < b by omega) hao hbo
    have := hOS (b + 1) q
    omega
  obtain ⟨T, hT⟩ := hpend
  refine ⟨T, fun t ht => ⟨hT t ht, fun hl => ?_⟩⟩
  have h := e.step_eq t
  cases hlt : e.lbl t with
  | inv q' o =>
    rw [hlt] at h hl; simp only [Label.proc] at hl; subst hl
    exact absurd (Impl.step_inv h).1 (hT t ht)
  | ret q' o =>
    rw [hlt] at h hl; simp only [Label.proc] at hl; subst hl
    have := (Impl.step_ret h).2.1
    exact absurd (by rw [this]; simp) (hT (t + 1) (by omega))
  | tau q' => rw [hlt] at hl; simp only [Label.proc] at hl; rw [hl]

end Exec

/-! ### The setting: from time `T₀` on only processes of `S` step, all pending forever -/

section Setting

variable {fix : Bool} {e : (fig3 (V := V) fix n m r).InfExec} {q : Fin n} {T₀ : ℕ}

/-- From time `T₀` on, only processes that step infinitely often take steps, and each of them is
pending and takes only internal steps. -/
def Setting (e : (fig3 (V := V) fix n m r).InfExec) (T₀ : ℕ) : Prop :=
  (∀ t ≥ T₀, (e.lbl t).proc ∈ e.infSteppers) ∧ ∀ q ∈ e.infSteppers, ∀ t ≥ T₀, StableAt e q t

lemma exists_setting (hOS : ∀ t, OneShot (e.pre t)) : ∃ T₀, Setting e T₀ := by
  have h : ∀ q : Fin n, ∃ T, ∀ t ≥ T,
      (q ∈ e.infSteppers → StableAt e q t) ∧ (q ∉ e.infSteppers → (e.lbl t).proc ≠ q) := by
    intro q
    by_cases hq : q ∈ e.infSteppers
    · obtain ⟨T, hT⟩ := exists_stable hOS hq
      exact ⟨T, fun t ht => ⟨fun _ => hT t ht, fun h => absurd hq h⟩⟩
    · have : ¬ ∀ N, ∃ t ≥ N, (e.lbl t).proc = q := hq
      push Not at this
      obtain ⟨T, hT⟩ := this
      exact ⟨T, fun t ht => ⟨fun h => absurd h hq, fun _ => hT t ht⟩⟩
  obtain ⟨T, -, hT⟩ := Nat.eventually_forall_of_finite h 0
  refine ⟨T, fun t ht => ?_, fun q hq t ht => (hT t ht q).1 hq⟩
  by_contra hc
  exact (hT t ht _).2 hc rfl

/-- The next step of `q ∈ S` after `t ≥ T₀` is internal, from the same local state. -/
lemma Setting.exists_step (hs : Setting e T₀) (hq : q ∈ e.infSteppers) {t : ℕ} (ht : T₀ ≤ t) :
    ∃ t' ≥ t, e.lbl t' = .tau q ∧ (e.cfg t').loc q = (e.cfg t).loc q := by
  obtain ⟨t', ht', hl, hloc, -⟩ := exists_next hq t
  exact ⟨t', ht', (hs.2 q hq t' (by omega)).2 hl, hloc⟩

/-- After `T₀`, processes of `S` never decide. -/
lemma Setting.not_decide (hs : Setting e T₀) (hq : q ∈ e.infSteppers) {t : ℕ} (ht : T₀ ≤ t)
    (hl : e.lbl t = .tau q) (hpc : ((e.cfg t).loc q).pc = .scan) :
    ¬ DecideCond m ((e.cfg t).mem ()) := by
  intro hd
  have h1 := (exec_scan hl hpc).2
  have hpc1 : ((e.cfg (t + 1)).loc q).pc = .ret := by
    rw [h1]; simp [afterScan, hd]
  obtain ⟨t', ht', hl', hloc⟩ := hs.exists_step hq (show T₀ ≤ t + 1 by omega)
  rcases exec_tau_pc hl' with h | h <;> rw [hloc, hpc1] at h <;> cases h

lemma Setting.exists_upd (hs : Setting e T₀) (hq : q ∈ e.infSteppers) {t : ℕ} (ht : T₀ ≤ t) :
    ∃ u ≥ t, e.lbl u = .tau q ∧ ((e.cfg u).loc q).pc = .upd := by
  obtain ⟨t', ht', hl, -⟩ := hs.exists_step hq ht
  rcases exec_tau_pc hl with h | h
  · exact ⟨t', ht', hl, h⟩
  · have h1 : ((e.cfg (t' + 1)).loc q).pc = .upd := by
      rw [(exec_scan hl h).2]
      exact afterScan_pc_of_not_decide (hs.not_decide hq (by omega) hl h)
    obtain ⟨u, hu, hl', hloc⟩ := hs.exists_step hq (show T₀ ≤ t' + 1 by omega)
    exact ⟨u, by omega, hl', by rw [hloc, h1]⟩

lemma Setting.exists_scan (hs : Setting e T₀) (hq : q ∈ e.infSteppers) {t : ℕ} (ht : T₀ ≤ t) :
    ∃ u ≥ t, e.lbl u = .tau q ∧ ((e.cfg u).loc q).pc = .scan := by
  obtain ⟨t', ht', hl, -⟩ := hs.exists_step hq ht
  rcases exec_tau_pc hl with h | h
  · have h1 : ((e.cfg (t' + 1)).loc q).pc = .scan := by rw [(exec_upd hl h).2]
    obtain ⟨u, hu, hl', hloc⟩ := hs.exists_step hq (show T₀ ≤ t' + 1 by omega)
    exact ⟨u, by omega, hl', by rw [hloc, h1]⟩
  · exact ⟨t', ht', hl, h⟩

/-- `q` *advances* at time `t`: a scan that satisfies neither line 9 nor line 11 (line 14). -/
def Adv (e : (fig3 (V := V) fix n m r).InfExec) (q : Fin n) (t : ℕ) : Prop :=
  e.lbl t = .tau q ∧ ((e.cfg t).loc q).pc = .scan ∧ ¬ DecideCond m ((e.cfg t).mem ()) ∧
    ¬ AdoptCond fix ((e.cfg t).mem ()) ((e.cfg t).loc q).i ((e.cfg t).loc q).pref q

lemma Adv.loc {t : ℕ} (h : Adv e q t) :
    (e.cfg (t + 1)).loc q = { (e.cfg t).loc q with pc := .upd, i := ((e.cfg t).loc q).i + 1 } := by
  rw [(exec_scan h.1 h.2.1).2, afterScan_of_not_adopt h.2.2.1 h.2.2.2]

/-- After `T₀`, the position `i` of `q ∈ S` changes only when `q` advances. -/
lemma Setting.i_succ (hs : Setting e T₀) (hq : q ∈ e.infSteppers) {t : ℕ} (ht : T₀ ≤ t)
    (hna : ¬ Adv e q t) : ((e.cfg (t + 1)).loc q).i = ((e.cfg t).loc q).i := by
  by_cases hp : (e.lbl t).proc = q
  · have hl := (hs.2 q hq t ht).2 hp
    rcases exec_tau_pc hl with h | h
    · rw [(exec_upd hl h).2]
    · have hd := hs.not_decide hq ht hl h
      have ha : AdoptCond fix ((e.cfg t).mem ()) ((e.cfg t).loc q).i ((e.cfg t).loc q).pref q := by
        by_contra ha; exact hna ⟨hl, h, hd, ha⟩
      rw [(exec_scan hl h).2, afterScan_of_adopt hd ha]
  · rw [(Impl.step_other (e.step_eq t) hp).1]

end Setting

/-! ### Duplicated pairs -/

section Dup

variable {fix : Bool} {s s₀ : Fin r → Cell V n}

lemma isDup_of_firstDup {j : Fin r} (h : firstDup s = some j) : IsDup s j := by
  unfold firstDup at h
  simpa using List.find?_some h

lemma exists_firstDup (h : ∃ j₁ j₂, j₁ ≠ j₂ ∧ s j₁ = s j₂) : ∃ j, firstDup s = some j := by
  obtain ⟨j₁, j₂, hne, heq⟩ := h
  have : ∃ j, IsDup s j := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨j₁, j₂, h, heq.symm⟩
    · exact ⟨j₂, j₁, h, heq⟩
  obtain ⟨j, hj⟩ := this
  cases hf : firstDup s with
  | some j' => exact ⟨j', rfl⟩
  | none =>
    unfold firstDup at hf
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using hj) (by simpa using hf j (List.mem_finRange j))

/-- If line 11 holds, the first duplicated pair is not `⊥`. -/
lemma exists_dupVal_of_adopt {i : Fin r} {pref : V} {id : Fin n} (h : AdoptCond fix s i pref id) :
    ∃ v, dupVal s = some v := by
  obtain ⟨j, hj⟩ := exists_firstDup h.2.1
  obtain ⟨j₂, hlt, heq⟩ := isDup_of_firstDup hj
  have : s j ≠ none := by
    by_cases hji : j = i
    · rw [← heq]; exact (h.1 j₂ (by rintro rfl; exact absurd hji (ne_of_lt hlt))).1
    · exact (h.1 j hji).1
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 this
  exact ⟨x.1, by simp [dupVal, hj, hx]⟩

/-- The first duplicated pair only depends on the components outside `M` if the components in `M`
are pairwise different and different from all components outside `M`. -/
lemma dupVal_congr (M : Fin r → Prop) (hNM : ∀ j, ¬ M j → s j = s₀ j)
    (hs : ∀ j j', M j → (¬ M j' → s j ≠ s j') ∧ (M j' → s j = s j' → j = j'))
    (hs₀ : ∀ j j', M j → (¬ M j' → s₀ j ≠ s₀ j') ∧ (M j' → s₀ j = s₀ j' → j = j')) :
    dupVal s = dupVal s₀ := by
  have key : ∀ t : Fin r → Cell V n,
      (∀ j j', M j → (¬ M j' → t j ≠ t j') ∧ (M j' → t j = t j' → j = j')) →
      ∀ j, IsDup t j ↔ ¬ M j ∧ ∃ j₂, j < j₂ ∧ ¬ M j₂ ∧ t j₂ = t j := by
    intro t ht j
    constructor
    · rintro ⟨j₂, hlt, heq⟩
      have hMj : ¬ M j := by
        intro hM
        by_cases hM₂ : M j₂
        · exact absurd ((ht j j₂ hM).2 hM₂ heq.symm) (ne_of_lt hlt)
        · exact (ht j j₂ hM).1 hM₂ heq.symm
      exact ⟨hMj, j₂, hlt, fun hM₂ => (ht j₂ j hM₂).1 hMj heq, heq⟩
    · rintro ⟨-, j₂, hlt, -, heq⟩
      exact ⟨j₂, hlt, heq⟩
  have hiff : ∀ j, IsDup s j ↔ IsDup s₀ j := by
    intro j
    rw [key s hs, key s₀ hs₀]
    constructor
    · rintro ⟨hM, j₂, hlt, hM₂, heq⟩
      exact ⟨hM, j₂, hlt, hM₂, by rw [← hNM j hM, ← hNM j₂ hM₂, heq]⟩
    · rintro ⟨hM, j₂, hlt, hM₂, heq⟩
      exact ⟨hM, j₂, hlt, hM₂, by rw [hNM j hM, hNM j₂ hM₂, heq]⟩
  have hf : firstDup s = firstDup s₀ := by
    unfold firstDup
    congr 1
    funext j
    exact decide_eq_decide.mpr (hiff j)
  unfold dupVal
  rw [hf]
  cases hj : firstDup s₀ with
  | none => rfl
  | some j =>
    have := ((key s₀ hs₀ j).1 (isDup_of_firstDup hj)).1
    simp [hNM j this]

end Dup

/-! ### Lemma 5 -/

section Lemma5

variable {e : (fig3 (V := V) true n m r).InfExec} {T₀ : ℕ}

/-- **Lemma 5** (for the corrected algorithm `fig3 true`): some process that takes infinitely many
steps advances (line 14) infinitely often. -/
theorem lemma5 (hs : Setting e T₀) (hne : e.infSteppers.Nonempty) :
    ∃ a ∈ e.infSteppers, ∀ N, ∃ t ≥ N, Adv e a t := by
  by_contra hcon
  push Not at hcon
  have : ∀ q : Fin n, ∃ N, ∀ t ≥ N, q ∈ e.infSteppers → ¬ Adv e q t := by
    intro q
    by_cases hq : q ∈ e.infSteppers
    · obtain ⟨N, hN⟩ := hcon q hq
      exact ⟨N, fun t ht _ => hN t ht⟩
    · exact ⟨0, fun _ _ h => absurd h hq⟩
  obtain ⟨μ, hμ, hna⟩ := Nat.eventually_forall_of_finite this T₀
  set S := e.infSteppers with hS
  -- after `μ` the positions are constant
  let ι : Fin n → Fin r := fun q => ((e.cfg μ).loc q).i
  have hi : ∀ q ∈ S, ∀ t ≥ μ, ((e.cfg t).loc q).i = ι q := by
    intro q hq t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hs.i_succ hq (by omega) (hna t ht q hq), ih]
  -- `M`: the components updated after `μ`; the others (`NM`) are constant
  let M : Fin r → Prop := fun j => ∃ q ∈ S, ι q = j
  have hNM : ∀ j, ¬ M j → ∀ t ≥ μ, (e.cfg t).mem () j = (e.cfg μ).mem () j := by
    intro j hj t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      rcases exec_mem (e := e) t with h | ⟨q, hl, hpc, h⟩
      · rw [h, ih]
      · have hq : q ∈ S := by have := hs.1 t (by omega); rwa [hl] at this
        rw [h, Function.update_of_ne, ih]
        rw [hi q hq t ht]; rintro rfl; exact hj ⟨q, hq, rfl⟩
  -- a pair written after `μ` is not in `NM` (Case 1 of the paper)
  have hmix : ∀ q ∈ S, ∀ u ≥ μ, e.lbl u = .tau q → ((e.cfg u).loc q).pc = .upd →
      ∀ j, ¬ M j → (e.cfg μ).mem () j ≠ some (((e.cfg u).loc q).pref, q) := by
    intro q hq u hu hl hpc j hj heq
    have h1 := (exec_upd hl hpc).2
    obtain ⟨t₂, ht₂, hl₂, hloc⟩ := hs.exists_step hq (show T₀ ≤ u + 1 by omega)
    rw [h1] at hloc
    have hpc₂ : ((e.cfg t₂).loc q).pc = .scan := by rw [hloc]
    refine hna t₂ (by omega) q hq ⟨hl₂, hpc₂, hs.not_decide hq (by omega) hl₂ hpc₂, ?_⟩
    intro ha
    have hji : j ≠ ((e.cfg t₂).loc q).i := by
      rw [hi q hq t₂ (by omega)]; rintro rfl; exact hj ⟨q, hq, rfl⟩
    apply (ha.1 j hji).2
    rw [hNM j hj t₂ (by omega), heq, hloc]
  -- after `μ'`, each component of `M` holds a pair written after `μ` by its owner
  let W : ℕ → Fin r → Prop := fun t j => ∃ v q, q ∈ S ∧ ι q = j ∧
    (e.cfg t).mem () j = some (v, q) ∧
      ∃ u ≥ μ, e.lbl u = .tau q ∧ ((e.cfg u).loc q).pc = .upd ∧ ((e.cfg u).loc q).pref = v
  have hWp : ∀ t ≥ μ, ∀ j, (M j → W t j) → (M j → W (t + 1) j) := by
    intro t ht j hW hM
    obtain ⟨v, q, hq, hqj, hmem, hu⟩ := hW hM
    rcases exec_mem (e := e) t with h | ⟨q', hl, hpc, h⟩
    · exact ⟨v, q, hq, hqj, by rw [h, hmem], hu⟩
    · have hq' : q' ∈ S := by have := hs.1 t (by omega); rwa [hl] at this
      by_cases hj : ((e.cfg t).loc q').i = j
      · exact ⟨_, q', hq', by rw [← hj, hi q' hq' t ht], by rw [h, hj, Function.update_self],
          t, ht, hl, hpc, rfl⟩
      · exact ⟨v, q, hq, hqj, by rw [h, Function.update_of_ne (Ne.symm hj), hmem], hu⟩
  have hWe : ∀ j, ∃ t ≥ μ, M j → W t j := by
    intro j
    by_cases hM : M j
    · obtain ⟨q, hq, rfl⟩ := hM
      obtain ⟨u, hu, hl, hpc⟩ := hs.exists_upd hq (show T₀ ≤ μ by omega)
      refine ⟨u + 1, by omega, fun _ => ⟨_, q, hq, rfl, ?_, u, hu, hl, hpc, rfl⟩⟩
      rw [(exec_upd hl hpc).1, hi q hq u hu, Function.update_self]
    · exact ⟨μ, le_rfl, fun h => absurd h hM⟩
  obtain ⟨μ', hμ', hW⟩ :=
    Nat.eventually_forall_of_imp_succ (P := fun t j => M j → W t j) μ hWp hWe
  have hsep : ∀ t ≥ μ', ∀ j j', M j → (¬ M j' → (e.cfg t).mem () j ≠ (e.cfg t).mem () j') ∧
      (M j' → (e.cfg t).mem () j = (e.cfg t).mem () j' → j = j') := by
    intro t ht j j' hM
    obtain ⟨v, q, hq, hqj, hmem, u, hu, hl, hpc, hv⟩ := hW t ht j hM
    refine ⟨fun hM' heq => ?_, fun hM' heq => ?_⟩
    · apply hmix q hq u hu hl hpc j' hM'
      rw [← hNM j' hM' t (by omega), ← heq, hmem, hv]
    · obtain ⟨v', q', hq', hqj', hmem', -⟩ := hW t ht j' hM'
      rw [hmem, hmem'] at heq
      cases heq
      rw [← hqj, ← hqj']
  -- hence the value of the first duplicated pair is constant after `μ'` (Case 2 of the paper)
  have hdup : ∀ t ≥ μ', dupVal ((e.cfg t).mem ()) = dupVal ((e.cfg μ').mem ()) := by
    intro t ht
    exact dupVal_congr M (fun j hj => by rw [hNM j hj t (by omega), hNM j hj μ' hμ'])
      (hsep t ht) (hsep μ' le_rfl)
  -- a process adopts that value, and at its next scan the corrected guard fails
  obtain ⟨q, hq⟩ := hne
  obtain ⟨t₁, ht₁, hl₁, hpc₁⟩ := hs.exists_scan hq (show T₀ ≤ μ' by omega)
  have hd₁ := hs.not_decide hq (by omega) hl₁ hpc₁
  have ha₁ : AdoptCond true ((e.cfg t₁).mem ()) ((e.cfg t₁).loc q).i ((e.cfg t₁).loc q).pref q := by
    by_contra ha; exact hna t₁ (by omega) q hq ⟨hl₁, hpc₁, hd₁, ha⟩
  obtain ⟨v, hv⟩ := exists_dupVal_of_adopt ha₁
  have hloc₁ := (exec_scan hl₁ hpc₁).2
  rw [afterScan_of_adopt hd₁ ha₁, hv] at hloc₁
  obtain ⟨t', ht', hl', hloc'⟩ := hs.exists_step hq (show T₀ ≤ t₁ + 1 by omega)
  rw [hloc₁] at hloc'
  have hpc' : ((e.cfg t').loc q).pc = .upd := by rw [hloc']
  have hloc'' := (exec_upd hl' hpc').2
  obtain ⟨t₂, ht₂, hl₂, hloc₂⟩ := hs.exists_step hq (show T₀ ≤ t' + 1 by omega)
  rw [hloc'', hloc'] at hloc₂
  have hpc₂ : ((e.cfg t₂).loc q).pc = .scan := by rw [hloc₂]
  have hd₂ := hs.not_decide hq (by omega) hl₂ hpc₂
  refine hna t₂ (by omega) q hq ⟨hl₂, hpc₂, hd₂, fun ha => ha.2.2 rfl ?_⟩
  rw [hdup t₂ (by omega), ← hdup t₁ (by omega), hv, hloc₂]
  rfl

end Lemma5

/-! ### Corollary 6 -/

section Cor6

variable {fix : Bool} {e : (fig3 (V := V) fix n m r).InfExec} {T₀ : ℕ} {a : Fin n}

/-- The next advance of `a` after `T` moves it to position `i + 1`. -/
lemma next_adv (hs : Setting e T₀) (ha : a ∈ e.infSteppers) (hadv : ∀ N, ∃ t ≥ N, Adv e a t)
    {T : ℕ} (hT : T₀ ≤ T) :
    ∃ t > T, ((e.cfg t).loc a).pc = .upd ∧ ((e.cfg t).loc a).i = ((e.cfg T).loc a).i + 1 := by
  classical
  have hex : ∃ k, Adv e a (T + k) := by
    obtain ⟨t, ht, h⟩ := hadv T
    exact ⟨t - T, by rwa [Nat.add_sub_cancel' ht]⟩
  have hconst : ∀ k ≤ Nat.find hex, ((e.cfg (T + k)).loc a).i = ((e.cfg T).loc a).i := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [← Nat.add_assoc, hs.i_succ ha (by omega) (Nat.find_min hex (by omega)), ih (by omega)]
  have h := (Nat.find_spec hex).loc
  refine ⟨T + Nat.find hex + 1, by omega, by rw [h], ?_⟩
  rw [h]
  show ((e.cfg (T + Nat.find hex)).loc a).i + 1 = _
  rw [hconst _ le_rfl]

open Fin.NatCast in
lemma iter_adv (hs : Setting e T₀) (ha : a ∈ e.infSteppers) (hadv : ∀ N, ∃ t ≥ N, Adv e a t)
    (d : ℕ) {T : ℕ} (hT : T₀ ≤ T) :
    ∃ t ≥ T, ((e.cfg t).loc a).pc = .upd ∧
      ((e.cfg t).loc a).i = ((e.cfg T).loc a).i + ((d + 1 : ℕ) : Fin r) := by
  induction d generalizing T with
  | zero =>
    obtain ⟨t, ht, h1, h2⟩ := next_adv hs ha hadv hT
    exact ⟨t, ht.le, h1, by rw [h2, Nat.zero_add, Nat.cast_one]⟩
  | succ d ih =>
    obtain ⟨t₁, ht₁, -, h₁⟩ := ih hT
    obtain ⟨t, ht, h1, h2⟩ := next_adv hs ha hadv (show T₀ ≤ t₁ by omega)
    exact ⟨t, by omega, h1, by rw [h2, h₁, Nat.cast_succ (d + 1), add_assoc]⟩

open Fin.NatCast in
/-- A process that advances infinitely often updates every component after any time. -/
lemma exists_upd_at (hs : Setting e T₀) (ha : a ∈ e.infSteppers)
    (hadv : ∀ N, ∃ t ≥ N, Adv e a t) {T : ℕ} (hT : T₀ ≤ T) (j : Fin r) :
    ∃ u ≥ T, e.lbl u = .tau a ∧ ((e.cfg u).loc a).pc = .upd ∧ ((e.cfg u).loc a).i = j := by
  obtain ⟨t, ht, h1, h2⟩ := iter_adv hs ha hadv (j - ((e.cfg T).loc a).i - 1).val hT
  have hj : ((e.cfg t).loc a).i = j := by
    rw [h2, Nat.cast_succ, Fin.cast_val_eq_self, sub_add_cancel, add_sub_cancel]
  obtain ⟨u, hu, hl, hloc⟩ := hs.exists_step ha (show T₀ ≤ t by omega)
  exact ⟨u, by omega, hl, by rw [hloc, h1], by rw [hloc, hj]⟩

/-- **Corollary 6** (for the corrected algorithm): from some time on, every component of `A` holds
a pair written by a process that takes infinitely many steps. -/
theorem cor6 (hs : Setting e T₀) (ha : a ∈ e.infSteppers) (hadv : ∀ N, ∃ t ≥ N, Adv e a t) :
    ∃ T, ∀ t ≥ T, ∀ j, ∃ v q, q ∈ e.infSteppers ∧ (e.cfg t).mem () j = some (v, q) := by
  have hp : ∀ t ≥ T₀, ∀ j, (∃ v q, q ∈ e.infSteppers ∧ (e.cfg t).mem () j = some (v, q)) →
      ∃ v q, q ∈ e.infSteppers ∧ (e.cfg (t + 1)).mem () j = some (v, q) := by
    rintro t ht j ⟨v, q, hq, hmem⟩
    rcases exec_mem (e := e) t with h | ⟨q', hl, hpc, h⟩
    · exact ⟨v, q, hq, by rw [h, hmem]⟩
    · have hq' : q' ∈ e.infSteppers := by have := hs.1 t ht; rwa [hl] at this
      by_cases hj : ((e.cfg t).loc q').i = j
      · exact ⟨_, q', hq', by rw [h, hj, Function.update_self]⟩
      · exact ⟨v, q, hq, by rw [h, Function.update_of_ne (Ne.symm hj), hmem]⟩
  have he : ∀ j, ∃ t ≥ T₀, ∃ v q, q ∈ e.infSteppers ∧ (e.cfg t).mem () j = some (v, q) := by
    intro j
    obtain ⟨u, hu, hl, hpc, hi⟩ := exists_upd_at hs ha hadv le_rfl j
    exact ⟨u + 1, by omega, _, a, ha, by rw [(exec_upd hl hpc).1, hi, Function.update_self]⟩
  obtain ⟨T, -, hT⟩ := Nat.eventually_forall_of_imp_succ
    (P := fun t j => ∃ v q, q ∈ e.infSteppers ∧ (e.cfg t).mem () j = some (v, q)) T₀ hp he
  exact ⟨T, hT⟩

end Cor6

/-! ### The decision condition -/

/-- If every component of `A` holds a pair of a process in `S` with `|S| ≤ m`, then the
condition of line 9 holds (by Lemma 3, there are at most `|S|` distinct pairs). -/
lemma decideCond_of_run {fix : Bool} {α : Exec V n} {C : Cfg V n r}
    (h : (fig3 (V := V) fix n m r).run α = some C) (hα : OneShot α) {S : Set (Fin n)}
    (hS : S.encard ≤ m) (hall : ∀ j, ∃ v q, q ∈ S ∧ C.mem () j = some (v, q)) :
    DecideCond m (C.mem ()) := by
  refine ⟨?_, fun j => by obtain ⟨v, q, -, h⟩ := hall j; rw [h]; simp⟩
  classical
  have hfin : S.Finite := Set.toFinite S
  have h1 : (Finset.univ.image (C.mem ())).card ≤ (hfin.toFinset.image some).card := by
    apply Finset.card_le_card_of_injOn (fun x : Cell V n => x.map Prod.snd)
    · intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨v, q, hq, hj⟩ := hall j
      simp [hj, hq]
    · intro x hx y hy hxy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨j₁, rfl⟩ := hx
      obtain ⟨j₂, rfl⟩ := hy
      obtain ⟨v₁, q₁, -, h₁⟩ := hall j₁
      obtain ⟨v₂, q₂, -, h₂⟩ := hall j₂
      simp only [h₁, h₂, Option.map_some, Option.some.injEq] at hxy ⊢
      subst hxy
      rw [lemma3 h hα h₁ h₂]
  have h2 : (hfin.toFinset.image some).card ≤ m := by
    rw [Finset.card_image_of_injective _ (Option.some_injective _)]
    rw [hfin.encard_eq_coe_toFinset_card] at hS
    exact_mod_cast hS
  omega

/-- In a one-shot infinite execution of the corrected algorithm, at least `m + 1` processes take
infinitely many steps (in particular, the set of such processes cannot be nonempty and of size
`≤ m`). -/
theorem false_of_infSteppers {e : (fig3 (V := V) true n m r).InfExec}
    (hOS : ∀ t, OneShot (e.pre t)) (hcard : e.infSteppers.encard ≤ m)
    (hne : e.infSteppers.Nonempty) : False := by
  obtain ⟨T₀, hs⟩ := exists_setting hOS
  obtain ⟨a, ha, hadv⟩ := lemma5 hs hne
  obtain ⟨T, hT⟩ := cor6 hs ha hadv
  obtain ⟨t, ht, hl, hpc⟩ := hs.exists_scan ha (show T₀ ≤ max T T₀ from le_max_right _ _)
  exact hs.not_decide ha (by omega) hl hpc
    (decideCond_of_run (e.run_pre t) (hOS t) hcard (hT t (by omega)))

end Liveness

end Podc.SetAgreementSpace

namespace Podc.SetAgreementSpace

variable {V : Type} [DecidableEq V] [Inhabited V] {n m r : ℕ} [NeZero r]

open Cslib.SharedMemory

/-- **Termination claim of Theorem 7** (Section 4.1, proof via Lemma 5 and Corollary 6), for the
corrected algorithm `fig3 true`: the algorithm of Figure 3 with the extra guard on line 11 is
`m`-obstruction-free on one-shot executions, for all `n`, `m` and all sizes `r ≥ 1` of the
snapshot object. -/
theorem fig3Fixed_mObstructionFree :
    (fig3 (V := V) true n m r).MObstructionFreeOn m OneShot := by
  intro e he hcard p N _
  by_contra h
  push Not at h
  refine Liveness.false_of_infSteppers he hcard ⟨p, fun N => ?_⟩
  obtain ⟨t, ht, hl⟩ := h N
  exact ⟨t, ht, by rw [hl]; rfl⟩

end Podc.SetAgreementSpace
