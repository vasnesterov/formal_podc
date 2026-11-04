import Papers.PODC2019.RecoverableHierarchy.Fig2Inv

/-!
# Figure 2: Lemmas 12, 13, 14 (in every execution)

* `lemma12`: each process accesses each consensus object `C[k]` at most once, in every
  execution (any crash pattern) — so `C[k]` may be implemented by any conventional (one-shot,
  wait-free) consensus algorithm.
* `lemma13` (validity) and `lemma14` (agreement) hold in **every** execution, without any bound on
  the number of failures. Agreement is CSLib's strong form: all outputs in all prefixes of an
  execution are equal (also outputs of the same process in different incarnations).
-/

namespace Podc.RecoverableHierarchy.Fig2

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {n f : ℕ}

/-! ## Stability of decisions -/

lemma Inv.mono_next {C : Cfg (A n f)} (hI : Inv C) : ∀ e : Ev n, Mono C (C.next e)
  | .step p => (hI.mono_step p).1
  | .crash _ => mono_refl_loc C _

lemma Inv.G_next {C : Cfg (A n f)} (hI : Inv C) {k : Fin (f + 1)} {d : Bool} (hG : G C k d) :
    ∀ e : Ev n, G (C.next e) k d
  | .step p => G_step hI p hG
  | .crash p => G_crash p hG

/-- `Decided` is stable. -/
lemma Inv.decided_run {C : Cfg (A n f)} (hI : Inv C) {d : Bool} (hd : Decided C d)
    (β : List (Ev n)) : Decided (run C β) d := by
  induction β generalizing C with
  | nil => exact hd
  | cons e β ih =>
    exact ih (hI.next e) ((hI.mono_next e).decided (fun _ _ h => hI.G_next h e) hd)

/-- Every output is `Decided`. -/
lemma Inv.decided_of_out {C : Cfg (A n f)} (hI : Inv C) {p : Fin n} {v : Bool} (h : C.Out p v) :
    Decided C v := by
  have := hI.loc p
  rw [out_iff.1 h] at this
  exact this

/-- Two decided values are equal. -/
lemma Inv.decided_agree {C : Cfg (A n f)} {v w : Bool} (hv : Decided C v) (hw : Decided C w) :
    v = w := by
  obtain ⟨k₁, h₁, g₁⟩ := hv
  obtain ⟨k₂, h₂, g₂⟩ := hw
  rcases lt_trichotomy k₁ k₂ with h | rfl | h
  · have : k₁.val ≠ f := by have := k₂.isLt; have : k₁.val < k₂.val := h; omega
    exact (g₁.resolve_left this).2.1 k₂ h w h₂ |>.symm
  · rw [h₁] at h₂; exact Option.some_injective _ h₂
  · have : k₂.val ≠ f := by have := k₁.isLt; have : k₂.val < k₁.val := h; omega
    exact (g₂.resolve_left this).2.1 k₁ h v h₁

/-- A decision of an execution is `Decided` at its end. -/
lemma decided_of_dec {x : Fin n → Bool} {γ : List (Ev n)} {v : Bool}
    (h : Dec (initCfg (A n f) x) γ v) : Decided (run (initCfg (A n f) x) γ) v := by
  obtain ⟨m, -, q, hq⟩ := h
  have hd := (inv_reach x (γ.take m)).decided_of_out hq
  have := (inv_reach x (γ.take m)).decided_run hd (γ.drop m)
  rwa [← run_append, List.take_append_drop] at this

/-- **Lemma 14** (agreement), in every execution and in CSLib's strong form: any two values
output in an execution (at any prefixes, by any processes or incarnations) are equal. -/
theorem lemma14 (x : Fin n → Bool) (γ : List (Ev n)) (v w : Bool)
    (hv : Dec (initCfg (A n f) x) γ v) (hw : Dec (initCfg (A n f) x) γ w) : v = w :=
  Inv.decided_agree (decided_of_dec hv) (decided_of_dec hw)

/-- **Lemma 13** (validity), in every execution: every output is the input of some process. -/
theorem lemma13 (x : Fin n → Bool) (γ : List (Ev n)) (v : Bool)
    (hv : Dec (initCfg (A n f) x) γ v) : ∃ p, x p = v := by
  obtain ⟨k, hk, -⟩ := decided_of_dec hv
  obtain ⟨q, hq⟩ := (inv_reach x γ).cval k v hk
  exact ⟨q, by simpa [initCfg] using hq⟩

/-! ## Lemma 12 -/

/-- Process `p` is poised on `C[k]` only at line 21 of iteration `k`. -/
lemma objOf_C {C : Cfg (A n f)} {p : Fin n} {k : Fin (f + 1)}
    (h : objOf C p = some (.inr k)) :
    ∃ j v, (C.loc p).pc = .scan k j v ∧ ¬ j < k.val := by
  unfold objOf at h
  rcases hl : C.loc p with ⟨i, pc⟩
  rw [hl] at h
  cases pc with
  | scan k' j v =>
    simp only [act] at h
    by_cases hj : j < k'.val
    · simp [hj] at h
    · simp only [hj, dite_false, Option.some.injEq, Sum.inr.injEq] at h
      subst h; exact ⟨j, v, rfl, hj⟩
  | _ => simp [act] at h

/-- `p` has completed line 21 of iteration `k`: `R[p] ≥ k+1` and `p` is neither at line 17 nor at
lines 18–21 of iteration `k`. -/
def Used (C : Cfg (A n f)) (p : Fin n) (k : Fin (f + 1)) : Prop :=
  k.val + 1 ≤ R C p ∧ (∀ v, (C.loc p).pc ≠ .wr17 k v) ∧ (∀ j v, (C.loc p).pc ≠ .scan k j v)

lemma goChk_ne_wr17 {i : Fin n} {k k' : Fin (f + 1)} {d v r : Bool} {y : ℕ} {v' : Bool} :
    goChk i k d v r y ≠ .wr17 k' v' := by
  intro he
  rcases goChk_cases i k d v r y with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp [h] at he

lemma goChk_ne_scan {i : Fin n} {k k' : Fin (f + 1)} {d v r : Bool} {y j : ℕ} {v' : Bool} :
    goChk i k d v r y ≠ .scan k' j v' := by
  intro he
  rcases goChk_cases i k d v r y with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp [h] at he

lemma Used.step {C : Cfg (A n f)} (hI : Inv C) {p : Fin n} {k : Fin (f + 1)} (hU : Used C p k)
    (q : Fin n) : Used (C.stepP q) p k := by
  have hR := ((hI.mono_step q).1.R p)
  by_cases hq : q = p
  · subst hq
    obtain ⟨h1, h2, h3⟩ := hU
    rcases hl : C.loc q with ⟨i, pc⟩
    obtain ⟨rfl, hpc⟩ := hI.locOf hl
    refine ⟨h1.trans hR, ?_⟩
    rw [hl] at h2 h3
    cases pc with
    | rd16 k' v =>
      rw [stepP_rd16 hl]
      simp only [Function.update_self]
      split_ifs with hk hRk
      · refine ⟨fun v' h => ?_, fun _ _ h => by simp at h⟩
        simp only [PC.wr17.injEq] at h
        have : k' = k.val := by rw [← h.1]
        omega
      · simp
      · simp
    | wr17 k' v =>
      rw [stepP_wr17 hl]
      simp only [Function.update_self]
      refine ⟨by simp, fun j v' h => ?_⟩
      simp only [PC.scan.injEq] at h; exact h2 v (by rw [h.1])
    | scan k' j v =>
      by_cases hj : j < k'.val
      · rw [stepP_scan_lt hl hj]
        simp only [Function.update_self]
        refine ⟨by simp, fun j' v' h => ?_⟩
        simp only [PC.scan.injEq] at h; exact h3 j v (by rw [h.1])
      · rw [stepP_scan_ge hl hj]; simp
    | wr22 k' d v =>
      rw [stepP_wr22 hl]
      simp only [Function.update_self]
      split_ifs
      · exact ⟨fun _ => goChk_ne_wr17, fun _ _ => goChk_ne_scan⟩
      · simp
    | chk k' d v r y =>
      rw [stepP_chk hl]
      simp only [Function.update_self]
      exact ⟨fun _ => goChk_ne_wr17, fun _ _ => goChk_ne_scan⟩
    | done d => rw [stepP_done hl, hl]; simp
  · unfold Used
    rw [stepP_loc_other C (Ne.symm hq)]
    exact ⟨hU.1.trans hR, hU.2⟩

lemma Used.crash {C : Cfg (A n f)} {p : Fin n} {k : Fin (f + 1)} (hU : Used C p k) (q : Fin n) :
    Used (C.next (.crash q)) p k := by
  by_cases hq : q = p
  · subst hq
    exact ⟨hU.1, by simp [Cfg.next], by simp [Cfg.next]⟩
  · rw [Used, next_loc_other C _ (by simpa using Ne.symm hq)]
    exact ⟨hU.1, hU.2⟩

lemma accCount_used {C : Cfg (A n f)} (hI : Inv C) {p : Fin n} {k : Fin (f + 1)}
    (hU : Used C p k) (β : List (Ev n)) : accCount C β p (.inr k) = 0 := by
  induction β generalizing C with
  | nil => rfl
  | cons e β ih =>
    rw [accCount_cons]
    have h2 : accCount (C.next e) β p (.inr k) = 0 := by
      refine ih (hI.next e) ?_
      rcases e with q | q
      · exact hU.step hI q
      · exact hU.crash q
    rw [h2, Nat.add_zero]
    refine ite_eq_right_of_eq_false _ _ (eq_false ?_)
    rintro ⟨-, ho⟩
    obtain ⟨j, v, hpc, -⟩ := objOf_C ho
    exact hU.2.2 j v hpc

lemma accCount_le_one {C : Cfg (A n f)} (hI : Inv C) (p : Fin n) (k : Fin (f + 1))
    (β : List (Ev n)) : accCount C β p (.inr k) ≤ 1 := by
  induction β generalizing C with
  | nil => simp
  | cons e β ih =>
    rw [accCount_cons]
    split_ifs with h
    · obtain ⟨rfl, ho⟩ := h
      obtain ⟨j, v, hpc, hj⟩ := objOf_C ho
      rcases hl : C.loc p with ⟨i, pc⟩
      obtain ⟨rfl, hpc'⟩ := hI.locOf hl
      rw [hl] at hpc; subst hpc
      have hU : Used (C.next (.step i)) i k := by
        show Used (C.stepP i) i k
        rw [stepP_scan_ge hl hj]
        exact ⟨by simp [hpc'.1], by simp, by simp⟩
      rw [accCount_used (hI.next _) hU]
    · simpa using ih (hI.next e)

/-- **Lemma 12**: in every execution (any crash pattern), each process accesses each
consensus object `C[k]` at most once. -/
theorem lemma12 (x : Fin n → Bool) (γ : List (Ev n)) (p : Fin n) (k : Fin (f + 1)) :
    accCount (initCfg (A n f) x) γ p (.inr k) ≤ 1 :=
  accCount_le_one (inv_init x) p k γ

end Podc.RecoverableHierarchy.Fig2
