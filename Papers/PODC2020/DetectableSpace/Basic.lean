import Papers.PODC2020.DetectableSpace.Model

/-!
# Basic facts about executions of recoverable implementations

* `exec_append`, `exec_singleton`, solo runs (`solo_succ`, `solo_hist`, `solo_ret`);
* events of other processes do not touch a process (`exec_free`);
* indistinguishability:
  - `EqEx p C D` (equal up to the state of `p`) is preserved by `p`-free schedules, with equal
    histories (`exec_eqEx`);
  - `Agree S C D` (same shared memory, same private memory and same state — up to operation
    identifiers — of the processes in `S`) is preserved by schedules of processes in `S` and
    crashes, with equal histories up to identifiers (`exec_agree`);
* operation identifiers: `exec_inv_bounds`, `exec_inv_unique`.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

variable {O : ObjSpec} {P : Type}

/-- Forget the operation identifier. -/
def PSt.erase {Op L : Type} : PSt Op L → Option (Op × Bool × L)
  | .idle => none
  | .run _ o b l => some (o, b, l)

/-- Forget the operation identifier of a history event. -/
def HEv.erase {Op R : Type} : HEv P Op R → HEv P Op R
  | .inv _ p o => .inv 0 p o
  | .res _ r b => .res 0 r b
  | .crash => .crash

/-- `e` is not an event of `p` and not a crash. -/
def Ev.Free {Op : Type} (p : P) : Ev P Op → Prop
  | .inv q _ => q ≠ p
  | .step q => q ≠ p
  | .crash => False

/-- `e` is an event of a process in `S`, or a crash. -/
def Ev.In {Op : Type} (S : Set P) : Ev P Op → Prop
  | .inv q _ => q ∈ S
  | .step q => q ∈ S
  | .crash => True

namespace RImpl

variable [DecidableEq P] (A : RImpl O P)

@[simp] lemma exec_singleton (C : A.Cfg) (e : Ev P O.Op) : A.exec C [e] = A.step1 C e := by
  simp [exec_cons]

lemma exec_fst_append (C : A.Cfg) (es fs : List (Ev P O.Op)) :
    (A.exec C (es ++ fs)).1 = (A.exec (A.exec C es).1 fs).1 := by
  rw [exec_append]

lemma exec_snd_append (C : A.Cfg) (es fs : List (Ev P O.Op)) :
    (A.exec C (es ++ fs)).2 = (A.exec C es).2 ++ (A.exec (A.exec C es).1 fs).2 := by
  rw [exec_append]

lemma solo_succ (p : P) (k : ℕ) : solo (O := O) p (k + 1) = .step p :: solo p k := by
  simp [solo, List.replicate_succ]

lemma solo_succ' (p : P) (k : ℕ) : solo (O := O) p (k + 1) = solo p k ++ [.step p] := by
  simp [solo, List.replicate_succ']

lemma solo_add (p : P) (j k : ℕ) : solo (O := O) p (j + k) = solo p j ++ solo p k := by
  simp only [solo]; rw [List.replicate_add]

lemma reachable_exec {C : A.Cfg} (hC : A.Reachable C) (es : List (Ev P O.Op)) :
    A.Reachable (A.exec C es).1 := by
  obtain ⟨es₀, rfl⟩ := hC
  exact ⟨es₀ ++ es, by rw [exec_fst_append]⟩

lemma reachable_init : A.Reachable A.init := ⟨[], rfl⟩

/-! ### Steps of idle processes, steps of other processes -/

@[simp] lemma step1_step_idle (C : A.Cfg) (p : P) (h : C.ps p = .idle) :
    A.step1 C (.step p) = (C, []) := by
  simp [step1, h]

lemma exec_solo_idle (C : A.Cfg) (p : P) (h : C.ps p = .idle) (k : ℕ) :
    A.exec C (solo p k) = (C, []) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [solo_succ, exec_cons, step1_step_idle A C p h]; simpa using ih

lemma step1_free (C : A.Cfg) (p : P) (e : Ev P O.Op) (he : e.Free p) :
    (A.step1 C e).1.ps p = C.ps p ∧ (A.step1 C e).1.pv p = C.pv p := by
  cases e with
  | inv q o =>
    have hq : q ≠ p := he
    simp only [step1]
    cases C.ps q <;> simp [Function.update_of_ne hq.symm]
  | step q =>
    have hq : q ≠ p := he
    simp only [step1]
    cases hc : C.ps q with
    | idle => simp
    | run a o b l =>
      simp only
      cases A.act q l <;> simp [Function.update_of_ne hq.symm]
  | crash => exact absurd he id

lemma exec_free (C : A.Cfg) (p : P) (es : List (Ev P O.Op)) (hes : ∀ e ∈ es, e.Free p) :
    (A.exec C es).1.ps p = C.ps p ∧ (A.exec C es).1.pv p = C.pv p := by
  induction es generalizing C with
  | nil => simp
  | cons e es ih =>
    rw [exec_cons]
    obtain ⟨h1, h2⟩ := ih (A.step1 C e).1 (fun e' he' => hes e' (by simp [he']))
    obtain ⟨h3, h4⟩ := A.step1_free C p e (hes e (by simp))
    exact ⟨h1.trans h3, h2.trans h4⟩

lemma solo_free {p q : P} (h : q ≠ p) (k : ℕ) : ∀ e ∈ solo (O := O) q k, e.Free p := by
  intro e he
  simp only [solo, List.mem_replicate] at he
  rw [he.2]; exact h

/-- Solo steps do not change the counter. -/
lemma exec_solo_cnt (C : A.Cfg) (p : P) (k : ℕ) : (A.exec C (solo p k)).1.cnt = C.cnt := by
  induction k generalizing C with
  | zero => rfl
  | succ k ih =>
    rw [solo_succ, exec_cons, ih]
    simp only [step1]
    cases hc : C.ps p with
    | idle => rfl
    | run a o b l => cases hact : A.act p l <;> simp [hact]

/-- Solo steps do not touch other processes' private memory and states. -/
lemma exec_solo_other (C : A.Cfg) {p q : P} (h : q ≠ p) (k : ℕ) :
    (A.exec C (solo p k)).1.ps q = C.ps q ∧ (A.exec C (solo p k)).1.pv q = C.pv q :=
  A.exec_free C q _ (solo_free h.symm k)

/-- A process running solo until it is idle produces exactly one response event. -/
lemma solo_hist (p : P) (k : ℕ) : ∀ (C : A.Cfg) a o b l, C.ps p = .run a o b l →
    (A.exec C (solo p k)).1.ps p = .idle → ∃ r, (A.exec C (solo p k)).2 = [.res a r b] := by
  induction k with
  | zero => intro C a o b l h1 h2; simp_all
  | succ k ih =>
    intro C a o b l h1 h2
    rw [solo_succ, exec_cons] at h2 ⊢
    simp only [step1, h1] at h2 ⊢
    cases hact : A.act p l with
    | sh f =>
      simp only [hact] at h2 ⊢
      obtain ⟨r, hr⟩ := ih _ a o b (f C.sh).1 (by simp) h2
      exact ⟨r, by simpa using hr⟩
    | pv f =>
      simp only [hact] at h2 ⊢
      obtain ⟨r, hr⟩ := ih _ a o b (f (C.pv p)).1 (by simp) h2
      exact ⟨r, by simpa using hr⟩
    | ret r =>
      simp only [hact] at h2 ⊢
      refine ⟨r, ?_⟩
      rw [exec_solo_idle _ _ _ (by simp)]
      simp

/-- A process running solo until it is idle: the configuration just before its return step. -/
lemma solo_ret (p : P) (k : ℕ) : ∀ (C : A.Cfg) a o b l, C.ps p = .run a o b l →
    (A.exec C (solo p k)).1.ps p = .idle → ∃ j < k, ∃ l' r,
      (A.exec C (solo p j)).1.ps p = .run a o b l' ∧ A.act p l' = .ret r ∧
      (A.exec C (solo p j)).2 = [] := by
  induction k with
  | zero => intro C a o b l h1 h2; simp_all
  | succ k ih =>
    intro C a o b l h1 h2
    rw [solo_succ, exec_cons] at h2
    simp only [step1, h1] at h2
    cases hact : A.act p l with
    | sh f =>
      simp only [hact] at h2
      obtain ⟨j, hj, l', r, h3, h4, h5⟩ := ih _ a o b (f C.sh).1 (by simp) h2
      refine ⟨j + 1, by omega, l', r, ?_, h4, ?_⟩
      · rw [solo_succ, exec_cons]; simpa [step1, h1, hact] using h3
      · rw [solo_succ, exec_cons]; simpa [step1, h1, hact] using h5
    | pv f =>
      simp only [hact] at h2
      obtain ⟨j, hj, l', r, h3, h4, h5⟩ := ih _ a o b (f (C.pv p)).1 (by simp) h2
      refine ⟨j + 1, by omega, l', r, ?_, h4, ?_⟩
      · rw [solo_succ, exec_cons]; simpa [step1, h1, hact] using h3
      · rw [solo_succ, exec_cons]; simpa [step1, h1, hact] using h5
    | ret r => exact ⟨0, by omega, l, r, by simpa using h1, hact, rfl⟩

lemma exec_snoc (C : A.Cfg) (es : List (Ev P O.Op)) (e : Ev P O.Op) :
    A.exec C (es ++ [e]) =
      ((A.step1 (A.exec C es).1 e).1, (A.exec C es).2 ++ (A.step1 (A.exec C es).1 e).2) := by
  rw [exec_append, exec_singleton]

/-- Bounded steps imply obstruction-freedom (indeed wait-freedom). -/
theorem BoundedSteps.obstructionFree {μ : A.L → ℕ} (hμ : A.BoundedSteps μ) :
    A.ObstructionFree := by
  have key : ∀ n (C : A.Cfg) (p : P) a o b l, C.ps p = .run a o b l → μ l < n →
      (A.exec C (solo p n)).1.ps p = .idle := by
    intro n
    induction n with
    | zero => intro C p a o b l _ h; omega
    | succ n ih =>
      intro C p a o b l h1 h2
      rw [solo_succ, exec_cons]
      have hμp := hμ p l
      simp only [step1, h1]
      cases hact : A.act p l with
      | sh f =>
        rw [hact] at hμp
        exact ih _ p a o b (f C.sh).1 (by simp)
          (by have h3 : μ (f C.sh).1 < μ l := hμp C.sh; omega)
      | pv f =>
        rw [hact] at hμp
        exact ih _ p a o b (f (C.pv p)).1 (by simp)
          (by have h3 : μ (f (C.pv p)).1 < μ l := hμp (C.pv p); omega)
      | ret r =>
        simp only
        rw [exec_solo_idle _ _ _ (by simp)]
        simp
  intro C _ p
  cases hc : C.ps p with
  | idle => exact ⟨0, by simpa using hc⟩
  | run a o b l => exact ⟨μ l + 1, key _ C p a o b l hc (by omega)⟩

/-- Proving correctness by an invariant maintained along executions. -/
theorem durLinDet_of_inv
    (Inv : A.Cfg → List (HEv P O.Op O.Resp) → List (ℕ × O.Op) → Prop)
    (h0 : Inv A.init [] [])
    (hstep : ∀ C h L e, A.Reachable C → Inv C h L →
      ∃ L', Inv (A.step1 C e).1 (h ++ (A.step1 C e).2) L')
    (hlin : ∀ C h L, Inv C h L → DLin O h O.init L)
    (hnf : ∀ C h L, Inv C h L → ∀ a, HEv.res a none false ∉ h) : A.DurLinDet := by
  have key : ∀ es, ∃ L, Inv (A.exec A.init es).1 (A.exec A.init es).2 L := by
    intro es
    induction es using List.reverseRecOn with
    | nil => exact ⟨[], h0⟩
    | append_singleton es e ih =>
      obtain ⟨L, hL⟩ := ih
      obtain ⟨L', hL'⟩ := hstep _ _ L e ⟨es, rfl⟩ hL
      exact ⟨L', by rw [exec_snoc]; exact hL'⟩
  intro es
  obtain ⟨L, hL⟩ := key es
  exact ⟨⟨L, hlin _ _ _ hL⟩, hnf _ _ _ hL⟩

/-! ### Equality up to one process -/

/-- `C` and `D` are equal except for the private memory and state of `p`. -/
structure EqEx (p : P) (C D : A.Cfg) : Prop where
  sh : C.sh = D.sh
  cnt : C.cnt = D.cnt
  pv : ∀ x, x ≠ p → C.pv x = D.pv x
  ps : ∀ x, x ≠ p → C.ps x = D.ps x

variable {A}

lemma EqEx.step1 {p : P} {C D : A.Cfg} (h : A.EqEx p C D) (e : Ev P O.Op) (he : e.Free p) :
    A.EqEx p (A.step1 C e).1 (A.step1 D e).1 ∧ (A.step1 C e).2 = (A.step1 D e).2 := by
  obtain ⟨hsh, hcnt, hpv, hps⟩ := h
  cases e with
  | inv q o =>
    have hq : q ≠ p := he
    simp only [RImpl.step1]
    rw [hps q hq]
    cases D.ps q with
    | idle =>
      refine ⟨⟨hsh, by simp [hcnt], ?_, ?_⟩, by simp [hcnt]⟩
      · intro x hx
        by_cases hxq : x = q
        · subst hxq; simp [hpv x hx]
        · simp [Function.update_of_ne hxq, hpv x hx]
      · intro x hx
        by_cases hxq : x = q
        · subst hxq; simp [hcnt]
        · simp [Function.update_of_ne hxq, hps x hx]
    | run a o' b l => exact ⟨⟨hsh, hcnt, hpv, hps⟩, rfl⟩
  | step q =>
    have hq : q ≠ p := he
    simp only [RImpl.step1]
    rw [hps q hq]
    cases D.ps q with
    | idle => exact ⟨⟨hsh, hcnt, hpv, hps⟩, rfl⟩
    | run a o b l =>
      simp only
      cases A.act q l with
      | sh f =>
        refine ⟨⟨by simp [hsh], hcnt, hpv, ?_⟩, rfl⟩
        intro x hx
        by_cases hxq : x = q
        · subst hxq; simp [hsh]
        · simp [Function.update_of_ne hxq, hps x hx]
      | pv f =>
        refine ⟨⟨hsh, hcnt, ?_, ?_⟩, rfl⟩
        · intro x hx
          by_cases hxq : x = q
          · subst hxq; simp [hpv x hx]
          · simp [Function.update_of_ne hxq, hpv x hx]
        · intro x hx
          by_cases hxq : x = q
          · subst hxq; simp [hpv x hx]
          · simp [Function.update_of_ne hxq, hps x hx]
      | ret r =>
        refine ⟨⟨hsh, hcnt, hpv, ?_⟩, rfl⟩
        intro x hx
        by_cases hxq : x = q
        · subst hxq; simp
        · simp [Function.update_of_ne hxq, hps x hx]
  | crash => exact absurd he id

lemma EqEx.exec {p : P} {C D : A.Cfg} (h : A.EqEx p C D) (es : List (Ev P O.Op))
    (hes : ∀ e ∈ es, e.Free p) :
    A.EqEx p (A.exec C es).1 (A.exec D es).1 ∧ (A.exec C es).2 = (A.exec D es).2 := by
  induction es generalizing C D with
  | nil => exact ⟨h, rfl⟩
  | cons e es ih =>
    obtain ⟨h1, h2⟩ := h.step1 e (hes e (by simp))
    obtain ⟨h3, h4⟩ := ih h1 (fun e' he' => hes e' (by simp [he']))
    simp only [RImpl.exec_cons]
    exact ⟨h3, by rw [h2, h4]⟩

/-! ### Agreement on a set of processes (up to identifiers) -/

/-- `C` and `D` have the same shared memory, and the processes of `S` have the same private
memory and the same state up to operation identifiers. -/
structure Agree (S : Set P) (C D : A.Cfg) : Prop where
  sh : C.sh = D.sh
  pv : ∀ x ∈ S, C.pv x = D.pv x
  ps : ∀ x ∈ S, (C.ps x).erase = (D.ps x).erase

lemma PSt.erase_eq_iff {Op L : Type} {s t : PSt Op L} :
    s.erase = t.erase ↔ (s = .idle ∧ t = .idle) ∨
      ∃ a a' o b l, s = .run a o b l ∧ t = .run a' o b l := by
  cases s with
  | idle => cases t <;> simp [PSt.erase]
  | run a o b l =>
    cases t with
    | idle => simp [PSt.erase]
    | run a' o' b' l' =>
      simp only [PSt.erase, Option.some.injEq, Prod.mk.injEq, PSt.run.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩
        exact Or.inr ⟨a, a', o, b, l, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
      · rintro (⟨h, _⟩ | ⟨_, _, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩)
        · cases h
        · exact ⟨rfl, rfl, rfl⟩

lemma Agree.step1 {S : Set P} {C D : A.Cfg} (h : A.Agree S C D) (e : Ev P O.Op) (he : e.In S) :
    A.Agree S (A.step1 C e).1 (A.step1 D e).1 ∧
      (A.step1 C e).2.map HEv.erase = (A.step1 D e).2.map HEv.erase := by
  obtain ⟨hsh, hpv, hps⟩ := h
  cases e with
  | inv q o =>
    have hq : q ∈ S := he
    simp only [RImpl.step1]
    rcases PSt.erase_eq_iff.1 (hps q hq) with ⟨h1, h2⟩ | ⟨a, a', o', b, l, h1, h2⟩
    · rw [h1, h2]
      refine ⟨⟨hsh, ?_, ?_⟩, by simp [HEv.erase]⟩
      · intro x hx
        by_cases hxq : x = q
        · subst hxq; simp [hpv x hx]
        · simp [Function.update_of_ne hxq, hpv x hx]
      · intro x hx
        by_cases hxq : x = q
        · subst hxq; simp [PSt.erase]
        · simp [Function.update_of_ne hxq, hps x hx]
    · rw [h1, h2]; exact ⟨⟨hsh, hpv, hps⟩, rfl⟩
  | step q =>
    have hq : q ∈ S := he
    simp only [RImpl.step1]
    rcases PSt.erase_eq_iff.1 (hps q hq) with ⟨h1, h2⟩ | ⟨a, a', o, b, l, h1, h2⟩
    · rw [h1, h2]; exact ⟨⟨hsh, hpv, hps⟩, rfl⟩
    · rw [h1, h2]
      simp only
      cases A.act q l with
      | sh f =>
        refine ⟨⟨by simp [hsh], hpv, ?_⟩, rfl⟩
        intro x hx
        by_cases hxq : x = q
        · subst hxq; simp [hsh, PSt.erase]
        · simp [Function.update_of_ne hxq, hps x hx]
      | pv f =>
        refine ⟨⟨hsh, ?_, ?_⟩, rfl⟩
        · intro x hx
          by_cases hxq : x = q
          · subst hxq; simp [hpv x hx]
          · simp [Function.update_of_ne hxq, hpv x hx]
        · intro x hx
          by_cases hxq : x = q
          · subst hxq; simp [hpv x hx, PSt.erase]
          · simp [Function.update_of_ne hxq, hps x hx]
      | ret r =>
        refine ⟨⟨hsh, hpv, ?_⟩, by simp [HEv.erase]⟩
        intro x hx
        by_cases hxq : x = q
        · subst hxq; simp
        · simp [Function.update_of_ne hxq, hps x hx]
  | crash =>
    refine ⟨⟨hsh, hpv, ?_⟩, rfl⟩
    intro x hx
    show (A.crashPS x (C.ps x)).erase = (A.crashPS x (D.ps x)).erase
    rcases PSt.erase_eq_iff.1 (hps x hx) with ⟨h1, h2⟩ | ⟨a, a', o, b, l, h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; rfl

lemma Agree.exec {S : Set P} {C D : A.Cfg} (h : A.Agree S C D) (es : List (Ev P O.Op))
    (hes : ∀ e ∈ es, e.In S) :
    A.Agree S (A.exec C es).1 (A.exec D es).1 ∧
      (A.exec C es).2.map HEv.erase = (A.exec D es).2.map HEv.erase := by
  induction es generalizing C D with
  | nil => exact ⟨h, rfl⟩
  | cons e es ih =>
    obtain ⟨h1, h2⟩ := h.step1 e (hes e (by simp))
    obtain ⟨h3, h4⟩ := ih h1 (fun e' he' => hes e' (by simp [he']))
    simp only [RImpl.exec_cons, List.map_append]
    exact ⟨h3, by rw [h2, h4]⟩

lemma solo_in (S : Set P) {p : P} (hp : p ∈ S) (k : ℕ) : ∀ e ∈ solo (O := O) p k, e.In S := by
  intro e he
  simp only [solo, List.mem_replicate] at he
  rw [he.2]; exact hp

/-! ### Operation identifiers -/

variable (A)

lemma step1_cnt_le (C : A.Cfg) (e : Ev P O.Op) : C.cnt ≤ (A.step1 C e).1.cnt := by
  cases e with
  | inv q o => simp only [step1]; cases C.ps q <;> simp
  | step q =>
    simp only [step1]
    cases C.ps q with
    | idle => simp
    | run a o b l => cases hact : A.act q l <;> simp [hact]
  | crash => simp [step1]

lemma step1_inv (C : A.Cfg) (e : Ev P O.Op) (a : ℕ) (q : P) (o : O.Op)
    (h : HEv.inv a q o ∈ (A.step1 C e).2) : a = C.cnt ∧ (A.step1 C e).1.cnt = C.cnt + 1 := by
  cases e with
  | inv q' o' =>
    simp only [step1] at h ⊢
    cases hc : C.ps q' with
    | idle => simp [hc] at h ⊢; exact h.1
    | run a' o'' b' l' => simp [hc] at h
  | step q' =>
    simp only [step1] at h
    cases hc : C.ps q' with
    | idle => simp [hc] at h
    | run a o b l =>
      simp only [hc] at h
      cases hact : A.act q' l <;> simp [hact] at h
  | crash => simp [step1] at h

lemma exec_cnt_le (C : A.Cfg) (es : List (Ev P O.Op)) : C.cnt ≤ (A.exec C es).1.cnt := by
  induction es generalizing C with
  | nil => simp
  | cons e es ih => rw [exec_cons]; exact (A.step1_cnt_le C e).trans (ih _)

/-- Identifiers of invocations in a history lie between the counters at its ends. -/
lemma exec_inv_bounds (C : A.Cfg) (es : List (Ev P O.Op)) (a : ℕ) (q : P) (o : O.Op)
    (h : HEv.inv a q o ∈ (A.exec C es).2) : C.cnt ≤ a ∧ a < (A.exec C es).1.cnt := by
  induction es generalizing C with
  | nil => simp at h
  | cons e es ih =>
    rw [exec_cons] at h
    show C.cnt ≤ a ∧ a < (A.exec (A.step1 C e).1 es).1.cnt
    rcases List.mem_append.1 h with h | h
    · obtain ⟨rfl, h2⟩ := A.step1_inv C e a q o h
      exact ⟨le_rfl, by have := A.exec_cnt_le (A.step1 C e).1 es; omega⟩
    · obtain ⟨h1, h2⟩ := ih _ h
      exact ⟨(A.step1_cnt_le C e).trans h1, h2⟩

/-- Each identifier is invoked at most once in a history. -/
lemma exec_inv_unique (C : A.Cfg) (es : List (Ev P O.Op)) (a : ℕ) (q q' : P) (o o' : O.Op)
    (h : HEv.inv a q o ∈ (A.exec C es).2) (h' : HEv.inv a q' o' ∈ (A.exec C es).2) :
    q = q' ∧ o = o' := by
  induction es generalizing C with
  | nil => simp at h
  | cons e es ih =>
    rw [exec_cons] at h h'
    rcases List.mem_append.1 h with h | h <;> rcases List.mem_append.1 h' with h' | h'
    · cases e with
      | inv q'' o'' =>
        simp only [step1] at h h'
        cases hc : C.ps q'' with
        | idle => simp [hc] at h h'; exact ⟨h.2.1.trans h'.2.1.symm, h.2.2.trans h'.2.2.symm⟩
        | run a' o'' b' l' => simp [hc] at h
      | step q'' =>
        simp only [step1] at h
        cases hc : C.ps q'' with
        | idle => simp [hc] at h
        | run a o b l =>
          simp only [hc] at h
          cases hact : A.act q'' l <;> simp [hact] at h
      | crash => simp [step1] at h
    · obtain ⟨ha, h2⟩ := A.step1_inv C e a q o h
      have := (A.exec_inv_bounds _ es a q' o' h').1; omega
    · obtain ⟨ha, h2⟩ := A.step1_inv C e a q' o' h'
      have := (A.exec_inv_bounds _ es a q o h).1; omega
    · exact ih _ h h'

end RImpl

end Papers.PODC2020.DetectableSpace
