import Papers.PODC2019.RecoverableHierarchy.Restricted

/-!
# Valency in the restricted failure model (proofs of Theorems 3 and 6)

Valency is defined with respect to the restricted executions (as in the paper): a schedule `σ`
is `v`-potent if some restricted extension contains a decision `v`, univalent if all decisions of
all extensions equal `v`, bivalent if it is both `0`- and `1`-potent.

Main results, for an algorithm correct on the restricted executions (`Restr.RCorrect`):
* `Restr.agree'`: in a restricted execution all outputs are equal (also outputs of the same
  process): `b` never crashes and eventually outputs, so it must agree with everybody;
* `Restr.biv_init`: the initial state with inputs `a ↦ 0`, `b ↦ 1` is bivalent;
* `Restr.exists_crit`: there is a reachable bivalent schedule `σ` all of whose one-move
  extensions are univalent ("critical state") — the construction terminates because restricted
  executions have finitely many crashes;
* `Restr.crit_values`: at a critical `σ`, `σ a` and `σ b` are univalent with different values;
* `Restr.contra_a`, `Restr.contra_b`: two univalent schedules with different values cannot end in
  states that `a` (resp. `b`) cannot distinguish (`a` may in addition never access some set of
  objects `S` on which the two states differ).
-/

namespace Podc.RecoverableHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

namespace Restr

variable (R : Restr A)

/-! ## Basic facts on restricted executions -/

lemma ev_ne_crash_b (s : RS A) (m : Bool) : R.ev s m ≠ .crash R.b := by
  cases m
  · by_cases h : s.pend
    · rw [R.ev_false_pend s h]; simp only [ne_eq, Ev.crash.injEq]; exact R.hab
    · simp only [Bool.not_eq_true] at h; rw [R.ev_false_npend s h]; simp
  · simp

lemma who_true : R.who true = R.b := rfl
lemma who_false : R.who false = R.a := rfl

/-- Infinite restricted executions have finitely many crashes. -/
lemma eventually_no_crash (x : Fin n → Bool) (sch : ℕ → Bool) :
    ∃ N, ∀ t ≥ N, ∀ p, R.eInf x sch t ≠ .crash p := by
  by_contra hcon
  push Not at hcon
  have hb : ∀ t, numCrashes (pre (R.eInf x sch) t) ≤ R.F.card := fun t => by
    rw [R.pre_eInf]; exact R.numCrashes_E_le x _
  have hmono : ∀ t d, numCrashes (pre (R.eInf x sch) t) ≤
      numCrashes (pre (R.eInf x sch) (t + d)) := by
    intro t d
    rw [pre_add, numCrashes_append]; omega
  have key : ∀ j, ∃ t, j ≤ numCrashes (pre (R.eInf x sch) t) := by
    intro j
    induction j with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨t', ht', p, hp⟩ := hcon t
      refine ⟨t' + 1, ?_⟩
      rw [pre_succ, numCrashes_append, hp]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht'
      have := hmono t d
      have h1 : numCrashes [Ev.crash p] = 1 := rfl
      omega
  obtain ⟨t, ht⟩ := key (R.F.card + 1)
  have := hb t
  omega

lemma S_append (x : Fin n → Bool) (σ τ : List Bool) :
    R.S x (σ ++ τ) = R.rrun (R.S x σ) τ := R.rrun_append _ _ _

lemma E_append (x : Fin n → Bool) (σ τ : List Bool) :
    R.E x (σ ++ τ) = R.E x σ ++ R.evs (R.S x σ) τ := R.evs_append _ _ _

lemma dec_append {x : Fin n → Bool} {σ : List Bool} {v : Bool}
    (h : Dec (initCfg A x) (R.E x σ) v) (τ : List Bool) :
    Dec (initCfg A x) (R.E x (σ ++ τ)) v := by
  rw [R.E_append]; exact h.append_right _

lemma outputs_append {x : Fin n → Bool} {σ : List Bool} {p : Fin n} {v : Bool}
    (h : Outputs (initCfg A x) (R.E x σ) p v) (τ : List Bool) :
    Outputs (initCfg A x) (R.E x (σ ++ τ)) p v := by
  obtain ⟨k, hk, hp⟩ := h
  refine ⟨k, by rw [R.E_append, List.length_append]; omega, ?_⟩
  rwa [R.E_append, List.take_append_of_le_length hk]

lemma dec_of_out {x : Fin n → Bool} {σ : List Bool} {p : Fin n} {v : Bool}
    (h : (R.S x σ).c.Out p v) : Dec (initCfg A x) (R.E x σ) v :=
  Dec.of_out (by rwa [← R.S_c])

lemma outputs_of_out {x : Fin n → Bool} {σ : List Bool} {p : Fin n} {v : Bool}
    (h : (R.S x σ).c.Out p v) : Outputs (initCfg A x) (R.E x σ) p v :=
  ⟨(R.E x σ).length, le_rfl, by rwa [List.take_length, ← R.S_c]⟩

/-- An output of `b` persists (`b` never crashes). -/
lemma out_b_run {s : RS A} {v : Bool} (h : s.c.Out R.b v) (τ : List Bool) :
    (R.rrun s τ).c.Out R.b v := by
  rw [R.rrun_c]; exact h.run (R.crash_b_not_mem s τ)

/-- If `b` output `v` at some point of `σ`, it is in an output state `v` at the end of `σ`. -/
lemma out_b_of_outputs {x : Fin n → Bool} {σ : List Bool} {v : Bool}
    (h : Outputs (initCfg A x) (R.E x σ) R.b v) : (R.S x σ).c.Out R.b v := by
  obtain ⟨k, hk, hb⟩ := h
  rw [R.evs_take, ← R.S_c] at hb
  have := R.out_b_run hb (σ.drop k)
  rwa [← R.rrun_append, List.take_append_drop] at this

lemma bpre_ext' (σ : List Bool) (m : Bool) {t : ℕ} (ht : σ.length ≤ t) :
    bpre (ext σ m) t = σ ++ List.replicate (t - σ.length) m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [bpre_ext]; simp

/-! ## Solo runs of `a` and `b` terminate -/

variable {R}

/-- `b` running solo (restricted) eventually outputs. -/
lemma solo_b (hR : R.RCorrect) (x : Fin n → Bool) (σ : List Bool) :
    ∃ k u, (R.S x (σ ++ List.replicate k true)).c.Out R.b u := by
  obtain ⟨t, ht, u, hu⟩ := hR.prog x (ext σ true) true σ.length
    (fun M => ⟨max M σ.length, le_max_left _ _, by simp [ext]⟩)
    (fun t _ => R.ev_ne_crash_b _ _)
  exact ⟨t - σ.length, u, by rwa [bpre_ext' σ true ht] at hu⟩

/-- `a` running solo (restricted, with its forced crashes) eventually outputs. -/
lemma solo_a (hR : R.RCorrect) (x : Fin n → Bool) (σ : List Bool) :
    ∃ k u, (R.S x (σ ++ List.replicate k false)).c.Out R.a u := by
  obtain ⟨N, hN⟩ := R.eventually_no_crash x (ext σ false)
  obtain ⟨t, ht, u, hu⟩ := hR.prog x (ext σ false) false (max N σ.length)
    (fun M => ⟨max M σ.length, le_max_left _ _, by simp [ext]⟩)
    (fun t ht => hN t (le_of_max_le_left ht) _)
  exact ⟨t - σ.length, u, by rwa [bpre_ext' σ false (le_of_max_le_right ht)] at hu⟩

/-- **Agreement on restricted executions**, for all outputs (also of the same process). -/
lemma agree' (hR : R.RCorrect) {x : Fin n → Bool} {σ : List Bool} {v w : Bool}
    (hv : Dec (initCfg A x) (R.E x σ) v) (hw : Dec (initCfg A x) (R.E x σ) w) : v = w := by
  obtain ⟨k, u, hu⟩ := solo_b hR x σ
  have key : ∀ v, Dec (initCfg A x) (R.E x σ) v → v = u := by
    intro v hv
    obtain ⟨p, hp⟩ := Dec.exists_outputs hv
    by_cases hpb : p = R.b
    · subst hpb
      have h1 := R.out_b_run (R.out_b_of_outputs hp) (List.replicate k true)
      rw [← R.S_append] at h1
      have := h1.symm.trans hu
      simpa using this
    · exact hR.agree x _ p R.b hpb v u (R.outputs_append hp _) (R.outputs_of_out hu)
  rw [key v hv, key w hw]

/-! ## Valency -/

variable (R)

/-- `σ` is `v`-potent: some restricted extension contains a decision `v`. -/
def Pot (x : Fin n → Bool) (σ : List Bool) (v : Bool) : Prop :=
  ∃ τ, Dec (initCfg A x) (R.E x (σ ++ τ)) v

/-- `σ` is `v`-univalent: every decision in every restricted extension is `v`. -/
def Univ (x : Fin n → Bool) (σ : List Bool) (v : Bool) : Prop :=
  ∀ τ w, Dec (initCfg A x) (R.E x (σ ++ τ)) w → w = v

/-- `σ` is bivalent. -/
def Biv (x : Fin n → Bool) (σ : List Bool) : Prop := R.Pot x σ true ∧ R.Pot x σ false

variable {R}

lemma Univ.append {x : Fin n → Bool} {σ : List Bool} {v : Bool} (h : R.Univ x σ v)
    (τ : List Bool) : R.Univ x (σ ++ τ) v := by
  intro τ' w hw
  rw [List.append_assoc] at hw
  exact h _ w hw

lemma Univ.of_out {x : Fin n → Bool} {σ : List Bool} {v : Bool} (h : R.Univ x σ v) {p : Fin n}
    {u : Bool} (hu : (R.S x σ).c.Out p u) : u = v :=
  h [] u (by simpa using R.dec_of_out hu)

lemma potent (hR : R.RCorrect) (x : Fin n → Bool) (σ : List Bool) : ∃ v, R.Pot x σ v := by
  obtain ⟨k, u, hu⟩ := solo_b hR x σ
  exact ⟨u, _, R.dec_of_out hu⟩

lemma univ_of_not_biv (hR : R.RCorrect) {x : Fin n → Bool} {σ : List Bool}
    (h : ¬ R.Biv x σ) : ∃ v, R.Univ x σ v := by
  obtain ⟨v, τ₀, hv⟩ := potent hR x σ
  refine ⟨v, fun τ w hw => ?_⟩
  by_contra hne
  apply h
  have hw' : R.Pot x σ w := ⟨τ, hw⟩
  have hv' : R.Pot x σ v := ⟨τ₀, hv⟩
  cases v <;> cases w <;> simp_all [Biv]

/-- A bivalent schedule has no output in its final state. -/
lemma not_out_of_biv (hR : R.RCorrect) {x : Fin n → Bool} {σ : List Bool} (hb : R.Biv x σ)
    {p : Fin n} {u : Bool} (hu : (R.S x σ).c.Out p u) : False := by
  have hd := R.dec_of_out hu
  obtain ⟨τ, hτ⟩ : R.Pot x σ (!u) := by cases u; exacts [hb.1, hb.2]
  have := agree' hR (R.dec_append hd τ) hτ
  cases u <;> simp at this

/-- The two one-move extensions of a critical schedule have different valencies. -/
lemma crit_values {x : Fin n → Bool} {σ : List Bool} (hb : R.Biv x σ) {v w : Bool}
    (hv : R.Univ x (σ ++ [false]) v) (hw : R.Univ x (σ ++ [true]) w) : v ≠ w := by
  rintro rfl
  have : R.Univ x σ v := by
    intro τ u hu
    cases τ with
    | nil => exact hv [] u (by simpa using R.dec_append hu [false])
    | cons m τ =>
      cases m
      · exact hv τ u (by simpa using hu)
      · exact hw τ u (by simpa using hu)
  obtain ⟨τ, hτ⟩ : R.Pot x σ (!v) := by cases v; exacts [hb.1, hb.2]
  have := this τ _ hτ
  cases v <;> simp_all

/-! ## Existence of a critical schedule -/

/-- **The critical state** (proof of Theorem 3): from a bivalent schedule, some extension is
bivalent with both one-move extensions univalent. -/
theorem exists_crit (hR : R.RCorrect) {x : Fin n → Bool} {σ₀ : List Bool} (h₀ : R.Biv x σ₀) :
    ∃ σ, R.Biv x σ ∧ ¬ R.Biv x (σ ++ [false]) ∧ ¬ R.Biv x (σ ++ [true]) := by
  classical
  by_contra hcon
  push Not at hcon
  -- an infinite bivalent schedule
  let nxt : List Bool → Bool := fun σ => if R.Biv x (σ ++ [false]) then false else true
  have hnxt : ∀ σ, R.Biv x σ → R.Biv x (σ ++ [nxt σ]) := by
    intro σ hσ
    by_cases h : R.Biv x (σ ++ [false])
    · simp [nxt, h]
    · simp only [nxt, h, ite_false]; exact hcon σ hσ h
  let L : ℕ → List Bool := fun t => Nat.rec σ₀ (fun _ σ => σ ++ [nxt σ]) t
  have hL : ∀ t, R.Biv x (L t) := by
    intro t
    induction t with
    | zero => exact h₀
    | succ t ih => exact hnxt _ ih
  let sch : ℕ → Bool := ext σ₀ false |>.comp id |> fun f t =>
    if t < σ₀.length then f t else nxt (L (t - σ₀.length))
  have hpre : ∀ t, bpre sch (σ₀.length + t) = L t := by
    intro t
    induction t with
    | zero =>
      rw [Nat.add_zero]
      apply List.ext_getElem (by simp [L])
      intro i h1 h2
      have hi : i < σ₀.length := by simpa using h1
      simp [bpre, sch, ext, hi, L]
    | succ t ih =>
      rw [← Nat.add_assoc, bpre_succ, ih]
      simp [sch, L]
  have hbiv : ∀ t ≥ σ₀.length, R.Biv x (bpre sch t) := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [hpre]; exact hL d
  -- some process moves infinitely often, and then outputs at a bivalent point
  have hfin : ∀ m N, (∀ M, ∃ t ≥ M, sch t = m) →
      (∀ t ≥ N, R.eInf x sch t ≠ .crash (R.who m)) → False := by
    intro m N hinf hN
    obtain ⟨t, ht, u, hu⟩ := hR.prog x sch m (max N σ₀.length) hinf
      (fun t ht => hN t (le_of_max_le_left ht))
    exact not_out_of_biv hR (hbiv t (le_of_max_le_right ht)) hu
  by_cases htrue : ∀ M, ∃ t ≥ M, sch t = true
  · exact hfin true 0 htrue (fun t _ => R.ev_ne_crash_b _ _)
  · push Not at htrue
    obtain ⟨M, hM⟩ := htrue
    obtain ⟨N, hN⟩ := R.eventually_no_crash x sch
    exact hfin false N (fun M' => ⟨max M M', le_max_right _ _, by
      simpa using hM (max M M') (le_max_left _ _)⟩) (fun t ht => hN t ht _)

/-! ## Indistinguishability for solo runs -/

/-- `s` and `s'` are indistinguishable to `a`, and agree on all objects outside `S`. -/
structure AgA (R : Restr A) (S : Set ι) (s s' : RS A) : Prop where
  mem : ∀ j ∉ S, s.c.mem j = s'.c.mem j
  loc : s.c.loc R.a = s'.c.loc R.a
  inp : s.c.inp R.a = s'.c.inp R.a
  trg : s.trg = s'.trg
  pend : s.pend = s'.pend

lemma newTrig_congr {s s' : RS A} (hl : s.c.loc R.a = s'.c.loc R.a) (ht : s.trg = s'.trg) :
    R.newTrig s = R.newTrig s' := by
  simp only [newTrig, hl, ht]

lemma AgA.mv {S : Set ι} {s s' : RS A} (h : R.AgA S s s')
    (hS : s.pend = false → ∀ i ∈ S, ¬ s.c.Poised R.a i) :
    R.AgA S (R.mv s false) (R.mv s' false) ∧ R.ev s false = R.ev s' false := by
  by_cases hp : s.pend
  · have hp' : s'.pend = true := h.pend ▸ hp
    rw [R.mv_false_pend s hp, R.mv_false_pend s' hp', R.ev_false_pend s hp,
      R.ev_false_pend s' hp']
    refine ⟨⟨fun j hj => h.mem j hj, ?_, h.inp, h.trg, rfl⟩, rfl⟩
    simp [Cfg.next, h.inp]
  · simp only [Bool.not_eq_true] at hp
    have hp' : s'.pend = false := h.pend ▸ hp
    rw [R.mv_false_npend s hp, R.mv_false_npend s' hp', R.ev_false_npend s hp,
      R.ev_false_npend s' hp', R.newTrig_congr h.loc h.trg]
    refine ⟨?_, rfl⟩
    -- the step of `a`
    have hstep : (∀ j ∉ S, (s.c.stepP R.a).mem j = (s'.c.stepP R.a).mem j) ∧
        (s.c.stepP R.a).loc R.a = (s'.c.stepP R.a).loc R.a := by
      rcases hact : A.act (s.c.loc R.a) with ⟨i, o, k⟩ | v
      · have hact' : A.act (s'.c.loc R.a) = .access i o k := by rw [← h.loc]; exact hact
        have hi : i ∉ S := fun hi => hS hp i hi ⟨o, k, hact⟩
        have hmi : s.c.mem i = s'.c.mem i := h.mem i hi
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [stepP_mem_of_access _ hact, stepP_mem_of_access _ hact']
          by_cases hji : j = i
          · subst hji; simp [hmi]
          · simp [Function.update_of_ne hji, h.mem j hj]
        · rw [stepP_loc_self _ hact, stepP_loc_self _ hact', hmi]
      · have hact' : A.act (s'.c.loc R.a) = .out v := by rw [← h.loc]; exact hact
        rw [stepP_of_out _ (show s.c.Out R.a v from hact),
          stepP_of_out _ (show s'.c.Out R.a v from hact')]
        exact ⟨h.mem, h.loc⟩
    rcases R.newTrig s' with _ | i
    · exact ⟨hstep.1, hstep.2, by simpa using h.inp, h.trg, h.pend⟩
    · exact ⟨hstep.1, hstep.2, by simpa using h.inp, by simp [h.trg], rfl⟩

lemma AgA.solo {S : Set ι} {s s' : RS A} (h : R.AgA S s s') (k : ℕ)
    (hS : ∀ j < k, (R.rrun s (List.replicate j false)).pend = false →
      ∀ i ∈ S, ¬ (R.rrun s (List.replicate j false)).c.Poised R.a i) :
    R.AgA S (R.rrun s (List.replicate k false)) (R.rrun s' (List.replicate k false)) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have ih' := ih (fun j hj => hS j (by omega))
    rw [List.replicate_succ', R.rrun_append, R.rrun_append]
    exact (ih'.mv (hS k (by omega))).1

lemma rrun_b_solo_c (s : RS A) (k : ℕ) :
    (R.rrun s (List.replicate k true)).c = run s.c (List.replicate k (.step R.b)) := by
  rw [R.rrun_c]
  congr 1
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

/-! ## Contradictions -/

variable {x : Fin n → Bool}

/-- If two schedules with different univalent values end in states indistinguishable to `b`,
contradiction (`b` running solo decides the same value from both). -/
theorem contra_b (hR : R.RCorrect) {σ₁ σ₂ : List Bool} {v w : Bool} (h₁ : R.Univ x σ₁ v)
    (h₂ : R.Univ x σ₂ w) (hag : AgreeOn {R.b} (R.S x σ₁).c (R.S x σ₂).c) : v = w := by
  obtain ⟨k, u, hu⟩ := solo_b hR x σ₁
  have e1 := h₁.append (List.replicate k true) |>.of_out hu
  rw [R.S_append, R.rrun_b_solo_c] at hu
  have hag' := run_agreeOn hag (List.replicate k (.step R.b)) (by simp)
  have hu' := (hag'.out_iff (Set.mem_singleton _) u).1 hu
  rw [← R.rrun_b_solo_c, ← R.S_append] at hu'
  have e2 := h₂.append (List.replicate k true) |>.of_out hu'
  rw [← e1, ← e2]

/-- If two schedules with different univalent values end in states indistinguishable to `a`
(including the restricted-model bookkeeping), which may differ on a set `S` of objects that `a`
never accesses in its solo run from the first state, contradiction. -/
theorem contra_a (hR : R.RCorrect) {σ₁ σ₂ : List Bool} {v w : Bool} {S : Set ι}
    (h₁ : R.Univ x σ₁ v) (h₂ : R.Univ x σ₂ w) (hag : R.AgA S (R.S x σ₁) (R.S x σ₂))
    (hS : ∀ j, (R.S x (σ₁ ++ List.replicate j false)).pend = false →
      ∀ i ∈ S, ¬ (R.S x (σ₁ ++ List.replicate j false)).c.Poised R.a i) : v = w := by
  obtain ⟨k, u, hu⟩ := solo_a hR x σ₁
  have e1 := h₁.append (List.replicate k false) |>.of_out hu
  have hag' := hag.solo k (fun j _ => by rw [← R.S_append]; exact hS j)
  rw [← R.S_append, ← R.S_append] at hag'
  have hu' : (R.S x (σ₂ ++ List.replicate k false)).c.Out R.a u := by
    unfold Cfg.Out at hu ⊢; rw [← hag'.loc]; exact hu
  have e2 := h₂.append (List.replicate k false) |>.of_out hu'
  rw [← e1, ← e2]

end Restr

end Podc.RecoverableHierarchy
