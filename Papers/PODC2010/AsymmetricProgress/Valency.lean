import Papers.PODC2010.AsymmetricProgress.Model

-- CSLib candidate: shared memory with caller-aware, possibly blocking base objects; valency
-- toolkit (deciders, critical configurations, all processes poised on one object).

/-!
# Valency (Section 3.3) and Lemmas 1–3

Since the system is deterministic, a finite run is determined by its last configuration (outputs
persist in the local states), so valency is defined on configurations:

* `CanDec C v` — some extension of `C` contains a decision `v`;
* `Val C v` — `C` is `v`-valent: every decision in an extension of `C` is `v`;
* `Biv C` — both values can still be decided;
* `Decider C p` — `p` is a decider at `C`: for every extension `y` of `C`, `y p` is not bivalent
  (under obstruction-freedom this means univalent, as in the paper).

Main statements: `lemma1` (Lemma 1), `lemma2` (Lemma 2), `lemma3` (Lemma 3), and the
commutation lemma `run_comm_of_avoids` used to repair the proof of Lemma 6.
-/

namespace Podc.AsymmetricProgress

set_option linter.unusedSectionVars false

variable {n : ℕ} {ι : Type} [DecidableEq ι] {T : ι → BObj n} {A : Alg n T}

/-- Some extension of `C` contains a decision `v`. -/
def CanDec (C : Cfg A) (v : Bool) : Prop := ∃ σ p, (run C σ).Out p v

/-- `C` is `v`-valent: every decision in every extension of `C` is `v`. -/
def Val (C : Cfg A) (v : Bool) : Prop := ∀ w, CanDec C w → w = v

/-- `C` is bivalent. -/
def Biv (C : Cfg A) : Prop := CanDec C true ∧ CanDec C false

/-- `p` is a decider at `C`: for every extension `y` of `C`, the run `y p` is not bivalent. -/
def Decider (C : Cfg A) (p : Fin n) : Prop := ∀ σ, ¬ Biv (run C (σ ++ [p]))

lemma CanDec.of_run {C : Cfg A} {σ : List (Fin n)} {v : Bool} (h : CanDec (run C σ) v) :
    CanDec C v := by
  obtain ⟨τ, p, hp⟩ := h
  exact ⟨σ ++ τ, p, by rwa [run_append]⟩

lemma CanDec.of_out {C : Cfg A} {p : Fin n} {v : Bool} (h : C.Out p v) : CanDec C v :=
  ⟨[], p, h⟩

lemma Val.run {C : Cfg A} {v : Bool} (h : Val C v) (σ : List (Fin n)) :
    Val (Podc.AsymmetricProgress.run C σ) v := fun w hw => h w hw.of_run

lemma Val.step {C : Cfg A} {v : Bool} (h : Val C v) (p : Fin n) : Val (C.step p) v :=
  h.run [p]

lemma Val.eq {C : Cfg A} {v w : Bool} (h : Val C v) (hw : CanDec C w) : w = v := h w hw

lemma biv_iff {C : Cfg A} : Biv C ↔ ∀ v, CanDec C v := by
  constructor
  · rintro ⟨h1, h2⟩ v; cases v <;> assumption
  · intro h; exact ⟨h true, h false⟩

lemma Biv.not_val {C : Cfg A} (h : Biv C) {v : Bool} : ¬ Val C v := by
  intro hv
  have h1 := hv.eq (biv_iff.1 h v)
  have h2 := hv.eq (biv_iff.1 h (!v))
  cases v <;> simp_all

/-- A non-bivalent configuration from which `w` can be decided is `w`-valent. -/
lemma val_of_not_biv {C : Cfg A} (h : ¬ Biv C) {w : Bool} (hw : CanDec C w) : Val C w := by
  intro u hu
  by_contra hne
  apply h
  rw [biv_iff]
  intro v
  rcases Bool.eq_or_eq_not v w with rfl | rfl
  · exact hw
  · have : u = !w := by cases u <;> cases w <;> simp_all
    rwa [← this]

lemma Biv.of_val {C : Cfg A} {σ τ : List (Fin n)} {v : Bool}
    (h1 : Val (run C σ) v) (h1' : CanDec (run C σ) v)
    (h2 : Val (run C τ) (!v)) (h2' : CanDec (run C τ) (!v)) : Biv C := by
  rw [biv_iff]
  intro w
  rcases Bool.eq_or_eq_not w v with rfl | rfl
  · exact h1'.of_run
  · exact h2'.of_run

/-- Under obstruction-freedom of some process, something can be decided from every reachable
configuration. -/
lemma exists_canDec {p : Fin n} (hOF : OFree A p) {C : Cfg A} (hC : Reachable C) :
    ∃ v, CanDec C v := by
  obtain ⟨k, v, hk⟩ := hOF C hC
  exact ⟨v, _, p, hk⟩

/-- A reachable configuration at which some process has output `v` is `v`-valent. -/
lemma Val.of_out (hS : Safe A) {C : Cfg A} (hC : Reachable C) {p : Fin n} {v : Bool}
    (h : C.Out p v) : Val C v := by
  rintro w ⟨σ, q, hq⟩
  exact (hS.agree (hC.run σ) (h.run σ) hq).symm

/-- Nobody has decided in a reachable bivalent configuration. -/
lemma Biv.not_out (hS : Safe A) {C : Cfg A} (hC : Reachable C) (h : Biv C) (p : Fin n)
    (v : Bool) : ¬ C.Out p v := fun hv => h.not_val (Val.of_out hS hC hv)

/-- Two univalent configurations of which the second extends the first have the same valency
(obstruction-freedom guarantees that something is decided). -/
lemma val_eq_of_run {p : Fin n} (hOF : OFree A p) {C : Cfg A} (hC : Reachable C) {v w : Bool}
    (hv : Val C v) (σ : List (Fin n)) (hw : Val (run C σ) w) : v = w := by
  obtain ⟨u, hu⟩ := exists_canDec hOF (hC.run σ)
  rw [← hv.eq hu.of_run, hw.eq hu]

/-! ## Lemma 1 -/

/-- `C` and `D` are indistinguishable to `p` and all objects have the same state. -/
def AgreeP (p : Fin n) (C D : Cfg A) : Prop := C.loc p = D.loc p ∧ C.mem = D.mem

lemma AgreeP.step {p : Fin n} {C D : Cfg A} (h : AgreeP p C D) : AgreeP p (C.step p) (D.step p) := by
  obtain ⟨h1, h2⟩ := h
  unfold Cfg.step
  rw [← h1, ← h2]
  split
  · rename_i i o k _
    refine ⟨?_, rfl⟩
    cases ((T i).δ (C.mem i) p o).2 <;> simp [h1]
  · exact ⟨h1, h2⟩

lemma AgreeP.solo {p : Fin n} {C D : Cfg A} (h : AgreeP p C D) (k : ℕ) :
    AgreeP p (run C (List.replicate k p)) (run D (List.replicate k p)) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [run_replicate_succ, run_replicate_succ]; exact ih.step

/-- **Lemma 1** of the paper. In an obstruction-free consensus algorithm, two univalent
configurations that are indistinguishable to some process `p` and in which all objects have the
same state are compatible (have the same valency). -/
theorem lemma1 {p : Fin n} (hOF : OFree A p) {C D : Cfg A} (hC : Reachable C)
    (h : AgreeP p C D) {v w : Bool} (hv : Val C v) (hw : Val D w) : v = w := by
  obtain ⟨k, u, hk⟩ := hOF C hC
  have hk' : (run D (List.replicate k p)).Out p u := by
    have := (h.solo k).1
    unfold Cfg.Out at hk ⊢
    rwa [← this]
  rw [← hv.eq ⟨_, p, hk⟩, ← hw.eq ⟨_, p, hk'⟩]

/-! ## Lemma 2 -/

lemma step_loc_self {C : Cfg A} {p : Fin n} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act (C.loc p) = .access i o k) :
    (C.step p).loc p = (((T i).δ (C.mem i) p o).2).elim (C.loc p) k := by
  rw [step_of_access h]
  cases ((T i).δ (C.mem i) p o).2 <;> simp

lemma step_mem_self {C : Cfg A} {p : Fin n} {i : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act (C.loc p) = .access i o k) :
    (C.step p).mem i = ((T i).δ (C.mem i) p o).1 := by
  rw [step_of_access h]; simp

lemma step_mem_ne {C : Cfg A} {p : Fin n} {i j : ι} {o : (T i).Op} {k : (T i).Resp → A.L}
    (h : A.act (C.loc p) = .access i o k) (hj : j ≠ i) : (C.step p).mem j = C.mem j := by
  rw [step_of_access h]; simp [Function.update_of_ne hj]

/-- **Lemma 2** of the paper. Let `D` be reachable, `p ≠ q`, `D p` `v`-valent and `D q p`
`(!v)`-valent. Then `p` and `q` are poised on the same object `i` and this object is not
read/write-like (in particular not an atomic register). -/
theorem lemma2 (hOF : ∀ r, OFree A r) {D : Cfg A} (hD : Reachable D)
    {p q : Fin n} (hpq : p ≠ q) {v : Bool} (h1 : Val (D.step p) v)
    (h2 : Val ((D.step q).step p) (!v)) :
    ∃ i, D.objOf p = some i ∧ D.objOf q = some i ∧ ¬ (T i).RWLike := by
  have hne : ∀ σ, ¬ Val (run (D.step p) σ) (!v) := fun σ h =>
    by have := val_eq_of_run (hOF p) (hD.step p) h1 σ h; cases v <;> simp at this
  rcases hp : A.act (D.loc p) with ⟨i, o, k⟩ | u
  · rcases hq : A.act (D.loc q) with ⟨j, o', k'⟩ | u'
    · by_cases hij : i = j
      · subst hij
        refine ⟨i, objOf_eq_some_iff.2 ⟨o, k, hp⟩, objOf_eq_some_iff.2 ⟨o', k', hq⟩, ?_⟩
        intro hrw
        have hq1 : A.act ((D.step p).loc q) = .access i o' k' := by
          rw [step_loc_other D hpq.symm, hq]
        have hp1 : A.act ((D.step q).loc p) = .access i o k := by
          rw [step_loc_other D hpq, hp]
        rcases hrw o with hro | hov
        · -- `p` reads: `D p q` and `D q p` are indistinguishable to `q`
          have hag : AgreeP q ((D.step p).step q) ((D.step q).step p) := by
            have hmp : (D.step p).mem = D.mem := by
              funext j
              by_cases hj : j = i
              · subst hj; rw [step_mem_self hp, hro]
              · exact step_mem_ne hp hj
            constructor
            · rw [step_loc_other _ hpq.symm, step_loc_self hq1, step_loc_self hq,
                step_loc_other D hpq.symm, hmp]
            · funext j
              by_cases hj : j = i
              · subst hj
                rw [step_mem_self hq1, step_mem_self hp1, hro, hmp, step_mem_self hq]
              · rw [step_mem_ne hq1 hj, step_mem_ne hp1 hj, step_mem_ne hp hj,
                  step_mem_ne hq hj]
          have := lemma1 (hOF q) ((hD.step p).step q) hag (h1.step q) h2
          cases v <;> simp at this
        · -- `p` overwrites: `D p` and `D q p` are indistinguishable to `p`
          have hag : AgreeP p (D.step p) ((D.step q).step p) := by
            constructor
            · rw [step_loc_self hp, step_loc_self hp1, step_loc_other D hpq,
                hov ((D.step q).mem i) (D.mem i)]
            · funext j
              by_cases hj : j = i
              · subst hj
                rw [step_mem_self hp, step_mem_self hp1, hov ((D.step q).mem j) (D.mem j)]
              · rw [step_mem_ne hp hj, step_mem_ne hp1 hj, step_mem_ne hq hj]
          have := lemma1 (hOF p) (hD.step p) hag h1 h2
          cases v <;> simp at this
      · -- different objects: the steps commute
        exfalso
        have hc := step_comm D hpq (by
          intro l hl hl'
          rw [objOf_eq_some_iff] at hl hl'
          obtain ⟨_, _, hl⟩ := hl; obtain ⟨_, _, hl'⟩ := hl'
          rw [hp] at hl; rw [hq] at hl'
          cases hl; cases hl'; exact hij rfl)
        rw [← hc] at h2
        exact hne [q] h2
    · exfalso
      have hqo : D.step q = D := step_of_out (show D.Out q u' from hq)
      rw [hqo] at h2
      exact hne [] h2
  · exfalso
    have hpo : D.step p = D := step_of_out (show D.Out p u from hp)
    rw [hpo] at h1 hne
    exact hne [q, p] (by simpa using h2)

/-! ## Lemma 3 -/

/-- In an obstruction-free consensus algorithm, a process running alone from an initial
configuration decides its own input (validity + indistinguishability from the unanimous
configuration). -/
lemma canDec_initial (hS : Safe A) (hOF : ∀ r, OFree A r) (x : Fin n → Bool) (p : Fin n) :
    CanDec (initCfg A x) (x p) := by
  obtain ⟨k, u, hk⟩ := hOF p (initCfg A (fun _ => x p)) (reachable_initCfg _)
  have hag : AgreeP p (initCfg A (fun _ => x p)) (initCfg A x) := ⟨rfl, rfl⟩
  have hk' : (run (initCfg A x) (List.replicate k p)).Out p u := by
    have := (hag.solo k).1
    unfold Cfg.Out at hk ⊢
    rwa [← this]
  obtain ⟨r, hr⟩ := hS.2 _ _ _ _ hk
  subst hr
  exact ⟨_, p, hk'⟩

/-- **Lemma 3** of the paper. Every obstruction-free consensus algorithm for `n ≥ 2` processes
has a bivalent initial configuration. -/
theorem lemma3 (hS : Safe A) (hOF : ∀ r, OFree A r) (hn : 2 ≤ n) :
    ∃ x, Biv (initCfg A x) := by
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨1, by omega⟩
  let x : Fin n → Bool := fun r => decide (r = q)
  refine ⟨x, ?_, ?_⟩
  · have := canDec_initial hS hOF x q
    simpa [x] using this
  · have := canDec_initial hS hOF x p
    have hpq : p ≠ q := by simp [p, q, Fin.ext_iff]
    simpa [x, hpq] using this

/-! ## Commuting a step past a run that avoids its object -/

/-- The schedule `τ`, run from `C`, never accesses object `i`. -/
def Avoids : Cfg A → List (Fin n) → ι → Prop
  | _, [], _ => True
  | C, r :: τ, i => C.objOf r ≠ some i ∧ Avoids (C.step r) τ i

/-- A step of `p` on object `i` commutes with a schedule of other processes that avoids `i`. -/
lemma run_comm_of_avoids {C : Cfg A} {p : Fin n} {i : ι} (hp : C.objOf p = some i)
    {τ : List (Fin n)} (hτ : Avoids C τ i) (hpτ : p ∉ τ) :
    run C (τ ++ [p]) = run (C.step p) τ := by
  induction τ generalizing C with
  | nil => simp
  | cons r τ ih =>
    obtain ⟨hr, hτ⟩ := hτ
    have hrp : r ≠ p := fun h => hpτ (by simp [h])
    have hpτ' : p ∉ τ := fun h => hpτ (by simp [h])
    rw [List.cons_append, run_cons, ih (by rw [objOf_step_other C hrp.symm]; exact hp) hτ hpτ',
      step_comm C hrp (fun j hj hj' => hr (by rw [hj]; rw [hp] at hj'; exact hj'.symm)),
      run_cons]

/-- Avoidance of `i` is not affected by a preceding step of a process poised on `i`. -/
lemma Avoids.step_of_poised {C : Cfg A} {q : Fin n} {i : ι} (hq : C.objOf q = some i)
    {τ : List (Fin n)} (hτ : Avoids C τ i) (hqτ : q ∉ τ) : Avoids (C.step q) τ i := by
  induction τ generalizing C with
  | nil => trivial
  | cons r τ ih =>
    obtain ⟨hr, hτ⟩ := hτ
    have hrq : r ≠ q := fun h => hqτ (by simp [h])
    refine ⟨by rwa [objOf_step_other C hrq], ?_⟩
    rw [← step_comm C hrq (fun j hj hj' => hr (by rw [hj]; rw [hq] at hj'; exact hj'.symm))]
    exact ih (by rw [objOf_step_other C hrq.symm]; exact hq) hτ (fun h => hqτ (by simp [h]))

lemma avoids_replicate {C : Cfg A} {s : Fin n} {i : ι} {j : ℕ}
    (h : ∀ l < j, (run C (List.replicate l s)).objOf s ≠ some i) :
    Avoids C (List.replicate j s) i := by
  induction j generalizing C with
  | zero => trivial
  | succ j ih =>
    refine ⟨h 0 (by omega), ih fun l hl => ?_⟩
    have := h (l + 1) (by omega)
    rwa [List.replicate_succ, run_cons] at this

lemma run_loc_other (C : Cfg A) {σ : List (Fin n)} {q : Fin n} (h : q ∉ σ) :
    (run C σ).loc q = C.loc q := by
  induction σ generalizing C with
  | nil => rfl
  | cons r σ ih =>
    rw [run_cons, ih _ (fun h' => h (by simp [h'])), step_loc_other C (fun h' => h (by simp [h']))]

lemma run_objOf_other (C : Cfg A) {σ : List (Fin n)} {q : Fin n} (h : q ∉ σ) :
    (run C σ).objOf q = C.objOf q := by
  unfold Cfg.objOf; rw [run_loc_other C h]

lemma Decider.run {C : Cfg A} {p : Fin n} (h : Decider C p) (σ : List (Fin n)) :
    Decider (Podc.AsymmetricProgress.run C σ) p := fun τ => by
  rw [← run_append]; simpa [List.append_assoc] using h (σ ++ τ)

end Podc.AsymmetricProgress
