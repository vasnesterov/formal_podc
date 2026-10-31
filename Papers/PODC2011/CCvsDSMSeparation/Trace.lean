import Papers.PODC2011.CCvsDSMSeparation.Model

/-!
# Basic lemmas about executions

Prefix-indexed predicates (`Steps`), projections, last writers and values, validity of
concatenations, erasing processes (`erase`, Lemma 6.7 of the paper), and transporting a segment of
an execution to another execution that agrees on the relevant local states and variables.
-/

namespace Podc.CCvsDSMSeparation

variable {N : ℕ} {V Val S : Type*}

/-! ### `Steps` -/

section Steps

variable {α : Type*} {P Q : List α → α → Prop}

@[simp] lemma stepsFrom_nil (ρ : List α) : StepsFrom P ρ [] := trivial

@[simp] lemma stepsFrom_cons (ρ : List α) (e : α) (σ : List α) :
    StepsFrom P ρ (e :: σ) ↔ P ρ e ∧ StepsFrom P (ρ ++ [e]) σ := Iff.rfl

lemma stepsFrom_append (ρ τ σ : List α) :
    StepsFrom P ρ (τ ++ σ) ↔ StepsFrom P ρ τ ∧ StepsFrom P (ρ ++ τ) σ := by
  induction τ generalizing ρ with
  | nil => simp
  | cons e τ ih => simp [ih, and_assoc]

lemma stepsFrom_iff (ρ σ : List α) :
    StepsFrom P ρ σ ↔ ∀ σ₁ e σ₂, σ = σ₁ ++ e :: σ₂ → P (ρ ++ σ₁) e := by
  induction σ generalizing ρ with
  | nil => simp
  | cons e σ ih =>
    simp only [stepsFrom_cons, ih]
    constructor
    · rintro ⟨h1, h2⟩ σ₁ e' σ₂ h
      cases σ₁ with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; simpa using h1
      | cons a σ₁ =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa using h2 σ₁ e' σ₂ rfl
    · intro h
      refine ⟨by simpa using h [] e σ rfl, fun σ₁ e' σ₂ h' => ?_⟩
      simpa using h (e :: σ₁) e' σ₂ (by simp [h'])

lemma steps_iff (σ : List α) :
    Steps P σ ↔ ∀ σ₁ e σ₂, σ = σ₁ ++ e :: σ₂ → P σ₁ e := by
  simp [Steps, stepsFrom_iff]

lemma steps_append (τ σ : List α) :
    Steps P (τ ++ σ) ↔ Steps P τ ∧ StepsFrom P τ σ := by
  simp [Steps, stepsFrom_append]

lemma steps_snoc (τ : List α) (e : α) : Steps P (τ ++ [e]) ↔ Steps P τ ∧ P τ e := by
  simp [steps_append]

@[simp] lemma steps_nil : Steps P ([] : List α) := trivial

lemma StepsFrom.mono {ρ σ : List α} (h : StepsFrom P ρ σ)
    (hPQ : ∀ σ₁ e, (σ₁ ++ [e]) <+: σ → P (ρ ++ σ₁) e → Q (ρ ++ σ₁) e) : StepsFrom Q ρ σ := by
  rw [stepsFrom_iff] at h ⊢
  intro σ₁ e σ₂ hs
  exact hPQ σ₁ e ⟨σ₂, by simp [hs]⟩ (h σ₁ e σ₂ hs)

lemma Steps.mono {σ : List α} (h : Steps P σ)
    (hPQ : ∀ σ₁ e, (σ₁ ++ [e]) <+: σ → P σ₁ e → Q σ₁ e) : Steps Q σ :=
  StepsFrom.mono h (by simpa using hPQ)

end Steps

/-! ### Projections, participants, writers -/

@[simp] lemma proj_nil (p : Fin N) : proj ([] : List (Ev N V Val)) p = [] := rfl

lemma proj_append (τ σ : List (Ev N V Val)) (p : Fin N) :
    proj (τ ++ σ) p = proj τ p ++ proj σ p := by
  simp [proj, List.filter_append]

lemma proj_cons (e : Ev N V Val) (σ : List (Ev N V Val)) (p : Fin N) :
    proj (e :: σ) p = (if e.p = p then [e.op] else []) ++ proj σ p := by
  by_cases h : e.p = p <;> simp [proj, h]

lemma proj_singleton (e : Ev N V Val) (p : Fin N) :
    proj [e] p = if e.p = p then [e.op] else [] := by
  simp [proj_cons]

lemma proj_snoc_self (τ : List (Ev N V Val)) (e : Ev N V Val) :
    proj (τ ++ [e]) e.p = proj τ e.p ++ [e.op] := by
  simp [proj_append, proj_singleton]

lemma proj_snoc_ne (τ : List (Ev N V Val)) (e : Ev N V Val) {p : Fin N} (h : e.p ≠ p) :
    proj (τ ++ [e]) p = proj τ p := by
  simp [proj_append, proj_singleton, h]

lemma proj_eq_nil_of_forall (σ : List (Ev N V Val)) (p : Fin N) (h : ∀ e ∈ σ, e.p ≠ p) :
    proj σ p = [] := by
  simp only [proj, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  exact h

lemma proj_append_of_forall (τ σ : List (Ev N V Val)) (p : Fin N) (h : ∀ e ∈ σ, e.p ≠ p) :
    proj (τ ++ σ) p = proj τ p := by
  simp [proj_append, proj_eq_nil_of_forall σ p h]

@[simp] lemma par_nil : par ([] : List (Ev N V Val)) = ∅ := rfl

lemma par_append (τ σ : List (Ev N V Val)) : par (τ ++ σ) = par τ ∪ par σ := by
  simp [par, List.toFinset_append]

lemma mem_par {τ : List (Ev N V Val)} {p : Fin N} : p ∈ par τ ↔ ∃ e ∈ τ, e.p = p := by
  simp [par]

lemma par_subset_of_forall {σ : List (Ev N V Val)} {T : Finset (Fin N)} (h : ∀ e ∈ σ, e.p ∈ T) :
    par σ ⊆ T := by
  intro p hp; obtain ⟨e, he, rfl⟩ := mem_par.1 hp; exact h e he

lemma signals_append (τ σ : List (Ev N V Val)) : signals (τ ++ σ) = signals τ + signals σ := by
  simp [signals, List.countP_append]

lemma signals_eq_zero {σ : List (Ev N V Val)} (h : ∀ e ∈ σ, e.op.isSigInv = false) :
    signals σ = 0 := by
  simp only [signals, List.countP_eq_zero]; intro e he; simp [h e he]

section Writer

open Classical

/-- The step function of `lastWrite`. -/
noncomputable def lwStep (v : V) (acc : Option (Fin N × Val)) (e : Ev N V Val) :
    Option (Fin N × Val) :=
  match e.op.written with
  | some (u, x) => if u = v then some (e.p, x) else acc
  | none => acc

lemma lastWrite_eq_foldl (v : V) (τ : List (Ev N V Val)) :
    lastWrite v τ = τ.foldl (lwStep v) none := rfl

@[simp] lemma lastWrite_nil (v : V) : lastWrite v ([] : List (Ev N V Val)) = none := rfl

/-- `e` writes `v`. -/
def Ev.Writes (e : Ev N V Val) (v : V) : Prop := ∃ x, e.op = .write v x

lemma lastWrite_snoc (v : V) (τ : List (Ev N V Val)) (e : Ev N V Val) :
    lastWrite v (τ ++ [e]) = lwStep v (lastWrite v τ) e := by
  simp [lastWrite_eq_foldl, List.foldl_append]

lemma lwStep_of_not_writes {v : V} (acc : Option (Fin N × Val)) {e : Ev N V Val}
    (h : ¬ e.Writes v) : lwStep v acc e = acc := by
  rcases e with ⟨p, op⟩
  cases op <;> simp_all [lwStep, Op.written, Ev.Writes]

lemma lwStep_of_write {v : V} (acc : Option (Fin N × Val)) {p : Fin N} {x : Val} :
    lwStep v acc ⟨p, .write v x⟩ = some (p, x) := by
  simp [lwStep, Op.written]

lemma lastWrite_append_of_not_writes (v : V) (τ σ : List (Ev N V Val))
    (h : ∀ e ∈ σ, ¬ e.Writes v) : lastWrite v (τ ++ σ) = lastWrite v τ := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ e ih =>
    rw [← List.append_assoc, lastWrite_snoc, lwStep_of_not_writes _ (h e (by simp)),
      ih (fun e' he' => h e' (by simp [he']))]

lemma writer_snoc (v : V) (τ : List (Ev N V Val)) (e : Ev N V Val) :
    writer v (τ ++ [e]) = if e.Writes v then some e.p else writer v τ := by
  unfold writer
  rw [lastWrite_snoc]
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    rcases e with ⟨p, op⟩; simp only at hx; subst hx
    simp [lwStep_of_write]
  · rw [lwStep_of_not_writes _ h]

lemma writer_append_of_not_writes (v : V) (τ σ : List (Ev N V Val))
    (h : ∀ e ∈ σ, ¬ e.Writes v) : writer v (τ ++ σ) = writer v τ := by
  simp [writer, lastWrite_append_of_not_writes v τ σ h]

lemma writer_mem {v : V} {τ : List (Ev N V Val)} {q : Fin N} (h : writer v τ = some q) :
    ∃ e ∈ τ, e.p = q ∧ e.Writes v := by
  induction τ using List.reverseRecOn with
  | nil => simp [writer] at h
  | append_singleton τ e ih =>
    rw [writer_snoc] at h
    split_ifs at h with hw
    · cases h; exact ⟨e, by simp, rfl, hw⟩
    · obtain ⟨e', he', h1, h2⟩ := ih h; exact ⟨e', by simp [he'], h1, h2⟩

lemma Ev.Writes.var {e : Ev N V Val} {v : V} (h : e.Writes v) : e.op.var = some v := by
  obtain ⟨x, hx⟩ := h; simp [hx, Op.var]

end Writer

/-! ### Values of variables -/

namespace Algorithm

variable (A : Algorithm N V Val S)

lemma memVal_eq_of_lastWrite {τ τ' : List (Ev N V Val)} {v : V}
    (h : lastWrite v τ' = lastWrite v τ) : A.memVal τ' v = A.memVal τ v := by
  simp [memVal, h]

lemma memVal_snoc_write (τ : List (Ev N V Val)) (p : Fin N) (v : V) (x : Val) :
    A.memVal (τ ++ [⟨p, .write v x⟩]) v = x := by
  simp [memVal, lastWrite_snoc, lwStep_of_write]

lemma memVal_append_of_not_writes (τ σ : List (Ev N V Val)) (v : V)
    (h : ∀ e ∈ σ, ¬ e.Writes v) : A.memVal (τ ++ σ) v = A.memVal τ v :=
  A.memVal_eq_of_lastWrite (lastWrite_append_of_not_writes v τ σ h)

open Classical in
lemma memVal_snoc (τ : List (Ev N V Val)) (e : Ev N V Val) (v : V) :
    A.memVal (τ ++ [e]) v = if e.Writes v then A.memVal [e] v else A.memVal τ v := by
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    rcases e with ⟨p, op⟩; simp only at hx; subst hx
    rw [memVal_snoc_write]; simpa using (A.memVal_snoc_write [] p v x).symm
  · exact A.memVal_append_of_not_writes τ [e] v (by simpa using h)

/-! ### Local runs -/

lemma lrun_snoc (p : Fin N) (l : List (Op V Val)) (op : Op V Val) :
    A.lrun p (l ++ [op]) = (A.lrun p l).bind fun c => A.lstep p c op := by
  simp [lrun, List.foldl_append]

@[simp] lemma lrun_nil (p : Fin N) : A.lrun p [] = some (A.locInit p, none) := rfl

lemma lrun_isSome_of_append {p : Fin N} {l m : List (Op V Val)}
    (h : (A.lrun p (l ++ m)).isSome) : (A.lrun p l).isSome := by
  induction m using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton m op ih =>
    apply ih
    rw [← List.append_assoc, lrun_snoc] at h
    cases h' : A.lrun p (l ++ m) <;> simp_all

/-! ### Validity -/

@[simp] lemma valid_nil : A.Valid [] := trivial

lemma valid_snoc (τ : List (Ev N V Val)) (e : Ev N V Val) :
    A.Valid (τ ++ [e]) ↔ A.Valid τ ∧ A.StepOK τ e := steps_snoc τ e

lemma valid_append (τ σ : List (Ev N V Val)) :
    A.Valid (τ ++ σ) ↔ A.Valid τ ∧ StepsFrom A.StepOK τ σ := steps_append τ σ

lemma Valid.of_append {τ σ : List (Ev N V Val)} (h : A.Valid (τ ++ σ)) : A.Valid τ :=
  ((A.valid_append τ σ).1 h).1

lemma Valid.of_prefix {τ σ : List (Ev N V Val)} (h : A.Valid σ) (hp : τ <+: σ) : A.Valid τ := by
  obtain ⟨ρ, rfl⟩ := hp; exact Valid.of_append A h

lemma Valid.state_isSome {τ : List (Ev N V Val)} (h : A.Valid τ) (p : Fin N) :
    (A.state τ p).isSome := by
  induction τ using List.reverseRecOn with
  | nil => simp [state]
  | append_singleton τ e ih =>
    rw [valid_snoc] at h
    by_cases hp : e.p = p
    · subst hp; unfold state; rw [proj_snoc_self]; exact h.2.1
    · unfold state; rw [proj_snoc_ne τ e hp]; exact ih h.1

lemma state_snoc_ne (τ : List (Ev N V Val)) (e : Ev N V Val) {p : Fin N} (h : e.p ≠ p) :
    A.state (τ ++ [e]) p = A.state τ p := by
  simp [state, proj_snoc_ne τ e h]

lemma state_snoc_self (τ : List (Ev N V Val)) (e : Ev N V Val) :
    A.state (τ ++ [e]) e.p = (A.state τ e.p).bind fun c => A.lstep e.p c e.op := by
  simp [state, proj_snoc_self, lrun_snoc]

lemma state_append_of_forall (τ σ : List (Ev N V Val)) {p : Fin N} (h : ∀ e ∈ σ, e.p ≠ p) :
    A.state (τ ++ σ) p = A.state τ p := by
  simp [state, proj_append_of_forall τ σ p h]

lemma stepOK_congr {τ τ' : List (Ev N V Val)} {e : Ev N V Val} (h : A.StepOK τ e)
    (hp : proj τ' e.p = proj τ e.p)
    (hm : ∀ v x, e.op = .read v x → A.memVal τ' v = A.memVal τ v) :
    A.StepOK τ' e := by
  refine ⟨by rw [hp]; exact h.1, fun v x hx => ?_⟩
  rw [h.2 v x hx, hm v x hx]

/-- **Transport.** A segment `σ` that can follow `τ` can also follow `τ'` if the processes of `σ`
have the same local histories and the variables accessed by `σ` have the same values. -/
lemma valid_transport {τ τ' σ : List (Ev N V Val)} (hv : A.Valid (τ ++ σ)) (hv' : A.Valid τ')
    (hp : ∀ e ∈ σ, proj τ' e.p = proj τ e.p)
    (hm : ∀ e ∈ σ, ∀ v, e.op.var = some v → A.memVal τ' v = A.memVal τ v) :
    A.Valid (τ' ++ σ) := by
  induction σ generalizing τ τ' with
  | nil => simpa using hv'
  | cons e σ ih =>
    have hv1 : A.Valid (τ ++ [e] ++ σ) := by simpa using hv
    have hs : A.StepOK τ e := ((A.valid_snoc τ e).1 (Valid.of_append A hv1)).2
    have hs' : A.StepOK τ' e := A.stepOK_congr hs (hp e (by simp))
      (fun v x hx => hm e (by simp) v (by simp [hx, Op.var]))
    have hv2 : A.Valid (τ' ++ [e]) := (A.valid_snoc τ' e).2 ⟨hv', hs'⟩
    have := ih hv1 hv2 ?_ ?_
    · simpa using this
    · intro e' he'
      by_cases hq : e.p = e'.p
      · rw [hq.symm, proj_snoc_self, proj_snoc_self, hp e (by simp)]
      · rw [proj_snoc_ne _ _ hq, proj_snoc_ne _ _ hq, hp e' (by simp [he'])]
    · intro e' he' v hv
      rw [memVal_snoc, memVal_snoc]
      split_ifs
      · rfl
      · exact hm e' (by simp [he']) v hv

end Algorithm

/-! ### Re-evaluating a read -/

/-- Replace the value of a read by the value given by `m`. -/
def Op.reval (m : V → Val) : Op V Val → Op V Val
  | .read v _ => .read v (m v)
  | op => op

@[simp] lemma Op.var_reval (m : V → Val) (op : Op V Val) : (op.reval m).var = op.var := by
  cases op <;> rfl

@[simp] lemma Op.isSigInv_reval (m : V → Val) (op : Op V Val) :
    (op.reval m).isSigInv = op.isSigInv := by
  cases op <;> rfl

@[simp] lemma Op.isAccess_reval (m : V → Val) (op : Op V Val) :
    (op.reval m).isAccess = op.isAccess := by
  cases op <;> rfl

@[simp] lemma Op.isInv_reval (m : V → Val) (op : Op V Val) :
    (op.reval m).isInv = op.isInv := by
  cases op <;> rfl

lemma Op.written_reval (m : V → Val) (op : Op V Val) : (op.reval m).written = op.written := by
  cases op <;> rfl

lemma Ev.writes_reval_iff (m : V → Val) (p : Fin N) (op : Op V Val) (v : V) :
    (Ev.Writes ⟨p, op.reval m⟩ v) ↔ (Ev.Writes ⟨p, op⟩ v) := by
  cases op <;> simp [Ev.Writes, Op.reval]

lemma Ev.remote_reval (home : V → Fin N) (m : V → Val) (p : Fin N) (op : Op V Val) :
    Ev.remote home ⟨p, op.reval m⟩ = Ev.remote home ⟨p, op⟩ := by
  simp [Ev.remote, Op.remoteFor]

namespace Algorithm

variable (A : Algorithm N V Val S)

lemma lstep_reval_isSome (p : Fin N) (c : LState S) (op : Op V Val) (m : V → Val)
    (h : (A.lstep p c op).isSome) : (A.lstep p c (op.reval m)).isSome := by
  rcases c with ⟨s, _ | o⟩
  · cases op <;> simp_all [lstep, Op.reval]
  · cases op with
    | read v x =>
      simp only [lstep, Op.reval] at h ⊢
      rcases hact : A.act p s with ⟨v', k⟩ | ⟨v', x', s'⟩ | ⟨b', s'⟩ <;> simp_all
    | _ => simpa [Op.reval] using h

/-- The next step of a process is determined by its local history, up to the value read. -/
lemma stepOK_reval {τ τ' : List (Ev N V Val)} {e : Ev N V Val} (h : A.StepOK τ e)
    (hp : proj τ' e.p = proj τ e.p) : A.StepOK τ' ⟨e.p, e.op.reval (A.memVal τ')⟩ := by
  refine ⟨?_, fun v x hx => ?_⟩
  · have h1 := h.1
    simp only at h1 ⊢
    rw [hp]
    rw [lrun_snoc] at h1 ⊢
    cases hc : A.lrun e.p (proj τ e.p) with
    | none => simp [hc] at h1
    | some c =>
      simp only [hc, Option.bind_some] at h1 ⊢
      exact A.lstep_reval_isSome _ _ _ _ h1
  · rcases e with ⟨p, op⟩
    cases op <;> simp [Op.reval] at hx ⊢
    obtain ⟨rfl, rfl⟩ := hx; rfl

end Algorithm

/-! ### RMR counting -/

namespace Algorithm

variable (A : Algorithm N V Val S)

lemma rmr_append (τ σ : List (Ev N V Val)) : A.rmr (τ ++ σ) = A.rmr τ + A.rmr σ := by
  simp [rmr, List.countP_append]

@[simp] lemma rmr_nil : A.rmr ([] : List (Ev N V Val)) = 0 := rfl

lemma rmr_singleton (e : Ev N V Val) : A.rmr [e] = if e.remote A.home then 1 else 0 := by
  simp [rmr, List.countP_cons]

/-- Number of RMRs of `p`. -/
noncomputable def rmrOf (τ : List (Ev N V Val)) (p : Fin N) : ℕ :=
  A.rmr (τ.filter fun e => e.p = p)

lemma rmrOf_append (τ σ : List (Ev N V Val)) (p : Fin N) :
    A.rmrOf (τ ++ σ) p = A.rmrOf τ p + A.rmrOf σ p := by
  simp [rmrOf, List.filter_append, rmr_append]

lemma rmrOf_eq_of_proj {τ τ' : List (Ev N V Val)} {p : Fin N} (h : proj τ' p = proj τ p) :
    A.rmrOf τ' p = A.rmrOf τ p := by
  have key : ∀ τ : List (Ev N V Val), A.rmrOf τ p =
      (proj τ p).countP (Op.remoteFor A.home p) := by
    intro τ
    simp only [rmrOf, rmr, proj, List.countP_map]
    apply List.countP_congr
    intro e he
    simp only [List.mem_filter, decide_eq_true_eq] at he
    simp [Ev.remote, he.2]
  rw [key, key, h]

lemma rmrOf_eq_rmr_of_forall {σ : List (Ev N V Val)} {p : Fin N} (h : ∀ e ∈ σ, e.p = p) :
    A.rmrOf σ p = A.rmr σ := by
  simp only [rmrOf]; rw [List.filter_eq_self.2]; simpa using h

lemma rmrOf_eq_zero_of_forall {σ : List (Ev N V Val)} {p : Fin N} (h : ∀ e ∈ σ, e.p ≠ p) :
    A.rmrOf σ p = 0 := by
  simp only [rmrOf]; rw [List.filter_eq_nil_iff.2 (by simpa using h)]; rfl

lemma sum_rmrOf_le (τ : List (Ev N V Val)) (T : Finset (Fin N)) :
    ∑ p ∈ T, A.rmrOf τ p ≤ A.rmr τ := by
  induction τ using List.reverseRecOn with
  | nil => simp [rmrOf]
  | append_singleton τ e ih =>
    simp only [rmrOf_append, Finset.sum_add_distrib, rmr_append]
    refine Nat.add_le_add ih ?_
    calc ∑ p ∈ T, A.rmrOf [e] p ≤ ∑ p ∈ T ∪ {e.p}, A.rmrOf [e] p :=
          Finset.sum_le_sum_of_subset Finset.subset_union_left
      _ = A.rmrOf [e] e.p := by
          refine Finset.sum_eq_single e.p (fun q _ hq => ?_) (fun h => by simp at h)
          exact A.rmrOf_eq_zero_of_forall (by simpa [eq_comm] using hq)
      _ = A.rmr [e] := A.rmrOf_eq_rmr_of_forall (by simp)

lemma rmr_le_rmr_append_left (τ σ : List (Ev N V Val)) : A.rmr σ ≤ A.rmr (τ ++ σ) := by
  rw [rmr_append]; omega

/-- If `σ` has an RMR, it has a first one. -/
lemma exists_first_remote {σ : List (Ev N V Val)} (h : A.rmr σ ≠ 0) :
    ∃ σ₁ e σ₂, σ = σ₁ ++ e :: σ₂ ∧ A.rmr σ₁ = 0 ∧ e.remote A.home = true := by
  induction σ with
  | nil => simp at h
  | cons e σ ih =>
    by_cases he : e.remote A.home = true
    · exact ⟨[], e, σ, rfl, rfl, he⟩
    · have : A.rmr σ ≠ 0 := by
        rw [show e :: σ = [e] ++ σ from rfl, rmr_append, rmr_singleton] at h; simpa [he] using h
      obtain ⟨σ₁, e', σ₂, h1, h2, h3⟩ := ih this
      refine ⟨e :: σ₁, e', σ₂, by simp [h1], ?_, h3⟩
      rw [show e :: σ₁ = [e] ++ σ₁ from rfl, rmr_append, rmr_singleton, h2]; simp [he]

lemma rmr_eq_zero_iff {σ : List (Ev N V Val)} :
    A.rmr σ = 0 ↔ ∀ e ∈ σ, e.remote A.home = false := by
  simp [rmr, List.countP_eq_zero]

/-- A non-remote access of `p` is to a variable in `p`'s module. -/
lemma home_eq_of_not_remote {e : Ev N V Val} {v : V} (h : e.remote A.home = false)
    (hv : e.op.var = some v) : A.home v = e.p := by
  simpa [Ev.remote, Op.remoteFor, hv] using h

lemma remote_of_var {e : Ev N V Val} {v : V} (hv : e.op.var = some v) (h : A.home v ≠ e.p) :
    e.remote A.home = true := by
  simpa [Ev.remote, Op.remoteFor, hv] using h

lemma home_ne_of_remote {e : Ev N V Val} {v : V} (h : e.remote A.home = true)
    (hv : e.op.var = some v) : A.home v ≠ e.p := by
  simpa [Ev.remote, Op.remoteFor, hv] using h

end Algorithm

/-! ### Erasing processes (Lemma 6.7) -/

/-- Erase all steps of the processes in `E`. -/
def erase (E : Finset (Fin N)) (τ : List (Ev N V Val)) : List (Ev N V Val) :=
  τ.filter fun e => e.p ∉ E

@[simp] lemma erase_nil (E : Finset (Fin N)) : erase E ([] : List (Ev N V Val)) = [] := rfl

lemma erase_append (E : Finset (Fin N)) (τ σ : List (Ev N V Val)) :
    erase E (τ ++ σ) = erase E τ ++ erase E σ := by
  simp [erase, List.filter_append]

lemma erase_singleton (E : Finset (Fin N)) (e : Ev N V Val) :
    erase E [e] = if e.p ∈ E then [] else [e] := by
  by_cases h : e.p ∈ E <;> simp [erase, h]

lemma erase_erase (E F : Finset (Fin N)) (τ : List (Ev N V Val)) :
    erase E (erase F τ) = erase (E ∪ F) τ := by
  simp [erase, List.filter_filter, Finset.mem_union, not_or]

lemma erase_empty (τ : List (Ev N V Val)) : erase ∅ τ = τ := by
  simp [erase]

lemma erase_of_disjoint {E : Finset (Fin N)} {σ : List (Ev N V Val)} (h : ∀ e ∈ σ, e.p ∉ E) :
    erase E σ = σ := by
  simp only [erase]; rw [List.filter_eq_self]; simpa using h

lemma proj_erase (E : Finset (Fin N)) (τ : List (Ev N V Val)) (p : Fin N) :
    proj (erase E τ) p = if p ∈ E then [] else proj τ p := by
  induction τ with
  | nil => simp
  | cons e τ ih =>
    rw [show e :: τ = [e] ++ τ from rfl, erase_append, proj_append, proj_append, ih,
      erase_singleton]
    by_cases he : e.p ∈ E
    · by_cases hp : p ∈ E
      · simp [he, hp]
      · have : e.p ≠ p := fun h => hp (h ▸ he)
        simp [he, hp, proj_singleton, this]
    · by_cases hp : p ∈ E
      · have : e.p ≠ p := fun h => he (h ▸ hp)
        simp [he, hp, proj_singleton, this]
      · simp [he, hp]

lemma proj_erase_of_not_mem {E : Finset (Fin N)} (τ : List (Ev N V Val)) {p : Fin N}
    (hp : p ∉ E) : proj (erase E τ) p = proj τ p := by
  simp [proj_erase, hp]

lemma par_erase (E : Finset (Fin N)) (τ : List (Ev N V Val)) : par (erase E τ) = par τ \ E := by
  ext p; simp only [mem_par, erase, List.mem_filter, decide_eq_true_eq, Finset.mem_sdiff]
  constructor
  · rintro ⟨e, ⟨he, hE⟩, rfl⟩; exact ⟨⟨e, he, rfl⟩, hE⟩
  · rintro ⟨⟨e, he, rfl⟩, hE⟩; exact ⟨e, ⟨he, hE⟩, rfl⟩

lemma signals_erase_le (E : Finset (Fin N)) (τ : List (Ev N V Val)) :
    signals (erase E τ) ≤ signals τ := by
  simp only [signals, erase]
  exact (List.filter_sublist).countP_le

lemma mem_erase {E : Finset (Fin N)} {τ : List (Ev N V Val)} {e : Ev N V Val} :
    e ∈ erase E τ ↔ e ∈ τ ∧ e.p ∉ E := by
  simp [erase]

/-- Erasing processes that did not write `v` last does not change the last write to `v`. -/
lemma lastWrite_erase {E : Finset (Fin N)} {τ : List (Ev N V Val)} {v : V}
    (h : ∀ q, writer v τ = some q → q ∉ E) : lastWrite v (erase E τ) = lastWrite v τ := by
  induction τ using List.reverseRecOn with
  | nil => simp
  | append_singleton τ e ih =>
    rw [erase_append, erase_singleton, lastWrite_snoc]
    by_cases hw : e.Writes v
    · have hE : e.p ∉ E := h e.p (by rw [writer_snoc]; simp [hw])
      simp only [hE, ite_false, lastWrite_snoc]
      obtain ⟨x, hx⟩ := hw
      rcases e with ⟨p, op⟩; simp only at hx; subst hx
      simp [lwStep_of_write]
    · have h' : ∀ q, writer v τ = some q → q ∉ E := by
        intro q hq; apply h q; rw [writer_snoc]; simp [hw, hq]
      rw [lwStep_of_not_writes _ hw]
      split_ifs
      · simpa using ih h'
      · rw [lastWrite_snoc, lwStep_of_not_writes _ hw, ih h']

lemma writer_erase {E : Finset (Fin N)} {τ : List (Ev N V Val)} {v : V}
    (h : ∀ q, writer v τ = some q → q ∉ E) : writer v (erase E τ) = writer v τ := by
  simp [writer, lastWrite_erase h]

lemma Algorithm.memVal_erase (A : Algorithm N V Val S) {E : Finset (Fin N)}
    {τ : List (Ev N V Val)} {v : V} (h : ∀ q, writer v τ = some q → q ∉ E) :
    A.memVal (erase E τ) v = A.memVal τ v :=
  A.memVal_eq_of_lastWrite (lastWrite_erase h)

/-- Nobody outside `E` reads a value last written by a process of `E`. -/
def NoSeeOf (E : Finset (Fin N)) (τ : List (Ev N V Val)) : Prop :=
  Steps (fun ρ e => e.p ∉ E → ∀ v x, e.op = .read v x → ∀ q, writer v ρ = some q → q ∉ E) τ

namespace Algorithm

variable (A : Algorithm N V Val S)

/-- **Lemma 6.7** (erasing): if no process outside `E` sees a process of `E`, erasing `E` yields
an execution. -/
lemma valid_erase {E : Finset (Fin N)} {τ : List (Ev N V Val)} (hv : A.Valid τ)
    (hn : NoSeeOf E τ) : A.Valid (erase E τ) := by
  induction τ using List.reverseRecOn with
  | nil => simp
  | append_singleton τ e ih =>
    rw [valid_snoc] at hv
    unfold NoSeeOf at hn; rw [steps_snoc] at hn
    rw [erase_append, erase_singleton]
    split_ifs with he
    · simpa using ih hv.1 hn.1
    · rw [valid_snoc]
      refine ⟨ih hv.1 hn.1, ?_⟩
      refine A.stepOK_congr hv.2 (proj_erase_of_not_mem τ he) ?_
      intro v x hx
      exact A.memVal_erase (hn.2 he v x hx)

end Algorithm


/-! ### Status after a step -/

namespace Algorithm

variable (A : Algorithm N V Val S)

lemma lstep_ret_status {p : Fin N} {c c' : LState S} {b : Bool}
    (h : A.lstep p c (.ret b) = some c') : c'.2 = none := by
  rcases c with ⟨s, _ | o⟩
  · simp [lstep] at h
  · simp only [lstep] at h
    rcases hact : A.act p s with ⟨v, k⟩ | ⟨v, x, s'⟩ | ⟨b', s'⟩ <;> simp [hact] at h
    obtain ⟨-, rfl⟩ := h; rfl

lemma lstep_access_status {p : Fin N} {c c' : LState S} {op : Op V Val}
    (hop : op.isAccess = true) (h : A.lstep p c op = some c') : ∃ o, c'.2 = some o := by
  rcases c with ⟨s, _ | o⟩
  · cases op <;> simp_all [lstep, Op.isAccess]
  · refine ⟨o, ?_⟩
    simp only [lstep] at h
    rcases hact : A.act p s with ⟨v, k⟩ | ⟨v, x, s'⟩ | ⟨b', s'⟩ <;>
      cases op <;> simp_all [Op.isAccess] <;> (obtain ⟨-, rfl⟩ := h; rfl)

lemma idle_of_not_par {τ : List (Ev N V Val)} {q : Fin N} (h : q ∉ par τ) : A.Idle τ q := by
  refine ⟨A.locInit q, ?_⟩
  simp only [state]
  rw [proj_eq_nil_of_forall τ q (fun e he heq => h (mem_par.2 ⟨e, he, heq⟩))]
  rfl

lemma idle_of_proj_eq {τ τ' : List (Ev N V Val)} {q : Fin N} (h : A.Idle τ q)
    (hp : proj τ' q = proj τ q) : A.Idle τ' q := by
  obtain ⟨s, hs⟩ := h; exact ⟨s, by simp only [state] at hs ⊢; rw [hp]; exact hs⟩

lemma busy_of_proj_eq {τ τ' : List (Ev N V Val)} {q : Fin N} {o : Proc} (h : A.Busy τ q o)
    (hp : proj τ' q = proj τ q) : A.Busy τ' q o := by
  obtain ⟨s, hs⟩ := h; exact ⟨s, by simp only [state] at hs ⊢; rw [hp]; exact hs⟩

lemma idle_snoc_ret {ρ : List (Ev N V Val)} {p : Fin N} {b : Bool}
    (h : A.Valid (ρ ++ [⟨p, .ret b⟩])) : A.Idle (ρ ++ [⟨p, .ret b⟩]) p := by
  have hs := Valid.state_isSome A h p
  rw [Option.isSome_iff_exists] at hs
  obtain ⟨⟨s, st⟩, hc⟩ := hs
  refine ⟨s, ?_⟩
  have hc' := hc
  rw [show p = (⟨p, .ret b⟩ : Ev N V Val).p from rfl, state_snoc_self] at hc'
  cases h0 : A.state ρ p with
  | none => simp [h0] at hc'
  | some c =>
    simp only [h0, Option.bind_some] at hc'
    have := A.lstep_ret_status hc'
    simp only at this; subst this; exact hc

lemma busy_snoc_access {ρ : List (Ev N V Val)} {e : Ev N V Val}
    (h : A.Valid (ρ ++ [e])) (hop : e.op.isAccess = true) : ∃ o, A.Busy (ρ ++ [e]) e.p o := by
  have hs := Valid.state_isSome A h e.p
  rw [Option.isSome_iff_exists] at hs
  obtain ⟨⟨s, st⟩, hc⟩ := hs
  have hc' := hc
  rw [state_snoc_self] at hc'
  cases h0 : A.state ρ e.p with
  | none => simp [h0] at hc'
  | some c =>
    simp only [h0, Option.bind_some] at hc'
    obtain ⟨o, ho⟩ := A.lstep_access_status hop hc'
    simp only at ho; subst ho; exact ⟨o, s, hc⟩

lemma lstep_access_keep {p : Fin N} {s : S} {o : Proc} {c' : LState S} {op : Op V Val}
    (hop : op.isAccess = true) (h : A.lstep p (s, some o) op = some c') : c'.2 = some o := by
  simp only [lstep] at h
  rcases hact : A.act p s with ⟨v, k⟩ | ⟨v, x, s'⟩ | ⟨b', s'⟩ <;>
    cases op <;> simp_all [Op.isAccess] <;> (obtain ⟨-, rfl⟩ := h; rfl)

lemma stepOK_inv {ρ : List (Ev N V Val)} {p : Fin N} (h : A.Idle ρ p) (o : Proc) :
    A.StepOK ρ ⟨p, .inv o⟩ := by
  obtain ⟨s, hs⟩ := h
  refine ⟨?_, fun v x hx => by cases hx⟩
  simp only [state] at hs
  simp [lrun_snoc, hs, lstep]

lemma busy_snoc_inv {ρ : List (Ev N V Val)} {p : Fin N} {o : Proc}
    (h : A.Valid (ρ ++ [⟨p, .inv o⟩])) : A.Busy (ρ ++ [⟨p, .inv o⟩]) p o := by
  have hs := Valid.state_isSome A h p
  rw [Option.isSome_iff_exists] at hs
  obtain ⟨⟨s, st⟩, hc⟩ := hs
  refine ⟨s, ?_⟩
  have hc' := hc
  rw [show p = (⟨p, .inv o⟩ : Ev N V Val).p from rfl, state_snoc_self] at hc'
  cases h0 : A.state ρ p with
  | none => simp [h0] at hc'
  | some c =>
    rcases c with ⟨s₀, _ | o'⟩
    · simp only [h0, Option.bind_some, lstep, Option.some.injEq, Prod.mk.injEq] at hc'
      rw [hc]; rw [← hc'.2]
    · simp [h0, lstep] at hc'

lemma busy_append_access {ρ σ : List (Ev N V Val)} {p : Fin N} {o : Proc} (h : A.Busy ρ p o)
    (hv : A.Valid (ρ ++ σ)) (hσ : ∀ e ∈ σ, e.p = p ∧ e.op.isAccess = true) :
    A.Busy (ρ ++ σ) p o := by
  induction σ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton σ e ih =>
    rw [← List.append_assoc] at hv ⊢
    have ih' := ih (Valid.of_append A hv) (fun e' he' => hσ e' (by simp [he']))
    obtain ⟨hep, hacc⟩ := hσ e (by simp)
    obtain ⟨s₀, hs₀⟩ := ih'
    have hs := Valid.state_isSome A hv e.p
    rw [Option.isSome_iff_exists] at hs
    obtain ⟨⟨s, st⟩, hc⟩ := hs
    refine ⟨s, ?_⟩
    have hc' := hc
    rw [state_snoc_self, hep, hs₀, Option.bind_some] at hc'
    have := A.lstep_access_keep hacc hc'
    simp only at this; subst this; rw [← hep]; exact hc

lemma idle_or_busy {τ : List (Ev N V Val)} (h : A.Valid τ) (p : Fin N) :
    A.Idle τ p ∨ ∃ o, A.Busy τ p o := by
  have hs := Valid.state_isSome A h p
  rw [Option.isSome_iff_exists] at hs
  obtain ⟨⟨s, st⟩, hc⟩ := hs
  rcases st with _ | o
  · exact Or.inl ⟨s, hc⟩
  · exact Or.inr ⟨o, s, hc⟩

lemma countP_mem_remote_eq_sum (τ : List (Ev N V Val)) (T : Finset (Fin N)) :
    τ.countP (fun e => decide (e.p ∈ T) && e.remote A.home) = ∑ p ∈ T, A.rmrOf τ p := by
  induction τ using List.reverseRecOn with
  | nil => simp [rmrOf]
  | append_singleton τ e ih =>
    rw [List.countP_append, ih]
    simp only [rmrOf_append, Finset.sum_add_distrib]
    congr 1
    by_cases he : e.p ∈ T
    · rw [Finset.sum_eq_single e.p (fun q _ hq => A.rmrOf_eq_zero_of_forall
        (by simpa [eq_comm] using hq)) (fun h' => absurd he h'),
        A.rmrOf_eq_rmr_of_forall (by simp), rmr_singleton]
      simp [he]
    · rw [Finset.sum_eq_zero (fun q hq => A.rmrOf_eq_zero_of_forall
        (by intro e' he' heq; simp at he'; subst he'; exact he (heq ▸ hq)))]
      simp [he]

end Algorithm

end Podc.CCvsDSMSeparation
