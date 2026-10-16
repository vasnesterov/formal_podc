import Papers.PODC2025.TwoShotConsensusObjects.Defs

/-!
# Two-shot objects solving two-process consensus — the system model

Model (Section 3 of the paper), on top of CSLib's asynchronous shared-memory model
`Cslib.SharedMemory.Recoverable` used without crashes (`WFConsensus` = wait-free binary
consensus in the crash-stop model):

* two deterministic processes `0 = p₀` and `1 = p₁` (`Fin 2`), starting with binary inputs;
  a process outputs (decides) by entering an output state;
* asynchronous scheduling; executions are lists of events (we only use crash-free ones);
* shared objects: read/write objects `R j` (`j : ιR`, every operation read-only or a blind write,
  `IsRW`; registers are an instance) and copies `k : ιS` (finitely many) of the deterministic
  type `O` under study; initial states are chosen freely by the algorithm (`Alg.mem₀`), as in
  Jayanti's model used by the paper;
* **two-shot** (`TwoShot`): in every execution each process applies at most two operations to
  each copy of `O`;
* **process-allowance map** (`Allowed m`): process `p` only applies operations of `m p` to the
  copies of `O`;
* wait-free consensus: agreement, validity and wait-freedom (`WFConsensus`).

`Solvable O m` — the paper's "objects of type `(O, m)` solve two-shot two-process consensus".
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

/-- Read/write-like objects: every operation is read-only, or a blind write whose new value and
response do not depend on the current value (registers are an instance: `isRW_register`). -/
def IsRW (S : ObjSpec) : Prop :=
  ∀ o : S.Op, (∀ s, (S.δ s o).1 = s) ∨ (∀ s s', S.δ s o = S.δ s' o)

lemma isRW_register (V : Type) (v₀ : V) : IsRW (register V v₀) := by
  intro o
  cases o with
  | read => left; intro s; rfl
  | write v => right; intro s s'; rfl

/-- The objects of an algorithm: read/write objects `R j` (`j : ιR`) and copies of `O`
(indexed by `ιS`). -/
abbrev withRW {ιR ιS : Type} (R : ιR → ObjSpec) (O : ObjSpec) : ιR ⊕ ιS → ObjSpec :=
  Sum.elim R (fun _ => O)

section Counting

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

/-- The object process `p` is poised to access in `C` (`none` if `p` is in an output state). -/
def objOf (C : Cfg A) (p : Fin n) : Option ι :=
  match A.act (C.loc p) with
  | .access i _ _ => some i
  | .out _ => none

/-- Number of operations applied by process `p` to object `i` in the execution `α` from `C`. -/
def accCount : Cfg A → List (Ev n) → Fin n → ι → ℕ
  | _, [], _, _ => 0
  | C, e :: α, p, i =>
    (if e = .step p ∧ objOf C p = some i then 1 else 0) + accCount (C.next e) α p i

@[simp] lemma accCount_nil (C : Cfg A) (p : Fin n) (i : ι) : accCount C [] p i = 0 := rfl

lemma accCount_cons (C : Cfg A) (e : Ev n) (α : List (Ev n)) (p : Fin n) (i : ι) :
    accCount C (e :: α) p i =
      (if e = .step p ∧ objOf C p = some i then 1 else 0) + accCount (C.next e) α p i := rfl

lemma accCount_append (C : Cfg A) (α β : List (Ev n)) (p : Fin n) (i : ι) :
    accCount C (α ++ β) p i = accCount C α p i + accCount (run C α) β p i := by
  induction α generalizing C with
  | nil => simp
  | cons e α ih => simp only [List.cons_append, accCount_cons, ih, run_cons]; omega

end Counting

section System

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}

/-- **Two-shot**: in every (crash-free) execution from an initial configuration, each process
applies at most two operations to each copy of `O`. -/
def TwoShot (A : Alg 2 (withRW (ιS := ιS) R O)) : Prop :=
  ∀ x α, CrashFree α → ∀ p (k : ιS), accCount (initCfg A x) α p (.inr k) ≤ 2

/-- **Process-allowance map**: in every reachable configuration, a process poised on a copy of
`O` is poised to apply an operation allowed by `m`. -/
def Allowed (m : Fin 2 → Set O.Op) (A : Alg 2 (withRW (ιS := ιS) R O)) : Prop :=
  ∀ x α, CrashFree α → ∀ p (k : ιS) (o : O.Op) (κ : O.Resp → A.L),
    A.act ((run (initCfg A x) α).loc p) = .access (.inr k) o κ → o ∈ m p

end System

/-- **Objects of type `(O, m)` solve two-shot two-process consensus** (Section 3): there is a
wait-free binary consensus algorithm for two processes using read/write objects and finitely many
two-shot copies of `O` accessed according to `m`. -/
def Solvable (O : ObjSpec) (m : Fin 2 → Set O.Op) : Prop :=
  ∃ (ιR ιS : Type) (_ : DecidableEq ιR) (_ : DecidableEq ιS) (_ : Fintype ιS)
    (R : ιR → ObjSpec) (_ : ∀ j, IsRW (R j)) (A : Alg 2 (withRW (ιS := ιS) R O)),
    WFConsensus A ∧ TwoShot A ∧ Allowed m A

/-! ## Generic tools for algorithms -/

section Tools

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {A : Alg n T}

lemma pre_crashFree_iff (e : ℕ → Ev n) : (∀ t, CrashFree (pre e t)) ↔ ∀ t, ∀ p, e t ≠ .crash p := by
  constructor
  · intro h t p hp
    have := h (t + 1) p
    apply this
    simp only [pre, List.mem_map, List.mem_range]
    exact ⟨t, by omega, hp⟩
  · intro h t p hp
    simp only [pre, List.mem_map, List.mem_range] at hp
    obtain ⟨t', -, ht'⟩ := hp
    exact h t' p ht'

/-- Steps of other processes and crash-free steps do not change the local state of `p` except
by `p`'s own steps. -/
lemma next_loc_eq_of_ne (C : Cfg A) (e : Ev n) {p : Fin n} (h : e.proc ≠ p) :
    (C.next e).loc p = C.loc p := next_loc_other C e (Ne.symm h)

/-- **Wait-freedom from a ranking function**: if every step strictly decreases a rank of the
local state, every process taking infinitely many (crash-free) steps eventually outputs. -/
theorem prog_of_rank (rank : A.L → ℕ)
    (hrank : ∀ l i o (κ : (T i).Resp → A.L) r, A.act l = .access i o κ → rank (κ r) < rank l)
    (x : Fin n → Bool) (e : ℕ → Ev n) (p : Fin n) (N : ℕ) (hcf : ∀ t, CrashFree (pre e t))
    (hinf : ∀ M, ∃ t ≥ M, e t = .step p) :
    ∃ t ≥ N, ∃ v, (run (initCfg A x) (pre e t)).Out p v := by
  classical
  have hcf' := (pre_crashFree_iff e).1 hcf
  set Cf : ℕ → Cfg A := fun t => run (initCfg A x) (pre e t) with hCf
  have hsucc : ∀ t, Cf (t + 1) = (Cf t).next (e t) := by
    intro t; simp [hCf, pre_succ, run_concat]
  by_contra hno
  push Not at hno
  -- rank of `p` along the run
  set r : ℕ → ℕ := fun t => rank ((Cf t).loc p) with hr
  have hle : ∀ t ≥ N, r (t + 1) ≤ r t := by
    intro t ht
    simp only [hr, hsucc]
    rcases he : e t with q | q
    · by_cases hq : q = p
      · subst hq
        simp only [Cfg.next]
        rcases hact : A.act ((Cf t).loc q) with ⟨i, o, κ⟩ | v
        · rw [stepP_of_access _ hact]; simp; exact (hrank _ i o κ _ hact).le
        · exact absurd hact (hno t ht v)
      · rw [next_loc_eq_of_ne _ _ (by simpa using hq)]
    · exact absurd he (hcf' t q)
  have hlt : ∀ t ≥ N, e t = .step p → r (t + 1) < r t := by
    intro t ht he
    simp only [hr, hsucc, he, Cfg.next]
    rcases hact : A.act ((Cf t).loc p) with ⟨i, o, κ⟩ | v
    · rw [stepP_of_access _ hact]; simp; exact hrank _ i o κ _ hact
    · exact absurd hact (hno t ht v)
  have hmono : ∀ t ≥ N, ∀ d, r (t + d) ≤ r t := by
    intro t ht d
    induction d with
    | zero => simp
    | succ d ih => exact (hle (t + d) (by omega)).trans ih
  have key : ∀ j, ∃ t ≥ N, r t + j ≤ r N := by
    intro j
    induction j with
    | zero => exact ⟨N, le_rfl, by simp⟩
    | succ j ih =>
      obtain ⟨t, ht, hj⟩ := ih
      obtain ⟨t', ht', he⟩ := hinf t
      refine ⟨t' + 1, by omega, ?_⟩
      have h1 := hlt t' (by omega) he
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht'
      have h2 := hmono t ht d
      omega
  obtain ⟨t, -, ht⟩ := key (r N + 1)
  omega

end Tools

section ToolsSys

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

/-- **Two-shot from a budget**: a budget `bud l k` of remaining accesses to copy `k` that is at
most `2` initially, decreases by one at each access to `k` and never increases. -/
theorem twoShot_of_budget (bud : A.L → ιS → ℕ) (hinit : ∀ p b k, bud (A.init p b) k ≤ 2)
    (hstep : ∀ l i o (κ : ((withRW (ιS := ιS) R O) i).Resp → A.L) r k,
      A.act l = .access i o κ → bud (κ r) k + (if i = .inr k then 1 else 0) ≤ bud l k) :
    TwoShot A := by
  classical
  intro x α hα p k
  -- general statement from any configuration
  have gen : ∀ (α : List (Ev 2)) (C : Cfg A), CrashFree α →
      accCount C α p (.inr k) + bud ((run C α).loc p) k ≤ bud (C.loc p) k := by
    intro α
    induction α with
    | nil => intro C _; simp
    | cons e α ih =>
      intro C hcf
      have hcf' : CrashFree α := fun q hq => hcf q (by simp [hq])
      rw [accCount_cons, run_cons]
      have h1 := ih (C.next e) hcf'
      rcases e with q | q
      · by_cases hq : q = p
        · subst hq
          simp only [Cfg.next] at h1 ⊢
          rcases hact : A.act (C.loc q) with ⟨i, o, κ⟩ | v
          · rw [stepP_of_access _ hact] at h1 ⊢
            simp only [Function.update_self] at h1
            have h2 := hstep _ i o κ ((((withRW (ιS := ιS) R O) i).δ (C.mem i) o).2) k hact
            have hobj : objOf C q = some i := by simp [objOf, hact]
            simp only [hobj, Option.some.injEq, true_and]
            split_ifs at h2 ⊢ <;> simp_all <;> omega
          · rw [stepP_of_out C (show C.Out q v from hact)] at h1 ⊢
            have hobj : objOf C q = none := by simp [objOf, hact]
            simp [hobj]; omega
        · have hne : (Ev.step q : Ev 2) ≠ .step p := by simpa using hq
          rw [next_loc_eq_of_ne C _ (by simpa using hq)] at h1
          simp [hne]; omega
      · exact absurd (by simp) (hcf q)
  have := gen α (initCfg A x) hα
  have h0 := hinit p (x p) k
  have hl : (initCfg A x).loc p = A.init p (x p) := rfl
  rw [hl] at this
  omega

/-- **Allowance from an invariant of local states.** -/
theorem allowed_of_inv (m : Fin 2 → Set O.Op) (G : Fin 2 → A.L → Prop)
    (hinit : ∀ p b, G p (A.init p b))
    (hstep : ∀ p l i o (κ : ((withRW (ιS := ιS) R O) i).Resp → A.L) r,
      G p l → A.act l = .access i o κ → G p (κ r))
    (hok : ∀ p l (k : ιS) (o : O.Op) (κ : O.Resp → A.L), G p l →
      A.act l = .access (.inr k) o κ → o ∈ m p) : Allowed m A := by
  intro x α hα p k o κ hact
  refine hok p _ k o κ ?_ hact
  have gen : ∀ (α : List (Ev 2)) (C : Cfg A), CrashFree α → G p (C.loc p) →
      G p ((run C α).loc p) := by
    intro α
    induction α with
    | nil => intro C _ h; simpa using h
    | cons e α ih =>
      intro C hcf hG
      have hcf' : CrashFree α := fun q hq => hcf q (by simp [hq])
      rw [run_cons]
      apply ih _ hcf'
      rcases e with q | q
      · by_cases hq : q = p
        · subst hq
          simp only [Cfg.next]
          rcases hact : A.act (C.loc q) with ⟨i, o, κ⟩ | v
          · rw [stepP_of_access _ hact]; simp only [Function.update_self]
            exact hstep q _ i o κ _ hG hact
          · rwa [stepP_of_out C (show C.Out q v from hact)]
        · rwa [next_loc_eq_of_ne C _ (by simpa using hq)]
      · exact absurd (by simp) (hcf q)
  exact gen α _ hα (hinit p (x p))

end ToolsSys

end TwoShotCons
