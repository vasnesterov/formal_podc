import Papers.PODC2012.LeaderElectionSpaceLB.Model

/-!
# Group Election for the location-oblivious adversary (Figure 1, Lemma 2.2, Claim 3.1)

Deterministic parts of Section 2.2 and one counting claim of Section 3.2 of Giakkoupis–Woelfel,
*On the time and space complexity of randomized test-and-set* (PODC 2012) [GW12].

## Figure 1 (`GroupElect.alg`)

Shared registers `flag` and `R[1..ℓ+1]`, all initially `0` (`ℓ = ⌈log n⌉`; we allow any `ℓ ≥ 1`).
Method `elect()`:
1. if `flag.Read() = 1` return `False`;
2. `flag.Write(1)`;
3. choose `x ∈ {1, …, ℓ}` at random (`Pr(x = i) = 2^{-i}` for `i < ℓ`, `Pr(x = ℓ) = 2^{-(ℓ-1)}`);
4. `R[x].Write(1)`;
5. if `R[x+1].Read() = 0` return `True`;
6. return `False`.

We model it in the nondeterministic model of `Model.lean`: the coin flip of line 3 is a
nondeterministic choice (folded into the step of line 2); its distribution is irrelevant for the
deterministic properties proved here. Registers are `Option (Fin (ℓ + 1))`: `none` is `flag`,
`some j` is `R[j+1]`. A choice `x ∈ {1, …, ℓ}` is `j : Fin ℓ` with `x = j + 1`, so line 4 writes
`some j.castSucc` (= `R[x]`) and line 5 reads `some j.succ` (= `R[x+1]`).

## Results

* `GroupElect.steps_le_four` / `GroupElect.waitFree` / `GroupElect.soloTerminating` /
  `GroupElect.card_reg`: step complexity `O(1)` (at most 4 steps per process, wait-free) and
  space `ℓ + 2` registers (Lemma 2.2).
* `GroupElect.isGroupElection`: in every crash-free execution some process is elected
  (Lemma 2.2, "at least one process gets elected").
* `GroupElect.not_groupElectLiteral`: the definition of `GroupElect` in Section 2.1 *read
  literally* ("If some processes call `elect()`, then at least one process must get elected", no
  crash-freedom qualifier) fails for Figure 1 if processes may crash.
* `GroupElect.lemma_2_2_final_bound` (via `GroupElect.final_bound`, which gives `+ 4` for any
  `1 ≤ k ≤ 2^ℓ`): the last real-number estimate in the proof of Lemma 2.2 (`… ≤ 2 log k + 6`);
  the paper's justification "since `ℓ = ⌈log n⌉ ≤ log k`" must read `≥`.
* `GroupElect.claim_3_1`: the counting argument behind Claim 3.1 (elimination path).
-/

namespace Podc.LeaderElectionSpaceLB.GroupElect

open Podc.LeaderElectionSpaceLB

/-- Registers of Figure 1: `none` = `flag`, `some j` = `R[j+1]` (`j ≤ ℓ`). -/
abbrev Reg (ℓ : ℕ) := Option (Fin (ℓ + 1))

/-- Local states (program counter) of Figure 1. -/
inductive Loc (ℓ : ℕ) where
  /-- Before line 1: about to read `flag`. -/
  | start
  /-- Line 2: about to write `flag := 1`. -/
  | wflag
  /-- Line 4 with `x = j + 1` chosen in line 3: about to write `R[x] := 1`. -/
  | wR (j : Fin ℓ)
  /-- Line 5 with `x = j + 1`: about to read `R[x+1]`. -/
  | rR (j : Fin ℓ)
  /-- Returned `b` (`true` = elected). -/
  | ret (b : Bool)
  deriving DecidableEq

variable {ℓ : ℕ}

/-- Next action of each local state. -/
def act : Loc ℓ → Act (Reg ℓ) ℕ
  | .start => .read none
  | .wflag => .write none 1
  | .wR j => .write (some j.castSucc) 1
  | .rR j => .read (some j.succ)
  | .ret b => .done b

/-- Successor states after a read. -/
def readNext : Loc ℓ → ℕ → Set (Loc ℓ)
  | .start, v => if v = 1 then {.ret false} else {.wflag}
  | .rR _, v => if v = 0 then {.ret true} else {.ret false}
  | _, _ => ∅

/-- Successor states after a write; after line 2 the choice of line 3 is nondeterministic. -/
def writeNext : Loc ℓ → Set (Loc ℓ)
  | .wflag => Set.range .wR
  | .wR j => {.rR j}
  | _ => ∅

/-- **Figure 1 of [GW12]**: Group Election for the location-oblivious adversary, as a
nondeterministic algorithm (the random choice of line 3 is a nondeterministic choice). -/
def alg (P : Type*) (ℓ : ℕ) : Alg P (Reg ℓ) ℕ (Loc ℓ) where
  init _ := {.start}
  init_nonempty _ := ⟨.start, rfl⟩
  v₀ _ := 0
  act := act
  readNext := readNext
  writeNext := writeNext

variable {P : Type*} [DecidableEq P]

omit [DecidableEq P] in
@[simp] theorem alg_act : (alg P ℓ).act = act := rfl
omit [DecidableEq P] in
@[simp] theorem alg_readNext : (alg P ℓ).readNext = readNext := rfl
omit [DecidableEq P] in
@[simp] theorem alg_writeNext : (alg P ℓ).writeNext = writeNext := rfl

/-- **Group Election**, crash-free reading (Section 2.1 of [GW12]): for every set `S` of
processes that call `elect()` and every finite execution from an initial configuration in which
only processes of `S` take steps and all of them have returned, some process of `S` is elected. -/
def IsGroupElection {Reg V L : Type*} [DecidableEq Reg] (A : Alg P Reg V L) : Prop :=
  ∀ C₀ es, A.IsInit C₀ → A.Valid C₀ es → ∀ S : Set P, (∀ e ∈ es, e.1 ∈ S) → S.Nonempty →
    (∀ p ∈ S, A.Finished (A.run C₀ es) p) → ∃ p ∈ S, A.Won (A.run C₀ es) p

/-- **Group Election**, literal reading of Section 2.1 of [GW12] in the model with crashes
("If some processes call `elect()`, then at least one process must get elected"): a crashed
process takes no further steps, so a finite execution is a complete execution in which the
processes that have not returned crashed. Even under the weak requirement that some call has
returned, some process must have been elected. -/
def GroupElectLiteral {Reg V L : Type*} [DecidableEq Reg] (A : Alg P Reg V L) : Prop :=
  ∀ C₀ es, A.IsInit C₀ → A.Valid C₀ es → (∃ p, A.Finished (A.run C₀ es) p) →
    ∃ p, A.Won (A.run C₀ es) p

/-! ### Basic lemmas about steps of `alg` -/

section Basic

variable {Reg V L : Type*} [DecidableEq Reg]

theorem run_cons (A : Alg P Reg V L) (C : Config P Reg V L) (e : P × L) (es : List (P × L)) :
    A.run C (e :: es) = A.run (A.apply C e) es := rfl

theorem apply_loc (A : Alg P Reg V L) (C : Config P Reg V L) (e : P × L) :
    (A.apply C e).loc = Function.update C.loc e.1 e.2 := by
  unfold Alg.apply; split <;> rfl

theorem apply_val_of_read (A : Alg P Reg V L) (C : Config P Reg V L) (e : P × L) {r : Reg}
    (h : A.act (C.loc e.1) = .read r) : (A.apply C e).val = C.val := by
  unfold Alg.apply; rw [h]

theorem apply_val_of_write (A : Alg P Reg V L) (C : Config P Reg V L) (e : P × L) {r : Reg}
    {v : V} (h : A.act (C.loc e.1) = .write r v) :
    (A.apply C e).val = Function.update C.val r v := by
  unfold Alg.apply; rw [h]

/-- Processes that take no step keep their local state. -/
theorem run_loc_of_not_mem (A : Alg P Reg V L) (C : Config P Reg V L) (es : List (P × L))
    (p : P) (h : ∀ e ∈ es, e.1 ≠ p) : (A.run C es).loc p = C.loc p := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    rw [run_cons, ih _ (fun e' he' => h e' (List.mem_cons_of_mem _ he')), apply_loc,
      Function.update_of_ne (h e List.mem_cons_self).symm]

/-- An invariant preserved by every enabled step holds at the end of every execution. -/
theorem run_invariant (A : Alg P Reg V L) (I : Config P Reg V L → Prop)
    (hI : ∀ C e, I C → A.Enabled C e → I (A.apply C e)) :
    ∀ C es, A.Valid C es → I C → I (A.run C es) := by
  intro C es hv hC
  induction es generalizing C with
  | nil => exact hC
  | cons e es ih => exact ih _ hv.2 (hI C e hC hv.1)

end Basic

/-- Progress measure: the line a process is at. -/
def rank : Loc ℓ → ℕ
  | .start => 0
  | .wflag => 1
  | .wR _ => 2
  | .rR _ => 3
  | .ret _ => 4

theorem rank_le_four (l : Loc ℓ) : rank l ≤ 4 := by cases l <;> simp [rank]

omit [DecidableEq P] in
/-- Every step strictly increases the rank of the stepping process. -/
theorem rank_lt_of_enabled {C : Config P (Reg ℓ) ℕ (Loc ℓ)} {e : P × Loc ℓ}
    (h : (alg P ℓ).Enabled C e) : rank (C.loc e.1) < rank e.2 := by
  unfold Alg.Enabled at h
  generalize C.loc e.1 = s at h ⊢
  cases s with
  | start =>
    simp only [alg, act, readNext] at h
    split_ifs at h <;> simp_all [rank]
  | wflag =>
    simp only [alg, act, writeNext, Set.mem_range] at h
    obtain ⟨j, hj⟩ := h; simp [← hj, rank]
  | wR j => simp only [alg, act, writeNext, Set.mem_singleton_iff] at h; simp [h, rank]
  | rR j =>
    simp only [alg, act, readNext] at h
    split_ifs at h <;> simp_all [rank]
  | ret b => simp [alg, act] at h

/-- Steps of `p` in an execution, plus its initial rank, bound its final rank. -/
theorem countP_add_rank_le (C : Config P (Reg ℓ) ℕ (Loc ℓ)) (es : List (P × Loc ℓ))
    (hv : (alg P ℓ).Valid C es) (p : P) :
    es.countP (fun e => e.1 = p) + rank (C.loc p) ≤ rank (((alg P ℓ).run C es).loc p) := by
  induction es generalizing C with
  | nil => simp [Alg.run]
  | cons e es ih =>
    have h1 := ih _ hv.2
    have h2 := rank_lt_of_enabled hv.1
    rw [run_cons, List.countP_cons]
    rw [apply_loc] at h1
    by_cases hp : e.1 = p
    · subst hp
      simp only [Function.update_self, decide_true, ite_true] at h1 ⊢
      omega
    · simp only [Function.update_of_ne (Ne.symm hp), hp, decide_false] at h1 ⊢
      simpa using h1

/-- **Lemma 2.2 of [GW12]** (step complexity `O(1)`): in every execution of Figure 1 (from any
configuration, in particular from an initial one), every process takes at most 4 steps. -/
theorem steps_le_four (C₀ : Config P (Reg ℓ) ℕ (Loc ℓ)) (es : List (P × Loc ℓ))
    (hv : (alg P ℓ).Valid C₀ es) (p : P) :
    es.countP (fun e => e.1 = p) ≤ 4 := by
  have h := countP_add_rank_le C₀ es hv p
  have := rank_le_four (((alg P ℓ).run C₀ es).loc p)
  omega

omit [DecidableEq P] in
/-- **Lemma 2.2 of [GW12]** (wait-freedom): if `ℓ ≥ 1`, in every configuration a process that has
not returned has an enabled step. -/
theorem waitFree (hℓ : 1 ≤ ℓ) (C : Config P (Reg ℓ) ℕ (Loc ℓ)) (p : P)
    (hp : ¬ (alg P ℓ).Finished C p) : ∃ l', (alg P ℓ).Enabled C (p, l') := by
  rcases hs : C.loc p with _ | _ | j | j | b
  · by_cases hv : C.val none = 1
    · exact ⟨.ret false, by simp [Alg.Enabled, hs, act, readNext, hv]⟩
    · exact ⟨.wflag, by simp [Alg.Enabled, hs, act, readNext, hv]⟩
  · exact ⟨.wR ⟨0, hℓ⟩, by simp [Alg.Enabled, hs, act, writeNext]⟩
  · exact ⟨.rR j, by simp [Alg.Enabled, hs, act, writeNext]⟩
  · by_cases hv : C.val (some j.succ) = 0
    · exact ⟨.ret true, by simp [Alg.Enabled, hs, act, readNext, hv]⟩
    · exact ⟨.ret false, by simp [Alg.Enabled, hs, act, readNext, hv]⟩
  · exact absurd ⟨b, by simp [hs, act]⟩ hp

/-- **Lemma 2.2 of [GW12]** (wait-freedom with `O(1)` steps): if `ℓ ≥ 1`, from every
configuration every process has a solo execution of at most 4 steps after which it has
returned. -/
theorem solo_run (hℓ : 1 ≤ ℓ) (C : Config P (Reg ℓ) ℕ (Loc ℓ)) (p : P) :
    ∃ es : List (P × Loc ℓ), (∀ e ∈ es, e.1 = p) ∧ (alg P ℓ).Valid C es ∧
      (alg P ℓ).Finished ((alg P ℓ).run C es) p ∧ es.length + rank (C.loc p) ≤ 4 := by
  induction h : 4 - rank (C.loc p) using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases hf : (alg P ℓ).Finished C p
    · exact ⟨[], by simp, trivial, hf, by simpa using rank_le_four (C.loc p)⟩
    · obtain ⟨l', hl'⟩ := waitFree hℓ C p hf
      have hlt := rank_lt_of_enabled hl'
      have hloc : ((alg P ℓ).apply C (p, l')).loc p = l' := by simp [apply_loc]
      have h4 := rank_le_four l'
      obtain ⟨es, hes, hv, hfin, hlen⟩ :=
        ih (4 - rank l') (by simp only at hlt; omega) ((alg P ℓ).apply C (p, l'))
          (by rw [hloc])
      refine ⟨(p, l') :: es, ?_, ⟨hl', hv⟩, hfin, ?_⟩
      · simpa using hes
      · rw [hloc] at hlen; simp only [List.length_cons] at hlen ⊢; simp only at hlt; omega

/-- Figure 1 satisfies nondeterministic solo-termination (indeed it is wait-free). -/
theorem soloTerminating (hℓ : 1 ≤ ℓ) : (alg P ℓ).SoloTerminating := by
  intro C _ p
  obtain ⟨es, h1, h2, h3, -⟩ := solo_run hℓ C p
  exact ⟨es, h1, h2, h3⟩

/-- **Lemma 2.2 of [GW12]** (space complexity `O(log n)`): Figure 1 uses `ℓ + 2` registers
(`flag` and `R[1..ℓ+1]`). -/
theorem card_reg : Fintype.card (Reg ℓ) = ℓ + 2 := by simp

/-- Non-vacuity of `isGroupElection`: every single process has a complete solo execution from an
initial configuration. -/
theorem exists_finished_run (hℓ : 1 ≤ ℓ) (p : P) :
    ∃ C₀ es, (alg P ℓ).IsInit C₀ ∧ (alg P ℓ).Valid C₀ es ∧ (∀ e ∈ es, e.1 ∈ ({p} : Set P)) ∧
      (alg P ℓ).Finished ((alg P ℓ).run C₀ es) p := by
  let C₀ : Config P (Reg ℓ) ℕ (Loc ℓ) := ⟨fun _ => .start, fun _ => 0, fun _ => none⟩
  obtain ⟨es, h1, h2, h3, -⟩ := solo_run hℓ C₀ p
  exact ⟨C₀, es, ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, h2, fun e he => h1 e he, h3⟩

/-! ### At least one process gets elected -/

/-- Invariant behind "at least one process gets elected" (proof of Lemma 2.2): a process has
been elected, or a process at line 5 will read `0` because its `R[x+1]` lies above every written
register (the paper's `i*`), or a process is at line 4 and no `R` is written yet, or `flag` is
not written and every process is at line 1 or 2. -/
def Good (C : Config P (Reg ℓ) ℕ (Loc ℓ)) : Prop :=
  (∃ p, C.loc p = .ret true) ∨
  (∃ p j, C.loc p = .rR j ∧ ∀ i, C.val (some i) ≠ 0 → i ≤ j.castSucc) ∨
  (∃ p j, C.loc p = .wR j ∧ ∀ i, C.val (some i) = 0) ∨
  (C.val none = 0 ∧ (∀ p, C.loc p = .start ∨ C.loc p = .wflag) ∧ ∀ i, C.val (some i) = 0)

omit [DecidableEq P] in
/-- `Good` holds initially. -/
theorem good_init (C₀ : Config P (Reg ℓ) ℕ (Loc ℓ)) (h : (alg P ℓ).IsInit C₀) : Good C₀ := by
  obtain ⟨hl, hv, -⟩ := h
  refine Or.inr (Or.inr (Or.inr ⟨hv _, fun p => Or.inl (hl p), fun i => hv _⟩))

/-- `Good` is preserved by every step. -/
theorem good_step (C : Config P (Reg ℓ) ℕ (Loc ℓ)) (e : P × Loc ℓ) (hC : Good C)
    (he : (alg P ℓ).Enabled C e) : Good ((alg P ℓ).apply C e) := by
  obtain ⟨q, l'⟩ := e
  have hloc := apply_loc (alg P ℓ) C (q, l')
  unfold Alg.Enabled at he
  simp only at he hloc
  -- a witness `p` whose state differs from `q`'s keeps its state
  have keep : ∀ p, C.loc p ≠ C.loc q → ((alg P ℓ).apply C (q, l')).loc p = C.loc p := by
    intro p hp
    rw [hloc, Function.update_of_ne]
    rintro rfl; exact hp rfl
  generalize hs : C.loc q = s at he keep
  cases s with
  | start =>
    have hval : ((alg P ℓ).apply C (q, l')).val = C.val :=
      apply_val_of_read _ _ (q, l') (r := none) (by simp [hs, alg, act])
    simp only [alg, act, readNext] at he
    rcases hC with ⟨p, hp⟩ | ⟨p, j, hp, hj⟩ | ⟨p, j, hp, hj⟩ | ⟨h0, hall, hR⟩
    · exact Or.inl ⟨p, by rw [keep p (by simp [hp])]; exact hp⟩
    · exact Or.inr (Or.inl ⟨p, j, by rw [keep p (by simp [hp])]; exact hp, by rwa [hval]⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, j, by rw [keep p (by simp [hp])]; exact hp,
        by rwa [hval]⟩))
    · rw [h0] at he
      simp only [zero_ne_one, ite_false, Set.mem_singleton_iff] at he
      refine Or.inr (Or.inr (Or.inr ⟨by rw [hval, h0], fun p => ?_, by rwa [hval]⟩))
      rw [hloc]
      by_cases hpq : p = q
      · subst hpq; simp [he]
      · rw [Function.update_of_ne hpq]; exact hall p
  | wflag =>
    have hval : ((alg P ℓ).apply C (q, l')).val = Function.update C.val none 1 :=
      apply_val_of_write _ _ (q, l') (by simp [hs, alg, act])
    have hR : ∀ i, ((alg P ℓ).apply C (q, l')).val (some i) = C.val (some i) := by
      intro i; rw [hval, Function.update_of_ne (by simp)]
    simp only [alg, act, writeNext, Set.mem_range] at he
    obtain ⟨j, rfl⟩ := he
    rcases hC with ⟨p, hp⟩ | ⟨p, j', hp, hj⟩ | ⟨p, j', hp, hj⟩ | ⟨-, -, hR0⟩
    · exact Or.inl ⟨p, by rw [keep p (by simp [hp])]; exact hp⟩
    · exact Or.inr (Or.inl ⟨p, j', by rw [keep p (by simp [hp])]; exact hp,
        by simpa only [hR] using hj⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, j', by rw [keep p (by simp [hp])]; exact hp,
        by simpa only [hR] using hj⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨q, j, by simp [hloc], by simpa only [hR] using hR0⟩))
  | wR j =>
    have hval : ((alg P ℓ).apply C (q, l')).val = Function.update C.val (some j.castSucc) 1 :=
      apply_val_of_write _ _ (q, l') (by simp [hs, alg, act])
    simp only [alg, act, writeNext, Set.mem_singleton_iff] at he
    subst he
    have hq : ((alg P ℓ).apply C (q, .rR j)).loc q = .rR j := by simp [hloc]
    -- after the write, a nonzero `R` register is `R[x]` or was nonzero before
    have hnz : ∀ i, ((alg P ℓ).apply C (q, .rR j)).val (some i) ≠ 0 →
        i = j.castSucc ∨ C.val (some i) ≠ 0 := by
      intro i hi
      by_cases hij : i = j.castSucc
      · exact Or.inl hij
      · right; rwa [hval, Function.update_of_ne (by simpa using hij)] at hi
    rcases hC with ⟨p, hp⟩ | ⟨p, j', hp, hj⟩ | ⟨p, j', hp, hj⟩ | ⟨-, hall, -⟩
    · exact Or.inl ⟨p, by rw [keep p (by simp [hp])]; exact hp⟩
    · by_cases hjj : j ≤ j'
      · refine Or.inr (Or.inl ⟨p, j', by rw [keep p (by simp [hp])]; exact hp, fun i hi => ?_⟩)
        rcases hnz i hi with rfl | hi'
        · exact Fin.castSucc_le_castSucc_iff.mpr hjj
        · exact hj i hi'
      · refine Or.inr (Or.inl ⟨q, j, hq, fun i hi => ?_⟩)
        rcases hnz i hi with rfl | hi'
        · exact le_rfl
        · exact (hj i hi').trans (Fin.castSucc_le_castSucc_iff.mpr (le_of_not_ge hjj))
    · refine Or.inr (Or.inl ⟨q, j, hq, fun i hi => ?_⟩)
      rcases hnz i hi with rfl | hi'
      · exact le_rfl
      · exact absurd (hj i) hi'
    · rcases hall q with h | h <;> simp [hs] at h
  | rR j =>
    have hval : ((alg P ℓ).apply C (q, l')).val = C.val :=
      apply_val_of_read _ _ (q, l') (r := some j.succ) (by simp [hs, alg, act])
    simp only [alg, act, readNext] at he
    have hq : ((alg P ℓ).apply C (q, l')).loc q = l' := by simp [hloc]
    rcases hC with ⟨p, hp⟩ | ⟨p, j', hp, hj⟩ | ⟨p, j', hp, hj⟩ | ⟨-, hall, -⟩
    · exact Or.inl ⟨p, by rw [keep p (by simp [hp])]; exact hp⟩
    · by_cases hpq : p = q
      · subst hpq
        rw [hs] at hp; cases hp
        have h0 : C.val (some j.succ) = 0 := by
          by_contra hne
          have := hj _ hne
          rw [Fin.le_def] at this; simp at this
        rw [h0] at he; simp only [ite_true, Set.mem_singleton_iff] at he
        exact Or.inl ⟨p, by rw [hq, he]⟩
      · exact Or.inr (Or.inl ⟨p, j', by rw [hloc, Function.update_of_ne hpq]; exact hp,
          by rwa [hval]⟩)
    · rw [hj] at he; simp only [ite_true, Set.mem_singleton_iff] at he
      exact Or.inl ⟨q, by rw [hq, he]⟩
    · rcases hall q with h | h <;> simp [hs] at h
  | ret b => simp [alg, act] at he

/-- **Lemma 2.2 of [GW12]** ("at least one process gets elected"): Figure 1 is a Group Election
in the crash-free sense: in every execution from an initial configuration in which only the
(nonempty) set `S` of callers takes steps and all of them have returned, some process of `S`
returned `True`. -/
theorem isGroupElection : IsGroupElection (alg P ℓ) := by
  intro C₀ es hC₀ hv S hS hne hfin
  have hgood := run_invariant (alg P ℓ) Good (good_step) C₀ es hv (good_init C₀ hC₀)
  -- a process outside `S` is still at line 1
  have hout : ∀ p, p ∉ S → ((alg P ℓ).run C₀ es).loc p = .start := by
    intro p hp
    rw [run_loc_of_not_mem _ _ _ _ (fun e he h => hp (by rw [← h]; exact hS e he))]
    exact hC₀.1 p
  have hin : ∀ p, ((alg P ℓ).run C₀ es).loc p ≠ .start → p ∈ S := by
    intro p hp; by_contra h; exact hp (hout p h)
  have nfin : ∀ p, ((alg P ℓ).run C₀ es).loc p ≠ .start →
      ¬ (∀ b, ((alg P ℓ).run C₀ es).loc p ≠ .ret b) := by
    intro p hp hnr
    obtain ⟨b, hb⟩ := hfin p (hin p hp)
    revert hb hnr
    generalize ((alg P ℓ).run C₀ es).loc p = s
    cases s <;> simp [alg, act]
  rcases hgood with ⟨p, hp⟩ | ⟨p, j, hp, -⟩ | ⟨p, j, hp, -⟩ | ⟨-, hall, -⟩
  · exact ⟨p, hin p (by simp [hp]), by simp [Alg.Won, hp, act]⟩
  · exact absurd (fun b => by simp [hp]) (nfin p (by simp [hp]))
  · exact absurd (fun b => by simp [hp]) (nfin p (by simp [hp]))
  · obtain ⟨p, hpS⟩ := hne
    obtain ⟨b, hb⟩ := hfin p hpS
    rcases hall p with h | h <;> simp [h, act] at hb

/-- **Section 2.1 of [GW12], literal reading fails**: the sentence "If some processes call
`elect()`, then at least one process must get elected" in the definition of `GroupElect` (unlike
the definition of `LeaderElect`) has no "if no process crashes" qualifier, but Figure 1 does not
satisfy it when processes may crash. Execution: process `0` reads `flag = 0` (line 1), writes
`flag := 1` (line 2, choosing `x = 1`) and crashes; process `1` reads `flag = 1` and returns
`False`. Process `1` has returned and nobody is elected. -/
theorem not_groupElectLiteral : ¬ GroupElectLiteral (alg (Fin 2) 1) := by
  intro h
  let C₀ : Config (Fin 2) (Reg 1) ℕ (Loc 1) := ⟨fun _ => .start, fun _ => 0, fun _ => none⟩
  let es : List (Fin 2 × Loc 1) := [(0, .wflag), (0, .wR 0), (1, .ret false)]
  have hC₀ : (alg (Fin 2) 1).IsInit C₀ := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hv : (alg (Fin 2) 1).Valid C₀ es := by
    simp [es, C₀, Alg.Valid, Alg.Enabled, Alg.apply, alg, act, readNext, writeNext,
      Function.update]
  have hfin : (alg (Fin 2) 1).Finished ((alg (Fin 2) 1).run C₀ es) 1 :=
    ⟨false, by simp [es, C₀, Alg.run, Alg.apply, alg, act, Function.update]⟩
  obtain ⟨p, hp⟩ := h C₀ es hC₀ hv ⟨1, hfin⟩
  revert hp
  fin_cases p <;> simp [Alg.Won, es, C₀, Alg.run, Alg.apply, alg, act, Function.update]

/-! ### The final estimate in the proof of Lemma 2.2 -/

/-- One term of the sum: `1 - (1 - 2^{-(i+1)})^k ≤ min(1, k / 2^{i+1})`. -/
theorem term_le (k i : ℕ) :
    1 - (1 - 1 / (2 : ℝ) ^ (i + 1)) ^ k ≤ 1 ∧
      1 - (1 - 1 / (2 : ℝ) ^ (i + 1)) ^ k ≤ k / 2 ^ (i + 1) := by
  have hx0 : 0 ≤ 1 / (2 : ℝ) ^ (i + 1) := by positivity
  have hx1 : 1 / (2 : ℝ) ^ (i + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  constructor
  · have : 0 ≤ (1 - 1 / (2 : ℝ) ^ (i + 1)) ^ k := pow_nonneg (by linarith) k
    linarith
  · have hb := one_add_mul_le_pow (a := -(1 / (2 : ℝ) ^ (i + 1))) (by linarith) k
    rw [← sub_eq_add_neg] at hb
    have : (k : ℝ) / 2 ^ (i + 1) = k * (1 / 2 ^ (i + 1)) := by ring
    rw [this]; linarith

/-- Geometric tail: `∑_{m ≤ i < ℓ} k / 2^{i+1} ≤ k / 2^m`. -/
theorem geom_tail (k m ℓ : ℕ) :
    ∑ i ∈ Finset.Ico m ℓ, (k : ℝ) / 2 ^ (i + 1) ≤ k / 2 ^ m := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hg : ∑ i ∈ Finset.range (ℓ - m), (1 / (2 : ℝ)) ^ i ≤ 2 := sum_geometric_two_le _
  have : ∑ i ∈ Finset.range (ℓ - m), (k : ℝ) / 2 ^ (m + i + 1) =
      (k / 2 ^ m) * ((1 / 2) * ∑ i ∈ Finset.range (ℓ - m), (1 / (2 : ℝ)) ^ i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_add, pow_add, one_div_pow]; field_simp
  rw [this]
  have hk : 0 ≤ (k : ℝ) / 2 ^ m := by positivity
  nlinarith

/-- **Proof of Lemma 2.2 of [GW12], final estimate** (sharpened to `+ 4`): for `1 ≤ k ≤ 2^ℓ`,
`2 ∑_{1 ≤ i < ℓ} (1 - (1 - 2^{-(i+1)})^k) + k / 2^{ℓ-1} ≤ 2 log k + 4`. -/
theorem final_bound (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ 2 ^ ℓ) :
    2 * ∑ i ∈ Finset.Ico 1 ℓ, (1 - (1 - 1 / (2 : ℝ) ^ (i + 1)) ^ k) + k / (2 : ℝ) ^ (ℓ - 1)
      ≤ 2 * Real.logb 2 k + 4 := by
  set t : ℕ → ℝ := fun i => 1 - (1 - 1 / (2 : ℝ) ^ (i + 1)) ^ k with ht
  set m := Nat.log 2 k + 1 with hm
  have hk0 : k ≠ 0 := by omega
  have hpow : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hk0
  have hlt : k < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) k
  -- split the sum at `m`
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 ℓ) (· < m)]
  have h1 : ∑ i ∈ (Finset.Ico 1 ℓ).filter (· < m), t i ≤ Nat.log 2 k := by
    calc ∑ i ∈ (Finset.Ico 1 ℓ).filter (· < m), t i
        ≤ ∑ _i ∈ (Finset.Ico 1 ℓ).filter (· < m), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => (term_le k i).1
      _ = ((Finset.Ico 1 ℓ).filter (· < m)).card := by simp
      _ ≤ (Finset.Ico 1 m).card := by
          exact_mod_cast Finset.card_le_card fun i hi => by
            simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢; omega
      _ = Nat.log 2 k := by simp [hm]
  have h2 : ∑ i ∈ (Finset.Ico 1 ℓ).filter (fun i => ¬ i < m), t i ≤ 1 := by
    calc ∑ i ∈ (Finset.Ico 1 ℓ).filter (fun i => ¬ i < m), t i
        ≤ ∑ i ∈ (Finset.Ico 1 ℓ).filter (fun i => ¬ i < m), (k : ℝ) / 2 ^ (i + 1) :=
          Finset.sum_le_sum fun i _ => (term_le k i).2
      _ ≤ ∑ i ∈ Finset.Ico m ℓ, (k : ℝ) / 2 ^ (i + 1) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun _ _ _ => by positivity
          simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢; omega
      _ ≤ k / 2 ^ m := geom_tail k m ℓ
      _ ≤ 1 := by
          rw [div_le_one (by positivity)]; exact_mod_cast hlt.le
  have h3 : (k : ℝ) / 2 ^ (ℓ - 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ^ ℓ = 2 * 2 ^ (ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (k : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast hkℓ
    linarith
  have h4 : (Nat.log 2 k : ℝ) ≤ Real.logb 2 k := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
    exact_mod_cast hpow
  linarith

/-- **Lemma 2.2 of [GW12], last displayed estimate**: for `2 ≤ n`, `ℓ = ⌈log₂ n⌉` and
`1 ≤ k ≤ n`, `2 ∑_{1 ≤ i < ℓ} (1 - (1 - 2^{-(i+1)})^k) + k / 2^{ℓ-1} ≤ 2 log k + 6`. (The paper
justifies the last step by "since `ℓ = ⌈log n⌉ ≤ log k`"; what is used is `ℓ ≥ log k`.) -/
theorem lemma_2_2_final_bound (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    2 * ∑ i ∈ Finset.Ico 1 (Nat.clog 2 n), (1 - (1 - 1 / (2 : ℝ) ^ (i + 1)) ^ k) +
      k / (2 : ℝ) ^ (Nat.clog 2 n - 1) ≤ 2 * Real.logb 2 k + 6 := by
  have hℓ : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) hn)
  have hkℓ : k ≤ 2 ^ Nat.clog 2 n := hkn.trans (Nat.le_pow_clog (by norm_num) n)
  linarith [final_bound k (Nat.clog 2 n) hk hℓ hkℓ]

/-! ### Claim 3.1: the elimination path -/

/-- **Claim 3.1 of [GW12]** (abstract counting core): consider an elimination path of `ℓ`
deterministic splitters `SP_1, …, SP_ℓ`; let `c i` be the number of processes that call
`SP_{i+1}.split()` (so `c 0` processes enter the path and `c ℓ` processes fall off its right
end). A deterministic splitter sends at most `(#callers − 1)` callers to the right, none if it
has no caller (`c (i+1) ≤ c i - 1` in truncated subtraction). If at most `ℓ` processes enter the
path, then no process falls off the right end. This is only the counting argument; the
splitter semantics and the path are not modelled here. -/
theorem claim_3_1 (ℓ : ℕ) (c : ℕ → ℕ) (h0 : c 0 ≤ ℓ) (hstep : ∀ i < ℓ, c (i + 1) ≤ c i - 1) :
    c ℓ = 0 := by
  have : ∀ i ≤ ℓ, c i ≤ ℓ - i := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have := hstep i (by omega)
      have := ih (by omega)
      omega
  simpa using this ℓ le_rfl

end Podc.LeaderElectionSpaceLB.GroupElect
