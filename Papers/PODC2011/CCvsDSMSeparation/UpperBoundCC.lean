import Papers.PODC2011.CCvsDSMSeparation.Trace

/-!
# The upper bound for the CC model (Section 5)

* `Cached`, `ccCost`, `ccRMROf`, `ccRMR`: RMRs in the cache-coherent model, following the paper's
  "loose definition" (Section 2): a read of `v` by `p` is free if `p` read `v` before and no other
  process has written `v` since `p`'s last read of `v`; every other access counts as one RMR. This
  over-approximates the RMRs of an ideal cache, which is what an upper bound needs.
* `ccAlg`: the algorithm of Section 5 — one shared Boolean `B` (initially `false`); `Signal()`
  writes `B := true`, `Poll()` reads and returns `B`.
* `ccAlg_solves`, `ccAlg_soloTerminating`: it solves the signaling problem (Specification 4.1)
  and is terminating (even wait-free: every call takes two steps).
* `ccAlg_ccRMROf_le`, `ccAlg_ccRMR_le`: every process incurs at most 2 RMRs in the CC model in
  every execution with at most one call to `Signal()`; in total at most `2k` RMRs when `k`
  processes participate.

Together with `theorem_6_2` this is the separation: the same problem has `O(1)` (amortized and
worst-case) RMR complexity in the CC model, but not even `O(1)` amortized RMR complexity in the DSM
model. `ccAlg` also shows that the hypotheses of `theorem_6_2` are satisfiable.
-/

namespace Podc.CCvsDSMSeparation

variable {N : ℕ} {V Val S : Type*}

/-! ### RMRs in the CC model -/

/-- `p` holds a valid cached copy of `v` after `ρ`: it has read `v`, and no other process has
written `v` since. -/
def Cached (ρ : List (Ev N V Val)) (p : Fin N) (v : V) : Prop :=
  ∃ ρ₁ x ρ₂, ρ = ρ₁ ++ ⟨p, .read v x⟩ :: ρ₂ ∧ ∀ e ∈ ρ₂, e.p ≠ p → ¬ e.Writes v

open Classical in
/-- CC cost of step `e` after `ρ`: `1` for every access except a read of a cached variable. -/
noncomputable def ccCost (ρ : List (Ev N V Val)) (e : Ev N V Val) : ℕ :=
  if e.op.isAccess = true ∧ ¬ ∃ v x, e.op = .read v x ∧ Cached ρ e.p v then 1 else 0

open Classical in
/-- CC RMRs of `p` in the segment `σ` following `ρ`. -/
noncomputable def ccRMROfFrom (p : Fin N) : List (Ev N V Val) → List (Ev N V Val) → ℕ
  | _, [] => 0
  | ρ, e :: σ => (if e.p = p then ccCost ρ e else 0) + ccRMROfFrom p (ρ ++ [e]) σ

/-- CC RMRs of `p` in `τ`. -/
noncomputable def ccRMROf (τ : List (Ev N V Val)) (p : Fin N) : ℕ := ccRMROfFrom p [] τ

/-- CC RMRs in the segment `σ` following `ρ`. -/
noncomputable def ccRMRFrom : List (Ev N V Val) → List (Ev N V Val) → ℕ
  | _, [] => 0
  | ρ, e :: σ => ccCost ρ e + ccRMRFrom (ρ ++ [e]) σ

/-- Total CC RMRs in `τ`. -/
noncomputable def ccRMR (τ : List (Ev N V Val)) : ℕ := ccRMRFrom [] τ

lemma ccRMROfFrom_snoc (p : Fin N) (ρ σ : List (Ev N V Val)) (e : Ev N V Val) :
    ccRMROfFrom p ρ (σ ++ [e]) = ccRMROfFrom p ρ σ + if e.p = p then ccCost (ρ ++ σ) e else 0 := by
  induction σ generalizing ρ with
  | nil => simp [ccRMROfFrom]
  | cons e' σ ih => simp only [List.cons_append, ccRMROfFrom, ih]; simp [Nat.add_assoc]

lemma ccRMROf_snoc (τ : List (Ev N V Val)) (e : Ev N V Val) (p : Fin N) :
    ccRMROf (τ ++ [e]) p = ccRMROf τ p + if e.p = p then ccCost τ e else 0 := by
  simp [ccRMROf, ccRMROfFrom_snoc]

lemma ccRMRFrom_snoc (ρ σ : List (Ev N V Val)) (e : Ev N V Val) :
    ccRMRFrom ρ (σ ++ [e]) = ccRMRFrom ρ σ + ccCost (ρ ++ σ) e := by
  induction σ generalizing ρ with
  | nil => simp [ccRMRFrom]
  | cons e' σ ih => simp only [List.cons_append, ccRMRFrom, ih]; simp [Nat.add_assoc]

lemma ccRMR_snoc (τ : List (Ev N V Val)) (e : Ev N V Val) :
    ccRMR (τ ++ [e]) = ccRMR τ + ccCost τ e := by
  simp [ccRMR, ccRMRFrom_snoc]

lemma ccRMR_eq_sum (τ : List (Ev N V Val)) : ccRMR τ = ∑ p, ccRMROf τ p := by
  induction τ using List.reverseRecOn with
  | nil => simp [ccRMR, ccRMROf, ccRMRFrom, ccRMROfFrom]
  | append_singleton τ e ih =>
    simp only [ccRMR_snoc, ccRMROf_snoc, Finset.sum_add_distrib, ih]
    simp

lemma ccRMROf_eq_zero_of_not_par {τ : List (Ev N V Val)} {p : Fin N} (h : p ∉ par τ) :
    ccRMROf τ p = 0 := by
  induction τ using List.reverseRecOn with
  | nil => rfl
  | append_singleton τ e ih =>
    rw [ccRMROf_snoc, ih (fun h' => h (by rw [par_append]; exact Finset.mem_union_left _ h'))]
    have : e.p ≠ p := fun h' => h (by rw [par_append]; simp [par, h'])
    simp [this]

/-- A per-process bound gives an amortized bound. -/
lemma ccRMR_le_of_forall {τ : List (Ev N V Val)} {k : ℕ} (h : ∀ p, ccRMROf τ p ≤ k) :
    ccRMR τ ≤ k * (par τ).card := by
  classical
  rw [ccRMR_eq_sum, ← Finset.sum_subset (Finset.subset_univ (par τ))
    (fun p _ hp => ccRMROf_eq_zero_of_not_par hp)]
  calc ∑ p ∈ par τ, ccRMROf τ p ≤ ∑ p ∈ par τ, k := Finset.sum_le_sum fun p _ => h p
    _ = k * (par τ).card := by simp [mul_comm]

lemma cached_snoc (ρ : List (Ev N V Val)) (e : Ev N V Val) (p : Fin N) (v : V) :
    Cached (ρ ++ [e]) p v ↔
      (∃ x, e = ⟨p, .read v x⟩) ∨ (Cached ρ p v ∧ (e.p ≠ p → ¬ e.Writes v)) := by
  constructor
  · rintro ⟨ρ₁, x, ρ₂, h, hno⟩
    rcases ρ₂.eq_nil_or_concat with rfl | ⟨ρ₂', e', rfl⟩
    · left
      have := List.append_inj' h rfl
      exact ⟨x, by simpa using this.2⟩
    · right
      have h' : ρ ++ [e] = (ρ₁ ++ ⟨p, .read v x⟩ :: ρ₂') ++ [e'] := by rw [h]; simp
      obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      exact ⟨⟨ρ₁, x, ρ₂', h1, fun e'' he'' => hno e'' (by simp [he''])⟩,
        hno _ (by simp)⟩
  · rintro (⟨x, rfl⟩ | ⟨⟨ρ₁, x, ρ₂, h, hno⟩, he⟩)
    · exact ⟨ρ, x, [], by simp, by simp⟩
    · refine ⟨ρ₁, x, ρ₂ ++ [e], by simp [h], fun e' he' => ?_⟩
      rcases List.mem_append.1 he' with he' | he'
      · exact hno e' he'
      · simp at he'; subst he'; exact he

/-- Number of writes in `τ`. -/
def writes (τ : List (Ev N V Val)) : ℕ := τ.countP fun e => (e.op.written).isSome

open Classical in
lemma ccCost_of_not_access {τ : List (Ev N V Val)} {e : Ev N V Val}
    (h : e.op.isAccess = false) : ccCost τ e = 0 := by
  simp [ccCost, h]

open Classical in
lemma ccCost_write (τ : List (Ev N V Val)) (q : Fin N) (u : V) (x : Val) :
    ccCost τ ⟨q, .write u x⟩ = 1 := by
  simp [ccCost, Op.isAccess]

open Classical in
lemma ccCost_read (τ : List (Ev N V Val)) (q : Fin N) (u : V) (x : Val) :
    ccCost τ ⟨q, .read u x⟩ = if Cached τ q u then 0 else 1 := by
  by_cases h : Cached τ q u
  · have : ¬ (Op.isAccess (Op.read u x : Op V Val) = true ∧
        ¬ ∃ v' x', (Op.read u x : Op V Val) = .read v' x' ∧ Cached τ q v') := by
      push Not; intro _; exact ⟨u, x, rfl, h⟩
    rw [ccCost]; simp only [this, h]; simp
  · have : Op.isAccess (Op.read u x : Op V Val) = true ∧
        ¬ ∃ v' x', (Op.read u x : Op V Val) = .read v' x' ∧ Cached τ q v' := by
      refine ⟨rfl, ?_⟩
      rintro ⟨v', x', h', h''⟩; cases h'; exact h h''
    rw [ccCost]; simp only [this, h]; simp

lemma writes_snoc (τ : List (Ev N V Val)) (e : Ev N V Val) :
    writes (τ ++ [e]) = writes τ + if (e.op.written).isSome then 1 else 0 := by
  simp [writes, List.countP_append]

open Classical in
/-- **Misses of an ideal cache.** If all accesses are to one variable `v`, process `p` incurs at
most `1 + #writes` RMRs in the CC model. -/
lemma ccRMROf_add_le (p : Fin N) (v : V) (τ : List (Ev N V Val))
    (hv : ∀ e ∈ τ, ∀ u, e.op.var = some u → u = v) :
    ccRMROf τ p + (if Cached τ p v then 0 else 1) ≤ 1 + writes τ := by
  induction τ using List.reverseRecOn with
  | nil =>
    have : ¬ Cached ([] : List (Ev N V Val)) p v := by
      rintro ⟨ρ₁, x, ρ₂, h, -⟩; simp at h
    simp [ccRMROf, ccRMROfFrom, this]
  | append_singleton τ e ih =>
    have ih' := ih (fun e' he' => hv e' (by simp [he']))
    rw [ccRMROf_snoc, writes_snoc]
    rcases e with ⟨q, op⟩
    have hve := hv ⟨q, op⟩ (by simp)
    cases op with
    | inv o =>
      have hc : Cached (τ ++ [⟨q, .inv o⟩]) p v ↔ Cached τ p v := by
        rw [cached_snoc]; simp [Ev.Writes]
      rw [ccCost_of_not_access rfl]
      simp only [hc, Op.written, Option.isSome_none, Bool.false_eq_true, ite_false, ite_self]
      omega
    | ret b =>
      have hc : Cached (τ ++ [⟨q, .ret b⟩]) p v ↔ Cached τ p v := by
        rw [cached_snoc]; simp [Ev.Writes]
      rw [ccCost_of_not_access rfl]
      simp only [hc, Op.written, Option.isSome_none, Bool.false_eq_true, ite_false, ite_self]
      omega
    | read u x =>
      have hu : u = v := hve u rfl
      subst hu
      simp only [Op.written, Option.isSome_none, Bool.false_eq_true, ite_false]
      by_cases hq : q = p
      · subst hq
        have hc : Cached (τ ++ [⟨q, .read u x⟩]) q u := (cached_snoc _ _ _ _).2 (Or.inl ⟨x, rfl⟩)
        rw [ccCost_read]
        by_cases hc0 : Cached τ q u <;> simp only [hc, hc0, ite_true, ite_false] at ih' ⊢ <;> omega
      · have hc : Cached (τ ++ [⟨q, .read u x⟩]) p u ↔ Cached τ p u := by
          rw [cached_snoc]; simp [Ev.Writes, hq]
        simp only [hc, hq, ite_false]
        omega
    | write u x =>
      have hu : u = v := hve u rfl
      subst hu
      simp only [Op.written, Option.isSome_some, ite_true]
      by_cases hq : q = p
      · subst hq
        have hc : Cached (τ ++ [⟨q, .write u x⟩]) q u ↔ Cached τ q u := by
          rw [cached_snoc]; simp [Ev.Writes]
        rw [ccCost_write]
        by_cases hc0 : Cached τ q u <;> simp only [hc, hc0, ite_true, ite_false] at ih' ⊢ <;> omega
      · have hc : ¬ Cached (τ ++ [⟨q, .write u x⟩]) p u := by
          rw [cached_snoc]; simp [Ev.Writes, hq]
        simp only [hc, hq, ite_false]
        by_cases hc0 : Cached τ p u <;> simp only [hc0, ite_true, ite_false] at ih' <;> omega

/-! ### The algorithm of Section 5 -/

/-- Local states of the algorithm of Section 5. -/
inductive CCLoc
  | idle
  | pollRead
  | pollRet (b : Bool)
  | sigWrite
  | sigRet

/-- **Section 5**: one shared Boolean `B` (the only variable, `Unit`), initially `false`.
`Signal()` writes `B := true`; `Poll()` reads `B` and returns its value. (The memory module of `B`
is irrelevant in the CC model; we put it at process `0`.) -/
def ccAlg (N : ℕ) [NeZero N] : Algorithm N Unit Bool CCLoc where
  home := fun _ => 0
  memInit := fun _ => false
  locInit := fun _ => .idle
  invoke := fun _ _ o => match o with
    | .poll => .pollRead
    | .signal => .sigWrite
  act := fun _ s => match s with
    | .pollRead => .read () fun b => .pollRet b
    | .pollRet b => .ret b .idle
    | .sigWrite => .write () true .sigRet
    | .sigRet => .ret false .idle
    | .idle => .ret false .idle

variable {N : ℕ} [NeZero N]

/-- The reachable local states of `ccAlg`. -/
def CCGood : LState CCLoc → Prop
  | (.idle, none) => True
  | (.pollRead, some .poll) => True
  | (.pollRet _, some .poll) => True
  | (.sigWrite, some .signal) => True
  | (.sigRet, some .signal) => True
  | _ => False

/-- Number of writes by `q`. -/
def writesBy (τ : List (Ev N Unit Bool)) (q : Fin N) : ℕ :=
  τ.countP fun e => decide (e.p = q) && (e.op.written).isSome

/-- Number of invocations of `Signal()` by `q`. -/
def signalsBy (τ : List (Ev N Unit Bool)) (q : Fin N) : ℕ :=
  τ.countP fun e => decide (e.p = q) && e.op.isSigInv

open Classical in
/-- The invariant of `ccAlg`. -/
structure CCInv (τ : List (Ev N Unit Bool)) : Prop where
  good : ∀ q, ∃ c, (ccAlg N).state τ q = some c ∧ CCGood c
  wtrue : ∀ e ∈ τ, ∀ v x, e.op = .write v x → x = true
  sigRet : ∀ q o, (ccAlg N).state τ q = some (.sigRet, o) → (ccAlg N).memVal τ () = true
  memTrue : (ccAlg N).memVal τ () = true → ∃ e ∈ τ, e.op.isSigInv
  retTrue : ∀ q o, (ccAlg N).state τ q = some (.pollRet true, o) → ∃ e ∈ τ, e.op.isSigInv
  cnt : ∀ q, writesBy τ q + (if ∃ o, (ccAlg N).state τ q = some (.sigWrite, o) then 1 else 0) =
    signalsBy τ q

lemma ccInv_nil : CCInv ([] : List (Ev N Unit Bool)) := by
  refine ⟨fun q => ⟨(.idle, none), rfl, trivial⟩, by simp, ?_, ?_, ?_, ?_⟩
  · intro q o h; cases h
  · intro h; simp [Algorithm.memVal, ccAlg] at h
  · intro q o h; cases h
  · intro q; simp [writesBy, signalsBy, Algorithm.state, ccAlg]

lemma memVal_snoc_unit (τ : List (Ev N Unit Bool)) (e : Ev N Unit Bool) :
    (ccAlg N).memVal (τ ++ [e]) () =
      match e.op with
      | .write _ x => x
      | _ => (ccAlg N).memVal τ () := by
  rcases e with ⟨p, op⟩
  cases op with
  | write u x => cases u; exact (ccAlg N).memVal_snoc_write τ p () x
  | _ =>
    exact (ccAlg N).memVal_append_of_not_writes τ _ () (by simp [Ev.Writes])

lemma ccAlg_lstep {p : Fin N} {c c' : LState CCLoc} {op : Op Unit Bool} (hg : CCGood c)
    (h : (ccAlg N).lstep p c op = some c') :
    (c = (.idle, none) ∧ ∃ o, op = .inv o ∧ c' = ((ccAlg N).invoke p .idle o, some o)) ∨
    (c = (.pollRead, some .poll) ∧ ∃ x, op = .read () x ∧ c' = (.pollRet x, some .poll)) ∨
    (∃ b, c = (.pollRet b, some .poll) ∧ op = .ret b ∧ c' = (.idle, none)) ∨
    (c = (.sigWrite, some .signal) ∧ op = .write () true ∧ c' = (.sigRet, some .signal)) ∨
    (c = (.sigRet, some .signal) ∧ op = .ret false ∧ c' = (.idle, none)) := by
  rcases c with ⟨_ | _ | b | _ | _, _ | o⟩ <;> simp only [CCGood] at hg <;>
    (try cases o) <;>
    cases op <;> simp [Algorithm.lstep, ccAlg] at h <;> (try simp_all)
  all_goals (subst h; rfl)

omit [NeZero N] in
lemma writesBy_snoc (τ : List (Ev N Unit Bool)) (e : Ev N Unit Bool) (q : Fin N) :
    writesBy (τ ++ [e]) q = writesBy τ q + if e.p = q ∧ (e.op.written).isSome then 1 else 0 := by
  simp [writesBy, List.countP_append]

omit [NeZero N] in
lemma signalsBy_snoc (τ : List (Ev N Unit Bool)) (e : Ev N Unit Bool) (q : Fin N) :
    signalsBy (τ ++ [e]) q = signalsBy τ q + if e.p = q ∧ e.op.isSigInv then 1 else 0 := by
  simp [signalsBy, List.countP_append]

omit [NeZero N] in
lemma exists_sigInv_of_signalsBy {τ : List (Ev N Unit Bool)} {q : Fin N}
    (h : 0 < signalsBy τ q) : ∃ e ∈ τ, e.op.isSigInv := by
  obtain ⟨e, he, h'⟩ := List.countP_pos_iff.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact ⟨e, he, h'.2⟩

lemma ccInv_snoc {τ : List (Ev N Unit Bool)} {e : Ev N Unit Bool} (hI : CCInv τ)
    (hs : (ccAlg N).StepOK τ e) : CCInv (τ ++ [e]) := by
  classical
  obtain ⟨c, hc, hgood⟩ := hI.good e.p
  have hsome := hs.1
  rw [(ccAlg N).lrun_snoc] at hsome
  change (((ccAlg N).state τ e.p).bind fun c => (ccAlg N).lstep e.p c e.op).isSome at hsome
  rw [hc, Option.bind_some, Option.isSome_iff_exists] at hsome
  obtain ⟨c', hc'⟩ := hsome
  have hst : (ccAlg N).state (τ ++ [e]) e.p = some c' := by
    rw [(ccAlg N).state_snoc_self, hc, Option.bind_some, hc']
  have hother : ∀ q, e.p ≠ q → (ccAlg N).state (τ ++ [e]) q = (ccAlg N).state τ q :=
    fun q hq => (ccAlg N).state_snoc_ne τ e hq
  have hread := hs.2
  have htr := ccAlg_lstep hgood hc'
  have hmem := memVal_snoc_unit τ e
  rcases e with ⟨p, op⟩
  simp only at hst hother hc hread hmem htr
  have hsig_old : (ccAlg N).memVal τ () = true → ∃ e ∈ τ ++ [⟨p, op⟩], e.op.isSigInv := by
    intro h; obtain ⟨e, he, h'⟩ := hI.memTrue h; exact ⟨e, by simp [he], h'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- good
    intro q
    by_cases hq : p = q
    · subst hq; refine ⟨c', hst, ?_⟩
      rcases htr with ⟨-, o, -, rfl⟩ | ⟨-, x, -, rfl⟩ | ⟨b, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · cases o <;> trivial
      all_goals trivial
    · rw [hother q hq]; exact hI.good q
  · -- writes write `true`
    intro e he v x hx
    rcases List.mem_append.1 he with he | he
    · exact hI.wtrue e he v x hx
    · simp at he; subst he; simp only at hx; subst hx
      rcases htr with ⟨-, o, h, -⟩ | ⟨-, x', h, -⟩ | ⟨b, -, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
        cases h; rfl
  · -- a process that wrote has `B = true`
    intro q o hq
    by_cases hpq : p = q
    · subst hpq; rw [hst] at hq; cases hq
      rcases htr with ⟨-, o', -, h⟩ | ⟨-, x', -, h⟩ | ⟨b, -, -, h⟩ | ⟨-, hop, -⟩ | ⟨-, -, h⟩
      · cases o' <;> cases h
      · cases h
      · cases h
      · rw [hmem, hop]
      · cases h
    · rw [hother q hpq] at hq
      have := hI.sigRet q o hq
      rw [hmem]
      cases op with
      | write v x =>
        rcases htr with ⟨-, o', h', -⟩ | ⟨-, x', h', -⟩ | ⟨b, -, h', -⟩ | ⟨-, h', -⟩ | ⟨-, h', -⟩ <;>
          cases h'
        rfl
      | _ => exact this
  · -- `B = true` only after a signal
    intro h
    rw [hmem] at h
    cases op with
    | write v x =>
      rcases htr with ⟨-, o, h', -⟩ | ⟨-, x', h', -⟩ | ⟨b, -, h', -⟩ | ⟨hc0, -, -⟩ | ⟨-, h', -⟩ <;>
        (try cases h')
      have := hI.cnt p
      rw [hc0] at hc
      have h1 : ∃ o, (ccAlg N).state τ p = some (.sigWrite, o) := ⟨_, hc⟩
      simp only [h1, ite_true] at this
      obtain ⟨e, he, h'⟩ := exists_sigInv_of_signalsBy (τ := τ) (q := p) (by omega)
      exact ⟨e, by simp [he], h'⟩
    | _ => exact hsig_old h
  · -- a poll that read `true` follows a signal
    intro q o hq
    by_cases hpq : p = q
    · subst hpq; rw [hst] at hq; cases hq
      rcases htr with ⟨-, o', -, h⟩ | ⟨-, x', hop, h⟩ | ⟨b, -, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
      · cases o' <;> cases h
      · simp only [Prod.mk.injEq, CCLoc.pollRet.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have := hread () true (by rw [hop])
        exact hsig_old this.symm
      · cases h
      · cases h
      · cases h
    · rw [hother q hpq] at hq
      obtain ⟨e, he, h'⟩ := hI.retTrue q o hq
      exact ⟨e, by simp [he], h'⟩
  · -- counting writes against signals
    intro q
    rw [writesBy_snoc, signalsBy_snoc]
    by_cases hpq : p = q
    · subst hpq
      rw [hst]
      have h0 := hI.cnt p
      rw [hc] at h0
      rcases htr with ⟨hc0, o, hop, rfl⟩ | ⟨hc0, x, hop, rfl⟩ | ⟨b, hc0, hop, rfl⟩ |
          ⟨hc0, hop, rfl⟩ | ⟨hc0, hop, rfl⟩ <;> subst hc0 <;> subst hop
      · cases o <;> simp_all [Op.written, Op.isSigInv, ccAlg]
      all_goals simp_all [Op.written, Op.isSigInv]
    · rw [hother q hpq]
      have := hI.cnt q
      simp only [hpq, false_and, ite_false, Nat.add_zero]
      exact this

/-- Every execution of `ccAlg` satisfies the invariant. -/
lemma ccInv_of_valid {τ : List (Ev N Unit Bool)} (h : (ccAlg N).Valid τ) : CCInv τ := by
  induction τ using List.reverseRecOn with
  | nil => exact ccInv_nil
  | append_singleton τ e ih =>
    rw [Algorithm.valid_snoc] at h
    exact ccInv_snoc (ih h.1) h.2

/-! ### Correctness, termination and RMR complexity of `ccAlg` -/

lemma stepOK_of_state {τ : List (Ev N Unit Bool)} {p : Fin N} {c c' : LState CCLoc}
    {op : Op Unit Bool} (hc : (ccAlg N).state τ p = some c)
    (hl : (ccAlg N).lstep p c op = some c')
    (hr : ∀ v x, op = .read v x → x = (ccAlg N).memVal τ v) :
    (ccAlg N).StepOK τ ⟨p, op⟩ := by
  refine ⟨?_, hr⟩
  simp only
  rw [(ccAlg N).lrun_snoc]
  change (((ccAlg N).state τ p).bind fun c => (ccAlg N).lstep p c op).isSome
  rw [hc, Option.bind_some, hl]; rfl

lemma state_of_stepOK {τ : List (Ev N Unit Bool)} {p : Fin N} {op : Op Unit Bool}
    (hI : CCInv τ) (hs : (ccAlg N).StepOK τ ⟨p, op⟩) :
    ∃ c c', (ccAlg N).state τ p = some c ∧ CCGood c ∧ (ccAlg N).lstep p c op = some c' ∧
      (ccAlg N).state (τ ++ [⟨p, op⟩]) p = some c' := by
  obtain ⟨c, hc, hg⟩ := hI.good p
  have h1 := hs.1
  simp only at h1
  rw [(ccAlg N).lrun_snoc] at h1
  change (((ccAlg N).state τ p).bind fun c => (ccAlg N).lstep p c op).isSome at h1
  rw [hc, Option.bind_some, Option.isSome_iff_exists] at h1
  obtain ⟨c', hc'⟩ := h1
  refine ⟨c, c', hc, hg, hc', ?_⟩
  rw [show p = (⟨p, op⟩ : Ev N Unit Bool).p from rfl, (ccAlg N).state_snoc_self, hc,
    Option.bind_some, hc']

/-- `B` stays `true` once it is `true`. -/
lemma memVal_true_mono {ρ σ : List (Ev N Unit Bool)} (hv : (ccAlg N).Valid (ρ ++ σ))
    (h : (ccAlg N).memVal ρ () = true) : (ccAlg N).memVal (ρ ++ σ) () = true := by
  induction σ using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton σ e ih =>
    rw [← List.append_assoc] at hv ⊢
    have ih' := ih (Algorithm.Valid.of_append _ hv)
    rw [memVal_snoc_unit]
    rcases e with ⟨q, op⟩
    cases op with
    | write v x => exact (ccInv_of_valid hv).wtrue ⟨q, .write v x⟩ (by simp) v x rfl
    | _ => exact ih'

/-- **Section 5**: the algorithm solves the signaling problem (Specification 4.1). -/
theorem ccAlg_solves : (ccAlg N).Solves := by
  intro τ p b hv _ hbusy
  have hvτ := Algorithm.Valid.of_append _ hv
  have hI := ccInv_of_valid hvτ
  obtain ⟨c, c', hc, hg, hl, -⟩ := state_of_stepOK hI ((Algorithm.valid_snoc _ _ _).1 hv).2
  obtain ⟨s₀, hs₀⟩ := hbusy
  rw [hs₀] at hc; cases hc
  have hret : s₀ = .pollRet b := by
    rcases ccAlg_lstep hg hl with ⟨h, -⟩ | ⟨h, x, hop, -⟩ | ⟨b', h, hop, -⟩ | ⟨h, hop, -⟩ |
        ⟨h, hop, -⟩
    · cases h
    · cases hop
    · simp only [Prod.mk.injEq] at h; cases hop; exact h.1
    · cases h
    · cases h
  subst hret
  refine ⟨fun hb => hI.retTrue p _ (by rw [hs₀, hb]), fun hb => ?_⟩
  subst hb
  rintro ⟨τ₁, s, b', τ₂, τ₃, rfl, hbs, hτ₃⟩
  -- the signaler had written `B := true`
  have hv₁ : (ccAlg N).Valid (τ₁ ++ [⟨s, .ret b'⟩]) :=
    Algorithm.Valid.of_prefix _ hvτ ⟨τ₂ ++ ⟨p, .inv .poll⟩ :: τ₃, by simp⟩
  have hI₁ := ccInv_of_valid (Algorithm.Valid.of_append _ hv₁)
  obtain ⟨d, d', hd, hdg, hdl, -⟩ := state_of_stepOK hI₁ ((Algorithm.valid_snoc _ _ _).1 hv₁).2
  obtain ⟨t₀, ht₀⟩ := hbs
  rw [ht₀] at hd; cases hd
  have hsigRet : t₀ = .sigRet := by
    rcases ccAlg_lstep hdg hdl with ⟨h, -⟩ | ⟨h, x, hop, -⟩ | ⟨b'', h, hop, -⟩ | ⟨h, hop, -⟩ |
        ⟨h, hop, -⟩
    · cases h
    · cases h
    · cases h
    · cases hop
    · simp only [Prod.mk.injEq] at h; exact h.1
  subst hsigRet
  have hB₁ : (ccAlg N).memVal τ₁ () = true := hI₁.sigRet s _ ht₀
  set ρ := τ₁ ++ ⟨s, .ret b'⟩ :: τ₂ ++ [⟨p, .inv .poll⟩] with hρ
  have hvρ : (ccAlg N).Valid ρ := Algorithm.Valid.of_prefix _ hvτ ⟨τ₃, by simp [hρ]⟩
  have hBρ : (ccAlg N).memVal ρ () = true := by
    have := memVal_true_mono (ρ := τ₁) (σ := ⟨s, .ret b'⟩ :: τ₂ ++ [⟨p, .inv .poll⟩])
      (by simpa [hρ] using hvρ) hB₁
    simpa [hρ] using this
  have hpρ : (ccAlg N).state ρ p = some (.pollRead, some .poll) := by
    have hv' : (ccAlg N).Valid (τ₁ ++ ⟨s, .ret b'⟩ :: τ₂ ++ [⟨p, .inv .poll⟩]) := hvρ
    obtain ⟨e₁, e₂, he₁, heg, hel, hes⟩ := state_of_stepOK
      (ccInv_of_valid (Algorithm.Valid.of_append _ hv')) ((Algorithm.valid_snoc _ _ _).1 hv').2
    rw [hρ, hes]
    rcases ccAlg_lstep heg hel with ⟨-, o, hop, rfl⟩ | ⟨-, x, hop, -⟩ | ⟨b'', -, hop, -⟩ |
        ⟨-, hop, -⟩ | ⟨-, hop, -⟩ <;> cases hop
    rfl
  -- after its invocation `p` only reads `true`
  have key : ∀ σ, σ <+: τ₃ →
      ((ccAlg N).state (ρ ++ σ) p = some (.pollRead, some .poll) ∨
       (ccAlg N).state (ρ ++ σ) p = some (.pollRet true, some .poll) ∨
       (ccAlg N).state (ρ ++ σ) p = some (.idle, none)) := by
    intro σ hσ
    induction σ using List.reverseRecOn with
    | nil => left; simpa using hpρ
    | append_singleton σ e ih =>
      have hσ' : σ <+: τ₃ := (List.prefix_append σ [e]).trans hσ
      have hvσ : (ccAlg N).Valid (ρ ++ σ ++ [e]) := by
        refine Algorithm.Valid.of_prefix _ hvτ ?_
        obtain ⟨t, ht⟩ := hσ
        exact ⟨t, by rw [← ht]; simp [hρ]⟩
      have he : e ∈ τ₃ := hσ.subset (by simp)
      by_cases hep : e.p = p
      · rcases e with ⟨q, op⟩
        simp only at hep; subst hep
        obtain ⟨c₁, c₂, hc₁, hcg, hcl, hcs⟩ := state_of_stepOK
          (ccInv_of_valid (Algorithm.Valid.of_append _ hvσ)) ((Algorithm.valid_snoc _ _ _).1 hvσ).2
        rw [← List.append_assoc, hcs]
        have hninv := hτ₃ _ he rfl
        have hB : (ccAlg N).memVal (ρ ++ σ) () = true := memVal_true_mono
          (Algorithm.Valid.of_append _ hvσ) hBρ
        have hrd := ((Algorithm.valid_snoc _ _ _).1 hvσ).2.2
        rcases ih hσ' with h | h | h <;> rw [h] at hc₁ <;> cases hc₁ <;>
          rcases ccAlg_lstep hcg hcl with ⟨h1, o, hop, rfl⟩ | ⟨h1, x, hop, rfl⟩ |
            ⟨b'', h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩ <;>
          simp only [Prod.mk.injEq, reduceCtorEq, false_and, and_false, CCLoc.pollRet.injEq]
            at h1 <;> subst hop <;> simp_all [Op.isInv]
      · rw [← List.append_assoc, (ccAlg N).state_snoc_ne _ _ hep]; exact ih hσ'
  have hfin : ρ ++ τ₃ = τ₁ ++ ⟨s, .ret b'⟩ :: (τ₂ ++ ⟨p, .inv .poll⟩ :: τ₃) := by simp [hρ]
  rcases key τ₃ (List.prefix_refl _) with h | h | h <;> rw [hfin, hs₀] at h <;> simp at h

/-- **Section 5**: the algorithm is terminating (in fact wait-free). -/
theorem ccAlg_soloTerminating : (ccAlg N).SoloTerminating := by
  intro τ p o hv _ _ hbusy
  have hI := ccInv_of_valid hv
  obtain ⟨s₀, hs₀⟩ := hbusy
  obtain ⟨c, hc, hg⟩ := hI.good p
  rw [hs₀] at hc; cases hc
  rcases s₀ with _ | _ | b | _ | _ <;> (try cases o) <;> simp only [CCGood] at hg
  · -- pollRead
    set x := (ccAlg N).memVal τ ()
    refine ⟨[⟨p, .read () x⟩], x, by simp [Op.isAccess], ?_⟩
    have h1 : (ccAlg N).Valid (τ ++ [⟨p, .read () x⟩]) :=
      (Algorithm.valid_snoc _ _ _).2 ⟨hv, stepOK_of_state hs₀ (c' := (.pollRet x, some .poll))
        (by simp [Algorithm.lstep, ccAlg]) (by intro v y h; cases h; rfl)⟩
    refine (Algorithm.valid_snoc _ _ _).2 ⟨h1, stepOK_of_state (c := (.pollRet x, some .poll))
      (c' := (.idle, none)) ?_ (by simp [Algorithm.lstep, ccAlg]) (by intro v y h; cases h)⟩
    rw [show p = (⟨p, .read () x⟩ : Ev N Unit Bool).p from rfl, (ccAlg N).state_snoc_self, hs₀]
    simp [Algorithm.lstep, ccAlg]
  · -- pollRet b
    exact ⟨[], b, by simp, (Algorithm.valid_snoc _ _ _).2 ⟨by simpa using hv,
      stepOK_of_state (by simpa using hs₀) (c' := (.idle, none)) (by simp [Algorithm.lstep, ccAlg])
        (by intro v y h; cases h)⟩⟩
  · -- sigWrite
    refine ⟨[⟨p, .write () true⟩], false, by simp [Op.isAccess], ?_⟩
    have h1 : (ccAlg N).Valid (τ ++ [⟨p, .write () true⟩]) :=
      (Algorithm.valid_snoc _ _ _).2 ⟨hv, stepOK_of_state hs₀ (c' := (.sigRet, some .signal))
        (by simp [Algorithm.lstep, ccAlg]) (by intro v y h; cases h)⟩
    refine (Algorithm.valid_snoc _ _ _).2 ⟨h1, stepOK_of_state (c := (.sigRet, some .signal))
      (c' := (.idle, none)) ?_ (by simp [Algorithm.lstep, ccAlg]) (by intro v y h; cases h)⟩
    rw [show p = (⟨p, .write () true⟩ : Ev N Unit Bool).p from rfl,
      (ccAlg N).state_snoc_self, hs₀]
    simp [Algorithm.lstep, ccAlg]
  · -- sigRet
    exact ⟨[], false, by simp, (Algorithm.valid_snoc _ _ _).2 ⟨by simpa using hv,
      stepOK_of_state (by simpa using hs₀) (c' := (.idle, none)) (by simp [Algorithm.lstep, ccAlg])
        (by intro v y h; cases h)⟩⟩

omit [NeZero N] in
lemma countP_eq_sum (τ : List (Ev N Unit Bool)) (f : Ev N Unit Bool → Bool) :
    τ.countP f = ∑ q, τ.countP (fun e => decide (e.p = q) && f e) := by
  induction τ using List.reverseRecOn with
  | nil => simp
  | append_singleton τ e ih =>
    simp only [List.countP_append, Finset.sum_add_distrib, ← ih]
    congr 1
    by_cases he : f e = true <;> simp [he, List.countP_cons]

lemma writes_le_signals {τ : List (Ev N Unit Bool)} (hv : (ccAlg N).Valid τ) :
    writes τ ≤ signals τ := by
  classical
  have hI := ccInv_of_valid hv
  rw [writes, signals, countP_eq_sum τ, countP_eq_sum τ]
  refine Finset.sum_le_sum fun q _ => ?_
  have := hI.cnt q
  simp only [writesBy, signalsBy] at this
  split_ifs at this <;> omega

/-- **Section 5**: in the CC model each process incurs at most 2 RMRs, in every execution with at
most one call to `Signal()`. -/
theorem ccAlg_ccRMROf_le {τ : List (Ev N Unit Bool)} (hv : (ccAlg N).Valid τ)
    (hs : signals τ ≤ 1) (p : Fin N) : ccRMROf τ p ≤ 2 := by
  have h1 := ccRMROf_add_le p () τ (fun _ _ u _ => rfl)
  have h2 := writes_le_signals hv
  split_ifs at h1 <;> omega

/-- **Section 5**: hence `O(1)` amortized RMR complexity in the CC model: at most `2k` RMRs when
`k` processes participate. -/
theorem ccAlg_ccRMR_le {τ : List (Ev N Unit Bool)} (hv : (ccAlg N).Valid τ)
    (hs : signals τ ≤ 1) : ccRMR τ ≤ 2 * (par τ).card :=
  ccRMR_le_of_forall (ccAlg_ccRMROf_le hv hs)

end Podc.CCvsDSMSeparation
