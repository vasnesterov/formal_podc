import Papers.PODC2025.UniqueIDsBoundedRegisters.Alg

/-!
# Algorithms 1 and 2: step lemmas, ghost state and the basic invariant

* Step lemmas of `alg n d m` for each local state.
* Counting lemma for residues (`count_mod`, `count_residue_le`).
* A ghost state (`Gh`), updated deterministically along a run (`gstep`, `ghostOf`):
  `t` = number of FAIs applied to `R₀`, `U` = consumed tickets (successful `R₀` tickets whose
  holder already applied FAI to `R_{i+1}`), `tk p` = ticket of a process in state `got`,
  `cur p` = global index of the current invocation of `p`, `own s` = invocation that obtained
  the successful ticket `s`, `ninv` = number of invocations.
* The basic invariant `Inv1` (unconditional), in particular
  `#{s < t | s % d < n} ≤ invCount α` (each invocation obtains at most one successful ticket).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- Configurations of `alg`. -/
abbrev ACfg (P : Type) (n m : ℕ) [NeZero m] :=
  Config uidObj (fun _ : Fin (n + 1) => bReg m) P (St n)

section Steps

variable {n d m : ℕ} [NeZero m] {C C' : ACfg P n m} {p : P}

lemma alg_step_inv {o : Unit} (h : (alg (P := P) n d m).step C (.inv p o) = some C') :
    C.pend p = none ∧ C'.pend = Function.update C.pend p (some o) ∧
      C'.loc = Function.update C.loc p .start ∧ C'.mem = C.mem := by
  obtain ⟨h1, -, h2, h3, h4⟩ := Impl.step_inv h
  exact ⟨h1, h2, h3, h4⟩

lemma alg_step_tau_start (h : (alg (P := P) n d m).step C (.tau p) = some C')
    (hl : C.loc p = .start) :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧
      C'.mem = Function.update C.mem 0 (C.mem 0 + 1) ∧
      C'.loc = Function.update C.loc p
        (if h : (C.mem 0).val % d < n then .got ⟨(C.mem 0).val % d, h⟩ else .start) := by
  obtain ⟨h1, h2, i, o, k, hact, h3, h4⟩ := Impl.step_tau h
  simp only [alg, hl, Action.access.injEq] at hact
  obtain ⟨rfl, ho, hk⟩ := hact
  cases eq_of_heq ho
  cases eq_of_heq hk
  exact ⟨h1, h2, h3, h4⟩

lemma alg_step_tau_got {i : Fin n} (h : (alg (P := P) n d m).step C (.tau p) = some C')
    (hl : C.loc p = .got i) :
    C.pend p ≠ none ∧ C'.pend = C.pend ∧
      C'.mem = Function.update C.mem i.succ (C.mem i.succ + 1) ∧
      C'.loc = Function.update C.loc p (.done (i.val * m + (C.mem i.succ).val)) := by
  obtain ⟨h1, h2, i', o, k, hact, h3, h4⟩ := Impl.step_tau h
  simp only [alg, hl, Action.access.injEq] at hact
  obtain ⟨rfl, ho, hk⟩ := hact
  cases eq_of_heq ho
  cases eq_of_heq hk
  exact ⟨h1, h2, h3, h4⟩

lemma alg_step_tau_idle (h : (alg (P := P) n d m).step C (.tau p) = some C')
    (hl : C.loc p = .idle) : False := by
  obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
  simp [alg, hl] at hact

lemma alg_step_tau_done {v : ℕ} (h : (alg (P := P) n d m).step C (.tau p) = some C')
    (hl : C.loc p = .done v) : False := by
  obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h
  simp [alg, hl] at hact

lemma alg_step_ret {r : ℕ} (h : (alg (P := P) n d m).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
      (C.loc p = .done r ∨ (C.loc p = .idle ∧ r = 0)) ∧
      C'.loc = Function.update C.loc p .idle := by
  obtain ⟨h1, h2, h3, l, hact, h4⟩ := Impl.step_ret h
  refine ⟨h1, h2, h3, ?_⟩
  cases hl : C.loc p with
  | idle =>
    simp only [alg, hl, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact; exact ⟨Or.inr ⟨rfl, rfl⟩, h4⟩
  | start => simp [alg, hl] at hact
  | got i => simp [alg, hl] at hact
  | done v =>
    simp only [alg, hl, Action.ret.injEq] at hact
    obtain ⟨rfl, rfl⟩ := hact; exact ⟨Or.inl rfl, h4⟩

end Steps

/-! ### Counting residues -/

lemma count_mod (Q : ℕ → Prop) [DecidablePred Q] (d k r : ℕ) (hr : r ≤ d) :
    Nat.count (fun s => Q (s % d)) (d * k + r) = k * Nat.count Q d + Nat.count Q r := by
  have base : ∀ r ≤ d, Nat.count (fun s => Q (s % d)) r = Nat.count Q r := by
    intro r hr
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro x hx
    rw [Finset.mem_range] at hx
    rw [Nat.mod_eq_of_lt (by omega)]
  induction k with
  | zero => simpa using base r hr
  | succ k ih =>
    rw [show d * (k + 1) + r = d + (d * k + r) by ring, Nat.count_add, base d le_rfl]
    simp only [Nat.add_mod_left, ih]; ring

lemma count_eq_self (i r : ℕ) : Nat.count (fun s => s = i) r = if i < r then 1 else 0 := by
  rw [Nat.count_eq_card_filter_range]
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor <;> intro <;> omega
  · simp; omega

lemma count_lt_self (n r : ℕ) : Nat.count (fun s => s < n) r = min n r := by
  rw [Nat.count_eq_card_filter_range]
  have : (Finset.range r).filter (fun s => s < n) = Finset.range (min n r) := by
    ext x; simp; omega
  rw [this, Finset.card_range]

/-- Residue counting: if at most `n * m` of the first `t` naturals have residue `< n` modulo
`d ≥ n`, then each residue `i < n` occurs at most `m` times among them. -/
lemma count_residue_le {n d m t i : ℕ} (hnd : n ≤ d) (hi : i < n)
    (h : Nat.count (fun s => s % d < n) t ≤ n * m) :
    Nat.count (fun s => s % d = i) t ≤ m := by
  have hd : 0 < d := by omega
  have ht : t = d * (t / d) + t % d := (Nat.div_add_mod t d).symm
  have hr : t % d ≤ d := (Nat.mod_lt t hd).le
  rw [ht, count_mod (fun s => s < n) d _ _ hr, count_lt_self, count_lt_self,
    min_eq_left hnd] at h
  rw [ht, count_mod (fun s => s = i) d _ _ hr, count_eq_self, count_eq_self,
    ite_eq_left (by omega)]
  set k := t / d
  split_ifs with h2
  · have : min n (t % d) ≥ 1 := by omega
    by_contra hc
    have h3 : m ≤ k := by omega
    have h4 := Nat.mul_le_mul_right n h3
    rw [mul_comm m n] at h4
    omega
  · by_contra hc
    have h3 : m + 1 ≤ k := by omega
    have h4 := Nat.mul_le_mul_right n h3
    rw [add_mul, one_mul, mul_comm m n] at h4
    omega

/-- If at most `N` of the first `t` naturals have residue `< n` modulo `d` (`1 ≤ n ≤ d`), then
`t < d * (N + 1)`. -/
lemma lt_of_count_residue {n d N t : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (h : Nat.count (fun s => s % d < n) t ≤ N) : t < d * (N + 1) := by
  have hd : 0 < d := by omega
  have ht : t = d * (t / d) + t % d := (Nat.div_add_mod t d).symm
  have hr : t % d < d := Nat.mod_lt t hd
  rw [ht, count_mod (fun s => s < n) d _ _ hr.le, count_lt_self, count_lt_self,
    min_eq_left hnd] at h
  have h1 : t / d ≤ t / d * n := Nat.le_mul_of_pos_right _ (by omega)
  have : t / d ≤ N := by omega
  have := Nat.mul_le_mul_left d (Nat.succ_le_succ this)
  rw [ht]; nlinarith

/-! ### Ghost state -/

/-- Ghost state of the correctness proof. -/
structure Gh (P : Type) where
  /-- Number of FAIs applied to `R₀` so far (tickets `0, …, t - 1` have been handed out). -/
  t : ℕ
  /-- Consumed successful tickets (their holder already applied FAI to `R_{i+1}`). -/
  U : Finset ℕ
  /-- The ticket held by a process in state `got`. -/
  tk : P → ℕ
  /-- Global index of the current invocation of a process. -/
  cur : P → ℕ
  /-- The invocation that obtained a successful ticket. -/
  own : ℕ → ℕ
  /-- Number of invocations so far. -/
  ninv : ℕ

/-- Initial ghost state. -/
def Gh.init : Gh P := ⟨0, ∅, fun _ => 0, fun _ => 0, fun _ => 0, 0⟩

/-- Number of consumed tickets with residue `i` modulo `d` (= number of FAIs applied to
`R_{i+1}`). -/
def faiCnt (d : ℕ) (U : Finset ℕ) (i : ℕ) : ℕ := (U.filter (fun s => s % d = i)).card

/-- Ghost update along a step from configuration `C`. -/
def gstep {m : ℕ} [NeZero m] (n d : ℕ) (g : Gh P) (C : ACfg P n m) : Label P uidObj → Gh P
  | .inv p _ => { g with ninv := g.ninv + 1, cur := Function.update g.cur p g.ninv }
  | .ret _ _ => g
  | .tau p => match C.loc p with
    | .start =>
      if (C.mem 0).val % d < n then
        { g with t := g.t + 1, own := Function.update g.own g.t (g.cur p),
                 tk := Function.update g.tk p g.t }
      else { g with t := g.t + 1 }
    | .got _ => { g with U := insert (g.tk p) g.U }
    | _ => g

/-- One step of the run together with the ghost (total: invalid steps are ignored). -/
noncomputable def gfold (n d m : ℕ) [NeZero m] (x : ACfg P n m × Gh P) (ℓ : Label P uidObj) :
    ACfg P n m × Gh P :=
  match (alg (P := P) n d m).step x.1 ℓ with
  | some C' => (C', gstep n d x.2 x.1 ℓ)
  | none => x

/-- The ghost state after an execution. -/
noncomputable def ghostOf (n d m : ℕ) [NeZero m] (α : List (Label P uidObj)) : Gh P :=
  (α.foldl (gfold n d m) ((alg (P := P) n d m).initCfg, Gh.init)).2

section Run

variable {n d m : ℕ} [NeZero m]

lemma alg_run_append_singleton {α : List (Label P uidObj)} {ℓ : Label P uidObj}
    {C' : ACfg P n m} (h : (alg (P := P) n d m).run (α ++ [ℓ]) = some C') :
    ∃ C, (alg (P := P) n d m).run α = some C ∧ (alg (P := P) n d m).step C ℓ = some C' := by
  rw [Impl.run, Impl.runFrom_append] at h
  cases hα : (alg (P := P) n d m).runFrom (alg (P := P) n d m).initCfg α with
  | none => simp [hα] at h
  | some C =>
    simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
    exact ⟨C, hα, h⟩

lemma foldl_gfold_fst {α : List (Label P uidObj)} {C : ACfg P n m}
    (h : (alg (P := P) n d m).run α = some C) :
    (α.foldl (gfold n d m) ((alg (P := P) n d m).initCfg, Gh.init)).1 = C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simpa [Impl.run] using h
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := alg_run_append_singleton h
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, gfold, ih h₀, hs]

lemma ghostOf_append {α : List (Label P uidObj)} {ℓ : Label P uidObj} {C C' : ACfg P n m}
    (h : (alg (P := P) n d m).run α = some C) (hs : (alg (P := P) n d m).step C ℓ = some C') :
    ghostOf n d m (α ++ [ℓ]) = gstep n d (ghostOf n d m α) C ℓ := by
  have hX := foldl_gfold_fst h
  unfold ghostOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize List.foldl (gfold n d m) ((alg (P := P) n d m).initCfg, Gh.init) α = X at hX ⊢
  obtain ⟨C₀, g₀⟩ := X
  simp only at hX
  subst hX
  simp [gfold, hs]

end Run

/-! ### The basic invariant -/

/-- The basic invariant of `alg n d m` over (execution, configuration, ghost). -/
structure Inv1 (n d m : ℕ) [NeZero m] (α : List (Label P uidObj)) (C : ACfg P n m)
    (g : Gh P) : Prop where
  ninv : g.ninv = invCount α
  m0 : (C.mem 0).val = g.t % m
  mi : ∀ i : Fin n, (C.mem i.succ).val = faiCnt d g.U i % m
  pendIdle : ∀ p, C.pend p = none ↔ C.loc p = .idle
  Usub : ∀ s ∈ g.U, s < g.t
  got : ∀ p (i : Fin n), C.loc p = .got i → g.tk p < g.t ∧ g.tk p % d = i ∧ g.tk p ∉ g.U
  gotInj : ∀ p q (i j : Fin n), C.loc p = .got i → C.loc q = .got j → g.tk p = g.tk q → p = q
  ownLt : ∀ s < g.t, s % d < n → g.own s < g.ninv
  ownInj : ∀ s₁ < g.t, s₁ % d < n → ∀ s₂ < g.t, s₂ % d < n → g.own s₁ = g.own s₂ → s₁ = s₂
  start : ∀ p, C.loc p = .start → g.cur p < g.ninv ∧ ∀ s < g.t, s % d < n → g.own s ≠ g.cur p
  curInj : ∀ p q, C.loc p = .start → C.loc q = .start → g.cur p = g.cur q → p = q

lemma inv1_init (n d m : ℕ) [NeZero m] :
    Inv1 n d m [] (alg (P := P) n d m).initCfg Gh.init where
  ninv := rfl
  m0 := by simp [Impl.initCfg, alg, Gh.init]
  mi := by simp [Impl.initCfg, alg, Gh.init, faiCnt]
  pendIdle := by simp [Impl.initCfg, alg]
  Usub := by simp [Gh.init]
  got := by simp [Impl.initCfg, alg]
  gotInj := by simp [Impl.initCfg, alg]
  ownLt := by simp [Gh.init]
  ownInj := by simp [Gh.init]
  start := by simp [Impl.initCfg, alg]
  curInj := by simp [Impl.initCfg, alg]

/-- Successful tickets are obtained by distinct invocations. -/
lemma Inv1.count_le {n d m : ℕ} [NeZero m] {α : List (Label P uidObj)} {C : ACfg P n m}
    {g : Gh P} (hI : Inv1 n d m α C g) :
    Nat.count (fun s => s % d < n) g.t ≤ invCount α := by
  rw [Nat.count_eq_card_filter_range, ← hI.ninv]
  calc _ ≤ (Finset.range g.ninv).card := by
        apply Finset.card_le_card_of_injOn g.own
        · intro s hs
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hs
          simp only [Finset.coe_range, Set.mem_Iio]
          exact hI.ownLt s hs.1 hs.2
        · intro s₁ hs₁ s₂ hs₂ he
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hs₁ hs₂
          exact hI.ownInj s₁ hs₁.1 hs₁.2 s₂ hs₂.1 hs₂.2 he
    _ = g.ninv := Finset.card_range _

section Preservation

variable {n d m : ℕ} [NeZero m] {α : List (Label P uidObj)} {C C' : ACfg P n m} {g : Gh P}

lemma Inv1.step_inv (hI : Inv1 n d m α C g) {p : P} {o : Unit}
    (hs : (alg (P := P) n d m).step C (.inv p o) = some C') :
    Inv1 n d m (α ++ [.inv p o]) C' (gstep n d g C (.inv p o)) := by
  obtain ⟨-, hpend, hloc, hmem⟩ := alg_step_inv hs
  have hl : ∀ q, C'.loc q = if q = p then .start else C.loc q := by
    intro q; rw [hloc, Function.update_apply]
  have hp : ∀ q, C'.pend q = if q = p then some o else C.pend q := by
    intro q; rw [hpend, Function.update_apply]
  have hc : ∀ q, Function.update g.cur p g.ninv q = if q = p then g.ninv else g.cur q := by
    intro q; rw [Function.update_apply]
  simp only [gstep]
  constructor
  · simp [hI.ninv, Label.isInv]
  · rw [hmem]; exact hI.m0
  · rw [hmem]; exact hI.mi
  · intro q; rw [hl, hp]; split_ifs
    · simp
    · exact hI.pendIdle q
  · exact hI.Usub
  · intro q i h; rw [hl] at h; split_ifs at h; exact hI.got q i h
  · intro q q' i j h h'; rw [hl] at h h'; split_ifs at h h'; exact hI.gotInj q q' i j h h'
  · intro s hs hd; exact (hI.ownLt s hs hd).trans (Nat.lt_succ_self _)
  · exact hI.ownInj
  · intro q h; rw [hl] at h; dsimp only; rw [hc]
    split_ifs at h ⊢ with hq
    · exact ⟨Nat.lt_succ_self _, fun s hs hd => (hI.ownLt s hs hd).ne⟩
    · exact ⟨(hI.start q h).1.trans (Nat.lt_succ_self _), (hI.start q h).2⟩
  · intro q q' h h'; rw [hl] at h h'; dsimp only; rw [hc, hc]
    split_ifs at h h' ⊢ with hq hq'
    · intro _; simp [hq, hq']
    · intro he; exact absurd he.symm (hI.start q' h').1.ne
    · intro he; exact absurd he (hI.start q h).1.ne
    · exact hI.curInj q q' h h'

lemma Inv1.step_tau_start (hdm : d ∣ m) (hI : Inv1 n d m α C g) {p : P}
    (hs : (alg (P := P) n d m).step C (.tau p) = some C') (hlp : C.loc p = .start) :
    Inv1 n d m (α ++ [.tau p]) C' (gstep n d g C (.tau p)) := by
  obtain ⟨hpe, hpend, hmem, hloc⟩ := alg_step_tau_start hs hlp
  have hr : (C.mem 0).val % d = g.t % d := by rw [hI.m0, Nat.mod_mod_of_dvd _ hdm]
  have hninv : invCount (α ++ [.tau p]) = invCount α := by simp [Label.isInv]
  have hm0 : (C'.mem 0).val = (g.t + 1) % m := by
    rw [hmem, Function.update_self, Fin.val_add, hI.m0]
    simp [Nat.add_mod]
  have hmi : ∀ i : Fin n, C'.mem i.succ = C.mem i.succ := by
    intro i; rw [hmem, Function.update_of_ne (Fin.succ_ne_zero i)]
  simp only [gstep, hlp]
  by_cases hsucc : (C.mem 0).val % d < n
  · rw [dite_eq_left hsucc] at hloc; rw [ite_eq_left hsucc]
    have hl : ∀ q, C'.loc q = if q = p then .got ⟨_, hsucc⟩ else C.loc q := by
      intro q; rw [hloc, Function.update_apply]
    constructor
    · rw [hninv]; exact hI.ninv
    · exact hm0
    · intro i; rw [hmi]; exact hI.mi i
    · intro q; rw [hl, hpend]; split_ifs with hq
      · subst hq; simp [hpe]
      · exact hI.pendIdle q
    · intro s hs; exact (hI.Usub s hs).trans (Nat.lt_succ_self _)
    · intro q i h; rw [hl] at h; dsimp only
      split_ifs at h with hq
      · subst hq; cases h
        simp only [Function.update_self]
        exact ⟨Nat.lt_succ_self _, hr.symm, fun hU => lt_irrefl _ (hI.Usub _ hU)⟩
      · rw [Function.update_of_ne hq]
        obtain ⟨a, b, c⟩ := hI.got q i h
        exact ⟨a.trans (Nat.lt_succ_self _), b, c⟩
    · intro q q' i j h h'; rw [hl] at h h'; dsimp only
      by_cases hq : q = p <;> by_cases hq' : q' = p <;> simp only [hq, hq', ite_true, ite_false] at h h'
      · intro _; rw [hq, hq']
      · rw [hq, Function.update_self, Function.update_of_ne hq']
        intro he; exact absurd he (hI.got q' j h').1.ne'
      · rw [hq', Function.update_self, Function.update_of_ne hq]
        intro he; exact absurd he (hI.got q i h).1.ne
      · rw [Function.update_of_ne hq, Function.update_of_ne hq']
        exact hI.gotInj q q' i j h h'
    · intro s hs hd; dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · rw [Function.update_of_ne hs.ne]; exact hI.ownLt s hs hd
      · rw [Function.update_self]; exact (hI.start p hlp).1
    · intro s₁ hs₁ hd₁ s₂ hs₂ hd₂; dsimp only
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs₁ with hs₁ | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hs₂ with hs₂ | rfl
      · rw [Function.update_of_ne hs₁.ne, Function.update_of_ne hs₂.ne]
        exact hI.ownInj s₁ hs₁ hd₁ s₂ hs₂ hd₂
      · rw [Function.update_of_ne hs₁.ne, Function.update_self]
        intro he; exact absurd he ((hI.start p hlp).2 s₁ hs₁ hd₁)
      · rw [Function.update_of_ne hs₂.ne, Function.update_self]
        intro he; exact absurd he.symm ((hI.start p hlp).2 s₂ hs₂ hd₂)
      · intro _; rfl
    · intro q h; rw [hl] at h
      split_ifs at h with hq
      dsimp only
      refine ⟨(hI.start q h).1, fun s hs hd => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · rw [Function.update_of_ne hs.ne]; exact (hI.start q h).2 s hs hd
      · rw [Function.update_self]
        intro he; exact hq (hI.curInj q p h hlp he.symm)
    · intro q q' h h'; rw [hl] at h h'
      split_ifs at h h' with hq hq'
      exact hI.curInj q q' h h'
  · rw [dite_eq_right hsucc] at hloc; rw [ite_eq_right hsucc]
    have hl : C'.loc = C.loc := by
      rw [hloc]; funext q; by_cases hq : q = p
      · subst hq; simp [hlp]
      · rw [Function.update_of_ne hq]
    have hsucc' : ¬ g.t % d < n := by rwa [← hr]
    have hlt : ∀ s < g.t + 1, s % d < n → s < g.t := by
      intro s hs hd; rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact hs
      · exact absurd hd hsucc'
    constructor
    · rw [hninv]; exact hI.ninv
    · exact hm0
    · intro i; rw [hmi]; exact hI.mi i
    · intro q; rw [hl, hpend]; exact hI.pendIdle q
    · intro s hs; exact (hI.Usub s hs).trans (Nat.lt_succ_self _)
    · intro q i h; rw [hl] at h
      obtain ⟨a, b, c⟩ := hI.got q i h
      exact ⟨a.trans (Nat.lt_succ_self _), b, c⟩
    · intro q q' i j h h'; rw [hl] at h h'; exact hI.gotInj q q' i j h h'
    · intro s hs hd; exact hI.ownLt s (hlt s hs hd) hd
    · intro s₁ hs₁ hd₁ s₂ hs₂ hd₂
      exact hI.ownInj s₁ (hlt s₁ hs₁ hd₁) hd₁ s₂ (hlt s₂ hs₂ hd₂) hd₂
    · intro q h; rw [hl] at h
      exact ⟨(hI.start q h).1, fun s hs hd => (hI.start q h).2 s (hlt s hs hd) hd⟩
    · intro q q' h h'; rw [hl] at h h'; exact hI.curInj q q' h h'

lemma faiCnt_insert {d : ℕ} {U : Finset ℕ} {x : ℕ} (hx : x ∉ U) (j : ℕ) :
    faiCnt d (insert x U) j = faiCnt d U j + if x % d = j then 1 else 0 := by
  unfold faiCnt; rw [Finset.filter_insert]; split_ifs with h1
  · rw [Finset.card_insert_of_notMem (by simp [hx])]
  · simp

lemma Inv1.step_tau_got (hI : Inv1 n d m α C g) {p : P} {i : Fin n}
    (hs : (alg (P := P) n d m).step C (.tau p) = some C') (hlp : C.loc p = .got i) :
    Inv1 n d m (α ++ [.tau p]) C' (gstep n d g C (.tau p)) := by
  obtain ⟨hpe, hpend, hmem, hloc⟩ := alg_step_tau_got hs hlp
  obtain ⟨htk, htkd, htkU⟩ := hI.got p i hlp
  have hl : ∀ q, C'.loc q = if q = p then .done (i.val * m + (C.mem i.succ).val)
      else C.loc q := by
    intro q; rw [hloc, Function.update_apply]
  have hninv : invCount (α ++ [.tau p]) = invCount α := by simp [Label.isInv]
  simp only [gstep, hlp]
  constructor
  · rw [hninv]; exact hI.ninv
  · rw [hmem, Function.update_of_ne (Fin.succ_ne_zero i).symm]; exact hI.m0
  · intro j
    by_cases hj : j = i
    · subst hj
      rw [hmem, Function.update_self, Fin.val_add, hI.mi, faiCnt_insert htkU, ite_eq_left htkd]
      simp [Nat.add_mod]
    · rw [hmem, Function.update_of_ne (fun h => hj (Fin.succ_injective _ h)), hI.mi,
        faiCnt_insert htkU, ite_eq_right (fun h => hj (Fin.ext (h.symm.trans htkd)))]
      simp
  · intro q; rw [hl, hpend]; split_ifs with hq
    · subst hq; simp [hpe]
    · exact hI.pendIdle q
  · intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact htk
    · exact hI.Usub s hs
  · intro q j h; rw [hl] at h
    split_ifs at h with hq
    obtain ⟨a, b, c⟩ := hI.got q j h
    refine ⟨a, b, fun hU => ?_⟩
    rcases Finset.mem_insert.1 hU with he | hU
    · exact hq (hI.gotInj q p j i h hlp he)
    · exact c hU
  · intro q q' j j' h h'; rw [hl] at h h'
    split_ifs at h h'
    exact hI.gotInj q q' j j' h h'
  · exact hI.ownLt
  · exact hI.ownInj
  · intro q h; rw [hl] at h
    split_ifs at h
    exact hI.start q h
  · intro q q' h h'; rw [hl] at h h'
    split_ifs at h h'
    exact hI.curInj q q' h h'

lemma Inv1.step_ret (hI : Inv1 n d m α C g) {p : P} {r : ℕ}
    (hs : (alg (P := P) n d m).step C (.ret p r) = some C') :
    Inv1 n d m (α ++ [.ret p r]) C' (gstep n d g C (.ret p r)) := by
  obtain ⟨hpe, hpend, hmem, hlr, hloc⟩ := alg_step_ret hs
  have hl : ∀ q, C'.loc q = if q = p then .idle else C.loc q := by
    intro q; rw [hloc, Function.update_apply]
  have hp : ∀ q, C'.pend q = if q = p then none else C.pend q := by
    intro q; rw [hpend, Function.update_apply]
  have hninv : invCount (α ++ [.ret p r]) = invCount α := by simp [Label.isInv]
  simp only [gstep]
  constructor
  · rw [hninv]; exact hI.ninv
  · rw [hmem]; exact hI.m0
  · rw [hmem]; exact hI.mi
  · intro q; rw [hl, hp]; split_ifs
    · simp
    · exact hI.pendIdle q
  · exact hI.Usub
  · intro q i h; rw [hl] at h; split_ifs at h; exact hI.got q i h
  · intro q q' i j h h'; rw [hl] at h h'; split_ifs at h h'; exact hI.gotInj q q' i j h h'
  · exact hI.ownLt
  · exact hI.ownInj
  · intro q h; rw [hl] at h; split_ifs at h; exact hI.start q h
  · intro q q' h h'; rw [hl] at h h'; split_ifs at h h'; exact hI.curInj q q' h h'

lemma Inv1.step (hdm : d ∣ m) (hI : Inv1 n d m α C g) {ℓ : Label P uidObj}
    (hs : (alg (P := P) n d m).step C ℓ = some C') :
    Inv1 n d m (α ++ [ℓ]) C' (gstep n d g C ℓ) := by
  cases ℓ with
  | inv p o => exact hI.step_inv hs
  | ret p r => exact hI.step_ret hs
  | tau p =>
    cases hlp : C.loc p with
    | idle => exact (alg_step_tau_idle hs hlp).elim
    | start => exact hI.step_tau_start hdm hs hlp
    | got i => exact hI.step_tau_got hs hlp
    | done v => exact (alg_step_tau_done hs hlp).elim

end Preservation

/-- The basic invariant holds along every execution (with the ghost `ghostOf`). -/
theorem inv1_of_run {n d m : ℕ} [NeZero m] (hdm : d ∣ m) {α : List (Label P uidObj)}
    {C : ACfg P n m} (h : (alg (P := P) n d m).run α = some C) :
    Inv1 n d m α C (ghostOf n d m α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom_nil, Option.some.injEq] at h
    subst h; exact inv1_init n d m
  | append_singleton α ℓ ih =>
    obtain ⟨C₀, h₀, hs⟩ := alg_run_append_singleton h
    rw [ghostOf_append h₀ hs]
    exact (ih h₀).step hdm hs

end Cslib.SharedMemory.UniqueIDs
