import Papers.PODC2013.MessageAdversariesVsFD.Async
import Papers.PODC2015.WeakestFDEventualConsistency.RunTools

/-!
# Theorem 1, asynchronous side: `AMP_{n,n-1}[fd : ∅]` solves exactly the local tasks

Raynal–Stainer (PODC 2013), Theorem 1 states that `SMP_n[adv : ∞]` and `AMP_{n,n-1}[fd : ∅]`
solve the same tasks. Both sides are characterized by locality (`Task.IsLocal`: every process can
compute its output from its own input). This file proves the asynchronous side,
`amp_solvable_iff_local`.

* `←`: every process outputs `f i (x i)` at each of its steps.
* `→` (the paper's argument "a process cannot distinguish a run where the others crashed
  initially from one where their messages are delayed", made precise): we use explicit
  schedules where process `i` steps at the global times `slot i u = n * u + idx i`. At its odd
  local times `2a + 1` it receives its own message sent at its local time `a`; at local times
  `4v` it takes a time-out; in the failure-free run with parameter `N` it receives at local time
  `4(s + N) + 2` the message of another process sent at global time `s`.
  - `soloRun x i`: all processes but `i` crash at time `0`. By solvability, `i` outputs; by
    indistinguishability (`sim2`), its output only depends on `x i`; this defines `f`.
  - `mergedRun x N`: failure-free; up to time `N` every process `i` behaves exactly as in its solo
    run (messages of other processes are only received after time `N`). With `N` beyond all solo
    decision times, every process outputs its solo value, and validity of this run gives an
    output vector `O ∈ Δ x` with `O i = f i (x i)`.
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.FailureDetectors
open Podc.WeakestFDEventualConsistency (policyRun policyCfg cfg_policyRun σ_policyRun
  event_recv_eq msg_succ_self_of_ne)

namespace AsyncLocal

/-! ### Local indistinguishability for two algorithms with the same code at `p` -/

section Sim

variable {P R M I O S : Type} [DecidableEq P]

-- Model candidate (generalizes `Podc.WeakestFDEventualConsistency.sim`)
/-- **Local indistinguishability** for two algorithms with the same transition function and the
same initial state at `p`: if `p` takes the same steps in two runs before `T` as long as it has
broadcast the same messages, sees the same failure-detector values and receives only its own
messages, then its states and broadcasts coincide up to `T`. -/
lemma sim2 (A₁ A₂ : Algorithm P R M I O S) (hstep : A₁.step = A₂.step) (p : P)
    (hinit : A₁.init p = A₂.init p) (r₁ r₂ : Run P R I) (T : ℕ)
    (hσ : ∀ t < T, (∀ s m, (A₁.cfg r₁ t).msg s = some (p, m) ↔ (A₂.cfg r₂ t).msg s = some (p, m)) →
      ∀ c, r₁.σ t = some (p, c) ↔ r₂.σ t = some (p, c))
    (hH : ∀ t < T, r₁.H p t = r₂.H p t)
    (hrecv : ∀ t < T, ∀ q s, r₁.σ t = some (p, .recv q s) → q = p) :
    ∀ t ≤ T, A₁.st r₁ p t = A₂.st r₂ p t ∧
      ∀ s m, (A₁.cfg r₁ t).msg s = some (p, m) ↔ (A₂.cfg r₂ t).msg s = some (p, m) := by
  intro t ht
  induction t with
  | zero => exact ⟨hinit, fun s m => by simp [Algorithm.initCfg]⟩
  | succ t ih =>
    obtain ⟨hst, hmsg⟩ := ih (by omega)
    have htT : t < T := by omega
    have hσt := hσ t htT hmsg
    by_cases hstep' : ∃ c, r₁.σ t = some (p, c)
    · obtain ⟨c, hc₁⟩ := hstep'
      have hc₂ := (hσt c).1 hc₁
      have hev : (A₁.cfg r₁ t).event c = (A₂.cfg r₂ t).event c := by
        cases c with
        | recv q s =>
          obtain rfl := hrecv t htT q s hc₁
          exact event_recv_eq (hmsg s)
        | tick => rfl
        | input i => rfl
      rcases he : (A₁.cfg r₁ t).event c with _ | e
      · have he₂ : (A₂.cfg r₂ t).event c = none := hev ▸ he
        obtain ⟨h₁, -⟩ := Algorithm.cfg_succ_of_event_none r₁ t p c hc₁ he
        obtain ⟨h₂, -⟩ := Algorithm.cfg_succ_of_event_none r₂ t p c hc₂ he₂
        simp only [Algorithm.st, h₁, h₂]
        exact ⟨hst, hmsg⟩
      · have he₂ : (A₂.cfg r₂ t).event c = some e := hev ▸ he
        obtain ⟨h₁, hm₁, -⟩ := Algorithm.cfg_succ_of_event r₁ t p c e hc₁ he
        obtain ⟨h₂, hm₂, -⟩ := Algorithm.cfg_succ_of_event r₂ t p c e hc₂ he₂
        rw [hH t htT, hst, hstep] at h₁ hm₁
        refine ⟨h₁.trans h₂.symm, fun s m => ?_⟩
        by_cases hs : s = t
        · subst hs; rw [hm₁, hm₂]
        · rw [Algorithm.msg_succ r₁ t s hs, Algorithm.msg_succ r₂ t s hs]; exact hmsg s m
    · push Not at hstep'
      have hstep₂ : ∀ c, r₂.σ t ≠ some (p, c) := fun c h => hstep' c ((hσt c).2 h)
      refine ⟨?_, fun s m => ?_⟩
      · rw [Algorithm.loc_succ_of_ne r₁ t p hstep', Algorithm.loc_succ_of_ne r₂ t p hstep₂]
        exact hst
      · by_cases hs : s = t
        · subst hs
          exact iff_of_false (msg_succ_self_of_ne hstep' m) (msg_succ_self_of_ne hstep₂ m)
        · rw [Algorithm.msg_succ r₁ t s hs, Algorithm.msg_succ r₂ t s hs]; exact hmsg s m

/-- Under the hypotheses of `sim2`, `p` produces the same outputs in both runs before `T`. -/
lemma sim2_out (A₁ A₂ : Algorithm P R M I O S) (hstep : A₁.step = A₂.step) (p : P)
    (hinit : A₁.init p = A₂.init p) (r₁ r₂ : Run P R I) (T : ℕ)
    (hσ : ∀ t < T, (∀ s m, (A₁.cfg r₁ t).msg s = some (p, m) ↔ (A₂.cfg r₂ t).msg s = some (p, m)) →
      ∀ c, r₁.σ t = some (p, c) ↔ r₂.σ t = some (p, c))
    (hH : ∀ t < T, r₁.H p t = r₂.H p t)
    (hrecv : ∀ t < T, ∀ q s, r₁.σ t = some (p, .recv q s) → q = p) :
    ∀ t < T, (∀ y, A₁.Out r₁ p y t ↔ A₂.Out r₂ p y t) ∧
      ((∃ c, r₂.σ t = some (p, c)) → A₁.outAt r₁ t = A₂.outAt r₂ t) := by
  intro t ht
  obtain ⟨hst, hmsg⟩ := sim2 A₁ A₂ hstep p hinit r₁ r₂ T hσ hH hrecv t ht.le
  have hσt := hσ t ht hmsg
  have hat : ∀ c, r₂.σ t = some (p, c) → A₁.outAt r₁ t = A₂.outAt r₂ t := by
    intro c hc₂
    have hc₁ := (hσt c).2 hc₂
    have hev : (A₁.cfg r₁ t).event c = (A₂.cfg r₂ t).event c := by
      cases c with
      | recv q s =>
        obtain rfl := hrecv t ht q s hc₁
        exact event_recv_eq (hmsg s)
      | tick => rfl
      | input i => rfl
    rcases he : (A₁.cfg r₁ t).event c with _ | e
    · have he₂ : (A₂.cfg r₂ t).event c = none := hev ▸ he
      rw [(Algorithm.cfg_succ_of_event_none r₁ t p c hc₁ he).2,
        (Algorithm.cfg_succ_of_event_none r₂ t p c hc₂ he₂).2]
    · have he₂ : (A₂.cfg r₂ t).event c = some e := hev ▸ he
      rw [(Algorithm.cfg_succ_of_event r₁ t p c e hc₁ he).2.2,
        (Algorithm.cfg_succ_of_event r₂ t p c e hc₂ he₂).2.2, hH t ht, hst, hstep]
  refine ⟨fun y => ⟨?_, ?_⟩, fun ⟨c, hc⟩ => hat c hc⟩
  · rintro ⟨⟨c, hc⟩, hy⟩
    have hc₂ := (hσt c).1 hc
    exact ⟨⟨c, hc₂⟩, hat c hc₂ ▸ hy⟩
  · rintro ⟨⟨c, hc⟩, hy⟩
    exact ⟨⟨c, (hσt c).2 hc⟩, (hat c hc).symm ▸ hy⟩

end Sim

/-! ### Computed values -/

section Output

variable {P R M X Y S : Type} [DecidableEq P] {A : AlgAMP P R M X Y S}

/-- A process that produces an output computes a value. -/
lemma output_isSome {x : P → X} {r : Run P R Empty} {p : P} (h : A.Decided x r p) :
    ∃ y, A.output x r p = some y := by
  classical
  have hd : ∃ t, ∃ y, (A.toAlg x).Out r p y t := h
  obtain ⟨y, hy⟩ := Nat.find_spec hd
  obtain ⟨z, l, hz⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hy.2)
  refine ⟨z, ?_⟩
  rw [AlgAMP.output, dite_eq_left hd, hz]
  rfl

/-- Two runs in which `p` produces the same outputs before `T`, and some output before `T`,
give `p` the same computed value. -/
lemma output_eq_of_agree {x₁ x₂ : P → X} {r₁ r₂ : Run P R Empty} {p : P} (T : ℕ)
    (hout : ∀ t < T, ∀ y, (A.toAlg x₁).Out r₁ p y t ↔ (A.toAlg x₂).Out r₂ p y t)
    (hat : ∀ t < T, (∃ y, (A.toAlg x₂).Out r₂ p y t) →
      (A.toAlg x₁).outAt r₁ t = (A.toAlg x₂).outAt r₂ t)
    (hd : ∃ t < T, ∃ y, (A.toAlg x₂).Out r₂ p y t) : A.output x₁ r₁ p = A.output x₂ r₂ p := by
  classical
  have hex : ∃ t, ∃ y, (A.toAlg x₂).Out r₂ p y t := let ⟨t, _, h⟩ := hd; ⟨t, h⟩
  have hT : Nat.find hex < T := by
    obtain ⟨t, ht, h⟩ := hd; exact lt_of_le_of_lt (Nat.find_min' hex h) ht
  have hfirst₂ : ∀ t' < Nat.find hex, ∀ y, ¬ (A.toAlg x₂).Out r₂ p y t' :=
    fun t' ht' y hy => Nat.find_min hex ht' ⟨y, hy⟩
  rw [AlgAMP.output_eq_of_first (Nat.find_spec hex) hfirst₂]
  obtain ⟨y, hy⟩ := Nat.find_spec hex
  rw [AlgAMP.output_eq_of_first ⟨y, (hout _ hT y).2 hy⟩
    (fun t' ht' y' hy' => hfirst₂ t' ht' y' ((hout t' (by omega) y').1 hy')),
    hat _ hT ⟨y, hy⟩]

end Output

/-! ### Schedules -/

variable {P : Type} [Fintype P] [Nonempty P] [DecidableEq P]

/-- The process that may step at global time `t` (round-robin). -/
noncomputable def owner (t : ℕ) : P :=
  (Fintype.equivFin P).symm ⟨t % Fintype.card P, Nat.mod_lt _ Fintype.card_pos⟩

/-- The global time of the `u`-th turn of process `i`. -/
noncomputable def slot (i : P) (u : ℕ) : ℕ := Fintype.card P * u + (Fintype.equivFin P i : ℕ)

omit [DecidableEq P] in
lemma slot_div (i : P) (u : ℕ) : slot i u / Fintype.card P = u := by
  have h := (Fintype.equivFin P i).isLt
  unfold slot
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ Fintype.card_pos, Nat.div_eq_of_lt h, zero_add]

omit [DecidableEq P] in
lemma owner_slot (i : P) (u : ℕ) : owner (slot i u) = i := by
  have h := (Fintype.equivFin P i).isLt
  unfold owner slot
  rw [Equiv.symm_apply_eq]
  ext
  simp [Nat.mod_eq_of_lt h]

omit [DecidableEq P] in
lemma slot_owner (t : ℕ) : slot (owner t : P) (t / Fintype.card P) = t := by
  unfold slot owner
  simp only [Equiv.apply_symm_apply]
  exact Nat.div_add_mod t _

omit [DecidableEq P] in
lemma le_slot (i : P) (u : ℕ) : u ≤ slot i u := by
  have : 1 ≤ Fintype.card P := Fintype.card_pos
  unfold slot; nlinarith

omit [Nonempty P] [DecidableEq P] in
lemma slot_lt_slot (i j : P) {u u' : ℕ} (h : u < u') : slot i u < slot j u' := by
  have h₁ := (Fintype.equivFin P i).isLt
  unfold slot
  have : Fintype.card P * (u + 1) ≤ Fintype.card P * u' := Nat.mul_le_mul_left _ h
  rw [Nat.mul_succ] at this
  omega

omit [DecidableEq P] in
lemma slot_inj {i j : P} {u u' : ℕ} (h : slot i u = slot j u') : i = j ∧ u = u' := by
  have := owner_slot i u
  rw [h, owner_slot] at this
  refine ⟨this.symm, ?_⟩
  have := congrArg (· / Fintype.card P) h
  simpa [slot_div] using this

variable {M S : Type}

open Classical in
/-- The choice of process `i` at its local time `u` (configuration `C`): at odd times `2a + 1`
receive its own message of local time `a` (if any); with parameter `some N`, at times
`4(s + N) + 2` receive the message of another process sent at global time `s` (if any);
otherwise a time-out. -/
noncomputable def choice (N : Option ℕ) (i : P) (u : ℕ) (C : Config P M S) : Choice P Empty :=
  if u % 2 = 1 then
    if ∃ m, C.msg (slot i (u / 2)) = some (i, m) then .recv i (slot i (u / 2)) else .tick
  else
    match N with
    | none => .tick
    | some N₀ =>
      if u % 4 = 2 ∧ N₀ ≤ u / 4 then
        match C.msg (u / 4 - N₀) with
        | some (j, _) => if j = i then .tick else .recv j (u / 4 - N₀)
        | none => .tick
      else .tick

omit [Nonempty P] in
lemma choice_eq_recv {N : Option ℕ} {i : P} {u : ℕ} {C : Config P M S} {q : P} {s : ℕ}
    (h : choice N i u C = .recv q s) :
    (q = i ∧ u % 2 = 1 ∧ s = slot i (u / 2) ∧ ∃ m, C.msg s = some (i, m)) ∨
    (∃ N₀, N = some N₀ ∧ q ≠ i ∧ u % 4 = 2 ∧ N₀ ≤ u / 4 ∧ s = u / 4 - N₀ ∧
      ∃ m, C.msg s = some (q, m)) := by
  unfold choice at h
  split_ifs at h with h₁ h₂
  · simp only [Choice.recv.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, h₁, rfl, h₂⟩
  · rcases N with _ | N₀
    · simp at h
    · simp only at h
      split_ifs at h with h₃
      · rcases hm : C.msg (u / 4 - N₀) with _ | ⟨j, m⟩
        · rw [hm] at h; simp at h
        · rw [hm] at h
          simp only at h
          split_ifs at h with h₄
          simp only [Choice.recv.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr ⟨N₀, rfl, h₄, h₃.1, h₃.2, rfl, m, hm⟩

omit [Nonempty P] in
lemma choice_four (N : Option ℕ) (i : P) (v : ℕ) (C : Config P M S) :
    choice N i (4 * v) C = .tick := by
  unfold choice
  have h2 : 4 * v % 2 = 0 := by omega
  have h4 : ¬ (4 * v % 4 = 2) := by omega
  rcases N with _ | N₀ <;> simp [h2]

omit [Nonempty P] in
lemma choice_own {N : Option ℕ} {i : P} {a : ℕ} {C : Config P M S}
    (h : ∃ m, C.msg (slot i a) = some (i, m)) : choice N i (2 * a + 1) C = .recv i (slot i a) := by
  unfold choice
  have h1 : (2 * a + 1) % 2 = 1 := by omega
  have h2 : (2 * a + 1) / 2 = a := by omega
  simp [h1, h2, h]

omit [Nonempty P] in
lemma choice_other {N₀ : ℕ} {i q : P} {s : ℕ} {C : Config P M S} {m : M}
    (h : C.msg s = some (q, m)) (hq : q ≠ i) :
    choice (some N₀) i (4 * (s + N₀) + 2) C = .recv q s := by
  unfold choice
  have h1 : ¬ (4 * (s + N₀) + 2) % 2 = 1 := by omega
  have h2 : (4 * (s + N₀) + 2) % 4 = 2 := by omega
  have h3 : (4 * (s + N₀) + 2) / 4 - N₀ = s := by omega
  have h4 : N₀ ≤ (4 * (s + N₀) + 2) / 4 := by omega
  have h1' : ¬ 4 * (s + N₀) % 2 = 1 := by omega
  simp [h1', h2, h3, h4, h, hq]

omit [Nonempty P] in
/-- The choice of `i` depends only on its own messages, when receptions from others are
disabled. -/
lemma choice_congr {N : Option ℕ} {i : P} {u : ℕ} {C₁ C₂ : Config P M S}
    (hC : ∀ s m, C₁.msg s = some (i, m) ↔ C₂.msg s = some (i, m))
    (hN : ∀ N₀, N = some N₀ → u / 4 < N₀) : choice N i u C₁ = choice none i u C₂ := by
  unfold choice
  by_cases h₁ : u % 2 = 1
  · simp only [h₁, ite_true]
    have : (∃ m, C₁.msg (slot i (u / 2)) = some (i, m)) ↔
        ∃ m, C₂.msg (slot i (u / 2)) = some (i, m) := exists_congr fun m => hC _ m
    by_cases h₂ : ∃ m, C₁.msg (slot i (u / 2)) = some (i, m)
    · rw [ite_eq_left h₂, ite_eq_left (this.1 h₂)]
    · rw [ite_eq_right h₂, ite_eq_right (fun h => h₂ (this.2 h))]
  · simp only [h₁, ite_false]
    rcases N with _ | N₀
    · rfl
    · have := hN N₀ rfl
      simp only
      rw [ite_eq_right (by omega)]

/-- The failure pattern in which exactly the processes of `Ac` are correct (the others crash at
time `0`). -/
def patternOf (Ac : Set P) : FailurePattern P := ⟨fun _ => Acᶜ, fun _ _ _ => le_rfl⟩

open Classical in
/-- The scheduling policy: at time `t`, process `owner t` takes its step if it is in `Ac`. -/
noncomputable def schedPolicy (N : Option ℕ) (Ac : Set P) (t : ℕ) (C : Config P M S) :
    Option (P × Choice P Empty) :=
  if owner t ∈ Ac then some (owner t, choice N (owner t) (t / Fintype.card P) C) else none

/-- The run with active processes `Ac` and parameter `N`. -/
noncomputable def schedRun (A : Algorithm P Unit M Empty Y S) (N : Option ℕ) (Ac : Set P) :
    Run P Unit Empty :=
  policyRun A (patternOf Ac) (fun _ _ => ()) (schedPolicy N Ac)

variable {Y : Type} (A : Algorithm P Unit M Empty Y S)

lemma σ_schedRun (N : Option ℕ) (Ac : Set P) (t : ℕ) {p : P} {c : Choice P Empty} :
    (schedRun A N Ac).σ t = some (p, c) ↔
      owner t = p ∧ p ∈ Ac ∧ c = choice N p (t / Fintype.card P) (A.cfg (schedRun A N Ac) t) := by
  classical
  rw [schedRun, σ_policyRun, ← schedRun]
  unfold schedPolicy
  split_ifs with h
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, h, rfl⟩
    · rintro ⟨rfl, -, rfl⟩; exact ⟨rfl, rfl⟩
  · simp only [false_iff]
    rintro ⟨rfl, hp, -⟩; exact h hp

omit [Fintype P] [Nonempty P] in
lemma msg_persist {r : Run P Unit Empty} {t t' s : ℕ} {v : P × M}
    (h : (A.cfg r t).msg s = some v) (h' : s < t') : (A.cfg r t').msg s = some v := by
  have hst : s < t := by
    by_contra hc
    rw [Algorithm.msg_eq_none_of_le r t s (by omega)] at h
    simp at h
  rw [Algorithm.msg_eq_succ r h', ← Algorithm.msg_eq_succ r hst, h]

/-- The scheduled runs are admissible (with `N = none`, at most one process is active). -/
lemma schedRun_admissible (N : Option ℕ) (Ac : Set P)
    (hN : N = none → ∀ i ∈ Ac, ∀ j ∈ Ac, i = j) : A.Admissible (schedRun A N Ac) := by
  set r := schedRun A N Ac with hr
  have hF : r.F = patternOf Ac := rfl
  have hcorr : ∀ p, r.F.Correct p ↔ p ∈ Ac := fun p =>
    ⟨fun h => by simpa [hF, patternOf] using h 0, fun h t => by simpa [hF, patternOf] using h⟩
  -- receptions designate existing earlier messages
  have hrecv : ∀ t p q s, r.σ t = some (p, .recv q s) →
      owner t = p ∧ ((q = p ∧ (t / Fintype.card P) % 2 = 1 ∧ s = slot p (t / Fintype.card P / 2) ∧
        ∃ m, (A.cfg r t).msg s = some (p, m)) ∨
      (∃ N₀, N = some N₀ ∧ q ≠ p ∧ (t / Fintype.card P) % 4 = 2 ∧
        N₀ ≤ t / Fintype.card P / 4 ∧ s = t / Fintype.card P / 4 - N₀ ∧
        ∃ m, (A.cfg r t).msg s = some (q, m))) := by
    intro t p q s h
    obtain ⟨ho, -, hc⟩ := (σ_schedRun A N Ac t).1 h
    exact ⟨ho, choice_eq_recv hc.symm⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t p c h
    obtain ⟨-, hp, -⟩ := (σ_schedRun A N Ac t).1 h
    simpa [hF, patternOf] using hp
  · intro t p q s h
    obtain ⟨ho, h⟩ := hrecv t p q s h
    have ht : slot p (t / Fintype.card P) = t := by rw [← ho]; exact slot_owner t
    rcases h with h | h
    · obtain ⟨rfl, hu, rfl, m, hm⟩ := h
      refine ⟨?_, m, hm⟩
      have h1 : t / Fintype.card P / 2 < t / Fintype.card P := by
        generalize t / Fintype.card P = u at hu ⊢; omega
      have := slot_lt_slot q q h1
      rwa [ht] at this
    · obtain ⟨N₀, -, -, hu, -, rfl, m, hm⟩ := h
      refine ⟨?_, m, hm⟩
      have := le_slot p (t / Fintype.card P)
      rw [ht] at this
      generalize t / Fintype.card P = u at this hu ⊢; omega
  · intro t t' p q s h h'
    obtain ⟨ho, h₁⟩ := hrecv t p q s h
    obtain ⟨ho', h₂⟩ := hrecv t' p q s h'
    have key : t / Fintype.card P = t' / Fintype.card P := by
      rcases h₁ with ⟨rfl, hu, hs, -⟩ | ⟨N₀, hN₀, hq, hu, hle, hs, -⟩ <;>
        rcases h₂ with ⟨hq', hu', hs', -⟩ | ⟨N₀', hN₀', hq', hu', hle', hs', -⟩
      · have := (slot_inj (hs.symm.trans hs')).2; omega
      · exact absurd rfl hq'
      · exact absurd hq' hq
      · rw [hN₀] at hN₀'; cases hN₀'; omega
    have e1 := slot_owner (P := P) t
    have e2 := slot_owner (P := P) t'
    rw [ho] at e1
    rw [ho'] at e2
    rw [← e1, ← e2, key]
  · intro p hp T
    refine ⟨slot p (4 * T), by have := le_slot p (4 * T); omega, ?_⟩
    rw [σ_schedRun]
    refine ⟨owner_slot p _, (hcorr p).1 hp, ?_⟩
    rw [slot_div, choice_four]
  · intro p hp t s q m hm
    have hpA := (hcorr p).1 hp
    obtain ⟨c, -, hσ, -, -⟩ := Algorithm.msg_spec r hm
    obtain ⟨hoq, hqA, -⟩ := (σ_schedRun A N Ac s).1 hσ
    by_cases hqp : q = p
    · subst hqp
      refine ⟨slot q (2 * (s / Fintype.card P) + 1), ?_⟩
      rw [σ_schedRun]
      refine ⟨owner_slot _ _, hpA, ?_⟩
      have hs : slot q (s / Fintype.card P) = s := by rw [← hoq]; exact slot_owner s
      have hlt : s < slot q (2 * (s / Fintype.card P) + 1) := by
        have := slot_lt_slot q q (u := s / Fintype.card P) (u' := 2 * (s / Fintype.card P) + 1)
          (by omega)
        rwa [hs] at this
      have hm' := msg_persist A hm hlt
      rw [slot_div, choice_own, hs]
      rw [hs]; exact ⟨m, hm'⟩
    · rcases hNc : N with _ | N₀
      · exact absurd (hN hNc q hqA p hpA) hqp
      · refine ⟨slot p (4 * (s + N₀) + 2), ?_⟩
        rw [σ_schedRun]
        refine ⟨owner_slot _ _, hpA, ?_⟩
        have hlt : s < slot p (4 * (s + N₀) + 2) := by
          have := le_slot p (4 * (s + N₀) + 2); omega
        have hm' := msg_persist A hm hlt
        have := choice_other (N₀ := N₀) hm' hqp
        rw [← hNc] at this
        rw [slot_div, this]

/-- Comparison of a scheduled run with a solo run of `p`: if receptions from other processes
are disabled before `T` in the first run, then `p` produces the same outputs in both runs
before `T`. -/
lemma sched_sim (A₁ A₂ : Algorithm P Unit M Empty Y S) (hstep : A₁.step = A₂.step) (p : P)
    (hinit : A₁.init p = A₂.init p) (N : Option ℕ) (Ac₁ Ac₂ : Set P) (hp₁ : p ∈ Ac₁)
    (hp₂ : p ∈ Ac₂) (T : ℕ) (hNT : ∀ N₀, N = some N₀ → T ≤ N₀) :
    ∀ t < T, (∀ y, A₁.Out (schedRun A₁ N Ac₁) p y t ↔ A₂.Out (schedRun A₂ none Ac₂) p y t) ∧
      ((∃ c, (schedRun A₂ none Ac₂).σ t = some (p, c)) →
        A₁.outAt (schedRun A₁ N Ac₁) t = A₂.outAt (schedRun A₂ none Ac₂) t) := by
  have hu : ∀ t < T, ∀ N₀, N = some N₀ → t / Fintype.card P / 4 < N₀ := by
    intro t ht N₀ hN₀
    have := hNT N₀ hN₀
    have : t / Fintype.card P ≤ t := Nat.div_le_self _ _
    omega
  refine sim2_out A₁ A₂ hstep p hinit _ _ T ?_ (fun _ _ => rfl) ?_
  · intro t ht hmsg c
    rw [σ_schedRun, σ_schedRun]
    rw [choice_congr hmsg (hu t ht)]
    simp [hp₁, hp₂]
  · intro t ht q s h
    obtain ⟨-, -, hc⟩ := (σ_schedRun A₁ N Ac₁ t).1 h
    rcases choice_eq_recv hc.symm with h' | ⟨N₀, hN₀, -, -, hle, -⟩
    · exact h'.1
    · exact absurd hle (by have := hu t ht N₀ hN₀; omega)

end AsyncLocal

open AsyncLocal

variable {P X Y : Type} [DecidableEq P]

/-- The local algorithm: process `i` outputs `f i (x i)` at each of its steps. -/
def localAlgAMP (f : P → X → Option Y) : AlgAMP P Unit Empty X Y X where
  init _ v := v
  step p _ s _ := (s, none, (f p s).toList)

lemma localAlgAMP_solves {T : Task P X Y} (f : P → X → Option Y)
    (hf : ∀ x ∈ T.inputs, ∃ O ∈ T.Δ x, ∀ i, f i (x i) = some (O i)) :
    (localAlgAMP f).SolvesAMP (trivialFD P) T := by
  intro x hx r _ _ hA
  have hst : ∀ t p, ((localAlgAMP f).toAlg x).st r p t = x p :=
    Algorithm.st_induction r (fun p s => s = x p) (fun _ => rfl) (fun _ _ _ _ _ _ h => h)
  obtain ⟨O, hO, hfO⟩ := hf x hx
  have hout : ∀ p y t, ((localAlgAMP f).toAlg x).Out r p y t ↔
      (∃ c, r.σ t = some (p, c)) ∧ f p (x p) = some y := by
    intro p y t
    rw [Algorithm.out_iff]
    constructor
    · rintro ⟨c, e, hσ, -, hy⟩
      refine ⟨⟨c, hσ⟩, ?_⟩
      change y ∈ (f p (((localAlgAMP f).toAlg x).st r p t)).toList at hy
      rw [hst] at hy
      simpa using hy
    · rintro ⟨⟨c, hσ⟩, hy⟩
      obtain ⟨e, he⟩ := hA.event_isSome hσ
      refine ⟨c, e, hσ, he, ?_⟩
      change y ∈ (f p (((localAlgAMP f).toAlg x).st r p t)).toList
      rw [hst]
      simp [hy]
  refine ⟨fun p hp => ?_, O, hO, fun i y h => ?_⟩
  · obtain ⟨t, -, hσ⟩ := hA.ticks p hp 0
    exact ⟨t, O p, (hout p (O p) t).2 ⟨⟨_, hσ⟩, hfO p⟩⟩
  · obtain ⟨t, ht⟩ := AlgAMP.output_spec h
    have := ((hout i y t).1 ht).2
    rw [hfO i] at this
    exact Option.some.inj this

/-- **Theorem 1** of Raynal–Stainer (PODC 2013), asynchronous side: a task is solvable in
`AMP_{n,n-1}[fd : ∅]` (asynchronous message passing, any number of crashes as long as one process
is correct, no failure detector) iff it is local, i.e. every process can compute its output from
its own input only. -/
theorem amp_solvable_iff_local [Fintype P] [Nonempty P] (T : Task P X Y) :
    SolvableAMP (trivialFD P) T ↔ T.IsLocal := by
  classical
  constructor
  · rintro ⟨M, S, A, hA⟩
    -- solo runs
    let solo : (P → X) → P → Run P Unit Empty := fun x i => schedRun (A.toAlg x) none {i}
    have hsoloAdm : ∀ x i, (A.toAlg x).Admissible (solo x i) := fun x i =>
      schedRun_admissible _ none {i} (fun _ a ha b hb => by
        rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb])
    have hsoloDec : ∀ x ∈ T.inputs, ∀ i, A.Decided x (solo x i) i := fun x hx i =>
      (hA x hx (solo x i) ⟨i, fun t h => by simp [solo, schedRun, policyRun, patternOf] at h⟩
        (mem_trivialFD _ _) (hsoloAdm x i)).1 i
        (fun t h => by simp [solo, schedRun, policyRun, patternOf] at h)
    -- the solo output only depends on the input of the process
    have hsoloEq : ∀ x ∈ T.inputs, ∀ x' : P → X, ∀ i, x' i = x i →
        A.output x' (solo x' i) i = A.output x (solo x i) i := by
      intro x hx x' i hi
      obtain ⟨d, y, hd⟩ := hsoloDec x hx i
      have hs := sched_sim (A.toAlg x') (A.toAlg x) rfl i (by simp [AlgAMP.toAlg, hi]) none {i}
        {i} rfl rfl (d + 1) (by simp)
      exact output_eq_of_agree (d + 1) (fun t ht => (hs t ht).1)
        (fun t ht ⟨y, hy⟩ => (hs t ht).2 hy.1) ⟨d, by omega, y, hd⟩
    let f : P → X → Option Y := fun i v =>
      if h : ∃ x ∈ T.inputs, x i = v then A.output h.choose (solo h.choose i) i else none
    refine ⟨f, fun x hx => ?_⟩
    -- a bound on the solo decision times
    choose d y hd using hsoloDec x hx
    let N := Finset.univ.sup d + 1
    have hdN : ∀ i, d i < N := fun i => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))
    let merged := schedRun (A.toAlg x) (some N) Set.univ
    have hmAdm : (A.toAlg x).Admissible merged :=
      schedRun_admissible _ _ _ (fun h => by simp at h)
    have hmCorr : ∀ p, merged.F.Correct p := fun p t h => by
      simp [merged, schedRun, policyRun, patternOf] at h
    obtain ⟨-, O, hO, hOv⟩ := hA x hx merged ⟨Classical.arbitrary P, hmCorr _⟩
      (mem_trivialFD _ _) hmAdm
    refine ⟨O, hO, fun i => ?_⟩
    have hs := sched_sim (A.toAlg x) (A.toAlg x) rfl i rfl (some N) Set.univ {i} trivial rfl N
      (by simp)
    have hmi : A.output x merged i = A.output x (solo x i) i :=
      output_eq_of_agree N (fun t ht => (hs t ht).1) (fun t ht ⟨y, hy⟩ => (hs t ht).2 hy.1)
        ⟨d i, hdN i, y i, hd i⟩
    have hex : ∃ x' ∈ T.inputs, x' i = x i := ⟨x, hx, rfl⟩
    have hfi : f i (x i) = A.output x (solo x i) i := by
      simp only [f, dite_eq_left hex]
      exact hsoloEq x hx _ i hex.choose_spec.2
    obtain ⟨z, hz⟩ := output_isSome ⟨d i, y i, hd i⟩
    rw [hfi, hz, hOv i z (hmi.trans hz)]
  · rintro ⟨f, hf⟩
    exact ⟨Empty, X, localAlgAMP f, localAlgAMP_solves f hf⟩

end Podc.MessageAdversariesVsFD
