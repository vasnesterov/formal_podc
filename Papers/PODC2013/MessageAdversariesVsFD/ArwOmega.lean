import Papers.PODC2013.MessageAdversariesVsFD.Model

/-!
# Tasks in `ARW_{n,n-1}[fd : Ω]`

Raynal–Stainer (PODC 2013), Sections 2.3 and 2.4: asynchronous processes communicating through
single-writer multi-reader atomic registers, where up to `n - 1` processes may crash, enriched with
the eventual leader failure detector `Ω`.

* Every process `p` owns a bank of atomic registers indexed by `K` (register `k` holds values of
  type `V k`, initially `Alg.v₀ k`); only `p` writes them, everybody reads them.
* A process is a deterministic state machine (`Alg.next`); one atomic step (`Act`) is a write to
  one of its own registers, a read of one register of any process, a query of its `Ω` module, or a
  decision `decide y` (the *first* decision is the value computed by the process; it may keep
  taking steps afterwards, e.g. to help others).
* An execution is given by the input vector, an infinite schedule `σ : ℕ → P` (`σ t` takes the
  atomic step number `t`) and an `Ω` history `H : P → ℕ → P` (`H p t` is the output of `p`'s `Ω`
  module if `p` queries it at time `t`). A process is correct iff it takes infinitely many steps;
  with finitely many processes some process is correct, so any number `≤ n - 1` of crashes is
  allowed (wait-freedom).
* `Ω` (`OmegaValid`): there are a correct process `ℓ` and a time after which the `Ω` modules of all
  correct processes output `ℓ`; before that time, and for faulty processes, outputs are arbitrary.
* `Alg.Solves T` (Section 2.4 semantics): for every valid input vector, schedule and valid `Ω`
  history, every correct process decides, and at every time the decided values are valid
  (`Task.Valid`; decisions are irrevocable, so this is the same as validity of the final ones).
-/

namespace Podc.MessageAdversariesVsFD

namespace ARW

/-- An atomic step: write `v` to own register `k`, read register `k` of process `q`
(continuation `cont` receives the value), query `Ω` (continuation receives the leader), or
decide `y`; each carries the next local state. -/
inductive Act (P K : Type) (V : K → Type) (Y S : Type) : Type where
  | write (k : K) (v : V k) (s : S)
  | read (q : P) (k : K) (cont : V k → S)
  | query (cont : P → S)
  | decide (y : Y) (s : S)

/-- A deterministic algorithm in `ARW[Ω]` with inputs `X`, outputs `Y`, registers `K` (values
`V k`) and local states `S`. -/
structure Alg (P X Y K : Type) (V : K → Type) (S : Type) where
  /-- Initial value of register `k` (of every process). -/
  v₀ : ∀ k, V k
  /-- Initial local state of process `p` with input `v`. -/
  init : P → X → S
  /-- The next atomic step of process `p` in local state `s`. -/
  next : P → S → Act P K V Y S

/-- A configuration: local states, memory (`mem p k` = register `k` of `p`), decided values. -/
structure Config (P K : Type) (V : K → Type) (Y S : Type) where
  /-- Local states. -/
  loc : P → S
  /-- Shared memory: `mem p k` is register `k` of process `p`. -/
  mem : P → (k : K) → V k
  /-- First decision of each process (`none`: not decided yet). -/
  out : P → Option Y

variable {P X Y K : Type} {V : K → Type} {S : Type} [DecidableEq P] [DecidableEq K]

namespace Alg

variable (A : Alg P X Y K V S)

/-- One atomic step of process `p`, whose `Ω` module outputs `ℓ`. -/
def step (p ℓ : P) (C : Config P K V Y S) : Config P K V Y S :=
  match A.next p (C.loc p) with
  | .write k v s =>
    { C with loc := Function.update C.loc p s,
             mem := Function.update C.mem p (Function.update (C.mem p) k v) }
  | .read q k f => { C with loc := Function.update C.loc p (f (C.mem q k)) }
  | .query f => { C with loc := Function.update C.loc p (f ℓ) }
  | .decide y s =>
    { C with loc := Function.update C.loc p s,
             out := Function.update C.out p ((C.out p).or (some y)) }

/-- The initial configuration for the input vector `x`. -/
def initCfg (x : P → X) : Config P K V Y S :=
  ⟨fun p => A.init p (x p), fun _ => A.v₀, fun _ => none⟩

/-- The configuration after `t` steps of schedule `σ` with `Ω` history `H`. -/
def conf (x : P → X) (σ : ℕ → P) (H : P → ℕ → P) : ℕ → Config P K V Y S
  | 0 => A.initCfg x
  | t + 1 => A.step (σ t) (H (σ t) t) (conf x σ H t)

end Alg

/-- `p` is correct in schedule `σ`: it takes infinitely many steps. -/
def Correct (σ : ℕ → P) (p : P) : Prop := ∀ T, ∃ t ≥ T, σ t = p

/-- `H` is a valid history of `Ω` for the schedule `σ`: eventually all correct processes have
the same correct leader. -/
def OmegaValid (σ : ℕ → P) (H : P → ℕ → P) : Prop :=
  ∃ ℓ, Correct σ ℓ ∧ ∃ T, ∀ t ≥ T, ∀ p, Correct σ p → H p t = ℓ

/-- `A` solves `T` in `ARW_{n,n-1}[fd : Ω]` (wait-free): in every execution with a valid `Ω`
history, every correct process decides and the decided values are always valid. -/
def Alg.Solves (A : Alg P X Y K V S) (T : Task P X Y) : Prop :=
  ∀ x ∈ T.inputs, ∀ (σ : ℕ → P) (H : P → ℕ → P), OmegaValid σ H →
    (∀ p, Correct σ p → ∃ t, ((A.conf x σ H t).out p).isSome) ∧
      ∀ t, T.Valid x (A.conf x σ H t).out

/-! ### Effect of a step -/

/-- The next local state after action `a` (reading memory `rd`, `Ω` output `ℓ`). -/
def Act.post {P K : Type} {V : K → Type} {Y S : Type} (a : Act P K V Y S)
    (rd : P → (k : K) → V k) (ℓ : P) : S :=
  match a with
  | .write _ _ s => s
  | .read q k f => f (rd q k)
  | .query f => f ℓ
  | .decide _ s => s

/-- The registers of the stepping process after action `a`. -/
def Act.memUpd {P K : Type} {V : K → Type} {Y S : Type} [DecidableEq K] (a : Act P K V Y S)
    (m : (k : K) → V k) : (k : K) → V k :=
  match a with
  | .write k v _ => Function.update m k v
  | _ => m

/-- The decision of the stepping process after action `a`. -/
def Act.outUpd {P K : Type} {V : K → Type} {Y S : Type} (a : Act P K V Y S) (o : Option Y) :
    Option Y :=
  match a with
  | .decide y _ => o.or (some y)
  | _ => o

namespace Alg

variable (A : Alg P X Y K V S)

/-- Local states after a step. -/
theorem step_loc (p ℓ : P) (C : Config P K V Y S) :
    (A.step p ℓ C).loc = Function.update C.loc p ((A.next p (C.loc p)).post C.mem ℓ) := by
  unfold step Act.post; split <;> simp_all

/-- Memory after a step. -/
theorem step_mem (p ℓ : P) (C : Config P K V Y S) :
    (A.step p ℓ C).mem = Function.update C.mem p ((A.next p (C.loc p)).memUpd (C.mem p)) := by
  unfold step Act.memUpd; split <;> simp_all

/-- Decisions after a step. -/
theorem step_out (p ℓ : P) (C : Config P K V Y S) :
    (A.step p ℓ C).out = Function.update C.out p ((A.next p (C.loc p)).outUpd (C.out p)) := by
  unfold step Act.outUpd; split <;> simp_all

/-- A step only changes the stepping process. -/
theorem step_eq (p ℓ : P) (C : Config P K V Y S) :
    A.step p ℓ C = ⟨Function.update C.loc p ((A.next p (C.loc p)).post C.mem ℓ),
      Function.update C.mem p ((A.next p (C.loc p)).memUpd (C.mem p)),
      Function.update C.out p ((A.next p (C.loc p)).outUpd (C.out p))⟩ := by
  rw [← step_loc, ← step_mem, ← step_out]

/-- Unfolding of `conf`. -/
theorem conf_succ (x : P → X) (σ : ℕ → P) (H : P → ℕ → P) (t : ℕ) :
    A.conf x σ H (t + 1) = A.step (σ t) (H (σ t) t) (A.conf x σ H t) := rfl

/-- Decisions are irrevocable. -/
theorem out_mono (x : P → X) (σ : ℕ → P) (H : P → ℕ → P) (p : P) {y : Y} {t t' : ℕ}
    (h : (A.conf x σ H t).out p = some y) (ht : t ≤ t') : (A.conf x σ H t').out p = some y := by
  induction ht with
  | refl => exact h
  | @step m _ ih =>
    rw [conf_succ, step_out]
    by_cases hp : p = σ m
    · subst hp; rw [Function.update_self]; unfold Act.outUpd; split <;> simp [ih]
    · rw [Function.update_of_ne hp, ih]

/-- The local state of `p` only changes when `p` steps. -/
theorem loc_succ_of_ne (x : P → X) (σ : ℕ → P) (H : P → ℕ → P) {p : P} {t : ℕ}
    (h : σ t ≠ p) : (A.conf x σ H (t + 1)).loc p = (A.conf x σ H t).loc p := by
  rw [conf_succ, step_loc, Function.update_of_ne (Ne.symm h)]

/-- **Progress.** If from time `t₀` on every step of the correct process `p` from a state outside
`G` leads into `G` or decreases the measure `μ`, then `p` eventually reaches `G`. -/
theorem reach (x : P → X) (σ : ℕ → P) (H : P → ℕ → P) {p : P} (hp : Correct σ p)
    (G : S → Prop) (μ : S → ℕ) (t₀ : ℕ)
    (h : ∀ t ≥ t₀, σ t = p → ¬ G ((A.conf x σ H t).loc p) →
      G ((A.conf x σ H (t + 1)).loc p) ∨
        μ ((A.conf x σ H (t + 1)).loc p) < μ ((A.conf x σ H t).loc p)) :
    ∀ t ≥ t₀, ∃ t' ≥ t, G ((A.conf x σ H t').loc p) := by
  suffices ∀ n, ∀ t ≥ t₀, μ ((A.conf x σ H t).loc p) = n → ∃ t' ≥ t, G ((A.conf x σ H t').loc p)
    from fun t ht => this _ t ht rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t ht hn
    by_cases hG : G ((A.conf x σ H t).loc p)
    · exact ⟨t, le_rfl, hG⟩
    -- the first step of `p` at or after `t`
    have hex : ∃ t', σ (t + t') = p := by
      obtain ⟨t', ht', h'⟩ := hp t; exact ⟨t' - t, by rwa [Nat.add_sub_cancel' ht']⟩
    classical
    let k := Nat.find hex
    have hk : σ (t + k) = p := Nat.find_spec hex
    have hsame : ∀ i ≤ k, (A.conf x σ H (t + i)).loc p = (A.conf x σ H t).loc p := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih' =>
        rw [← Nat.add_assoc, loc_succ_of_ne A x σ H (Nat.find_min hex (by omega)), ih' (by omega)]
    have hGk : ¬ G ((A.conf x σ H (t + k)).loc p) := by rw [hsame k le_rfl]; exact hG
    rcases h (t + k) (by omega) hk hGk with h1 | h1
    · exact ⟨t + k + 1, by omega, h1⟩
    · rw [hsame k le_rfl, hn] at h1
      obtain ⟨t', ht', hG'⟩ := ih _ h1 (t + k + 1) (by omega) rfl
      exact ⟨t', by omega, hG'⟩

/-- A correct process takes a step at or after any time, in the state it has at that time. -/
theorem exists_step (x : P → X) (σ : ℕ → P) (H : P → ℕ → P) {p : P} (hp : Correct σ p)
    (t : ℕ) : ∃ t' ≥ t, σ t' = p ∧ (A.conf x σ H t').loc p = (A.conf x σ H t).loc p := by
  have hex : ∃ t', σ (t + t') = p := by
    obtain ⟨t', ht', h'⟩ := hp t; exact ⟨t' - t, by rwa [Nat.add_sub_cancel' ht']⟩
  classical
  let k := Nat.find hex
  have hsame : ∀ i ≤ k, (A.conf x σ H (t + i)).loc p = (A.conf x σ H t).loc p := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih' =>
      rw [← Nat.add_assoc, loc_succ_of_ne A x σ H (Nat.find_min hex (by omega)), ih' (by omega)]
  exact ⟨t + k, by omega, Nat.find_spec hex, hsame k le_rfl⟩

end Alg

end ARW

/-- `T` is solvable in `ARW_{n,n-1}[fd : Ω]`. -/
def SolvableARWOmega {P X Y : Type} [DecidableEq P] (T : Task P X Y) : Prop :=
  ∃ (K : Type) (_ : DecidableEq K) (V : K → Type) (S : Type) (A : ARW.Alg P X Y K V S),
    A.Solves T

end Podc.MessageAdversariesVsFD
