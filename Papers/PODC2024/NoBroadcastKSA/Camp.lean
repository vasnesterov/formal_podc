import Papers.PODC2024.NoBroadcastKSA.Spec

/-!
# The model `CAMP_n[k-SA]` and implementations of broadcast abstractions

Section 2 of the paper: `n` asynchronous processes, any number of which may crash, reliable
non-FIFO point-to-point channels (SR-Validity, SR-No-Duplication, SR-Termination), and any number
of k-set agreement objects (k-SA-Validity, k-SA-Agreement, k-SA-Termination, Section 4.1).

An algorithm `B` implementing a broadcast abstraction (`BAlgo`) is deterministic: the next
action of process `p` is a function of its local history (`B.next p h`), which consists of its
own actions, the invocations of `broadcast` by the upper layer, the receptions of point-to-point
messages and the answers of the k-SA objects. Its actions are: send a message, propose a value to
a k-SA object, return from the pending `broadcast`, B-deliver a message, or a local computation.

An execution (`CExec`) is a sequence of steps (`none`: no step at that time):

* `act p a` — a step of `B` at `p`, performing `a`;
* `inv p m` — the upper layer of `p` invokes `B.broadcast(m)`;
* `recv p q x s` — `p` receives the message `x` sent by `q` at time `s`;
* `dec p o w` — the k-SA object `o` returns `w` to `p`;
* `up p` — an internal step of the upper layer of `p` (invisible to `B`).

`Adm B k C α`: `α` is an admissible execution of `B` in `CAMP_n[k-SA]` with correct processes `C`:
`B`'s steps follow `B`, correct processes take infinitely many steps of `B`, faulty processes take
finitely many steps (they crash), the channel and k-SA properties hold, and the upper layer is
well-formed (it invokes `broadcast` only after the previous invocation returned, with a fresh
message). `Implements B k S`: the broadcast events of every admissible execution form an
execution admitted by `S`.
-/

namespace Podc.NoBroadcastKSA.Camp

set_option linter.unusedSectionVars false

/-- Actions of an implementation `B` of a broadcast abstraction. -/
inductive BAct (P M X O W : Type) where
  /-- send the point-to-point message `x` to `q` -/
  | send (q : P) (x : X)
  /-- propose `w` to the k-SA object `o` -/
  | propose (o : O) (w : W)
  /-- return from the pending `B.broadcast(m)` -/
  | ret (m : M)
  /-- B-deliver `m` from `q` -/
  | deliver (q : P) (m : M)
  /-- local computation -/
  | skip
  deriving DecidableEq

/-- The local events of a process, as seen by `B`. -/
inductive CLEv (P M X O W : Type) where
  | act (a : BAct P M X O W)
  | inv (m : M)
  | recv (q : P) (x : X)
  | dec (o : O) (w : W)
  deriving DecidableEq

/-- A deterministic algorithm of `CAMP_n[k-SA]` implementing a broadcast abstraction. -/
structure BAlgo (P M X O W : Type) where
  /-- The next action of `p` after the local history `h` (oldest event first). -/
  next : P → List (CLEv P M X O W) → BAct P M X O W

/-- The standard assumption of Section 4.1: a process proposes at most once to each k-SA
object. -/
def BAlgo.OneShot {P M X O W : Type} (B : BAlgo P M X O W) : Prop :=
  ∀ p h o w, B.next p h = .propose o w → ∀ w', CLEv.act (.propose o w') ∉ h

/-- Steps of an execution of `CAMP_n[k-SA]`. -/
inductive CStep (P M X O W : Type) where
  | act (p : P) (a : BAct P M X O W)
  | inv (p : P) (m : M)
  | recv (p q : P) (x : X) (s : ℕ)
  | dec (p : P) (o : O) (w : W)
  | up (p : P)
  deriving DecidableEq

variable {P M X O W : Type}

namespace CStep

/-- The process taking a step. -/
def proc : CStep P M X O W → P
  | act p _ => p
  | inv p _ => p
  | recv p _ _ _ => p
  | dec p _ _ => p
  | up p => p

/-- The local event of `B` produced by a step of `p` (`up` steps are invisible to `B`). -/
def bloc : CStep P M X O W → Option (CLEv P M X O W)
  | act _ a => some (.act a)
  | inv _ m => some (.inv m)
  | recv _ q x _ => some (.recv q x)
  | dec _ o w => some (.dec o w)
  | up _ => none

/-- The broadcast event of a step, if any. -/
def toB : CStep P M X O W → Option (BEv P M)
  | act p (.ret m) => some (.ret p m)
  | act p (.deliver q m) => some (.dl p q m)
  | inv p m => some (.bc p m)
  | _ => none

end CStep

/-- Executions of `CAMP_n[k-SA]`. -/
abbrev CExec (P M X O W : Type) := ℕ → Option (CStep P M X O W)

variable [DecidableEq P]

/-- The local history of `B` at `p` before time `t`. -/
def bhist (α : CExec P M X O W) (p : P) : ℕ → List (CLEv P M X O W)
  | 0 => []
  | t + 1 => bhist α p t ++
      ((α t).bind fun s => if s.proc = p then s.bloc else none).toList

/-- The broadcast events of an execution. -/
def proj (α : CExec P M X O W) (C : Set P) : BExec P M where
  ev t := (α t).bind CStep.toB
  correct := C

/-- Admissible executions of `B` in `CAMP_n[k-SA]` with correct processes `C`. -/
structure Adm (B : BAlgo P M X O W) (k : ℕ) (C : Set P) (α : CExec P M X O W) : Prop where
  /-- The steps of `B` follow `B`. -/
  cons : ∀ (t : ℕ) (p : P) (a : BAct P M X O W), α t = some (.act p a) →
    a = B.next p (bhist α p t)
  /-- A correct process takes infinitely many steps of `B`. -/
  fair : ∀ p ∈ C, ∀ t, ∃ t' ≥ t, ∃ a, α t' = some (.act p a)
  /-- A faulty process crashes: it takes finitely many steps. -/
  crash : ∀ p ∉ C, ∃ T, ∀ t ≥ T, ∀ s, α t = some s → s.proc ≠ p
  /-- **SR-Validity.** -/
  srValid : ∀ (t : ℕ) (p q : P) (x : X) (s : ℕ), α t = some (.recv p q x s) →
    s < t ∧ α s = some (.act q (.send p x))
  /-- **SR-No-Duplication.** -/
  srNoDup : ∀ (t t' : ℕ) (p q : P) (x x' : X) (s : ℕ), α t = some (.recv p q x s) →
    α t' = some (.recv p q x' s) → t = t'
  /-- **SR-Termination.** -/
  srTerm : ∀ p ∈ C, ∀ (s : ℕ) (q : P) (x : X), α s = some (.act q (.send p x)) →
    ∃ t, α t = some (.recv p q x s)
  /-- A k-SA object answers a pending proposal of the process, once. -/
  ksaPend : ∀ (t : ℕ) (p : P) (o : O) (w : W), α t = some (.dec p o w) →
    ∃ s < t, ∃ w', α s = some (.act p (.propose o w'))
  ksaOnce : ∀ (t t' : ℕ) (p : P) (o : O) (w w' : W), α t = some (.dec p o w) →
    α t' = some (.dec p o w') → t = t'
  /-- **k-SA-Validity.** -/
  ksaValid : ∀ (t : ℕ) (p : P) (o : O) (w : W), α t = some (.dec p o w) →
    ∃ s < t, ∃ q, α s = some (.act q (.propose o w))
  /-- **k-SA-Agreement.** -/
  ksaAgree : ∀ (o : O) (f : Fin (k + 1) → W), Function.Injective f →
    ¬ ∀ i, ∃ t p, α t = some (.dec p o (f i))
  /-- **k-SA-Termination.** -/
  ksaTerm : ∀ p ∈ C, ∀ (s : ℕ) (o : O) (w : W), α s = some (.act p (.propose o w)) →
    ∃ t > s, ∃ w', α t = some (.dec p o w')
  /-- The upper layer is well-formed: it invokes `broadcast` with a fresh message, after the
  previous invocations returned. -/
  invWF : ∀ (t : ℕ) (p : P) (m : M), α t = some (.inv p m) → ∀ s < t, ∀ m',
    α s = some (.inv p m') → m' ≠ m ∧ ∃ s', s < s' ∧ s' < t ∧ α s' = some (.act p (.ret m'))

/-- `B` implements the broadcast abstraction `S` in `CAMP_n[k-SA]`. -/
def Implements (B : BAlgo P M X O W) (k : ℕ) (S : Set (BExec P M)) : Prop :=
  ∀ (C : Set P) (α : CExec P M X O W), Adm B k C α → proj α C ∈ S

/-! ## Basic lemmas -/

lemma mem_bhist {α : CExec P M X O W} {p : P} {t : ℕ} {e : CLEv P M X O W} :
    e ∈ bhist α p t ↔ ∃ s < t, ∃ st, α s = some st ∧ st.proc = p ∧ st.bloc = some e := by
  induction t with
  | zero => simp [bhist]
  | succ t ih =>
    simp only [bhist, List.mem_append, ih, Option.mem_toList,
      Option.bind_eq_some_iff]
    constructor
    · rintro (⟨s, hs, st, h1, h2, h3⟩ | ⟨st, h1, h2⟩)
      · exact ⟨s, by omega, st, h1, h2, h3⟩
      · split_ifs at h2 with hp
        · exact ⟨t, by omega, st, h1, hp, h2⟩
    · rintro ⟨s, hs, st, h1, h2, h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact Or.inl ⟨s, hs, st, h1, h2, h3⟩
      · exact Or.inr ⟨st, h1, by simp [h2, h3]⟩

lemma proj_ev_eq_some {α : CExec P M X O W} {C : Set P} {t : ℕ} {e : BEv P M} :
    (proj α C).ev t = some e ↔ ∃ st, α t = some st ∧ st.toB = some e := by
  simp [proj, Option.bind_eq_some_iff]

end Podc.NoBroadcastKSA.Camp
