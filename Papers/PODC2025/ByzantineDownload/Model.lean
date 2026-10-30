import Mathlib

/-!
# The synchronous Data Retrieval model with crash faults (§1.1, §5 of arXiv 2412.19649)

`k` peers `Fin k` form a clique; a trusted source stores `X : Fin n → Bool`. Execution proceeds in
synchronous rounds `r = 1, 2, …`; round `r` consists of

1. the **query sub-round**: peer `p` in local state `s` queries the bits `query p s`;
2. the **response sub-round**: it gets the answers `ans X (query p s)`;
3. the **message sub-round**: it sends `send p s a q` to every peer `q` (possibly itself; `none` =
   no message), receives its inbox, and moves to the state `step p s a inbox`.

Protocols are deterministic. **Crash faults** (`Pattern`): `crash p = some c` means that `p`
crashes in round `c`: it behaves correctly in rounds `< c`, in round `c` its messages reach only the
peers `q` with `reach p q` (it may stop in the middle of the message sub-round), and it does nothing
afterwards (its state is frozen; it is never looked at again). At most `f` peers crash
(`Pattern.Admissible f`). The adversary chooses the input and the crash pattern (deterministic
protocols: an all-knowing adversary is the same as quantifying over all patterns).

Complexity measures: `queries` (bits queried by a peer during the first `T` rounds; the paper's `Q`
is its maximum over nonfaulty peers), and the time `T` after which all nonfaulty peers have output
`X` (`res`).
-/

namespace Podc.ByzantineDownload

/-- A deterministic protocol in the synchronous DR model, with local states `S` and messages `M`. -/
structure Protocol (k n : ℕ) (S M : Type*) where
  /-- Initial local states. -/
  init : Fin k → S
  /-- The bits queried in the query sub-round. -/
  query : Fin k → S → Finset (Fin n)
  /-- The message sent to `q` in the message sub-round, given the query answers. -/
  send : Fin k → S → (Fin n → Option Bool) → Fin k → Option M
  /-- The new local state, given the query answers and the inbox (`inbox p` = message from `p`). -/
  step : Fin k → S → (Fin n → Option Bool) → (Fin k → Option M) → S
  /-- The output array `res` (`none` = `⊥`). -/
  res : S → Fin n → Option Bool

/-- The source's answers to the queries `Q`. -/
def ans {n : ℕ} (X : Fin n → Bool) (Q : Finset (Fin n)) : Fin n → Option Bool :=
  fun i => if i ∈ Q then some (X i) else none

/-- A crash pattern: `crash p = some c` — `p` crashes in round `c`, and in that round its messages
reach exactly the peers `q` with `reach p q`. -/
structure Pattern (k : ℕ) where
  /-- Crash round (`none` = nonfaulty). -/
  crash : Fin k → Option ℕ
  /-- Recipients of the messages of the crashing round. -/
  reach : Fin k → Fin k → Bool

namespace Pattern

variable {k : ℕ} (π : Pattern k)

/-- `p` completes round `r` (it does not crash in rounds `≤ r`); `alive p 0` always holds. -/
def alive (p : Fin k) (r : ℕ) : Bool :=
  match π.crash p with
  | none => true
  | some c => r < c

/-- The message of `p` to `q` in round `r` is delivered. -/
def delivers (p q : Fin k) (r : ℕ) : Bool :=
  match π.crash p with
  | none => true
  | some c => r < c || (r == c && π.reach p q)

/-- `p` is nonfaulty. -/
def Nonfaulty (p : Fin k) : Prop := π.crash p = none

/-- The faulty peers. -/
def faulty : Finset (Fin k) := Finset.univ.filter (fun p => (π.crash p).isSome)

/-- At most `f` peers crash. -/
def Admissible (f : ℕ) : Prop := π.faulty.card ≤ f

end Pattern

namespace Protocol

variable {k n : ℕ} {S M : Type*} (A : Protocol k n S M) (X : Fin n → Bool) (π : Pattern k)

/-- The answers `p` gets in state `s`. -/
def answers (p : Fin k) (s : S) : Fin n → Option Bool := ans X (A.query p s)

/-- The inbox of `q` in round `r` when the peers are in states `c`. -/
def inbox (r : ℕ) (c : Fin k → S) (q : Fin k) : Fin k → Option M :=
  fun p => if π.delivers p q r then A.send p (c p) (A.answers X p (c p)) q else none

/-- One synchronous round `r`: peers that complete round `r` take a step; crashed peers freeze. -/
def round (r : ℕ) (c : Fin k → S) : Fin k → S :=
  fun q => if π.alive q r then A.step q (c q) (A.answers X q (c q)) (A.inbox X π r c q) else c q

/-- The configuration at time `t` (after `t` rounds). -/
def cfg : ℕ → Fin k → S
  | 0 => A.init
  | t + 1 => A.round X π (t + 1) (cfg t)

/-- The number of bits queried by `p` in rounds `1, …, T`. -/
def queries (p : Fin k) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, (A.query p (A.cfg X π t p)).card

/-- The number of messages sent by `p` in rounds `1, …, T` (messages to oneself excluded). -/
def msgsSent (p : Fin k) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, (Finset.univ.filter
    (fun q => q ≠ p ∧ (A.send p (A.cfg X π t p) (A.answers X p (A.cfg X π t p)) q).isSome)).card

/-- `A` solves Download within `T` rounds against at most `f` crashes: in every admissible
execution, from time `T` on every nonfaulty peer has `res = X`. -/
def SolvesWithin (f T : ℕ) : Prop :=
  ∀ (X : Fin n → Bool) (π : Pattern k), π.Admissible f → ∀ p, π.Nonfaulty p → ∀ t ≥ T,
    A.res (A.cfg X π t p) = fun i => some (X i)

lemma cfg_succ (t : ℕ) : A.cfg X π (t + 1) = A.round X π (t + 1) (A.cfg X π t) := rfl

end Protocol

/-! ### Views, leaders and output arrays (shared by Algorithms 6 and 7) -/

section Views

variable {k n : ℕ} [NeZero k]

/-- `lead(v) = v mod k`. -/
def lead (v : ℕ) : Fin k := ⟨v % k, Nat.mod_lt _ (Nat.pos_of_neZero k)⟩

/-- Line 19 of Algorithm 6 / line 31 of Algorithm 7: the least view `v' > v` whose leader is not
in `F` (`v + 1` if every peer is in `F`, which never happens in our executions). -/
def nextView (F : Finset (Fin k)) (v : ℕ) : ℕ :=
  match (List.range k).find? (fun d => decide (lead (k := k) (v + 1 + d) ∉ F)) with
  | some d => v + 1 + d
  | none => v + 1

/-- `res[i]` for a natural-number index (`⊥` out of range). -/
def get (res : Fin n → Option Bool) (i : ℕ) : Option Bool :=
  if h : i < n then res ⟨i, h⟩ else none

/-- `res[i] ← b`. -/
def set (res : Fin n → Option Bool) (i : ℕ) (b : Bool) : Fin n → Option Bool :=
  fun j => if j.val = i then some b else res j

end Views

end Podc.ByzantineDownload
