import Mathlib

/-!
# The Kowalski–Mostéfaoui protocol (PODC 2013), Sections 4.1–4.2

D. R. Kowalski, A. Mostéfaoui. *Synchronous Byzantine Agreement with Nearly a Cubic Number of
Communication Bits.* PODC 2013.

`n` processes `Fin n`, at most `t` Byzantine, `t + 1` synchronous rounds, point-to-point
authenticated channels (the receiver knows the sender), every process also receives its own
message. We formalize the protocol exactly as specified in Section 4:

* **Messages** (`Msg`). One record type for all rounds; the fields not used in a round are ignored.
  Round 1: the proposal `v1`. Round 2: the echo `e2` of the round-1 values. Round 3: the suspicion
  set `sus` (main part) and the echo `e3` of the round-2 arrays. Round `r ≥ 4`: `sus` and the echo
  `ek` of the suspicion sets received in round `r - 1`.
* **Local view** (`View`): `ib r j` is the message received from `j` in round `r` (rounds are
  numbered from `1`, as in the paper; `none` = nothing / not well-formed).
* **Suspicion** (`susp`): after round `r ≥ 2`, a process suspects `j` if it suspected `j` before, or
  if the round-`(r-1)` main part of `j` (as received directly) is not echoed identically by at least
  `n - t` processes in round `r` (`confirmed`). A message from a process suspected in an earlier
  round is treated as `⊥` (`recv`).
* **EIG tree** (Section 4.1 bullets and Section 4.2). Labels are lists of distinct ids written in
  *reverse* order: the paper's label `y k ℓ` is `ℓ :: k :: y'` (`y'` = reverse of `y`), so the
  children of `x` are the lists `k :: x` with `k ∉ x`. Level-1 values are proposals (`Option V`),
  values on levels `≥ 2` are `⊤`/`⊥` (`Bool`, `true` = `⊤` = "do not suspect").
  - `val1 [j]`: the value received from `j` in round 1;
  - `cval2 [k, j]` (paper `cval(jk)`): the round-1 value of `j` reported by `k` in round 2;
  - `valB (ℓ :: k :: _)` (levels `2..t`): `⊤` iff `ℓ` never reported by round `t` that it
    suspects `k`; `leafVal` is the same for leaves (level `t + 1`), with reports up to round `t+1`;
  - `cvalB (ℓ :: k :: j :: _)` (levels `≥ 3`): `⊤` iff `ℓ` never reported by round `t + 1` that `k`
    reported that it suspects `j`;
  - `newvalB` (levels `≥ 2`): leaves copy `leafVal`; an internal node of level `l` takes the
    strict majority of the `cval`s of its children in `T = {children with newval ⊤}` provided
    `|T| ≥ n - t - l`, and `⊥` otherwise; `newval1` is the same rule on level 1 (the result is a
    proposal or `⊥`); the decision (`decision`) is the strict majority of the `newval1`s if it is a
    non-`⊥` value, and the default `v0` otherwise.
-/

namespace Podc.CubicBitsBA

/-- A message. Each round uses some of the fields (see the module docstring); the others are
ignored by the receivers. -/
structure Msg (n : ℕ) (V : Type) where
  /-- Round 1: the proposed value. -/
  v1 : Option V := none
  /-- Round 2: the echo of the values received in round 1. -/
  e2 : Fin n → Option V := fun _ => none
  /-- Rounds `≥ 3` (main part): the set of processes the sender suspects. -/
  sus : Fin n → Bool := fun _ => false
  /-- Round 3: the echo of the arrays received in round 2. -/
  e3 : Fin n → Option (Fin n → Option V) := fun _ => none
  /-- Rounds `≥ 4`: the echo of the suspicion sets received in the previous round. -/
  ek : Fin n → Option (Fin n → Bool) := fun _ => none

/-- The local view of a process: `ib r j` is what it received from `j` in round `r ≥ 1`
(including its own message, `j = i`). -/
abbrev View (n : ℕ) (V : Type) := ℕ → Fin n → Option (Msg n V)

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- Does `e` (an echoer's round-`(r+1)` message) echo `m` (the round-`r` message of `j`)
identically? Round 1: the proposal; round 2: the array of echoed proposals; rounds `≥ 3`: the
suspicion set. -/
def echoMatch (r : ℕ) (m e : Msg n V) (j : Fin n) : Bool :=
  match r with
  | 1 => m.v1.isSome && decide (e.e2 j = m.v1)
  | 2 => decide (e.e3 j = some m.e2)
  | _ => decide (e.ek j = some m.sus)

/-- The message from `j` in round `r`, treated as `⊥` if `j ∈ S` (suspected before). -/
def recvF (S : Fin n → Bool) (ib : View n V) (r : ℕ) (j : Fin n) : Option (Msg n V) :=
  if S j then none else ib r j

/-- The number of processes whose round-`(r+1)` message (not suspected: `Scur`) echoes `m` as the
round-`r` message of `j`. -/
def echoCount (Scur : Fin n → Bool) (ib : View n V) (r : ℕ) (m : Msg n V) (j : Fin n) : ℕ :=
  ((List.finRange n).filter fun k =>
    match recvF Scur ib (r + 1) k with
    | some e => echoMatch r m e j
    | none => false).length

/-- `j`'s round-`r` message is confirmed in round `r + 1` (Bracha–Toueg echo with threshold
`n - t`). `Sprev`, `Scur`: suspected after rounds `r - 1` and `r`. -/
def confirmed (t : ℕ) (Sprev Scur : Fin n → Bool) (ib : View n V) (r : ℕ) (j : Fin n) : Bool :=
  match recvF Sprev ib r j with
  | none => false
  | some m => decide (n - t ≤ echoCount Scur ib r m j)

/-- `susp t ib r j`: `j` is suspected after round `r` (cumulative; nobody is suspected before the
end of round 2). -/
def susp (t : ℕ) (ib : View n V) : ℕ → Fin n → Bool
  | 0 => fun _ => false
  | 1 => fun _ => false
  | r + 2 => fun j => susp t ib (r + 1) j || !confirmed t (susp t ib r) (susp t ib (r + 1)) ib (r + 1) j

/-- The message received from `j` in round `r`, `⊥` if `j` was suspected after round `r - 1`. -/
def recv (t : ℕ) (ib : View n V) (r : ℕ) (j : Fin n) : Option (Msg n V) :=
  recvF (susp t ib (r - 1)) ib r j

/-- The message a correct process with input `x` and view `ib` sends (to everybody) in round `r`.
It only reads rounds `< r` of `ib` (`out_congr`). -/
def out (t : ℕ) (x : V) (ib : View n V) : ℕ → Msg n V
  | 0 => {}
  | 1 => { v1 := some x }
  | 2 => { e2 := fun j => (recv t ib 1 j).bind (·.v1) }
  | 3 => { sus := susp t ib 2, e3 := fun j => (recv t ib 2 j).map (·.e2) }
  | r + 4 => { sus := susp t ib (r + 3), ek := fun j => (recv t ib (r + 3) j).map (·.sus) }

/-! ### Decorating the EIG tree -/

/-- `ℓ` reported in round `r` that it suspects `k` (main part of its round-`r` message). -/
def rep (t : ℕ) (ib : View n V) (r : ℕ) (l k : Fin n) : Bool :=
  match recv t ib r l with
  | some m => m.sus k
  | none => false

/-- `ℓ` reported in some round `3 ≤ r ≤ a` that it suspects `k`. -/
def repBy (t : ℕ) (ib : View n V) (a : ℕ) (l k : Fin n) : Bool :=
  (List.range' 3 (a - 2)).any fun r => rep t ib r l k

/-- `ℓ` reported in round `r` (echo part) that `k` reported that it suspects `j`. -/
def erep (t : ℕ) (ib : View n V) (r : ℕ) (l k j : Fin n) : Bool :=
  match recv t ib r l with
  | some m =>
    match m.ek k with
    | some s => s j
    | none => false
  | none => false

/-- `ℓ` reported in some round `4 ≤ r ≤ a` that `k` reported that it suspects `j`. -/
def erepBy (t : ℕ) (ib : View n V) (a : ℕ) (l k j : Fin n) : Bool :=
  (List.range' 4 (a - 3)).any fun r => erep t ib r l k j

/-- `val` on level 1: the value received from `j` in round 1 (paper: `val(j)`). -/
def val1 (t : ℕ) (ib : View n V) (j : Fin n) : Option V :=
  (recv t ib 1 j).bind (·.v1)

/-- `cval` on level 2: the round-1 value of `j` reported by `k` in round 2 (paper: `cval(jk)`). -/
def cval2 (t : ℕ) (ib : View n V) (k j : Fin n) : Option V :=
  (recv t ib 2 k).bind (·.e2 j)

/-- `val` on the internal levels `2..t` (paper label `y k ℓ` = `ℓ :: k :: _`): `⊤` iff `ℓ` never
reported by round `t` that it suspects `k`. -/
def valB (t : ℕ) (ib : View n V) : List (Fin n) → Bool
  | l :: k :: _ => !repBy t ib t l k
  | _ => false

/-- `val` on the leaves (level `t + 1`): `⊤` iff `ℓ` did not report (by round `t + 1`) that it
suspects `k`. -/
def leafVal (t : ℕ) (ib : View n V) : List (Fin n) → Bool
  | l :: k :: _ => !repBy t ib (t + 1) l k
  | _ => false

/-- `cval` on the levels `≥ 3` (paper label `y j k ℓ` = `ℓ :: k :: j :: _`): `⊤` iff `ℓ` never
reported by round `t + 1` that `k` reported that it suspects `j`. -/
def cvalB (t : ℕ) (ib : View n V) : List (Fin n) → Bool
  | l :: k :: j :: _ => !erepBy t ib (t + 1) l k j
  | _ => false

/-- The strict majority value of a list, if any. -/
def majority {α : Type} [DecidableEq α] (l : List α) : Option α :=
  l.find? fun a => decide (l.length < 2 * l.count a)

/-- The ids `k` such that `k :: x` is a child of `x` (i.e. `k ∉ x`) and `p k` holds. -/
def childIds (x : List (Fin n)) (p : Fin n → Bool) : List (Fin n) :=
  (List.finRange n).filter fun k => !decide (k ∈ x) && p k

/-- `newval` on levels `≥ 2`, computed with fuel `d` = the distance to the leaves. -/
def nvB (t : ℕ) (ib : View n V) : ℕ → List (Fin n) → Bool
  | 0, x => leafVal t ib x
  | d + 1, x =>
    let T := childIds x fun k => nvB t ib d (k :: x)
    decide (n - t - x.length ≤ T.length) &&
      decide (majority (T.map fun k => cvalB t ib (k :: x)) = some true)

/-- `newval(x)` for a label `x` of level `2 ≤ |x| ≤ t + 1`. -/
def newvalB (t : ℕ) (ib : View n V) (x : List (Fin n)) : Bool :=
  nvB t ib (t + 1 - x.length) x

/-- The top set `T` of the level-1 node `[j]`. -/
def top1 (t : ℕ) (ib : View n V) (j : Fin n) : List (Fin n) :=
  childIds [j] fun k => newvalB t ib [k, j]

/-- `newval(j)` on level 1: the strict majority of the `cval(jk)`, `k ∈ T`, if `|T| ≥ n - t - 1`;
`⊥` (`none`) otherwise. For `t = 0` the level-1 nodes are leaves and `newval(j) = val(j)`. -/
def newval1 (t : ℕ) (ib : View n V) (j : Fin n) : Option V :=
  if t = 0 then val1 t ib j
  else if n - t - 1 ≤ (top1 t ib j).length then
    (majority ((top1 t ib j).map fun k => cval2 t ib k j)).join
  else none

/-- The decision (`newval(λ)`): the strict majority of the level-1 new values if it is a
non-`⊥` value, the default value `v0` otherwise. -/
def decision (t : ℕ) (v0 : V) (ib : View n V) : V :=
  match majority ((List.finRange n).map fun j => newval1 t ib j) with
  | some (some v) => v
  | _ => v0

/-! ### Causality: round-`r` messages only depend on rounds `< r` -/

omit [DecidableEq V] in
lemma recvF_congr {S S' : Fin n → Bool} {ib ib' : View n V} {r : ℕ} (hS : S = S')
    (h : ib r = ib' r) (j : Fin n) : recvF S ib r j = recvF S' ib' r j := by
  simp [recvF, hS, h]

lemma susp_congr (t : ℕ) {ib ib' : View n V} :
    ∀ r, (∀ r', 1 ≤ r' → r' ≤ r → ib r' = ib' r') → susp t ib r = susp t ib' r
  | 0, _ => rfl
  | 1, _ => rfl
  | r + 2, h => by
    have h0 := susp_congr t r (fun r' h1 hr' => h r' h1 (by omega))
    have h1 := susp_congr t (r + 1) (fun r' h1 hr' => h r' h1 (by omega))
    funext j
    simp only [susp, confirmed, echoCount, h0, h1,
      recvF_congr rfl (h (r + 1) (by omega) (by omega)),
      recvF_congr rfl (h (r + 1 + 1) (by omega) le_rfl)]
    rfl

lemma recv_congr (t : ℕ) {ib ib' : View n V} {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ r', 1 ≤ r' → r' ≤ r → ib r' = ib' r') (j : Fin n) :
    recv t ib r j = recv t ib' r j := by
  rw [recv, recv, susp_congr t (r - 1) (fun r' h1 hr' => h r' h1 (by omega)),
    recvF_congr rfl (h r hr le_rfl)]

/-- The message sent in round `r` only depends on the rounds `1, …, r - 1` of the view. -/
lemma out_congr (t : ℕ) (x : V) {ib ib' : View n V} {r : ℕ}
    (h : ∀ r', 1 ≤ r' → r' < r → ib r' = ib' r') :
    out t x ib r = out t x ib' r := by
  match r, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, h => simp only [out, recv_congr t (r := 1) le_rfl (fun r' h1 hr' => h r' h1 (by omega))]
  | 3, h => simp only [out, recv_congr t (r := 2) (by omega) (fun r' h1 hr' => h r' h1 (by omega)),
      susp_congr t 2 (fun r' h1 hr' => h r' h1 (by omega))]
  | r + 4, h => simp only [out,
      recv_congr t (r := r + 3) (by omega) (fun r' h1 hr' => h r' h1 (by omega)),
      susp_congr t (r + 3) (fun r' h1 hr' => h r' h1 (by omega))]

/-! ### Executions -/

/-- An execution of the protocol with `t + 1` rounds (synchronous, reliable point-to-point channels,
static Byzantine set `byz`). `view i r j` is the message `i` receives from `j` in round `r`.
A correct sender `j` sends `out t (input j) (view j) r` to everybody (itself included) in every
round `1 ≤ r ≤ t + 1`; messages of Byzantine senders are arbitrary (and may differ per receiver).
Since `out` at round `r` only reads rounds `< r` of the view (`out_congr`), the honest messages are
determined by the earlier rounds; `Bridge.lean` shows that executions are exactly the runs of the
protocol in CSLib's lock-step model. -/
structure Exec (n t : ℕ) (V : Type) [DecidableEq V] where
  /-- The Byzantine processes. -/
  byz : Finset (Fin n)
  /-- The proposals. -/
  input : Fin n → V
  /-- `view i r j`: the message received by `i` from `j` in round `r`. -/
  view : Fin n → View n V
  /-- Correct processes follow the protocol. -/
  honest : ∀ j ∉ byz, ∀ i r, 1 ≤ r → r ≤ t + 1 → view i r j = some (out t (input j) (view j) r)

/-- The decision of process `i` in the execution `E` (default value `v0`). -/
def Exec.decide {t : ℕ} (E : Exec n t V) (v0 : V) (i : Fin n) : V :=
  decision t v0 (E.view i)

end Podc.CubicBitsBA
