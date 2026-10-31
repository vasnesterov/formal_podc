import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
# Section 4: the generic translation of Figure 2 is unsound

Section 4 claims a translation of every protocol tolerating `f` crash faults into one
tolerating `f` Byzantine faults with the same number of processes, using non-equivocation and
transferable authentication (Figure 2, correctness argument in Appendix B). We model Figure 2
literally and give a crash-tolerant protocol whose translation is **not** Byzantine-tolerant:
with `n = 3` processes and a single Byzantine process, a correct process reaches a state that
no crash execution of the original protocol can reach.

## The translation (Figure 2)

A B-message is `((k, m, R, S), σ_p)` (`TMsg.mk p k m R S`, the signature of `p` being symbolic):
`k` is the sequence number (non-equivocation key), `m` the payload, `R` the B-messages `p`
received (with their own proofs), `S` the B-messages `p` sent before. Upon B-receiving it from
`q`, a process checks (`check`): the signature is `q`'s; `k = |S| + 1`; the messages of `S` are
`q`'s; replaying `q`'s state machine on the inputs `R` from the initial state produces the
outputs `S` followed by `m`; and recursively the same checks for every message in `R`. If all
checks pass, `m` is T-received from `q`, the B-message is added to `R`, and every resulting
T-send `m'` to a set of processes is B-sent as `((k+1, m', R, S), σ)` and added to `S`.

**The gap.** Neither the signed tuple nor the checks mention *recipients*: a message of `R` is
only checked to be authentic and valid, not to have been sent *to* `q`. So a Byzantine process
can feed its own replayed state machine a message that a correct process sent to somebody
else (it learns it, with its signature, from the `R` field of any later message of that
recipient), and its resulting messages pass every check. The paper's own Integrity requirement
(§4.1, "`m` is valid if it corresponds to the output of applying a sequence of valid messages
to the state machine") has the same blind spot, so Appendix B's argument does not exclude it.

## The counterexample (`grantProto`, `n = 3`, `f = 1`)

Process `0` (a server) grants a token to process `1` only. A client that receives the grant
from `0` multicasts `use` to the two other processes; the server records every `use` sender.
In every crash execution the server only ever records `1` (`crash_safe`), since only `1` is ever
granted. In the translated system with Byzantine process `2`:
1. `1` receives the grant `g` and multicasts `u₁ = ((1, use, [g], []), σ₁)` to `0` and `2`;
2. `2` extracts `g` (signed by `0`) from `u₁` and sends `u₂ = ((1, use, [g], []), σ₂)` to `0`;
3. `u₂` passes all checks of `0` (it is exactly what a *correct* `2` would send after receiving
   `g`, `attack_eq_honest`), so the correct server records `2` (`translation_unsafe`).
The adversary respects unforgeability (it signs only as `2` and relays `0`'s signed `g`, which
it has seen) and non-equivocation (it uses key `1` once).
-/

namespace Podc.NonEquivocationLimits.Translation

/-! ### Protocols and their crash executions -/

/-- A crash-model protocol in the format of Section 2.2: a deterministic automaton per process,
with an initial state and initial sends, and a transition per received message. Sends are
`(message, recipients)` pairs. -/
structure Protocol (P V St : Type) where
  /-- Initial state and initial T-sends. -/
  start : P → St × List (V × List P)
  /-- `step p σ q v`: process `p` in state `σ` receives `v` from `q`. -/
  step : P → St → P → V → St × List (V × List P)

variable {P V St : Type} [DecidableEq P] [DecidableEq V]

section crash

/-- A configuration of the crash model: states, in-flight messages `(from, to, payload)`,
crashed processes. -/
structure CConfig (P V St : Type) where
  st : P → St
  net : List (P × P × V)
  crashed : List P

/-- The initial in-flight messages of the processes in `ps`. -/
def startNet (Pr : Protocol P V St) (ps : List P) : List (P × P × V) :=
  ps.flatMap fun p => (Pr.start p).2.flatMap fun o => o.2.map fun d => (p, d, o.1)

/-- One step of the crash model. Messages are delivered in any order (also from crashed
senders), may be lost, and processes may crash at any time. -/
inductive CStep (Pr : Protocol P V St) : CConfig P V St → CConfig P V St → Prop
  | deliver (c : CConfig P V St) (i : ℕ) (e : P × P × V) (he : c.net[i]? = some e)
      (halive : e.2.1 ∉ c.crashed) :
      CStep Pr c { c with
        st := Function.update c.st e.2.1 (Pr.step e.2.1 (c.st e.2.1) e.1 e.2.2).1
        net := c.net.eraseIdx i ++
          (Pr.step e.2.1 (c.st e.2.1) e.1 e.2.2).2.flatMap fun o => o.2.map fun d => (e.2.1, d, o.1) }
  | drop (c : CConfig P V St) (i : ℕ) : CStep Pr c { c with net := c.net.eraseIdx i }
  | crash (c : CConfig P V St) (p : P) : CStep Pr c { c with crashed := p :: c.crashed }

/-- Reachable configurations of the crash model (all processes `ps` start). -/
inductive CReach (Pr : Protocol P V St) (ps : List P) : CConfig P V St → Prop
  | init : CReach Pr ps ⟨fun p => (Pr.start p).1, startNet Pr ps, []⟩
  | step {c c'} : CReach Pr ps c → CStep Pr c c' → CReach Pr ps c'

end crash

/-! ### The translation -/

/-- B-messages `((k, m, R, S), σ_signer)` of Figure 2. -/
inductive TMsg (P V : Type) where
  | mk (signer : P) (k : ℕ) (m : V) (R S : List (TMsg P V))

namespace TMsg

/-- The signer. -/
def signer : TMsg P V → P | mk p _ _ _ _ => p
/-- The key (sequence number). -/
def k : TMsg P V → ℕ | mk _ k _ _ _ => k
/-- The payload. -/
def m : TMsg P V → V | mk _ _ m _ _ => m

mutual
/-- Decidable equality of B-messages. -/
def decEq : (a b : TMsg P V) → Decidable (a = b)
  | .mk p k m R S, .mk p' k' m' R' S' =>
    if hp : p = p' then if hk : k = k' then if hm : m = m' then
      match decEqList R R', decEqList S S' with
      | isTrue hR, isTrue hS => isTrue (by subst hp hk hm hR hS; rfl)
      | isFalse hR, _ => isFalse (by intro h; cases h; exact hR rfl)
      | _, isFalse hS => isFalse (by intro h; cases h; exact hS rfl)
    else isFalse (by intro h; cases h; exact hm rfl)
    else isFalse (by intro h; cases h; exact hk rfl)
    else isFalse (by intro h; cases h; exact hp rfl)
/-- Decidable equality of lists of B-messages. -/
def decEqList : (a b : List (TMsg P V)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by simp)
  | _ :: _, [] => isFalse (by simp)
  | a :: as, b :: bs =>
    match decEq a b, decEqList as bs with
    | isTrue h, isTrue h' => isTrue (by rw [h, h'])
    | isFalse h, _ => isFalse (by intro e; cases e; exact h rfl)
    | _, isFalse h' => isFalse (by intro e; cases e; exact h' rfl)
end

instance : DecidableEq (TMsg P V) := decEq

mutual
/-- All signed tuples contained in a B-message (itself, and recursively its `R` and `S`). -/
def subterms : TMsg P V → List (TMsg P V)
  | t@(.mk _ _ _ R S) => t :: (subtermsList R ++ subtermsList S)
/-- `subterms` of a list. -/
def subtermsList : List (TMsg P V) → List (TMsg P V)
  | [] => []
  | t :: ts => subterms t ++ subtermsList ts
end

end TMsg

/-- Replaying `p`'s state machine on a sequence of inputs `(sender, payload)` from its initial
state: the final state and the sequence of produced payloads. -/
def replay (Pr : Protocol P V St) (p : P) (inputs : List (P × V)) : St × List V :=
  inputs.foldl (fun acc i =>
      let r := Pr.step p acc.1 i.1 i.2
      (r.1, acc.2 ++ r.2.map Prod.fst))
    ((Pr.start p).1, (Pr.start p).2.map Prod.fst)

mutual
/-- **The checks of Figure 2** on a B-message received from `q`: the signature is `q`'s;
`k = |S| + 1`; `S` consists of `q`'s messages; replaying `q`'s state machine on the inputs `R`
yields the outputs `S` followed by `m`; recursively, every message of `R` passes the checks
(as a message from its signer). -/
def check (Pr : Protocol P V St) (q : P) : TMsg P V → Bool
  | .mk p k m R S =>
    decide (p = q) && decide (k = S.length + 1) && S.all (fun x => decide (x.signer = p)) &&
      ((S.map TMsg.m) ++ [m]).isPrefixOf (replay Pr p (R.map fun r => (r.signer, r.m))).2 &&
      checkAll Pr R
/-- `check` for every message of a list, each as a message from its signer. -/
def checkAll (Pr : Protocol P V St) : List (TMsg P V) → Bool
  | [] => true
  | r :: rs => check Pr r.signer r && checkAll Pr rs
end

/-- Local state of a translated process: the state of the original state machine, the key
counter `k`, received messages `R`, sent messages `S`. -/
structure LState (P V St : Type) where
  σ : St
  k : ℕ
  R : List (TMsg P V)
  S : List (TMsg P V)

/-- T-send (Figure 2, second handler): each T-send of `v` to the recipients `ds` increments `k`,
B-sends `((k, v, R, S), σ_p)` to `ds` and adds it to `S`. Returns the B-sends
`(recipient, message)`. -/
def tsend (p : P) : LState P V St → List (V × List P) → LState P V St × List (P × TMsg P V)
  | st, [] => (st, [])
  | st, (v, ds) :: rest =>
    let msg := TMsg.mk p (st.k + 1) v st.R st.S
    let r := tsend p { st with k := st.k + 1, S := st.S ++ [msg] } rest
    (r.1, ds.map (fun d => (d, msg)) ++ r.2)

/-- Start of a translated process. -/
def tstart (Pr : Protocol P V St) (p : P) : LState P V St × List (P × TMsg P V) :=
  tsend p ⟨(Pr.start p).1, 0, [], []⟩ (Pr.start p).2

/-- B-receive (Figure 2, first handler) of `tm` from `q` at process `p`: if the checks pass,
T-receive the payload, record `tm` in `R`, and T-send the outputs. -/
def trecv (Pr : Protocol P V St) (p : P) (st : LState P V St) (q : P) (tm : TMsg P V) :
    LState P V St × List (P × TMsg P V) :=
  if check Pr q tm then
    let r := Pr.step p st.σ q tm.m
    tsend p { st with σ := r.1, R := st.R ++ [tm] } r.2
  else (st, [])

section byzantine

/-- Configuration of the translated system with Byzantine processes: local states, in-flight
B-messages `(from, to, message)`, messages delivered to Byzantine processes (`seen`), signed
tuples produced by Byzantine processes (`byzOut`). -/
structure TConfig (P V St : Type) where
  loc : P → LState P V St
  net : List (P × P × TMsg P V)
  seen : List (TMsg P V)
  byzOut : List (TMsg P V)

/-- Initial in-flight messages of the correct processes `ps`. -/
def tstartNet (Pr : Protocol P V St) (ps : List P) : List (P × P × TMsg P V) :=
  ps.flatMap fun p => (tstart Pr p).2.map fun e => (p, e)

/-- Unforgeability: every signed tuple in `tm` is signed by a Byzantine process or was seen (as
part of a message delivered to a Byzantine process). -/
def Unforged (F : List P) (seen : List (TMsg P V)) (tm : TMsg P V) : Prop :=
  ∀ x ∈ tm.subterms, x.signer ∈ F ∨ x ∈ TMsg.subtermsList seen

/-- Non-equivocation: a Byzantine signer never signs two different tuples with the same key. -/
def NonEquiv (F : List P) (byzOut : List (TMsg P V)) (tm : TMsg P V) : Prop :=
  ∀ x ∈ tm.subterms, x.signer ∈ F →
    ∀ y ∈ byzOut ++ tm.subterms, y.signer = x.signer → y.k = x.k → y = x

/-- Steps of the translated system with Byzantine set `F`. -/
inductive TStep (Pr : Protocol P V St) (F : List P) : TConfig P V St → TConfig P V St → Prop
  /-- A correct process B-receives an in-flight message and runs the handler of Figure 2. -/
  | deliver (c : TConfig P V St) (i : ℕ) (e : P × P × TMsg P V) (he : c.net[i]? = some e)
      (hp : e.2.1 ∉ F) :
      TStep Pr F c { c with
        loc := Function.update c.loc e.2.1 (trecv Pr e.2.1 (c.loc e.2.1) e.1 e.2.2).1
        net := c.net.eraseIdx i ++
          (trecv Pr e.2.1 (c.loc e.2.1) e.1 e.2.2).2.map fun d => (e.2.1, d) }
  /-- A Byzantine process receives an in-flight message. -/
  | deliverByz (c : TConfig P V St) (i : ℕ) (e : P × P × TMsg P V) (he : c.net[i]? = some e)
      (hp : e.2.1 ∈ F) :
      TStep Pr F c { c with net := c.net.eraseIdx i, seen := c.seen ++ [e.2.2] }
  /-- A Byzantine process `b` B-sends any unforged, non-equivocating message to `p`. -/
  | inject (c : TConfig P V St) (b p : P) (tm : TMsg P V) (hb : b ∈ F)
      (hu : Unforged F c.seen tm) (hne : NonEquiv F c.byzOut tm) :
      TStep Pr F c { c with
        net := c.net ++ [(b, p, tm)]
        byzOut := c.byzOut ++ tm.subterms.filter fun x => decide (x.signer ∈ F) }

/-- Reachable configurations of the translated system (`ps`: all processes). -/
inductive TReach (Pr : Protocol P V St) (ps F : List P) : TConfig P V St → Prop
  | init : TReach Pr ps F
      ⟨fun p => (tstart Pr p).1, tstartNet Pr (ps.filter fun p => decide (p ∉ F)), [], []⟩
  | step {c c'} : TReach Pr ps F c → TStep Pr F c c' → TReach Pr ps F c'

end byzantine

/-! ### The counterexample -/

/-- Payloads of the grant protocol. -/
inductive GMsg
  | grant
  | use
  deriving DecidableEq, Repr

/-- States of the grant protocol: whether the process was granted, and (for the server) the
list of processes that announced `use`. -/
structure GState where
  granted : Bool
  served : List (Fin 3)
  deriving DecidableEq, Repr

/-- The other two processes. -/
def others (p : Fin 3) : List (Fin 3) := (List.finRange 3).filter fun q => q ≠ p

/-- **The grant protocol.** Server `0` grants to `1` only. A client granted by `0` multicasts
`use` to the two others. The server records the senders of `use`. -/
def grantProto : Protocol (Fin 3) GMsg GState where
  start p := if p = 0 then (⟨false, []⟩, [(.grant, [1])]) else (⟨false, []⟩, [])
  step p σ q v := match v with
    | .grant => if p ≠ 0 ∧ q = 0 ∧ σ.granted = false then
        ({ σ with granted := true }, [(.use, others p)]) else (σ, [])
    | .use => if p = 0 then ({ σ with served := σ.served ++ [q] }, []) else (σ, [])

/-- Invariant of the crash executions of `grantProto`. -/
def CInv (c : CConfig (Fin 3) GMsg GState) : Prop :=
  (∀ e ∈ c.net, e.2.2 = .grant → e.1 = 0 ∧ e.2.1 = 1) ∧ (∀ e ∈ c.net, e.2.2 = .use → e.1 ≠ 2) ∧
    (c.st 2).granted = false ∧ 2 ∉ (c.st 0).served

theorem cinv_init : CInv ⟨fun p => (grantProto.start p).1, startNet grantProto (List.finRange 3), []⟩ := by
  unfold CInv; decide

theorem cinv_step {c c' : CConfig (Fin 3) GMsg GState} (h : CInv c)
    (hs : CStep grantProto c c') : CInv c' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases hs with
  | drop i =>
    exact ⟨fun e he => h1 e (List.mem_of_mem_eraseIdx he),
      fun e he => h2 e (List.mem_of_mem_eraseIdx he), h3, h4⟩
  | crash p => exact ⟨h1, h2, h3, h4⟩
  | deliver i e he halive =>
    obtain ⟨q, p, v⟩ := e
    have hmem : (q, p, v) ∈ c.net := List.mem_of_getElem? he
    cases v with
    | grant =>
      obtain ⟨rfl, rfl⟩ := h1 _ hmem rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro e he
        simp only [List.mem_append] at he
        rcases he with he | he
        · exact h1 e (List.mem_of_mem_eraseIdx he)
        · simp only [grantProto] at he
          split_ifs at he
          · simp [others, List.finRange] at he
            rcases he with rfl | rfl <;> simp
          · simp at he
      · intro e he
        simp only [List.mem_append] at he
        rcases he with he | he
        · exact h2 e (List.mem_of_mem_eraseIdx he)
        · simp only [grantProto] at he
          split_ifs at he
          · simp [others, List.finRange] at he
            rcases he with rfl | rfl <;> simp
          · simp at he
      · simpa [Function.update_of_ne (show (2 : Fin 3) ≠ 1 by decide)] using h3
      · simpa [Function.update_of_ne (show (0 : Fin 3) ≠ 1 by decide)] using h4
    | use =>
      have hq := h2 _ hmem rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro e he
        simp only [List.mem_append] at he
        rcases he with he | he
        · exact h1 e (List.mem_of_mem_eraseIdx he)
        · simp only [grantProto] at he; split_ifs at he <;> simp at he
      · intro e he
        simp only [List.mem_append] at he
        rcases he with he | he
        · exact h2 e (List.mem_of_mem_eraseIdx he)
        · simp only [grantProto] at he; split_ifs at he <;> simp at he
      · by_cases hp : p = 2
        · subst hp; simpa [grantProto] using h3
        · simpa [Function.update_of_ne (Ne.symm hp)] using h3
      · by_cases hp : p = 0
        · subst hp; simp [grantProto, h4]; exact Ne.symm hq
        · simpa [Function.update_of_ne (Ne.symm hp)] using h4

/-- **The grant protocol is safe in the crash model**: in every execution (any crashes, any
message order, any losses), the server never records process `2`. -/
theorem crash_safe {c : CConfig (Fin 3) GMsg GState}
    (hc : CReach grantProto (List.finRange 3) c) : 2 ∉ (c.st 0).served := by
  have : CInv c := by
    induction hc with
    | init => exact cinv_init
    | step _ hs ih => exact cinv_step ih hs
  exact this.2.2.2

section attack

/-- The grant B-message of the server. -/
def g : TMsg (Fin 3) GMsg := .mk 0 1 .grant [] []
/-- The `use` B-message of the correct client `1`. -/
def u₁ : TMsg (Fin 3) GMsg := .mk 1 1 .use [g] []
/-- The `use` B-message forged by the Byzantine client `2` from `g`. -/
def u₂ : TMsg (Fin 3) GMsg := .mk 2 1 .use [g] []

/-- The attack message passes the checks of Figure 2. -/
theorem check_u₂ : check grantProto 2 u₂ = true := by decide

/-- The attack message is exactly what the translated code of a *correct* process `2` would
B-send after B-receiving `g` from `0`. Its signed tuple equals that of the honest `u₁`, except for
the signer, so any check that does not look at the recipients of the replayed inputs and
accepts `u₁` from `1` also accepts `u₂` from `2`. -/
theorem attack_eq_honest :
    (trecv grantProto 2 (tstart grantProto 2).1 0 g).2 = [(0, u₂), (1, u₂)] := by decide

/-- Configurations of the attack. -/
def c₀ : TConfig (Fin 3) GMsg GState :=
  ⟨fun p => (tstart grantProto p).1,
    tstartNet grantProto ((List.finRange 3).filter fun p => decide (p ∉ [2])), [], []⟩

theorem c₀_net : c₀.net = [(0, 1, g)] := by decide

/-- Step 1: client `1` receives the grant. -/
def c₁ : TConfig (Fin 3) GMsg GState :=
  { c₀ with
    loc := Function.update c₀.loc 1 (trecv grantProto 1 (c₀.loc 1) 0 g).1
    net := c₀.net.eraseIdx 0 ++ (trecv grantProto 1 (c₀.loc 1) 0 g).2.map fun d => (1, d) }

theorem c₁_net : c₁.net = [(1, 0, u₁), (1, 2, u₁)] := by decide

/-- Step 2: the Byzantine client `2` receives `u₁`. -/
def c₂ : TConfig (Fin 3) GMsg GState :=
  { c₁ with net := c₁.net.eraseIdx 1, seen := c₁.seen ++ [u₁] }

/-- Step 3: process `2` sends `u₂` to the server. -/
def c₃ : TConfig (Fin 3) GMsg GState :=
  { c₂ with
    net := c₂.net ++ [(2, 0, u₂)]
    byzOut := c₂.byzOut ++ u₂.subterms.filter fun x => decide (x.signer ∈ [2]) }

theorem c₃_net : c₃.net = [(1, 0, u₁), (2, 0, u₂)] := by decide

/-- Step 4: the server receives `u₂`. -/
def c₄ : TConfig (Fin 3) GMsg GState :=
  { c₃ with
    loc := Function.update c₃.loc 0 (trecv grantProto 0 (c₃.loc 0) 2 u₂).1
    net := c₃.net.eraseIdx 1 ++ (trecv grantProto 0 (c₃.loc 0) 2 u₂).2.map fun d => (0, d) }

theorem reach_c₄ : TReach grantProto (List.finRange 3) [2] c₄ := by
  have r₀ : TReach grantProto (List.finRange 3) [2] c₀ := TReach.init
  have r₁ : TReach grantProto (List.finRange 3) [2] c₁ :=
    r₀.step (TStep.deliver c₀ 0 (0, 1, g) (by rw [c₀_net]; rfl) (by decide))
  have r₂ : TReach grantProto (List.finRange 3) [2] c₂ :=
    r₁.step (TStep.deliverByz c₁ 1 (1, 2, u₁) (by rw [c₁_net]; rfl) (by decide))
  have r₃ : TReach grantProto (List.finRange 3) [2] c₃ :=
    r₂.step (TStep.inject c₂ 2 0 u₂ (by decide) (by unfold Unforged; decide)
      (by unfold NonEquiv; decide))
  exact r₃.step (TStep.deliver c₃ 1 (2, 0, u₂) (by rw [c₃_net]; rfl) (by decide))

/-- In the attack, the correct server has recorded the Byzantine process `2`. -/
theorem c₄_served : 2 ∈ ((c₄.loc 0).σ).served := by decide

end attack

/-- **The translation of Section 4 (Figure 2) is unsound.** The grant protocol never lets the
server record process `2` in any crash execution (any number of crashes), but its translation
does, with `n = 3 = 2f + 1` processes and the single Byzantine process `2` (which respects
unforgeability and non-equivocation); the server `0` is correct. -/
theorem translation_unsafe :
    (∀ c, CReach grantProto (List.finRange 3) c → 2 ∉ (c.st 0).served) ∧
      ∃ c, TReach grantProto (List.finRange 3) [2] c ∧ (0 : Fin 3) ∉ [2] ∧
        2 ∈ ((c.loc 0).σ).served :=
  ⟨fun _ hc => crash_safe hc, c₄, reach_c₄, by decide, c₄_served⟩

end Podc.NonEquivocationLimits.Translation
