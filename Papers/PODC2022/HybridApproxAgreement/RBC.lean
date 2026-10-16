import Papers.PODC2022.HybridApproxAgreement.Spec
import Cslib.Computability.Distributed.Byzantine.PartialSync.Sync

/-!
# The Reliable Broadcast protocol `Π_rBC` (Section 4.1) and a counterexample to Theorem 4.1

`Π_rBC` (after Momose–Ren), code for party `P` with `τ_start = 0`:

1. the sender `S` sends `(propose, v, sig_S(v))` to all;
2. upon receiving the first valid `propose v` and when `τ_now ≥ Δ`: forward it to all;
4. when `τ_now ≥ 2Δ`: if no valid `propose v'` with `v' ≠ v` was received, send `(vote, v, sig_P(v))`;
6. upon holding `n - tₛ` valid votes for the same `v` and when `τ_now ≥ 3Δ`: send the certificate
   `C(v)`, output `v` and terminate.

**Theorem 4.1** claims `(tₛ, tₐ, 3, 1)`-security for all `tₐ ≤ tₛ` with `2 tₛ + tₐ < n`; in particular
`(tₛ, 1)`-Synchronized Consistency: in a synchronous network with `≤ tₛ` corruptions all honest
parties output the same value.

**This is false** whenever `n ≤ 3 tₛ` (the regime `tₛ ≥ n/3` that the paper is about). The checks of
lines 2/4 only detect equivocation for proposals received by time `Δ` (whose forwards arrive by
`2Δ`); a Byzantine sender can deliver *different* proposals to two honest parties *late* (at time
`2Δ`). Both vote immediately, before the conflicting forwards arrive, and the Byzantine parties
complete both vote sets to `n - tₛ`: with `n = 3`, `tₛ = 1`, `tₐ = 0` (so `2 tₛ + tₐ < n`), honest
`P₀`, `P₁` and Byzantine sender `C`, `C` sends `propose 0` to `P₀` and `propose 1` to `P₁` so that
they arrive at `2Δ`, and votes for both values; at `3Δ`, `P₀` holds the votes `{P₀, C}` for `0` and
outputs `0`, `P₁` holds `{P₁, C}` for `1` and outputs `1` (`rbc_not_syncConsistent`).

## Model

`CSLib`'s PSync model with lock-step synchrony (`δ = 0`; time unit = `Δ = 1` tick): a message
produced in the step at time `τ` (after processing the messages delivered at `τ`) is sent at `τ + 1`
and processed by its receivers in their step at time `τ + 1 + (delay)`. The run used is fully
synchronous with zero delay, i.e. every message produced at `kΔ` is processed at `(k+1)Δ` — exactly
the paper's synchronous model with delivery after exactly `Δ`. Signatures are the abstract tokens of
`Cslib.Byzantine.PartialSync.Auth`: a `propose v` message carries the sender's token on `v`, a vote
of `p` on `v` carries `p`'s token, a certificate carries the tokens of its votes. The adversary of the
counterexample only uses the Byzantine sender's own tokens (`Run.AuthValid`).

Parties are `Fin n` (the order of `Fin n` is used to process the messages received at the same time;
irrelevant in the counterexample, where no party receives two proposals at once before voting).
Valid messages are those carrying the required tokens; in the token model every message carries its
tokens by construction, so all received messages are valid.

As a sanity check of the encoding, `rbc_honest_sender`: with an honest sender, all parties output
its value at time `3Δ` (in the synchronous run where the Byzantine party is silent).
-/

open Cslib.Byzantine.PartialSync Finset

namespace HybridApproxAgreement.RBC

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- Messages of one `Π_rBC` instance. -/
inductive Msg (n : ℕ) (V : Type) where
  /-- `(propose, v, sig_S(v))` -/
  | propose (v : V)
  /-- `(vote, v, sig_p(v))` -/
  | vote (p : Fin n) (v : V)
  /-- a certificate `C(v)`: the votes on `v` of the listed parties -/
  | cert (v : V) (C : List (Fin n))
  deriving DecidableEq

/-- Local state of one `Π_rBC` instance. -/
structure St (n : ℕ) (V : Type) where
  /-- the first valid proposal received -/
  first : Option V := none
  /-- a valid proposal different from `first` was received -/
  conflict : Bool := false
  /-- line 3 executed -/
  fwd : Bool := false
  /-- line 4 executed (voted, or declined because of a conflict) -/
  voteDone : Bool := false
  /-- valid votes received: (voter, value) -/
  votes : List (Fin n × V) := []
  /-- output (line 7); the instance has terminated iff this is `some _` -/
  out : Option V := none
  deriving DecidableEq

/-- Processing one received message. -/
def recv (s : St n V) : Msg n V → St n V
  | .propose v => match s.first with
    | none => { s with first := some v }
    | some w => if v = w then s else { s with conflict := true }
  | .vote p v => { s with votes := (p, v) :: s.votes }
  | .cert v C => { s with votes := C.map (fun p => (p, v)) ++ s.votes }

/-- The parties that voted for `v`. -/
def voters (s : St n V) (v : V) : List (Fin n) :=
  (List.finRange n).filter fun p => decide ((p, v) ∈ s.votes)

/-- Values with at least `q = n - tₛ` votes. -/
def certified (q : ℕ) (s : St n V) : List V :=
  (s.votes.map Prod.snd).filter fun v => decide (q ≤ (voters s v).length)

/-- Line 3 (forward), executed when `τ_now ≥ Δ`. -/
def actFwd (Δ now : ℕ) (s : St n V) : St n V × List (Msg n V) :=
  match s.first with
  | some v => if !s.fwd && Δ ≤ now then ({ s with fwd := true }, [.propose v]) else (s, [])
  | none => (s, [])

/-- Line 4 (vote), executed when `τ_now ≥ 2Δ` after the forward. -/
def actVote (Δ now : ℕ) (self : Fin n) (s : St n V) : St n V × List (Msg n V) :=
  match s.first with
  | some v =>
    if s.fwd && !s.voteDone && 2 * Δ ≤ now then
      ({ s with voteDone := true }, if s.conflict then [] else [.vote self v])
    else (s, [])
  | none => (s, [])

/-- Lines 6–7 (certificate, output, terminate), when `τ_now ≥ 3Δ`. -/
def actOut (Δ q now : ℕ) (s : St n V) : St n V × List (Msg n V) :=
  match certified q s with
  | v :: _ => if 3 * Δ ≤ now then ({ s with out := some v }, [.cert v (voters s v)]) else (s, [])
  | [] => (s, [])

/-- One step of the instance at time `now`: process the received messages, then execute the
time-triggered actions. A terminated instance ignores everything. -/
def stepI (Δ q now : ℕ) (self : Fin n) (s : St n V) (ms : List (Msg n V)) :
    St n V × List (Msg n V) :=
  if s.out.isSome then (s, []) else
    let s1 := ms.foldl recv s
    let r2 := actFwd Δ now s1
    let r3 := actVote Δ now self r2.1
    let r4 := actOut Δ q now r3.1
    (r4.1, r2.2 ++ r3.2 ++ r4.2)

/-- A party running one instance: clock, instance state, messages to broadcast at the next tick. -/
structure Node (n : ℕ) (V : Type) where
  clock : ℕ
  st : St n V
  outbox : List (Msg n V)
  deriving DecidableEq

/-- `Π_rBC` with sender `S`, time unit `Δ` and vote threshold `q = n - tₛ`, as a PSync algorithm
(the input of the sender is the value it broadcasts; other inputs are ignored). -/
def alg (Δ q : ℕ) (S : Fin n) : Algorithm (Fin n) (Msg n V) (Node n V) V V where
  init p v := ⟨0, {}, if p = S then [.propose v] else []⟩
  step p s inbox :=
    let r := stepI Δ q s.clock p s.st ((List.finRange n).flatMap inbox)
    ⟨s.clock + 1, r.1, r.2⟩
  send _ s _ := s.outbox
  decide _ s := s.st.out

/-- Signature tokens: the sender's signature on a proposal, a party's signature on a vote. -/
inductive Tok (n : ℕ) (V : Type) where
  | prop (v : V)
  | vote (p : Fin n) (v : V)

/-- The signature structure of the instance with sender `S`. -/
def auth (S : Fin n) : Auth (Fin n) (Msg n V) (Tok n V) where
  signer
    | .prop _ => S
    | .vote p _ => p
  tokens
    | .propose v => {.prop v}
    | .vote p v => {.vote p v}
    | .cert v C => {t | ∃ p ∈ C, t = .vote p v}

/-- `(t, 1)`-Synchronized Consistency of Definition 2.3 (in particular the output-agreement part):
in every synchronous run (`gst = 0`, delays `≤ δ`) with at most `t` corruptions that respects
unforgeability, honest parties do not output different values. -/
def SyncConsistent (Δ q : ℕ) (S : Fin n) (t δ : ℕ) : Prop :=
  ∀ R : Run (Fin n) (Msg n V) V, R.Valid t δ → R.gst = 0 → R.AuthValid (auth S) (alg Δ q S) →
    ∀ p ∉ R.faulty, ∀ p' ∉ R.faulty, ∀ v v',
      R.Decides (alg Δ q S) p v → R.Decides (alg Δ q S) p' v' → v = v'

/-! ### The counterexample: `n = 3`, `tₛ = 1`, `tₐ = 0`, `Δ = 1` -/

/-- The Byzantine sender `C = 2`: proposals `false` to `P₀` and `true` to `P₁` delivered at time
`2Δ = 2`, votes for both values delivered at `3Δ = 3`. -/
def attack : Run (Fin 3) (Msg 3 Bool) Bool where
  faulty := {2}
  inp _ := false
  gst := 0
  byz _ τ p :=
    if τ = 2 then (if p = 0 then [.propose false] else if p = 1 then [.propose true] else [])
    else if τ = 3 then (if p = 0 then [.vote 2 false] else if p = 1 then [.vote 2 true] else [])
    else []
  dl _ τ _ := τ

/-- Instance state of `P₀`/`P₁` after voting (time `3`). -/
def st3 (b : Bool) : St 3 Bool where
  first := some b
  fwd := true
  voteDone := true

/-- Instance state of `P₀`/`P₁` after outputting (time `4`). -/
def st4 (b : Bool) : St 3 Bool where
  first := some b
  conflict := true
  fwd := true
  voteDone := true
  votes := [(2, b), (1, true), (0, false)]
  out := some b

/-- The states of the honest parties `P₀`, `P₁` in the attack, at times `0, …, 4`. -/
def attackSt (τ : ℕ) (p : Fin 3) : Node 3 Bool :=
  match τ with
  | 0 => ⟨0, {}, []⟩
  | 1 => ⟨1, {}, []⟩
  | 2 => ⟨2, {}, []⟩
  | 3 => ⟨3, st3 (decide (p = 1)), [.propose (decide (p = 1)), .vote p (decide (p = 1))]⟩
  | _ => ⟨4, st4 (decide (p = 1)), [.cert (decide (p = 1)) [p, 2]]⟩

theorem attack_inbox (p : Fin 3) (τ : ℕ) (q : Fin 3) :
    attack.inbox (alg 1 2 2) p τ q = attack.out (alg 1 2 2) q τ p :=
  Run.inbox_of_dl_eq _ (fun _ _ _ => rfl) p τ q

/-- The run, computed. -/
theorem attack_st : ∀ τ ≤ 4, ∀ p : Fin 3, p ≠ 2 → attack.st (alg 1 2 2) τ p = attackSt τ p := by
  intro τ hτ
  induction τ with
  | zero => intro p hp; fin_cases p <;> simp_all <;> rfl
  | succ τ ih =>
    intro p hp
    have ih' := ih (by omega)
    rw [Run.st_succ]
    have hin : attack.inbox (alg 1 2 2) p τ = fun q =>
        if q = 2 then attack.byz 2 τ p else (attackSt τ q).outbox := by
      funext q
      rw [attack_inbox]
      by_cases hq : q = 2
      · subst hq; simp [Run.out_of_faulty _ _ (show (2 : Fin 3) ∈ attack.faulty by simp [attack])]
      · rw [Run.out_of_correct _ _ (by simpa [attack] using hq), ih' q hq]
        simp [hq, alg]
    rw [hin, ih' p hp]
    have : τ ≤ 3 := by omega
    interval_cases τ <;> fin_cases p <;> simp_all <;> decide

theorem attack_valid : attack.Valid 1 0 :=
  ⟨by simp [attack], fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => by simp [attack]⟩

/-- The adversary only uses the Byzantine sender's own signatures. -/
theorem attack_authValid : attack.AuthValid (auth 2) (alg 1 2 2) := by
  intro b hb τ r _ m hm x hx
  left
  simp only [attack, mem_singleton] at hb ⊢
  subst hb
  simp only [attack] at hm
  split_ifs at hm <;> simp at hm <;> subst hm <;> simp [auth] at hx <;> subst hx <;> rfl

/-- **Theorem 4.1 is false**: for `n = 3`, `tₛ = 1`, `tₐ = 0` (`tₐ ≤ tₛ`, `2 tₛ + tₐ < n`), `Δ = 1`
and the vote threshold `n - tₛ = 2`, there is a synchronous run with one Byzantine party (the sender)
respecting unforgeability in which the honest parties `P₀` and `P₁` output different values (both at
time `3Δ`). -/
theorem rbc_attack :
    attack.Valid 1 0 ∧ attack.gst = 0 ∧ attack.AuthValid (auth 2) (alg 1 2 2) ∧
      (0 : Fin 3) ∉ attack.faulty ∧ (1 : Fin 3) ∉ attack.faulty ∧
      (alg 1 2 2).decide 0 (attack.st (alg 1 2 2) 4 0) = some false ∧
      (alg 1 2 2).decide 1 (attack.st (alg 1 2 2) 4 1) = some true ∧
      (∀ τ < 4, (alg 1 2 2).decide 0 (attack.st (alg 1 2 2) τ 0) = none ∧
        (alg 1 2 2).decide 1 (attack.st (alg 1 2 2) τ 1) = none) := by
  refine ⟨attack_valid, rfl, attack_authValid, by decide, by decide, ?_, ?_, ?_⟩
  · rw [attack_st 4 le_rfl 0 (by decide)]; rfl
  · rw [attack_st 4 le_rfl 1 (by decide)]; rfl
  · intro τ hτ
    rw [attack_st τ hτ.le 0 (by decide), attack_st τ hτ.le 1 (by decide)]
    interval_cases τ <;> exact ⟨rfl, rfl⟩

theorem rbc_not_syncConsistent : ¬ SyncConsistent (V := Bool) 1 2 (2 : Fin 3) 1 0 := by
  intro h
  obtain ⟨hv, hg, ha, h0, h1, d0, d1, -⟩ := rbc_attack
  exact absurd (h attack hv hg ha 0 h0 1 h1 false true ⟨4, d0⟩ ⟨4, d1⟩) (by decide)

/-! ### Sanity check: honest sender -/

/-- `n = 3`, honest sender `P₀` with input `true`, Byzantine `P₂` silent, zero delays. -/
def honestRun : Run (Fin 3) (Msg 3 Bool) Bool where
  faulty := {2}
  inp _ := true
  gst := 0
  byz _ _ _ := []
  dl _ τ _ := τ

/-- Instance state of `P₀`, `P₁` at time `4` in `honestRun`. -/
def hst4 : St 3 Bool where
  first := some true
  fwd := true
  voteDone := true
  votes := [(1, true), (0, true)]
  out := some true

/-- The states of `P₀`, `P₁` in `honestRun`. -/
def honestSt (τ : ℕ) (p : Fin 3) : Node 3 Bool :=
  match τ with
  | 0 => ⟨0, {}, if p = 0 then [.propose true] else []⟩
  | 1 => ⟨1, { first := some true }, []⟩
  | 2 => ⟨2, { first := some true, fwd := true }, [.propose true]⟩
  | 3 => ⟨3, { first := some true, fwd := true, voteDone := true }, [.vote p true]⟩
  | _ => ⟨4, hst4, [.cert true [0, 1]]⟩

theorem honestRun_st : ∀ τ ≤ 4, ∀ p : Fin 3, p ≠ 2 →
    honestRun.st (alg 1 2 0) τ p = honestSt τ p := by
  intro τ hτ
  induction τ with
  | zero => intro p hp; fin_cases p <;> simp_all <;> rfl
  | succ τ ih =>
    intro p hp
    have ih' := ih (by omega)
    rw [Run.st_succ]
    have hin : honestRun.inbox (alg 1 2 0) p τ = fun q =>
        if q = 2 then [] else (honestSt τ q).outbox := by
      funext q
      rw [Run.inbox_of_dl_eq _ (fun _ _ _ => rfl) p τ q]
      by_cases hq : q = 2
      · subst hq
        rw [Run.out_of_faulty _ _ (show (2 : Fin 3) ∈ honestRun.faulty by simp [honestRun])]
        rfl
      · rw [Run.out_of_correct _ _ (by simpa [honestRun] using hq), ih' q hq]
        simp [hq, alg]
    rw [hin, ih' p hp]
    have : τ ≤ 3 := by omega
    interval_cases τ <;> fin_cases p <;> simp_all <;> decide

/-- With an honest sender, both honest parties output the sender's value at time `3Δ` (state at
`3Δ + 1`), as `(tₛ, 3)`-Synchronized Validity requires: the encoding of `Π_rBC` behaves as intended. -/
theorem rbc_honest_sender : honestRun.Valid 1 0 ∧
    (alg 1 2 0).decide 0 (honestRun.st (alg 1 2 0) 4 0) = some true ∧
    (alg 1 2 0).decide 1 (honestRun.st (alg 1 2 0) 4 1) = some true := by
  refine ⟨⟨by simp [honestRun], fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => by simp [honestRun]⟩,
    ?_, ?_⟩
  · rw [honestRun_st 4 le_rfl 0 (by decide)]; rfl
  · rw [honestRun_st 4 le_rfl 1 (by decide)]; rfl

end HybridApproxAgreement.RBC
