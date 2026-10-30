import Mathlib

/-!
# The hedged two-party swap (§5.2 of [Xue–Herlihy 2021])

Y. Xue, M. Herlihy, *Hedging Against Sore Loser Attacks in Cross-Chain Transactions*, PODC 2021
(arXiv:2105.06322), §5.2, Figure 1.

Alice owns an asset on the apricot chain, Bob one on the banana chain. Premiums `pa pb : ℕ`:
Alice deposits `pa + pb` on Bob's banana contract, Bob deposits `pb` on Alice's apricot contract.

## Model

* Synchronous, discrete time `ℕ` in units of `Δ`; conforming parties act in lock-step: a reaction
  to an event visible at time `t` takes effect at time `t + 1`. Deadlines are inclusive.
* An execution is a record `Exec` of the times of the (accepted) contract events, `none` meaning
  "never happened / rejected":
  `aP` Alice's premium (deadline 1), `bP` Bob's premium (2), `aE` Alice escrows her principal on
  apricot (3), `bE` Bob escrows on banana (4), `aR` Alice redeems the banana principal by sending
  the secret `s` (5, needs `bE`), `bR` Bob redeems the apricot principal (6, needs `aE` and `s`);
  `sK` is the time at which `s` becomes known to Bob (Alice's redemption reveals it).
* `Exec.Valid`: the contracts' acceptance rules; they bind every party.
* `AliceCompliant`, `BobCompliant`: the protocol rules; a deviating party is otherwise arbitrary
  (Byzantine, within what the contracts accept). The safety/hedging theorems quantify over all
  valid records in which one given party is compliant.
* Compliance is stated directly on accepted events when the protocol step is guaranteed to be
  accepted (e.g. compliant Alice's redemption at `bE + 1 ≤ 5`).
* Interpretation of the protocol (the paper's description of the swap phase is brief): compliant
  Alice redeems Bob's principal at `bE + 1` **whenever** Bob escrowed, even if she did not escrow
  herself, and reveals `s` only through that redemption call. Under the alternative reading
  "Alice redeems only if she escrowed", Alice is not hedged: see `alt_reading_alice_loses`.
  Compliant Bob redeems as soon as he knows `s` and sees Alice's escrow, i.e. at
  `max aE sK + 1` (the paper's "within 3Δ Bob learns s, he forwards s").

## Payoff rules (§5.2, items (1), (2))

* banana: if `aP`: if `bE` and not `aR`, Alice's premium `pa + pb` goes to Bob, else refunded;
* apricot: if `bP`: if `aE` and not `bR`, Bob's premium `pb` goes to Alice, else refunded;
* principals: `bE ∧ aR` ⇒ Bob's asset to Alice; `aE ∧ bR` ⇒ Alice's asset to Bob; else refunds.
-/

namespace Podc.SoreLoserHedging.TwoParty

/-- Times of the contract events of one execution (`none` = never happened / rejected). -/
structure Exec where
  /-- Alice deposits her premium `pa + pb` on the banana contract. -/
  aP : Option ℕ
  /-- Bob deposits his premium `pb` on the apricot contract. -/
  bP : Option ℕ
  /-- Alice escrows her principal on the apricot contract. -/
  aE : Option ℕ
  /-- Bob escrows his principal on the banana contract. -/
  bE : Option ℕ
  /-- Alice redeems Bob's principal (sending the secret `s`). -/
  aR : Option ℕ
  /-- The time at which the secret `s` becomes known to Bob. -/
  sK : Option ℕ
  /-- Bob redeems Alice's principal (sending `s`). -/
  bR : Option ℕ
  deriving DecidableEq

/-- The acceptance rules of the two contracts (binding for everyone). -/
structure Exec.Valid (x : Exec) : Prop where
  aP_le : ∀ t, x.aP = some t → t ≤ 1
  bP_le : ∀ t, x.bP = some t → t ≤ 2
  aE_le : ∀ t, x.aE = some t → t ≤ 3
  bE_le : ∀ t, x.bE = some t → t ≤ 4
  /-- Alice's redemption needs Bob's escrow and the deadline `5Δ`. -/
  aR_ok : ∀ t, x.aR = some t → t ≤ 5 ∧ ∃ e, x.bE = some e ∧ e ≤ t
  /-- Alice's redemption publishes `s`. -/
  aR_reveals : ∀ t, x.aR = some t → ∃ k, x.sK = some k ∧ k ≤ t
  /-- Bob's redemption needs Alice's escrow, the secret, and the deadline `6Δ`. -/
  bR_ok : ∀ t, x.bR = some t →
    t ≤ 6 ∧ (∃ a, x.aE = some a ∧ a ≤ t) ∧ ∃ k, x.sK = some k ∧ k ≤ t

/-- The protocol rules for Alice. -/
structure AliceCompliant (x : Exec) : Prop where
  premium : x.aP = some 1
  escrow_of : ∀ b, x.bP = some b → x.aE = some (b + 1)
  escrow_only : ∀ a, x.aE = some a → ∃ b, x.bP = some b
  /-- Alice redeems as soon as Bob's escrow is visible (always accepted: `e + 1 ≤ 5`). -/
  redeem : ∀ e, x.bE = some e → x.aR = some (e + 1)
  /-- Alice reveals `s` only through her redemption call. -/
  reveal_only : ∀ k, x.sK = some k → ∃ e, x.bE = some e ∧ k = e + 1

/-- The protocol rules for Bob. -/
structure BobCompliant (x : Exec) : Prop where
  premium_of : ∀ a, x.aP = some a → x.bP = some (a + 1)
  premium_only : ∀ b, x.bP = some b → ∃ a, x.aP = some a
  escrow_of : ∀ a b, x.aE = some a → x.bP = some b → x.bE = some (max a b + 1)
  escrow_only : ∀ e, x.bE = some e → (∃ a, x.aE = some a) ∧ ∃ b, x.bP = some b
  /-- Bob redeems as soon as he knows `s` and sees Alice's escrow (if still before `6Δ`). -/
  redeem : ∀ a k, x.aE = some a → x.sK = some k → max a k + 1 ≤ 6 →
    x.bR = some (max a k + 1)

/-! ### Payoffs -/

/-- The banana contract awards Alice's premium `pa + pb` to Bob. -/
def premiumAliceToBob (x : Exec) : Bool := x.aP.isSome && x.bE.isSome && x.aR.isNone

/-- The apricot contract awards Bob's premium `pb` to Alice. -/
def premiumBobToAlice (x : Exec) : Bool := x.bP.isSome && x.aE.isSome && x.bR.isNone

/-- Bob's principal is transferred to Alice. -/
def bobPrincipalToAlice (x : Exec) : Bool := x.bE.isSome && x.aR.isSome

/-- Alice's principal is transferred to Bob. -/
def alicePrincipalToBob (x : Exec) : Bool := x.aE.isSome && x.bR.isSome

/-- Alice's net premium: what she receives minus what she pays. -/
def aliceNet (pa pb : ℕ) (x : Exec) : ℤ :=
  (if premiumBobToAlice x then (pb : ℤ) else 0) -
    (if premiumAliceToBob x then (pa + pb : ℤ) else 0)

/-- Bob's net premium: what he receives minus what he pays. -/
def bobNet (pa pb : ℕ) (x : Exec) : ℤ :=
  (if premiumAliceToBob x then (pa + pb : ℤ) else 0) -
    (if premiumBobToAlice x then (pb : ℤ) else 0)

lemma bobNet_eq_neg (pa pb : ℕ) (x : Exec) : bobNet pa pb x = -aliceNet pa pb x := by
  unfold bobNet aliceNet; ring

/-! ### Basic consequences -/

/-- Compliant Alice never pays her premium: whenever Bob escrows, she redeems. -/
lemma AliceCompliant.not_premiumAliceToBob {x : Exec} (h : AliceCompliant x) :
    premiumAliceToBob x = false := by
  unfold premiumAliceToBob
  cases hb : x.bE with
  | none => simp
  | some e => simp [h.redeem e hb]

/-- If compliant Bob escrowed and Alice redeemed, then Bob redeems too. -/
lemma BobCompliant.bR_isSome {x : Exec} (hv : x.Valid) (h : BobCompliant x) {e r : ℕ}
    (he : x.bE = some e) (hr : x.aR = some r) : x.bR.isSome := by
  obtain ⟨⟨a, ha⟩, -⟩ := h.escrow_only e he
  obtain ⟨k, hk, hkr⟩ := hv.aR_reveals r hr
  have := hv.aE_le a ha
  have := (hv.aR_ok r hr).1
  rw [h.redeem a k ha hk (by omega)]; rfl

/-! ### Liveness -/

/-- §5.2, liveness: if both parties are compliant, the principals are swapped and both premiums
are refunded. (The concrete schedule is `aP = 1, bP = 2, aE = 3, bE = 4, aR = 5, bR = 6`.) -/
theorem liveness {x : Exec} (hv : x.Valid) (ha : AliceCompliant x) (hb : BobCompliant x) :
    bobPrincipalToAlice x = true ∧ alicePrincipalToBob x = true ∧
      premiumAliceToBob x = false ∧ premiumBobToAlice x = false := by
  have hbP := hb.premium_of 1 ha.premium
  have haE := ha.escrow_of 2 hbP
  have hbE := hb.escrow_of 3 2 haE hbP
  have haR := ha.redeem _ hbE
  obtain ⟨k, hk, -⟩ := hv.aR_reveals _ haR
  obtain ⟨e, he, rfl⟩ := ha.reveal_only k hk
  rw [hbE] at he
  cases he
  have hbR := hb.redeem 3 _ haE hk (by decide)
  simp [bobPrincipalToAlice, alicePrincipalToBob, premiumAliceToBob, premiumBobToAlice, hbE,
    haR, haE, hbR]

/-! ### Safety -/

/-- §5.2, safety for Alice: if compliant Alice's principal is transferred to Bob, she receives
Bob's principal (whatever Bob does). -/
theorem safety_alice {x : Exec} (hv : x.Valid) (ha : AliceCompliant x)
    (h : alicePrincipalToBob x = true) : bobPrincipalToAlice x = true := by
  simp only [alicePrincipalToBob, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨-, t, ht⟩ := h
  obtain ⟨-, -, k, hk, -⟩ := hv.bR_ok t ht
  obtain ⟨e, he, -⟩ := ha.reveal_only k hk
  simp [bobPrincipalToAlice, he, ha.redeem e he]

/-- §5.2, safety for Bob: if compliant Bob's principal is transferred to Alice, he receives
Alice's principal (whatever Alice does). -/
theorem safety_bob {x : Exec} (hv : x.Valid) (hb : BobCompliant x)
    (h : bobPrincipalToAlice x = true) : alicePrincipalToBob x = true := by
  simp only [bobPrincipalToAlice, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨e, he⟩, r, hr⟩ := h
  obtain ⟨⟨a, ha⟩, -⟩ := hb.escrow_only e he
  simp [alicePrincipalToBob, ha, hb.bR_isSome hv he hr]

/-! ### Hedging (Definition 1) -/

/-- A compliant Alice never loses premium. -/
theorem aliceNet_nonneg {x : Exec} (ha : AliceCompliant x) (pa pb : ℕ) :
    0 ≤ aliceNet pa pb x := by
  unfold aliceNet
  rw [ha.not_premiumAliceToBob]
  split <;> simp

/-- Definition 1 for Alice: if compliant Alice escrows and her principal is not redeemed, she
receives Bob's premium `pb` (and pays nothing): her net premium is exactly `pb`. -/
theorem hedged_alice {x : Exec} (ha : AliceCompliant x) (pa pb : ℕ) (haE : x.aE.isSome)
    (hbR : x.bR = none) : aliceNet pa pb x = pb := by
  obtain ⟨a, haa⟩ := Option.isSome_iff_exists.1 haE
  obtain ⟨b, hb⟩ := ha.escrow_only a haa
  unfold aliceNet
  rw [ha.not_premiumAliceToBob]
  simp [premiumBobToAlice, hb, haa, hbR]

/-- A compliant Bob never loses premium. -/
theorem bobNet_nonneg {x : Exec} (hv : x.Valid) (hb : BobCompliant x) (pa pb : ℕ) :
    0 ≤ bobNet pa pb x := by
  unfold bobNet
  by_cases hp : premiumBobToAlice x = true
  · -- Bob pays `pb`: then Alice escrowed and Bob did not redeem, so Alice pays `pa + pb`.
    simp only [premiumBobToAlice, Bool.and_eq_true, Option.isSome_iff_exists,
      Option.isNone_iff_eq_none] at hp
    obtain ⟨⟨⟨b, hbP⟩, a, haE⟩, hbR⟩ := hp
    obtain ⟨a', haP⟩ := hb.premium_only b hbP
    have hbE := hb.escrow_of a b haE hbP
    have hq : premiumAliceToBob x = true := by
      cases haR : x.aR with
      | none => simp [premiumAliceToBob, haP, hbE, haR]
      | some r => simpa [hbR] using hb.bR_isSome hv hbE haR
    simp only [hq, ite_true]
    split_ifs <;> omega
  · simp only [Bool.not_eq_true] at hp
    simp only [hp, Bool.false_eq_true, ite_false]
    split_ifs <;> omega

/-- Definition 1 for Bob: if compliant Bob escrows and his principal is not redeemed, his net
premium is at least `pa` (exactly `pa` if he did not redeem Alice's principal, `pa + pb`
otherwise). -/
theorem hedged_bob {x : Exec} (hb : BobCompliant x) (pa pb : ℕ) (hbE : x.bE.isSome)
    (haR : x.aR = none) : (pa : ℤ) ≤ bobNet pa pb x := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hbE
  obtain ⟨-, b, hbP⟩ := hb.escrow_only e he
  obtain ⟨a, haP⟩ := hb.premium_only b hbP
  have hq : premiumAliceToBob x = true := by simp [premiumAliceToBob, haP, he, haR]
  unfold bobNet
  simp only [hq, ite_true]
  split_ifs <;> omega

/-! ### The paper's two sentences on who pays whom -/

/-- §5.2: "If Alice is the first to omit a step after Bob escrows his principal, she will pay Bob
`pa + pb`, and Bob will pay Alice `pb`." Formally: Bob compliant, Bob escrowed, and Alice never
releases `s` (so she does not redeem); then both premiums are forfeited and Bob's net
compensation is `pa`. (If Alice leaks `s` without redeeming, Bob redeems and nets `pa + pb`, see
`hedged_bob`.) -/
theorem alice_omits_after_bob_escrow {x : Exec} (hv : x.Valid) (hb : BobCompliant x) (pa pb : ℕ)
    (hbE : x.bE.isSome) (hsK : x.sK = none) :
    premiumAliceToBob x = true ∧ premiumBobToAlice x = true ∧
      aliceNet pa pb x = -pa ∧ bobNet pa pb x = pa := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hbE
  obtain ⟨⟨a, haE⟩, b, hbP⟩ := hb.escrow_only e he
  obtain ⟨a', haP⟩ := hb.premium_only b hbP
  have haR : x.aR = none := by
    cases h : x.aR with
    | none => rfl
    | some r => obtain ⟨k, hk, -⟩ := hv.aR_reveals r h; simp [hsK] at hk
  have hbR : x.bR = none := by
    cases h : x.bR with
    | none => rfl
    | some r => obtain ⟨-, -, k, hk, -⟩ := hv.bR_ok r h; simp [hsK] at hk
  have h1 : premiumAliceToBob x = true := by simp [premiumAliceToBob, haP, he, haR]
  have h2 : premiumBobToAlice x = true := by simp [premiumBobToAlice, hbP, haE, hbR]
  refine ⟨h1, h2, ?_, ?_⟩ <;> simp only [aliceNet, bobNet, h1, h2, ite_true] <;> ring

/-- §5.2: "If Bob is first to deviate after Alice escrows her principal, he will pay Alice `pb`."
Formally: Alice compliant and escrowed, Bob does not redeem Alice's principal (whether or not he
escrowed); then Alice's premium is refunded, Bob's premium goes to Alice. -/
theorem bob_deviates_after_alice_escrow {x : Exec} (ha : AliceCompliant x) (pa pb : ℕ)
    (haE : x.aE.isSome) (hbR : x.bR = none) :
    premiumAliceToBob x = false ∧ premiumBobToAlice x = true ∧
      aliceNet pa pb x = pb ∧ bobNet pa pb x = -pb := by
  obtain ⟨a, haa⟩ := Option.isSome_iff_exists.1 haE
  obtain ⟨b, hb⟩ := ha.escrow_only a haa
  have h2 : premiumBobToAlice x = true := by simp [premiumBobToAlice, hb, haa, hbR]
  refine ⟨ha.not_premiumAliceToBob, h2, hedged_alice ha pa pb haE hbR, ?_⟩
  simp [bobNet, h2, ha.not_premiumAliceToBob]

/-! ### Remark: the alternative reading of Alice's redemption rule -/

/-- Alternative reading of compliant Alice: she redeems Bob's principal only if she escrowed her
own (otherwise identical to `AliceCompliant`). -/
structure AliceCompliantAlt (x : Exec) : Prop where
  premium : x.aP = some 1
  escrow_of : ∀ b, x.bP = some b → x.aE = some (b + 1)
  escrow_only : ∀ a, x.aE = some a → ∃ b, x.bP = some b
  redeem : ∀ e, x.bE = some e → x.aE.isSome → x.aR = some (e + 1)
  reveal_only : ∀ k, x.sK = some k → ∃ e, x.bE = some e ∧ x.aE.isSome ∧ k = e + 1

/-- Under the alternative reading `AliceCompliantAlt`, Alice is not protected: Bob skips his
premium (so Alice does not escrow) but escrows his principal anyway; Alice does not redeem, and
the banana contract awards her premium `pa + pb` to Bob. -/
theorem alt_reading_alice_loses (pa pb : ℕ) :
    ∃ x : Exec, x.Valid ∧ AliceCompliantAlt x ∧ x.aE = none ∧ aliceNet pa pb x = -(pa + pb) := by
  refine ⟨⟨some 1, none, none, some 4, none, none, none⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨rfl, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩ <;>
    simp [aliceNet, premiumAliceToBob, premiumBobToAlice]

/-- Non-vacuity: the both-compliant schedule is a valid execution. -/
example : ∃ x : Exec, x.Valid ∧ AliceCompliant x ∧ BobCompliant x := by
  refine ⟨⟨some 1, some 2, some 3, some 4, some 5, some 5, some 6⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨rfl, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩ <;> simp

end Podc.SoreLoserHedging.TwoParty
