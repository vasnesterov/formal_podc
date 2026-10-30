import Mathlib

/-!
# The hedged auction (§9 of [Xue–Herlihy 2021]; Lemmas 7, 8)

Y. Xue, M. Herlihy, *Hedging Against Sore Loser Attacks in Cross-Chain Transactions*, PODC 2021
(arXiv:2105.06322), §9.

Alice (`A`, auctioneer) auctions tickets to the bidders Bob (`B`) and Carol (`C`). There are two
chains, `coin` (bids) and `ticket`. Alice holds two secrets, one per bidder (`s_B` to be used if
Bob wins, `s_C` if Carol wins). A *hashkey* for a secret carries a path `q` of signers (outermost
signer first, Alice last).

## Model

* Synchronous, discrete time `ℕ` in units of `Δ`, lock-step parties: a reaction to an event
  visible at time `t` takes effect at `t + 1`; deadlines are inclusive. Phases: bidding `[0, 1]`,
  declaration `[1, 2]`, challenge `[2, 5]`, commit at `5`.
* **Timeouts.** The paper says a hashkey with path `q` "times out after time `|q|Δ`". Measured from
  the start of the protocol, Alice's own key `(A)` would time out at `Δ`, before the declaration
  phase ends at `2Δ`; so we measure from the start of the declaration phase (time `1`): a key with
  path `q` is accepted iff it arrives at time `t ≤ 1 + |q|` (`(A)` until 2, `(B, A)` until 3,
  `(C, B, A)` until 4, all before the end of the challenge phase at 5).
* An execution `Exec` records the bids (amounts) and, for each secret `X` and chain `c`, the
  **first accepted** hashkey `pub X c = some (t, q)` (arrival time and path), `none` if none was
  ever accepted. The contracts' settlement depends only on whether a key was received.
* `Exec.Valid`: acceptance rule (valid path, before its timeout); binds everyone.
* Unforgeability of signatures is folded into the compliance predicates: a key whose path contains
  a compliant party `Y` with suffix `Y :: q₂` exists only if `Y` signed exactly that, which the
  protocol allows only in the situations described by `BidderCompliant.signs` /
  `AliceCompliant.signs`. Deviating parties are otherwise arbitrary.
* Compliant bidder `Y` (challenge phase): when a key `(t, q)` for `X` is the first one on chain
  `c` and the other chain has no key by time `t`, `Y` sends `Y :: q` to the other chain at `t + 1`.
  We record this as "the first accepted key on the other chain arrives no later than `t + 1`",
  conditional on `Y`'s submission being acceptable, and *prove* that it is (`forward_accepted`).
* Compliant Alice publishes the winner's key `(A)` on both chains at time `2` and never releases
  the other secret. The winner is given by a parameter `WinnerRule` (the paper leaves ties
  unspecified; we only require that the winner, if any, submitted a highest bid).

## Commit rules (§9.1 (4))

* coin: if it received the actual winner's key and not the other one, the winner's bid goes to
  Alice and the other bid is refunded; otherwise all bids are refunded;
* ticket: exactly one key received ⇒ tickets to that bidder; zero or two ⇒ refund to Alice.

The paper's proof of Lemma 7 uses a length argument ("if `q` has no compliant party then
`|q| ≤ 2`"); in this model it is unnecessary: the forwarded key `Y :: q` is one signature longer,
hence has one more `Δ` before it times out, which is exactly the reaction time.
-/

namespace Podc.SoreLoserHedging.Auction

/-- The three parties. -/
inductive Party
  | A
  | B
  | C
  deriving DecidableEq, Repr

instance : Fintype Party := ⟨{.A, .B, .C}, fun x => by cases x <;> simp⟩

/-- The two bidders (they also index Alice's two secrets). -/
inductive Bidder
  | B
  | C
  deriving DecidableEq, Repr

instance : Fintype Bidder := ⟨{.B, .C}, fun x => by cases x <;> simp⟩

/-- The two chains. -/
inductive Chain
  | coin
  | ticket
  deriving DecidableEq, Repr

instance : Fintype Chain := ⟨{.coin, .ticket}, fun x => by cases x <;> simp⟩

/-- A bidder as a party. -/
def Bidder.toParty : Bidder → Party
  | .B => .B
  | .C => .C

/-- The other bidder. -/
def Bidder.other : Bidder → Bidder
  | .B => .C
  | .C => .B

/-- The other chain. -/
def Chain.other : Chain → Chain
  | .coin => .ticket
  | .ticket => .coin

@[simp] lemma Bidder.other_ne (X : Bidder) : X.other ≠ X := by cases X <;> decide

@[simp] lemma Chain.other_other (c : Chain) : c.other.other = c := by cases c <;> rfl

lemma Chain.eq_or_eq_other (c d : Chain) : d = c ∨ d = c.other := by
  cases c <;> cases d <;> simp [Chain.other]

/-- A valid hashkey path: distinct signers, the last one is Alice. -/
def ValidPath (q : List Party) : Prop := q.Nodup ∧ ∃ q₁, q = q₁ ++ [Party.A]

/-- A hashkey with path `q` arriving at time `t` is accepted. -/
def Accepted (t : ℕ) (q : List Party) : Prop := ValidPath q ∧ t ≤ 1 + q.length

/-- An auction execution. -/
structure Exec where
  /-- The bids (amounts) recorded by the coin contract, `none` = no bid. -/
  bid : Bidder → Option ℕ
  /-- First accepted hashkey for secret `X` on chain `c`: arrival time and path. -/
  pub : Bidder → Chain → Option (ℕ × List Party)

/-- Acceptance rule of both contracts. -/
structure Exec.Valid (x : Exec) : Prop where
  accepted : ∀ X c t q, x.pub X c = some (t, q) → Accepted t q

/-- No key for `X` arrived on chain `c` at time `≤ t`. -/
def NoKeyBy (x : Exec) (X : Bidder) (c : Chain) (t : ℕ) : Prop :=
  ∀ t' q', x.pub X c = some (t', q') → t < t'

/-- The protocol rules of bidder `Y` (challenge phase), including unforgeability of `Y`'s
signature. -/
structure BidderCompliant (x : Exec) (Y : Bidder) : Prop where
  /-- `Y` signs `Y :: q₂` only when forwarding the first key `(t₁, q₂)` of chain `c₁` to the other
  chain, which then had no key by `t₁`; the forwarded key exists from time `t₁ + 1` on. -/
  signs : ∀ X c t q q₂, x.pub X c = some (t, q) → (Y.toParty :: q₂) <:+ q →
    ∃ c₁ t₁, x.pub X c₁ = some (t₁, q₂) ∧ NoKeyBy x X c₁.other t₁ ∧ t₁ + 1 ≤ t
  /-- `Y` forwards a key missing on the other chain at the next step (if acceptable). -/
  forward : ∀ X c t q, x.pub X c = some (t, q) → NoKeyBy x X c.other t →
    Accepted (t + 1) (Y.toParty :: q) → ∃ t' q', x.pub X c.other = some (t', q') ∧ t' ≤ t + 1

/-- How the winner is determined from the bids (ties are left open, as in the paper). -/
structure WinnerRule where
  winner : (Bidder → Option ℕ) → Option Bidder
  /-- The winner submitted a highest bid. -/
  winner_bid : ∀ b W, winner b = some W → ∃ v, b W = some v ∧ ∀ Y v', b Y = some v' → v' ≤ v

/-- The protocol rules of Alice, including unforgeability of her signature. -/
structure AliceCompliant (w : WinnerRule) (x : Exec) : Prop where
  /-- Alice publishes the winner's key on both chains in the declaration phase. -/
  publish : ∀ W, w.winner x.bid = some W → ∀ c, ∃ t q, x.pub W c = some (t, q) ∧ t ≤ 2
  /-- Alice signs only the one-element path, and only for the winner's secret. -/
  signs : ∀ X c t q q₂, x.pub X c = some (t, q) → (Party.A :: q₂) <:+ q →
    q₂ = [] ∧ w.winner x.bid = some X

/-! ### Settlement -/

/-- The coin contract: `some W` if the winner `W`'s bid is transferred to Alice (the other bid is
refunded); `none` if all bids are refunded. -/
def coinPaysAlice (w : WinnerRule) (x : Exec) : Option Bidder :=
  match w.winner x.bid with
  | some W => if (x.pub W .coin).isSome && (x.pub W.other .coin).isNone then some W else none
  | none => none

/-- The ticket contract: `some X` if the tickets go to `X`, `none` if they are refunded to Alice. -/
def ticketsTo (x : Exec) : Option Bidder :=
  if (x.pub .B .ticket).isSome && (x.pub .C .ticket).isNone then some .B
  else if (x.pub .C .ticket).isSome && (x.pub .B .ticket).isNone then some .C
  else none

lemma coinPaysAlice_eq_some {w : WinnerRule} {x : Exec} {W : Bidder}
    (h : coinPaysAlice w x = some W) :
    w.winner x.bid = some W ∧ (x.pub W .coin).isSome ∧ x.pub W.other .coin = none := by
  unfold coinPaysAlice at h
  rcases hw : w.winner x.bid with _ | W'
  · simp [hw] at h
  · simp only [hw] at h
    split_ifs at h with h'
    cases h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h'
    exact ⟨rfl, h'⟩

lemma ticketsTo_of {x : Exec} {W : Bidder} (h1 : (x.pub W .ticket).isSome)
    (h2 : x.pub W.other .ticket = none) : ticketsTo x = some W := by
  cases W <;> simp_all [ticketsTo, Bidder.other]

/-! ### Lemma 7 -/

/-- A compliant bidder never appears on the path of the first key of a chain whose key is missing
on the other chain. -/
lemma BidderCompliant.not_mem {x : Exec} {Y X : Bidder} {c : Chain} {t : ℕ} {q : List Party}
    (hY : BidderCompliant x Y) (h : x.pub X c = some (t, q)) (hn : NoKeyBy x X c.other t) :
    Y.toParty ∉ q := by
  intro hm
  obtain ⟨s, u, hq⟩ := List.append_of_mem hm
  subst hq
  obtain ⟨c₁, t₁, h₁, -, ht⟩ := hY.signs X c t _ u h (List.suffix_append s _)
  rcases Chain.eq_or_eq_other c c₁ with rfl | rfl
  · simp only [h, Option.some.injEq, Prod.mk.injEq] at h₁; omega
  · have := hn t₁ u h₁; omega

/-- The key that a compliant bidder forwards in the challenge phase is accepted. -/
lemma forward_accepted {x : Exec} (hv : x.Valid) {Y X : Bidder} {c : Chain} {t : ℕ}
    {q : List Party} (hY : BidderCompliant x Y) (h : x.pub X c = some (t, q))
    (hn : NoKeyBy x X c.other t) : Accepted (t + 1) (Y.toParty :: q) := by
  obtain ⟨⟨hnd, q₁, rfl⟩, ht⟩ := hv.accepted X c t _ h
  refine ⟨⟨List.nodup_cons.2 ⟨hY.not_mem h hn, hnd⟩, Y.toParty :: q₁, rfl⟩, ?_⟩
  simp only [List.length_cons] at ht ⊢
  omega

/-- If some bidder is compliant, a key for `X` received on chain `c` is also received on the
other chain. -/
lemma forwarded {x : Exec} (hv : x.Valid) {Y : Bidder} (hY : BidderCompliant x Y) (X : Bidder)
    (c : Chain) (h : (x.pub X c).isSome) : (x.pub X c.other).isSome := by
  obtain ⟨⟨t, q⟩, hp⟩ := Option.isSome_iff_exists.1 h
  by_cases hn : NoKeyBy x X c.other t
  · obtain ⟨t', q', h', -⟩ := hY.forward X c t q hp hn (forward_accepted hv hY hp hn)
    simp [h']
  · simp only [NoKeyBy, not_forall, not_lt] at hn
    obtain ⟨t', q', h', -⟩ := hn
    simp [h']

/-- Lemma 7 of [Xue–Herlihy 2021]: if a hashkey for a secret is published on one contract, then
one is also published on the other — provided some bidder is compliant (the paper's proof relies
on a compliant party; without one the claim fails, see `lemma7_needs_compliant_bidder`). -/
theorem lemma7 {x : Exec} (hv : x.Valid) {Y : Bidder} (hY : BidderCompliant x Y) (X : Bidder) :
    (x.pub X .coin).isSome ↔ (x.pub X .ticket).isSome :=
  ⟨forwarded hv hY X .coin, forwarded hv hY X .ticket⟩

/-! ### Lemma 8 -/

/-- If some bidder is compliant and the coin contract transfers `W`'s bid to Alice, then `W`
receives the tickets. -/
theorem tickets_of_coinPaysAlice {w : WinnerRule} {x : Exec} (hv : x.Valid) {Y : Bidder}
    (hY : BidderCompliant x Y) {W : Bidder} (h : coinPaysAlice w x = some W) :
    ticketsTo x = some W := by
  obtain ⟨-, h1, h2⟩ := coinPaysAlice_eq_some h
  refine ticketsTo_of ((lemma7 hv hY W).1 h1) ?_
  by_contra h3
  have := (lemma7 hv hY W.other).2 (Option.ne_none_iff_isSome.1 h3)
  simp [h2] at this

/-- Lemma 8 of [Xue–Herlihy 2021] ("no compliant bidder's bid can be stolen"), first part: a
compliant bidder's bid is transferred to Alice only if that bidder receives the tickets. -/
theorem lemma8 {w : WinnerRule} {x : Exec} (hv : x.Valid) {Y : Bidder}
    (hY : BidderCompliant x Y) (h : coinPaysAlice w x = some Y) : ticketsTo x = some Y :=
  tickets_of_coinPaysAlice hv hY h

/-- Lemma 8 of [Xue–Herlihy 2021], second part: the bid of a bidder who is not the winner (the
low bidder) is never transferred to Alice (it is always refunded). -/
theorem lemma8_low_bidder {w : WinnerRule} {x : Exec} {Y : Bidder}
    (hY : w.winner x.bid ≠ some Y) : coinPaysAlice w x ≠ some Y :=
  fun h => hY (coinPaysAlice_eq_some h).1

/-! ### §9.2: compliant Alice -/

/-- §9 / §9.2 of [Xue–Herlihy 2021]: the protocol "is not vulnerable to a sore loser attack from
the low bidder": if Alice is compliant and there is a winner `W`, then whatever the bidders do,
the auction completes — `W`'s bid goes to Alice and the tickets go to `W`. -/
theorem completes_of_alice_compliant {w : WinnerRule} {x : Exec} (hv : x.Valid)
    (ha : AliceCompliant w x) {W : Bidder} (hW : w.winner x.bid = some W) :
    coinPaysAlice w x = some W ∧ ticketsTo x = some W := by
  have hpub : ∀ c, (x.pub W c).isSome := fun c => by
    obtain ⟨t, q, h, -⟩ := ha.publish W hW c
    simp [h]
  have hnone : ∀ c, x.pub W.other c = none := fun c => by
    by_contra hc
    obtain ⟨⟨t, q⟩, h⟩ := Option.ne_none_iff_exists'.1 hc
    obtain ⟨⟨-, q₁, rfl⟩, -⟩ := hv.accepted _ _ _ _ h
    have := (ha.signs _ c t _ [] h (List.suffix_append q₁ _)).2
    rw [hW] at this
    exact W.other_ne (Option.some_injective _ this).symm
  refine ⟨?_, ticketsTo_of (hpub _) (hnone _)⟩
  simp [coinPaysAlice, hW, hpub, hnone]

/-! ### §9.2: premiums -/

/-- §9.2: Alice deposits `2p`; if the bids are refunded, each bidder is awarded `p`. -/
def premiumToBidder (w : WinnerRule) (p : ℕ) (x : Exec) (_Y : Bidder) : ℕ :=
  if coinPaysAlice w x = none then p else 0

/-- §9.2: if the auction completes, Alice's premiums `2p` are refunded. -/
def premiumRefund (w : WinnerRule) (p : ℕ) (x : Exec) : ℕ :=
  if coinPaysAlice w x = none then 0 else 2 * p

/-- The premium payouts exhaust Alice's deposit `2p`. -/
lemma premium_conserved (w : WinnerRule) (p : ℕ) (x : Exec) :
    premiumToBidder w p x .B + premiumToBidder w p x .C + premiumRefund w p x = 2 * p := by
  unfold premiumToBidder premiumRefund; split_ifs <;> omega

/-- §9.2 (hedging the bidders): a compliant bidder either has its bid refunded together with the
premium `p`, or keeps its bid (it was not the winner and the auction completed), or pays its bid
and receives the tickets. -/
theorem compliant_bidder_outcome {w : WinnerRule} {x : Exec} (hv : x.Valid) {Y : Bidder}
    (hY : BidderCompliant x Y) (p : ℕ) :
    (coinPaysAlice w x = none ∧ premiumToBidder w p x Y = p) ∨
      (coinPaysAlice w x = some Y.other) ∨
      (coinPaysAlice w x = some Y ∧ ticketsTo x = some Y) := by
  rcases h : coinPaysAlice w x with _ | W
  · simp [premiumToBidder, h]
  · by_cases hW : W = Y
    · subst hW; exact Or.inr (Or.inr ⟨rfl, lemma8 hv hY h⟩)
    · refine Or.inr (Or.inl ?_)
      cases W <;> cases Y <;> simp_all [Bidder.other]

/-- Remark: when there is no winner (no bid, or a tie the winner rule does not break), even a
compliant Alice forfeits her premium `2p` to the bidders under the literal §9.2 rule. -/
theorem no_winner_alice_pays (w : WinnerRule) (p : ℕ) (x : Exec) (h : w.winner x.bid = none) :
    premiumRefund w p x = 0 := by
  simp [premiumRefund, coinPaysAlice, h]

/-! ### Examples -/

/-- The highest bid wins; ties and missing bids give no winner. -/
def highestBid : WinnerRule where
  winner b := match b .B, b .C with
    | some u, some v => if v < u then some .B else if u < v then some .C else none
    | some _, none => some .B
    | none, some _ => some .C
    | none, none => none
  winner_bid b W h := by
    rcases hB : b .B with _ | u <;> rcases hC : b .C with _ | v <;> simp only [hB, hC] at h
    · cases h
    · cases h
      exact ⟨v, hC, fun Y v' hY => by cases Y <;> simp_all⟩
    · cases h
      exact ⟨u, hB, fun Y v' hY => by cases Y <;> simp_all⟩
    · split_ifs at h with h1 h2 <;> cases h
      · exact ⟨u, hB, fun Y v' hY => by cases Y <;> simp_all; omega⟩
      · exact ⟨v, hC, fun Y v' hY => by cases Y <;> simp_all⟩

/-- Example: Bob bids 10, Carol 5; a deviating Alice publishes Bob's key only on the coin chain at
time 2; compliant Bob forwards `(B, A)` to the ticket chain at time 3. -/
def exBob : Exec where
  bid | .B => some 10 | .C => some 5
  pub
    | .B, .coin => some (2, [.A])
    | .B, .ticket => some (3, [.B, .A])
    | .C, _ => none

lemma exBob_valid : exBob.Valid := by
  constructor
  intro X c t q h
  cases X <;> cases c <;> simp only [exBob, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨by decide, [], rfl⟩, by decide⟩
  · obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨by decide, [.B], rfl⟩, by decide⟩

lemma exBob_bob : BidderCompliant exBob .B := by
  constructor
  · intro X c t q q₂ h hs
    cases X <;> cases c <;> simp only [exBob, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    · obtain ⟨rfl, rfl⟩ := h; simp [Bidder.toParty, List.suffix_cons_iff] at hs
    · obtain ⟨rfl, rfl⟩ := h
      simp [Bidder.toParty, List.suffix_cons_iff] at hs
      subst hs
      refine ⟨.coin, 2, rfl, ?_, le_refl _⟩
      intro t' q' h'
      simp only [Chain.other, exBob, Option.some.injEq, Prod.mk.injEq] at h'
      omega
  · intro X c t q h hn _
    cases X <;> cases c <;> simp only [exBob, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨3, _, rfl, le_refl _⟩
    · obtain ⟨rfl, rfl⟩ := h; exact absurd (hn 2 [.A] rfl) (by decide)

/-- Non-vacuity: a valid execution with Bob compliant (Alice deviating) in which the auction
completes thanks to Bob's forwarding. -/
example : exBob.Valid ∧ BidderCompliant exBob .B ∧ coinPaysAlice highestBid exBob = some .B ∧
    ticketsTo exBob = some .B :=
  ⟨exBob_valid, exBob_bob, rfl, rfl⟩

/-- Example: Alice publishes Bob's key only on the coin chain and nobody forwards it. -/
def exNoForward : Exec where
  bid | .B => some 10 | .C => some 5
  pub
    | .B, .coin => some (2, [.A])
    | _, _ => none

/-- Lemma 7 (and Lemma 8) need a compliant bidder: in `exNoForward` (a valid execution where both
bidders deviate by not forwarding) Bob's bid goes to Alice but the tickets are refunded to Alice. -/
theorem lemma7_needs_compliant_bidder :
    exNoForward.Valid ∧ (exNoForward.pub .B .coin).isSome ∧ exNoForward.pub .B .ticket = none ∧
      coinPaysAlice highestBid exNoForward = some .B ∧ ticketsTo exNoForward = none := by
  refine ⟨⟨fun X c t q h => ?_⟩, rfl, rfl, rfl, rfl⟩
  cases X <;> cases c <;>
    simp only [exNoForward, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨by decide, [], rfl⟩, by decide⟩

end Podc.SoreLoserHedging.Auction
