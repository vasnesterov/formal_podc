# Hedging Against Sore Loser Attacks — PODC 2021

Yingjie Xue, Maurice Herlihy. *Hedging Against Sore Loser Attacks in Cross-Chain Transactions.* PODC 2021. DOI
[10.1145/3465084.3467904](https://doi.org/10.1145/3465084.3467904). Formalized version: arXiv
[2105.06322](https://arxiv.org/abs/2105.06322) v2. It has the same text as the proceedings version, and the
numbering follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🔧 Easy fix.** Once the protocols' unspecified details are filled in consistently, the hedged two-party swap
is safe, live and hedged, the multi-party swap protocol is hedged (Lemma 6: a conforming party gains at least `p` for
every escrowed asset that is not redeemed, whatever the other parties do), and the auction lemmas (7, 8) hold. This
takes local changes to Lemmas 2 and 3, Equation (1) and Alice's redemption rule in §5.2. Brokered commerce and the
general liveness of multi-party swaps were not checked.

## Mistakes in the paper

### 🔧 Lemmas 2 and 3 (a leader that withholds its secret)
Lemma 2 is false for `v = Lᵢ` withholding its own secret: on `A ⇄ B` with leader `A`, Alice's net
redemption-premium profit is `−p`, not `≥ p` (`TwoCycle.lemma_2_false`). Lemma 3's split claim (escrow profit `≥ 0`
*and* redemption profit `≥ p` per escrowed asset) fails in the same execution (`TwoCycle.lemma_3_split_false`).

**Impact.** The hedging result (Lemma 6) is unaffected. Lemma 2 holds for every `v ≠ Lᵢ` (`lemma_2`) and for a leader
that released its secret (`lemma_2_leader_released`). In Lemma 3 the redemption part is `−p` but the escrow part there
is `+2p`, so the total, `+p`, is what matters, and it is what we prove (`lemma_3`).

**Details.** The claim: if hashkey `kᵢ` never appears on `v`'s leaving arcs, then `v`'s net redemption-premium
profit is at least `p` per escrowed asset. Take `v = Lᵢ` withholding its own secret. It pays its whole redemption
premium `R(Lᵢ)` and receives only `p` per leaving arc, because `Lᵢ ∥ q` is a cycle. The proof's cycle case ("v is
awarded at least p") forgets the leader's own deposits. Counterexample: the two-party digraph `A ⇄ B` with leader
`A`. Bob deposits all his premiums but does not escrow his asset. Alice escrowed hers, so she withholds her
secret. She pays `R(A) = 2p` and receives `p`, a net of `−p`. (`TwoCycle.lemma_2_false`)

The proof of Lemma 3 charges the leader's own redemption premiums to the escrow premium `E(u, v) = R(v)` ("the premium
`E(u,v)` is enough to cover…") and only then cites Lemma 2. So the intended accounting is recoverable.

### 🔧 Equation (1) (redemption premiums, not well defined)
For `v ∥ q` that is not a cycle, Eq. (1) recurses on `R(v ∥ q, u)`, which never ends when `v` already occurs
inside `q` (this happens with two or more leaders).

**Impact.** One case condition changes: the value `p` in that case is what the protocol needs, since a conforming `v`
does not extend such a `q` (`R_eq`).

**Details.** When `v` occurs inside `q`, `v ∥ q` is not a path. The argument "each path is finite, being acyclic"
covers only paths. (`R_eq`)

### 🔧 §5.2 (Alice's redemption rule)
§5.2 is hedged for Alice only if she redeems Bob's principal whenever he escrows it, even if she escrowed nothing, and
the paper does not have this rule. Under the other reading, Bob can escrow without paying his premium, and Alice loses
`pa + pb` (`TwoParty.alt_reading_alice_loses`).

**Impact.** With this one rule Alice never loses premiums (`TwoParty.aliceNet_nonneg`, `TwoParty.hedged_alice`).

**Details.** The parties run the swap only "if this premium distribution phase is successful". If Bob skips his premium,
Alice does not escrow, and Bob escrows anyway, her unredeemed Bob principal awards her premium to Bob. This does not
violate Definition 1, since Alice escrowed nothing, but it contradicts the claim that a party's risk is limited to
locking up premiums.

### ✏️ Slips
- Lemma 7 needs at least one conforming bidder, and it fails without one (`Auction.lemma7_needs_compliant_bidder`). The
  proof names the compliant party, and Lemma 8 uses the lemma only for a compliant bidder.
- §9's hashkey timeout `|q|Δ` must be counted from the start of the declaration phase. Counted from time 0,
  Alice's own key `(A)` would expire before she can publish it.
- The proof of Lemma 6 says "a profit of at least `p` for that asset" for every escrowed asset. That holds only
  for assets that are *not redeemed*, since Lemma 1 refunds everything otherwise.
- §7 defines paths with arcs `(uᵢ₊₁, uᵢ)`. Figure 3b and every later use need `(uᵢ, uᵢ₊₁)`.

### Typos
- The proof of Lemma 2 writes `q = (v, w, …, Lᵢ)` for `q = (w, …, Lᵢ)`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Multi-party swap (§7)* (`Model.lean`):
  * The swap digraph `G` is a Mathlib `Digraph` on a finite type, without loops. The leaders `L` form a feedback
    vertex set (`IsFVS`).
  * Time is synchronous and discrete, in units of `Δ`. Conforming parties act in lock-step: a reaction lands
    exactly one `Δ` after its trigger. Deadlines are inclusive.
  * An execution is a record `Exec` of the on-chain events. These are escrow premiums, redemption premiums with
    their signed paths, escrowed assets and the first accepted hashkeys with their paths, together with each
    party's first observed premium and key. The scheduler breaks ties.
  * `Admissible S X C` lists the contract rules (deadlines, path checks) and unforgeability. A path containing a
    conforming `x` carries, from `x` on, what `x` signed, no later than the event. Keys and premiums are public as
    soon as they are submitted, so front-running is allowed.
  * It also lists the four phases of conforming behaviour for every `v ∉ C`, including the truncated versions
    used in the proofs of Lemmas 3–5.
  * The coalition `C` is arbitrary. Payoffs are the contracts' refund and award rules. `net v` is `v`'s net
    premium profit.
  * Timeouts form a parameter family (`Swap`) with one `Δ` of slack per step. The theorems hold for every such
    family.
* *Two-party swap (§5.2)* (`TwoParty.lean`): the same style, with a record of the seven event times.
* *Auction (§9)* (`Auction.lean`): records of the first hashkey for each secret on each chain, unforgeable signed
  paths, and bidders who forward.
* There is no randomness. Cryptography is idealized: signatures cannot be forged and secrets cannot be guessed.

**Protocol details we completed.** The protocol is under-specified, and we completed it.
* No timeouts are given beyond "each step's timeout increases by `Δ`". We impose one `Δ` of slack per step, and
  the proofs use it (`Swap`).
* The paper does not say whether followers escrow only on *activated* arcs. We require it, as the paper does for
  leaders.
* A leader that escrowed nothing releases its secret at once (as in the proof of Lemma 4). Otherwise it releases
  it iff all its entering arcs carry assets (as in the proof of Lemma 3).
* Contracts must reject cycles as redemption-premium paths. The §7 notion of path includes cycles, and a cycle
  premium on an arc can activate it while the arcs entering its tail stay inactive (argued in
  `differencies.md`, not formalized).
* Hashkey paths are those of [Herlihy 2018]: every vertex except possibly the last is distinct. The companion
  formalization `Papers/PODC2018/AtomicCrossChainSwaps` shows that simple paths and cycles do not work for
  keys.
* In §6, "`r` rounds" counts the swap's own premium round. The "$1,000,000 swap" example needs `A = B = 10⁶`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Eq. (1), (2) (well-definedness) | `R_eq`, `Ein_eq` | `Premiums.lean` |
| Lemma 1 (all conform, swap completes ⇒ all premiums refunded) | `Swap.lemma_1`, `Swap.lemma_1_net` | `Hedged.lean` |
| Lemma 2 (`v ≠ Lᵢ`; leader that released) | `Swap.lemma_2`, `Swap.lemma_2_leader_released` | `Hedged.lean` |
| Lemma 2 for a withholding leader: false | `TwoCycle.lemma_2_false` | `Examples.lean` |
| Lemma 3 (total form) / split form false | `Swap.lemma_3` / `TwoCycle.lemma_3_split_false` | `Hedged.lean`, `Examples.lean` |
| Lemma 4, Lemma 5 | `Swap.lemma_4`, `Swap.lemma_5` (and `Swap.netE_nonneg`) | `Hedged.lean` |
| Lemma 6 (the protocol is hedged) | `Swap.lemma_6`, `Swap.net_nonneg` | `Hedged.lean` |
| non-vacuity: Figure 3a, everybody conforms | `Fig3.fig3_admissible` | `Examples.lean` |
| §5.2 liveness, safety | `TwoParty.liveness`, `TwoParty.safety_alice`, `TwoParty.safety_bob` | `TwoParty.lean` |
| §5.2 hedged (Def. 1), premiums never lost | `TwoParty.hedged_alice`, `TwoParty.hedged_bob`, `TwoParty.aliceNet_nonneg`, `TwoParty.bobNet_nonneg` | `TwoParty.lean` |
| §5.2 "first to omit a step pays …" | `TwoParty.alice_omits_after_bob_escrow`, `TwoParty.bob_deviates_after_alice_escrow` | `TwoParty.lean` |
| §6 premiums `(rA+B)/Pʳ`, `A/Pʳ`; $1M example | `Bootstrap.premiums_closed_form`, `Bootstrap.example_one_million` | `Bootstrap.lean` |
| Lemma 7 / needs a conforming bidder | `Auction.lemma7` / `Auction.lemma7_needs_compliant_bidder` | `Auction.lean` |
| Lemma 8 | `Auction.lemma8`, `Auction.lemma8_low_bidder` | `Auction.lean` |
| §9.2 no sore-loser attack by bidders; premiums | `Auction.completes_of_alice_compliant`, `Auction.compliant_bidder_outcome` | `Auction.lean` |

**Not formalized.**
* Lemma 1 with deviators: we prove it only when everybody conforms. With deviators a conforming `v` may pay a premium
  and be compensated by another, which is argued in `differencies.md` and depends on premium deadlines the paper does
  not fix.
* The safety and liveness of the base multi-party protocol, which the paper cites from [Herlihy 2018]. See the
  companion `Papers/PODC2018/AtomicCrossChainSwaps`.
* Liveness of the hedged multi-party protocol in general. It is shown only on the Figure 3a example.
* The brokered-commerce protocol of §8, which states no lemma.
* The premium-size remarks (linear or exponential in `n`) and the lock-up durations.
* Correctness of the bootstrapping protocol itself. Only its premium arithmetic is formalized.

**Trust.**
* No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
* Admissibility of the concrete executions is checked by `decide`, via the decidable twin `AdmD` of `Admissible`.
* Everything is self-contained on Mathlib.
* Limitation: lock-step timing (every conforming reaction takes exactly `Δ`). Our timeouts are one consistent
  completion of the paper's informal ones.
