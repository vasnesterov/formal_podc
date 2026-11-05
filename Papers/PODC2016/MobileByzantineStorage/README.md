# Optimal Mobile Byzantine Fault Tolerant Distributed Storage — PODC 2016

Silvia Bonomi, Antonella Del Pozzo, Maria Potop-Butucaru, Sébastien Tixeuil. *Optimal Mobile Byzantine
Fault Tolerant Distributed Storage.* PODC 2016. DOI
[10.1145/2933057.2933100](https://doi.org/10.1145/2933057.2933100). Formalized version: the full version,
research report HAL [hal-01348830v2](https://hal.sorbonne-universite.fr/hal-01348830v2) (Feb 2017, 42 pp);
numbering follows it.

**Verdict: 🚨 Headline claim false.** Both "optimal" regular-register protocols are wrong at the paper's
own parameters: a read with no concurrent write returns a never-written value. In the CAM model
(Theorems 8/9, for `2δ ≤ Δ < 3δ` and `δ ≤ Δ < 3δ/2`) the extra liars are faulty servers that send a
fake reply just *before* the read starts, delivered during the read. In the CUM model (Theorems 11/12,
for `2δ ≤ Δ < 5δ/2` and `δ ≤ Δ < 5δ/4`) the faulty and cured servers that the paper itself counts already
outnumber the threshold `#reply_CUM`. The lower-bound proofs (Theorems 3–6) compare
executions that the reader can tell apart, because replies are authenticated. We repair Theorems 3 and 5
in the paper's own lower-bound model. The optimality claims therefore have no matching upper bound.

## Mistakes in the paper

### 🚨 Theorems 8 and 9 (the `(ΔS, CAM)` protocol, Section 5)
A read with no concurrent write returns a never-written value: for `2δ ≤ Δ < 3δ`, `n = 4f + 1`,
`#reply_CAM = 2f + 1`, the `3f` servers hosting an agent during `(t − δ, t + 2δ)` all report a fake pair
with the highest sequence number, and for `δ ≤ Δ < 3δ/2`, `n = 5f + 1`, `#reply_CAM = 3f + 1`, `4f` such
servers do (`theorem9_false_k1`, `theorem9_false_k2`, `theorem9_false`).

**Impact.** The headline protocol violates even safe-register validity, in a read with no concurrent
write, at the parameters of Table 1. So the claimed tight bounds `n ≥ 4f + 1` and `n ≥ 5f + 1` for the CAM
model have no proved upper bound. Lemma 7, the counting lemma behind the proof, is true (`lemma7`) but
counts the wrong time window.

**Details.** The paper bounds the liars of a read `[t, t+2δ]` by `MaxB̃(t, t+2δ)`, "as if each message to/from them
is delivered instantaneously" (Section 5.2; Corollary 3 states the resulting majority). But in the
round-free synchronous model (Section 2) a message sent at time `τ` is delivered at any time of
`(τ, τ + δ]`. So a server that hosts an agent at some `τ ∈ (t − δ, t)` can send a `reply` that arrives
during the read. The reader's `reply_i` is reset at `t`, but replies carry no read identifier and the
reader accepts all of them (Fig. 24, lines 01, 07–09).

The window `(t − δ, t + 2δ)` has length `3δ`, so it can meet `⌈3δ/Δ⌉ + 1` agent periods. That is 3 for
`2δ ≤ Δ < 3δ` (`3f ≥ 2f + 1` liars) and 4 for `δ ≤ Δ < 3δ/2` (`4f ≥ 3f + 1` liars). The agents sweep
disjoint blocks of `f` servers. Each liar sends one reply `{⟨v′, N + 1⟩}`, where `N` is the number of
writes so far. `select_value` returns, among the pairs with at least `#reply_CAM` occurrences, the one with
the highest sequence number, which is the fake pair.

The Lean statement quantifies over *all* other replies whose sequence numbers are at most `N`. In the
counterexample the faulty servers send nothing to servers, so correct servers only ever hold written
pairs (and `⟨⊥, 0⟩`). The result holds for any tie-breaking rule of `select_value` and for every `n ≥ 3f`
(resp. `4f`) with these thresholds. The paper's Theorem 9 has no upper bound on `Δ`. For
`3δ/2 ≤ Δ < 2δ` and for `Δ ≥ 3δ` the attack gives too few liars; correctness there is open.

*Scope.* The attack needs only what the system model allows: a delay of at most `δ` on the faulty
servers' messages. No foresight is needed either: a faulty server may send the fake reply to every client
repeatedly while it hosts the agent, and any read starting less than `δ` later receives it. If one
instead *postulated* that faulty servers' messages are delivered instantly, the CAM attack would not
apply (the CUM attack below would).

**Repair.** None proved. Counting the liars over `(t − δ, t + 2δ)` suggests
`#reply_CAM > (⌈3δ/Δ⌉ + 1) f` and `n ≥ #reply_CAM + 2f`, i.e. `n ≥ 5f + 1` for `2δ ≤ Δ < 3δ` and
`n ≥ 6f + 1` for `δ ≤ Δ < 3δ/2`. This is not verified.

### 🚨 Theorems 11, 12 and 13 (the `(ΔS, CUM)` protocol, Section 6)
The CUM read is fooled even without replies sent before the read: for `2δ ≤ Δ < 5δ/2`
(`#reply_CUM = 3f + 1`) `3f` faulty and `f` cured servers, and for `δ ≤ Δ < 5δ/4` (`#reply_CUM = 5f + 1`)
`4f` faulty and `2f` cured servers, report a fake pair with the highest sequence number
(`theorem12_false_k1`, `theorem12_false_k2`, `theorem12_false`).

**Impact.** The CUM protocol fails at the parameters of Table 3 (`n = 5f + 1`, `8f + 1`), so the
tightness claim of Theorem 13 is false as well. This refutation does not depend on the delay argument of
the CAM item: the proof of Theorem 11 itself counts "up to `4f`" (resp. `6f`) non-correct servers that
can reply with non-valid values, and then claims that `#reply_CUM = 3f + 1` (resp. `5f + 1`) exceeds
this. It does not, once these servers all report the same pair.

**Details.** The cured liars are those allowed by the paper's Lemma 18. A server cured at time `c` may answer a
`read` with a non-valid value until `c + 2δ`. The agent leaves an entry `⟨⟨v′, sn′⟩, 2δ⟩` in `W_i`, and
`conCut(V_i, Vsafe_i, W_i)` returns it (Fig. 27, line 11), since `sn′` is the newest. In the
counterexample the cured server receives the read request during `(t, t+δ]` and before `c + 2δ`, and
replies at once.

Every lying reply is sent during the read. The faulty liars are the servers hosting an agent during
the read `[t, t + 3δ]`: `3f` (resp. `4f`). The cured liars are the servers whose agent left at most `2δ`
before the request reaches them: `f` (resp. `2f`).

Theorem 12 also states the hypothesis `n ≥ 2(k+1)f + 1`, which contradicts Table 3 (`n ≥ (3k+2)f + 1`)
and Theorem 4 (no protocol for `n ≤ 8f` when `δ ≤ Δ < 2δ`). The counterexamples need only `4f` resp.
`6f` servers, so they refute both readings.

### ⚠️ Theorems 3–6 (lower bounds, Sections 4.5–4.6)
The executions `E₁`, `E₀` are not indistinguishable: they use the same agent schedule, so the reader
receives `1` from `s₀` in `E₁` and `0` from `s₀` in `E₀`; only the multisets of *values* coincide, while
replies are authenticated.

**Impact.** As written, the proofs establish nothing for a reader that looks at senders. Theorems 3 and 5
hold in the paper's own lower-bound model with a corrected pair of executions (`theorem3`, `theorem5`).
The claim for arbitrary protocols remains unproved, and Theorems 4 and 6 (CUM) were not formalized.

**Details.** Section 4.4 fixes the model of the lower bounds. A correct server replies once, when the request
reaches it; faulty and cured servers do not reply correctly; faulty servers may send anything. The
paper's `E₁` of Fig. 5 is fine. `E₀` must use a different schedule: the agent visits `s₀, s₄, s₃` instead
of `s₁, s₂, s₃`.

In general, label the servers by blocks of at most `f`: `A₁, B₁` (faulty in `E₁` before and during the
request time), `A₀, B₀` (same in `E₀`), and `C` (faulty right after, in both). Every server is then
either honest in one execution and impersonated, with the same delivery time, in the other, or (`C`)
heard with both values in both. So the reader's full view — senders, values and delivery times — is the
same, for every read duration and every decision rule. That gives `n ≤ 5f` for `δ ≤ Δ < 2δ` and
`n ≤ 4f` (no `C`) for `Δ ≥ 2δ`. The cure duration `γ` plays no role.

In this model correct servers reply only once, so "waiting more does not help" is true. For general
protocols — e.g. the paper's own, where cured servers reply again once correct — it is not proved.

### ⚠️ Lemma 6 (`MaxB̃(t, t+T) = (⌈T/Δ⌉ + 1) f`)
The equality is false when `(⌈T/Δ⌉ + 1) f > n`, e.g. for `n = 6 = 5f + 1`, `f = 1`, `δ = Δ = 1`,
`T = 10` it claims `11` affected servers out of `6` (`lemma6_false`).

**Impact.** Harmless: the paper uses it only for `T ∈ {δ, 2δ, 3δ}`, where the bound is below `n`. The
correct value is `min(n, (⌈T/Δ⌉ + 1) f)` (`lemma6`); the hypotheses `δ ≤ Δ < 3δ`, `T ≥ δ` are not needed.

### Typos and slips
- Lemma 7, proof: `minC̃oR(t, t+2δ) = n − (⌈2δ/Δ⌉ + 1) f` should read `⌈δ/Δ⌉`; the numbers used
  (`5f + 1 − 2f`) are those of `⌈δ/Δ⌉ = 1`.
- Lemma 8, proof: `n − 2f = 3(k+1)f + 1 − 2f = (k+1)f + 1` should start from `n = (k+3)f + 1`.
- Theorem 6, proof: "we consider directly `n ≤ 5`" (for `5f`), and the two multisets listed for
  `E₁‴`, `E₀‴` are identical.
- Corollary 2 ends with "□ Lemma 2", Theorem 5 with "□ Theorem 3".

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Real time; `n` servers `Fin n`; `f` mobile Byzantine agents moving simultaneously at the times
  `t₀ + iΔ` (`ΔS`). A schedule gives, for each period `i ∈ ℤ`, the at most `f` servers hosting an
  agent (`Schedule`); `affected` is the paper's `B̃[a, b]`.
- Round-free synchrony: every message delay is in `(0, δ]`, chosen by the adversary.
- Protocol attacks (`ReadAttack.lean`): only the reader is modelled. A read invoked at `t` collects the
  triples `⟨j, ⟨v, sn⟩⟩` of all replies delivered in `(t, t + D]` (`collected`) and returns any pair
  allowed by `select_value` (`SelectValue`). Replies of faulty servers must be sent while faulty
  (`ByzReply`); in CUM a cured server may also lie, when the request reaches it, during `2δ` after
  being left (`CuredLiar`, `LyingReply`, the paper's Lemma 18). All other replies are arbitrary
  (universally quantified) with sequence numbers at most `N`.
- Lower bounds (`LowerBound.lean`): the paper's Section 4.4 model (`ReadExec`). Request arrival times are
  in `(t, t + δ]`; a server correct at that time replies once with the register value; faulty servers
  send arbitrary replies. The reader's view is the set of (sender, value, delivery time) triples, and the
  reader may use any decision rule.
- Values in the attacks are of any type `V` (a fake `v′` is supplied); in the lower bounds they are `Bool`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 6 (corrected: `min n ((⌈T/Δ⌉+1) f)`) | `lemma6` (`Schedule.card_affected_le`, `Schedule.exists_card_affected_eq`) | `Model.lean` |
| Lemma 6 as stated is false | `lemma6_false` | `Model.lean` |
| Lemma 7 | `lemma7` | `Model.lean` |
| Theorems 8/9 false (CAM, `k = 1`: `2δ ≤ Δ < 3δ`) | `theorem9_false_k1` | `ReadAttack.lean` |
| Theorems 8/9 false (CAM, `k = 2`: `δ ≤ Δ < 3δ/2`) | `theorem9_false_k2` | `ReadAttack.lean` |
| Theorem 9 false at Table 1's parameters | `theorem9_false` | `ReadAttack.lean` |
| Theorems 11/12 false (CUM, `2δ ≤ Δ < 5δ/2` and `δ ≤ Δ < 5δ/4`) | `theorem12_false_k1`, `theorem12_false_k2` | `ReadAttack.lean` |
| Theorem 12 false at Table 3's parameters | `theorem12_false` | `ReadAttack.lean` |
| Theorem 3 (repaired, Section 4.4 model, any read duration) | `theorem3` | `LowerBound.lean` |
| Theorem 5 (repaired, Section 4.4 model, any read duration) | `theorem5` | `LowerBound.lean` |

**Not formalized.** Theorems 1 and 2, Lemmas 1–3 and Corollaries 1–2 (informal claims about all
protocols, with no system semantics to state them against). Theorems 4 and 6 (CUM lower bounds).
Lemmas 8–12 and 14–21, which prove correctness of the refuted protocols. Theorems 7 and 10 (termination;
the operations just wait `δ`, `2δ`, `3δ`).

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. The attack hypotheses are satisfied by explicit schedules and messages built in the
proofs, and the lower-bound executions are admissible by construction. The model is self-contained,
built on Mathlib only. CSLib candidate: the `ΔS` mobile-agent schedule with Lemma 6 (`Model.lean`).
