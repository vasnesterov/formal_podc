# Delayed (inline) timestamps — PODC 2017

Sandeep S. Kulkarni, Nitin H. Vaidya. *Effectiveness of Delaying Timestamp Computation.* PODC 2017. DOI
[10.1145/3087801.3087818](https://doi.org/10.1145/3087801.3087818). Formalized version: the full version, arXiv
[1606.05962](https://arxiv.org/abs/1606.05962) v1 (N. H. Vaidya, S. S. Kulkarni, *Efficient Timestamps for Capturing
Causality*, June 2016; all proofs in Appendices A–C). No open copy of the PODC text was found, so the numbering
(Lemmas 1–4, Theorems 1–2, Appendices) follows the arXiv version.

**Verdict: 🔧 Easy fix.** The lower bounds for online vector timestamps (Lemmas 1–4), the matching `n − 1` upper
bound for the star graph (Appendix B.2) and the offline bound for the 4-process star (Theorem 2) all hold. The headline
inline algorithm (Theorem 1, `2c + 2` integers for a vertex cover of size `c`) is correct only for FIFO channels, which
the paper does not assume. A one-line change to the `next` field (keep the least receive index) repairs it for
arbitrary reliable channels.

## Mistakes in the paper

### 🔧 Theorem 1 (inline algorithm, non-FIFO channels)
With reliable but non-FIFO channels Theorem 1 is false: if `p_1 ∉ C` sends two messages to `p_0 ∈ C` and `p_0`
receives the second one first (event `f`), then the first send `e → f`, yet `Q_t(e).next[0] = 2 > 1 = Q_t(f).vect[0]`,
so `Q_t(e) ≮ Q_t(f)` (`theorem_1_false`).

**Impact.** Local fix; the headline result survives. Either assume FIFO channels (`theorem_1`), or let `next[j]` be
the *least* receive index of the messages `p_i` sent to `p_j` at or after `e` (`theorem_1_min`, any reliable channels).
The size `2c + 2` and the order `<` are unchanged.

**Details.** Section 2 defines `inbound(p_j, e) = recv(outbound(p_j, e))`, where `outbound(p_j, e)` is the *first*
message `p_i` sends to `p_j` at or after `e`. Section 4.2 and the example of Figure 2 then set
`next[j] = index(inbound(p_j, e))`. The paper's model has only "reliable bidirectional channels"; Lemma 1 even relies
on arbitrary delays, and nothing says FIFO. The control messages carry the index of the send event, which only makes
sense if acknowledgements can arrive out of order. Without FIFO, a later message from `p_i` may be received earlier,
and `next[j]` is then too large.

The literal pseudo-code (Steps 2–3 with the sets `N_e`, plus the remark that a finite `next[j]` is never changed)
gives the right value or the wrong one depending on which acknowledgement arrives first. If the acknowledgement of
the first message arrives first, it returns `next[0] = 2` as above. Appendix E's variant, which marks `next[j]` as
pending at the send, always returns 2.

The proof of Case 3 (Appendix A) reads `next[i]` as "the *earliest* event `g_i` at `p_i` created by a message from
the process of `e`". The "Intuition" paragraph of Section 4 also speaks of "the *earliest* event at each `p_j ∈ C`". That is the minimum, so the proof is correct for the repaired definition and wrong for the
algorithm.

**Repair.** In Step 3 use `τ(g).next[j] := min(τ(g).next[j], index(inbound(p_j, e)))`. The query must then wait for
the acknowledgements of all messages `p_i` sent to `p_j` in `[e, t]`. With this change, Theorem 1 holds for every
reliable execution (`theorem_1_min`). With FIFO channels the original definition already works (`theorem_1`). In
both versions the hypothesis `t ≥ e_r` is not needed; only `t ≥ f_r` is.

### Typos
- Proof of Lemma 1: "By event `e_{i,n−2}`" should be `e_{0,n−2}`.
- Proof of Lemma 2: the last computation event of `p_0` is called `e_{0,Pn}` with `P = (M+2)n`, and the gathering
  event `e_{0,Pn+n−2}`. Both should be `e_{0,P}` and `e_{0,P+n−2}`.
- Section 4.4: "timestamps for events at processes in `C` do include an id field" should read "outside `C`".
- Appendix E, second bullet: "for an event `e` at process `p_i ∈ C`, the `j`-th element of the `next` field" should be
  `p_i ∉ C`.
- Section 3: "vector connectivity" should be "vertex connectivity".

## Proof gaps (statements true)

### 🔧 Lemma 2 (integer entries, star graph)
The proof assumes "without loss of generality" that all entries are non-negative integers, which is not justified,
and it mixes up the maximum over the radial events with the maximum over `W` ("since `p_k ∉ W`" should be `p_k ∉ S`).

**Impact.** Statement true; repaired (`lemma_2`, general form `card_lt_of_online_int`).

**Details.** An algorithm may use negative entries, and there is no uniform shift. The repair replaces the bound "some
entry exceeds `M`" by a sum argument: along the chain of `P` local events of `p_0`, the coordinate sum grows by at least
1 per event, starting from a value fixed before `P` is chosen. The rest of the argument is the paper's: each radial
`k` owns a coordinate where it is the strict maximum, and `p_0`'s large coordinate is owned by none of them.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous message passing over an undirected communication graph `G`. An execution is the list of its events in
  real-time order: `send p q` (unicast), `recv p m` (receives the message sent at position `m`), `comp p`. Channels
  are reliable in the sense that each receive matches an earlier send to the receiver, at most once (`Exec.WF`); they
  are **not** FIFO unless `Exec.FIFO` is assumed. Messages use only edges of `G` (`Exec.OnGraph`). No failures, no
  randomness. Happened-before `→` is Lamport's (`Exec.HB`).
* **Online algorithm** (`IsOnlineTimestamping G A`): the timestamp of an event is `A` applied to the prefix of the
  execution ending with it. Timestamps must be distinct and satisfy `e → f ↔ τ(e) < τ(f)` on every execution over
  `G`. `A` may use the entire prefix (global knowledge, real-time order), which only strengthens the lower bounds.
  Vectors are `Fin s → α` with the componentwise order of Section 3, for any linear order `α`: reals, rationals,
  naturals. Lemma 2 uses `α = ℤ`.
* **Offline** (Theorem 2): any assignment of vectors to the events of a given execution.
* **Inline** (Theorem 1): `Q_t(e)` is the value the query of Section 4.2 returns (`query`). `vect` is computed by the
  algorithm itself (`inlineAlg`, merge-and-update). `next[j]` is given by its specification
  `index(recv(outbound(p_j, e)))`, with `outbound` evaluated at time `t`; the control messages are not simulated.
  The receive may happen after `t`, since the query waits for it.
* The B.2 algorithm is defined literally as a distributed fold (`starAlg`). "Any value in the open interval" is an
  arbitrary choice function `pick` (position, coordinate, old value) with the interval property.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 1 (star, real entries, `s ≥ n − 1`) | `lemma_1` | `LowerBounds.lean` |
| Lemma 2 (star, integer entries, `s ≥ n`) | `lemma_2` | `LowerBounds.lean` |
| Lemma 3 (vertex connectivity `≥ 2`, `s ≥ n`) | `lemma_3` | `LowerBounds.lean` |
| Lemma 4 (non-cut vertices `X`, `s ≥ |X|`) | `lemma_4` | `LowerBounds.lean` |
| General forms of Lemmas 1–4 | `card_le_of_online`, `card_lt_of_online_int` | `LowerBounds.lean` |
| §3 / B.2: `n = 2` needs length 2, vector clocks suffice | `two_le_of_ne`, `appendix_B2_two` | `LowerBounds.lean`, `StarUpper.lean` |
| Appendix B.2 (star, `n ≥ 3`, length `n − 1` suffices) | `appendix_B2` | `StarUpper.lean` |
| B.3.2 remark (cut vertex as centre, length `n − 1`) | `starOnline_isOnline` | `StarUpper.lean` |
| Upper bound `n` by vector clocks | `vectorClock_isOnline` | `Podc/…/Causality/VectorClock.lean` |
| Theorem 1 (FIFO channels) | `theorem_1` | `Inline.lean` |
| Theorem 1 false without FIFO | `theorem_1_false` | `Inline.lean` |
| Theorem 1 repaired (least receive index) | `theorem_1_min` | `Inline.lean` |
| Inline timestamps are distinct | `query_injective` | `Inline.lean` |
| Theorem 2 (4-process star, offline, length 2 impossible) | `theorem_2` | `Offline4.lean` |

Remarks.
* Lemmas 1, 3 and 4 are one theorem (`card_le_of_online`): if for every `k ∈ X` the other processes of `X` can reach a
  common `r ≠ k` without passing through `k`, then `s ≥ |X|`. The paper's flooding with tuned delays is replaced by
  explicit routing along walks that avoid `k` (`Routing.lean`). Lemma 4 needs only that `G` is connected with at least
  2 vertices, not vertex connectivity exactly 1.
* The paper omits the correctness proof of the B.2 algorithm ("straightforward"). It holds, and more generally with
  any cut vertex as centre (`starAlg_captures`): `⌊v[k]⌋` is the vector clock entry of `p_k` (`floor_ts`). An event
  of the centre is detected through a coordinate in another component of `G − c`, which can reach `f` only through
  the centre (`ts_cut_invariant`).
* Theorem 2: the paper's proof is a Z3 run. We give a manual proof. Each coordinate must place `E7` between `E3` and
  `E5`, and `E4` between `E3` and `E7`, which contradicts `E5 → E4`. Distinctness of timestamps is not used.
* Theorem 1 never uses the hypothesis `t ≥ e_r`.

**Not formalized.** The control-message protocol of Section 4.2 and the optimizations of Appendix E. Section 5 and
Appendix D are related work. The `n = 1` case of B.2 is trivial.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
hypotheses are satisfiable: vector clocks (`vectorClock_isOnline`) and the B.2 algorithm with the midpoint choice
(`midPick_spec`) are online timestamping algorithms, and the counterexample execution is well formed, uses only star
edges and satisfies the vertex-cover hypothesis (`theorem_1_false`). The execution model, happened-before, merge-and-update
algorithms and vector clocks are staged in `Podc/Computability/Distributed/MessagePassing/Causality/` (CSLib candidates).
