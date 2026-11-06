# A Paradox of Eventual Linearizability in Shared Memory — PODC 2014

Rachid Guerraoui, Eric Ruppert. *A Paradox of Eventual Linearizability in Shared Memory.* PODC 2014.
DOI [10.1145/2611462.2611484](https://doi.org/10.1145/2611462.2611484). Formalized version: the EPFL
Infoscience copy of the PODC paper (10 pages, with the appendix proving Proposition 11); no arXiv
version.

**Verdict: 🔧 Easy fix.** Eventually linearizable objects cannot implement any non-trivial linearizable object
(Theorem 12, Proposition 14), they make consensus easy (Proposition 16), and an eventually linearizable non-blocking
fetch&increment can be turned into a linearizable one (Lemma 17, Proposition 18). This needs only the implied assumption
that operations are total, which the paper's model leaves out although every type it uses is total, and a local repair
of one wrong step in the proof of Lemma 17. The claim that eventually linearizable objects do not boost the consensus
power of registers (Proposition 15) was not checked.

## Mistakes in the paper

### ✏️ Slips
- **Partial operations: Lemma 6 (prefixes of `t`-linearizable histories).** Lemma 6 is false for types whose operations
  are not applicable in every state: the paper's `δ ⊆ Q × OP × RES × Q` may leave an operation without a transition
  (`lemma6_false_partial`). The lemma and its proof are correct for total types (`TLinearizable.prefix`,
  `tLinearizable_take_self`), and every type the paper uses is total. So are its other uses of totality ("a prefix of
  length at most `t` is trivially `t`-linearizable", "any permutation yields a legal sequential history").

  Counterexample: take a one-bit object whose operation `use` is only enabled once `enable` has set the bit. Process 0
  runs `use` (events 1–2), then process 1 runs `enable` (events 3–4). With `t = 2` the history is `2`-linearizable: the
  order `enable`, `use` is legal, and `use` responded among the first two events, so its response is unconstrained. The
  prefix of length 2 is not `2`-linearizable: it contains only `use`, which must be linearized and cannot be applied in
  the initial state. The proof breaks when it completes the early operations "with the responses they would have if
  executed in that order".
- **Partial operations: Theorem 12 and Proposition 14 (base objects that never respond).** Both need base objects whose
  operations always have a legal response (total types with an initial state), which the paper never states. Every base
  object in the paper is total, and the proof of Theorem 12 presupposes it. With it added (`theorem12`, `prop14`), both
  results hold.

  The model only says a programme "can invoke an operation on a base object and await a response". If a base type has an
  operation with no transition, no response to it is weakly consistent, so the caller waits forever. An implementation of
  any type whose operations all start with such a call never responds. It is therefore linearizable, and it is vacuously
  obstruction-free: no process takes infinitely many steps. So item 4 of Theorem 12 holds for every type, while item 1
  fails for registers. This is argued in prose, not as a Lean counterexample.
- **Partial operations: Lemma 8, "if" direction (weak consistency is local).** The proof inserts the process's operations
  on other objects "with responses as dictated by the objects' sequential specifications", which needs total operations.
  The statement is true even without totality (`weaklyConsistent_iff_restrict`): for each other object, take the
  weak-consistency witness of the process's last operation on it, and concatenate these witnesses (they are on different
  objects) before `op`'s own witness.
- **Claim 1 in the proof of Proposition 18** applies Lemma 17 with `t = ℓ₀ = 0`, outside its hypothesis `t > 0`. Lemma 17
  holds for `t = 0` (`lemma17`).

## Proof gaps (statements true)

### 🔧 Lemma 17 (fetch&increment: `t`-linearizable prefixes ⇒ `t`-linearizable)
In the real-time case `op₂ ∈ A₄`, the proof's claim that in a `t`-linearization of the prefix with all
responses `≤ v` "all the slots of `E` prior to slot `v` are filled using operations of `A₁` and
operations of `A₄`" is false.

**Impact.** The statement stands, with a repaired proof (`lemma17`). The hypothesis `t > 0` is not needed.

**Details.** An operation of `A₂ ∪ A₃` that is still pending in that prefix, and later returns a value
`> v`, can occupy an `E`-slot below `v`. Example with `t = 1`: `x`, `z` and `y` are invoked at positions
0, 1, 2, and `y` returns 1 at position 3. Later `x` returns 2, and `z` never returns. The paper's prefix
ends at `y`'s response, and `x(0), y(1)` is a `1`-linearization of it. Slot 0 is in `E` and holds `x ∈ A₃`.

**Repair.** Take instead a prefix containing `op₁`'s response and the responses of all late operations
invoked before `op₂`. In any `t`-linearization of it, the `E`-slots below `v` hold operations of
`A₁ ∪ A₄` invoked before `op₁`'s response (`count_free_le`). With finitely many processes the bound
`|E| ≤ |A₁| + |A₄|` then follows from the prefixes alone. The `t₀`-linearization is needed only for
`|A₁| ≤ |E|`.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Histories* (Section 3) are finite or infinite *timed* sequences `ℕ → Option Ev`. An operation is
  named by the position of its invocation, and a response event names the operation it answers.
  Positions without events are allowed. On gap-free histories, "the first `t` events" are the
  positions `< t`. Sequential histories are `ℕ`-indexed (possibly infinite), and legality is per
  object. Weak consistency (Definition 1), `t`-linearizations (Definition 2) and eventual
  linearizability (Definition 3) are transcribed literally.
- *Implementations* (Section 3) are asynchronous, with deterministic processes of arbitrary
  (infinite) state. A process may stop forever (crash). Executions are infinite label sequences; a
  finite execution is one that is eventually idle. The environment invokes arbitrary operations.
  Each step writes its event at its own position, so `t` counts steps.
- *Eventually linearizable base objects* (Theorem 12, Propositions 14 and 16): a base access is an
  invocation step plus a later response step of the same process, so base objects are wait-free. The
  adversary chooses the response values. An execution is admissible iff every base object's history
  is eventually linearizable for its type. Base types are total, with initial states (needed for
  wait-freedom).
- *Linearizable base objects* (Proposition 18) are atomic: one step applies a transition of a
  possibly nondeterministic total type. The implementation fixes the initial states of the base
  objects; Proposition 18's `A'` uses the states of the stable configuration `C₀`, as in the paper.
- Progress conditions: wait-free (a process taking infinitely many steps completes each of its
  operations), obstruction-free (likewise, if from some time on only it steps), non-blocking (if an
  operation is pending and steps continue, some operation completes). There is no randomness and no
  failure detector.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Definitions 1–3 | `WeaklyConsistent`, `IsTLin`, `TLinearizable`, `EventuallyLinearizable` | `Defs.lean` |
| Lemma 5 | `TLinearizable.mono` | `Basic.lean` |
| Lemma 6 (total types) | `TLinearizable.prefix` | `Basic.lean` |
| Lemma 6, false for partial types | `lemma6_false_partial` | `Counterexamples.lean` |
| Lemma 7 (finitely many objects, infinite histories) | `exists_tLinearizable_iff_restrict` | `Locality.lean` |
| Lemma 8 | `weaklyConsistent_iff_restrict` | `Locality.lean` |
| Proposition 9 | `eventuallyLinearizable_iff_restrict` | `Locality.lean` |
| Prop. 9 fails with infinitely many objects (§3.2) | `prop9_false_infinite_objects` | `Locality.lean` |
| Lemma 10 | `weaklyConsistent_isSafety` | `Basic.lean` |
| §3.2: `t`-linearizability not limit-closed (`t > 0`) | `tLinearizable_not_limitClosed` | `Safety.lean` |
| §3.2: "`t`-linearizable for some `t`" is a liveness property | `exists_tLinearizable_isLiveness` | `Basic.lean` |
| §3.2: linearizability is a safety property (finite nondeterminism) | `linearizable_of_forall_take` | `Safety.lean` |
| §3.2: not with infinite nondeterminism | `linearizable_not_limitClosed_of_infiniteNondet` | `Safety.lean` |
| Theorem 12 | `theorem12`, `localImpl_correct` | `Theorem12.lean` |
| Proposition 14 | `prop14` | `Prop14.lean` |
| Proposition 16 | `prop16` | `Prop16.lean` |
| Lemma 17 | `lemma17` | `Lemma17.lean` |
| Proposition 18 (Claim 1: `claim1`) | `prop18` | `Prop18.lean` |
| Corollary 19 (reduction to the classical impossibility) | `cor19_of_no_linearizable` | `Prop18.lean` |

Theorem 12 holds for any finite number of processes, not only `n ≥ 2`. Its delicate step is sound: the
local-copy histories are weakly consistent, and every finite prefix is eventually linearizable
(`sim_weaklyConsistent`, `sim_solo_isLin`). Claim 1 of Proposition 18 needs no König's lemma: the
infinite path is built directly. König's lemma is used only for the safety of linearizability, which
Theorem 12 needs. Proposition 16 is proved register by register, without Lemma 7.

**Not formalized.**
- Proposition 11 (appendix).
- Proposition 15 (valency argument), so it is open here whether eventually linearizable objects can boost the consensus
  power of registers.
- The remark after Proposition 18 (obstruction-free and wait-free variants) and the test&set and one-shot remarks of
  Section 4.
- The classical fact behind Corollary 19 (registers cannot solve two-process consensus, while a linearizable
  fetch&increment and registers can): only the reduction is proved, and this fact is a hypothesis.
- Computability in Definition 13 and Proposition 14: dropped on both sides of the equivalence.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Non-vacuity: `trivImpl` is a linearizable wait-free implementation of every trivial
type (so the conditions of Theorem 12 are satisfiable), and `consImpl` is a concrete eventually
linearizable consensus. The model is self-contained: it uses Mathlib only, not CSLib's
shared-memory model. Weak consistency and `t`-linearizability here follow this paper's definitions,
which differ from Serafini et al.'s (`Papers/PODC2010/EventualLinearizability`).
