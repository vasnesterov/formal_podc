# Store-collect over an abstract MAC layer — PODC 2022

Lewis Tseng, Qinzi Zhang. *Brief Announcement: Computability and Anonymous Storage-Efficient Consensus with an
Abstract MAC Layer.* PODC 2022. DOI [10.1145/3519270.3538462](https://doi.org/10.1145/3519270.3538462).
Formalized version: the 3-page brief announcement (no arXiv version); numbering as there.

**Verdict: ⚠️ Minor statement issues.** Theorem 1 holds: MAC-SC (Algorithm 1) implements a regular
store-collect object in the single-hop abstract MAC layer with any number of crashes. We prove it in a model
where stored values carry sequence numbers, which is how the paper says uniqueness is obtained. The paper's
assumption (iii), that the message handler has priority over the main thread, is really needed for this. But
taken literally, it lets the adversary starve a node's main thread, so the abstract's claim that "all of the
algorithms are wait-free" fails for MAC-SC. A weaker form of (iii), which is all the proof uses, keeps both
properties.

## Mistakes in the paper

* **MAC-SC is not wait-free under assumption (iii) as stated.** The abstract says all algorithms are
  wait-free. Section 2 says the handler processes queued messages one by one and "has a priority over the
  execution of the main thread". So line 1 or line 4 of an operation can run only when the handler's queue is
  empty. Take two nodes. Node `1` runs `Store₁` operations forever. In every round, its new message reaches
  node `0` before node `0`'s handler has processed the previous one. Node `0`'s queue then always holds one or
  two messages and is never empty. In this infinite execution nobody crashes, every broadcast is delivered and
  acknowledged, and node `1` completes one operation per round. Node `0`'s handler processes every message it
  receives, within two rounds. Yet node `0`'s `Collect₀` never executes line 4 and never returns. The property
  is false as written, but the intended fix is local and can be read off the proof of Theorem 1. The proof only
  needs the messages delivered *before an operation's invocation* to be processed before its line 1/4. Under
  that weaker rule the main thread cannot starve. We classify it as a missing implied assumption (R3/R4). It is
  borderline: a reader who takes the paper's asynchrony literally gets a non-wait-free algorithm.
  (`Starvation.mac_sc_not_wait_free`)
* **Assumption (iii) is necessary for Theorem 1 (not an error; the paper does assume it).** Suppose the main
  thread may read `view_i` while delivered messages are still queued. Node `0` completes `Store₀(7)`, and its
  message waits in node `1`'s queue. Node `1` then invokes `Collect₁` and returns `∅`. This violates Property
  I(i). The proof sketch of Property I ("node `i` has not received any message from `j`'s mac-broadcast") and
  of Property II both use (iii) silently. (`theorem_1_needs_priority`)
* **Minor imprecisions** (the statements are unaffected):
  - The merge `A ∪ B` keeps "the newer value from each node". The paper calls this well defined because values
    are unique and operations sequential. But a node cannot compute it from unique values alone, because a stale
    view can arrive after a newer one. It needs the sequence numbers that the paper mentions as the way to
    make values unique. We tag every stored value with the index of its store operation and merge by that
    index.
  - The proof sketch of Property II says that when a mac-broadcast completes "all the fault-free nodes have
    received the broadcast message". What is needed, and what the MAC layer gives, is "every node not crashed
    yet". The node of the later collect may crash after that collect returns, so it need not be fault-free.
  - Property I(ii)'s "we can prove by contradiction" is left to the reader. The argument needs the merge to
    never replace an entry by an older one, which again relies on sequence numbers.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Model.lean`).
* Asynchronous, single-hop abstract MAC layer, deterministic nodes, any number of crash failures. Nodes form an
  arbitrary type `ι` (possibly infinite); the algorithm never uses `n`.
* Events: client invocation (only at an idle node, so at most one pending operation); lines 1–2 / 4–5, which
  compute `currentView` and start `mac-broadcast`; delivery of a broadcast to any node, at most once per node,
  even after the sender crashed; one handler step, which pops the first queued message and merges it (lines
  7–8); the acknowledgment, enabled once every node that has not crashed yet has received the message; the
  return (lines 3/6); crash. Any interleaving is allowed.
* Handler priority (`prio = true`): lines 1/4 may run only when the node's queue is empty.
* Histories are lists of `inv i n o` / `ret i n r` events, where operation `(i, n)` is the `n`-th operation of
  node `i`. The real-time order is the order in the list. Regularity (`Regular` = `RegularI` ∧ `RegularII`)
  transcribes the paper's two bullets and `⪯`. A view maps each node to an optional `(index, value)` entry.
* Theorem 1 is quantified over all finite executions (`Reach true c h`), so it covers every prefix of every
  infinite execution.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (MAC-SC implements a regular store-collect object) | `theorem_1` | `Main.lean` |
| Assumption (iii) is needed (counterexample without it) | `theorem_1_needs_priority` | `Main.lean` |
| Abstract: "all of the algorithms are wait-free" — fails for MAC-SC under literal (iii) | `Starvation.mac_sc_not_wait_free` | `Starvation.lean` |
| Non-vacuity: a collect after a completed store sees it | `collect_sees_store` | `Main.lean` |

Proof structure: `Invariant.lean` defines the inductive invariant (`HInv` holds the history well-formedness and
`PastOK`, the facts a collect records when it reads its view; `Knows` says that the broadcast of every completed
operation is in the view or queue of every live node). `Preservation.lean` proves that every step preserves it.
`Regular.lean` derives regularity from it.

**Not formalized.** The stacked constructions of [4] (snapshots, counters, multi-writer registers) and the
anonymous approximate / randomized consensus algorithms of the full paper (they are only mentioned in the
BA). Under the repaired priority rule, both regularity and wait-freedom are argued in prose only (Theorem 1 is
proved under the literal rule (iii)).

**Trust.** No `sorry`. `theorem_1`, `theorem_1_needs_priority`, `collect_sees_store` and
`Starvation.mac_sc_not_wait_free` use only the axioms `propext`, `Classical.choice` and `Quot.sound`. The model
is self-contained and paper-specific. The staged `Podc/Computability/Distributed/AbstractMAC/` model is built
for consensus impossibility proofs: it has binary inputs and decisions, no client operations, and acks that wait
for crashed nodes. So it is not reused here. No CSLib candidates.
