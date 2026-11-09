# Differences between the formalization and the paper

Paper: Bonomi, Dolev, Potop-Butucaru, Raynal, *Stabilizing Server-Based Storage in Byzantine
Asynchronous Message-Passing Systems*, PODC 2015; formalized from the full version arXiv:1503.00140v1
(numbering of lemmas/theorems/figures follows it).

## Mistakes of the paper (labels: `mistakes-labeling.md`)

1. ❌ **Theorem 3 / Lemma 13 (Fig. 3, practically stabilizing SWSR atomic register) are false.**
   `Atomic.theorem3_false`: a fair infinite execution (`n = 9`, `t = 1`, one Byzantine server,
   sequence numbers mod `2^64 + 1`) with a new/old inversion between two regular reads in every
   158-step cycle, forever. The step of Lemma 13 that fails: "the local sequence number can be reset
   to a value smaller than `sn1` only if [...] N6 [...] the writer sequence number wrapped around" —
   N6 lowers `pwsn` whenever `2t + 1` servers still hold an older helping pair, which is the normal
   situation (`Atomic.Cex.sanity_check_lowers_pwsn`). Every choice at a threshold test in the
   counterexample is the freshest candidate (`Atomic.Cex.cycle_allFresh`), so the ambiguity of
   line 12 ("let `v` be this value" when two values have `2t + 1` copies) is resolved in the most
   natural way. A variant (`Atomic.Cex.variant_labels`, `Robust.lean`; a finite execution up to the
   inverted read) has the same inversion when every choice is also the strictly most frequent
   candidate (`Atomic.Cex.variant_allMostFrequent`). The execution respects the "system-life-span"
   bound of Section 4 (four writes between successive write-free reads) and the bound of Lemma 13
   (each read overlaps at most four writes). No repair proved; removing N6 breaks stabilization from a corrupted `pwsn`, which is
   what N6 is for.
2. (consequence of 1, not a separate mistake) **Theorem 4** (MWMR register) is built from the SWMR
   registers of Section 5.1, themselves built from Fig. 3; its premise fails. Fig. 4 itself was not
   checked.
3. ✏️ **Lemma 9** claims `4t + 1` *correct* servers share the helping pair when a write returns; when
   the test of line 03 fails because `4t + 1` acks agree, up to `t` of them are Byzantine, so only
   `3t + 1` correct servers are guaranteed (`Atomic.Cex.lemma9_false`). `3t + 1` (stated correctly in
   Claim C(b) of Lemma 2) suffices for the later uses.

## Proof gaps of true statements

4. 🔧 **Lemma 2** (read termination, Fig. 2). The many-writes case assumes that the first write after the
   reset sees `4t + 1` acks `⊥` and refreshes; false when `NEW_HELP_VAL`s of concurrent writes are
   delivered after the reset. The proof also refers to `τ_stab` (defined in Lemma 3) and confuses "`2t + 1`
   replies carry `x` or `y`" with "`2t + 1` replies carry the same value". Repaired with a different
   argument (`Regular.lemma2_read_terminates`), which needs only `n > 6t`.
5. 🔧 **Lemma 3** (regularity, Fig. 2). Returns through the helping values (line 15) are not argued, and
   the "and so on" induction over concurrent writes is not given. Repaired with an invariant
   (`Regular.lemma3_regular`, `Regular.lemma3_regular_exec`); holds for every `n` and from the return of
   the first write on (`τ_stab = τ_1w`).

## Stronger / different statements in the formalization

- Theorem 1 is proved with `6t < n` (paper: `8t < n`); regularity needs no bound on `n`.
- Theorem 1 assumes assumption (b) of the paper (at least one write is invoked) only for read
  termination; it is used in the form "some `invWrite` occurs in the execution".
- Liveness is stated for fair infinite executions (`Regular.Fair`): every correct server eventually
  delivers each pending message (its link is empty or shrinks infinitely often), and each client's
  enabled step is eventually taken (weak fairness). Byzantine servers are not required to do anything.

## Modelling choices and their effect

- **Asynchronous message passing, interleaving semantics.** One step = one server delivering the
  head of one of its two incoming FIFO links, or one client action. Processing is instantaneous
  (as in the paper).
- **`ss-broadcast` axiomatised**, as in the paper: a broadcast appends the message to the link of
  every server; *no duplication*, *validity* and *FIFO order* hold by construction; *synchronized
  delivery* (`n − 2t` correct servers deliver during the call) is the guard of the client step that
  ends the broadcast (`syncW`, `syncR`); *termination* and *eventual delivery* are fairness
  conditions. The bounded-capacity data-link implementation (footnote 3) is not modelled.
- **Acknowledgment matching (favourable to the paper).** The paper relies on FIFO order to match
  `ACK_WRITE`/`ACK_READ` with the client's broadcasts, without sequence numbers (Remark of
  Section 3.1). We record a server's reply in a ghost slot only if it answers the client's *current*
  broadcast; stale replies (to older broadcasts, or initial garbage in the reverse links) are never
  used. Without this, garbage acknowledgments in the initial link contents (allowed by the paper's
  failure model) could shift the reply streams permanently; we do not claim this as a mistake.
- **Transient failures.** `τ_no_tr = 0`. The initial configuration is arbitrary for the servers and
  for the links from the clients (garbage messages are delivered before the messages broadcast
  later on the same link, as with the stabilizing data link of footnote 3). For Fig. 2 the clients
  start between operations (an operation in progress at `τ_no_tr` is not modelled); their local
  variables are reset at each invocation anyway. The counterexample to Theorem 3 starts from a clean
  configuration, which only makes it stronger.
- **Byzantine servers** (`B`, `#B ≤ t`) are modelled by arbitrary replies in every collection; their
  local states are irrelevant. They may answer the writer and the reader differently.
- **Threshold tests with several candidates** (lines N4, 12, 14 when two values both have `2t + 1`
  copies): the pseudo-code does not say which one is taken; the model allows any. See item 1 for why
  the counterexample does not depend on this.
- **Sequence numbers**: `Fin m` with `m = 2^64 + 1` in the counterexample, compared with `>cd`
  (`gtcd x y := (x − y) mod m < (y − x) mod m`, the paper's clockwise-distance order).
- **Values** in the counterexample are natural numbers, each written once (write `j` writes `j`), so
  inversions are unambiguous.
- **Specifications.** Regularity and new/old inversion are stated on the sequence of invocation /
  response events (`ReadOp`, `WriteOp`, `RegularRead`, `Inversion`); "eventual" = there is a finite
  `τ_stab` per execution (`EventuallyNoInversion`). For Fig. 2, regularity is proved with ghost
  variables (`vals`, `nDone`, `base`) recording the write history; they are never read by the
  algorithm.
- **Mobile Byzantine faults** (footnote 1) are not modelled.

## Not formalized

- Theorem 2 / Lemmas 4–6 (synchronous links, Fig. 5, `t < n/3`).
- Lemmas 7, 8, 10–12 (liveness and eventual regularity of Fig. 3) individually: Theorem 3 is refuted
  through Lemma 13. The "practical" stabilization from a corrupted `pwsn` (Lemma 12) is not checked.
- Section 5.1 (SWMR from SWSR registers, one paragraph) and Fig. 4 / Lemmas 14–18 (MWMR from SWMR,
  bounded epochs of [1]).
