# Differences between the formalization and the paper

Paper: J. Skrzypczak, F. Schintke, T. Schütt, *Linearizable State Machine Replication of State-Based CRDTs
without Logs*, PODC 2019; full version arXiv:1905.08733v2 (numbering as there).

## Errors in the paper

1. **Lemma 3 is false.** It states that two learned states are comparable if one is learned by consistent quorum.
   The counterexample `Cex.run` (`Counterexample.lean`) uses five processes, majority quorums, the G-set over
   `{u₁, u₂}` and incremental prepares only. In it, query `B` learns `{u₁}` by consistent quorum and query `A`
   learns `{u₂}` by vote (`Cex.lemma3_false`).
   The proof's step "it follows from C1 and C2 that `a` has received p₁'s PREPARE in between p₂'s PREPARE and
   VOTE" applies C1 (stated for `Q₁ ∩ Q₂`) to a voter `a ∈ Q₁` that is not in `Q₂`. It also implicitly assumes that
   an acceptor which accepted another proposer's `PREPARE` first cannot assign p₂'s incremental prepare the same
   round number as the members of `Q₂` did. Earlier prepares (query `C` in the run) make the numbers coincide.
2. **Theorem 3 (Consistency) is false**: same execution (`Cex.theorem3_false`).
3. **Theorem 4 (Update Stability) is false.** `u₁` completes before `u₂` is invoked, and `A` learns `{u₂}`
   (`Cex.theorem4_false`). The proof claims "∄Q: a.r = r for all a ∈ Q, as all a ∈ Q_u updated their round". But
   acceptors of `Q_u` that receive the `PREPARE` after the `MERGE` hold round `r`. They may vote although their
   payloads (containing `u₁`) were not among the `ACK`s whose LUB is proposed.
4. **The main claim (linearizability, Section III-E applied to Algorithm 2) is false.** The history of `Cex.run`
   has no linearization for the G-set (`Cex.runHist_not_linearizable`, `Cex.not_linearizable`,
   `Cex.linearizableClaim_false`). For the paper's G-counter with the `sum` query this particular execution *is*
   linearizable; the counterexample needs a CRDT whose queries distinguish which updates are included.
5. **Lemma 4: correct, proof incomplete.** The proof does not treat equal round numbers of different attempts, and
   it relies without proof on round numbers of accepted prepares strictly increasing at each acceptor. Our proof
   (`lemma4`) uses three acceptor invariants:
   * round numbers of `ACK`s are at most `rnr`;
   * two `ACK`s of one acceptor with equal numbers have equal ids;
   * a `VOTED` for round `n` is below every later `ACK` with a number `> n`.
6. **Repair (ours).** An acceptor answers `VOTE(r', s')` only if `r' = r` *and* its payload before the merge is
   `⊑ s'` (`Variant.fixed`, flag `fix`). With it, Theorems 1–5 and linearizability hold (`fixed_*` in `Main.lean`).
   Theorems 1, 2, 5, Lemmas 1, 2, 4 and Corollary 1 hold for both variants.

7. **Versions.** The formalization follows arXiv v2 (2020). arXiv v1 (2019) has the same Algorithm 2 up to
   line numbering (updates and merges set `rid ← write` instead of `⊥`; `VOTE` accepted iff `r' = r`; prepares
   compared by round number only), and the same proofs of Lemma 3.6 and Theorem 3.9, so items 1–4 apply to it
   as well.

## Definitions and modelling choices

* **CRDT.** `CRDT` follows Definition 3: `S` is a `SemilatticeSup` with decidable `=`/`≤`, `app : U → S → S` is
  inflationary, and queries `query : Q → S → R`. We add a decidability assumption for the line-13 and VOTE tests.
* **Equivalence `≡`.** Line 13 is modelled by a Boolean test `cons` (`Variant`). All results assume
  `cons s t = true → s = t` (equality, `Variant.paper`). The paper defines `≡` as query equivalence. With a coarser
  test the proof of Lemma 2(i) breaks, since it needs `s' ⊑ a.s` for the learned LUB `s'`. We did not investigate
  that reading further.
* **Causal histories.** The paper treats `C(s)` as a function of the state, with `C(s₀) = ∅`, `u ∈ C(u(s))`,
  `C(s₁ ⊔ s₂) = C(s₁) ∪ C(s₂)`, and quotes `C(s₁) = C(s₂) ⇒ s₁ ≡ s₂`. We assume a map `H.C : S → Set U` with these
  properties, strengthening the second to `C(u(s)) = C(s) ∪ {u}` (the paper's intended meaning; needed for
  Validity). Theorems 1, 4, 5 and the linearizability results are stated for CRDTs having such a map. The G-set has
  one (`gsetHistory`); a G-counter whose state forgets update identities in general does not.
* **"Includes `u`"** is `u ∈ H.C s`; "update `u₁` precedes `u₂`" is CSLib's real-time order `Precedes` on
  operation instances with commands `upd u₁`, `upd u₂`.
* **Unique updates.** Assumed as a hypothesis `UniqueUpd h` in Theorem 4 and in the linearizability claim. The
  Section III-E theorem keeps the field `unique` of `LearnedHistory` for fidelity, although its proof does not use
  it.
* **Sequential specification.** `CRDT.spec`: the state is a payload, an update applies its command and returns
  `done`, a query returns `val (cmd_q s)` and does not change the state. The paper's equation (1)
  (`∃ s' ≡ q.s, C(s') = U_q`) is implied: the state after the preceding updates has causal history `U_q`, and
  `faithful` gives the same query result.
* **System model.** CSLib `Cslib.AsyncMP`:
  * channels are unordered and arbitrarily slow, with crash-stop processes;
  * message loss is not modelled separately, since safety concerns finite executions where undelivered messages
    are simply lost;
  * duplication is not modelled;
  * each process has at most one pending operation, as CSLib histories require. The paper allows many concurrent
    commands per proposer. The counterexample has one operation per process, so it is valid in the paper's model.
* **Processes and roles.** Every process is proposer and acceptor ("we assume that all processes implement both
  roles"). Messages to self go through the network.
* **Updates.** Lines 1–6: the local acceptor applies `u` (resetting `rid`), and `MERGE(s)` goes to the *other*
  acceptors. The update completes once a quorum has merged, counting the local acceptor as merged. This reading
  is more permissive than requiring a quorum of remote `MERGED`s. The counterexample's update collects a quorum of
  remote `MERGED`s anyway.
* **Queries.**
  * Line 10 `PREPARE` carries `s₀`; retries (line 23 and `retry`) carry the LUB of the received payloads (or the
    proposal).
  * Request ids are attempt ids `(p, k, j)`: process, operation index, attempt counter. The id `j` is fresh per
    attempt (`new_id()`); the round of an attempt is `(n, id)`.
  * The proposer acts (`advance`) on all `ACK`s of the current attempt received so far, once they contain a
    quorum; the paper acts exactly when a quorum is reached. The scheduler can always take `advance` right after
    the quorum-completing reception, so the paper's behaviour is included.
  * Line 16 "all rounds equal": all received round numbers equal (ids are equal by construction).
  * Line 22: the fixed retry uses number `max R̆ + 1`.
* **Retries after NACK** (Section III-B, not in Algorithm 2) are modelled by the internal action `retry n`, which a
  pending query may take at any time with any `n`. This is more permissive than "retry upon a NACK".
* **VOTED.** Carries the round and the state of the `VOTE`. The proposer counts `VOTED(s')` only for its current
  attempt, round and proposal, as line 24 "`VOTED, {s, …, s}`" suggests.
* **Ghost state.**
  * The learned state of each query and how it was learned (`Loc.learned`), written exactly at the response.
  * "Learned state" in Theorems 1–4 means the state learned by a query that has *returned*. A state learned and
    used for the response is the same thing in the model.
* **Statement forms.**
  * Corollary 1 is stated as: an `ACK` present in `C` carries a state `⊑` every `ACK` of the same acceptor sent
    later in an execution from `C`.
  * Lemma 1 is stated for steps from reachable configurations.
  * Theorem 1 is stated as: every update in `C(s)` was invoked by some operation that is not preceded by the query.
* **Lemmas 5–8.** Lemma 5 is the monotonicity of `C` (`CausalHistory.C_mono`). Lemmas 6–8 are replaced by an
  explicit construction (`linOrder`):
  * all invoked updates and all completed queries are sorted by `level · N + invocation index`;
  * a query that learned `s` has level `2·rank(s)+1`, where `rank(s)` is the number of learned states not above
    `s`;
  * an update `u` has level `2·urank(u)`, where `urank(u)` is the number of learned states not containing `u`.

  This is equivalent to rules S1–S3 and avoids the auxiliary query `r*`. Pending queries are dropped and pending
  updates kept, which is how the paper extends `H` to `H̄`.

## Not formalized

* Section III-F (finite-writes termination / liveness) and Section III-G (optimizations, batching).
* Section IV (experiments).
