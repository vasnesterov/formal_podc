# Differences between the formalization and the paper

Paper: Abraham, Malkhi, Spiegelman, *Asymptotically Optimal Validated Asynchronous Byzantine
Agreement*, PODC 2019, arXiv:1811.01332v1 (the only arXiv version). Numbering follows arXiv v1.

## Errors and gaps in the paper

1. **The thresholds `2f + 1` are only correct for `n = 3f + 1`.** *(False statement for
   `n > 3f + 1`; correct for `n = 3f + 1`.)* The model allows any `f < n/3` (§2, Theorem 1).
   But the protocol hard-codes `2f + 1` as the signature threshold (threshold validation), as the
   number of `done`/skip shares and as the number of view-change messages waited for. Two proofs
   use `n = 3f + 1`:
   - Lemma 3 (PB-provability): "there are at least `f + 1` honest parties in `P_j`, and thus there
     is an honest party in both `P_1` and `P_2`". This needs `2(f + 1) > n - f`.
   - Lemma 8: "`2f + 1 = n − f`".
   - Lemma 23 also computes the success probability as "`(2f + 1)/(3f + 1) > 2/3`", i.e. with
     `n = 3f + 1` (with threshold `n − f` it is `(n − f)/n > 2/3`).

   The paper never restricts to `n = 3f + 1`: §2 says "the adversary may control up to
   `f < n/3` parties", and so do Theorem 1 and §3. The only occurrence of `n = 3f + 1` is the
   introduction's definition of optimal resilience. Theorem 1 itself (an existence claim) still
   holds, since the protocol with threshold `n − f` works.

   For `n = 5`, `f = 1` we give a reachable run of the model (58 steps) with threshold `3`. The
   corrupted party 4 is elected leader of view 1 and equivocates in all four stages. Honest parties
   0 and 2 decide `true` and `false` (`Counterexample.agreement_fails`). A shorter run
   (`provability_fails`) shows that PB-provability already fails at stage 1.

   With the threshold `Q = n − f`, everything is proved for every `n > 3f`. Safety needs
   `n + f < 2Q`, liveness `Q ≤ n − f`.
2. **Termination is proved vacuously, and Efficiency fails as stated.** *(Proof gap,
   under-specified protocol.)* The main loop of Algorithm 6 never exits: deciding (Algorithm 7,
   line 27) does not stop a party. The proof of Lemma 20 says: "the number of views in the
   protocol is unbounded, and thus honest parties never stop sending new messages. Therefore,
   termination trivially follows." This uses the vacuity of "all messages have been delivered".
   For the same reason the total number of messages sent by honest parties is infinite, so the
   Efficiency property of Definition 4 does not hold. Lemma 24 bounds only the messages sent
   before all honest parties decide.

   The intended statements are:
   - every view completes (Lemma 19);
   - each view succeeds with probability `≥ 2/3`, independently of the past (Lemma 23).

   A halting rule is still needed, e.g. forward the commit certificate and halt. A party cannot
   halt right after deciding: other honest parties may only have locked in that view, and they
   need its messages in the next view.

   We formalize the per-view statements (`view_progress`, `decide_of_completed`,
   `card_undecided_le`, `expected_views_lt`). We do not formalize a halting mechanism or the
   message count.
3. **Algorithm 6, line 4: `j ≠ 1` must be `j ≠ 0`.** *(Typo in the pseudocode.)*
   - In `EX-BC-VALIDATION(id, ⟨v, ⟨j, σ⟩⟩)`, `j` is the view of the *key*, and the initial key is
     `⟨0, ⊥⟩`.
   - Read literally, every honest proposal of view 1 is rejected: `threshold-validate` with
     `L[0] = ⊥` and `σ = ⊥` fails. So view 1 never completes.
   - Read literally, keys of view 1 are also accepted without any check.
   - The proof of Lemma 15 ("a valid key is not required in view 1") reads `j` as the *current*
     view. That reading also fails: in view 2, a party that got no key in view 1 still proposes
     with `⟨0, ⊥⟩`, and every honest party rejects the proposal.

   We use: a key `⟨r, σ⟩` is valid iff `r = 0`, or `σ` is a stage-1 certificate of the leader of
   view `r`; and `r ≥ LOCK`.
4. **View-change messages that arrive before the receiver knows the leader.** *(Under-specified
   pseudocode.)*
   - Algorithm 7, line 25 uses `L[j]`, which is `⊥` until the receiver's own `elect` returns.
   - Fast parties may send their view-change messages of view `j` before that.
   - Read literally, such a message fails validation and its content is lost, yet it may still
     count among the `2f + 1` messages of line 23.
   - Lemma 8 ("every honest party gets a view-change message that includes …") needs these
     messages to be buffered until `L[j]` is known.

   We model that: `recvVC` and `recvQC` require the receiver to know the leader. We have not
   checked whether the literal reading breaks agreement; our partial analysis suggests that a
   party's own view-change message often saves it.
5. **Lemma 14 is stated too weakly for its use in Lemma 15.** *(Proof gap; the statement used is
   true.)*
   - Lemma 14 covers a party that sets `LOCK` to `j` *in view `j`*.
   - View-change messages are processed whenever they arrive, so a party can set `LOCK` to `j`
     later, in some view `> j`.
   - Lemma 15 needs: for every `LOCK` value `i` of every honest party, all honest parties that
     left view `i` have `KEY` of view `≥ i`.

   This holds by the same quorum argument; it is our `Inv.key_of_lockQC`. Lemma 15 itself is
   `proposal_valid`.
6. **Lemma 6 covers only stages `{2, 3, 4}`, but Lemma 12 uses it for stage 1.** *(Imprecise
   statement; the proof covers stages `1–4`.)* Our `Inv.qc_agree` covers all stages.
7. **Quality** (Definition 4: "the probability of choosing a value that was proposed by an honest
   party is at least `1/2`") is required in Definition 4. It is never proved and is not mentioned
   in Theorem 1's proof. *(Missing proof.)* Not formalized. Remark, not a claim: against an
   *adaptive* adversary, "proposed by an honest party" is delicate, since the adversary may
   corrupt the elected leader after the coin is revealed.
8. Typos:
   - Algorithm 3, line 5: `return σ` should be `return σ_in`.
   - Algorithm 7, lines 28 and 30: `lock` and `key.round` should be `LOCK` and `KEY.view`.
   - Algorithm 7, lines 22–23 forward a `skip` message even if its signature is invalid.
   - Lemma 21: "`2f = 1`" should be "`2f + 1`".
   - Lemma 3's proof writes `σ'_1` for `σ'_j`.

## Modelling choices (formalization vs. paper)

- **Cryptography as ideal functionalities.**
  - A threshold signature on a statement exists iff at least `Q` parties produced shares on it
    (`QC`).
  - Corrupted parties may produce any shares (`byzSign`). Honest parties produce shares only by
    the protocol.
  - Anybody may forward existing certificates. Certificates cannot be forged.
  - The "except with negligible probability" qualifiers are therefore dropped.
- **Common coin.**
  - The leaders form a sequence `c : ℕ → P`.
  - The coin of view `j` is *revealed* when the first honest party invokes `elect` for view `j`:
    together with the `f` shares of the corrupted parties, one honest share determines the coin.
  - A party learns the coin when its own `elect` returns, which needs the coin to be revealed.
  - Unpredictability is exact. The adversary's choices are functions of the history of states,
    and states contain only revealed coins (`ExpectedViews.lean`, `good_congr` is *proved*).
- **Asynchrony.**
  - Executions are interleavings of actions whose guards hold. There are no explicit message
    buffers.
  - A message may be received iff its sending event happened. A PB message of an honest
    proposer must be its proposal (`SentBy`). A view-change message of an honest sender carries
    its frozen deliveries (`Past`). `done` messages are abstracted to "a stage-4 certificate
    exists" (`completed`).
  - The proposer's collection of shares is not modelled: the stage-`s` message of an honest
    proposer may be delivered as soon as a stage-`(s − 1)` certificate on its value exists.
  - These are over-approximations for safety. Under them, honest proposals still pass
    validation (Lemma 15) and views complete (Lemma 19, constructive form).
- **Adversary.**
  - Adaptive corruption of at most `f` parties (`corrupt`). A corrupted party's local state is
    frozen.
  - All local invariants hold for every party; decisions of a party made while it was honest
    are covered by `agreement`.
  - For the probabilistic statements the adversary is a deterministic strategy on histories that
    sees everything except unrevealed coins. A randomized adversary is a mixture of these, so the
    bounds still hold.
- **Agreement and validity** are stated for all decisions made by honest parties at any time,
  including several decisions by one party (`decs` is a set). This is stronger than "all honest
  parties that terminate decide the same value".
- **Probability.** "Probability `≥ 2/3` per view" (Lemma 23) and "`< (1/3)^l`" (Lemma 24) become
  counts over uniform coin sequences `x : Fin k → P` for the views `1, …, k`:
  - `card_undecided_le`: at most `(n − Q)^k` of the `n^k` sequences let some party leave view `k`
    undecided;
  - `prob_undecided_le`: probability `≤ (f/n)^k`, with `f/n < 1/3`;
  - `expected_views_lt`: the expected number of views up to the first view whose leader
    completed before the coin was revealed is `≤ n/(n−f) < 3/2`, truncated at any horizon. This
    uses the shared coin game `Podc/Probability/CoinGame.lean`.
- **Liveness** (Lemmas 7, 17–19) is formalized in the constructive form `view_progress`. From any
  reachable state, honest steps alone (delivering honest messages) bring every honest party past
  the current view. We did not formalize the statement for all fair schedules.

## Not formalized

- Word/message complexity: `O(n²)` words per view, PB-linear-complexity.
- The cryptographic implementations (threshold signatures, coin) and the negligible-probability
  accounting (Definition 3, Lemma 1).
- Appendix B: the `Ω(n²)` lower bound for adaptive adversaries (Theorem 3), which reduces to a
  cited theorem of Abraham et al.
- Quality (Definition 4).
