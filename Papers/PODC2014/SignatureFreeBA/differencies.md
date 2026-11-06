# Differences between the formalization and the paper

Paper: Mostéfaoui, Moumen, Raynal, *Signature-Free Asynchronous Byzantine Consensus with t < n/3 and
O(n²) Messages*, PODC 2014; full version IRISA PI-2016 (hal-00944019).

## Statement-level issues

1. ❌ **Lemma 5, Theorem 2 (BC-Termination), Theorem 3 are false** (`Attack.counterexample`,
   `Attack.prob_termination_eq_zero`). For `n = 4`, `t = 1`, inputs `0, 0, 1` and one Byzantine
   process, an adversary of the paper's model prevents every decision, for every coin sequence.
   The proof's error is in the third case of the Claim: `v` (the value adopted at line 09) is
   chosen by the adversary after the coin `s` is known, so `P(s = v) = 1/2` does not hold.
   Theorem 2 and the abstract ("the expected number of rounds to decide is four")
   are claims about the paper's specific algorithm. The model does not
   excuse it. The paper explicitly lets the Byzantine processes control the schedule and only
   asks that the coin cannot be computed *in advance* (Section 4.1, footnote 2). Our adversary
   uses the coin of round `r` only after two correct processes (and the Byzantine one) have
   called `random()` in round `r` (`Attack.coin_used_late`). A threshold coin revealed by `n − t`
   shares gives it exactly this. A coin hidden until all correct processes have passed line 05
   would save the Claim, but the paper does not assume it, and no asynchronous coin can wait for
   all correct processes.
   The adversary learns the coin of round `r` from `p0`'s broadcast `B_VAL[r+1](coin r)` (received
   by the Byzantine `p3`), so even an ideal coin oracle does not help; only a content-oblivious
   scheduler (footnote 2, which the paper sets aside) would. The problem was reported earlier by
   Tholoniat and Gramoli (arXiv:1909.07453, 2019).
   *Journal version.* The title's existential claim (signature-free, `t < n/3`, `O(n²)` messages)
   survives through the new algorithm of the J. ACM 2015 version, which we did not formalize, but
   Theorem 2 and the abstract's "expected number of rounds to decide is four" name the paper's
   specific algorithm (Figure 2).
   *Not an artefact of the model.* The counterexample is not an artefact of our liberal guards. In each round
   every delivery happens when no correct process has a pending step (`Local.eager`). The
   `bin_values` used at line 04 is a singleton, and every admissible set of `n − t` `AUX` messages
   at line 05 yields the same `values` (`Local.forced`). At the end of a round no step of that
   round is enabled (`Local.quiet_final`). So it is an execution of the deterministic code under
   any resolution of its nondeterminism. In Lean these checks are per round. That no step of
   *another* round is enabled while a round is scheduled holds as well, but we argue it in prose
   only: earlier rounds are quiet by `quiet_final`; in the next round, nothing has been delivered
   yet, so no echo, `AUX` or line-05 step is enabled (and the decision guard never holds, as
   `Attack.fair` shows). This prose part only concerns eagerness: that the whole execution is a legal,
   weakly fair execution of the model (every correct-to-correct message delivered, every
   persistently enabled step taken) is proved in Lean globally (`Attack.fair`), and the paper's
   processes may in any case proceed "at their own pace".

## Proof-level issues

2. **Lemma 2, proof**: "`p_x` sent `AUX[r](v)` to `p_i` and `AUX[r](w)` to `p_i`" — the second
   `p_i` should be `p_j`. Typo.
3. **Lemma 5, proof**: the parts "no correct process blocks forever" and "once all correct
   processes have the same estimate they decide when the coin matches" are correct
   (`Exec.no_blocking`, `Exec.decide_of_unanimous`). The proof of BV-Termination via
   BV-Obligation needs that all correct processes BV-broadcast in the instance, which the paper
   states.
4. **Theorem 3, proof**: besides relying on the false Claim, it is informal about the expected value
   (sum of two geometric phases). Not formalized.

## Modelling choices

5. **Model.** `Cslib.Byzantine.AsyncBroadcast`: interleaving semantics, reliable authenticated
   channels, each delivery a separate adversary event. The Byzantine processes are modelled as
   corrupted parties that can make anybody receive any message from them.
   * Corruption is *adaptive* (up to `t` parties at any time). The paper's model is static. Safety
     results are therefore stronger. For the counterexample the Byzantine process is corrupted at
     time 3, before it ever acts, i.e. statically.
   * "Correct" in safety statements: a set `H` with `σ.bad ⊆ Hᶜ` and `|Hᶜ| ≤ t`. In the static model,
     `H` is the set of correct processes. In liveness statements, correct = never corrupted
     (`Exec.Correct`).
6. **Liberal guards.** A `wait until` may be passed at any later time with any admissible set of
   `n − t` messages. Echoes (Figure 1, line 03) and decisions (line 08) are separate steps, not
   atomic with the receipt or with lines 06–11. This adds behaviours, so safety transfers to the
   code. The counterexample avoids this freedom (item 1).
7. **Messages carry a local tag.** A process's own `B_VAL[r](v)` (Figure 1, line 01) carries
   `some d`, an echo carries `none`. Receivers ignore the tag (they count senders of `B_VAL[r](v)`
   with any tag). The tag records the process's local variables (`est`, whether `values` was a
   singleton) in its broadcast set, as required by the guard-based model. A process may broadcast
   `B_VAL[r](v)` twice (once as echo, once as own estimate), as in the paper, where line 01 is
   unconditional.
8. **`values` at line 05.** Literal reading: there are `n − t` distinct senders `S` and, for each,
   a received `AUX[r](f s)` with `f s ∈ bin_values[r]`, and `values = f(S)` (`AuxQuorum`). A
   Byzantine sender that sent both values may contribute either.
9. **Common coin.** A fixed sequence `coin : ℕ → Bool`, the same at every process (`random()`
   at round `r` returns `coin r`). Safety holds for every sequence. In the counterexample the
   adversary is a function of the time and the global state. The global state reflects a coin
   only after a process has used it (through its next estimate), so the adversary cannot see
   future coins. The probability statement (`prob_termination_eq_zero`) holds for every measure on
   coin sequences, because the set of terminating sequences is empty.
10. **Validity** is stated for binary values as "if all correct processes propose `v`, no correct
   process decides `¬v`", which the paper notes is equivalent to BC-Validity.
11. **Lemma 1** is stated as an invariant. Under "all correct processes that start round `r₀`
   do so with estimate `v`", no correct process ever broadcasts `B_VAL[r](¬v)` or `AUX[r](¬v)` for
   `r ≥ r₀`. This implies the paper's "never change their estimates".
12. **Lemma 4** is proved for processes that are correct in the current state (decisions of
   processes corrupted later are not covered).
13. **Theorem 1** liveness properties are proved for weakly fair executions of the whole algorithm
   (the BV-broadcast instance of each round). BV-Termination assumes, as the paper does, that every
   correct process BV-broadcasts in the instance. Justification and uniformity are slightly
   stronger than stated: uniformity starts from `v ∈ bin_values` at *any* process (correct or not
   at that time).
14. **Not formalized**: the cost analyses (messages per round, bits per message, `O(n² r log r)`
   bits), the expected-rounds computation, and the counterexample for general `n = 3t + 1`.
