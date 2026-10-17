# Differences between the formalization and the paper

Paper: R. Guerraoui, P. Kuznetsov, M. Monti, M. Pavlovič, D.-A. Seredinschi, *The Consensus Number
of a Cryptocurrency*, PODC 2019 (DOI 10.1145/3293611.3331589). Text used: arXiv:1906.05574v1
(extended version; arXiv has only v1). The journal version (Distributed Computing, 2022) was not
checked. Numbering follows it.

## Errors in the paper

1. **Lemma 3 and the liveness part of Theorem 3 (Figure 4, message passing) are false as written** —
   false statement (main finding, verdict ❌). The paper's proofs explicitly use the check without `h`:
   Lemma 3's proof claims that conditions 23–25 hold. The repair is easy. Line 2 lets `p` spend `balance(a, hist[p] ∪ deps)`, which
   counts the incoming transfers `deps` it received since its last outgoing transfer. Line 4 ships
   `deps` as `h`. Validation (line 25), however, checks `balance(c, hist[q]) ≥ y` *without* `h`, and
   incoming transfers enter `hist[q]` (line 15) only after a later transfer of `q` is validated.
   Two correct processes, no Byzantine process, a perfect broadcast: process `0` (balance 5) pays 5
   to process `1` (balance 0). Both validate it. Process `1` then pays the 5 back. Its message is
   never valid at any process, so `transfer` never returns (`Fig4.lemma_3_false`, all extensions
   quantified). With `balance(c, hist[q] ∪ h) ≥ y` the same transfer completes
   (`Fig4.fixed_completes`). The pseudocode also contradicts the variable's description ("`hist[q]`:
   set of validated transfers involving `q`"). Another fix: also add `t` to `hist[d]` in line 15.
   Theorem 3 as stated is therefore also false for the literal Figure 4: Definition 1 requires every
   invocation of a correct process to get a response, and the proof of Theorem 3 uses Lemma 3. Only
   its safety argument is unaffected (not formalized).
2. **Figure 1 (Theorem 1) is not linearizable as written** — a slip with evident intent (Figure 3
   tags transfers with unique sequence numbers), trivially repaired. `ops_p` is a *set* of triples `(a, b, x)` and line 4 does
   `ops_p := ops_p ∪ {(a, b, x)}`. A second transfer with the same arguments is therefore not
   recorded, although it returns `true`. Counterexample: one process owns account `0` with
   balance `2`, and it calls `transfer(0, 1, 1)` three times solo. All three calls return `true`,
   which no sequential history allows (`Fig1.Bug.literal_not_linearizable`,
   `Fig1.Bug.no_linearization`; `Fig1.Bug.not_valid_fixed` shows the repaired algorithm cannot
   produce this execution). The owner can even spend an unbounded amount, which is double-spending.
   Fix: keep `ops_p` as a sequence (or tag each transfer with a sequence number, as Figure 3
   does). With this fix, Theorem 1 is proved with the paper's linearization points
   (`Fig1.fig1_linearizable`, `Fig1.fig1_waitFree`).
3. **Theorem 2 in the degenerate case `k = 0`** — false only in a degenerate case. "`k`-shared" is
   `max_a |μ(a)| = k`, so an object in which no account has an owner is `0`-shared. Theorem 2 then
   gives it consensus number `0`. But one process always solves consensus, so the consensus number
   is `1` (`atSolvable_one`; `not_atSolvable` shows it is not `≥ 2`). For `k ≥ 1` the theorem is
   correct (`theorem_2`). (If `A = ∅`, `max_a |μ(a)|` is undefined.)
4. **The relation `Δ` is not total** (Section 2.2) — under-specified definition. For a self-transfer
   `transfer(a, a, x)` with `x > 0` by an owner with enough balance, the first clause demands
   `q'(a) = q(a) − x` and `q'(a) = q(a) + x`. The second clause demands `p ∉ μ(a) ∨ q(a) < x`. So no
   transition exists, which contradicts "we assume that `Δ` is total". We use the sequential reading
   "debit `a`, then credit `b`": a successful self-transfer leaves the balances unchanged
   (`moveFunds` in `Defs.lean`). The results do not depend on this choice.

## Lemma 2 (Figure 3): the algorithm is correct, the proof has gaps

We formalized Figure 3 in CSLib's `Impl` model. The base objects are an atomic snapshot `AS`, the
registers `R_a[i]`, and `k`-consensus objects `kC_a[r]` for all accounts and rounds. We proved it
linearizable and wait-free whenever every account has at most `k` owners
(`Fig3.fig3_linearizable`, `Fig3.fig3_waitFree`). The algorithm itself has no bug. The proof has
the following gaps:

5. **Incomplete transfers decided as failures** — proof gap, statement true. The proof completes
   every incomplete transfer included in an `AS.update` "with response true". That is wrong when
   the decided result is `failure`. Such a transfer must be completed with response `false`, or be
   linearized at the proposer's snapshot.
6. **Non-owner transfers (lines 1–2)** get no linearization point — proof gap. We linearize them at
   their invocation.
7. **"The linearization of a prefix of `E` is a prefix of `L`"** — false side claim, not needed. A
   failed transfer is linearized at the snapshot (line 8) of the process `q_o` whose proposal
   decided it. That snapshot can precede the decision, so the linearization is extended
   retroactively. We insert such operations retroactively (`IsLinearization.insert`, `Podc/SharedMemory/LinResp.lean`).
8. **Successful-transfer case** — proof gap. The text mixes `L_k` and `L_s`. Its key step, that no
   outgoing transfer of `a` is linearized between `q_o`'s snapshot and the first `AS.update`
   containing `o`, is asserted without justification. We prove it from the round ordering: every
   process runs the rounds of `a` in order and updates `AS` with round `r`'s decision before it
   proposes in round `r + 1`.
9. **Wait-freedom** — proof gap, statement true. "Eventually `o` becomes the request with the lowest
   round number … some instance of `k`-consensus will be only accessed with `o`" is false as
   stated. Processes that collected before `o` was announced keep proposing other transfers from
   their stale `collected` sets. We replace it with a potential argument (`Fig3Pot.lean`,
   `Fig3WF.lean`).
10. **`collect` (lines 22–23)** reads `R_a[i]` twice: once for the test, once for the value. We read
    it once (imprecision).


## Smaller imprecisions (not errors)

- **Proof of Theorem 2, "at most `k`".** The paper combines Lemma 2, the cited fact that
  `k`-consensus objects (+ registers) cannot solve `(k+1)`-consensus [Jayanti–Toueg / Herlihy],
  and, implicitly, the composition of linearizable implementations (atomic snapshots from
  registers, Afek et al.). We instead prove it directly by a valency argument
  (`no_consensus`). It is stronger: any number of asset-transfer objects with possibly different
  owner maps, any read/write objects, and every `n > k`.
- **Message-passing Definition 1 (2)** asks `ops(H̄) ⊆ ops(S_p)` for every correct `p` and every
  history. This cannot hold for finite executions in which `p` has not yet delivered other
  processes' transfers. It also covers reads and failed transfers of other processes, which the
  proof's `S_p` (built from messages validated at `p`) does not contain. It only makes sense for
  infinite (fair) executions, restricted to successful transfers. Not formalized.
- **Figure 4's `balance`** (line 28) is "incoming minus outgoing transfers" without initial
  balances. Taken literally, no transfer of a positive amount ever succeeds. Our model adds the
  initial balances `q₀`.
- Figure 3's `proposal((a, b, q, x), snapshot)` uses 4-tuples where transfers are 5-tuples
  `(a, b, x, s, r)` (typo).

## Modelling choices

- **Callers.** CSLib's sequential specifications do not see the invoking process. So
  `ATOp.transfer p a b x` carries the caller `p`, and the algorithms must use their own identity:
  `allowed` in the `Impl` model (Theorem 1; `Fig1.allowed_iff` shows that all reads and all own
  transfers are allowed) and `Honest` in the consensus model. Lemma 1's algorithm is proved honest
  (`Lemma1.lemma_1`).
- **Consensus model** (`System.lean`): CSLib `Recoverable` without crashes. It has `n`
  deterministic processes with binary inputs, wait-free consensus (`WFConsensus`: agreement,
  validity, and every process taking infinitely many steps decides), and objects with arbitrary
  initial values. The paper does not fix the value domain of consensus; binary consensus is the
  standard choice for consensus numbers. Lemma 1's algorithm works for any domain. Read/write
  objects are anything `ObjSpec.RWLike` (each operation read-only or a blind write), which includes
  registers. Any number of objects is allowed.
- **`k`-shared** is formalized as `∀ a, |μ(a)| ≤ k` (`KShared`) for the impossibility. Lemma 1
  uses an object with an account owned by exactly `k` processes (`Lemma1.μ₁_card`), so
  `theorem_2` is the paper's statement for `k ≥ 1`.
- **Theorem 1** uses an atomic snapshot *base object* (`snapObj`). The paper cites its wait-free
  read/write implementation [Afek et al.]. That implementation, and composition, are not
  formalized. Each process's component stores the list of its successful transfers.
- **Granularity.** In all algorithms each shared-memory access is one atomic step. Local
  computation is folded into the continuation.
- **Figure 4 model** (`Fig4.lean`): only what the counterexample needs. Two correct processes,
  account of `q` = `q`. Secure broadcast is modelled as per-sender FIFO delivery, each message
  once, so integrity and source order hold by construction. The claim is about *all* extensions,
  so agreement and validity of the broadcast are irrelevant.
