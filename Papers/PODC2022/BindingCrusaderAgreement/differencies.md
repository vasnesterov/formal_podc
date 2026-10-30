# Differences between the formalization and the paper

Paper: Abraham, Ben-David, Yandamuri, *Efficient and Adaptively Secure Asynchronous Binary
Agreement via Binding Crusader Agreement*, PODC 2022 (11-page proceedings version, the only one used;
the "full version" it refers to was not available to us).

## Statement-level observations (with the deciding rule of `verdicts.md`)

1. **Algorithm 5, line 9 (all `echo2` messages `⊥`).** Read literally, "if all of the messages contain
   the same value `v` then decide `v, 2`" also fires when all `n − t` messages carry `⊥`: line 10 treats `⊥`
   as "a value other than `v`", so "value" includes `⊥` in this pseudocode. Example: `n = 3`, `t = 1`, inputs
   `0, 1, 0`, no crash, every party first receives one `⟨val, 0⟩` and one `⟨val, 1⟩`. Everybody sends
   `⟨echo, ⊥⟩`, then `⟨echo2, ⊥⟩`, and line 9 decides "`⊥` grade 2". This is not one of the five buckets of
   Definition 3.2, so the literal algorithm does not implement GBCA (Theorem 5.1). Line 11 becomes dead
   code, and Algorithm 2, line 7 ("if grade = 2 then commit val") would commit `⊥`. The prose just above the
   algorithm says that the party then decides `⊥`. We model that: all `⊥` gives `⊥` grade 0
   (`Alg5.decideG`), and prove Theorem 5.1 for this version.
   *Rule:* R3 (typo with evident intent: recoverable from the prose, local fix: "non-`⊥`" in line 9).
   This is the only statement-level issue and sets the verdict to ⚠️. **Borderline call (R6):** one could
   read "`⊥` grade 2" as the `⊥` bucket and call this notation, which would give 🛠️. We follow the
   precedent for literal pseudocode slips (⚠️), since the literal output also breaks Algorithm 2. The same
   phrase in Algorithm 3, line 6 is harmless (`⊥` is a valid BCA output).
2. **"Terminates in at most 4 (6, 3, 2) communication rounds"** (Theorem 4.3 / Lemma 4.7, Theorem 5.3,
   Theorem 5.1, Theorem 4.1). Lemma 4.7's proof counts messages: "a party sends at most 4 messages". §3
   fixes the measure as broadcasts ("we measure broadcasts, i.e., the number of communication steps").
   We prove exactly this: every party broadcasts at most 4 (6, 3, 2) messages (`out_ncard_le_*`).
   *Remark (not counted as an error):* this is not the asynchronous latency in the usual normalized-delay
   measure (each message delay ≤ 1). For Algorithm 4 with `n = 7`, `t = 2` there is a schedule in which
   every correct party sends 4 messages but decides only at time `5 − ε`. Inputs: `A1, A2 = 1`,
   `B1, B2, B3 = 0`. Both Byzantine parties send `⟨echo, 1⟩` only to `B2`, at time `2 − ε`. All other
   delays are 1. `B2` then approves 1 just before 0 and sends `⟨echo2, 1⟩`, while everybody else sends
   `⟨echo2, 0⟩`. Now nobody can use the `n − t` same-`echo2` branch. Everybody has to wait until both values
   are approved, which happens at `4 − ε`, and the decisions come one delay later. We checked this with an
   event simulation (not in Lean): [`scripts/latency.py`](scripts/latency.py). The
   comparisons with [9, 11, 28] in Tables 1–2 are fair only if those papers count the same way.

*Typo.* Algorithm 6, line 11 reads "if 1 then"; evidently "if (1) then" (as in Algorithm 4, line 11).
Our liberal guards make the branch choice irrelevant. *Rule:* R3, harmless.

Apart from the pseudocode slip of item 1, no statement checked here is false.

## Proof-level differences (repairs)

3. **Lemma 4.5 (validity), second part.** "In order to decide `1 − v`, a non-faulty party must have
   `1 − v` in its `approvedVals` set (line 15)". Line 15 only requires `n − t` messages `⟨echo3, 1 − v⟩`, so the
   cited justification is wrong. Repair: some uncorrupted sender of `⟨echo3, 1 − v⟩` received
   `⟨echo2, 1 − v⟩` from `n − t` parties. One of those is uncorrupted, so it approved `1 − v`, which by the
   first part needs an uncorrupted party with input `1 − v` (`Alg4.validity`).
4. **Lemma 4.9 (binding) against an adaptive adversary.** The proof picks "the `t + 1` messages from
   non-faulty parties". Who is non-faulty depends on the *extension*, while `b` must be fixed at time `τ`.
   Our proof (`Alg4.binding`) fixes `b` from the prefix. If some party has broadcast `⟨echo3, u⟩` with `u ≠ ⊥`,
   take `b = u` and use Lemma 4.8 in the extension. Otherwise the decider's `n − t` `echo3` messages include at
   least `n − t − |bad(τ)|` genuine `⊥`'s. A later quorum `⟨echo3, w⟩` would need `n − t` senders among the
   remaining `n − |G|` parties plus the at most `t − |bad(τ)|` parties corrupted later, which is at most `2t`
   parties. The paper's argument can be completed this way. The same repair is used for Algorithm 6
   (`Alg6.graded_binding`, via the first `⟨echo4, ⊥⟩`).
5. **Theorems 4.1, 5.1, 5.3** have no proofs in this version (deferred to the full version). We supply our
   own. For Algorithm 6 the binding argument has to go through the `echo4` level: a grade-`≥ 1` decision on `v`
   needs a genuine `⟨echo4, v⟩` (line 25 requires `t + 1` of them), and the `echo3` level is consistent as
   in Lemma 4.8.
6. **Theorem 3.1's termination** argument ("at least a 50% chance") is formalized only as a counting
   statement. Let the adversary be deterministic, with binding values a function `β` of the earlier coins.
   Then at most `k + 1` of the `2^k` coin prefixes of length `k` leave all rounds `< k` without a round in
   which everybody commits (`Alg1.rounds_count`), and `∑ (k + 1)/2^k = 4` (`Alg1.tsum_succ_div_two_pow`).
   This matches the claimed 4 expected rounds. The probability space (`E[T] = ∑ P(T > k)`, independence of
   the strong coin from the past) is not formalized.

## Modelling choices

7. **Model** (`Podc/Computability/Distributed/Byzantine/AsyncBroadcast.lean`). Interleaving semantics:
   * every broadcast is one event, and each delivery to each receiver is a separate event;
   * the adversary corrupts parties adaptively, at most `t` in total;
   * Byzantine parties can make anybody receive anything from them;
   * crashed parties stop, and their earlier broadcasts may or may not be delivered (crash during a
     broadcast).

   Executions are infinite (with stuttering). Fairness is weak fairness for never-corrupted parties only:
   their messages to each other are delivered, and a guard that stays enabled forever is eventually taken.
   Messages of parties corrupted later and injected messages are unconstrained. This only weakens the
   adversary's obligations, so the termination results are at least as strong as the paper's.
8. **Liberal guards.** "Upon receiving messages from `n − t` parties, if they all contain `v`…" is modelled
   as "`v` received from `n − t` parties". "Not all the same" is modelled as "messages from `n − t` parties, and
   a `⊥` or two different values among them". If both branches of a "wait until" are enabled, either may be
   taken (the paper gives priority to branch (1)). This is a superset of the paper's deterministic behaviours,
   so the safety results (agreement, validity, binding, message counts) transfer. The liveness results hold
   for every weakly fair execution of the liberal protocol, which includes the paper's executions.
9. **Sequencing.** Algorithm 4 decides only after its own `echo3`. Algorithm 6 sends `echo(k+1)` only
   after its own `echo k` (`k = 3, 4`) and decides only after its own `echo5`. This is the sequential "wait
   until" structure of the pseudocode. `echo2` is an "upon" clause and is not required before `echo3`, as in
   the paper.
10. **No termination after deciding.** A party keeps executing all clauses after deciding, so "decide" and
   "terminate" coincide. The paper never says when a party may stop running Algorithm 4. Lemma 4.6 explicitly
   assumes that no non-faulty party terminates, and the framework keeps parties running after they commit.
11. **Stronger statements than the paper's.** Agreement, validity and binding are proved for *all*
   recorded decisions, including those of parties corrupted after deciding. Binding holds for every
   reachable state that contains a decision, which is equivalent to the paper's "first decision" form. In the
   Byzantine theorems, validity is stated for any set `H` of parties with `|Hᶜ| ≤ t` and no corrupted member;
   with adaptive corruption, `H` is the set of parties that are never corrupted.
12. **Crash versions** (BCA-Crash, GBCA-Crash; the paper defers their full definitions to the full
   version). Agreement and binding are proved for all parties. Weak validity is "if all parties have input
   `v`, every decision is `v` (grade 2)". The bound `t < ⌈n/2⌉` of Theorem 4.1 is the same as `2t < n`.
13. **Framework (Algorithms 1, 2).** We reason at the level of BCA instances: per round, the parties that
   start and finish it, their inputs, outputs and coins, with BCA agreement and validity as hypotheses. One
   statement covers the Byzantine case (`Start = Dec = H`) and the crash case. For the crash case we need
   weak validity for the *participants* of the instance ("all parties that start round `r + 1` have input
   `v`"), since crashed parties never start later rounds. This is how Theorem 3.3 must read "all parties have
   the same input".
14. **One instance.** Instance identifiers `id` are dropped: each protocol is a single instance.

## Not formalized

* Section 6 (BCA with threshold signatures, Theorems 6.1, 6.2), the EVBCA variants, and Theorems 4.2,
  4.10, 4.11, 5.2, 5.4. These are broadcast counts of composed protocols whose constructions are in the full
  version.
* Probability spaces: the `ε`-good and `t`-unpredictable coins, "termination with probability 1", the
  `1 + 1/ε` bound of Theorems 3.4/3.5. Only the deterministic steps (`Alg2.binding_step`) and the counting
  bound for Algorithm 1 are formalized.
* The attack on Cachin–Zanolini and the discussion of earlier protocols (full version).
