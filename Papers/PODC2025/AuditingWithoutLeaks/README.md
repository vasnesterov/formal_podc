# Auditing without Leaks Despite Curiosity — PODC 2025

Hagit Attiya, Antonio Fernández Anta, Alessia Milani, Alexandre Rapetti, Corentin Travers.
*Auditing without Leaks Despite Curiosity.* PODC 2025. DOI
[10.1145/3732772.3733516](https://doi.org/10.1145/3732772.3733516). Formalized version: arXiv
[2505.00665](https://arxiv.org/abs/2505.00665) v1; numbering follows it.

**Verdict: ❌ False claim.** The main result holds. Theorem 8: Algorithm 1 is a linearizable,
wait-free auditable MWMR register whose audits report exactly the effective reads, and whose writes
and reads are uncompromised by curious readers. We prove it in full, and the register is even
strongly linearizable. The proof of Lemma 7 has two genuine gaps, which we repair. The max-register
extension is wrong as stated: Lemma 38 ("no writeMax has input `w`" in some indistinguishable
execution) fails when nonces are natural numbers, even fresh ones, for `w` equal to the initial
value `w₀`. The paper never fixes the nonce domain.

## Mistakes in the paper

* **Lemma 38 is false for natural-number nonces, at the initial value `w₀`.**
  The claim: in Algorithm 2, for every value `w` and reader `p_j`, either `p_j` has a `w`-effective
  read, or some execution indistinguishable to `p_j` has no `writeMax(w)`. The proof replaces
  `(w, N)` by `(u, N')`, where `u` is "the largest input smaller than `w`" and `N' > N`.
  Counterexample (values and nonces in ℕ, initial pair `(0, 0)`, one reader, two writers):
  - writer A runs `writeMax(0)` with nonce 2, so `R` becomes `(1, (0,2), ·)`;
  - writer B runs `writeMax(1)` with nonce 1, so `R` becomes `(2, (1,1), ·)`;
  - the reader runs one read, fetching `(2, (1,1), ·)` and returning 1.

  The reader has no 0-effective read. Yet in every execution it cannot distinguish from this one, it
  fetches the same triple. `R.seq` grows by one per change and `R.val` strictly increases, so the
  pair stored at sequence number 1 lies strictly between `(0,0)` and `(1,1)`. That pair is `(0, N)`
  with `N ≥ 1`, or `(1, 0)`. `(1, 0)` reuses the initial nonce and is excluded by freshness. So a
  `writeMax(0)` occurs in every such execution. The reader learns that 0 was written without
  reading it.

  The proof fails because no input smaller than `w = w₀` exists. With bounded nonces (k-bit
  strings) the leak the nonces were meant to prevent comes back: reading `(v, N_max)` and later
  `(v+2, N_min)` two sequence numbers apart reveals a `writeMax(v+1)`. The lemma seems to need
  nonces from a domain with no least and no greatest element, such as ℤ or ℚ. That case is not
  formalized, and neither is the bounded-nonce leak.

  How far this goes. With nonces in ℕ the failure is confined to `w = w₀`. Any other pair the
  reader knows, it has fetched (which makes its read effective), and ℕ has no largest nonce.
  `writeMax(w₀)` does not change the abstract max register, and the paper's own use (Algorithm 3,
  version numbers ≥ 1) never invokes it. Our Lean counterexample uses two writers. Under a
  per-instance reading of Definition 3, the writers could swap inputs, so it refutes Lemma 38's
  "no writeMax has input `w`", not that reading of Theorem 40's clause. With a single writer the
  swap is impossible, but that variant is argued, not formalized. This is a false numbered lemma in
  a secondary result (the max-register extension); see differencies.md, item 1, for the verdict
  call (`lemma38_false`, all nonces; `lemma38_false_fresh`, fresh nonces).
* **Lemma 7's proof has two gaps (the statement is true).** The proof removes the reads of `p_k`
  and flips bit `k` of the pads. This misses two effects of `p_k`.
  - A direct read also runs `SN.compare&swap(sn−1, sn)` (line 5). If that step is the one that
    moves `SN`, removing it changes the values of `SN` that `p_j` reads later.
  - A writer's `R.compare&swap` may fail only because `p_k` inserted itself into the reader set.
    Without `p_k` it would succeed earlier, and the executions diverge.

  Our repair: the writer poised at line 15 takes over `p_k`'s successful `SN` step. Writer loop
  iterations whose compare&swap fails in α are dropped. These iterations start and end in the same
  local state and only write `V`/`B`, which readers never read. With these repairs the lemma holds
  in a stronger form: in the indistinguishable execution `p_k` invokes nothing at all (`lemma7`,
  `read_uncompromised`).
* **Claim 4, Lemma 3 and Lemma 5 need at least one writer and two distinct values.** These are
  degenerate cases. Without writers, a read is `v₀`-effective as soon as it is invoked. An audit
  invoked right after the invocation does not report it, so Lemma 5 fails. We assume a writer and
  two distinct values; "multi-writer" implies the first (`claim4`, `lemma5`). Lemma 5 also needs
  the audit to be invoked *after* α. An audit already running when the read becomes effective may
  miss it. The proof ("linearized after the read is effective") shows this is the intended
  reading.
* **The linearization `L(α)` is described only in outline.** Rules R1–R3 push silent reads and
  silent writes back before the visible write. We use a different, prefix-closed linearization
  instead. The writes with sequence number `x+1` are linearized at the step that moves `SN` to
  `x+1`. Fetch&xor and audit reads of `R` in the window between are linearized there too, in
  access order. This gives strong linearizability, which the paper does not claim
  (`alg1_stronglyLinearizable`).
* **Typos and slips.**
  - Algorithm 1, line 22: `lsa ← sn` should be `lsa ← rsn`.
  - Line 21 uses `bits` for the audit's `rbits`.
  - Lemma 19 has "for x > 1" where it means `x ≥ 1`.
  - Claim 4's proof has "`x > prev_val`" where it means `prev_sn`.
  - Appendix B: `q_x` reads `x − 1`, not `x`, from `SN`.
  - Appendix B: `V[x−1]` and `B[x−1]` are finalized by `A_x`, not `V[x]` and `B[x]`.
  - Algorithm 2, line 30: `continue` must restart at line 26, since `mval` is undefined otherwise.

Full list of differences, including modelling choices and minor imprecisions:
[differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory in CSLib (`Cslib.SharedMemory.Impl`) with deterministic processes.
  Crashes are modelled by processes that stop taking steps; this matches the paper's
  honest-but-curious attacker.
* Processes: `m` readers, any type `W` of writers and any type `Au` of auditors.
* Base objects: `R`, holding a triple with read, fetch&xor on one tracking bit, and
  compare&swap returning a success flag; `SN`, a compare&swap register; registers `V[s]`; Boolean
  registers `B[s][j]`.
* Each step applies one primitive, so the `for each` loops are unfolded.
* Randomness (one-time pads; nonces for Algorithm 2) is a parameter of a *family* of
  implementations.
* The implemented object is an auditable register. `read j` records `(j, value)` and `audit`
  returns the set of recorded pairs; the reader's identity is an argument of `read`.
* **Views and indistinguishability** (`Podc/.../SharedMemory/View.lean`): `p`'s view is its
  initial local state plus its sequence of invocations, primitive *responses* and returned values.
  This is the finest reasonable reading of `α|p`, so "indistinguishable" results are as strong as
  possible.
* **Definition 2** is formalized literally, quantifying over all indistinguishable executions
  (any pads) and all extensions (`Impl.EffectiveFam`).
* **Definition 3** is `Impl.UncompromisedFam`: some indistinguishable execution does not invoke
  the same operation, with the same arguments, as that instance. For writes this is the paper's
  "no write with input `v`" (Lemma 6).
* Algorithm 2: values and nonces in ℕ, lexicographic pairs, initial pair `(0, 0)`.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 8: linearizable (in fact strongly linearizable) | `alg1_linearizable`, `alg1_stronglyLinearizable` | `Lin.lean` |
| Lemma 2 / Thm 8: wait-free | `alg1_waitFree` | `WaitFree.lean` |
| Lemmas 16–18 (phase structure, unique value per sequence number) | `Inv`, `Inv.step`, `DInv2`, `BInv` | `Inv.lean`, `LinAux.lean` |
| Claim 4 (characterization of effective reads) | `claim4`, `effective_of_fixed` | `Effective.lean` |
| Lemma 3 (linearized reads are effective; effective reads are fetched) | `effective_of_mem_lin`, `effective_read_iff` | `Effective.lean` |
| Lemma 5 / Thm 8: audits report every effective read | `lemma5` (core: `audit_reports`) | `Effective.lean` |
| Lemma 24 / Thm 8: audits report only effective reads | `audit_sound` | `Effective.lean` |
| Lemma 6 / Thm 8: writes uncompromised | `lemma6` (core: `rename_writes`) | `Theorem8.lean`, `RenameWrites.lean` |
| Lemma 7 / Thm 8: reads uncompromised (strengthened) | `lemma7`, `read_uncompromised` (core: `remove_reader`) | `Theorem8.lean`, `RemoveReader.lean` |
| Lemma 38 (writes uncompromised in Alg. 2): **false** for ℕ nonces, `w = w₀` | `lemma38_false`, `lemma38_false_fresh` | `MaxRegCex.lean` |
| Invariant 26, Lemmas 25/27 (Alg. 2) | `MaxReg.Inv.of_run` | `MaxRegInv.lean` |

**Not formalized.**
* Linearizability and wait-freedom of Algorithm 2 (Lemmas 28–37).
* Section 5: auditable snapshots (Theorem 12) and versioned types (Theorem 13).
* Lemma 3 as an "iff" for a single linearization. Our `L` omits the pending reads of the current
  D phase, which are linearized at the next `σ`. We prove that every read in `L` is effective and
  characterize effective reads by fetches (`effective_read_iff`).

**Trust.**
* No `sorry`; the listed theorems use only `propext`, `Classical.choice` and `Quot.sound`.
* The counterexample runs are checked by `decide` in the kernel.
* The model uses CSLib's `SharedMemory` modules: `Model`, `History`, `Linearization`,
  `LinPoints`, `StrongLin`, `Progress` and `Potential`.
* CSLib candidate: `Podc/Computability/Distributed/SharedMemory/View.lean` (views,
  indistinguishability, effective and uncompromised operations, replaying local states).
