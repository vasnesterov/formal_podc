# Differences between the formalization and the paper

Paper: Attiya, Fernández Anta, Milani, Rapetti, Travers, *Auditing without Leaks Despite Curiosity*,
PODC 2025 (arXiv 2505.00665 v1).

## Statement-level issues (with the deciding rule of `verdicts.md`)

1. **Lemma 38 ("no writeMax has input `w`" in some indistinguishable execution) is false for
   nonces in ℕ, at `w = w₀`.**
   Decided **❌** by R4 and R5.
   - Lean: `MaxReg.lemma38_false` (arbitrary nonces) and `MaxReg.lemma38_false_fresh` (nonces
     pairwise distinct and ≠ N₀). Both refute the Lean statement `Lemma38` of the paper's lemma.
   - The paper never fixes the nonce domain ("a fresh random nonce", "a random number"). The proof
     silently needs a domain with no least element (no input `u < w₀` exists for `w = w₀`) and, for
     bounded nonces, no greatest element (`N' > N`). R4 does not excuse such an unstated
     value-domain property.
   - The max register is presented as an extension ("We extend this implementation…"), not as the
     primary contribution, so this is ❌, not 🚨.
   - Borderline aspects (a close call between ❌ and ⚠️):
     - ℕ is our choice; the paper's model does not force it. The paper's proof (`N' > N`) implies
       nonces unbounded above. Among such domains the lemma fails exactly when the domain has a
       least element (ℕ, ℕ \ {N₀}, …). It seems to hold when the domain has none (ℤ, ℚ); this is not
       formalized. With bounded nonces (k-bit strings, the usual reading of "a random number") it
       fails for every `w`, but the proof's `N' > N` rules that reading out.
     - With ℕ nonces the failure is confined to `w = w₀`. A reader learns a pair only by fetching
       it (then its read is effective), the initial pair excepted, and ℕ has no largest nonce. So
       the leaked operation is `writeMax(w₀)`, which does not change the abstract max register.
       Algorithm 3, the paper's only use, writes version numbers ≥ 1 and never invokes it.
       This argues for R2 ("parameter corners never used"). We do not apply R2: the lemma
       explicitly quantifies "for every value `w`", `writeMax(w₀)` is an ordinary invocation
       with a real leak under Definition 3, and the proof covers `w₀` ("the largest input smaller
       than `w`") without noticing that no such input exists. With `w = w₀` the proof breaks in
       every nonce domain; only the statement is rescued in ℤ, by a different construction.
     - R4's explicit exclusion applies: the proof silently needs a value-domain property that the
       paper never fixes.
   - Theorem 40's clause vs Lemma 38. The Lean counterexample has two writers and refutes
     Lemma 38's "no writeMax has input `w`" in any indistinguishable execution. Under the
     per-instance Definition 3 (`UncompromisedFam`, item 4), the two writers can swap inputs, and
     the specific instance `writeMax(0)` of `A` is uncompromised. With a single writer the swap is
     impossible: `M` is monotone, so the writer's first operation must have input `w₀`. That
     variant would refute the per-instance reading of Theorem 40 too; it is not formalized. The
     verdict rests on Lemma 38, a numbered lemma (R1).
2. **Claim 4, Lemma 3, Lemma 5 need at least one writer and two values.** Decided ⚠️ (R2/R4):
   these are degenerate cases, and "multi-writer" implies a writer exists.
   - With `W = ∅`, a just-invoked read is `v₀`-effective but not reported by a later audit.
   - Lean hypotheses: `[Nonempty W]`, `∃ v1 v2, v1 ≠ v2` (`claim4`, `effective_read_iff`, `lemma5`).
   - Lemma 6 similarly needs a value `v' ≠ v` (`lemma6`).
3. **Lemma 5's quantification.** "An audit invoked and returns in an extension α' of α": we read
   this as invoked *after* α (`¬ Invoked α (au a, n)`). An audit already running when the read
   becomes effective can miss it (it read `R` before the fetch&xor). The proof's "audit linearized
   after the read is effective" shows the intent. This is an ambiguity, not counted as an error.
4. **Definition 3 for writes.** "op is not invoked in β" is formalized as "the instance `x` is not
   invoked with the same operation (same input)". This is what Lemma 6's proof uses: it replaces
   the input.
   - If the instance itself (process plus index) had to be absent, Theorem 8's write clause would
     fail trivially. With a single writer, a reader that fetches sequence number 2 knows the writer
     invoked at least two writes.
   - Theorem 8's write clause is formalized as Lemma 6.

## Proof-level issues (🛠️)

5. **Lemma 7's proof is incomplete.** The lemma is true; we prove a stronger version (`lemma7`,
   `read_uncompromised`). The two gaps:
   - Removing `p_k`'s direct read also removes its `SN.compare&swap` (line 5). That step can be the
     one advancing `SN`, which `p_j` observes. Repair: the writer poised at line 15 for that
     sequence number takes that step instead; it exists by `DInv`. Its own later line-15 step is
     dropped.
   - Writers' `R.compare&swap` may fail only because of `p_k`'s fetch&xor. Without `p_k` it would
     succeed and the executions diverge. Repair: drop every writer loop iteration whose
     compare&swap fails in α (or is unfinished). Such an iteration is a loop in the writer's local
     state and only writes `V`/`B`.
   - Also dropped are the writers' `B[s][k]` writes. The new pads are flipped at bit `k` exactly
     where `p_j` observes `p_k`'s bit (`padsB`).
6. **Linearization.** The paper's `L(α)` (rules R1–R3) is only sketched; Lemmas 21–24 are given
   with proofs that rely on it. We use a different, forward-simulation linearization (`Lin.lean`):
   - the abstract value is the value of sequence number `SN`;
   - all writes with sequence number `x+1` (silent ones first, then the visible one) are linearized
     at `σ_{x+1}`;
   - fetch&xor / audit reads of `R` during `D_{x+1}` are linearized there too, in access order
     (ghost list `Dl`);
   - other operations are linearized as in R1 (silent reads at their `SN` read, even during `D`).

   This avoids the retroactive insertions of R2/R3 and yields strong linearizability (not claimed
   by the paper). Lemma 3 refers to the paper's `L(α)`; we prove its content for our linearization
   (`effective_of_mem_lin`, `effective_read_iff`, `audit_sound`).
7. **Lemma 2 / §3.2 prose.** "The repeat loop terminates after at most m+1 iterations": with the
   exiting read of `R` counted as an iteration, `m + 2` iterations are possible (`m` failures
   caused by readers, one by a concurrent visible write, then the exit). Not formalized as a
   bound. Wait-freedom is proved with a potential that allows `m + 2` (`alg1_waitFree`).

## Typos (not counted)

8. Algorithm 1:
   - line 22: `lsa ← sn` should be `lsa ← rsn`;
   - line 21: `bits[j]` should be `rbits[j]`.
9. Lemma 19 "For x > 1" should be `x ≥ 1`. Claim 4's proof "`x > prev_val`" should be `prev_sn`.
   Lemma 7's proof "only changes the kth tracking bit of R unchanged to, say, b".
10. Appendix B:
    - `q_x` "reads `x` from SN" should be `x − 1`;
    - "`V[x]` and the `B[x]` are set to their final value by `q_x` when applying `A_x`" should
      refer to `V[x−1]`, `B[x−1]`;
    - Lemma 25 lists the `σ_ℓ` lines inconsistently.
11. Algorithm 2, line 30: `continue` must re-enter the loop at line 26. The agent model reads it
    so; otherwise `mval` at line 34 is undefined.

## Modelling choices

12. **Shared-memory model.** CSLib `Impl`: each step applies exactly one primitive. The
    `for each` loops (lines 13, 18–20) are unfolded into one step per register access. The writer
    writes only the `B[s][j]` with deciphered bit set (no dummy steps); the auditor reads all
    `B[s][j]`, `j < m`.
13. **Primitives.**
    - fetch&xor on `R` flips the one tracking bit of the caller; this is `fetch&xor(2^j)` on the
      encoded triple.
    - compare&swap returns a success flag.
    - `SN.compare&swap(-1, 0)` (paper) becomes `cas(0, 0)` on ℕ. It is harmless: it never changes
      `SN`.
14. **Processes.** Readers, writers and auditors are disjoint roles (`Proc.rd/wr/au`). The
    paper's writers and auditors share the pads; here the pads are a parameter of the
    implementation. The reader's identity is an argument of `read` (`AOp.read j`), and only reader
    `j` may invoke it (`allowed`).
15. **Randomness.** One-time pads `rnd : ℕ → Fin m → Bool`, and for Algorithm 2 the nonces
    `nc : W → ℕ → ℕ`. These are the parameter `θ` of a family of deterministic implementations.
    Indistinguishable executions may use other pads and nonces (`Impl.IndistFam`).
16. **Views.** The view of `p` is its initial local state and its observations: invocations,
    primitive responses, returned values. Lemmas 6 and 7 are therefore proved for the finest
    notion of indistinguishability.
17. **Audit sets** are `Set (Fin m × V)` in Algorithm 1 and `Finset` in Algorithm 2 (for `decide`).
18. **Algorithm 2 instance.** Values and nonces in ℕ, lexicographic pairs, initial pair `(0,0)`.
    The counterexample instance has one reader, two writers and no auditors. The model itself is
    generic in `m`, `W`, `Au`.

## Not formalized

19. Linearizability and wait-freedom of Algorithm 2 (Lemmas 28–37, rest of Theorem 40), Section 5
    (Theorem 12, auditable snapshot; Theorem 13, versioned types), the consensus-number discussion.
