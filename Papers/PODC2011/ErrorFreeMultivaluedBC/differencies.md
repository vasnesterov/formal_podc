# Differences between the formalization and the paper

Paper: G. Liang, N. Vaidya, *Error-Free Multi-Valued Consensus with Byzantine Failures*, PODC 2011.
Formalized version: arXiv:1101.3520v1 (numbering as there; the algorithm and lemmas are the same as in
the proceedings version).

## Errors and gaps in the paper

1. **Isolated processors can still trigger the diagnosis stage (Theorem 1's `t(t+1)` bound, Lemma 4).**
   In Algorithm 1 as printed, every `P_j ∉ P_match` broadcasts `Detected_j` (2(b)), and every processor
   receives `Detected_j` from every `P_j ∉ P_match` (2(c)). Nothing excludes a processor whose vertex is
   already isolated. Such a faulty processor is never in `P_match`, so it can announce `Detected = true`
   in every generation, and nothing is then removed. Case 2 of the proof of Lemma 4 ("either a bad edge
   `(j,k)` … was removed in Line 3(e), or none … These bad edges are removed in Line 3(f)") overlooks
   the case where vertex `j` has no edge left. So Lemma 4 ("at least one edge … will be removed") and the
   bound "diagnosis stage performed at most `t(t+1)` times" are false for the literal pseudo-code.
   Lean: `Counterexample.literal_not_theorem_1` (`n = 4`, `t = 1`, 3 generations, 3 diagnosis stages
   `> t(t+1) = 2`; any MDS code, e.g. `rs42`), `Counterexample.literal_numDiag` (diagnosis in all `N`
   generations), `Counterexample.literal_lemma_4_false` (a diagnosis stage that removes no edge).
   The run is admissible, and `P_match = {0,1,2}` is the *only* matching set in every generation
   (`Counterexample.isMatch_iff`), so it does not depend on the selection rule of step 1(e).
   *Repair* (formalized as `Variant.repaired`): ignore the `Detected` bits of processors that have no edge
   in the diagnosis graph. This matches the prose ("Once a faulty processor is identified, it is
   effectively isolated from the network"; "the fault-free processors will not communicate with it
   anymore"; proof of Theorem 1: after all faulty processors are identified "the fault-free processors
   will not communicate with the faulty processors. Thus, the diagnosis stage will not be performed any
   more"). With the repair, Lemma 4 and the bound hold (`Gen.lemma_4_progress`,
   `Run.theorem_1_numDiag`). The consensus properties hold for **both** variants
   (`Run.theorem_1_consensus` takes any `A.var`).
2. **`⊥` in the checks of steps 2(a), 2(c) is under-specified.** `R_j[k] = ⊥` for untrusted `k`, and
   `V/A ∈ C₂ₜ` is defined as "some codeword `Z` has `Z/A = V/A`". Read literally, a vector with a `⊥`
   entry is never in `C₂ₜ`. Then a fault-free `P_j ∉ P_match` that distrusts a faulty member of `P_match`
   always reports `Detected_j = true`. Step 3(f) can then isolate this *fault-free* processor (e.g.
   `n = 4`, `t = 1`, faulty `P₃`: generation 1 removes edge `(0,3)`; in generation 2 `P₀` has another
   input, so `P_match = {1,2,3}`; `P₀` reports `true` because of the `⊥` at position 3; no edge at 0 is
   removed in 3(e), `R#/P_match ∈ C₂ₜ`, and 3(f) removes all edges at `P₀`). This breaks "fault-free
   processors always trust each other". The prose of §3.2 ("checks whether the symbols received from
   the trusted processors in `P_match` are consistent with a valid codeword") and the paper's proof of Lemma 4 (case 2(a): "`P_j` computes
   `Detected_j` by checking whether `R_j/X ∈ C₂ₜ` … any message from untrusted processors … should have
   been ignored") use the erasure reading: check and decode on the trusted members `X` of `P_match`.
   We formalize this reading (`Gen.X`, `Gen.Det`, `Gen.out`). We did not formalize the literal `⊥`
   reading in Lean.
3. **Lemma 3's hypothesis.** "If no processor detects inconsistency" should be "if no processor
   *announces* a detection" (faulty processors may detect and stay silent). Our `lemma_3` assumes
   `¬Diag`, i.e. no counted announcement.

## Modelling choices

4. **Generation-level model with a broadcast black box.** We model each generation directly, not message
   by message. Every value sent with `Broadcast_Single_Bit` (`M_j`, `Detected_j`, `R#[j]`, `Trust_j`) is
   one common value for all fault-free processors. It is the prescribed value if the source is fault-free
   and an adversary choice otherwise. This is exactly the specification of error-free Byzantine broadcast
   for `t < n/3` that the paper uses (refs [1, 2]); the broadcast protocol itself is not formalized. The
   point-to-point symbols of step 1(a) are explicit: a faulty `j` may send a different symbol to each `i`
   (`Adv.sym`).
5. **Static faulty set.** The paper's adversary may corrupt processors "at any point during the
   algorithm". The algorithm is deterministic and the adversary omniscient, so this is equivalent to a
   static set `F` (the processors corrupted at some point; until corruption they behave correctly, which a
   Byzantine processor may do). The properties concern the processors that are never corrupted.
6. **Choice of `P_match`, `P_decide`.** "Find a set …" (1(e), 3(h)) is resolved by the adversary
   (`Adv.pmatch`, `Adv.pdecide`), subject to validity (`Gen.ChoicesValid`). This includes every
   deterministic selection rule, so the positive results are stronger than for a fixed rule. Valid
   choices always exist: `P_match` by definition whenever some matching set exists, and `P_decide` by
   `Gen.exists_pdecide` (the first sentence of the proof of Lemma 5), so `Run.Valid` excludes no
   behaviour of the algorithm.
7. **Own symbol.** `R_i[i] = S_i[i]` (a processor "receives" its own symbol), as the decoding in 2(c) for
   `P_i ∈ P_match` needs. The diagnosis graph has no self-loops; `Trust_i[i]` is never used.
8. **Step 1(f) "decide on a default value and terminate".** We decide the default value `A.d` for the
   current generation and continue with the next generation. If "terminate" means "decide the default
   `L`-bit value", nothing changes: then the fault-free inputs differ in that generation (Lemma 1), so
   validity is vacuous, and all fault-free processors agree.
9. **Values.** A `D`-bit part is an element of the data type `α` of an abstract code
   `Cslib.MDSCode n (n - 2t) α β` (any `n - 2t` symbols determine the data). The `L`-bit value is a vector
   `Fin N → α` with `N = L/D` parts. Divisibility of `L` by `D` and of `D` by `n - 2t`, and the field size
   `n ≤ 2^{D/(n-2t)} - 1`, are therefore not needed. A concrete Reed–Solomon instance is
   `Cslib.MDSCode.reedSolomon` (any field, distinct evaluation points; the counterexample uses
   `(4, 2)` over `ZMod 5`).
10. **Step 3(g)** is applied in a single pass, as printed (vertices reaching `t + 1` removed edges
    *because of* this step are only isolated in a later diagnosis stage). The `t(t+1)` bound holds for
    this reading. The proof is our own: the potential `0` / `t + 1 - min(removed, t)` of the faulty
    vertices decreases in every diagnosis stage. The paper only sketches it.
11. **Termination** is built in: the model is synchronous and every processor outputs in every generation.
    The final statement uses CSLib's `Cslib.Byzantine.Problem.Consensus` (agreement + strong unanimity on
    output functions) over the honest set `(↑F)ᶜ`.
12. **`t < n/3`** is `3 * t < n`. The algorithm itself only needs `n - 2t ≥ t + 1` (Lemma 5) and
    `n - 2t ≥ 1`; `3t < n` is also what the broadcast black box needs.

## Complexity (Section 3.4)

13. The model has no bits on the wire. The per-stage counts of Section 3.4 (`baseCost`, `diagCost`) are
    taken from the paper as definitions, not derived from the model. We verify that summing them over the
    generations and using the diagnosis bound gives equation (1) (`Run.cost_le`, repaired algorithm).
14. Equations (2)–(3) are verified over the reals (`ccon_opt`, `ccon_opt_le`), with the paper's real
    `D = √((n²-n+t)(n-2t)L / (t(t+1)(n-t)))`, without rounding `D`. We assume `t ≥ 1` (for `t = 0` this
    `D` is undefined; then there is no diagnosis at all). Equation (3) is stated with explicit constants:
    if `B ≤ b n²` then `C_con(L) ≤ 3nL + 4b n⁴ √L + b n⁶`.

## Typos

15. Section 3.1, "Line 1(a)": "`v_i(g)`, represented by `n − t` symbols" should be `n − 2t` symbols.
16. Section 3.2, "Lines 2(a) and 2(b)": "broadcasted as a 1-bit notification `Detected_i`" should be
    `Detected_j`.
