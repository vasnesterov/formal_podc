# Differences between the formalization and the paper

Sean Ovens, *The Space Complexity of Scannable Binary Objects*, PODC 2021 (proceedings version; no
arXiv full version exists).

## Statements of the paper

1. **Observation 3 is false as stated when the start configuration `C` is not `p₀`-idle**
   (false only in a degenerate case). Let `p₀` have a pending `Update` that has taken no step yet in
   `C`, and let the object's value before this update be `V`. Let `α` be a complete solo `Scan` of a
   scanner. The only `p₀`-idle configuration reached during `αα'` is the one after `p₀` completes its
   update, whose value differs from `V` if the update changes the value, so `α` is `V`-absent; but the
   scan may be (and in every natural implementation is) linearized before the update and return `V`.
   The paper only applies Observation 3 to executions from `C₀α_j`, which is `p₀`-idle, so nothing
   breaks. Formalized correct version: `scan_resp` (a scan returns the value after `i` operations of
   `p₀`, with `i` at least the number of `p₀`'s operations *completed* before the scan is invoked);
   all uses start from `p₀`-idle configurations.
2. **Abstract / introduction: "when `n ≤ 2^(k-1) + 2`, a lower bound of `n + k − 2`"** is stated
   without the restriction `k ≥ 3`, `n ≥ 2` of the body (Theorem 8 / Corollary 9 need `k ≥ 3`,
   `n > 2`). The conclusion (§6) repeats it as "holds when `2 ≤ n ≤ 2^(k−1) + 2`".
   * `k = 1`, `n = 3`: the bound claims 2 base objects, but one 1-bit object suffices for any `n`
     (the atomic implementation; the single component is itself a readable 1-bit object). Also
     Lemma 6's hypothesis `k ≥ 2` is necessary. False only in a degenerate case
     (`one_component_one_object`, `abstract_bound_fails_k1`).
   * `n = 1`, `k ≥ 2`: the bound claims `k − 1 ≥ 1` objects, but with a single process (which can
     only update) no shared object is needed at all. Degenerate; not formalized.
   * `k = 2`, `n = 4`: the bound claims 4 objects; the paper only proves 3 (Lemma 6; Theorem 8 needs
     `k ≥ 3` because Lemma 7 reduces to `k − 1 ≥ 2` components). Unproved claim; we do not know
     whether it holds (the single-updater upper bound is `2^k = 4`).
3. **Introduction / start of §5: the range `2^k − 2^(k−r) < n − 2 ≤ 2^k − 2^(k−r−1)` is stated
   without `k ≥ r + 3`** (Theorem 8 has it). For `r = k − 2` the range is `n ∈ {2^k − 1, 2^k}` and
   the claim is `n` objects; for `r = k − 1` it is `n = 2^k + 1` with claim `2^k`. Thus for
   `n ∈ {2^k, 2^k + 1}` it claims `2^k` objects (which would make the `2^k` single-updater upper bound
   tight), but the paper proves only `2^k − 1` (Corollary 9 (c)). Unproved claim, under-specified
   statement; we formalize Theorem 8 with `k ≥ r + 3`.
4. **Corollary 9 (c) for `n > 2^k − 2`**: the paper says "this lower bound also applies to larger
   values of `n`" without proof. True (proof gap, trivial). We prove (c) directly for all
   `n ≥ 2^k − 2` and all `k ≥ 2` (`corollary9c`, by induction on `k`), not only `k ≥ 3`.
5. **Corollary 9 (a)** is stated for `k ≥ 3`, `n = 2`; Lemma 6 gives it for all `k ≥ 2`, `n ≥ 2`
   (`lemma6`).

## Proofs of the paper

6. **Lemma 6, proof**: "Since `V₁` contains a 1 in every component" — `V₁` was only chosen with a 1 in
   its `k`-th component; that is all the argument needs (intermediate values of `λ_j` have `0` in
   component `k`). Typo.
7. **Lemma 6, proof** assumes `m = k` and derives a contradiction; the case `m < k` is not mentioned
   (the same pigeonhole argument works). Tiny gap; our proof covers `m ≤ k`.
8. **Lemma 7 (simulation)**: the obstruction-freedom of the simulated implementation `I'` is not
   argued — a process `q_j` "locally simulates steps of `p_j`" on the frozen objects `B_h`, and these
   local simulations must terminate (they do: otherwise `p_j` would run solo forever in `I`,
   contradicting obstruction-freedom of `I`). The simulated `I'` has process-specific initial states
   and arbitrary initial base-object values, which the model allows. Proof gap with true statement.
   **We do not build `I'`** (see 12).

9. **Lemma 1, proof**: "checks its handshaking bit `R_j` immediately following each of these final
   `n` collects": should be `u + 1`. Typo. Lemma 1 itself is correct (also when a process is both
   scanner and updater); it is not a separate Lean theorem: its counting argument ("dangerous updates +
   dirty collects ≤ u") is part of the linearizability invariant of Implementation 1.
10. **Theorem 2, lock-freedom**: the argument ("if a Scan runs forever, infinitely many Updates must be
   completed") is informal. We prove lock-freedom with two potential functions, without using the
   "infinitely many steps" hypothesis of CSLib's `LockFree`. Proof gap with a true statement.

## Modelling choices and generalizations

11. **Value of the object / `𝒱`-absent.** The paper defines the value in a `p₀`-idle configuration
   via the (unique) linearization of `p₀`'s updates. We define it syntactically: `valAt p₀ ε i` is the
   value after the first `i` operations invoked by `p₀` (`curVal` = after all of them), and
   `Absent p₀ V ε β` requires `valAt p₀ (ε ++ β) i ∉ V` for all `i` between the number of operations
   `p₀` invoked before `β` and by the end of `β`. This matches the paper's definition (configurations
   reached during `αα'`, with the completion `α'` of `p₀`'s pending update, including the start
   configuration). Observation 4 becomes trivial (`absent_append_noP0`).
12. **Lemma 7 replaced by stages.** Instead of constructing a new implementation `I'` with one
    component, `h` processes and `h` base objects fewer, we stay inside `I`: a `Stage` is a reachable
    configuration with a set `A` of active processes (idle, containing `p₀`), a set `F` of frozen base
    objects and `k'` live components, such that no execution from it by active processes that only
    updates live components changes `F`; the components `≥ k' − 1` are `0`. The executions of the
    paper's `I'` are exactly these restricted executions of `I`, so Lemma 5 for stages (`lemma5`) is
    Lemma 5 for `I'`, and `reduce_stage` is Lemma 7 (one component fewer, `h` processes fewer, `h`
    more frozen objects). The final bounds count `|F| + (objects outside F)`. This removes the
    simulation, the linearizability/obstruction-freedom transfer and the initial-configuration
    bookkeeping of Lemma 7. The bookkeeping execution `κ` (reset all components to 0) is kept.
13. **Single-updater discipline as a lower bound on `allowed`.** The hypothesis is
    `∀ p o, SingleUpdater p₀ p o → I.allowed p o` (`p₀` may update, every other process may scan), so
    the theorems cover single-updater implementations (`allowed = SingleUpdater p₀`) as well as
    multi-updater/multi-scanner ones; linearizability and obstruction-freedom are required (as in
    CSLib) for all executions the implementation allows.
14. **Base objects.** `B : ι → ObjSpec`, each with `OneBit (B i).State` (the states inject into
    `Bool`), arbitrary invocations and responses, arbitrary (possibly different) types and arbitrary
    initial values (`Impl.memInit`); `m = Fintype.card ι`. This is the paper's "arbitrary 1-bit base
    objects" (Table 1 lists the 8 invocations up to renaming of responses; we allow any).
15. **Components.** `BitObj`: value `Bool`, arbitrary invocations/responses, initial value `0`;
    non-monotonic. The paper also requires components to be *readable*; the lower bound does not use
    reads, so we drop this assumption (stronger theorem).
16. **Processes, steps.** CSLib model: deterministic processes, invocation and response are separate
    labels (`inv`/`ret`) rather than parts of the first/last step — harmless. `n = Fintype.card P`.
17. **Lemma 5** is stated for `j ≤ min(|A| − 1, 2^(k'−1))` with `V_{t+1} = vec k' t` (binary digits of
    `t` below the top live component, `1` at the top, `0` above), the scanner removed at each step
    chosen arbitrarily among the active non-updaters (the paper takes `p_{n−j−1}`).
18. **Construction of `γ` in Lemma 5** is a separate generic lemma `replay` (replay a solo execution
    of `s` from a configuration `s` cannot distinguish, inserting fix-up executions of other
    processes before each access to an object whose value differs).
19. **Implementation 1** (`Impl1.lean`). Scanners `Sc` and updaters `Up` are arbitrary finsets (a process
    may be both). The base objects are `ι = Fin k ⊕ Sc`: `B i` has the type of component `i`, and each
    scanner has one binary register. Components must be readable (`BitObj.Readable`: invocation `rd`
    with `δ v rd = (v, r)` and a decoder of `r`), as in the paper. The handshake bits have arbitrary
    initial values `h₀`. Each loop iteration is one base-object access. A scan does `u + 1` checking
    collects, each reading `B_1..B_k` and then `R_j`, and restarts from the first collect on any
    mismatch or on reading `1`. Every component of a restarted scan's `b` is overwritten.
20. **§4.2** (single-updater wait-free implementation from `2^k` single-writer bits, via Vidyasankar) is
    a citation and is not formalized.
