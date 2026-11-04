# Differences between the formalization and the paper

Paper: D. Hendler, V. Khait. *Complexity Tradeoffs for Read and Update Operations.* PODC 2014
(author copy with complete proofs, 10 pp.). Numbering follows the paper.

## Model

1. **Shared memory.** CSLib's `Cslib.SharedMemory.Impl`: asynchronous, deterministic processes,
   one atomic base-object access per step, invocations and responses are separate labels. Base
   objects are read/write/CAS registers over an arbitrary value type `V` with arbitrary initial
   values (`RWC ι V v₀`: every object is a `casObject V v₀`; the index type `ι` is arbitrary and may
   be infinite). The paper's model is the same.
2. **Step-complexity hypothesis.** The paper assumes "the step complexity of CounterRead / Scan /
   ReadMax is O(f)". We assume only the weaker `SoloBound I r rd R`: from every reachable
   configuration in which the reader is idle, its read completes within `R` *solo* steps. This is
   implied by obstruction-freedom plus any worst-case bound, so our lower bounds are stronger. We
   never need obstruction-freedom of the updaters.
3. **Conclusion form.** The paper states `Ω(·)` lower bounds on "the step complexity of
   CounterIncrement / Update / WriteMax". We prove the existence of an execution in which an update
   operation (invoked once, not yet returned) *has already taken* the stated number of steps, with
   explicit constants (non-asymptotic statements), plus the asymptotic forms derived from them
   (`Theorem2.lean`, `Theorem3.lean`, `Asymptotics.lean`).
4. **Objects.** Counter: `counterObj` (`inc`/`read`, defined here). Snapshot: CSLib `snapObj n`
   with processes `Fin n`, update `update p 1` by process `p` (only these invocations need to be
   allowed). Max register: CSLib `maxRegObj` over ℕ (initial value `0` instead of `−∞`); the
   `M`-bound is modelled by `allowed`: only `WriteMax(v)` with `v ≤ M` need be allowed.
5. **Generic counter/snapshot theorem.** Theorem 1 and Corollary 1 are instances of one generic
   theorem `update_lower_bound` for any object whose read *reveals* all updaters (`Reveals`).
   Corollary 1 is proved directly, not by the paper's reduction to a counter (CSLib has no
   composition theorem for implementations); the content is the same.

## Definitions (Section 3)

6. **Awareness, visibility and familiarity (Definitions 1–4) are replaced by a sound data-flow
   semantics** (`Podc/Computability/Distributed/SharedMemory/Awareness.lean`). The paper's
   definitions are unsound — see items 7 and 8 — and the paper's own reasoning (proof of Lemma 1:
   "`AW(p, Eσ) ≤ AW(p, E) + F(o, E)`") uses process-level awareness that grows through local state,
   which Definition 2 does not express. Our semantics: `AW(p)` (initially `{p}`) grows by the
   familiarity set of every object `p` reads or CASes; every write and every value-changing CAS
   pushes an entry (writer, value, writer's `AW`) on the object's history, and the familiarity set
   is the `AW` of the top entry. Trivial events (reads, failed CAS, CAS with `new = old`) do not
   touch histories. This matches the intent ("information flow via shared memory") and the paper's
   arithmetic (Lemma 1 holds with the same factor 3).
7. **Lemma 2 is false as stated (❌, rule R1; not excusable by R3/R4).** Two independent problems:
   (a) it removes only the events of `q` that are aware of `p`, not all events of `q` from the
   first such event on (the proof of Lemma 3 uses the latter; this alone would be an R3 typo);
   (b) with Definition 1, an overwritten write is invisible, and so is the trivial write that
   overwrites it. Counterexample `PaperDefs.lemma2_false`: in a single-writer max register
   (`toyImpl`), the writer `q` writes `5` twice, then the reader reads `5`; no event is aware of an
   event of `q` (even with a more generous transitive closure than Definition 2), yet removing `q`'s
   events leaves a sequence that is not an execution. Fixing it requires changing Definition 1, which
   the paper's proofs rely on, so R3 does not apply: the proof of Lemma 1 schedules "read, trivial CAS
   and trivial write events" in `σ₁` and asserts "No event in `σ₁` is visible", i.e. it uses exactly
   the clause that makes a trivial write invisible. (A definition under which a write is invisible
   only when overwritten before being accessed would not be refuted by this example, but it is not the
   paper's definition.) The counterexample does not depend on the toy's double write inside one
   operation: two `WriteMax(5)` operations of `q` with one write each give the same event sequence,
   and the same works for a 2-process *multi-writer* max register (process `p` keeps its running
   maximum in its own register `R_p`; `ReadMax` by `p` reads `R_{1−p}` once and returns the max with
   its own maximum), not formalized. Lemma 2 itself (Section 3) is stated for an arbitrary execution
   of an arbitrary implementation. Our sound replacement: `arun_erase`.
8. **Claim 1 is false as stated (❌, rule R1).** Same execution: `{q}` is hidden after `E`
   (Definition 5; also no object is familiar with `q`, no event is visible), but `E − {q}` is not an
   execution (`PaperDefs.claim1_false`). `toyImpl` is a genuine wait-free linearizable max register
   (`PaperDefsLin.lean`), so the counterexample lies in the paper's setting. Our sound replacement:
   `arun_filter_hidden` / `ess_erase`.
9. **Definition 2's transitive clause** literally requires the aware event `e_p` to access the same
   object `o` as `e_q`; chains through other objects are then impossible. Evidently unintended; our
   semantics propagates awareness through local state.

## Section 3 (counters and snapshots)

10. **Lemma 1:** true in our semantics with the paper's constant 3 and the paper's three-phase
    schedule (`exists_round`). Reformulated as "all `AW` and `F` sets ≤ `B` ⇒ ≤ `3B` after one step
    of each process of `T`". In phase 1 we schedule reads and CAS that do not change the value
    (the paper also lists "trivial writes" there; we schedule all writes in phase 2, which is
    needed because in our semantics every write overwrites the familiarity set).
11. **Lemma 3:** proved in the generic form `reader_aware_all` (the reader's single read after all
    `N − 1` single updates completed is aware of all `N` processes). The proof uses our erasure
    lemma (erase the suffix of every process from the moment it becomes aware of `q`).
12. **Theorem 1:** `counter_tradeoff`: if `R · 3^k + 1 < N` some increment has taken `k + 1` steps;
    `counter_update_logb`: some increment takes `≥ log₃((N − 1)/R)` steps. The paper's iteration
    bound `⌈log₃(N/f(N))⌉` and its "`r = o(log₃ N/f(N))`" argument are replaced by this exact
    count: after `k` rounds the reader's awareness set has at most `1 + R · 3^k` elements.
13. **Corollary 1 / Theorem 2:** `snapshot_tradeoff`, `snapshot_update_logb`; Theorem 2 as
    `theorem2_counter` / `theorem2_snapshot`: if `R ≤ c log N` then some update takes
    `≥ log₃ N / 2` steps for `N ≥ N₀(c)`. The paper restricts Theorem 2 to read/write base objects
    and polynomially many updates; we allow CAS and our executions use `N − 1` updates, so the
    restriction is harmless.

## Section 4 (max registers)

14. **Essential sets (Definition 7) are strengthened by the block invariant** `BlockOK`: for every
    object, the top segment of its history written by essential processes was written by a single
    process. Our `Ess` also records the halted set `H` (supremacy = halted values are smaller), that
    every process of `E ∪ H` invoked exactly one `WriteMax(val p)` and none returned, and that every
    essential process is still pending. "Hidden set" (Definition 5, second condition `|F(o) ∩ P| ≤ 1`)
    is automatic in our semantics and dropped.
15. **Lemma 4: proof gap; proved for essential sets with the block invariant (⚠️ unestablished as
    stated).** The paper's proof erases essential processes and then reasons with `F(o, E_i) \ K`
    as if erasing could only shrink familiarity sets. Erasing the last writer of an object
    *resurrects* the previous write, possibly by another essential process, which the next step then
    reads — breaking hiddenness. Also, the high-contention case classifies processes as
    reading / writing / value-changing-CAS w.r.t. the value of `o` after `E_i`, but the steps are
    taken after the erasure, which may change that value (a "trivial" CAS may then succeed). Repair
    (`lemma4`, `lemma4_low`, `lemma4_T`, `lemma4_W`, `lemma4_C`): maintain `BlockOK`; in the
    low-contention case build the conflict graph from block owners (out-degree ≤ 1; independent set
    of size `≥ k/3` by `exists_indep`, replacing Turán); in the high-contention case erase the block
    owner of `o` and classify after the erasure. The bound is `⌊√m⌋ ≤ 3(|E'| + 1)` for all `m`,
    which implies the paper's `|E'| ≥ √m/3 − 2` and needs no `m ≥ 81`. Whether Lemma 4 holds for
    essential sets without the block invariant is left open (borderline call: neither proved nor
    refuted → ⚠️ "unestablished", rule R5 note; it does not affect Theorem 3).
16. **Lemma 5** is folded into the proof of Lemma 6 (the linearizability argument `read_lt` /
    `read_ge`).
17. **Lemma 6: proof gap; proved for essential sets with the block invariant (⚠️ unestablished as
    stated).** The paper erases, before each step of the reader, the completed hidden process the
    accessed object is familiar with; the same resurrection problem lets the reader see another
    completed process afterwards. Our proof (`lemma6`) compares two erasures instead: run the
    reader with all essential processes erased, record the `≤ m` objects it accesses (`accFrom`,
    `solo_transfer`), keep exactly the completed processes that own none of their blocks.
18. **Theorem 3:** `theorem3` (non-asymptotic): if `|W| ≥ T := max(2m, X₀)` (`X₀ = 10^6`), some
    execution has `≥ T` writers that each took exactly `t ≥ log₃(log |W| / log T) − 1` steps in a
    single pending `WriteMax`. With `m = O(f(K))` this is the paper's `Ω(f(K))` processes taking
    `Ω(log(log K / log f(K)))` steps. The stopping rule ("half of `E_i` terminate, or
    `|E_{i+1}| < f(K)`") is replaced by Lemma 6 directly (`|E| − m` processes remain enabled) and the
    recursion `|E_{i+1}| ≥ gStep m |E_i| = ⌊√(|E_i| − m)⌋/3 − 1`. The paper's Eq. (4)
    ("`½|E_{i−1}|^{1/2} − 2 = Ω(|E_{i−1}|^{1/3})`, hence `|E_i| = Ω(K^{1/3^i})`") hides constants that
    are iterated `i` times and a threshold; we make them explicit (`gStep_ge_rpow`, `rpow_le_iterate`).
19. **Theorem 4:** `theorem4` (generic, `m ≤ c · log |W|`) and `theorem4_fin` (paper's setting with
    processes `Fin N`, an `M`-bounded max register, writers `p₁…p_{M−1}`, reader `p₀`, `M ≤ N`,
    `ReadMax ≤ c log M`). **Not covered: `M > N`.** The paper says Theorem 4 is "immediate from
    Theorem 3", but with `K = min(N, M) = N` and `f(K) = log M`, Theorem 3 gives
    `Ω(log(log N / log log M))`, which is `Ω(log log N)` only if `log log M = O((log N)^{1−δ})`; e.g.
    for `M = 2^N` it gives nothing. So for very large `M` Theorem 4 is unestablished (proof gap; we
    neither prove nor refute it). This gap concerns only ReadMax complexities between `c log N` and
    `c log M`: the generic `theorem4` (with `W` = the `min(N, M) − 1` writers, all values `≤ M`) gives
    `Ω(log log min(N, M))` whenever ReadMax takes `O(log min(N, M))` steps, for all `N, M`; in
    particular the abstract's "read-optimal ⇒ `Ω(log log min(N, M))`" is established. Also the
    hypotheses `W` writers distinct values `≥ 1` and the reader not a writer are explicit.
20. **Values:** writers write their (distinct, positive) values `val p`; the paper uses identifiers
    `1 … K−1` and reader `p_K`. `theorem4_fin` is the literal instance.

## Section 5 (Algorithm A) — formalized in `AlgA/`

21. **Model:** `impl lay` in CSLib; values ℕ with `0` for `−∞`; base objects `casObject ℕ 0`, heap-indexed
    nodes; leaf layout a parameter (`stdLayout`: B₁-like `T_L`, complete `T_R`). Theorem 5 is proved
    for every layout.
22. **Definitions 8/9 (linearization points via "counts"), Invariant 1 and the uniqueness/existence
    of linearization points used in the proof of Theorem 5 are wrong (🛠️ proof gap; Theorem 5 is
    true).** A completed `WriteMax` may never be "counted" by the root (its CASes succeed trivially,
    its leaf write is trivial, or it returns at line 16), so Definition 9 gives it no linearization
    point (`AlgA.not_counts`: `N = 2`, `WriteMax(3)` by `p₀` then `WriteMax(2)` by `p₁`). The proof of
    Invariant 1 confuses a trivial CAS with a failed one. Invariant 1 is stated inside the proof of
    Lemma 9 (rule R1: not a statement); Observation 2 presupposes existence of the point. Repair:
    linearize `WriteMax(v)` at the first moment of its interval at which root `≥ v`
    (`AlgA.linearizable`).
23. Line 5 typo `n ← node.parent` (should be `n.parent`); `T_L` has `N` (not `N − 1`) leaves for the
    values `v < N`; the "WLOG no process writes a smaller value" assumption is unnecessary and not
    used.
24. **Theorem 6:** `AlgA.waitFree`, `readMax_steps_le` (≤ 1 access), `writeMax_steps_le`
    (`≤ 16⌊log₂ min(N, v+1)⌋ + 18` for `stdLayout`); `O(min(log N, log v))` read as
    `O(1 + min(log N, log v))`.

## Verdict decision

Worst label: ❌ — Lemma 2 and Claim 1 are numbered statements that are false with the paper's own
definitions (items 7–8), not headline results (R5), and the fix changes a definition the proofs use
(R3 does not apply). The headline tradeoffs (Theorems 1–4) and Algorithm A (Theorems 5–6) hold, with
repaired proofs, except Theorem 4 for `M ≫ N` (not formalized, item 19).
