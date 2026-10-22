# Differences between the formalization and the paper

Attiya, Castañeda, Hendler, Perrin. *Separating Lock-Freedom from Wait-Freedom.* PODC 2018
(HAL version hal-02053248, cited as [ACHP18]).

## Scope

* Formalized: Definition 2 (`n`-LLAA), Definitions 3–5 (valency, criticality), Lemma 10, Lemma 8
  with Claim 9, Theorem 11.
* Not formalized: Sections 3 and 4 (Algorithm 1 / Theorem 4, Algorithm 5 / Theorem 7). Algorithm 1
  was only model-checked, as a bounded sanity check (see the end of this file).

## Model

* CSLib asynchronous shared memory (`Cslib.SharedMemory.Impl`). Processes are deterministic. Each
  step applies one primitive to one base object. Invocations and responses are separate labels that
  do not touch memory, as in I/O automata. The paper folds the response into the last primitive
  step. Our model only adds interleavings and memory-free steps, so the impossibility is not weakened.
* **Objects.** The paper uses `(n-1)`-window registers. We allow any family of base objects (any
  index type) that are *window-like with window `n-1`* (`ObjSpec.WindowLike (n-1)`). This means
  every operation is read-only or has a state-independent response, and any `n-1` consecutive
  non-read-only operations determine the state. `k`-window registers with `k ≤ n-1` qualify
  (`theorem_11_window`), and so do read/write registers. This is a generalization.
* **The LLAA object.** The operation `output()` of a process of side `i` is modelled as the
  operation `i : Fin 2`, so the object "knows" the side of the caller, as the paper assumes. The
  specification `llaaSpec` is nondeterministic: any output satisfying the convergence requirement
  is allowed. Linearizability is CSLib's `IsNLinearization` w.r.t. this specification. The side
  assignment is fixed: `p₀` is the only process of side `0`, all others are on side `1`. Section 5
  of the paper makes the same choice.
* **Which executions must be correct.** The paper requires wait-freedom and linearizability for
  all executions and then only looks at those where `p₀` performs a single `output()`. Our main
  theorem `theorem_11` assumes both properties **only** on admissible executions (`Adm p₀`): every
  process invokes `output()` of its side and `p₀` invokes at most once. It also assumes only that
  each process *may* invoke its side's operation (`allowed`). This is a strengthening.
  `theorem_11_window` states the unrestricted version, with CSLib `WaitFree` and linearizability of
  all executions.
* `n ≥ 2` is explicit, as the hypothesis `p₁ ≠ p₀`. For `n = 1` the statement is meaningless.

## Definitions

* **Valency (Section 5).** `Potent`, `Univ` and `Biv` are defined on finite executions (label
  lists), not on configurations, because whether `p₀` already returned is part of the history.
  `p₀(C)` is modelled as `X.ext1 α p₀`, the extension by `p₀`'s next label. `q(C)` for an idle
  `q ≠ p₀` is its next invocation.
* **Definition 3 (ambivalent) and Definition 4 (critical `q`-extension)** are not defined
  separately. Lemma 8 and the proof of Theorem 11 are merged (see below).
* **Definition 5 (critical).** The paper requires `p₀(C')` to be univalent for *all* extensions
  `C'` of `C`. We require it only for extensions in which `p₀` takes no step
  (`Ctx.Critical`). Claim 9 only uses those, and the weaker notion makes Lemma 8 stronger.
  Lemma 10 still yields such an execution. (If `p₀` has returned, "`p₀(C')`" is undefined in the
  paper anyway.)

## Proofs

* **Lemma 10.** The paper argues "since `A` is wait-free, eventually we reach a bivalent execution
  …". We make this precise (`exists_biv_univ`): if every bivalent execution had an extension
  without `p₀`-steps followed by a non-univalent `p₀`-step, iterating would give an infinite
  admissible execution in which `p₀` is pending forever and takes infinitely many steps. That
  contradicts wait-freedom. The choice of `β₂` as "the longest prefix …" is done with `Nat.find`.
  The first paragraph (the empty execution is bivalent: output `≥ 1/2` solo, `≤ 3/8` after two
  operations of `p₁`) is `biv_nil`. It uses linearizability of the two solo executions,
  including the real-time order.
* **Lemma 8 (case analysis).** The paper fixes the critical process as `p₁` "without loss of
  generality". We keep an arbitrary `q`. The paper's cases (different registers or `p₁` reads;
  `p₀` reads; both write the same register, split into `n = 2` and `n > 2`) are re-organised by
  the semantic criterion "does `q`'s step write the base object accessed by `p₀`'s step?":
  * no → the steps commute for `p₀` (`Good.swap'`), contradiction (paper: first case);
  * yes and `p₀`'s step is read-only → ambivalent for `q` (paper: second case);
  * yes and `p₀`'s step writes → both write `R` (paper: third case). Here `n = 2` is handled by
    the same window argument as `n > 2`: with `n = 2` the block `p₀, p₂, …` is just `p₀`.
  Steps that access no memory (invocations, responses) are covered, which the paper does not
  discuss.
* **Lemma 8, case `n > 2`.** The paper lets `p₂, …, p_{n-1}` run in turn until each is about to
  write `R`, "otherwise" some `q` runs solo forever without writing `R`, giving a critical
  `q`-extension. We stop each solo run as soon as the process is about to write `R` **or** has
  completed `k + 3` operations (`Ctx.build`), with `k` fixed in advance from `|v - v'|`. In the
  second case the final argument of Theorem 11 (Case 2) is applied directly to this finite run.
  No infinite run or critical `q`-extension (Definition 4) is needed.
* **Claim 9.** The paper's induction distinguishes "`q` accesses another register" (configurations
  equal) and "`q` reads `R`" (indistinguishable to `p₀`). We use a single commutation lemma
  (`step_swap`): if `a`'s step does not change the object accessed by `b`'s step, both orders agree
  on the memory and on all processes but `a`. For the second statement (`p₀(p₁(C''))`) the paper
  just says "similarly". We commute `r`'s step past `p₁`'s and then past `p₀`'s write (two swaps).
* **Theorem 11.** The paper concludes Case 1 (ambivalent) and Case 2 (critical `q`-extension)
  separately. We merge both into `false_of_witness`: from a `v`-univalent and a `w`-univalent
  execution in which the same `q ≠ p₀` returned the same `x` in its `m`-th operation, `m ≥ k + 2`,
  we get `|x - v|, |x - w| < 1/2^(k+1)`, a contradiction. The estimate is `close_of_univ`
  (the paper's computation). It applies linearizability to a completion of the univalent
  execution and uses that `q`'s operation is preceded in real time by `q`'s `m` earlier
  operations. The paper takes "the last operation of `q`" after `k + 3` solo operations. We take the
  last response in the solo segment, which has index `≥ k + 2` whatever `q` did before.
* **Arithmetic.** The paper's bound
  `|x − v| ≤ 2^{-(k+3)} + 2^{-(k+3+k')} + 2^{-(k+3+k'+1)} < 2^{-(k+1)}` is proved as
  `close_of_legal` for any legal sequence, with the slightly coarser intermediate bounds
  `2^{-(k+3)}, 2^{-(k+3)}, 2^{-(k+4)}`.

## Paper issues found

* None in Section 5: Lemma 10, Lemma 8, Claim 9 and Theorem 11 are correct. The proofs are
  sketchy only where noted above (the "eventually" in Lemma 10, the infinite solo run in Lemma 8,
  "WLOG `p₁`").

## Supplementary check of Algorithm 1 (not formalized)

`modelcheck/llaa_mc.py` is a bounded exhaustive model checker (Python, exact rationals; not part of
the Lean development) for Algorithm 1 exactly as in Figure 1, with the paper's atomicity
convention of Section 3.1 (the read of line 05 and the local computation of lines 06–15 are one
step). It explores all interleavings with up to 3 operations per process, both with the
invocation merged into line 02 and as a separate step, and checks lock-freedom (no reachable
cycle) and linearizability of every reachable quiescent history w.r.t. Definition 1 (with
real-time order). No violation was found. As a sensitivity check, the deliberately wrong mutant
`you.pos < min(prev)` in place of the paper's `you.pos ∉ prev` in line 08 is detected as not
linearizable (with 1 + 3 operations). Note: `pdftotext` renders the `∉` of line 08 (and of the
definition of the invalid position rule) as `<`; the PDF itself has `∉`.
