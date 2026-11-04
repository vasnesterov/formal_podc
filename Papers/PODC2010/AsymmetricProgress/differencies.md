# Differences between the formalization and the paper

Paper: Imbs, Raynal, Taubenfeld, *On Asymmetric Progress Conditions*, PODC 2010; formalized from the
extended version IRISA PI-1952 (May 2010, HAL inria-00486977). Numbering follows that version (it
matches the PODC version for Theorems 1–6 and Lemmas 1–11; Lemmas 12–16 are in its Appendix A).

## Model (all results)

1. **Processes, failures, schedules** (`Model.lean`). `n` deterministic asynchronous processes `Fin n`,
   crash-stop. Infinite executions are schedules `e : ℕ → Fin n`; a process is correct iff it occurs
   infinitely often. A crashed process simply stops being scheduled. Same as the paper.
2. **Every process participates and proposes at time 0** (Theorems 1–4): process `p` starts in the local
   state `A.init p x` given by its input. The paper's runs of a consensus object also allow processes
   that never invoke `propose()`. Executions where everybody invokes are a subset of the paper's
   executions. So an implementation that is correct in the paper's sense is correct in ours, and our
   impossibility results imply the paper's. The paper's own proof (Lemma 3, "empty run with inputs")
   uses the same convention.
3. **Binary consensus** (Theorems 1–4). The proofs of the paper also consider binary consensus
   (Section 3.3). For impossibility this is no loss: a multi-valued algorithm restricted to two values is
   a binary one.
4. **Base objects are deterministic, caller-aware and possibly blocking** (`BObj`): a step of `p` on
   object `i` applies `δ : State → Fin n → Op → State × Option Resp`, and `none` means "no answer yet,
   `p` stays poised on the same operation". Atomic objects (registers, wait-free / linearizable objects)
   always answer (`BObj.ofSpec` embeds CSLib sequential specifications). The paper defines events only
   for atomic objects (Section 3.3). It never says what a step on a non-wait-free `(n, x)`-live base
   object is, although the proof of Theorem 2 needs it. Blocking objects fill this gap.
5. **"Atomic register" is generalized to read/write-like objects** (`BObj.RWLike`: every operation is
   read-only, or a blind overwrite whose new state and response do not depend on the old state).
   Registers are an instance (`BObj.register_rwLike`). Lemma 2 and Theorems 1, 2, 4 are proved for this
   larger class.
6. **Ports.** The paper's object `(Y, X)` "can only be accessed by the processes of `Y`". We state this
   as a property of the algorithm (`RespectsPorts A Y`: in every reachable configuration a process poised
   on `i` is in `Y i`). Theorems 1 and 4 assume `(Y i).ncard ≤ n − 1` for every object that is not
   read/write-like.
7. **Correctness notions** (`Safe`, `OFree`, `WFree`, `FFree`, `Live`). Agreement and validity range
   over all finite executions. Obstruction-freedom of `p`: from every reachable configuration, a solo run
   of `p` long enough produces its output. Wait-freedom of `p`: in every infinite schedule in which `p` is
   correct, `p` outputs. Fault-freedom of `p`: in every infinite schedule in which every process is
   correct, `p` outputs. `Live A X`: safe, obstruction-free for all, wait-free for `X`. The paper's
   `(n, x)`-liveness is `Live A X` with `|X| = x`. Our theorems allow any nonempty `X` (Theorem 1) and any
   `X` with `|X| = x + 1` (Theorem 2).
8. **Valency is defined on configurations**, not on runs. The system is deterministic and outputs
   persist in the local states, so the configuration determines all extensions. `Val C v` ("all
   decisions in extensions are `v`"), `Biv C`, `Decider C p` ("for every extension `y`, `y p` is not
   bivalent"; with obstruction-freedom, "univalent", as in the paper).

## Statements

9. **`n ≥ 2` added** (Theorems 1 and 4; Lemmas 3–9). These are false for `n = 1`. One process that
   decides its own input is a wait-free consensus algorithm without any objects
   (`theorem1_false_one_process`), and it has no bivalent run (`lemma3_false_one_process`). Rule R2/R4:
   degenerate case and a standard implicit assumption, so ⚠️.
10. **Lemma 1** (`lemma1`) assumes that *all* objects have the same state (not only those `p` can access)
    and that the first configuration is reachable. This is the form used everywhere in the paper's proofs.
11. **Lemma 2** (`lemma2`) is stated for configurations `D` with `D p` `v`-valent and `D q p`
    `(!v)`-valent. Its hypothesis (1) (`y ≠ yp`, `y ≠ yq`) is a consequence, not an assumption. The
    conclusion "not an atomic register" becomes "not read/write-like" (stronger).
12. **Lemmas 4–6 are proved for any obstruction-free consensus algorithm with a reachable bivalent
    configuration that has a decider.** Lemma 4 (`lemma4`) gives one from wait-freedom of one process,
    Lemma 7 (`lemma7`) from fault-freedom of one process. Lemma 5 (`lemma5`) and Lemma 6 (`lemma6`)
    then serve for both (they are also Lemmas 8 and 9). `lemma5` needs no agreement hypothesis.
13. **Theorem 1** (`theorem1`) is proved for arbitrary base objects with at most `n − 1` ports (any
    deterministic, possibly blocking objects, not only `(n−1, n−1)`-live consensus objects) plus
    read/write-like objects, and for wait-freedom of any nonempty set of processes. The abstract's "any
    wait-free objects with `n − 1` ports" is covered. `theorem1_single` is the literal `(n, 1)` form.
14. **Theorem 2** (`theorem2`). The base consensus objects behave as `advCons (X c)`: processes in `X c`
    are answered at once, any other process only at a step that directly follows its own previous step
    on the object. `advCons_isLive` proves that this is a legal `(n, X c)`-live consensus object (validity,
    agreement, wait-free for `X c`, obstruction-free for all). An implementation must work for every
    legal behaviour of its base objects, so this adversarial one suffices for the impossibility. Also: the
    base objects may have arbitrary, different sets `X c` with `|X c| ≤ x` and arbitrary initial states,
    and `x = 0` is allowed (the paper requires `1 ≤ x`).
15. **Theorem 3** is split into `theorem3_lower` and `theorem3_upper`. Lower bound: a legal
    `(x+1, x)`-live consensus object (any behaviour, `ConsObj.IsLive B X` with `|X| = x`) is a wait-free
    consensus object for `x + 1` processes. Upper bound: for every `k ≥ x + 2`, no wait-free consensus
    algorithm for `k` processes exists from read/write-like objects and `(k, ≤ x)`-live consensus objects
    behaving as `advCons`. This needs no "consensus number" definition; together the two bounds are the
    statement "consensus number `x + 1`". The paper's "restrict an `(n, x)`-live object to `x + 1` ports"
    step is not formalized as an operation on objects. The lower bound is stated directly for
    `(x+1, x)`-live objects. Likewise for the upper bound with `n > x + 2`: the paper's "prevent the
    `n − (x+2)` additional processes from participating" is used in the form `k = x + 2`, where an
    `(n, x)`-live object accessed by `x + 2` processes is an `(x+2, ≤ x)`-live object (this is why
    `theorem2`/`theorem3_upper` allow `|X c| ≤ x`).
16. **Corollary 1.** Monotonicity (`(n, y)`-live implies `(n, x)`-live for `x ≤ y`) is `Live.mono`.
    Strictness `(n, x) ≺ (n, x+1)` for `x + 1 ≤ n − 1` is `theorem2` (including `x = 0`).
    `(n, n−1) ≃ (n, n)` is `corollary1_top`, via the general lemma `wFree_of_wFree_others`: if all
    processes but `r` are wait-free and `r` is obstruction-free, then `r` is wait-free.
17. **Theorem 4** (`theorem4`): same generalizations as Theorem 1.
18. **Not formalized:** Section 3.5 (Common2 objects instead of registers; it relies on external
    results [1, 2, 6]), the remark at the end of Section 6.3, and the "fairness" remark of Section 1.2.
    Section 3.2's remark ("`(n, n−1)`-live consensus is stronger than `(n−1, n−1)`-live consensus")
    follows from `theorem1` and `corollary1_top` but is not stated separately.

## Proofs

19. **Lemma 6, induction step (proof repaired).** The paper applies Lemma 1 to `x` and `z` (and to `xq`
    and `zq`, later to `x`, `y`). It claims that "the state of all the objects that `p` can access in `x`
    and `z` are the same, because the only object that `p` accesses in `x` and `z` is `o`". The suffix
    `z − x` consists of steps of `s` that may write registers, which `p` can access. So the hypothesis of
    Lemma 1 fails. The conclusions (`xp`, `zp` compatible; `xqp`, `zqp` compatible) are still true: the
    step of `p` (on `o`) commutes with the steps of `s` (which avoid `o`), so `zp = xp (z − x)` is an
    extension of `xp`. Repaired with `run_comm_of_avoids` and `Avoids.step_of_poised` (`CritK.extend`).
    Classified as a proof gap (🛠️).
20. **Theorem 2 (proof repaired).** The proof applies Lemma 6 to an implementation from `(n, x)`-live
    base objects, but Lemmas 1–6 are developed only for atomic events. "The other `n − x` processes
    access `o` simultaneously … may never run in isolation" needs a semantics of steps on non-atomic
    objects. Our blocking-object model (item 4) and the adversarial object `advCons` make this precise.
    The process `w` must be chosen wait-free for the implementation but not for `o` (it exists because
    `|X_P| = x + 1 > |X_o|`), and the second process `r ∉ X_o ∪ {w}` exists because `x + 1 < n`. Both stay
    blocked forever when they alternate, starting with the one that did not take the last step on `o`
    (`theorem2`). Classified as a proof gap (🛠️).
21. **Lemma 5, Cases 1/2.** The claims "`z′ = z`" and "`z′p = z`" are correct but not needed. We only use
    "`z′p` is `v̄`-valent". The prefix `z′` is obtained by a structural recursion
    (`exists_prefix_without`) instead of "longest prefix".
22. **Lemmas 4 and 7: termination of the bivalence-preserving procedure.** The paper says "the
    procedure terminates" by wait-freedom (resp. fault-freedom). We build the infinite schedule from the
    infinite chain of extensions (`exists_exec_of_chain`), check that `p` (resp. every process) occurs
    infinitely often, and derive a contradiction with agreement (a decision would make a configuration of
    the chain univalent). Routine.
23. **Theorem 3, lower bound.** The paper says "there is a finite time after which no process of `X` is
    concurrent with `p`, so `p` runs alone". We formalize this as `wFree_of_wFree_others`. After the
    maximum over `q ≠ r` of "the time `q` decided or took its last step", every configuration equals
    `C_T` followed by a solo run of `r`.

## Section 6 (Theorems 5 and 6)

24. **Separate concrete model** (`Arbiter.lean`, `GroupConsensus.lean`, namespace
    `Podc.AsymmetricProgress.Group`). Crash-stop processes and arbitrary schedules. A process participates
    iff it takes ≥ 1 step and is correct iff it takes infinitely many. One shared access per step.
    Proposals are of arbitrary type `V`. Groups are `grp : Fin n → ℕ` with `grp q < m`, and group `0` is the
    paper's group 1.
25. **`(x,x)`-live objects are atomic.** `GXCONS[g]` and each arbiter's `XCONS` are wait-free objects
    accessed by at most `x` processes, so they are modelled as atomic consensus objects (first proposal
    wins, one step). The bound "at most `x` owners" only guarantees this access pattern and plays no other
    role.
26. **Tasks T1/T2** are interleaved alternately (T1, T2, T1, …). T2's busy-wait read and its return read
    are folded into one read. Deciding does not stop T1 (the paper does not say). This only adds executions,
    so safety is stronger. Termination is proved for this fair interleaving.
27. **Arbiter validity in real-time form** (`arbiter_validity_owner`/`_guest`): "a process with role
    `owner` (resp. `guest`) took a step before the return". The paper's specification (Section 6.1) omits
    "before", but its proofs of Lemma 10 Case 2 and Lemma 11 Case 2 use the real-time version. Figure 4
    satisfies it. Classified as a proof gap of Theorem 6 (🛠️).
28. **Theorem 6 validity** (left to the reader in the paper) is proved in real-time form
    (`group_validity`).
29. **Theorem 5** is stated for the standalone Figure 4 algorithm: each process invokes once, with a fixed
    role `role : ι → Role`. The `arbiter_termination` hypothesis "only guests invoke" is "every scheduled
    process is a guest". Theorem 6 reuses the arbiter invariant through a projection of the full program
    counter.
30. **Lemma 10** typo: "`y ∈ [1..n]`" should be "`[1..m]`" (slip; the proof is about groups). Its end marker
    reads "Lemma 11".
