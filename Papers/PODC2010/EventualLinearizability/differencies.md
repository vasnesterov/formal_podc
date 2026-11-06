# Differences between the formalization and the paper

Paper: Serafini, Dobre, Majuntke, Bokor, Suri. *Eventually Linearizable Shared Objects.* PODC 2010.
Version used: the authors' copy with the appendix (full proofs of Theorems 1–3, Lemmas 1–7).

## Modelling choices (history level, Section 3)

- **Histories** are CSLib Herlihy–Wing histories (`Cslib.SharedMemory.HerlihyWing`): lists of
  `inv p x o` / `res p x r`; an operation instance is its `OpId` `(p, x, k)`, which is invariant under
  `H|x`. The paper's "all operations are unique" is this identification.
- **Time.** The paper's global clock enters `t`-linearizability only through "the operations invoked
  after `t`". We state everything for an arbitrary set `A` of late operations (`IsTLin spec H A L`),
  and `after invTime t` gives the paper's set for a clock `invTime`. This is more general: Lemma 2 is
  proved for any `A ⊆ A_x` (in particular `A = after invTime tmax`, `A_x = after invTime t_x`,
  `tLinearizable_of_restrictX_after`). In the Theorem 1 counterexample the clock is the event position
  (`late = after (tInv H₀) 3`).
- **Sequential histories with explicit identities** (`IdSeq`): `τ(i, o)` and `t`-permutations are
  lists of `(OpId, record)`. CSLib's `idsOf` would force each process's operations into program order,
  which the paper does not require for `τ(i, o)` or for operations invoked before `t`.
- **`t`-permutations are complete**: (P1) says every operation invoked in `H` is in `P`, including
  pending ones; we give every entry a response. The paper's sequential histories may end with one
  pending invocation. For total operations (the paper's assumption in Lemmas 3–4) this changes
  nothing, and all our objects are deterministic, hence total.
- **Weak consistency, condition (iii)** "for each operation `o'` invoked by `p_i` before `o`" is
  `b.p = a.p ∧ Precedes H b a` (in a well-formed history, an earlier operation of the same process
  completes before the next one is invoked). `τ(i, o)` is indexed by `o` alone (its identity contains
  the process). We require `τ(i, o)` to have distinct operations (a sequential history of unique
  operations).
- **Empty history legal.** The "only if" directions of Lemmas 1 and 2 and Lemma 3 assume `[] ∈ spec y`
  for every object (true for every sequential specification; CSLib's `Legal` requires each object
  restriction to be in the object's specification, so it is needed formally). Same assumption as
  CSLib's `IsLinA.restrictX`.
- **Nonblocking** is formalized as in Herlihy–Wing and as in the paper's Lemmas 3–4: if `H` has the
  property and `inv` is a pending invocation of a total operation, some response `resp` gives
  `H · resp` the property, for the same `t` (same `A`).

## Modelling choices (layer level, Sections 4–5, Appendix B)

- **Layer runs** (`LayerRun`): `S i t` for all `t : ℕ`, submissions `sub o = some (j, t)`, a set of
  correct processes. Nontriviality, set stability, (C1)–(C3), Eventual Stability, `t`-consistency are
  transcribed literally. `t`-consistency quantifies over all times `t_i, t_j > t` (with `S(i, t_i)`
  the sequence delivered last), not only delivery times; in `lemma5_false` the two sequences are
  delivered at time 4, so this makes no difference.
- **Eventual Stability is per run** ("there exists a time `t`" in the run), like every other
  property of `S(i, t)`. See the discussion of Theorem 3/4 below for the uniform alternative.
- **Algorithm 1** (`alg1`): a run is a list of low-level inputs (invocations, deliveries), one per
  time unit; operations are identified by invocation order; `execute(o, H)` runs the deterministic
  specification on `H` up to and including `o`. The layer run is derived from the input list
  (`layerOf`), and is constant after the last input.
- **General implementations** (`ImplModel.lean`, for Theorems 2 and 3): deterministic local automata
  reacting to invocations, deliveries and ticks, communicating only through the layer (submitted
  items are `(submitter, index, payload)`); an adversary chooses one action per time unit (it plays
  environment, scheduler and layer); admissibility = crashed processes stop, correct processes tick
  infinitely often, environment well-formed and allowed (SWSR), and the layer run satisfies its
  specification.
- The model does not forbid an implementation to emit a response without a pending operation;
  such histories are simply not well-formed, and nothing in the proofs relies on this freedom.
  Non-vacuity of the termination hypothesis: `localImpl` (answers from a local copy, never
  submits) satisfies `Terminates` (`localImpl_terminates`).
- In the proof of Theorem 2, weak consistency is used only in `σ1` (where `p0` crashed),
  `t_l`-linearizability only in `σ2` (no crashes), termination only in `σ0` and `σ1`. The general run
  lemmas (agreement of runs, logs, the round-robin layer satisfying Eventual Consensus) are in
  `Runs.lean`.
- **Termination** (`Terminates`): every operation of a correct process completes. The paper's
  definition of Eventual Linearizability contains no liveness requirement, but its proofs use it
  (Theorem 2: "Let `t_w` be the time when the write operation completes"; Lemma 6: "each invoked
  operation is eventually completed"). Without it the statement of Theorem 2 is false (an
  implementation that never responds is trivially eventually linearizable). Implied assumption (✏️).
- **Eventual Linearizability of an implementation** (`EventuallyLinearizable`): one `t_l` for all
  admissible runs (the paper insists on this: "Showing Eventual Linearizability on an implementation
  entails identifying a single value of `t` for all histories"); every prefix weakly consistent, and
  `t_l`-linearizable in runs without crashes. This is weaker than both the uniform notion of Section 3
  and the non-uniform notion of Appendix B, so the impossibility results are stronger.
- **Theorem 2** uses infinite admissible runs (the paper claims Eventual Consistency for three
  *finite* runs, where the liveness property (C3) has no meaning, and where `p1` "takes no actions"
  in `σ0`; we let `p1` crash in `σ0` and `p0` crash in `σ1`, and extend `σ2` by a canonical
  round-robin layer). Only two processes, as in the paper's proof.

## Statement-level findings

1. **Theorem 1, nonblocking part — false** (❌). `theorem1_nonblocking_false`,
   `not_eventuallyLinearizable_nonblocking`. Lemma 3 and Lemma 4 are true
   (`weaklyConsistent_nonblocking`, `tLinearizable_nonblocking`), but "directly follows from Lemmas
   1, 2, 3 and 4" combines two different responses. Other reading: if "Eventual Linearizability"
   of a single history meant "weakly consistent and `t`-linearizable for *some* `t`", nonblocking would
   hold, but trivially (the paper itself notes every finite history is `t`-linearizable for a late
   `t`), and Lemma 4 (which keeps `t`) would be pointless; the paper's notion fixes one `t` for all
   histories of an implementation, so the fixed-`t` reading is the meaningful one.
   A further reading: Section 3.2 words nonblocking as "there exist no history such
   that every extension of the history violates Eventual Linearizability". Taken literally (arbitrary
   extensions), `H₀` is not a counterexample: if `p2` first invokes `swap(0)` and `o` then returns
   `0` with `τ(p0, o) = [i1, swap(0), o]`, both properties hold. But that literal notion is nearly
   vacuous (it lets `o` wait for another process, and the empty extension already qualifies), and
   the paper proves Theorem 1 through Lemmas 3–4, which are Herlihy–Wing's nonblocking (append the
   response of the pending invocation), and claims "the same ... nonblocking properties as
   Linearizability". We judge the claim against that notion.
2. **Theorem 1, locality — true.** Lemma 1 (`weaklyConsistent_iff_restrictX`) and Lemma 2
   (`tLinearizable_iff_restrictX`, `tLinearizable_of_restrictX_after`) hold.
3. **Lemma 5 — false** (❌). `lemma5_false`, `not_lemma5`. The proof applies (C3) to
   arbitrary operations, but (C3) only covers operations submitted by correct processes. The
   counterexample needs a faulty process (it submits `a`, `b`, then never receives anything); all
   other ingredients are as the paper allows. If all processes are correct the proof goes through.
4. **Theorem 3, sufficiency (Lemma 6 / Algorithm 1) — false** (❌).
   - Algorithm 1 is not weakly consistent over an Eventual Consensus layer
     (`algorithm1_not_weaklyConsistent`): set stability allows an operation observed earlier to be
     reordered after the new one. Holds under either reading of Eventual Stability (the
     counterexample is stable from time 7) and of `t_l` (weak consistency is required of every
     history). The paper's remark that weak consistency lets "subsequent serializations ...
     reorder previously-observed operations" does not help: `τ(i, o)` must still end with `o`,
     so previously observed operations stay before `o`.
   - `not_eventuallyLinearizable_eCons` needs one `t_l` for all runs (the paper: "identifying a
     single value of `t` for all histories"; its proof of Theorem 2 fixes `t_l` for all runs).
     If `t_l` is also read per run, sufficiency is not refuted (only Algorithm 1 / Lemma 6's proof).
   - Under the per-run reading of Eventual Stability, *no* implementation over an Eventual Consensus
     layer is eventually linearizable, even for a SWSR binary register
     (`not_eventuallyLinearizable_eCons`): the paper's own proof of Theorem 2 works verbatim, because
     its layer behaviour satisfies Eventual Stability from the final delivery on. So Theorem 3's
     sufficiency is false under this reading.
   - Under the uniform reading ("one stability time for all runs", used in the proof of Theorem 4),
     sufficiency is plausible with a repaired Algorithm 1 (complete `o` after the earlier-observed
     operations), but the proof of Lemma 6 also uses the false Lemma 5 and a `t_l` built from per-run
     times (`t_c`, the crash time of faulty processes, and `t_p`), which does not give one `t_l` for
     all runs. Not formalized.
   - Necessity (Lemma 7) is not formalized. Its proof builds a per-run stability time
     `t_s > max(t_l, t_d)` (`t_d` depends on the run), so under the uniform reading it is
     unestablished.
   Conclusion: under each reading of Eventual Stability one half of Theorem 3 fails or is
   unestablished; under the per-run reading the sufficiency half is refuted.
5. **Theorem 2 — true** (`theorem2`), assuming termination (implied, see above).

## Proof-level findings (statements true)

- **Lemma 1, "if" direction.** The paper reuses `τ_x(i, o)` of `H|x` for `H`; this violates
  condition (iii) across objects (`τ(i, o')` for an earlier `o'` on another object is not contained
  in `τ_x(i, o)`). Repaired by gluing, for each object `y`, `τ_y` of the last earlier operation of
  `p_i` on `y` (`weaklyConsistent_of_restrictX`).
- **Lemma 2, "if" direction.** The minimal-cycle argument asserts `o_k <_{H,tmax} o_i <_{H,tmax} o_j`,
  which does not follow (`o_i` need not be related to `o_k` by real time). Repaired by a key-sorting
  construction: the key of an operation on `x` is the latest invocation time of a late operation at
  or before it in `L_x`; keys are monotone along each `L_x` and strictly increase along `<_{H,t}`
  (`tLinearizable_of_restrictX`).
- **Lemma 3.** The proof writes `p_j` for `p_i`, and needs the empty history to be legal when `p_i`
  has no earlier operation (it then takes `τ = inv · resp`).
- **Lemma 4.** "If not, `inv` is not included in `L` since `L` only contains completed operations"
  contradicts (P1); under (P1) the pending operation is always in `L` and its result there is the
  response. Totality is not needed (`tLinearizable_nonblocking` has no totality hypothesis).
- **Section 3.2**, "every well-formed history `H` has a `t`-permutation `P` for each value of `t`":
  needs total operations (results of pending operations must exist). Remark, not formalized.

## Not formalized

- Theorem 4 (impossibility with `◇S`). Its proof fixes "a time `t` after which eventual stability holds
  for each run", i.e. reads Eventual Stability uniformly over runs; with the per-run definition (the
  one Lemma 7 constructs and Theorem 3 needs for its necessity part) the construction does not
  apply, because each extension `σE…` may have its own, later, stability time. The base case also
  does not need the consensus impossibility of [6]: in `σ0`'s extensions the processes of `Π_m`
  never hear of `s`. The proof also has slips: messages inside `Π_m` before `t_k` must be received in
  `σ_k` (the text puts all messages sent after `σ_{k-1}` into `M_k`, "not received"), and "Runs `σE21`
  and `σE22` are indistinguishable" should read `σE22` and `σE23`.
- Lemma 7 (necessity part of Theorem 3), Section 5 Aurora (Lemmas 8–13), Section 2 remarks.
