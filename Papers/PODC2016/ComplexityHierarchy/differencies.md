# Differences between the formalization and the paper

Paper: Ellen, Gelashvili, Shavit, Zhu, *A Complexity-Based Hierarchy for Multiprocessor
Synchronization*, PODC'16 / arXiv 1607.06139v2. Summary: **all main theorems formalized are
correct as stated**; Lemma 8.2 is false in an edge case that is never used; several proofs have
gaps that we repaired (Lemma 9.1, Lemma 7.1's proof, Lemmas 6.5/7.3 for `R = ∅`, Lemma 3.2's
validity, linearization of double-collect scans in Sections 4 and 8); one statement in the text of
Section 7 is inconsistent with Theorem 7.5.

## Modelling differences (all harmless or strengthening)

1. **Inputs / validity.** The paper: every process has an input from the start; validity = the
   decision is the input of *some* process (possibly one that never takes a step). We use the task
   framework: a process participates by invoking the task with its input. Lower bounds assume only
   `weakConsensus` (if all participants have input `v`, every decision is `v`), which is implied by
   the paper's validity (take all non-participants with input `v`) and by the standard one
   (`Impl.Solves.weakConsensus`); so the lower bounds are *stronger*. Lower-bound proofs start
   from configurations in which all processes have been invoked (`Impl.Reach`), i.e. the paper's
   initial configurations.
2. **Obstruction-freedom.** Lower bounds assume only one-shot obstruction-freedom (`OneShotOF`);
   upper bounds prove CSLib's `ObstructionFree` (also after re-invocations).
3. **Decisions.** "`Q` can decide `v` from `C`" is formalized as "some `Q`-only execution *from*
   `C` contains a decision `v`" (`CanDecide`); decisions made before `C` do not count. With
   agreement, this coincides with the paper's notion on the configurations used (bivalent
   configurations have no previous decision: `Reach.pend_of_bivalent`).
4. **Binary vs `n`-consensus.** Lower bounds are proved for binary consensus (as in the paper) and
   transferred to `m`-valued consensus (`m ≥ 2`, e.g. `n`-consensus) by `Impl.toBinary`
   (`NConsensus.lean`); the paper only remarks this.
5. **Memory contents.** ℓ-buffers store the list of the last `≤ ℓ` written values (most recent
   first) instead of an `ℓ`-vector padded with `⊥`; the initial content is arbitrary
   (`memInit`) — the lower bounds hold for every initialization. Values in max-registers come from
   an arbitrary linear order; read/write/fetch-and-increment locations hold integers (`ℤ`, arbitrary
   writes, including negative values); test-and-set locations hold natural numbers (we prove "at
   least `k` nonzero locations" instead of "`k` locations set to 1", which covers arbitrary initial
   values).
6. **Multiple assignment** (Section 7) is modelled with the whole memory as a single base object
   `MB R ℓ V` with an atomic multi-location write; Section 6's per-location model is embedded into
   it (`toMB`, a step-by-step simulation), and both lower bounds are instances of one theorem
   (`lowerBound_core`) with packing capacity `k = ℓ` (single-location writes) resp. `k = 2ℓ`.
7. **Numbering of bounds.** We prove `n − 1 ≤ ℓ·#locations` resp. `n − 1 ≤ 2ℓ·#locations`, and
   the ceiling forms `(n − 1 + ℓ − 1)/ℓ ≤ #locations` etc. (`_ceil` corollaries).

## Issues found in the paper

### Section 6 (ℓ-buffers)

* **Lemma 6.5 assumes `R ≠ ∅`** ("suppose some process `p ∈ R` can decide…"), but Theorem 6.8 uses
  it for `n = 2`, where `R = P − Q = ∅` (Lemma 6.7 also uses it with `R = ∅` when `|P| = 3`, but
  there only the bivalence part is needed, which is trivial for `R = ∅`). For `n = 2` the needed
  conclusion "some location exists" follows from a separate (easy) argument: with no locations,
  two processes cannot communicate (`no_locations`). Same for Lemma 7.3 / Theorem 7.5.
* Lemma 6.6: "Let `q ∈ U''`. Then `q` decides `v` from `C''`" and "`α' ≠ α` because `v̄` is decided
  in `α`" implicitly need that all processes of `U'` are still undecided along the relevant prefix
  of `α`; we truncate `α` right after its first decision and use agreement to show that processes
  stay pending (`Reach.exists_two_deciders`). Minor.
* Lemma 6.7 is proved generically with `k`-packings; for single-location writes "at most
  `ℓ`-covered by `R`" is exactly "there is an `ℓ`-packing of `R`", and the `ℓ`-covered locations are
  the fully `ℓ`-packed ones.

* Lemma 6.1 (proved, `BufferAlg.lean`): correct. Exhaustive model check (ℓ ≤ 4, ≤ ℓ appenders, ≤ 6
  appends each) found no violation; the claim "no other append is linearized between `R_m` and
  `W_1`" needs `h_m` to be a *longest* history (so `R_m` is the latest of `R_1..R_ℓ`), as the paper
  says. With `ℓ + 1` appenders the construction fails (ℓ = 1: `p`, `q` read `⊥`, `q` writes
  `([],b)`, `p` writes `([],a)`, a reader reconstructs `[a]`), so the hypothesis is necessary.
  Formal deviations: values tagged with (process, sequence number) — the paper's "w.l.o.g.";
  ties among longest histories broken by the first one; linearizability via a ghost list of writes
  instead of the paper's nested induction.
* Theorem 6.3 (proved, `BufferAlgConsensus.lean`): the algorithm is flattened (racing counters +
  double collect + Lemma 6.1's reconstruction); Lemma 6.2's register layer is skipped (increments are
  appended directly to the group's history object), which is an equivalent but simpler simulation.

### Section 7 (multiple assignment)

* **Inconsistent bound in the text:** the introduction of Section 7 says "Then `⌈n/2ℓ⌉` locations
  are necessary", while Theorem 7.5 (and the abstract/§1.1) state `⌈(n−1)/2ℓ⌉`. The proof gives
  `⌈(n−1)/2ℓ⌉`; we formalize that.
* **Lemma 7.1: the proof is wrong as written, the statement is true.** The proof takes "any maximal
  Eulerian path" `r_1, …, r_t` and claims, for every `1 ≤ j < t`, a packing `g'` with one less
  process in `r_j` and one more in `r_t`. If the trail visits `r_t` earlier (`r_j = r_t` for some
  `j < t`), this is impossible. Concrete example (`lemma71_trail_counterexample`, by `decide`):
  locations `A,B,C`, processes `p1,p2,p3`, `g = (A,B,C)`, `h = (B,C,B)` (2-packings); the unique
  maximal trail from `A` is `A→B→C→B`, and re-packing from `j = 2` leaves `B` unchanged. Choosing a
  *shortest* such sequence fixes the proof; in the two applications in Lemma 7.2 one always has
  `r_j ≠ r_t`. We do not use Lemma 7.1: Lemma 7.2 (`fullyPacked_of_cov`) is proved with a
  closure/counting argument plus an augmenting-path lemma (`exists_packing_lt_of_walk`).
* Lemma 7.3: typo "longest prefix of `ζ` such that `p` can decide `v` from `Cζβ1β2`" — should be
  `Cξβ1β2`; "`Cξβ` and `Cξδβ`" means `β = β1β2`.
* Lemma 7.4: typo "a set `Q ⊆ P` of at mostwot two processes".
* Clarification (not an error): the commutation argument "the value of `r` is the same in
  `Cξδβ1β2` and `Cξβ1δβ2` due to `β2`" uses that `β2` writes each location of `L` at least `ℓ`
  times and (Lemma 7.2) only inside `L`; the formalization makes these conditions explicit
  (`IsBlock`).

### Section 8 (swap and read; proved by a subagent, `SwapAlg*.lean`)

* Theorem 8.8 holds (agreement, *standard* validity, obstruction-freedom; for `|P| ≤ #locations + 1`;
  with one process more there is a 10-step disagreement found by the model checker).
* **Lemma 8.2 is false as stated for every scan `S` with `ℓ_v(S) = 1`**: it asks for an earlier
  scan `T` with `ℓ_v(T) = 0` and `ℓ_{v'}(T) ≤ ℓ_v(T)` for all `v'`, i.e. all laps `0`; but every
  scanner has `ℓ_{input} ≥ 1` (line 1), so no such `T` exists. It is only applied with
  `ℓ_v(S) ≥ 2` (Lemma 8.4), where it holds; the formalization encodes the needed facts in the
  invariant `AInv`.
* Lemma 8.6 proves only weak validity ("if all inputs are `x`, only `x` is decided"); standard
  validity (decision = input of a participant) also holds and is proved.
* The paper gets linearizable scans from the double collect with `(id, seq)` tags (citing
  [AAD+93]) and then reasons with scans as atomic steps (Lemmas 8.3–8.5); only the composition
  step is implicit. The formalization proves it (`SInv.sim`: the algorithm with double-collect
  scans is simulated by the one with atomic scans). Lemma 8.3's counting argument is correct.
* "Anonymous" is inaccurate as written: the swapped values carry process identifiers (for the
  double collect).
* The bound "at most `3n − 2` scans in a solo execution" (Lemma 8.7) is not formalized, only solo
  termination.
* Model checks (C++, exhaustive for small `n` and lap bounds, plus 1M random runs for n ≤ 5) found
  no violation.

### Section 9 (test-and-set) — gap in the proof of Lemma 9.1, repaired

The proof defines `β` as the shortest prefix of `z`'s solo execution from `Cα_kξ` ending with a
test-and-set on a location `r ∉ L_k`, and then reasons about `Cα_kξψβ` and `Cα_kξψψ'β`, where
`ψ, ψ'` are steps of `p_1`. But `z`'s preliminary steps in `β` (reads, test-and-sets on `L_k`) are
executed *after* `ψ` there and may return different values (`ψ` may set locations to 1, `ψ'` may
be a test-and-set on `r`), so `z` need not perform `β`, and the claims "`β` sets `r ∉ L_k` to 1" /
"`Cα_kξψψ'β` is indistinguishable from `Cα_kξψβ` to `p_0`" are unjustified. **Repair**
(`TestAndSet.lean`): run `z`'s preliminary steps first (they change no memory), so that `z` is
poised to test-and-set `r`; then argue with `z`'s single remaining step, which commutes with any
single step of `p_0`/`p_1` as far as the other process and the memory are concerned
(`soloStep_comm_agree`; this also removes the paper's case analysis on `ψ'`). The lemma and
Theorem 9.2 hold as stated.

### Section 4 / Section 5

* Theorem 4.1: the paper's interleaving is described in segments and the reason why each process
  sees exactly its solo view is left implicit; the needed invariant (a process that is not poised
  to write has the larger solo value; a process poised to `write-max(x)` dominates after its write)
  is made explicit (`InvW`). Correct.
* Theorem 5.1: "without loss of generality at least as many fetch-and-increments in `β'` as in
  `α'`" is made explicit by comparing the register values reached; "`p` has decided `0` since `q`
  takes no steps" uses the indistinguishability argument of Lemma 6.4 (`canDecide_initial`).
  Correct.

* Theorem 4.2 (two max-registers): correct. Typo "(r,x) ≺ (r′,x)" should be "(r,x) ≺ (r′,x′)";
  "this scan occurred after `p`'s scan" relies on linearization points of the non-atomic
  double-collect scans, which exist because both registers only increase (as the paper notes on
  p. 6); the step from linearizable scans to the agreement argument is left implicit (the formal
  proof uses a ghost chain of all pairs seen when reading `m2`); validity needs the
  unstated observation that a process seeing `m1 = (0,0)` has itself written `(0, input)`, so `0`
  is an input. Registers range over the lexicographic order `ℕ ×ₗ Fin n`; the paper's encoding
  `(x+1)·y^r` is an order embedding for every `y > n` (primality not needed,
  `TwoMax.encode_strictMono`).

### Section 3 (racing counters; proved by a subagent)

* Lemma 3.2 (bounded counters): validity needs every scan to see a nonzero component (otherwise the
  argmax of an all-zero vector could be an unproposed value, since decrements lower counts); not
  argued in the paper. Closed with an invariant ("pending decrements + 1 ≤ total count"); the
  bounds `0 ≤ c ≤ 3n − 1` are proved with explicit invariants. A Python model check (n ≤ 4,
  m ≤ 3) found no violation.
* Tie-breaking (`argmax`) is a fixed choice; a decided process that is re-invoked returns its old
  decision; increments return dummy acknowledgements; the first promotion in Lemma 3.2 is a plain
  increment.

### Not formalized (see README)

Lemma 5.2/Thm 5.3, Thms 9.3/9.4, remarks on heterogeneous capacities and other instruction sets.
