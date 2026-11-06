# Differences between the formalization and the paper

Paper: Aghazadeh, Golab, Woelfel, *Making Objects Writable*, PODC 2014. The PODC version is not openly
available; we formalize Chapter 4 of Aghazadeh's PhD thesis (*Efficient Shared Memory Algorithms for
Bounding Space*, U. Calgary 2018), which is the paper with full proofs. **All numbering is the thesis
numbering** (Theorem 4.1, Lemmas 4.2, 4.5, 4.8, Claims 4.6–4.25, Figures 4.2–4.15).

## Statement-level issues

None of the formalized statements is false.

- **Lemma 4.2, `k ≥ 1`** (degenerate): the `(k,b)`-array implementation computes `Ver + 1 mod k`;
  for `k = 0` there is nothing to implement. We assume `[NeZero k]`. Not an issue.

## Proof gaps

- **Lemma 4.5, proof of Claim 4.7 / construction of `S_ℓ`** (🛠️: a step inside a proof of a true
  lemma). The proof takes the sub-history `Λ_ℓ` of the base-object operations of the calls with
  timestamp `ℓ` and says: "Subsequence `Λ_ℓ` is a history, and by (4.1), no `A[i_ℓ].SWrite()` overlaps any
  other operation call on `A[i_ℓ]`. Therefore, there is a linearization `S_ℓ` of `Λ_ℓ`." Sequential
  writability is a property of the histories of the object `A[i_ℓ]`; `Λ_ℓ` is only a sub-history, and a
  sub-history of a linearizable history need not be linearizable. The inference is false without the
  template's requirement that the write-index is *not in use* when the `Write` is invoked, a
  requirement the proof never uses. `Counterexample.lean`: a transcript following the template except for
  that requirement, satisfying (C) and ownership, with each base object's history linearizable, whose
  high-level history is not linearizable (`notInUse_necessary`); its `Λ_1` is not linearizable
  (`lambda1_not_linearizable`). Repair (`Lemma45.lean`): take one linearization `L_i` of the *whole*
  history of each `A[i]` and show that the timestamps are sorted along `L_i`
  (`IsCtrl.ret_before_of_keyPos_lt`, which is where "not in use" is needed); then each block of
  timestamp `ℓ` is a contiguous segment of `L_{i_ℓ}` starting with its `SWrite`, and the legality of the
  block follows from that of `L_{i_ℓ}`.
- **Lemma 4.5, (4.1)** — "no `A[i].SWrite()` overlaps any other operation on `A[i]`" — is stated from
  (C2) and ownership; we prove it (`IsCtrl.writesIsolated`). For `SWrite`s of the owner the paper's
  argument ("processes are sequential") is fine.
- **Lemma 4.2, proof of Part (b1)**: typos — "`[t_W@rsp, t_R@inv] = [t_W@64, t_R@60]`" and "q reads
  `(x_W, v_W)` from `A[i*]` in line 60" should be line 59; "when p reads this variable in line 60 of R"
  should be `q`. The proof also does not say how pending operations are linearized; the formalization
  handles them (linearization points at lines 59/64/58).

- **Theorem 4.1 / Figure 4.4 "not in use"** (🔧): the template requires that the write-index is not in use
  when chosen; the proof of Theorem 4.1 only proves (C) (Lemma 4.8). It holds (from Claims 4.22/4.23) and is
  part of our invariant (`WF.Inv.notInUse`, `WF.lemma_4_8` gives `Template ∧ CondC`).
- **Lemma 4.8, proof of (4.32)** (🔧): "p invokes more than n Write() calls during `[t_E@36, t_E@39]`, and so
  q completes at least n Write() calls during this interval" — the counted `Write`s may include one invoked
  before `t_E@35`, outside the hypothesis of Claim 4.20; only its line 14 must come after `t_E@35`, which holds.
  Typo: "q completes" should be "p completes".
- **Claims 4.15(b), 4.16** (✏️, inside the proof): false at the level of single points — within one
  `recycle()`, line 26 may add `i*` to `free_p` at the same point at which lines 27–28 read `i*` from `Annc`
  and enqueue it (mechanism: `example` at the end of `Lemma48.lean`; we did not build a full execution). The
  uses of these claims keep one `recycle()` call of margin, so nothing breaks; our invariant uses "an index is
  held in the queues until the next read of its slot" instead.
- **Claim 4.19**: "if p writes `(j, s)` to one of `H_p[q]`, `H'_p[q]` during a `Write`, it writes `(j, s')` to
  the other one during the same `Write`" is asserted for pairs of last writes without argument; true
  (`pairIn`/`pairOut` in the invariant).
- **Not proved**: Claim 4.14 (`free_p` never empty) — in the model the step `free_p.remove()` is disabled when
  `free_p = ∅`, which does not affect safety (linearizability); wait-freedom and the step/space bounds of
  Theorem 4.1 are not formalized beyond the shape of the step relation.

## Modelling choices

- **Transcripts instead of composed implementations.** CSLib has no composition theorem, and the base
  objects `A[i]` of the transformation are not atomic. Lemma 4.5 is therefore stated on *transcripts*
  (`Ev`): lists of the high-level invocations/responses, the invocations/responses of operations on the
  `A[i]`, and the writes to `Ptr`; other steps are irrelevant to the lemma and omitted. The high-level
  history `highH` and the base-object histories `lowH i` are CSLib histories, so the CSLib notions
  (`IsLinearization`, `Precedes`) apply unchanged.
- **Sequential writability** is a hypothesis on the base-object histories occurring in the transcript
  (`SeqWritable W (lowH W i α)`: linearizable whenever no write overlaps another operation), which is
  exactly what "the objects `A[i]` are sequentially writable" provides.
- **Writable type** (`Writable`): an `ObjSpec` with operations `wr v` that set the state to `v`; the
  response `wresp v` of `Write(v)` may depend on `v` (the paper: "returns nothing").
- **The template** (`Template`): a per-process control automaton (`PStep`) records exactly what
  Figure 4.4 fixes: `Write(v)` = `A[f].SWrite(v)` on an owned index `f`, then `Ptr.Write(f)`, return;
  `Exec(o)` (for a non-write operation `o`) = one `A[i].Oper(o)`, return its response. How the indices are
  chosen is unconstrained. "Not in use": we require `Ptr ≠ f` when `A[f].SWrite` is *invoked*
  (`NotInUse`); the paper requires it at the invocation of the `Write` call, which implies ours
  (`notInUse_of_atWriteInv`), so our Lemma 4.5 is slightly more general.
- **Condition (C)** (`CondC`): a *point* is a position between events; `t*` lies after the
  invocation event of `E` and no later than the invocation of `Op`; "no `SWrite` overlaps `[t*, Op's
  response]`" = each `SWrite` on `A[i]` returned before `t*` or was invoked after `Op` returned (a
  pending `SWrite`/`Op` never returns).
- **Initial `Write(v₀)`.** The paper starts transcripts with a `Write(v₀)` of process 0 in isolation and
  `Ptr = ⊥`. Our Lemma 4.5 needs no such prefix: `Ptr` is initially `⊥` (`none`), and an `Exec` can only
  satisfy (C) after some `Write` has put an object into use.
- **The paper's `t(M)`** is "the latest point satisfying (C1) and (C2)"; any such point works
  (`tsOf` chooses one).
- **The algorithm of Figure 4.5** (`Algorithm.lean`, namespace `WF`): `n ≥ 1` processes; indices
  `Fin n × Fin (8n+9)` with owner `Prod.fst` (the paper's `i mod n = p` up to relabelling); `ctr_p` kept as an
  unbounded counter used `mod n`; one shared-register access per step with the local lines attached as on
  p. 58–59 (lines 25–28 form one step, etc.); `free_p.remove()` nondeterministic; the `SW` objects are black
  boxes (invocation and response separate steps, arbitrary responses — their correctness is the `SeqWritable`
  hypothesis of Theorem 4.1); line 38 is disabled on `Ptr = ⊥` (never happens after the initial write,
  `ptr_ne_none`); ghost fields (transcript, write numbers, epochs, positions) never influence guards or
  written values. Executions (`IsExecution`) start with the solo complete `Write(v₀)` of process 0, as in
  the paper, and the linearized high-level history includes it.
- **Theorem 4.1 / Corollary 4.4** are formalized for linearizability only (`WF.theorem_4_1`,
  `WF.corollary_4_4`). For Corollary 4.4 the objects `A[i]` are required to have histories of executions of
  the Figure 4.2 implementation (`kWordImpl`), up to internal steps (`dropTau`); CSLib has no composition
  theorem, so the flattened implementation is not built as one `Impl`.
- **Lemma 4.2**: the `(k,b)`-array is `kbArray k V v₀` with entries in an arbitrary type `V` (the
  `b`-bit values) and initial/reset value `⊥ = v₀`; `Read` returns `some S[i]`, `Write`/`Reset` return
  `none`. Base objects: CSLib registers `Ver : Fin k` and `A[i] : V × Option (Fin k)` (the version
  `⊥ = none`). "Executed in isolation" = `ResetsIsolated`. Register sizes (`b + O(log k)` bits) are by
  the types; step bounds: at most 3 base-object accesses per operation.
- **Figure 4.2** (`k`-word register): "It is obvious that any history … is linearizable, provided that
  each `SWrite()` operation call is not executed concurrently with any other operation" — proved
  (`kWord_seqWritable`).
