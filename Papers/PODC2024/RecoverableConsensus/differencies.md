# Differences between the formalization and the paper

Ovens, *Determining Recoverable Consensus Numbers*, PODC 2024 (arXiv 2405.04775v1).

**Summary.** The main result (Theorem 13: `n`-recording is necessary for recoverable wait-free
consensus among `n` processes using deterministic types) is **correct** and fully formalized,
following the paper's proof closely. We found only imprecisions and small gaps in Section 3
(missing reachability assumption, an over-general Observation 5, typos). In Section 4 one step of
the proof of Lemma 15 is false as stated (but easily repaired), the proof of Lemma 16 has a
non-symmetric "symmetric" case and off-by-one bookkeeping, and the claim that `T_{n,n'}` is
non-readable fails for `n' = n − 1` if readability is understood up to encoding of responses.

## Modelling choices (not errors)

1. **Configurations contain the inputs.** A crash resets a process to "its initial state", which
   depends on its input; we store the inputs in the configuration (`Cfg.inp`, never changed).
   Indistinguishability to `Q` (`AgreeOn Q`) requires equal local states *and* inputs on `Q`.
2. **Steps.** Every step of a process that is not in an output state is exactly one operation on
   one object (local computation folded into the continuation); steps in output states are no-ops.
   The paper's "a step can be an operation applied to some object or a no op" is read as: no-ops
   only in output states.
3. **Decisions.** "Some process has decided `v` in `Cαβ`" is formalized relative to the base
   configuration `C` of the set of executions: some process is in an output state with value `v`
   at some configuration of the execution `αβ` from `C`, including `C` itself (`Dec C (α ++ β) v`).
   The paper's notion is history-based ("has output in some earlier step"); for the valency
   arguments only decisions in the considered executions matter.
4. **Agreement** is "all values output in an execution are equal", including two outputs of the
   same process in different incarnations. The paper writes "no two processes output different
   values"; its proof (Lemma 6: "some process has decided `v̄` … contradicts agreement") needs the
   stronger reading (the second decider may be the same process after a crash), which is also the
   standard definition (Golab; Delporte-Gallet et al.).
5. **Recoverable wait-freedom** ("every process either crashes or outputs a value after taking a
   finite number of steps from its initial state") is formalized on infinite executions: if `p`
   takes infinitely many steps and does not crash after time `N`, then `p` is in an output state at
   some time `≥ N` (it outputs in its last incarnation). Wait-freedom (crash-stop model) is the same
   on crash-free executions.
6. **Binary consensus**, every process has an input from the start (as in the paper).
7. **Objects.** Arbitrary index type `ι` of objects (the paper: types `T₀, T₁, T₂, …`); registers are
   generalized to read/write-like objects `ObjSpec.RWLike` (every operation read-only or a blind write) in
   `WFSolvable`/`RecSolvable`; initial values are chosen by the algorithm.
   The test&set object in `tas_not_recSolvable` (Golab) is the library's readable test&set `rtasObj`
   (same states and transitions as a test&set with read: `tas` sets the bit and returns the old value).
8. **Readable** is formalized up to encoding of responses: some operation never changes the value
   and its response determines the value (`ObjSpec.Readable`). Only used in the statement of Theorem 14 and
   in the remark on `T_{n,n−1}` below.
9. **Consensus numbers.** `ConsensusNumber S n` / `RecConsensusNumber S n` quantify over all
   `m > n` ("no such algorithm for `n + 1` or more processes"); the impossibility proofs are done for
   every `m > n` directly (the paper argues for `n + 1` processes).
10. Valency, criticality and teams are defined on executions (event lists) from a base
    configuration, as in the paper; since the system is deterministic, "an execution `β` from
    `C′` indistinguishable from `α′`" is literally the same event list.

## Section 3

11. **Lemma 6 (standard implicit assumption).** "Let `C` be a configuration": the proof applies agreement and
    recoverable wait-freedom to executions through `C`, so `C` must be reachable from an initial
    configuration. Lean: hypothesis `Reach A Adm C` (`exists_crit`, `exists_stuck`); the same for
    Lemmas 7–10, 12. All configurations used in Theorem 13 are reachable; this is the usual implicit
    convention of valency arguments, not a real gap.
12. **Observation 2** says "suppose that `P` is univalent in `α`" (should be `P′`). Only the
    direction "`v`-univalent in `α` ⇒ `v`-univalent in `αβ`" is justified in the paper; the converse
    needs that some decision is reachable from `αβ` by `P′` (true when `P′ ≠ ∅` by solo
    termination). The formalization only uses the forward direction (`UnivQ.append`) and solo runs.
13. **Observation 5 (imprecise; minor edge case).** As stated ("for any configuration `C′` such that `C′ ∼_{P′} Cα`
    and all objects have the same values") it fails when a process outside `P′` has already decided
    the other value in `C′` (with our configuration-based `Dec`), and with the paper's history-based
    notion of "decided" it is not even well defined for an arbitrary configuration `C′`. Lean
    (`UnivQ.transfer`): extra hypothesis "no process outside `P′` is in an output state in `C′`".
    It holds in every application (the processes outside `P′` have the same state as at a critical
    configuration, where nobody has decided: `Crit.not_out`).
14. **Lemma 7.** Formalized with the paper's proof; the case "`β_{v̄}` is empty" (some process has
    already decided `v̄` in `Cα`) is not mentioned in the paper and is handled separately (minor edge
    case: it contradicts the `v`-univalence of `αp₀` directly).
15. **Lemma 10** is formalized as stated (`lemma10`); the conclusion "`value(O,·)` equal" is turned
    into equality of the whole memory, which holds because all processes are poised on `O` and each
    process of a schedule in `S(·)` takes one step (`mem_eq_of_valAfter_eq`).
16. **Lemma 12.** Typo: "critical with respect to `E*_z(C′Xλ_k)`" should be `E*_z(CαXλ_k)`. The
    hypotheses are formalized slightly more generally: `X` is any execution of processes with
    identifiers `≥ k` (the paper: `X = ⟨⟩`, or `X = p_{n−1}` with `p_{n−1}` on team `v̄` — the team
    condition is never used), the schedule `pρ` must only contain some `p_ℓ` with `ℓ < k`, and the
    equality of the value of `O` is replaced by equality of the memory. The paper's Lemma 12 does
    not state that all processes are poised on a common object in `CαXλ_kα′`; this follows from
    Lemma 9 and is a hypothesis (`hpo'`) of `lemma12`.
17. **Theorem 13.** The proof follows the paper (stages `Stage` with properties (a)–(f)). Minor
    differences: the object `O` is not tracked across stages (the paper shows it stays the same;
    the conclusion only needs the object of the final `n`-recording configuration); "without loss of
    generality `p_{n−1}` is on team `v̄`" is realized by choosing `v` as the opposite of
    `p_{n−1}`'s team; "`p_{n−1}` is on team `v` in `D₁′`" is derived from univalence of
    `{p_{n−1}}` (as in the general step) rather than from solo runs; bivalence of `D_i` additionally
    uses that `p_{n−1}` running solo from `D_i` decides (the paper only states univalence).
    The stage index `i` is bounded (`i ≤ n − 1`) via the existence of a team-`v̄` process
    `p_j`, `j < n − i`, exactly as in the paper.
18. **Theorem 14** is stated conditionally on DFFR'22 Theorem 8 (hypothesis `dffr`), which the paper
    cites. DFFR'22 Theorem 8 is now formalized in `Papers/PODC2022/RecoverableHarder`, and
    `ovens_theorem14` there is Theorem 14 without the hypothesis. Our `ObjSpec.Readable` (some operation preserves the value and
    its response is an injective function of the value) is slightly broader than a literal Read
    operation returning the value itself; DFFR's result still covers it, since an algorithm can
    decode the response into the value.

## Section 4

19. **Lemma 15, proof, case `o_i = opR` (false claim, repaired).** The paper claims that if `p_i`
    (team `v`) applies `opR` then `value(O, C′p_ip_j) = value(O, C′p_j)` for `p_j` on team `v̄`
    "in either case". This is false when `value(O, C′) = s_{x,t}` with `n′ < t < n − 1` and `p_j`
    applies `op_y`: then `C′p_ip_j` has `O = s⊥` but `C′p_j` has `O = s_{x,t+1}`. Repair (used in
    `lemma15` and `lemma16`): in this case `p_i` gets `⊥` both in `C′p_i` and in `C′p_jp_i`, and
    `O = s⊥` in both, so these configurations are indistinguishable to `p_i` (no third process
    needed). The case where `opR` does not change the value is as in the paper.
20. **Lemma 16, case `o_i = opR`, "the case `j < i` is symmetric"** is not symmetric (the crash
    of `p_j` is only in budget when a smaller process has stepped). The crash-free comparison of
    item 19 handles both cases.
21. **Lemma 16, construction of `ρ, τ`.** The bound `ℓ < n − n′ − 1` is off by one (up to
    `n − n′ − 1` rounds); this is harmless, since the crash count `ℓ + 1 ≤ n − n′ ≤ n − 1` used for
    the budget still holds. When `O` becomes `s⊥` the process `p_{n′}` has not decided yet (the claim
    "`p_{n′}` has decided in `Cασ₀ρ_ℓ`" fails) — the formal proof concludes directly from equal
    memory and equal state of the last process (`team_contra`); typo `τ_{i+1} = ρ_iδ′…` (should be
    `τ_iδ′…`); typo in the first invariant `Cασ₀ρ_i ∼ Cασ₀τ_i` (should be `Cασ₁τ_i`); missing "is"
    in the statement of Lemma 16 ("the recoverable consensus number of type `T_{n,n′}` [is] `n′`").
    The case where the last process decides before accessing `O` is covered by the paper's `δ`
    ("until it decides or is poised on `O`"); the formal proof merely treats it as a separate lemma
    (`contra_out`) — not a gap in the paper.
22. **Crash budget in Lemma 16.** The formalization uses `E*_z` with `z = n` (any `m > n′`
    processes); the paper uses `m = ⌈n/2⌉` with exactly `n′ + 1` processes. Any sufficiently large
    constant works; this does not change the statement.
23. **Number of processes.** The impossibility parts of Lemmas 15 and 16 are proved for every
    `m > n` resp. `m > n′` (the paper treats `n + 1` resp. `n′ + 1` processes).
24. **Hypothesis `1 ≤ n′`** (as in the paper) is used in Lemma 15's impossibility proof (it needs
    `m ≥ 3`); the algorithms need only `n′ < n`.
25. The paper's counting arguments for the algorithms ("at least `i` operations must be applied")
    are replaced by explicit inductive invariants (`Inv15` on crash-free executions, `Inv16` under
    arbitrary crashes, including that the bit recorded in `O` never changes once set).

## Remark on readability of `T_{n,n'}`

26. The paper describes `T_{n,n'}` as a non-readable type for all `n > n′ ≥ 1`. For `n′ + 1 < n`
    this holds (`not_readable_Tnn`). For `n′ = n − 1`, however, `opR` never changes the value (all
    `s_{x,i}` have `i ≤ n − 1 = n′`) and its response determines the value (`⊥` only at `s⊥`), so
    `opR` is a read up to the encoding of `s⊥` as `⊥` (`readable_Tnn_pred`). Under a literal reading
    of "Read returns the current value", `T_{n,n−1}` is non-readable only because `opR` returns
    `⊥` instead of the name `s⊥`. This does not affect any theorem (and is consistent with DFFR:
    `T_{n,n−1}` is `(n−1)`- but not `n`-recording for `n ≤ 4` by our exhaustive check).
