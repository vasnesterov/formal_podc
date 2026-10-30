# Differences between the formalization and the paper

Paper: Constantinescu, Dufay, Paramonov, Wattenhofer, *From Few to Many Faults: Optimal Adaptive Byzantine
Agreement*, PODC 2026, arXiv 2505.19989 v3. Checked: Theorems 3.1, 3.3, 3.8 (with 6.2), and the lemmas of
Appendix B / Section 10.1 behind Theorem 3.1.

## Verdict calibration

* Worst issue: **the view number is not part of the signed statements** (Appendix B.1: `tcombine((KEY, value),
  ρ)`, same for `LOCK`, `COMMIT`). As written, the key-phase lock check compares an *unauthenticated* claimed
  view, and a Byzantine leader can replay an old key proof under a larger view number (see README). This is
  an algorithm that is wrong as written, but the intended version is recoverable from the paper's own proofs
  ("key proof with view number view3", "a commit proof contains a view number"). The fix is local: sign
  `(KEY, value, view)`. → **R3 → ⚠️**. *Borderline:* the sentence "for every message sent, we implicitly
  bundle along it the view number" could be read as covering partial signatures; under that reading this
  item is only an imprecision and the verdict would be 🛠️ (because of the repairs of 3.3 and 3.8).
* Theorem 3.3 and Theorem 3.8: statements true, proofs with a wrong step / a gap → 🛠️ (dominated by ⚠️).

## Theorem 3.1 (synchronous BA, `SyncBA`)

1. **Static adversary** instead of the paper's dynamic adversary (CSLib `LockStep` has a static Byzantine
   set). For deterministic protocols, correctness against adaptive corruption reduces to the static case
   (corrupt the final set from the start and play honestly until the corruption time). The message bound
   counts only messages of parties honest for the whole run: messages a later-corrupted party sent while
   honest are not counted (not formalized).
2. **Signatures:** ideal unforgeable tokens (`Cslib.Byzantine.LockStep.Auth`). The adversary is rushing and
   may replay any honest token emitted so far. A threshold signature is a *set* of `≥ k` partial signatures
   on one statement (`Valid`). Real threshold signatures are one word; we count messages, not words, and every
   message has a bounded number of components (certificates count as one component each).
3. **View in signed statements:** `Stmt.key b v`, `Stmt.lock b v`, `Stmt.commit b v` include the view (see
   calibration above). Retrieval signatures `Stmt.inp b` carry no view, as in the paper (`tsign(v_in)`).
   The key-phase lock check follows the pseudocode of Appendix B.1 (reject iff the proposed key's view is
   *strictly less* than the lock's view, i.e. accept iff `lock view ≤ key view`, `lockOK`); the overview
   in Section 7 says "their current lock has a lower view number than the proposed key" (strict). Both
   versions are safe (a key and a lock of the same view are for the same value, Lemma B.1).
4. **Fixed synchronous schedule of a view (11 rounds = `11Δ`):** phase 0 complain / request suggestions,
   1 suggest, 2 leader decision (broadcast commit, or `RunRetrieval`), 3 retrieval answers, 4 `ProposeKey`,
   5 `CheckedKey`, 6 `ProposeLock`, 7 `CheckedLock`, 8 `ProposeCommit`, 9 `CheckedCommit`, 10 `SendCommit`. The
   paper's "wait for `k` messages" become fixed rounds. The leader uses *all* valid suggestions received in
   phase 1, not just the first `k`, and picks one with the highest view. If it proposes a suggested key, it
   still waits until phase 4.
5. **Self-delivery:** the leader is also a party. Its own party-role messages (suggestion, partial
   signatures) reach it by self-delivery inside the local transition. A message carries a party-role
   component (for the leader) and a leader-role component (from the leader), so a leader sends one message
   per receiver and round.
6. **Activity:** a party is *active* in a view iff it had no commit at the suggestion phase. Only active
   parties answer `RunRetrieval` and sign `CheckedKey`/`CheckedLock`/`CheckedCommit`. The paper's "if
   commit ≠ ⊥ … wait for the rest of the view" leaves the `RunRetrieval` handler ambiguous; Lemma 10.1 needs
   all honest parties to answer an honest leader's retrieval, which our reading guarantees (see the proof of
   `retrieval_fail`).
7. **Leader without the leader protocol:** a leader that has a commit at the start of its view (`lead =
   false`) only answers complaints, in phase 1. A leader that obtains a commit from a suggestion broadcasts it
   in phase 2 and adopts it as its own commit (line 5 of `ViewLeaderProtocol`).
8. **"Never sent the commit to this leader" and "save the commit suggestion for the next leadership"** are
   not modelled: in `SyncBA` (`n` views, round robin) every party leads exactly once.
9. **Fallback-detection rounds:** round `11n` (`HELP` if no commit), `11n+1` (`PROOF` to `HELP` senders, and
   `FALLBACK` if `≥ t+1` `HELP` signatures were received; both bundled in one message), `11n+2` (`LOCK` if a
   fallback certificate is held). A fallback certificate is either built from the received `HELP`s or
   received in round `11n+1`; `FALLBACK` messages arriving later are ignored. Commits are accepted
   (`SendCommit` or `PROOF`) in every round of stage A, and a commit is the decision.
10. **Value entering the fallback:** commit value, else the highest valid received `LOCK` (including the
    party's own, by self-delivery), else the party's *original input* (the paper's line 30 uses `v_in`,
    which may have become `⊥`; then the honest inputs are not unanimous, so validity is unaffected).
11. **Fallback as a black box** (`Fallback`): unforging, solves authenticated BA for `≤ t` faults, all honest
    parties decide within `Rfb` rounds, and every honest party sends at most `mfb` messages in total *in
    every scenario* (whatever the other parties do, including silent honest parties). This is Theorem B.15
    (Momose–Ren, "even if not all honest parties join"), not formalized. Theorem B.15 states only the total
    `O(n²)`; the per-party `O(n)` bound we assume follows from the fixed communication pattern of
    Momose–Ren argued in its proof (each party multicasts `O(1)` times per recursion level, in groups
    of geometrically decreasing size). Non-participating honest parties are
    silent; their silence is modelled by declaring them silent Byzantine parties in the fallback's scenario
    (`bScen`). This is used only for the complexity bound, and for correctness only when all honest parties
    participate, where the Byzantine set is unchanged (`bScen_byz`).
12. **Decisions after stage A:** a party without commit decides the fallback's output if it participates, and
    otherwise its value at round `11n+3`. An honest party never ends up in the second case: it has a commit
    or a fallback certificate. Commits received during stage B are ignored (the paper does not say).
13. **Complexities with explicit constants** (`roundBound`, `msgBound`): `11(2f+1)` rounds and `22n(2f+1)+3nf`
    messages when `f + k ≤ n` (`k = ⌈(n+t+1)/2⌉`, i.e. `f ≤ ⌊(n−t−1)/2⌋`). Otherwise `11n+3+Rfb` rounds and
    `25n²+n·mfb` messages, with `n ≤ 4f+1` in that case. Theorem 3.1 is stated as `O(f+1)` rounds and
    `O(n(f+1))` messages (paper: `O(f)`, `O(n·f)` with the convention `f ≥ 1`).
14. Theorem 10.5's condition `f < ⌊(n−t−1)/2⌋` vs Theorem 7.2's `f ≤ n − k`: we use `f + k ≤ n` (the weaker,
    correct condition). Lemma B.12 gives `f > n − k`, slightly stronger than the stated `f ≥ n − k`.
15. **Lemma B.1** is proved for key certificates (`key_unique`). Uniqueness of lock/commit certificates per
    view is not needed separately; `commit_unique` (Lemma B.3) covers all views.
16. **Lemma 10.3** (retrieval succeeds after `f+1` distinct honest leaders) is not stated separately. It is
    the counting inside `all_commit`: `#honest + #(honest with ⊥) ≥ (n−f) + f = n > 2t`.

## Theorem 3.3 (asynchronous lower bound)

17. **Model** (`AsyncLowerBound.lean`): message-driven. Parties act at initialization and on each receipt;
    local timers / null steps are not modelled, and self-sends are discarded. The scheduler sees only the
    current metadata (who sent to whom, delivered set, who decided), so it is memoryless and
    payload-oblivious. Faults are static and omission-style: faulty parties run the code but their links
    need not be fair. Restricting the adversary and scheduler weakens the requirement on the protocol, which
    strengthens the lower bound.
18. **Correctness requirement per fair run:** `Solves` asks, for every scheduler, that almost every *fair* run
    is correct. The paper's model admits only schedulers that are fair (almost surely); the two formulations
    are equivalent by a standard truncation argument (not formalized).
19. **Constants:** `|C| = ⌊t/2⌋+1` and `d = ⌈t/2⌉` (the paper: `|C| = d = t/2`, `t` even). The bound is
    `M ≥ (⌊t/2⌋+1)(⌈t/2⌉+1) ≥ t²/4` *almost surely*, both for messages sent before everyone decided
    (`msgsAtDecision`) and for all messages (`totalMsgs`). Hence `E[M] ≥ t²/4`. Needs `1 ≤ t < n`.
20. **Proof differences:** the Markov / union-bound step is replaced by a pointwise argument, because the
    paper's inclusion `⋂ E_pᶜ ⊆ {M ≥ t²/2}` is false (only `M > t²/4`). "Decides within time `T`" becomes
    "decides at initialization", i.e. before receiving any message (`no_init_decision`). The coupling "`p`
    cannot distinguish `Main` from `S_Q`" is made exact: `S_Q` uses the *same* scheduler as `Main`, with
    another faulty set, and `Q` is the set of senders of held messages to `p` (`main_fair_Q`).

## Theorem 3.8 and Theorem 6.2 (dispersers, committees)

21. Def 6.1 with `ε = 1/2` and left degree `≤ d` instead of `= d` (`IsDisperser`); Theorem 3.8 only needs
    the upper bound.
22. **Theorem 6.2 is proved** (`exists_disperser`, union bound over random left-`d`-regular multigraphs), for
    all `N, M` (no `M ≤ N`): degree `≤ 2(⌈log₂ N⌉+1)`, `k = ⌈M/(⌈log₂ N⌉+1)⌉` (`theorem_6_2`). With an
    *integer* `k`, the unpacked form `k ≤ c_k·M/log N` cannot hold for `1 ≤ M < log N / c_k` (a `(k,1/2)`
    disperser with `M ≥ 1` needs `k ≥ 1`). With a real threshold `k` (so that "size ≥ k" means "non-empty")
    it holds. The abstract version used by `theorem_3_8_of_disperser` therefore assumes `log N ≤ M ≤ N`.
23. **Theorem 3.8** with explicit constants (`theorem_3_8`): `(4f̂+1)(⌈log₂ n⌉+1)` committees, `≤ 2(⌈log₂ n⌉+1)`
    per party, `≤ 4f̂` blocked parties for every byzantine set of size `≤ f̂`, for all `n, f̂` including `f̂ = 0`.
    The paper's own derivation (`theorem_3_8_of_disperser`, blocked `< 4c_kc_d f̂`) needs `f̂ ≥ 1` and
    `4c_d f̂ (⌈log₂ n⌉+1) ≤ n` (the `M ≤ N` range of Theorem 6.2); outside it the paper's proof has a gap, and
    for `f̂ = 0` its construction has no committees (every party blocked). Our direct proof covers all cases.

## Not formalized

Theorems 3.2, 3.4, 3.5, 3.6, 5.1, 6.3, 7.2 (partial synchrony), B.15, Lemmas 8.1–8.8 and Section 9–11 QAB
protocols.
