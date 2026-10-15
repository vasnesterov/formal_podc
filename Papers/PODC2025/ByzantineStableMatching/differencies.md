# Differences between the formalization and the paper

Paper: A. Constantinescu, M. Dufay, D. Ghinea, R. Wattenhofer, *Byzantine Stable Matching*, PODC 2025
(arXiv 2502.05889v2, which includes the appendix).

## Errors in the paper

1. **`k = 1` breaks all "only if" directions (Theorems 2, 3, 4, 6, 7).** The paper never assumes
   `k ≥ 2`. For `k = 1` bSM is solvable without any communication on every network against every
   adversary (each party outputs the only party on the other side): `bSM_solvable_k1`,
   `bSM_solvableAuth_k1`, `theorem2_only_if_false_k1` (`Necessity.lean`). E.g. Theorem 2 claims
   unsolvability for `k = 1`, `tL = tR = 1` (since `1 ≥ 1/3`). All our characterizations assume `k ≥ 2`.
2. **`k = 2` is not covered by the paper's proof of Theorem 2 (necessity).** The proof applies
   Lemma 3 with `d = 3`, which needs `k ≥ d = 3`. The claim is nevertheless true for `k = 2`: our
   generalized Lemma 5 (`lemma5`) covers every `k ≥ 2` (for `k = 2` the cover degenerates to an 8-node
   double cover of `K₄`).
3. **Lemma 13's reduction is invalid.** "Using Corollary 2 and Lemma 3, this means that there exists a
   protocol Π which solves sSM on n := 6 nodes with tR = 3 and tL = 1." Lemma 3 with `d = 3` only gives
   `⌊tR/⌈k/3⌉⌋ = ⌊k/⌈k/3⌉⌋` Byzantine parties on the right, which is `< 3` for `k = 4, 5, 7, 8, …`
   (`lemma3_not_enough_for_lemma13`: `4 / ⌈4/3⌉ = 2`), and it needs `k ≥ 3`; Corollary 2 is about
   unauthenticated bipartite networks and is irrelevant. The statement is still true: we run the split-brain
   argument directly for every `k ≥ 2` with groups (`lemma13_sSM`). (A generalized Lemma 3 tolerating
   "any union of groups that is admissible" would also repair it; our `GroupSim.Solvable.of_groupSim` is
   such a statement.)
4. **Proof of Theorem 7, case `tR = k`, `tL < k/3`, cites the wrong result.** It invokes Theorem 4,
   which requires `tR < k/2` (unauthenticated one-sided). The case is still solvable: the protocol
   `ΠbSM` of Lemma 9 also works on the one-sided network (it only uses `L–R` edges); we use it there.
5. **Typos / misreferences (harmless).** Lemma 5's proof says "c1 must … decide to match party v2"
   (should be `v1`). Corollary 1 says "if `tL < k/2`" — it should be `tR < k/2` (in a one-sided network
   `L` is disconnected and relays through `R`). The proof of Theorem 4 says "Corollary 2" (should be
   Corollary 1) and "one of the conditions `tL < k/3`, `tR < k/2`" (should be `tR < k/3`). The proof of
   Theorem 8 writes `n − 2tL` for `k − 2tL`.

## Modelling choices

- **Model** (CSLib `Cslib/Computability/Distributed/Byzantine/LockStep/`): synchronous lock-step rounds, deterministic history-based protocols,
  static Byzantine adversary (the paper's protocols are claimed secure against adaptive adversaries; we
  only treat static corruption). Byzantine messages are an arbitrary function of round, sender and
  receiver; for deterministic protocols this covers rushing/adaptive message choices. Channels are
  authenticated (the receiver knows the sender). Time is measured in rounds (no `Δ`).
- **Outputs**: a party's output is its *first* decision (`Decides`); "termination" = every honest party
  decides at some round.
- **Parties** are `Fin k ⊕ Fin k`; outputs are `Option (Fin k)` (index on the other side, `none` =
  nobody), so "outputs a party on the opposite side" holds by typing. Preference lists are
  `Equiv.Perm (Fin k)` (`π 0` first); "prefers `v` over `w`" is `π.symm v < π.symm w`.
- **Non-competition** is stated as: distinct honest parties never output the same party (`partner`).
  Symmetry is stated as an `↔` for honest `u ∈ L`, `v ∈ R` (equivalent to the paper's two implications).
- **Authenticated setting**: ideal signatures as abstract tokens (`Cslib.Byzantine.LockStep.Auth`): honest
  parties emit only own or received tokens; Byzantine messages to honest parties contain only Byzantine-signed
  tokens or tokens honest parties already emitted (in this or earlier rounds, to anyone). I.e. a rushing,
  eavesdropping adversary. This is the strongest standard adversary; impossibility results hold against
  it a fortiori, and it is the one preserved by signature relays (relays see honest-to-honest traffic).
- **Adversary structure** `thresholds k tL tR`: at most `tL` Byzantine parties in `L` and `tR` in `R`.
- **Impossibility proofs are done directly for all `k ≥ 2`** (group-level covers) instead of "small `n`
  + Lemma 3"; Lemma 3 itself is also formalized (`Scaling.lean`). Lemma 5 and Lemma 7/13 are proved for
  every network (resp. every network without edges inside `L`), which subsumes the paper's
  "the bipartite network is weaker than the one-sided one" remarks. Lemma 7 does not need the paper's
  preliminary reduction from one-sided to bipartite networks (the cover handles the `R–R` edges).
- **Lemma 5's cover**: the paper gives the 12-node graph only as a picture; we use the voltage assignment
  determined by the three honest sets of Fig. 2 (ii)–(iv) (edges `a–c`, `a–w`, `c–u`, `u–w` cross).

## Results taken as hypotheses (not proved)

- Theorem 10 = [Fitzi–Maurer'98, Thm 2] (`FitziMaurerBB`), Dolev–Strong BB (`DolevStrongBB`),
  Theorems 8/9 (BA/BB among `L` with omissions, `OmissionBA`, `OmissionBB`) — explicitly allowed by the
  task. They are stated for finite nonempty value types. `OmissionBA/BB` are stated on `Party k` with `R`
  isolated (equivalent to the `k`-party statements).

## Sufficiency side: construction details

- **Lemma 1** goes through interactive consistency: `IC_of_BB` runs one BB per party in parallel,
  then `offlineMatch` applies the offline Gale–Shapley step. Byzantine senders need no "default list";
  BB consistency suffices.
- **Lemma 3** (`Scaling.lean`): the paper only asserts that a partition into `d` groups of size
  `≤ ⌈k/d⌉` exists. The obvious `i ↦ i / ⌈k/d⌉` can give fewer than `d` groups (`k = 4, d = 3`), so we
  use `i ↦ i % d`. The lemma itself is correct.
- **Lemmas 6, 8, 10** (`Cslib/Computability/Distributed/Byzantine/LockStep/Relay.lean`): one simulated round costs two real rounds
  (send packets, then forward). Wrappers `(origin, dest, round, payload)` replace the paper's
  `(P → P′, τ, id, m)`: the round number plays the role of the timestamp, and packets make ids
  unnecessary.
  - The transfer theorems need the spec to depend only on honest decisions (`Spec.HonestOnly`). This
    holds for bSM (`bSM_honestOnly`). Byzantine receivers can be lied to by relays, so their simulated
    decisions are meaningless.
  - In the signature relay, a receiver accepts a wrapper forwarded by any designated relay.
  - Corollary 3/4 are proved as `corollary34` for any network between `bipartite` and `fully`.
- **ΠbSM** (`PiBSM.lean`, `Main.lean`): we verify a protocol `Φ` on the network "`L` complete +
  `L–R` edges" with omissions allowed only on `L–L` messages and only if all of `R` is Byzantine. We
  then compile it with the signature relay (relays = `R`) to the bipartite or one-sided network.
  - This factorization is the paper's Lemma 10 + Lemmas 11/12.
  - `R`-parties decide by **strict majority** of the suggestions instead of "the most common" one; the
    result is `none` if there is no strict majority. When some `R`-party is honest, the honest
    suggestion has `≥ k − tL > k/2` votes, so the rules coincide.
  - `R`-parties' lists are sent in round 0 and BA instances start afterwards, all in lock-step. The
    paper's `Δ`-timing (`max(ΔBA(2Δ)+Δ, ΔBB(2Δ))`) becomes the common round bound `T` of the instances.
- **Theorems 8/9** are hypotheses (`OmissionBA`, `OmissionBB`) stated on `Party k` with `R` isolated
  (`lClique`) and Byzantine sets `thresholds k tL k`. On reliable runs they require BA/BB with non-`⊥`
  outputs (`SomeSpec`). This "outputs are not `⊥` without omissions" is implicit in the paper but
  needed: otherwise honest `L`-parties could output nobody while honest `R`-parties follow Byzantine
  suggestions.
- **Theorem 4 sufficiency** uses Corollary 1 (with the corrected condition `tR < k/2`) and Theorem 2,
  as the paper intends.
- **Theorem 6 (ii), case `tR < k/3`**: the paper says "symmetrical". We obtain it from the `tL < k/3`
  case by swapping sides (`Symmetry.lean`).
- **Adaptive adversaries**: not treated (static only). The paper claims its protocols are adaptively
  secure; we only prove static security.
