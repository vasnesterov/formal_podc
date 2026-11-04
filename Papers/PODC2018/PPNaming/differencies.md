# Differences between the formalization and the paper

Source: full version HAL hal-01790517v3 (the PODC 2018 brief announcement has no proofs).

## Model and definitions

1. **Executions and fairness** are CSLib's (`Cslib.PopulationProtocol`): labelled configurations
   `A → Q`, one ordered pair of distinct agents per step. Weak fairness means every *unordered* pair interacts
   infinitely often, in either role. This is the paper's "every pair of agents interacts infinitely often" and is
   weaker than the ordered reading, so the positive results are stronger. Global fairness is the paper's definition
   on labelled configurations.
2. **Symmetric rules** are `δ q p = (δ p q).swap` (`IsSymmetric`; for leader protocols `LeaderProtocol.Symmetric`:
   symmetric mobile–mobile rules, and leader rules independent of who initiates). This is the paper's definition.
3. **Leader.** A leader protocol has three rule tables (mobile–mobile, leader–mobile, mobile–leader) and is
   encoded as a CSLib protocol on `L ⊕ Q` with agents `Option A`. The leader–leader entry is junk and never
   used. The leader's state set `L` is arbitrary, possibly infinite ("as powerful as needed"); it is finite only
   where global fairness is involved (finitely many configurations).
4. **Naming.** A name is an arbitrary function `name : Q → N` of the mobile state. Naming means the names of the
   mobile agents are eventually constant and pairwise distinct (the paper: "a variable … that eventually does not
   change and such that no two agents have the same name"). For `P`-state protocols we *prove* that `name` is
   injective (Lemma 2), so the paper's "same state ⇔ same name" holds there.
5. **"Solves naming"** quantifies over all weakly (globally) fair executions from the allowed initial
   configurations (`SolvesWeak`, `SolvesGlobal`). The paper's "terminal configuration" is not part of the
   definition. Its role is played by the derived fact `exists_stablyGood_of_weaklyFair` /
   `exists_stablyGood_of_globallyFair`: a closed named configuration is reachable from every reachable
   configuration.
6. **Population sizes.** "For any `n ≤ P`" is quantified over finite agent types. The impossibilities use only
   the sizes they need: Prop. 1 any even `n ≥ 2`; Lemma 2, Props. 3 and 4 `n = P`; Prop. 6 and Theorem 11
   `n ∈ {P - 1, P}`. They are therefore stronger than the paper's statements. `thm11_paper` also gives the
   paper's form ("for all `n ≤ P`").
7. **States.** `P` is `Fintype.card Q`. Prop. 12 uses `Fin P`, Prop. 13 `Fin (P + 1)` with special state
   `Fin.last P`, Prop. 14 `Fin (k + 1)` (`P = k + 1`) with names `0..k−1` plus the initial state `k`, where the
   paper uses names `1..P` and initial state `P`. These are relabellings.

## Statements

8. **Prop. 1** is proved for every population of even size `n ≥ 2` (the paper's proof), any state set (even
   infinite), uniform initialization (hence also arbitrary initialization). The perfect matchings are built
   explicitly (`exists_matching`). The phases need not cover all pairs at once: one matching per pair suffices.
9. **Lemma 2** is proved without the symmetry hypothesis (`lemma2_core`, `lemma2_leader_core`). The paper assumes a
   symmetric protocol, but symmetry is not used.
10. **Props. 3 and 4** need `P ≥ 2` (degenerate case R2: for `P = 1` naming is trivial). Prop. 4 is proved for
    arbitrary (`initArb`) and for uniformly initialized mobile agents with an arbitrary leader
    (`initArbLeaderUniform`), under weak and global fairness. The core `prop4_core` only needs, for some mobile
    configuration with homonyms, all leader states to be allowed.
11. **Lemma 5** is stated in the paper for every weakly fair execution of size `n < P` ("eventually no agent in
    a state `m` with `(m,m) →* (m,m)`"). We prove the form used by Prop. 6: a stably named configuration of size
    `P − 1` reachable from an initial configuration has no agent in a `hom`-periodic state (`lemma5`). The
    proof is the paper's cloning argument (a fresh agent in `m` replaces the `m`-agent); the execution is built
    with `exists_weaklyFair_of_phases`.
12. **Prop. 6** is proved as stated (existence, `hom m = m`, attraction of every homonym pair, uniqueness of
    the periodic state), assuming correctness for the sizes `P − 1` and `P` and `P ≥ 2`.
13. **Theorem 11** is proved as stated (and stronger: only the sizes `P − 1`, `P` are used, the leader may have
    infinitely many states), for `P ≥ 2` (R2: false for `P = 1`). Rule R1: the theorem is true; the gap is in
    the proof (🛠️, see below).
14. **Prop. 12** is proved for the leaderless case under weak (unordered) and global fairness, arbitrary
    initialization, all `n ≤ P`. The "with leader" cells of Table 1 (an idle leader) are not formalized. The
    proof uses the single potential `∑_{holes h} ∑_x ((h − state x) mod P)` instead of the paper's
    lexicographic (holes, hole distance); the paper's argument is also correct.
15. **Prop. 13** is proved as stated (global fairness, arbitrary initialization, `3 ≤ n ≤ P`). The step "pick a
    unique name `s` with `s + 1 mod P` absent" is proved by counting.
16. **Table 1 / §1 (⚠️, rule R3).** The summary "no leader, global fairness, symmetric: possible with `P + 1`
    states" and "with symmetric rules the norm is `P + 1` states" hold only for `n ≥ 3`. For `n = 2` no
    symmetric leaderless protocol names under any fairness (`not_solvesGlobal_of_card_two`,
    `not_solvesWeak_of_card_two`). `n = 2` is not degenerate (R2), and the model demands correctness for all
    `n ≤ P`. The intended version is recoverable from Prop. 13 itself (it says `n > 2`) and the fix is local,
    so ⚠️ rather than ❌. *Borderline:* one may read the table as merely pointing to Prop. 13 with its
    hypothesis. We count it as a minor statement issue because §1 restates it as a claim without the restriction.
    *Review:* ⚠️ confirmed. Taken literally in the paper's model (one protocol for all `n ≤ P`), the cell's
    true entry is "impossible" for every `P ≥ 2`, and the abstract claims a protocol for every combination, so
    this is a claim (R1), not mere navigation. `n = 2` is the basic symmetry-breaking instance, not a trivial one
    (R2 does not apply). R3 applies: the paper's numbered Prop. 13 carries `n > 2` and its proof uses it, so
    the fix (add `n ≥ 3` to the cell and to §1) is local and recoverable. Not ❌: no numbered statement is false.
17. **Prop. 14** is proved as stated (weak and global fairness, all `n ≤ P`).
18. **Not formalized:** Corollary 7, Lemmas 8–10 (bypassed by the repaired proof of Theorem 11), Theorem 15
    (cited from [6]), Props. 16 and 17 (they depend on the internals of the counting protocol `Count_P` of
    [6], which the paper does not give).

## Proofs

19. **Lemma 2, Prop. 4 (proof remark).** The paper's proofs use "after stabilization, a name change is
    impossible" (Ce is "terminal"). Under weak fairness this is not immediate: a stabilized *execution* does not
    make its configuration closed. We derive the needed form (a closed named configuration is reachable) from
    correctness via a weakly fair adversary (`exists_stablyGood_of_weaklyFair`). Prop. 4's proof is replaced by
    a mirror argument: in `ofLM λ* c₀` (`c₀` with homonyms, `λ*` the leader state of a closed named
    configuration) every leader interaction behaves as in the closed configuration, so homonyms persist
    (`prop4_core`).
20. **Theorem 11 (🛠️).** The paper builds `e` by alternating segments transferred between `C⁻ˢ` and `C`
    (Lemmas 9, 10). It asserts weak fairness of `e` only through "every agent in `e` has the opportunity to
    interact repeatedly", and it ends `e` in a stable `C*` through a segment `C_k e_k C*` in which the
    `s`-agent should be idle, which the construction does not provide (all constructed even segments end with
    the `s`-agent being reduced). The repair (`Thm11.lean`) uses reduced steps `rstep`, the relation `Rel`
    between a plus and a minus world (multisets `plus + {m} = minus + {s}`), the mirror lemma `mirror`,
    reduced reachability of naming `exists_rreach_injective`, and `drive`. The adversary always lets the minus
    world drive, and the actual execution performs the pair required by weak fairness at the start of each of
    its minus phases. The execution is weakly fair, starts from an initial configuration (the two initial
    worlds are a bijection and the same with the `s`-agent set to `m`; no hidden agent is needed), and has two
    `m`-agents infinitely often.
21. **Prop. 6.** The paper's proof uses "at least `P − 1` states appear infinitely often in an execution with
    `n = P − 1`". We use the stably named configuration of size `P − 1` (`P − 1` distinct non-periodic states)
    and a counting argument; same idea.
