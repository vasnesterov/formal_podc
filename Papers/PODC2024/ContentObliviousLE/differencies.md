# Differences between the formalization and the paper

Paper: F. Frei, R. Gelles, A. Ghazy, A. Nolin, *Brief Announcement: Content-Oblivious Leader Election
on Rings*, PODC 2024 (DOI 10.1145/3662158.3662785). Proofs from the full version, arXiv
[2405.03646](https://arxiv.org/abs/2405.03646) v1 (the only version). Numbering: the brief
announcement (BA) has Theorems 1 and 3 and Corollary 2; the full version has the same Theorems 1–3,
plus Lemmas 5–25 and Theorem 17. We use the full version's numbering.

## Errors and imprecisions in the paper

1. **Theorem 3 is only true as a worst case over ID assignments (imprecise statement).** BA/full
   Theorem 3: "Any deterministic terminating content-oblivious algorithm for leader election in
   rings with unique IDs sends at least `n⌊log₂(IDmax/n)⌋` messages." Read per instance (every
   execution on a ring whose maximal ID is `IDmax`), it is false. Algorithm 2 run on IDs relabelled
   by the transposition `1 ↔ 16` is still a correct quiescently terminating leader election (for
   every ring size, positive IDs). On the 1-node ring with ID `16` it sends at most
   `1·(2·1+1) = 3` pulses in every execution, but `1·⌊log₂(16/1)⌋ = 4`
   (`LowerBound.theorem_3_per_instance_false`). What the proof (Theorem 17) gives, and what we
   prove (`LowerBound.theorem_3`), is: for every `n ≤ M`, *some* assignment of distinct IDs from
   `{1,…,M}` has an execution with at least `n⌊log₂(M/n)⌋ ≥ n⌊log₂(IDmax/n)⌋` pulses. "Theorem 3
   is an immediate corollary since the number of distinct IDs is bounded by IDmax" is right only
   with this quantifier order.

2. **Lemma 19 / Theorem 17: proof gap, statements true.** The proofs claim that in the lockstep
   execution "both nodes send their first pulse in the same direction … thus both receive and send
   exactly the pattern" and "sending one pulse in each time step". Equal solitude patterns (the
   sequences of *received* pulses) do not imply equal sending behaviour: two IDs may send the same
   pulses in different batches (e.g. two pulses at start-up versus one at start-up and one after the
   first reception). The paper's synchronized scheduler ("one pulse per time step") then has to be made precise. Repair
   (`Cslib.ContentOblivious.reach_sync`): schedule by rounds of *receptions*. In round `k` every
   node consumes one pulse at the port given by the `k`-th symbol of the common prefix. That pulse
   exists because its sender, in its own solitude run, had already sent it after the same `k − 1`
   receptions. This works for any solitude scheduler, not only the FIFO one of Definition 18, and
   for nodes that poll only some ports. The bound counts *received* pulses: `n·s` receptions, hence
   at least `n·s` sent pulses (`Reach.totalRecvd_le_totalSent`).

3. **IDs must be positive (under-specified definition).** The paper takes `ID_v ∈ ℕ` without saying whether `0` is included. With ID `0`
   Algorithm 2 (and Algorithm 1) never terminates: on the 1-node ring the node relays its own pulse
   forever (`Alg2.infinite_execution_id_zero`). The proofs use positivity: Lemma 5's base case
   (`ρcw = 0 < ID`) and "`k` distinct IDs have one ≥ `k`" in Lemma 22. We assume `0 < ID`
   everywhere. For Theorem 3 any ID set works; `theorem_3` uses `{1,…,M}`.

4. **Rings with one and two nodes (modelling assumption, made explicit).** Rings are defined as
   "connected graphs where all nodes have degree 2", which excludes `n = 1, 2` for simple graphs.
   The lower-bound proof needs correctness on the 1-node ring (a self-loop joining the node's two
   ports) and on the 2-node ring (two parallel links), and Theorem 17 explicitly speaks of "rings
   with just a single node". We model rings as `ZMod n` with `Port1` of `v` linked to `Port0` of
   `v + 1` for every `n ≥ 1`. Algorithms 1–3 are proved correct for all `n ≥ 1`, including `1` and
   `2`. The lower bound assumes correctness on rings of sizes 1 and 2 (`SolvesLE A 1`, `SolvesLE A 2`).
   For algorithms that need only be correct on rings with `n ≥ 3` nodes, the bound is not proved
   here.

5. **Wrong cross-references (typos).** Several proofs cite "Lemma 1", "Lemma 2", …. In Lemmas 6–8
   these mean invariants (1)/(2) of Lemma 5. In the proofs of Lemma 25 and Theorem 1 (Appendix A),
   "Lemma 1"–"Lemma 5" mean items 1–5 of Lemma 24. Section 3.2 cites "Algorithms 2–2" for line
   ranges of Algorithm 2. Lemma 11's proof writes `ρcw[b] < ID_v` for `ID_b`.

## Modelling choices (not errors)

* **Model.** Two-port nodes; a link is a pair of directed channels; a channel is a counter (pulses
  are indistinguishable, so FIFO is irrelevant). The configuration holds local states and ghost
  counters `sent`/`recvd` per port. Every node performs its initial action at time 0. A step is
  the delivery of one pulse to a node chosen by the adversary. Deterministic algorithms only
  (`Cslib/Computability/Distributed/ContentOblivious/Model.lean`).
* **Polling.** The pseudo-code polls `recvCW()`/`recvCCW()` in a busy loop and leaves unread pulses
  in the queue (Algorithm 2 reads CCW pulses only once `ρcw ≥ ID`, and reads only CCW pulses while
  waiting for the termination pulse). We model this with a predicate `ready s p`: the scheduler may
  deliver a pulse at port `p` only if the node is ready to read `p`. An unread pulse is "in
  transit". Every polling execution is an execution of our model and vice versa. One loop iteration
  with a reception becomes one atomic step: the reception plus the rest of the iteration (lines
  9–10, 16–17, 20 of Algorithm 2). Iterations without a reception change nothing, except possibly
  the start of the CCW instance. That start can only become enabled through a CW reception, which
  executes it in the same step.
* **Termination / stabilization.** The paper's "eventually" (finite but unbounded delays) is replaced
  by a stronger finite statement. We prove a bound on the number of pulses sent in *every* reachable
  configuration. Each step consumes a pulse, so every execution is finite (`no_infinite_execution`)
  and every execution can be completed (`exists_final`). Correctness is stated for *final*
  configurations (no step possible), i.e. for every maximal execution. This implies the statement
  under any fairness assumption.
* **Quiescent termination** (Section 1.1) is formalized as two invariants. In every reachable
  configuration no pulse is in transit towards a terminated node, so a terminated node never
  receives anything (`Alg2.terminated_spec`). If `ℓ` has terminated, all nodes have terminated and
  the network is quiescent (`Alg2.leader_last`).
* **Message complexity.** We prove `≤ n(2·IDmax + 1)` in every reachable configuration and `=` in
  every final one. The paper states the exact count.
* **Lemma 22 and the analysis of Algorithm 2** are reformulated as *static* lemmas on counter
  configurations (`Alg2.Counters.rccw_lt`, `Alg2.Counters.trigger`) plus two inductive invariants
  (`Inv1` before the termination event, `Inv2` after it). The paper argues along executions. The
  mathematical content (the CW/CCW chains and the pigeonhole on `k` distinct IDs) is the same.
* **Algorithm 3's output** (lines 8–16) is a function of the current state. Only its value in final
  configurations matters. The "consistent orientation" of Theorem 2 is stated as: all ports named
  CW point in the same physical direction (`xor (cwPort v) (flip v)` is constant), and `ℓ`'s
  `Port1` is CW, as in the proof of Proposition 14.
* **Solitude patterns (Definition 18)** are histories of *any* complete solitude execution, not only
  the FIFO one, and we use only that patterns of distinct IDs differ. The lower bound applies to the
  class of `Algo`s, which includes algorithms that poll only some ports (`ready`). This class is
  larger than the paper's.
* **`⌊log₂(k/n)⌋`** is `Nat.log 2 (k / n)` with natural-number division. This is equal for
  `k ≥ n ≥ 1`.

## Not formalized

* Corollary 2 / Corollary 4: simulation of arbitrary asynchronous algorithms, which relies on the
  external compiler of Censor-Hillel et al. Section 1.1's composability discussion is covered only
  through the quiescent-termination properties above.
* Appendix B (anonymous rings): Corollary 26 (from Itai–Rodeh), Lemma 28 (random ID sampling),
  Theorem 27, Proposition 29.
