# The MBroadcast Abstraction — PODC 2023

Mathilde Déprés, Achour Mostéfaoui, Matthieu Perrin, Michel Raynal. *Brief Announcement: The MBroadcast
Abstraction.* PODC 2023. DOI [10.1145/3583668.3594569](https://doi.org/10.1145/3583668.3594569). Formalized
version: the brief announcement (Theorems 1, 2, Property 1). For the converse direction we used the algorithm and
proof of the extended version (DISC 2023, *Send/Receive Patterns Versus Read/Write Patterns in Crash-Prone
Asynchronous Distributed Systems*, Algorithm 2 and App. A), since the brief announcement gives no algorithm for it.

**Verdict: ✅ Correct.** Every result we checked holds: Property 1, Theorem 1 (Algorithm 2 builds MBroadcast from
causal message delivery when t < n/2), Theorem 2 (Algorithm 3 builds a linearizable, terminating MWMR register on
top of MBroadcast, for any number of crashes), and the converse (MBroadcast, even a FIFO and reliable version, from
atomic SWMR registers, for any number of crashes). The one weak spot is the wording of *mutual ordering*. The
abstract says "p delivers first m and then m′". Read literally (p delivers both messages), this property is too
weak, and then Property 1 and Theorem 2 are false. Everything holds under the reading the paper itself uses
elsewhere for "deliver m′ before m". We count this as an imprecise paraphrase, not an error; see the first item
below.

## Mistakes in the paper

* **Mutual ordering: the meaning of "before" (imprecise wording, results true).** The main text says "it is not
  possible that p mdelivers m before m′ and p′ mdelivers m′ before m". The abstract paraphrases it as "it is not
  possible for p to deliver first m and then m′ while p′ delivers first m′ and then m". The pattern MP1 of the full
  version is also drawn with both processes delivering both messages. The results need the stronger reading: "when
  p mdelivers its m, it has not (yet, or ever) mdelivered m′". This is the reading of the paper's own FIFO and
  causal properties ("no process mdelivers m′ before m"), of Property 1 ("p′ cannot return … before it has
  mdelivered m") and of the introduction ("p′ does not ignore p").
  Under the literal reading both claims fail. Take two processes. p₀ writes 1 with Algorithm 3: it mbroadcasts
  `synch` and `write(1, ⟨1, p₀⟩)`, mdelivers both itself, returns, and crashes. Then p₁ reads: its `synch` and its
  write-back of `(0, ⊥)` are mdelivered only by p₁ itself, and the read returns 0. No process mdelivers both
  messages of a pair, so the literal mutual ordering holds vacuously. Validity and no-duplication hold too, and
  Global CS-termination is respected since p₀ is faulty. Yet Property 1 fails, and the history "write(1) completes,
  then read() returns 0" is not linearizable (`property1_false_weak`, `alg3_weak_not_linearizable`). Under the
  strong reading the same trace violates mutual ordering (`weakTrace_not_mutualOrdering`). We formalize the strong
  reading (`DelivBefore`).
* **No other mistakes.** The proofs of the full version for Theorem 2 (timestamps plus cycle-freeness) and for the
  register-based construction (write-then-read) go through as written. The brief announcement gives no proof of
  Theorem 1; ours follows the quorum-intersection argument the paper suggests.
  * Small observations, none of them errors:
    * Algorithm 3 needs only validity and mutual ordering of the layer, not no-duplication
      (`alg3_linearizable_of_validity_mutualOrdering`).
    * The liveness part of Theorem 1 needs only "at most t crashes", not t < n/2.
    * The register-based Algorithm 2 of the full version is FIFO but **not causal**
      (`FromRegisters.not_causalOrdering`; the paper does not claim it is). The paper's remark that the causal
      variant has the same power is still true: we give a variant of our own that is causal (see the table).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* *Specification* (`Spec.lean`). An MBroadcast trace is the real-time list of events `bc p m` and `dl p q m`
  (p mdelivers m from q). Validity, No-duplication, Mutual ordering (strong reading), FIFO and causal ordering are
  properties of finite traces. Messages are identified by (sender, message), each mbroadcast at most once (the
  paper's "all messages are different", `UniqueBc`).
* *Theorem 2* (`Register*.lean`): `CAMP_{n,t}[MB-broadcast]`.
  * Asynchronous crash-prone processes (any linear order of identities), communicating only through MBroadcast.
  * The layer is modelled by its specification: any process may mdeliver any message at any time. Safety is
    proved for every execution whose MBroadcast trace satisfies the safety properties (they are prefix-closed),
    i.e. for every implementation of MBroadcast.
  * Termination assumes weak fairness of local steps and Global CS-termination of the layer.
  * Each code block between two `wait`s is atomic; line 2 may choose any date with ⟨d, i⟩ > clockᵢ.
  * Atomicity = CSLib's linearizability (`IsLinearization`) for `register V v₀`.
  * Any number of crashes.
* *Theorem 1* (`Causal*.lean`): `CAMP_{n,t}[t < n/2]` with causal delivery.
  * Reliable, non-FIFO channels, crash failures.
  * Causal delivery: a message is received only after every message causally preceding it with the same
    destination (one causal order across `causal_broadcast` and `causal_send`).
  * One append-only log of network and MBroadcast events; a causal broadcast is one atomic step and is never lost.
    Safety covers the paper's partial broadcasts, as finite prefixes.
  * Safety holds for any number of actual crashes provided 2t < n. Liveness assumes weak fairness and at most t
    crashes.
* *Converse* (`FromRegisters*.lean`): `CARW_{n,t}[∅]`.
  * n asynchronous processes, n **atomic** SWMR registers `SENT[i]` (the full version needs only regular ones),
    any number of crashes.
  * One step per register access (the local lines 6–7 together with the read). An invocation together with
    line 1 is one step, taken when no `catch_up` runs.
  * Liveness: every correct process takes infinitely many steps.
* No randomness, no timing assumptions.

**Main results in Lean.** Namespaces `Podc.MBroadcast` (+ `.Alg3`, `.Causal`, `.FromRegisters`).

| Paper | Lean | File |
|---|---|---|
| Section 3, definition of MBroadcast (+ FIFO, causal) | `Validity`, `NoDuplication`, `MutualOrdering`, `DelivBefore`, `FifoOrdering`, `CausalOrdering` | `Spec.lean` |
| Property 1 (real-time property, Fig. 1) | `property1` | `Spec.lean` |
| Literal reading of mutual ordering is too weak | `property1_false_weak`, `Alg3.alg3_weak_not_linearizable` | `Spec.lean`, `RegisterExamples.lean` |
| Theorem 1, safety (Validity, No-dup., Mutual ordering; 2t < n) | `Causal.theorem1_safety` | `CausalSafety.lean` |
| Theorem 1, Local termination, Global CS-termination | `Causal.Exec.local_termination`, `Causal.Exec.global_cs_termination` | `CausalLiveness.lean` |
| Theorem 2, atomicity (linearizable MWMR register) | `Alg3.alg3_linearizable` | `RegisterSafety.lean` |
| Theorem 2, termination | `Alg3.alg3_terminates` | `RegisterLiveness.lean` |
| "MBroadcast can be implemented using atomic RW registers" (full version Thm 2: reliable-MBroadcast) | `FromRegisters.safe`, `FromRegisters.fifoOrdering`, `FromRegisters.localTermination`, `FromRegisters.globalCFTermination`, `FromRegisters.globalCSTermination` | `FromRegisters.lean`, `FromRegistersLiveness.lean` |
| Variants "do not change its computing power" (causal-MBroadcast from registers; our algorithm) | `FromRegisters.Causal.safe`, `FromRegisters.Causal.causalOrdering`, `FromRegisters.Causal.fifoOrdering`, `FromRegisters.Causal.globalCFTermination` | `FromRegistersCausalVariant.lean`, `FromRegistersCausalVariantLiveness.lean` |
| Full-version Alg. 2 is not causal (not claimed) | `FromRegisters.not_causalOrdering` | `FromRegistersCausal.lean` |
| "Neither construction needs t < n/2" | no crash bound in the hypotheses of the four theorems above | — |

**Not formalized.**
* The message-complexity remark ("O(n) implementation messages").
* The equivalence of reliable broadcast and causal broadcast with variants of MBroadcast, which is definitional.
* A generic composition theorem ("same computability power" as a statement about simulations). We prove the two
  constructions separately.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity checks:
* `Alg3.alg3_nonvacuous`: a write followed by a read returning the written value, whose MBroadcast trace is safe.
* `Causal.example_reachable` (n = 3, t = 1).
* `FromRegisters.exampleExec_delivers`: a fair execution exists.

Linearizability is CSLib's (`Cslib.SharedMemory.IsLinearization`), through the new staged timestamp criterion
`Cslib.SharedMemory.TSLin` (`Podc/Computability/Distributed/SharedMemory/TimestampLin.lean`, CSLib candidate) on top
of the staged `MWMRReadsFrom`. CSLib candidates (`-- CSLib candidate` comments):
* `TSLin` (TimestampLin.lean);
* the list lemmas `exists_of_getElem?_filterMap` (CausalModel.lean), `exists_forall_of_mono` (CausalLiveness.lean),
  `eq_of_prefix_of_nodup` (FromRegistersTrace.lean), `getElem?_of_prefix` (FromRegistersCausalVariantLiveness.lean).
