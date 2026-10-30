# Differences between the formalization and the paper

Paper: Aguilera, Ben-David, Guerraoui, Marathe, Zablotchi, *The Impact of RDMA on Agreement*, PODC 2019,
arXiv 1905.12143v2 (extended version, Feb 2021). Formalized: Theorem 6.1, Algorithm 7 with Theorems D.1, D.2 and
Lemma D.4, Lemma 4.1 with Algorithm 2. Not formalized: Theorems 4.2–4.9 and Lemmas 4.3–4.8 (Robust Backup,
Cheap Quorum, Preferential Paxos, Fast & Robust), Theorem 5.1's termination and 2-deciding parts (D.6–D.8),
Aligned Paxos (§5.2).

## Theorem 6.1 (`LowerBound/`)

Verdict for this statement: true as formalized; the proof needed repair (🛠️).

**Definitions.**
- *2-deciding.* §3 defines "k-deciding: in common-case executions, some process decides in k delays" (common case:
  synchronous, no failures; a message takes one delay, a memory operation two). This is informal. We formalize the
  common-case execution as the failure-free synchronous run `syncRun x ∅`. In it, an operation invoked at time `t`
  takes effect at `t + 1` and its response arrives at `t + 2`. Simultaneous operations take effect **reads first**.
  `TwoDecidingOn x` means some process has decided by time 2. We prove that no process has decided by time 2, for
  every input vector. This refutes every reading of the form "in every common-case execution some process decides in
  2 delays".
- *Existential reading.* The paper's proof begins "there is some execution E of A in which some process p decides v
  with 2 delays". Read this way, with simultaneous operations allowed to take effect write-first, the theorem is
  **false** (not formalized). Take n = 2. At time 0, p2 writes its input to a register X and p1 reads X. If p1 reads
  a value w, it decides w at time 2. Then both run any consensus algorithm B for this model (e.g. Disk Paxos): p2
  with its input, p1 with w if it read w and with its own input otherwise. If p1 decided w, all inputs to B are w, so
  B decides w by validity. Termination comes from B. So the theorem is true only for the universal / read-first
  notion. *Rule:* the definition is ambiguous; we formalize the reading under which the claim holds (R3/R4,
  borderline). We record this rather than call it a false claim, because the paper never fixes how simultaneous
  operations are ordered.
- *Hypotheses weaker than the paper's (so the theorem is stronger):*
  - termination is assumed only in synchronous runs with at most one process crashed from the start
    (`SyncTermination 1`), which partially synchronous termination implies (GST = 0);
  - agreement and validity are assumed only in executions where responses are delivered in linearization order
    (FIFO);
  - processes may have any number of pending operations, even on the same register (the paper allows one per
    object/memory).
- *Added hypotheses:* `2 ≤ |P|` and `|V| ≥ 2`. With one process, it decides its input at time 0 (R2, degenerate).
- *Memory regions:* with static permissions every (process, register) pair has a fixed access right, modelled by
  `canRead`/`canWrite`; a region parameter on operations would add nothing.
- *Process model:* deterministic automata. A step receives the oldest `k ≥ 0` undelivered responses and invokes a
  finite list of operations, so local computation is instantaneous (§3). Registers are atomic, the memory never
  fails, and there is one memory (several memories that never fail are equivalent to one).
- *Non-vacuity:* `NonVacuity.hypotheses_satisfiable`. A 2-process algorithm (write own register, read the other's;
  P1 publishes its decision, which P0 adopts when it is not fast) satisfies `Agreement`, `Validity` and
  `SyncTermination 1`.

**Proof gaps (repaired):**
1. The proof starts from an arbitrary execution E in which p decides in 2 delays. It claims that E′ (p's reads
   return by t₀, the others start after t₀) is indistinguishable to p from E. This fails when p's reads in E
   returned values written by others in E. Repair: take E to be the read-first synchronous run. There, p's reads
   return the initial memory, and write responses are fixed by the static permissions. So p's state up to time 2 is
   a function of its input alone (`syncRun_view`). This is exactly where static permissions are used.
2. "Since A … terminates if there is no contention, p′ must eventually decide": solo termination does not follow
   from the model when n ≥ 3 and only one crash is tolerated, because p′ running alone looks like n − 1 crashes.
   Repair: run all processes except p. To them p looks crashed: its reads change nothing and its writes are pending.
   That is one crash.
3. Why p′ decides v′ ≠ v is not explained: validity alone would allow p's input. Repair: give every process other
   than p the input v′. They behave exactly as in the run where p is crashed from the start and all inputs are v′,
   so by validity they decide v′.
4. The remarks "R and W must be disjoint" and "p must issue all of its reads and writes without waiting" are not
   needed.

## Algorithm 7, Theorems D.1, D.2, Lemma D.4 (`PMP/`)

Verdict for this statement: Theorem D.2 is false for Algorithm 7 as written, with a Lean counterexample. With two
local fixes whose intent is recoverable, the algorithm is safe (proved). Classified ⚠️ (R3/R4); see "Borderline"
below.

**Model choices** (module docstring of `PMP/Model.lean`):
- *Asynchrony:* interleaving semantics with one thread per (process, memory). Every memory operation
  (getPermission, write, read-all-slots) is invoked, takes effect atomically later, and is answered later still. A
  process has at most one outstanding operation per memory.
- *Ended attempts:* when an attempt aborts or decides, its threads are killed, but operations already invoked
  still take effect ("zombie" operations). The paper does not consider these; the repaired algorithm is safe with
  them.
- *Crashes and Ω:* crashes do not matter for safety. Ω is arbitrary: any process whose loop is idle may start a new
  attempt, including after it decided (the loop is `repeat forever`).
- *Ballots:* globally unique, and increasing for each process. The paper only says "a higher value than any proposal
  number seen before"; uniqueness is the standard Paxos convention (R4). p1's first attempt, which skips phase 1,
  uses the smallest ballot (see bug 2).
- *Lines 24–26* are ambiguous: "non-null value", and "highest propNr" of which field? We use the semantics that the
  proof of D.2 and Algorithm 12 (p. 17) fix (R3). Abort if *any* slot has minProp > propNr; otherwise adopt the
  value with the highest accProp among the slots that hold a value. Under the other readings, the line-21
  counterexample still works (no slot holds a value), or the leader adopts its own fresh slot `(propNr, ⊥, ⊥)` and
  decides ⊥.
- *Atomicity:* local code is merged with the neighbouring memory step. The behaviours this removes are equivalent
  for safety.
- *Scope:* only safety is formalized: D.1, D.2, D.4, for any number of processes and memories and any schedule.

**Bugs:**
1. **Line 21 erases the process's own accepted value** (`theorem_D2_false`; n = 2, m = 1, no crashes, unique
   ballots, p1's first ballot minimal). Line 21 writes `(propNr, ⊥, ⊥)`, and the loop repeats forever after
   deciding. The run:
   - p2 decides `true` at ballot 2;
   - p2 starts ballot 4, gets the permission, and its line-21 write erases its slot;
   - p1 starts ballot 5, gets the permission, and reads no value and no larger minProp;
   - p1 writes its own input and decides `false`.

   Fix (formalized as `Variant.repaired`): line 21 writes `(propNr, a, w)`, where `(a, w)` is the last phase-2 pair
   the process issued, as in Disk Paxos. The prose supports this ("write a new proposal number in its slot"), and so
   does Algorithm 10, which writes `{propNr, -, -}`.

   *Dependence on post-decision attempts.* The run needs the decided p2 to start a new attempt. The pseudocode
   allows this (`decide` is inside `repeat forever`, and Ω is arbitrary). Elsewhere the paper treats a decision as
   ending the instance: §2 says "irrevocable decision", the D.8 proof says "p1 terminates, deciding", and §5.1 says
   "the leader terminates one instance". If `decide` ends the loop, the run is impossible. Then only the decider
   writes its slot, so the slot keeps `(b, b, v)` on its majority. A missing `return` after line 39 is therefore an
   equally local fix (not formalized).
   *Zombie caveat for that fix:* in our zombie model, a pending line-21 write of an earlier attempt could still
   land later, but only on a memory outside the decided majority, because there is one outstanding operation per
   (process, memory).
2. **p1's first ballot must be the smallest, even after the repair** (`first_ballot_not_minimal_false`; n = 2,
   m = 3). The run:
   - q decides c at ballot 5 on memories 2 and 3;
   - p1's first attempt uses ballot 100, which "higher than any seen" allows because p1 has seen nothing. It skips
     phase 1, and its line-35 write `(100, 100, a)` succeeds on memory 1, where p1 still holds the initial
     permission;
   - q then runs ballot 200 on memories 1 and 2, adopts a (accProp 100), and decides a.

   The Lean run again lets the decided q start a new attempt (ballot 200). If deciding ends the loop, a third
   process r can run ballot 200 instead of q, with the same effect. So this issue does not depend on the halting
   question for n ≥ 3 (argued, not formalized). For n = 2 under the literal line 21, p1's own retry would erase
   `(100, 100, a)`. The standard convention that only the lowest ballot may skip phase 1 excludes this (R4).

**Proof gaps (repaired):**
- In both cases, the proof of D.2 assumes that p's slot on m still holds `(b_p, v_p)` when q reads it ("q must have
  seen v_p"). Line 21 breaks exactly this. With the repair it holds, because a slot's accProp only grows.
- The induction "b_q is the smallest proposal number larger than b_p for which some process enters phase 2 with
  CurrentVal ≠ v_p" has two gaps:
  - It needs an unstated invariant: a slot with accProp c holds the value with which ballot c entered phase 2.
  - Its case 2 assumes the minimal attempt performed phase 1. That attempt can be p1's first attempt, which is what
    bug 2 exploits.

  We use Lamport's `SafeAt` invariant together with a permission-based "promise". While a thread holds m's
  permission after reading m, no slot of m has a larger minProp than it read.
- Lemma D.3 ("the values a leader accesses cannot change between when it reads them and when it writes them") is
  loose. What is true and needed: if p's write on m succeeds after p read m, nobody else wrote m in between.
- D.4: with unique ballots, "same proposal number" means same leader and same attempt, as the paper assumes.
- D.1: the paper's argument is fine. Formally, every phase-2 value is an input, since only slots that hold a value
  are adopted.

**Borderline (R3/R4, recorded per R6).** D.2 is a numbered theorem about the paper's specific algorithm, and it is
false as written. We classify it ⚠️, not ❌, for three reasons:
- The intended line 21 is recoverable from the paper: the prose, Algorithm 10, and the proof of D.2, which reasons
  as if accepted values persist.
- The fix is one line.
- Minimality of the phase-1-skipping ballot is the standard Paxos convention.

A stricter reading would count the explicit `(propNr, ⊥, ⊥)` as a protocol design rather than a slip, and would
give ❌. The independent review endorses ⚠️, for three reasons:
- *R3, recoverable and local.* Two one-line fixes each restore safety. One keeps the accepted pair at line 21
  (proved). The other ends the loop at `decide`, which matches the paper's "terminates" wording. Neither changes the
  protocol's design or its two-delay fast path: p1's first attempt never executes line 21.
- *R3, the proof uses the intended version.* The D.2 proof reasons with the intended behaviour, namely that the
  decider's phase-2 entries persist ("q must have seen p's value"). It never uses the erasing line 21. So the R3
  exclusion "the proof reasons with the wrong version" does not apply. The proof is incomplete (the gaps above),
  but not built on the faulty line.
- *R5, the ceiling if not excused.* Algorithm 7 is the paper's crash-failure algorithm, which the abstract presents
  as a primary contribution. But the headline, Theorem 5.1, is existential ("there exists a 2-deciding
  algorithm"), and a repaired protocol exists (safety proved here). So even the strict reading gives ❌, not 🚨.

Bug 2 (the first ballot must be minimal) is the more delicate R4 call. The paper never fixes p1's first ballot, and
D.2 case 2 silently needs it. We excuse it because it is the universal convention for a pre-established leader that
skips phase 1 (Fast Paxos and Multi-Paxos use ballot 0 for it). A competent reader would assume it.

## Lemma 4.1 and Algorithm 2 (`RB/`)

Verdict for this statement: true; the pseudocode has typos and Observation 1 is false as stated (⚠️).

**Model choices** (`RB/Model.lean`):
- *Registers:* SWMR **regular** registers, as in the lemma. A pending read of a correct process may return the value
  current at invocation, or the value of any write pending during the read (candidate-set encoding). Writes of
  correct processes have an invocation and a response.
- *Byzantine processes:* they write anything, any time, any number of times, but only to their own registers
  (atomically, which loses nothing: the adversary controls those read results anyway).
- *Signatures:* abstract, unforgeable and transferable, with nested terms (copies, L1 proofs, L2 proofs). Byzantine
  processes may use any signature a correct process ever produced. This gives the adversary slightly more power
  than in reality.
- *Steps:* a correct thread's step is a response, then local computation, then the next invocation. Operations are
  invoked as early as possible; this only enlarges candidate sets (argued, not proved as a simulation).
- *Fairness:* every delivery thread of a correct process runs infinitely often, and every write of a correct
  process completes.
- *Hypotheses:* properties (2) and (3) need only |F| ≤ f; (4) needs fairness; (1) needs fairness and n ≥ 2f + 1.
  `[Inhabited P]`.
- *Non-vacuity:* `lemma_4_1_nonvacuous` gives a fair execution in which a correct broadcast is delivered by all
  correct processes.

**Pseudocode fixes (R3, evident intent):**
1. *Off by one:* `try_deliver` uses `k = last[q]` with `last[q] = 0` initially, while the first key is 1
   (Definition 1). Taken literally, nothing is ever delivered. We use `last[q] + 1`.
2. *Wrong signer:* lines 38 and 47 check `sValid(p, val)`, the reader's own signature. Intended: val carries the
   sender q's signature on (k, m), and in line 47 it is endorsed by the slot owner i.
3. *Scoping:* `state` must be per sender (`state[q]`). Line 30 delivers `proof.msg`, but `proof` is local to
   `checkL2proof`; the delivered value `val` is meant.
4. *Threshold:* we use f + 1 (as in the prose) instead of "majority". Both work when n ≥ 2f + 1.
5. *Proof validity:* `check` / `checkL1Proof` are unspecified. Safety needs *distinct* endorsers in an L1 proof and
   *distinct* authors in an L2 proof, all for one (k, m) (prose: "each such valid proof has signed copies of only
   one value").
6. *Doubly signed echo:* line 38 must also accept the sender's own echo `sign_p(sign_p(k, m))`, because
   `Value[p,k,p]` is both the broadcast slot (line 12) and p's echo slot (line 40).

**Observation 1 is false as stated** ("no slot that belongs to a correct p is written more than once"):
- `Value[p,k,p]` is written at line 12 and again at line 40. With regular registers, the line-40 write may even
  complete before the line-12 write.
- `L2Proof[p,k,q]` is written at line 64 and again at line 18, possibly with a different proof.

Nothing breaks. The proof needs, and we prove, weaker facts:
- every value a correct process writes to its Value slot endorses one and the same signed pair;
- a non-⊥ correct slot stays non-⊥;
- every write to a correct L2Proof slot is a valid L2 proof for that key;
- L1Proof slots are written once.

*Rule:* R3 (evident intent: "a correct slot is never overwritten with content supporting a different message";
the overwrites are harmless). This is a borderline ⚠️: a false numbered observation would otherwise be ❌.

**Proof gaps (repaired):**
- *Property 2:* "r wrote (k,m) before r′ wrote (k,m′), so r′ later saw both" needs "wrote" to mean the write
  *completed* and "later" to mean the reads were *invoked* afterwards. With regular registers this is the only
  valid form. We formalize it with ghost completion and scan-start times (`InvD`, `l1_agree`).
- *Properties 2 and 3* use unforgeability for nested terms, and that a valid L2 proof contains an L1 proof by a
  correct author. Both need the distinctness in fix 5.
- *Property 1* needs the broadcast write to complete (fairness of operations).
- *Observation 2* says `try_deliver` has no loops, but it has the finite `for i ∈ Π` loops; liveness needs explicit
  fairness.
