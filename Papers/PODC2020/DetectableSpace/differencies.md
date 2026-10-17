# Differences between the formalization and the paper

Ben-Baruch, Hendler, Rusanovsky. *Upper and Lower Bounds on the Space Complexity of Detectable
Objects.* PODC 2020 (arXiv 2002.11378v1).

## Errors in the paper

1. **Lemma 2 / Algorithm 2 (detectable CAS) is false when `Cas(v, v)` is allowed.**
   *False statement.* `Cas(v, v)` is a legitimate operation that the paper never excludes. Two processes both run `Cas(v₀, v₀)` while
   the value is `v₀`. Both read `C = ⟨v₀, vec⟩`. One hardware CAS succeeds and flips its bit in
   `vec`. The other hardware CAS then fails and returns `false`, although the value was `v₀`
   throughout. These are the first operations of both processes. The history `inv a, inv b, res a true, res b false` has no linearization, even
   without crashes. The proof's claim "the CAS fails only if another process performed a
   successful CAS to C …, hence the value of C after it must be other than old" fails for a
   successful `Cas(old, old)`. Lean: `alg2_not_durLinDet` (`Alg2Counter.lean`).
   Repair: `Cas(v, v)` only reads `C`, persists `val = v` and returns it, and never writes `C`.
   The repaired algorithm is wait-free, durably linearizable and detectable: `alg2fix_durLinDet`,
   `alg2Gen_obstructionFree` / `alg2Gen_boundedSteps` (`Alg2Fix.lean`, `Alg2Defs.lean`). For
   `old ≠ new` Lemma 2 holds as stated.

2. **Lemma 1 / Algorithm 1 (detectable read/write register): the initialization is
   under-specified.** *Under-specified definition.* The paper's ids are 1-based ("for i = 1 to N",
   `p1, …, pN`), so "process 0" is fictitious. But then `A[p][0][·]` (line 2 for the initial
   triple) is not an entry of `A[N][N][2]`. If process 0 is instead a real process (0-based ids),
   the algorithm is incorrect.
   Initially `R = ⟨v_init, 0, 0⟩`, "attributing this value to a write by process 0 that used
   toggle-bit array 0", and `T_0 = 0`. If process 0 is a real process (0-based ids, matching
   `A[N][N][2]` and "process 0"), the key observation of the proof fails for this fictitious write.
   That observation says that q writes with the same toggle index again only after completing a
   write with the other index. Process 0 writes the initial triple again with toggle 0 in its
   first write.

   Counterexample (2 processes, 1 crash, found by our bounded model checker):
   - Process 0 starts `Write(v_init)` and runs lines 1–6. It reads `⟨v_init,0,0⟩`, sets `A[0][0][1] := 0` and `CP := 1`.
   - Process 1 completes `Write(v₁)`.
   - Process 0 executes line 7, writing `⟨v_init,0,0⟩` again.
   - Process 1 completes a `Read`, which returns `v_init`.
   - The system crashes.
   - In `Write.Recover`, process 0 finds `CP = 1`, `R` equal to the triple it read, and `A[0][0][1] = 0`, so it returns `fail`.

   The only `Write(v_init)` therefore failed, yet a `Read` invoked after `Write(v₁)` completed
   returned `v_init`: no durable detectable linearization exists.
   Lean: `alg1_not_durLinDet` (`Alg1Counter.lean`, any `n ≥ 2`, initial toggle `t₀ = false`).
   Repair (our choice, keeping the data layout): initialize `R = ⟨v_init, 0, 1⟩`.
   A fictitious writer with its own column of `A` would also work. Our model checker found no
   violation for either repair (2 processes × 2 operations × 1 crash). We prove the repaired
   algorithm wait-free, durably linearizable and detectable for all `n` and `V`:
   `alg1fix_durLinDet`, `alg1_boundedSteps` (`Alg1Fix.lean`, `Alg1Defs.lean`). The invariant
   behind it ("a process never reuses the toggle of its last visible write") holds initially
   exactly when `t₀ = 1`.

## Gaps in proofs (statements true)

3. **Theorem 2, last step.** The paper argues "since `Op_p` is perturbing w.r.t. `Op_q` after
   `H₂`, executing `Op_q` starting from `E₁` returns `u ≠ v`". This is not justified by
   linearizability: in `E₁` the second `Op_p` is pending, and it may be linearized before `Op_q`.
   The contradiction still follows. In execution `D`, the only `Op_p` is linearized before
   `Op_r`. So `Op_q` after `D₂` returns the response after `H₂`. In `E`, the recovery `ζ` returns
   a non-`fail` value, so the second `Op_p` is linearized before `Op_q`, which then returns the
   response after `H₂ ∘ Op_p`. `D₂` and `E₂` are indistinguishable. Lean: `theorem2`
   (`lin_D`, `lin_E` in `Thm2.lean`).
4. **Theorem 1.**
   - The induction hypothesis is applied to an "algorithm" `A'` whose initial configuration
     `C_ns` is not initial: `p_N` is halted with a pending `Cas(0,1)`, and the value domain is
     shrunk to `V ∖ {0}`. The statement being proved by induction is therefore not the theorem
     itself.
   - "A solo execution of `Cas_q(0,1)` after `C ∘ α` returns true" is not immediate when α is
     empty: `p_N`'s pending operation might be linearized first. One argues from the
     configuration before `p_N`'s invocation, by indistinguishability.
   - We unroll the induction into an explicit construction over levels (`Thm1.lean`), with
     one "level" lemma about linearizations of chains of `Cas(w_i, w_{i+1})`.
5. **Lemma 2, failing hardware CAS.** A CAS at line 35 can fail while the value is `old` again,
   because `C` changed and came back with a different bit vector. Such an operation must be
   linearized retroactively, at the first change of `C` after its read. The paper says this only
   loosely; our proof uses speculative linearization entries that are retracted when needed.
6. **Lemma 1, proof details.**
   - The description of line 20 claims "a write occurred between p's reads iff q's toggle bit is
     1". The "only if" direction is false: q may complete a whole write with the other toggle
     between p's lines 1 and 2. Only the "if" direction is needed.
   - "Linearize W immediately before W′" needs W′ to be the first write to `R` after p's line 1.
   - A crash between the line-20 decision `fail` and the return re-runs the recovery, which may
     then return `ack`. Linearizations therefore have to be retractable; our proof uses
     speculative entries.
   - Both claims of the paper's proof fail only for the fictitious initial write (item 2).
7. **Algorithm 3** (max register without auxiliary state) is given without proof. We prove it
   durably linearizable, detectable and obstruction-free (`alg3_durLinDet`,
   `alg3_obstructionFree`).

## Imprecise definitions / typos

8. **Definition 1 (auxiliary state via NVM).** The definition reads "in-between every two
   successive invocations of Op, a write is made to a non-volatile variable that can be
   accessed by Op". Read literally, it is satisfied by any operation that itself writes to its
   NVM, e.g. `Ann_p.result := …` at the end of `Op`. The conclusion of Theorem 2 would then be
   trivially satisfied. The proof
   (and the abstract: "provided from outside the operation") needs writes made *outside* the
   operation, by the system or the caller. We model these as `RImpl.aux` (applied at
   invocation). "No auxiliary state via NVM" is `∀ p o v, A.aux p o v = v`.
9. **Algorithm 2, line 41.** The proof says that when `CP = 0` "Cas.Recover simply re-invokes
   Op (line 41)", but the code returns `fail`. We follow the code.
10. The initial value `⊥` of `RD_p` (Algorithm 2) is modelled as `false`. This is irrelevant,
   because `RD_p` is read only when `CP = 1`.

## Modelling choices (all explicit in `Model.lean`)

- **System-wide crashes only** (the paper's main model). The remark that all results also hold
  for independent crashes is not formalized. The shared-cache model (Section 6) is not
  formalized either; we use the private-cache model of Section 2.
- **Atomic steps.** A step either applies an arbitrary atomic transformation to the whole shared
  memory or accesses only the process's own private NVM. The lower bounds (Theorems 1, 2) are
  therefore proved for arbitrary primitives, even multi-word ones, which is stronger than the
  paper. The algorithms only use single-variable read/write/CAS steps (checked by inspection of
  `act`).
- **Correctness.** Durable linearizability and detectability are one condition on histories
  (`DLin`): one sequential order containing every operation that returned a value, with that
  value; no operation whose recovery returned `fail`; pending operations optional; real-time
  order respected. In addition, `fail` may be returned only by a recovery function.
- **Auxiliary state via arguments** is excluded by construction: implementation operations are
  exactly `O.Op`.
- **Theorem 2's statement.** "Let Op be a recoverable operation", read universally, is false: a
  register `read` needs no auxiliary state. We state it for the witness `Op_p` of Definition 3:
  `DPWitness O p op → WeakOF → DurLinDet → ∃ v, aux p op v ≠ v` (`theorem2`).
  `theorem2_exists` is the corollary for doubly-perturbing objects.
- **Theorem 1** counts reachable *shared* memory states (`Set.encard`, ≥ `2^(N−1)`). Private NVM
  is not counted, which is stronger than counting all NVM. The paper's corollary "Ω(N)
  additional bits when |V| = O(N)" is the asymptotic reading of our exact bound `N − 1 ≤ b` for
  any injective encoding into `b` bits (`theorem1_bits`). The hypothesis |V| ≥ N is
  `Nonempty (Fin N ↪ V)`.
- **CAS object.** Theorem 1 and Algorithm 2 use the paper's object with `read` and
  `cas old new` (`casRC`).
- **Definition 3** is formalized over process-labelled sequential histories (`DPWitness`). The
  proof of Theorem 2 does not use the requirement that `Op_q` is by a process other than `p`.
- **Objects.**
  - Counter (Lemma 5): over ℕ, with `inc` returning a dummy 0; the bounded counter
    `{0,1,2}` (`bcounter 2`) is saturating.
  - FAA (Lemma 7): over ℤ.
  - Queue (Lemma 8): `deq` returns `none` when the queue is empty.
  - Max register (Lemma 4, Algorithm 3): over ℕ with initial value 0, as in Algorithm 3.
- **Algorithm 3.**
  - `while a ≠ MR do a := MR` is read as a comparison collect (N reads, then the test)
    followed, on failure, by an assignment collect (N reads).
  - The recovery functions re-invoke the operation, as the paper says.
- **Algorithm 2.** Purely local lines (29, 32) are merged with the preceding memory step.
- **Algorithm 1.** Processes are `Fin n` (0-based) and the toggle index is a `Bool`. Every line is
  one step, the loops take `n` steps and line 20 takes two steps (it reads `R`, then `A`).
  Recovery lines 22–27 reuse the states of lines 8–13.

## Not formalized

- "A bounded counter is not perturbable" and "a max register is perturbable": the notion of
  perturbable objects (Jayanti–Tan–Toueg) is not formalized. "Max register is not
  doubly-perturbing" (Lemma 4) is formalized.
- Section 6: the shared-cache model, the NRL transformation, and the remarks on universal
  constructions.
