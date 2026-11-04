# Differences between the formalization and the paper

Paper: W. Golab, *Brief Announcement: The Recoverable Consensus Hierarchy*, PODC 2019; formalized from the full
version *Recoverable Consensus in Shared Memory*, arXiv:1804.10597v2 (May 2018). Numbering follows the full version.

## Model (all results)

- CSLib's crash-recovery shared-memory model (`Cslib.SharedMemory.Recoverable`): deterministic processes, one
  atomic operation on one object per step (local computation folded into continuations), objects with
  deterministic sequential specifications, initial object values chosen by the algorithm. A crash resets the local
  state of the process to its initial state (which contains its input); shared objects are unaffected. A step in an
  output state is a no-op; a process that has output and later crashes runs again. The paper's model (Section 2) is
  the same, described informally.
- **Binary consensus.** CSLib's model fixes inputs and outputs to `Bool`. The impossibility results are thereby
  slightly stronger than the paper's (binary consensus is a special case), the algorithms slightly weaker
  (Figures 1 and 2 are proved for binary inputs; the algorithms never inspect values except for `⊥`-tests, so the
  proofs are value-agnostic, but this is not formalized).
- **Recoverable wait-freedom** is CSLib's progress condition: in every infinite execution whose prefixes are
  admissible, a process that takes infinitely many steps and does not crash after time `N` is in an output state
  at some time `≥ N`. This is the paper's "each time a process executes its algorithm from the beginning, it
  either returns after finitely many of its own steps or crashes" (no uniform bound).
- **Agreement.** The paper's agreement is "distinct processes never output different decisions". Impossibility
  results are proved for exactly this (`SolvesP`), which is weaker than CSLib's `Solves` (all outputs of an
  execution agree, also outputs of one process in different incarnations); the algorithms are proved for the
  stronger `Solves` (Figure 2) resp. the analogous `SolvesS` (Figure 1).
- **`f` failures** = at most `f` crash events in total (all processes), as in footnote 3 (`AtMost f`).
- **Conventional consensus algorithms `C`, `C[k]` (Figures 1, 2)** are modelled as atomic (sticky) consensus
  objects `consObj Bool` (one `propose` step returning the decision of the first proposal). A conventional
  wait-free algorithm accessed at most once per process, where a process crashing in the middle never comes back
  to it, behaves like an atomic object with a halting failure; we additionally prove that each process accesses
  each `C`/`C[k]` at most once (Lemmas 8 and 12), so the abstraction is used only within its contract. The
  composition theorem "replace the atomic object by an implementation" is not formalized.
- **Simultaneous failures** (Section 3): own event type `SEv` (`step p` | `crashAll`, resetting all local states)
  on CSLib configurations; `SolvesS`: agreement of all outputs, validity, recoverable wait-freedom, arbitrarily many
  crashes.

## Theorem 3 / Corollary 4 (rTAS lower bound)

- Statement: `theorem3` is the paper's statement for every `f` (the paper assumes `f > 0`); registers are
  generalized to arbitrary read/write-like objects (`ObjSpec.RWLike`: every operation is read-only or a blind
  overwrite), the rTAS objects are indexed by a finite type of size `≤ f`. `theorem3_gen`: any `n`, any two
  participating processes, any admissible set containing the restricted executions.
- **Proof gap (🛠️, deciding the verdict): Assumption 1 and Case C.** Assumption 1 makes `p₁` crash right after
  its first *access* to each TAS object. For *readable* TAS (the theorem's objects) a read is an access (the paper
  itself uses "access" for reads: Case D is "both processes are poised to access the same base object and at least
  one process is poised to read"), and Case C
  ("at least one process, say `p₁`, has accessed `T` already ... Then `T` holds the value 1") is false when that
  access was a read: in the critical state both processes may be poised to `tas` an object that still holds `0`
  and that `p₁` has only read; then `p₁` does not crash after its `tas` (not its first access), the two `tas`
  operations do not commute, and neither Case B nor Case C applies. This is not a technicality of the proof
  presentation: with the literal Assumption 1, the restricted-model statement the proof establishes is false —
  `Assumption1Gap.lean` gives a 2-process algorithm with one rTAS object and two registers that is correct
  (agreement, validity, recoverable wait-freedom) on all executions obeying the literal Assumption 1
  (`literal_assumption1_rcorrect`), although it is incorrect in the real model (`A₀_not_solvesP`, from Theorem 3).
  **Repair**: crash `p₁` right after its first `tas` operation on each rTAS object (reads do not count). Then an
  rTAS object on which `p₁` has applied `tas` holds `1` (`Theorem3.tasInv`), Case B applies whenever the object
  holds `0`, Case C whenever it holds `1`, and the crash budget is still `≤` the number of rTAS objects. Statement
  true; verdict rule R1 (a wrong step in the proof of a true theorem) ⇒ 🛠️.
- Gap (routine): the proof does not show that an initial bivalent state exists (it starts "in the initial system
  state"); `biv_init` (inputs `p₁ ↦ 0`, `p₂ ↦ 1`; `p₁` alone decides `0`, `p₂` alone `1` by validity).
- Gap (routine): "the construction must succeed eventually by the wait-freedom of `A`": made precise in
  `exists_crit` (an infinite bivalent schedule has finitely many crashes, so some process steps forever without
  crashing and must output, contradicting bivalence via agreement).
- Gap (routine): the valency argument needs agreement of all outputs (also the same process's), while the paper's
  agreement is only between distinct processes; in the restricted model it follows because `p₂` never crashes and
  must output (`agree'`).
- Case D-1 says "say `p₁`" for the process that reads or crashes; the two processes are not symmetric (only `p₁`
  crashes). When `p₂` reads, `p₁` cannot distinguish `s·p₂·p₁` from `s·p₁` and runs solo *with its forced crashes*;
  handled by `contra_a`/`absorb_a_of_absorb`. When `p₁`'s move is a crash, `p₂` cannot distinguish (handled).
- Case B/D "indistinguishable to `p₁`" must include the bookkeeping of Assumption 1 (which objects `p₁` already
  triggered, whether a crash is pending), since it determines `p₁`'s future crashes (`AgA`).
- Corollary 4: `corollary4` (paper's spec), `corollary4'` (CSLib's `Solves`).

## Theorem 6 / Corollary 7 (generic constructions)

- The paper's "`n`-consensus objects" are modelled as atomic sticky consensus objects over an arbitrary value
  type `V` (`consObj V`), with no bound on the number of accesses (the paper's proof uses exactly this: "any access
  to an `n`-process consensus base object is a single atomic step", "C has already settled ... both Decide return
  `v`"). With port-bounded objects that answer differently after `n` accesses, Case C would need more care; not
  formalized.
- Definition 5 (genericity) is formalized as `Generic`: in every admissible execution of the form
  `α · (p accesses C) · β · (crash of p) · γ · (step of p)`, the last step is not an access to `C`. Theorem 6 only
  needs it on the executions with at most `f` crashes and two participants (`AtMostTwo f`), a weaker hypothesis than
  the paper's "in all executions".
- `theorem6`: for every `f` (paper: `f > 0`) and `n ≥ 2`; correctness required only on executions with at most `f`
  crashes in which only `p₁, p₂` take steps ("even if ... at most two processes participate").
- The proof is the paper's; Case C is correct here (consensus objects have no read, so "accessed ⇒ decided").
  Initial bivalence and termination of the construction: as for Theorem 3.
- Abstract/introduction claim (iv) ("any universal construction of `n`-process recoverable consensus from a type `T`
  with consensus number `n` ... requires at least `f + 1` base objects of type `T`") and the remark after
  Corollary 7 ("as well as from any type with consensus number `n`") go beyond Theorem 6, which concerns generic
  constructions from consensus objects. We read "universal construction" as "generic construction from consensus
  objects" (the paper's own Section 6 framing) and formalize only that; the broader reading (arbitrary types `T`,
  non-generic constructions) is neither proved nor refuted by the paper. Not counted against the verdict
  (interpretation of a loosely worded summary). Borderline call: in the same list, (i) and (ii) use "any
  conventional consensus algorithm" in the black-box sense, and the main text states the result only for "generic
  constructions" (Section 6 before Definition 5, remark after Corollary 7), so "universal construction" =
  black-box (generic) construction is the paper's evident meaning; the paper proves nothing about non-generic
  constructions and introduces Definition 5 precisely to exclude them (non-generically, e.g. one atomic sticky
  consensus object without port bound, re-proposed after each crash, suffices for every `f`). Had the abstract wording
  been counted as wrong, the fix ("universal" → "generic") is local and recoverable from the paper (R3, ⚠️); we judge
  the abstract faithful under its evident meaning and keep 🛠️.

## Theorem 1 / Theorem 11 / Lemma 8 (Figure 1, simultaneous failures)

- `theorem1 : SolvesS alg` (Theorem 1 = Theorem 11): agreement of **all** outputs of an execution (also of one
  process in different epochs — stronger than the paper's agreement between distinct processes), validity,
  recoverable wait-freedom, with arbitrarily many simultaneous crashes. `lemma8`: in every execution each process
  accesses `C` at most once (`saccCount`, the simultaneous-model analogue of CSLib's `accCount`).
- Pseudo-code fidelity: every shared access is one step; the two-register conditions of lines 2, 9 and 11 are
  evaluated by two separate reads (`P[i]`, then `P[other]`), each line re-reading as written; `C` is an atomic
  sticky consensus object. Lines 13–14 read `P[1]`; if it were `⊥` the process would return its own input — proved
  unreachable (`l13_recorded`).
- Proof gaps (🛠️, statements true; README item "Lemmas 9, 10, 14"): the paper's proofs treat the two-register tests as atomic snapshots without
  arguing that the non-atomic reads are safe (they are: `P[i]` only changes when `p_i` writes it, and `P` never
  returns to `⊥`); the fact that "an idle process whose proposal is recorded implies nobody is in lines 3–5" is used
  implicitly in Lemmas 9 and 10 (invariant field `quiet`). The space claim ("three registers in addition to `C`")
  holds by construction (objects `P 0`, `P 1`, `D`, `C`).
- Typos: Lemma 9, Case 3 says "reads `P[j] = ⊥` at line 10" (line 9); Lemma 9, Cases 4–5 say "`p_j` returns" for
  `p_i`.

## Theorem 2 / Theorem 16 / Lemmas 12–15 (Figure 2, independent failures)

- `Fig2.theorem16 n f : Solves (A n f) (AtMost f)` (Theorem 2 = Theorem 16) for all `n`, `f` (paper: `n > 1`,
  `f > 0`), with CSLib's strong agreement; `theorem16P` for the paper's spec. Agreement (`lemma14`) and validity
  (`lemma13`) hold in **every** execution (any number of crashes), as the paper remarks; progress (`lemma15`) needs at
  most `f` crashes. `lemma12`: each process accesses each `C[k]` at most once in every execution.
  `fig2_generic`: Figure 2 is generic (Definition 5) — the paper's remark after Definition 5.
- Objects: `withRW (Rr n f) (consObj Bool)`: `R[z]` (`register ℕ 0`), `D[k]` (`register (Option Bool) none`),
  `C[k]` (atomic consensus objects); `n + (f+1)` registers and `f+1` consensus objects, i.e. the space claim
  `O(fB + n)` with `B = 1`.
- Pseudo-code fidelity: one shared access per step; line 25 compares `R[z]` with `k+1`, which equals `R[i]` (only `p_i`
  writes `R[i]`), instead of re-reading `R[i]`; the loop's end without return (footnote 4) is a stuck state that
  never outputs (keeps reading `R[i]`) — proved unreachable with at most `f` crashes; `v` is the proposal carried
  across iterations and reset to the input after a crash.
- Proof gaps (🛠️, statements true; README item "Lemmas 9, 10, 14"): Lemma 14's "at the time when `p_i` reached line 26 in iteration `k_i`, no process
  had reached line 17 in its own iteration `k_i` or higher" treats the scan of `R[1..n]` as atomic (each `R[z]` is
  read at a different time; the argument works per process, invariant "`G k₀ d` holds or some unchecked process has
  `R ≥ k₀+2`"), and "`k_i` or higher" should be "`k_i + 1` or higher". Lemma 15, Case 1 does not consider a process
  reaching iteration `k` by skipping iterations at line 16 in a fresh run (covered by the invariant `PInv`).
- Typos: Lemma 15 / proof sketch of Theorem 2 Case 2: "`R[z] > R[j] = x`" should be `R[j] = x + 1`; Lemma 13:
  "line 20 is bypassed due to the condition `k > 0` at line 19" (there is no such condition; the loop `0..k-1` is
  empty); proof sketch of Theorem 2, Validity: "a process only returns a value decided using some `C[k]` at line 4"
  (line 21).

## Remarks of the text not formalized

- Section 5, after Corollary 4: "if 2-process conventional consensus is implemented using a single TAS (or rTAS)
  object and no additional read/write registers": 2-process consensus needs registers besides the TAS object (the
  loser must learn the winner's input); the intended `O(f)` bound holds with `O(1)` registers per instance. Slip,
  not formalized.
- Θ(f) tightness for TAS (Corollary 4 + Section 4 with TAS-based `C[k]`): needs the composition of Figure 2 with a
  TAS-based 2-process consensus implementation; not formalized. For generic constructions from atomic consensus
  objects the bound is exactly `f + 1` (Theorem 6 + Figure 2), see README.
- Section 6 (universality of CAS etc.) and the consensus-number consequences ("level two remains level two") are
  not formalized.
