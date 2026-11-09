# Differences between the formalization and the paper

Paper: V. Gramoli, P. Kuznetsov, S. Ravi, *From Sequential to Concurrent: Correctness and Relative
Efficiency* (brief announcement), PODC 2012. Formalized version: the full version, arXiv
1203.4751v8, *Optimism for Boosting Concurrency* (2015), whose numbering we follow: Definition 1,
Theorems 2, 3, 5, 6, 7, 11, Corollary 4, Lemmas 8–10.

## Errors in the paper

1. ❌ **Theorem 3 (optimality of `I_RM`) is false.** `I_RM` rejects the observable schedule
   `σ_bad` (`theorem_3_false`, `not_theorem_3`, `IRMReject.lean`). From `{1, 3, 4}`, `contains(4)`
   reads `head` and `X₁`; then `remove(3)` runs alone and returns; then `contains(4)` reads
   `X₃`, `X₄` and returns `true`. Line 27 of `remove`'s write has marked `X₃` before the write
   returned, so the later read of `X₃` returns `⊥` (line 15) in every execution of `I_RM`. The
   schedule is observable even in a much stronger sense than §6 asks (`ObservableStrong`: an
   honest history exports it, and `contains(v)` run afterwards on the actual memory keeps it LSL
   for every `v`; `sigmaBad_observableStrong`). The proof sketch fails in subcase (1a): "since no
   removed element can be read in a sequential execution of `LL`, the history is not locally
   serializable" ignores that local serializability is *per operation* (Definition 1):
   `contains(4)`'s own witness is the sequential history without `remove(3)`. Subcase (1b) ends
   with "there exist executions that export such schedules", which proves nothing either.
2. ❌ **Corollary 4** (`I_RM` accepts every schedule accepted by an implementation in `P` or `SM`)
   has no valid proof: it is derived from Theorem 3, plus the unproved remark that `SM` and `P`
   only accept observable schedules. `σ_bad` is exported by an honest, LSL, quiescent,
   safe-strict serializable history (`sigmaBad_sm`, `Corollary4.lean`), so the definition of `SM`
   does not exclude it; TL2 (invisible reads, no validation of read-only transactions) accepts it.
   We do not formalize a TM, so the falsity of Corollary 4 itself is argued, not mechanized.
3. ❌ **Theorem 7 (part 2 of Theorem 2: no implementation in `P` accepts `σ`)** is false
   (`theorem_7_false`, `lookahead_classP`, `lookahead_accepts`, `Lookahead.lean`/`Theorem7.lean`): a deadlock-free, pessimistic, honest
   (hence obedient), LS-linearizable lock-based implementation accepts `σ` (Figure 2(a)). The
   global reader–writer lock is taken at the first read of an operation, in shared mode when the
   operation does not change the abstract set of the current memory (lookahead, using the
   operation's argument), in exclusive mode otherwise. Its LSL proof uses the sequential
   correctness of `LL` (`soloRun_correct`, `LLCorrect.lean`), which the paper takes for granted. The step "if some `I ∈ P` accepts `σ` it must accept `σ′`" is wrong:
   the base objects after the different prefixes of `σ` and `σ′` differ, so processes *can*
   distinguish the two executions before their reads of `X₁` return.
   *Assumption used:* the implementation of `read(head)` executed by `insert(v)` knows `v` (the
   paper's implementations are derived by inserting synchronization into the sequential code of
   the operation, where `v` is in scope; Algorithm 1 and `I_H` also branch on the operation type;
   §5 says `P` contains implementations "fine-tuned to the semantics of the type"). The paper
   restricts implementations only by LSL, pessimism, deadlock-freedom and obedience. Not checked:
   whether Theorem 7 holds for the narrower class of implementations that cannot see the
   arguments of operations.
4. 🔧 **Theorem 6 (part 1 of Theorem 2, the `SM` half): `σ₀` (Figure 1) is not accepted by any
   implementation in `SM`.** As defined, acceptance looks only at `complete(H)`, while strict
   serializability may use commit-pending transactions. `theorem_6_loophole`
   (`Serializability.lean`): a history with a stalled commit-pending `remove(2)` (process 4, which
   re-links `X₁ := ⟨1, X₃⟩`) is honest, LSL, safe-strict serializable and exports `σ₀`
   (serialization: prefix, `insert(2)`, `insert(5)`, `remove(2)`, `contains(5)`; a value-validating
   TM such as NOrec produces it when process 4 stops after its write-back; only the history is
   mechanized, not the TM). Appendix C.1 restates strict serializability with `cseq(α)` = the
   complete operations only; with that definition the theorem holds. Repair, proved:
   `theorem_6_appendix` — no history that is strictly serializable in the sense of Appendix C.1
   and whose committed operations follow `LL` (`LocSer SigLL (complete H)`) exports `σ₀`; this is
   the paper's two-case argument. Corollary for the §4 definition: `theorem_6_quiescent` (every
   transaction committed or aborted).

## Proof gaps and imprecisions (statements true or unaffected)

- Theorem 5 (compositionality): the proof starts with "Let H … be LS-linearizable with respect to
  IS" (the conclusion), and builds interleavings `S_π` of witnesses of both components; since each
  operation acts on one object, `H|π = (H|O_i)|π` and no interleaving is needed. We prove the
  statement directly (`theorem_5`): the local-serializability half is immediate and the
  linearizability half is Herlihy–Wing locality.
- "Observable" (§6) is ambiguous: if the read values of the appended `contains(v)` are only
  constrained by LS-linearizability (Definition 1 does not tie reads to writes), then the lost
  update schedule `σ′` of Figure 2(b) is observable too (`contains(1)` may read a node holding
  `1`), contrary to the text. We prove `σ_bad` observable under the literal reading
  (`Observable`) and under a strong reading (`ObservableStrong`, honest memory), so the
  refutation of Theorem 3 holds under both.
- §2 says the exported history omits reads and writes that return `⊥`, while `H|π` (§3) removes
  "the last aborted read or write", which presupposes that they are present. We keep `⊥` events in
  histories (needed to tell aborted from pending operations).
- Appendix D: the linearization points of writes are swapped (the write of `insert` is linearized
  at "line 22", which is `remove`'s `cas`, and vice versa).
- Theorem 7's proof uses obedience for `α′` although the relevant prefix is not a complete
  sequential execution followed only by reads.

## Modelling choices

- **Histories** (`Basic.lean`): events carry the process and the high-level object; reads/writes
  of base objects (`rinv/rres`, `winv/wres`); `⊥` is `rres _ _ none` / `wres _ _ false` and also
  ends the operation. `H|π` is `localView`; local serializability takes the witness `S ∈ Σ_IS`
  ending with `π` (equivalent since `Σ_IS` is prefix-closed and sequential). The high-level
  history `hl H` drops aborted operations; linearizability is the (amended) Herlihy–Wing
  definition from CSLib. Histories are meaningful when well-formed; Theorem 5 assumes the
  high-level history is well-formed.
- **Schedules**: a schedule is the erasure of `complete(H)` (read values, high-level responses and
  ok/⊥ flags forgotten; written values kept, as invocations). `Accepts I σ`: some exported `H`
  has `complete(H)` erasing to `σ`.
- **`LL`** (`ListSet.lean`): Algorithm 2 as a program; `new-node(v, prev.next)` is a write of the
  new node to a *fresh* location (an extra write event before the linking write; the figures show
  "only important events"). Keys are `-∞`, integers, `+∞`; the set type is the deterministic
  object `setObj`. `Σ_LL` = sequential runs of `LL` from the empty list (reads return memory).
- **Implementations** (`ImplModel.lean`): sets of exported histories, prefix-closed, receptive to
  every invocation the `LL` client can issue, and producing only responses to pending reads and
  writes; responses may depend on the whole history (base objects are arbitrary). Class `P`
  (`ClassP`) uses the strongest reading of each condition (all histories LSL and honest, no `⊥`,
  deadlock-freedom as "never stuck + bounded number of events without a new invocation before a
  response"), so a member of `ClassP` is a member of the paper's `P`.
- **`I_RM`** (`IRM.lean`): every shared access of Algorithm 1 is one atomic step, in any
  interleaving; the model over-approximates the real `I_RM` (arbitrary client, arbitrary initial
  `t-var`, a failed `cas` may abort or retry with the current version — the refinement described
  in the text of §6 —, allocation of new nodes as a plain store), so `irm_rejects` applies to the
  real algorithm a fortiori. `rbuf` is not reset between operations (the paper does not say);
  for `LL` clients this is irrelevant, since every operation reads `head` and its successor
  before its first write, so `rbuf` then holds the same two entries. Process identities are
  natural numbers.
- **`SM`** (`Serializability.lean`): transactions = high-level operations; commit-pending = all
  reads/writes done and `LL`'s next action is to return; `Cseq`, legal sequential executions from
  the empty list, strict and safe-strict serializability as in §4 / Appendix C.1.

## Not formalized

- Theorem 11 / Lemmas 8–10 (`I_RM` is LS-linearizable): not checked. We did not find a
  counterexample; the proof sketch is informal (e.g. Lemma 10(1) compares a write "by π₂" with
  itself).
- The pessimistic hand-over-hand implementation `I_H` (Theorem 6, first half: `I_H ∈ P` accepts
  `σ₀`): not modelled; we only prove that `σ₀` is LSL (`sigma0_lsl`).
- `I_C ∈ SM` accepting `σ` (Theorem 7, second half) and the experiments (§8, Appendix E).
