# Differences between the formalization and the paper

Paper: Guerraoui, Ruppert. *A Paradox of Eventual Linearizability in Shared Memory.* PODC 2014
(EPFL Infoscience copy with the appendix).

## Modelling choices: histories (Section 3)

- **Timed histories.** A history is `ℕ → Option Ev`. Positions may be empty, and an operation is named by
  the position of its invocation, so a response event `res a r` names its operation `a`. On a gap-free
  history the matching is the one forced by well-formedness, and "the first `t` events" are the
  positions `< t`. With gaps, `t` counts positions (steps), so `t`-linearizability with gaps is
  `t'`-linearizability for the number `t'` of events before position `t`. Eventual linearizability
  ("for some `t`") is the same notion either way. Lemma 17 and Proposition 18 are stated for positions
  (step counts), which is what the paper's `|α_C|` (number of tree edges) uses.
- **Well-formedness** (`WellFormed`) is explicit: a response follows its invocation and is unique, and a
  process invokes only after its previous operation responded. The paper assumes all histories are
  well-formed. Lemma 7 needs it (a response without an invocation vanishes from every `H|x`).
- **Sequential histories** are gappy `ℕ`-indexed sequences of `(operation, response)` (only the order
  matters), so infinite `t`-linearizations of infinite histories are `ω`-sequences, as the paper's
  "sequence". Legality is per object: for each object, a state sequence starting in `Q₀` follows `δ`
  along the entries on that object. This is the paper's definition via `H|o`.
- **One spec per object, common operation/response types** (`spec : X → ObjType Q Op Res`); the
  paper's objects of various types are embedded in common types.
- **Definition 1**: "contains all operations performed by the same process that does `op` and precede
  `op` in `H`" uses real-time precedence (`Precedes`). The witness is a finite sequence of distinct
  operations.
- **Definition 2**: transcribed literally. Real-time constraints apply when `op₁`'s response is at a
  position `≥ t` and `op₂`'s invocation comes after it (hence also `≥ t`). Responses are fixed for
  operations responding at positions `≥ t`. Pending operations may or may not be in `S`.
- **Safety/liveness** (Lemma 10, §3.2) are stated for well-formed histories with prefixes `take H m`.
  Limit-closure is "`H` has the property if all its prefixes do".

## Modelling choices: implementations

- **Programs** (`Impl`) are deterministic with arbitrary local states. Actions are: access a base
  object, take a local step, or return. The paper's programmes are Turing machines and its transition
  relations are Turing-computable; computability is not modelled (see Proposition 14).
- **Executions** are infinite label sequences (`none` = no step), all labels enabled (`Proper`). Finite
  executions are those that are eventually `none`. Processes may stop at any time (crashes). The
  environment may invoke any operation at an idle process.
- **Eventually linearizable base objects** (`elSys`, `ELAdm`): a base access is an invocation step and a
  later response step of the same process. The response is chosen by the adversary, and an execution
  is admissible iff each base object's history (`restrict (bhist lab) x`) is eventually linearizable
  for its type. Base objects are wait-free in the sense that the response step is the process's own
  next step. Theorem 12 and Proposition 14 assume base types that are total and have initial states.
  The paper does not say base objects always respond; a base type with an operation that has no
  legal response could block forever and make every implementation vacuously obstruction-free.
- **Linearizable base objects** (`atSys`, Proposition 18) are atomic: a single step applies a transition
  of the (possibly nondeterministic) base type and records the chosen response and state in the label.
  Base types are total. The implementation fixes the initial base states `m₀`.
- **Progress**: wait-free = every operation of a process that takes infinitely many steps completes.
  Obstruction-free = the same when from some time on only that process steps. Non-blocking = if an
  operation is pending at time `N` and infinitely many steps follow, some operation completes after
  `N`.
- **Correctness of an implementation**: every admissible execution's history is linearizable
  (`IsLinearizable`), resp. eventually linearizable (`IsEventuallyLinearizable`, Definition 4) for the
  implemented type initialized to `q₀` (`T.initAt q₀`). The paper's "for each `q₀ ∈ Q₀` a programme"
  becomes one implementation per initial state.

## Statement-level findings

- **Lemma 6 is false for partial types** (`lemma6_false_partial`). Rule R4: the implied assumption
  "operations are total" holds for every type the paper uses (registers, fetch&increment, consensus,
  test&set), and the paper's own remarks ("trivially `t`-linearizable", "any permutation yields a
  legal sequential history") assume it. But its model (`δ ⊆ Q × OP × RES × Q`, finite nondeterminism
  allowing zero transitions) does not exclude partial operations. Verdict ⚠️ (excused, not ❌). Proved
  for total types: `TLinearizable.prefix`. The liveness remark (`exists_tLinearizable_isLiveness`) and
  `tLinearizable_take_self` also assume totality and initial states.
- **Theorem 12 / Proposition 14 need total base types** (rule R4, ⚠️; not a separate verdict level).
  The paper never says its base objects always respond: its model only says a programme "can invoke an
  operation on a base object and await a response from it". If some base type has an operation with no
  transition (or no initial state), no response to it is weakly consistent, so a process calling it
  waits forever. An implementation of any type `T` whose every operation first calls such an operation
  is then linearizable (no responses ever) and vacuously obstruction-free (no process takes infinitely
  many steps), so item 4 of Theorem 12 holds for every `T` while item 1 fails for, e.g., registers.
  This is the same implied totality assumption as for Lemma 6: it holds for every base object the paper
  uses, its proof ("the eventually linearizable objects ... can return arbitrary answers (that satisfy
  weak consistency)") presupposes it, and it is the standard convention (Herlihy's objects have total
  operations). We add `∀ x, (B x).init.Nonempty ∧ (B x).Total` to `theorem12` and `prop14`. (Argued
  in prose; no Lean counterexample.)

## Proof-level findings (statements true)

- **Lemma 17**: the step "In that t-linearization, all the slots of `E` prior to slot `v` are filled using
  operations of `A₁` and operations of `A₄` that begin before `op₁`'s response" is false (a pending
  `A₂ ∪ A₃` operation can fill an `E`-slot); counterexample in the README. Repaired with a different
  prefix (`count_free_le`). The hypothesis `t > 0` is unnecessary; the statement is proved for every
  `t` and any finite number of processes. It uses only that `H` is `t₀`-linearizable for some `t₀` (not
  weak consistency). The bound `|E| ≤ |A₁| + |A₄|` comes from the prefixes; the `t₀`-linearization is
  only needed for `|A₁| ≤ |E|`.
- **Claim 1 of Proposition 18** applies Lemma 17 with `t = ℓ₀ = 0`, outside its hypothesis `t > 0`;
  harmless since `lemma17` has no such hypothesis.
- **Lemma 8**: the "if" proof needs total operations; our proof concatenates the witnesses of the
  process's last operations on the other objects instead and needs no totality.
- **Lemma 7**: cited from [16] with "the proof carries over". For infinite histories the merge of the
  per-object `t`-linearizations into one `ω`-sequence is not obvious. We merge by the key "largest
  late operation at or before the entry" (`lateKey`), with `t = max t_x + 1`.
- **Proposition 16**: the paper's proof uses Lemma 7. Ours works register by register: each register is
  written at most once, so from some time on all its reads return a fixed value. Four terse steps are
  spelled out: the first-read/later-reads property of `Proposal[i]` from weak consistency (only `p_i`
  writes it), at most one write per register, the case `op₀ = op` of the weak-consistency witness, and
  a pending `op₀`.
- **Proposition 18**: Claim 1 needs no König's lemma (the infinite path is built directly, by dependent
  choice). After the stable node, the paper's `C_idle` and the solo run of `p` are one schedule
  (`idleSched`): some pending process steps; when all are idle, `p₀` invokes. The good operation `op₀`
  is found by comparing a `t`-linearization with the set of operations invoked before each solo phase
  (`exists_good_phase`).
- **Theorem 12**: the step "every finite history of `I'` is a possible history of `I`" is checked
  (`sim_weaklyConsistent`: local copies give weakly consistent base histories; a finite execution's
  base histories are `t`-linearizable for `t` beyond their end). The safety of linearizability for
  finite nondeterminism (cited [8, 13]) is proved (`linearizable_of_forall_take`, König). `I'` takes
  two local steps per base access, so that executions of `I'` and `I` match step by step. The theorem
  holds for any finite number of processes, not only `n ≥ 2`.

## Changed definitions / statements

- **Definition 13 / Proposition 14**: "computable function `r`" is replaced by "function `r`"; on the
  implementation side, programmes are arbitrary functions too, so both sides drop computability.
  Proposition 14 is stated for any finite set of at least two processes (the paper says "2 processes";
  the proof uses two of them). "Correct response for every reachable state" is `∃ q', δ q op (r q₀ op) q'`
  (for deterministic types: the unique response).
- **Proposition 16**: registers hold `Option D` (`⊥ = none`) and `write v` takes `v : D` (the algorithm
  never writes `⊥`). Processes and registers are `Fin n`. The algorithm returns its own proposal if the
  scan finds only `⊥`; this is proved never to happen.
- **Proposition 18**: stated for fetch&increment initialized to `0`, nonempty finite process set,
  atomic base objects with total (possibly nondeterministic) types. The conclusion gives
  `A' = shiftImpl A loc₀ v₀` (the same programs and base object types, initial local states `loc₀` and
  initial base states `m₀'` from the stable configuration `C₀`, responses decreased by `v₀`). The paper
  says "from O", meaning the same objects with the states they have in `C₀`.
- **Corollary 19**: only the reduction is formalized (`cor19_of_no_linearizable`). The classical
  impossibility of a linearizable non-blocking two-process fetch&increment from registers (via
  consensus numbers) is a hypothesis.

## Not formalized

- Proposition 11 (appendix: announcing operations restores weak consistency), Proposition 15 (valency
  argument with linearizable registers plus eventually linearizable objects), the remark after
  Proposition 18 (obstruction-free / wait-free variants), the test&set and one-shot remarks of
  Section 4.
