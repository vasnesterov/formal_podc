# Differences between the formalization and the paper

Paper: arXiv 1905.11762v2 (*Acute Cloud Types*), the full version of the PODC 2019 paper. Only
Section 6 (Theorem 5, Corollary 1) is formalized, together with the definitions of Sections 3–5
that it uses.

## Statement-level issues (verdict rules)

1. **Proof of Theorem 5: the hypothesis is strengthened (proof gap, statement true; 🛠️).** The
   proof assumes `BEC(weak) ∧ SinOrd(strong) ∧ BEC(strong)` "in both the asynchronous and stable
   runs". The theorem assumes it in stable runs only. The final execution `H` leaves `R1`'s
   `TOB`-cast messages undelivered, so it is not a stable run when there are such messages. We
   deliver all outstanding `TOB` messages at every replica during the final healing, `R2`'s first
   and then `R1`'s. `H` is then a fair stable run (`CH_stable`). The theorem is proved under its
   own, weaker hypothesis (`NoReordering`). This is a genuine repair of a proof step (R1: the false
   step is inside the proof, the theorem is true).
2. **Local clocks are ignored in the indistinguishability steps (proof gap, statement true; 🛠️).**
   Section 3.2.1 gives replicas local clocks. The arguments "each read returns the same response as
   `e'_c`" (Claim 1) and "the state of `R1` is the same as in `H'`, thus `rval(e_r) = v`" use only
   the state. We pass the clock (= number of the replica's previous steps) to every step. We choose
   a late read in `H'` that sees both appends and replay the whole local input sequence, including
   earlier reads, so that states and clocks coincide (`claim1`, `rvalOf_weak`, `main_contra`). With
   clock-free replicas, the paper's argument would be fine.
3. **Reading of "satisfies `SinOrd(strong) ∧ BEC(strong, F)` in stable runs, and `BEC(weak, F)` in
   both".** We read it like Theorems 1 and 3: in a stable run, *one* abstract execution satisfies
   `BEC(weak) ∧ SinOrd(strong) ∧ BEC(strong)`. The proof needs this, because the contradiction combines
   `er`'s (weak) and `ex`'s (strong) constraints on the same `ar`. With separate abstract executions
   for the weak and the strong part, the proof does not go through. We did not study whether the
   statement would still hold. Not counted as an error (R4: the paper's own usage of conjunctions
   of guarantees).

Verdict: worst label 🛠️ (items 1–2). No checked statement is false.

Borderline calls (why not ⚠️). (a) Restriction 3 read literally (item 5) admits *fewer*
implementations than our reading, so Theorem 5 and Corollary 1 with the literal restriction are
weaker statements and follow from ours: the slip makes no checked statement false. It only
affects the (unformalized) claim that AcuteBayou obeys the ACT restrictions. (b) The `F_seq` typo
(item 4) sits in the witness used by the proof; Theorem 5 is existential and does not mention
`F_seq`. (c) Theorem 5 as printed (strong guarantees assumed in stable runs only) is what
`theorem5` proves; the paper's proof assumed more (item 1), which is a proof repair (R1).
(d) Our classes of runs are subclasses of the paper's fair runs and our `IsACT` admits a
superclass of the paper's ACT implementations (reading restriction 2 as in item 7), so
`theorem5` implies the paper's statement.

## Definitions and typos

4. **`F_seq` (Figure 3): rank off by one.** `rank(A, rel, a) = |{x ∈ A : x rel a}|` is `0`-based,
   while the definition asks for `rank(appends(E), ar, e) = i` for `i ≤ n`, meaning `i = 1..n`.
   Also `n` is undefined. Read literally, `read` has no value on nonempty contexts. We use rank
   `i − 1` and `n = |appends(E)|` (`Fseq`, `wordAt`). The alphabet `$ = {a..z}` is generalised to any
   type; `theorem5` instantiates `Fin 26`, and `theorem5_seq` works for any type with two distinct
   letters.
5. **Op-driven messages (restriction 3).** Literally, only "not read-only" operations may license
   casts. This contradicts the proof ("[strong reads] can cause `R2` to `RB-cast` and `TOB-cast`
   messages") and AcuteBayou, which `TOB-casts` strong read-only operations. We exempt only weak
   read-only operations (`IsACT.op_driven`, `Licensing`). This allows more implementations and only
   strengthens Theorem 5.
6. **Invisible reads** is formalized as: a weak read-only invocation in a reachable configuration
   leaves the state unchanged and responds in the same step. The paper derives "immediate
   response" itself. Whether the read step may cast messages is governed by restriction 3 alone,
   as in the paper (on a passive replica it may not; on an active one it may).
7. **Input-driven processing** is formalized as: from a reachable configuration there is no
   infinite sequence of enabled internal events of one replica (`IsACT.input_driven`). This is the
   paper's "after executing a finite number of internal events (when no new external events are
   executed), the replica enters a passive state". The requirement "initially each replica is
   passive" is not needed.
8. **Restrictions 4 and 5** (highly available weak operations, non-blocking strong operations)
   are not assumed. `RVAL` already forbids pending operations of the relevant level, which is all
   the proof needs. This strengthens Theorem 5.
9. The typo "show how it can be easily to a system with `n > 2` replicas" (a word is missing).

## Modelling choices (all make the impossibility stronger or are neutral)

10. **Runs.** Only crash-free runs, in which every replica invokes infinitely many operations, is
    passive infinitely often, and `RB`-delivers every `RB`-cast message. Asynchronous runs add `TOB`
    agreement; stable runs add `TOB` liveness for every message. The paper's fairness ("infinitely
    many steps of each type of enabled event") holds in all of these. Restricting the class of runs
    weakens the hypothesis "the implementation satisfies P in all runs", so the impossibility gets
    stronger. Stable runs are a subclass of asynchronous runs here; the paper asks for
    `BEC(weak)` in both kinds, which we state literally (`IsAsyncRun ∨ IsStableRun`).
11. **`TOB` order.** All replicas' delivery sequences are prefixes of one total order (no gaps).
    This is the standard reading of "messages are `TOB`-delivered by all replicas in the same total
    order". As in the paper (footnote 7), `TOB` is an abstract oracle, so `R2` may deliver its own
    messages while `R1` is cut off.
12. **Sessions.** Every invocation is its own session (`ss` = equality). This is a legal choice of
    clients, so it restricts the runs. The replica does not see client identities.
13. **Clock.** The clock of a step is the number of the replica's previous steps, a strictly
    increasing local clock. Implementations may use it arbitrarily (also in weak reads).
14. **Messages.** A delivered message comes with its sender, and deliveries are identified by
    `(sender, cast index)`. Passing the sender only enlarges the class of implementations.
15. **Internal events.** An implementation has an arbitrary type of internal events, with
    enabledness depending on the state. Which enabled internal event is executed is chosen by the
    run, which is more general than a deterministic choice.
16. **`H |= P`.** We ask for one well-formed abstract execution satisfying `P`. The paper asks `P`
    for all isomorphic copies, which is stronger for general `P` and equivalent for the predicates
    used.
17. **`n > 2` replicas.** The paper adds extra replicas to one of the partitions. We let them stay
    silent until the final healing in `H'` and `H`, and act like `R1` in `H''`; they never cast
    messages.
18. **Structure of `H''`.** As in the paper, except that the other replicas catch up on *all*
    messages in every round, and `q` first catches up on its own `RB` and `TOB` messages after its
    weak append, which matches `H`.

## Not formalized

19. Theorems 1–4 (ANNC/AcuteBayou correctness in stable and asynchronous runs), the comparisons
    `FEC(F) < BEC(F)` and the parametrised variants, and Section 7. `FEC`, `CPAR`, `SEQ` and `LIN` are
    defined in `Framework.lean` but not used.
