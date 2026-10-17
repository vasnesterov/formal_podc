# Differences between the formalization and the paper

Paper: Biely, Robinson, Schmid, *Easy Impossibility Proofs for k-Set Agreement in Message Passing
Systems*, PODC 2011 (2-page brief announcement, pp. 227–228). We formalize the full version, arXiv
1103.3671v2 (March 2011, the latest arXiv version, which predates the conference).
Notation as in the paper: `D = D₁ ∪ … ∪ D_{k-1}`, `D̄ = Π \ D` (the subsystem in which consensus is
impossible). In Lean the groups are `Dg i` and `D̄` is `Dbar`.

## Errors and gaps in the paper

1. **Theorem 1 is false in its literal generality** (under-specified statement: an implicit
   input-independence property of the model; the paper's applications are not affected). The proof derives Fact 1 ("all processes of `D̄` decide on a
   common value in each run of `R(D̄)`") from (B) and `k`-agreement only, and then claims that
   `A|D̄` solves consensus in `M'`. Both steps need that the processes of `D̄` can only decide
   values proposed in `D̄`: otherwise `D̄` may decide some `v_i` (two values `v_1`, `w` in `D̄`
   plus `v_1, …, v_{k-1}` in `D` are only `k` values), and the decision of `A|D̄` need not be
   valid in `M'`. Counterexample (`Abstract.Counterexample.theorem1_statement_false`): `n = 3`,
   `k = 2`, `D₁ = {0}`, `D̄ = {1, 2}`, `V = {0,1,2,3}`; in `M` nobody communicates and process 0
   always proposes 0; `A` = "decide 0" solves consensus (hence 2-set agreement) in `M`; (A), (B),
   (D) hold trivially and (C) holds for `M'` = two non-communicating processes with distinct
   inputs in `{1,2,3}`. The counterexample restricts the inputs of `M` (process 0 always
   proposes 0). The paper's models do not: all `x_q ∈ V` are possible, and changing the inputs of
   `D` changes neither `D̄`'s views until decision nor admissibility. In such models (E) below
   follows by changing `D`'s inputs. Combined with item 2, the literal statement is then
   vacuously true. Repaired version: `Abstract.theorem1_corrected`, with the extra hypothesis
   (E) "in the runs of `R(D̄)` the processes of `D̄` decide only values proposed in `D̄`". In the
   concrete asynchronous instance (`theorem1_async`) (E) is obtained by giving the initially dead
   processes inputs of `D̄`.
2. **Theorem 1, condition (B) is unsatisfiable as stated in the paper's applications**
   (under-specified statement). The values `v_1, …, v_{k-1}` are fixed before the runs, and
   `R(D, D̄)` requires `v_i` to be proposed in `D`. Any run of `R(D̄)` in which a process of `D̄`
   proposes `v_1` (such runs exist whenever inputs are arbitrary distinct values, as in
   Theorems 2 and 10) has no `D̄`-indistinguishable run in `R(D, D̄)` (`Abstract.condB_fails`).
   The proof works if the values may depend on the run; `theorem1_corrected` is stated that way.
3. **Theorem 1, two further proof gaps** (proof gaps; repaired by strengthening (D) in
   `theorem1_corrected`). (a) "Clearly, the same is true for the indistinguishable run ρ, … hence
   ρ ∈ R(D̄)": indistinguishability is only *until each process' own decision*, while `(dec-D̄)`
   forbids receptions until *all* of `D̄` has decided; a process of `D̄` that decided early may
   receive a message from `D` in `ρ` before another process of `D̄` decides. (b) Termination of
   `A|D̄` in `M'` is not addressed: a process that is correct in `ρ'` and never decides could be
   faulty in the compatible run `ρ`; (D) has to preserve correctness. In the paper's applications
   both hold by construction. Condition (A) is never used (it is implied by (B)–(D) whenever
   `M'_{A|D̄}` is nonempty), so `theorem1_corrected` drops it.
4. **Theorem 8, "only if", is not proved for `k n < (k+1) f`** (proof gap; the statement is
   true). Section VI only treats the border case `k n = (k+1) f` by partitioning and otherwise
   relies on "Theorem 2 tightly captures the impossibility". But Theorem 2 is about a *different*
   failure model (`f − 1` initially dead processes plus one crash during the execution), which is
   strictly harder for the algorithm than "up to `f` initially dead", so its impossibility does not
   transfer; and its bound `(n − 1)/(n − f)` is not the bound `f/(n − f)` of Theorem 8 — e.g. for
   `n = 5, f = 3, k = 2` Theorem 2 gives impossibility (with one running crash) while Theorem 8
   gives solvability (initial crashes only). The paper's partitioning argument works verbatim for
   every `k n ≤ (k+1) f` (split into `k+1` groups of size `n − f`); we prove it that way
   (`initDead_impossible`).
5. **Theorem 8 is false for `f = n`** (false only in a degenerate case). With all processes
   possibly initially dead and `k ≥ n`, `k n > (k+1) f` fails, yet "decide your own input"
   solves `k`-set agreement (`theorem8_false_of_f_eq_n`). We assume `f < n`.
6. **Theorem 2 / Corollary 5 need `f < n`** (degenerate case; the paper's bound `(n−1)/(n−f)`
   is undefined at `f = n`, so this concerns only the multiplied-out form; the sets `D_i` of size
   `n − f` must be nonempty). For `f = n = k`, `k (n − f) = 0 ≤ n − 1`, but
   "decide your own input" solves `n`-set agreement (`theorem2_false_of_f_eq_n`).
7. **Section VI, minor slips** (proof gaps / imprecisions, statements true). Lemma 6 needs a
   nonempty graph (the empty graph has no source component); `δ > 0` is not needed
   (`SourceComp.exists_sourceComponent` assumes `Nonempty α`). After stage 2 a process does not
   have "complete knowledge of G", only of its ancestors; this suffices, but the safety proof also
   needs that the ancestor set of a chosen root is frozen once all its ancestors have chosen their
   in-lists (`InitDeadAlg.kSafe`). For `k = 1` the paper calls the chosen set an "initial clique
   (fully connected)"; it is a source component, only strongly connected.
8. **Typos / slips.** Proof of Theorem 10: "the conditions required for applying Theorem 2"
   should be Theorem 1. Proof of Lemma 7: "the previous theorem" is Lemma 6. Section VI: "when
   `2δ ≥ n`, then there can be only one source component" (true, already for `2δ ≥ n − 1`).

## Modelling choices

- **Model.** CSLib's asynchronous FLP model (`Cslib.FLP.Algorithm`): a step is the reception of
  one in-flight message (multiset, unordered, no loss) with atomic local transition, sending and
  deciding; stuttering steps; a crash is "stops receiving from some point on while a message to it
  is in flight"; correct = receives every message sent to it. The paper's model (from [DDS87]) lets
  a step receive any subset of the buffer and lets a crashing process omit some sends in its last
  step. Our adversary is weaker (fewer schedules/failures), so our impossibility results imply the
  paper's; the possibility result (Theorem 8) only involves initial crashes.
- **Inputs.** CSLib's processes have Boolean inputs delivered by a wake-up message. `KAlgorithm`
  has inputs in an arbitrary `V`, in the initial state; messages that arrive before the wake-up
  message are buffered and processed right after it (equivalently: the first step of a process
  receives nothing). This only restricts schedules; an unbuffered algorithm can buffer itself.
  The input `x : P → V` is arbitrary (not only distinct); the paper's problem quantifies over all
  inputs from `V` with `|V| ≥ n`. Our impossibilities only need `k + 1` distinct values.
- **Specification.** k-Agreement and Validity are required in every reachable state (so they bind
  correct and faulty processes, as in the paper); Termination in every admissible infinite run for
  every non-faulty process. Decisions are write-once by construction.
- **Failure assumptions** are run predicates: `InitDead f` (≤ f processes never take a step, all
  others correct), `OneCrash f` (≤ f − 1 initially dead plus at most one other faulty process —
  Theorem 2's pattern), `Crash f` (CSLib's admissible runs with ≤ f faulty processes).
- **Theorem 2** is formalized for *asynchronous* processes (Corollary 5's model) with Theorem 2's
  failure pattern. The paper's Theorem 2 has synchronous processes and atomic broadcast; its
  condition (C) then rests on [DDS87, Table I], which we do not formalize. Corollary 5
  (asynchronous, up to `f` crashes) follows (`corollary5`).
- **Theorem 1** is formalized twice: abstractly (`Abstract.lean`: models as sets of runs with
  views, inputs and decisions read off views, Definition 2 as equality of views; the literal
  statement is refuted and a corrected one proved), and concretely for the asynchronous model
  (`theorem1_async`), where (C) is CSLib's FLP theorem and (A), (B), (D), (E) are discharged by
  solo runs, merging and lifting.
- In `theorem1_async` the processes outside all groups are not required to belong to `D̄`
  (`D̄` need not be `Π \ D`); the extra processes are simply never scheduled.

- **Theorem 8's algorithm** (`Algorithm*.lean`): stage 1 broadcasts, a process waits for stage-1
  messages from `n − f − 1` others (its in-list); stage 2 broadcasts (input, in-list); a process
  decides once its knowledge is closed under in-lists, on the input of the minimum *root* (a vertex
  in a source component) among its ancestors. Messages carry the sender id explicitly.

## Not formalized

- Section VII (failure detectors `Σ_k`, `Ω_k`, partition failure detector, Lemmas 9, 11, 12,
  Theorem 10, Corollary 13): needs a failure-detector framework and cited results (weakest failure
  detector for consensus, `(Σ, Ω₂)` strictly weaker than `(Σ, Ω)` via [21] and a shared-memory
  simulation [9]).
- Definition 6 / Observation 1 (T-independence) as a separate notion; Lemma 4 is used in the form
  "solo runs of the groups are admissible".
- The partially synchronous variant of Theorem 2 (synchronous processes, atomic broadcast).
