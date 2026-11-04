# Disjoint-Access Parallelism and Wait-Freedom in Universal Constructions — PODC 2012

Faith Ellen, Panagiota Fatourou, Eleftherios Kosmas, Alessia Milani, Corentin Travers. *Universal Constructions
that Ensure Disjoint-Access Parallelism and Wait-Freedom.* PODC 2012. DOI
[10.1145/2332432.2332457](https://doi.org/10.1145/2332432.2332457). Formalized version: the full version, HAL
research report [hal-00697198v2](https://inria.hal.science/hal-00697198v2) (May 2012, 34 pp.); no arXiv version.
Numbering follows the full version.

**Verdict: ✅ Correct.** The impossibility result (Theorem 5: no feebly disjoint-access parallel universal
construction is wait-free) holds, and its proof (Lemma 4 and the construction of the infinite execution `α'`)
goes through as written. The construction DAP-UC and its correctness (Theorem 6) are not formalized.

## Mistakes in the paper

No mistakes in the statements.

### Typos and slips
- Section 4 calls the pointer to the first node `L.first` (Section 3: `first`/`last`), while the code of Figure 6
  calls it `L.start`/`L.end`.
- Assumption 3 speaks of "the sets of base objects read from and written to during any solo execution of a
  sequence of consecutive instances"; the proof needs these sets *per instance* (it uses `B(ℓ)`, the objects
  written by the `ℓ`-th instance alone). The per-instance reading is the one we formalize.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory, CSLib's `Cslib.SharedMemory.Impl`: deterministic processes, every step applies one
  primitive to one base object, base objects are arbitrary sequential objects (registers, CAS, LL/SC, …), the
  scheduler is arbitrary. Crashes need no extra structure: wait-freedom (`Impl.WaitFree`) quantifies over all
  infinite executions, so a process that stops taking steps is a crashed one. Every process may invoke every
  operation. Randomized implementations are not covered (the paper reduces them to deterministic ones by fixing
  the coin tosses).
- A primitive is *trivial* if it never changes the state of its base object (`ObjSpec.ReadOnly`); two executions
  *contend* on `b` if both apply a primitive to `b` and one of them is non-trivial (`Contend`). Base objects cannot
  see the caller, so LL/SC is encoded with a version number kept by the caller (`versionedLLSC`: `LL` reads the
  value and version and is trivial, `SC` is a compare-and-increment on the version); this gives the paper's
  classification. (CSLib's `llscObj` keeps the link set in the object's state, making `LL` non-trivial; with that
  encoding feeble DAP would be a stronger hypothesis.)
- A sequential data structure (`SeqDS`) is its sequential specification together with the data items each
  operation accesses from each state (its *data set*, determined by the code). A universal construction maps every
  data structure to an implementation (`UniversalConstruction`). The list of Figures 5/6 is `listDS`: states are
  lists of keys, data items are `L.start`, `L.end` and the nodes; the data sets are read off the code of Figure 6.
- **Definition 1** (`FeeblyDAP`): for every quiescent configuration `C` reached by an execution `α` all of whose
  linearizations end in the same state `s`, solo executions (complete or partial) from `C` of two operations by
  two different processes whose data sets from `s` are disjoint do not contend.
- **Assumption 3** (`ImplValueOblivious`): from every reachable quiescent configuration, the base objects accessed
  and the base objects written by each instance of a solo sequence of instances of a value-oblivious operation do
  not depend on the parameters (`UniversalConstruction.ValueObliviousAssumption`: for every value-oblivious
  operation of every data structure).
- Linearizability is CSLib's `Impl.Linearizable`.

**Proof remarks.**
- The proof uses wait-freedom only to make the appends `αᵢ` and the searches `σᵢ` terminate; the contradiction is
  an infinite execution in which `p` takes infinitely many steps and never returns.
- `βᵢʲ` is represented by its length `blen` (steps of `p`'s solo run from `Cᵢ` before the first step that accesses
  a base object of some `B(k)` or writes one of some `A(k)`, `k ≥ j`); `γ_{i+1}` is the difference of two such
  lengths. That the steps of `α'` form an execution is proved by commuting `p`'s fragment with the next append
  (`Impl.runFrom_comm`), which is the paper's indistinguishability argument.
- `theorem_5_list` is the statement to read: every linearizable implementation of the list (data sets read off
  Figure 6) satisfying Definition 1 and Assumption 3 for `Append` is not wait-free. `theorem_5` lifts it to
  universal constructions, but its hypotheses range over every `SeqDS`, including data-set annotations no code
  produces (e.g. all empty, which already rules out wait-free linearizable implementations by a one-line
  argument), so it is weaker than the paper's statement on its own.
- Feeble DAP is applied to a *partial* solo execution of `Search(0)` (`βᵢⁱ⁻²` plus one step), as the proof does;
  under wait-freedom this is equivalent to using the complete one.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 5, for the implementation of the list (faithful form) | `theorem_5_list` | `Theorem5.lean` |
| Theorem 5, for universal constructions (corollary) | `theorem_5` | `Theorem5.lean` |
| `α'` is an execution (each finite prefix) | `run_exec` | `Theorem5.lean` |
| `γⱼ` nonempty for infinitely many `j` | `M_lt`, `M_unbounded` | `Impossibility.lean`, `Theorem5.lean` |
| Lemma 4 | `blen_stable`, `M_mono` | `Impossibility.lean` |
| `Search(0)` has not returned after `βᵢⁱ⁻²` | `pending_bad` | `Impossibility.lean` |
| Section 3: `Append` is value oblivious, `Search` is not | `append_valueOblivious`, `search_not_valueOblivious` | `List.lean` |
| Definition 1, Assumption 3, universal constructions | `FeeblyDAP`, `ImplValueOblivious`, `UniversalConstruction` | `Model.lean` |

**Not formalized.** The DAP-UC algorithm and Theorem 6 (Theorem 24 linearizability, Theorem 32 wait-freedom,
Lemmas 33–41 disjoint-access parallelism, Definition 2); the claims that feeble DAP is weaker than all other DAP
variants and that the impossibility extends to transactional memory with re-execution of aborted transactions
(stated without proof); randomized implementations.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity (`NonVacuity.lean`): the atomic implementation of the list (CSLib `atomicImpl`) is linearizable,
wait-free and satisfies Assumption 3 for `Append`, so these hypotheses are jointly satisfiable; by Theorem 5 it
is not feebly DAP (`atomic_not_feeblyDAP`). The versioned LL/SC object has a trivial `LL`. The model is CSLib's `Cslib.Computability.Distributed.SharedMemory`
(`Model`, `Progress`, `Linearization`, `Covering`, `Atomic`); the contention/commutation library is staged in
`Podc/Computability/Distributed/SharedMemory/Contention.lean` (CSLib candidate).
