# Efficient Recoverable Writable-CAS (DuraCAS) — PODC 2023

Prasad Jayanti, Siddhartha Jayanti, Sucharita Jayanti. *Brief Announcement: Efficient Recoverable
Writable-CAS.* PODC 2023. DOI [10.1145/3583668.3594592](https://doi.org/10.1145/3583668.3594592).
Formalized version: the brief announcement (statements, Algorithms 1–2, line numbers) with the proofs of
the full version *Durable Algorithms for Writable LL/SC and CAS with Dynamic Joining*, arXiv
[2302.00135](https://arxiv.org/abs/2302.00135) v1 (Appendix A.1, A.3). Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** Theorem 4.1(1) (DuraCAS is durably linearizable) is false under
the recovery rule the brief announcement states ("recover `O` before invoking any other operation on
`O`"): with two objects sharing a handle, a value proposed to one object shows up in the other. Under
the usual per-process rule (recover before invoking anything else) Theorem 4.1(1) holds, with
detectability, and so does Theorem 4.1(2) (wait-free, at most 54 steps). Some DurEC lemmas are
misstated, and the composition step "W and Z behave like atomic EC objects" is unproved in the paper;
both are repaired.

## Mistakes in the paper

### 🚨 Theorem 4.1(1) (recoverable linearizability, per-object recovery rule)
Two processes, two DuraCAS objects with initial value 0, only `CAS(0,1)` and `READ` on `O₀`: a `READ` of
`O₀` returns 2, a value only ever proposed to `O₁` (`theorem_4_1_1_false`, `perObject_counterexample`).

**Impact.** The headline correctness claim fails in the model the brief announcement states. It holds
under the per-process rule, which the full version's wording ("when p restarts, it is required to
execute `O.Recover()`") arguably intends. With that rule we prove it in full (`theorem_4_1_1`). The fix is
a usage restriction, not a change to the algorithm.

**Details.** DurEC handles, and their `Val` and `DetVal` fields, are shared by all objects of the type, as
the paper requires. Process p₀ runs `O₀.CAS(0,1)` and installs `(h, 1)` in `X` of `O₀`'s `Z` (DurEC
line 10). It then crashes before forwarding. Under the stated rule p₀ may now invoke `O₁.CAS(0,2)`
without recovering `O₀`. Its DurEC `ECSC` on `O₁`'s `Z` writes `h.Val ← (2,0)` (line 7). Then p₁ runs
`O₀.CAS(0,1)`: its install fails, and its `FORWARD` moves `h.Val = (2,0)` into `O₀`'s `Z`. The
following `READ` of `O₀` returns 2 (`ceSchedule`, 32 steps, checked by `decide +kernel`). Lemma
`read_val_of_durLin` shows that a durably linearizable history can never do this. The paper's own
composition argument (start of A.2/A.3) also reasons per object. Our Python model checker shows that
detectability fails under this rule as well: the `DETECT` bracket of a later operation picks up the
earlier install.

**Repair.** We assume the per-process discipline, so a crashed process runs `RECOVER` before
anything else. Under it, `theorem_4_1_1` proves durable linearizability *and* detectability of every
history. The setting has any number of processes and objects, values of any type, and individual
crashes.

### ⚠️ Algorithm 1, `FORWARD` (lines 14 and 16: null dereference)
`X` starts as `(null, 0)`, and `RECOVER` (which DuraCAS always runs on both `W` and `Z`) runs `FORWARD`
even on objects that never had an install, where `x.hndl.DetVal` dereferences null.

**Impact.** A missing case in the pseudocode with an evident fix ("if `x.hndl = null` return"), which we
model. Nothing else depends on it.

### ⚠️ Lemma A.10(2) (who can change `h.DetVal`)
"If `h.DetVal` is changed by line 15, then `X.hndl = h` and `h.pc ∈ {13,14,15}`" is false, since a helper can
raise `h.DetVal` while the installer sits at line 11 or has crashed (`lemmaA10_2_counterexample`).

**Impact.** The intended statement ("h's installing `ECSC` has not completed") is what the rest of the
proof uses. The corrected version is proved (`detVal_help_pending`), and detectability (A.10(1), A.10(3),
A.11) holds.

**Details.** The invariant used to prove A.10 has its proof omitted, and it is also wrong. Statement 3
fails once a helper moves while the installer is still at lines 13–15. Statement 4 fails once a handle is
used on two DurEC objects, which DuraCAS does with `h.Critical` on `W` and `Z`.

### ⚠️ Lemma 4.4 / A.5(1) (handle of the installer)
"`X.hndl = h`, `h.Val = v`" names the mover's handle `h` instead of the installer's `h′`, so as written it
is false whenever another process moves.

**Impact.** A typo; the proof reasons with `h′`.

### Typos and slips
- Definition 4.6(2) (full version, main text) linearizes a hitchhiker at "the earliest move"; it must be
  the earliest move after `α[6]`, as Definition A.8 has it.
- Definition A.43(2): "the earliest time when `Z.val ≠ old`" must be read within the operation's
  interval.
- Lemma A.9, case 4 is a copy of case 3 (it says `ECVL` returns `Y`). A.3 says imprints happen "at
  Line 14" (line 10).

## Proof gaps (statements true)

### 🛠️ Appendix A.2/A.3 ("W and Z behave like atomic EC objects")
This is asserted without proof, and it is true only in a weaker sense: a crashed DurEC `ECSC` can take
effect after the crash, while its process is down or recovering, up until the matching `RECOVER`
completes.

**Impact.** Statement true under the per-process discipline; proved as a refinement (`reach_aReach`).

**Repair.** `AModel.lean` defines DuraCAS over *atomic durable* EC objects, where a crashed `ECSC` may
stay pending as an *orphan*. `reach_aReach` shows that every execution of the inlined code (DurEC over
hardware CAS) is matched by an A-level execution with the same history. `aReach_durLinDet` redoes A.3 on
the A-level model with orphans. The paper's linearization points for a failing `CAS` and a hitchhiking
write (Definitions A.42(3), A.43(2)) cannot be decided forward in time. For example, `Z.val` can go
`old → x → old` and the `CAS` still succeed in its second iteration. So these operations are inserted
retroactively at a witness step (`ALin.lean`). Lemma A.38 needs an extra ghost: whether the last change
of `Z` was a move.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- Asynchronous shared memory (NVM) with read and CAS. Any process may crash at any time, any number of
  times. A crash erases the program counter and the locals; memory persists.
- No randomness; the adversary controls the schedule and the crashes.
- The DurEC code is inlined into DuraCAS, one hardware access per step (`Model.lean`).
- Processes, objects and values range over arbitrary types (dynamic joining = unboundedly many
  processes). Process `p` owns the handles `(p,crit)` and `(p,cas)`; `Val` starts arbitrary.
- Most general client. A crashed busy process restarts at `RECOVER` of its object (per-process
  discipline); `StepPO` adds the per-object discipline for the counterexample.
- Histories record invocations, responses, crashes and `RECOVER` completions. Each event carries the
  current `DETECT` value.
- `DurLin` is durable linearizability: a crashed operation takes effect between its invocation and the
  end of its `RECOVER`, or never. `Detectable` is the two-property contract: `d₂ > d₁` ⇒ the operation
  took effect with response `true`; `d₂ = d₁` after a crash ⇒ no effect.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Thm 4.1(1) false as stated (per-object rule) | `theorem_4_1_1_false`, `perObject_counterexample` | `Main.lean`, `Counterexample.lean` |
| Thm 4.1(1) (per-process rule): durably linearizable + detectable | `theorem_4_1_1` | `Main.lean` |
| Thm 4.1(2): wait-free, ≤ 54 own steps per operation / `RECOVER` | `waitFree`, `steps_le_rank` | `WaitFree.lean` |
| DurEC correctness (FV Thm 4.10(1), Lemmas A.1–A.11) + "W, Z atomic" | `reach_aReach` | `Refinement.lean`, `CInv*.lean`, `CStep*.lean` |
| Lemma A.2 | `reach_Yseq_le_Xseq` | `LemmaA10.lean` |
| Lemma A.10(2) false / corrected | `lemmaA10_2_counterexample` / `detVal_help_pending` | `LemmaA10.lean` |
| Lemmas A.28–A.45 (A.3, over atomic durable EC objects) | `aReach_durLinDet` | `ADurLin.lean`, `AInv.lean`, `AStep*.lean` |

**Not formalized.** Theorem 4.1(3) and 4.1(4): dynamic joining is reflected only by the arbitrary
process type, and the space bound `O(m+n)` is immediate from the data layout. DurEC standalone with an
arbitrary client is not formalized; we prove it only as used inside DuraCAS. DurECW and DuraLL appear
only in the full version and are not formalized.

**Trust.** No `sorry`; the listed theorems use only `propext`, `Classical.choice`, `Quot.sound` (the
counterexamples only `propext`, `Quot.sound`, via `decide +kernel`). Self-contained paper-local model on
Mathlib. Both invariants were first checked with exhaustive Python model checkers on small instances.
