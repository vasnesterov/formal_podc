# Differences between the formalization and the paper

Paper: R. L. Jones, M. S. Khan, N. H. Vaidya, *Optimal Record and Replay under Causal Consistency*
(brief announcement PODC 2018), full version arXiv:1805.08804v2; numbering follows the full version.

## Statement-level issues (verdict rules)

1. **Definition 6.4 lacks `w₃ ≠ w₄`, so Theorem 6.6 is false as written** (⚠️, R3). With the literal
   definition, `(o₁, o₁) ∈ C¹_i(V, o₁, w₂)` whenever `o₁` is a write of `i`. `B_i` then contains such
   edges, and the record is not good: `Counterexample.theorem_6_6_literal_false`. The proof of Lemma C.1(a)
   says "`w³ ≠ w⁴₁`, by Definition 6.4", so the intent is recoverable and the fix is local. We model
   Definition 6.4 with a flag `d : Bool` (`Ck`, `Crel`, `B2`, `rec2`). All positive results use `d = true`
   (distinctness at every level); the counterexample uses `d = false`.
2. **Lemma C.1: not a statement issue.** The statement (arXiv v2, p. 27, checked on the rendered page) has
   `R_i = Â_i(V) \ (SWO_i(V) ∪ PO ∪ B_i(V))`, the record of Theorem 6.6, and holds (`lemma_C_1_a`,
   `lemma_C_1_b`). Only Case 1 of the proof of (a) writes `SWO(V)`. This is a typo inside the proof: with
   `SWO` the case split misses the edges in `SWO(V) \ SWO₁(V)`, while with `SWO₁` it is complete.
   `Counterexample.lemma_C_1_SWO_record_false` shows that Lemma C.1(a) fails for the mistyped record. It
   refutes no statement of the paper. An earlier draft of this formalization listed it as a false
   statement, which was wrong.
3. **Theorem 5.6: "online record of V" is per-execution** (⚠️, R4/R3). Taken literally, any record of a fixed
   `V` is "online" and the theorem contradicts Theorem 5.3. We formalize the evident intent: online
   *schemes* (`IsOnline`) whose decision for `(o₁, o₂)` at `i` depends only on `i`'s knowledge when it
   observes `o₂` (`SameKnow`: the prefix of `V_i` up to `o₂`, and the prefix of `V_j` up to every observed
   write of `j`), good for every execution. The paper's "process `i` can check `(o₁,o₂) ∈ SCO(V)`" is
   restricted accordingly. This is exactly the paper's "at most" knowledge bound. An SCO oracle
   unrestricted by that bound would let `i` detect some `B_i` edges and break Theorem 5.6. This is argued on
   paper only (3-process example in the README), not in Lean. The intent is recoverable from the proof of
   Theorem 5.6, which argues by indistinguishability, i.e. over all executions. Borderline between ⚠️ and
   a modelling choice; it does not change the verdict, which Item 1 already makes ⚠️.

## Proof gaps (statements true)

- **Theorem 6.7**: the paper's `U₁` contains both `(o₁,o₂)` and `(o₂,o₁)` whenever `o₁` and `o₂` are writes
  and `o₂` is a write of `i` (`paper_U_has_cycle`). The claim "`SCO(U) \ SCO(A) ⊆ C` by Definition 6.4"
  ignores paths through `(o₂,o₁)`, and "each `U_i` is a partial order by Definition 6.5" needs an extra
  argument. Repaired in `Necessity2.lean` with the constraint relation `F` (`Frel`), computed over
  `A_i \ {(o₁,o₂)}`. The read case matches the paper (typo `(o³, w⁴)` for `(w³, w⁴)` there).
- **Lemma C.1(b)**: the reduction to "bad write pairs" changes the `m = i` clause of Definition 6.5, and the
  cycle surgery of Claim C.3 may use the removed pair. New proof: `cov_preserved` (extremal violated cover,
  `stepA` = Claim C.2, `lemmaX`, `stepB` = Claim C.3), then `lemma_C_1_b`.
- **Lemma A.1(b), Case 4**: maximality is w.r.t. `SCO(V)` but the proof derives an `SCO(V')` pair; the
  `SCO(V)` pair also holds (`lemma_A_1_b`).
- **Theorem 5.6**: no indistinguishable execution is constructed; ours is `exists_indistinguishable`
  (`Online1.lean`).
- **Lemma C.5**: proved differently. Each process is completed independently, adding one safe orientation
  of an unrelated pair at a time (`exists_strictTotal_extension`, `lemma_C_5`).

## Modelling choices

- Operations form a finite type `Op`; processes an arbitrary type `P`; variables `X`. Program order is a
  field of `Program`: a strict total order on each process's operations, and it is fixed (the paper's
  assumption that the replay executes the same operations).
- Write values are not modelled (the paper notes they are redundant given unique write identities). An
  execution is a writes-to map with `none` for the initial value.
- "`V_i` respects `SCO(V) ∪ PO|…`" (union with transitive closure) is formalized literally with `TransGen`
  (`StronglyCausal`), and shown equivalent to containing both relations (`stronglyCausal_iff`).
- Transitive reduction `Â` is `Cov` (the cover relation); `transGen_cov_eq`/`cov_le_of_transGen_eq` show it is
  the unique transitive reduction for finite strict partial orders.
- `SWO` and `C` are defined by levels as in the paper (`SWOk`, `Ck`), with level `0` the paper's level `1`.
  In Necessity2, the auxiliary relation `F` is defined as a least closed relation, not by levels.
- `B_i(V)` cycles: "`A_m ∪· C_i` has a cycle" is `HasCycle` (a `TransGen` loop) of the union.
- Theorems are stated for every process `i` rather than "WLOG process 1".
- Theorem 5.5 is stated as: `rec1on` is an online scheme, and it gives good records. Theorem 5.6 is stated
  as: every online scheme giving good records contains `rec1on` (`rec1on_least_online` combines both).
- Not formalized: the examples of Figures 2–10 and Sections 5.3/6.2 (causal consistency). They were only
  tested by external brute-force Python scripts (not in this folder, not Lean-verified); all claims there
  held in those tests.
