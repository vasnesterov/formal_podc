# Differences between the formalization and the paper

Paper: Attiya, Kumari, Somani, Welch. *Store-Collect in the Presence of Continuous Churn with
Application to Snapshots and Lattice Agreement* (arXiv 2003.07787v3, full version of the PODC 2020
brief announcement). Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Store-collect specification (Section 2) — `Spec.lean`

- A schedule is a `List (SCEv P V)`; an operation is identified by the position of its invocation,
  its response is the next event of the same client (`Next`). Views are partial functions
  `P → Option V`.
- Regularity (1), second half, "no other store operation by `p` occurs between this invocation and
  the invocation of `cop`" is read as: no store of `p` whose invocation **and** response both lie
  in that interval (the usual regular-register reading). This is the weaker of the two possible
  readings; Theorem 8 is proved under it, so it also holds under the stronger one. The CCC
  counterexample violates part (2), which does not depend on this choice.
- `V₁ ⪯ V₂` follows the paper literally ("the invocation of `STORE_p(v₁)` does not occur after the
  response of `STORE_p(v₂)`"; vacuous if that store has no response).
- Uniqueness of stored values (`UniqueValues`) is a separate predicate. Algorithm 7 never needs it
  as a hypothesis (its stored values are distinct automatically); the CCC counterexample satisfies it.

## CCC algorithm (Algorithms 1–3) — `CCC.lean`, `CCCCounterexample.lean`

- **Static fragment.** The counterexample uses executions without ENTER/LEAVE/CRASH, so Algorithm 1
  never fires and `Members = S₀` is constant; only Algorithms 2–3 are modelled operationally. Such
  executions are executions of the full algorithm.
- Times are natural numbers (the paper uses reals); `D = 20`; delays in `(0, D]`; FIFO per sender;
  reliable broadcast to all nodes including the sender; the execution is *complete* (every broadcast
  received by every node, no event afterwards), hence a full admissible execution of Section 3 with
  all nodes active forever.
- The server handler for `store` broadcasts two messages (store-ack, store-echo) in one step, as in
  the pseudocode (Section 3 allows one message per step; immaterial).
- `optype` is replaced by an explicit phase (`idle`/`collect`/`store`).
- **Charitable repair 1** (⚠️ typo, R3): `is_joined` is initialized to `true` for the nodes of `S₀`
  (the pseudocode initializes it to `false` for everyone, which would make every collect and every
  join block forever in a system consisting of `S₀`; the proofs assume `S₀` nodes are joined).
- **Charitable repair 2** (⚠️ missing case, R3): client handlers act only on messages of the current
  phase of a pending operation. Literally, collect-replies arriving during the store-back increment
  the shared `counter`, and store-acks arriving after the return trigger "return" again. In the
  counterexample no stray reply/ack reaches `p₁`/`p₂` before the violation (up to time 12), so the
  violation also occurs under the literal code; the repair keeps the tail of the run well formed.
- Parameters of the counterexample: `α = Δ = 1/100`, `γ = 3/4`, `β = 3/5`, `N_min = 2`,
  5 nodes; they satisfy Constraints A–D (printed and cleared forms, `params_ok`).
- **Theorem 6 / Corollary 7 are false** (`theorem6_false`), **Lemma 10 is false**
  (`lemma10_false`), **Observation 5 is false** (`observation5_false`). Lemmas 7 and 8 (and Case I
  of Lemma 10) rely on Observation 5 with the same `view(·)`; we did not refute them separately.
  Decisive rule: R5 — the headline names the paper's algorithm (CCC), which is wrong as written.
  **Borderline (recorded):** the likely repair is local (Line 47 should return the view broadcast
  at Line 36, and `view(φ)` should be the view broadcast in `φ`), but it is not recoverable from
  the paper (the text says "returning LView", `view(φ)` is explicitly "LView at the end of the
  phase", and the proofs of Observation 5, Lemmas 7, 8, 10 reason with that `view`), so R3 does
  not excuse it.
  *Reviewer's note on the borderline.* For ⚠️: the justifications of Observation 5 ("p receives
  phase s's store message directly") and of Lemma 10 Case II (a node of `Qs ∩ Qc` has
  `LView ⪰ view(s)`) are valid exactly for the view *carried by the store message*, so with
  `view(φ)` := that view and Line 47 returning it, the paper's own arguments for Observation 5 and
  Lemmas 7, 8, 10 and Theorem 6 go through essentially verbatim (informal check, not in Lean).
  For 🚨 (endorsed): the error is a missed interleaving (the client returns a variable that its own
  server thread mutates), i.e. a protocol bug, not a symbol slip; prose, pseudocode and
  definition consistently say "LView"; Theorem 6(2)'s proof uses `view(s) = V₁`, which needs the
  printed definition; and the journal version (Information and Computation 285, 2022, Line 51
  "else return LView", same definition of `view(φ)`) keeps it. Same calibration as the
  CRDTReplication (PODC 2019) and DetectableSpace (PODC 2020) verdicts (one-line protocol repairs,
  still 🚨).
- Observation 5 and Lemmas 7, 8 refer to store phases that call "broadcast (Line 42)", the store
  operation's broadcast; the Lean refutation (`observation5_false`) uses a store-back phase (Line 36),
  which is how Lemma 10 / Theorem 6(2) apply them. The same failure occurs for a store operation
  (its `LView` at the end can contain a concurrently merged value; not in Lean). We did not verify the repaired algorithm (the churn part, Lemmas 4–9, is not
  formalized).
- Slip: the proof of Lemma 10, Case I, says "enter-echo message" for "collect-reply".

## Churn model and arithmetic (Lemmas 1–3, Corollary 1, Constraints) — `Churn.lean`, `Constraints.lean`

- Nodes have an entry time, an optional leave time and an optional crash time (at most one of the
  two), `S₀` = nodes entering at `0`. **Local finiteness** (finitely many nodes have entered by any
  time) is an explicit assumption; the paper uses it implicitly (`N(t)` is a number).
- The Churn Assumption is stated as in the paper, for `t > 0` only; the case `t = 0`, used by
  Lemmas 1–2 at `t = 0`, is **derived** (`churn_zero`, needs local finiteness). Proof remark.
- Lemma 1 and the extension to intervals of length `≤ i·D` (`N_le`, used implicitly by Lemma 3 and
  Lemma 10 at times that are not multiples of `D`) — routine.
- Lemma 2 is proved as stated (`lemma2`, `α < 0.206`, `i ≤ 3`). Remark: the proof needs only
  `2(1−α)² ≥ 1`, i.e. `α ≤ 0.293` (`lemma2_of_sq`); `α < 0.206 ≈ 1 − 2^{-1/3}` already gives `i ≤ 4`
  (`lemma2_four`). Lemmas use the weaker hypotheses `α ≥ 0`, `Δ ≥ 0`.
- Lemma 3 needs `t₁ ≥ 0` (implicit in the paper).
- **Constraint (A)** (⚠️ R3): printed as `N_min ≥ 1 / (Z + γ − (1+α)³)`; its denominator can be `≤ 0`
  while (B)–(D) hold, and then (A) is vacuous (`literal_constraints_not_imply_ZNmin`: `α = 0.04`,
  `Δ = 0.01`, `γ = 0.1`, `β = 0.8`, `N_min = 1` satisfy the printed A–D but `Z·N_min < 1`). We use
  the evident intent `N_min·(Z + γ − (1+α)³) ≥ 1` (`ConstraintA'`), which is what Lemma 5 uses.
- Constraint (D) is used in the cleared form; equivalent to the printed one under `β > 0` and (C)
  (`constraintD_iff`).
- Corollary 1 (`corollary1`) is proved from (A′), (B), `γ > 0`. Remark: (A) is not needed for it —
  `Z > 0` and `N_min ≥ 1` suffice (`corollary1_of_Z_pos`).
- The standing constraints imply Lemma 2's hypothesis: (C) ∧ (D) force `α < 1/20`
  (`alpha_lt_of_CD`, `alpha_lt_0206_of_CD`) and `Δ < 0.22` (`Delta_lt_of_CD`); Section 7's
  "less than one-third" is true but loose (`Delta_lt_third_of_CD`).
- Example parameters (p. 11): the set `α = 0.04, Δ = 0.01, γ = 0.77, β = 0.80, N_min ≥ 2` satisfies
  A–D (`example_alpha_004`); the set `α = 0, Δ = 0.21, γ = β = 0.79` satisfies A–D at `α = 0`
  (`example_alpha_zero`) but `α = 0` is excluded by the model (`α > 0`), and for every `α > 0`
  these `γ, β` violate (B) and (C) (`not_constraintB_021_079`, `not_constraintC_021_079`);
  `γ = β = 0.78` works at `α = 1/1000` (`example_alpha_small`). Slip, not a statement error (the
  text speaks of the extreme case `α = 0`).
- The arithmetic core of Lemma 10 Case II (`lemma10_core`) and the inequalities used in Theorems
  3–4 (from (B), (C)) are proved; the operational parts are not.

## Algorithm 7 (atomic snapshot) — `Snapshot*.lean`

- **Abstract store-collect object.** Algorithm 7 runs on top of an arbitrary object: the
  environment chooses the interleaving and the views returned by collects; the only hypothesis is
  that the resulting schedule is `Regular` (Section 2). This is exactly the paper's assumption
  ("Our algorithm … uses a store-collect object"); in particular the theorem holds for any correct
  store-collect implementation, independently of the churn model.
- Nodes form an arbitrary type `P` (possibly infinite), values an arbitrary type `V`; `⊥` is `none`.
  Snapshot views, `scounts` are partial functions.
- Each node runs Algorithm 7 as a deterministic automaton (`lstep`); the choice of `q` at Line 77
  ("if ∃ q such that …") is an arbitrary choice rule `Pick` (any rule returning a witness when one
  exists); the theorem holds for every rule.
- **Line 71** `STORE_p(⟨−, −, ssqno, −, −⟩)` — "with all the other components unchanged": we read the
  `−` components as those of the value `p` stored last (the paper's wording). With the other
  conceivable reading (the current local variables), the embedded scan of an `UPDATE` would store
  the *new* `scounts` (assigned at Line 79) together with the *old* `sview` of the previous update,
  and a scan could borrow a view older than its own start: e.g. `q` completes `UPDATE(a)` whose
  embedded scan returned `∅`; `w` completes `UPDATE(b)`; `p` starts `SCAN`; `q` starts `UPDATE(a′)`,
  its Line 79 sees `p`'s ssqno, its Line 71 stores old `sview = ∅` with the new `scounts`; an update
  of a fourth node between `p`'s two collects makes `p`'s double collect fail, and `p` borrows `∅`,
  missing `b` although `UPDATE_w(b)` completed before `p`'s scan started. Not formalized in Lean;
  recorded as an ambiguity of the pseudocode, not as an error (the text supports our reading).
- Executions are finite lists of events (`hist E` = CSLib `Label`s, store-collect events become
  internal `tau` steps); linearizability is CSLib's `IsLinearization` w.r.t. `snapSpec P V`
  (update ops carry the writer, as a sequential specification does not see the caller). Since every
  prefix of an execution is an execution, this covers all prefixes of infinite executions.
- The UPDATE response is modelled as the empty view (`ACK`).
- **Linearization.** The paper orders direct scans by `⪯`, borrowed scans after the direct scan they
  borrow from, and updates before the first scan that sees them. We give every completed scan a
  *certificate* (a successful double collect inside it; for borrowed scans obtained from the stored
  `sview` via Lemma 12) and order all scans by the vector of their certificate (a chain by
  Lemma 11), ties by completion time; updates are placed as in the paper. This avoids the explicit
  borrowing chains; Lemma 12's nesting (`borrow_cert`) is what makes the certificate lie inside the
  borrowing scan, so chains are not needed and the well-foundedness of borrowing is automatic.
- Lemma 11 is proved for the certificates of all scans (`vec_total`), Lemma 13 in the form
  `kU_le_vec_of_precedes_upd`. Slips: Lemma 11's proof says "Consider any `⟨r, w⟩ ∈ W₂`" for `W₁`;
  Lemma 13's proof speaks of "both stores of `uop_p`".
- Updates included in the linearization: those some stored value reflects (`Vis`; includes all
  completed ones), rather than "those whose Line 83 store started" (same set up to updates whose
  store started but whose value is never stored — irrelevant: neither is seen by any scan).

- **Theorem 8, round bound** (`theorem8_collects`): after the scan's Line-71 store completes at `t`,
  the scan performs at most `#{p | p has an UPDATE pending at t} + 2` collects (one store before; an
  `UPDATE` adds one collect and one store). The paper says "linear in the number of nodes present
  when the operation starts"; its argument (and ours) counts pending updaters at `t`, which under
  churn is bounded by `N(t) ≤ (1+α)²·N(start)` (not formalized; linear either way).
  Both counts ignore a node that left with an `UPDATE` pending (not present, but its store may still
  be observed); the abstract model has no `LEAVE`, so this does not affect the Lean statement. The count may
  include `q` itself (through its own enclosing update). `StoredOK` records, for a stored value with
  `usqno = k ≥ 1`, the invocation of the `k`-th update before its Line-79 collect.

## Not formalized

- Lemmas 4–9, Theorems 3–4 (joining within `2D`, phases complete within `2D`), the operational part
  of Lemma 10 — moot for the algorithm as written (Theorem 6 is false); the repaired CCC is not
  verified.
- Section 6.1 (max register, abort flag, set) and Section 6.3 (generalized lattice agreement from
  the snapshot).
