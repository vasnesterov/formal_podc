# Differences between the formalization and the paper

Ghinea, Liu-Zhang, Wattenhofer, *Optimal Synchronous Approximate Agreement with Asynchronous Fallback*,
PODC 2022 (proceedings version; the full version, ePrint 2022/354, has the same protocols and statements).

## Errors in the paper

1. **Theorem 4.1 (Π_rBC is (tₛ, tₐ, 3, 1)-secure): false statement.** `(tₛ,1)`-Synchronized
   Consistency fails whenever `tₛ ≥ n/3` (and `tₛ ≥ 1`). The cause is late proposals from a
   Byzantine sender. Lean counterexample for `n = 3`, `tₛ = 1`, `tₐ = 0`, `Δ = 1`, a lock-step
   synchronous run: `RBC.rbc_attack`, `RBC.rbc_not_syncConsistent`. The general case (`n ≤ 3tₛ`) is
   argued in the README, not formalized. The paper's informal argument ("by time `τ_start + 2Δ`, any
   inconsistent messages … are observed") covers only proposals received by `Δ`. In the full version (ePrint 2022/354, Lemma 6.2) the failing
   step is "`P` has received and forwarded a valid propose message for `v` at time `τ − Δ`", where `τ` is
   the time of `P`'s vote; with a proposal arriving at `2Δ`, `P` forwards and votes at the same time `2Δ`.
2. **Lemma 4.3 and Lemma 4.4 (synchronous part of Theorem 4.2): false statements.** Their proofs rely
   on Theorem 4.1. In the run of `AA.lean`, `Π_oBC` violates `tₛ`-Consistency (Lemma 4.4): the honest
   parties hold `(0, P₂)` and `(1, P₂)`. If `P₂` instead *withholds* its reports, neither honest party
   ever gathers `n − tₛ = 2` witnesses. The other honest party reported a value for `P₂` that it does
   not hold. So `tₛ`-Synchronized Termination (Lemma 4.3) fails. This variant was checked only by
   executing the Lean encoding for 30 ticks (both parties stay in the second loop); it is not
   formalized.
3. **Theorem 3.1 (1) (`Π_AA` is `tₛ`-secure in a synchronous network): false statement** for the
   protocol as written. Lean: `AA.theorem_3_1_sync_false` (`n = 3`, `tₛ = 1`, `tₐ = 0`, `Δ = 1`,
   `ε = 1/2`, inputs in `[0, δmax] = [0, 1]`, so `S = 1` (`AA.S_eq_one`)). Honest outputs are `0` and
   `1`. Lemma 3.3 is the failing step: `|V ∪ V′| ≤ n` does not hold (`|V ∪ V′| = 4 > 3`).
4. **Theorem 5.1 for `n = 1`: false (degenerate case).** With one party, "output the own input" is
   secure for every `tₛ`, `tₐ` (`theorem_5_1_false_n_eq_one`, `hybridAASolvable_of_card_le_one`). We
   assume `n ≥ 2`. For `n = 0` the statement is vacuous.
5. **Theorem 5.1, proof: gap, statement true.**
   (a) "Let `n = 2tₛ + tₐ`" is not a valid reduction in general. For `n = 3`, `tₛ = 2`, `tₐ = 0` no
   `t′ₛ ≤ tₛ`, `t′ₐ ≤ tₐ` gives `2t′ₛ + t′ₐ = 3`.
   (b) For `tₛ = 0` (then `tₐ ≥ n`) the sets `S±ε` of size `tₛ` are empty and the three scenarios
   give no contradiction.
   Fix: groups `S₋`, `S₊` non-empty of size `≤ max(tₛ, tₐ)`, and `Sₐ` of size `≤ tₐ`
   (`exists_split`). Scenarios 1 and 2 use asynchronous security when the group exceeds `tₛ`
   (synchronous executions are asynchronous executions).
6. **Definition 2.2 (asynchronous guarantees): under-specified.** Lemma 3.4 needs values attributed
   to honest senders to be their real inputs. Definition 2.2 does not provide this (in the synchronous
   case it follows from `tₛ`-Synchronized Overlap and `tₛ`-Consistency). We add it as
   `AsyncOBC.authentic`. The concrete `Π_oBC` would provide it via `Π_rBC`'s validity and consistency
   (not formalized).
7. **Definition 2.1: under-specified.** Termination is not stated explicitly ("terminates upon
   generating an output"; agreement "eventually holds"), while the proof of Theorem 5.1 uses it.
   `SecureAA` requires termination, validity and agreement. We take the *first* decision as the output
   (`Outputs`). "For any `ε > 0`" is read as "for the given `ε`": protocols such as `Π_AA` take `ε` and
   `δmax` as parameters.
8. **Typos.** Lemma 3.6: "`0 ≤ tₐ, c ≤ tₛ`" should be `0 ≤ tₐ ≤ tₛ`. Proof of Lemma 3.6: "`i_v`" should
   be "`i_u`". Lemmas 3.3, 3.5: "`length(T ∪ T)`" should be `length(T ∪ T′)`. Lemma 3.5: "Let `P` and
   `P`" should be `P` and `P′`. `Π_oBC` lines 9 and 15: "`(v′, P′)`" should be `(v, P′)`.

## Differences in statements and proofs (results that hold)

* **Theorem 5.1** is proved in a stronger form (`not_secure_sync_and_psync`):
  - asynchronous security is required only on partially synchronous runs (`psyncRuns ta δa`, any GST,
    any `δa`), a subset of the asynchronous runs (`psyncRuns_le_asyncRuns`);
  - synchronous security is used only on zero-delay runs with silent Byzantine parties (any `δs`);
  - only inputs from a domain `D` with two points at distance `> ε` are needed. This covers `D = ℝ`
    (`theorem_5_1'`, inputs `±ε`) and the bounded input space `[0, δmax]` of `Π_AA` when `δmax > ε`;
  - any signature scheme (`Auth`, unforging algorithms) and any message and state types;
  - the adversary is static and the Byzantine behaviour is a replay of honest messages (weaker than
    the paper's adaptive, strongly rushing adversary).
  Only deterministic protocols are covered, as in the paper.
* **Lemma 3.7** is proved directly with order statistics and counting (`card_filter_lt_kth`,
  `le_kth_of_card_filter_lt`, …) instead of the arrays with `⊥` entries. The statement is the
  multiset form: `kth V d ≤ kth V′ (|V′| − 1 − d′)` and symmetrically.
* **Lemma 3.6** (`lemma_3_6`) is stated for any interval `[lo, hi] ⊇ T ∪ T′`, which is the form used in
  Lemmas 3.3/3.5. The paper's form, with `lo`/`hi` the minimum/maximum of `T ∪ T′`, is `lemma_3_6'`.
  Hypothesis: `tₐ ≤ tₛ` (needed; implied by the paper's `tₐ < n/3 ≤ tₛ`). The new value
  `(min T + max T)/2` is `midTrim V d = (kth V d + kth V (|V| − 1 − d))/2` (`kth_mem_trim`,
  `trim_bounds`).
* **Lemmas 3.2–3.5 and Theorem 3.1** are proved *relative to* the guarantees of `Π_oBC` (`SyncOBC`,
  `AsyncOBC`) for every iteration (`theorem_3_1_sync`, `theorem_3_1_async`). Only `tₐ ≤ tₛ` and
  `2tₛ + tₐ < n` are used; `n/3 ≤ tₛ` and `tₐ < n/3` are not needed. The output of `Π_oBC` at a party
  is a partial map sender ↦ value. Consistency with `P = P′` gives at most one value per sender, so
  this loses nothing. Termination of `Π_AA` is inherited from `Π_oBC` and is not restated. The
  iteration count: honest values stay in the range `[lo, hi]` of the honest inputs and are within
  `(hi − lo)/2^S` of each other. `S = ⌈log₂(δmax/ε)⌉` gives `ε` when `hi − lo ≤ δmax`
  (`le_two_pow_ceil_logb`).
* `SyncOBC.overlap` is `tₛ`-Synchronized Overlap stated for every honest party (all honest parties
  terminate in the synchronous case). `AsyncOBC.overlap` is `(tₛ, tₐ)`-Overlap: at least `n − tₛ`
  senders with the same value at `P` and `P′`.

## Modelling choices for the protocol encodings (`RBC.lean`, `OBC.lean`, `AA.lean`)

* Discrete time, `Δ` = 1 tick, `τ_start = 0` for all parties (all start simultaneously, as assumed in
  the synchronous case). A party processes all messages delivered at time `t`, then executes the
  time-triggered actions of time `t` ("when `τ_now ≥ kΔ`"). The messages produced are sent at `t + 1`.
  With delay 0 they are processed at `t + 1`, i.e. every message takes exactly `Δ`. "`τ_now > kΔ`" is
  the first tick after `kΔ`.
* `Π_rBC`: "the first valid `propose`" counts forwarded proposals too. In the counterexample every
  proposal received before voting comes directly from the sender, so the other reading gives the same
  run. Simultaneous messages are processed in the order of the senders' indices, which does not matter
  in the runs used. Line 4 is executed once, at the first tick where the party has forwarded and
  `τ_now ≥ 2Δ`; with a conflict it never votes. Certificates count as received votes. A terminated
  instance ignores further messages. Valid messages are those carrying the right signature tokens. In
  the token model this holds by construction, and `Run.AuthValid` prevents forgeries.
* `Π_oBC`: one `Π_rBC` state per sender (messages tagged by the instance). `O` is a partial map. The
  FIFO channels use sequence numbers, as suggested in the paper: `R_P″` is the longest gap-free prefix
  of the reports received from `P″`, and `|R_P″|` counts distinct pairs. Reports carry no signatures
  (authenticated channels). A terminated party stops completely.
* `Π_AA` is encoded only for `S = 1` iteration (`aaAlg`); the iteration tag is dropped. This suffices
  for a counterexample, since `S = 1` is the parameter choice `ε < δmax ≤ 2ε`.
* The concrete runs are computed with Boolean values (`decide`, via the memoised `simStates`). They
  are transferred to real values (`false ↦ 0`, `true ↦ 1`) with `Run.st_map`. This uses `RBC.stepI_map`
  and `OBC.step_map`: the broadcast layers only compare values for equality.
* Not formalized: the asynchronous correctness of `Π_rBC`/`Π_oBC` (Theorem 4.1 asynchronous part,
  Lemmas 4.5–4.7), `Π_AA` with `S > 1` as a concrete protocol, message complexity (`O(n⁴)` per
  iteration), and the general-`n` versions of the counterexamples.
