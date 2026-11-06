# Differences between the formalization and the paper

Paper: Bonomi, Del Pozzo, Potop-Butucaru, Tixeuil, *Optimal Mobile Byzantine Fault Tolerant Distributed
Storage*, PODC 2016; full version HAL hal-01348830v2 (Feb 2017).

## Model

- **Time and schedule.** Real time. The `ΔS` adversary moves all agents at the times `t₀ + iΔ`,
  `i ∈ ℤ`. Each period `[t₀ + iΔ, t₀ + (i+1)Δ)` has a set of at most `f` hosting servers (`Schedule`). The
  paper says "at most `f` agents"; agents may also stay on a server. Periods are indexed by `ℤ` (the
  paper starts at `t₀`); this only matters for times before `t₀`, and every construction stays after `t₀`.
  At a move time `m` the agent is on the *new* server (half-open periods). The paper does not fix this
  convention; all constructions keep strict margins, so nothing depends on it.
- **Delays.** Every message is delivered within `(0, δ]` of its sending, at a time chosen by the
  adversary (Section 2: "delivered by time `t + δ`"; we use one `δ = δ_b ≥ δ_p` as the paper does).
  Faulty servers' messages obey the same bound. In every counterexample the replies are delivered
  strictly inside the read's waiting window `(t, t + D)`, so the convention for a delivery at exactly
  `t + D` does not matter. The paper's lower-bound scenarios deliver them
  instantly; we require a positive delay, which only weakens the adversary in the lower bounds.
- **Reader (attacks).** Only the client side of `read()` is modelled. `reply_i` collects the triples
  `⟨j, ⟨v, sn⟩⟩` of all replies delivered in `(t, t + D]`, with `D = 2δ` (CAM) or `3δ` (CUM). The result
  is any pair allowed by `select_value` (`SelectValue`): at least `thr` occurrences and maximal `sn` among
  such pairs; ties are left open. Replies of correct and cured servers are universally quantified,
  constrained only by `sn ≤ N`. The README explains why this holds in the counterexample executions (the
  faulty servers send nothing to servers, so correct servers store only written pairs and `⟨⊥, 0⟩`).
  This argument is informal: the server code and the writer are not modelled.
- **Cured liars (CUM).** `CuredLiar` is a server not faulty now but faulty during the last `2δ`. Such a
  server may send a non-valid reply when the read request reaches it (`LyingReply`). This is Lemma 18
  of the paper. The code-level justification (an adversarial `W_i` entry with timer `2δ`, returned by
  `conCut`) is argued in the docstring, not modelled. Fig. 25, line 02 removes `W_i` entries only if
  "`Expired(timer) ∧ timer > 2δ`". Read literally, an entry with timer `≤ 2δ` is never removed, which
  would make cured servers lie even longer; we use the prose reading (removed at expiry).
- **Lower-bound model (`ReadExec`).** This is the scenario of Section 4.4. One read with no concurrent
  write; request arrival times in `(t, t + δ]`; a server correct (neither faulty nor cured) at its
  request time replies once with the register value, with delay in `(0, δ]`; faulty and cured servers do
  not reply correctly; faulty servers send arbitrary (sender, value, time) replies. The reader sees the
  set of (sender, value, delivery time) and may use any decision rule. This is stronger for the reader
  than the paper, which only compares multisets of values. It restricts protocols as the paper does:
  correct servers reply exactly once; there is no forwarding and no later reply after a cure.
- **Values.** The attacks work for any value type `V` with a fake value `v′`; lower bounds use `Bool`.
- **γ.** The paper's cure duration `γ` is a parameter of `Cured`, but the lower-bound constructions
  never use it (the silent servers are faulty when the request arrives). So `theorem3`/`theorem5` hold
  for every `γ`; the paper's hypothesis `γ ≤ δ` is not needed.

## Statements

- **Lemma 6** (`lemma6`, `lemma6_false`). The paper's equality `MaxB̃(t, t+T) = (⌈T/Δ⌉+1) f` is false
  when it exceeds `n`. Formalized: the upper bound for every schedule, and `MaxB̃ = min(n, (⌈T/Δ⌉+1) f)`
  (as an `IsGreatest`) for `0 < f`. The hypotheses `δ ≤ Δ < 3δ`, `T ≥ δ` are dropped (only `Δ > 0`,
  `T ≥ 0` are needed). ✏️: the missing `min n` holds at every use (`T ≤ 3δ` with `n ≥ 4f + 1`).
- **Lemma 7** (`lemma7`). Stated with the paper's reading of `minC̃oR(t, t+2δ)` (servers never affected
  during `[t, t+δ]`), as: for every schedule and every `t`, `n − |B̃[t, t+δ]| ≥ (k+1) f + 1` and
  `> |B̃[t, t+2δ]|`. True. The paper's formula `n − (⌈2δ/Δ⌉+1) f` in the proof is a typo for `⌈δ/Δ⌉`.
- **Theorems 8/9** (`theorem9_false_k1`, `theorem9_false_k2`, `theorem9_false`). Refuted for
  `2δ ≤ Δ < 3δ` (`k = 1`) and `δ ≤ Δ < 3δ/2` (`k = 2`). `theorem9_false` instantiates `n = (k+3) f + 1`
  and `#reply_CAM = (k+1) f + 1` (Table 1); `_k1`/`_k2` hold for all `n ≥ 3f` resp. `4f`. Not
  decided: `3δ/2 ≤ Δ < 2δ` and `Δ ≥ 3δ`. ❌: `f = 1` and the paper's own `n`, `#reply` are used; the delay
  assumption is the paper's own system model. *Note*: the refutation depends on faulty servers being allowed to
  use the full delay `δ`. The paper's correctness section assumes instant delivery "as the worst case",
  but that is a (false) claim about the worst case, not a model assumption (Section 2 allows any delay
  `≤ δ`).
- **Corollary 3** (more valid than non-valid replies in every read) is false for the same reason, e.g.
  `3f` liars against `n − 2f = 2f + 1` correct replies for `k = 1`, `f ≥ 2`. Not formalized separately,
  because correct servers are not modelled. Covered by the Theorem 9 item.
- **Theorems 11/12** (`theorem12_false_k1`, `theorem12_false_k2`, `theorem12_false`). Refuted for
  `2δ ≤ Δ < 5δ/2` (`k = 1`: `3f` faulty + `f` cured liars) and `δ ≤ Δ < 5δ/4` (`k = 2`: `4f` faulty +
  `2f` cured liars), with Table 3's `#reply_CUM = (2k+1) f + 1` and `n = (3k+2) f + 1`. Unlike the CAM
  case, no lying reply is sent before the read starts, so this refutation stands even if faulty
  servers' messages were assumed to be delivered instantly; it matches the paper's own count of `4f`
  (resp. `6f`) non-correct servers in the proof of Theorem 11. The CUM `select_value` is worded "if there
  are more pairs with the same occurrence, it returns the one with the highest sequence number"; we read
  it like the CAM one (highest sequence number among the pairs reaching the threshold), as the proof of
  Theorem 11 confirms ("even if an older value has `#reply_CUM` occurrences the one with the highest
  sequence number is chosen"). The statement of Theorem 12 itself has `n ≥ 2(k+1) f + 1`, which contradicts
  Table 3 and Theorem 4. Both readings are refuted (the attack needs `4f` resp. `6f` servers). The
  refutation uses the paper's Lemma 18 window of `2δ` for cured liars. ❌: the CUM protocol is the paper's
  second main protocol. **Theorem 13** (tightness of the CUM protocol) falls with it.
- **Theorems 3 and 5** (`theorem3`, `theorem5`). The paper's proofs compare executions with the same
  schedule, which an authenticated reader distinguishes. Re-proved in the Section 4.4 model with
  different schedules, for every read duration `D` and every decision rule. `theorem5` assumes only
  `Δ ≥ 2δ` (no upper bound `3δ`); the proof works for `Δ > δ/2`. The general statement "no protocol
  `P_reg`" (arbitrary server behaviour, e.g. replying again after a cure) is not established by the paper
  and not by us. ⚠️: proof broken, statement in the restricted model repaired, general statement
  unestablished.
- **Theorems 4 and 6** (CUM lower bounds): not formalized. Their executions have the same defect
  (e.g. Theorem 4, `s₁` replies `0` in `E₁` and `1` in `E₀`). In Theorem 6 the multisets of `E₁‴` and
  `E₀‴` are printed identically.

## Not formalized

- Theorem 1, Corollaries 1–2, Lemmas 1–3, Theorem 2 (necessity of maintenance; asynchronous
  impossibility). These are informal claims about all protocols in a model whose semantics the paper
  does not define (e.g. "valid state", "maintenance operation").
- Lemmas 4–5, Theorems 7 and 10 (termination: the operations wait a fixed time).
- Lemmas 8–12 and 13–21 (correctness of the two protocols; moot after the counterexamples). Lemma 13 is
  Lemma 6 verbatim.
- Definitions 1–5, 10–13 are used only informally; Definition 8 is `Schedule.affected`, Definition 9 is
  the `IsGreatest` in `lemma6`, and Definition 11 is the quantity in `lemma7`.
