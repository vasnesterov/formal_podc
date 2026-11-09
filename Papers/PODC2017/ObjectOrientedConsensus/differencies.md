# Differences between the formalization and the paper

Paper: Afek, Aspnes, Cohen, Vainstein, *Object Oriented Consensus*, PODC 2017 (BA); full version (16 pp.).

## Mistakes (labelled)

1. **⚠️ Lemma 3 / §4.1: Algorithm 4 is not a valid conciliator, and Algorithm 2 with Algorithms 3–4 violates
   agreement.** A Byzantine king sends an arbitrary value. With "on commit: decide", an honest process can decide
   `0` in round 1 while others decide `1` in round 2 (`n = 4`, `t = 1`; `PhaseKing.template_disagreement`).
   Repaired: decide on a commit only in rounds `≥ t + 1`, with distinct kings in rounds `1..t+1`
   (`PhaseKing.repaired_agreement`, `repaired_termination`, `repaired_validity`). Lemma 3's eventual agreement
   (`lemma3_honest_king`) and persistence hold.
2. **🔧 Lemma 1 + Lemmas 4–5: Ben-Or composed with Algorithm 1 ("decide, then halt") does not terminate.**
   Halted processes stop sending, so the `n − t` waits of Algorithm 5 can block forever without a crash
   (`BenOr.halting_blocks`). Fix: decided processes keep participating, as the paper does for Phase-King.
   Lemma 1's safety is proved for both variants.
3. **🔧 Lemma 2, validity: Algorithm 3 can return `(adopt, 2)`**, even fault-free
   (`PhaseKing.lemma2_validity_false`). The paper's "validity" proof shows convergence instead. Corrected:
   the output is an honest input or `2` (`lemma2_validity_bot`). The fix "adopt the own input instead of `2`"
   gives a correct AC (`lemma2_fixed`).
4. **✏️ Lemma 1, validity** needs every reconciliator output to be valid. The definition only asks for this
   at the agreement point (footnote 1), but the proof assumes it. It is a hypothesis here (`Exec1.RecValid`).
5. **🔧 (proof gap) Lemma 5, coherence over adopt & commit.** The paper's inference "one live process broadcast
   ratify, so everybody received one" is wrong. The correct argument is the quorum intersection
   `(n − t) + (t + 1) > n` (`BenOr.Round.lemma5`).

## Modelling choices and imprecisions

- **Objects as round specifications.** Objects are specified per invocation round (invokers `I`, returners
  `O ⊆ I`), not as linearizable shared objects. "Termination" of an object (every non-crashed invoker returns)
  belongs to the concrete models: synchronous rounds for Phase-King, and `wait_completes_iff` for Ben-Or.
- **Byzantine object properties.** The paper states the object properties for "all processors". In the
  Byzantine setting we state them for the honest processes `H` (`I = O = H`), with convergence for
  unanimous honest inputs.
- **Lemma 1 termination** ("with probability 1, at some point all invoking processors receive the same value") is
  formalized deterministically: if weak agreement holds in round `m` (`Exec1.WeakAgreementAt`), all
  returners of round `m + 1` commit. The measure-theoretic step (some round succeeds with probability 1) is
  not formalized.
- **Lemma 3** claims "probabilistic agreement". The paper replaces it by eventual agreement at an honest king's
  round, and so do we. The paper also lists "coherence" for the conciliator, which is not a conciliator property.
- **Phase-King values** are `Fin 3`. A Byzantine king's message is any `Fin 3` value (a missing message is
  modelled as some value). Byzantine processes may send any `Option (Fin 3)` in the exchanges (`none` =
  nothing). The king of round `m` is any function `king : ℕ → P`. The paper uses `p_m`, which is undefined
  for `m > n`. Repaired theorems assume the kings of rounds `0..t` (0-based) are distinct.
- **Phase-King participation.** Every process runs every round, and an honest king broadcasts `min(1, σ)` even
  when it committed. In the literal Algorithm 2 a committing process does not call the conciliator, so a
  committed honest king would send nothing. Our reading favours the paper.
- **Algorithm 4** broadcasts `MIN(1, v)`. We use the king's adopt-commit output `σ`, as the proof of
  Lemma 3 requires.
- **Algorithm 5.** "received more than `n/2` `⟨1, v⟩`" and "`⟨2, v, ratify⟩`" bind `v` to the received value,
  following Aspnes' survey (`Finset.threshold?`). Ties cannot occur (`rat_unique`). Each wait is for exactly
  `n − t` messages from processes that sent one in that round of the protocol.
- **Ben-Or crash model.** A round is given by arbitrary views. A process that crashes during a broadcast is
  in `I` (or `I2`), and its message is in some views and not in others. This covers all asynchronous
  executions for safety.
- **Lemma 4.** The paper argues "any value has non-zero probability". We prove the deterministic fact behind
  it. The adopt/commit value of a round is the strict-majority value of that round's inputs, so it is fixed
  before any coin is flipped (`adopted_value_majority`). Coins equal to it (or to any common value if there is
  no majority) yield weak agreement (`lemma4_good_coins`). The probability bound `≥ 2^{-n}` per round is not
  formalized.
- **Algorithm 2** ("correctness proved similarly") is formalized at the specification level
  (`Exec2.agreement`, `Exec2.validity`, `Exec2.termination`). Its agreement and validity need the conciliator's
  validity (`Exec2.ConciliatorValid`), as in Aspnes' framework.
- **Not formalized.** Raft (§4.3, Lemmas 6–7): informal timing assumptions, and the paper concedes that
  Algorithm 10 lacks convergence. Section 5 (informal argument that AC is not enough; the claim that VAC can
  be implemented from two ACs is not shown in the paper).
