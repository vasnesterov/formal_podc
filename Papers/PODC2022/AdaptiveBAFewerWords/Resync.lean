import Papers.PODC2022.AdaptiveBAFewerWords.StrongBA

/-!
# Lemma 18 of [CKS22]: running a synchronous protocol from skewed start times

[CKS22] S. Cohen, I. Keidar, A. Spiegelman. *Make Every Word Count: Adaptive Byzantine Agreement with
Fewer Words.* PODC 2022; full version arXiv:2202.09123v2, Appendix B, Lemma 18.

A synchronous protocol `A` is started by every correct process at a local time `s_p`, the start
times being at most `δ` apart; rounds last `2δ`, so round `r` (counted from `0`) of `p` starts at
`t^p_r = s_p + 2δ·r` (`roundStart`), and a correct process sends its round-`r` messages at `t^p_r`.
Lemma 18 says that a round-`r` message of a correct process, with delay `≤ δ`, arrives at every
correct receiver `q` in the window `[t^q_r − δ, t^q_r + 2δ]` in which `q` accepts round-`r`
messages; in particular it has arrived when `q` ends round `r` at `t^q_{r+1} = t^q_r + 2δ`
(`lemma18`, `lemma18_processed`). Hence the correct processes behave as in a lock-step run.

What the lemma does *not* give (and the paper does not discuss):
* the windows of rounds `r` and `r + 1` overlap, and a message may arrive before its receiver
  starts the round; messages must carry round numbers and be buffered (`windows_overlap`);
* the adversary is stronger than the usual rushing adversary of a lock-step run: a Byzantine
  process may receive the round-`(r+1)` messages of an early starter and still deliver a
  round-`r` message to a late starter inside its round-`r` window (`skew_lookahead`). The black-box
  assumption on `A_fallback` (`FallbackSpec`) has to cover this stronger adversary.

`lemma18_alg5` instantiates the lemma with the start times of `A_fallback` in Algorithm 5
(Lemma 25).
-/

namespace Podc.AdaptiveBAFewerWords.StrongBA

/-- Local start time of round `r` (from `0`) at a process that started the protocol at `s`, with
rounds of length `2δ`. -/
def roundStart (δ s r : ℕ) : ℕ := s + 2 * δ * r

/-- **Lemma 18** of [CKS22] (timing content). If the start times of `p` and `q` are at most `δ`
apart and `p`'s round-`r` message (sent at `t^p_r`) has delay at most `δ`, it arrives at `q` within
`q`'s window `[t^q_r − δ, t^q_r + 2δ]`. -/
theorem lemma18 {δ sp sq r ta : ℕ} (hpq : sp ≤ sq + δ) (hqp : sq ≤ sp + δ)
    (h₁ : roundStart δ sp r ≤ ta) (h₂ : ta ≤ roundStart δ sp r + δ) :
    roundStart δ sq r ≤ ta + δ ∧ ta ≤ roundStart δ sq r + 2 * δ := by
  unfold roundStart at *
  constructor <;> omega

/-- Consequence of Lemma 18: the message has arrived by the time `q` ends round `r`, i.e. starts
round `r + 1`, so `q`'s round-`(r+1)` messages can depend on it, as in a lock-step run. -/
theorem lemma18_processed {δ sp sq r ta : ℕ} (hpq : sp ≤ sq + δ) (hqp : sq ≤ sp + δ)
    (h₁ : roundStart δ sp r ≤ ta) (h₂ : ta ≤ roundStart δ sp r + δ) :
    ta ≤ roundStart δ sq (r + 1) := by
  have := (lemma18 hpq hqp h₁ h₂).2
  unfold roundStart at *
  rw [Nat.mul_succ]
  omega

/-- The windows overlap: with equal start times and delay `0`, a round-`(r+1)` message of `p`
arrives inside `q`'s round-`r` window (at its right end), so round numbers are needed. -/
theorem windows_overlap (δ s r : ℕ) :
    roundStart δ s r ≤ roundStart δ s (r + 1) + δ ∧
      roundStart δ s (r + 1) ≤ roundStart δ s r + 2 * δ := by
  unfold roundStart
  rw [Nat.mul_succ]
  constructor <;> omega

/-- **The resynchronised run is not a lock-step run with a rushing adversary.** Let `q` start `δ`
after `p`. A Byzantine process `b` receives `p`'s round-`(r+1)` message at the time `p` sends it
(delay `0`), and only then sends a round-`r` message to `q`, with delay `δ`. It arrives inside
`q`'s round-`r` window, so `b`'s round-`r` message to `q` may depend on correct round-`(r+1)`
messages. -/
theorem skew_lookahead (δ sp r : ℕ) :
    let sq := sp + δ
    -- `b` sends at the time it receives `p`'s round-`(r+1)` message
    let tb := roundStart δ sp (r + 1)
    -- arrival at `q`
    let ta := tb + δ
    sp ≤ sq + δ ∧ sq ≤ sp + δ ∧ roundStart δ sq r ≤ ta + δ ∧ ta ≤ roundStart δ sq r + 2 * δ := by
  simp only [roundStart]
  rw [Nat.mul_succ]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

variable {t : ℕ} {inp : Proc t → Bool} {A : Adversary t}

/-- Lemma 18 applied to `A_fallback` in Algorithm 5: by Lemma 25 the correct processes start it
at most `δ` apart, so (rounds of `2δ`) every round-`r` message between correct processes arrives in
the receiver's round-`r` window. -/
theorem lemma18_alg5 {δ : ℕ} (hA : AdvValid inp A δ) {p q : Proc t} (hp : p ∈ correct A)
    (hq : q ∈ correct A) {sp sq : ℕ} (hsp : fbStart inp A δ p = some sp)
    (hsq : fbStart inp A δ q = some sq) {r ta : ℕ}
    (h₁ : roundStart δ sp r ≤ ta) (h₂ : ta ≤ roundStart δ sp r + δ) :
    roundStart δ sq r ≤ ta + δ ∧ ta ≤ roundStart δ sq r + 2 * δ := by
  have h := (lemma25 hA ⟨p, hp, sp, hsp⟩).2
  exact lemma18 (h p hp q hq sp sq hsp hsq) (h q hq p hp sq sp hsq hsp) h₁ h₂

end Podc.AdaptiveBAFewerWords.StrongBA
