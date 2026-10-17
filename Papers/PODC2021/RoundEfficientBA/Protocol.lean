import Papers.PODC2021.RoundEfficientBA.Expansion
import Cslib.Computability.Distributed.Byzantine.LockStep.Agreement

/-!
# The `r`-round Proxcensus protocol for `t < n/3` (Corollary 3.3) and fixed-round BA (Cor. 3.8)

The protocol `proxProtocol t θ r` runs in CSLib's synchronous lock-step model
(`Cslib.Byzantine.LockStep`) on the complete network: every party starts with the output `(x, 0)`
of the trivial `Prox_2` (its input with grade `0`), and in each of `r` rounds echoes its current
output to everybody and applies the expansion step (`expandOut`) to the echoes it received
(including its own), turning `Prox_{2^k+1}` into `Prox_{2^{k+1}+1}`. After `r` rounds it decides.

* `proxProtocol_spec` (**Corollary 3.3, corrected**): with threshold `θ = t + 1`, for every
  `n > 3t` and every static Byzantine adversary corrupting at most `t` parties, the honest outputs
  form a `(2^r + 1)`-slot Proxcensus after `r` rounds (perfect security, deterministic).
* `proxProtocol_spec_paper`: the paper's protocol (threshold `n - 2t`) for `n = 3t + 1`.
* `ba_third` (**Corollary 3.8, `t < n/3`, corrected**): `κ` rounds of the protocol followed by one
  ideal `2^κ`-valued coin and the extraction function: binary BA with validity for every coin and
  error probability at most `2^{-κ}`; `κ + 1` rounds.

The adversary is static and deterministic (an arbitrary function `adv` of round, sender and
receiver); for a deterministic protocol this covers rushing, and an adaptive adversary is
simulated by statically corrupting the parties it corrupts by the end of the execution. In the BA
theorem the coin is drawn after the `κ` rounds (it is unknown to the adversary before the coin
round, as for the paper's ideal coin), and the adversary may still corrupt further parties after
seeing it (`Hc`).
-/

namespace RoundEfficientBA

open Cslib.Byzantine.LockStep

variable {P D : Type*} [Fintype P] [DecidableEq P] [Fintype D] [LinearOrder D]

/-! ### The protocol -/

/-- The inbox `ib` completed with the party's own echo `own`. -/
def ownView (p : P) (own : D × ℕ) (ib : Inbox P (D × ℕ)) : P → Option (D × ℕ) :=
  fun q => if q = p then some own else ib q

/-- Processing the inboxes of rounds `k, k+1, …` starting from the current output `cur` (an output
of `Prox_{2^k+1}`). -/
def stepState (t θ : ℕ) (p : P) : ℕ → D × ℕ → History P (D × ℕ) → D × ℕ
  | _, cur, [] => cur
  | k, cur, ib :: rest =>
    stepState t θ p (k + 1)
      (expandOut (2 ^ k + 1) (Fintype.card P) t θ cur (viewCnt (ownView p cur ib))) rest

/-- The current Proxcensus output of `p` with input `x` after history `h`. -/
def proxState (t θ : ℕ) (p : P) (x : D) (h : History P (D × ℕ)) : D × ℕ :=
  stepState t θ p 0 (x, 0) h

/-- **Protocol `Prox_{2^r+1}`** for `t < n/3` (Section 3.3.1, iterated `r` times from `Prox_2`):
echo the current output every round, decide after `r` rounds. -/
def proxProtocol (t θ r : ℕ) : Protocol P D (D × ℕ) (D × ℕ) where
  send p x h _ := some (proxState t θ p x h)
  decide p x h := if h.length = r then some (proxState t θ p x h) else none

/-! ### Unfolding the rounds -/

lemma stepState_append (t θ : ℕ) (p : P) (k : ℕ) (cur : D × ℕ) (l : History P (D × ℕ))
    (ib : Inbox P (D × ℕ)) :
    stepState t θ p k cur (l ++ [ib]) =
      expandOut (2 ^ (k + l.length) + 1) (Fintype.card P) t θ (stepState t θ p k cur l)
        (viewCnt (ownView p (stepState t θ p k cur l) ib)) := by
  induction l generalizing k cur with
  | nil => simp [stepState]
  | cons ib' l ih =>
    simp only [List.cons_append, stepState, List.length_cons]
    rw [ih]
    congr 3
    omega

variable (t θ r : ℕ) (sc : Scenario P D (D × ℕ))

/-- The output of `p` after `k` rounds of the run. -/
noncomputable def roundOut (k : ℕ) (p : P) : D × ℕ :=
  proxState t θ p (sc.input p) (hist ⊤ (proxProtocol t θ r) sc k p)

open Classical in
/-- What an honest party `p` "sees" in round `k`: honest parties' current outputs (its own
included) and the Byzantine messages. -/
lemma roundOut_succ (hrel : sc.Reliable) (k : ℕ) (p : P) (hp : p ∉ sc.byz) :
    roundOut t θ r sc (k + 1) p =
      expandOut (2 ^ k + 1) (Fintype.card P) t θ (roundOut t θ r sc k p)
        (viewCnt fun q => if q ∈ sc.byz then sc.adv k q p else some (roundOut t θ r sc k q)) := by
  classical
  unfold roundOut proxState
  rw [hist_succ, stepState_append, length_hist, Nat.zero_add]
  congr 2
  funext q
  unfold ownView deliver
  by_cases hqp : q = p
  · subst hqp; simp [proxProtocol, proxState, hp]
  · have hadj : (⊤ : SimpleGraph P).Adj q p := hqp
    simp only [hqp, if_false, hadj, if_true]
    by_cases hq : q ∈ sc.byz
    · simp [hq]
    · simp [hq, hrel k q p, proxProtocol, proxState]

lemma roundOut_zero (p : P) : roundOut t θ r sc 0 p = (sc.input p, 0) := by
  simp [roundOut, proxState, stepState]

/-! ### Corollary 3.3 -/

/-- The honest parties as a `Finset`. -/
noncomputable def honestF : Finset P := by
  classical exact Finset.univ.filter fun p => p ∉ sc.byz

omit [DecidableEq P] in
lemma mem_honestF {p : P} : p ∈ honestF sc ↔ p ∉ sc.byz := by
  classical
  unfold honestF; simp

omit [DecidableEq P] in
lemma coe_honestF : (honestF sc : Set P) = sc.honest := by
  ext p; simp [mem_honestF, Scenario.honest]

lemma card_compl_honestF : (Finset.univ \ honestF sc).card = sc.byz.ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext p; simp [mem_honestF]

lemma isProx_two (x : P → D) (H : Set P) : IsProx 2 x H (fun p => (x p, 0)) := by
  refine ⟨fun p _ => by simp [maxGrade], fun v hv p hp => ?_, fun p _ q _ => ?_⟩
  · simp [hv p hp, maxGrade]
  · simp [ProxCons]

open Classical in
/-- Main induction: after `k` rounds the honest outputs form a `(2^k + 1)`-slot Proxcensus. -/
theorem roundOut_isProx (ht : 3 * t < Fintype.card P) (hB : sc.byz.ncard ≤ t)
    (hrel : sc.Reliable) (k : ℕ) :
    IsProx (2 ^ k + 1) sc.input sc.honest (roundOut t (t + 1) r sc k) := by
  induction k with
  | zero =>
    have h0 : roundOut t (t + 1) r sc 0 = fun p => (sc.input p, 0) :=
      funext (roundOut_zero t (t + 1) r sc)
    rw [h0]
    simpa using isProx_two sc.input sc.honest
  | succ k ih =>
    have hcard : (honestF sc).card + (Finset.univ \ honestF sc).card = Fintype.card P := by
      rw [add_comm, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    have hf : (Finset.univ \ honestF sc).card ≤ t := by rw [card_compl_honestF]; exact hB
    rw [← coe_honestF] at ih ⊢
    have hstep := expand_isProx (s := 2 ^ k + 1) (Nat.le_add_left 1 _) ht hf hcard ih
      (fun p => viewCnt fun q => if q ∈ sc.byz then sc.adv k q p
        else some (roundOut t (t + 1) r sc k q))
      (fun p _ A => (viewCnt_bounds (fun q hq => by
          rw [mem_honestF] at hq; simp [hq]) A).1)
      (fun p _ A => (viewCnt_bounds (fun q hq => by
          rw [mem_honestF] at hq; simp [hq]) A).2)
    have he : 2 * (2 ^ k + 1) - 1 = 2 ^ (k + 1) + 1 := by rw [pow_succ]; omega
    rw [he] at hstep
    refine ⟨fun p hp => ?_, fun v hv p hp => ?_, fun p hp q hq => ?_⟩
    · rw [roundOut_succ t (t + 1) r sc hrel k p ((mem_honestF sc).1 hp)]
      exact hstep.grade_le p hp
    · rw [roundOut_succ t (t + 1) r sc hrel k p ((mem_honestF sc).1 hp)]
      exact hstep.validity v hv p hp
    · rw [roundOut_succ t (t + 1) r sc hrel k p ((mem_honestF sc).1 hp),
        roundOut_succ t (t + 1) r sc hrel k q ((mem_honestF sc).1 hq)]
      exact hstep.consistency p hp q hq

/-- The status of `p` after `k` rounds. -/
lemma status_proxProtocol (k : ℕ) (p : P) :
    status ⊤ (proxProtocol t θ r) sc k p =
      if k = r then some (roundOut t θ r sc k p) else none := by
  simp [status, proxProtocol, roundOut]

lemma decides_proxProtocol_iff (p : P) (o : D × ℕ) :
    Decides ⊤ (proxProtocol t θ r) sc p o ↔ o = roundOut t θ r sc r p := by
  constructor
  · rintro ⟨k, hk, -⟩
    rw [status_proxProtocol] at hk
    split_ifs at hk with h
    · subst h; exact (Option.some_injective _ hk).symm
  · rintro rfl
    refine ⟨r, by rw [status_proxProtocol, if_pos rfl], fun k hk => ?_⟩
    rw [status_proxProtocol, if_neg (by omega)]

/-- The Proxcensus specification as a lock-step `Spec`: every honest party decides, and the
honest decisions satisfy `s`-slot Proxcensus. -/
def ProxSpec (s : ℕ) : Spec P D (D × ℕ) := fun x H dec =>
  (∀ p ∈ H, ∃ o, dec p o) ∧ ∀ out : P → D × ℕ, (∀ p ∈ H, dec p (out p)) → IsProx s x H out

/-- **Corollary 3.3 (corrected threshold).** Let `n > 3t`. For every `r ≥ 0`, `proxProtocol t (t+1) r`
achieves `(2^r + 1)`-slot Proxcensus against any (static, deterministic) adversary corrupting at
most `t` parties, with perfect security, and all honest parties decide in round `r`. -/
theorem proxProtocol_spec (ht : 3 * t < Fintype.card P) (hB : sc.byz.ncard ≤ t)
    (hrel : sc.Reliable) :
    ProxSpec (2 ^ r + 1) sc.input sc.honest (Decides ⊤ (proxProtocol t (t + 1) r) sc) ∧
      TerminatesBy ⊤ (proxProtocol t (t + 1) r) sc r := by
  have hP := roundOut_isProx t r sc ht hB hrel r
  refine ⟨⟨fun p _ => ⟨_, (decides_proxProtocol_iff _ _ _ _ p _).2 rfl⟩, fun out hout => ?_⟩,
    fun p _ => ⟨r, le_rfl, _, by rw [status_proxProtocol, if_pos rfl]⟩⟩
  have : ∀ p ∈ sc.honest, out p = roundOut t (t + 1) r sc r p :=
    fun p hp => (decides_proxProtocol_iff _ _ _ _ p _).1 (hout p hp)
  refine ⟨fun p hp => ?_, fun v hv p hp => ?_, fun p hp q hq => ?_⟩
  · rw [this p hp]; exact hP.grade_le p hp
  · rw [this p hp]; exact hP.validity v hv p hp
  · rw [this p hp, this q hq]; exact hP.consistency p hp q hq

/-- **Corollary 3.3 as stated, for `n = 3t + 1`**: the paper's threshold `n - 2t` equals `t + 1`. -/
theorem proxProtocol_spec_paper (hn : Fintype.card P = 3 * t + 1) (hB : sc.byz.ncard ≤ t)
    (hrel : sc.Reliable) :
    ProxSpec (2 ^ r + 1) sc.input sc.honest
        (Decides ⊤ (proxProtocol t (Fintype.card P - 2 * t) r) sc) ∧
      TerminatesBy ⊤ (proxProtocol t (Fintype.card P - 2 * t) r) sc r := by
  have : Fintype.card P - 2 * t = t + 1 := by omega
  rw [this]
  exact proxProtocol_spec t r sc (by omega) hB hrel

end RoundEfficientBA

/-! ### Corollary 3.8, `t < n/3` -/

namespace RoundEfficientBA

open Cslib.Byzantine.LockStep

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **Corollary 3.8 (`t < n/3`), with the corrected threshold.** Binary BA from `κ` rounds of
`proxProtocol` (yielding `Prox_{2^κ+1}`) followed by one ideal coin uniform in `[1, 2^κ]` and the
extraction function, `κ + 1` rounds in total:
* validity: if all honest inputs are `b`, every honest party outputs `b` for every coin value;
* agreement except with probability `≤ 2^{-κ}` over the coin, even if the adversary corrupts
  further parties after seeing the coin (honest set `Hc i ⊆ honest` for coin `i + 1`). -/
theorem ba_third (t κ : ℕ) (sc : Scenario P Bool (Bool × ℕ)) (ht : 3 * t < Fintype.card P)
    (hB : sc.byz.ncard ≤ t) (hrel : sc.Reliable) :
    (∀ b, (∀ p ∈ sc.honest, sc.input p = b) → ∀ c, 1 ≤ c → c ≤ 2 ^ κ →
        ∀ p ∈ sc.honest, extract (2 ^ κ + 1) (roundOut t (t + 1) κ sc κ p) c = b) ∧
      ∀ Hc : Fin (2 ^ κ) → Set P, (∀ i, Hc i ⊆ sc.honest) →
        (PMF.uniformOfFintype (Fin (2 ^ κ))).toOuterMeasure
            {i | ∃ p ∈ Hc i, ∃ q ∈ Hc i,
              extract (2 ^ κ + 1) (roundOut t (t + 1) κ sc κ p) (i + 1) ≠
                extract (2 ^ κ + 1) (roundOut t (t + 1) κ sc κ q) (i + 1)}
          ≤ 1 / (2 ^ κ : ℕ) := by
  have hP := roundOut_isProx t κ sc ht hB hrel κ
  refine ⟨fun b hb c hc1 hc2 => iter_validity hP b hb c hc1 (by omega), fun Hc hHc => ?_⟩
  have : NeZero (2 ^ κ) := ⟨by positivity⟩
  exact iter_error_le (Nat.add_sub_cancel _ _).symm hP.grade_le hP.consistency Hc hHc

end RoundEfficientBA

namespace RoundEfficientBA

open Cslib.Byzantine.LockStep

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- **Corollary 3.8 (`t < n/3`) as stated, for `n = 3t + 1`** (paper's threshold `n - 2t`). -/
theorem ba_third_paper (t κ : ℕ) (sc : Scenario P Bool (Bool × ℕ))
    (hn : Fintype.card P = 3 * t + 1) (hB : sc.byz.ncard ≤ t) (hrel : sc.Reliable) :
    (∀ b, (∀ p ∈ sc.honest, sc.input p = b) → ∀ c, 1 ≤ c → c ≤ 2 ^ κ →
        ∀ p ∈ sc.honest,
          extract (2 ^ κ + 1) (roundOut t (Fintype.card P - 2 * t) κ sc κ p) c = b) ∧
      ∀ Hc : Fin (2 ^ κ) → Set P, (∀ i, Hc i ⊆ sc.honest) →
        (PMF.uniformOfFintype (Fin (2 ^ κ))).toOuterMeasure
            {i | ∃ p ∈ Hc i, ∃ q ∈ Hc i,
              extract (2 ^ κ + 1) (roundOut t (Fintype.card P - 2 * t) κ sc κ p) (i + 1) ≠
                extract (2 ^ κ + 1) (roundOut t (Fintype.card P - 2 * t) κ sc κ q) (i + 1)}
          ≤ 1 / (2 ^ κ : ℕ) := by
  rw [show Fintype.card P - 2 * t = t + 1 by omega]
  exact ba_third t κ sc (by omega) hB hrel

end RoundEfficientBA
