import Papers.PODC2015.SynchronousCounting.Boost
import Podc.Foundations.Data.Nat.Log

/-!
# The recursive construction (Section 4 of Lenzen–Rybicki–Suomela, PODC 2015)

We apply Theorem 1 (`SynchronousCounting.boost`) recursively, with explicit (non-asymptotic)
constants.

* `achievable_one`: the trivial `c`-counter on one node (base case, §4.1).
* `corollary1`, `corollary1_bounds`: optimal resilience `n = 3f + 1` (Corollary 1).
* `achievable_iterate`: a generic iteration of `boost` with `k = 2h` blocks and `F = f·h` along a
  list of values `h` (listed top-first). Every intermediate counter counts modulo the
  `boostTime` required by the next level.
* `theorem3`, `theorem3_asymptotic`: the varying-blocks construction of §4.3 (Theorem 3):
  resilience `f = n^{1-o(1)}`, stabilisation time `O(f)`, `O(log² f / log log f + log C)` state bits.
* `theorem2`, `corollary2`: the fixed-blocks construction of §4.2 (Theorem 2, Corollary 2), with
  `h = 2^a`.

Notes on the paper's computations (all asymptotic claims survive):
* Theorem 1 costs `3(F+2)(2m)^k` per step; the proof of Corollary 1 writes `(3f+2)(2m)^k`, and the
  proof of Theorem 2 writes `h^k` (`h = k/2`) instead of `(2m)^k = k^k`.
* In §4.3 the paper computes `n/f = 2^{2(2^P-1)}`, which corresponds to `R_p = 2·2^{P-p}` and drops
  the factor `4`; with the stated `R_p = 2k_p = 8·2^{P-p}` one gets `n/f = 2^{8·2^P-6}` (`thm3N`).
* The constructions only produce the special network sizes `n = 3f+1`, `n = 4(2h)^L`, `thm3N P`.
-/

namespace SynchronousCounting

open Cslib.Byzantine.SyncCounting

/-! ### The base case -/

/-- The trivial `c`-counter on a single node: the state is the counter value, incremented every
round. -/
def trivialCounter (c : ℕ) (hc : 0 < c) : Algorithm (Fin 1) (Fin c) c where
  g i m := ⟨((m i : ℕ) + 1) % c, Nat.mod_lt _ hc⟩
  h _ s := s

/-- §4.1: the trivial `0`-resilient `c`-counter on one node, stabilising in `0` rounds and using
`⌈log₂ c⌉` bits. -/
theorem achievable_one {c : ℕ} (hc : 0 < c) : Achievable 1 0 c 0 (Nat.clog 2 c) := by
  refine ⟨Fin c, inferInstance, ⟨⟨0, hc⟩⟩, trivialCounter c hc, ?_, ?_⟩
  · simpa using Nat.le_pow_clog (by norm_num) c
  · intro F hF x hx
    have hF0 : F = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hF)
    subst hF0
    refine ⟨x 0 0, fun r i _ => ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    induction r with
    | zero => simp [trivialCounter, Nat.mod_eq_of_lt (x 0 0).isLt]
    | succ r ih =>
      obtain ⟨m, hm, hstep⟩ := hx r 0 (Finset.notMem_empty _)
      have h0 := hm 0 (Finset.notMem_empty _)
      simp only [trivialCounter, zero_add] at ih ⊢
      rw [hstep]
      simp only [trivialCounter, h0, ih]
      rw [← add_assoc, Nat.mod_add_mod]

/-! ### Corollary 1: optimal resilience -/

/-- Corollary 1 (exact form): for `f ≥ 1` and `C > 1` there is an `f`-resilient `C`-counter on
`3f + 1` nodes. It is Theorem 1 applied to the trivial one-node counter with `k = 3f + 1` blocks
of one node each and `F = f`. -/
theorem corollary1 {f C : ℕ} (hf : 1 ≤ f) (hC : 1 < C) :
    Achievable (3 * f + 1) f C (boostTime (3 * f + 1) f)
      (Nat.clog 2 (boostTime (3 * f + 1) f) + Nat.clog 2 (C + 1) + 1) := by
  have h1 := achievable_one (c := boostTime (3 * f + 1) f)
    (Nat.mul_pos (by positivity) (pow_pos (by simp only [half]; omega) _))
  have := boost h1 (k := 3 * f + 1) (F := f) (C := C) (by omega) (by simp [half]; omega) hC
    dvd_rfl (by norm_num) (by omega)
  simpa using this

lemma two_mul_half_le (k : ℕ) : 2 * half k ≤ k + 1 := by simp only [half]; omega

/-- The time bound of Corollary 1 is `f^{O(f)}`: `3(f+2)(2m)^{3f+1} ≤ (3f+2)^{3f+3}`. -/
lemma boostTime_corollary1_le {f : ℕ} (hf : 1 ≤ f) :
    boostTime (3 * f + 1) f ≤ (3 * f + 2) ^ (3 * f + 3) := by
  have h1 : (2 * half (3 * f + 1)) ^ (3 * f + 1) ≤ (3 * f + 2) ^ (3 * f + 1) :=
    Nat.pow_le_pow_left (two_mul_half_le _) _
  have h2 : 3 * (f + 2) ≤ (3 * f + 2) ^ 2 := by nlinarith
  calc boostTime (3 * f + 1) f = 3 * (f + 2) * (2 * half (3 * f + 1)) ^ (3 * f + 1) := rfl
    _ ≤ (3 * f + 2) ^ 2 * (3 * f + 2) ^ (3 * f + 1) := Nat.mul_le_mul h2 h1
    _ = (3 * f + 2) ^ (3 * f + 3) := by rw [← pow_add]; ring_nf

/-- Corollary 1 with explicit bounds: an `f`-resilient `C`-counter on `3f + 1` nodes stabilising in
`(3f+2)^{3f+3} = f^{O(f)}` rounds with `(3f+3)⌈log₂(3f+2)⌉ + ⌈log₂(C+1)⌉ + 1 = O(f log f + log C)`
state bits. -/
theorem corollary1_bounds {f C : ℕ} (hf : 1 ≤ f) (hC : 1 < C) :
    Achievable (3 * f + 1) f C ((3 * f + 2) ^ (3 * f + 3))
      ((3 * f + 3) * Nat.clog 2 (3 * f + 2) + Nat.clog 2 (C + 1) + 1) := by
  refine (corollary1 hf hC).mono (boostTime_corollary1_le hf) ?_
  have := (Nat.clog_mono_right 2 (boostTime_corollary1_le hf)).trans (Nat.clog_pow_le_mul _ _ _)
  omega

/-! ### Iterating Theorem 1 with an even number of blocks -/

@[simp] lemma half_two_mul (h : ℕ) : half (2 * h) = h := by simp only [half]; omega

/-- Stabilisation time after applying `boost` along `hs` (top-first: the head of the list is the
last step), with `k = 2h` blocks and `F = f·h` at each step, starting from a base counter with
resilience `f₀` and time `T₀`. -/
def iterTime (T₀ f₀ : ℕ) : List ℕ → ℕ
  | [] => T₀
  | h :: hs => iterTime T₀ f₀ hs + boostTime (2 * h) (f₀ * (h :: hs).prod)

/-- State bits (excluding the `⌈log₂(C+1)⌉` bits of the final output) after applying `boost`
along `hs`; the counter of every intermediate level counts modulo the `boostTime` of the next
level. -/
def iterSpace (S₀ f₀ : ℕ) : List ℕ → ℕ
  | [] => S₀
  | h :: hs => iterSpace S₀ f₀ hs + Nat.clog 2 (boostTime (2 * h) (f₀ * (h :: hs).prod) + 1) + 1

lemma prod_map_two_mul (hs : List ℕ) :
    (hs.map (2 * ·)).prod = 2 ^ hs.length * hs.prod := by
  induction hs with
  | nil => simp
  | cons h hs ih => simp only [List.map_cons, List.prod_cons, ih, List.length_cons, pow_succ]; ring

lemma prod_pos_of_two_le {hs : List ℕ} (hh : ∀ h ∈ hs, 2 ≤ h) : 0 < hs.prod :=
  List.prod_pos fun h hm => by have := hh h hm; omega

/-- Generic iteration of Theorem 1 (`boost`) with `k = 2h ≥ 4` blocks and `F = f·h` at every step,
along the list `hs` (top-first). The base family must provide `C`-counters for every `C > 1`
with time `T₀` and `S₀ + ⌈log₂(C+1)⌉` bits, and satisfy `3f₀ < n₀`. -/
theorem achievable_iterate {n₀ f₀ T₀ S₀ : ℕ}
    (hbase : ∀ C, 1 < C → Achievable n₀ f₀ C T₀ (S₀ + Nat.clog 2 (C + 1)))
    (hf : 3 * f₀ < n₀) (hs : List ℕ) (hh : ∀ h ∈ hs, 2 ≤ h) {C : ℕ} (hC : 1 < C) :
    Achievable (n₀ * 2 ^ hs.length * hs.prod) (f₀ * hs.prod) C (iterTime T₀ f₀ hs)
      (iterSpace S₀ f₀ hs + Nat.clog 2 (C + 1)) := by
  induction hs generalizing C with
  | nil => simpa [iterTime, iterSpace] using hbase C hC
  | cons h hs ih =>
    have hh' : ∀ h ∈ hs, 2 ≤ h := fun x hx => hh x (List.mem_cons_of_mem _ hx)
    have h2 : 2 ≤ h := hh h List.mem_cons_self
    have hp := prod_pos_of_two_le hh'
    set c := boostTime (2 * h) (f₀ * (h :: hs).prod) with hc
    have hc1 : 1 < c := by
      have : 0 < (2 * h) ^ (2 * h) := pow_pos (by omega) _
      have h6 : 6 ≤ 3 * (f₀ * (h :: hs).prod + 2) := by omega
      simp only [hc, boostTime, half_two_mul]
      calc 1 < 6 * 1 := by norm_num
        _ ≤ _ := Nat.mul_le_mul h6 this
    have hlow := ih hh' hc1
    have hinv : 3 * (f₀ * hs.prod) < n₀ * 2 ^ hs.length * hs.prod := by
      have : 1 ≤ 2 ^ hs.length := Nat.one_le_two_pow
      calc 3 * (f₀ * hs.prod) = 3 * f₀ * hs.prod := by ring
        _ < n₀ * hs.prod := Nat.mul_lt_mul_of_pos_right hf hp
        _ ≤ n₀ * 2 ^ hs.length * hs.prod :=
          Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ this)
    have := boost hlow (k := 2 * h) (F := f₀ * (h :: hs).prod) (C := C) (by omega)
      (by simp only [half_two_mul, List.prod_cons]; nlinarith) hC dvd_rfl (by omega)
      (by have := Nat.mul_lt_mul_of_pos_left hinv (show 0 < h by omega)
          simp only [List.prod_cons]
          calc 3 * (f₀ * (h * hs.prod)) = h * (3 * (f₀ * hs.prod)) := by ring
            _ < h * (n₀ * 2 ^ hs.length * hs.prod) := this
            _ ≤ 2 * h * (n₀ * 2 ^ hs.length * hs.prod) := Nat.mul_le_mul_right _ (by omega))
    have e1 : 2 * h * (n₀ * 2 ^ hs.length * hs.prod) =
        n₀ * 2 ^ (h :: hs).length * (h :: hs).prod := by
      simp only [List.length_cons, List.prod_cons, pow_succ]; ring
    rw [e1] at this
    refine this.mono le_rfl ?_
    simp only [iterSpace, ← hc]
    omega

/-! ### Generic bounds for the iteration -/

/-- `∑` over the steps of `(product of the h's at and below the step) · (2h)^{2h}`; the time of
the iteration is at most `T₀ + 9 f₀ · weight hs` (`iterTime_le`). -/
def weight : List ℕ → ℕ
  | [] => 0
  | h :: hs => (h :: hs).prod * (2 * h) ^ (2 * h) + weight hs

lemma iterTime_le {T₀ f₀ : ℕ} (hf₀ : 1 ≤ f₀) (hs : List ℕ) (hh : ∀ h ∈ hs, 2 ≤ h) :
    iterTime T₀ f₀ hs ≤ T₀ + 9 * f₀ * weight hs := by
  induction hs with
  | nil => simp [iterTime, weight]
  | cons h hs ih =>
    have hh' : ∀ h ∈ hs, 2 ≤ h := fun x hx => hh x (List.mem_cons_of_mem _ hx)
    have hp := prod_pos_of_two_le hh
    have hF : 0 < f₀ * (h :: hs).prod := Nat.mul_pos hf₀ hp
    have key : boostTime (2 * h) (f₀ * (h :: hs).prod) ≤
        9 * f₀ * ((h :: hs).prod * (2 * h) ^ (2 * h)) := by
      simp only [boostTime, half_two_mul]
      have : 3 * (f₀ * (h :: hs).prod + 2) ≤ 9 * (f₀ * (h :: hs).prod) := by omega
      calc _ ≤ 9 * (f₀ * (h :: hs).prod) * (2 * h) ^ (2 * h) := Nat.mul_le_mul_right _ this
        _ = _ := by ring
    simp only [iterTime, weight]
    have := ih hh'
    nlinarith

lemma iterSpace_le {S₀ f₀ H M : ℕ} (hf₀ : 1 ≤ f₀) (hs : List ℕ)
    (hh : ∀ h ∈ hs, 2 ≤ h ∧ h ≤ H) (hM : f₀ * hs.prod ≤ M) :
    iterSpace S₀ f₀ hs ≤ S₀ + hs.length * (Nat.clog 2 (16 * M * (2 * H) ^ (2 * H)) + 1) := by
  induction hs with
  | nil => simp [iterSpace]
  | cons h hs ih =>
    have hh' : ∀ x ∈ hs, 2 ≤ x ∧ x ≤ H := fun x hx => hh x (List.mem_cons_of_mem _ hx)
    obtain ⟨h2, hH⟩ := hh h List.mem_cons_self
    have hp := prod_pos_of_two_le (fun x hx => (hh x hx).1)
    have hp' : hs.prod ≤ (h :: hs).prod := by
      rw [List.prod_cons]; exact Nat.le_mul_of_pos_left _ (by omega)
    have hM' : f₀ * hs.prod ≤ M := le_trans (Nat.mul_le_mul_left _ hp') hM
    have hX : (2 * h) ^ (2 * h) ≤ (2 * H) ^ (2 * H) :=
      le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
    have hX1 : 1 ≤ (2 * h) ^ (2 * h) := Nat.one_le_pow _ _ (by omega)
    have hF : 1 ≤ f₀ * (h :: hs).prod := Nat.mul_pos hf₀ hp
    have key : boostTime (2 * h) (f₀ * (h :: hs).prod) + 1 ≤ 16 * M * (2 * H) ^ (2 * H) := by
      simp only [boostTime, half_two_mul]
      have e1 : 3 * (f₀ * (h :: hs).prod + 2) * (2 * h) ^ (2 * h) + 1 ≤
          16 * (f₀ * (h :: hs).prod) * (2 * h) ^ (2 * h) := by nlinarith
      exact e1.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hX)
    simp only [iterSpace, List.length_cons]
    have := ih hh' hM'
    have := Nat.clog_mono_right 2 key
    nlinarith

/-! ### Theorem 3: varying the number of blocks -/

/-- The steps (top-first) of the phases with `h = 2^(a+1), 2^(a+2), …, 2^(a+P)`. The phase with
`h = 2^(a+1)`, i.e. with `k = 2h = 2^(a+2)` blocks, consists of `R = 2k = 2^(a+3)` steps. The
construction of Theorem 3 with `P` phases is `phases 0 P`: its top phase uses `k = 4` blocks and
its bottom phase `k = 2^(P+1) = 4 · 2^(P-1)` blocks. -/
def phases : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, P + 1 => List.replicate (2 ^ (a + 3)) (2 ^ (a + 1)) ++ phases (a + 1) P

/-- `log₂` of the product of `phases a P`. -/
def phaseExp : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, P + 1 => (a + 1) * 2 ^ (a + 3) + phaseExp (a + 1) P

lemma prod_phases (a P : ℕ) : (phases a P).prod = 2 ^ phaseExp a P := by
  induction P generalizing a with
  | zero => simp [phases, phaseExp]
  | succ P ih =>
    simp only [phases, phaseExp, List.prod_append, List.prod_replicate, ih, pow_add]
    ring

lemma phaseExp_closed (a P : ℕ) :
    phaseExp a P + a * 2 ^ (a + 3) + 2 ^ (a + P + 3) = (a + P) * 2 ^ (a + P + 3) + 2 ^ (a + 3) := by
  induction P generalizing a with
  | zero => simp [phaseExp]
  | succ P ih =>
    have := ih (a + 1)
    simp only [phaseExp]
    rw [show a + 1 + P + 3 = a + (P + 1) + 3 by ring, show a + 1 + 3 = a + 3 + 1 by ring,
      pow_succ] at this
    nlinarith

lemma length_phases (a P : ℕ) : (phases a P).length + 2 ^ (a + 3) = 2 ^ (a + P + 3) := by
  induction P generalizing a with
  | zero => simp [phases]
  | succ P ih =>
    have := ih (a + 1)
    simp only [phases, List.length_append, List.length_replicate]
    rw [show a + 1 + P + 3 = a + (P + 1) + 3 by ring, show a + 1 + 3 = a + 3 + 1 by ring,
      pow_succ] at this
    omega

lemma mem_phases {a P h : ℕ} (hh : h ∈ phases a P) : 2 ^ (a + 1) ≤ h ∧ h ≤ 2 ^ (a + P) := by
  induction P generalizing a with
  | zero => simp [phases] at hh
  | succ P ih =>
    simp only [phases, List.mem_append, List.mem_replicate] at hh
    rcases hh with ⟨-, rfl⟩ | hh
    · exact ⟨le_rfl, Nat.pow_le_pow_right (by norm_num) (by omega)⟩
    · obtain ⟨h1, h2⟩ := ih hh
      exact ⟨le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h1,
        h2.trans_eq (by ring_nf)⟩

lemma weight_replicate_append {h : ℕ} (h2 : 2 ≤ h) (R : ℕ) (rest : List ℕ) :
    weight (List.replicate R h ++ rest) ≤
      2 * h ^ R * rest.prod * (2 * h) ^ (2 * h) + weight rest := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [List.replicate_succ, List.cons_append, weight, List.prod_cons, List.prod_append,
      List.prod_replicate, pow_succ]
    have := Nat.mul_le_mul_right (h ^ R * rest.prod * (2 * h) ^ (2 * h)) h2
    nlinarith

lemma weight_phases_succ {a P B D : ℕ}
    (hrest : weight (phases (a + 1) P) ≤ B * (phases (a + 1) P).prod)
    (hBD : B ≤ D * (2 ^ (a + 1)) ^ (2 ^ (a + 3))) :
    weight (phases a (P + 1)) ≤
      (2 * 2 ^ ((a + 2) * 2 ^ (a + 2)) + D) * (phases a (P + 1)).prod := by
  have hX : (2 * 2 ^ (a + 1)) ^ (2 * 2 ^ (a + 1)) = 2 ^ ((a + 2) * 2 ^ (a + 2)) := by
    rw [← pow_succ', ← pow_mul]
  have h2 : 2 ≤ 2 ^ (a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := weight_replicate_append h2 (2 ^ (a + 3)) (phases (a + 1) P)
  rw [hX] at this
  simp only [phases, List.prod_append, List.prod_replicate]
  have := Nat.mul_le_mul_right (phases (a + 1) P).prod hBD
  nlinarith

lemma weight_phases_of {a B D : ℕ}
    (hrest : ∀ P, weight (phases (a + 1) P) ≤ B * (phases (a + 1) P).prod)
    (hBD : B ≤ D * (2 ^ (a + 1)) ^ (2 ^ (a + 3))) (P : ℕ) :
    weight (phases a P) ≤ (2 * 2 ^ ((a + 2) * 2 ^ (a + 2)) + D) * (phases a P).prod := by
  cases P with
  | zero => simp [phases, weight]
  | succ P => exact weight_phases_succ (hrest P) hBD

/-- For the lower phases (`a ≥ 3`) the weight is dominated by the top phase. -/
lemma weight_phases_ge_three (a P : ℕ) (ha : 3 ≤ a) :
    weight (phases a P) ≤ 4 * 2 ^ ((a + 2) * 2 ^ (a + 2)) * (phases a P).prod := by
  induction P generalizing a with
  | zero => simp [phases, weight]
  | succ P ih =>
    have hBD : 4 * 2 ^ ((a + 1 + 2) * 2 ^ (a + 1 + 2)) ≤
        2 * 2 ^ ((a + 2) * 2 ^ (a + 2)) * (2 ^ (a + 1)) ^ (2 ^ (a + 3)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_mul, ← pow_succ', ← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      have hu : 1 ≤ 2 ^ (a + 2) := Nat.one_le_two_pow
      rw [show a + 1 + 2 = a + 2 + 1 by ring, show a + 3 = a + 2 + 1 by ring, pow_succ]
      nlinarith
    refine (weight_phases_succ (ih (a + 1) (by omega)) hBD).trans (le_of_eq ?_)
    ring

/-- The weight of the whole construction of Theorem 3 is at most `2^29` times its resilience. -/
lemma weight_phases_zero (P : ℕ) : weight (phases 0 P) ≤ 2 ^ 29 * (phases 0 P).prod := by
  have h3 : ∀ P, weight (phases 3 P) ≤ 4 * 2 ^ 160 * (phases 3 P).prod := fun P =>
    weight_phases_ge_three 3 P le_rfl
  have h2 := weight_phases_of (a := 2) (D := 2 ^ 66) h3 (by norm_num)
  have h1 := weight_phases_of (a := 1) (D := 2 ^ 35) h2 (by norm_num)
  have h0 := weight_phases_of (a := 0) (D := 2 ^ 28) h1 (by norm_num) P
  refine h0.trans (Nat.mul_le_mul_right _ (by norm_num))

/-- The base of the construction of Theorem 3 (and Theorem 2): Corollary 1 with `f = 1`, i.e. a
`1`-resilient `C`-counter on `4` nodes with time `boostTime 4 1 = 2304`. -/
lemma achievable_four {C : ℕ} (hC : 1 < C) : Achievable 4 1 C 2304 (13 + Nat.clog 2 (C + 1)) := by
  have := corollary1 (f := 1) le_rfl hC
  have hb : boostTime (3 * 1 + 1) 1 = 2304 := by norm_num [boostTime, half]
  rw [hb] at this
  refine this.mono le_rfl ?_
  have : Nat.clog 2 2304 ≤ 12 := (Nat.clog_le_iff_le_pow (by norm_num)).2 (by norm_num)
  omega

/-- The resilience of Theorem 3's construction with `P ≥ 1` phases: `f_P = 2^((P-1)·2^(P+3)+8)`. -/
abbrev thm3F (P : ℕ) : ℕ := 2 ^ ((P - 1) * 2 ^ (P + 3) + 8)

/-- The number of nodes of Theorem 3's construction with `P ≥ 1` phases:
`n_P = 2^(8·2^P - 6) · f_P`. -/
abbrev thm3N (P : ℕ) : ℕ := 2 ^ (8 * 2 ^ P - 6) * thm3F P

lemma phaseExp_zero {P : ℕ} (hP : 1 ≤ P) : phaseExp 0 P = (P - 1) * 2 ^ (P + 3) + 8 := by
  have := phaseExp_closed 0 P
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  simp only [zero_add, zero_mul, add_zero, Nat.add_sub_cancel] at this ⊢
  rw [show Q + 1 + 3 = Q + 3 + 1 by ring, pow_succ] at this ⊢
  nlinarith

/-- Theorem 3 with explicit constants. With `P ≥ 1` phases (phase `p` uses `k_p = 4·2^(P-p)` blocks
and `R_p = 2k_p` iterations of Theorem 1), starting from the `1`-resilient counter on `4` nodes,
we get a `C`-counter on `n = 2^(8·2^P-6) · f` nodes with resilience `f = 2^((P-1)·2^(P+3)+8)`,
stabilisation time `≤ 2^33 · f` and `≤ 128 · 4^P · (P+1) + ⌈log₂(C+1)⌉ + 13` state bits. -/
theorem theorem3 {P C : ℕ} (hP : 1 ≤ P) (hC : 1 < C) :
    Achievable (thm3N P) (thm3F P) C (2 ^ 33 * thm3F P)
      (128 * 4 ^ P * (P + 1) + Nat.clog 2 (C + 1) + 13) := by
  have hmem : ∀ h ∈ phases 0 P, 2 ≤ h ∧ h ≤ 2 ^ P := fun h hh => by
    simpa using mem_phases hh
  have hprod : (phases 0 P).prod = thm3F P := by rw [prod_phases, phaseExp_zero hP]
  have hlen := length_phases 0 P
  simp only [zero_add] at hlen
  have hA := achievable_iterate (fun C hC => achievable_four hC) (by norm_num) (phases 0 P)
    (fun h hh => (hmem h hh).1) hC
  have hN : 4 * 2 ^ (phases 0 P).length * (phases 0 P).prod = thm3N P := by
    rw [hprod, thm3N, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 2
    rw [pow_add] at hlen
    omega
  rw [hN, one_mul, hprod] at hA
  have hf1 : 1 ≤ thm3F P := Nat.one_le_two_pow
  refine hA.mono ?_ ?_
  · -- time
    have h1 := iterTime_le (T₀ := 2304) le_rfl (phases 0 P) (fun h hh => (hmem h hh).1)
    have h2 := weight_phases_zero P
    rw [hprod] at h2
    nlinarith
  · -- space
    have h1 := iterSpace_le (S₀ := 13) (M := thm3F P) le_rfl (phases 0 P) hmem
      (by rw [one_mul, hprod])
    have hc : Nat.clog 2 (16 * thm3F P * (2 * 2 ^ P) ^ (2 * 2 ^ P)) =
        4 + ((P - 1) * 2 ^ (P + 3) + 8) + (P + 1) * (2 * 2 ^ P) := by
      rw [thm3F, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_succ', ← pow_mul, ← pow_add, ← pow_add,
        Nat.clog_pow _ _ (by norm_num)]
    rw [hc] at h1
    -- arithmetic with `v = 2^P`
    obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h1 hlen
    have hv : 1 ≤ 2 ^ (Q + 1) := Nat.one_le_two_pow
    have e1 : 2 ^ (Q + 1 + 3) = 8 * 2 ^ (Q + 1) := by rw [pow_add]; ring
    have e2 : (4 : ℕ) ^ (Q + 1) = 2 ^ (Q + 1) * 2 ^ (Q + 1) := by
      rw [← mul_pow]; norm_num
    rw [e1] at h1 hlen
    rw [e2]
    generalize 2 ^ (Q + 1) = v at *
    generalize (phases 0 (Q + 1)).length = l at *
    have hl : l ≤ 8 * v := by omega
    have : l * (4 + (Q * (8 * v) + 8) + (Q + 1 + 1) * (2 * v) + 1) ≤
        8 * v * (4 + (Q * (8 * v) + 8) + (Q + 1 + 1) * (2 * v) + 1) := Nat.mul_le_mul_right _ hl
    nlinarith

/-- Arithmetic behind the asymptotic form of Theorem 3: with `L = log₂ f_P` and `P ≥ 2`,
`4^P (P+1) ≤ L² / log₂ L` and `2^P ≤ L / log₂ L`. -/
lemma thm3_log_bounds {P : ℕ} (hP : 2 ≤ P) :
    4 ^ P * (P + 1) ≤ Nat.log 2 (thm3F P) ^ 2 / Nat.log 2 (Nat.log 2 (thm3F P)) ∧
      2 ^ P ≤ Nat.log 2 (thm3F P) / Nat.log 2 (Nat.log 2 (thm3F P)) := by
  rw [thm3F, Nat.log_pow (by norm_num)]
  have hv : P < 2 ^ P := Nat.lt_two_pow_self
  have e1 : 2 ^ (P + 3) = 8 * 2 ^ P := by rw [pow_add]; ring
  have e2 : (4 : ℕ) ^ P = 2 ^ P * 2 ^ P := by rw [← mul_pow]; norm_num
  have e3 : (2 : ℕ) ^ (2 * P + 4) = 16 * (2 ^ P * 2 ^ P) := by rw [pow_add, two_mul, pow_add]; ring
  rw [e1, e2]
  set E := (P - 1) * (8 * 2 ^ P) + 8 with hE
  have hE4 : 4 * P * 2 ^ P ≤ E := by
    obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 2 := ⟨P - 2, by omega⟩
    rw [hE, show Q + 2 - 1 = Q + 1 by omega]
    nlinarith
  have hElt : E < 2 ^ (2 * P + 4) := by
    rw [e3, hE]
    have : (P - 1) * (8 * 2 ^ P) ≤ (2 ^ P - 1) * (8 * 2 ^ P) := Nat.mul_le_mul_right _ (by omega)
    have h1 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
    obtain ⟨w, hw⟩ : ∃ w, 2 ^ P = w + 1 := ⟨2 ^ P - 1, by omega⟩
    rw [hw] at this ⊢
    simp only [Nat.add_sub_cancel] at this
    nlinarith
  have hLL : Nat.log 2 E ≤ 2 * P + 3 := by
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hElt
    omega
  have hLL1 : 0 < Nat.log 2 E := Nat.log_pos (by norm_num) (by nlinarith)
  constructor
  · rw [Nat.le_div_iff_mul_le hLL1]
    have h1 : 2 ^ P * 2 ^ P * (P + 1) * Nat.log 2 E ≤ 2 ^ P * 2 ^ P * (P + 1) * (2 * P + 3) :=
      Nat.mul_le_mul_left _ hLL
    have h2 : (4 * P * 2 ^ P) ^ 2 ≤ E ^ 2 := Nat.pow_le_pow_left hE4 2
    have h3 : (P + 1) * (2 * P + 3) ≤ 16 * P ^ 2 := by nlinarith
    have h4 := Nat.mul_le_mul_left (2 ^ P * 2 ^ P) h3
    nlinarith
  · rw [Nat.le_div_iff_mul_le hLL1]
    have h1 : 2 ^ P * Nat.log 2 E ≤ 2 ^ P * (2 * P + 3) := Nat.mul_le_mul_left _ hLL
    have h2 : 2 ^ P * (2 * P + 3) ≤ 2 ^ P * (4 * P) := Nat.mul_le_mul_left _ (by omega)
    nlinarith

/-- Theorem 3 (asymptotic form). There is an absolute constant `K` such that for every `C > 1`
there are `C`-counters with arbitrarily large resilience `f` on `n` nodes, with
* stabilisation time `T ≤ K f` (`O(f)`),
* `S ≤ K ⌊L² / log₂ L⌋ + ⌈log₂(C+1)⌉ + K` state bits, where `L = ⌊log₂ f⌋`
  (`O(log² f / log log f + log C)`),
* `log₂ n ≤ log₂ f + K ⌊L / log₂ L⌋`, i.e. `n ≤ f^{1 + O(1/log log f)}`, so `f = n^{1-o(1)}`. -/
theorem theorem3_asymptotic : ∃ K : ℕ, ∀ C, 1 < C → ∀ m : ℕ, ∃ n f T S : ℕ, m ≤ f ∧
    Achievable n f C T S ∧ T ≤ K * f ∧
    S ≤ K * (Nat.log 2 f ^ 2 / Nat.log 2 (Nat.log 2 f)) + Nat.clog 2 (C + 1) + K ∧
    Nat.log 2 n ≤ Nat.log 2 f + K * (Nat.log 2 f / Nat.log 2 (Nat.log 2 f)) := by
  refine ⟨2 ^ 33, fun C hC m => ?_⟩
  have hP : 2 ≤ m + 2 := by omega
  refine ⟨thm3N (m + 2), thm3F (m + 2), _, _, ?_, theorem3 (by omega) hC, le_rfl, ?_, ?_⟩
  · have h1 : m + 2 < 2 ^ (m + 2) := Nat.lt_two_pow_self
    have h2 : 2 ^ (m + 2) ≤ thm3F (m + 2) := Nat.pow_le_pow_right (by norm_num) (by
      have : 1 ≤ 2 ^ (m + 2 + 3) := Nat.one_le_two_pow
      rw [show m + 2 - 1 = m + 1 by omega]; nlinarith)
    omega
  · have := (thm3_log_bounds hP).1
    have := Nat.mul_le_mul_left 128 this
    have h33 : 128 * (Nat.log 2 (thm3F (m + 2)) ^ 2 / Nat.log 2 (Nat.log 2 (thm3F (m + 2)))) ≤
        2 ^ 33 * (Nat.log 2 (thm3F (m + 2)) ^ 2 / Nat.log 2 (Nat.log 2 (thm3F (m + 2)))) :=
      Nat.mul_le_mul_right _ (by norm_num)
    nlinarith
  · have hb := (thm3_log_bounds hP).2
    rw [thm3N, thm3F, ← pow_add, Nat.log_pow (by norm_num), Nat.log_pow (by norm_num)] at *
    have h8 := Nat.mul_le_mul_left 8 hb
    have : 8 * (((m + 2 - 1) * 2 ^ (m + 2 + 3) + 8) / Nat.log 2 ((m + 2 - 1) * 2 ^ (m + 2 + 3) + 8))
        ≤ 2 ^ 33 * (((m + 2 - 1) * 2 ^ (m + 2 + 3) + 8) /
          Nat.log 2 ((m + 2 - 1) * 2 ^ (m + 2 + 3) + 8)) := Nat.mul_le_mul_right _ (by norm_num)
    omega

/-! ### Theorem 2: a fixed number of blocks -/

lemma two_mul_two_pow_pow (a : ℕ) :
    (2 * 2 ^ a) ^ (2 * 2 ^ a) = 2 ^ ((a + 1) * 2 ^ (a + 1)) := by
  rw [← pow_succ', ← pow_mul]

/-- Theorem 2 with explicit constants, for `h = 2^a` (`a ≥ 1`, the paper's `ε = 1/a`): `L`
iterations of Theorem 1 with `k = 2h` blocks, starting from the `1`-resilient counter on `4` nodes,
give a `C`-counter with resilience `f = h^L = 2^(aL)` on `n = 4 (2h)^L = 2^(L+2) · f` nodes (so
`n / f = 4 · 2^L = 4 f^(1/a)`), stabilisation time `≤ 2^((a+1)·2^(a+1) + 12) · f` and
`≤ L (aL + (a+1) 2^(a+1) + 5) + ⌈log₂(C+1)⌉ + 13` state bits
(`= O(log² f / a + 2^a log f + log C)`). -/
theorem theorem2 {a L C : ℕ} (ha : 1 ≤ a) (hC : 1 < C) :
    Achievable (2 ^ (L + 2) * 2 ^ (a * L)) (2 ^ (a * L)) C
      (2 ^ ((a + 1) * 2 ^ (a + 1) + 12) * 2 ^ (a * L))
      (L * (a * L + (a + 1) * 2 ^ (a + 1) + 5) + Nat.clog 2 (C + 1) + 13) := by
  have h2 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) ha
  have hmem : ∀ h ∈ List.replicate L (2 ^ a), 2 ≤ h ∧ h ≤ 2 ^ a := fun h hh => by
    rw [List.eq_of_mem_replicate hh]; exact ⟨h2, le_rfl⟩
  have hprod : (List.replicate L (2 ^ a)).prod = 2 ^ (a * L) := by
    rw [List.prod_replicate, ← pow_mul]
  have hA := achievable_iterate (fun C hC => achievable_four hC) (by norm_num)
    (List.replicate L (2 ^ a)) (fun h hh => (hmem h hh).1) hC
  have hN : 4 * 2 ^ (List.replicate L (2 ^ a)).length * (List.replicate L (2 ^ a)).prod =
      2 ^ (L + 2) * 2 ^ (a * L) := by
    rw [hprod, List.length_replicate, pow_add]; ring
  rw [hN, one_mul, hprod] at hA
  have hf1 : 1 ≤ 2 ^ (a * L) := Nat.one_le_two_pow
  refine hA.mono ?_ ?_
  · have h1 := iterTime_le (T₀ := 2304) le_rfl (List.replicate L (2 ^ a))
      (fun h hh => (hmem h hh).1)
    have h3 := weight_replicate_append h2 L []
    simp only [List.append_nil, List.prod_nil, mul_one, weight, add_zero] at h3
    rw [two_mul_two_pow_pow, ← pow_mul, mul_comm a L] at h3
    rw [pow_add]
    have hX : 16 ≤ 2 ^ ((a + 1) * 2 ^ (a + 1)) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by
          have : 2 ≤ 2 ^ (a + 1) := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
          nlinarith)
    rw [mul_comm L a] at h3
    generalize 2 ^ ((a + 1) * 2 ^ (a + 1)) = X at *
    generalize 2 ^ (a * L) = f at *
    nlinarith
  · have h1 := iterSpace_le (S₀ := 13) (M := 2 ^ (a * L)) le_rfl (List.replicate L (2 ^ a)) hmem
      (by rw [one_mul, hprod])
    rw [two_mul_two_pow_pow, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_add,
      Nat.clog_pow _ _ (by norm_num), List.length_replicate] at h1
    nlinarith

/-- Corollary 2 (asymptotic form of Theorem 2 for a constant `ε`; here `h = 2^a`): there is `K`
(depending on `a` only) such that for every `C > 1` there are `C`-counters with arbitrarily large
resilience `f` on `n` nodes with `n^a = 4^a f^(a+1)` (i.e. `f = (n/4)^(1 - 1/(a+1))`), stabilisation
time `≤ K f` and `≤ K ⌊log₂ n⌋² + ⌈log₂(C+1)⌉ + K` state bits. -/
theorem corollary2 {a : ℕ} (ha : 1 ≤ a) : ∃ K : ℕ, ∀ C, 1 < C → ∀ m : ℕ, ∃ n f T S : ℕ,
    m ≤ f ∧ Achievable n f C T S ∧ T ≤ K * f ∧
    S ≤ K * Nat.log 2 n ^ 2 + Nat.clog 2 (C + 1) + K ∧ n ^ a = 4 ^ a * f ^ (a + 1) := by
  refine ⟨2 ^ ((a + 1) * 2 ^ (a + 1) + 12) + (a + (a + 1) * 2 ^ (a + 1) + 5), fun C hC m => ?_⟩
  refine ⟨2 ^ (m + 2) * 2 ^ (a * m), 2 ^ (a * m), _, _, ?_, theorem2 (L := m) ha hC, ?_, ?_, ?_⟩
  · have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ m ≤ 2 ^ (a * m) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega
  · exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  · rw [← pow_add, Nat.log_pow (by norm_num)]
    have h13 : 13 ≤ 2 ^ ((a + 1) * 2 ^ (a + 1) + 12) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 12 _))
    generalize (a + 1) * 2 ^ (a + 1) = B at *
    have hm : m ≤ m + 2 + a * m := by omega
    have hmm : m ≤ m * m := Nat.le_mul_self m
    have hm2 : m * m ≤ (m + 2 + a * m) ^ 2 := by nlinarith
    have : (a + B + 5) * (m * m) ≤ (2 ^ (B + 12) + (a + B + 5)) * (m + 2 + a * m) ^ 2 :=
      Nat.mul_le_mul (Nat.le_add_left _ _) hm2
    nlinarith
  · rw [← pow_add, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring

end SynchronousCounting
