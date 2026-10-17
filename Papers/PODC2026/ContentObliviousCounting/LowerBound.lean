import Papers.PODC2026.ContentObliviousCounting.LowerBoundSplice
import Cslib.Computability.Distributed.ContentOblivious.Prog
import Mathlib

/-!
# The `Ω(n log n)` lower bound for counting (§10, Theorem 3)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, Theorem 3.

**Model.** Oriented ring `oriented n` (`n ≥ 1`) on `ZMod n`, asynchronous, content-oblivious
(pulses), adversarial scheduler, no failures, deterministic algorithms. The input of a node is
`(ID, isLeader)`; IDs are distinct and exactly one node `ℓ` is the leader (`Admissible`).
An algorithm is a single program `P : Prog (ℕ × Bool)` used for every ring size (*processes do not
know `n`*), with an output map `out : P.State → Option ℕ` (the leader's count).

`CountingCorrect P out` is the safety part of counting: whenever the leader has an output, it is
the ring size. (No termination requirement is needed for the per-execution bound.)

**Results.**
* `count_lower_bound`: in *every* execution of a correct counting algorithm at the end of which the
  leader has an output, the number `M` of delivered pulses satisfies
  `n * log₂ n ≤ 14 * M + 4 * n`; in particular `n * log₂ n ≤ 28 * M` for `n ≥ 2^10`
  (`count_lower_bound'`). This is stronger than the paper's statement.
* `theorem3`: the paper's form — if moreover the leader has an output in every final configuration,
  then on every ring of size `n` with admissible inputs some execution sends at least
  `(n * log₂ n - 4 n) / 14` pulses.

**Proof** (as in the paper, with different constants): choose a sparse edge `{s-1, s}` among the
`⌊n/2⌋` edges following the leader clockwise; among the intervals `I_t = (s, …, s+t-1)`,
`1 ≤ t ≤ ofs s ℓ` (the clockwise distance from `s` to `ℓ`), which avoid the leader, at least
half have a sparse right edge; their interface traces are short, so two of them coincide
(Observation 27) and Lemma 28 yields an
execution on a smaller ring in which the leader ends in the same state, hence outputs the same
count — contradicting correctness. Instead of the paper's "w.l.o.g. the long arc is clockwise"
(which needs a mirror argument, as ports are not symmetric), we only use clockwise intervals
starting within distance `n/2` after the leader.
-/

namespace Podc.ContentOblivious.Counting

open Cslib.ContentOblivious Finset

/-- Admissible inputs `(ID, isLeader)`: distinct IDs and `ℓ` is the unique leader. -/
def Admissible {n : ℕ} (x : ZMod n → ℕ × Bool) (ℓ : ZMod n) : Prop :=
  Function.Injective (fun v => (x v).1) ∧ ∀ v, (x v).2 = true ↔ v = ℓ

/-- Safety of counting on oriented rings, for a uniform algorithm (the same program for all ring
sizes): on every oriented ring of size `n ≥ 1` with admissible inputs, in every reachable
configuration, if the leader has output `m` then `m = n`. -/
def CountingCorrect (P : Prog (ℕ × Bool)) (out : P.State → Option ℕ) : Prop :=
  ∀ n, 1 ≤ n → ∀ (x : ZMod n → ℕ × Bool) (ℓ : ZMod n), Admissible x ℓ →
    ∀ c, P.Reach (oriented n) x c → ∀ m, out (c.st ℓ) = some m → m = n

variable {P : Prog (ℕ × Bool)} {out : P.State → Option ℕ}

/-- The core contradiction: two trace-equivalent intervals sharing their left boundary and avoiding
the leader cannot exist in an execution in which the leader has an output. -/
theorem no_equal_traces (hP : CountingCorrect P out) {n : ℕ} [NeZero n]
    {x : ZMod n → ℕ × Bool} {ℓ : ZMod n} (hx : Admissible x ℓ) {l : List (ZMod n × Bool)}
    (hl : ValidSteps (oriented n) P.toAlgo (initCfg P.toAlgo fun v => Encodable.encode (x v)) l)
    {m : ℕ}
    (hm : out ((runSteps P.toAlgo (initCfg P.toAlgo fun v => Encodable.encode (x v)) l).st ℓ) =
      some m)
    {s : ZMod n} {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) (hbℓ : b ≤ ofs s ℓ)
    (htr : ringTrace n s a l = ringTrace n s b l) : False := by
  have hbn : b < n := hbℓ.trans_lt (ofs_lt s ℓ)
  obtain ⟨c', hc', hag⟩ := lemma28 ha hab hbn s P.toAlgo _ l hl htr
  obtain ⟨ℓ', hℓ'⟩ := (exists_spliceEmb_iff ha hab hbn s ℓ).2 (Or.inr hbℓ)
  have hinj := spliceEmb_injective ha hab hbn s
  have hx' : Admissible (x ∘ spliceEmb n a b s) ℓ' := by
    refine ⟨fun v w h => hinj (hx.1 h), fun v => ?_⟩
    simp only [Function.comp_apply, hx.2, ← hℓ']
    exact hinj.eq_iff
  have hreach : P.Reach (oriented (n - (b - a))) (x ∘ spliceEmb n a b s) c' := hc'
  have hst : c'.st ℓ' = _ := (hag ℓ').1
  rw [hℓ'] at hst
  have h1 := hP _ (by omega) _ _ hx' c' hreach m (by rw [hst]; exact hm)
  have h2 := hP n (Nat.pos_of_ne_zero (NeZero.ne n)) x ℓ hx _
    (by unfold Prog.Reach; exact hl.reflTransGen) m hm
  omega

/-! ### Averaging -/

lemma exists_mul_le_of_sum_le {h M : ℕ} (F : ℕ → ℕ) (hh : 0 < h)
    (hs : ∑ i ∈ range h, F i ≤ M) : ∃ i < h, h * F i ≤ M := by
  by_contra hcon
  push Not at hcon
  have : ∑ i ∈ range h, M < ∑ i ∈ range h, h * F i :=
    Finset.sum_lt_sum_of_nonempty (by simp; omega) fun i hi => hcon i (by simpa using hi)
  rw [Finset.sum_const, card_range, smul_eq_mul, ← Finset.mul_sum] at this
  have := Nat.mul_le_mul_left h hs
  omega

lemma card_filter_mul_le {D M : ℕ} (F : ℕ → ℕ) (hs : ∑ i ∈ range D, F i ≤ M) :
    D ≤ 2 * ((range D).filter fun i => D * F i ≤ 2 * M).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := range D) (fun i => D * F i ≤ 2 * M)
  simp only [not_le, card_range] at hsplit
  set B := (range D).filter fun i => 2 * M < D * F i
  have h1 : ∑ i ∈ B, (2 * M + 1) ≤ ∑ i ∈ B, D * F i :=
    Finset.sum_le_sum fun i hi => by simp only [B, mem_filter] at hi; omega
  have h2 : ∑ i ∈ B, D * F i ≤ D * M := by
    rw [← Finset.mul_sum]
    exact Nat.mul_le_mul_left D ((Finset.sum_le_sum_of_subset (by simp [B])).trans hs)
  rw [Finset.sum_const, smul_eq_mul] at h1
  have h3 : B.card * (2 * M + 1) ≤ D * M := h1.trans h2
  by_contra hcon
  have h4 : D + 1 ≤ 2 * B.card := by omega
  have h5 : (D + 1) * M ≤ 2 * B.card * M := Nat.mul_le_mul_right M h4
  nlinarith

/-! ### Edge loads -/

section loads

variable {n : ℕ} [NeZero n] {S : Type*}

lemma totalRecvd_eq_sum_edgeLoad (c : Config (ZMod n) S) :
    totalRecvd c = ∑ u, edgeLoad c u := by
  simp only [totalRecvd, edgeLoad, Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight 1) _ _ fun _ => by simp

omit [NeZero n] in
lemma natCast_injOn (ℓ : ZMod n) :
    Set.InjOn (fun k : ℕ => ℓ + (k : ZMod n)) ↑(range n) := by
  intro k hk k' hk' h
  simp only [coe_range, Set.mem_Iio] at hk hk'
  have h' : ((k : ℕ) : ZMod n) = (k' : ZMod n) := add_left_cancel h
  have := congrArg ZMod.val h'
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at this

/-- Edge loads of distinct edges `{ℓ+k, ℓ+k+1}`, `k < n`, add up to at most the total. -/
lemma sum_edgeLoad_le (c : Config (ZMod n) S) (ℓ : ZMod n) {T : Finset ℕ} (hT : T ⊆ range n) :
    ∑ k ∈ T, edgeLoad c (ℓ + (k : ZMod n)) ≤ totalRecvd c := by
  rw [totalRecvd_eq_sum_edgeLoad, ← Finset.sum_image ((natCast_injOn ℓ).mono hT)]
  exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

end loads

/-! ### Theorem 3 -/

/-- **Theorem 3** of [Chalopin–Chang–Di Luna–Zhou, PODC 2026], per-execution form (stronger than
the paper): for a correct uniform counting algorithm on oriented content-oblivious rings with unique
IDs and a pre-selected leader, in every execution at the end of which the leader has an output, the
number of delivered pulses `M` satisfies `n * log₂ n ≤ 14 * M + 4 * n`. -/
theorem count_lower_bound (hP : CountingCorrect P out) {n : ℕ} [NeZero n]
    {x : ZMod n → ℕ × Bool} {ℓ : ZMod n} (hx : Admissible x ℓ) {c : Config (ZMod n) P.State}
    (hc : P.Reach (oriented n) x c) {m : ℕ} (hm : out (c.st ℓ) = some m) :
    n * Nat.log 2 n ≤ 14 * totalRecvd c + 4 * n := by
  obtain ⟨l, hl, rfl⟩ := (reach_iff_validSteps _ _).1 hc
  set c := runSteps P.toAlgo (initCfg P.toAlgo fun v => Encodable.encode (x v)) l with hcdef
  set M := totalRecvd c
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have : n = 1 := by have := NeZero.ne n; omega
    subst this; simp
  -- the sparse left edge `{s-1, s}`, `s = ℓ + j`, `1 ≤ j ≤ n/2`
  set h := n / 2 with hh
  have hh0 : 0 < h := by omega
  set F : ℕ → ℕ := fun k => edgeLoad c (ℓ + (k : ZMod n)) with hF
  obtain ⟨i, hi, hiM⟩ := exists_mul_le_of_sum_le F hh0
    (sum_edgeLoad_le c ℓ (by intro k; simp; omega))
  set j := i + 1 with hj
  set s : ZMod n := ℓ + (j : ZMod n) with hs
  set D := n - j with hD
  have hjn : j < n := by omega
  have hsℓ : ofs s ℓ = D := by
    rw [ofs_eq_iff (by omega), hs, hD, Nat.cast_sub hjn.le, ZMod.natCast_self]; ring
  have hleft : edgeLoad c (s - 1) = F i := by
    simp only [hF, hs, j]; congr 1; push_cast; ring
  -- the good intervals `I_{t+1}`, `t < D`
  have hsumR : ∑ t ∈ range D, F (j + t) ≤ M := by
    have := sum_edgeLoad_le c ℓ (T := (range D).image (j + ·)) (by
      intro k; simp only [mem_image, mem_range]; omega)
    rwa [Finset.sum_image (by intro a _ b _ h; simpa using h)] at this
  set G := (range D).filter fun t => D * F (j + t) ≤ 2 * M with hG
  have hGcard : D ≤ 2 * G.card := card_filter_mul_le (fun t => F (j + t)) hsumR
  set K := M / h + 2 * M / D with hK
  have hD0 : 0 < D := by omega
  have htrace : ∀ t ∈ G, ringTrace n s (t + 1) l ∈ wordsUpTo K := by
    intro t ht
    simp only [hG, mem_filter, mem_range] at ht
    rw [mem_wordsUpTo, ringTrace_length (by omega) (by omega), hleft]
    have e : s + ((t + 1 : ℕ) : ZMod n) - 1 = ℓ + ((j + t : ℕ) : ZMod n) := by
      simp only [hs]; push_cast; ring
    rw [e]
    have h1 : F i ≤ M / h := (Nat.le_div_iff_mul_le hh0).2 (by linarith)
    have h2 : F (j + t) ≤ 2 * M / D := (Nat.le_div_iff_mul_le hD0).2 (by linarith [ht.2])
    exact Nat.add_le_add h1 h2
  -- two good intervals have the same trace, unless there are few good intervals
  have hGle : G.card ≤ 4 ^ (K + 1) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁, t₂, ht₂, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      ((card_wordsUpTo_le K).trans_lt hcon) (f := fun t => ringTrace n s (t + 1) l) htrace
    have hG' : ∀ t ∈ G, t < D := fun t ht => by simp [hG] at ht; exact ht.1
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact no_equal_traces hP hx hl hm (a := t₁ + 1) (b := t₂ + 1) (by omega) (by omega)
        (by rw [hsℓ]; have := hG' _ ht₂; omega) heq
    · exact no_equal_traces hP hx hl hm (a := t₂ + 1) (b := t₁ + 1) (by omega) (by omega)
        (by rw [hsℓ]; have := hG' _ ht₁; omega) heq.symm
  -- arithmetic
  have hnK : n ≤ 2 ^ (2 * K + 4) := by
    have : 2 ^ (2 * K + 4) = 4 * 4 ^ (K + 1) := by
      rw [show 2 * K + 4 = 2 * (K + 2) by ring, pow_mul]; norm_num; ring
    rw [this]; omega
  have hlog : Nat.log 2 n ≤ 2 * K + 4 := by
    have := Nat.log_mono_right (b := 2) hnK
    rwa [Nat.log_pow (by norm_num)] at this
  have hK1 : n * (M / h) ≤ 3 * M := by
    have := Nat.div_mul_le_self M h
    calc n * (M / h) ≤ (3 * h) * (M / h) := Nat.mul_le_mul_right _ (by omega)
      _ = 3 * (M / h * h) := by ring
      _ ≤ 3 * M := by omega
  have hK2 : n * (2 * M / D) ≤ 4 * M := by
    have := Nat.div_mul_le_self (2 * M) D
    calc n * (2 * M / D) ≤ (2 * D) * (2 * M / D) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * (2 * M / D * D) := by ring
      _ ≤ 4 * M := by omega
  calc n * Nat.log 2 n ≤ n * (2 * K + 4) := Nat.mul_le_mul_left n hlog
    _ = 2 * (n * (M / h)) + 2 * (n * (2 * M / D)) + 4 * n := by rw [hK]; ring
    _ ≤ 14 * M + 4 * n := by omega

/-- Corollary of `count_lower_bound` with a single constant:
`n * log₂ n ≤ 28 * M` for `n ≥ 2^10`. -/
theorem count_lower_bound' (hP : CountingCorrect P out) {n : ℕ} [NeZero n] (hn : 2 ^ 10 ≤ n)
    {x : ZMod n → ℕ × Bool} {ℓ : ZMod n} (hx : Admissible x ℓ) {c : Config (ZMod n) P.State}
    (hc : P.Reach (oriented n) x c) {m : ℕ} (hm : out (c.st ℓ) = some m) :
    n * Nat.log 2 n ≤ 28 * totalRecvd c := by
  have h := count_lower_bound hP hx hc hm
  have hlog : 10 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have : n * 10 ≤ n * Nat.log 2 n := Nat.mul_le_mul_left n hlog
  omega

/-- **Theorem 3** of [Chalopin–Chang–Di Luna–Zhou, PODC 2026] (lower bound), in the paper's form:
a correct uniform counting algorithm on oriented content-oblivious rings with unique IDs and a
pre-selected leader, whose leader has an output in every final configuration, has on every ring of
size `n` (and every admissible input) an execution with message complexity `M` satisfying
`n * log₂ n ≤ 14 * M + 4 * n`, i.e. `M = Ω(n log n)`. -/
theorem theorem3 (hP : CountingCorrect P out) {n : ℕ} [NeZero n]
    {x : ZMod n → ℕ × Bool} {ℓ : ZMod n} (hx : Admissible x ℓ)
    (hterm : ∀ c, P.Reach (oriented n) x c → P.Final (oriented n) c → (out (c.st ℓ)).isSome) :
    ∃ c, P.Reach (oriented n) x c ∧ n * Nat.log 2 n ≤ 14 * totalSent c + 4 * n := by
  by_cases hB : ∀ c, P.Reach (oriented n) x c → totalSent c ≤ n * Nat.log 2 n
  · have h0 : Reach (oriented n) P.toAlgo (fun v => Encodable.encode (x v))
        (initCfg P.toAlgo fun v => Encodable.encode (x v)) := Relation.ReflTransGen.refl
    obtain ⟨c, hc, hfin⟩ := exists_final hB h0
    have hcR : P.Reach (oriented n) x c := hc
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (hterm c hcR hfin)
    have h1 := count_lower_bound hP hx hcR hm
    have h2 := Reach.totalRecvd_le_totalSent hcR
    exact ⟨c, hcR, by omega⟩
  · push Not at hB
    obtain ⟨c, hc, hlt⟩ := hB
    exact ⟨c, hc, by omega⟩

end Podc.ContentOblivious.Counting
