import Papers.PODC2026.ContentObliviousCounting.AnonCountingProbe

/-!
# Anonymous counting: waves of the last phase

Generic facts about a wave of `K` pulses sent around the ring by the last leader (`pipeTr`,
`PipeOk`), and the steps of the wave stages `pipe κ a b`.
-/

namespace Podc.ContentOblivious.AnonCounting

open Podc.ContentOblivious Finset

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-! ## Successor / predecessor positions -/

lemma nxt_lt {n q : ℕ} (hq : q < n) : nxt n q < n := by unfold nxt; split_ifs <;> omega
lemma prv_lt {n q : ℕ} (hq : q < n) : prv n q < n := by unfold prv; split_ifs <;> omega
lemma prv_nxt {n q : ℕ} (hq : q < n) : prv n (nxt n q) = q := by
  simp only [nxt, prv]; split_ifs at * <;> omega
lemma nxt_prv {n q : ℕ} (hq : q < n) : nxt n (prv n q) = q := by
  simp only [nxt, prv]; split_ifs at * <;> omega
lemma prv_eq_iff {n p q : ℕ} (hp : p < n) (hq : q < n) : prv n p = q ↔ p = nxt n q := by
  constructor
  · rintro rfl; rw [nxt_prv hp]
  · rintro rfl; rw [prv_nxt hq]
lemma nxt_eq_iff {n p q : ℕ} (hp : p < n) (hq : q < n) : nxt n p = q ↔ p = prv n q := by
  constructor
  · rintro rfl; rw [prv_nxt hp]
  · rintro rfl; rw [nxt_prv hq]
lemma nxt_ne_self {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) : nxt n q ≠ q := by
  unfold nxt; split_ifs <;> omega
lemma prv_ne_self {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) : prv n q ≠ q := by
  unfold prv; split_ifs <;> omega

/-- Where a wave travelling in direction `cw` goes after `p`. -/
def dst (n : ℕ) (cw : Bool) (p : ℕ) : ℕ := if cw then nxt n p else prv n p

lemma src_dst {n : ℕ} (cw : Bool) {q : ℕ} (hq : q < n) : src n cw (dst n cw q) = q := by
  cases cw <;> simp [src, dst, prv_nxt hq, nxt_prv hq]

lemma src_eq_iff {n : ℕ} (cw : Bool) {p q : ℕ} (hp : p < n) (hq : q < n) :
    src n cw p = q ↔ p = dst n cw q := by
  cases cw <;> simp [src, dst, prv_eq_iff hp hq, nxt_eq_iff hp hq]

lemma src_lt {n : ℕ} (cw : Bool) {p : ℕ} (hp : p < n) : src n cw p < n := by
  cases cw <;> simp [src, prv_lt hp, nxt_lt hp]

lemma dst_lt {n : ℕ} (cw : Bool) {p : ℕ} (hp : p < n) : dst n cw p < n := by
  cases cw <;> simp [dst, prv_lt hp, nxt_lt hp]

/-! ## Paths around the ring -/

/-- The position at distance `d` from `L` in direction `cw`. -/
def pathAt (n L : ℕ) (cw : Bool) (d : ℕ) : ℕ :=
  if cw then (if L + d < n then L + d else L + d - n) else (if d ≤ L then L - d else L + n - d)

lemma pathAt_zero {n L : ℕ} (cw : Bool) (hL : L < n) : pathAt n L cw 0 = L := by
  cases cw <;> simp [pathAt, hL]

lemma pathAt_lt {n L : ℕ} (cw : Bool) (hL : L < n) {d : ℕ} (hd : d ≤ n) : pathAt n L cw d < n := by
  cases cw <;> simp only [pathAt, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

lemma pathAt_ne {n L : ℕ} (cw : Bool) (hL : L < n) {d : ℕ} (h1 : 1 ≤ d) (h2 : d < n) :
    pathAt n L cw d ≠ L := by
  cases cw <;> simp only [pathAt, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

lemma src_pathAt {n L : ℕ} (cw : Bool) (hL : L < n) {d : ℕ} (hd : d + 1 ≤ n) :
    src n cw (pathAt n L cw (d + 1)) = pathAt n L cw d := by
  cases cw <;> simp only [src, pathAt, nxt, prv, Bool.false_eq_true, ↓reduceIte] <;> split_ifs at * <;> omega

lemma src_lead {n L : ℕ} (cw : Bool) (hL : L < n) : src n cw L = pathAt n L cw (n - 1) := by
  have h := src_pathAt cw hL (d := n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at h
  rw [← h]; congr 1
  cases cw <;> simp only [pathAt, Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

lemma exists_pathAt {n L : ℕ} (cw : Bool) (hL : L < n) {p : ℕ} (hp : p < n) (hpL : p ≠ L) :
    ∃ d, 1 ≤ d ∧ d < n ∧ pathAt n L cw d = p := by
  cases cw
  · refine ⟨if p ≤ L then L - p else L + n - p, ?_, ?_, ?_⟩ <;>
      (try simp only [pathAt, Bool.false_eq_true, ↓reduceIte]) <;>
      split_ifs at * <;> omega
  · refine ⟨if L ≤ p then p - L else p + n - L, ?_, ?_, ?_⟩ <;>
      (try simp only [pathAt, Bool.false_eq_true, ↓reduceIte]) <;>
      split_ifs at * <;> omega

/-! ## Chains of a wave profile -/

/-- Number of pulses of the wave that position `x` has sent on. -/
def srcCnt (L K : ℕ) (a : ℕ → ℕ) (x : ℕ) : ℕ := if x = L then K else a x

lemma pipeOk_srcCnt_le {n L K : ℕ} {cw : Bool} {a : ℕ → ℕ} {b : ℕ} (h : PipeOk n L K cw a b)
    {x : ℕ} (hx : x < n) : srcCnt L K a x ≤ K := by
  unfold srcCnt; split_ifs with h1
  · exact le_rfl
  · exact (h.2.1 x hx h1).1

/-- When the leader receives the last pulse of the wave, every node has relayed all of them. -/
lemma pipe_full {n L K : ℕ} {cw : Bool} {a : ℕ → ℕ} {b : ℕ} (hL : L < n)
    (h : PipeOk n L K cw a b) (hb : K ≤ b + 1)
    (hpos : b < srcCnt L K a (src n cw L)) : ∀ p < n, p ≠ L → a p = K := by
  intro p hp hpL
  have hn : 2 ≤ n := by omega
  have hsl : src n cw L = pathAt n L cw (n - 1) := src_lead cw hL
  have hne : pathAt n L cw (n - 1) ≠ L := pathAt_ne cw hL (by omega) (by omega)
  rw [hsl, srcCnt, if_neg hne] at hpos
  -- downward induction along the path
  have key : ∀ k, k ≤ n - 2 → K ≤ a (pathAt n L cw (n - 1 - k)) := by
    intro k
    induction k with
    | zero => intro _; simp only [Nat.sub_zero]; omega
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have hs := src_pathAt cw hL (d := n - 1 - (k + 1)) (by omega)
      rw [show n - 1 - (k + 1) + 1 = n - 1 - k by omega] at hs
      have hne' : pathAt n L cw (n - 1 - k) ≠ L := pathAt_ne cw hL (by omega) (by omega)
      have hlt := pathAt_lt cw hL (d := n - 1 - k) (by omega)
      have h2 := (h.2.1 _ hlt hne').2
      rw [hs, if_neg (pathAt_ne cw hL (by omega) (by omega))] at h2
      omega
  obtain ⟨d, hd1, hd2, rfl⟩ := exists_pathAt cw hL hp hpL
  have := key (n - 1 - d) (by omega)
  rw [show n - 1 - (n - 1 - d) = d by omega] at this
  have := (h.2.1 _ hp hpL).1
  omega

/-- While the wave is not over, some pulse of it is in transit. -/
lemma pipe_exists {n L K : ℕ} {cw : Bool} {a : ℕ → ℕ} {b : ℕ} (hL : L < n)
    (h : PipeOk n L K cw a b) : ∃ p < n, 0 < pipeTr n L K cw a b p (!cw) := by
  by_contra hc
  push Not at hc
  have hz : ∀ p < n, srcCnt L K a (src n cw p) ≤ (if p = L then b else a p) := by
    intro p hp
    have := hc p hp
    simp only [pipeTr, if_true] at this
    unfold srcCnt; omega
  -- upward induction along the path
  have key : ∀ d, 1 ≤ d → d < n → a (pathAt n L cw d) = K := by
    intro d
    induction d with
    | zero => intro h; omega
    | succ d ih =>
      intro _ hd
      have hlt := pathAt_lt cw hL (d := d + 1) (by omega)
      have hne := pathAt_ne cw hL (d := d + 1) (by omega) hd
      have h1 := hz _ hlt
      rw [if_neg hne, src_pathAt cw hL (by omega)] at h1
      have h2 := (h.2.1 _ hlt hne).1
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · rw [pathAt_zero cw hL, srcCnt, if_pos rfl] at h1; omega
      · rw [srcCnt, if_neg (pathAt_ne cw hL hd0 (by omega)), ih hd0 (by omega)] at h1; omega
  have h1 := hz L hL
  rw [if_pos rfl, src_lead cw hL] at h1
  have hb := h.1
  rcases Nat.lt_or_ge 1 n with hn | hn
  · rw [srcCnt, if_neg (pathAt_ne cw hL (by omega) (by omega)), key _ (by omega) (by omega)] at h1
    omega
  · rw [show n - 1 = 0 by omega, pathAt_zero cw hL, srcCnt, if_pos rfl] at h1; omega

/-! ## Transit after a relay step -/

/-- One pulse sent onwards by a node relaying a wave in direction `cw`. -/
def wout (cw : Bool) : Bool → ℕ := if cw then out 0 1 else out 1 0

lemma pipeTr_eq (n L K : ℕ) (cw : Bool) (a : ℕ → ℕ) (b p : ℕ) (b' : Bool) :
    pipeTr n L K cw a b p b' =
      if b' = !cw then srcCnt L K a (src n cw p) - (if p = L then b else a p) else 0 := rfl

lemma srcCnt_update {L K q v : ℕ} {a : ℕ → ℕ} (hqL : q ≠ L) (x : ℕ) :
    srcCnt L K (Function.update a q v) x = if x = q then v else srcCnt L K a x := by
  unfold srcCnt
  by_cases h1 : x = L
  · subst h1; simp [Ne.symm hqL]
  · by_cases h2 : x = q
    · subst h2; simp [h1]
    · simp [h1, h2]

lemma tr_core {c aq ap b : ℕ} {P Q S R : Prop} [Decidable P] [Decidable Q] [Decidable S]
    [Decidable R] (hSQ : S ↔ Q) (hPQ : P → ¬Q) (hPS : P → ¬S) (hc : S → c = aq)
    (hpos : P → aq < c) (hPR : P → ¬R) (hap : P → ap = aq)
    (hle : Q → (if R then b else ap) ≤ aq) :
    c - (if R then b else ap) - (if P then 1 else 0) + (if Q then 1 else 0) =
      (if S then aq + 1 else c) - (if R then b else if P then aq + 1 else ap) := by
  by_cases hP : P
  · have := hpos hP; have := hap hP
    simp only [hP, hPQ hP, hPS hP, hPR hP, ite_true, ite_false]; omega
  · by_cases hQ : Q
    · have hS := hSQ.2 hQ; have := hc hS; have := hle hQ
      simp only [hP, hQ, hS, ite_true, ite_false] at this ⊢
      split_ifs at * <;> omega
    · have hS : ¬S := fun h => hQ (hSQ.1 h)
      simp only [hP, hQ, hS, ite_false]; omega

lemma pipeTr_node {n L K : ℕ} {cw : Bool} {a : ℕ → ℕ} {b q : ℕ} (hL : L < n) (hqn : q < n)
    (hqL : q ≠ L) (hok : PipeOk n L K cw a b) (hpos : a q < srcCnt L K a (src n cw q))
    (p : ℕ) (hp : p < n) (b' : Bool) :
    pipeTr n L K cw a b p b' - (if p = q ∧ b' = !cw then 1 else 0) +
      (if b' = false ∧ p = nxt n q then wout cw true else 0) +
      (if b' = true ∧ p = prv n q then wout cw false else 0) =
    pipeTr n L K cw (Function.update a q (a q + 1)) b p b' := by
  have hn : 2 ≤ n := by omega
  have hsq : src n cw q ≠ q := by
    intro h; rw [src_eq_iff cw hqn hqn] at h
    cases cw <;> simp [dst] at h
    · exact prv_ne_self hn hqn h.symm
    · exact nxt_ne_self hn hqn h.symm
  have hdq : dst n cw q ≠ q := by
    intro h; have := src_dst cw hqn; rw [h] at this; exact hsq this
  have hsc : srcCnt L K a q = a q := by simp [srcCnt, hqL]
  have hle : p = dst n cw q → (if p = L then b else a p) ≤ a q := by
    intro hpd
    have hs : src n cw p = q := by rw [hpd, src_dst cw hqn]
    split_ifs with hpL
    · have := hok.2.2; rw [← hpL, hs, if_neg (fun h => hqL (h.trans hpL))] at this; exact this
    · have := (hok.2.1 p hp hpL).2; rw [hs, if_neg hqL] at this; exact this
  have hcore := tr_core (c := srcCnt L K a (src n cw p)) (aq := a q) (ap := a p) (b := b)
    (P := p = q) (Q := p = dst n cw q) (S := src n cw p = q) (R := p = L)
    (src_eq_iff cw hp hqn) (fun h1 h2 => hdq (h1 ▸ h2).symm) (fun h1 h2 => hsq (h1 ▸ h2))
    (fun h => by rw [h, hsc]) (fun h => h ▸ hpos) (fun h1 h2 => hqL (h1 ▸ h2)) (fun h => h ▸ rfl)
    hle
  have e2 : (if p = L then b else Function.update a q (a q + 1) p) =
      (if p = L then b else if p = q then a q + 1 else a p) := by
    by_cases h2 : p = q
    · subst h2; simp
    · simp [h2, Function.update_of_ne h2]
  cases cw <;> cases b' <;>
    simp only [pipeTr_eq, srcCnt_update hqL, e2, wout, dst, Bool.not_true, Bool.not_false,
      ite_true, ite_false, true_and, and_true, Bool.false_eq_true, Bool.true_eq_false, false_and,
      and_false, out_true, out_false, add_zero, Nat.zero_sub, zero_add, ite_self] at hcore ⊢ <;>
    first | omega | exact hcore | (simp only [Nat.add_zero]; exact hcore) | skip

/-! ## Steps of a wave stage (generic part) -/

lemma lead_lt {n : ℕ} (hn : 0 < n) : lead n < n := tri_phaseOf_lt hn

lemma wout_sum (cw : Bool) : wout cw false + wout cw true = 1 := by cases cw <;> rfl

lemma sum_update_succ {S : Finset ℕ} {a : ℕ → ℕ} {q : ℕ} (hq : q ∈ S) :
    ∑ p ∈ S, Function.update a q (a q + 1) p = ∑ p ∈ S, a p + 1 := by
  rw [Finset.sum_update_of_mem hq, Finset.sdiff_singleton_eq_erase, ← Finset.add_sum_erase S a hq]
  ring

lemma pipe_en {n : ℕ} {κ : Kind} {a : ℕ → ℕ} {b q : ℕ} {j : Bool}
    (h : (absPipe n κ a b).En n q j) :
    j = !κ.cw n ∧ (if q = lead n then b else a q) < srcCnt (lead n) κ.K a (src n (κ.cw n) q) := by
  obtain ⟨-, h, -⟩ := h
  simp only [absPipe, pipeTr_eq] at h
  by_cases h1 : j = !κ.cw n
  · rw [if_pos h1] at h; exact ⟨h1, by omega⟩
  · rw [if_neg h1] at h; simp at h

lemma pipeOk_srcCnt {n L K : ℕ} {cw : Bool} {a : ℕ → ℕ} {b : ℕ} :
    PipeOk n L K cw a b ↔ b < K ∧ (∀ p < n, p ≠ L → a p ≤ K ∧ a p ≤ srcCnt L K a (src n cw p)) ∧
      b ≤ srcCnt L K a (src n cw L) := Iff.rfl

theorem pipe_node {n : ℕ} {κ : Kind} {a : ℕ → ℕ} {b q : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe κ a b).Ok n) (hqL : q ≠ lead n) (hen : (absPipe n κ a b).En n q j)
    (hf : ∀ k < κ.K, recv (κ.f n q k) (!κ.cw n) = (κ.f n q (k + 1), wout (κ.cw n))) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((absPipe n κ a b).step n q j) (s'.abs n) := by
  obtain ⟨hκ, hpo⟩ := hok
  have hL := lead_lt hn
  have hqn : q < n := hen.1
  obtain ⟨rfl, hpos⟩ := pipe_en hen
  rw [if_neg hqL] at hpos
  have hpo' := pipeOk_srcCnt.1 hpo
  have hK : a q < κ.K := lt_of_lt_of_le hpos (pipeOk_srcCnt_le hpo (src_lt _ hqn))
  have hn2 : 2 ≤ n := by omega
  have hsq : src n (κ.cw n) q ≠ q := by
    intro h; rw [src_eq_iff _ hqn hqn] at h
    cases hc : κ.cw n <;> simp [dst, hc] at h
    · exact prv_ne_self hn2 hqn h.symm
    · exact nxt_ne_self hn2 hqn h.symm
  have hmono : ∀ x, srcCnt (lead n) κ.K a x ≤
      srcCnt (lead n) κ.K (Function.update a q (a q + 1)) x := by
    intro x; rw [srcCnt_update hqL]; split_ifs with h
    · subst h; simp [srcCnt, hqL]
    · exact le_rfl
  refine ⟨.pipe κ (Function.update a q (a q + 1)) b, ⟨hκ, ?_⟩, ?_⟩
  · refine pipeOk_srcCnt.2 ⟨hpo'.1, fun p hp hpL => ?_, (hpo'.2.2).trans (hmono _)⟩
    by_cases hpq : p = q
    · subst hpq
      rw [Function.update_self, srcCnt_update hqL, if_neg hsq]
      omega
    · rw [Function.update_of_ne hpq]
      exact ⟨(hpo'.2.1 p hp hpL).1, (hpo'.2.1 p hp hpL).2.trans (hmono _)⟩
  have hst : (absPipe n κ a b).st q = κ.f n q (a q) := by simp [absPipe, hqL]
  refine agree_of (by rw [hst, hf _ hK]) ?_ ?_ ?_ ?_
  · intro p hp hpq
    simp only [Stage.abs, absPipe, Function.update_of_ne hpq]
  · simp [Stage.abs, absPipe, hqL]
  · intro p hp b'
    exact pipeTr_node hL hqn hqL hpo hpos p hp b'
  · simp only [Stage.abs, absPipe]
    rw [sum_update_succ (by simp [hqn, hqL])]
    have := wout_sum (κ.cw n)
    omega

theorem pipe_lead_mid {n : ℕ} {κ : Kind} {a : ℕ → ℕ} {b : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe κ a b).Ok n) (hen : (absPipe n κ a b).En n (lead n) j)
    (hb : b + 1 < κ.K)
    (hg : recv (κ.g n b) (!κ.cw n) = (κ.g n (b + 1), out 0 0)) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((absPipe n κ a b).step n (lead n) j) (s'.abs n) := by
  obtain ⟨hκ, hpo⟩ := hok
  have hL := lead_lt hn
  obtain ⟨rfl, hpos⟩ := pipe_en hen
  rw [if_pos rfl] at hpos
  have hpo' := pipeOk_srcCnt.1 hpo
  refine ⟨.pipe κ a (b + 1), ⟨hκ, pipeOk_srcCnt.2 ⟨hb, hpo'.2.1, by omega⟩⟩, ?_⟩
  have hst : (absPipe n κ a b).st (lead n) = κ.g n b := by simp [absPipe]
  refine agree_of (by rw [hst, hg]) ?_ ?_ ?_ ?_
  · intro p hp hpq
    simp [Stage.abs, absPipe, hpq]
  · simp [Stage.abs, absPipe]
  · intro p hp b'
    simp only [Stage.abs, absPipe, pipeTr_eq, out_true, out_false, ite_self, add_zero]
    by_cases hp' : p = lead n
    · subst hp'; cases b' <;> cases hc : κ.cw n <;> simp [hc] at hpos ⊢ <;> omega
    · simp [hp']
  · simp [Stage.abs, absPipe]

theorem pipe_exit {n : ℕ} {κ : Kind} {a : ℕ → ℕ} {b : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe κ a b).Ok n) (hen : (absPipe n κ a b).En n (lead n) j)
    (hb : b + 1 = κ.K) {σ : St} {o : Bool → ℕ}
    (hrecv : recv (κ.g n b) (!κ.cw n) = (σ, o)) (s' : Stage)
    (hst : ∀ p < n, p ≠ lead n → κ.f n p κ.K = (s'.abs n).st p)
    (hsq : σ = (s'.abs n).st (lead n))
    (htr : ∀ p < n, ∀ b', (if b' = false ∧ p = nxt n (lead n) then o true else 0) +
      (if b' = true ∧ p = prv n (lead n) then o false else 0) = (s'.abs n).tr p b')
    (htot : κ.base n + (n - 1) * κ.K + o false + o true = (s'.abs n).tot) :
    Agree n ((absPipe n κ a b).step n (lead n) j) (s'.abs n) := by
  obtain ⟨hκ, hpo⟩ := hok
  have hL := lead_lt hn
  obtain ⟨rfl, hpos⟩ := pipe_en hen
  rw [if_pos rfl] at hpos
  have hfull := pipe_full hL hpo (by omega) hpos
  have hst0 : (absPipe n κ a b).st (lead n) = κ.g n b := by simp [absPipe]
  refine agree_of (by rw [hst0, hrecv]) ?_ hsq ?_ ?_
  · intro p hp hpq
    simp only [absPipe, if_neg hpq, hfull p hp hpq]
    exact hst p hp hpq
  · intro p hp b'
    rw [← htr p hp b']
    have hz : pipeTr n (lead n) κ.K (κ.cw n) a b p b' - (if p = lead n ∧ b' = !κ.cw n then 1 else 0)
        = 0 := by
      rw [pipeTr_eq]
      have hle := pipeOk_srcCnt_le hpo (src_lt (κ.cw n) hp)
      by_cases h1 : b' = !κ.cw n
      · by_cases hpL : p = lead n
        · subst hpL; simp only [h1, ite_true, and_self]; omega
        · simp only [h1, hpL, ite_true, ite_false, and_true]
          rw [hfull p hp hpL]; omega
      · simp only [h1, ite_false, and_false]
    simp only [absPipe] at hz ⊢
    omega
  · simp only [absPipe]
    rw [Finset.sum_congr rfl (fun p hp => hfull p (by simp at hp; omega) (by simp at hp; omega))]
    rw [Finset.sum_const, Finset.card_erase_of_mem (by simp [hL]), Finset.card_range, smul_eq_mul]
    omega

/-! ## The waves of the last phase -/

lemma fst_nil (n : ℕ) (pc : PC) (p : ℕ) :
    fst n pc p [] = nst pc (lastPhase n) (lastPhase n) (n - 1) p 1 := rfl

lemma D_lt {n x : ℕ} (h : x ∈ D n) : x < 2 := Nat.digits_lt_base (by norm_num) h

lemma D_getD_lt (n i : ℕ) : (D n).getD i 0 < 2 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (D n)[i]? with
  | none => simp
  | some x => simpa using D_lt (List.mem_of_getElem? h)

lemma D_drop {n i : ℕ} (hi : i < (D n).length) :
    (D n).drop i = (D n).getD i 0 :: (D n).drop (i + 1) := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.drop_eq_getElem_cons hi

lemma D_take {n i : ℕ} (hi : i < (D n).length) :
    (D n).take (i + 1) = (D n).take i ++ [(D n).getD i 0] := by
  rw [List.getD_eq_getElem _ _ hi, List.take_succ, List.getElem?_eq_getElem hi]; rfl

/-- Relaying a pulse of a wave. -/
lemma kind_f_step {n : ℕ} {κ : Kind} (hκ : κ.Ok n) {p : ℕ} (hp : p < n) {k : ℕ} (hk : k < κ.K) :
    recv (κ.f n p k) (!κ.cw n) = (κ.f n p (k + 1), wout (κ.cw n)) := by
  cases κ with
  | comp =>
    simp only [Kind.K] at hk
    obtain rfl : k = 0 := by omega
    simp only [Kind.f, Kind.cw, ite_true, Bool.not_true, wout]
    rw [recv_main_cnt (by omega)]; rfl
  | fin3 =>
    simp only [Kind.K] at hk
    simp only [Kind.f, Kind.cw, Bool.not_false, wout]
    interval_cases k
    · simp only [ite_true, fst_nil, recv_relay]; rfl
    · simp only [fst_nil, show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true]
      rw [recv_main_wait (by simp)]; rfl
    · simp only [fst_nil, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false,
        ite_true, recv_wait_true]
      rfl
  | bit i =>
    simp only [Kind.K] at hk
    simp only [Kind.Ok] at hκ
    simp only [Kind.f, Kind.cw, wout]
    have h2 := D_getD_lt n i
    have h01 : (D n).getD i 0 = 0 ∨ (D n).getD i 0 = 1 := by omega
    interval_cases k
    · rcases h01 with h | h <;> simp only [List.getD_eq_getElem?_getD] at h <;>
        simp [h, fst, nst, recv]
    · rw [D_take hκ]
      rcases h01 with h | h <;> simp only [List.getD_eq_getElem?_getD] at h <;>
        simp [h, fst, nst, recv]
  | end1 =>
    simp only [Kind.K] at hk
    obtain rfl : k = 0 := by omega
    simp [Kind.f, Kind.cw, wout, fst, nst, recv]
  | end2 =>
    simp only [Kind.K] at hk
    obtain rfl : k = 0 := by omega
    simp [Kind.f, Kind.cw, wout, fst, nst, recv]

lemma pipeOk_zero {n L K : ℕ} {cw : Bool} (hK : 0 < K) : PipeOk n L K cw (fun _ => 0) 0 :=
  ⟨hK, fun _ _ _ => ⟨Nat.zero_le _, Nat.zero_le _⟩, Nat.zero_le _⟩

/-- Transit at the start of a wave of `K` pulses in direction `cw`. -/
lemma pipeTr_start {n L K : ℕ} (cw : Bool) (hL : L < n) {p : ℕ} (hp : p < n) (b' : Bool) :
    pipeTr n L K cw (fun _ => 0) 0 p b' =
      (if b' = false ∧ p = nxt n L then (if cw then K else 0) else 0) +
      (if b' = true ∧ p = prv n L then (if cw then 0 else K) else 0) := by
  rw [pipeTr_eq]
  cases cw <;> cases b' <;>
    simp [srcCnt, src, nxt_eq_iff hp hL, prv_eq_iff hp hL]

lemma pipe_st_ne {n : ℕ} {κ : Kind} {a : ℕ → ℕ} {b p : ℕ} (hp : p ≠ lead n) :
    (absPipe n κ a b).st p = κ.f n p (a p) := by simp [absPipe, hp]

lemma pipe_st_lead {n : ℕ} {κ : Kind} {a : ℕ → ℕ} {b : ℕ} :
    (absPipe n κ a b).st (lead n) = κ.g n b := by simp [absPipe]

lemma exit_comp {n : ℕ} {a : ℕ → ℕ} {b : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe .comp a b).Ok n) (hen : (absPipe n .comp a b).En n (lead n) j) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((absPipe n .comp a b).step n (lead n) j) (s'.abs n) := by
  have hb : b = 0 := by have := hok.2.1; simp only [Kind.K] at this; omega
  subst hb
  have hL := lead_lt hn
  refine ⟨.pipe .fin3 (fun _ => 0) 0, ⟨trivial, pipeOk_zero (by simp [Kind.K])⟩, ?_⟩
  refine pipe_exit hn hok hen (by simp [Kind.K]) (σ := gst n (.fin 0) []) (o := out 3 0) ?_ _ ?_ ?_
    ?_ ?_
  · simp only [Kind.g, Kind.cw, gst_nil, Bool.not_true, recv_probe_fin]
  · intro p hp hpL
    simp only [Stage.abs, pipe_st_ne hpL, Kind.f, Kind.K]; rfl
  · simp only [Stage.abs, pipe_st_lead, Kind.g]
  · intro p hp b'
    simp only [Stage.abs, absPipe, Kind.K, Kind.cw, pipeTr_start false hL hp b']
    simp
  · simp only [Stage.abs, absPipe, Kind.base, Kind.K, out_false, out_true, Finset.sum_const_zero]
    omega

lemma recv_fin2 (n : ℕ) : recv (gst n (.fin 2) []) true = sndStart (gst n (.fin 2) []) (D n) := by
  simp [recv, gst, lst, nst, D]

lemma exit_fin3 {n : ℕ} {a : ℕ → ℕ} {b : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe .fin3 a b).Ok n) (hen : (absPipe n .fin3 a b).En n (lead n) j)
    (hb : ¬ b + 1 < Kind.K .fin3) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((absPipe n .fin3 a b).step n (lead n) j) (s'.abs n) := by
  have hb2 : b = 2 := by have := hok.2.1; simp only [Kind.K] at this hb; omega
  subst hb2
  have hL := lead_lt hn
  have hrecv := recv_fin2 n
  rcases hD : D n with _ | ⟨d, r⟩
  · rw [hD] at hrecv
    refine ⟨.pipe .end1 (fun _ => 0) 0, ⟨trivial, pipeOk_zero (by simp [Kind.K])⟩, ?_⟩
    refine pipe_exit hn hok hen (by simp [Kind.K]) (σ := gst n .sndEnd1 []) (o := out 0 1) ?_ _ ?_
      ?_ ?_ ?_
    · simp only [Kind.g, Kind.cw, Bool.not_false, hrecv, sndStart]; rfl
    · intro p hp hpL
      simp only [Stage.abs, pipe_st_ne hpL, Kind.f, Kind.K, hD]; simp
    · simp only [Stage.abs, pipe_st_lead, Kind.g]
    · intro p hp b'
      simp only [Stage.abs, absPipe, Kind.K, Kind.cw, pipeTr_start true hL hp b']
      simp
    · simp only [Stage.abs, absPipe, Kind.base, Kind.K, out_false, out_true, Finset.sum_const_zero,
        hD, List.length_nil]
      have := Nat.sub_add_cancel hn
      nlinarith
  · rw [hD] at hrecv
    have hd : d < 2 := D_lt (by rw [hD]; simp)
    have hlen : 0 < (D n).length := by rw [hD]; simp
    refine ⟨.pipe (.bit 0) (fun _ => 0) 0, ⟨hlen, pipeOk_zero (by simp [Kind.K])⟩, ?_⟩
    refine pipe_exit hn hok hen (by simp [Kind.K]) (σ := gst n (.sndBit 0) (d :: r))
      (o := if d = 0 then out 2 0 else out 0 2) ?_ _ ?_ ?_ ?_ ?_
    · simp only [Kind.g, Kind.cw, Bool.not_false, hrecv, sndStart]; rfl
    · intro p hp hpL
      simp only [Stage.abs, pipe_st_ne hpL, Kind.f, Kind.K]; simp
    · simp only [Stage.abs, pipe_st_lead, Kind.g, List.drop_zero, hD]
    · intro p hp b'
      simp only [Stage.abs, absPipe, Kind.K, Kind.cw, pipeTr_start _ hL hp b', hD]
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> simp
    · simp only [Stage.abs, absPipe, Kind.base, Kind.K, Finset.sum_const_zero]
      have := Nat.sub_add_cancel hn
      rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl <;> simp <;> nlinarith

lemma recv_bit1 (n i : ℕ) (q : Bool) :
    recv (gst n (.sndBit 1) ((D n).drop i)) q =
      sndStart (gst n (.sndBit 1) ((D n).drop i)) ((D n).drop (i + 1)) := by
  simp [recv, gst, lst, nst, List.tail_drop]

lemma exit_bit {n i : ℕ} {a : ℕ → ℕ} {b : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe (.bit i) a b).Ok n) (hen : (absPipe n (.bit i) a b).En n (lead n) j)
    (hb : ¬ b + 1 < Kind.K (.bit i)) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((absPipe n (.bit i) a b).step n (lead n) j) (s'.abs n) := by
  have hb1 : b = 1 := by have := hok.2.1; simp only [Kind.K] at this hb; omega
  subst hb1
  have hi : i < (D n).length := hok.1
  have hL := lead_lt hn
  have hrecv := recv_bit1 n i (!Kind.cw n (.bit i))
  by_cases hi' : i + 1 < (D n).length
  · rw [D_drop hi'] at hrecv
    have hd := D_getD_lt n (i + 1)
    refine ⟨.pipe (.bit (i + 1)) (fun _ => 0) 0, ⟨hi', pipeOk_zero (by simp [Kind.K])⟩, ?_⟩
    refine pipe_exit hn hok hen (by simp [Kind.K])
      (σ := gst n (.sndBit 0) ((D n).drop (i + 1)))
      (o := if (D n).getD (i + 1) 0 = 0 then out 2 0 else out 0 2) ?_ _ ?_ ?_ ?_ ?_
    · simp only [Kind.g, hrecv, sndStart, ← D_drop hi']; rfl
    · intro p hp hpL
      simp only [Stage.abs, pipe_st_ne hpL, Kind.f, Kind.K]; simp
    · simp only [Stage.abs, pipe_st_lead, Kind.g]
    · intro p hp b'
      simp only [Stage.abs, absPipe, Kind.K, Kind.cw, pipeTr_start _ hL hp b']
      rcases (show (D n).getD (i + 1) 0 = 0 ∨ (D n).getD (i + 1) 0 = 1 by omega) with h | h <;>
        simp only [List.getD_eq_getElem?_getD] at h <;> simp [h]
    · simp only [Stage.abs, absPipe, Kind.base, Kind.K, Finset.sum_const_zero]
      have := Nat.sub_add_cancel hn
      rcases (show (D n).getD (i + 1) 0 = 0 ∨ (D n).getD (i + 1) 0 = 1 by omega) with h | h <;>
        simp only [List.getD_eq_getElem?_getD] at h <;> simp [h] <;> nlinarith
  · have hlen : (D n).length = i + 1 := by omega
    rw [List.drop_eq_nil_of_le (as := D n) (i := i + 1) (by omega)] at hrecv
    refine ⟨.pipe .end1 (fun _ => 0) 0, ⟨trivial, pipeOk_zero (by simp [Kind.K])⟩, ?_⟩
    refine pipe_exit hn hok hen (by simp [Kind.K]) (σ := gst n .sndEnd1 []) (o := out 0 1) ?_ _ ?_
      ?_ ?_ ?_
    · simp only [Kind.g, hrecv, sndStart]; rfl
    · intro p hp hpL
      simp only [Stage.abs, pipe_st_ne hpL, Kind.f, Kind.K]
      simp [List.take_of_length_le (show (D n).length ≤ i + 1 by omega)]
    · simp only [Stage.abs, pipe_st_lead, Kind.g]
    · intro p hp b'
      simp only [Stage.abs, absPipe, Kind.K, Kind.cw, pipeTr_start true hL hp b']
      simp
    · simp only [Stage.abs, absPipe, Kind.base, Kind.K, out_false, out_true, Finset.sum_const_zero,
        hlen]
      have := Nat.sub_add_cancel hn
      nlinarith

lemma exit_end1 {n : ℕ} {a : ℕ → ℕ} {b : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe .end1 a b).Ok n) (hen : (absPipe n .end1 a b).En n (lead n) j) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((absPipe n .end1 a b).step n (lead n) j) (s'.abs n) := by
  have hb : b = 0 := by have := hok.2.1; simp only [Kind.K] at this; omega
  subst hb
  have hL := lead_lt hn
  refine ⟨.pipe .end2 (fun _ => 0) 0, ⟨trivial, pipeOk_zero (by simp [Kind.K])⟩, ?_⟩
  refine pipe_exit hn hok hen (by simp [Kind.K]) (σ := gst n .sndEnd2 []) (o := out 1 0) ?_ _ ?_ ?_
    ?_ ?_
  · simp [Kind.g, Kind.cw, gst, lst, nst, recv]
  · intro p hp hpL
    simp only [Stage.abs, pipe_st_ne hpL, Kind.f, Kind.K]; simp
  · simp only [Stage.abs, pipe_st_lead, Kind.g]
  · intro p hp b'
    simp only [Stage.abs, absPipe, Kind.K, Kind.cw, pipeTr_start false hL hp b']
    simp
  · simp only [Stage.abs, absPipe, Kind.base, Kind.K, out_false, out_true, Finset.sum_const_zero]
    omega

lemma exit_end2 {n : ℕ} {a : ℕ → ℕ} {b : ℕ} {j : Bool} (hn : 0 < n)
    (hok : (Stage.pipe .end2 a b).Ok n) (hen : (absPipe n .end2 a b).En n (lead n) j) :
    ∃ s' : Stage, s'.Ok n ∧ Agree n ((absPipe n .end2 a b).step n (lead n) j) (s'.abs n) := by
  have hb : b = 0 := by have := hok.2.1; simp only [Kind.K] at this; omega
  subst hb
  refine ⟨.final, trivial, ?_⟩
  refine pipe_exit hn hok hen (by simp [Kind.K]) (σ := gst n .doneL []) (o := out 0 0) ?_ _ ?_ ?_
    ?_ ?_
  · simp [Kind.g, Kind.cw, gst, lst, nst, recv]
  · intro p hp hpL
    simp only [Stage.abs, absFinal, if_neg hpL, Kind.f, Kind.K]; simp
  · simp only [Stage.abs, absFinal, ite_true]
  · intro p hp b'
    simp [Stage.abs, absFinal]
  · simp only [Stage.abs, absFinal, Kind.base, Kind.K, out_false, out_true, totalPulses, lastBase,
      D]
    omega

/-- Every enabled delivery in a wave stage leads to another stage. -/
theorem stepOk_pipe {n : ℕ} {κ : Kind} {a : ℕ → ℕ} {b : ℕ} (hn : 0 < n)
    (hok : (Stage.pipe κ a b).Ok n) : StepOk n (.pipe κ a b) := by
  intro q j hen
  by_cases hq : q = lead n
  · subst hq
    by_cases hb : b + 1 < κ.K
    · cases κ with
      | fin3 =>
        refine pipe_lead_mid hn hok hen hb ?_
        simp only [Kind.K] at hb
        simp [Kind.g, Kind.cw, gst, lst, nst, recv, hb]
      | bit i =>
        refine pipe_lead_mid hn hok hen hb ?_
        simp only [Kind.K] at hb
        obtain rfl : b = 0 := by omega
        simp [Kind.g, Kind.cw, gst, lst, nst, recv]
      | comp => simp [Kind.K] at hb
      | end1 => simp [Kind.K] at hb
      | end2 => simp [Kind.K] at hb
    · cases κ with
      | comp => exact exit_comp hn hok hen
      | fin3 => exact exit_fin3 hn hok hen hb
      | bit i => exact exit_bit hn hok hen hb
      | end1 => exact exit_end1 hn hok hen
      | end2 => exact exit_end2 hn hok hen
  · exact pipe_node hn hok hq hen (fun k hk => kind_f_step hok.1 hen.1 hk)

end Podc.ContentOblivious.AnonCounting
