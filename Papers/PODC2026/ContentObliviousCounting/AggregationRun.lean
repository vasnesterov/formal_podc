import Papers.PODC2026.ContentObliviousCounting.AggregationPhases

/-!
# The synchronous run of the aggregation driver

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, proof of Theorem 1.

We compute the synchronous run (`syncRun`, see `Podc/ContentOblivious/Staged.lean`) of the
aggregation driver with the exact stage results (`oracle`): all nodes go through the same stages
in lockstep:
* stages `0 … λ`: λ-preprocessing (`ComputeOR(size(ID) ≥ i)`, `i = 1 … λ+1`, `λ` = maximal ID
  length);
* stages `λ + 2t` (`t ≤ P`): loneliness test of phase `t`; stages `λ + 2t + 1` (`t < P`):
  simulation of `misAlg` on the active nodes of phase `t`;
* stages `λ + 2P + 1 + 2k` (`k ≤ L`) and `λ + 2P + 2 + 2k` (`k < L`): dissemination of the `L`
  bits of the final aggregate;
* after `K = λ + 2P + 2L + 2` stages every node halts with the final aggregate.
-/

namespace Podc.ContentOblivious.Aggregation

open Podc.ContentOblivious Simulation Finset

variable {n : ℕ} [NeZero n] (op2 : List Bool → List Bool → List Bool) {U : Type}
  (w0 : U → List Bool) (x : ZMod n → ℕ × Bool × U)

/-- Shorthand for the synchronous run. -/
abbrev sr : ℕ → ZMod n → DSt × Option J := syncRun (aggDriver w0) (oracle op2) x

lemma sr_next {k : ℕ} {d : ZMod n → DSt} {j : ZMod n → J}
    (h : ∀ v, sr op2 w0 x k v = (d v, some (j v))) (v : ZMod n) :
    sr op2 w0 x (k + 1) v = (aggDriver w0).next (d v) (oracle op2 j v) := by
  simp only [sr] at h ⊢
  have hj : syncInput (aggDriver w0) (oracle op2) x k = j := funext fun u => by
    simp only [syncInput]; rw [h u]; rfl
  rw [syncRun_succ _ _ _ (by rw [h v]; rfl), hj, h v]

lemma sr_none {k : ℕ} {v : ZMod n} (h : (sr op2 w0 x k v).2 = none) :
    (sr op2 w0 x (k + 1) v).2 = none := by
  simp only [sr] at h ⊢
  simp only [syncRun]
  rw [h]; exact h

lemma oracle_or (b : ZMod n → Bool) (l : ZMod n → Bool) (v : ZMod n) :
    oracle op2 (fun u => (.inl (l u, b u) : J)) v = .inl (decide (∃ u, b u = true)) := by
  simp only [oracle, orBit]
  congr 1

lemma oracle_sim (l a : ZMod n → Bool) (s : ZMod n → MState) (lam : ℕ)
    (hs : ∀ u, (s u).lam = lam) (v : ZMod n) :
    oracle op2 (fun u => (.inr (l u, a u, s u) : J)) v =
      .inr ⟨l v, a v, stateAt (misAlg op2) a (vnext a) (vprev a) s (rounds lam) v,
        rounds lam, rounds lam⟩ := by
  simp [oracle, simAct, simS0, hs]

/-! ### Trajectory -/

/-- Local state during the λ-preprocessing. -/
def dPre (i : ℕ) (v : ZMod n) : DSt := ⟨(x v).1, (x v).2.1, w0 (x v).2.2, .pre i, 0, true, []⟩

/-- Local state at the loneliness test of phase `t`. -/
def dPh (t : ℕ) (v : ZMod n) : DSt :=
  ⟨(x v).1, (x v).2.1, (phase op2 w0 x t).2 v, .lonely, lamOf x, (phase op2 w0 x t).1 v, []⟩

/-- Local state during the dissemination of bit `k`. -/
def dDiss (P : ℕ) (y : List Bool) (m : Mode) (k : ℕ) (v : ZMod n) : DSt :=
  ⟨(x v).1, (x v).2.1, (phase op2 w0 x P).2 v, m, lamOf x, (phase op2 w0 x P).1 v, y.take k⟩

lemma exists_size_ge {i : ℕ} (hil : i ≤ lamOf x) : ∃ u, i ≤ Nat.size (x u).1 := by
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_eq_sup (univ : Finset (ZMod n)) univ_nonempty
    (fun v => Nat.size (x v).1)
  exact ⟨u, by unfold lamOf at hil; omega⟩

lemma sr_pre {i : ℕ} (hi : 1 ≤ i) (hil : i ≤ lamOf x + 1) (v : ZMod n) :
    sr op2 w0 x (i - 1) v =
      (dPre w0 x i v, some (.inl ((x v).2.1, decide (i ≤ Nat.size (x v).1)))) := by
  induction i, hi using Nat.le_induction generalizing v with
  | base => rfl
  | succ i hi ih =>
    rw [show i + 1 - 1 = (i - 1) + 1 by omega, sr_next op2 w0 x (ih (by omega)), oracle_or]
    obtain ⟨u, hu⟩ := exists_size_ge x (i := i) (by omega)
    simp [aggDriver, dPre, show ∃ u, i ≤ Nat.size (x u).1 from ⟨u, hu⟩]

lemma not_size_ge (u : ZMod n) : ¬ lamOf x + 1 ≤ Nat.size (x u).1 := by
  have := Finset.le_sup (f := fun v => Nat.size (x v).1) (mem_univ u)
  unfold lamOf; omega

lemma sr_ph0 (v : ZMod n) :
    sr op2 w0 x (lamOf x + 1) v =
      (dPh op2 w0 x 0 v, some (.inl ((x v).2.1, (phase op2 w0 x 0).1 v && !(x v).2.1))) := by
  have h := sr_pre op2 w0 x (i := lamOf x + 1) (by omega) le_rfl
  rw [show lamOf x + 1 - 1 = lamOf x by omega] at h
  rw [sr_next op2 w0 x h, oracle_or]
  have : ∀ u, Nat.size (x u).1 ≤ lamOf x :=
    fun u => Finset.le_sup (f := fun v => Nat.size (x v).1) (mem_univ u)
  simp [aggDriver, dPre, dPh, this, phase]

/-- Local state during the simulation stage of phase `t`. -/
def dSim (t : ℕ) (v : ZMod n) : DSt :=
  ⟨(x v).1, (x v).2.1, (phase op2 w0 x t).2 v, .sim, lamOf x, (phase op2 w0 x t).1 v, []⟩

/-- Input of the simulation stage of phase `t`. -/
def simIn (t : ℕ) (v : ZMod n) : J :=
  .inr ((x v).2.1, (phase op2 w0 x t).1 v,
    initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v))

lemma simIn_fun (t : ℕ) : simIn op2 w0 x t = fun v => (.inr ((x v).2.1, (phase op2 w0 x t).1 v,
    initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v)) : J) := rfl

lemma sr_ph_sim {t : ℕ} (hnd : ∀ s < t, NotDone op2 w0 x s) :
    (∀ v, sr op2 w0 x (lamOf x + 1 + 2 * t) v =
      (dPh op2 w0 x t v, some (.inl ((x v).2.1, (phase op2 w0 x t).1 v && !(x v).2.1)))) ∧
    (NotDone op2 w0 x t →
      ∀ v, sr op2 w0 x (lamOf x + 2 + 2 * t) v =
        (dSim op2 w0 x t v, some (simIn op2 w0 x t v))) := by
  induction t with
  | zero =>
    have h0 := sr_ph0 op2 w0 x
    refine ⟨h0, fun hnd0 v => ?_⟩
    rw [sr_next op2 w0 x h0, oracle_or]
    obtain ⟨u, hu, hul⟩ := hnd0
    have : ∃ u, ((phase op2 w0 x 0).1 u && !(x u).2.1) = true := ⟨u, by simp [hu, hul]⟩
    simp only [decide_eq_true this]
    simp [aggDriver, dPh, dSim, simIn]
  | succ t ih =>
    obtain ⟨-, hsim⟩ := ih fun s hs => hnd s (by omega)
    have hsim' := hsim (hnd t (by omega))
    have hph : ∀ v, sr op2 w0 x (lamOf x + 1 + 2 * (t + 1)) v =
        (dPh op2 w0 x (t + 1) v,
          some (.inl ((x v).2.1, (phase op2 w0 x (t + 1)).1 v && !(x v).2.1))) := by
      intro v
      rw [show lamOf x + 1 + 2 * (t + 1) = lamOf x + 2 + 2 * t + 1 by ring]
      rw [sr_next op2 w0 x hsim' v, simIn_fun, oracle_sim op2 _ _ _ (lamOf x) (fun u => rfl)]
      simp [aggDriver, dSim, dPh, phase]
    refine ⟨hph, fun hnd1 v => ?_⟩
    rw [show lamOf x + 2 + 2 * (t + 1) = lamOf x + 1 + 2 * (t + 1) + 1 by ring,
      sr_next op2 w0 x hph, oracle_or]
    obtain ⟨u, hu, hul⟩ := hnd1
    have : ∃ u, ((phase op2 w0 x (t + 1)).1 u && !(x u).2.1) = true := ⟨u, by simp [hu, hul]⟩
    simp only [decide_eq_true this]
    simp [aggDriver, dPh, dSim, simIn]

lemma take_getD_succ (y : List Bool) {k : ℕ} (hk : k < y.length) :
    y.take k ++ [y.getD k false] = y.take (k + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]; simp [List.getD_eq_getElem?_getD, hk]

section diss

variable {ℓ : ZMod n} (hlead : ∀ v, (x v).2.1 = true ↔ v = ℓ) {P : ℕ}
  (hP : ∀ s < P, NotDone op2 w0 x s) (hPd : ¬ NotDone op2 w0 x P)

omit [NeZero n] in
include hlead in
lemma exists_lead_and (b : ZMod n → Bool) : (∃ u, ((x u).2.1 && b u) = true) ↔ b ℓ = true := by
  constructor
  · rintro ⟨u, hu⟩
    simp only [Bool.and_eq_true] at hu
    rw [← (hlead u).1 hu.1]; exact hu.2
  · intro h; exact ⟨ℓ, by simp [(hlead ℓ).2 rfl, h]⟩

include hlead hP hPd in
lemma sr_diss (k : ℕ) (hk : k ≤ ((phase op2 w0 x P).2 ℓ).length) :
    (∀ v, sr op2 w0 x (lamOf x + 2 + 2 * P + 2 * k) v =
      (dDiss op2 w0 x P ((phase op2 w0 x P).2 ℓ) (.more k) k v,
        some (.inl ((x v).2.1, (x v).2.1 && decide (k < ((phase op2 w0 x P).2 v).length))))) ∧
    (k < ((phase op2 w0 x P).2 ℓ).length →
      ∀ v, sr op2 w0 x (lamOf x + 3 + 2 * P + 2 * k) v =
      (dDiss op2 w0 x P ((phase op2 w0 x P).2 ℓ) (.bit k) k v,
        some (.inl ((x v).2.1, (x v).2.1 && ((phase op2 w0 x P).2 v).getD k false)))) := by
  set y := (phase op2 w0 x P).2 ℓ with hy
  have hbit : ∀ k, k < y.length → (∀ v, sr op2 w0 x (lamOf x + 2 + 2 * P + 2 * k) v =
      (dDiss op2 w0 x P y (.more k) k v,
        some (.inl ((x v).2.1, (x v).2.1 && decide (k < ((phase op2 w0 x P).2 v).length))))) →
      ∀ v, sr op2 w0 x (lamOf x + 3 + 2 * P + 2 * k) v =
      (dDiss op2 w0 x P y (.bit k) k v,
        some (.inl ((x v).2.1, (x v).2.1 && ((phase op2 w0 x P).2 v).getD k false))) := by
    intro k hk hm v
    rw [show lamOf x + 3 + 2 * P + 2 * k = lamOf x + 2 + 2 * P + 2 * k + 1 by ring,
      sr_next op2 w0 x hm, oracle_or]
    have : ∃ u, ((x u).2.1 && decide (k < ((phase op2 w0 x P).2 u).length)) = true :=
      (exists_lead_and x hlead _).2 (by simpa [← hy] using hk)
    simp only [decide_eq_true this]
    simp [aggDriver, dDiss]
  induction k with
  | zero =>
    have h0 : ∀ v, sr op2 w0 x (lamOf x + 2 + 2 * P + 2 * 0) v =
        (dDiss op2 w0 x P y (.more 0) 0 v,
          some (.inl ((x v).2.1, (x v).2.1 && decide (0 < ((phase op2 w0 x P).2 v).length)))) := by
      intro v
      rw [show lamOf x + 2 + 2 * P + 2 * 0 = lamOf x + 1 + 2 * P + 1 by ring,
        sr_next op2 w0 x (sr_ph_sim op2 w0 x hP).1, oracle_or]
      have : ¬ ∃ u, ((phase op2 w0 x P).1 u && !(x u).2.1) = true := by
        rintro ⟨u, hu⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hu
        exact hPd ⟨u, hu.1, hu.2⟩
      simp only [decide_eq_false this]
      simp [aggDriver, dDiss, dPh]
    exact ⟨h0, fun hk v => hbit 0 hk h0 v⟩
  | succ k ih =>
    obtain ⟨-, hb⟩ := ih (by omega)
    have hb' := hb (by omega)
    have hm : ∀ v, sr op2 w0 x (lamOf x + 2 + 2 * P + 2 * (k + 1)) v =
        (dDiss op2 w0 x P y (.more (k + 1)) (k + 1) v,
          some (.inl ((x v).2.1, (x v).2.1 &&
            decide (k + 1 < ((phase op2 w0 x P).2 v).length)))) := by
      intro v
      rw [show lamOf x + 2 + 2 * P + 2 * (k + 1) = lamOf x + 3 + 2 * P + 2 * k + 1 by ring,
        sr_next op2 w0 x hb', oracle_or]
      have : decide (∃ u, ((x u).2.1 && ((phase op2 w0 x P).2 u).getD k false) = true) =
          y.getD k false := by
        rw [Bool.eq_iff_iff, decide_eq_true_iff, exists_lead_and x hlead]
      rw [this]
      simp only [aggDriver, dDiss]
      rw [take_getD_succ y (by omega)]
    exact ⟨hm, fun hk v => hbit (k + 1) hk hm v⟩

include hlead hP hPd in
lemma sr_halt (v : ZMod n) :
    sr op2 w0 x (lamOf x + 3 + 2 * P + 2 * ((phase op2 w0 x P).2 ℓ).length) v =
      (dDiss op2 w0 x P ((phase op2 w0 x P).2 ℓ) .done ((phase op2 w0 x P).2 ℓ).length v,
        none) := by
  set L := ((phase op2 w0 x P).2 ℓ).length
  rw [show lamOf x + 3 + 2 * P + 2 * L = lamOf x + 2 + 2 * P + 2 * L + 1 by ring,
    sr_next op2 w0 x (sr_diss op2 w0 x hlead hP hPd L le_rfl).1, oracle_or]
  have : ¬ ∃ u, ((x u).2.1 && decide (L < ((phase op2 w0 x P).2 u).length)) = true := by
    rw [exists_lead_and x hlead]; simp [L]
  simp only [decide_eq_false this]
  simp [aggDriver, dDiss]

end diss

end Podc.ContentOblivious.Aggregation
