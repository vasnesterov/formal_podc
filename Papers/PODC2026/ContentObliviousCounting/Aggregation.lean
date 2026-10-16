import Papers.PODC2026.ContentObliviousCounting.AggregationRun

/-!
# Theorem 1 (efficient aggregation) and Corollary 2 (efficient counting)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026, Theorem 1 and Corollary 2.

**Model.** Oriented ring `oriented n` on `ZMod n`, asynchronous, content-oblivious (pulses),
adversarial scheduler, no failures, deterministic. Node input `(ID, isLeader, x)`, distinct IDs,
exactly one leader `ℓ`. Nodes know neither `n` nor the ID length. The algorithm `aggProg` is a
staged program whose stages are `ComputeOR` (`OR`) or a simulation (Theorem 14) of `misAlg`
(Lemma 26 + one aggregation round); the round procedures `OR`, `CW`, `CCW` are abstract and
assumed to satisfy `RoundSpec` (Theorems 17 and 21) on every virtual ring of active nodes that
contains the leader.

**Results.**
* `aggregation`: with encoded aggregates `E X` (`AggHyp`): every final configuration is
  quiescent and every node outputs `E (multiset of all inputs)`; every execution sends at most
  `3n(λ + 2 log₂ n + 2β + 3) + log₂ n · (78 n λ + 15 n β + 180 n)` pulses; the program is
  composable.
* `theorem1`: the same for a self-decomposable `f` with operator `op` and an encoding
  `enc`/`dec` of its values: every node outputs (the encoding of) `f (⊎ₚ {xₚ})`, with
  `O((λ + β) n log n)` pulses.
* `corollary2`: counting (`f = card`), `O(n log² n)` pulses for `O(log n)`-bit IDs.
-/

namespace Podc.ContentOblivious.Aggregation

open Podc.ContentOblivious Simulation MsgExchange Finset

variable {n : ℕ} [NeZero n] {OR : Proc (Bool × Bool) Bool}
  {CW CCW : Proc (Bool × Bool × Option Bool) (Option Bool)}
  {op2 : List Bool → List Bool → List Bool} {U : Type} [Encodable U] [Inhabited U]
  {w0 : U → List Bool} {x : ZMod n → ℕ × Bool × U} {ℓ : ZMod n} {E : Multiset U → List Bool}

/-- `RoundSpec` for every virtual ring of active nodes containing the leader. -/
def RoundSpecAll (OR : Proc (Bool × Bool) Bool)
    (CW CCW : Proc (Bool × Bool × Option Bool) (Option Bool)) (lead : ZMod n → Bool)
    (ℓ : ZMod n) : Prop :=
  ∀ act : ZMod n → Bool, act ℓ = true → RoundSpec OR CW CCW lead act (vnext act) (vprev act)

omit [Encodable U] [Inhabited U] in
lemma syncInput_eq {k : ℕ} {d : ZMod n → DSt} {j : ZMod n → J}
    (h : ∀ v, sr op2 w0 x k v = (d v, some (j v))) :
    syncInput (aggDriver w0) (oracle op2) x k = j :=
  funext fun u => by simp only [syncInput]; rw [show syncRun _ _ _ k u = _ from h u]; rfl

omit [Encodable U] [Inhabited U] in
/-- The stage classification: every stage of the synchronous run is a `ComputeOR` or the
simulation of phase `t < P`. -/
lemma stage_cases (h : AggHyp op2 w0 x ℓ E) {k : ℕ}
    (hk : k < lamOf x + 3 + 2 * numPhases op2 w0 x h +
      2 * ((phase op2 w0 x (numPhases op2 w0 x h)).2 ℓ).length) :
    (∃ b : ZMod n → Bool, syncInput (aggDriver w0) (oracle op2) x k =
        fun v => .inl ((x v).2.1, b v)) ∨
    (∃ t < numPhases op2 w0 x h, k = lamOf x + 2 + 2 * t ∧
      syncInput (aggDriver w0) (oracle op2) x k = simIn op2 w0 x t) := by
  set P := numPhases op2 w0 x h
  have hP : ∀ s < P, NotDone op2 w0 x s := fun s hs => notDone_of_lt h hs
  have hPd := not_notDone h
  rcases Nat.lt_or_ge k (lamOf x + 1) with h1 | h1
  · left
    have := sr_pre op2 w0 x (i := k + 1) (by omega) (by omega)
    rw [show k + 1 - 1 = k by omega] at this
    exact ⟨_, syncInput_eq this⟩
  rcases Nat.lt_or_ge k (lamOf x + 2 + 2 * P) with h2 | h2
  · obtain ⟨m, rfl⟩ : ∃ m, k = lamOf x + 1 + m := ⟨k - (lamOf x + 1), by omega⟩
    rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · left
      have := (sr_ph_sim op2 w0 x (t := t) fun s hs => hP s (by omega)).1
      rw [show t + t = 2 * t by ring]
      exact ⟨_, syncInput_eq this⟩
    · right
      have := (sr_ph_sim op2 w0 x (t := t) fun s hs => hP s (by omega)).2 (hP t (by omega))
      refine ⟨t, by omega, by ring, ?_⟩
      rw [show lamOf x + 1 + (2 * t + 1) = lamOf x + 2 + 2 * t by ring]
      exact syncInput_eq this
  · left
    obtain ⟨m, rfl⟩ : ∃ m, k = lamOf x + 2 + 2 * P + m := ⟨k - (lamOf x + 2 + 2 * P), by omega⟩
    rcases Nat.even_or_odd m with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have := (sr_diss op2 w0 x h.lead_iff hP hPd t (by omega)).1
      rw [show t + t = 2 * t by ring]
      exact ⟨_, syncInput_eq this⟩
    · have := (sr_diss op2 w0 x h.lead_iff hP hPd t (by omega)).2 (by omega)
      rw [show lamOf x + 2 + 2 * P + (2 * t + 1) = lamOf x + 3 + 2 * P + 2 * t by ring]
      exact ⟨_, syncInput_eq this⟩

omit [Encodable U] [Inhabited U] in
lemma sr_none_add {k : ℕ} {v : ZMod n} (h : (sr op2 w0 x k v).2 = none) (m : ℕ) :
    (sr op2 w0 x (k + m) v).2 = none := by
  induction m with
  | zero => exact h
  | succ m ih => exact sr_none op2 w0 x ih

lemma stage_init (hOR : ∀ a, OR.result (OR.init a).1 = none) (a : J) :
    (stageProc OR CW CCW op2).result ((stageProc OR CW CCW op2).init a).1 = none := by
  rcases a with a | a
  · show (OR.result (OR.init a).1).map Sum.inl = none
    simp [hOR]
  · show ((simProg OR CW CCW (misAlg op2)).result
      ((simProg OR CW CCW (misAlg op2)).init (simInput a)).1).map Sum.inr = none
    simp [simInput, rounds, Simulation.driver, Proc.launch]

lemma oriented_hnxt {A : ZMod n → Bool} (hℓ : A ℓ = true) (v : ZMod n) : A (vnext A v) = true :=
  act_vnext hℓ v

lemma oriented_hprv {A : ZMod n → Bool} (hℓ : A ℓ = true) (v : ZMod n) : A (vprev A v) = true :=
  act_vprev hℓ v

omit [Encodable U] [Inhabited U] in
/-- The synchronous run of the aggregation driver is a schedule (generalized Theorem 9). -/
theorem schedule_agg (hR : RoundSpecAll OR CW CCW (fun v => (x v).2.1) ℓ)
    (h : AggHyp op2 w0 x ℓ E) :
    Schedule (stageProc OR CW CCW op2) (aggDriver w0) (oriented n) x
      (lamOf x + 3 + 2 * numPhases op2 w0 x h +
        2 * ((phase op2 w0 x (numPhases op2 w0 x h)).2 ℓ).length)
      (fun k v => (sr op2 w0 x k v).1) (syncInput (aggDriver w0) (oracle op2) x)
      (fun k => oracle op2 (syncInput (aggDriver w0) (oracle op2) x k)) := by
  set P := numPhases op2 w0 x h
  set L := ((phase op2 w0 x P).2 ℓ).length
  have hP : ∀ s < P, NotDone op2 w0 x s := fun s hs => notDone_of_lt h hs
  have hPd := not_notDone h
  have hR0 := hR (fun _ => true) rfl
  refine schedule_of_syncRun _ (stage_init hR0.or_init) (fun k hk v => ?_)
    (fun v => ?_) (fun k hk => ?_) (fun k hk => ?_)
  · by_contra hc
    simp only [Option.not_isSome_iff_eq_none] at hc
    have := sr_none_add (op2 := op2) (w0 := w0) (x := x) hc (lamOf x + 2 + 2 * P + 2 * L - k)
    rw [show k + (lamOf x + 2 + 2 * P + 2 * L - k) = lamOf x + 2 + 2 * P + 2 * L by omega,
      (sr_diss op2 w0 x h.lead_iff hP hPd L le_rfl).1 v] at this
    cases this
  · rw [show syncRun _ _ _ _ v = _ from sr_halt op2 w0 x h.lead_iff hP hPd v]
  · rcases stage_cases h hk with ⟨b, hb⟩ | ⟨t, ht, -, hsim⟩
    · rw [hb]
      exact (Proc.Hom.inl OR (simStage OR CW CCW op2)).composable (hR0.or_comp b)
    · rw [hsim, simIn_fun]
      have hinv := phaseInv_le h ht.le
      obtain ⟨-, -, -, -, hℓ⟩ := hinv
      have h14 := theorem_14_of_rounds (A := misAlg op2)
        (s0 := fun v => initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v))
        (T := rounds (lamOf x)) (hR _ hℓ) (oriented_hnxt hℓ) (oriented_hprv hℓ)
      exact (Proc.Hom.inr OR (simStage OR CW CCW op2)).composable
        (Proc.precomp_composable (g := simInput) h14.2.2)
  · rcases stage_cases h hk with ⟨b, hb⟩ | ⟨t, ht, -, hsim⟩
    · rw [hb]
      have e : oracle op2 (fun v => (.inl ((x v).2.1, b v) : J)) =
          fun _ => .inl (decide (∃ u, b u = true)) := funext (oracle_or op2 b _)
      rw [e]
      exact (Proc.Hom.inl OR (simStage OR CW CCW op2)).returns (hR0.or_ret b)
    · rw [hsim, simIn_fun]
      have hinv := phaseInv_le h ht.le
      obtain ⟨-, -, -, -, hℓ⟩ := hinv
      have hret := returns_sim (A := misAlg op2)
        (s0 := fun v => initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v))
        (T := rounds (lamOf x)) (hR _ hℓ) (oriented_hnxt hℓ) (oriented_hprv hℓ)
      have e := funext (oracle_sim op2 (fun v => (x v).2.1) (phase op2 w0 x t).1
        (fun v => initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v)) (lamOf x)
        (fun u => rfl))
      rw [e]
      exact (Proc.Hom.inr OR (simStage OR CW CCW op2)).returns
        (Proc.precomp_returns (g := simInput) hret)

/-! ### Pulse complexity -/

/-- Bound on the message length of round `r` of `misAlg`. -/
def lenBound (lam β r : ℕ) : ℕ := if r < lam then wd lam r else if r < lam + 9 then 1 else 1 + β

omit [NeZero n] in
lemma sum_lenBound (lam β : ℕ) :
    ∑ r ∈ range (rounds lam), (15 * n * lenBound lam β r + 3 * n) ≤
      78 * n * lam + 15 * n * β + 180 * n := by
  have h1 : ∑ r ∈ range lam, (15 * n * lenBound lam β r + 3 * n) =
      15 * n * ∑ r ∈ range lam, wd lam r + 3 * n * lam := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, card_range, smul_eq_mul]
    congr 1
    · exact Finset.sum_congr rfl fun r hr => by simp [lenBound, mem_range.1 hr]
    · ring
  have h2 := sum_wd_le lam lam
  rw [rounds, Finset.sum_range_add, h1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, lenBound]
  simp only [show ¬ lam + 0 < lam by omega, show ¬ lam + 1 < lam by omega,
    show ¬ lam + 2 < lam by omega, show ¬ lam + 3 < lam by omega, show ¬ lam + 4 < lam by omega,
    show ¬ lam + 5 < lam by omega, show ¬ lam + 6 < lam by omega, show ¬ lam + 7 < lam by omega,
    show ¬ lam + 8 < lam by omega, show ¬ lam + 9 < lam by omega, show lam + 0 < lam + 9 by omega,
    show lam + 1 < lam + 9 by omega, show lam + 2 < lam + 9 by omega,
    show lam + 3 < lam + 9 by omega, show lam + 4 < lam + 9 by omega,
    show lam + 5 < lam + 9 by omega, show lam + 6 < lam + 9 by omega,
    show lam + 7 < lam + 9 by omega, show lam + 8 < lam + 9 by omega,
    show ¬ lam + 9 < lam + 9 by omega, ite_false, ite_true]
  have := Nat.mul_le_mul_left (15 * n) h2
  nlinarith

omit [Encodable U] [Inhabited U] in
lemma lenAt_le (h : AggHyp op2 w0 x ℓ E) {β : ℕ}
    (hβ : ∀ S : Finset (ZMod n), S.Nonempty → (E (S.val.map fun u => (x u).2.2)).length ≤ β)
    {t : ℕ} (ht : t ≤ numPhases op2 w0 x h) {r : ℕ} (hr : r < rounds (lamOf x)) :
    lenAt (misAlg op2) (phase op2 w0 x t).1 (vnext (phase op2 w0 x t).1)
      (vprev (phase op2 w0 x t).1)
      (fun v => initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v)) r ≤
      lenBound (lamOf x) β r := by
  apply Finset.sup_le
  intro v _
  split_ifs with hv
  · have hlen := msg_len_le op2 (vnext (phase op2 w0 x t).1) (vprev (phase op2 w0 x t).1)
      (lamOf x) (fun v => (x v).2.1) (fun v => (x v).1) (phase op2 w0 x t).2 hr v
    have hβv := phase_len_le h hβ ht hv
    simp only [mcwAt, mccwAt, outMsgs, stateAt, hv, ite_true]
    refine le_trans hlen ?_
    unfold lenBound
    split_ifs <;> omega
  · exact Nat.zero_le _

omit [Encodable U] [Inhabited U] in
lemma sim_cost (hR : RoundSpecAll OR CW CCW (fun v => (x v).2.1) ℓ) (h : AggHyp op2 w0 x ℓ E)
    {β : ℕ}
    (hβ : ∀ S : Finset (ZMod n), S.Nonempty → (E (S.val.map fun u => (x u).2.2)).length ≤ β)
    {t : ℕ} (ht : t ≤ numPhases op2 w0 x h) :
    ∀ c, (stageProc OR CW CCW op2).Reach (oriented n) (simIn op2 w0 x t) c →
      totalSent c ≤ 78 * n * lamOf x + 15 * n * β + 180 * n := by
  obtain ⟨-, -, -, -, hℓ⟩ := phaseInv_le h ht
  have h14 := theorem_14_of_rounds (A := misAlg op2)
    (s0 := fun v => initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v))
    (T := rounds (lamOf x)) (hR _ hℓ) (oriented_hnxt hℓ) (oriented_hprv hℓ)
  have hb : ∀ c, (simProg OR CW CCW (misAlg op2)).Reach (oriented n)
      (fun v => ((x v).2.1, (phase op2 w0 x t).1 v,
        initSt (lamOf x) (x v).2.1 (x v).1 ((phase op2 w0 x t).2 v), rounds (lamOf x))) c →
      totalSent c ≤ 78 * n * lamOf x + 15 * n * β + 180 * n := by
    intro c hc
    refine le_trans (h14.2.1 c hc) (le_trans (Finset.sum_le_sum fun r hr => ?_)
      (sum_lenBound (lamOf x) β))
    have := lenAt_le h hβ ht (mem_range.1 hr)
    have := Nat.mul_le_mul_left (15 * n) this
    omega
  rw [simIn_fun]
  exact (Proc.Hom.inr OR (simStage OR CW CCW op2)).totalSent_le
    (Proc.precomp_totalSent (g := simInput) hb)

lemma sum_sim_indicator (lam P K S : ℕ) (hK : lam + 2 * P + 1 < K) :
    ∑ k ∈ range K, (if ∃ t < P, k = lam + 2 + 2 * t then S else 0) = P * S := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul]
  congr 1
  have : (range K).filter (fun k => ∃ t < P, k = lam + 2 + 2 * t) =
      (range P).image (fun t => lam + 2 + 2 * t) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨-, t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨by omega, t, ht, rfl⟩
  rw [this, Finset.card_image_of_injective _ (fun a b hab => by simp at hab; omega), card_range]

/-- **Theorem 1 (abstract rounds, encoded aggregates).** Under `RoundSpec` for the round
procedures, the aggregation program quiescently terminates with every node holding the encoding
`E X` of the aggregate of the multiset `X` of all inputs; it sends at most
`3n(λ + 2 log₂ n + 2β + 3) + log₂ n · (78 n λ + 15 n β + 180 n)` pulses (`λ` = bound on the ID
lengths, `β` = bound on the lengths of the encoded aggregates of nonempty sets of processes); and it
is composable. -/
theorem aggregation (hR : RoundSpecAll OR CW CCW (fun v => (x v).2.1) ℓ)
    (h : AggHyp op2 w0 x ℓ E) {lam β : ℕ} (hlam : ∀ v, Nat.size (x v).1 ≤ lam)
    (hβ : ∀ S : Finset (ZMod n), S.Nonempty → (E (S.val.map fun u => (x u).2.2)).length ≤ β) :
    (∀ c, (aggProg OR CW CCW op2 w0).Reach (oriented n) x c →
      (aggProg OR CW CCW op2 w0).Final (oriented n) c →
      (aggProg OR CW CCW op2 w0).Quiescent (oriented n) c ∧
        ∀ v, (c.st v).1.out = E (univ.val.map fun u => (x u).2.2)) ∧
    (∀ c, (aggProg OR CW CCW op2 w0).Reach (oriented n) x c →
      totalSent c ≤ 3 * n * (lam + 2 * Nat.log 2 n + 2 * β + 3) +
        Nat.log 2 n * (78 * n * lam + 15 * n * β + 180 * n)) ∧
    (aggProg OR CW CCW op2 w0).Composable (oriented n) x := by
  have hS := schedule_agg hR h
  set P := numPhases op2 w0 x h with hPdef
  set L := ((phase op2 w0 x P).2 ℓ).length with hL
  have hP : ∀ s < P, NotDone op2 w0 x s := fun s hs => notDone_of_lt h hs
  have hPd := not_notDone h
  set S := 78 * n * lamOf x + 15 * n * β + 180 * n with hSdef
  set B : ℕ → ℕ := fun k => 3 * n + if ∃ t < P, k = lamOf x + 2 + 2 * t then S else 0 with hBdef
  have hR0 := hR (fun _ => true) rfl
  have hB : ∀ k < lamOf x + 3 + 2 * P + 2 * L, ∀ c, (stageProc OR CW CCW op2).Reach (oriented n)
      (syncInput (aggDriver w0) (oracle op2) x k) c → totalSent c ≤ B k := by
    intro k hk c hc
    rcases stage_cases h hk with ⟨b, hb⟩ | ⟨t, ht, hkt, hsim⟩
    · rw [hb] at hc
      have := (Proc.Hom.inl OR (simStage OR CW CCW op2)).totalSent_le (hR0.or_bound b) c hc
      simp only [hBdef]; omega
    · rw [hsim] at hc
      have := sim_cost hR h hβ ht.le c hc
      have hif : (∃ t < P, k = lamOf x + 2 + 2 * t) := ⟨t, ht, hkt⟩
      simp only [hBdef, hif, ↓reduceIte]; omega
  have hfin := phase_final h
  have hLβ : L ≤ β := phase_len_le h hβ le_rfl ((hfin.1 ℓ).2 rfl)
  have hPlog : P ≤ Nat.log 2 n := numPhases_le_log h
  have hlamle : lamOf x ≤ lam := Finset.sup_le fun v _ => hlam v
  refine ⟨fun c hc hfc => ?_, fun c hc => ?_, hS.composable hB⟩
  · obtain ⟨hq, hst⟩ := hS.final hc hfc
    refine ⟨hq, fun v => ?_⟩
    rw [hst v]
    simp only
    rw [sr_halt op2 w0 x h.lead_iff hP hPd v]
    simp only [dDiss, List.take_length]
    exact hfin.2
  · have h1 := hS.totalSent_le hB hc
    have h2 : ∑ k ∈ range (lamOf x + 3 + 2 * P + 2 * L), B k =
        3 * n * (lamOf x + 3 + 2 * P + 2 * L) + P * S := by
      simp only [hBdef, Finset.sum_add_distrib, Finset.sum_const, card_range, smul_eq_mul]
      rw [sum_sim_indicator _ _ _ _ (by omega)]; ring
    rw [h2] at h1
    refine le_trans h1 ?_
    have e1 : 3 * n * (lamOf x + 3 + 2 * P + 2 * L) ≤ 3 * n * (lam + 2 * Nat.log 2 n + 2 * β + 3) :=
      Nat.mul_le_mul_left _ (by omega)
    have e2 : S ≤ 78 * n * lam + 15 * n * β + 180 * n := by
      have := Nat.mul_le_mul_left (78 * n) hlamle; omega
    have e3 : P * S ≤ Nat.log 2 n * (78 * n * lam + 15 * n * β + 180 * n) :=
      Nat.mul_le_mul hPlog e2
    omega

/-! ### Theorem 1 -/

section theorem1

variable {Y : Type} (f : Multiset U → Y) (op : Y → Y → Y) (enc : Y → List Bool)
  (dec : List Bool → Y)

/-- The aggregation algorithm of Theorem 1 for `f` with operator `op` and the encoding
`enc`/`dec` of its values: node input `(ID, isLeader, x)`; the initial partial aggregate is
`f {x}`; cluster centres combine values with `op`. -/
abbrev aggAlg (OR : Proc (Bool × Bool) Bool)
    (CW CCW : Proc (Bool × Bool × Option Bool) (Option Bool)) :
    Proc (ℕ × Bool × U) DSt :=
  aggProg OR CW CCW (fun a b => enc (op (dec a) (dec b))) (fun a => enc (f {a}))

variable {f op enc dec}

/-- **Theorem 1** of [Chalopin–Chang–Di Luna–Zhou, PODC 2026] (efficient aggregation), with the
round procedures of the simulator abstract (`RoundSpecAll`). Let `f` be self-decomposable
(`f (X₁ + X₂) = op (f X₁) (f X₂)` for nonempty multisets) with values encoded by `enc`
(`dec ∘ enc = id`) in at most `β` bits for every nonempty set of processes, and let the IDs be
distinct with at most `lam` bits, with a unique leader `ℓ`. Then the algorithm quiescently
terminates with every process holding `enc (f (⊎ₚ {xₚ}))` (so `dec` of its output is the
aggregate), sends at most `3n(lam + 2 log₂ n + 2β + 3) + log₂ n · (78 n lam + 15 n β + 180 n)`
pulses, i.e. `O((lam + β) n log n)`, and is composable. -/
theorem theorem1 (hR : RoundSpecAll OR CW CCW (fun v => (x v).2.1) ℓ)
    (hid : Function.Injective fun v => (x v).1) (hlead : ∀ v, (x v).2.1 = true ↔ v = ℓ)
    (hdec : ∀ y, dec (enc y) = y)
    (hself : ∀ X₁ X₂, X₁ ≠ 0 → X₂ ≠ 0 → f (X₁ + X₂) = op (f X₁) (f X₂))
    {lam β : ℕ} (hlam : ∀ v, Nat.size (x v).1 ≤ lam)
    (hβ : ∀ S : Finset (ZMod n), S.Nonempty → (enc (f (S.val.map fun u => (x u).2.2))).length ≤ β) :
    (∀ c, (aggAlg f op enc dec OR CW CCW).Reach (oriented n) x c →
      (aggAlg f op enc dec OR CW CCW).Final (oriented n) c →
      (aggAlg f op enc dec OR CW CCW).Quiescent (oriented n) c ∧
        ∀ v, (c.st v).1.out = enc (f (univ.val.map fun u => (x u).2.2)) ∧
          dec (c.st v).1.out = f (univ.val.map fun u => (x u).2.2)) ∧
    (∀ c, (aggAlg f op enc dec OR CW CCW).Reach (oriented n) x c →
      totalSent c ≤ 3 * n * (lam + 2 * Nat.log 2 n + 2 * β + 3) +
        Nat.log 2 n * (78 * n * lam + 15 * n * β + 180 * n)) ∧
    (aggAlg f op enc dec OR CW CCW).Composable (oriented n) x := by
  have h : AggHyp (fun a b => enc (op (dec a) (dec b))) (fun a => enc (f {a})) x ℓ
      (fun X => enc (f X)) :=
    ⟨hid, hlead, fun _ => rfl, fun X Y hX hY => by simp only [hdec, hself X Y hX hY]⟩
  obtain ⟨h1, h2, h3⟩ := aggregation hR h hlam hβ
  refine ⟨fun c hc hfc => ?_, h2, h3⟩
  obtain ⟨hq, hout⟩ := h1 c hc hfc
  exact ⟨hq, fun v => ⟨hout v, by rw [hout v, hdec]⟩⟩

/-- Termination part of Theorem 1: every execution of the aggregation algorithm is finite, i.e.
every reachable configuration can be extended to a final one (which is quiescent with the right
output by `theorem1`). -/
theorem theorem1_terminates (hR : RoundSpecAll OR CW CCW (fun v => (x v).2.1) ℓ)
    (hid : Function.Injective fun v => (x v).1) (hlead : ∀ v, (x v).2.1 = true ↔ v = ℓ)
    (hdec : ∀ y, dec (enc y) = y)
    (hself : ∀ X₁ X₂, X₁ ≠ 0 → X₂ ≠ 0 → f (X₁ + X₂) = op (f X₁) (f X₂))
    {lam β : ℕ} (hlam : ∀ v, Nat.size (x v).1 ≤ lam)
    (hβ : ∀ S : Finset (ZMod n), S.Nonempty → (enc (f (S.val.map fun u => (x u).2.2))).length ≤ β)
    {c : Config (ZMod n) (aggAlg f op enc dec OR CW CCW).State}
    (hc : (aggAlg f op enc dec OR CW CCW).Reach (oriented n) x c) :
    ∃ c', Relation.ReflTransGen ((aggAlg f op enc dec OR CW CCW).Step (oriented n)) c c' ∧
      (aggAlg f op enc dec OR CW CCW).Final (oriented n) c' :=
  exists_final (theorem1 hR hid hlead hdec hself hlam hβ).2.1 hc

end theorem1

/-! ### Corollary 2 -/

section corollary2

/-- Binary encoding of natural numbers (little-endian digits). -/
def natEnc (m : ℕ) : List Bool := (Nat.digits 2 m).map fun d => decide (d = 1)

/-- Decoding of `natEnc`. -/
def natDec (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

lemma natDec_natEnc (m : ℕ) : natDec (natEnc m) = m := by
  unfold natDec natEnc
  rw [List.map_map]
  have : ∀ d ∈ Nat.digits 2 m, (Bool.toNat ∘ fun d => decide (d = 1)) d = d := by
    intro d hd
    have := Nat.digits_lt_base (by norm_num) hd
    interval_cases d <;> rfl
  rw [List.map_congr_left this, List.map_id', Nat.ofDigits_digits]

lemma natEnc_length_le {m k : ℕ} (hm : m ≤ k) : (natEnc m).length ≤ Nat.log 2 k + 1 := by
  unfold natEnc
  rw [List.length_map]
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  · rw [Nat.length_digits _ _ (by norm_num) hm0.ne']
    have := Nat.log_mono_right (b := 2) hm
    omega

/-- The counting algorithm of Corollary 2: aggregation of `f X = |X|` (inputs `Unit`). -/
abbrev countAlg (OR : Proc (Bool × Bool) Bool)
    (CW CCW : Proc (Bool × Bool × Option Bool) (Option Bool)) : Proc (ℕ × Bool × Unit) DSt :=
  aggAlg (fun X : Multiset Unit => Multiset.card X) (· + ·) natEnc natDec OR CW CCW

/-- **Corollary 2** of [Chalopin–Chang–Di Luna–Zhou, PODC 2026] (efficient counting), with the
round procedures abstract (`RoundSpecAll`): on an oriented content-oblivious ring of `n` processes
with distinct IDs of at most `lam` bits and a unique leader, the counting algorithm quiescently
terminates with every process holding (the binary encoding of) `n`, and sends at most
`3n(lam + 4 log₂ n + 5) + log₂ n · (78 n lam + 15 n (log₂ n + 1) + 180 n)` pulses. -/
theorem corollary2 {x : ZMod n → ℕ × Bool × Unit}
    (hR : RoundSpecAll OR CW CCW (fun v => (x v).2.1) ℓ)
    (hid : Function.Injective fun v => (x v).1) (hlead : ∀ v, (x v).2.1 = true ↔ v = ℓ)
    {lam : ℕ} (hlam : ∀ v, Nat.size (x v).1 ≤ lam) :
    (∀ c, (countAlg OR CW CCW).Reach (oriented n) x c → (countAlg OR CW CCW).Final (oriented n) c →
      (countAlg OR CW CCW).Quiescent (oriented n) c ∧ ∀ v, natDec (c.st v).1.out = n) ∧
    (∀ c, (countAlg OR CW CCW).Reach (oriented n) x c →
      totalSent c ≤ 3 * n * (lam + 4 * Nat.log 2 n + 5) +
        Nat.log 2 n * (78 * n * lam + 15 * n * (Nat.log 2 n + 1) + 180 * n)) ∧
    (countAlg OR CW CCW).Composable (oriented n) x := by
  have hβ : ∀ S : Finset (ZMod n), S.Nonempty →
      (natEnc (Multiset.card (S.val.map fun u => (x u).2.2))).length ≤ Nat.log 2 n + 1 := by
    intro S _
    apply natEnc_length_le
    rw [Multiset.card_map, Finset.card_val]
    exact le_trans (Finset.card_le_univ S) (by simp)
  obtain ⟨h1, h2, h3⟩ := theorem1 (f := fun X : Multiset Unit => Multiset.card X) (op := (· + ·))
    hR hid hlead natDec_natEnc (fun X₁ X₂ _ _ => Multiset.card_add X₁ X₂) hlam hβ
  refine ⟨fun c hc hfc => ?_, fun c hc => ?_, h3⟩
  · obtain ⟨hq, hout⟩ := h1 c hc hfc
    refine ⟨hq, fun v => ?_⟩
    rw [(hout v).2]
    simp
  · have := h2 c hc
    have e : 3 * n * (lam + 2 * Nat.log 2 n + 2 * (Nat.log 2 n + 1) + 3) =
        3 * n * (lam + 4 * Nat.log 2 n + 5) := by ring
    omega

/-- Corollary 2 in `O(n log² n)` form: with IDs of at most `C (log₂ n + 1)` bits, the counting
algorithm sends at most `(81 C + 216) · n · (log₂ n + 1)²` pulses. -/
theorem corollary2_bigO {x : ZMod n → ℕ × Bool × Unit}
    (hR : RoundSpecAll OR CW CCW (fun v => (x v).2.1) ℓ)
    (hid : Function.Injective fun v => (x v).1) (hlead : ∀ v, (x v).2.1 = true ↔ v = ℓ)
    {C : ℕ} (hlam : ∀ v, Nat.size (x v).1 ≤ C * (Nat.log 2 n + 1))
    (c : Config (ZMod n) (countAlg OR CW CCW).State)
    (hc : (countAlg OR CW CCW).Reach (oriented n) x c) :
    totalSent c ≤ (81 * C + 216) * n * (Nat.log 2 n + 1) ^ 2 := by
  have := (corollary2 hR hid hlead hlam).2.1 c hc
  refine le_trans this ?_
  set L := Nat.log 2 n
  nlinarith [Nat.zero_le L, Nat.zero_le n, Nat.zero_le C, Nat.zero_le (C * n), Nat.zero_le (n * L),
    Nat.zero_le (C * n * L)]

end corollary2

end Podc.ContentOblivious.Aggregation
