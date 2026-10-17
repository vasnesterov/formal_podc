import Papers.PODC2023.LeaderTradeoffs.Isolation
import Cslib.Foundations.Data.Real.Logb

/-!
# The time–message tradeoff lower bound (Lemma 3.9 and Theorem 3.8, corrected)

Fix `n = m + 1 = 2^k`, a deterministic algorithm `A` that elects a leader within `T` rounds for
all ID assignments from a universe `U` and all port maps, and sends at most `n · f` messages,
`1 < f ≤ 2^c`. Write `σ_r = (c + 1) r`.

`Good A k c r V` (Lemma 3.9): for every ID assignment `I ⊆ V` there is a partial port mapping,
valid through round `r`, whose links never leave the blocks of a partition of `I` into
`2^(k - σ_r)` blocks of exactly `2^σ_r` nodes.

`good_step` is the induction step of Lemma 3.9 (with the pruning of costly blocks, Claim 1):
removing fewer than `n` further IDs, the adversary can keep the partition for one more round,
merging `2^(c+1)` blocks into one.

`tradeoff_lower_bound`: if `U` has at least `(T + 2) n` IDs then `k ≤ (c + 1) T`.

**Index shift.** Lemma 3.9 controls the communication graph `G_r`, which only contains messages of
rounds `< r`; the messages of the last round `T` merge further blocks. The paper applies the lemma
with `r = T` and therefore claims `T > (log n - 1)/(⌈log f⌉ + 1) + 1`; the argument only gives
(and the truth only allows, see `Counterexamples.lean`) `T > (log n - 1)/(⌈log f⌉ + 1)`
(`theorem_3_8_corrected`).
-/

open Classical Finset Function

namespace LeaderTradeoffs

variable {m : ℕ}

theorem nat_div_eq_iff {x b g : ℕ} (hb : 0 < b) : x / b = g ↔ g * b ≤ x ∧ x < (g + 1) * b := by
  have h1 : g ≤ x / b ↔ g * b ≤ x := Nat.le_div_iff_mul_le hb
  have h2 : x / b < g + 1 ↔ x < (g + 1) * b := Nat.div_lt_iff_lt_mul hb
  constructor
  · intro h
    exact ⟨h1.1 (by omega), h2.1 (by omega)⟩
  · rintro ⟨ha, hc⟩
    have := h1.2 ha
    have := h2.2 hc
    omega

/-- Restricting a partial execution to a closed subset. -/
theorem restrict {A : Algorithm m} {p : PortMap m} {I X : Finset ℕ} {r : ℕ} (hp : WF p I)
    (hXI : X ⊆ I) (hcl : ∀ u ∈ X, ∀ j v, p u j = some v → v ∈ X) (hv : Valid A p r I) :
    ∃ q : PortMap m, WF q X ∧ Valid A q r X ∧ ∀ r', ∀ u ∈ X, run A q r' u = run A p r' u := by
  let q : PortMap m := fun u => if u ∈ X then p u else fun _ => none
  have hq : ∀ u ∈ X, q u = p u := fun u hu => by simp [q, hu]
  have hrun : ∀ r', ∀ u ∈ X, run A q r' u = run A p r' u :=
    run_congr hq (fun u hu j v h => hcl u hu j v (by rw [← hq u hu]; exact h))
  refine ⟨q, ⟨?_, ?_, ?_, ?_⟩, ?_, hrun⟩
  · intro u hu j v h; rw [hq u hu] at h; exact hcl u hu j v h
  · intro u hu j h; rw [hq u hu] at h; exact hp.ne u (hXI hu) j h
  · intro u hu i j v hi hj; rw [hq u hu] at hi hj; exact hp.inj u (hXI hu) i j v hi hj
  · intro u hu j v h
    rw [hq u hu] at h
    obtain ⟨i, hi⟩ := hp.symm u (hXI hu) j v h
    exact ⟨i, by rw [hq v (hcl u hu j v h)]; exact hi⟩
  · intro r' hr' u hu j hj
    rw [hq u hu] at hj
    rw [hrun r' u hu]
    exact hv r' hr' u (hXI hu) j hj

/-- The invariant of Lemma 3.9 after `r` rounds, for all ID assignments from `V`. -/
def Good (A : Algorithm m) (k c r : ℕ) (V : Finset ℕ) : Prop :=
  ∀ I ⊆ V, I.card = m + 1 → ∃ (p : PortMap m) (blk : ℕ → ℕ), WF p I ∧ Valid A p r I ∧
    (∀ u ∈ I, blk u < 2 ^ (k - (c + 1) * r)) ∧
    (∀ i < 2 ^ (k - (c + 1) * r), (I.filter fun u => blk u = i).card = 2 ^ ((c + 1) * r)) ∧
    (∀ u ∈ I, ∀ j v, p u j = some v → blk v = blk u)

/-- Base case of Lemma 3.9: before round 1 every node is its own block. -/
theorem good_zero {A : Algorithm m} {k c : ℕ} (hk : m + 1 = 2 ^ k) (V : Finset ℕ) :
    Good A k c 0 V := by
  intro I _ hcard
  let e := I.equivFin
  refine ⟨fun _ _ => none, fun u => if h : u ∈ I then (e ⟨u, h⟩ : ℕ) else 0,
    ⟨by simp, by simp, by simp, by simp⟩, fun r' hr' => absurd hr' (Nat.not_lt_zero _), ?_, ?_,
    by simp⟩
  · intro u hu
    simp only [hu, dite_true, mul_zero, Nat.sub_zero, ← hk, ← hcard]
    exact (e ⟨u, hu⟩).2
  · intro i hi
    simp only [mul_zero, Nat.sub_zero, pow_zero] at hi ⊢
    have hi' : i < I.card := by rw [hcard, hk]; exact hi
    rw [Finset.card_eq_one]
    refine ⟨(e.symm ⟨i, hi'⟩).1, ?_⟩
    ext u
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hu, h⟩
      simp only [hu, dite_true] at h
      have : e ⟨u, hu⟩ = ⟨i, hi'⟩ := Fin.ext h
      rw [← this, Equiv.symm_apply_apply]
    · rintro rfl
      refine ⟨(e.symm ⟨i, hi'⟩).2, ?_⟩
      simp

/-- A group of `2^t` consecutive blocks has `2^(σ+t)` nodes. -/
theorem card_group {I : Finset ℕ} {blk : ℕ → ℕ} {σ t K : ℕ}
    (hbcard : ∀ i < 2 ^ K, (I.filter fun u => blk u = i).card = 2 ^ σ) (g : ℕ)
    (hg : (g + 1) * 2 ^ t ≤ 2 ^ K) :
    (I.filter fun v => blk v / 2 ^ t = g).card = 2 ^ (σ + t) := by
  have ht : 0 < 2 ^ t := by positivity
  have heq : (I.filter fun v => blk v / 2 ^ t = g) =
      (Finset.Ico (g * 2 ^ t) ((g + 1) * 2 ^ t)).biUnion fun i => I.filter fun u => blk u = i := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_Ico, nat_div_eq_iff ht]
    constructor
    · rintro ⟨hv, h1, h2⟩
      exact ⟨blk v, ⟨h1, h2⟩, hv, rfl⟩
    · rintro ⟨i, ⟨h1, h2⟩, hv, rfl⟩
      exact ⟨hv, h1, h2⟩
  rw [heq, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun i hi => hbcard i (by
      simp only [Finset.mem_Ico] at hi; omega)]
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, pow_add]
    rw [show (g + 1) * 2 ^ t - g * 2 ^ t = 2 ^ t by rw [add_mul, one_mul]; omega, mul_comm]
  · intro i _ j _ hij
    exact Finset.disjoint_filter.2 fun u _ h1 h2 => hij (h1.symm.trans h2)

/-- The induction step of Lemma 3.9, including the pruning of costly blocks (Claim 1). -/
theorem good_step {A : Algorithm m} {U : Finset ℕ} {k c T : ℕ} (hk : m + 1 = 2 ^ k) {f : ℝ}
    (hf : 1 < f) (hfc : f ≤ 2 ^ c) (hM : MsgBound A U T ((m + 1) * f)) {r : ℕ} (hr : r < T)
    (hσ : (c + 1) * (r + 1) ≤ k) {V : Finset ℕ} (hVU : V ⊆ U) (hV : Good A k c r V) :
    ∃ V' ⊆ V, V.card ≤ V'.card + (m + 1) ∧ Good A k c (r + 1) V' := by
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = (c + 1) * r := ⟨_, rfl⟩
  have hσt : (c + 1) * (r + 1) = σ + (c + 1) := by rw [hσdef]; ring
  have hσk : σ + (c + 1) ≤ k := by rw [← hσt]; exact hσ
  have hnb : 2 ^ (k - σ) * 2 ^ σ = m + 1 := by
    rw [← pow_add, hk]; congr 1; omega
  unfold Good at hV
  rw [← hσdef] at hV
  choose! P B hP using hV
  let μ : ℝ := 2 ^ σ * (2 * f - 1)
  let Costly : Finset ℕ → Prop := fun X => ∃ I ⊆ V, I.card = m + 1 ∧ ∃ i < 2 ^ (k - σ),
    X = I.filter (fun u => B I u = i) ∧ μ ≤ roundMsgs A (P I) r X
  obtain ⟨F, hF, hFd, hmax⟩ := exists_maximal_disjoint V Costly
  have hFcard : F.card < 2 ^ (k - σ) := by
    by_contra hlt
    push Not at hlt
    obtain ⟨e, he, heF⟩ := exists_fin_embedding F (2 ^ (k - σ)) hlt
    have hc : ∀ a, Costly (e a) := fun a => (hF _ (heF a)).2
    choose I hIV hIc i hi hXe hμ using hc
    have hres : ∀ a, ∃ q : PortMap m, WF q (e a) ∧ Valid A q r (e a) ∧
        ∀ r', ∀ u ∈ e a, run A q r' u = run A (P (I a)) r' u := by
      intro a
      obtain ⟨hwf, hval, -, -, hlink⟩ := hP (I a) (hIV a) (hIc a)
      refine restrict hwf ?_ ?_ hval
      · rw [hXe a]; exact Finset.filter_subset _ _
      · intro u hu j v h
        rw [hXe a] at hu ⊢
        simp only [Finset.mem_filter] at hu ⊢
        exact ⟨hwf.mem u hu.1 j v h, by rw [hlink u hu.1 j v h]; exact hu.2⟩
    choose q hqwf hqval hqrun using hres
    have hdisj : Pairwise (Disjoint on e) :=
      fun a b hab => hFd _ (heF a) _ (heF b) (fun h => hab (he h))
    have hcardX : ∀ a, (e a).card = 2 ^ σ := by
      intro a; rw [hXe a]; exact (hP (I a) (hIV a) (hIc a)).2.2.2.1 (i a) (hi a)
    have hJ : (univ.biUnion e).card = m + 1 := by
      rw [card_biUnion_univ e hdisj _ hcardX, Fintype.card_fin, hnb]
    obtain ⟨Pf, hPf, hrunf⟩ := glue_full A e q hdisj hqwf r hqval hJ
    have hJU : univ.biUnion e ⊆ U := by
      intro u hu
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
      rw [hXe a] at ha
      exact hVU (hIV a (Finset.mem_filter.1 ha).1)
    have hbound := hM _ hJU hJ Pf hPf
    have hround : roundMsgs A Pf r (univ.biUnion e) = ∑ a, roundMsgs A (P (I a)) r (e a) := by
      rw [roundMsgs, Finset.sum_biUnion (fun a _ b _ hab => hdisj hab)]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun u hu => ?_
      rw [hrunf a u hu r le_rfl, hqrun a r u hu]
    have hge : ((2 ^ (k - σ) : ℕ) : ℝ) * μ ≤ roundMsgs A Pf r (univ.biUnion e) := by
      rw [hround]
      push_cast
      calc ((2 : ℝ) ^ (k - σ)) * μ = ∑ _a : Fin (2 ^ (k - σ)), μ := by simp
        _ ≤ _ := Finset.sum_le_sum fun a _ => hμ a
    have hle := roundMsgs_le_msgs (A := A) (p := Pf) (S := univ.biUnion e) hr
    have hnbμ : ((2 ^ (k - σ) : ℕ) : ℝ) * μ = (m + 1) * (2 * f - 1) := by
      simp only [μ]
      rw [← mul_assoc]
      congr 1
      exact_mod_cast hnb
    have : ((m : ℝ) + 1) * (2 * f - 1) ≤ (m + 1) * f := by
      rw [← hnbμ]
      exact hge.trans ((Nat.cast_le.2 hle).trans hbound)
    have hm : (0 : ℝ) < m + 1 := by positivity
    nlinarith
  refine ⟨V \ F.biUnion id, Finset.sdiff_subset, ?_, ?_⟩
  · have hXc : ∀ X ∈ F, X.card = 2 ^ σ := by
      intro X hX
      obtain ⟨I, hIV, hIc, i, hi, rfl, -⟩ := (hF X hX).2
      exact (hP I hIV hIc).2.2.2.1 i hi
    have h1 : (F.biUnion id).card = F.card * 2 ^ σ := by
      rw [Finset.card_biUnion (s := F) (t := id) (fun X hX Y hY h => hFd X hX Y hY h)]
      rw [Finset.sum_congr rfl fun X hX => (show (id X).card = 2 ^ σ from hXc X hX)]
      simp
    have h2 : V.card ≤ (V \ F.biUnion id).card + (F.biUnion id).card := by
      have := Finset.card_le_card_sdiff_add_card (s := V) (t := F.biUnion id)
      omega
    have h3 : F.card * 2 ^ σ ≤ m + 1 := by
      rw [← hnb]; exact Nat.mul_le_mul_right _ hFcard.le
    omega
  · intro I hI hIc
    have hIV : I ⊆ V := hI.trans Finset.sdiff_subset
    obtain ⟨hwf, hval, hblt, hbcard, hlink⟩ := hP I hIV hIc
    -- the blocks of `I` are not costly
    have hcheap : ∀ u ∈ I,
        (roundMsgs A (P I) r (I.filter fun v => B I v = B I u) : ℝ) < μ := by
      intro u hu
      by_contra hcon
      push Not at hcon
      have hX : I.filter (fun v => B I v = B I u) ⊆ V \ F.biUnion id :=
        (Finset.filter_subset _ _).trans hI
      have h0 := hmax _ hX ⟨I, hIV, hIc, B I u, hblt u hu, rfl, hcon⟩
      have hc := hbcard (B I u) (hblt u hu)
      rw [h0, Finset.card_empty] at hc
      exact absurd hc.symm (by positivity)
    obtain ⟨t, htdef⟩ : ∃ t, t = c + 1 := ⟨_, rfl⟩
    rw [← htdef] at hσt hσk
    have ht : 0 < 2 ^ t := by positivity
    have hgroupK : 2 ^ (k - σ) = 2 ^ (k - (σ + t)) * 2 ^ t := by
      rw [← pow_add]; congr 1; omega
    have hgroup : ∀ g < 2 ^ (k - (σ + t)),
        (I.filter fun v => B I v / 2 ^ t = g).card = 2 ^ (σ + t) := by
      intro g hg
      refine card_group hbcard g ?_
      rw [hgroupK]
      exact Nat.mul_le_mul_right _ hg
    have hblt' : ∀ u ∈ I, B I u / 2 ^ t < 2 ^ (k - (σ + t)) := by
      intro u hu
      rw [Nat.div_lt_iff_lt_mul ht, ← hgroupK]
      exact hblt u hu
    let R : ℕ → Finset ℕ := fun u =>
      (I.filter fun v => B I v / 2 ^ t = B I u / 2 ^ t).filter fun v => B I v ≠ B I u
    let N : ℕ → Finset (Fin m) := fun u =>
      (freePorts (P I) u).filter fun j => (A.send (run A (P I) r u) j).isSome
    have hRcard : ∀ u ∈ I, (R u).card + 2 ^ σ = 2 ^ (σ + t) := by
      intro u hu
      have h1 := Finset.card_filter_add_card_filter_not
        (s := I.filter fun v => B I v / 2 ^ t = B I u / 2 ^ t) (fun v => B I v ≠ B I u)
      have h2 : ((I.filter fun v => B I v / 2 ^ t = B I u / 2 ^ t).filter
          fun v => ¬ B I v ≠ B I u) = I.filter fun v => B I v = B I u := by
        ext v
        simp only [Finset.mem_filter, not_not]
        constructor
        · rintro ⟨⟨hv, -⟩, h⟩; exact ⟨hv, h⟩
        · rintro ⟨hv, h⟩; exact ⟨⟨hv, by rw [h]⟩, h⟩
      rw [h2, hbcard _ (hblt u hu), hgroup _ (hblt' u hu)] at h1
      exact h1
    have hfree : ∀ u ∈ I, 2 ^ (σ + t) ≤ (freePorts (P I) u).card + 2 ^ σ := by
      intro u hu
      have h1 := card_nbrs hwf hu
      have h2 : nbrs (P I) u ⊆ (I.filter fun v => B I v = B I u).erase u := by
        intro v hv
        obtain ⟨j, hj⟩ := mem_nbrs.1 hv
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨hwf.mem u hu j v hj, hlink u hu j v hj⟩⟩
        intro h; rw [h] at hj; exact hwf.ne u hu j hj
      have h3 := Finset.card_le_card h2
      have hmem : u ∈ I.filter fun v => B I v = B I u := Finset.mem_filter.2 ⟨hu, rfl⟩
      rw [Finset.card_erase_of_mem hmem, hbcard _ (hblt u hu)] at h3
      have h4 : 2 ^ (σ + t) ≤ m + 1 := by
        rw [hk]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : 0 < 2 ^ σ := by positivity
      omega
    have hNR : ∀ u ∈ I, (N u).card ≤ (R u).card := by
      intro u hu
      have h1 : (N u).card ≤ sendCount A (run A (P I) r u) := by
        apply Finset.card_le_card
        intro j hj
        simp only [N, Finset.mem_filter] at hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hj.2
      have h2 : sendCount A (run A (P I) r u) ≤
          roundMsgs A (P I) r (I.filter fun v => B I v = B I u) :=
        Finset.single_le_sum (f := fun v => sendCount A (run A (P I) r v))
          (fun _ _ => Nat.zero_le _)
          (show u ∈ I.filter fun v => B I v = B I u from Finset.mem_filter.2 ⟨hu, rfl⟩)
      have h3 := hcheap u hu
      have h4 : μ ≤ (R u).card := by
        have := hRcard u hu
        have h5 : ((R u).card : ℝ) = 2 ^ (σ + t) - 2 ^ σ := by
          rw [eq_sub_iff_add_eq]; exact_mod_cast this
        rw [h5]
        simp only [μ, pow_add, htdef, pow_succ]
        have : (0 : ℝ) < 2 ^ σ := by positivity
        nlinarith
      have h6 : ((N u).card : ℝ) < (R u).card := by
        calc ((N u).card : ℝ) ≤ roundMsgs A (P I) r (I.filter fun v => B I v = B I u) := by
              exact_mod_cast h1.trans h2
          _ < μ := h3
          _ ≤ _ := h4
      exact_mod_cast h6.le
    obtain ⟨p', hwf', hext, hcases, -, hN⟩ := augment (P I) I hwf R N
      (fun u _ => (Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      (fun u _ h => by simp [R] at h)
      (fun u hu v hv j hj => by
        simp only [R, Finset.mem_filter] at hv
        exact hv.2 (hlink u hu j v hj))
      (fun u hu v hv => by
        simp only [R, Finset.mem_filter] at hv ⊢
        exact ⟨⟨hu, hv.1.2.symm⟩, fun h => hv.2 h.symm⟩)
      (fun u _ j hj => by
        simp only [N, freePorts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hj.1)
      hNR
      (fun u hu => by have := hRcard u hu; have := hfree u hu; omega)
    refine ⟨p', fun u => B I u / 2 ^ t, hwf', ?_, ?_, ?_, ?_⟩
    · intro r' hr' u hu j hj
      have hpj : P I u j = none := by
        rcases h : P I u j with _ | v
        · rfl
        · rw [hext u hu j v h] at hj; cases hj
      rw [run_eq_of_extends hwf hwf' hext hval r' (by omega) u hu]
      rcases Nat.lt_or_ge r' r with h | h
      · exact hval r' h u hu j hpj
      · have : r' = r := by omega
        subst this
        by_contra hs
        have hjN : j ∈ N u := by
          simp only [N, freePorts, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hpj, Option.ne_none_iff_isSome.1 hs⟩
        have := hN u hu j hjN
        rw [hj] at this
        cases this
    · intro u hu
      show B I u / 2 ^ t < _
      rw [← htdef, hσt]
      exact hblt' u hu
    · intro g hg
      rw [← htdef, hσt] at hg ⊢
      exact hgroup g hg
    · intro u hu j v h
      show B I v / 2 ^ t = B I u / 2 ^ t
      rcases hcases u hu j v h with h | h
      · rw [hlink u hu j v h]
      · simp only [R, Finset.mem_filter] at h
        exact h.1.2

/-- **Theorem 3.8 (corrected), core form.** Let `n = m + 1 = 2^k` and let `A` be a deterministic
algorithm that elects a leader within `T` rounds for all ID assignments from `U` (with
`|U| ≥ (T + 2) n`) and all port maps, sending at most `n · f` messages, where `1 < f ≤ 2^c`.
Then `k ≤ (c + 1) · T`. -/
theorem tradeoff_lower_bound {k c T : ℕ} (hk : m + 1 = 2 ^ k) {f : ℝ} (hf : 1 < f)
    (hfc : f ≤ 2 ^ c) {A : Algorithm m} {U : Finset ℕ} (hU : (T + 2) * (m + 1) ≤ U.card)
    (hA : ElectsBy A U T) (hM : MsgBound A U T ((m + 1) * f)) : k ≤ (c + 1) * T := by
  by_contra hlt
  push Not at hlt
  have hsN : 2 ^ ((c + 1) * T) * 2 ^ (k - (c + 1) * T) = m + 1 := by
    rw [← pow_add, hk]; congr 1; omega
  have hN : 2 ≤ 2 ^ (k - (c + 1) * T) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k - (c + 1) * T) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨U₀, hU₀, hc₀, hno⟩ := exists_universe_no_isolable hA hsN hN (by positivity)
  have hiter : ∀ r ≤ T, ∃ V ⊆ U₀, U₀.card ≤ V.card + r * (m + 1) ∧ Good A k c r V := by
    intro r
    induction r with
    | zero => intro _; exact ⟨U₀, subset_rfl, by simp, good_zero hk U₀⟩
    | succ r ih =>
      intro hr
      obtain ⟨V, hV, hc, hg⟩ := ih (by omega)
      have hσ : (c + 1) * (r + 1) ≤ k := (Nat.mul_le_mul_left _ hr).trans hlt.le
      obtain ⟨V', hV', hc', hg'⟩ := good_step hk hf hfc hM (by omega) hσ (hV.trans hU₀) hg
      exact ⟨V', hV'.trans hV, by rw [Nat.succ_mul]; omega, hg'⟩
  obtain ⟨V, hV, hcV, hg⟩ := hiter T le_rfl
  have hVc : m + 1 ≤ V.card := by nlinarith
  obtain ⟨I, hIV, hIc⟩ := Finset.exists_subset_card_eq hVc
  obtain ⟨p, blk, hwf, hval, hblt, hbcard, hlink⟩ := hg I hIV hIc
  have hXc : (I.filter fun u => blk u = 0).card = 2 ^ ((c + 1) * T) :=
    hbcard 0 (by positivity)
  obtain ⟨q, hq, hqv, -⟩ := restrict (X := I.filter fun u => blk u = 0) hwf
    (Finset.filter_subset _ _) (fun u hu j v h => by
      simp only [Finset.mem_filter] at hu ⊢
      exact ⟨hwf.mem u hu.1 j v h, by rw [hlink u hu.1 j v h]; exact hu.2⟩) hval
  exact hno _ ((Finset.filter_subset _ _).trans (hIV.trans hV)) hXc ⟨q, hq, hqv⟩

/-- **Theorem 3.8 (corrected).** Let `n = m + 1` be a power of two, and let the IDs come from a
universe `U` of at least `2 n log₂ n + n` IDs (as in the paper). If a deterministic algorithm
elects a leader within `T` rounds and always sends at most `n · f` messages, `f > 1`, then
`T > (log₂ n - 1) / (⌈log₂ f⌉ + 1)`.

The paper claims `T > (log₂ n - 1) / (log₂ f + 1) + 1`; the additional `+ 1` is false
(`theorem_3_8_as_stated_false`), and the ceiling is what the proof (block sizes `2^σ_r`) gives. -/
theorem theorem_3_8_corrected {k T : ℕ} (hk : m + 1 = 2 ^ k) {f : ℝ} (hf : 1 < f)
    {A : Algorithm m} {U : Finset ℕ} (hU : 2 * (m + 1) * k + (m + 1) ≤ U.card)
    (hA : ElectsBy A U T) (hM : MsgBound A U T ((m + 1) * f)) :
    (Real.logb 2 (m + 1) - 1) / (⌈Real.logb 2 f⌉ + 1) < T := by
  set c := ⌈Real.logb 2 f⌉.toNat with hcdef
  have hpos : 0 < Real.logb 2 f := Real.logb_pos (by norm_num) hf
  have hc0 : (0 : ℤ) ≤ ⌈Real.logb 2 f⌉ := (Int.ceil_pos.2 hpos).le
  have hcz : ((c : ℤ) : ℝ) = (⌈Real.logb 2 f⌉ : ℝ) := by
    rw [hcdef, Int.toNat_of_nonneg hc0]
  have hkT : k ≤ (c + 1) * T := by
    by_contra h
    push Not at h
    have hT : T + 2 ≤ 2 * k + 1 := by
      have : T ≤ (c + 1) * T := Nat.le_mul_of_pos_left T (by omega)
      omega
    have hU' : (T + 2) * (m + 1) ≤ U.card := by
      calc (T + 2) * (m + 1) ≤ (2 * k + 1) * (m + 1) := Nat.mul_le_mul_right _ hT
        _ = 2 * (m + 1) * k + (m + 1) := by ring
        _ ≤ _ := hU
    have hf2 : f ≤ 2 ^ ⌈Real.logb 2 f⌉.toNat := by
      rw [Int.ceil_toNat]; exact Real.le_pow_natCeil_logb one_lt_two f
    exact absurd (tradeoff_lower_bound hk hf hf2 hU' hA hM) (not_le.2 h)
  have hlog : Real.logb 2 ((m : ℝ) + 1) = k := by
    rw [show ((m : ℝ) + 1) = (2 : ℝ) ^ k by exact_mod_cast hk,
      Real.logb_self_pow two_pos (by norm_num)]
  rw [hlog, ← hcz]
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  push_cast
  rw [div_lt_iff₀ hc1]
  have : (k : ℝ) ≤ (c + 1) * T := by exact_mod_cast hkT
  nlinarith

/-- **Consequence of Theorem 3.8 (corrected)** for algorithms with a given number of rounds: if
`(c + 1) T < log₂ n` with `c ≥ 1`, every `T`-round algorithm sends more than `n · 2^c` messages in
some execution. Taking `c = ⌈log₂ n / T⌉ - 2` this is `Ω(n^(1 + 1/T))` messages for `T`-round
algorithms (the paper claims `Ω((n/2)^(1 + 1/(T-1)))`, which relies on the false `+ 1`). -/
theorem rounds_messages_tradeoff {k c T : ℕ} (hk : m + 1 = 2 ^ k) (hc : 1 ≤ c)
    (hcT : (c + 1) * T < k) {A : Algorithm m} {U : Finset ℕ}
    (hU : 2 * (m + 1) * k + (m + 1) ≤ U.card) (hA : ElectsBy A U T) :
    ∃ I ⊆ U, I.card = m + 1 ∧ ∃ p : PortMap m, IsPortMap p I ∧ (m + 1) * 2 ^ c < msgs A p T I := by
  by_contra h
  push Not at h
  have hM : MsgBound A U T ((m + 1) * (2 ^ c : ℝ)) := by
    intro I hI hIc p hp
    exact_mod_cast h I hI hIc p hp
  have hT : T + 2 ≤ 2 * k + 1 := by
    have : T ≤ (c + 1) * T := Nat.le_mul_of_pos_left T (by omega)
    omega
  have hU' : (T + 2) * (m + 1) ≤ U.card := by
    calc (T + 2) * (m + 1) ≤ (2 * k + 1) * (m + 1) := Nat.mul_le_mul_right _ hT
      _ = 2 * (m + 1) * k + (m + 1) := by ring
      _ ≤ _ := hU
  have hf : (1 : ℝ) < 2 ^ c := one_lt_pow₀ (by norm_num) (by omega)
  have := tradeoff_lower_bound hk hf le_rfl hU' hA hM
  omega

end LeaderTradeoffs
