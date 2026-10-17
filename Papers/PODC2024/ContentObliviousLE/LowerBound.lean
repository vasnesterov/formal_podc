import Cslib.Computability.Distributed.ContentOblivious.Lockstep
import Mathlib
import Papers.PODC2024.ContentObliviousLE.Theorem1

/-!
# The message lower bound (Theorem 3 / Theorem 17)

Frei, Gelles, Ghazy, Nolin, *Content-Oblivious Leader Election on Rings*, PODC 2024 (brief
announcement), Theorem 3; full version arXiv 2405.03646, Section 5 (Definition 18, Lemmas 19–20,
Corollary 21, Theorem 17).

The lower bound holds for every deterministic algorithm in our model (`Cslib.ContentOblivious.Algo`)
that solves terminating leader election on oriented rings of sizes `1` and `2` (`SolvesLE`). As in
the paper, the argument uses rings with a single node (a self-loop) and with two nodes (a double
link).

We also show that Theorem 3 must be read as a *worst case over ID assignments*: read per instance
("every execution on every ring sends at least `n⌊log(IDmax/n)⌋` pulses") it is false
(`theorem_3_per_instance_false`).
-/

namespace Podc.ContentOblivious.LowerBound

open Cslib.ContentOblivious Finset

variable {A : Algo} {Ids : Set ℕ}

/-- `A` solves (terminating) leader election on oriented rings of size `n` with distinct IDs from
`Ids`: some maximal execution exists, and every maximal execution ends with all nodes terminated and
exactly one node in state `Leader`. -/
def SolvesLE (A : Algo) (n : ℕ) [NeZero n] (Ids : Set ℕ) : Prop :=
  ∀ id : ZMod n → ℕ, Function.Injective id → (∀ v, id v ∈ Ids) →
    (∃ c, Reach (oriented n) A id c ∧ Final (oriented n) A c) ∧
    ∀ c, Reach (oriented n) A id c → Final (oriented n) A c →
      (∀ v, A.terminated (c.st v) = true) ∧ ∃! v, A.leader (c.st v) = true

/-- **Definition 18 (solitude pattern).** A history `w` (sequence of ports at which pulses were
consumed) of a complete solitude execution of a node with ID `i`: realizable on the 1-node ring and
ending with the node terminated as `Leader`. (The paper fixes one particular FIFO scheduler; any
complete solitude execution works.) -/
def IsPattern (A : Algo) (i : ℕ) (w : List Bool) : Prop :=
  Valid A i w ∧ A.terminated (run A i w).1 = true ∧ A.leader (run A i w).1 = true

lemma exists_pattern (h : SolvesLE A 1 Ids) {i : ℕ} (hi : i ∈ Ids) : ∃ w, IsPattern A i w := by
  obtain ⟨⟨c, hr, hf⟩, hspec⟩ := h (fun _ => i) (fun a b _ => Subsingleton.elim a b) (fun _ => hi)
  obtain ⟨w, hw, rfl⟩ := reach_one hr
  obtain ⟨ht, v, hv, -⟩ := hspec _ hr hf
  exact ⟨w, hw, by simpa [syncCfg] using ht 0, by simpa [syncCfg] using hv⟩

/-- **Lemma 19.** Distinct IDs have distinct solitude patterns. (Both nodes of a 2-node ring with
equal patterns behave as in solitude under a lockstep scheduler, so both terminate as leaders.) -/
theorem lemma_19 (h2 : SolvesLE A 2 Ids) {i j : ℕ} (hi : i ∈ Ids) (hj : j ∈ Ids) (hij : i ≠ j)
    {w : List Bool} (hpi : IsPattern A i w) (hpj : IsPattern A j w) : False := by
  let id : ZMod 2 → ℕ := fun v => if v = 0 then i else j
  have h01 : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide
  have hinj : Function.Injective id := by
    intro a b hab
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> simp_all [id, eq_comm]
  have hmem : ∀ v, id v ∈ Ids := by intro v; by_cases hv : v = 0 <;> simp [id, hv, hi, hj]
  have hvalid : ∀ v, Valid A (id v) w := by
    intro v; by_cases hv : v = 0 <;> simp [id, hv, hpi.1, hpj.1]
  have hr := reach_sync id w hvalid
  have hfin : Final (oriented 2) A (syncCfg id fun _ => w) := by
    intro v d hen
    have := hen.1
    by_cases hv : v = 0 <;> simp [syncCfg, id, hv, hpi.2.1, hpj.2.1] at this
  obtain ⟨-, ℓ, -, huniq⟩ := (h2 id hinj hmem).2 _ hr hfin
  have e0 := huniq 0 (by simpa [syncCfg, id] using hpi.2.2)
  have e1 := huniq 1 (by simpa [syncCfg, id] using hpj.2.2)
  exact absurd (e0.trans e1.symm) (by decide)

/-- **Lemma 20.** Any set of at least `n·2^s` binary strings contains `n` strings with a common
prefix of length `s`. -/
theorem lemma_20 (n : ℕ) (hn : 1 ≤ n) (s : ℕ) (S : Finset (List Bool)) (hS : n * 2 ^ s ≤ S.card) :
    ∃ q : List Bool, q.length = s ∧ n ≤ (S.filter (q <+: ·)).card := by
  classical
  induction s generalizing S with
  | zero => exact ⟨[], rfl, by simpa using hS⟩
  | succ s ih =>
    let F : Bool → Finset (List Bool) := fun b => S.filter (fun l => l.head? = some b)
    have hcard : S.card ≤ 1 + (F false).card + (F true).card := by
      rw [card_eq_sum_card_fiberwise (f := List.head?) (t := univ) (fun _ _ => mem_univ _)]
      rw [Fintype.sum_option, Fintype.sum_bool]
      have : (S.filter fun l => l.head? = none).card ≤ 1 := by
        refine card_le_one.2 fun a ha b hb => ?_
        simp only [mem_filter, List.head?_eq_none_iff] at ha hb
        rw [ha.2, hb.2]
      simp only [F]; omega
    have hpos : 1 ≤ n * 2 ^ s := Nat.one_le_iff_ne_zero.2 (by positivity)
    obtain ⟨b, hb⟩ : ∃ b, n * 2 ^ s ≤ (F b).card := by
      by_contra hc
      push_neg at hc
      have := hc false; have := hc true
      have e : n * 2 ^ (s + 1) = 2 * (n * 2 ^ s) := by ring
      rw [e] at hS
      omega
    have hinj : Set.InjOn List.tail (F b : Set (List Bool)) := by
      intro x hx y hy hxy
      simp only [F, coe_filter, Set.mem_setOf_eq] at hx hy
      rw [List.eq_cons_of_mem_head? hx.2, List.eq_cons_of_mem_head? hy.2, hxy]
    obtain ⟨q, hq, hqc⟩ := ih ((F b).image List.tail) (by rwa [card_image_of_injOn hinj])
    refine ⟨b :: q, by simp [hq], hqc.trans ?_⟩
    refine card_le_card_of_injOn (fun l => b :: l) (fun l hl => ?_) (fun x _ y _ h => by simpa using h)
    simp only [coe_filter, Set.mem_setOf_eq, mem_image] at hl ⊢
    obtain ⟨⟨m, hm, rfl⟩, hpre⟩ := hl
    simp only [F, mem_filter] at hm
    have hm' := List.eq_cons_of_mem_head? hm.2
    refine ⟨by rw [← hm']; exact hm.1, ?_⟩
    exact (List.prefix_cons_inj b).2 hpre

/-- **Corollary 21** (the size condition): `n · 2^⌊log₂(k/n)⌋ ≤ k` for `1 ≤ n ≤ k`. Here
`⌊log₂(k/n)⌋ = Nat.log 2 (k / n)` with natural-number division. -/
lemma corollary_21 {n k : ℕ} (hn : 1 ≤ n) (hk : n ≤ k) : n * 2 ^ Nat.log 2 (k / n) ≤ k := by
  have h1 : 2 ^ Nat.log 2 (k / n) ≤ k / n :=
    Nat.pow_log_le_self 2 (Nat.div_pos hk hn).ne'
  calc n * 2 ^ Nat.log 2 (k / n) ≤ n * (k / n) := Nat.mul_le_mul_left _ h1
    _ ≤ k := Nat.mul_div_le k n

/-- **Theorem 17.** Let `A` solve terminating leader election on oriented rings of sizes 1 and 2
with IDs from `Ids`. For every ring size `n` and every set `K ⊆ Ids` of `k ≥ n` IDs, some
assignment of distinct IDs from `K` to the `n` nodes admits an execution sending at least
`n·⌊log₂(k/n)⌋` pulses. -/
theorem theorem_17 (h1 : SolvesLE A 1 Ids) (h2 : SolvesLE A 2 Ids) (n : ℕ) [NeZero n]
    (K : Finset ℕ) (hK : (K : Set ℕ) ⊆ Ids) (hn : n ≤ K.card) :
    ∃ id : ZMod n → ℕ, Function.Injective id ∧ (∀ v, id v ∈ K) ∧
      ∃ c, Reach (oriented n) A id c ∧ n * Nat.log 2 (K.card / n) ≤ totalSent c := by
  classical
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hpat : ∀ i ∈ K, ∃ w, IsPattern A i w := fun i hi => exists_pattern h1 (hK hi)
  choose! pat hpat using hpat
  have hinj : Set.InjOn pat K := by
    intro i hi j hj hij
    by_contra hne
    exact lemma_19 h2 (hK hi) (hK hj) hne (hpat i hi) (hij ▸ hpat j hj)
  set s := Nat.log 2 (K.card / n)
  obtain ⟨q, hq, hqc⟩ := lemma_20 n hn1 s (K.image pat)
    (by rw [card_image_of_injOn hinj]; exact corollary_21 hn1 hn)
  set K' := K.filter fun i => q <+: pat i
  have hK' : n ≤ K'.card := by
    refine hqc.trans ?_
    rw [show (K.image pat).filter (q <+: ·) = K'.image pat by
      ext x; simp [K', mem_filter, mem_image]; constructor
      · rintro ⟨⟨a, ha, rfl⟩, h⟩; exact ⟨a, ⟨ha, h⟩, rfl⟩
      · rintro ⟨a, ⟨ha, h⟩, rfl⟩; exact ⟨⟨a, ha, rfl⟩, h⟩]
    exact card_image_le
  obtain ⟨T, hTK, hTc⟩ := exists_subset_card_eq hK'
  let e : ZMod n ≃ T := Fintype.equivOfCardEq (by simp [ZMod.card, hTc])
  let id : ZMod n → ℕ := fun v => (e v : ℕ)
  have hidT : ∀ v, id v ∈ K' := fun v => hTK (e v).2
  have hidK : ∀ v, id v ∈ K := fun v => (mem_filter.1 (hidT v)).1
  refine ⟨id, Subtype.val_injective.comp e.injective, hidK, syncCfg id fun _ => q, ?_, ?_⟩
  · refine reach_sync id q fun v => (hpat _ (hidK v)).1.of_prefix ?_
    exact (mem_filter.1 (hidT v)).2
  · have hr := reach_sync (A := A) id q fun v => (hpat _ (hidK v)).1.of_prefix (mem_filter.1 (hidT v)).2
    refine le_trans ?_ hr.totalRecvd_le_totalSent
    rw [totalRecvd, Fintype.sum_prod_type]
    simp [syncCfg, List.count_true_add_count_false, hq, ZMod.card, Fintype.sum_bool, add_comm]

/-- **Theorem 3** (brief announcement). For IDs from `{1, …, M}` (`M ≥ n`), some assignment of
distinct IDs (so with `IDmax ≤ M`) admits an execution with at least `n·⌊log₂(M/n)⌋ ≥
n·⌊log₂(IDmax/n)⌋` pulses. -/
theorem theorem_3 (h1 : SolvesLE A 1 Ids) (h2 : SolvesLE A 2 Ids) (n : ℕ) [NeZero n] (M : ℕ)
    (hIds : ∀ i, 1 ≤ i → i ≤ M → i ∈ Ids) (hM : n ≤ M) :
    ∃ id : ZMod n → ℕ, Function.Injective id ∧ (∀ v, 1 ≤ id v ∧ id v ≤ M) ∧
      ∃ c, Reach (oriented n) A id c ∧ n * Nat.log 2 (M / n) ≤ totalSent c ∧
        n * Nat.log 2 (univ.sup id / n) ≤ totalSent c := by
  obtain ⟨id, hinj, hK, c, hr, hc⟩ := theorem_17 h1 h2 n (Icc 1 M)
    (fun i hi => by simp only [coe_Icc, Set.mem_Icc] at hi; exact hIds i hi.1 hi.2)
    (by simpa using hM)
  simp only [Nat.card_Icc, add_tsub_cancel_right] at hc
  have hb : ∀ v, 1 ≤ id v ∧ id v ≤ M := fun v => by simpa using hK v
  refine ⟨id, hinj, hb, c, hr, hc, le_trans ?_ hc⟩
  refine Nat.mul_le_mul_left _ (Nat.log_mono_right (Nat.div_le_div_right ?_))
  exact Finset.sup_le fun v _ => (hb v).2

/-- Theorem 17, last sentence: with an infinite supply of IDs the number of pulses is unbounded,
even on the ring with a single node. -/
theorem unbounded_single_node (h1 : SolvesLE A 1 Ids) (h2 : SolvesLE A 2 Ids)
    (hIds : ∀ i, 1 ≤ i → i ∈ Ids) (B : ℕ) :
    ∃ i, 1 ≤ i ∧ ∃ c, Reach (oriented 1) A (fun _ => i) c ∧ B ≤ totalSent c := by
  obtain ⟨id, -, hK, c, hr, hc⟩ := theorem_17 h1 h2 1 (Icc 1 (2 ^ B))
    (fun i hi => by simp only [coe_Icc, Set.mem_Icc] at hi; exact hIds i hi.1)
    (by simp; exact Nat.one_le_two_pow)
  refine ⟨id 0, (mem_Icc.1 (hK 0)).1, c, ?_, ?_⟩
  · have : id = fun _ => id 0 := funext fun v => by rw [Subsingleton.elim v 0]
    rwa [this] at hr
  · simpa [Nat.log_pow] using hc

/-! ## Non-vacuity and the per-instance reading -/

/-- Algorithm 2 satisfies the hypothesis of the lower bound for positive IDs and every ring size
(so Theorems 17 and 3 are not vacuous). -/
theorem alg2_solves (n : ℕ) [NeZero n] : SolvesLE Alg2.alg n {i | 0 < i} := by
  intro id hid hpos
  obtain ⟨ℓ, -, hℓ⟩ := Finset.exists_max_image univ id univ_nonempty
  have hℓ' : ∀ v, id v ≤ id ℓ := fun v => hℓ v (mem_univ v)
  refine ⟨?_, fun c hr hf => ?_⟩
  · obtain ⟨c, hc, hf⟩ := Alg2.exists_final hid hpos hℓ' (Relation.ReflTransGen.refl (a := initCfg _ id))
    exact ⟨c, hc, hf⟩
  · obtain ⟨-, hdone, hlead, -⟩ := Alg2.final_spec hid hpos hℓ' hr hf
    exact ⟨hdone, ℓ, (hlead ℓ).2 rfl, fun v hv => (hlead v).1 hv⟩

/-- Relabelling IDs by an injective map preserving positivity preserves `SolvesLE`. -/
theorem alg2_relabel_solves (π : ℕ → ℕ) (hπ : Function.Injective π) (hπpos : ∀ i, 0 < i → 0 < π i)
    (n : ℕ) [NeZero n] : SolvesLE (Alg2.alg.relabel π) n {i | 0 < i} := by
  intro id hid hpos
  obtain ⟨⟨c, hc, hf⟩, h⟩ := alg2_solves n (π ∘ id) (hπ.comp hid) (fun v => hπpos _ (hpos v))
  refine ⟨⟨c, (reach_relabel (W := oriented n) (A := Alg2.alg) π id c).2 hc, hf⟩, fun c hr hf => h c ((reach_relabel (W := oriented n) (A := Alg2.alg) π id c).1 hr) hf⟩

/-- **Theorem 3 is false if read per instance.** There is a terminating leader election algorithm
(Algorithm 2 run on IDs relabelled by the transposition `1 ↔ 16`) solving the problem on every
oriented ring with positive IDs, such that on the 1-node ring with ID `16` every execution sends at
most `3 < 4 = 1·⌊log₂(16/1)⌋` pulses. -/
theorem theorem_3_per_instance_false :
    ∃ A : Algo, (∀ n [NeZero n], SolvesLE A n {i | 0 < i}) ∧
      ∀ c, Reach (oriented 1) A (fun _ => 16) c →
        totalSent c ≤ 3 ∧ totalSent c < 1 * Nat.log 2 ((univ.sup fun _ : ZMod 1 => 16) / 1) := by
  let π : ℕ → ℕ := Equiv.swap 1 16
  have hπ : Function.Injective π := (Equiv.swap 1 16).injective
  have hπpos : ∀ i, 0 < i → 0 < π i := by
    intro i hi
    simp only [π, Equiv.swap_apply_def]
    split_ifs <;> omega
  refine ⟨Alg2.alg.relabel π, fun n _ => alg2_relabel_solves π hπ hπpos n, fun c hr => ?_⟩
  have hr' : Reach (oriented 1) Alg2.alg (fun _ => π 16) c := (reach_relabel (W := oriented 1) (A := Alg2.alg) π _ c).1 hr
  have h := Alg2.totalSent_le (id := fun _ : ZMod 1 => π 16) (ℓ := 0)
    (fun a b _ => Subsingleton.elim a b) (fun _ => by simp [π, Equiv.swap_apply_right])
    (fun _ => le_rfl) hr'
  have h16 : π 16 = 1 := by simp [π, Equiv.swap_apply_right]
  simp only [h16] at h
  have h' : totalSent c ≤ 3 := le_of_le_of_eq h (by norm_num)
  refine ⟨h', ?_⟩
  have : (univ.sup fun _ : ZMod 1 => 16) = 16 := by simp
  rw [this]
  have : Nat.log 2 16 = 4 := by decide
  simp only [Nat.div_one, this]
  omega

end Podc.ContentOblivious.LowerBound
