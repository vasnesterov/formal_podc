import Papers.PODC2010.BroadcastUnreliableRadio.LowerBoundCore

/-!
# Theorem 12: an `Ω(n log n)` lower bound for deterministic broadcast in undirected dual graphs

The network (`layerNet m`): nodes `0, …, n - 1` with `n = 2^m + 1`, layers `L₀ = {0}`,
`L_k = {2k - 1, 2k}` (`layer v = (v + 1) / 2`), reliable edges inside a layer and between
consecutive layers, `G'` complete.

The execution is built in stages (`Stage k`): after stage `k` we have a placement `π` of processes
on the nodes of layers `≤ k` (extended arbitrarily), a delivery rule `D`, and a time `t ≥ k (m-1)`
at which exactly the processes of layers `≤ k` may be informed and one of them is about to send
alone. A stage extends the execution by the pair of `exists_pair` (Claim 13), placed on layer
`k + 1`, until one of the two sends alone (at least `L + 1 = m - 1` rounds later). If at some point
the next isolation never happens, broadcast fails outright.

Main result: `theorem_12`.
-/

namespace Podc.BroadcastUnreliableRadio

open Finset

/-! ## The layered network -/

/-- The layer of a node: `L₀ = {0}`, `L_k = {2k - 1, 2k}`. -/
def layer {n : ℕ} (v : Fin n) : ℕ := (v.val + 1) / 2

theorem layer_le_iff {n : ℕ} (v : Fin n) (k : ℕ) : layer v ≤ k ↔ v.val ≤ 2 * k := by
  simp only [layer]; omega

/-- The network of Theorem 12 on `2^m + 1` nodes: a complete layered graph `G`, complete `G'`. -/
def layerNet (m : ℕ) : DualGraph (Fin (2 ^ m + 1)) where
  E u v := u ≠ v ∧ layer u ≤ layer v + 1 ∧ layer v ≤ layer u + 1
  E' u v := u ≠ v
  le _ _ h := h.1
  src := 0
  reachable := by
    rintro ⟨k, hk⟩
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      refine Relation.ReflTransGen.tail (ih (by omega)) ⟨?_, ?_, ?_⟩
      · simp [Fin.ext_iff]
      · simp only [layer]; omega
      · simp only [layer]; omega

theorem layerNet_undirected (m : ℕ) : (layerNet m).Undirected :=
  ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩, fun _ _ h => Ne.symm h⟩

variable {I S M : Type*} [Fintype I] [DecidableEq I]

/-- The processes placed on layers `≤ k`. -/
def lowSet {n : ℕ} (π : Fin n ≃ I) (k : ℕ) : Finset I :=
  (univ.filter fun v : Fin n => layer v ≤ k).map π.toEmbedding

theorem mem_lowSet {n : ℕ} {π : Fin n ≃ I} {k : ℕ} {x : I} :
    x ∈ lowSet π k ↔ layer (π.symm x) ≤ k := by
  simp [lowSet, Finset.mem_map_equiv]

theorem mem_lowSet' {n : ℕ} {π : Fin n ≃ I} {k : ℕ} {x : I} :
    x ∈ lowSet π k ↔ ∃ v, layer v ≤ k ∧ π v = x := by
  rw [mem_lowSet]
  constructor
  · intro h; exact ⟨_, h, by simp⟩
  · rintro ⟨v, hv, rfl⟩; simpa using hv

theorem card_lowSet_le {n : ℕ} (π : Fin n ≃ I) (k : ℕ) : (lowSet π k).card ≤ 2 * k + 1 := by
  rw [lowSet, card_map]
  calc (univ.filter fun v : Fin n => layer v ≤ k).card
      ≤ (range (2 * k + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun v => v.val)
        · intro v hv
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, layer_le_iff] at hv
          simp only [coe_range, Set.mem_Iio]; omega
        · intro a _ b _ h; exact Fin.ext h
    _ = 2 * k + 1 := card_range _

/-- Extending a placement by two new processes on two new nodes. -/
theorem exists_equiv_extend {V : Type*} [DecidableEq V] (π : V ≃ I) (Q : Finset V) {u₁ u₂ : V}
    (hu : u₁ ≠ u₂) (h₁ : u₁ ∉ Q) (h₂ : u₂ ∉ Q) {a b : I} (hab : a ≠ b) (ha : a ∉ Q.map π.toEmbedding)
    (hb : b ∉ Q.map π.toEmbedding) :
    ∃ π' : V ≃ I, (∀ v ∈ Q, π' v = π v) ∧ π' u₁ = a ∧ π' u₂ = b := by
  set π₁ := π.trans (Equiv.swap (π u₁) a)
  have hπ₁ : ∀ v ∈ Q, π₁ v = π v := by
    intro v hv
    simp only [π₁, Equiv.trans_apply]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) (fun h => ha ?_)
    · exact h₁ (π.injective h ▸ hv)
    · rw [← h]; exact mem_map_of_mem _ hv
  have hπ₁u : π₁ u₁ = a := by simp [π₁]
  set π₂ := π₁.trans (Equiv.swap (π₁ u₂) b)
  refine ⟨π₂, fun v hv => ?_, ?_, by simp [π₂]⟩
  · simp only [π₂, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne, hπ₁ v hv]
    · intro h; exact h₂ (π₁.injective h ▸ hv)
    · rw [hπ₁ v hv]; intro h; exact hb (h ▸ mem_map_of_mem _ hv)
  · simp only [π₂, Equiv.trans_apply, hπ₁u]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) hab
    rw [← hπ₁u] at h
    exact hu (π₁.injective h)

/-! ## Stages -/

section Stages

variable (A : Algorithm I S M) (m : ℕ) (i₀ : I)

/-- Broadcast fails within `T` rounds for some placement and admissible adversary. -/
def Fail (T : ℕ) : Prop :=
  ∃ (π : Fin (2 ^ m + 1) ≃ I) (R : Adversary (Fin (2 ^ m + 1))),
    R.Admissible (layerNet m) ∧ ¬ BroadcastWithin A (layerNet m) π R T

/-- The delivery rule only restricts messages of processes of layers `≤ s < k` to layers `≤ s+1`. -/
def LayerAdm (k : ℕ) (π : Fin (2 ^ m + 1) ≃ I) (D : Delivery I) : Prop :=
  ∀ t B j, D t B j = univ ∨ ∃ s < k, layer (π.symm j) ≤ s ∧ D t B j = lowSet π (s + 1)

/-- The state after stage `k` of the construction. -/
def Stage (k L : ℕ) : Prop :=
  ∃ (π : Fin (2 ^ m + 1) ≃ I) (D : Delivery I) (t : ℕ) (j : I),
    π 0 = i₀ ∧ k * (L + 1) ≤ t ∧ A.senders (A.run (A.initConf i₀) D t) = {j} ∧
    j ∈ lowSet π k ∧
    (∀ x, A.informed (A.initConf i₀) D (· = i₀) t x → x ∈ lowSet π k) ∧ LayerAdm m k π D

variable {A m i₀}

theorem fail_of {k : ℕ} (hk : 2 * k + 1 < 2 ^ m + 1) (hI : Fintype.card I = 2 ^ m + 1)
    {π : Fin (2 ^ m + 1) ≃ I} {D : Delivery I} (h0 : π 0 = i₀) (hadm : LayerAdm m k π D) {T : ℕ}
    (hinf : ∀ x, A.informed (A.initConf i₀) D (· = i₀) T x → x ∈ lowSet π k) : Fail A m T := by
  refine ⟨π, fromDelivery π D, admissible_fromDelivery (fun _ _ h => h) ?_, fun hbc => ?_⟩
  · intro t B v w hvw
    rcases hadm t B (π v) with h | ⟨s, -, hs, h⟩
    · rw [h]; exact mem_univ _
    · rw [h, mem_lowSet]
      simp only [Equiv.symm_apply_apply] at hs ⊢
      have := hvw.2.2
      omega
  · have hall : ∀ i, i ∈ lowSet π k := by
      intro i
      have := hbc i
      simp only [informedAt, toDelivery_fromDelivery, layerNet, h0] at this
      exact hinf i this
    have := card_lowSet_le π k
    have h2 : (univ : Finset I) ⊆ lowSet π k := fun i _ => hall i
    have := card_le_card h2
    rw [card_univ, hI] at this
    omega

theorem stage_zero (hI : Fintype.card I = 2 ^ m + 1) (hm : 1 ≤ m) (L T : ℕ) :
    Stage A m i₀ 0 L ∨ Fail A m T := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin (2 ^ m + 1) ≃ I) := Fintype.card_eq.1 (by simp [hI])
  set π := e.trans (Equiv.swap (e 0) i₀)
  have hπ0 : π 0 = i₀ := by simp [π]
  set D : Delivery I := fun _ _ _ => univ
  have hadm : LayerAdm m 0 π D := fun _ _ _ => Or.inl rfl
  have hlow : ∀ x, x = i₀ → x ∈ lowSet π 0 := by
    rintro x rfl; rw [mem_lowSet, ← hπ0]; simp [layer]
  have h1 : 2 * 0 + 1 < 2 ^ m + 1 := by
    have := Nat.one_le_two_pow (n := m); omega
  by_cases hex : ∃ t, A.senders (A.run (A.initConf i₀) D t) = {i₀}
  · left
    refine ⟨π, D, Nat.find hex, i₀, hπ0, by simp, Nat.find_spec hex, hlow _ rfl, ?_, hadm⟩
    intro x hx
    exact hlow _ (A.informed_univ_subset _ i₀ _ (fun r hr => Nat.find_min hex hr) x hx)
  · right
    push Not at hex
    exact fail_of h1 hI hπ0 hadm (fun x hx =>
      hlow _ (A.informed_univ_subset _ i₀ T (fun r _ => hex r) x hx))

theorem stage_succ (hI : Fintype.card I = 2 ^ m + 1) (hm : 2 ≤ m) {k : ℕ}
    (hk : k + 1 ≤ 2 ^ (m - 2)) (T : ℕ) (hst : Stage A m i₀ k (m - 2)) :
    Stage A m i₀ (k + 1) (m - 2) ∨ Fail A m T := by
  classical
  obtain ⟨π, D, t, jstar, hπ0, ht, hstar, hjP, hinf, hadm⟩ := hst
  set L := m - 2
  have hp : 2 ^ m = 4 * 2 ^ L := by
    rw [show m = L + 2 by omega, pow_add]; ring
  set P := lowSet π k
  set c₀ := A.run (A.initConf i₀) D t
  -- candidates: processes not yet placed
  have hPcard : P.card ≤ 2 * k + 1 := card_lowSet_le π k
  have hC₀ : 2 ^ (L + 1) ≤ (univ \ P).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, hI, pow_succ]
    omega
  obtain ⟨a, ha, b, hb, hab, hiso⟩ := A.exists_pair c₀ P jstar hstar hjP (univ \ P)
    sdiff_disjoint L hC₀
  have haP : a ∉ P := (mem_sdiff.1 ha).2
  have hbP : b ∉ P := (mem_sdiff.1 hb).2
  -- the new layer `L_{k+1} = {2k+1, 2k+2}`
  have hk2 : 2 * k + 2 < 2 ^ m + 1 := by
    have : 1 ≤ 2 ^ L := Nat.one_le_two_pow; omega
  set u₁ : Fin (2 ^ m + 1) := ⟨2 * k + 1, by omega⟩
  set u₂ : Fin (2 ^ m + 1) := ⟨2 * k + 2, by omega⟩
  set Q := univ.filter fun v : Fin (2 ^ m + 1) => layer v ≤ k
  have hu₁ : u₁ ∉ Q := by simp [Q, u₁, layer_le_iff]
  have hu₂ : u₂ ∉ Q := by simp [Q, u₂, layer_le_iff]
  obtain ⟨π', hπ'Q, hπ'1, hπ'2⟩ := exists_equiv_extend π Q (u₁ := u₁) (u₂ := u₂)
    (by simp [u₁, u₂, Fin.ext_iff]) hu₁ hu₂ hab haP hbP
  -- the old placement is kept on layers `≤ k`
  have hsymm : ∀ x, layer (π.symm x) ≤ k → π'.symm x = π.symm x := by
    intro x hx
    rw [Equiv.symm_apply_eq, hπ'Q _ (by simp [Q, hx]), Equiv.apply_symm_apply]
  have hlow_eq : ∀ s ≤ k, lowSet π' s = lowSet π s := by
    intro s hs
    ext x
    simp only [lowSet, mem_map_equiv, mem_filter, mem_univ, true_and]
    constructor
    · intro hx
      have hx' : π.symm x = π'.symm x := by
        have : π' (π'.symm x) = π (π'.symm x) := hπ'Q _ (by simp [Q]; omega)
        rw [Equiv.symm_apply_eq, ← this, Equiv.apply_symm_apply]
      rwa [hx']
    · intro hx
      rwa [hsymm x (by omega)]
  have hlow_succ : lowSet π' (k + 1) = insert a (insert b P) := by
    ext x
    simp only [mem_insert, P, mem_lowSet']
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [layer_le_iff] at hv
      rcases Nat.lt_or_ge v.val (2 * k + 1) with h | h
      · right; right
        exact ⟨v, (layer_le_iff v k).2 (by omega), (hπ'Q v (by simp [Q, layer_le_iff]; omega)).symm⟩
      · rcases Nat.lt_or_ge v.val (2 * k + 2) with h' | h'
        · left; rw [show v = u₁ from Fin.ext (by simp [u₁]; omega), hπ'1]
        · right; left; rw [show v = u₂ from Fin.ext (by simp [u₂]; omega), hπ'2]
    · rintro (rfl | rfl | ⟨v, hv, rfl⟩)
      · exact ⟨u₁, by rw [layer_le_iff]; show 2 * k + 1 ≤ 2 * (k + 1); omega, hπ'1⟩
      · exact ⟨u₂, by rw [layer_le_iff]; show 2 * k + 2 ≤ 2 * (k + 1); omega, hπ'2⟩
      · exact ⟨v, by omega, hπ'Q v (by simp [Q, hv])⟩
  -- the extended delivery rule: `D` up to time `t`, then the rules of stage `k + 1`
  set D' : Delivery I := fun t' => if t' ≤ t then D t' else pairDel P a b t'
  have hD'pre : ∀ t', 1 ≤ t' → t' ≤ t → D' t' = D t' := fun t' _ h => if_pos h
  have hD'post : ∀ u, 1 ≤ u → u ≤ u → (fun u => D' (t + u)) u = pairDel P a b u := by
    intro u hu _
    simp only [D', if_neg (show ¬ t + u ≤ t by omega)]
    rfl
  have hrun_t : A.run (A.initConf i₀) D' t = c₀ := A.run_congr hD'pre t le_rfl
  have hshift : ∀ r, A.run (A.initConf i₀) D' (t + r) = A.run c₀ (pairDel P a b) r := by
    intro r
    rw [A.run_add, hrun_t]
    exact A.run_congr (fun u hu hur => hD'post u hu le_rfl) r le_rfl
  have hinf_shift : ∀ r, A.informed (A.initConf i₀) D' (· = i₀) (t + r) =
      A.informed c₀ (pairDel P a b) (A.informed (A.initConf i₀) D (· = i₀) t) r := by
    intro r
    rw [A.informed_add, hrun_t, A.informed_congr hD'pre t le_rfl]
    exact A.informed_congr (fun u hu hur => hD'post u hu le_rfl) r le_rfl
  have hadm' : LayerAdm m (k + 1) π' D' := by
    intro t' B j
    by_cases ht' : t' ≤ t
    · simp only [D', if_pos ht']
      rcases hadm t' B j with h | ⟨s, hs, hj, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, by omega, by rwa [hsymm j (by omega)],
          by rw [h, hlow_eq (s + 1) (by omega)]⟩
    · simp only [D', if_neg ht', pairDel]
      split_ifs with hc
      · exact Or.inr ⟨k, by omega, by rw [hsymm j (mem_lowSet.1 hc.2)]; exact mem_lowSet.1 hc.2,
          hlow_succ.symm⟩
      · exact Or.inl rfl
  have hπ'0 : π' 0 = i₀ := by
    rw [hπ'Q 0 (mem_filter.2 ⟨mem_univ _, by rw [layer_le_iff]; simp⟩)]; exact hπ0
  by_cases hex : ∃ r, A.senders (A.run c₀ (pairDel P a b) r) = {a} ∨
      A.senders (A.run c₀ (pairDel P a b) r) = {b}
  · left
    have hmin : ∀ r' < Nat.find hex, A.senders (A.run c₀ (pairDel P a b) r') ≠ {a} ∧
        A.senders (A.run c₀ (pairDel P a b) r') ≠ {b} := by
      intro r' hr'
      have := Nat.find_min hex hr'
      push Not at this
      exact this
    have hrL : L + 1 ≤ Nat.find hex := by
      by_contra hcon
      have := hiso (Nat.find hex) (by omega)
      rcases Nat.find_spec hex with h | h
      · exact this.1 h
      · exact this.2 h
    obtain ⟨j, hj, hjab⟩ : ∃ j, A.senders (A.run c₀ (pairDel P a b) (Nat.find hex)) = {j} ∧
        (j = a ∨ j = b) := by
      rcases Nat.find_spec hex with h | h
      · exact ⟨a, h, Or.inl rfl⟩
      · exact ⟨b, h, Or.inr rfl⟩
    refine ⟨π', D', t + Nat.find hex, j, hπ'0, ?_, by rw [hshift]; exact hj, ?_, ?_, hadm'⟩
    · have : (k + 1) * (L + 1) = k * (L + 1) + (L + 1) := by ring
      omega
    · rw [hlow_succ]; rcases hjab with rfl | rfl <;> simp
    · intro x hx
      rw [hinf_shift] at hx
      rw [hlow_succ]
      exact A.informed_pairDel_subset c₀ P a b _ hinf _ hmin x hx
  · right
    push Not at hex
    have h1 : 2 * (k + 1) + 1 < 2 ^ m + 1 := by
      have : 1 ≤ 2 ^ L := Nat.one_le_two_pow; omega
    refine fail_of h1 hI hπ'0 hadm' (T := T) (fun x hx => ?_)
    have hx' := A.informed_mono _ _ _ (Nat.le_add_left T t) hx
    rw [hinf_shift] at hx'
    rw [hlow_succ]
    exact A.informed_pairDel_subset c₀ P a b _ hinf T (fun r _ => hex r) x hx'

end Stages

/-- **Theorem 12.** For `n = 2^m + 1` (`m ≥ 2`) there is an undirected network on `n` nodes such
that every deterministic algorithm (any identifier set of size `n`, CR1, synchronous start) has an
execution in which some process has not received the message after
`2^(m-2) (m-1) = (n-1)/4 · (log₂(n-1) - 1)` rounds (`≥ (n-1) log₂(n-1) / 8`, see
`theorem_12_nlogn`). -/
theorem theorem_12 (m : ℕ) (hm : 2 ≤ m) :
    ∃ N : DualGraph (Fin (2 ^ m + 1)), N.Undirected ∧
      ∀ (I : Type*) [Fintype I] [DecidableEq I], Fintype.card I = 2 ^ m + 1 →
        ∀ {S M : Type*} (A : Algorithm I S M),
          ∃ (π : Fin (2 ^ m + 1) ≃ I) (R : Adversary (Fin (2 ^ m + 1))),
            R.Admissible N ∧ ¬ BroadcastWithin A N π R (2 ^ (m - 2) * (m - 1)) := by
  refine ⟨layerNet m, layerNet_undirected m, ?_⟩
  intro I _ _ hI S M A
  obtain ⟨e⟩ : Nonempty (Fin (2 ^ m + 1) ≃ I) := Fintype.card_eq.1 (by simp [hI])
  set i₀ := e 0
  set T := 2 ^ (m - 2) * (m - 1)
  have hall : ∀ k ≤ 2 ^ (m - 2), Stage A m i₀ k (m - 2) ∨ Fail A m T := by
    intro k
    induction k with
    | zero => intro _; exact stage_zero hI (by omega) _ _
    | succ k ih =>
      intro hk
      rcases ih (by omega) with h | h
      · exact stage_succ hI hm hk T h
      · exact Or.inr h
  rcases hall _ le_rfl with h | h
  · obtain ⟨π, D, t, j, hπ0, ht, -, -, hinf, hadm⟩ := h
    have hp : 2 ^ m = 4 * 2 ^ (m - 2) := by
      rw [show m = (m - 2) + 2 by omega, pow_add]; simp; ring
    have hpos : 1 ≤ 2 ^ (m - 2) := Nat.one_le_two_pow
    refine fail_of (k := 2 ^ (m - 2)) (by omega) hI hπ0 hadm (T := T) (fun x hx => hinf x ?_)
    exact A.informed_mono _ _ _ (by simp only [T]; rw [show m - 2 + 1 = m - 1 by omega] at ht; exact ht) hx
  · exact h

/-- Theorem 12 in `Ω(n log n)` form: with `n = 2^m + 1`, every deterministic algorithm that solves
broadcast within `k` rounds in the network of Theorem 12 needs `k ≥ (n-1) log₂(n-1) / 8`. -/
theorem theorem_12_nlogn (m : ℕ) (hm : 2 ≤ m) :
    ∃ N : DualGraph (Fin (2 ^ m + 1)), N.Undirected ∧
      ∀ (I : Type*) [Fintype I] [DecidableEq I], Fintype.card I = 2 ^ m + 1 →
        ∀ {S M : Type*} (A : Algorithm I S M) (k : ℕ), SolvesWithin A N k →
          (2 ^ m + 1 - 1) * Nat.log 2 (2 ^ m + 1 - 1) < 8 * k := by
  obtain ⟨N, hN, h⟩ := theorem_12 m hm
  refine ⟨N, hN, fun I _ _ hI S M A k hk => ?_⟩
  obtain ⟨π, R, hR, hfail⟩ := h I hI A
  have hT : 2 ^ (m - 2) * (m - 1) < k := by
    by_contra hcon
    exact hfail fun i => A.informed_mono _ _ _ (not_lt.1 hcon) (hk π R hR i)
  simp only [Nat.add_sub_cancel, Nat.log_pow (by norm_num : 1 < 2)]
  have hp : 2 ^ m = 4 * 2 ^ (m - 2) := by
    rw [show m = (m - 2) + 2 by omega, pow_add]; simp; ring
  rw [hp]
  have : 4 * 2 ^ (m - 2) * m ≤ 8 * (2 ^ (m - 2) * (m - 1)) := by
    have h2 : m ≤ 2 * (m - 1) := by omega
    calc 4 * 2 ^ (m - 2) * m = 4 * 2 ^ (m - 2) * m := rfl
      _ ≤ 4 * 2 ^ (m - 2) * (2 * (m - 1)) := Nat.mul_le_mul_left _ h2
      _ = 8 * (2 ^ (m - 2) * (m - 1)) := by ring
  omega

end Podc.BroadcastUnreliableRadio
