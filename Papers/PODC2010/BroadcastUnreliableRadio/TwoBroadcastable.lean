import Papers.PODC2010.BroadcastUnreliableRadio.Model

/-!
# Bounds for 2-broadcastable networks (Section 4: Theorems 2 and 4)

The network: a clique `C` on all nodes but a *receiver* `r`, containing the source `s` and a
*bridge* `b`, plus the reliable edge `b – r`; `G'` is complete. It is 2-broadcastable (`s` then `b`),
but the adversary that delivers a lone message of a node of `C - {b}` exactly to `C` (and every
other message everywhere) hides the bridge among the `n - 2` candidates, forcing `n - 2` rounds
for deterministic algorithms (Theorem 2) and success probability `≤ k / (n - 2)` within `k` rounds
for randomized ones (Theorem 4).

* `claim_3`: Claim 3 for the ID-level executions `alpha` (bridge = `i`).
* `theorem_2`, `theorem_4`: the theorems for `Fin n`, any identifier set of size `n`.
-/

namespace Podc.BroadcastUnreliableRadio

open Finset

variable {I S M : Type*} [Fintype I] [DecidableEq I]

/-! ## ID-level part -/

/-- The adversary rules of Theorem 2, seen from the processes, when the receiver process is `ir`
and the bridge process is `i`: a lone message of a process other than `i`, `ir` reaches everybody
but `ir`; all other messages reach everybody. -/
def bridgeDel (ir i : I) : Delivery I :=
  fun _ B j => if B.card = 1 ∧ j ≠ i ∧ j ≠ ir then univ.erase ir else univ

namespace Algorithm

variable (A : Algorithm I S M)

/-- The execution `αᵢ` of the proof of Theorem 2 (bridge process `i`). -/
noncomputable def alpha (is ir i : I) : ℕ → I → S :=
  A.run (A.initConf is) (bridgeDel ir i)

/-- Claim 3 of the paper: after `k` rounds there is a set `J` of at least `n - 2 - k` bridge
candidates `i` such that `i` has not sent alone in the first `k` rounds of `αᵢ`, and all `αᵢ`,
`i ∈ J`, are in the same configuration. -/
theorem claim_3 (is ir : I) (cand : Finset I) :
    ∀ k : ℕ, ∃ J ⊆ cand, cand.card ≤ J.card + k ∧
      (∀ i ∈ J, ∀ t < k, A.senders (A.alpha is ir i t) ≠ {i}) ∧
      (∀ i₁ ∈ J, ∀ i₂ ∈ J, A.alpha is ir i₁ k = A.alpha is ir i₂ k)
  | 0 => ⟨cand, subset_rfl, by simp, by simp, fun _ _ _ _ => rfl⟩
  | k + 1 => by
    classical
    obtain ⟨J, hJc, hcard, hb, hc⟩ := claim_3 is ir cand k
    -- the common set of senders in round `k + 1`
    by_cases hJ : J.Nonempty
    swap
    · refine ⟨J, hJc, by omega, ?_, ?_⟩ <;> simp [Finset.not_nonempty_iff_eq_empty.1 hJ]
    obtain ⟨i₀, hi₀⟩ := hJ
    set B := A.senders (A.alpha is ir i₀ k) with hB
    have hBi : ∀ i ∈ J, A.senders (A.alpha is ir i k) = B := fun i hi => by rw [hc i hi i₀ hi₀]
    let J' := if h : ∃ i ∈ J, B = {i} then J.erase h.choose else J
    have hJ'J : J' ⊆ J := by
      simp only [J']; split_ifs
      · exact erase_subset _ _
      · exact subset_rfl
    have hcard' : cand.card ≤ J'.card + (k + 1) := by
      simp only [J']; split_ifs with h
      · have := Finset.card_erase_of_mem h.choose_spec.1; omega
      · omega
    have hb' : ∀ i ∈ J', B ≠ {i} := by
      intro i hi hBeq
      simp only [J'] at hi
      split_ifs at hi with h
      · have e : h.choose = i := Finset.singleton_inj.1 (h.choose_spec.2.symm.trans hBeq)
        exact (Finset.mem_erase.1 hi).1 e.symm
      · exact h ⟨i, hi, hBeq⟩
    refine ⟨J', hJ'J.trans hJc, hcard', ?_, ?_⟩
    · intro i hi t ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact hb i (hJ'J hi) t ht
      · rw [hBi i (hJ'J hi)]; exact hb' i hi
    · intro i₁ h₁ i₂ h₂
      simp only [alpha, run_succ]
      have e := hc i₁ (hJ'J h₁) i₂ (hJ'J h₂)
      simp only [alpha] at e
      rw [e]
      apply step_congr
      intro x hx
      have hs : A.senders (A.run (A.initConf is) (bridgeDel ir i₂) k) = B := hBi i₂ (hJ'J h₂)
      rw [hs] at hx ⊢
      simp only [bridgeDel]
      by_cases h1 : B.card = 1
      · obtain ⟨y, hy⟩ := Finset.card_eq_one.1 h1
        rw [hy, Finset.mem_singleton] at hx
        subst hx
        have n1 : x ≠ i₁ := fun e => hb' i₁ h₁ (by rw [hy, e])
        have n2 : x ≠ i₂ := fun e => hb' i₂ h₂ (by rw [hy, e])
        simp [n1, n2]
      · simp [h1]

/-- In `αᵢ`, the receiver process stays uninformed as long as the bridge `i` has not sent alone. -/
theorem not_informed_receiver {is ir i : I} (hsr : is ≠ ir) {k : ℕ}
    (hk : ∀ t < k, A.senders (A.alpha is ir i t) ≠ {i}) :
    ¬ A.informed (A.initConf is) (bridgeDel ir i) (· = is) k ir := by
  intro hinf
  have key := A.informed_of_invariant (A.initConf is) (bridgeDel ir i) (· = is)
    (fun t x => t ≤ k → x ≠ ir) (fun x hx _ => by rw [hx]; exact hsr)
    (fun t x h ht => h (by omega)) ?_ k ir hinf le_rfl
  · exact key rfl
  intro t x j _ hH hj htk hx
  have hj' : j ≠ x := hx ▸ hj (by omega)
  have hjH : j ∈ A.hearers (bridgeDel ir i) (t + 1) (A.run (A.initConf is) (bridgeDel ir i) t) x :=
    by rw [hH]; exact Finset.mem_singleton_self _
  rw [mem_hearers] at hjH
  obtain ⟨hjs, hjr⟩ := hjH
  set B := A.senders (A.run (A.initConf is) (bridgeDel ir i) t)
  have hjr : x ∈ bridgeDel ir i (t + 1) B j := hjr.resolve_right (Ne.symm hj')
  by_cases h1 : B.card = 1
  · obtain ⟨y, hy⟩ := Finset.card_eq_one.1 h1
    have hjy : j = y := by rw [hy] at hjs; simpa using hjs
    subst hjy
    by_cases hji : j = i
    · subst hji; exact hk t (by omega) (by rw [alpha]; exact hy)
    · have hjir : j ≠ ir := hx ▸ hj'
      simp [bridgeDel, h1, hji, hjir, hx] at hjr
  · -- at least two senders, all messages reach everybody
    have hall : A.hearers (bridgeDel ir i) (t + 1)
        (A.run (A.initConf is) (bridgeDel ir i) t) x = B :=
      A.hearers_eq_senders (fun y _ => by simp [B, bridgeDel, h1])
    rw [hall] at hH
    exact h1 (by rw [hH]; simp)

/-- The ID-level core of Theorems 2 and 4: for every deterministic algorithm, at least
`|cand| - k` of the executions `αᵢ` (`i ∈ cand`) do not inform the receiver within `k` rounds. -/
theorem exists_many_failures {is ir : I} (hsr : is ≠ ir) (cand : Finset I) (k : ℕ) :
    ∃ J ⊆ cand, cand.card ≤ J.card + k ∧
      ∀ i ∈ J, ¬ A.informed (A.initConf is) (bridgeDel ir i) (· = is) k ir := by
  obtain ⟨J, hJ, hc, hb, -⟩ := A.claim_3 is ir cand k
  exact ⟨J, hJ, hc, fun i hi => A.not_informed_receiver hsr (hb i hi)⟩

end Algorithm

/-! ## The network -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The clique-plus-bridge network of Theorem 2 with source `s`, bridge `b`, receiver `r`. -/
def bridgeNet (s b r : V) (hsb : s ≠ b) (hsr : s ≠ r) (hbr : b ≠ r) : DualGraph V where
  E u v := u ≠ v ∧ ((u ≠ r ∧ v ≠ r) ∨ (u = b ∧ v = r) ∨ (u = r ∧ v = b))
  E' u v := u ≠ v
  le _ _ h := h.1
  src := s
  reachable v := by
    by_cases hvs : v = s
    · subst hvs; exact Relation.ReflTransGen.refl
    by_cases hvr : v = r
    · subst hvr
      exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hsb, Or.inl ⟨hsr, hbr⟩⟩)
        ⟨hbr, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact Relation.ReflTransGen.single ⟨Ne.symm hvs, Or.inl ⟨hsr, hvr⟩⟩

theorem bridgeNet_undirected (s b r : V) (hsb hsr hbr) :
    (bridgeNet s b r hsb hsr hbr).Undirected := by
  constructor
  · rintro u v ⟨huv, h⟩
    refine ⟨Ne.symm huv, ?_⟩
    rcases h with h | h | h
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
  · intro u v h; exact Ne.symm h

/-- The fixed node-level adversary of Theorems 2 and 4 (rules 1–3 of the proof of Theorem 2). -/
def bridgeAdv (b r : V) : Adversary V :=
  fun _ X v => if X.card = 1 ∧ v ≠ b ∧ v ≠ r then univ.erase r else univ

theorem bridgeAdv_admissible (s b r : V) (hsb hsr hbr) :
    (bridgeAdv b r).Admissible (bridgeNet s b r hsb hsr hbr) := by
  intro t X v w
  refine ⟨fun hvw => ?_, fun _ => ?_⟩
  · simp only [bridgeAdv]
    split_ifs with h
    · rcases hvw with ⟨-, h' | h' | h'⟩
      · simpa using h'.2
      · exact absurd h'.1 h.2.1
      · exact absurd h'.1 h.2.2
    · exact mem_univ _
  · by_cases h : w = v
    · exact Or.inl h
    · exact Or.inr (Ne.symm h)

theorem toDelivery_bridgeAdv (π : V ≃ I) (b r : V) :
    toDelivery π (bridgeAdv b r) = bridgeDel (π r) (π b) := by
  funext t B j
  simp only [toDelivery, bridgeAdv, bridgeDel, Finset.card_map]
  have e1 : π.symm j ≠ b ↔ j ≠ π b := by
    rw [Ne, Equiv.symm_apply_eq]
  have e2 : π.symm j ≠ r ↔ j ≠ π r := by
    rw [Ne, Equiv.symm_apply_eq]
  by_cases h : B.card = 1 ∧ j ≠ π b ∧ j ≠ π r
  · rw [if_pos h, if_pos ⟨h.1, e1.2 h.2.1, e2.2 h.2.2⟩]
    ext x; simp [Equiv.apply_eq_iff_eq_symm_apply]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, e1.1 h'.2.1, e2.1 h'.2.2⟩)]
    ext x; simp

/-- The two-round algorithm: process `is` sends in round 1, process `ib` in round 2. The state is
the identifier and the number of rounds played. -/
def twoStep (is ib : I) : Algorithm I (I × ℕ) Unit where
  init i _ := (i, 0)
  send st := if (st.1 = is ∧ st.2 = 0) ∨ (st.1 = ib ∧ st.2 = 1) then some () else none
  trans st _ := (st.1, st.2 + 1)

/-- The bridge-node network is 2-broadcastable: the source sends in round 1, the bridge in
round 2 (any placement with the source process at `s` and the bridge process at `b`). -/
theorem bridgeNet_broadcastable (s b r : V) (hsb hsr hbr) (I : Type) [Fintype I] [DecidableEq I]
    (hcard : Fintype.card I = Fintype.card V) :
    Broadcastable (bridgeNet s b r hsb hsr hbr) I 2 := by
  classical
  obtain ⟨π⟩ : Nonempty (V ≃ I) := Fintype.card_eq.1 hcard.symm
  refine ⟨I × ℕ, Unit, twoStep (π s) (π b), π, ?_⟩
  intro R hR i
  set N := bridgeNet s b r hsb hsr hbr
  set A : Algorithm I (I × ℕ) Unit := twoStep (π s) (π b)
  set D := toDelivery π R
  -- states: `(id, round)`
  have hrun : ∀ t j, A.run (A.initConf (π s)) D t j = (j, t) := by
    intro t; induction t with
    | zero => intro j; rfl
    | succ t ih =>
      intro j
      simp only [Algorithm.run_succ, Algorithm.step]
      rw [ih]; rfl
  have hsend : ∀ t, A.senders (A.run (A.initConf (π s)) D t) =
      if t = 0 then {π s} else if t = 1 then {π b} else ∅ := by
    intro t
    ext j
    rw [Algorithm.mem_senders, hrun]
    simp only [A, twoStep]
    have : π s ≠ π b := fun h => hsb (π.injective h)
    split_ifs with h0 h1 <;> subst_vars <;> simp <;> aesop
  -- the reach of a lone sender `π v` covers the `π`-images of the `G`-neighbours of `v`
  have hreach : ∀ t v w, N.E v w → π w ∈ D t {π v} (π v) := by
    intro t v w hvw
    have := (hR t {v} v w).1 hvw
    simp only [D, toDelivery, Finset.mem_map_equiv, Equiv.symm_symm]
    simpa using this
  have hhear : ∀ t (v : V) x, A.senders (A.run (A.initConf (π s)) D t) = {π v} →
      (x = π v ∨ N.E v (π.symm x)) →
      A.hearers D (t + 1) (A.run (A.initConf (π s)) D t) x = {π v} := by
    intro t v x hS hx
    ext j
    rw [Algorithm.mem_hearers, hS, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      refine ⟨rfl, ?_⟩
      rcases hx with hx | hx
      · exact Or.inr hx
      · left; simpa using hreach (t + 1) v _ hx
  -- after round 1 everybody but the receiver is informed
  have h1 : ∀ x, x ≠ π r → A.informed (A.initConf (π s)) D (· = π s) 1 x := by
    intro x hx
    by_cases hxs : x = π s
    · exact Or.inl hxs
    right
    refine ⟨π s, hhear 0 s x (by rw [hsend]; simp) (Or.inr ⟨?_, Or.inl ⟨hsr, ?_⟩⟩), rfl⟩
    · intro h; apply hxs; rw [h]; simp
    · intro h; apply hx; rw [← h]; simp
  show A.informed (A.initConf (π s)) D (· = π s) 2 i
  by_cases hir : i = π r
  · subst hir
    right
    refine ⟨π b, hhear 1 b (π r) (by rw [hsend]; simp) (Or.inr ⟨by simpa using hbr, Or.inr (Or.inl ⟨rfl, ?_⟩)⟩),
      h1 _ (fun h => hbr (π.injective h))⟩
    simp
  · exact Or.inl (h1 i hir)

/-! ## The theorems -/

/-- Placement with the source process `π₀ s` at `s`, receiver `π₀ r` at `r` and process `i` at
the bridge `b`. -/
def bridgePlacement (π₀ : V ≃ I) (b : V) (i : I) : V ≃ I :=
  π₀.trans (Equiv.swap (π₀ b) i)

theorem bridgePlacement_apply_of_ne (π₀ : V ≃ I) {b v : V} {i : I} (hvb : v ≠ b) (hvi : π₀ v ≠ i) :
    bridgePlacement π₀ b i v = π₀ v := by
  simp only [bridgePlacement, Equiv.trans_apply]
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hvb (π₀.injective h)) hvi

theorem bridgePlacement_apply_bridge (π₀ : V ≃ I) (b : V) (i : I) :
    bridgePlacement π₀ b i b = i := by
  simp [bridgePlacement]

/-- The deterministic core shared by Theorems 2 and 4, at the node level: for every algorithm,
for at least `n - 2 - k` of the `n - 2` placements `bridgePlacement π₀ b i` the fixed adversary
`bridgeAdv` defeats broadcast within `k` rounds. -/
theorem bridge_failures (s b r : V) (hsb : s ≠ b) (hsr : s ≠ r) (hbr : b ≠ r) (π₀ : V ≃ I)
    (A : Algorithm I S M) (k : ℕ) :
    ∃ J ⊆ ((univ.erase (π₀ s)).erase (π₀ r)),
      ((univ.erase (π₀ s)).erase (π₀ r)).card ≤ J.card + k ∧
      ∀ i ∈ J, ¬ BroadcastWithin A (bridgeNet s b r hsb hsr hbr) (bridgePlacement π₀ b i)
        (bridgeAdv b r) k := by
  have hsr' : π₀ s ≠ π₀ r := fun h => hsr (π₀.injective h)
  obtain ⟨J, hJ, hc, hf⟩ := A.exists_many_failures hsr' ((univ.erase (π₀ s)).erase (π₀ r)) k
  refine ⟨J, hJ, hc, fun i hi hbc => ?_⟩
  have hmem := hJ hi
  simp only [Finset.mem_erase] at hmem
  have es : bridgePlacement π₀ b i s = π₀ s :=
    bridgePlacement_apply_of_ne π₀ hsb (Ne.symm hmem.2.1)
  have er : bridgePlacement π₀ b i r = π₀ r :=
    bridgePlacement_apply_of_ne π₀ (Ne.symm hbr) (Ne.symm hmem.1)
  have := hbc (π₀ r)
  simp only [informedAt, bridgeNet, toDelivery_bridgeAdv, es, er,
    bridgePlacement_apply_bridge] at this
  exact hf i hi (by simpa [bridgeNet] using this)

/-- **Theorem 2.** For `n ≥ 3` there is a 2-broadcastable undirected network on `n` nodes in which
no deterministic algorithm solves broadcast within `n - 3` rounds (CR1, synchronous start), for
any identifier set of size `n`. -/
theorem theorem_2 (n : ℕ) (hn : 3 ≤ n) :
    ∃ N : DualGraph (Fin n), N.Undirected ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I], Fintype.card I = n →
        Broadcastable N I 2 ∧
        ∀ {S M : Type*} (A : Algorithm I S M), ¬ SolvesWithin A N (n - 3) := by
  have hsb : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hsr : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
  have hbr : (⟨1, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
  refine ⟨bridgeNet _ _ _ hsb hsr hbr, bridgeNet_undirected _ _ _ _ _ _, ?_⟩
  intro I _ _ hI
  refine ⟨bridgeNet_broadcastable _ _ _ _ _ _ I (by simp [hI]), ?_⟩
  intro S M A hA
  obtain ⟨π₀⟩ : Nonempty (Fin n ≃ I) := Fintype.card_eq.1 (by simp [hI])
  obtain ⟨J, -, hc, hf⟩ := bridge_failures _ _ _ hsb hsr hbr π₀ A (n - 3)
  have hcard : ((univ.erase (π₀ ⟨0, by omega⟩)).erase (π₀ ⟨n - 1, by omega⟩)).card = n - 2 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (mem_univ _), card_univ, hI]
    · omega
    · simp only [Finset.mem_erase, mem_univ, and_true, ne_eq, EmbeddingLike.apply_eq_iff_eq]
      exact Ne.symm hsr
  obtain ⟨i, hi⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  exact hf i hi (hA _ _ (bridgeAdv_admissible _ _ _ _ _ _))

open MeasureTheory in
/-- **Theorem 4.** For `n ≥ 3` there is a 2-broadcastable undirected network on `n` nodes and an
admissible deterministic adversary rule `R` (the rules of the proof of Theorem 2) such that, for the
adversary class that only chooses the placement of processes on nodes (and then follows `R`), no
probabilistic algorithm solves broadcast within `k` rounds with probability greater than
`k / (n - 2)`. (The paper states this for `1 ≤ k ≤ n - 3`; it holds for every `k`.) -/
theorem theorem_4 (n : ℕ) (hn : 3 ≤ n) :
    ∃ (N : DualGraph (Fin n)) (R : Adversary (Fin n)), N.Undirected ∧ R.Admissible N ∧
      ∀ (I : Type) [Fintype I] [DecidableEq I], Fintype.card I = n →
        Broadcastable N I 2 ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {S M : Type*}
          (A : Ω → Algorithm I S M) (k : ℕ) (q : ENNReal), (k : ENNReal) / (n - 2 : ℕ) < q →
          ¬ SolvesWithinWithProb μ A N {p | p.2 = R} k q := by
  have hsb : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hsr : (⟨0, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
  have hbr : (⟨1, by omega⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
  refine ⟨bridgeNet _ _ _ hsb hsr hbr, bridgeAdv _ _, bridgeNet_undirected _ _ _ _ _ _,
    bridgeAdv_admissible _ _ _ _ _ _, ?_⟩
  intro I _ _ hI
  refine ⟨bridgeNet_broadcastable _ _ _ _ _ _ I (by simp [hI]), ?_⟩
  intro Ω _ μ _ S M A k q hq hsolve
  classical
  obtain ⟨π₀⟩ : Nonempty (Fin n ≃ I) := Fintype.card_eq.1 (by simp [hI])
  set cand := (univ.erase (π₀ ⟨0, by omega⟩)).erase (π₀ ⟨n - 1, by omega⟩)
  have hcard : cand.card = n - 2 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem (mem_univ _), card_univ, hI]
    · omega
    · simp only [Finset.mem_erase, mem_univ, and_true, ne_eq, EmbeddingLike.apply_eq_iff_eq]
      exact Ne.symm hsr
  choose T hTm hTs hTq using fun i : I => hsolve (bridgePlacement π₀ ⟨1, by omega⟩ i, bridgeAdv _ _) rfl
  -- pointwise: at most `k` of the events `T i` (`i ∈ cand`) occur
  have hpt : ∀ ω, (cand.filter fun i => ω ∈ T i).card ≤ k := by
    intro ω
    obtain ⟨J, hJ, hc, hf⟩ := bridge_failures _ _ _ hsb hsr hbr π₀ (A ω) k
    have hsub : cand.filter (fun i => ω ∈ T i) ⊆ cand \ J := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_sdiff]
      exact ⟨hi.1, fun hiJ => hf i hiJ (hTs i hi.2)⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hJ] at this
    omega
  have hsum : ∑ i ∈ cand, μ (T i) ≤ k := by
    calc ∑ i ∈ cand, μ (T i) = ∑ i ∈ cand, ∫⁻ ω, (T i).indicator 1 ω ∂μ := by
          simp [lintegral_indicator_one (hTm _)]
      _ = ∫⁻ ω, ∑ i ∈ cand, (T i).indicator 1 ω ∂μ := by
          rw [lintegral_finset_sum]
          intro i _
          exact measurable_one.indicator (hTm i)
      _ ≤ ∫⁻ _, (k : ENNReal) ∂μ := by
          apply lintegral_mono
          intro ω
          have : ∑ i ∈ cand, (T i).indicator (1 : Ω → ENNReal) ω =
              ((cand.filter fun i => ω ∈ T i).card : ENNReal) := by
            simp [Set.indicator_apply, Finset.sum_boole]
          simp only [this]
          exact_mod_cast hpt ω
      _ = k := by simp
  have hlow : (cand.card : ENNReal) * q ≤ ∑ i ∈ cand, μ (T i) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => hTq i
  rw [hcard] at hlow
  have hn2 : ((n - 2 : ℕ) : ENNReal) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero]; omega
  rw [ENNReal.div_lt_iff (Or.inl hn2) (Or.inl (by simp))] at hq
  rw [mul_comm] at hq
  exact absurd (hlow.trans hsum) (not_le.2 hq)

end Podc.BroadcastUnreliableRadio
