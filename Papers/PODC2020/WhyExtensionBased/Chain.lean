import Papers.PODC2020.WhyExtensionBased.Actions

/-!
# Lemma 5.6: every chain of queries in phase 1 is finite

We consider an infinite chain of queries `(C k, q k)` in phase 1, `C (k+1) = C k · q k`, answered by
the adversary (`A (k+1) = qstep (A k) (C k) (q k)`), and derive a contradiction (`no_chain`):
1. only finitely many vertices get terminated (a terminated process is never queried again), so the
   protocol `δ` of the adversary is eventually constant;
2. the number `t` of subdivisions tends to infinity, increasing by one at each subdivision, and each
   subdivision increases the distances `T(a)`–`U(a)` and `T(a)`–`T(b)` (Lemma 5.5);
3. at the first query creating a vertex `s` of `r ≥ t₀ + 2` rounds, `s` is at distance `≥ 3` from all
   terminated vertices (otherwise it would be safe and terminated); all vertices `Σ` of the chain with
   `r` rounds are within distance 1 of `s` and have seen the same input `a` (the process with the
   smallest view of `S_r`); by Lemma 4.13 every vertex with carrier in `Σ`, in particular the next
   vertex created with `r + 1` rounds, is safe for `a` — so the adversary terminates it,
   contradicting that it subdivides.
-/

namespace Podc.WhyExtensionBased

open Cslib.NIS Cslib.NIS.Subdiv St
open scoped Classical

variable {P X : Type} [DecidableEq P]

/-- The three possible reactions to a query. -/
lemma qstep_cases (A : AState P X) (C : Config P X) (q : P) :
    (qstep A C q = A ∧ ¬ ((stepState C q).Settled ∧ (stepState C q).rounds = A.t ∧
        decided A.term (stepState C q) = none)) ∨
    ((stepState C q).Settled ∧ (stepState C q).rounds = A.t ∧
        decided A.term (stepState C q) = none ∧
      ((∃ a, Safe A.term A.t (stepState C q) a ∧
          qstep A C q = { A with term := setTerm A.term (stepState C q) a }) ∨
       ((¬ ∃ a, Safe A.term A.t (stepState C q) a) ∧ qstep A C q = subdivide A))) := by
  unfold qstep
  split_ifs with h1 h2
  · exact Or.inr ⟨h1.1, h1.2.1, h1.2.2, Or.inl ⟨_, Classical.choose_spec h2, rfl⟩⟩
  · exact Or.inr ⟨h1.1, h1.2.1, h1.2.2, Or.inr ⟨h2, rfl⟩⟩
  · exact Or.inl ⟨rfl, h1⟩

section Chain

variable [Fintype P] (A : ℕ → AState P X) (C : ℕ → Config P X) (q : ℕ → P)

/-- The hypotheses of Lemma 5.6: an infinite chain of legal queries in phase 1. -/
structure IsChain : Prop where
  inv : ∀ k, AInv (A k)
  rc : ∀ k, RC (A k).term (A k).t (C k)
  act : ∀ k, Active (A k).term (C k) (q k)
  next : ∀ k, A (k + 1) = qstep (A k) (C k) (q k)
  conf : ∀ k, C (k + 1) = step (C k) (q k)

variable {A C q}

lemma IsChain.le_succ (h : IsChain A C q) (k : ℕ) : Le (A k) (A (k + 1)) := by
  rw [h.next k]; exact (qstep_spec (h.inv k) (h.rc k) (h.act k)).2.1

lemma IsChain.le (h : IsChain A C q) {k m : ℕ} (hkm : k ≤ m) : Le (A k) (A m) := by
  induction m, hkm using Nat.le_induction with
  | base => exact Le.refl _
  | succ m _ ih => exact ih.trans (h.le_succ m)

lemma IsChain.anc_mono (h : IsChain A C q) {k m : ℕ} (hkm : k ≤ m) (j : P) :
    (C k j).anc ⊆ (C m j).anc := by
  induction m, hkm using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih =>
    intro x hx
    have hx' := ih hx
    rw [h.conf m]
    by_cases hj : j = q m
    · subst hj; rw [step_self, anc_stepState]; exact List.mem_cons_of_mem _ hx'
    · rw [step_ne _ hj]; exact hx'

/-- Number of terminated processes. -/
noncomputable def nTerm (A : AState P X) (E : Config P X) : ℕ :=
  (Finset.univ.filter fun j => decided A.term (E j) ≠ none).card

lemma IsChain.nTerm_mono (h : IsChain A C q) (k : ℕ) :
    nTerm (A k) (C k) ≤ nTerm (A (k + 1)) (C (k + 1)) := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  have hjq : j ≠ q k := by rintro rfl; exact hj (h.act k)
  rw [h.conf k, step_ne _ hjq, (h.le_succ k).2.2 _ (Or.inr hj)]; exact hj

lemma IsChain.nTerm_succ (h : IsChain A C q) {k : ℕ} (hk : (A (k + 1)).term ≠ (A k).term) :
    nTerm (A k) (C k) < nTerm (A (k + 1)) (C (k + 1)) := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun j hj => ?_) |>.2 ⟨q k, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have hjq : j ≠ q k := by rintro rfl; exact hj (h.act k)
    rw [h.conf k, step_ne _ hjq, (h.le_succ k).2.2 _ (Or.inr hj)]; exact hj
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h.conf k, step_self]
    rcases qstep_cases (A k) (C k) (q k) with ⟨h1, -⟩ | ⟨hss, hst, hsd, ⟨a, -, h1⟩ | ⟨-, h1⟩⟩
    · exact absurd (by rw [h.next k, h1]) hk
    · rw [h.next k, h1]
      show decided (setTerm _ _ a) _ ≠ none
      rw [decided_setTerm hss (Settled.not_isInit_of_rounds (by have := (h.inv k).one_le; omega))]
      simp
    · exact absurd (by rw [h.next k, h1]; rfl) hk
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]; exact h.act k

/-- Step 1: the protocol of the adversary is eventually constant. -/
lemma IsChain.term_const (h : IsChain A C q) :
    ∃ K, ∀ k, K ≤ k → (A k).term = (A K).term := by
  have hmono : ∀ k m, k ≤ m → nTerm (A k) (C k) ≤ nTerm (A m) (C m) := fun k m hkm => by
    induction m, hkm using Nat.le_induction with
    | base => exact le_rfl
    | succ m _ ih => exact ih.trans (h.nTerm_mono m)
  have hbd : ∀ k, nTerm (A k) (C k) ≤ Fintype.card P := fun k =>
    (Finset.card_le_univ _)
  by_contra hne
  push_neg at hne
  -- infinitely many changes give arbitrarily many terminated processes
  have hgrow : ∀ i : ℕ, ∃ k, i ≤ nTerm (A k) (C k) := by
    intro i
    induction i with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ i ih =>
      obtain ⟨k, hk⟩ := ih
      -- a change after `k`
      have : ∃ m, k ≤ m ∧ (A (m + 1)).term ≠ (A m).term := by
        by_contra hc
        push_neg at hc
        have key : ∀ m, k ≤ m → (A m).term = (A k).term := fun m hkm => by
          induction m, hkm using Nat.le_induction with
          | base => rfl
          | succ m hkm ih => rw [hc m hkm]; exact ih
        obtain ⟨m, hkm, hm⟩ := hne k
        exact hm (key m hkm)
      obtain ⟨m, hkm, hm⟩ := this
      exact ⟨m + 1, by have := hmono k m hkm; have := h.nTerm_succ hm; omega⟩
  obtain ⟨k, hk⟩ := hgrow (Fintype.card P + 1)
  have := hbd k; omega

end Chain


/-! ## Every state has seen its own input; a common seen input for a layer of a configuration -/

lemma inPast_init_self : ∀ s : St P X, InPast (init s.pid s.input) s
  | init i x => InPast.refl _
  | upd s => InPast.upd (inPast_init_self s)
  | scan s v => InPast.scanSelf (inPast_init_self s)

lemma seen_input_self (s : St P X) : Seen s.input s := ⟨_, inPast_init_self s⟩

/-- All states after `r ≥ 1` rounds occurring in a configuration have seen a common input: the input
of the process whose scan of `S_r` returned the smallest view. -/
lemma common_seen [Fintype P] {E : Config P X} (hE : Rch E) {r : ℕ} (hr : 1 ≤ r)
    (S : Set (St P X)) (hS : ∀ z ∈ S, ∃ j, z ∈ (E j).anc ∧ z.Settled ∧ z.rounds = r)
    (hne : S.Nonempty) : ∃ a, ∀ z ∈ S, Seen a z := by
  let cnt : St P X → ℕ := fun z => (Finset.univ.filter fun i => (z.view i).isSome).card
  obtain ⟨z0, hz0S, hmin⟩ := WellFounded.has_min (measure cnt).wf S hne
  obtain ⟨j0, hz0a, hz0s, hz0r⟩ := hS z0 hz0S
  -- shape of the states of `S`
  have hshape : ∀ z j, z ∈ (E j).anc → z.Settled → z.rounds = r →
      ∃ w v, z = scan (upd w) v ∧ v j = some w ∧ w.rounds + 1 = r := by
    intro z j hz hzs hzr
    cases z with
    | init => simp [rounds] at hzr; omega
    | upd => exact absurd hzs id
    | scan s v =>
      obtain ⟨w, rfl, -, hv⟩ := Rch.scan_shape hE hz
      exact ⟨w, v, rfl, hv, by simpa [rounds] using hzr⟩
  obtain ⟨w0, v0, rfl, hv0, hw0r⟩ := hshape z0 j0 hz0a hz0s hz0r
  refine ⟨w0.input, fun z hzS => ?_⟩
  have hw0z : ∀ v w, z = scan (upd w) v → v j0 = some w0 → Seen w0.input z := by
    rintro v w rfl hv
    exact (seen_input_self w0).mono (InPast.scanView hv (InPast.upd (InPast.refl _)))
  obtain ⟨j, hza, hzs, hzr⟩ := hS z hzS
  obtain ⟨w, v, rfl, hv, hwr⟩ := hshape z j hza hzs hzr
  rcases Rch.view_nested hE hz0a hza (by omega) with h | h
  · exact hw0z v w rfl (h j0 w0 hv0)
  · -- the view of `z` is contained in the smallest view, hence equal to it
    have hsub : (Finset.univ.filter fun i => (v i).isSome) ⊆
        (Finset.univ.filter fun i => (v0 i).isSome) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists] at hi ⊢
      obtain ⟨w', hw'⟩ := hi; exact ⟨w', h i w' hw'⟩
    have hle : cnt (scan (upd w0) v0) ≤ cnt (scan (upd w) v) := by
      by_contra hlt; push_neg at hlt; exact hmin _ hzS hlt
    have heq := Finset.eq_of_subset_of_card_le hsub hle
    have hj0 : j0 ∈ (Finset.univ.filter fun i => (v i).isSome) := by
      rw [heq]; simp [hv0]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists] at hj0
    obtain ⟨w', hw'⟩ := hj0
    have : w' = w0 := Option.some_injective _ ((h j0 w' hw').symm.trans hv0)
    subst this
    exact hw0z v w rfl hw'

section Chain2

variable [Fintype P] {A : ℕ → AState P X} {C : ℕ → Config P X} {q : ℕ → P}

lemma depth_le_rounds {E : Config P X} (hE : Rch E) (j : P) :
    (E j).depth ≤ 2 * (E j).rounds + 1 := by
  cases hj : E j with
  | init => simp [St.depth]
  | upd s =>
    have := Rch.depth_upd hE (j := j) (s := s) (by rw [hj]; exact St.mem_anc_self _)
    simp [rounds] at this ⊢; omega
  | scan s v =>
    have := Rch.depth_settled hE (j := j) (z := scan s v) (by rw [hj]; exact St.mem_anc_self _)
      trivial
    omega

/-- Step 2: the number of subdivisions is unbounded. -/
lemma IsChain.t_unbounded (h : IsChain A C q) (T : ℕ) : ∃ k, T ≤ (A k).t := by
  by_contra hne
  push_neg at hne
  have hdepth : ∀ k, totalDepth (C k) = totalDepth (C 0) + k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [h.conf k, measure_step, ih]; ring
  have hbound : ∀ k, totalDepth (C k) ≤ Fintype.card P * (2 * T + 1) := by
    intro k
    unfold totalDepth
    calc ∑ j, (C k j).depth ≤ ∑ _j : P, (2 * T + 1) := by
          apply Finset.sum_le_sum
          intro j _
          have h1 := depth_le_rounds (h.rc k).1.rch j
          have h2 : (C k j).rounds ≤ (A k).t := by
            rcases (h.rc k).2 j with h | ⟨h, _⟩ <;> omega
          have := hne k
          omega
      _ = Fintype.card P * (2 * T + 1) := by simp
  have := hbound (Fintype.card P * (2 * T + 1) + 1)
  rw [hdepth] at this; omega

/-- After the protocol is constant, every step keeps the state or subdivides. -/
lemma IsChain.step_cases (h : IsChain A C q) {K : ℕ}
    (hK : ∀ k, K ≤ k → (A k).term = (A K).term) {k : ℕ} (hk : K ≤ k) :
    A (k + 1) = A k ∨
    (A (k + 1) = subdivide (A k) ∧ (stepState (C k) (q k)).Settled ∧
      (stepState (C k) (q k)).rounds = (A k).t ∧ decided (A k).term (stepState (C k) (q k)) = none ∧
      ¬ ∃ a, Safe (A k).term (A k).t (stepState (C k) (q k)) a) := by
  rcases qstep_cases (A k) (C k) (q k) with ⟨h1, -⟩ | ⟨hss, hst, hsd, ⟨a, -, h1⟩ | ⟨hns, h1⟩⟩
  · exact Or.inl (by rw [h.next k, h1])
  · exfalso
    have hterm : (A (k + 1)).term = (A k).term := by rw [hK _ (by omega), hK k hk]
    rw [h.next k, h1] at hterm
    have := congrArg (fun δ => decided δ (stepState (C k) (q k))) hterm
    simp only at this
    rw [decided_setTerm hss (Settled.not_isInit_of_rounds (by have := (h.inv k).one_le; omega)),
      hsd] at this
    simp at this
  · exact Or.inr ⟨by rw [h.next k, h1], hss, hst, hsd, hns⟩

/-- Step 3: distances grow by one at each subdivision. -/
lemma IsChain.far_grow (h : IsChain A C q) {K : ℕ} (hK : ∀ k, K ≤ k → (A k).term = (A K).term)
    {k : ℕ} (hk : K ≤ k) :
    (∀ a, Far (Adj (A K).term (A k).t) (Tset (A K).term (A k).t a) (Uset (A K).term (A k).t a)
      (2 + ((A k).t - (A K).t))) ∧
    (∀ a b, a ≠ b → Far (Adj (A K).term (A k).t) (Tset (A K).term (A k).t a)
      (Tset (A K).term (A k).t b) (3 + ((A k).t - (A K).t))) := by
  induction k, hk using Nat.le_induction with
  | base => simpa using ⟨(h.inv K).far4, (h.inv K).far5⟩
  | succ k hk ih =>
    have hle := (h.le hk).1
    rcases h.step_cases hK hk with h1 | ⟨h1, -⟩
    · rw [h1]; exact ih
    · rw [h1]
      have h0 : ∀ s, decided (A K).term s ≠ none → s.rounds ≤ (A k).t := fun s hs => by
        have := (h.inv K).dec_le s hs; omega
      obtain ⟨h4, h5⟩ := subdiv_far h0 ih.1 ih.2 (by omega) (by omega)
      simp only [subdivide]
      refine ⟨fun a => (h4 a).mono le_rfl le_rfl (by omega),
        fun a b hab => (h5 a b hab).mono le_rfl le_rfl (by omega)⟩

end Chain2


section Chain3

variable [Fintype P] {A : ℕ → AState P X} {C : ℕ → Config P X} {q : ℕ → P}

/-- `t` reaches every value above its value at time `K` exactly at a subdivision. -/
lemma IsChain.exists_subdiv_at (h : IsChain A C q) {K R : ℕ} (hR : (A K).t ≤ R) :
    ∃ k, K ≤ k ∧ (A k).t = R ∧ (A (k + 1)).t = R + 1 := by
  have hex : ∃ m, R + 1 ≤ (A (K + m)).t := by
    obtain ⟨k, hk⟩ := h.t_unbounded (R + 1)
    refine ⟨k, le_trans hk ?_⟩
    exact (h.le (by omega : k ≤ K + k)).1
  let m := Nat.find hex
  have hm : R + 1 ≤ (A (K + m)).t := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    have : R + 1 ≤ (A K).t := by simpa [h0] using hm
    omega
  have hprev : ¬ R + 1 ≤ (A (K + (m - 1))).t := Nat.find_min hex (by omega)
  have hstep : (A (K + (m - 1) + 1)).t ≤ (A (K + (m - 1))).t + 1 := by
    rw [h.next]
    rcases qstep_cases (A (K + (m - 1))) (C (K + (m - 1))) (q (K + (m - 1))) with
      ⟨h1, -⟩ | ⟨-, -, -, ⟨a, -, h1⟩ | ⟨-, h1⟩⟩ <;> rw [h1] <;> simp [subdivide]
  have heq : K + (m - 1) + 1 = K + m := by omega
  rw [heq] at hstep
  have hmono := (h.le (show K ≤ K + (m - 1) by omega)).1
  exact ⟨K + (m - 1), by omega, by omega, by rw [heq]; omega⟩

/-- **Lemma 5.6**: there is no infinite chain of queries in phase 1. -/
theorem IsChain.false (h : IsChain A C q) : False := by
  obtain ⟨K, hK⟩ := h.term_const
  set δ := (A K).term with hδ
  have hterm : ∀ k, K ≤ k → (A k).term = δ := hK
  set r := (A K).t + 2 with hr
  obtain ⟨k1, hk1, ht1, ht1'⟩ := h.exists_subdiv_at (K := K) (R := r) (by omega)
  obtain ⟨k2, hk2, ht2, ht2'⟩ := h.exists_subdiv_at (K := K) (R := r + 1) (by omega)
  have hk12 : k1 + 1 ≤ k2 := by
    by_contra hlt; push_neg at hlt
    have := (h.le (show k2 ≤ k1 by omega)).1; omega
  have hdecK : ∀ z, decided δ z ≠ none → z.rounds ≤ (A K).t := (h.inv K).dec_le
  -- the vertex created at time `k1`
  obtain ⟨-, hss, hsr, hsd, hns⟩ := (h.step_cases hK hk1).resolve_left (by
    intro h'; have := congrArg AState.t h'; omega)
  rw [ht1] at hsr hns; rw [hterm k1 hk1] at hsd hns
  set s := stepState (C k1) (q k1) with hs
  obtain ⟨hf4, hf5⟩ := h.far_grow hK hk1
  rw [ht1] at hf4 hf5
  have hf4' : ∀ a, Far (Adj δ r) (Tset δ r a) (Uset δ r a) (2 + 2) :=
    fun a => (hf4 a).mono le_rfl le_rfl (by omega)
  have hf5' : ∀ a b, a ≠ b → Far (Adj δ r) (Tset δ r a) (Tset δ r b) (3 + 2) :=
    fun a b hab => (hf5 a b hab).mono le_rfl le_rfl (by omega)
  -- (U1) `s` is far from all terminated vertices
  have hU1 : ∀ c, Far (Adj δ r) {s} (Tset δ r c) 3 := by
    intro c
    by_contra hnf
    simp only [Far, not_forall, not_le, exists_prop] at hnf
    obtain ⟨l, hl, z, hz, hzs, b, hb, hbT, hlen⟩ := hnf
    rw [Set.mem_singleton_iff] at hzs; subst hzs
    apply hns
    refine ⟨c, Far.of_walk (e := 2) adj_symm (hf4' c) hl hz hb hbT (by omega), fun b' hb' => ?_⟩
    exact Far.of_walk (e := 2) adj_symm (hf5' c b' (Ne.symm hb')) hl hz hb hbT (by omega)
  -- the layer `Σ` at time `k2`
  have hRE : Reach δ (C k2) := by have := (h.rc k2).1; rwa [hterm k2 hk2] at this
  set S : Set (St P X) := {z | ∃ j, z ∈ (C k2 j).anc ∧ z.Settled ∧ z.rounds = r} with hS
  have hsS : s ∈ S := by
    refine ⟨q k1, h.anc_mono hk12 _ ?_, hss, hsr⟩
    rw [h.conf k1, step_self]; exact St.mem_anc_self _
  have hSact : ∀ z ∈ S, decided δ z = none := by
    rintro z ⟨j, -, -, hzr⟩
    by_contra hz; have := hdecK z hz; omega
  have hSvtx : ∀ z ∈ S, Vtx δ r z ∧ Occ δ z := by
    rintro z ⟨j, hz, hzs, hzr⟩
    exact ⟨⟨hzs, Or.inl hzr⟩, hRE.occ_of_anc hz⟩
  have hSadj : ∀ z ∈ S, z = s ∨ Adj δ r s z := by
    rintro z ⟨j, hz, hzs, hzr⟩
    obtain ⟨-, hsa, -, -⟩ := hsS
    have hsa : s ∈ (C k2 (q k1)).anc := h.anc_mono hk12 _ (by
      rw [h.conf k1, step_self]; exact St.mem_anc_self _)
    by_cases hj : j = q k1
    · subst hj
      left
      refine St.eq_of_mem_anc_of_depth_eq hz hsa ?_
      rw [Rch.depth_settled hRE.rch hz hzs, Rch.depth_settled hRE.rch hsa hss, hzr, hsr]
    · exact Or.inr (hRE.adj_of_anc (Ne.symm hj) hsa hz hss hzs hsr hzr)
  obtain ⟨a, ha⟩ := common_seen hRE.rch (r := r) (by omega) S (fun z hz => hz) ⟨s, hsS⟩
  have hFT : ∀ b, Far (Adj δ r) S (Tset δ r b) 2 := fun b =>
    far_of_forall_singleton fun z hz => by
      rcases hSadj z hz with rfl | hadj
      · exact (hU1 b).mono subset_rfl subset_rfl (by omega)
      · exact Far.of_adj adj_symm (hU1 b) rfl hadj
  have hFU : Far (Adj δ r) S (Uset δ r a) 1 := far_of_forall_singleton fun z hz =>
    far_of_neighbors (fun hzU => hzU.2.2 (ha z hz)) fun _ _ => far_zero _ _
  have hcut : ∀ B : Set (St P X), Far (Adj δ r) S B 1 →
      ActCut (Adj δ r) (fun s => decided δ s = none) S B := by
    intro B hB l hl x0 hx0 hx0S z hz hzB
    match l, hl, hx0, hz with
    | [y], hl, hx0, hz =>
      simp at hx0 hz; subst hx0; subst hz
      exact (far_not_mem hB le_rfl hx0S hzB).elim
    | y0 :: y1 :: rest, hl, hx0, hz =>
      simp at hx0; subst hx0
      have h01 : Adj δ r y0 y1 := (List.isChain_cons_cons.1 hl.2).1
      refine ⟨y0, y1, ⟨[], rest, by simp⟩, hSact y0 hx0S, ?_⟩
      by_contra hy1
      obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hy1
      exact far_not_adj (hFT c) le_rfl hx0S (mem_Tset_of_adj h01 hc) h01
  have hnew : ∀ z : St P X, z.rounds = r + 1 → decided δ z = none := fun z hz => by
    by_contra h'; have := hdecK z h'; omega
  have hA'U : Far (Adj δ (r + 1)) {x | car r x ⊆ S} (Uset δ (r + 1) a) (1 + 1) :=
    far_layer_succ (fun x hx => hx) (car_Uset a) hFU (hcut _ hFU)
  have hA'T : ∀ b, Far (Adj δ (r + 1)) {x | car r x ⊆ S} (Tset δ (r + 1) b) (2 + 1) := fun b =>
    far_layer_succ (fun x hx => hx) (car_Tset hnew) (hFT b)
      (hcut _ ((hFT b).mono subset_rfl subset_rfl (by omega)))
  -- the vertex created at time `k2` has its carrier in `Σ`, hence is safe
  obtain ⟨-, hss', hsr', hsd', hns'⟩ := (h.step_cases hK hk2).resolve_left (by
    intro h'; have := congrArg AState.t h'; omega)
  rw [ht2] at hsr' hns'; rw [hterm k2 hk2] at hsd' hns'
  set s' := stepState (C k2) (q k2) with hs'
  have hR2 : Reach δ (C (k2 + 1)) := by
    have := (h.rc (k2 + 1)).1; rwa [hterm (k2 + 1) (by omega)] at this
  have hs'eq : C (k2 + 1) (q k2) = s' := by rw [h.conf k2, step_self]
  have hs'occ : Occ δ s' := ⟨C (k2 + 1), hR2, by rw [← hs'eq, hR2.pid]⟩
  have hcarS : car r s' ⊆ S := by
    intro c hc
    obtain ⟨hcv, -, -, hcr, hcp⟩ := hs'occ.mem_car hss' hsr' hc
    have hpa := Rch.past_anc hR2.rch (i := q k2) (by rw [hs'eq]; exact hcp)
    refine ⟨c.pid, ?_, hcv.1, hcr⟩
    by_cases hcq : c.pid = q k2
    · rw [hcq, h.conf k2, step_self, anc_stepState] at hpa
      rw [hcq]
      rcases List.mem_cons.1 hpa with h1 | h1
      · exfalso; rw [h1, hsr'] at hcr; omega
      · exact h1
    · rw [h.conf k2, step_ne _ hcq] at hpa; exact hpa
  exact hns' ⟨a, (hA'U.mono (by simpa using hcarS) subset_rfl le_rfl),
    fun b _ => (hA'T b).mono (by simpa using hcarS) subset_rfl le_rfl⟩

end Chain3

end Podc.WhyExtensionBased
