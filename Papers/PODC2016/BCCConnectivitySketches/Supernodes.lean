import Papers.PODC2016.BCCConnectivitySketches.Model

/-!
# Theorem 1: connectivity in `⌈1/ε⌉` rounds of `BClique[n^ε log n]` by merging supernodes

Montealegre–Todinca, *Deterministic graph connectivity in the broadcast congested clique*
(PODC 2016 BA; arXiv:1602.04095v3), Theorem 1.

Protocol (`Supernodes.alg k`). Every node stores its input `N(v)` and the *announced graph* `A_t`
(all edges broadcast so far; the same at every node). The supernodes of round `t` are the connected
components of `A_t`. In round `t`, node `u` broadcasts `sel k A_t N(u) u`: neighbours lying in
pairwise different components of `A_t`, none in `u`'s own component, `min(k, #foreign components
adjacent to u)` of them. Then `A_{t+1} = A_t ⊔ {uw | w announced by u}`. A message is a set of at
most `k` nodes, i.e. `k ⌈log₂(n+1)⌉` bits.

Analysis. Call a component of `A_t` *open* if some edge of `G` leaves it (`IsOpenComp`). Since
`A_t ≤ G`, a closed component is a component of `G` and never grows. Every open component of
`A_{t+1}` contains at least `k+1` open components of `A_t` (`exists_fiber`), so
`o_t (k+1)^t ≤ n` for the number `o_t` of open components (`card_openComps_mul_pow_le`). Once
`n < (k+1)^T`, `A_T` has no open component, i.e. it has the same connected components as `G`, and
every node outputs a spanning forest of `A_T` (`isSpanningForest_run`).

The paper uses `k = n^ε`; with `k = ⌈n^ε⌉₊` and `T = ⌈1/ε⌉₊` we have `n ≤ k^T < (k+1)^T`
(`theorem_1`).

Remark on the paper's termination criterion. The proof sketch says that a supernode of round `t`
is *active* if it contains at least `n^ε` supernodes of round `t-1`, and that the protocol stops
when all supernodes are inactive. Taken literally, this test can need one round more than
`⌈1/ε⌉`: for `ε = 1` and connected `G` the single supernode after round 1 contains `n ≥ n^ε`
supernodes of round 0 and so is "active". The fixed-round protocol formalized here needs no
termination test (nodes simply output after `⌈1/ε⌉` rounds), so Theorem 1 as stated holds.
-/

namespace Podc.BCCConnectivitySketches

open Cslib.CongestedClique SimpleGraph Finset

namespace Supernodes

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Selection of announced neighbours -/

/-- The components of `A` (supernodes) other than `u`'s own containing an element of `N`. -/
noncomputable def foreign (A : SimpleGraph V) (N : Finset V) (u : V) :
    Finset A.ConnectedComponent :=
  (N.filter fun w => ¬ A.Reachable u w).image A.connectedComponentMk

/-- `min k |foreign A N u|` of the foreign components, chosen arbitrarily. -/
noncomputable def chosen (k : ℕ) (A : SimpleGraph V) (N : Finset V) (u : V) :
    Finset A.ConnectedComponent :=
  Classical.choose (exists_subset_card_eq (s := foreign A N u) (min_le_right k _))

lemma chosen_subset (k : ℕ) (A : SimpleGraph V) (N : Finset V) (u : V) :
    chosen k A N u ⊆ foreign A N u :=
  (Classical.choose_spec (exists_subset_card_eq (s := foreign A N u) (min_le_right k _))).1

lemma card_chosen (k : ℕ) (A : SimpleGraph V) (N : Finset V) (u : V) :
    (chosen k A N u).card = min k (foreign A N u).card :=
  (Classical.choose_spec (exists_subset_card_eq (s := foreign A N u) (min_le_right k _))).2

/-- A representative in `N` of a foreign component. -/
noncomputable def rep (A : SimpleGraph V) (N : Finset V) (u : V) (c : A.ConnectedComponent) : V :=
  if h : ∃ w ∈ N, ¬ A.Reachable u w ∧ A.connectedComponentMk w = c then h.choose else u

lemma rep_spec {A : SimpleGraph V} {N : Finset V} {u : V} {c : A.ConnectedComponent}
    (hc : c ∈ foreign A N u) :
    rep A N u c ∈ N ∧ ¬ A.Reachable u (rep A N u c) ∧ A.connectedComponentMk (rep A N u c) = c := by
  have h : ∃ w ∈ N, ¬ A.Reachable u w ∧ A.connectedComponentMk w = c := by
    simp only [foreign, mem_image, mem_filter] at hc
    obtain ⟨w, ⟨hw, hr⟩, rfl⟩ := hc
    exact ⟨w, hw, hr, rfl⟩
  rw [rep, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- The neighbours announced by `u`: one representative of each chosen foreign component. -/
noncomputable def sel (k : ℕ) (A : SimpleGraph V) (N : Finset V) (u : V) : Finset V :=
  (chosen k A N u).image (rep A N u)

lemma card_sel_le (k : ℕ) (A : SimpleGraph V) (N : Finset V) (u : V) :
    (sel k A N u).card ≤ k :=
  card_image_le.trans ((card_chosen k A N u).le.trans (min_le_left _ _))

lemma sel_spec {k : ℕ} {A : SimpleGraph V} {N : Finset V} {u w : V} (hw : w ∈ sel k A N u) :
    w ∈ N ∧ ¬ A.Reachable u w := by
  simp only [sel, mem_image] at hw
  obtain ⟨c, hc, rfl⟩ := hw
  have := rep_spec (chosen_subset k A N u hc)
  exact ⟨this.1, this.2.1⟩

lemma image_sel (k : ℕ) (A : SimpleGraph V) (N : Finset V) (u : V) :
    (sel k A N u).image A.connectedComponentMk = chosen k A N u := by
  rw [sel, image_image]
  conv_rhs => rw [← image_id (s := chosen k A N u)]
  exact image_congr fun c hc => (rep_spec (chosen_subset k A N u hc)).2.2

lemma mk_not_mem_foreign (A : SimpleGraph V) (N : Finset V) (u : V) :
    A.connectedComponentMk u ∉ foreign A N u := by
  simp only [foreign, mem_image, mem_filter, not_exists, not_and]
  intro w hw he
  exact hw.2 (ConnectedComponent.eq.1 he).symm

/-! ### The protocol -/

/-- Messages: sets of at most `k` nodes. -/
abbrev Msg (V : Type*) [Fintype V] (k : ℕ) := {S : Finset V // S.card ≤ k}

instance (k : ℕ) : Nonempty (Msg V k) := ⟨⟨∅, by simp⟩⟩

/-- The supernode protocol; state = (input neighbourhood, announced graph). -/
noncomputable def alg (k : ℕ) : TAlg V (Finset V) (Finset V × SimpleGraph V) (Msg V k) where
  init _ N := (N, ⊥)
  send u s := ⟨sel k s.2 s.1 u, card_sel_le k s.2 s.1 u⟩
  step _ s m := (s.1, s.2 ⊔ fromRel fun u w => w ∈ (m u).1)

/-- The announced graph after `t` rounds on input graph `G`. -/
noncomputable def ann (k : ℕ) (G : SimpleGraph V) : ℕ → SimpleGraph V
  | 0 => ⊥
  | t + 1 => ann k G t ⊔ fromRel fun u w => w ∈ sel k (ann k G t) (nbrs G u) u

theorem run_alg (k : ℕ) (G : SimpleGraph V) :
    ∀ t v, (alg k).run (nbrs G) t v = (nbrs G v, ann k G t)
  | 0, v => rfl
  | t + 1, v => by
      have ih := run_alg k G t
      simp only [TAlg.run, ih]
      rfl

/-- Output: a spanning forest of the announced graph. -/
noncomputable def out (s : Finset V × SimpleGraph V) : SimpleGraph V :=
  Classical.choose (exists_isSpanningForest s.2)

/-! ### Analysis -/

variable {k : ℕ} {G : SimpleGraph V}

lemma ann_le : ∀ t, ann k G t ≤ G
  | 0 => bot_le
  | t + 1 => by
      refine sup_le (ann_le t) fun u w h => ?_
      rw [fromRel_adj] at h
      rcases h.2 with h | h
      · exact (mem_nbrs G u w).1 (sel_spec h).1
      · exact ((mem_nbrs G w u).1 (sel_spec h).1).symm

lemma ann_le_succ (t : ℕ) : ann k G t ≤ ann k G (t + 1) := le_sup_left

lemma adj_of_mem_sel {t : ℕ} {u w : V} (h : w ∈ sel k (ann k G t) (nbrs G u) u) :
    (ann k G (t + 1)).Adj u w := by
  refine Or.inr ((fromRel_adj _ _ _).2 ⟨?_, Or.inl h⟩)
  rintro rfl
  exact (sel_spec h).2 (Reachable.refl u)

/-- A component of `A` is open if an edge of `G` leaves it. -/
def IsOpenComp (G A : SimpleGraph V) (c : A.ConnectedComponent) : Prop :=
  ∃ u w, A.connectedComponentMk u = c ∧ G.Adj u w ∧ A.connectedComponentMk w ≠ c

/-- The open components. -/
noncomputable def openComps (G A : SimpleGraph V) : Finset A.ConnectedComponent :=
  univ.filter (IsOpenComp G A)

omit [Fintype V] [DecidableEq V] in
/-- A closed component of `A` is closed under reachability in any `A' ≤ G`. -/
lemma mk_eq_of_closed {A A' : SimpleGraph V} (hA' : A' ≤ G) {c : A.ConnectedComponent}
    (hc : ¬ IsOpenComp G A c) {x y : V} (hx : A.connectedComponentMk x = c)
    (hxy : A'.Reachable x y) : A.connectedComponentMk y = c := by
  rw [reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => exact hx
  | tail _ hab ih =>
      by_contra hne
      exact hc ⟨_, _, ih, hA' hab, hne⟩

omit [Fintype V] [DecidableEq V] in
/-- A component of `A` lying inside an open component of `A' ≥ A` is open. -/
lemma isOpenComp_of_map {A A' : SimpleGraph V} (hAA' : A ≤ A') (hA' : A' ≤ G)
    {c : A.ConnectedComponent} (hD : IsOpenComp G A' (c.map (Hom.ofLE hAA'))) :
    IsOpenComp G A c := by
  by_contra hc
  obtain ⟨u, w, hu, huw, hw⟩ := hD
  induction c using ConnectedComponent.ind with | h x => ?_
  rw [ConnectedComponent.map_mk] at hu hw
  have hxu : A'.Reachable x u := ConnectedComponent.eq.1 hu.symm
  have h1 : A.connectedComponentMk u = A.connectedComponentMk x :=
    mk_eq_of_closed hA' hc rfl hxu
  have h2 : A.connectedComponentMk w = A.connectedComponentMk x := by
    by_contra hne
    exact hc ⟨u, w, h1, huw, hne⟩
  apply hw
  exact ConnectedComponent.eq.2 ((ConnectedComponent.eq.1 h2).mono hAA')

/-- The map from components of `A_t` to components of `A_{t+1}` (supernode merging). -/
noncomputable def up (t : ℕ) :
    (ann k G t).ConnectedComponent → (ann k G (t + 1)).ConnectedComponent :=
  ConnectedComponent.map (Hom.ofLE (ann_le_succ t))

lemma up_mk (t : ℕ) (x : V) :
    up (k := k) (G := G) t ((ann k G t).connectedComponentMk x) =
      (ann k G (t + 1)).connectedComponentMk x := rfl

/-- Key lemma: an open component of `A_{t+1}` contains at least `k+1` components of `A_t`. -/
lemma exists_fiber (t : ℕ) (D : (ann k G (t + 1)).ConnectedComponent)
    (hD : IsOpenComp G (ann k G (t + 1)) D) :
    ∃ s : Finset (ann k G t).ConnectedComponent, s.card = k + 1 ∧ ∀ c ∈ s, up t c = D := by
  obtain ⟨u, w, hu, huw, hw⟩ := hD
  have hsel : ∀ x ∈ sel k (ann k G t) (nbrs G u) u,
      (ann k G (t + 1)).connectedComponentMk x = D := by
    intro x hx
    rw [← hu]
    exact ConnectedComponent.eq.2 (adj_of_mem_sel hx).reachable.symm
  have hnot : ¬ (ann k G t).Reachable u w := fun h => hw (hu ▸ ConnectedComponent.eq.2
    (h.mono (ann_le_succ t)).symm)
  by_cases hk : (foreign (ann k G t) (nbrs G u) u).card ≤ k
  · -- `u` announced a neighbour in every foreign component, in particular in `w`'s one.
    exfalso
    have hch : chosen k (ann k G t) (nbrs G u) u = foreign (ann k G t) (nbrs G u) u :=
      eq_of_subset_of_card_le (chosen_subset k _ _ u) (by rw [card_chosen]; omega)
    have hwf : (ann k G t).connectedComponentMk w ∈ foreign (ann k G t) (nbrs G u) u :=
      mem_image.2 ⟨w, mem_filter.2 ⟨(mem_nbrs G u w).2 huw, hnot⟩, rfl⟩
    rw [← hch, ← image_sel] at hwf
    obtain ⟨x, hx, hxw⟩ := mem_image.1 hwf
    apply hw
    rw [← hsel x hx]
    exact ConnectedComponent.eq.2 ((ConnectedComponent.eq.1 hxw).mono (ann_le_succ t)).symm
  · refine ⟨insert ((ann k G t).connectedComponentMk u) (chosen k (ann k G t) (nbrs G u) u),
      ?_, ?_⟩
    · rw [card_insert_of_notMem (fun h => mk_not_mem_foreign _ _ u (chosen_subset k _ _ u h)),
        card_chosen]
      omega
    · intro c hc
      rcases mem_insert.1 hc with rfl | hc
      · rw [up_mk]; exact hu
      · rw [← image_sel] at hc
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
        rw [up_mk]
        exact hsel x hx

/-- The number of open components drops by a factor `k+1` every round. -/
lemma card_openComps_succ (t : ℕ) :
    (k + 1) * (openComps G (ann k G (t + 1))).card ≤ (openComps G (ann k G t)).card := by
  let s := (openComps G (ann k G t)).filter fun c => IsOpenComp G (ann k G (t + 1)) ((up t) c)
  have hfib : ∀ D ∈ s.image (up t), k + 1 ≤ (s.filter fun c => (up t) c = D).card := by
    intro D hD
    have hDo : IsOpenComp G _ D := by
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hD
      exact (mem_filter.1 hc).2
    obtain ⟨S, hS, hSD⟩ := exists_fiber t D hDo
    rw [← hS]
    refine card_le_card fun c hc => ?_
    have hcD := hSD c hc
    refine mem_filter.2 ⟨mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩, hcD⟩
    · exact isOpenComp_of_map (ann_le_succ t) (ann_le _)
        (show IsOpenComp G _ (up t c) by rw [hcD]; exact hDo)
    · rw [hcD]; exact hDo
  have h1 := mul_card_image_le_card s (k + 1) hfib
  have h2 : openComps G (ann k G (t + 1)) ⊆ s.image (up t) := by
    intro D hD
    have hDo := (mem_filter.1 hD).2
    obtain ⟨S, hS, hSD⟩ := exists_fiber t D hDo
    obtain ⟨c, hc⟩ : S.Nonempty := by rw [← card_pos, hS]; omega
    have hcD := hSD c hc
    refine mem_image.2 ⟨c, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩, hcD⟩
    · exact isOpenComp_of_map (ann_le_succ t) (ann_le _)
        (show IsOpenComp G _ (up t c) by rw [hcD]; exact hDo)
    · rw [hcD]; exact hDo
  calc (k + 1) * (openComps G (ann k G (t + 1))).card ≤ (k + 1) * (s.image (up t)).card :=
        Nat.mul_le_mul_left _ (card_le_card h2)
    _ ≤ s.card := h1
    _ ≤ _ := card_filter_le _ _

lemma card_openComps_mul_pow_le :
    ∀ t, (openComps G (ann k G t)).card * (k + 1) ^ t ≤ Fintype.card V
  | 0 => by
      rw [pow_zero, mul_one]
      exact (card_le_univ _).trans
        (Fintype.card_le_of_surjective (ann k G 0).connectedComponentMk fun c => c.exists_rep)
  | t + 1 => by
      have h1 := card_openComps_succ (k := k) (G := G) t
      have h2 := card_openComps_mul_pow_le t
      calc _ = ((k + 1) * (openComps G (ann k G (t + 1))).card) * (k + 1) ^ t := by ring
        _ ≤ (openComps G (ann k G t)).card * (k + 1) ^ t := Nat.mul_le_mul_right _ h1
        _ ≤ _ := h2

/-- After `T` rounds with `n < (k+1)^T`, the announced graph has the components of `G`. -/
theorem reachable_ann_iff {T : ℕ} (hT : Fintype.card V < (k + 1) ^ T) (u v : V) :
    (ann k G T).Reachable u v ↔ G.Reachable u v := by
  have h0 : openComps G (ann k G T) = ∅ := by
    have := card_openComps_mul_pow_le (k := k) (G := G) T
    rw [← card_eq_zero]
    by_contra h
    have : (k + 1) ^ T ≤ (openComps G (ann k G T)).card * (k + 1) ^ T :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
    omega
  have hedge : ∀ a b, G.Adj a b → (ann k G T).Reachable a b := by
    intro a b hab
    by_contra hr
    have : (ann k G T).connectedComponentMk a ∈ openComps G (ann k G T) :=
      mem_filter.2 ⟨mem_univ _, a, b, rfl, hab, fun h => hr (ConnectedComponent.eq.1 h).symm⟩
    simp [h0] at this
  refine ⟨fun h => h.mono (ann_le T), fun h => ?_⟩
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hab ih => exact ih.trans (hedge _ _ hab)

/-- After `T` rounds with `n < (k+1)^T`, every node outputs a spanning forest of `G`. -/
theorem isSpanningForest_run (k T : ℕ) (hT : Fintype.card V < (k + 1) ^ T)
    (G : SimpleGraph V) (v : V) : IsSpanningForest G (out ((alg k).run (nbrs G) T v)) := by
  rw [run_alg]
  exact (Classical.choose_spec (exists_isSpanningForest (ann k G T))).of_le (ann_le T)
    (reachable_ann_iff hT)

/-! ### Message size -/

omit [DecidableEq V] in
/-- At most `(n+1)^k` sets of size at most `k`. -/
lemma card_msg_le_pow (k : ℕ) : Fintype.card (Msg V k) ≤ (Fintype.card V + 1) ^ k := by
  let g : Msg V k → Fin k → Option V := fun T i =>
    if h : i.1 < T.1.card then some (T.1.equivFin.symm ⟨i.1, h⟩) else none
  have hmem : ∀ T : Msg V k, ∀ v, v ∈ T.1 ↔ ∃ i, g T i = some v := by
    intro T v
    constructor
    · intro hv
      refine ⟨⟨(T.1.equivFin ⟨v, hv⟩).1, by have := T.2; omega⟩, ?_⟩
      simp [g]
    · rintro ⟨i, hi⟩
      simp only [g] at hi
      split_ifs at hi with h
      simp only [Option.some.injEq] at hi
      rw [← hi]; exact (T.1.equivFin.symm _).2
  have hinj : Function.Injective g := by
    intro T T' he
    ext v
    rw [hmem T, hmem T', he]
  calc _ ≤ Fintype.card (Fin k → Option V) := Fintype.card_le_of_injective g hinj
    _ = _ := by simp

omit [DecidableEq V] in
/-- A message fits in `k ⌈log₂(n+1)⌉` bits. -/
lemma card_msg_le (k : ℕ) :
    Fintype.card (Msg V k) ≤ 2 ^ (k * Nat.clog 2 (Fintype.card V + 1)) := by
  refine (card_msg_le_pow k).trans ?_
  rw [mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (card_le_two_pow_clog _) k

/-- The `BClique[k ⌈log₂(n+1)⌉]` protocol. -/
noncomputable def bitAlg (k : ℕ) :
    Bcast.Algorithm V (Finset V) (Finset V × SimpleGraph V) (k * Nat.clog 2 (Fintype.card V + 1)) :=
  (alg k).toBits _ (card_msg_le k)

/-- General form of Theorem 1: `T` rounds of `BClique[k ⌈log₂(n+1)⌉]` compute a spanning forest
whenever `n < (k+1)^T`. -/
theorem bitAlg_isSpanningForest (k T : ℕ) (hT : Fintype.card V < (k + 1) ^ T)
    (G : SimpleGraph V) (v : V) : IsSpanningForest G (out ((bitAlg k).run (nbrs G) T v)) := by
  rw [bitAlg, TAlg.run_toBits]
  exact isSpanningForest_run k T hT G v

end Supernodes

/-- `n ≤ ⌈n^ε⌉₊ ^ ⌈1/ε⌉₊` for `0 < ε`. -/
lemma le_ceil_rpow_pow_ceil (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    n ≤ ⌈(n : ℝ) ^ ε⌉₊ ^ ⌈1 / ε⌉₊ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT : 1 ≤ ε * (⌈1 / ε⌉₊ : ℝ) := by
    have := Nat.le_ceil (1 / ε)
    rw [div_le_iff₀ hε] at this
    linarith
  have key : (n : ℝ) ≤ ((⌈(n : ℝ) ^ ε⌉₊ ^ ⌈1 / ε⌉₊ : ℕ) : ℝ) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ (ε * (⌈1 / ε⌉₊ : ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 hT
      _ = ((n : ℝ) ^ ε) ^ ⌈1 / ε⌉₊ := by rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ (⌈(n : ℝ) ^ ε⌉₊ : ℝ) ^ ⌈1 / ε⌉₊ :=
          pow_le_pow_left₀ (by positivity) (Nat.le_ceil _) _
      _ = _ := by push_cast; rfl
  exact_mod_cast key

/-- Theorem 1 of [Montealegre–Todinca]: for `0 < ε ≤ 1` there is a `⌈1/ε⌉`-round deterministic
protocol in `BClique[n^ε · log n]` (precisely: `⌈n^ε⌉ · ⌈log₂(n+1)⌉`-bit messages) after which
every node outputs a spanning forest of the input graph. -/
theorem theorem_1 (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (σ : Type) (A : Bcast.Algorithm (Fin n) (Finset (Fin n)) σ (⌈(n : ℝ) ^ ε⌉₊ * Nat.clog 2 (n + 1)))
      (out : σ → SimpleGraph (Fin n)),
      ∀ (G : SimpleGraph (Fin n)) (v : Fin n),
        IsSpanningForest G (out (A.run (nbrs G) ⌈1 / ε⌉₊ v)) := by
  have _ := hε1 -- `ε ≤ 1` is not needed
  have hb : Fintype.card (Supernodes.Msg (Fin n) ⌈(n : ℝ) ^ ε⌉₊) ≤
      2 ^ (⌈(n : ℝ) ^ ε⌉₊ * Nat.clog 2 (n + 1)) := by
    simpa using Supernodes.card_msg_le (V := Fin n) ⌈(n : ℝ) ^ ε⌉₊
  refine ⟨Finset (Fin n) × SimpleGraph (Fin n), (Supernodes.alg _).toBits _ hb,
    Supernodes.out, fun G v => ?_⟩
  rw [TAlg.run_toBits]
  refine Supernodes.isSpanningForest_run _ _ ?_ G v
  rw [Fintype.card_fin]
  have hT : ⌈1 / ε⌉₊ ≠ 0 := by
    rw [Ne, Nat.ceil_eq_zero, not_le]; positivity
  exact (le_ceil_rpow_pow_ceil n hε).trans_lt (Nat.pow_lt_pow_left (Nat.lt_succ_self _) hT)

/-- `⌈log₂ m⌉ ≤ log₂ m + 1` for `m ≥ 1`. -/
lemma clog_le_logb_add_one (m : ℕ) (hm : 1 ≤ m) : (Nat.clog 2 m : ℝ) ≤ Real.logb 2 m + 1 := by
  rcases Nat.lt_or_ge 1 m with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 : ((Nat.clog 2 m).pred : ℝ) ≤ Real.logb 2 m := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
      exact_mod_cast h1.le
    have h3 : Nat.clog 2 m ≤ (Nat.clog 2 m).pred + 1 := by rw [Nat.pred_eq_sub_one]; omega
    have h3' : (Nat.clog 2 m : ℝ) ≤ ((Nat.clog 2 m).pred : ℝ) + 1 := by exact_mod_cast h3
    linarith
  · obtain rfl : m = 1 := by omega
    simp

/-- The message size of `theorem_1` is `O(n^ε log n)`:
`⌈n^ε⌉ ⌈log₂(n+1)⌉ ≤ (n^ε + 1)(log₂(n+1) + 1)`. -/
lemma theorem_1_bits_le (n : ℕ) (ε : ℝ) :
    ((⌈(n : ℝ) ^ ε⌉₊ * Nat.clog 2 (n + 1) : ℕ) : ℝ) ≤
      ((n : ℝ) ^ ε + 1) * (Real.logb 2 (n + 1) + 1) := by
  push_cast
  have h1 : (⌈(n : ℝ) ^ ε⌉₊ : ℝ) ≤ (n : ℝ) ^ ε + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 := clog_le_logb_add_one (n + 1) (by omega)
  push_cast at h2
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

end Podc.BCCConnectivitySketches
