import Papers.PODC2025.DynamicSubgraphFinding.Theorem14Alg

/-!
# Correctness of the algorithm of Theorem 1.4

`alg14_solves`: for parameters `T ≥ 1`, `2T ≤ d` and an injective block encoding, `alg14` solves
one-round `MemList(K₃)` under edge insertions on networks of maximum degree `≤ Δ`.

* Basic facts about the true histories: `nb_st`, `nbrsAt_st`, `inbH_st`, `sig_recv`, `mem_rEdge`,
  `mem_rSig`, `blk_recv` (the received blocks of a period decode to the sender's neighbourhood at
  the period start), `card_rEdge` / `card_rSig` (`|R_edge| ≤ Δ`, `|R_signal| ≤ Δ²`).
* Soundness of the five evidence rules (`sound_sig`, `sound_per`, `sound_rsig`, `sound_redge`):
  each uses that a round inserts at most one edge (`new_unique`) and no edge is ever deleted.
* Completeness (`complete`): the case analysis of the paper on the round `t` in which the last
  edge of a triangle appeared (`endpoint`: `z` is an endpoint of the last edge; otherwise `z` is
  the paper's node `w` and receives two `(Signal)`s in round `t`).
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Alg14

variable {V : Type} {Δ d K T : ℕ}

/-! ### First-adjacency times -/

/-- The round in which the edge `{x, z}` appeared (`0` for edges of `G⁰`). -/
noncomputable def tAdj (D : InsNet V) (x z : V) : ℕ := firstP fun k => D.adj k x z

variable (D : InsNet V)

lemma tAdj_comm (x z : V) : tAdj D x z = tAdj D z x := by
  unfold tAdj
  congr 1
  funext k
  exact propext ⟨D.symm _ _ _, D.symm _ _ _⟩

lemma adj_iff_tAdj_le {r : ℕ} {x z : V} (h : D.adj r x z) (j : ℕ) :
    D.adj j x z ↔ tAdj D x z ≤ j := by
  obtain ⟨h1, -, h3⟩ := firstP_spec (P := fun k => D.adj k x z) h
  constructor
  · intro hj
    by_contra hc
    exact h3 j (not_le.1 hc) hj
  · intro hj
    exact D.adj_le hj h1

lemma tAdj_le {r : ℕ} {x z : V} (h : D.adj r x z) : tAdj D x z ≤ r :=
  (adj_iff_tAdj_le D h r).1 h

/-- At most one edge is inserted per round. -/
lemma new_unique (hE : D.EdgeIns) {k : ℕ} {a b a' b' : V} (h1 : D.adj (k + 1) a b)
    (h1' : ¬ D.adj k a b) (h2 : D.adj (k + 1) a' b') (h2' : ¬ D.adj k a' b') :
    s(a, b) = s(a', b') :=
  (hE k).2 a b a' b' ⟨h1, h1'⟩ ⟨h2, h2'⟩

/-- An edge is new in only one round. -/
lemma new_round_unique {j j' : ℕ} {u v : V} (h1 : D.adj (j + 1) u v) (h1' : ¬ D.adj j u v)
    (h2 : D.adj (j' + 1) u v) (h2' : ¬ D.adj j' u v) : j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd (D.adj_le h h1) h2'
  · exact h
  · exact absurd (D.adj_le h h2) h1'

/-- Two edges that appeared in the same round `≥ 1` are equal. -/
lemma tAdj_inj (hE : D.EdgeIns) {r : ℕ} {a b a' b' : V} (h : D.adj r a b) (h' : D.adj r a' b')
    (h1 : 1 ≤ tAdj D a b) (he : tAdj D a b = tAdj D a' b') : s(a, b) = s(a', b') := by
  obtain ⟨k, hk⟩ : ∃ k, tAdj D a b = k + 1 := ⟨tAdj D a b - 1, by omega⟩
  refine new_unique D hE (k := k) ((adj_iff_tAdj_le D h _).2 hk.le)
    (fun hc => by have := (adj_iff_tAdj_le D h _).1 hc; omega)
    ((adj_iff_tAdj_le D h' _).2 (by omega))
    (fun hc => by have := (adj_iff_tAdj_le D h' _).1 hc; omega)

/-! ### The true histories -/

lemma setOf_loc (k : ℕ) (v : V) : setOf (D.loc k v) = {w | D.adj k w v} := by
  unfold InsNet.loc
  split_ifs with hp
  · rfl
  · ext w
    simp only [setOf, Set.mem_empty_iff_false, false_iff]
    exact fun h => hp (D.pres_of_adj _ _ _ (D.symm _ _ _ h))

variable [Fintype V] (hT : 0 < T) (enc : (Fin Δ → Option V) → Fin T → Fin K)

set_option quotPrecheck false in
local notation "st" => (alg14 (d := d) hT enc).state D

lemma st_r (r : ℕ) (v : V) : (st r v).r = r := histAlg_r _ _ D r v

lemma st_id (r : ℕ) (v : V) : (st r v).id = v := histAlg_id _ _ D r v

lemma st_g0a (r : ℕ) (v : V) : (st r v).g0a = D.adj 0 := by
  unfold alg14
  rw [histAlg_state]

lemma nb_st {r k : ℕ} (hk : k ≤ r) (v : V) : nb (st r v) k = {w | D.adj k w v} := by
  unfold nb alg14
  rw [histAlg_locH _ _ D hk, setOf_loc]

lemma nbrsAt_st {r k : ℕ} (hk : k ≤ r + 1) (v : V) :
    nbrsAt (st r v) (D.loc (r + 1) v) k = {w | D.adj k w v} := by
  unfold nbrsAt
  rw [st_r]
  split_ifs with h
  · subst h
    exact setOf_loc D _ _
  · unfold alg14
    rw [histAlg_locH _ _ D (by omega), setOf_loc]

lemma gotNew_st {r k : ℕ} (hk : k ≤ r + 1) (v : V) :
    GotNew (st r v) (D.loc (r + 1) v) k ↔ 1 ≤ k ∧ ∃ w, D.adj k w v ∧ ¬ D.adj (k - 1) w v := by
  unfold GotNew
  rw [nbrsAt_st D hT enc hk, nbrsAt_st D hT enc (by omega)]
  rfl

lemma inbH_st {r k : ℕ} (hk : k + 1 ≤ r) (z x : V) :
    (st r z).inbH (k + 1) x =
      if D.adj (k + 1) x z then some (snd hT enc (k + 1) (st k x) (D.loc (k + 1) x) z) else none := by
  have h1 := congrFun (histAlg_inbH (snd (d := d) hT enc) (out enc) D (r := r) (k := k + 1)
    (by omega) hk z) x
  simp only [Nat.add_sub_cancel] at h1
  exact h1.trans (histAlg_inbox _ _ D k z x)

lemma snd_sig (k : ℕ) (x z : V) :
    (snd hT enc (k + 1) (st k x) (D.loc (k + 1) x) z).1 = true ↔
      ∃ w, D.adj (k + 1) w x ∧ ¬ D.adj k w x := by
  simp only [snd, decide_eq_true_iff]
  rw [gotNew_st D hT enc le_rfl]
  simp

/-- `z` received a `(Signal)` from `w` in round `j` iff `w` is a neighbour of `z` that obtained a
new edge in round `j`. -/
lemma sig_recv {r j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ r) (z w : V) :
    (∃ m, (st r z).inbH j w = some (true, m)) ↔
      D.adj j w z ∧ ∃ w', D.adj j w' w ∧ ¬ D.adj (j - 1) w' w := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [inbH_st D hT enc hj]
  simp only [Nat.add_sub_cancel]
  split_ifs with h
  · simp only [Option.some.injEq, h, true_and]
    rw [← snd_sig D hT enc k w z]
    constructor
    · rintro ⟨m, hm⟩
      rw [hm]
    · intro hs
      exact ⟨_, Prod.ext hs rfl⟩
  · simp [h]

lemma snd_rec_eq {k : ℕ} {x z : V} {p : RList Δ d × RList (Δ ^ 2) d}
    (h : (snd hT enc (k + 1) (st k x) (D.loc (k + 1) x) z).2.1 = some p) :
    p = (listEnc Δ (rEdge d (k + 1) (st k x) (D.loc (k + 1) x)),
      listEnc (Δ ^ 2) (rSig (k + 1) (st k x))) := by
  simp only [snd] at h
  split_ifs at h
  exact (Option.some.inj h).symm

lemma snd_rec_new {k : ℕ} {x z : V} (h1 : D.adj (k + 1) z x) (h2 : ¬ D.adj k z x) :
    (snd hT enc (k + 1) (st k x) (D.loc (k + 1) x) z).2.1 =
      some (listEnc Δ (rEdge d (k + 1) (st k x) (D.loc (k + 1) x)),
        listEnc (Δ ^ 2) (rSig (k + 1) (st k x))) := by
  simp only [snd]
  refine ite_eq_left ?_
  rw [nbrsAt_st D hT enc le_rfl, nbrsAt_st D hT enc (by omega)]
  exact ⟨h1, by simpa using h2⟩

lemma mem_rEdge {k : ℕ} {x : V} (a : Fin (d + 1)) :
    a ∈ rEdge d (k + 1) (st k x) (D.loc (k + 1) x) ↔
      1 ≤ a.val ∧ a.val ≤ k ∧ ∃ w, D.adj (k + 1 - a.val) w x ∧ ¬ D.adj (k - a.val) w x := by
  simp only [rEdge, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [gotNew_st D hT enc (by omega)] at h3
    obtain ⟨-, w, hw1, hw2⟩ := h3
    exact ⟨h1, by omega, w, hw1, by rwa [show k + 1 - a.val - 1 = k - a.val by omega] at hw2⟩
  · rintro ⟨h1, h2, w, hw1, hw2⟩
    refine ⟨h1, by omega, ?_⟩
    rw [gotNew_st D hT enc (by omega)]
    exact ⟨by omega, w, hw1, by rwa [show k + 1 - a.val - 1 = k - a.val by omega]⟩

lemma mem_rSig {k : ℕ} {x : V} (a : Fin (d + 1)) :
    a ∈ rSig (k + 1) (st k x) ↔
      1 ≤ a.val ∧ a.val ≤ k ∧ ∃ w, D.adj (k + 1 - a.val) w x ∧
        ∃ w', D.adj (k + 1 - a.val) w' w ∧ ¬ D.adj (k - a.val) w' w := by
  simp only [rSig, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2, w, hw⟩
    rw [sig_recv D hT enc (by omega) (by omega)] at hw
    rw [show k + 1 - a.val - 1 = k - a.val by omega] at hw
    exact ⟨h1, by omega, w, hw⟩
  · rintro ⟨h1, h2, w, hw⟩
    refine ⟨h1, by omega, w, ?_⟩
    rw [sig_recv D hT enc (by omega) (by omega), show k + 1 - a.val - 1 = k - a.val by omega]
    exact hw

lemma start_nbrsAt {k : ℕ} {x z : V} (h : D.adj (k + 1) z x) :
    start (nbrsAt (st k x) (D.loc (k + 1) x)) z = max 1 (tAdj D z x) := by
  unfold start tAdj
  congr 1
  refine firstP_congr (m := k + 1) (fun j hj => ?_) (by rw [nbrsAt_st D hT enc le_rfl]; exact h)
  rw [nbrsAt_st D hT enc hj]
  rfl

lemma start_nb {r : ℕ} {x z : V} (h : D.adj r x z) :
    start (nb (st r z)) x = max 1 (tAdj D x z) := by
  unfold start tAdj
  congr 1
  refine firstP_congr (m := r) (fun j hj => ?_) (by rw [nb_st D hT enc le_rfl]; exact h)
  rw [nb_st D hT enc hj]
  rfl

/-- The block sent along `{x, z}` in round `s₀ + k'T + i`. -/
lemma snd_blk {x z : V} {k' m : ℕ} (i : Fin T)
    (hm : m + 1 = max 1 (tAdj D z x) + k' * T + i) (h : D.adj (m + 1) z x) :
    (snd hT enc (m + 1) (st m x) (D.loc (m + 1) x) z).2.2 =
      enc (listEnc Δ (toFs {w | D.adj (max 1 (tAdj D z x) + k' * T) w x})) i := by
  simp only [snd]
  have hs := start_nbrsAt (d := d) D hT enc h
  have hmod : (m + 1 - max 1 (tAdj D z x)) % T = i := by
    rw [show m + 1 - max 1 (tAdj D z x) = i + k' * T by omega, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt i.isLt]
  congr 1
  · rw [hs, hmod, nbrsAt_st D hT enc (by omega),
      show m + 1 - (i : ℕ) = max 1 (tAdj D z x) + k' * T by omega]
  · ext
    simp only
    rw [hs, hmod]

/-- The blocks received from `x` during a period decode to `x`'s neighbourhood at the start of
the period. -/
lemma blk_recv {r : ℕ} {x z : V} (hx : D.adj r x z) (k : ℕ) (i : Fin T)
    (hr : max 1 (tAdj D x z) + k * T + i ≤ r) :
    ((st r z).inbH (max 1 (tAdj D x z) + k * T + i) x).map (fun m => m.2.2) =
      some (enc (listEnc Δ (toFs {w | D.adj (max 1 (tAdj D x z) + k * T) w x})) i) := by
  obtain ⟨m, hm⟩ : ∃ m, max 1 (tAdj D x z) + k * T + i = m + 1 :=
    ⟨max 1 (tAdj D x z) + k * T + i - 1, by omega⟩
  have hadj : D.adj (m + 1) x z := (adj_iff_tAdj_le D hx _).2 (by omega)
  rw [hm, inbH_st D hT enc (by omega), ite_eq_left hadj, Option.map_some,
    snd_blk D hT enc i (k' := k) (by rw [tAdj_comm]; omega) (D.symm _ _ _ hadj), tAdj_comm]

/-! ### Sizes of the recent records -/

lemma card_rEdge (hΔ : D.DegLE Δ) (k : ℕ) (x : V) :
    (rEdge d (k + 1) (st k x) (D.loc (k + 1) x)).card ≤ Δ := by
  calc _ ≤ (toFs {w | D.adj k w x}).card := by
        refine Finset.card_le_card_of_forall_subsingleton
          (fun (a : Fin (d + 1)) w => D.adj (k + 1 - a.val) w x ∧ ¬ D.adj (k - a.val) w x)
          (fun a ha => ?_) (fun w _ => ?_)
        · obtain ⟨h1, h2, w, hw1, hw2⟩ := (mem_rEdge D hT enc a).1 ha
          exact ⟨w, mem_toFs.2 (D.adj_le (by omega) hw1), hw1, hw2⟩
        · rintro a ⟨ha, h1, h2⟩ a' ⟨ha', h1', h2'⟩
          obtain ⟨b1, b2, -⟩ := (mem_rEdge D hT enc a).1 ha
          obtain ⟨b1', b2', -⟩ := (mem_rEdge D hT enc a').1 ha'
          rw [show k + 1 - a.val = k - a.val + 1 by omega] at h1
          rw [show k + 1 - a'.val = k - a'.val + 1 by omega] at h1'
          have := new_round_unique D h1 h2 h1' h2'
          exact Fin.ext (by omega)
    _ = _ := card_toFs _
    _ ≤ Δ := hΔ k x

lemma card_rSig (hΔ : D.DegLE Δ) (k : ℕ) (x : V) :
    (rSig (k + 1) (st k x)).card ≤ Δ ^ 2 := by
  calc _ ≤ ((toFs {w | D.adj k w x}).biUnion
          fun w => (toFs {w' | D.adj k w' w}).image fun w' => (w, w')).card := by
        refine Finset.card_le_card_of_forall_subsingleton
          (fun (a : Fin (d + 1)) (p : V × V) => D.adj (k + 1 - a.val) p.1 x ∧
            D.adj (k + 1 - a.val) p.2 p.1 ∧ ¬ D.adj (k - a.val) p.2 p.1)
          (fun a ha => ?_) (fun p _ => ?_)
        · obtain ⟨h1, h2, w, hw, w', hw1, hw2⟩ := (mem_rSig D hT enc a).1 ha
          refine ⟨(w, w'), ?_, hw, hw1, hw2⟩
          simp only [Finset.mem_biUnion, Finset.mem_image]
          exact ⟨w, mem_toFs.2 (D.adj_le (by omega) hw), w',
            mem_toFs.2 (D.adj_le (by omega) hw1), rfl⟩
        · rintro a ⟨ha, -, h1, h2⟩ a' ⟨ha', -, h1', h2'⟩
          obtain ⟨b1, b2, -⟩ := (mem_rSig D hT enc a).1 ha
          obtain ⟨b1', b2', -⟩ := (mem_rSig D hT enc a').1 ha'
          rw [show k + 1 - a.val = k - a.val + 1 by omega] at h1
          rw [show k + 1 - a'.val = k - a'.val + 1 by omega] at h1'
          have := new_round_unique D h1 h2 h1' h2'
          exact Fin.ext (by omega)
    _ ≤ ∑ w ∈ toFs {w | D.adj k w x}, ((toFs {w' | D.adj k w' w}).image fun w' => (w, w')).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ toFs {w | D.adj k w x}, Δ :=
        Finset.sum_le_sum fun w _ => Finset.card_image_le.trans ((card_toFs _).trans_le (hΔ k w))
    _ = (toFs {w | D.adj k w x}).card * Δ := by simp
    _ ≤ Δ * Δ := Nat.mul_le_mul_right _ ((card_toFs _).trans_le (hΔ k x))
    _ = Δ ^ 2 := (sq Δ).symm

/-! ### Soundness of the evidence rules -/

lemma sound_g0 {r : ℕ} {z x y : V} (h : EvG0 (st r z) x y) : D.adj r x y := by
  unfold EvG0 at h
  rw [st_g0a D hT enc] at h
  exact D.adj_le (Nat.zero_le r) h

/-- Rule (b) (node `w`): two distinct neighbours signalling in the same round are the endpoints
of the edge inserted in that round. -/
lemma sound_sig (hE : D.EdgeIns) {r : ℕ} {z x y : V} (hxy : x ≠ y) (h : EvSig (st r z) x y) :
    D.adj r x y := by
  obtain ⟨k, hk1, hkr, hx, hy⟩ := h
  rw [st_r D hT enc] at hkr
  obtain ⟨-, w, hw1, hw2⟩ := (sig_recv D hT enc hk1 hkr z x).1 hx
  obtain ⟨-, w', hw1', hw2'⟩ := (sig_recv D hT enc hk1 hkr z y).1 hy
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hw2 hw2'
  have := new_unique D hE hw1 hw2 hw1' hw2'
  rw [Sym2.eq_iff] at this
  rcases this with ⟨-, h⟩ | ⟨rfl, -⟩
  · exact absurd h hxy
  · exact D.adj_le hkr (D.symm _ _ _ hw1)

/-- Rule (c) (periodic updates). -/
lemma sound_per (henc : Function.Injective enc) {r : ℕ} {z x y : V} (hx : D.adj r x z)
    (h : EvPer enc (st r z) x y) : D.adj r x y := by
  obtain ⟨k, L, hkr, hblk, i, hi⟩ := h
  rw [st_r D hT enc, start_nb D hT enc hx] at hkr
  rw [start_nb D hT enc hx] at hblk
  have hL : L = listEnc Δ (toFs {w | D.adj (max 1 (tAdj D x z) + k * T) w x}) := by
    apply henc
    funext j
    have := j.isLt
    exact Option.some.inj ((hblk j).symm.trans (blk_recv D hT enc hx k j (by omega)))
  rw [hL] at hi
  have := mem_toFs.1 (listEnc_sound hi)
  exact D.adj_le (by omega) (D.symm _ _ _ this)

/-- Rule (d) (node `u`). -/
lemma sound_rsig (hE : D.EdgeIns) {r : ℕ} {z x y : V} (h : EvRSig (st r z) x y) :
    D.adj r x y := by
  obtain ⟨t, a, RE, RS, b, c, ht1, htr, hxt, hxt', hmsg, ⟨i, hi⟩, ha1, hat, hyt, hyt'⟩ := h
  rw [st_r D hT enc] at htr
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [nb_st D hT enc htr] at hxt
  rw [nb_st D hT enc (by omega)] at hxt' hyt hyt'
  simp only [Nat.add_sub_cancel, Set.mem_ofPred_eq] at hxt hxt' hyt hyt'
  rw [inbH_st D hT enc htr, ite_eq_left hxt] at hmsg
  have hrec := congrArg (fun m => m.2.1) (Option.some.inj hmsg)
  simp only at hrec
  have hRS : RS = listEnc (Δ ^ 2) (rSig (t + 1) (st t x)) :=
    congrArg Prod.snd (snd_rec_eq D hT enc hrec)
  rw [hRS] at hi
  obtain ⟨-, -, w, hw, w', hw1, hw2⟩ := (mem_rSig D hT enc a).1 (listEnc_sound hi)
  rw [show t + 1 - a.val = t - a.val + 1 by omega] at hw hw1 hyt
  rw [show t + 1 - a.val - 1 = t - a.val by omega] at hyt'
  have := new_unique D hE hw1 hw2 hyt hyt'
  rw [Sym2.eq_iff] at this
  rcases this with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact absurd (D.adj_le (by omega) (D.symm _ _ _ hw)) hxt'
  · exact D.adj_le (by omega) (D.symm _ _ _ hw)

/-- Rule (e) (node `v`). -/
lemma sound_redge (hE : D.EdgeIns) {r : ℕ} {z x y : V} (h : EvREdge (st r z) x y) :
    D.adj r x y := by
  obtain ⟨t, a, RE, RS, b, c, ht1, htr, hxt, hxt', hmsg, ⟨i, hi⟩, ha1, hat, hyx, hsig⟩ := h
  rw [st_r D hT enc] at htr
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [nb_st D hT enc htr] at hxt
  simp only [Set.mem_ofPred_eq] at hxt
  rw [inbH_st D hT enc htr, ite_eq_left hxt] at hmsg
  have hrec := congrArg (fun m => m.2.1) (Option.some.inj hmsg)
  simp only at hrec
  have hRE : RE = listEnc Δ (rEdge d (t + 1) (st t x) (D.loc (t + 1) x)) :=
    congrArg Prod.fst (snd_rec_eq D hT enc hrec)
  rw [hRE] at hi
  obtain ⟨-, -, w, hw1, hw2⟩ := (mem_rEdge D hT enc a).1 (listEnc_sound hi)
  obtain ⟨-, w', hw1', hw2'⟩ := (sig_recv D hT enc (by omega) (by omega) z y).1 hsig
  rw [show t + 1 - a.val = t - a.val + 1 by omega] at hw1 hw1'
  rw [show t + 1 - a.val - 1 = t - a.val by omega] at hw2'
  have := new_unique D hE hw1 hw2 hw1' hw2'
  rw [Sym2.eq_iff] at this
  rcases this with ⟨-, h⟩ | ⟨rfl, -⟩
  · exact absurd h.symm hyx
  · exact D.adj_le (by omega) (D.symm _ _ _ hw1)

lemma sound (hE : D.EdgeIns) (henc : Function.Injective enc) {r : ℕ} {z x y : V}
    (hx : D.adj r x z) (hxy : x ≠ y) (h : Ev enc (st r z) x y) : D.adj r x y := by
  rcases h with h | h | h | h | h
  · exact sound_g0 D hT enc h
  · exact sound_sig D hT enc hE hxy h
  · exact sound_per D hT enc henc hx h
  · exact sound_rsig D hT enc hE h
  · exact sound_redge D hT enc hE h

/-! ### Completeness -/

/-- The case where `z` is an endpoint of the last edge `{z, x}` of the triangle `{z, x, y}`
(inserted in round `t₁ = tAdj D x z ≥ 1`); the paper's nodes `u` (`t_xy ≤ t_zy`) and `v`
(`t_zy ≤ t_xy`). With `m = max t_zy t_xy`: if `m = 0` the edge `{x, y}` is in `G⁰`; if
`t₁ - m ≤ d` the recent records sent by `x` in round `t₁` show the edge (rule (d) or (e));
otherwise a complete period of updates `y → z` starting in `[m, m + T - 1]` lists `x`. -/
lemma endpoint (hE : D.EdgeIns) (hΔ : D.DegLE Δ) (hTd : 2 * T ≤ d) {r : ℕ} {z x y : V}
    (hxz : D.adj r x z) (hyz : D.adj r y z) (hxy : D.adj r x y)
    (h1 : 1 ≤ tAdj D x z) (h2 : tAdj D y z ≤ tAdj D x z) (h3 : tAdj D x y < tAdj D x z) :
    Ev enc (st r z) x y ∨ Ev enc (st r z) y x := by
  have hne_xy : x ≠ y := fun h => D.irrefl r x (h ▸ hxy)
  have hne_xz : x ≠ z := fun h => D.irrefl r x (h ▸ hxz)
  have fxz := adj_iff_tAdj_le D hxz
  have fyz := adj_iff_tAdj_le D hyz
  have fxy := adj_iff_tAdj_le D hxy
  have h1r : tAdj D x z ≤ r := tAdj_le D hxz
  have h2' : tAdj D y z < tAdj D x z := by
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exfalso
      have := tAdj_inj D hE hxz hyz h1 h.symm
      rw [Sym2.eq_iff] at this
      rcases this with ⟨h, -⟩ | ⟨h, -⟩
      · exact hne_xy h
      · exact hne_xz h
  obtain ⟨t, ht⟩ : ∃ t, tAdj D x z = t + 1 := ⟨tAdj D x z - 1, by omega⟩
  by_cases hm0 : tAdj D y z = 0 ∧ tAdj D x y = 0
  · -- (a): `{x, y} ∈ G⁰`
    left; left
    show (st r z).g0a x y
    rw [st_g0a D hT enc]
    exact (fxy 0).2 (by omega)
  -- the recent records sent by `x` to its new neighbour `z` in round `t + 1`
  have hxz1 : D.adj (t + 1) x z := (fxz _).2 (by omega)
  have hrec := snd_rec_new (d := d) D hT enc (k := t) (D.symm _ _ _ hxz1)
    (fun hc => by have := (fxz t).1 (D.symm _ _ _ hc); omega)
  have hmsg : (st r z).inbH (t + 1) x = some ((snd hT enc (t + 1) (st t x) (D.loc (t + 1) x) z).1,
      some (listEnc Δ (rEdge d (t + 1) (st t x) (D.loc (t + 1) x)),
        listEnc (Δ ^ 2) (rSig (t + 1) (st t x))),
      (snd hT enc (t + 1) (st t x) (D.loc (t + 1) x) z).2.2) := by
    rw [inbH_st D hT enc (by omega), ite_eq_left hxz1]
    exact congrArg some (Prod.ext rfl (Prod.ext hrec rfl))
  have hxnb : x ∈ nb (st r z) (t + 1) := by
    rw [nb_st D hT enc (by omega)]
    exact hxz1
  have hxnb' : x ∉ nb (st r z) (t + 1 - 1) := by
    rw [nb_st D hT enc (by omega)]
    intro hc
    have := (fxz _).1 hc
    omega
  by_cases hmd : t + 1 - max (tAdj D y z) (tAdj D x y) ≤ d
  · left
    by_cases h23 : tAdj D x y ≤ tAdj D y z
    · -- (d): rule for node `u`; `a = t₁ - t_zy`
      right; right; right; left
      refine ⟨t + 1, ⟨t + 1 - tAdj D y z, by omega⟩, _, _, _, _, by omega,
        by rw [st_r D hT enc]; omega, hxnb, hxnb', hmsg,
        listEnc_complete (card_rSig D hT enc hΔ t x) ((mem_rSig D hT enc _).2 ⟨?_, ?_, y, ?_, z,
          ?_, ?_⟩), ?_, ?_, ?_, ?_⟩ <;> dsimp only
      · omega
      · omega
      · rw [show t + 1 - (t + 1 - tAdj D y z) = tAdj D y z by omega]
        exact D.symm _ _ _ ((fxy _).2 h23)
      · rw [show t + 1 - (t + 1 - tAdj D y z) = tAdj D y z by omega]
        exact D.symm _ _ _ ((fyz _).2 le_rfl)
      · intro hc
        have := (fyz _).1 (D.symm _ _ _ hc)
        omega
      · omega
      · omega
      · rw [nb_st D hT enc (by omega), show t + 1 - (t + 1 - tAdj D y z) = tAdj D y z by omega]
        exact (fyz _).2 le_rfl
      · rw [nb_st D hT enc (by omega)]
        intro hc
        have := (fyz _).1 hc
        omega
    · -- (e): rule for node `v`; `a = t₁ - t_xy`
      right; right; right; right
      refine ⟨t + 1, ⟨t + 1 - tAdj D x y, by omega⟩, _, _, _, _, by omega,
        by rw [st_r D hT enc]; omega, hxnb, hxnb', hmsg,
        listEnc_complete (card_rEdge D hT enc hΔ t x) ((mem_rEdge D hT enc _).2 ⟨?_, ?_, y, ?_,
          ?_⟩), ?_, ?_, hne_xy.symm, ?_⟩ <;> dsimp only
      · omega
      · omega
      · rw [show t + 1 - (t + 1 - tAdj D x y) = tAdj D x y by omega]
        exact D.symm _ _ _ ((fxy _).2 le_rfl)
      · intro hc
        have := (fxy _).1 (D.symm _ _ _ hc)
        omega
      · omega
      · omega
      · rw [show t + 1 - (t + 1 - tAdj D x y) = tAdj D x y by omega]
        refine (sig_recv D hT enc (by omega) (by omega) z y).2 ⟨(fyz _).2 (by omega), x,
          (fxy _).2 le_rfl, fun hc => ?_⟩
        have := (fxy _).1 hc
        omega
  · -- (c): periodic updates `y → z`
    right; right; right; left
    have hs := start_nb (d := d) D hT enc hyz
    set m := max (tAdj D y z) (tAdj D x y) with hm
    set q := (m - max 1 (tAdj D y z) + T - 1) / T with hq
    have hq1 := Nat.div_add_mod (m - max 1 (tAdj D y z) + T - 1) T
    have hq2 := Nat.mod_lt (m - max 1 (tAdj D y z) + T - 1) hT
    rw [← hq, Nat.mul_comm] at hq1
    refine ⟨q, listEnc Δ (toFs {w | D.adj (max 1 (tAdj D y z) + q * T) w y}), ?_, ?_, ?_⟩
    · rw [hs, st_r D hT enc]
      omega
    · rw [hs]
      intro i
      have := i.isLt
      exact blk_recv D hT enc hyz q i (by omega)
    · refine listEnc_complete ((card_toFs _).trans_le (hΔ _ y)) (mem_toFs.2 ?_)
      exact (fxy _).2 (by omega)

/-- **Completeness**: every node of a triangle has evidence for the opposite edge. -/
lemma complete (hE : D.EdgeIns) (hΔ : D.DegLE Δ) (hTd : 2 * T ≤ d) {r : ℕ} {z x y : V}
    (hxz : D.adj r x z) (hyz : D.adj r y z) (hxy : D.adj r x y) :
    Ev enc (st r z) x y ∨ Ev enc (st r z) y x := by
  have fxz := adj_iff_tAdj_le D hxz
  have fyz := adj_iff_tAdj_le D hyz
  have fxy := adj_iff_tAdj_le D hxy
  by_cases h3 : tAdj D x z ≤ tAdj D x y ∧ tAdj D y z ≤ tAdj D x y
  · left
    by_cases h0 : tAdj D x y = 0
    · -- (a)
      left
      show (st r z).g0a x y
      rw [st_g0a D hT enc]
      exact (fxy 0).2 (by omega)
    · -- (b): the last edge is `{x, y}`; `z` is the paper's node `w`
      right; left
      have h3r := tAdj_le D hxy
      refine ⟨tAdj D x y, by omega, by rw [st_r D hT enc]; exact h3r, ?_, ?_⟩
      · refine (sig_recv D hT enc (by omega) h3r z x).2 ⟨(fxz _).2 h3.1, y,
          D.symm _ _ _ ((fxy _).2 le_rfl), fun hc => ?_⟩
        have := (fxy _).1 (D.symm _ _ _ hc)
        omega
      · refine (sig_recv D hT enc (by omega) h3r z y).2 ⟨(fyz _).2 h3.2, x,
          (fxy _).2 le_rfl, fun hc => ?_⟩
        have := (fxy _).1 hc
        omega
  · by_cases h12 : tAdj D y z ≤ tAdj D x z
    · exact endpoint D hT enc hE hΔ hTd hxz hyz hxy (by omega) h12 (by omega)
    · have h := tAdj_comm D y x
      exact (endpoint D hT enc hE hΔ hTd hyz hxz (D.symm _ _ _ hxy) (by omega) (by omega)
        (by omega)).symm

end Alg14

/-! ### The algorithm solves `MemList(K₃)` -/

open Alg14 in
/-- For `T ≥ 1`, `2T ≤ d` and an injective block encoding `enc`, the algorithm `alg14` solves
one-round `MemList(K₃)` under edge insertions on networks of maximum degree `≤ Δ`. -/
theorem alg14_solves {V : Type} [Fintype V] {Δ d K T : ℕ} (hT : 0 < T) (hTd : 2 * T ≤ d)
    (enc : (Fin Δ → Option V) → Fin T → Fin K) (henc : Function.Injective enc) :
    Solves (alg14 (d := d) hT enc) InsNet.EdgeIns Δ MemListOK := by
  intro D hE hΔ r z _ Q
  constructor
  · rintro ⟨x, y, hxy, hx, hy, hev, rfl⟩
    rw [st_r D hT enc, nb_st D hT enc le_rfl] at hx hy
    have hx' : D.adj r x z := hx
    have hy' : D.adj r y z := hy
    have hxy' : D.adj r x y := by
      rcases hev with h | h
      · exact sound D hT enc hE henc hx' hxy h
      · exact D.symm _ _ _ (sound D hT enc hE henc hy' (Ne.symm hxy) h)
    rw [st_id D hT enc]
    exact ⟨SimpleGraph.is3Clique_triple_iff.2 ⟨D.symm _ _ _ hx', D.symm _ _ _ hy', hxy'⟩,
      by simp⟩
  · rintro ⟨hQ, hzQ⟩
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := SimpleGraph.is3Clique_iff.1 hQ
    obtain ⟨x, y, hQe, hxz, hyz, hxy⟩ : ∃ x y, ({a, b, c} : Finset V) = {z, x, y} ∧
        D.adj r x z ∧ D.adj r y z ∧ D.adj r x y := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzQ
      rcases hzQ with rfl | rfl | rfl
      · exact ⟨b, c, rfl, D.symm _ _ _ hab, D.symm _ _ _ hac, hbc⟩
      · exact ⟨a, c, Finset.insert_comm _ _ _, hab, D.symm _ _ _ hbc, hac⟩
      · exact ⟨a, b, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto,
          hac, hbc, hab⟩
    rw [hQe]
    refine ⟨x, y, fun h => D.irrefl r x (h ▸ hxy), ?_, ?_,
      complete D hT enc hE hΔ hTd hxz hyz hxy, by rw [st_id D hT enc]⟩
    · rw [st_r D hT enc, nb_st D hT enc le_rfl]
      exact hxz
    · rw [st_r D hT enc, nb_st D hT enc le_rfl]
      exact hyz

end Podc.DynamicSubgraphFinding
