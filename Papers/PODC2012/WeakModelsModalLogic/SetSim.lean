import Papers.PODC2012.WeakModelsModalLogic.Bisimulation

/-!
# `MV = SV`: Theorem 4, Lemmas 5 and 6, Corollary 7 (§5.1 of Hella et al.)

The local algorithm `C_Δ ∈ Set` of the paper computes, for `t = 0, 1, …`,
`β_t(v) = (β_{t-1}(v), B_{t-1}(v))`, where `B_t(v)` is the set of messages
`m_t(u, v) = (β_t(u), deg u, π(u, v))` received by `v` in round `t` (`β_0 = ∅`, `B_0 = ∅`).
We define these values mathematically on `(G, p)` (`beta`, `Bset`), encoding the pair
`(β_{t-1}(v), B_{t-1}(v))` injectively into `ℕ`; only equalities of `β`-values matter.

* `lemma5`: Lemma 5 (indistinguishable neighbours of order `k` in round `t ≥ 4` are
  indistinguishable neighbours of order `k + 1` in round `t - 2`; we prove it for `t ≥ 3`);
* `lemma6`, `lemma6_consequence`: Lemma 6;
* `theorem4`: Theorem 4 (a `Multiset` algorithm with running time `T` is simulated by a `Set`
  algorithm with running time `T + 2Δ + 1`);
* `cor7`: Corollary 7 (`MV = SV`, `MV(1) = SV(1)`).
-/

namespace Podc.WeakModelsModalLogic

open Function Finset

variable {V : Type*} {G : SimpleGraph V} (P : PortNumbering G)

namespace PortNumbering

/-- The set of messages `(b(u), deg u, π(u, v))` received by `v` from its neighbours `u`, for a
labelling `b` of the nodes. -/
noncomputable def msgSet (b : V → ℕ) (v : V) : Finset (ℕ × ℕ × ℕ) :=
  univ.image fun i : Fin (deg G v) =>
    (b (P.inNbr v i), deg G (P.inNbr v i), P.outPort (P.inNbr v i) v)

/-- `β_t(v)` of algorithm `C_Δ`, encoded as a natural number:
`β_0 = ∅`, `β_{t+1} = (β_t, B_t)` with `B_0 = ∅` and `B_t = {m_t(u, v)}` for `t ≥ 1`. -/
noncomputable def beta : ℕ → V → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun v =>
    Encodable.encode (beta t v, if t = 0 then (∅ : Finset (ℕ × ℕ × ℕ)) else P.msgSet (beta t) v)

/-- `B_t(v)`: the set of messages received by `v` in round `t` of `C_Δ` (`B_0 = ∅`). -/
noncomputable def Bset (t : ℕ) (v : V) : Finset (ℕ × ℕ × ℕ) :=
  if t = 0 then ∅ else P.msgSet (P.beta t) v

/-- `m_t(u, v) = (β_t(u), deg u, π(u, v))`. -/
noncomputable def msg (t : ℕ) (u v : V) : ℕ × ℕ × ℕ := (P.beta t u, deg G u, P.outPort u v)

theorem beta_succ (t : ℕ) (v : V) :
    P.beta (t + 1) v = Encodable.encode (P.beta t v, P.Bset t v) := rfl

theorem beta_succ_eq_iff (t : ℕ) (u v : V) :
    P.beta (t + 1) u = P.beta (t + 1) v ↔ P.beta t u = P.beta t v ∧ P.Bset t u = P.Bset t v := by
  rw [beta_succ, beta_succ, Encodable.encode_injective.eq_iff, Prod.mk.injEq]

theorem beta_eq_of_succ {t : ℕ} {u v : V} (h : P.beta (t + 1) u = P.beta (t + 1) v) :
    P.beta t u = P.beta t v := ((P.beta_succ_eq_iff t u v).1 h).1

theorem beta_eq_of_le {s t : ℕ} (hst : s ≤ t) {u v : V} (h : P.beta t u = P.beta t v) :
    P.beta s u = P.beta s v := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t _ ih => exact ih (P.beta_eq_of_succ h)

theorem Bset_eq_of_beta {t : ℕ} {u v : V} (h : P.beta (t + 1) u = P.beta (t + 1) v) :
    P.Bset t u = P.Bset t v := ((P.beta_succ_eq_iff t u v).1 h).2

theorem msg_mem_Bset {t : ℕ} (ht : t ≠ 0) {u v : V} (h : G.Adj v u) : P.msg t u v ∈ P.Bset t v := by
  obtain ⟨i, rfl⟩ := P.inNbr_surj v u h
  simp only [Bset, ht, ite_false, msgSet, mem_image, mem_univ, true_and]
  exact ⟨i, rfl⟩

theorem mem_Bset {t : ℕ} {v : V} {m : ℕ × ℕ × ℕ} (h : m ∈ P.Bset t v) :
    ∃ u, G.Adj v u ∧ P.msg t u v = m := by
  by_cases ht : t = 0
  · simp [Bset, ht] at h
  · simp only [Bset, ht, ite_false, msgSet, mem_image, mem_univ, true_and] at h
    obtain ⟨i, rfl⟩ := h
    exact ⟨_, P.adj_inNbr v i, rfl⟩

/-- `π(v, ·)` is injective on the neighbours of `v`. -/
theorem outPort_inj {v x y : V} (hx : G.Adj v x) (hy : G.Adj v y)
    (h : P.outPort v x = P.outPort v y) : x = y := by
  have e1 := P.outNbr_outPort hx
  have e2 := P.outNbr_outPort hy
  rw [← e1, ← e2]
  congr 1
  exact Fin.ext h

/-- Distinct messages to `v` come from distinct senders; equal messages from one sender to
different receivers are impossible. -/
theorem eq_of_msg_eq_right {t : ℕ} {v x y : V} (hx : G.Adj v x) (hy : G.Adj v y)
    (h : P.msg t v x = P.msg t v y) : x = y :=
  P.outPort_inj hx hy (congrArg (fun m => m.2.2) h)

end PortNumbering

/-! ### Indistinguishable neighbours -/

namespace PortNumbering

/-- `u` and `w` are a pair of indistinguishable neighbours of `v` in round `t`. -/
def Indist (t : ℕ) (v u w : V) : Prop :=
  u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ P.beta t u = P.beta t w ∧ deg G u = deg G w ∧
    P.outPort u v = P.outPort w v

/-- `u` and `w` are a pair of indistinguishable neighbours of `v` of order `k` in round `t`:
moreover, `v` has `k` distinct neighbours `v₁, …, v_k` with `β_t(vᵢ) = β_t(u)`. -/
def IndistOrder (t : ℕ) (v u w : V) (k : ℕ) : Prop :=
  P.Indist t v u w ∧ ∃ s : Finset V, k ≤ s.card ∧ ∀ x ∈ s, G.Adj v x ∧ P.beta t x = P.beta t u

theorem Indist.msg_eq {t : ℕ} {v u w : V} (h : P.Indist t v u w) : P.msg t u v = P.msg t w v := by
  obtain ⟨-, -, -, h1, h2, h3⟩ := h
  simp [msg, h1, h2, h3]

theorem Indist.mono {s t : ℕ} (hst : s ≤ t) {v u w : V} (h : P.Indist t v u w) :
    P.Indist s v u w := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  exact ⟨h0, h1, h2, P.beta_eq_of_le hst h3, h4, h5⟩

/-- Lemma 5 of [Hella et al.], for rounds `t ≥ 3` (the paper assumes `t ≥ 4`). -/
theorem lemma5' [Finite V] {t : ℕ} (ht : 3 ≤ t) {v u w : V} {k : ℕ}
    (h : P.IndistOrder t v u w k) : P.IndistOrder (t - 2) v u w (k + 1) := by
  classical
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
  have ht' : t' ≠ 0 := by omega
  simp only [Nat.add_sub_cancel]
  obtain ⟨hI, s, hks, hs⟩ := h
  have hI' : P.Indist t' v u w := Indist.mono P (by omega) hI
  refine ⟨hI', ?_⟩
  obtain ⟨huw, hvu, hvw, -, -, -⟩ := hI
  -- the case `k = 0`
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact ⟨{u}, by simp, by simpa using hvu⟩
  obtain ⟨v1, hv1⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨hvv1, hb1⟩ := hs v1 hv1
  -- step 1: for `x ∈ s`, `v₁` has a neighbour `u_x` sending it the message `m_{t-1}(v, x)`
  have step1 : ∀ x ∈ s, ∃ ux, G.Adj v1 ux ∧ P.msg (t' + 1) ux v1 = P.msg (t' + 1) v x := by
    intro x hx
    obtain ⟨hvx, hbx⟩ := hs x hx
    have hB : P.Bset (t' + 1) x = P.Bset (t' + 1) v1 :=
      P.Bset_eq_of_beta (hbx.trans hb1.symm)
    have hm : P.msg (t' + 1) v x ∈ P.Bset (t' + 1) v1 :=
      hB ▸ P.msg_mem_Bset (by omega) hvx.symm
    exact P.mem_Bset hm
  choose! f hf using step1
  have hf_inj : Set.InjOn f s := by
    intro x hx y hy hxy
    have := (hf x hx).2.symm.trans (hxy ▸ (hf y hy).2)
    exact P.eq_of_msg_eq_right (hs x hx).1 (hs y hy).1 this
  -- step 2: `v` has a neighbour `y_x` sending it `m_{t-2}(v₁, u_x)`
  have step2 : ∀ x ∈ s, ∃ y, G.Adj v y ∧ P.msg t' y v = P.msg t' v1 (f x) := by
    intro x hx
    obtain ⟨hv1f, hmf⟩ := hf x hx
    have hbf : P.beta (t' + 1) (f x) = P.beta (t' + 1) v := congrArg Prod.fst hmf
    have hB : P.Bset t' (f x) = P.Bset t' v := P.Bset_eq_of_beta hbf
    have hm : P.msg t' v1 (f x) ∈ P.Bset t' v := hB ▸ P.msg_mem_Bset ht' hv1f.symm
    exact P.mem_Bset hm
  choose! g hg using step2
  have hgf_inj : Set.InjOn (g) s := by
    intro x hx y hy hxy
    have h1 := (hg x hx).2
    have h2 := (hg y hy).2
    rw [hxy] at h1
    have := h1.symm.trans h2
    exact hf_inj hx hy (P.eq_of_msg_eq_right (hf x hx).1 (hf y hy).1 this)
  have hbv1 : P.beta t' v1 = P.beta t' u := P.beta_eq_of_le (by omega) hb1
  -- the neighbours `y_x` have `β_{t-2}(y_x) = β_{t-2}(u)`
  have hgprop : ∀ x ∈ s, G.Adj v (g x) ∧ P.beta t' (g x) = P.beta t' u := by
    intro x hx
    refine ⟨(hg x hx).1, ?_⟩
    have := congrArg Prod.fst (hg x hx).2
    simp only [msg] at this
    rw [this, hbv1]
  set s1 := s.image (g) with hs1
  have hs1card : s1.card = s.card := Finset.card_image_of_injOn hgf_inj
  -- step 3: `u, w ∉ s1` simultaneously is impossible; so `s1 ∪ {u, w}` has `k + 1` elements
  have key : u ∉ s1 ∨ w ∉ s1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hu1, hw1⟩ := hcon
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.1 hu1
    obtain ⟨y, hy, hyw⟩ := Finset.mem_image.1 hw1
    have hmx := (hg x hx).2
    have hmy := (hg y hy).2
    rw [hxu] at hmx
    rw [hyw] at hmy
    have hmuw := hI'.msg_eq
    have hfxy : f x = f y :=
      P.eq_of_msg_eq_right (hf x hx).1 (hf y hy).1 (hmx.symm.trans (hmuw.trans hmy))
    have hxy : x = y := hf_inj hx hy hfxy
    subst hxy
    exact huw (hxu.symm.trans hyw)
  have hbw : P.beta t' w = P.beta t' u := hI'.2.2.2.1.symm
  rcases key with hu | hw
  · refine ⟨insert u s1, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hu]; omega
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨hvu, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        exact hgprop y hy
  · refine ⟨insert w s1, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hw]; omega
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨hvw, hbw⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        exact hgprop y hy

/-- Lemma 5 of [Hella et al.]: if `u` and `w` are a pair of indistinguishable neighbours of `v`
of order `k` in round `t ≥ 4`, then they are a pair of indistinguishable neighbours of `v` of
order `k + 1` in round `t - 2`. -/
theorem lemma5 [Finite V] {t : ℕ} (ht : 4 ≤ t) {v u w : V} {k : ℕ}
    (h : P.IndistOrder t v u w k) : P.IndistOrder (t - 2) v u w (k + 1) :=
  P.lemma5' (by omega) h

theorem card_le_deg [Finite V] {v : V} (s : Finset V) (hs : ∀ x ∈ s, G.Adj v x) :
    s.card ≤ deg G v := by
  rw [deg, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun x hx => hs x hx) (Set.toFinite _)

/-- Lemma 6 of [Hella et al.]: if `v` has two indistinguishable neighbours of order `k` in round
`2t` (`t ≥ 1`), then `v` has at least `t + k - 1` neighbours. -/
theorem lemma6 [Finite V] {t : ℕ} (ht : 1 ≤ t) {v u w : V} {k : ℕ}
    (h : P.IndistOrder (2 * t) v u w k) : t + k - 1 ≤ deg G v := by
  induction t, ht using Nat.le_induction generalizing k with
  | base =>
    obtain ⟨-, s, hks, hs⟩ := h
    have := card_le_deg s (fun x hx => (hs x hx).1)
    omega
  | succ t ht ih =>
    have h' := P.lemma5 (by omega) h
    have : 2 * (t + 1) - 2 = 2 * t := by omega
    rw [this] at h'
    have := ih h'
    omega

/-- Lemma 6, consequence: no node has a pair of indistinguishable neighbours in round `2Δ`. -/
theorem lemma6_consequence [Finite V] {Δ : ℕ} (hG : MaxDegLE G Δ) (v u w : V) :
    ¬ P.Indist (2 * Δ) v u w := by
  intro h
  rcases Nat.eq_zero_or_pos Δ with hΔ | hΔ
  · subst hΔ
    have := card_le_deg {u} (by simpa using h.2.1)
    have := hG v
    simp at *
    omega
  · have hO : P.IndistOrder (2 * Δ) v u w 2 := by
      classical
      refine ⟨h, {u, w}, by rw [Finset.card_pair h.1], ?_⟩
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨h.2.1, rfl⟩
      · rw [Finset.mem_singleton.1 hx]; exact ⟨h.2.2.1, h.2.2.2.1.symm⟩
    have := P.lemma6 hΔ hO
    have := hG v
    omega

/-- The messages `m_t(u, v)`, `t ≥ 2Δ`, of distinct neighbours `u` of `v` are distinct. -/
theorem msg_injective [Finite V] {Δ : ℕ} (hG : MaxDegLE G Δ) {t : ℕ} (ht : 2 * Δ ≤ t)
    {v u w : V} (hu : G.Adj v u) (hw : G.Adj v w) (h : P.msg t u v = P.msg t w v) : u = w := by
  by_contra hne
  apply P.lemma6_consequence hG v u w
  simp only [msg, Prod.mk.injEq] at h
  exact ⟨hne, hu, hw, P.beta_eq_of_le ht h.1, h.2.1, h.2.2⟩

end PortNumbering


/-! ### The simulating `Set` algorithm -/

namespace Machine

variable {Δ : ℕ} {Y : Type}

theorem recv_apply_lt (A : Machine Δ Y) (x : V → Y ⊕ A.Z) (v : V) (i : Fin Δ)
    (hi : (i : ℕ) < deg G v) :
    A.recv G P x v i = A.send (x (P.inNbr v ⟨i, hi⟩)) (P.outPort (P.inNbr v ⟨i, hi⟩) v) := by
  simp only [recv, dif_pos hi]
  rw [P.symm_snd]
  rfl

/-- States of the simulating `Set` machine: during the first `2Δ + 1` rounds the node runs `C_Δ`
(`c s d b`: round counter, degree, current `β`); afterwards it simulates `A`
(`sim d L z`: degree, final label `L = β`, current state of `A`). -/
inductive SState (Z : Type) where
  | c (s d b : ℕ)
  | sim (d L : ℕ) (z : Z)

/-- The (non-`m0`) entries of a vector are pairwise distinct. -/
def NoDupSome {M : Type*} (w : Fin Δ → Option M) : Prop :=
  ∀ i j, w i = w j → w i ≠ none → i = j

theorem multiset_eq_of_noDupSome {M : Type*} {w w' : Fin Δ → Option M} (hw : NoDupSome w)
    (hw' : NoDupSome w') (hr : Set.range w = Set.range w') :
    Multiset.map w univ.val = Multiset.map w' univ.val := by
  classical
  have key : ∀ (u : Fin Δ → Option M),
      Multiset.map u univ.val =
        (Multiset.map u univ.val).filter (· ≠ none) +
          Multiset.replicate (Δ - ((Multiset.map u univ.val).filter (· ≠ none)).card) none := by
    intro u
    set m := Multiset.map u univ.val with hm
    have hc : Multiset.card m = Δ := by simp [hm]
    have hsplit := Multiset.filter_add_not (· ≠ none) m
    have hrep : m.filter (fun x => ¬ x ≠ none) =
        Multiset.replicate (Δ - (m.filter (· ≠ none)).card) none := by
      rw [Multiset.eq_replicate]
      refine ⟨?_, fun b hb => by simpa using (Multiset.mem_filter.1 hb).2⟩
      have := congrArg Multiset.card hsplit
      rw [Multiset.card_add, hc] at this
      omega
    rw [← hrep, hsplit]
  have hnd : ∀ (u : Fin Δ → Option M), NoDupSome u →
      ((Multiset.map u univ.val).filter (· ≠ none)).Nodup := by
    intro u hu
    rw [Multiset.filter_map]
    refine Multiset.Nodup.map_on ?_ (Multiset.Nodup.filter _ univ.nodup)
    intro i hi j _ hij
    exact hu i j hij (by simpa using (Multiset.mem_filter.1 hi).2)
  have hfe : (Multiset.map w univ.val).filter (· ≠ none) =
      (Multiset.map w' univ.val).filter (· ≠ none) := by
    refine Multiset.Nodup.ext (hnd w hw) (hnd w' hw') |>.2 fun x => ?_
    simp only [Multiset.mem_filter, Multiset.mem_map, mem_val, mem_univ, true_and]
    have := congrArg (x ∈ ·) hr
    simp only [Set.mem_range, eq_iff_iff] at this
    rw [this]
  rw [key w, key w', hfe]

variable (A : Machine Δ Y)

/-- Projection of a message of the simulating machine to the simulated message of `A`. -/
def proj4 : Option (ℕ × ℕ × ℕ × A.M) → A.M
  | some m => m.2.2.2
  | none => A.m0

open Classical in
/-- A canonical vector with a given set of entries and pairwise distinct non-`m0` entries
(chosen if it exists), projected to messages of `A`. -/
noncomputable def canon (S : Set (Option (ℕ × ℕ × ℕ × A.M))) : Fin Δ → A.M :=
  if h : ∃ w : Fin Δ → Option (ℕ × ℕ × ℕ × A.M), Set.range w = S ∧ NoDupSome w then
    fun i => A.proj4 (h.choose i) else fun _ => A.m0

open Classical in
/-- The set `B_t` of triples `(β, deg, port)` received in a round of `C_Δ`. -/
noncomputable def recvSet (w : Fin Δ → Option (ℕ × ℕ × ℕ × A.M)) : Finset (ℕ × ℕ × ℕ) :=
  (univ.image w).biUnion fun o => (o.map fun m => (m.1, m.2.1, m.2.2.1)).toFinset

/-- The `Set` machine of Theorem 4: run `C_Δ` for `2Δ + 1` rounds, then simulate `A`, tagging
each message with the label `β_{2Δ+1}`, the degree and the out-port number. -/
noncomputable abbrev setMachine : Machine Δ Y where
  Z := SState A.Z
  M := Option (ℕ × ℕ × ℕ × A.M)
  m0 := none
  z0 d := .inr (.c 0 d (Encodable.encode ((0 : ℕ), (∅ : Finset (ℕ × ℕ × ℕ)))))
  μ
    | .c _ d b, i => some (b, d, i, A.m0)
    | .sim d L z, i => some (L, d, i, A.μ z i)
  δ
    | .c s d b, w =>
      if s + 1 < 2 * Δ + 1 then .inr (.c (s + 1) d (Encodable.encode (b, A.recvSet w)))
      else (A.z0 d).map id (.sim d b)
    | .sim d L z, w => (A.δ z (A.canon (Set.range w))).map id (.sim d L)

@[simp] theorem setMachine_m0 : A.setMachine.m0 = none := rfl
theorem setMachine_z0 (d : ℕ) : A.setMachine.z0 d =
    .inr (.c 0 d (Encodable.encode ((0 : ℕ), (∅ : Finset (ℕ × ℕ × ℕ))))) := rfl
@[simp] theorem setMachine_μ_c (s d b i : ℕ) : A.setMachine.μ (.c s d b) i = some (b, d, i, A.m0) :=
  rfl
@[simp] theorem setMachine_μ_sim (d L : ℕ) (z : A.Z) (i : ℕ) :
    A.setMachine.μ (.sim d L z) i = some (L, d, i, A.μ z i) := rfl
theorem setMachine_δ_c (s d b : ℕ) (w : Fin Δ → Option (ℕ × ℕ × ℕ × A.M)) :
    A.setMachine.δ (.c s d b) w =
      if s + 1 < 2 * Δ + 1 then .inr (.c (s + 1) d (Encodable.encode (b, A.recvSet w)))
      else (A.z0 d).map id (.sim d b) := rfl
theorem setMachine_δ_sim (d L : ℕ) (z : A.Z) (w : Fin Δ → Option (ℕ × ℕ × ℕ × A.M)) :
    A.setMachine.δ (.sim d L z) w = (A.δ z (A.canon (Set.range w))).map id (.sim d L) := rfl

theorem recvSet_congr {w w' : Fin Δ → Option (ℕ × ℕ × ℕ × A.M)}
    (h : Set.range w = Set.range w') : A.recvSet w = A.recvSet w' := by
  classical
  have : univ.image w = univ.image w' := by
    apply Finset.coe_injective
    simp [h]
  simp only [recvSet]
  convert congrArg (fun s => s.biUnion fun o => (o.map fun m => (m.1, m.2.1, m.2.2.1)).toFinset)
    this

theorem setMachine_isSet : A.setMachine.IsSet := by
  intro z w w' h
  cases z with
  | c s d b => simp only [setMachine, A.recvSet_congr h]
  | sim d L z =>
    exact congrArg (fun S => Sum.map id (SState.sim d L) (A.δ z (A.canon S))) h

variable [Finite V]

omit [Finite V] in
/-- The set received by `v` in a round of `C_Δ` is the set of messages `(b u, deg u, π(u, v))`. -/
theorem recvSet_recv_c (hG : MaxDegLE G Δ) (s : ℕ) (b : V → ℕ)
    (x : V → Y ⊕ A.setMachine.Z) (hx : ∀ u, x u = .inr (.c s (deg G u) (b u))) (v : V) :
    A.recvSet (A.setMachine.recv G P x v) = P.msgSet b v := by
  classical
  ext m
  simp only [recvSet, mem_biUnion, mem_image, mem_univ, true_and, PortNumbering.msgSet]
  constructor
  · rintro ⟨o, ⟨i, rfl⟩, hm⟩
    by_cases hi : (i : ℕ) < deg G v
    · rw [A.setMachine.recv_apply_lt P _ v i hi, hx] at hm
      exact ⟨⟨i, hi⟩, (Finset.mem_singleton.1 hm).symm⟩
    · rw [A.setMachine.recv_eq_m0 P _ i hi] at hm
      simp at hm
  · rintro ⟨i, rfl⟩
    have hi : ((⟨i, lt_of_lt_of_le i.2 (hG v)⟩ : Fin Δ) : ℕ) < deg G v := i.2
    refine ⟨_, ⟨⟨i, lt_of_lt_of_le i.2 (hG v)⟩, rfl⟩, ?_⟩
    rw [A.setMachine.recv_apply_lt P _ v _ hi, hx]
    exact Finset.mem_singleton.2 rfl


omit [Finite V] in
/-- During the first `2Δ + 1` rounds the simulating machine computes `β`. -/
theorem setMachine_state_c (hG : MaxDegLE G Δ) (s : ℕ) (hs : s < 2 * Δ + 1) (v : V) :
    A.setMachine.state G P s v = .inr (.c s (deg G v) (P.beta (s + 1) v)) := by
  induction s generalizing v with
  | zero => rfl
  | succ s ih =>
    rw [state_succ]
    change A.setMachine.update (A.setMachine.state G P s v)
      (A.setMachine.recv G P (A.setMachine.state G P s) v) = _
    rw [ih (by omega) v, update_inr, setMachine_δ_c, if_pos hs, P.beta_succ (s + 1),
      A.recvSet_recv_c P hG s _ _ (fun u => ih (by omega) u)]
    simp [PortNumbering.Bset]

omit [Finite V] in
theorem canon_spec {w : Fin Δ → Option (ℕ × ℕ × ℕ × A.M)} (hw : NoDupSome w) :
    Multiset.map (A.canon (Set.range w)) univ.val = Multiset.map (A.proj4 ∘ w) univ.val := by
  have h : ∃ w' : Fin Δ → Option (ℕ × ℕ × ℕ × A.M), Set.range w' = Set.range w ∧ NoDupSome w' :=
    ⟨w, rfl, hw⟩
  simp only [canon, dif_pos h]
  have hm := multiset_eq_of_noDupSome h.choose_spec.2 hw h.choose_spec.1
  rw [← Multiset.map_map A.proj4 w, ← hm, Multiset.map_map]
  rfl

/-- The vector received in a simulation round, projected to `A`'s messages, is exactly the vector
`A` receives; and its non-`m0` entries are pairwise distinct (by Lemma 6). -/
theorem recv_sim (hG : MaxDegLE G Δ) (t : ℕ) (x : V → Y ⊕ A.setMachine.Z)
    (hx : ∀ u, x u = (A.state G P t u).map id (SState.sim (deg G u) (P.beta (2 * Δ + 1) u)))
    (v : V) :
    A.proj4 ∘ A.setMachine.recv G P x v = A.recv G P (A.state G P t) v ∧
      NoDupSome (A.setMachine.recv G P x v) := by
  constructor
  · funext i
    by_cases hi : (i : ℕ) < deg G v
    · simp only [comp_apply]
      rw [A.setMachine.recv_apply_lt P _ v i hi, A.recv_apply_lt P _ v i hi, hx]
      cases A.state G P t (P.inNbr v ⟨i, hi⟩) <;> rfl
    · simp only [comp_apply]
      rw [A.setMachine.recv_eq_m0 P _ i hi, A.recv_eq_m0 P _ i hi]
      rfl
  · -- the non-`m0` entries are `(β_{2Δ+1}(u), deg u, π(u, v), ·)` for distinct senders `u`
    have hform : ∀ i : Fin Δ, A.setMachine.recv G P x v i ≠ none →
        ∃ hi : (i : ℕ) < deg G v, ∃ a, A.setMachine.recv G P x v i =
          some (P.beta (2 * Δ + 1) (P.inNbr v ⟨i, hi⟩), deg G (P.inNbr v ⟨i, hi⟩),
            P.outPort (P.inNbr v ⟨i, hi⟩) v, a) := by
      intro i hne
      by_cases hi : (i : ℕ) < deg G v
      · refine ⟨hi, ?_⟩
        rw [A.setMachine.recv_apply_lt P _ v i hi, hx] at hne ⊢
        cases hs : A.state G P t (P.inNbr v ⟨i, hi⟩) with
        | inl y => rw [hs] at hne; exact absurd rfl hne
        | inr z => exact ⟨A.μ z (P.outPort (P.inNbr v ⟨i, hi⟩) v), rfl⟩
      · exact absurd (A.setMachine.recv_eq_m0 P _ i hi) hne
    intro i j hij hne
    obtain ⟨hi, a, ha⟩ := hform i hne
    obtain ⟨hj, b, hb⟩ := hform j (hij ▸ hne)
    rw [ha, hb] at hij
    simp only [Option.some.injEq, Prod.mk.injEq] at hij
    obtain ⟨h1, h2, h3, -⟩ := hij
    have hm : P.msg (2 * Δ + 1) (P.inNbr v ⟨i, hi⟩) v = P.msg (2 * Δ + 1) (P.inNbr v ⟨j, hj⟩) v := by
      simp only [PortNumbering.msg] at h1 ⊢
      rw [h1, h2, h3]
    have := P.msg_injective hG (by omega) (P.adj_inNbr v _) (P.adj_inNbr v _) hm
    have := P.injective_inNbr v this
    exact Fin.ext (by simpa using congrArg Fin.val this)

/-- After the `C_Δ` phase, the simulating machine simulates `A` step by step. -/
theorem setMachine_state_sim (hA : A.IsMultiset) (hG : MaxDegLE G Δ) (t : ℕ) (v : V) :
    A.setMachine.state G P (2 * Δ + 1 + t) v =
      (A.state G P t v).map id (SState.sim (deg G v) (P.beta (2 * Δ + 1) v)) := by
  induction t generalizing v with
  | zero =>
    rw [Nat.add_zero, state_succ]
    change A.setMachine.update (A.setMachine.state G P (2 * Δ) v)
      (A.setMachine.recv G P (A.setMachine.state G P (2 * Δ)) v) = _
    rw [A.setMachine_state_c P hG (2 * Δ) (by omega) v, update_inr, setMachine_δ_c,
      if_neg (by omega)]
    rfl
  | succ t ih =>
    rw [show 2 * Δ + 1 + (t + 1) = (2 * Δ + 1 + t) + 1 by omega, state_succ, state_succ]
    change A.setMachine.update (A.setMachine.state G P (2 * Δ + 1 + t) v)
      (A.setMachine.recv G P (A.setMachine.state G P (2 * Δ + 1 + t)) v) =
      (A.update (A.state G P t v) (A.recv G P (A.state G P t) v)).map id _
    obtain ⟨h1, h2⟩ := A.recv_sim P hG t _ ih v
    rw [ih v]
    cases A.state G P t v with
    | inl y => rfl
    | inr z =>
      change A.setMachine.δ (SState.sim _ _ z) _ = _
      rw [setMachine_δ_sim, update_inr]
      congr 1
      apply hA
      rw [A.canon_spec h2, h1]

end Machine

/-- Theorem 4 of [Hella et al.]: if a `Multiset` algorithm solves `Π` in time `T`, then a `Set`
algorithm solves `Π` in time `T + O(Δ)` (here `T + 2Δ + 1`). -/
theorem theorem4 {Y : Type} {Pr : GraphProblem Y} {T : ℕ → ℕ → ℕ} {A : Algorithm Y}
    (hM : ∀ Δ, (A Δ).IsMultiset) (hA : A.SolvesIn Pr T) :
    ∃ B : Algorithm Y, (∀ Δ, (B Δ).IsSet) ∧
      B.SolvesIn Pr (fun Δ n => T Δ n + (2 * Δ + 1)) := by
  refine ⟨fun Δ => (A Δ).setMachine, fun Δ => (A Δ).setMachine_isSet, ?_⟩
  intro Δ V _ G hG P
  obtain ⟨S, hS, hSP⟩ := hA Δ V G hG P
  refine ⟨S, fun u => ?_, hSP⟩
  show (A Δ).setMachine.state G P (T Δ (Nat.card V) + (2 * Δ + 1)) u = _
  rw [add_comm, (A Δ).setMachine_state_sim P (hM Δ) hG, hS u]
  rfl

/-- Corollary 7 of [Hella et al.]: `MV = SV` and `MV(1) = SV(1)`. -/
theorem cor7 (Y : Type) : MV Y = SV Y ∧ MV1 Y = SV1 Y := by
  refine ⟨le_antisymm ?_ (SV_subset_MV), le_antisymm ?_ (SV1_subset_MV1)⟩
  · rintro Pr ⟨A, T, hM, hA⟩
    obtain ⟨B, hB, hBs⟩ := theorem4 hM hA
    exact ⟨B, _, hB, hBs⟩
  · rintro Pr ⟨A, T, hM, hA⟩
    obtain ⟨B, hB, hBs⟩ := theorem4 hM hA
    exact ⟨B, fun Δ => T Δ + (2 * Δ + 1), hB, hBs⟩

end Podc.WeakModelsModalLogic
