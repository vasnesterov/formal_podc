import Papers.PODC2025.DynamicSubgraphFinding.Views
import Papers.PODC2025.DynamicSubgraphFinding.Counting
import Papers.PODC2025.DynamicSubgraphFinding.Arith

/-!
# Theorem 1.3: `Ω(log log n)` for one-round `MemDetect(K_s)` under edge insertions

Section 4.2. Fix an algorithm `A`. Notation: `R = 2qt` (last round before `t_final = R + 1`).

* `patA K A w j u`: the messages `w` receives from `K^j` in rounds `1..t_final` of `S1(w, j, u)`.
  Two nodes `u, v` are *friends* w.r.t. `(w, j)` if `patA K A w j u = patA K A w j v`.
* `patB K A b v j`: the messages `b` receives from `K^j` in rounds `1..R` of `S1(v, j, b)`.
* `msgB K A a b j`: the message `b` sends to `a` in round `t_final` of `S1(a, j, b)`.

`a_state_S2`: if `b, c` are friends w.r.t. `(a, i)`, `patB b a = patB b d` (Lemma 4.2), and
`msgB a b i = msgB a b i'` (Lemma 4.3), then `a` is in the same state after round `t_final` in
`S2(a, i, c, d, i', b)` and in `S1(a, i, b)`. The counting (Lemmas 4.1–4.3) is in
`exists_params_13`; `not_solves_13` is the finite form of Theorem 1.3.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Hard

variable {V M : Type} {q t : ℕ}

section Defs

variable (K : Fin t → Fin q → V) {O : Type} (A : Algorithm V M O)

/-- Messages received by `w` from `K^j` in rounds `1..T` of `S1(w, j, u)`. -/
noncomputable def patA (w : V) (j : Fin t) (u : V) : Fin (2 * q * t + 1) → Fin q → Option M :=
  fun k p => A.inbox (net K (S1 True w j u)) (A.state (net K (S1 True w j u)) k) (k + 1) w (K j p)

/-- Messages received by `b` from `K^j` in rounds `1..R` of `S1(v, j, b)`. -/
noncomputable def patB (b : V) (v : V) : Fin t → Fin (2 * q * t) → Fin q → Option M :=
  fun j k p => A.inbox (net K (S1 True v j b)) (A.state (net K (S1 True v j b)) k) (k + 1) b (K j p)

/-- The message `b` sends to `a` in round `T` of `S1(a, j, b)`. -/
noncomputable def msgB (a b : V) (j : Fin t) : M :=
  A.send (2 * q * t + 1) (A.state (net K (S1 True a j b)) (2 * q * t) b)
    ((net K (S1 True a j b)).loc (2 * q * t + 1) b) a

end Defs

variable {K : Fin t → Fin q → V} {O : Type} (A : Algorithm V M O)

lemma send_eq_of_inbox_eq {D D' : InsNet V} {k : ℕ} {u w : V} (h : D.adj (k + 1) u w)
    (h' : D'.adj (k + 1) u w)
    (he : A.inbox D (A.state D k) (k + 1) w u = A.inbox D' (A.state D' k) (k + 1) w u) :
    A.send (k + 1) (A.state D k u) (D.loc (k + 1) u) w =
      A.send (k + 1) (A.state D' k u) (D'.loc (k + 1) u) w := by
  unfold Algorithm.inbox at he
  rw [ite_eq_left h, ite_eq_left h'] at he
  exact Option.some.inj he

/-- Friends see the same thing: the state of `a` after round `R` of `S1(a, i, c)` and of
`S1(a, i, b)` coincide if `b` and `c` are friends w.r.t. `(a, i)`. -/
lemma state_a_of_patA (hK : KInj K) {a b c : V} {i : Fin t} (ha : ¬ IsK K a) (hb : ¬ IsK K b)
    (hc : ¬ IsK K c) (hab : a ≠ b) (hac : a ≠ c) (h : patA K A a i c = patA K A a i b) :
    A.state (net K (S1 True a i c)) (2 * q * t) a = A.state (net K (S1 True a i b)) (2 * q * t) a := by
  have hw1 := wf_S1 (full := True) (i := i) ha hc hac
  have hw2 := wf_S1 (full := True) (i := i) ha hb hab
  have hc1 : (S1 True a i c).cr i = some (a, c) := by simp [S1, crOne]
  have hc2 : (S1 True a i b).cr i = some (a, b) := by simp [S1, crOne]
  have hadj : ∀ k ≤ 2 * q * t, ∀ u, (net K (S1 True a i c)).adj k u a ↔ (net K (S1 True a i b)).adj k u a :=
    fun k hk u => adj_fst_eq hw1 hw2 hc1 hc2 hk u
  refine A.state_eq_of_msgs (g0_eq hK hw1 hw2 Iff.rfl) a _
    (fun k hk => loc_eq_of_adj (sp := S1 True a i c) (sp' := S1 True a i b) Iff.rfl k a (hadj k hk))
    hadj (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_fst_iff hw1 hc1] at hu0
  rcases hu0 with ⟨p, rfl, -⟩ | ⟨-, h1, -⟩
  · exact send_eq_of_inbox_eq A hu ((hadj (k + 1) hk _).1 hu)
      (congrFun (congrFun h ⟨k, by omega⟩) p)
  · omega

/-- The state of `b` after round `R` of `S1(v, j, b)` is determined by `patB b v j`. -/
lemma state_b_of_patB (hK : KInj K) {a b d : V} (ha : ¬ IsK K a) (hb : ¬ IsK K b)
    (hd : ¬ IsK K d) (hab : a ≠ b) (hdb : d ≠ b) (h : patB K A b a = patB K A b d) (j : Fin t) :
    A.state (net K (S1 True d j b)) (2 * q * t) b = A.state (net K (S1 True a j b)) (2 * q * t) b := by
  have hw1 := wf_S1 (full := True) (i := j) hd hb hdb
  have hw2 := wf_S1 (full := True) (i := j) ha hb hab
  have hc1 : (S1 True d j b).cr j = some (d, b) := by simp [S1, crOne]
  have hc2 : (S1 True a j b).cr j = some (a, b) := by simp [S1, crOne]
  have hadj : ∀ k ≤ 2 * q * t, ∀ u, (net K (S1 True d j b)).adj k u b ↔ (net K (S1 True a j b)).adj k u b :=
    fun k hk u => adj_snd_eq hw1 hw2 hc1 hc2 hk u
  refine A.state_eq_of_msgs (g0_eq hK hw1 hw2 Iff.rfl) b _
    (fun k hk => loc_eq_of_adj (sp := S1 True d j b) (sp' := S1 True a j b) Iff.rfl k b (hadj k hk))
    hadj (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_snd_iff hw1 hc1] at hu0
  rcases hu0 with ⟨p, rfl, -⟩ | ⟨-, h1, -⟩
  · exact send_eq_of_inbox_eq A hu ((hadj (k + 1) hk _).1 hu)
      (congrFun (congrFun (congrFun h j) ⟨k, by omega⟩) p).symm
  · omega

/-- **Indistinguishability of (S1) and (S2) for `a`** (proof of Theorem 1.3). -/
lemma a_state_S2 (hK : KInj K) {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup)
    (hA : patA K A a i c = patA K A a i b) (hB : patB K A b a = patB K A b d)
    (hm : msgB K A a b i = msgB K A a b i') :
    A.state (net K (S2 True a i c d i' b)) (2 * q * t + 1) a =
      A.state (net K (S1 True a i b)) (2 * q * t + 1) a := by
  have hd' := hdist
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hd'
  have hw := wf_S2 (full := True) hii ha hb hc hd hdist
  have hw1 := wf_S1 (full := True) (i := i) ha hb hab
  have hwc := wf_S1 (full := True) (i := i) ha hc hac
  have hwd := wf_S1 (full := True) (i := i') hd hb (Ne.symm hbd)
  have hwa' := wf_S1 (full := True) (i := i') ha hb hab
  have hci : (S2 True a i c d i' b).cr i = some (a, c) := by simp [S2, crTwo]
  have hci' : (S2 True a i c d i' b).cr i' = some (d, b) := by simp [S2, crTwo, Ne.symm hii]
  have hc1 : (S1 True a i b).cr i = some (a, b) := by simp [S1, crOne]
  have hcc : (S1 True a i c).cr i = some (a, c) := by simp [S1, crOne]
  have hcd : (S1 True d i' b).cr i' = some (d, b) := by simp [S1, crOne]
  have hca : (S1 True a i' b).cr i' = some (a, b) := by simp [S1, crOne]
  have hadj : ∀ k ≤ 2 * q * t + 1, ∀ u,
      (net K (S2 True a i c d i' b)).adj k u a ↔ (net K (S1 True a i b)).adj k u a := by
    intro k _ u
    rw [adj_fst_iff hw hci, adj_fst_iff hw1 hc1]
    exact Iff.rfl
  refine A.state_eq_of_msgs (g0_eq hK hw hw1 Iff.rfl) a _
    (fun k hk => loc_eq_of_adj (sp := S2 True a i c d i' b) (sp' := S1 True a i b) Iff.rfl k a
      (hadj k hk)) hadj (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_fst_iff hw hci] at hu0
  rcases hu0 with ⟨p, rfl, -⟩ | ⟨hne, h1, hf⟩
  · -- a message from the clique `K^i`
    have hk : k ≤ 2 * q * t := by omega
    have e1 : A.send (k + 1) (A.state (net K (S2 True a i c d i' b)) k (K i p))
        ((net K (S2 True a i c d i' b)).loc (k + 1) (K i p)) a =
        A.send (k + 1) (A.state (net K (S1 True a i c)) k (K i p))
        ((net K (S1 True a i c)).loc (k + 1) (K i p)) a := by
      rw [comp_state A hK hw hwc Iff.rfl hci hcc hk _ (Or.inr (Or.inr ⟨p, rfl⟩)),
        loc_eq_of_adj (sp := S2 True a i c d i' b) (sp' := S1 True a i c) Iff.rfl _ _
          (fun u => K_adj hK hw hwc hci hcc _ u p)]
    have hu1 : (net K (S1 True a i c)).adj (k + 1) (K i p) a := by
      rw [adj_fst_iff hwc hcc]; rw [adj_fst_iff hw hci] at hu
      rcases hu with h | ⟨-, -, h | h⟩
      · exact Or.inl h
      · exact absurd h.2 hab
      · exact absurd ⟨i, p, h.2⟩ hb
    rw [e1]
    exact send_eq_of_inbox_eq A hu1 ((hadj (k + 1) (by omega) _).1 hu)
      (congrFun (congrFun hA ⟨k, by omega⟩) p)
  · -- the message from `b` in round `T`
    have hkR : k = 2 * q * t := by omega
    subst hkR
    have hub : u = b := by
      rcases hf with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact absurd rfl hne
      · rfl
    subst hub
    have hlocb : (net K (S2 True a i c d i' u)).loc (2 * q * t + 1) u =
        (net K (S1 True a i' u)).loc (2 * q * t + 1) u := by
      refine loc_eq_of_adj (sp := S2 True a i c d i' u) (sp' := S1 True a i' u) Iff.rfl _ _
        (fun v => ?_)
      rw [adj_snd_iff hw hci', adj_snd_iff hwa' hca]
      exact Iff.rfl
    rw [comp_state A hK hw hwd Iff.rfl hci' hcd le_rfl _ (Or.inr (Or.inl rfl)), hlocb,
      state_b_of_patB A hK ha hb hd hab (Ne.symm hbd) hB i']
    exact hm.symm

/-- **Theorem 1.3, finite form.** Let `I` be the nodes outside the `t` cliques of size `q = s - 2`.
If `|M| < t`, `|patterns of b| < k₀` and `k₀ (1 + 2t·|patterns of w|) < |I|`, then no algorithm
with message alphabet `M` solves one-round `MemDetect(K_{q+2})` under edge insertions, even on
networks of maximum degree `q + 1 = s - 1`. -/
theorem not_solves_13 [Fintype V] [Fintype M] (hK : KInj K) (hq : 1 ≤ q)
    (A : Algorithm V M Bool) (I : Finset V) (hI : ∀ v ∈ I, ¬ IsK K v) (k0 : ℕ)
    (h1 : Fintype.card M < t)
    (h2 : Fintype.card (Fin t → Fin (2 * q * t) → Fin q → Option M) < k0)
    (h3 : k0 + k0 * (t * (2 * Fintype.card (Fin (2 * q * t + 1) → Fin q → Option M))) < I.card) :
    ¬ Solves A InsNet.EdgeIns (q + 1) (MemDetectOK (q + 2)) := by
  intro hA
  obtain ⟨a, haI, b, hbI, c, hcI, d, hdI, i, i', hii, hdist, hpA, hpB, hm⟩ :=
    select13 I t (patA K A) (patB K A) (msgB K A) k0 h1 h2 h3
  have ha := hI a haI
  have hb := hI b hbI
  have hc := hI c hcI
  have hd := hI d hdI
  have hab : a ≠ b := by simp at hdist; tauto
  -- in (S1), `a` belongs to an `s`-clique, so it must output `true`
  have hS1 := hA _ (edgeIns_S1 (i := i) hK ha hb hab) (degLE_S1 hK ha hb hab) (2 * q * t + 1) a
    (Or.inl trivial)
  have hyes : A.output (net K (S1 True a i b)) (2 * q * t + 1) a = true :=
    hS1.2 ⟨_, clique_S1 hK ha hb hab, by simp⟩
  -- in (S2), it is in no `s`-clique
  have hS2 := hA _ (edgeIns_S2 hK hii ha hb hc hd hdist) (degLE_S2 hK hii ha hb hc hd hdist)
    (2 * q * t + 1) a (Or.inl trivial)
  unfold Algorithm.output at hyes hS2
  rw [a_state_S2 A hK hii ha hb hc hd hdist hpA hpB hm] at hS2
  obtain ⟨Q, hQ, -⟩ := hS2.1 hyes
  exact no_clique_S2 hK hq hii ha hb hc hd hdist _ Q hQ

end Hard

/-! ### The asymptotic statement -/

/-- From `B < (1/8) log₂ log₂ n` to `2^{8B} ≤ ⌊log₂ n⌋`. -/
lemma pow_le_log_of_lt {n B : ℕ} (c : ℕ) (hc : 0 < c) (hn : 2 ≤ n)
    (h : (B : ℝ) < (1 / c : ℝ) * Real.logb 2 (Real.logb 2 n)) :
    2 ^ (c * B) ≤ Nat.log 2 n := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.logb 2 n := Real.logb_pos one_lt_two hn'
  have h1 : ((c * B : ℕ) : ℝ) < Real.logb 2 (Real.logb 2 n) := by
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    push_cast
    rw [one_div, inv_mul_eq_div, lt_div_iff₀ hc'] at h
    linarith
  rw [Real.lt_logb_iff_rpow_lt one_lt_two hlog, Real.rpow_natCast] at h1
  have h2 : (((2 ^ (c * B) : ℕ) : ℕ) : ℝ) < Real.logb 2 n := by exact_mod_cast h1
  rw [Real.lt_logb_iff_rpow_lt one_lt_two (by positivity), Real.rpow_natCast] at h2
  have h3 : 2 ^ (2 ^ (c * B)) < n := by exact_mod_cast h2
  exact Nat.le_log_of_pow_le one_lt_two h3.le

/-- Cliques `K i k = i q + k` in `Fin n`. -/
def blockK (n q t : ℕ) (h : t * q ≤ n) : Fin t → Fin q → Fin n :=
  fun i k => ⟨i * q + k, by
    have h1 : (i : ℕ) * q + q ≤ t * q := by
      have := Nat.mul_le_mul_right q (Nat.succ_le_of_lt i.2)
      rw [Nat.succ_mul] at this; exact this
    have := k.2
    omega⟩

lemma blockK_inj {n q t : ℕ} (h : t * q ≤ n) : Hard.KInj (blockK n q t h) := by
  intro i k i' k' he
  have he' : (k : ℕ) + q * i = k' + q * i' := by
    have := congrArg Fin.val he
    simp only [blockK] at this
    linarith
  have hq : 0 < q := by have := k.2; omega
  have hd := congrArg (· / q) he'
  rw [Nat.add_mul_div_left _ _ hq, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt k.2,
    Nat.div_eq_of_lt k'.2, Nat.zero_add, Nat.zero_add] at hd
  have hi : i = i' := Fin.ext hd
  subst hi
  exact ⟨rfl, Fin.ext (by omega)⟩

lemma card_I_ge {n q t : ℕ} (h : t * q ≤ n) :
    n - t * q ≤ (Finset.univ.filter (fun v => ¬ Hard.IsK (blockK n q t h) v)).card := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (p := Hard.IsK (blockK n q t h))
  have h2 : (Finset.univ.filter (Hard.IsK (blockK n q t h))).card ≤ t * q := by
    refine (Finset.card_le_card (t := Finset.univ.image
      (fun p : Fin t × Fin q => blockK n q t h p.1 p.2)) ?_).trans ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨i, k, rfl⟩ := hv
      simp
    · exact Finset.card_image_le.trans (by simp)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- **Theorem 1.3.** For every `s ≥ 3`, the one-round bandwidth complexity of `MemDetect(K_s)`
under edge insertions is `Ω(log log n)`, even in dynamic networks of maximum degree `s - 1`:
for all large `n`, every one-round algorithm on identifiers `[n]` whose messages take at most
`2^B` values (i.e. `B` bits) satisfies `B ≥ (1/8) log₂ log₂ n`. -/
theorem theorem_1_3 (s : ℕ) (hs : 3 ≤ s) : ∃ N : ℕ, ∀ n ≥ N, ∀ (M : Type) [Fintype M] (B : ℕ),
    Fintype.card M ≤ 2 ^ B → ∀ A : Algorithm (Fin n) M Bool,
    Solves A InsNet.EdgeIns (s - 1) (MemDetectOK s) →
    (1 / 8 : ℝ) * Real.logb 2 (Real.logb 2 n) ≤ B := by
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  have hq : 1 ≤ q := by omega
  refine ⟨2 ^ ((40 * q ^ 2) ^ 3 + 1), fun n hn M _ B hM A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hn2 : 2 ≤ n := le_trans (by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ((40 * q ^ 2) ^ 3 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) hn
  have hL1 : 2 ^ (8 * B) ≤ Nat.log 2 n := pow_le_log_of_lt 8 (by norm_num) hn2 (by exact_mod_cast hlt)
  have hL2 : (40 * q ^ 2) ^ 3 < Nat.log 2 n :=
    Nat.lt_of_succ_le (Nat.le_log_of_pow_le one_lt_two hn)
  have hkey := key_bound q B (Nat.log 2 n) hL1 hL2
  set W := 2 ^ (B + 1) with hW
  have hW2 : 2 ≤ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  set R := 2 * q * W with hR
  set a := q * R * W with ha
  set b := q * (R + 1) with hb
  set m := Fintype.card M
  have hmW : m + 1 ≤ W := by
    have : 2 ^ B < W := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hcγ : Fintype.card (Fin W → Fin R → Fin q → Option M) ≤ W ^ a := by
    simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
    rw [← pow_mul, ← pow_mul]
    refine (Nat.pow_le_pow_left hmW _).trans (le_of_eq ?_)
    rw [ha]; ring_nf
  have hcβ : Fintype.card (Fin (R + 1) → Fin q → Option M) ≤ W ^ b := by
    simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
    rw [← pow_mul]
    refine (Nat.pow_le_pow_left hmW _).trans (le_of_eq ?_)
    rw [hb]
  have hqa : q ≤ W ^ a := by
    have h1 : q < 2 ^ q := Nat.lt_two_pow_self
    have h2 : 2 ^ q ≤ W ^ q := Nat.pow_le_pow_left hW2 q
    have h3 : W ^ q ≤ W ^ a := Nat.pow_le_pow_right (by omega) (by
      rw [ha, hR]; nlinarith)
    omega
  have hZ : a + b + 5 ≤ 10 * q ^ 2 * W ^ 2 := by
    rw [ha, hb, hR]; nlinarith
  have hbig : W ^ (a + b + 5) < n := by
    calc W ^ (a + b + 5) ≤ W ^ (10 * q ^ 2 * W ^ 2) := Nat.pow_le_pow_right (by omega) hZ
      _ = 2 ^ ((B + 1) * (10 * q ^ 2 * W ^ 2)) := by rw [hW, ← pow_mul]
      _ < 2 ^ Nat.log 2 n := Nat.pow_lt_pow_right (by norm_num) hkey
      _ ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hsum := sum_bound W a b q hW2 hqa
  set cγ := Fintype.card (Fin W → Fin R → Fin q → Option M)
  set cβ := Fintype.card (Fin (R + 1) → Fin q → Option M)
  have hsum' : (cγ + 1) + (cγ + 1) * (W * (2 * cβ)) + W * q < n := by
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hsum hbig)
    gcongr
  have hWq : W * q ≤ n := by
    have : W * q ≤ (cγ + 1) + (cγ + 1) * (W * (2 * cβ)) + W * q := by omega
    omega
  have hI := card_I_ge hWq
  refine Hard.not_solves_13 (blockK_inj hWq) hq A
    (Finset.univ.filter (fun v => ¬ Hard.IsK (blockK n q W hWq) v))
    (fun v hv => (Finset.mem_filter.mp hv).2) (cγ + 1) (by omega) (Nat.lt_succ_self _) ?_ hA
  exact (show (cγ + 1) + (cγ + 1) * (W * (2 * cβ)) < _ by omega)

end Podc.DynamicSubgraphFinding
