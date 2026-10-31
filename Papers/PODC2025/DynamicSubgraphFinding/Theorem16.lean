import Papers.PODC2025.DynamicSubgraphFinding.Theorem13

/-!
# Theorem 1.6: `Ω(log log log n)` for one-round `Detect(K_s)` under node and edge insertions

Section 4.3. Model: node insertions and edge insertions; nodes of `I` are inserted with their
first edge (`full = False`). Notation `R = 2qt`, `t_final = R + 1`.

* `col16 K A x y i`: the colour of the ordered pair `(x, y)` at index `i`: the messages from `K^i`
  to `x` and to `y` in rounds `1..t_final`, and from `x` and `y` to `K^i` in round `t_final`, in
  `S1(x, i, y)`.
* `msgs16 K A a b j`: the two messages across `{a, b}` in round `t_final` of `S1(a, j, b)`.

Indistinguishability: `K_state_S4` (`K^i` cannot distinguish (S1) and (S4)), `a_state_S2F`,
`b_state_S3F`. `not_solves_16` is the finite form; `theorem_1_6` the asymptotic one.
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Hard

variable {V M : Type} {q t : ℕ}

section Defs

variable (K : Fin t → Fin q → V) {O : Type} (A : Algorithm V M O)

/-- Message from `K i p` to `z` in round `k + 1` of `S1(x, i, y)` (node-insertion model). -/
noncomputable def inK (x : V) (i : Fin t) (y z : V) (k : ℕ) (p : Fin q) : Option M :=
  A.inbox (net K (S1 False x i y)) (A.state (net K (S1 False x i y)) k) (k + 1) z (K i p)

/-- Message from `z` to `K i p` in round `t_final` of `S1(x, i, y)`. -/
noncomputable def outK (x : V) (i : Fin t) (y z : V) (p : Fin q) : Option M :=
  A.inbox (net K (S1 False x i y)) (A.state (net K (S1 False x i y)) (2 * q * t))
    (2 * q * t + 1) (K i p) z

/-- The colour of the ordered pair `(x, y)` (Lemma 4.4). -/
noncomputable def col16 (x y : V) : Fin t →
    (Fin (2 * q * t + 1) → Fin q → Option M) × (Fin (2 * q * t + 1) → Fin q → Option M) ×
      (Fin q → Option M) × (Fin q → Option M) :=
  fun i => (fun k p => inK K A x i y x k p, fun k p => inK K A x i y y k p,
    fun p => outK K A x i y x p, fun p => outK K A x i y y p)

/-- The messages `a → b` and `b → a` in round `t_final` of `S1(a, j, b)` (Lemma 4.5). -/
noncomputable def msgs16 (a b : V) (j : Fin t) : M × M :=
  (A.send (2 * q * t + 1) (A.state (net K (S1 False a j b)) (2 * q * t) a)
      ((net K (S1 False a j b)).loc (2 * q * t + 1) a) b,
    A.send (2 * q * t + 1) (A.state (net K (S1 False a j b)) (2 * q * t) b)
      ((net K (S1 False a j b)).loc (2 * q * t + 1) b) a)

end Defs

variable {K : Fin t → Fin q → V} {O : Type} (A : Algorithm V M O)

lemma inK_eq {x y x' y' z : V} {i : Fin t} (h : col16 K A x y i = col16 K A x' y' i)
    {k : ℕ} (hk : k ≤ 2 * q * t) (p : Fin q) (hz : (z = x ∧ z = x') ∨ (z = y ∧ z = y')) :
    inK K A x i y z k p = inK K A x' i y' z k p := by
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact congrFun (congrFun (congrArg Prod.fst h) ⟨k, by omega⟩) p
  · exact congrFun (congrFun (congrArg (fun z => z.2.1) h) ⟨k, by omega⟩) p

/-- **`K^i` cannot distinguish (S1) and (S4)** (uses the colours of `(a, c)` and `(c, b)`). -/
lemma K_state_S4 (hK : KInj K) {a b c : V} {i : Fin t} (ha : ¬ IsK K a) (hb : ¬ IsK K b)
    (hc : ¬ IsK K c) (hdist : [a, b, c].Nodup) (h1 : col16 K A a c i = col16 K A a b i)
    (h2 : col16 K A c b i = col16 K A a b i) (p : Fin q) :
    A.state (net K (S4 a i b c)) (2 * q * t + 1) (K i p) =
      A.state (net K (S1 False a i b)) (2 * q * t + 1) (K i p) := by
  have hd' := hdist
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨hab, hac⟩, hbc⟩ := hd'
  have hw4 := wf_S4 (i := i) ha hb hc hab
  have hw1 := wf_S1 (full := False) (i := i) ha hb hab
  have hwac := wf_S1 (full := False) (i := i) ha hc hac
  have hwcb := wf_S1 (full := False) (i := i) hc hb (Ne.symm hbc)
  have hc4 : (S4 a i b c).cr i = some (a, b) := by simp [S4, crOne]
  have hc1 : (S1 False a i b).cr i = some (a, b) := by simp [S1, crOne]
  have hcac : (S1 False a i c).cr i = some (a, c) := by simp [S1, crOne]
  have hccb : (S1 False c i b).cr i = some (c, b) := by simp [S1, crOne]
  have hadj : ∀ k u, (net K (S4 a i b c)).adj k u (K i p) ↔ (net K (S1 False a i b)).adj k u (K i p) :=
    fun k u => K_adj hK hw4 hw1 hc4 hc1 k u p
  refine A.state_eq_of_msgs (g0_eq hK hw4 hw1 Iff.rfl) (K i p) _
    (fun k _ => loc_eq_of_adj (sp := S4 a i b c) (sp' := S1 False a i b) Iff.rfl k _ (hadj k))
    (fun k _ => hadj k) (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_K_iff hK hw4, hc4] at hu0
  have hucomp : Comp K i a b u := by
    rcases hu0 with ⟨p', -, rfl⟩ | ⟨x, y, he, h | h⟩
    · exact Or.inr (Or.inr ⟨p', rfl⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he); exact Or.inl h.1
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj he); exact Or.inr (Or.inl h.1)
  by_cases hkR : k + 1 ≤ 2 * q * t
  · exact comp_send A hK hw4 hw1 Iff.rfl hc4 hc1 hkR hucomp _
  have hk' : k = 2 * q * t := by omega
  subst hk'
  rcases hucomp with rfl | rfl | ⟨p', rfl⟩
  · -- the message from `a`
    have hl : (net K (S4 u i b c)).loc (2 * q * t + 1) u = (net K (S1 False u i c)).loc (2 * q * t + 1) u := by
      refine loc_eq_of_adj (sp := S4 u i b c) (sp' := S1 False u i c) Iff.rfl _ _ (fun v => ?_)
      rw [adj_fst_iff hw4 hc4, adj_fst_iff hwac hcac]
      simp only [S4, S1]
      constructor
      · rintro (h | ⟨h1, h2, h3⟩)
        · exact Or.inl h
        · refine Or.inr ⟨h1, h2, ?_⟩
          rcases h3 with (⟨-, h⟩ | ⟨-, h⟩) | (⟨-, h⟩ | ⟨h, h'⟩)
          · exact absurd h hac
          · exact absurd h hac
          · exact Or.inr ⟨trivial, h⟩
          · exact absurd h hab
      · rintro (h | ⟨h1, h2, ⟨-, h⟩ | ⟨-, h⟩⟩)
        · exact Or.inl h
        · exact absurd h hac
        · exact Or.inr ⟨h1, h2, Or.inr (Or.inl ⟨trivial, h⟩)⟩
    have hs : A.state (net K (S1 False u i b)) (2 * q * t) u =
        A.state (net K (S1 False u i c)) (2 * q * t) u :=
      state_fst_of_msgs A hK hw1 hwac Iff.rfl hc1 hcac le_rfl
        (fun k hk p => (inK_eq A h1 (by omega) p (Or.inl ⟨rfl, rfl⟩)).symm)
    rw [comp_state A hK hw4 hw1 Iff.rfl hc4 hc1 le_rfl _ (Or.inl rfl), hl]
    refine Eq.trans (by rw [hs]) ?_
    have hadj1 : (net K (S1 False u i c)).adj (2 * q * t + 1) u (K i p) :=
      (net K _).symm _ _ _ ((adj_fst_iff hwac hcac _ _).2
        (Or.inl ⟨p, rfl, by have := ct_le i.2 zero_le_one p.2 (q := q); omega⟩))
    have hadj2 : (net K (S1 False u i b)).adj (2 * q * t + 1) u (K i p) :=
      (net K _).symm _ _ _ ((adj_fst_iff hw1 hc1 _ _).2
        (Or.inl ⟨p, rfl, by have := ct_le i.2 zero_le_one p.2 (q := q); omega⟩))
    exact send_eq_of_inbox_eq' A hadj1 hadj2
      (congrFun (congrArg (fun z => z.2.2.1) h1) p)
  · -- the message from `b`
    have hl : (net K (S4 a i u c)).loc (2 * q * t + 1) u = (net K (S1 False c i u)).loc (2 * q * t + 1) u := by
      refine loc_eq_of_adj (sp := S4 a i u c) (sp' := S1 False c i u) Iff.rfl _ _ (fun v => ?_)
      rw [adj_snd_iff hw4 hc4, adj_snd_iff hwcb hccb]
      simp only [S4, S1]
      constructor
      · rintro (h | ⟨h1, h2, h3⟩)
        · exact Or.inl h
        · refine Or.inr ⟨h1, h2, ?_⟩
          rcases h3 with (⟨-, h⟩ | ⟨-, h⟩) | (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h hbc
          · exact absurd h hbc
          · exact absurd h.symm hab
          · exact Or.inl ⟨h, trivial⟩
      · rintro (h | ⟨h1, h2, ⟨h, -⟩ | ⟨h, -⟩⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, h2, Or.inr (Or.inr ⟨trivial, h⟩)⟩
        · exact absurd h hbc
    have hs : A.state (net K (S1 False a i u)) (2 * q * t) u =
        A.state (net K (S1 False c i u)) (2 * q * t) u :=
      state_snd_of_msgs A hK hw1 hwcb Iff.rfl hc1 hccb le_rfl
        (fun k hk p => (inK_eq A h2 (by omega) p (Or.inr ⟨rfl, rfl⟩)).symm)
    rw [comp_state A hK hw4 hw1 Iff.rfl hc4 hc1 le_rfl _ (Or.inr (Or.inl rfl)), hl]
    refine Eq.trans (by rw [hs]) ?_
    have hadj1 : (net K (S1 False c i u)).adj (2 * q * t + 1) u (K i p) :=
      (net K _).symm _ _ _ ((adj_snd_iff hwcb hccb _ _).2
        (Or.inl ⟨p, rfl, by have := ct_le i.2 le_rfl p.2 (q := q); omega⟩))
    have hadj2 : (net K (S1 False a i u)).adj (2 * q * t + 1) u (K i p) :=
      (net K _).symm _ _ _ ((adj_snd_iff hw1 hc1 _ _).2
        (Or.inl ⟨p, rfl, by have := ct_le i.2 le_rfl p.2 (q := q); omega⟩))
    exact send_eq_of_inbox_eq' A hadj1 hadj2
      (congrFun (congrArg (fun z => z.2.2.2) h2) p)
  · exact K_send_T A hK hw4 hw1 Iff.rfl hc4 hc1 p' _

/-- **`a` cannot distinguish (S1) and (S2)** (node-insertion model). -/
lemma a_state_S2F (hK : KInj K) {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup)
    (h1 : col16 K A a c i = col16 K A a b i) (h2 : col16 K A d b i' = col16 K A a b i')
    (hm : (msgs16 K A a b i).2 = (msgs16 K A a b i').2) :
    A.state (net K (S2 False a i c d i' b)) (2 * q * t + 1) a =
      A.state (net K (S1 False a i b)) (2 * q * t + 1) a := by
  have hd' := hdist
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hd'
  have hw := wf_S2 (full := False) hii ha hb hc hd hdist
  have hw1 := wf_S1 (full := False) (i := i) ha hb hab
  have hwc := wf_S1 (full := False) (i := i) ha hc hac
  have hwd := wf_S1 (full := False) (i := i') hd hb (Ne.symm hbd)
  have hwa' := wf_S1 (full := False) (i := i') ha hb hab
  have hci : (S2 False a i c d i' b).cr i = some (a, c) := by simp [S2, crTwo]
  have hci' : (S2 False a i c d i' b).cr i' = some (d, b) := by simp [S2, crTwo, Ne.symm hii]
  have hc1 : (S1 False a i b).cr i = some (a, b) := by simp [S1, crOne]
  have hcc : (S1 False a i c).cr i = some (a, c) := by simp [S1, crOne]
  have hcd : (S1 False d i' b).cr i' = some (d, b) := by simp [S1, crOne]
  have hca : (S1 False a i' b).cr i' = some (a, b) := by simp [S1, crOne]
  have hadj : ∀ k ≤ 2 * q * t + 1, ∀ u,
      (net K (S2 False a i c d i' b)).adj k u a ↔ (net K (S1 False a i b)).adj k u a := by
    intro k _ u
    rw [adj_fst_iff hw hci, adj_fst_iff hw1 hc1]
    exact Iff.rfl
  refine A.state_eq_of_msgs (g0_eq hK hw hw1 Iff.rfl) a _
    (fun k hk => loc_eq_of_adj (sp := S2 False a i c d i' b) (sp' := S1 False a i b) Iff.rfl k a
      (hadj k hk)) hadj (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_fst_iff hw hci] at hu0
  rcases hu0 with ⟨p, rfl, -⟩ | ⟨hne, h1', hf⟩
  · -- a message from the clique `K^i`
    have hk : k ≤ 2 * q * t := by omega
    have e1 : A.send (k + 1) (A.state (net K (S2 False a i c d i' b)) k (K i p))
        ((net K (S2 False a i c d i' b)).loc (k + 1) (K i p)) a =
        A.send (k + 1) (A.state (net K (S1 False a i c)) k (K i p))
        ((net K (S1 False a i c)).loc (k + 1) (K i p)) a := by
      rw [comp_state A hK hw hwc Iff.rfl hci hcc hk _ (Or.inr (Or.inr ⟨p, rfl⟩)),
        loc_eq_of_adj (sp := S2 False a i c d i' b) (sp' := S1 False a i c) Iff.rfl _ _
          (fun u => K_adj hK hw hwc hci hcc _ u p)]
    have hu1 : (net K (S1 False a i c)).adj (k + 1) (K i p) a := by
      rw [adj_fst_iff hwc hcc]; rw [adj_fst_iff hw hci] at hu
      rcases hu with h | ⟨-, -, h | h⟩
      · exact Or.inl h
      · exact absurd h.2 hab
      · exact absurd ⟨i, p, h.2⟩ hb
    rw [e1]
    exact send_eq_of_inbox_eq' A hu1 ((hadj (k + 1) (by omega) _).1 hu)
      (inK_eq A h1 hk p (Or.inl ⟨rfl, rfl⟩))
  · -- the message from `b` in round `T`
    have hkR : k = 2 * q * t := by omega
    subst hkR
    have hub : u = b := by
      rcases hf with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact absurd rfl hne
      · rfl
    subst hub
    have hlocb : (net K (S2 False a i c d i' u)).loc (2 * q * t + 1) u =
        (net K (S1 False a i' u)).loc (2 * q * t + 1) u := by
      refine loc_eq_of_adj (sp := S2 False a i c d i' u) (sp' := S1 False a i' u) Iff.rfl _ _
        (fun v => ?_)
      rw [adj_snd_iff hw hci', adj_snd_iff hwa' hca]
      exact Iff.rfl
    have hsb : A.state (net K (S1 False d i' u)) (2 * q * t) u =
        A.state (net K (S1 False a i' u)) (2 * q * t) u :=
      state_snd_of_msgs A hK hwd hwa' Iff.rfl hcd hca le_rfl
        (fun k hk p => inK_eq A h2 (by omega) p (Or.inr ⟨rfl, rfl⟩))
    rw [comp_state A hK hw hwd Iff.rfl hci' hcd le_rfl _ (Or.inr (Or.inl rfl)), hlocb, hsb]
    exact hm.symm

/-- **`b` cannot distinguish (S1) and (S3)** (node-insertion model). -/
lemma b_state_S3F (hK : KInj K) {a b c d : V} {i i' : Fin t} (hii : i ≠ i') (ha : ¬ IsK K a)
    (hb : ¬ IsK K b) (hc : ¬ IsK K c) (hd : ¬ IsK K d) (hdist : [a, b, c, d].Nodup)
    (h1 : col16 K A d b i = col16 K A a b i) (h2 : col16 K A a c i' = col16 K A a b i')
    (hm : (msgs16 K A a b i).1 = (msgs16 K A a b i').1) :
    A.state (net K (S3 False a i c d i' b)) (2 * q * t + 1) b =
      A.state (net K (S1 False a i b)) (2 * q * t + 1) b := by
  have hd' := hdist
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨hab, hac, had⟩, ⟨hbc, hbd⟩, hcd⟩ := hd'
  have hw := wf_S3 (full := False) hii ha hb hc hd hdist
  have hw1 := wf_S1 (full := False) (i := i) ha hb hab
  have hwd := wf_S1 (full := False) (i := i) hd hb (Ne.symm hbd)
  have hwc := wf_S1 (full := False) (i := i') ha hc hac
  have hwa' := wf_S1 (full := False) (i := i') ha hb hab
  have hci : (S3 False a i c d i' b).cr i = some (d, b) := by simp [S3, crTwo]
  have hci' : (S3 False a i c d i' b).cr i' = some (a, c) := by simp [S3, crTwo, Ne.symm hii]
  have hc1 : (S1 False a i b).cr i = some (a, b) := by simp [S1, crOne]
  have hcd : (S1 False d i b).cr i = some (d, b) := by simp [S1, crOne]
  have hcc : (S1 False a i' c).cr i' = some (a, c) := by simp [S1, crOne]
  have hca : (S1 False a i' b).cr i' = some (a, b) := by simp [S1, crOne]
  have hadj : ∀ k ≤ 2 * q * t + 1, ∀ u,
      (net K (S3 False a i c d i' b)).adj k u b ↔ (net K (S1 False a i b)).adj k u b := by
    intro k _ u
    rw [adj_snd_iff hw hci, adj_snd_iff hw1 hc1]
    exact Iff.rfl
  refine A.state_eq_of_msgs (g0_eq hK hw hw1 Iff.rfl) b _
    (fun k hk => loc_eq_of_adj (sp := S3 False a i c d i' b) (sp' := S1 False a i b) Iff.rfl k b
      (hadj k hk)) hadj (fun k hk u hu => ?_)
  have hu0 := hu
  rw [adj_snd_iff hw hci] at hu0
  rcases hu0 with ⟨p, rfl, -⟩ | ⟨hne, h1', hf⟩
  · -- a message from the clique `K^i`
    have hk : k ≤ 2 * q * t := by omega
    have e1 : A.send (k + 1) (A.state (net K (S3 False a i c d i' b)) k (K i p))
        ((net K (S3 False a i c d i' b)).loc (k + 1) (K i p)) b =
        A.send (k + 1) (A.state (net K (S1 False d i b)) k (K i p))
        ((net K (S1 False d i b)).loc (k + 1) (K i p)) b := by
      rw [comp_state A hK hw hwd Iff.rfl hci hcd hk _ (Or.inr (Or.inr ⟨p, rfl⟩)),
        loc_eq_of_adj (sp := S3 False a i c d i' b) (sp' := S1 False d i b) Iff.rfl _ _
          (fun u => K_adj hK hw hwd hci hcd _ u p)]
    have hu1 : (net K (S1 False d i b)).adj (k + 1) (K i p) b := by
      rw [adj_snd_iff hwd hcd]; rw [adj_snd_iff hw hci] at hu
      rcases hu with h | ⟨-, -, h | h⟩
      · exact Or.inl h
      · exact absurd ⟨i, p, h.1⟩ ha
      · exact absurd h.1 (Ne.symm hab)
    rw [e1]
    exact send_eq_of_inbox_eq' A hu1 ((hadj (k + 1) (by omega) _).1 hu)
      (inK_eq A h1 hk p (Or.inr ⟨rfl, rfl⟩))
  · -- the message from `a` in round `T`
    have hkR : k = 2 * q * t := by omega
    subst hkR
    have hua : u = a := by
      rcases hf with ⟨rfl, -⟩ | ⟨h, -⟩
      · rfl
      · exact absurd h.symm hab
    subst hua
    have hloca : (net K (S3 False u i c d i' b)).loc (2 * q * t + 1) u =
        (net K (S1 False u i' b)).loc (2 * q * t + 1) u := by
      refine loc_eq_of_adj (sp := S3 False u i c d i' b) (sp' := S1 False u i' b) Iff.rfl _ _
        (fun v => ?_)
      rw [adj_fst_iff hw hci', adj_fst_iff hwa' hca]
      exact Iff.rfl
    have hsa : A.state (net K (S1 False u i' c)) (2 * q * t) u =
        A.state (net K (S1 False u i' b)) (2 * q * t) u :=
      state_fst_of_msgs A hK hwc hwa' Iff.rfl hcc hca le_rfl
        (fun k hk p => inK_eq A h2 (by omega) p (Or.inl ⟨rfl, rfl⟩))
    rw [comp_state A hK hw hwc Iff.rfl hci' hcc le_rfl _ (Or.inl rfl), hloca, hsa]
    exact hm.symm

/-- The present non-clique nodes of (S1) at `t_final` are `a` and `b`. -/
lemma pres_S1F {a b v : V} {i : Fin t} (ha : ¬ IsK K a) (hb : ¬ IsK K b) (hab : a ≠ b)
    (hv : ¬ IsK K v) {r : ℕ} (h : (net K (S1 False a i b)).pres r v) : v = a ∨ v = b := by
  rcases h with h | h | ⟨u, hu⟩
  · exact h.elim
  · exact absurd h hv
  · change (net K _).adj _ u v at hu
    rw [adj_I_iff _ _ _ hv] at hu
    rcases hu with ⟨j, x, y, k, hj, -, h | h⟩ | ⟨-, -, h | h⟩
    · obtain ⟨-, rfl, -⟩ := crOne_eq_some hj; exact Or.inl h.1
    · obtain ⟨-, -, rfl⟩ := crOne_eq_some hj; exact Or.inr h.1
    · exact Or.inr h.2
    · exact Or.inl h.1

/-- **Theorem 1.6, finite form.** With `X ≥` the number of colours, `|I| ≥ gSel X (2X + 1)`
(Lemma 4.4) and `|M|² < t` (Lemma 4.5), no algorithm with message alphabet `M` solves one-round
`Detect(K_{q+2})` under node and edge insertions, even on networks of maximum degree `q + 1`. -/
theorem not_solves_16 [Fintype V] [Fintype M] (hK : KInj K) (hq : 1 ≤ q)
    (A : Algorithm V M Bool) (I : Finset V) (hI : ∀ v ∈ I, ¬ IsK K v) (X : ℕ)
    (hX : Fintype.card (Fin t → (Fin (2 * q * t + 1) → Fin q → Option M) ×
      (Fin (2 * q * t + 1) → Fin q → Option M) × (Fin q → Option M) × (Fin q → Option M)) ≤ X)
    (hIX : gSel X (2 * X + 1) ≤ I.card) (h5 : Fintype.card M * Fintype.card M < t) :
    ¬ Solves A InsNet.NodeEdgeIns (q + 1) (DetectOK (q + 2)) := by
  intro hA
  obtain ⟨a, haI, b, hbI, c, hcI, d, hdI, hdist, hac, -, hcb, hdb⟩ :=
    lemma_4_4 (col16 K A) X hX I hIX
  obtain ⟨i, i', hii, hm⟩ := Fintype.exists_ne_map_eq_of_card_lt (msgs16 K A a b)
    (by simpa [Fintype.card_prod] using h5)
  have ha := hI a haI
  have hb := hI b hbI
  have hc := hI c hcI
  have hd := hI d hdI
  have hd' := hdist
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at hd'
  obtain ⟨⟨hab, hac', had⟩, ⟨hbc, hbd⟩, hcd⟩ := hd'
  have hdist3 : [a, b, c].Nodup := by simp; tauto
  -- (S1) contains an `s`-clique, so some present node outputs `true`
  have hS1 := hA _ (nodeEdgeIns_S1 (i := i) hK hq ha hb hab) (degLE_S1 hK ha hb hab)
    (2 * q * t + 1)
  obtain ⟨v, hvp, hv⟩ := hS1.1 ⟨_, clique_S1 hK ha hb hab⟩
  unfold Algorithm.output at hv
  by_cases hvK : IsK K v
  · -- a clique node: (S4) has no `s`-clique
    obtain ⟨j, p, rfl⟩ := hvK
    have hS4 := hA _ (nodeEdgeIns_S4 (i := i) hK hq ha hb hc hdist3)
      (degLE_S4 hK hq ha hb hc hdist3) (2 * q * t + 1)
    have hst : A.state (net K (S4 a i b c)) (2 * q * t + 1) (K j p) =
        A.state (net K (S1 False a i b)) (2 * q * t + 1) (K j p) := by
      by_cases hj : j = i
      · subst hj
        exact K_state_S4 A hK ha hb hc hdist3 (congrFun hac j) (congrFun hcb j) p
      · exact K_state_none A hK (wf_S4 ha hb hc hab) (wf_S1 ha hb hab) Iff.rfl
          (by simp [S4, crOne, hj]) (by simp [S1, crOne, hj]) _ p
    obtain ⟨Q, hQ⟩ := hS4.2 ⟨K j p, pres_K ⟨j, p, rfl⟩, by unfold Algorithm.output; rw [hst]; exact hv⟩
    exact no_clique_S4 hK hq ha hb hc hdist3 _ Q hQ
  rcases pres_S1F ha hb hab hvK hvp with rfl | rfl
  · -- `v = a`: (S2)
    have hS2 := hA _ (nodeEdgeIns_S2 hK hq hii ha hb hc hd hdist)
      (degLE_S2 hK hii ha hb hc hd hdist) (2 * q * t + 1)
    have hw := wf_S2 (full := False) hii ha hb hc hd hdist
    have hpres : (net K (S2 False v i c d i' b)).pres (2 * q * t + 1) v :=
      (net K _).pres_mono _ _ (pres_of_cr hK hw hq (show (S2 False v i c d i' b).cr i = some (v, c)
        by simp [S2, crTwo]) (Or.inl rfl))
    obtain ⟨Q, hQ⟩ := hS2.2 ⟨v, hpres, by
      unfold Algorithm.output
      rw [a_state_S2F A hK hii ha hb hc hd hdist (congrFun hac i) (congrFun hdb i')
        (congrArg Prod.snd hm)]
      exact hv⟩
    exact no_clique_S2 hK hq hii ha hb hc hd hdist _ Q hQ
  · -- `v = b`: (S3)
    have hS3 := hA _ (nodeEdgeIns_S3 hK hq hii ha hb hc hd hdist)
      (degLE_S3 hK hii ha hb hc hd hdist) (2 * q * t + 1)
    have hw := wf_S3 (full := False) hii ha hb hc hd hdist
    have hpres : (net K (S3 False a i c d i' v)).pres (2 * q * t + 1) v :=
      (net K _).pres_mono _ _ (pres_of_cr hK hw hq (show (S3 False a i c d i' v).cr i = some (d, v)
        by simp [S3, crTwo]) (Or.inr rfl))
    obtain ⟨Q, hQ⟩ := hS3.2 ⟨v, hpres, by
      unfold Algorithm.output
      rw [b_state_S3F A hK hii ha hb hc hd hdist (congrFun hdb i) (congrFun hac i')
        (congrArg Prod.fst hm)]
      exact hv⟩
    exact no_clique_S3 hK hq hii ha hb hc hd hdist _ Q hQ

end Hard

/-! ### The asymptotic statement -/

/-- From `B < (1/16) log₂ log₂ log₂ n` to `2^{16B} ≤ ⌊log₂ ⌊log₂ n⌋⌋`. -/
lemma pow_le_loglog_of_lt {n B : ℕ} (hn : 4 < n)
    (h : (B : ℝ) < (1 / 16 : ℝ) * Real.logb 2 (Real.logb 2 (Real.logb 2 n))) :
    2 ^ (16 * B) ≤ Nat.log 2 (Nat.log 2 n) := by
  have hn' : (4 : ℝ) < n := by exact_mod_cast hn
  have hx : 2 < Real.logb 2 n := by
    rw [Real.lt_logb_iff_rpow_lt one_lt_two (by linarith)]
    norm_num; linarith
  have hy : 0 < Real.logb 2 (Real.logb 2 n) := Real.logb_pos one_lt_two (by linarith)
  have h1 : ((16 * B : ℕ) : ℝ) < Real.logb 2 (Real.logb 2 (Real.logb 2 n)) := by
    push_cast; linarith
  rw [Real.lt_logb_iff_rpow_lt one_lt_two hy, Real.rpow_natCast] at h1
  have h2 : (((2 ^ (16 * B) : ℕ) : ℝ)) < Real.logb 2 (Real.logb 2 n) := by exact_mod_cast h1
  rw [Real.lt_logb_iff_rpow_lt one_lt_two (by linarith), Real.rpow_natCast] at h2
  have h3 : (((2 ^ (2 ^ (16 * B)) : ℕ) : ℝ)) < Real.logb 2 n := by exact_mod_cast h2
  rw [Real.lt_logb_iff_rpow_lt one_lt_two (by linarith), Real.rpow_natCast] at h3
  have h4 : 2 ^ (2 ^ (2 ^ (16 * B))) < n := by exact_mod_cast h3
  exact Nat.le_log_of_pow_le one_lt_two (Nat.le_log_of_pow_le one_lt_two h4.le)

/-- **Theorem 1.6.** For every `s ≥ 3`, the one-round bandwidth complexity of `Detect(K_s)` under
node insertions and edge insertions is `Ω(log log log n)`, even in dynamic networks of maximum
degree `s - 1`: for all large `n`, every one-round algorithm on identifiers `[n]` whose messages
take at most `2^B` values satisfies `B ≥ (1/16) log₂ log₂ log₂ n`. -/
theorem theorem_1_6 (s : ℕ) (hs : 3 ≤ s) : ∃ N : ℕ, ∀ n ≥ N, ∀ (M : Type) [Fintype M] (B : ℕ),
    Fintype.card M ≤ 2 ^ B → ∀ A : Algorithm (Fin n) M Bool,
    Solves A InsNet.NodeEdgeIns (s - 1) (DetectOK s) →
    (1 / 16 : ℝ) * Real.logb 2 (Real.logb 2 (Real.logb 2 n)) ≤ B := by
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  have hq : 1 ≤ q := by omega
  refine ⟨2 ^ (2 ^ ((304 * q ^ 2) ^ 4)) + 5, fun n hn M _ B hM A hA => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hn4 : 4 < n := by
    have : 1 ≤ 2 ^ (2 ^ ((304 * q ^ 2) ^ 4)) := Nat.one_le_two_pow
    omega
  have hLL1 : 2 ^ (16 * B) ≤ Nat.log 2 (Nat.log 2 n) := pow_le_loglog_of_lt hn4 (by exact_mod_cast hlt)
  have hLL2 : (304 * q ^ 2) ^ 4 ≤ Nat.log 2 (Nat.log 2 n) := by
    apply Nat.le_log_of_pow_le one_lt_two
    apply Nat.le_log_of_pow_le one_lt_two
    omega
  have hkey := key_bound16 q B _ hLL1 hLL2
  set W := 2 ^ (B + 1) with hW
  have hW2 : 2 ≤ W := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ W := Nat.pow_le_pow_right (by norm_num) (by omega)
  set t := W ^ 2 with ht
  have ht4 : t = 4 ^ (B + 1) := by rw [ht, hW, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num,
    ← pow_mul, mul_comm]
  set R := 2 * q * t with hR
  set Y := t * (2 * (q * (R + 1)) + 2 * q) with hY
  set m := Fintype.card M
  have hmW : m + 1 ≤ W := by
    have : 2 ^ B < W := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  set X := Fintype.card (Fin t → (Fin (R + 1) → Fin q → Option M) ×
      (Fin (R + 1) → Fin q → Option M) × (Fin q → Option M) × (Fin q → Option M)) with hXdef
  have hXY : X ≤ W ^ Y := by
    rw [hXdef]
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    calc (((m + 1) ^ q) ^ (R + 1) * (((m + 1) ^ q) ^ (R + 1) * ((m + 1) ^ q * (m + 1) ^ q))) ^ t
        ≤ ((W ^ q) ^ (R + 1) * ((W ^ q) ^ (R + 1) * (W ^ q * W ^ q))) ^ t := by gcongr
      _ = W ^ Y := pow_combo W q R t
  have hm2 : m * m < t := by
    have : m * m ≤ 2 ^ B * 2 ^ B := Nat.mul_le_mul hM hM
    have h4 : 2 ^ B * 2 ^ B < t := by
      rw [ht4, ← pow_add, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have ht4' : 4 ≤ t := by
    rw [ht4]
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- the size condition of Lemma 4.4
  set G := (B + 1) * (Y + 1) with hG
  have hG2 : 2 * G + 1 ≤ Nat.log 2 (Nat.log 2 n) := by
    refine le_trans ?_ hkey
    rw [← ht4]
    exact G_bound q t B hq ht4'
  have hX1 : X + 1 ≤ 2 ^ G := by
    have e : W ^ Y = 2 ^ ((B + 1) * Y) := by rw [hW, ← pow_mul]
    have h2 : 2 ^ ((B + 1) * Y) < 2 ^ G :=
      Nat.pow_lt_pow_right (by norm_num) (by rw [hG]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega))
    omega
  have htqY : t * q ≤ 2 ^ G := by
    have h1 : t * q ≤ Y := by
      rw [hY]
      exact Nat.mul_le_mul_left _ (by omega)
    have h2 : Y < 2 ^ G := lt_of_le_of_lt (by rw [hG]; nlinarith) Nat.lt_two_pow_self
    omega
  have hn' : 2 ^ (2 ^ (2 * G + 1)) ≤ n := by
    have hL2 : 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le one_lt_two (by omega)
    have h1 : 2 ^ (2 * G + 1) ≤ Nat.log 2 n :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hG2) (Nat.pow_log_le_self 2 (by omega))
    exact le_trans (Nat.pow_le_pow_right (by norm_num) h1) (Nat.pow_log_le_self 2 (by omega))
  have hgsel : gSel X (2 * X + 1) + t * q < n :=
    lt_of_le_of_lt (Nat.add_le_add_right (gSel_le X _) _) (size_bound X G (t * q) n hX1 htqY hn')
  have htq : t * q ≤ n := by omega
  have hI := card_I_ge htq
  exact Hard.not_solves_16 (blockK_inj htq) hq A
    (Finset.univ.filter (fun v => ¬ Hard.IsK (blockK n q t htq) v))
    (fun v hv => (Finset.mem_filter.mp hv).2) X le_rfl (by omega) hm2 hA

end Podc.DynamicSubgraphFinding
