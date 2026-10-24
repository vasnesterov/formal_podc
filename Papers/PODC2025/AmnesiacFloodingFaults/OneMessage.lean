import Papers.PODC2025.AmnesiacFloodingFaults.Balance

/-!
# Adding or removing one message on a cycle or on the path of a faux-even cycle

If `S` is balanced along a cycle containing the edge `uv`, then `S \ {(u,v)}` (if `(u,v) ∈ S`) and
`S ∪ {(u,v)}` (if `(u,v) ∉ S`) are not: the flow around the cycle changes by `±1`. If `uv` lies on
the path of a faux-even cycle `F`, the alternating occupancy of `F.walk` changes by `±2`. These are
the imbalance arguments behind Theorems 5.6, 5.7 and 5.8 ("the dropping of the message must produce
an imbalance").
-/

namespace AmnesiacFloodingFaults

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-! ### Elementary identities for `walkFlow` and `walkSig` -/

lemma aux_walkFlow_sub (g₁ g₂ : V → V → ℤ) {u v : V} (p : G.Walk u v) :
    walkFlow g₁ p - walkFlow g₂ p = walkFlow (fun x y => g₁ x y - g₂ x y) p := by
  induction p with
  | nil => simp [walkFlow]
  | cons h p ih => simp only [walkFlow, ← ih]; ring

lemma aux_walkFlow_neg (g : V → V → ℤ) {u v : V} (p : G.Walk u v) :
    walkFlow (fun x y => - g x y) p = - walkFlow g p := by
  induction p with
  | nil => simp [walkFlow]
  | cons h p ih => simp only [walkFlow, ih]; ring

lemma aux_walkSig_sub (o₁ o₂ : V → V → ℤ) {u v : V} (p : G.Walk u v) :
    walkSig o₁ p - walkSig o₂ p = walkSig (fun x y => o₁ x y - o₂ x y) p := by
  induction p with
  | nil => simp [walkSig]
  | cons h p ih => simp only [walkSig, ← ih]; ring

lemma aux_walkSig_append (o : V → V → ℤ) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkSig o (p.append q) = walkSig o p + (-1) ^ p.length * walkSig o q := by
  induction p with
  | nil => simp [walkSig]
  | cons h p ih =>
    rw [Walk.cons_append, walkSig, walkSig, ih, Walk.length_cons, pow_succ]; ring

lemma aux_walkSig_reverse (o : V → V → ℤ) (ho : ∀ x y, o x y = o y x) {u v : V}
    (p : G.Walk u v) : walkSig o p.reverse = - (-1) ^ p.length * walkSig o p := by
  induction p with
  | nil => simp [walkSig]
  | cons h p ih =>
    rw [Walk.reverse_cons, ← Walk.concat_eq_append, walkSig_concat_aux, ih, Walk.length_cons,
      Walk.length_reverse, walkSig, ho]
    rw [pow_succ]; ring_nf

/-! ### The effect of one message -/

/-- Change of the antisymmetric weight when the message `m` is added. -/
noncomputable def δf (m : V × V) (x y : V) : ℤ := ind ((x, y) = m) - ind ((y, x) = m)

/-- Change of the symmetric weight when the message `m` is added. -/
noncomputable def δo (m : V × V) (x y : V) : ℤ := ind ((x, y) = m) + ind ((y, x) = m)

lemma gS_sdiff (S : Config V) {m : V × V} (hm : m ∈ S) (x y : V) :
    gS S x y - gS (S \ {m}) x y = δf m x y := by
  have key : ∀ e : V × V, ind (e ∈ S) - ind (e ∈ S \ {m}) = ind (e = m) := by
    intro e
    by_cases he : e = m
    · subst he; rw [ind_of hm, ind_of_not (fun h => h.2 rfl), ind_of rfl]; norm_num
    · rw [ind_of_not he, ind_congr (show e ∈ S \ {m} ↔ e ∈ S by simp [he])]; ring
  unfold gS δf
  have h1 := key (x, y); have h2 := key (y, x)
  linarith

lemma oS_sdiff (S : Config V) {m : V × V} (hm : m ∈ S) (x y : V) :
    oS S x y - oS (S \ {m}) x y = δo m x y := by
  have key : ∀ e : V × V, ind (e ∈ S) - ind (e ∈ S \ {m}) = ind (e = m) := by
    intro e
    by_cases he : e = m
    · subst he; rw [ind_of hm, ind_of_not (fun h => h.2 rfl), ind_of rfl]; norm_num
    · rw [ind_of_not he, ind_congr (show e ∈ S \ {m} ↔ e ∈ S by simp [he])]; ring
  unfold oS δo
  have h1 := key (x, y); have h2 := key (y, x)
  linarith

lemma gS_union (S : Config V) {m : V × V} (hm : m ∉ S) (x y : V) :
    gS (S ∪ {m}) x y - gS S x y = δf m x y := by
  have := gS_sdiff (S ∪ {m}) (m := m) (by simp) x y
  have e : (S ∪ {m}) \ {m} = S := by
    ext e; by_cases he : e = m <;> simp_all
  rwa [e] at this

lemma oS_union (S : Config V) {m : V × V} (hm : m ∉ S) (x y : V) :
    oS (S ∪ {m}) x y - oS S x y = δo m x y := by
  have := oS_sdiff (S ∪ {m}) (m := m) (by simp) x y
  have e : (S ∪ {m}) \ {m} = S := by
    ext e; by_cases he : e = m <;> simp_all
  rwa [e] at this

lemma δo_symm (m : V × V) (x y : V) : δo m x y = δo m y x := by unfold δo; ring

lemma ne_pairs {u v x y : V} (h : s(x, y) ≠ s(u, v)) : (x, y) ≠ (u, v) ∧ (y, x) ≠ (u, v) := by
  refine ⟨fun he => ?_, fun he => ?_⟩ <;> cases he
  · exact h rfl
  · exact h Sym2.eq_swap

lemma δf_eq_zero {u v x y : V} (h : s(x, y) ≠ s(u, v)) : δf (u, v) x y = 0 := by
  unfold δf
  rw [ind_of_not (ne_pairs h).1, ind_of_not (ne_pairs h).2]; ring

lemma δo_eq_zero {u v x y : V} (h : s(x, y) ≠ s(u, v)) : δo (u, v) x y = 0 := by
  unfold δo
  rw [ind_of_not (ne_pairs h).1, ind_of_not (ne_pairs h).2]; ring

lemma δf_of_eq {u v x y : V} (huv : u ≠ v) (h : s(x, y) = s(u, v)) :
    δf (u, v) x y = 1 ∨ δf (u, v) x y = -1 := by
  unfold δf
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; rw [ind_of rfl, ind_of_not (by simp [Prod.ext_iff]; tauto)]; norm_num
  · right; rw [ind_of_not (by simp [Prod.ext_iff]; tauto), ind_of rfl]; norm_num

lemma δo_of_eq {u v x y : V} (huv : u ≠ v) (h : s(x, y) = s(u, v)) : δo (u, v) x y = 1 := by
  unfold δo
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [ind_of rfl, ind_of_not (by simp [Prod.ext_iff]; tauto)]; norm_num
  · rw [ind_of_not (by simp [Prod.ext_iff]; tauto), ind_of rfl]; norm_num

lemma walkFlow_δf_of_notMem {u v : V} {a b : V} (p : G.Walk a b) (h : s(u, v) ∉ p.edges) :
    walkFlow (δf (u, v)) p = 0 := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
    simp only [Walk.edges_cons, List.mem_cons, not_or] at h
    rw [walkFlow, δf_eq_zero (Ne.symm h.1), ih h.2]; ring

lemma walkSig_δo_of_notMem {u v : V} {a b : V} (p : G.Walk a b) (h : s(u, v) ∉ p.edges) :
    walkSig (δo (u, v)) p = 0 := by
  induction p with
  | nil => rfl
  | cons hadj p ih =>
    simp only [Walk.edges_cons, List.mem_cons, not_or] at h
    rw [walkSig, δo_eq_zero (Ne.symm h.1), ih h.2]; ring

lemma walkFlow_δf_of_isTrail {u v : V} (huv : u ≠ v) {a b : V} (p : G.Walk a b)
    (hp : p.IsTrail) (h : s(u, v) ∈ p.edges) :
    walkFlow (δf (u, v)) p = 1 ∨ walkFlow (δf (u, v)) p = -1 := by
  induction p with
  | nil => simp at h
  | @cons x y z hadj p ih =>
    rw [Walk.isTrail_cons] at hp
    simp only [Walk.edges_cons, List.mem_cons] at h
    by_cases he : s(x, y) = s(u, v)
    · rw [walkFlow, walkFlow_δf_of_notMem p (he ▸ hp.2), add_zero]
      exact δf_of_eq huv he
    · rw [walkFlow, δf_eq_zero he, zero_add]
      exact ih hp.1 (h.resolve_left (Ne.symm he))

lemma walkSig_δo_of_isTrail {u v : V} (huv : u ≠ v) {a b : V} (p : G.Walk a b)
    (hp : p.IsTrail) (h : s(u, v) ∈ p.edges) :
    walkSig (δo (u, v)) p = 1 ∨ walkSig (δo (u, v)) p = -1 := by
  induction p with
  | nil => simp at h
  | @cons x y z hadj p ih =>
    rw [Walk.isTrail_cons] at hp
    simp only [Walk.edges_cons, List.mem_cons] at h
    by_cases he : s(x, y) = s(u, v)
    · rw [walkSig, walkSig_δo_of_notMem p (he ▸ hp.2), δo_of_eq huv he]; left; norm_num
    · rw [walkSig, δo_eq_zero he, zero_sub]
      rcases ih hp.1 (h.resolve_left (Ne.symm he)) with h1 | h1 <;> rw [h1] <;> simp

/-- The edge `uv` of the path of a faux-even cycle changes the alternating occupancy of its even
cycle representation by `±2`. -/
lemma walkSig_δo_fec {u v : V} (F : FEC G) (he : s(u, v) ∈ F.p.edges) :
    walkSig (δo (u, v)) F.walk = 2 ∨ walkSig (δo (u, v)) F.walk = -2 := by
  have huv : u ≠ v := (F.p.adj_of_mem_edges he).ne
  have hu := F.p.fst_mem_support_of_mem_edges he
  have hv := F.p.snd_mem_support_of_mem_edges he
  have h1 : s(u, v) ∉ F.c₁.edges := by
    intro h
    have := F.inter₁ u hu (F.c₁.fst_mem_support_of_mem_edges h)
    have := F.inter₁ v hv (F.c₁.snd_mem_support_of_mem_edges h)
    exact huv (by simp_all)
  have h2 : s(u, v) ∉ F.c₂.edges := by
    intro h
    have := F.inter₂ u hu (F.c₂.fst_mem_support_of_mem_edges h)
    have := F.inter₂ v hv (F.c₂.snd_mem_support_of_mem_edges h)
    exact huv (by simp_all)
  have hp := walkSig_δo_of_isTrail huv F.p F.isPath.isTrail he
  have hodd2 : ((-1 : ℤ) ^ F.c₂.length) = -1 := F.odd₂.neg_one_pow
  have hsq : ((-1 : ℤ) ^ F.p.length) * (-1) ^ F.p.length = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hc1 : ((-1 : ℤ) ^ F.c₁.length) = -1 := F.odd₁.neg_one_pow
  rw [FEC.walk, aux_walkSig_append, aux_walkSig_append, aux_walkSig_append,
    aux_walkSig_reverse _ (δo_symm _), walkSig_δo_of_notMem _ h1, walkSig_δo_of_notMem _ h2,
    hodd2, hc1]
  rcases hp with hp | hp <;> rw [hp]
  · right; linear_combination (-1 : ℤ) * hsq
  · left; linear_combination hsq

/-! ### Imbalance after adding or removing one message -/

lemma not_balancedAll_of_flow {S S' : Config V} {u : V} (c : G.Walk u u) (hc : c.IsCycle)
    (hS : BalancedAll G S) (hd : walkFlow (gS S) c - walkFlow (gS S') c ≠ 0) :
    ¬ BalancedAll G S' := by
  intro hS'
  have hpos : 0 < c.length := by have := hc.three_le_length; omega
  have : NeZero c.length := ⟨by omega⟩
  have h1 := ((balancedOn_iff S _).1 (hS c.length (toFun c) (isClosedWalk_toFun c hpos))).1
  have h2 := ((balancedOn_iff S' _).1 (hS' c.length (toFun c) (isClosedWalk_toFun c hpos))).1
  rw [flowSum_toFun] at h1 h2
  exact hd (by rw [h1, h2]; ring)

lemma not_balancedAll_of_sig {S S' : Config V} (F : FEC G)
    (hS : BalancedAll G S) (hd : walkSig (oS S) F.walk - walkSig (oS S') F.walk ≠ 0) :
    ¬ BalancedAll G S' := by
  intro hS'
  have hlen : F.walk.length = F.c₁.length + (F.p.length + (F.c₂.length + F.p.length)) := by
    simp [FEC.walk]
  have heven : Even F.walk.length := by
    rw [hlen]
    obtain ⟨a, ha⟩ := F.odd₁; obtain ⟨b, hb⟩ := F.odd₂
    exact ⟨a + b + 1 + F.p.length, by omega⟩
  have hpos : 0 < F.walk.length := by
    rw [hlen]; have := F.odd₁.pos; omega
  have : NeZero F.walk.length := ⟨by omega⟩
  have h1 := ((balancedOn_iff S _).1 (hS _ (toFun F.walk) (isClosedWalk_toFun _ hpos))).2 heven
  have h2 := ((balancedOn_iff S' _).1 (hS' _ (toFun F.walk) (isClosedWalk_toFun _ hpos))).2 heven
  rw [sigSum_toFun] at h1 h2
  exact hd (by rw [h1, h2]; ring)

/-- Removing a message on a cycle edge or on the path of a faux-even cycle from a balanced
configuration produces an imbalanced one. -/
theorem not_balancedAll_sdiff {S : Config V} (hS : BalancedAll G S) {u v : V} (hm : (u, v) ∈ S)
    (hadj : G.Adj u v) (h : ¬ G.IsBridge s(u, v) ∨ ∃ F : FEC G, s(u, v) ∈ F.p.edges) :
    ¬ BalancedAll G (S \ {(u, v)}) := by
  rcases h with h | ⟨F, hF⟩
  · rw [isBridge_iff_forall_cycle_notMem (by simpa using hadj)] at h
    push Not at h
    obtain ⟨x, c, hc, he⟩ := h
    apply not_balancedAll_of_flow c hc hS
    rw [aux_walkFlow_sub]
    simp only [gS_sdiff S hm]
    rcases walkFlow_δf_of_isTrail hadj.ne c hc.isTrail he with h1 | h1 <;> rw [h1] <;> norm_num
  · apply not_balancedAll_of_sig F hS
    rw [aux_walkSig_sub]
    simp only [oS_sdiff S hm]
    rcases walkSig_δo_fec F hF with h1 | h1 <;> rw [h1] <;> norm_num

/-- Adding a message on a cycle edge or on the path of a faux-even cycle to a balanced
configuration produces an imbalanced one. -/
theorem not_balancedAll_union {S : Config V} (hS : BalancedAll G S) {u v : V} (hm : (u, v) ∉ S)
    (hadj : G.Adj u v) (h : ¬ G.IsBridge s(u, v) ∨ ∃ F : FEC G, s(u, v) ∈ F.p.edges) :
    ¬ BalancedAll G (S ∪ {(u, v)}) := by
  rcases h with h | ⟨F, hF⟩
  · rw [isBridge_iff_forall_cycle_notMem (by simpa using hadj)] at h
    push Not at h
    obtain ⟨x, c, hc, he⟩ := h
    apply not_balancedAll_of_flow c hc hS
    rw [aux_walkFlow_sub]
    simp only [fun x y => (show gS S x y - gS (S ∪ {(u, v)}) x y = - δf (u, v) x y by
      linarith [gS_union S hm x y])]
    have := walkFlow_δf_of_isTrail hadj.ne c hc.isTrail he
    have e : walkFlow (fun x y => - δf (u, v) x y) c = - walkFlow (δf (u, v)) c :=
      aux_walkFlow_neg _ c
    rw [e]; rcases this with h1 | h1 <;> rw [h1] <;> norm_num
  · apply not_balancedAll_of_sig F hS
    rw [aux_walkSig_sub]
    have e : walkSig (fun x y => oS S x y - oS (S ∪ {(u, v)}) x y) F.walk =
        - walkSig (δo (u, v)) F.walk := by
      have := aux_walkSig_sub (oS (S ∪ {(u, v)})) (oS S) F.walk
      simp only [oS_union S hm] at this
      rw [← this, ← aux_walkSig_sub]; ring
    rw [e]; rcases walkSig_δo_fec F hF with h1 | h1 <;> rw [h1] <;> norm_num

end AmnesiacFloodingFaults
