import Podc.Computability.Distributed.DistributedAutomata.Fairness

/-!
# Halting acceptance cannot distinguish cyclic graphs (Lemma 3.1)

Czerner, Guttenberg, Helfrich, Esparza, *Decision Power of Weak Asynchronous Models of Distributed
Computing*, PODC 2021 (arXiv:2102.11630v2), Lemma 3.1.

Given graphs `G`, `H` with edges `{u_G, v_G}`, `{u_H, v_H}` on cycles, the paper glues `2g + 1`
copies of `G` and `2h + 1` copies of `H` into a chain `GH`: in every copy the cycle edge is
removed and replaced by an edge to the next copy, and the last copy of `G` is joined to the first
copy of `H`. We use `n = 2T + 1` copies of both graphs (`T` the length of the simulated prefix)
and describe the chain as a "voltage graph" over the disjoint union `X = G ⊕ H`: node `(x, i)`
is adjacent to `(y, i + volt x y)` for every edge `{x, y}` of `X`, where the voltage is `±1` on the
cycle edges and `0` elsewhere, plus the junction edge `(v_G, n - 1) — (u_H, 0)`.

The projection `GH → X` is a local isomorphism away from four special nodes, and the copy index
changes by at most one along an edge, so nodes of the middle copies (index `T`) see, during `T`
steps, exactly what their projections see in `X` (`sim`). The reference run on `X` simulates an
accepting run of `G` and a rejecting run of `H` (interleaved for liberal and exclusive selection,
in lock-step for synchronous selection). With halting acceptance, middle-copy nodes of `G` and of
`H` then stay accepting resp. rejecting forever, so the run is neither accepting nor rejecting,
contradicting the consistency condition.
-/

namespace Podc.WeakAsyncDecisionPower

open Cslib.DistributedAutomata Set

variable {Λ Q : Type*}

section Chain

/-- The data of the chain construction: two labelled graphs with a chosen edge each. -/
structure ChainData (Λ : Type*) where
  G : LGraph Λ
  H : LGraph Λ
  uG : G.V
  vG : G.V
  uH : H.V
  vH : H.V

variable (D : ChainData Λ) (T : ℕ)

/-- The disjoint union `X = G ⊕ H`. -/
abbrev ChainData.X : SimpleGraph (D.G.V ⊕ D.H.V) := D.G.graph ⊕g D.H.graph

open Classical in
/-- Half of the voltage: `1` on the oriented cycle edges `v_G → u_G`, `v_H → u_H`. -/
noncomputable def voltHalf (x y : D.G.V ⊕ D.H.V) : ℤ :=
  if (x = .inl D.vG ∧ y = .inl D.uG) ∨ (x = .inr D.vH ∧ y = .inr D.uH) then 1 else 0

/-- The voltage of the oriented edge `x → y` (antisymmetric by construction). -/
noncomputable def volt (x y : D.G.V ⊕ D.H.V) : ℤ := voltHalf D x y - voltHalf D y x

/-- Nodes of the chain: `2T + 1` copies of `G ⊕ H`. -/
abbrev CNode := (D.G.V ⊕ D.H.V) × Fin (2 * T + 1)

/-- The `G`-end of the junction edge. -/
def jG : CNode D T := (.inl D.vG, Fin.last (2 * T))
/-- The `H`-end of the junction edge. -/
def jH : CNode D T := (.inr D.uH, 0)

/-- The chain graph `GH`. -/
noncomputable def chain : SimpleGraph (CNode D T) where
  Adj p q := (D.X.Adj p.1 q.1 ∧ (q.2.val : ℤ) = p.2.val + volt D p.1 q.1) ∨
    (p = jG D T ∧ q = jH D T) ∨ (p = jH D T ∧ q = jG D T)
  symm := ⟨by
    intro p q h
    rcases h with ⟨h1, h2⟩ | h | h
    · left
      refine ⟨h1.symm, ?_⟩
      simp only [volt] at h2 ⊢
      omega
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨by
    intro p h
    rcases h with ⟨h1, -⟩ | h | h
    · exact D.X.irrefl h1
    · have := h.1.symm.trans h.2; simp [jG, jH] at this
    · have := h.1.symm.trans h.2; simp [jG, jH] at this⟩

/-- The labelled chain. -/
@[reducible] noncomputable def chainL : LGraph Λ where
  V := CNode D T
  graph := chain D T
  label p := Sum.elim D.G.label D.H.label p.1

/-- Position of a node along the chain. -/
def pos (p : CNode D T) : ℤ := Sum.elim (fun _ => 0) (fun _ => (2 * T + 1 : ℤ)) p.1 + p.2.val

/-- The four nodes where the projection to `G ⊕ H` is not a local isomorphism. -/
def special : Set (CNode D T) :=
  {(.inl D.uG, 0), jG D T, jH D T, (.inr D.vH, Fin.last (2 * T))}

lemma voltHalf_nonneg (x y) : 0 ≤ voltHalf D x y := by
  unfold voltHalf; split_ifs <;> omega

lemma voltHalf_le_one (x y) : voltHalf D x y ≤ 1 := by
  unfold voltHalf; split_ifs <;> omega

lemma abs_pos_sub_le_one {p q : CNode D T} (h : (chain D T).Adj p q) :
    |pos D T p - pos D T q| ≤ 1 := by
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  have h0 := voltHalf_nonneg D x y
  have h1 := voltHalf_le_one D x y
  have h2 := voltHalf_nonneg D y x
  have h3 := voltHalf_le_one D y x
  rcases h with ⟨hxy, hv⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · simp only [volt] at hv
    rcases x with x | x <;> rcases y with y | y <;> simp at hxy <;>
      simp only [pos, Sum.elim_inl, Sum.elim_inr] <;> rw [abs_le] <;> constructor <;> omega
  · simp only [jG, jH, Prod.mk.injEq] at h1' h2'
    obtain ⟨rfl, rfl⟩ := h1'
    obtain ⟨rfl, rfl⟩ := h2'
    simp [pos]
  · simp only [jG, jH, Prod.mk.injEq] at h1' h2'
    obtain ⟨rfl, rfl⟩ := h1'
    obtain ⟨rfl, rfl⟩ := h2'
    simp [pos]

/-- Away from the special nodes, the projection is a bijection on neighbourhoods. -/
lemma bijOn_fst (hG : D.uG ≠ D.vG) (hH : D.uH ≠ D.vH) {p : CNode D T}
    (hp : p ∉ special D T) :
    BijOn Prod.fst {q | (chain D T).Adj p q} {y | (D.X).Adj p.1 y} := by
  have hpG : p ≠ jG D T := fun h => hp (by simp [special, h])
  have hpH : p ≠ jH D T := fun h => hp (by simp [special, h])
  have hadj : ∀ q, (chain D T).Adj p q ↔
      (D.X).Adj p.1 q.1 ∧ (q.2.val : ℤ) = p.2.val + volt D p.1 q.1 := by
    intro q
    constructor
    · rintro (h | h | h)
      · exact h
      · exact (hpG h.1).elim
      · exact (hpH h.1).elim
    · exact Or.inl
  refine ⟨fun q hq => ((hadj q).1 hq).1, fun q hq q' hq' hqq => ?_, fun y hy => ?_⟩
  · have h1 := ((hadj q).1 hq).2
    have h2 := ((hadj q').1 hq').2
    rw [hqq] at h1
    exact Prod.ext hqq (Fin.ext (by omega))
  · obtain ⟨x, i⟩ := p
    simp only [mem_ofPred_eq] at hy ⊢
    -- the target index is in range
    have hrange : 0 ≤ (i.val : ℤ) + volt D x y ∧
        (i.val : ℤ) + volt D x y < 2 * T + 1 := by
      have hi := i.isLt
      simp only [volt, voltHalf]
      rcases x with x | x <;> rcases y with y | y <;> simp at hy
      · by_cases h1 : x = D.vG ∧ y = D.uG
        · obtain ⟨rfl, rfl⟩ := h1
          have : i ≠ Fin.last (2 * T) := fun h => hpG (by simp [jG, h])
          have : i.val ≠ 2 * T := fun h => this (Fin.ext h)
          simp [hG.symm, hG]; omega
        · by_cases h2 : x = D.uG ∧ y = D.vG
          · obtain ⟨rfl, rfl⟩ := h2
            have : i ≠ 0 := fun h => hp (by simp [special, h])
            have : i.val ≠ 0 := fun h => this (Fin.ext h)
            simp [hG.symm, hG]; omega
          · have h2' : ¬(y = D.vG ∧ x = D.uG) := fun h => h2 ⟨h.2, h.1⟩
            simp [h1, h2']; omega
      · by_cases h1 : x = D.vH ∧ y = D.uH
        · obtain ⟨rfl, rfl⟩ := h1
          have : i ≠ Fin.last (2 * T) := fun h => hp (by simp [special, h])
          have : i.val ≠ 2 * T := fun h => this (Fin.ext h)
          simp [hH.symm, hH]; omega
        · by_cases h2 : x = D.uH ∧ y = D.vH
          · obtain ⟨rfl, rfl⟩ := h2
            have : i ≠ 0 := fun h => hpH (by simp [jH, h])
            have : i.val ≠ 0 := fun h => this (Fin.ext h)
            simp [hH.symm, hH]; omega
          · have h2' : ¬(y = D.vH ∧ x = D.uH) := fun h => h2 ⟨h.2, h.1⟩
            simp [h1, h2']; omega
    refine ⟨(y, ⟨((i.val : ℤ) + volt D x y).toNat, by omega⟩), ?_, rfl⟩
    rw [mem_ofPred_eq, hadj]
    exact ⟨hy, by simp; omega⟩

/-- Copies of the same node of `G ⊕ H` are never adjacent. -/
lemma not_adj_of_fst_eq {p q : CNode D T} (h : p.1 = q.1) :
    ¬ (chain D T).Adj p q := by
  rintro (⟨h1, -⟩ | h' | h')
  · rw [h] at h1; exact D.X.irrefl h1
  · have := h'.1 ▸ h'.2 ▸ h; simp [jG, jH] at this
  · have := h'.1 ▸ h'.2 ▸ h; simp [jG, jH] at this

open Classical in
lemma voltHalf_inl_inl {a b : D.G.V} :
    voltHalf D (.inl a) (.inl b) = if a = D.vG ∧ b = D.uG then 1 else 0 := by
  simp [voltHalf]

open Classical in
lemma voltHalf_inr_inr {a b : D.H.V} :
    voltHalf D (.inr a) (.inr b) = if a = D.vH ∧ b = D.uH then 1 else 0 := by
  simp [voltHalf]

lemma volt_inl_eq_zero {a b : D.G.V} (h : s(a, b) ≠ s(D.uG, D.vG)) :
    volt D (.inl a) (.inl b) = 0 := by
  have h1 : ¬(a = D.vG ∧ b = D.uG) := by rintro ⟨rfl, rfl⟩; exact h Sym2.eq_swap
  have h2 : ¬(b = D.vG ∧ a = D.uG) := by rintro ⟨rfl, rfl⟩; exact h rfl
  simp only [volt, voltHalf_inl_inl, h1, h2]; norm_num

lemma volt_inr_eq_zero {a b : D.H.V} (h : s(a, b) ≠ s(D.uH, D.vH)) :
    volt D (.inr a) (.inr b) = 0 := by
  have h1 : ¬(a = D.vH ∧ b = D.uH) := by rintro ⟨rfl, rfl⟩; exact h Sym2.eq_swap
  have h2 : ¬(b = D.vH ∧ a = D.uH) := by rintro ⟨rfl, rfl⟩; exact h rfl
  simp only [volt, voltHalf_inr_inr, h1, h2]; norm_num

/-- Copy `i` of `G` minus its cycle edge embeds into the chain. -/
def copyG (i : Fin (2 * T + 1)) :
    D.G.graph.deleteEdges {s(D.uG, D.vG)} →g chain D T where
  toFun a := (.inl a, i)
  map_rel' := by
    intro a b h
    rw [SimpleGraph.deleteEdges_adj] at h
    exact Or.inl ⟨by simpa using h.1, by simp [volt_inl_eq_zero D h.2]⟩

/-- Copy `i` of `H` minus its cycle edge embeds into the chain. -/
def copyH (i : Fin (2 * T + 1)) :
    D.H.graph.deleteEdges {s(D.uH, D.vH)} →g chain D T where
  toFun a := (.inr a, i)
  map_rel' := by
    intro a b h
    rw [SimpleGraph.deleteEdges_adj] at h
    exact Or.inl ⟨by simpa using h.1, by simp [volt_inr_eq_zero D h.2]⟩

lemma reach_copyG (hr : (D.G.graph.deleteEdges {s(D.uG, D.vG)}).Reachable D.uG D.vG)
    (i : Fin (2 * T + 1)) {a b : D.G.V} (h : D.G.graph.Reachable a b) :
    (chain D T).Reachable (.inl a, i) (.inl b, i) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    refine ih.trans ?_
    rename_i b c _
    by_cases he : s(b, c) = s(D.uG, D.vG)
    · have huv := hr.map (copyG D T i)
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    · exact (SimpleGraph.Adj.reachable ((copyG D T i).map_rel
        (SimpleGraph.deleteEdges_adj.2 ⟨hbc, he⟩)))

lemma reach_copyH (hr : (D.H.graph.deleteEdges {s(D.uH, D.vH)}).Reachable D.uH D.vH)
    (i : Fin (2 * T + 1)) {a b : D.H.V} (h : D.H.graph.Reachable a b) :
    (chain D T).Reachable (.inr a, i) (.inr b, i) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    refine ih.trans ?_
    rename_i b c _
    by_cases he : s(b, c) = s(D.uH, D.vH)
    · have huv := hr.map (copyH D T i)
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact huv
      · exact huv.symm
    · exact (SimpleGraph.Adj.reachable ((copyH D T i).map_rel
        (SimpleGraph.deleteEdges_adj.2 ⟨hbc, he⟩)))

lemma chain_connected (hG : D.G.graph.Connected) (hH : D.H.graph.Connected)
    (hGe : D.G.graph.Adj D.uG D.vG) (hHe : D.H.graph.Adj D.uH D.vH)
    (hGr : (D.G.graph.deleteEdges {s(D.uG, D.vG)}).Reachable D.uG D.vG)
    (hHr : (D.H.graph.deleteEdges {s(D.uH, D.vH)}).Reachable D.uH D.vH) :
    (chain D T).Connected := by
  have hGne : D.uG ≠ D.vG := hGe.ne
  have hHne : D.uH ≠ D.vH := hHe.ne
  set base : CNode D T := (.inl D.uG, 0)
  have hGall : ∀ k (hk : k < 2 * T + 1) (a : D.G.V),
      (chain D T).Reachable base (.inl a, ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro hk a; exact reach_copyG D T hGr 0 (hG.preconnected _ _)
    | succ k ih =>
      intro hk a
      refine (ih (by omega) D.vG).trans (SimpleGraph.Adj.reachable ?_ |>.trans
        (reach_copyG D T hGr _ (hG.preconnected D.uG a)))
      refine Or.inl ⟨by simpa using hGe.symm, ?_⟩
      simp [volt, voltHalf_inl_inl, hGne, hGne.symm]
  have hHall : ∀ k (hk : k < 2 * T + 1) (b : D.H.V),
      (chain D T).Reachable base (.inr b, ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk b
      have hj : (chain D T).Adj (jG D T) (jH D T) := Or.inr (Or.inl ⟨rfl, rfl⟩)
      have := (hGall (2 * T) (by omega) D.vG).trans hj.reachable
      exact this.trans (reach_copyH D T hHr 0 (hH.preconnected _ _))
    | succ k ih =>
      intro hk b
      refine (ih (by omega) D.vH).trans (SimpleGraph.Adj.reachable ?_ |>.trans
        (reach_copyH D T hHr _ (hH.preconnected D.uH b)))
      refine Or.inl ⟨by simpa using hHe.symm, ?_⟩
      simp [volt, voltHalf_inr_inr, hHne, hHne.symm]
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨base, fun ⟨x, i⟩ => ?_⟩
  rcases x with a | b
  · exact hGall i.val i.isLt a
  · exact hHall i.val i.isLt b

lemma chainL_admissible (hG : D.G.Admissible ⊤) (hH : D.H.Admissible ⊤)
    (hGe : D.G.graph.Adj D.uG D.vG) (hHe : D.H.graph.Adj D.uH D.vH)
    (hGr : (D.G.graph.deleteEdges {s(D.uG, D.vG)}).Reachable D.uG D.vG)
    (hHr : (D.H.graph.deleteEdges {s(D.uH, D.vH)}).Reachable D.uH D.vH) :
    (chainL D T).Admissible ⊤ where
  connected := chain_connected D T hG.connected hH.connected hGe hHe hGr hHr
  three_le := by
    show 3 ≤ Nat.card ((D.G.V ⊕ D.H.V) × Fin (2 * T + 1))
    rw [Nat.card_prod, Nat.card_sum, Nat.card_fin]
    have := hG.three_le
    nlinarith
  degree_le := fun _ => le_top

end Chain

section Runs

variable {V : Type*}

/-- Under a halting machine, a node in an accepting or rejecting state keeps its state. -/
lemma runFrom_halting {M : Machine Λ Q} (hhalt : M.Halting) (Gr : SimpleGraph V) (C : V → Q)
    (σ : ℕ → Set V) {v : V} (hv : C v ∈ M.Y ∪ M.N) (t : ℕ) : runFrom M Gr C σ t v = C v := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [runFrom_succ]
    by_cases h : v ∈ σ t
    · rw [step_of_mem _ _ h, ih, hhalt _ hv]
    · rw [step_of_notMem _ _ h, ih]

/-- Interleaving a schedule with idle steps. -/
lemma runFrom_two_mul (M : Machine Λ Q) (Gr : SimpleGraph V) (C : V → Q) (σ' S : ℕ → Set V)
    (h : ∀ t, (σ' (2 * t) = S t ∧ σ' (2 * t + 1) = ∅) ∨ (σ' (2 * t) = ∅ ∧ σ' (2 * t + 1) = S t))
    (t : ℕ) : runFrom M Gr C σ' (2 * t) = runFrom M Gr C S t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, runFrom_succ, runFrom_succ, ih, runFrom_succ]
    rcases h t with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, step_empty]
    · rw [h1, h2, step_empty]

/-- Runs on `G ⊕ H` restrict to runs on `G`. -/
lemma runFrom_sum_inl (M : Machine Λ Q) (G H : LGraph Λ) (C : G.V ⊕ H.V → Q)
    (R : ℕ → Set (G.V ⊕ H.V)) (t : ℕ) (a : G.V) :
    runFrom M (G.graph ⊕g H.graph) C R t (.inl a) =
      runFrom M G.graph (C ∘ Sum.inl) (fun t => Sum.inl ⁻¹' R t) t a := by
  have := sim_global M (G.graph ⊕g H.graph) G.graph Sum.inl R C (fun C w => by
    apply view_comp_of_bijOn
    refine ⟨fun u hu => by simpa using hu, Sum.inl_injective.injOn, fun x hx => ?_⟩
    rcases x with b | b
    · exact ⟨b, by simpa using hx, rfl⟩
    · simp at hx) t
  rw [this]; rfl

/-- Runs on `G ⊕ H` restrict to runs on `H`. -/
lemma runFrom_sum_inr (M : Machine Λ Q) (G H : LGraph Λ) (C : G.V ⊕ H.V → Q)
    (R : ℕ → Set (G.V ⊕ H.V)) (t : ℕ) (b : H.V) :
    runFrom M (G.graph ⊕g H.graph) C R t (.inr b) =
      runFrom M H.graph (C ∘ Sum.inr) (fun t => Sum.inr ⁻¹' R t) t b := by
  have := sim_global M (G.graph ⊕g H.graph) H.graph Sum.inr R C (fun C w => by
    apply view_comp_of_bijOn
    refine ⟨fun u hu => by simpa using hu, Sum.inr_injective.injOn, fun x hx => ?_⟩
    rcases x with a | a
    · simp at hx
    · exact ⟨a, by simpa using hx, rfl⟩) t
  rw [this]; rfl

end Runs

/-- The core of Lemma 3.1: if a reference run on `G ⊕ H` with liftable selections puts all nodes of
`G` into accepting and all nodes of `H` into rejecting states within `T` steps, the chain with
`2T + 1` copies has a fair run that is neither accepting nor rejecting. -/
theorem chain_contra (A : Automaton Λ Q) (hhalt : A.M.Halting) (hA : A.Consistent ⊤)
    (D : ChainData Λ) (hG : D.G.Admissible ⊤) (hH : D.H.Admissible ⊤)
    (hGe : D.G.graph.Adj D.uG D.vG) (hHe : D.H.graph.Adj D.uH D.vH)
    (hGr : (D.G.graph.deleteEdges {s(D.uG, D.vG)}).Reachable D.uG D.vG)
    (hHr : (D.H.graph.deleteEdges {s(D.uH, D.vH)}).Reachable D.uH D.vH)
    (T : ℕ) (R : ℕ → Set (D.G.V ⊕ D.H.V))
    (hR : ∀ t, A.sel.Liftable (chain D T) (Prod.fst ⁻¹' R t))
    (hY : ∀ a, runFrom A.M D.X (A.M.init ∘ Sum.elim D.G.label D.H.label) R T (.inl a) ∈ A.M.Y)
    (hN : ∀ b, runFrom A.M D.X (A.M.init ∘ Sum.elim D.G.label D.H.label) R T (.inr b) ∈ A.M.N) :
    False := by
  set C₀ := A.M.init ∘ Sum.elim D.G.label D.H.label
  set Good : ℕ → Set (CNode D T) :=
    fun t => {p | ∀ s ∈ special D T, (t : ℤ) ≤ |pos D T p - pos D T s|}
  have hnot : ∀ t, ∀ p ∈ Good (t + 1), p ∉ special D T := by
    intro t p hp hs
    have := hp p hs
    simp at this
    omega
  have hsim := sim A.M D.X (chain D T) Prod.fst R C₀ (A.init (chainL D T)) Good
    (fun _ _ => rfl)
    (fun t p hp s hs => by have := hp s hs; push_cast at this; linarith)
    (fun t p hp q hq s hs => by
      have h1 := hp s hs
      have h2 := abs_pos_sub_le_one D T hq
      have h3 := abs_sub_abs_le_abs_sub (pos D T p - pos D T s) (pos D T q - pos D T s)
      rw [show pos D T p - pos D T s - (pos D T q - pos D T s) = pos D T p - pos D T q by ring]
        at h3
      push_cast at h1
      linarith)
    (fun t p hp => view_comp_of_bijOn (bijOn_fst D T hGe.ne hHe.ne (hnot t p hp)) _) T
  -- middle copies
  obtain ⟨a₀⟩ := hG.nonempty
  obtain ⟨b₀⟩ := hH.nonempty
  let pG : CNode D T := (.inl a₀, ⟨T, by omega⟩)
  let pH : CNode D T := (.inr b₀, ⟨T, by omega⟩)
  have hpG : pG ∈ Good T := by
    rintro s (rfl | rfl | rfl | rfl) <;> simp [pG, pos, jG, jH] <;> rw [le_abs] <;> omega
  have hpH : pH ∈ Good T := by
    rintro s (rfl | rfl | rfl | rfl) <;> simp [pH, pos, jG, jH] <;> rw [le_abs] <;> omega
  set DT := runFrom A.M (chain D T) (A.init (chainL D T)) (fun t => Prod.fst ⁻¹' R t) T
  have hDG : DT pG ∈ A.M.Y := by rw [hsim pG hpG]; exact hY a₀
  have hDH : DT pH ∈ A.M.N := by rw [hsim pH hpH]; exact hN b₀
  obtain ⟨l, hl, hlD⟩ := reach_runFrom_of_liftable (M := A.M) hR (A.init (chainL D T)) T
  have hadm := chainL_admissible D T hG hH hGe hHe hGr hHr
  have : Nonempty (chainL D T).V := hadm.nonempty
  obtain ⟨σ₀, hσ₀⟩ := exists_fair (V := (chainL D T).V) A.sel A.fair
  have hσ : A.FairSchedule (chainL D T) (prepend l σ₀) := hσ₀.prepend hl
  have hlate : ∀ t, ∀ p, DT p ∈ A.M.Y ∪ A.M.N →
      A.run (chainL D T) (prepend l σ₀) (l.length + t) p = DT p := by
    intro t p hp
    simp only [Automaton.run]
    rw [runFrom_prepend]
    erw [hlD]
    exact runFrom_halting hhalt _ _ _ hp t
  rcases A.eventuallyIn_or hA hadm hσ with ⟨t₀, ht₀⟩ | ⟨t₀, ht₀⟩
  · have h1 := ht₀ (l.length + t₀) (by omega) pH
    rw [hlate t₀ pH (Or.inr hDH)] at h1
    exact A.M.disjoint.ne_of_mem h1 hDH rfl
  · have h1 := ht₀ (l.length + t₀) (by omega) pG
    rw [hlate t₀ pG (Or.inl hDG)] at h1
    exact A.M.disjoint.ne_of_mem hDG h1 rfl

/-- An edge on a cycle of a graph that is not acyclic. -/
lemma exists_nonbridge {V : Type*} {Gr : SimpleGraph V} (h : ¬ Gr.IsAcyclic) :
    ∃ u v, Gr.Adj u v ∧ (Gr.deleteEdges {s(u, v)}).Reachable u v := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge] at h
  push Not at h
  obtain ⟨e, he, hnb⟩ := h
  induction e using Sym2.ind with
  | h u v =>
    refine ⟨u, v, he, ?_⟩
    rw [SimpleGraph.isBridge_iff] at hnb
    exact not_not.1 hnb

/-- One direction of Lemma 3.1: a halting automaton cannot accept a cyclic graph and reject
another cyclic graph. -/
theorem lemma_3_1_aux (A : Automaton Λ Q) (hhalt : A.M.Halting) (hA : A.Consistent ⊤)
    {G H : LGraph Λ} (hG : G.Admissible ⊤) (hH : H.Admissible ⊤) (hGc : ¬ G.graph.IsAcyclic)
    (hHc : ¬ H.graph.IsAcyclic) (hacc : A.Accepts G) (hrej : ¬ A.Accepts H) : False := by
  obtain ⟨σG, hσG, g, hg⟩ := hacc
  have := hH.nonempty
  obtain ⟨σH, hσH⟩ := exists_fair (V := H.V) A.sel A.fair
  obtain ⟨h, hh⟩ := (A.not_accepts_iff hA hH hσH).1 hrej
  obtain ⟨uG, vG, hGe, hGr⟩ := exists_nonbridge hGc
  obtain ⟨uH, vH, hHe, hHr⟩ := exists_nonbridge hHc
  let D : ChainData Λ := ⟨G, H, uG, vG, uH, vH⟩
  by_cases hsync : A.sel = .synchronous
  · -- lock-step reference run
    have hσG' : σG = fun _ => univ := funext fun t => by
      have := hσG.1 t; rw [hsync] at this; exact this
    have hσH' : σH = fun _ => univ := funext fun t => by
      have := hσH.1 t; rw [hsync] at this; exact this
    refine chain_contra A hhalt hA D hG hH hGe hHe hGr hHr (max g h) (fun _ => univ)
      (fun t => by rw [hsync]; show Prod.fst ⁻¹' univ = univ; simp) (fun a => ?_) (fun b => ?_)
    · rw [runFrom_sum_inl]
      have := hg (max g h) (le_max_left _ _) a
      simp only [Automaton.run, hσG', preimage_univ] at this ⊢
      exact this
    · rw [runFrom_sum_inr]
      have := hh (max g h) (le_max_right _ _) b
      simp only [Automaton.run, hσH', preimage_univ] at this ⊢
      exact this
  · -- interleaved reference run
    set m := max g h
    let R : ℕ → Set (G.V ⊕ H.V) := fun s =>
      if s % 2 = 0 then Sum.inl '' σG (s / 2) else Sum.inr '' σH (s / 2)
    have hR0 : ∀ t, R (2 * t) = Sum.inl '' σG t := fun t => by simp [R]
    have hR1 : ∀ t, R (2 * t + 1) = Sum.inr '' σH t := fun t => by
      simp [R, Nat.add_mod, Nat.add_div]
    refine chain_contra A hhalt hA D hG hH hGe hHe hGr hHr (2 * m) R (fun s => ?_)
      (fun a => ?_) (fun b => ?_)
    · cases hsel : A.sel with
      | liberal => trivial
      | synchronous => exact (hsync hsel).elim
      | exclusive =>
        have hG1 := hσG.1 (s / 2)
        have hH1 := hσH.1 (s / 2)
        rw [hsel] at hG1 hH1
        obtain ⟨v, hv⟩ := hG1
        obtain ⟨w, hw⟩ := hH1
        have hRs : R s = {Sum.inl v} ∨ R s = {Sum.inr w} := by
          simp only [R, hv, hw, image_singleton]
          split_ifs <;> simp
        refine ⟨fun p hp q hq _ => not_adj_of_fst_eq D (2 * m) ?_, ?_⟩
        · rcases hRs with hRs | hRs <;>
            · simp only [mem_preimage, hRs, mem_singleton_iff] at hp hq; rw [hp, hq]
        · rcases hRs with hRs | hRs
          · exact ⟨(.inl v, 0), by simp [hRs]⟩
          · exact ⟨(.inr w, 0), by simp [hRs]⟩
    · rw [runFrom_sum_inl, runFrom_two_mul _ _ _ _ σG (fun t => Or.inl ⟨?_, ?_⟩)]
      · exact hg m (le_max_left _ _) a
      · simp only [hR0, preimage_image_eq _ Sum.inl_injective]
      · simp [hR1]
    · rw [runFrom_sum_inr, runFrom_two_mul _ _ _ _ σH (fun t => Or.inr ⟨?_, ?_⟩)]
      · exact hh m (le_max_right _ _) b
      · simp [hR0]
      · simp only [hR1, preimage_image_eq _ Sum.inr_injective]

/-- **Lemma 3.1.** Let `A` be an automaton with halting acceptance (the paper states this for
`DaF`-automata; we prove it for every halting machine, every counting bound, selection constraint
and fairness constraint). For all graphs `G` and `H` containing a cycle, `A` accepts `G` iff it
accepts `H`. -/
theorem lemma_3_1 (A : Automaton Λ Q) (hhalt : A.M.Halting) (hA : A.Consistent ⊤)
    {G H : LGraph Λ} (hG : G.Admissible ⊤) (hH : H.Admissible ⊤) (hGc : ¬ G.graph.IsAcyclic)
    (hHc : ¬ H.graph.IsAcyclic) : A.Accepts G ↔ A.Accepts H := by
  constructor
  · intro hacc
    by_contra hrej
    exact lemma_3_1_aux A hhalt hA hG hH hGc hHc hacc hrej
  · intro hacc
    by_contra hrej
    exact lemma_3_1_aux A hhalt hA hH hG hHc hGc hacc hrej

end Podc.WeakAsyncDecisionPower
