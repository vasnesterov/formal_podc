import Papers.PODC2025.HidingColoringCertification.Theta

/-!
# Theorem 4.1: hiding the colouring at a node of degree one

Lemma 4.1 of arXiv:2502.13854v1. Certificates `⊥, ⊤, 0, 1` (`L1`). Decoder `degOneLCP`:
* `⊥` accepts iff its degree is 1 and its neighbour is labelled `⊤`;
* `⊤` accepts iff exactly one neighbour is labelled `⊥` and all other neighbours carry the
  *same* colour `β ∈ {0,1}`;
* a colour `b` accepts iff at most one neighbour is labelled `⊤` and every other neighbour
  carries the colour `1 - b`.

Results:
* `degOneLCP_complete`: complete on *every* bipartite graph (the plain 2-colouring is accepted).
* `degOneLCP_stronglySoundAll`: on every graph and for every labelling the accepting nodes
  induce a bipartite graph — by an explicit 2-colouring (a `⊤` node gets `1 - β`, a `⊥` node the
  colour `β` of its `⊤` neighbour). The paper's proof of this step ("since `C` is odd, then
  `u ∈ V(C)`") is not an argument; uniformity of `β` is what makes it work.
* `degOneLCP_anonHiding`: hiding against anonymous extraction algorithms on every class containing
  `P₆ ⊔ K₂` (three labellings of this 8-node graph; the paper's Fig. 4 odd cycle in `V(D,4)` is
  not valid, see `fig4_edge_not_compatible`).
* `literalLCP_not_sound`: if `β` may differ between the neighbours of `⊤` (a possible reading of
  the paper's rule 2(b)), even plain soundness fails (5-cycle with a pendant node).
* `theorem_4_1`: Theorem 4.1 of the brief announcement.
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-- Certificates of Lemma 4.1: `⊥`, `⊤`, or a colour. -/
inductive L1 where
  | bot
  | top
  | col (b : Bool)
  deriving DecidableEq, Fintype

open L1

/-- Acceptance rule of Lemma 4.1 (with a uniform `β` in rule 2(b)). -/
def degOneRule (μ : View L1) : Prop :=
  match μ.label with
  | bot => μ.deg = 1 ∧ ∀ x ∈ μ.nbrs, x.label = top
  | top => μ.nbrs.countP (fun x => x.label = bot) = 1 ∧
      ∃ β : Bool, ∀ x ∈ μ.nbrs, x.label ≠ bot → x.label = col β
  | col b => μ.nbrs.countP (fun x => x.label = top) ≤ 1 ∧
      ∀ x ∈ μ.nbrs, x.label ≠ top → x.label = col (!b)

instance (μ : View L1) : Decidable (degOneRule μ) := by
  unfold degOneRule; split <;> infer_instance

/-- The LCP of Lemma 4.1 (constant-size certificates). -/
def degOneLCP : LCP L1 where
  D μ := decide (degOneRule μ)
  sz _ := Set.univ

variable {bound : ℕ → ℕ}

section Soundness

variable (P : PortGraph) (ℓ : P.V → L1)

lemma acc_iff (v : P.V) : degOneLCP.Acc P ℓ v ↔ degOneRule (P.view ℓ v) := by
  simp [LCP.Acc, degOneLCP]

lemma acc_bot {v : P.V} (h : degOneLCP.Acc P ℓ v) (hv : ℓ v = bot) :
    P.G.degree v = 1 ∧ ∀ w, P.G.Adj v w → ℓ w = top := by
  rw [acc_iff] at h
  unfold degOneRule at h
  simp only [PortGraph.view, hv] at h
  refine ⟨h.1, fun w hw => ?_⟩
  exact h.2 _ (Multiset.mem_map.2 ⟨w, by simpa using hw, rfl⟩)

lemma acc_top {v : P.V} (h : degOneLCP.Acc P ℓ v) (hv : ℓ v = top) :
    ∃ β : Bool, ∀ w, P.G.Adj v w → ℓ w ≠ bot → ℓ w = col β := by
  rw [acc_iff] at h
  unfold degOneRule at h
  simp only [PortGraph.view, hv] at h
  obtain ⟨β, hβ⟩ := h.2
  exact ⟨β, fun w hw => hβ _ (Multiset.mem_map.2 ⟨w, by simpa using hw, rfl⟩)⟩

lemma acc_col {v : P.V} {b : Bool} (h : degOneLCP.Acc P ℓ v) (hv : ℓ v = col b) :
    ∀ w, P.G.Adj v w → ℓ w ≠ top → ℓ w = col (!b) := by
  rw [acc_iff] at h
  unfold degOneRule at h
  simp only [PortGraph.view, hv] at h
  exact fun w hw => h.2 _ (Multiset.mem_map.2 ⟨w, by simpa using hw, rfl⟩)

open Classical in
/-- The explicit 2-colouring of the accepting nodes. -/
noncomputable def pot (v : P.V) : Bool :=
  match ℓ v with
  | col b => b
  | top => !decide (∃ w, P.G.Adj v w ∧ ℓ w = col true)
  | bot => decide (∃ u, P.G.Adj v u ∧ ∃ w, P.G.Adj u w ∧ ℓ w = col true)

lemma pot_top_eq {u : P.V} (hu : degOneLCP.Acc P ℓ u) (htop : ℓ u = top) {a : P.V}
    (ha : P.G.Adj u a) {x : Bool} (hx : ℓ a = col x) :
    decide (∃ w, P.G.Adj u w ∧ ℓ w = col true) = x := by
  obtain ⟨β, hβ⟩ := acc_top P ℓ hu htop
  have hxβ : x = β := by have := hβ a ha (by simp [hx]); rw [hx] at this; simpa using this
  subst hxβ
  cases x
  · simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro w hw hwt
    have := hβ w hw (by simp [hwt]); rw [hwt] at this; simp at this
  · simpa using ⟨a, ha, hx⟩

lemma pot_ne {a b : P.V} (ha : degOneLCP.Acc P ℓ a) (hb : degOneLCP.Acc P ℓ b)
    (hab : P.G.Adj a b) : pot P ℓ a ≠ pot P ℓ b := by
  -- one-sided cases, then symmetry
  have one : ∀ a b, degOneLCP.Acc P ℓ a → degOneLCP.Acc P ℓ b → P.G.Adj a b →
      (∃ x, ℓ a = col x) → pot P ℓ a ≠ pot P ℓ b := by
    intro a b ha hb hab ⟨x, hx⟩
    rcases hlb : ℓ b with _ | _ | y
    · exact absurd ((acc_bot P ℓ hb hlb).2 a hab.symm) (by simp [hx])
    · simp only [pot, hx, hlb]
      rw [pot_top_eq P ℓ hb hlb hab.symm hx]; cases x <;> simp
    · have := acc_col P ℓ ha hx b hab (by simp [hlb])
      rw [hlb] at this
      simp only [pot, hx, hlb]; injection this with h; rw [h]; cases x <;> simp
  rcases hla : ℓ a with _ | _ | x
  · rcases hlb : ℓ b with _ | _ | y
    · exact absurd ((acc_bot P ℓ ha hla).2 b hab) (by simp [hlb])
    · -- `a` is `⊥`, `b` is `⊤`
      obtain ⟨hdeg, -⟩ := acc_bot P ℓ ha hla
      have huniq : ∀ u, P.G.Adj a u → u = b := by
        intro u hu
        obtain ⟨z, hz⟩ := Finset.card_eq_one.1 ((P.G.card_neighborFinset_eq_degree a).trans hdeg)
        have h1 : u ∈ P.G.neighborFinset a := by simpa using hu
        have h2 : b ∈ P.G.neighborFinset a := by simpa using hab
        rw [hz] at h1 h2; simp at h1 h2; rw [h1, h2]
      have : decide (∃ u, P.G.Adj a u ∧ ∃ w, P.G.Adj u w ∧ ℓ w = col true) =
          decide (∃ w, P.G.Adj b w ∧ ℓ w = col true) := by
        apply decide_eq_decide.2
        constructor
        · rintro ⟨u, hu, hw⟩; rw [huniq u hu] at hw; exact hw
        · intro hw; exact ⟨b, hab, hw⟩
      simp only [pot, hla, hlb, this]; cases decide (∃ w, P.G.Adj b w ∧ ℓ w = col true) <;> simp
    · exact fun h => one b a hb ha hab.symm ⟨y, hlb⟩ h.symm
  · rcases hlb : ℓ b with _ | _ | y
    · -- `a` is `⊤`, `b` is `⊥`
      obtain ⟨hdeg, -⟩ := acc_bot P ℓ hb hlb
      have huniq : ∀ u, P.G.Adj b u → u = a := by
        intro u hu
        obtain ⟨z, hz⟩ := Finset.card_eq_one.1 ((P.G.card_neighborFinset_eq_degree b).trans hdeg)
        have h1 : u ∈ P.G.neighborFinset b := by simpa using hu
        have h2 : a ∈ P.G.neighborFinset b := by simpa using hab.symm
        rw [hz] at h1 h2; simp at h1 h2; rw [h1, h2]
      have : decide (∃ u, P.G.Adj b u ∧ ∃ w, P.G.Adj u w ∧ ℓ w = col true) =
          decide (∃ w, P.G.Adj a w ∧ ℓ w = col true) := by
        apply decide_eq_decide.2
        constructor
        · rintro ⟨u, hu, hw⟩; rw [huniq u hu] at hw; exact hw
        · intro hw; exact ⟨a, hab.symm, hw⟩
      simp only [pot, hla, hlb, this]; cases decide (∃ w, P.G.Adj a w ∧ ℓ w = col true) <;> simp
    · obtain ⟨β, hβ⟩ := acc_top P ℓ ha hla
      have := hβ b hab (by simp [hlb]); rw [hlb] at this; simp at this
    · exact fun h => one b a hb ha hab.symm ⟨y, hlb⟩ h.symm
  · exact one a b ha hb hab ⟨x, hla⟩

/-- **Strong soundness of Lemma 4.1**, on every graph and for every labelling. -/
theorem degOneLCP_stronglySoundAll : degOneLCP.StronglySoundAll 2 := by
  intro P ℓ
  refine ⟨Coloring.mk (fun v => if pot P ℓ v.1 then (1 : Fin 2) else 0) ?_⟩
  intro a b hab heq
  apply pot_ne P ℓ a.2 b.2 hab
  revert heq
  cases pot P ℓ a.1 <;> cases pot P ℓ b.1 <;> simp

end Soundness

/-- **Completeness** on every bipartite graph (the proper 2-colouring is accepted). -/
theorem degOneLCP_complete : degOneLCP.Complete bound Bipartite := by
  intro P _ hbip
  obtain ⟨c⟩ := hbip
  refine ⟨fun v => col (decide (c v = 1)), fun _ => trivial, fun v => ?_⟩
  rw [acc_iff]
  simp only [degOneRule, PortGraph.view]
  refine ⟨?_, ?_⟩
  · rw [Multiset.countP_eq_zero.2]
    · omega
    · intro x hx; obtain ⟨w, -, rfl⟩ := Multiset.mem_map.1 hx; simp [PortGraph.nbrInfo]
  · intro x hx _
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
    have hne := c.valid (by simpa using hw : P.G.Adj v w)
    simp only [PortGraph.nbrInfo, col.injEq]
    revert hne; generalize c v = a; generalize c w = b; revert a b; decide

lemma degOneLCP_anonymous : degOneLCP.Anonymous := by
  intro μ μ' h
  simp only [View.anon, AnonView.mk.injEq] at h
  obtain ⟨hN, hl, hd, hn⟩ := h
  have hcp : ∀ p : L1 → Prop, [DecidablePred p] →
      μ.nbrs.countP (fun x => p x.label) = μ'.nbrs.countP (fun x => p x.label) := by
    intro p _
    have e : ∀ s : Multiset (NbrInfo L1),
        s.countP (fun x => p x.label) = (s.map NbrInfo.anon).countP (fun x => p x.label) := by
      intro s; rw [Multiset.countP_map, Multiset.countP_eq_card_filter]; rfl
    rw [e, e μ'.nbrs, hn]
  have hall : ∀ q : L1 → Prop, (∀ x ∈ μ.nbrs, q x.label) ↔ (∀ x ∈ μ'.nbrs, q x.label) := by
    intro q
    have e : ∀ s : Multiset (NbrInfo L1),
        (∀ x ∈ s, q x.label) ↔ ∀ y ∈ s.map NbrInfo.anon, q y.label := by
      intro s; simp [NbrInfo.anon]
    rw [e, e μ'.nbrs, hn]
  simp only [degOneLCP]
  apply decide_eq_decide.2
  unfold degOneRule
  rw [← hl, ← hd]
  split
  · exact and_congr Iff.rfl (hall (fun l => l = top))
  · rw [hcp (· = bot)]
    exact and_congr Iff.rfl (exists_congr fun β => hall (fun l => l ≠ bot → l = col β))
  · rename_i b _
    rw [hcp (· = top)]
    exact and_congr Iff.rfl (hall (fun l => l ≠ top → l = col (!b)))

/-! ### Hiding -/

/-- `P₆ ⊔ K₂`: the path `0–1–2–3–4–5` and the edge `6–7`. -/
def p6k2 : SimpleGraph (Fin 8) := edgeGraph 8 [(0,1),(1,2),(2,3),(3,4),(4,5),(6,7)]

instance : DecidableRel p6k2.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

/-- Ports symmetric under the reflection `i ↦ 5 - i` of the path. -/
def p6k2Port (v w : Fin 8) : ℕ :=
  if v.val = 0 ∨ v.val = 5 ∨ 6 ≤ v.val then 0
  else if v.val ≤ 2 then (if w.val < v.val then 0 else 1)
  else (if v.val < w.val then 0 else 1)

lemma p6k2_degree : ∀ v : Fin 8, p6k2.degree v =
    if v.val = 0 ∨ v.val = 5 ∨ 6 ≤ v.val then 1 else 2 := by decide

/-- `P₆ ⊔ K₂` as a port graph (identifiers = indices). -/
abbrev p6k2PG (N : ℕ) (hN : 8 ≤ N) : PortGraph where
  V := Fin 8
  G := p6k2
  port := p6k2Port
  port_lt := fun {v w} h => by
    rw [p6k2_degree]; revert v w; decide
  port_inj := fun {v w w'} => by revert v w w'; decide
  id := fun v => v.val
  id_inj := fun a b h => Fin.ext h
  N := N
  id_lt v := lt_of_lt_of_le v.isLt hN

/-- `⊥⊤0101 ⊔ ⊥⊤`. -/
def lab1 : Fin 8 → L1 := ![bot, top, col false, col true, col false, col true, bot, top]
/-- `⊥⊤1010 ⊔ ⊥⊤`. -/
def lab2 : Fin 8 → L1 := ![bot, top, col true, col false, col true, col false, bot, top]
/-- `⊥⊤01⊤⊥ ⊔ ⊥⊤`. -/
def lab3 : Fin 8 → L1 := ![bot, top, col false, col true, top, bot, bot, top]

lemma p6k2_view_eq (N : ℕ) (hN : 8 ≤ N) (ℓ : Fin 8 → L1) (v : Fin 8) (s : Finset (Fin 8))
    (hs : ∀ w : Fin 8, p6k2.Adj v w ↔ w ∈ s) :
    (p6k2PG N hN).view ℓ v = ⟨N, v.val, ℓ v, s.card, s.val.map ((p6k2PG N hN).nbrInfo ℓ v)⟩ :=
  PortGraph.view_eq_mk (P := p6k2PG N hN) s hs

lemma p6k2_view_N (N : ℕ) (hN : 8 ≤ N) (ℓ : Fin 8 → L1) (v : Fin 8) :
    (p6k2PG N hN).view ℓ v = {(p6k2PG 8 le_rfl).view ℓ v with N := N} := rfl

lemma degOneRule_N (μ : View L1) (N : ℕ) : degOneRule {μ with N := N} ↔ degOneRule μ := by
  unfold degOneRule; rfl

lemma p6k2_acc8 :
    (∀ v, degOneLCP.Acc (p6k2PG 8 le_rfl) lab1 v) ∧ (∀ v, degOneLCP.Acc (p6k2PG 8 le_rfl) lab2 v) ∧
      (∀ v, degOneLCP.Acc (p6k2PG 8 le_rfl) lab3 v) := by
  decide

lemma p6k2_acc (N : ℕ) (hN : 8 ≤ N) :
    (∀ v, degOneLCP.Acc (p6k2PG N hN) lab1 v) ∧ (∀ v, degOneLCP.Acc (p6k2PG N hN) lab2 v) ∧
      (∀ v, degOneLCP.Acc (p6k2PG N hN) lab3 v) := by
  exact p6k2_acc8

lemma p6k2_anon (N : ℕ) (hN : 8 ≤ N) :
    ((p6k2PG N hN).view lab1 (0 : Fin 8)).anon = ((p6k2PG N hN).view lab2 (0 : Fin 8)).anon ∧
    ((p6k2PG N hN).view lab1 (2 : Fin 8)).anon = ((p6k2PG N hN).view lab3 (2 : Fin 8)).anon ∧
    ((p6k2PG N hN).view lab2 (2 : Fin 8)).anon = ((p6k2PG N hN).view lab3 (3 : Fin 8)).anon := by
  refine ⟨?_, ?_, ?_⟩
  · rw [p6k2_view_eq N hN lab1 0 {1} (by decide), p6k2_view_eq N hN lab2 0 {1} (by decide)]
    rfl
  · rw [p6k2_view_eq N hN lab1 2 {1, 3} (by decide), p6k2_view_eq N hN lab3 2 {1, 3} (by decide)]
    rfl
  · rw [p6k2_view_eq N hN lab2 2 {1, 3} (by decide), p6k2_view_eq N hN lab3 3 {2, 4} (by decide)]
    rw [show ({1, 3} : Finset (Fin 8)).val = (1 : Fin 8) ::ₘ {3} by decide,
      show ({2, 4} : Finset (Fin 8)).val = (4 : Fin 8) ::ₘ {2} by decide]
    simp only [View.anon, Multiset.map_cons, Multiset.map_singleton, PortGraph.nbrInfo,
      NbrInfo.anon]
    rfl

lemma fin_two_eq_of_ne_ne {a b c : Fin 2} (h1 : a ≠ b) (h2 : b ≠ c) : a = c := by
  revert a b c; decide

/-- **Hiding of Lemma 4.1** (against anonymous extraction algorithms) on every class containing
`P₆ ⊔ K₂`. With the labellings `⊥⊤0101`, `⊥⊤1010` and `⊥⊤01⊤⊥` (plus `⊥⊤` on `K₂`): the first
two force the node after `⊤` to get the colour of `⊥`, in both colourings; the third puts two
such nodes next to each other. -/
theorem degOneLCP_anonHiding (hb : 8 ≤ bound 8) (H : GraphClass) (hH : H (Fin 8) p6k2) :
    degOneLCP.AnonHiding bound H 2 := by
  intro A
  by_contra hcon
  push Not at hcon
  have adm : (p6k2PG (bound 8) hb).Admissible bound := by simp [PortGraph.Admissible]
  obtain ⟨a1, a2, a3⟩ := p6k2_acc (bound 8) hb
  have n1 := hcon _ adm hH lab1 (fun _ => trivial) a1
  have n2 := hcon _ adm hH lab2 (fun _ => trivial) a2
  have n3 := hcon _ adm hH lab3 (fun _ => trivial) a3
  simp only [LCP.Fails, not_exists, not_and, Function.comp] at n1 n2 n3
  obtain ⟨e0, e2, e3⟩ := p6k2_anon (bound 8) hb
  have h1 := fin_two_eq_of_ne_ne (n1 (0 : Fin 8) (1 : Fin 8) (by decide))
    (n1 (1 : Fin 8) (2 : Fin 8) (by decide))
  have h2 := fin_two_eq_of_ne_ne (n2 (0 : Fin 8) (1 : Fin 8) (by decide))
    (n2 (1 : Fin 8) (2 : Fin 8) (by decide))
  have h3 := n3 (2 : Fin 8) (3 : Fin 8) (by decide)
  rw [← e2, ← e3, ← h1, ← h2, e0] at h3
  exact h3 rfl

/-- Graphs of minimum degree one. -/
def H1 : GraphClass := fun V G => ∃ (_ : Fintype V) (_ : DecidableRel G.Adj), G.minDegree = 1

/-- Even cycles. -/
def H2 : GraphClass := fun _ G => ∃ n, 2 ≤ n ∧ Nonempty (G ≃g cycleGraph (2 * n))

/-- The (bipartite part of the) class `H = H₁ ∪ H₂` of Theorem 4.1. -/
def H41 : GraphClass := fun V G => G.Colorable 2 ∧ (H1 V G ∨ H2 V G)

lemma p6k2_minDegree : p6k2.minDegree = 1 := by
  apply le_antisymm
  · have := p6k2.minDegree_le_degree 0
    rw [p6k2_degree] at this; simpa using this
  · apply le_minDegree_of_forall_le_degree
    intro v; rw [p6k2_degree]; split_ifs <;> omega

lemma p6k2_colorable : p6k2.Colorable 2 :=
  ⟨Coloring.mk (fun v => (⟨(if v.val < 6 then v.val else v.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))
    (fun {a b} h => by revert a b; decide)⟩

/-- **Theorem 4.1** of the brief announcement: there is a strong and hiding one-round anonymous
LCP for `2-col_H`, `H = H₁ ∪ H₂`, with constant-size certificates (4 certificate values). In
fact the LCP is complete on all bipartite graphs and strongly sound on all graphs. -/
theorem theorem_4_1 (hb : 8 ≤ bound 8) :
    ∃ S : LCP L1, Fintype.card L1 = 4 ∧ S.Anonymous ∧ S.Complete bound H41 ∧
      S.Sound bound 2 ∧ S.StronglySound bound 2 ∧ S.AnonHiding bound H41 2 := by
  refine ⟨degOneLCP, rfl, degOneLCP_anonymous,
    fun P hP hH => degOneLCP_complete P hP hH.1,
    degOneLCP_stronglySoundAll.stronglySound.sound, degOneLCP_stronglySoundAll.stronglySound,
    degOneLCP_anonHiding hb H41 ⟨p6k2_colorable, Or.inl ⟨inferInstance, inferInstance,
      p6k2_minDegree⟩⟩⟩

/-! ### The literal reading of rule 2(b) is not sound -/

/-- Rule 2(b) read with a possibly different colour for each neighbour of `⊤`. -/
def literalRule (μ : View L1) : Prop :=
  match μ.label with
  | bot => μ.deg = 1 ∧ ∀ x ∈ μ.nbrs, x.label = top
  | top => μ.nbrs.countP (fun x => x.label = bot) = 1 ∧
      ∀ x ∈ μ.nbrs, x.label ≠ bot → ∃ β : Bool, x.label = col β
  | col b => μ.nbrs.countP (fun x => x.label = top) ≤ 1 ∧
      ∀ x ∈ μ.nbrs, x.label ≠ top → x.label = col (!b)

instance (μ : View L1) : Decidable (literalRule μ) := by
  unfold literalRule; split <;> infer_instance

/-- The decoder of Lemma 4.1 with the literal (non-uniform) reading of rule 2(b). -/
def literalLCP : LCP L1 where
  D μ := decide (literalRule μ)
  sz _ := Set.univ

/-- A 5-cycle `0–1–2–3–4–0` with a pendant node `5` at `0`. -/
def c5pendant : SimpleGraph (Fin 6) := edgeGraph 6 [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5)]

instance : DecidableRel c5pendant.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

/-- `⊤` at `0`, `⊥` at the pendant node, alternating colours `0101` on the rest of the cycle. -/
def labC5 : Fin 6 → L1 := ![top, col false, col true, col false, col true, bot]

lemma c5pendant_not_colorable : ¬ c5pendant.Colorable 2 := by
  rintro ⟨c⟩
  have : ∀ f : Fin 6 → Fin 2, ∃ a b, c5pendant.Adj a b ∧ f a = f b := by decide
  obtain ⟨a, b, hab, h⟩ := this c
  exact c.valid hab h

lemma literal_acc6 : ∀ v, literalLCP.Acc (PortGraph.ofFin c5pendant 6 le_rfl) labC5 v := by
  decide

/-- **With the literal reading of rule 2(b), Lemma 4.1's decoder is not even sound**: all nodes
of the non-bipartite graph "5-cycle plus pendant" accept. -/
theorem literalLCP_not_sound (hb : 6 ≤ bound 6) : ¬ literalLCP.Sound bound 2 := by
  intro h
  obtain ⟨v, hv⟩ := h (PortGraph.ofFin c5pendant (bound 6) hb)
    (by simp [PortGraph.Admissible]) c5pendant_not_colorable labC5 (fun _ => trivial)
  exact hv (literal_acc6 v)

/-! ### Fig. 4 -/

/-- **The odd cycle of Fig. 4 is not in `V(D,4)`**: the views `μ₃` (node 3 in `I₁`, neighbours
2 and 4) and `μ₄'` (node 4 in `I₂`, neighbours 2 and 3) can only be adjacent in an instance in
which the nodes with identifiers 2, 3, 4 form a triangle, which is not a yes-instance. (The
lemma's conclusion survives: see `degOneLCP_anonHiding`.) -/
theorem fig4_edge_not_compatible {L : Type} (P : PortGraph) (ℓ : P.V → L) (u v : P.V)
    (huv : P.G.Adj u v) (hu : ∃ x ∈ (P.view ℓ u).nbrs, x.id = 2)
    (hv : ∃ x ∈ (P.view ℓ v).nbrs, x.id = 2) : ¬ P.G.Colorable 2 := by
  obtain ⟨_, hx, hx2⟩ := hu
  obtain ⟨_, hy, hy2⟩ := hv
  obtain ⟨x, hux, rfl⟩ := P.mem_view_nbrs.1 hx
  obtain ⟨y, hvy, rfl⟩ := P.mem_view_nbrs.1 hy
  have : x = y := P.id_inj (by simp only [PortGraph.nbrInfo] at hx2 hy2; rw [hx2, hy2])
  subst this
  rintro ⟨c⟩
  have h1 := c.valid huv
  have h2 := c.valid hux
  have h3 := c.valid hvy
  revert h1 h2 h3
  generalize c u = a; generalize c v = b; generalize c x = d
  revert a b d; decide

end Podc.HidingColoringCertification
