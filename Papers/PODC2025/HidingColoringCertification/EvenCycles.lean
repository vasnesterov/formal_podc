import Papers.PODC2025.HidingColoringCertification.MinDegreeOne

/-!
# Lemma 4.2 (arXiv v1): even cycles, hiding by a 2-edge-colouring

Certificates: for each of the two ports `i ∈ {0,1}` of a node, an entry `(i, j, c)` where `j` is
the port of the edge at the other end and `c ∈ {0,1}` its colour (constant size, given that the
graphs of the class are cycles; ports are 0-based here). A node accepts iff it has degree 2, its
entries describe its two edges (`here = i`, `there` = the actual remote port), the two colours
differ, and each neighbour's entry for the same edge carries the same colour.

* `cycleLCP_stronglySoundAll`: on every graph, the accepting nodes induce a bipartite graph —
  along a cycle of accepting nodes the edge colours alternate, so the cycle is even (the paper's
  argument), and a graph without odd cycles is bipartite (`exists_odd_cycle`).
* `cycleLCP_complete`: complete on even cycles (any ports and identifiers).
* `cycleLCP_anonHiding`: hiding against anonymous algorithms on every class containing `C₄`:
  with suitable ports the reflection swapping the adjacent nodes `0` and `1` preserves ports and
  certificates, so `0` and `1` have the same anonymous view. (The paper combines a `C₄` and a
  `C₆`, whose views differ in `N` in the paper's own model; a single `C₄` suffices.)
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-- One entry of a certificate: port here, port at the other end, colour of the edge. -/
structure CEntry where
  here : ℕ
  there : ℕ
  c : Bool
  deriving DecidableEq

/-- Certificates of Lemma 4.2: the entries for ports 0 and 1. -/
abbrev LC := CEntry × CEntry

/-- Entry for port `i`. -/
def entryOf (l : LC) (i : ℕ) : CEntry := if i = 0 then l.1 else l.2

/-- The acceptance rule of Lemma 4.2. -/
def cycleRule (μ : View LC) : Prop :=
  μ.deg = 2 ∧ μ.label.1.here = 0 ∧ μ.label.2.here = 1 ∧ μ.label.1.c ≠ μ.label.2.c ∧
    ∀ x ∈ μ.nbrs, x.portHere < 2 ∧ (entryOf μ.label x.portHere).there = x.portThere ∧
      entryOf x.label x.portThere = ⟨x.portThere, x.portHere, (entryOf μ.label x.portHere).c⟩

instance (μ : View LC) : Decidable (cycleRule μ) := by unfold cycleRule; infer_instance

/-- The LCP of Lemma 4.2. -/
def cycleLCP : LCP LC where
  D μ := decide (cycleRule μ)
  sz _ := Set.univ

variable {bound : ℕ → ℕ}

section Soundness

variable (P : PortGraph) (ℓ : P.V → LC)

/-- Colour of the edge `vw` according to `v`. -/
def ecol (v w : P.V) : Bool := (entryOf (ℓ v) (P.port v w)).c

lemma cycle_acc {v : P.V} (h : cycleLCP.Acc P ℓ v) :
    (ℓ v).1.c ≠ (ℓ v).2.c ∧ ∀ w, P.G.Adj v w → P.port v w < 2 ∧ ecol P ℓ w v = ecol P ℓ v w := by
  simp only [LCP.Acc, cycleLCP, decide_eq_true_eq, cycleRule] at h
  obtain ⟨-, -, -, hc, hn⟩ := h
  refine ⟨hc, fun w hw => ?_⟩
  obtain ⟨h1, -, h3⟩ := hn _ (P.nbrInfo_mem_view hw)
  refine ⟨h1, ?_⟩
  simp only [PortGraph.nbrInfo] at h3
  simp only [ecol, h3]
  rfl

lemma ecol_ne {v w w' : P.V} (h : cycleLCP.Acc P ℓ v) (hw : P.G.Adj v w) (hw' : P.G.Adj v w')
    (hne : w ≠ w') : ecol P ℓ v w ≠ ecol P ℓ v w' := by
  obtain ⟨hc, hn⟩ := cycle_acc P ℓ h
  have h1 := (hn w hw).1
  have h2 := (hn w' hw').1
  have hp : P.port v w ≠ P.port v w' := fun e => hne (P.port_inj hw hw' e)
  simp only [ecol, entryOf]
  rcases (by omega : (P.port v w = 0 ∧ P.port v w' = 1) ∨ (P.port v w = 1 ∧ P.port v w' = 0))
    with ⟨a, b⟩ | ⟨a, b⟩
  · simp [a, b, hc]
  · simp [a, b, Ne.symm hc]

/-- A cycle through accepting nodes is even. -/
lemma cycle_even {y} (C : (cycleLCP.accGraph P ℓ).Walk y y) (hC : C.IsCycle) :
    Even C.length := by
  set L := C.length
  have hL := hC.three_le_length
  let x : ℕ → P.V := fun i => (C.getVert i).1
  have hadj : ∀ i < L, P.G.Adj (x i) (x (i + 1)) := fun i hi => C.adj_getVert_succ hi
  have hacc : ∀ i, cycleLCP.Acc P ℓ (x i) := fun i => (C.getVert i).2
  let col : ℕ → Bool := fun i => ecol P ℓ (x i) (x (i + 1))
  have step : ∀ i, i + 1 < L → col (i + 1) = !col i := by
    intro i hi
    have hne : x i ≠ x (i + 2) := by
      intro e
      exact hC.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega) (Subtype.ext e)
    have h1 := ecol_ne P ℓ (hacc (i + 1)) (hadj i (by omega)).symm (hadj (i + 1) hi) hne
    have h2 := ((cycle_acc P ℓ (hacc (i + 1))).2 (x i) (hadj i (by omega)).symm).2
    simp only [col]
    rw [← h2] at h1
    revert h1; cases ecol P ℓ (x i) (x (i + 1)) <;> cases ecol P ℓ (x (i + 1)) (x (i + 1 + 1)) <;>
      simp
  have hcol : ∀ i, i < L → col i = (col 0 ^^ decide (i % 2 = 1)) := by
    intro i
    induction i with
    | zero => intro; simp
    | succ i ih =>
      intro hi
      rw [step i hi, ih (by omega)]
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · have : (i + 1) % 2 = 1 := by omega
        simp [h, this]
      · have : (i + 1) % 2 = 0 := by omega
        simp [h, this]
  -- wrap-around at `y`
  have hxL : x L = x 0 := by simp [x, L, Walk.getVert_length]
  have hne : x 1 ≠ x (L - 1) := by
    intro e
    apply hC.snd_ne_penultimate
    rw [Walk.snd, Walk.penultimate]
    exact Subtype.ext e
  have h0 : x 0 = y.1 := by simp [x]
  have hA1 : P.G.Adj (x 0) (x 1) := hadj 0 (by omega)
  have hA2 : P.G.Adj (x 0) (x (L - 1)) := by
    have := (hadj (L - 1) (by omega)).symm
    rwa [show L - 1 + 1 = L by omega, hxL] at this
  have hw := ecol_ne P ℓ (hacc 0) hA1 hA2 hne
  have hagree := ((cycle_acc P ℓ (hacc 0)).2 (x (L - 1)) hA2).2
  have hlast : col (L - 1) = ecol P ℓ (x (L - 1)) (x 0) := by
    simp only [col]; rw [show L - 1 + 1 = L by omega, hxL]
  have hc0 : col 0 = ecol P ℓ (x 0) (x 1) := rfl
  rw [← hagree, ← hlast, ← hc0, hcol (L - 1) (by omega)] at hw
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have : (L - 1) % 2 = 0 := by obtain ⟨k, hk⟩ := hodd; omega
  simp [this] at hw

/-- **Strong soundness of Lemma 4.2** on every graph and for every labelling. -/
theorem cycleLCP_stronglySoundAll : cycleLCP.StronglySoundAll 2 := by
  intro P ℓ
  rw [two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨y, C, hC, hCo⟩ := exists_odd_cycle _ w rfl hodd
  exact (Nat.not_even_iff_odd.2 hCo) (cycle_even P ℓ C hC)

end Soundness

/-! ### Completeness on even cycles -/

lemma cycleGraph_adj_val {m : ℕ} (hm : 2 ≤ m) (a b : Fin m) :
    (cycleGraph m).Adj a b ↔ b.val = a.val + 1 ∨ a.val = b.val + 1 ∨
      (a.val = 0 ∧ b.val = m - 1) ∨ (b.val = 0 ∧ a.val = m - 1) := by
  rw [cycleGraph_adj']
  have key : ∀ u v : Fin m, (u - v).val = 1 ↔ u.val = v.val + 1 ∨ (u.val = 0 ∧ v.val = m - 1) := by
    intro u v
    have hu := u.isLt; have hv := v.isLt
    rcases le_or_gt v u with h | h
    · rw [(Fin.coe_sub_iff_le).2 h]; rw [Fin.le_def] at h; omega
    · rw [(Fin.coe_sub_iff_lt).2 h]; rw [Fin.lt_def] at h; omega
  rw [key, key]
  omega

/-- The proper 2-edge-colouring of `C_m` (`m` even): edge `{i, i+1}` gets colour `i mod 2`. -/
def cycColor {m : ℕ} (a b : Fin m) : Bool :=
  decide ((if b.val = a.val + 1 ∨ (b.val = 0 ∧ a.val = m - 1) then a.val else b.val) % 2 = 1)

lemma cycColor_symm {m : ℕ} (hm : 4 ≤ m) {a b : Fin m} (h : (cycleGraph m).Adj a b) :
    cycColor a b = cycColor b a := by
  rw [cycleGraph_adj_val (by omega)] at h
  have := a.isLt; have := b.isLt
  unfold cycColor
  simp only [decide_eq_decide]
  split_ifs <;> omega

lemma cycColor_ne {m : ℕ} (hm : 4 ≤ m) (hev : Even m) {a b b' : Fin m}
    (h : (cycleGraph m).Adj a b) (h' : (cycleGraph m).Adj a b') (hne : b ≠ b') :
    cycColor a b ≠ cycColor a b' := by
  rw [cycleGraph_adj_val (by omega)] at h h'
  have hne' : b.val ≠ b'.val := fun e => hne (Fin.ext e)
  have := a.isLt; have := b.isLt; have := b'.isLt
  obtain ⟨k, hk⟩ := hev
  unfold cycColor
  split_ifs <;> simp only [ne_eq, decide_eq_decide] <;> omega

section Complete

variable (P : PortGraph) {m : ℕ} (e : P.G ≃g cycleGraph m)

open Classical in
/-- The neighbour at port `i` (if any). -/
noncomputable def nbAt (v : P.V) (i : ℕ) : P.V :=
  if h : ∃ w, P.G.Adj v w ∧ P.port v w = i then h.choose else v

lemma nbAt_spec {v : P.V} {i : ℕ} (h : ∃ w, P.G.Adj v w ∧ P.port v w = i) :
    P.G.Adj v (nbAt P v i) ∧ P.port v (nbAt P v i) = i := by
  unfold nbAt; rw [dite_eq_left h]; exact h.choose_spec

lemma nbAt_port {v w : P.V} (h : P.G.Adj v w) : nbAt P v (P.port v w) = w := by
  have := nbAt_spec P ⟨w, h, rfl⟩
  exact P.port_inj this.1 h this.2

/-- The honest certificate of `v`. -/
noncomputable def cycLabel (v : P.V) : LC :=
  (⟨0, P.port (nbAt P v 0) v, cycColor (e v) (e (nbAt P v 0))⟩,
    ⟨1, P.port (nbAt P v 1) v, cycColor (e v) (e (nbAt P v 1))⟩)

lemma entryOf_cycLabel (v : P.V) {i : ℕ} (hi : i < 2) :
    entryOf (cycLabel P e v) i = ⟨i, P.port (nbAt P v i) v, cycColor (e v) (e (nbAt P v i))⟩ := by
  unfold entryOf cycLabel
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp

end Complete

/-- Even cycles (of length ≥ 4). -/
def EvenCycleClass : GraphClass := fun _ G => ∃ n, 2 ≤ n ∧ Nonempty (G ≃g cycleGraph (2 * n))

/-- **Completeness of Lemma 4.2** on even cycles. -/
theorem cycleLCP_complete : cycleLCP.Complete bound EvenCycleClass := by
  rintro P - ⟨n, hn, ⟨e⟩⟩
  have hm : 4 ≤ 2 * n := by omega
  have hdeg : ∀ v, P.G.degree v = 2 := by
    intro v
    rw [← e.degree_eq]
    obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 3 := ⟨2 * n - 3, by omega⟩
    revert e; rw [hk]; intro e; exact cycleGraph_degree_three_le
  -- both ports are used
  have hports : ∀ v, ∀ i < 2, ∃ w, P.G.Adj v w ∧ P.port v w = i := by
    intro v i hi
    obtain ⟨a, b, hab, hnb⟩ := Finset.card_eq_two.1 ((P.G.card_neighborFinset_eq_degree v).trans (hdeg v))
    have ha : P.G.Adj v a := (P.G.mem_neighborFinset v a).1 (by rw [hnb]; simp)
    have hb : P.G.Adj v b := (P.G.mem_neighborFinset v b).1 (by rw [hnb]; simp)
    have pa := P.port_lt ha; have pb := P.port_lt hb
    rw [hdeg] at pa pb
    have hp : P.port v a ≠ P.port v b := fun h => hab (P.port_inj ha hb h)
    rcases (by omega : P.port v a = i ∨ P.port v b = i) with h | h
    · exact ⟨a, ha, h⟩
    · exact ⟨b, hb, h⟩
  refine ⟨cycLabel P e, fun _ => trivial, fun v => ?_⟩
  simp only [LCP.Acc, cycleLCP, decide_eq_true_eq, cycleRule]
  refine ⟨hdeg v, rfl, rfl, ?_, ?_⟩
  · show cycColor (e v) (e (nbAt P v 0)) ≠ cycColor (e v) (e (nbAt P v 1))
    obtain ⟨h0, p0⟩ := nbAt_spec P (hports v 0 (by omega))
    obtain ⟨h1, p1⟩ := nbAt_spec P (hports v 1 (by omega))
    refine cycColor_ne hm ⟨n, by omega⟩ (e.map_adj_iff.2 h0) (e.map_adj_iff.2 h1) ?_
    intro h; have := e.injective h; rw [this] at p0; omega
  · intro x hx
    obtain ⟨w, hw, rfl⟩ := P.mem_view_nbrs.1 hx
    have hlt : P.port v w < 2 := hdeg v ▸ P.port_lt hw
    have hlt' : P.port w v < 2 := hdeg w ▸ P.port_lt hw.symm
    simp only [PortGraph.nbrInfo, PortGraph.view]
    rw [entryOf_cycLabel P e v hlt, entryOf_cycLabel P e w hlt', nbAt_port P hw,
      nbAt_port P hw.symm]
    exact ⟨hlt, rfl, by rw [cycColor_symm hm (e.map_adj_iff.2 hw)]⟩

/-! ### Hiding on `C₄` -/

/-- Ports of `C₄` invariant under the reflection `0 ↔ 1, 2 ↔ 3`. -/
def c4Port (v w : Fin 4) : ℕ :=
  match v.val, w.val with
  | 0, 1 => 1 | 1, 0 => 1 | 2, 3 => 1 | 3, 2 => 1 | _, _ => 0

/-- `C₄` with these ports, identifiers `i ↦ i`. -/
abbrev c4PG (N : ℕ) (hN : 4 ≤ N) : PortGraph where
  V := Fin 4
  G := cycleGraph 4
  port := c4Port
  port_lt := fun {v w} h => by
    have : ∀ v w : Fin 4, (cycleGraph 4).Adj v w → c4Port v w < (cycleGraph 4).degree v := by
      decide
    exact this v w h
  port_inj := fun {v w w'} => by revert v w w'; decide
  id := fun v => v.val
  id_inj := fun a b h => Fin.ext h
  N := N
  id_lt v := lt_of_lt_of_le v.isLt hN

/-- The honest certificates for the 2-edge-colouring `{0,1} ↦ 0, {1,2} ↦ 1, {2,3} ↦ 0,
{3,0} ↦ 1`: all four nodes get the same certificate. -/
def c4Lab : Fin 4 → LC := fun _ => (⟨0, 0, true⟩, ⟨1, 1, false⟩)

lemma c4_acc4 : ∀ v, cycleLCP.Acc (c4PG 4 le_rfl) c4Lab v := by decide

lemma c4_acc (N : ℕ) (hN : 4 ≤ N) : ∀ v, cycleLCP.Acc (c4PG N hN) c4Lab v := c4_acc4

lemma c4_anon (N : ℕ) (hN : 4 ≤ N) :
    ((c4PG N hN).view c4Lab (0 : Fin 4)).anon = ((c4PG N hN).view c4Lab (1 : Fin 4)).anon := by
  rw [PortGraph.view_eq_mk (P := c4PG N hN) ({1, 3} : Finset (Fin 4))
      (by decide : ∀ w : Fin 4, (cycleGraph 4).Adj 0 w ↔ w ∈ ({1, 3} : Finset (Fin 4))),
    PortGraph.view_eq_mk (P := c4PG N hN) ({0, 2} : Finset (Fin 4))
      (by decide : ∀ w : Fin 4, (cycleGraph 4).Adj 1 w ↔ w ∈ ({0, 2} : Finset (Fin 4)))]
  rw [show ({1, 3} : Finset (Fin 4)).val = (1 : Fin 4) ::ₘ {3} by decide,
    show ({0, 2} : Finset (Fin 4)).val = (0 : Fin 4) ::ₘ {2} by decide]
  simp only [View.anon, Multiset.map_cons, Multiset.map_singleton, PortGraph.nbrInfo,
    NbrInfo.anon]
  rfl

/-- **Hiding of Lemma 4.2** against anonymous extraction algorithms, on every class containing
`C₄`: the adjacent nodes `0` and `1` have the same anonymous view. -/
theorem cycleLCP_anonHiding (hb : 4 ≤ bound 4) (H : GraphClass) (hH : H (Fin 4) (cycleGraph 4)) :
    cycleLCP.AnonHiding bound H 2 := fun A =>
  ⟨c4PG (bound 4) hb, by simp [PortGraph.Admissible], hH, c4Lab, fun _ => trivial,
    c4_acc _ hb, (0 : Fin 4), (1 : Fin 4), (show (cycleGraph 4).Adj 0 1 by decide),
    by simp only [Function.comp, c4_anon]⟩

lemma cycleLCP_anonymous : cycleLCP.Anonymous := by
  intro μ μ' h
  simp only [View.anon, AnonView.mk.injEq] at h
  obtain ⟨-, hl, hd, hn⟩ := h
  simp only [cycleLCP]
  apply decide_eq_decide.2
  unfold cycleRule
  rw [hl, hd]
  have e : ∀ (s : Multiset (NbrInfo LC)) (q : AnonNbrInfo LC → Prop),
      (∀ x ∈ s, q x.anon) ↔ ∀ y ∈ s.map NbrInfo.anon, q y := by
    intro s q; simp
  have := e μ.nbrs (fun y => y.portHere < 2 ∧ (entryOf μ'.label y.portHere).there = y.portThere ∧
      entryOf y.label y.portThere = ⟨y.portThere, y.portHere, (entryOf μ'.label y.portHere).c⟩)
  rw [hn, ← e μ'.nbrs] at this
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl this)))

/-- **Lemma 4.2** of arXiv v1: an anonymous, strong and hiding one-round LCP for 2-colouring on
even cycles, with constant-size certificates (ports in `{0,1}` on cycles). -/
theorem lemma_4_2 (hb : 4 ≤ bound 4) :
    cycleLCP.Anonymous ∧ cycleLCP.Complete bound EvenCycleClass ∧ cycleLCP.Sound bound 2 ∧
      cycleLCP.StronglySound bound 2 ∧ cycleLCP.AnonHiding bound EvenCycleClass 2 :=
  ⟨cycleLCP_anonymous, cycleLCP_complete, cycleLCP_stronglySoundAll.stronglySound.sound,
    cycleLCP_stronglySoundAll.stronglySound,
    cycleLCP_anonHiding hb _ ⟨2, le_rfl, ⟨Iso.refl⟩⟩⟩

end Podc.HidingColoringCertification
