import Papers.PODC2025.HidingColoringCertification.MinDegreeOne
import Papers.PODC2025.HidingColoringCertification.Theorem42

/-!
# Theorems 4.3 and 4.4: the statements hold, the paper's decoders do not

**Theorem 4.3** (shatter points) and **Theorem 4.4** (watermelons) claim strong and hiding
one-round LCPs with `O(min{Δ², n} + log n)` resp. `O(log n)` certificates. The proofs are in
Section 7 of arXiv:2502.13854v1.

* The statements are true (`theorem_4_3`, `theorem_4_4`): the hard instances of the constant-size
  anonymous LCP of Lemma 4.1 (`P₆ ⊔ K₂`) admit a shatter point, and the counter LCP
  (`ModCounter.lean`, `O(log n)` bits) is hiding on the watermelon `θ(5,5,5)`.
* The paper's shatter-point decoder (`shatterLCP`) is **not strongly sound**
  (`shatterLCP_not_stronglySound`): two type-1 nodes `u, u'` attached to the same type-0 node
  (which rejects) may carry different colour vectors, `(0,0)` and `(0,1)`; then the accepting
  nodes `u – w – u' – z' – z – u` (`w` in component 1, `z, z'` in component 2) form a 5-cycle.
  The proof's step "by condition 2(c), all neighbors of nodes of type 1 share the same color" is
  false (neighbours in different components may have different colours).
* The paper's watermelon decoder (`watermelonLCP`) is **not even sound**
  (`watermelonLCP_not_sound`): rule 2(b) only asks that *some* entry of a path node records the
  endpoint's port, and a path node never checks the entry pointing to an endpoint. On the
  5-cycle `v₁ – a – v₂ – b₂ – b₁ – v₁` (endpoints `v₁, v₂`), `a`'s entry towards `v₂` happens to
  carry `v₁`'s port number, so `v₁` reads the colour of the wrong edge and the parity argument
  breaks: every node accepts a non-bipartite graph.
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-! ### Shatter points -/

/-- Certificates of Theorem 4.3: `(type, content)`. -/
inductive ShLabel where
  /-- type 0: claimed shatter point, with its claimed identifier. -/
  | t0 (id : ℕ)
  /-- type 1: neighbour of the shatter point `id`, colour vector `colors`. -/
  | t1 (id : ℕ) (colors : List Bool)
  /-- type 2: node of component `num` of `G - N[v]`, `v` = shatter point `id`, colour `x`. -/
  | t2 (id : ℕ) (num : ℕ) (x : Bool)
  deriving DecidableEq

open ShLabel

/-- Is the certificate of type 0? -/
def ShLabel.isT0 : ShLabel → Bool
  | t0 _ => true
  | _ => false

/-- Is the certificate of type 1? -/
def ShLabel.isT1 : ShLabel → Bool
  | t1 _ _ => true
  | _ => false

/-- The identifier field. -/
def ShLabel.idf : ShLabel → ℕ
  | t0 i => i
  | t1 i _ => i
  | t2 i _ _ => i

/-- Check of a type-1 node `(i, cs)` on a neighbour's certificate (rule 2(c)). -/
def ShLabel.okFromT1 (i : ℕ) (cs : List Bool) : ShLabel → Bool
  | t2 j n b => decide (j = i ∧ cs[n]? = some b)
  | _ => true

/-- Check of a type-2 node `(i, n, b)` on a neighbour's certificate (rules 3(b), 3(c)). -/
def ShLabel.okFromT2 (i n : ℕ) (b : Bool) : ShLabel → Bool
  | t1 j cs => decide (j = i ∧ cs[n]? = some b)
  | t2 j m b' => decide (j = i ∧ m = n ∧ b' ≠ b)
  | _ => true

/-- The decoder of Theorem 4.3 (rules 1, 2(a–c), 3(a–c) of arXiv v1, p. 25–26). The colour
check `colors_# = x` fails if `#` is out of range (stricter than the paper). -/
def shatterRule (μ : View ShLabel) : Prop :=
  match μ.label with
  | t0 i => i = μ.id ∧ (∀ x ∈ μ.nbrs, x.label.isT1 = true ∧ x.label.idf = μ.id) ∧
      ∀ x ∈ μ.nbrs, ∀ y ∈ μ.nbrs, x.label = y.label
  | t1 i cs =>
      (∀ x ∈ μ.nbrs, x.label.isT1 = false) ∧
      μ.nbrs.countP (fun x => x.label.isT0 = true) = 1 ∧
      (∀ x ∈ μ.nbrs, x.label.isT0 = true → x.label.idf = i) ∧
      (∀ x ∈ μ.nbrs, x.label.okFromT1 i cs = true)
  | t2 i n b =>
      (∀ x ∈ μ.nbrs, x.label.isT0 = false) ∧
      (∀ x ∈ μ.nbrs, x.label.okFromT2 i n b = true)

instance (μ : View ShLabel) : Decidable (shatterRule μ) := by
  unfold shatterRule; split <;> infer_instance

/-- The LCP of Theorem 4.3. -/
def shatterLCP : LCP ShLabel where
  D μ := decide (shatterRule μ)
  sz _ := Set.univ

/-- Counterexample graph: shatter point candidate `0`, type-1 nodes `1, 2`, type-2 nodes
`3` (component 0) and `4, 5` (component 1). The nodes `1,3,2,5,4` form a 5-cycle. -/
def shG : SimpleGraph (Fin 6) := edgeGraph 6 [(0,1),(0,2),(1,3),(2,3),(1,4),(2,5),(4,5)]

instance : DecidableRel shG.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

/-- The malicious certificates. -/
def shLab : Fin 6 → ShLabel :=
  ![t0 0, t1 0 [false, false], t1 0 [false, true], t2 0 0 false, t2 0 1 false, t2 0 1 true]

lemma shG_acc6 : ∀ v : Fin 6, v ≠ 0 → shatterLCP.Acc (PortGraph.ofFin shG 6 le_rfl) shLab v := by
  decide

lemma not_colorable_of_c5 {V : Type*} {G : SimpleGraph V} {a b c d e : V} (h1 : G.Adj a b)
    (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d e) (h5 : G.Adj e a) : ¬ G.Colorable 2 := by
  rintro ⟨col⟩
  have e1 := fin_two_eq_of_ne_ne (col.valid h1) (col.valid h2)
  have e2 := fin_two_eq_of_ne_ne (col.valid h3) (col.valid h4)
  exact col.valid h5 (by rw [← e2, ← e1])

/-- **The decoder of Theorem 4.3 is not strongly sound.** -/
theorem shatterLCP_not_stronglySound (bound : ℕ → ℕ) (hb : 6 ≤ bound 6) :
    ¬ shatterLCP.StronglySound bound 2 := by
  intro h
  have hacc : ∀ v : Fin 6, v ≠ 0 →
      shatterLCP.Acc (PortGraph.ofFin shG (bound 6) hb) shLab v := fun v hv => shG_acc6 v hv
  have hcol := h (PortGraph.ofFin shG (bound 6) hb) (by simp [PortGraph.Admissible])
    (not_colorable_of_c5 (G := shG) (a := 1) (b := 3) (c := 2) (d := 5) (e := 4)
      (by decide) (by decide) (by decide) (by decide) (by decide)) shLab (fun _ => trivial)
  exact not_colorable_of_c5 (G := shatterLCP.accGraph (PortGraph.ofFin shG (bound 6) hb) shLab)
    (a := ⟨1, hacc 1 (by decide)⟩) (b := ⟨3, hacc 3 (by decide)⟩) (c := ⟨2, hacc 2 (by decide)⟩)
    (d := ⟨5, hacc 5 (by decide)⟩) (e := ⟨4, hacc 4 (by decide)⟩)
    (show shG.Adj 1 3 by decide) (show shG.Adj 3 2 by decide) (show shG.Adj 2 5 by decide)
    (show shG.Adj 5 4 by decide) (show shG.Adj 4 1 by decide) hcol

/-! ### Watermelons -/

/-- Certificates of Theorem 4.4 (ports are 0-based: entry `i` describes the edge at port `i`). -/
inductive WmLabel where
  /-- type 1: an endpoint; identifiers of the two endpoints. -/
  | t1 (id1 id2 : ℕ)
  /-- type 2: an inner path node; endpoints, path number, and for its ports 0 and 1 the port at
  the other end and the colour of the edge. -/
  | t2 (id1 id2 num p0 : ℕ) (c0 : Bool) (p1 : ℕ) (c1 : Bool)
  deriving DecidableEq


/-- The endpoint identifiers of a certificate. -/
def WmLabel.ids : WmLabel → ℕ × ℕ
  | .t1 a b => (a, b)
  | .t2 a b .. => (a, b)

/-- Entry `i` (port `p`, colour `c`) of a type-2 certificate. -/
def WmLabel.entry : WmLabel → ℕ → Option (ℕ × Bool)
  | .t2 _ _ _ p0 c0 _ _, 0 => some (p0, c0)
  | .t2 _ _ _ _ _ p1 c1, 1 => some (p1, c1)
  | _, _ => none

/-- Path number of a type-2 certificate. -/
def WmLabel.num : WmLabel → Option ℕ
  | .t2 _ _ n .. => some n
  | _ => none

/-- Colours of the entries of `l` that record the port `p`. -/
def WmLabel.matchCol (l : WmLabel) (p : ℕ) : List Bool :=
  [0, 1].filterMap fun i => (l.entry i).bind fun e => if e.1 = p then some e.2 else none

/-- Is the certificate of type 1? -/
def WmLabel.isT1 : WmLabel → Bool
  | .t1 .. => true
  | _ => false

/-- Rule 3(c) for a neighbour at our port `ph`: with `(j, c)` our entry `ph`, the neighbour's
entry `j` must be `(ph, c)`. -/
def WmLabel.entryOk (me : WmLabel) (ph : ℕ) (nb : WmLabel) : Bool :=
  match me.entry ph with
  | some (j, c) => decide (nb.entry j = some (ph, c))
  | none => false

/-- The decoder of Theorem 4.4 (rules 1, 2(a–d), 3(a–c) of arXiv v1, p. 28), with the format
checks `id₁ < id₂` and `c₁ ≠ c₂`. -/
def watermelonRule (μ : View WmLabel) : Prop :=
  μ.label.ids.1 < μ.label.ids.2 ∧ (∀ x ∈ μ.nbrs, x.label.ids = μ.label.ids) ∧
  match μ.label with
  | .t1 i1 i2 =>
      (i1 = μ.id ∨ i2 = μ.id) ∧
      -- 2(b): every neighbour is of type 2 and records our port in *some* entry
      (∀ x ∈ μ.nbrs, x.label.num.isSome ∧ x.label.matchCol x.portHere ≠ []) ∧
      -- 2(c): distinct path numbers
      (μ.nbrs.map (fun x => x.label.num)).Nodup ∧
      -- 2(d): the colours of the matching entries form a singleton
      ∃ c : Bool, ∀ x ∈ μ.nbrs, ∀ c' ∈ x.label.matchCol x.portHere, c' = c
  | .t2 _ _ n _ c0 _ c1 =>
      c0 ≠ c1 ∧ μ.deg = 2 ∧
      (∀ x ∈ μ.nbrs, x.portHere < 2) ∧
      -- 3(b): a type-1 neighbour is one of the endpoints
      (∀ x ∈ μ.nbrs, x.label.isT1 = true → μ.label.ids.1 = x.id ∨ μ.label.ids.2 = x.id) ∧
      -- 3(c): a type-2 neighbour at port `i` has the same path number, and with `j = pᵢ` its
      -- entry `j` records port `i` and the same colour
      (∀ x ∈ μ.nbrs, x.label.num.isSome → x.label.num = some n ∧
        μ.label.entryOk x.portHere x.label = true)

instance (μ : View WmLabel) : Decidable (watermelonRule μ) := by
  unfold watermelonRule; split <;> infer_instance

/-- The LCP of Theorem 4.4. -/
def watermelonLCP : LCP WmLabel where
  D μ := decide (watermelonRule μ)
  sz _ := Set.univ

/-- The 5-cycle `0 – 2 – 1 – 4 – 3 – 0`: endpoints `0, 1`, path nodes `2` (path 0) and `3, 4`
(path 1). -/
def wmG : SimpleGraph (Fin 5) := edgeGraph 5 [(0,2),(2,1),(0,3),(3,4),(4,1)]

instance : DecidableRel wmG.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

/-- Ports: `0`: `2 ↦ 0, 3 ↦ 1`; `1`: `2 ↦ 0, 4 ↦ 1`; `2`: `0 ↦ 0, 1 ↦ 1`; `3`: `4 ↦ 0, 0 ↦ 1`;
`4`: `3 ↦ 0, 1 ↦ 1`. -/
def wmPort (v w : Fin 5) : ℕ :=
  match v.val, w.val with
  | 0, 3 => 1 | 1, 4 => 1 | 2, 1 => 1 | 3, 0 => 1 | 4, 1 => 1 | _, _ => 0

/-- The 5-cycle with these ports. -/
abbrev wmPG (N : ℕ) (hN : 5 ≤ N) : PortGraph where
  V := Fin 5
  G := wmG
  port := wmPort
  port_lt := fun {v w} h => by revert v w; decide
  port_inj := fun {v w w'} => by revert v w w'; decide
  id := fun v => v.val
  id_inj := fun a b h => Fin.ext h
  N := N
  id_lt v := lt_of_lt_of_le v.isLt hN

/-- The malicious certificates: node `2`'s entry for port 0 (towards `0`) carries the wrong port
`1`, its entry for port 1 (towards `1`) carries port `0`, which is also `0`'s port towards `2`. -/
def wmLab : Fin 5 → WmLabel :=
  ![.t1 0 1, .t1 0 1, .t2 0 1 0 1 true 0 false, .t2 0 1 1 0 true 1 false,
    .t2 0 1 1 0 true 1 false]

lemma wm_acc5 : ∀ v : Fin 5, watermelonLCP.Acc (wmPG 5 le_rfl) wmLab v := by
  decide

/-- **The decoder of Theorem 4.4 is not sound**: every node of a 5-cycle accepts. -/
theorem watermelonLCP_not_sound (bound : ℕ → ℕ) (hb : 5 ≤ bound 5) :
    ¬ watermelonLCP.Sound bound 2 := by
  intro h
  obtain ⟨v, hv⟩ := h (wmPG (bound 5) hb) (by simp [PortGraph.Admissible])
    (not_colorable_of_c5 (G := wmG) (a := 0) (b := 2) (c := 1) (d := 4) (e := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide)) wmLab (fun _ => trivial)
  exact hv (wm_acc5 v)

/-! ### The statements of Theorems 4.3 and 4.4 hold -/

/-- `G` admits a shatter point: `G - N[v]` is disconnected for some `v`. -/
def HasShatterPoint {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ v a b, ∃ (ha : ¬ G.Adj v a ∧ a ≠ v) (hb : ¬ G.Adj v b ∧ b ≠ v),
    ¬ (G.induce {x | ¬ G.Adj v x ∧ x ≠ v}).Reachable ⟨a, ha⟩ ⟨b, hb⟩

lemma not_reachable_of_isolated {V : Type} {G : SimpleGraph V} {a b : V} (hab : a ≠ b)
    (ha : ∀ w, ¬ G.Adj a w) : ¬ G.Reachable a b := by
  rintro ⟨p⟩
  cases p with
  | nil => exact hab rfl
  | cons h _ => exact ha _ h

lemma not_reachable_induce {V : Type} {G : SimpleGraph V} {s : Set V} {a b : V} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) (hiso : ∀ w ∈ s, ¬ G.Adj a w) :
    ¬ (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩ :=
  not_reachable_of_isolated (by simpa using hab) (fun w h => hiso w.1 w.2 (by simpa using h))

/-- The path `0–1–2–3–4–5`. -/
def path6 : SimpleGraph (Fin 6) := edgeGraph 6 [(0,1),(1,2),(2,3),(3,4),(4,5)]

instance : DecidableRel path6.Adj := inferInstanceAs (DecidableRel (edgeGraph _ _).Adj)

lemma path6_shatter : HasShatterPoint path6 :=
  ⟨2, 0, 4, by decide, by decide,
    not_reachable_induce _ _ (by decide) (fun w hw => by revert w; decide)⟩

lemma path6_colorable : path6.Colorable 2 :=
  ⟨Coloring.mk (fun v => (⟨v.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))
    (fun {a b} h => by revert a b; decide)⟩

lemma p6k2_shatter : HasShatterPoint p6k2 :=
  ⟨2, 0, 4, by decide, by decide,
    not_reachable_induce _ _ (by decide) (fun w hw => by revert w; decide)⟩

/-- Ports of the path: inner nodes have port 0 towards smaller indices. -/
def path6Port (v w : Fin 6) : ℕ := if v.val = 0 ∨ v.val = 5 then 0 else if w < v then 0 else 1

/-- `path6` with rotating identifiers on `0..4`. -/
abbrev path6PG (s N : ℕ) (hN : 6 ≤ N) : PortGraph where
  V := Fin 6
  G := path6
  port := path6Port
  port_lt := fun {v w} h => by
    have : ∀ v w : Fin 6, path6.Adj v w → path6Port v w < path6.degree v := by decide
    exact this v w h
  port_inj := fun {v w w'} => by revert v w w'; decide
  id := fun v => if v.val < 5 then (s + v.val) % 5 else 5
  id_inj := fun a b h => by
    apply Fin.ext; simp only at h; split_ifs at h <;> omega
  N := N
  id_lt v := by
    show (if v.val < 5 then (s + v.val) % 5 else 5) < N
    split_ifs <;> omega

/-- Counter labelling `v ↦ t + v`. -/
def path6Label {M : ℕ} [NeZero M] (t : ZMod M) (v : Fin 6) : ℕ := (t + (v.val : ZMod M)).val

lemma path6_view_shift (N : ℕ) (hN : 6 ≤ N) (t : ZMod (modulus N)) :
    (path6PG (t + 1).val N hN).view (path6Label (t + 1)) (2 : Fin 6) =
      (path6PG t.val N hN).view (path6Label t) (3 : Fin 6) := by
  rw [PortGraph.view_eq_mk (P := path6PG (t + 1).val N hN) ({1, 3} : Finset (Fin 6))
      (by decide : ∀ w : Fin 6, path6.Adj 2 w ↔ w ∈ ({1, 3} : Finset (Fin 6))),
    PortGraph.view_eq_mk (P := path6PG t.val N hN) ({2, 4} : Finset (Fin 6))
      (by decide : ∀ w : Fin 6, path6.Adj 3 w ↔ w ∈ ({2, 4} : Finset (Fin 6)))]
  simp only [PortGraph.nbrInfo, View.mk.injEq, true_and]
  have hid : ∀ i : ℕ, ((t + 1).val + i) % 5 = (t.val + (i + 1)) % 5 := fun i => by
    rw [val_add_one_mod_five]; ring_nf
  have hlab : ∀ a b : Fin 6, b.val = a.val + 1 → path6Label (t + 1) a = path6Label t b :=
    fun a b h => by
      unfold path6Label; rw [h]; congr 1; push_cast; ring
  refine ⟨?_, hlab 2 3 rfl, ?_⟩
  · simpa using hid 2
  · refine ⟨by decide, ?_⟩
    rw [show ({1, 3} : Finset (Fin 6)).val = (1 : Fin 6) ::ₘ {3} by decide,
      show ({2, 4} : Finset (Fin 6)).val = (2 : Fin 6) ::ₘ {4} by decide]
    simp only [Multiset.map_cons, Multiset.map_singleton, PortGraph.nbrInfo]
    have e1 : (if (1 : Fin 6).val < 5 then ((t + 1).val + (1 : Fin 6).val) % 5 else 5) =
        (if (2 : Fin 6).val < 5 then (t.val + (2 : Fin 6).val) % 5 else 5) := by
      simpa using hid 1
    have e2 : (if (3 : Fin 6).val < 5 then ((t + 1).val + (3 : Fin 6).val) % 5 else 5) =
        (if (4 : Fin 6).val < 5 then (t.val + (4 : Fin 6).val) % 5 else 5) := by
      simpa using hid 3
    rw [e1, e2, hlab 1 2 rfl, hlab 3 4 rfl]
    simp only [show path6Port 2 1 = 0 by decide, show path6Port 3 2 = 0 by decide,
      show path6Port 1 2 = 1 by decide, show path6Port 2 3 = 1 by decide,
      show path6Port 3 4 = 1 by decide, show path6Port 4 3 = 0 by decide,
      show path6.degree 1 = 2 by decide, show path6.degree 2 = 2 by decide,
      show path6.degree 3 = 2 by decide, show path6.degree 4 = 2 by decide]

/-- The counter LCP is hiding on every class containing the path `P₆`. -/
theorem counterLCP_hiding_path6 {bound : ℕ → ℕ} (hb : 6 ≤ bound 6) (H : GraphClass)
    (hH : H (Fin 6) path6) : (counterLCP bound).Hiding bound H 2 := by
  refine hiding_of_shift (counterLCP bound) bound H (modulus (bound 6)) (modulus_odd _)
    (fun t => path6PG t.val (bound 6) hb) (fun t => path6Label t)
    (fun t => by simp [PortGraph.Admissible]) (fun _ => hH) (fun t v => ?_) (fun t v => ?_)
    (fun _ => (2 : Fin 6)) (fun _ => (3 : Fin 6)) (fun _ => show path6.Adj 2 3 by decide)
    (fun t => path6_view_shift (bound 6) hb t)
  · show path6Label t v < modulus (bound (Fintype.card (Fin 6)))
    rw [Fintype.card_fin]; exact ZMod.val_lt _
  · rw [counterLCP_acc_iff]
    intro w hw
    unfold CounterStep
    simp only [path6Label, ZMod.natCast_zmod_val]
    have : ∀ v w : Fin 6, path6.Adj v w → w.val = v.val + 1 ∨ v.val = w.val + 1 := by decide
    rcases this v w hw with h | h
    · left; rw [h]; push_cast; ring
    · right; rw [h]; push_cast; ring

/-- The bipartite graphs admitting a shatter point. -/
def ShatterClass : GraphClass := fun _ G => G.Colorable 2 ∧ HasShatterPoint G

/-- **Theorem 4.3 (statement)**: there is a strong and hiding one-round LCP for `2-col_H`, `H` =
graphs with a shatter point, with `O(log n)`-bit certificates — the counter LCP; and even an
anonymous one with constant-size certificates (hiding against anonymous algorithms): the LCP of
Lemma 4.1. -/
theorem theorem_4_3 {bound : ℕ → ℕ} (hb6 : 6 ≤ bound 6) (hb8 : 8 ≤ bound 8) :
    ((counterLCP bound).Complete bound ShatterClass ∧ (counterLCP bound).Sound bound 2 ∧
      (counterLCP bound).StronglySound bound 2 ∧ (counterLCP bound).Hiding bound ShatterClass 2) ∧
    (degOneLCP.Anonymous ∧ degOneLCP.Complete bound ShatterClass ∧ degOneLCP.Sound bound 2 ∧
      degOneLCP.StronglySound bound 2 ∧ degOneLCP.AnonHiding bound ShatterClass 2) := by
  refine ⟨⟨fun P hP hH => counterLCP_complete P hP hH.1,
    counterLCP_stronglySoundAll.stronglySound.sound, counterLCP_stronglySoundAll.stronglySound,
    counterLCP_hiding_path6 hb6 _ ⟨path6_colorable, path6_shatter⟩⟩,
    degOneLCP_anonymous, fun P hP hH => degOneLCP_complete P hP hH.1,
    degOneLCP_stronglySoundAll.stronglySound.sound, degOneLCP_stronglySoundAll.stronglySound,
    degOneLCP_anonHiding hb8 _ ⟨p6k2_colorable, p6k2_shatter⟩⟩

/-- **Theorem 4.4 (statement)**: the counter LCP (`O(log n)`-bit certificates) is a strong and
hiding one-round LCP for `2-col_H` for every class `H` of bipartite graphs containing the
watermelon `θ(5,5,5)` (three paths of length 5 between the endpoints `4` and `5`), e.g. the
bipartite watermelons. -/
theorem theorem_4_4 {bound : ℕ → ℕ} (hb : 14 ≤ bound 14) (H : GraphClass)
    (hHbip : ∀ V G, H V G → G.Colorable 2) (hθ : H (Fin 14) thetaG) :
    (counterLCP bound).Complete bound H ∧ (counterLCP bound).Sound bound 2 ∧
      (counterLCP bound).StronglySound bound 2 ∧ (counterLCP bound).Hiding bound H 2 :=
  let h := counterLCP_strong_hiding hb H hHbip hθ
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end Podc.HidingColoringCertification
