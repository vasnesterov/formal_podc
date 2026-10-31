import Papers.PODC2025.DynamicSubgraphFinding.FullHist

/-!
# The algorithm of Theorem 1.4 (one-round `MemList(K₃)` under edge insertions)

Section 5.2 of the paper. The algorithm is given as a full-history algorithm (`histAlg`), with
parameters `d` (window of the recent records), `T ≥ 1` (period of the neighbourhood updates),
`K` (alphabet of one update block) and an injective encoding
`enc : (Fin Δ → Option V) → (Fin T → Fin K)` of neighbourhood lists into `T` blocks.

Message of `u` to its neighbour `x` in round `r` (`Msg Δ d K`):
* `(Signal)` — `u` obtained a new neighbour in round `r` (Step 1);
* only if `x` is a *new* neighbour (the edge `{u, x}` was inserted in round `r`): the recent records
  `R^d_edge(u)` (ages `a ∈ [1, d]` such that `u` obtained a new edge in round `r - a`) and
  `R^d_signal(u)` (ages `a ∈ [1, d]` such that some neighbour sent `u` a `(Signal)` in round
  `r - a`), each as a padded list of at most `Δ` resp. `Δ²` ages (Step 2);
* one block of the periodic neighbourhood update along `{u, x}` (Step 3): the stream `u → x`
  starts in round `s₀ = max 1 t_{ux}` (`t_{ux}` = round in which `{u, x}` appeared, `0` for edges
  of `G⁰`); in round `s₀ + kT + j` (`j < T`) `u` sends block `j` of the encoding of its
  neighbourhood in round `s₀ + kT`.

Output of `z` after round `r`: the triples `{z, x, y}` (`x ≠ y` current neighbours of `z`) for
which `z` has evidence (`Ev`) for the edge `{x, y}`: the edge is in `G⁰` (`EvG0`); `x` and `y`
both sent `(Signal)` in the same round (`EvSig`, the paper's rule for node `w`); a complete period
of updates from `x` lists `y` (`EvPer`, case `t_uv - t_uw > d`); the recent records sent by `x` when
`{x, z}` was inserted show it (`EvRSig`: rule for node `u`, `EvREdge`: rule for node `v`, case
`t_uv - t_uw ≤ d`).
-/

namespace Podc.DynamicSubgraphFinding

open Classical

namespace Alg14

variable {V : Type}

/-! ### Generic helpers -/

/-- The set of neighbours given by a local input (`∅` for an absent node). -/
def setOf : Option (Set V) → Set V
  | some N => N
  | none => ∅

/-- A finite set of size `≤ k`, encoded as a padded list of length `k`. -/
noncomputable def listEnc {α : Type} (k : ℕ) (S : Finset α) : Fin k → Option α :=
  fun i => S.toList[i.val]?

lemma listEnc_sound {α : Type} {k : ℕ} {S : Finset α} {i : Fin k} {a : α}
    (h : listEnc k S i = some a) : a ∈ S :=
  Finset.mem_toList.1 (List.mem_of_getElem? h)

lemma listEnc_complete {α : Type} {k : ℕ} {S : Finset α} (hk : S.card ≤ k) {a : α} (ha : a ∈ S) :
    ∃ i, listEnc k S i = some a := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 ha)
  refine ⟨⟨i, lt_of_lt_of_le hi (by simpa using hk)⟩, ?_⟩
  simp [listEnc, List.getElem?_eq_getElem hi, he]

/-- A set of nodes as a `Finset`. -/
noncomputable def toFs [Fintype V] (S : Set V) : Finset V := Finset.univ.filter (· ∈ S)

lemma mem_toFs [Fintype V] {S : Set V} {v : V} : v ∈ toFs S ↔ v ∈ S := by simp [toFs]

lemma card_toFs [Fintype V] (S : Set V) : (toFs S).card = S.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext v
  simp [toFs]

/-- The first index satisfying `P` (`0` if there is none). -/
noncomputable def firstP (P : ℕ → Prop) : ℕ := if h : ∃ k, P k then Nat.find h else 0

lemma firstP_spec {P : ℕ → Prop} {m : ℕ} (hm : P m) :
    P (firstP P) ∧ firstP P ≤ m ∧ ∀ j < firstP P, ¬ P j := by
  have he : ∃ k, P k := ⟨m, hm⟩
  rw [firstP, dite_eq_left_of_eq_true (eq_true he)]
  exact ⟨Nat.find_spec he, Nat.find_min' he hm, fun j hj => Nat.find_min he hj⟩

lemma firstP_congr {P Q : ℕ → Prop} {m : ℕ} (hPQ : ∀ j ≤ m, (P j ↔ Q j)) (hm : P m) :
    firstP P = firstP Q := by
  obtain ⟨h1, h2, h3⟩ := firstP_spec hm
  obtain ⟨g1, g2, g3⟩ := firstP_spec ((hPQ m le_rfl).1 hm)
  refine le_antisymm ?_ ?_
  · by_contra hc
    exact h3 _ (not_le.1 hc) ((hPQ _ g2).2 g1)
  · by_contra hc
    exact g3 _ (not_le.1 hc) ((hPQ _ h2).1 h1)

/-! ### Messages and views of a history -/

/-- A recent-record list: up to `k` ages in `[0, d]`. -/
abbrev RList (k d : ℕ) := Fin k → Option (Fin (d + 1))

/-- Messages: `(Signal)` bit, the recent records `(R^d_edge, R^d_signal)` (only to a new
neighbour), one block of the periodic neighbourhood update. -/
abbrev Msg (Δ d K : ℕ) := Bool × Option (RList Δ d × RList (Δ ^ 2) d) × Fin K

variable {M : Type}

/-- Neighbours in round `k` as seen by a sender in round `h.r + 1` (history `h`, current local
input `x`). -/
def nbrsAt (h : Hist V M) (x : Option (Set V)) (k : ℕ) : Set V :=
  setOf (if k = h.r + 1 then x else h.locH k)

/-- Neighbours in round `k` according to a history. -/
def nb (h : Hist V M) (k : ℕ) : Set V := setOf (h.locH k)

/-- The node obtained a new neighbour in round `k ≥ 1`. -/
def GotNew (h : Hist V M) (x : Option (Set V)) (k : ℕ) : Prop :=
  1 ≤ k ∧ ∃ y, y ∈ nbrsAt h x k ∧ y ∉ nbrsAt h x (k - 1)

/-- Start round of the periodic updates along the edge to `w` (`f k`: neighbours in round `k`):
the round in which the edge appeared, and round `1` for edges of `G⁰`. -/
noncomputable def start (f : ℕ → Set V) (w : V) : ℕ := max 1 (firstP fun k => w ∈ f k)

/-- `R^d_edge` computed in round `r`: ages `a ∈ [1, d]`, `a < r`, such that the node obtained a
new edge in round `r - a`. -/
noncomputable def rEdge (d r : ℕ) (h : Hist V M) (x : Option (Set V)) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun a => 1 ≤ a.val ∧ a.val < r ∧ GotNew h x (r - a.val)

/-- `R^d_signal` computed in round `r`: ages `a ∈ [1, d]`, `a < r`, such that some neighbour sent
the node a `(Signal)` in round `r - a`. -/
noncomputable def rSig {Δ d K : ℕ} (r : ℕ) (h : Hist V (Msg Δ d K)) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun a => 1 ≤ a.val ∧ a.val < r ∧ ∃ w m, h.inbH (r - a.val) w = some (true, m)

variable [Fintype V] {Δ d K T : ℕ}

/-- The message of a node with history `h` and current local input `x` to its neighbour `w` in
round `r`. -/
noncomputable def snd (hT : 0 < T) (enc : (Fin Δ → Option V) → Fin T → Fin K) (r : ℕ)
    (h : Hist V (Msg Δ d K)) (x : Option (Set V)) (w : V) : Msg Δ d K :=
  (decide (GotNew h x r),
    if w ∈ nbrsAt h x r ∧ w ∉ nbrsAt h x (r - 1) then
      some (listEnc Δ (rEdge d r h x), listEnc (Δ ^ 2) (rSig r h)) else none,
    enc (listEnc Δ (toFs (nbrsAt h x (r - (r - start (nbrsAt h x) w) % T))))
      ⟨(r - start (nbrsAt h x) w) % T, Nat.mod_lt _ hT⟩)

/-! ### Evidence for an edge `{x, y}` at a node with history `h` -/

/-- (a) `{x, y}` is an edge of `G⁰`. -/
def EvG0 (h : Hist V (Msg Δ d K)) (x y : V) : Prop := h.g0a x y

/-- (b) Rule for node `w`: `x` and `y` both sent `(Signal)` in the same round. -/
def EvSig (h : Hist V (Msg Δ d K)) (x y : V) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ h.r ∧ (∃ m, h.inbH k x = some (true, m)) ∧ ∃ m, h.inbH k y = some (true, m)

/-- (c) Periodic updates: a complete period `[p, p + T - 1]` (`p = s₀ + kT`) of updates from `x`
was received and decodes to a list containing `y`. -/
def EvPer (enc : (Fin Δ → Option V) → Fin T → Fin K) (h : Hist V (Msg Δ d K)) (x y : V) : Prop :=
  ∃ k L, start (nb h) x + k * T + T ≤ h.r + 1 ∧
    (∀ i : Fin T, (h.inbH (start (nb h) x + k * T + i) x).map (fun m => m.2.2) = some (enc L i)) ∧
    ∃ i, L i = some y

/-- (d) Rule for node `u`: `x` became a neighbour in round `t` and sent `R_signal(x) ∋ a`, and the
edge to `y` appeared in round `t - a`. -/
def EvRSig (h : Hist V (Msg Δ d K)) (x y : V) : Prop :=
  ∃ t a RE RS b c, 1 ≤ t ∧ t ≤ h.r ∧ x ∈ nb h t ∧ x ∉ nb h (t - 1) ∧
    h.inbH t x = some (b, some (RE, RS), c) ∧ (∃ i, RS i = some a) ∧ 1 ≤ a.val ∧ a.val < t ∧
    y ∈ nb h (t - a.val) ∧ y ∉ nb h (t - a.val - 1)

/-- (e) Rule for node `v`: `x` became a neighbour in round `t` and sent `R_edge(x) ∋ a`, and
`y ≠ x` sent `(Signal)` in round `t - a`. -/
def EvREdge (h : Hist V (Msg Δ d K)) (x y : V) : Prop :=
  ∃ t a RE RS b c, 1 ≤ t ∧ t ≤ h.r ∧ x ∈ nb h t ∧ x ∉ nb h (t - 1) ∧
    h.inbH t x = some (b, some (RE, RS), c) ∧ (∃ i, RE i = some a) ∧ 1 ≤ a.val ∧ a.val < t ∧
    y ≠ x ∧ ∃ m, h.inbH (t - a.val) y = some (true, m)

/-- Evidence for the edge `{x, y}` (from the side of `x`). -/
def Ev (enc : (Fin Δ → Option V) → Fin T → Fin K) (h : Hist V (Msg Δ d K)) (x y : V) : Prop :=
  EvG0 h x y ∨ EvSig h x y ∨ EvPer enc h x y ∨ EvRSig h x y ∨ EvREdge h x y

/-- Output: the triangles `{z, x, y}` through two current neighbours `x ≠ y` with evidence for
the edge `{x, y}`. -/
def out (enc : (Fin Δ → Option V) → Fin T → Fin K) (h : Hist V (Msg Δ d K)) : Set (Finset V) :=
  {Q | ∃ x y, x ≠ y ∧ x ∈ nb h h.r ∧ y ∈ nb h h.r ∧ (Ev enc h x y ∨ Ev enc h y x) ∧
    Q = {h.id, x, y}}

/-- The algorithm of Theorem 1.4. -/
noncomputable def alg14 (hT : 0 < T) (enc : (Fin Δ → Option V) → Fin T → Fin K) :
    Algorithm V (Msg Δ d K) (Set (Finset V)) :=
  histAlg (snd hT enc) (out enc)

end Alg14

end Podc.DynamicSubgraphFinding
