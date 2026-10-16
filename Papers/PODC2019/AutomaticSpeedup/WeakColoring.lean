import Papers.PODC2019.AutomaticSpeedup.TritEquiv

/-!
# Weak 2-colouring, its pointer version, and 0-round impossibility (Brandt, PODC 2019, §4.6, §5.2)

* `superweakMono`: superweak `j`-colouring solutions are superweak `j'`-colouring solutions for
  `j ≤ j'` (proof of Theorem 4).
* `IsWeak2Col`, `Weak2ColSolvableIn`: weak 2-colouring in the port-numbering model (every node of
  positive degree has a neighbour of a different colour), solvable in `t` rounds by a CSLib
  algorithm. This is not an edge-checkable problem, so it is not a `Problem`.
* `weakPtr`: the pointer version of weak 2-colouring (Problem `Π` of §4.6, for `Δ`-regular
  graphs); `solvableIn_weakPtr`: weak 2-colouring in `t` rounds ⇒ pointer version in `t + 1`
  rounds; `weakPtrToSuperweak`: the pointer version is a special case of superweak 2-colouring.
* `RichFor`, `not_solvableIn_superweak_zero`: superweak `k`-colouring is not solvable in `0` rounds
  on a class rich enough w.r.t. an orientation (end of the proof of Theorem 4).
-/

namespace AutomaticSpeedup

open Cslib.PortNumbering Problem

/-! ### Monotonicity in `k` -/

/-- Superweak `j`-colouring is a special case of superweak `j'`-colouring for `j ≤ j'`. -/
def superweakMono {j j' : ℕ} (hj : j ≤ j') (Δ : ℕ) :
    LabelHom (superweak j) (superweak j') Δ where
  φ x := (Fin.castLE hj x.1, x.2)
  map_f _ _ := trivial
  map_g m hm := by
    obtain ⟨a, b, rfl, h⟩ := hm
    refine ⟨(Fin.castLE hj a.1, a.2), (Fin.castLE hj b.1, b.2), by simp, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl fun e => h (Fin.castLE_injective hj e)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  map_h m hm := by
    obtain ⟨h1, ⟨c, hc⟩, h3⟩ := hm
    refine ⟨by simpa using h1, ⟨Fin.castLE hj c, ?_⟩, ?_⟩
    · simp only [Multiset.mem_map]
      rintro _ ⟨x, hx, rfl⟩
      simp [hc x hx]
    · simp only [Multiset.filter_map, Multiset.card_map]
      have : min (j + 1) (Multiset.card (m.filter (·.2 = Ptr.demand))) ≤
          min (j' + 1) (Multiset.card (m.filter (·.2 = Ptr.demand))) :=
        min_le_min_right _ (by omega)
      exact lt_of_lt_of_le h3 this

theorem SolvableIn.superweak_mono {I : Type} {n Δ t j j' : ℕ} {𝒢 : Set (LGraph I n)}
    (hj : j ≤ j') (h : SolvableIn 𝒢 (superweak j) Δ t) : SolvableIn 𝒢 (superweak j') Δ t :=
  h.of_labelHom (superweakMono hj Δ)

/-! ### Weak 2-colouring and its pointer version -/

variable {I : Type} {n : ℕ}

/-- `col` is a weak 2-colouring of `G`: every node with at least one neighbour has a neighbour of a
different colour (§4.6). -/
def IsWeak2Col (G : LGraph I n) (col : Fin n → Bool) : Prop :=
  ∀ v, 0 < G.deg v → ∃ i < G.deg v, col (G.nbr v i) ≠ col v

/-- Weak 2-colouring is solvable in `t` rounds on the class `𝒢`: some deterministic CSLib
port-numbering algorithm (local input: the node's input labels) outputs a weak 2-colouring of
every graph of `𝒢` after `t` rounds. -/
def Weak2ColSolvableIn (𝒢 : Set (LGraph I n)) (t : ℕ) : Prop :=
  ∃ A : Algorithm (List I) Bool, ∀ G ∈ 𝒢, IsWeak2Col G (A.eval G.G t G.inputs)

theorem Weak2ColSolvableIn.view {𝒢 : Set (LGraph I n)} {t : ℕ} (h : Weak2ColSolvableIn 𝒢 t) :
    ∃ F : ViewT I t → Bool, ∀ G ∈ 𝒢, IsWeak2Col G fun v => F (G.view t v) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨fun w => A.out (ViewT.stOf A t w), fun G hG => ?_⟩
  have e : A.eval G.G t G.inputs = fun v => A.out (ViewT.stOf A t (G.view t v)) := by
    funext v; simp [Algorithm.eval, state_eq_stOf]
  rw [← e]; exact hA G hG

/-- Pointer kinds of the pointer version of weak 2-colouring: a pointer `→` or none `•`. -/
inductive WPtr
  | point
  | dot
  deriving DecidableEq, Repr

/-- The pointer version of weak 2-colouring (Problem `Π` of §4.6), for `Δ`-regular graphs: labels
`{1, 2} × {→, •}` (colours as `Bool`); a node configuration has `Δ` labels of one colour, exactly
one of them with `→`; an edge is good if the colours differ or there is no pointer on it. -/
def weakPtr : Problem (Bool × WPtr) where
  f _ := Set.univ
  g _ := {m | ∃ a b : Bool × WPtr, m = {a, b} ∧ (a.1 ≠ b.1 ∨ (a.2 = .dot ∧ b.2 = .dot))}
  h Δ := {m | Multiset.card m = Δ ∧ (∃ c, ∀ x ∈ m, x.1 = c) ∧
    Multiset.card (m.filter (·.2 = .point)) = 1}

open Classical in
/-- The port of the first neighbour (in port order) whose colour differs from the own colour, as
read from a radius-`(t+1)` view; `0` if there is none. -/
noncomputable def ptrIdx {t : ℕ} (F : ViewT I t → Bool) (w : ViewT I (t + 1)) : ℕ :=
  if h : ∃ i, i < w.deg ∧ F (w.child i).1 ≠ F w.restrict then Nat.find h else 0

theorem ptrIdx_spec {t : ℕ} {F : ViewT I t → Bool} {w : ViewT I (t + 1)}
    (h : ∃ i, i < w.deg ∧ F (w.child i).1 ≠ F w.restrict) :
    ptrIdx F w < w.deg ∧ F (w.child (ptrIdx F w)).1 ≠ F w.restrict := by
  classical
  unfold ptrIdx
  simp only [h, ↓reduceDIte]
  exact Nat.find_spec h

open Classical in
/-- The `(t+1)`-round algorithm for the pointer version: own colour from the radius-`t` view, and
a pointer to the first neighbour of a different colour. -/
noncomputable def ptrAlg {t : ℕ} (F : ViewT I t → Bool) (w : ViewT I (t + 1)) (i : ℕ) :
    Bool × WPtr :=
  (F w.restrict, if i = ptrIdx F w then .point else .dot)

/-- **§4.6**: a `t`-round algorithm for weak 2-colouring yields a `(t+1)`-round algorithm for its
pointer version, on any class of `Δ`-regular graphs, `Δ ≥ 1`. -/
theorem solvableIn_weakPtr {𝒢 : Set (LGraph I n)} {Δ t : ℕ} (hΔ : 1 ≤ Δ)
    (hreg : ∀ G ∈ 𝒢, ∀ v, G.deg v = Δ) (h : Weak2ColSolvableIn 𝒢 t) :
    SolvableIn 𝒢 weakPtr Δ (t + 1) := by
  classical
  obtain ⟨F, hF⟩ := h.view
  rw [solvableIn_iff_view]
  refine ⟨ptrAlg F, fun G hG => ?_⟩
  -- the pointer is well defined and points to a neighbour of a different colour
  have hspec : ∀ v, ptrIdx F (G.view (t + 1) v) < G.deg v ∧
      F (G.view t (G.nbr v (ptrIdx F (G.view (t + 1) v)))) ≠ F (G.view t v) := by
    intro v
    obtain ⟨i, hi, hne⟩ := hF G hG v (by rw [hreg G hG v]; omega)
    have hex : ∃ i, i < (G.view (t + 1) v).deg ∧
        F ((G.view (t + 1) v).child i).1 ≠ F (G.view (t + 1) v).restrict :=
      ⟨i, by simpa using hi, by rwa [LGraph.child_view _ _ _ hi, LGraph.restrict_view]⟩
    obtain ⟨h1, h2⟩ := ptrIdx_spec hex
    rw [LGraph.deg_view] at h1
    rw [LGraph.child_view _ _ _ h1, LGraph.restrict_view] at h2
    exact ⟨h1, h2⟩
  refine ⟨fun _ _ _ => trivial, fun v i hi => ?_, fun v => ?_⟩
  · refine ⟨_, _, rfl, ?_⟩
    simp only [ptrAlg, LGraph.restrict_view]
    by_cases hc : F (G.view t v) = F (G.view t (G.nbr v i))
    · refine Or.inr ⟨?_, ?_⟩
      · split_ifs with hp
        · subst hp; exact absurd hc.symm (hspec v).2
        · rfl
      · split_ifs with hp
        · exfalso
          have := (hspec (G.nbr v i)).2
          have e : G.nbr (G.nbr v i) (G.rport v i) = v := PNGraph.nbr_nbr _ hi
          rw [← hp, e] at this
          exact this hc
        · rfl
    · exact Or.inl hc
  · refine ⟨by simp [hreg G hG v], ⟨F (G.view t v), ?_⟩, ?_⟩
    · simp [ptrAlg]
    · rw [Multiset.filter_map, Multiset.card_map]
      have e : (Multiset.range (G.deg v)).filter
          ((fun x : Bool × WPtr => x.2 = WPtr.point) ∘ ptrAlg F (G.view (t + 1) v)) =
          (Multiset.range (G.deg v)).filter (· = ptrIdx F (G.view (t + 1) v)) := by
        refine Multiset.filter_congr fun i _ => ?_
        simp only [Function.comp_apply, ptrAlg]
        split_ifs with hp <;> simp [hp]
      rw [e, Multiset.filter_eq', Multiset.card_replicate]
      exact Multiset.count_eq_one_of_mem (Multiset.nodup_range _)
        (Multiset.mem_range.2 (hspec v).1)

/-- Colours `Bool → Fin 2`. -/
def boolFin2 (b : Bool) : Fin 2 := if b then 1 else 0

theorem boolFin2_injective : Function.Injective boolFin2 := by
  intro a b; cases a <;> cases b <;> simp [boolFin2]

/-- Pointers `→ ↦ →` (demanding), `• ↦ •`. -/
def WPtr.toPtr : WPtr → Ptr
  | .point => .demand
  | .dot => .none

/-- The pointer version of weak 2-colouring is a special case of superweak 2-colouring (§5.2). -/
def weakPtrToSuperweak (Δ : ℕ) : LabelHom weakPtr (superweak 2) Δ where
  φ x := (boolFin2 x.1, x.2.toPtr)
  map_f _ _ := trivial
  map_g m hm := by
    obtain ⟨a, b, rfl, h⟩ := hm
    refine ⟨(boolFin2 a.1, a.2.toPtr), (boolFin2 b.1, b.2.toPtr), by simp, ?_⟩
    rcases h with h | ⟨h1, h2⟩
    · exact Or.inl fun e => h (boolFin2_injective e)
    · exact Or.inr (Or.inl ⟨by simp [h1, WPtr.toPtr], by simp [h2, WPtr.toPtr]⟩)
  map_h m hm := by
    obtain ⟨h1, ⟨c, hc⟩, h3⟩ := hm
    refine ⟨by simpa using h1, ⟨boolFin2 c, ?_⟩, ?_⟩
    · simp only [Multiset.mem_map]
      rintro _ ⟨x, hx, rfl⟩
      simp [hc x hx]
    · simp only [Multiset.filter_map, Multiset.card_map]
      have e1 : m.filter ((fun x : Fin 2 × Ptr => x.2 = Ptr.accept) ∘
          fun x : Bool × WPtr => (boolFin2 x.1, x.2.toPtr)) = 0 :=
        Multiset.filter_eq_nil.2 fun x _ => by
          rcases x with ⟨_, _ | _⟩ <;> simp [WPtr.toPtr]
      have e2 : m.filter ((fun x : Fin 2 × Ptr => x.2 = Ptr.demand) ∘
          fun x : Bool × WPtr => (boolFin2 x.1, x.2.toPtr)) = m.filter (·.2 = WPtr.point) :=
        Multiset.filter_congr fun x _ => by
          rcases x with ⟨_, _ | _⟩ <;> simp [WPtr.toPtr]
      rw [e1, e2, h3]
      simp

/-! ### 0-round impossibility -/

/-- The class `𝒢` is *rich* for the input list `ι` w.r.t. the orientation `o`: for all ports `p`, `q`
with `o ι[p] ≠ o ι[q]`, some graph of `𝒢` has an edge joining port `p` of a node with inputs `ι`
to port `q` of a node with inputs `ι`. (In the proof of Theorem 4: a node with a fixed in/out
pattern can be connected, at any port, to any port of opposite orientation of a node with the same
pattern.) -/
def RichFor (𝒢 : Set (LGraph I n)) (o : I → Bool) (ι : List I) : Prop :=
  ∀ p q : Fin ι.length, o ι[p] ≠ o ι[q] →
    ∃ G ∈ 𝒢, ∃ v, G.inputs v = ι ∧ G.inputs (G.nbr v p) = ι ∧ G.rport v p = q

/-- **End of the proof of Theorem 4.** If `𝒢` is rich for an input list `ι` of length `Δ` with at
least `k + 1` ports of each orientation, superweak `k`-colouring is not solvable in `0` rounds:
`0`-round outputs depend only on the input list; the node outputs `→` at some port `p`, and at
some port `q` of the opposite orientation it does not output `⊸` (at most `k` ports carry `⊸`);
joining `p` to `q` of an identical node gives a bad edge. -/
theorem not_solvableIn_superweak_zero {𝒢 : Set (LGraph I n)} {o : I → Bool} {k Δ : ℕ}
    (ι : List I) (hlen : ι.length = Δ) (hrich : RichFor 𝒢 o ι)
    (hcount : ∀ b, k + 1 ≤ (Finset.univ.filter fun p : Fin ι.length => o ι[p] = b).card) :
    ¬ SolvableIn 𝒢 (superweak k) Δ 0 := by
  classical
  rintro h
  obtain ⟨F, hF⟩ := (solvableIn_iff_view _ _ _ _).1 h
  have hv0 : ∀ G : LGraph I n, ∀ v, G.view 0 v = G.inputs v := fun _ _ => rfl
  -- some node with inputs `ι` exists
  have hne : ∀ b, ∃ p : Fin ι.length, o ι[p] = b := by
    intro b
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (lt_of_lt_of_le (Nat.succ_pos k) (hcount b))
    exact ⟨p, (Finset.mem_filter.1 hp).2⟩
  obtain ⟨p₀, hp₀⟩ := hne true
  obtain ⟨q₀, hq₀⟩ := hne false
  obtain ⟨G₀, hG₀, v₀, hι₀, -⟩ := hrich p₀ q₀ (by rw [hp₀, hq₀]; decide)
  have hdeg₀ : G₀.deg v₀ = Δ := by rw [← hlen, ← hι₀, LGraph.length_inputs]
  obtain ⟨-, ⟨c, hc⟩, hcnt⟩ := (hF G₀ hG₀).2.2 v₀
  simp only [hv0, hι₀, hdeg₀] at hc hcnt
  rw [Multiset.filter_map, Multiset.card_map, Multiset.filter_map, Multiset.card_map] at hcnt
  have hcol : ∀ i < Δ, (F ι i).1 = c := fun i hi =>
    hc _ (Multiset.mem_map.2 ⟨i, Multiset.mem_range.2 hi, rfl⟩)
  -- a demanding port
  obtain ⟨p, hpΔ, hp⟩ : ∃ p < Δ, (F ι p).2 = Ptr.demand := by
    have : 0 < Multiset.card ((Multiset.range Δ).filter
        ((fun x : Fin k × Ptr => x.2 = Ptr.demand) ∘ F ι)) := by
      have := lt_min_iff.1 (lt_of_le_of_lt (Nat.zero_le _) hcnt); exact this.2
    obtain ⟨p, hp⟩ := Multiset.card_pos_iff_exists_mem.1 this
    rw [Multiset.mem_filter, Multiset.mem_range] at hp
    exact ⟨p, hp.1, hp.2⟩
  have hacc : Multiset.card ((Multiset.range Δ).filter
      ((fun x : Fin k × Ptr => x.2 = Ptr.accept) ∘ F ι)) ≤ k := by
    exact Nat.lt_succ_iff.1 (lt_min_iff.1 hcnt).1
  let p' : Fin ι.length := ⟨p, by omega⟩
  -- a port of the opposite orientation without `⊸`
  obtain ⟨q, hq, hqa⟩ : ∃ q : Fin ι.length, o ι[q] = !o ι[p'] ∧ (F ι q).2 ≠ Ptr.accept := by
    by_contra hall
    push Not at hall
    have hsub : ((Finset.univ.filter fun q : Fin ι.length => o ι[q] = !o ι[p']).map
        Fin.valEmbedding) ⊆ (Finset.range Δ).filter ((fun x : Fin k × Ptr => x.2 = Ptr.accept) ∘ F ι) := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hx
      rw [Finset.mem_filter] at hq ⊢
      exact ⟨Finset.mem_range.2 (hlen ▸ q.2), hall q hq.2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_map] at this
    have h2 := hcount (!o ι[p'])
    have h3 : ((Finset.range Δ).filter ((fun x : Fin k × Ptr => x.2 = Ptr.accept) ∘ F ι)).card =
        Multiset.card ((Multiset.range Δ).filter ((fun x : Fin k × Ptr => x.2 = Ptr.accept) ∘ F ι)) :=
      rfl
    omega
  obtain ⟨G, hG, v, hιv, hιu, hport⟩ := hrich p' q (by rw [hq]; cases o ι[p'] <;> decide)
  have hdeg : G.deg v = Δ := by rw [← hlen, ← hιv, LGraph.length_inputs]
  have hedge := (hF G hG).2.1 v p (by omega)
  have hιu' : G.inputs (G.nbr v p) = ι := hιu
  have hport' : G.rport v p = q := hport
  simp only [hv0, hιv, hιu'] at hedge
  change ({F ι p, F ι (G.rport v p)} : Multiset (Fin k × Ptr)) ∈ (superweak k).g Δ at hedge
  rw [hport', superweak_g_iff] at hedge
  have hqΔ : (q : ℕ) < Δ := hlen ▸ q.2
  rcases hedge with h | h | h | h
  · exact h (by rw [hcol p hpΔ, hcol q hqΔ])
  · rw [hp] at h; exact absurd h.1 (by decide)
  · rw [hp] at h; exact absurd h (by decide)
  · exact hqa h

end AutomaticSpeedup
