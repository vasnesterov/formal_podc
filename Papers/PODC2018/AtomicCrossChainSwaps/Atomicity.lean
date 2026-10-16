import Papers.PODC2018.AtomicCrossChainSwaps.Basic

/-!
# §3: outcomes, uniform and atomic protocols, Theorem 3.5

An *outcome* is the set `T` of triggered arcs (`T u v`: the transfer `u → v` happened). Payoff
classes for a coalition `S` (a single party is `S = {v}`) are defined from the arcs entering and
leaving `S`, exactly as in §3. A protocol is abstracted by its *game*: for every deviating
coalition `S`, the set of outcomes that can result when the members of `S` deviate (in any way)
and everybody else conforms.
-/

namespace AtomicSwap

variable {V : Type*} (D : Digraph V)

/-- Arc `(u, v)` enters `S`. -/
def Enters (S : Set V) (u v : V) : Prop := D.Adj u v ∧ u ∉ S ∧ v ∈ S
/-- Arc `(u, v)` leaves `S`. -/
def Leaves (S : Set V) (u v : V) : Prop := D.Adj u v ∧ u ∈ S ∧ v ∉ S

variable (S : Set V) (T : V → V → Prop)

/-- FreeRide: some entering arc is triggered, no leaving arc is triggered. -/
def FreeRide : Prop := (∃ u v, Enters D S u v ∧ T u v) ∧ ∀ u v, Leaves D S u v → ¬ T u v
/-- Discount: all entering arcs are triggered, some leaving arc is not. -/
def Discount : Prop := (∀ u v, Enters D S u v → T u v) ∧ ∃ u v, Leaves D S u v ∧ ¬ T u v
/-- Deal: all entering and leaving arcs are triggered. -/
def Deal : Prop := (∀ u v, Enters D S u v → T u v) ∧ ∀ u v, Leaves D S u v → T u v
/-- NoDeal: no entering or leaving arc is triggered. -/
def NoDeal : Prop := (∀ u v, Enters D S u v → ¬ T u v) ∧ ∀ u v, Leaves D S u v → ¬ T u v
/-- Underwater: some entering arc is not triggered and some leaving arc is triggered. -/
def Underwater : Prop := (∃ u v, Enters D S u v ∧ ¬ T u v) ∧ ∃ u v, Leaves D S u v ∧ T u v

/-- The five classes cover all outcomes, and the acceptable ones (Deal, NoDeal, Discount,
FreeRide) are exactly the non-Underwater ones. -/
theorem not_underwater_iff :
    ¬ Underwater D S T ↔ FreeRide D S T ∨ Discount D S T ∨ Deal D S T ∨ NoDeal D S T := by
  unfold Underwater FreeRide Discount Deal NoDeal
  constructor
  · intro h
    by_cases hin : ∀ u v, Enters D S u v → T u v
    · by_cases hout : ∀ u v, Leaves D S u v → T u v
      · exact Or.inr (Or.inr (Or.inl ⟨hin, hout⟩))
      · push Not at hout
        exact Or.inr (Or.inl ⟨hin, hout⟩)
    · push Not at hin
      have hout : ∀ u v, Leaves D S u v → ¬ T u v := by
        intro u v hl ht; exact h ⟨hin, u, v, hl, ht⟩
      by_cases hsome : ∃ u v, Enters D S u v ∧ T u v
      · exact Or.inl ⟨hsome, hout⟩
      · push Not at hsome
        exact Or.inr (Or.inr (Or.inr ⟨hsome, hout⟩))
  · rintro (⟨-, h2⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h2⟩) ⟨⟨a, b, h3, h4⟩, ⟨c, d, h5, h6⟩⟩
    · exact h2 c d h5 h6
    · exact h4 (h1 a b h3)
    · exact h4 (h1 a b h3)
    · exact h2 c d h5 h6

/-- The abstract semantics of a swap protocol on `D`: `outcomes S` is the set of outcomes that can
arise when exactly the coalition `S` deviates (cooperatively, in any way) and all other parties
conform. -/
structure SwapGame (D : Digraph V) where
  outcomes : Set V → Set (V → V → Prop)

variable {D}

namespace SwapGame

variable (G : SwapGame D)

/-- Definition 3.1 (uniform): if all conform, everybody ends with Deal; whatever coalition
deviates, no conforming party ends Underwater. -/
def Uniform : Prop :=
  (∀ T ∈ G.outcomes ∅, ∀ v, Deal D {v} T) ∧
  ∀ S, ∀ T ∈ G.outcomes S, ∀ v ∉ S, ¬ Underwater D {v} T

/-- Strong Nash equilibrium (§3): no deviating coalition achieves a payoff better than Deal. As in
the proof of Lemma 3.3, "better than Deal" means FreeRide or Discount (Fig. 3). -/
def StrongNash : Prop := ∀ S, ∀ T ∈ G.outcomes S, ¬ FreeRide D S T ∧ ¬ Discount D S T

/-- Definition 3.2 (atomic). -/
def Atomic : Prop := G.Uniform ∧ G.StrongNash

/-- The modelling assumption used by Lemma 3.4: a coalition can always refuse to give away its own
assets, i.e. some deviation leaves every arc leaving the coalition untriggered. -/
def CanAbstain : Prop := ∀ S, ∃ T ∈ G.outcomes S, ∀ u v, Leaves D S u v → ¬ T u v

end SwapGame

/-! ### The combinatorial core of Lemma 3.3 -/

section core

variable {S : Set V} {T : V → V → Prop}

/-- Acceptability of a single party `v`, unfolded: if some arc leaving `v` is triggered then all
arcs entering `v` are. -/
lemma all_in_of_out (h : ¬ Underwater D {v} T) {w : V} (hvw : D.Adj v w) (hvw' : w ≠ v)
    (ht : T v w) : ∀ u, D.Adj u v → u ≠ v → T u v := by
  intro u hu hu'
  by_contra hn
  exact h ⟨⟨u, v, ⟨hu, by simpa using hu', rfl⟩, hn⟩, ⟨v, w, ⟨hvw, rfl, by simpa using hvw'⟩, ht⟩⟩

lemma all_out_of_in (h : ¬ Underwater D {v} T) {u : V} (huv : D.Adj u v) (huv' : u ≠ v)
    (ht : ¬ T u v) : ∀ w, D.Adj v w → w ≠ v → ¬ T v w := by
  intro w hw hw' htw
  exact h ⟨⟨u, v, ⟨huv, by simpa using huv', rfl⟩, ht⟩, ⟨v, w, ⟨hw, rfl, by simpa using hw'⟩, htw⟩⟩

/-- Forward propagation of triggered arcs: a walk from `a ∈ S` to an outsider `b` all of whose
entering arcs are triggered yields a triggered arc leaving `S`. -/
lemma exists_leaves_triggered (hacc : ∀ v ∉ S, ¬ Underwater D {v} T) {a b : V}
    (hab : Reach D a b) (ha : a ∈ S) :
    b ∉ S → (∀ u, D.Adj u b → u ≠ b → T u b) → ∃ u v, Leaves D S u v ∧ T u v := by
  induction hab with
  | refl => intro hb; exact absurd ha hb
  | @tail c b _ hcb ih =>
    intro hb hin
    by_cases hcb' : c = b
    · subst hcb'; exact ih hb hin
    by_cases hc : c ∈ S
    · exact ⟨c, b, ⟨hcb, hc, hb⟩, hin c hcb hcb'⟩
    · exact ih hc (all_in_of_out (hacc c hc) hcb (Ne.symm hcb') (hin c hcb hcb'))

/-- Backward propagation of untriggered arcs: a walk from an outsider `a`, none of whose leaving
arcs is triggered, to `b ∈ S` yields an untriggered arc entering `S`. -/
lemma exists_enters_untriggered (hacc : ∀ v ∉ S, ¬ Underwater D {v} T) {a b : V}
    (hab : Reach D a b) (hb : b ∈ S) :
    a ∉ S → (∀ w, D.Adj a w → w ≠ a → ¬ T a w) → ∃ u v, Enters D S u v ∧ ¬ T u v := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => intro ha; exact absurd hb ha
  | @head a c hac _ ih =>
    intro ha hout
    by_cases hca : c = a
    · subst hca; exact ih ha hout
    by_cases hc : c ∈ S
    · exact ⟨a, c, ⟨hac, ha, hc⟩, hout c hac hca⟩
    · exact ih hc (all_out_of_in (hacc c hc) hac (Ne.symm hca) (hout c hac hca))

/-- **Lemma 3.3, combinatorial core.** If reachability in `D` is symmetric (e.g. `D` strongly
connected) and no party outside `S` is Underwater, then `S` gets neither FreeRide nor Discount. -/
theorem not_freeRide_discount (hsym : ∀ u v, Reach D u v → Reach D v u)
    (hacc : ∀ v ∉ S, ¬ Underwater D {v} T) : ¬ FreeRide D S T ∧ ¬ Discount D S T := by
  constructor
  · rintro ⟨⟨u, c, ⟨huc, hu, hc⟩, ht⟩, hno⟩
    have hcu : Reach D c u := hsym _ _ (Relation.ReflTransGen.single huc)
    by_cases hcu' : c = u
    · subst hcu'; exact hu hc
    obtain ⟨a, b, hl, hab⟩ := exists_leaves_triggered hacc hcu hc hu
      (all_in_of_out (hacc u hu) huc hcu' ht)
    exact hno a b hl hab
  · rintro ⟨hall, c, v, ⟨hcv, hc, hv⟩, ht⟩
    have hvc : Reach D v c := hsym _ _ (Relation.ReflTransGen.single hcv)
    by_cases hcv' : c = v
    · subst hcv'; exact hv hc
    obtain ⟨a, b, he, hab⟩ := exists_enters_untriggered hacc hvc hc hv
      (all_out_of_in (hacc v hv) hcv hcv' ht)
    exact hab (hall a b he)

end core

namespace SwapGame

variable {G : SwapGame D}

/-- **Lemma 3.3.** If `D` is strongly connected, every uniform protocol is atomic. (Proved under
the weaker hypothesis that reachability is symmetric; only the second clause of uniformity is
used.) -/
theorem atomic_of_uniform (hsym : ∀ u v, Reach D u v → Reach D v u) (hU : G.Uniform) :
    G.Atomic :=
  ⟨hU, fun S T hT => not_freeRide_discount hsym (hU.2 S T hT)⟩

theorem atomic_of_uniform_of_stronglyConnected (hD : StronglyConnected D) (hU : G.Uniform) :
    G.Atomic :=
  atomic_of_uniform (fun u v _ => hD v u) hU

lemma exists_cross {r : V → V → Prop} {P : V → Prop} {a b : V} (h : Relation.ReflTransGen r a b)
    (ha : P a) (hb : ¬ P b) : ∃ c d, r c d ∧ P c ∧ ¬ P d := by
  induction h with
  | refl => exact absurd ha hb
  | @tail c d _ hcd ih =>
    by_cases hc : P c
    · exact ⟨c, d, hcd, hc, hb⟩
    · exact ih hc

/-- **Lemma 3.4.** If some `y` is reachable from `x` but not vice versa, then no protocol in which
coalitions can withhold their own assets is a strong Nash equilibrium: the coalition `X` of
vertices not reachable from `y` withholds all its assets and gets Discount (the paper says
FreeRide, but `X` has no entering arcs at all). -/
theorem not_strongNash (hG : G.CanAbstain) {x y : V} (hxy : Reach D x y) (hyx : ¬ Reach D y x) :
    ¬ G.StrongNash := by
  intro hN
  set X : Set V := {w | ¬ Reach D y w}
  obtain ⟨T, hT, hno⟩ := hG X
  apply (hN X T hT).2
  refine ⟨fun u v ⟨huv, hu, hv⟩ => ?_, ?_⟩
  · exact absurd ((not_not.mp hu).tail huv) hv
  · obtain ⟨c, d, hcd, hc, hd⟩ := exists_cross (P := (· ∈ X)) hxy hyx
      (by simp [X]; exact Relation.ReflTransGen.refl)
    exact ⟨c, d, ⟨hcd, hc, hd⟩, hno c d ⟨hcd, hc, hd⟩⟩

/-- **Theorem 3.5, exact form.** A uniform protocol in which coalitions can withhold their own
assets is atomic iff reachability in `D` is symmetric (every weakly connected component of `D` is
strongly connected). -/
theorem atomic_iff (hU : G.Uniform) (hG : G.CanAbstain) :
    G.Atomic ↔ ∀ u v, Reach D u v → Reach D v u := by
  refine ⟨fun hA u v huv => ?_, fun h => atomic_of_uniform h hU⟩
  by_contra hvu
  exact not_strongNash hG huv hvu hA.2

lemma stronglyConnected_iff (hW : WeaklyConnected D) :
    StronglyConnected D ↔ ∀ u v, Reach D u v → Reach D v u := by
  refine ⟨fun h u v _ => h v u, fun h => ?_⟩
  have key : ∀ u v, Relation.ReflTransGen (fun a b => D.Adj a b ∨ D.Adj b a) u v →
      Reach D u v := by
    intro u v huv
    induction huv with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      rcases hbc with hbc | hcb
      · exact ih.tail hbc
      · exact ih.trans (h _ _ (Relation.ReflTransGen.single hcb))
  exact fun u v => key u v (hW u v)

/-- **Theorem 3.5** (for a connected swap digraph, as assumed w.l.o.g. in §3): a uniform protocol
in which coalitions can withhold their assets is atomic iff `D` is strongly connected. -/
theorem atomic_iff_stronglyConnected (hW : WeaklyConnected D) (hU : G.Uniform)
    (hG : G.CanAbstain) : G.Atomic ↔ StronglyConnected D := by
  rw [atomic_iff hU hG, stronglyConnected_iff hW]

/-- The most permissive uniform game: any outcome without Underwater conforming parties, and
`Deal` when nobody deviates. -/
def maximal (D : Digraph V) : SwapGame D where
  outcomes S := {T | (S = ∅ → ∀ u v, D.Adj u v → T u v) ∧ ∀ v ∉ S, ¬ Underwater D {v} T}

end SwapGame

/-- Two disjoint 2-cycles `0 ⇄ 1`, `2 ⇄ 3`. -/
def twoTwoCycles : Digraph (Fin 4) where
  Adj a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)

instance : DecidableRel twoTwoCycles.Adj := fun a b => by unfold twoTwoCycles; infer_instance

/-- Without the paper's standing assumption that `D` is connected, the "only if" half of
Theorem 3.5 fails: on two disjoint 2-cycles there is a uniform, atomic protocol (game) in which
coalitions can withhold their assets, although `D` is not strongly connected. -/
theorem theorem_3_5_needs_connected :
    ¬ StronglyConnected twoTwoCycles ∧ ∃ G : SwapGame twoTwoCycles,
      G.Uniform ∧ G.CanAbstain ∧ G.Atomic := by
  have hstep : ∀ b c : Fin 4, twoTwoCycles.Adj b c → b.val / 2 = c.val / 2 := by decide
  have hreach : ∀ u v : Fin 4, Reach twoTwoCycles u v → (u.val / 2 = v.val / 2) := by
    intro u v h
    induction h with
    | refl => rfl
    | @tail b c _ hbc ih =>
      rw [ih]; exact hstep _ _ hbc
  have hsym : ∀ u v : Fin 4, Reach twoTwoCycles u v → Reach twoTwoCycles v u := by
    intro u v h
    have := hreach u v h
    have hadj : ∀ a b : Fin 4, a.val / 2 = b.val / 2 → a ≠ b → twoTwoCycles.Adj a b := by
      decide
    by_cases huv : v = u
    · subst huv; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (hadj v u this.symm huv)
  refine ⟨fun h => by have := hreach 0 2 (h 0 2); simp at this, SwapGame.maximal _, ?_, ?_, ?_⟩
  · refine ⟨fun T hT v => ⟨fun a b h => hT.1 rfl a b h.1, fun a b h => hT.1 rfl a b h.1⟩,
      fun S T hT v hv => hT.2 v hv⟩
  · intro S
    refine ⟨fun _ _ => S = ∅, ⟨fun h a b _ => h, fun v hv => ?_⟩, fun u v hl h => ?_⟩
    · rintro ⟨⟨a, b, -, hab⟩, ⟨c, d, ⟨-, hc, -⟩, hcd⟩⟩
      exact hab hcd
    · subst h; exact hl.2.1
  · refine SwapGame.atomic_of_uniform hsym ⟨fun T hT v =>
      ⟨fun a b h => hT.1 rfl a b h.1, fun a b h => hT.1 rfl a b h.1⟩, fun S T hT v hv => hT.2 v hv⟩

end AtomicSwap
