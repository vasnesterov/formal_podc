import Papers.PODC2015.LoopFreeUpdates.Rounds

/-!
# The reduction of §3.2 is wrong: the variable gadgets always contain a cycle

§3.2.2 replaces every variable `x` of the 3-SAT formula by copies `x₀, …, x_{pₓ}, x_l` and
`x̄₀, …, x̄_{nₓ}, x̄_l` with *assignment* clauses `(x₀ ∨ x̄₀)`, *implication* clauses `xᵢ → xᵢ₊₁`
(the last one `x_{pₓ} → x_l`) and an *exclusive* clause `(¬x_l ∨ ¬x̄_l)`. §3.2.3 turns every clause into
a gadget: every copy is an `FF` node (white), updated in round 1 iff the copy is true; `BB` nodes (black)
must be updated in round 2; helper nodes (grey) are of type `B·` and keep their old rule in round 2.

* clause gadget: a vertical solid path `v₂ᴷ, …literal blocks…, v₁ᴷ` with the backward dashed edge
  `v₁ᴷ ⇢ v₂ᴷ`;
* implication `xᵢ → xᵢ₊₁`: dashed `xᵢ ⇢ xᵢ₊₁^IN`, solid `xᵢ₊₁^IN → xᵢ₊₁ → xᵢ₊₁^BB`, dashed
  `xᵢ₊₁^BB ⇢ xᵢ^H`, solid `xᵢ^H → xᵢ^IN → xᵢ` (the block of a copy is `x^H, x^IN, x, x^BB` bottom-up);
* exclusive clause: four solid paths; dashed `x̄_l ⇢ v₁`, `x_l ⇢ v₃`, solid `v₁ → v₂`, `v₃ → v₄`,
  dashed `v₂ ⇢ x_l^H`, `v₄ ⇢ x̄_l^H`.

Theorem 2 of the paper claims that a satisfying assignment gives a cycle-free second round. It does
not: whatever the assignment, the gadgets of a single variable contain a second-round cycle. For
`x` true the cycle is the *ring*
`x₀ ⇢ x₁^IN → x₁ ⇢ x_l^IN → x_l ⇢ v₃ → v₄ ⇢ x̄_l^H → x̄_l^IN → x̄_l → x̄_l^BB ⇢ x̄₀^H → x̄₀ → v₁ᴬ ⇢ v₂ᴬ → x₀^H → x₀`
(true copies forward along dashed edges, the exclusive gadget, false copies backward along the
implication `BB` edges, the assignment clause back to `x₀`); every other choice violates a clause and
closes one of the paper's own cycles (`gadget_cycle`).

We formalize the gadgets of one variable with one positive and no negative occurrence
(`pₓ = 1`, `nₓ = 0`; e.g. every variable of the satisfiable formula `x ∨ y ∨ z`): 22 nodes and their
edges and colours exactly as described in §3.2.3. The only unspecified detail is the order of the two
blocks on the assignment path; both orders are covered (`o : Bool`). Then:

* `gadget_cycle`: in the paper's gadget graph, every choice of round-1 copies leaves a second-round
  cycle (this refutes Theorem 2, (⇒));
* `not_hasSLF_three_of_realizes`: every network-update instance that contains these gadgets with the
  colours the paper requires — in particular every instance produced by §3.2.4 for `x ∨ y ∨ z`, a
  satisfiable formula — has **no** strongly loop-free 3-round schedule; so the reduction maps
  satisfiable formulas to no-instances;
* `realizes_example`: such instances exist (a 41-node instance built like §3.2.4: helper nodes `R`
  on the left, one connector after each vertical path).
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

/-- The 22 gadget nodes of one variable `x` with `pₓ = 1`, `nₓ = 0`. `xb` stands for `x̄`, `e₁…e₄`
for the helper nodes `v₁…v₄` of the exclusive gadget, `v₁A`, `v₂A` for `v₁ᴷ`, `v₂ᴷ` of the
assignment clause `(x₀ ∨ x̄₀)`. -/
inductive GNode
  | v2A | x0H | x0 | xb0H | xb0 | v1A
  | x1H | x1IN | x1 | x1BB
  | xlH | xlIN | xl | xlBB
  | xblH | xblIN | xbl | xblBB
  | e1 | e2 | e3 | e4
  deriving DecidableEq, Repr

instance : Fintype GNode :=
  Fintype.ofList [.v2A, .x0H, .x0, .xb0H, .xb0, .v1A, .x1H, .x1IN, .x1, .x1BB, .xlH, .xlIN, .xl,
    .xlBB, .xblH, .xblIN, .xbl, .xblBB, .e1, .e2, .e3, .e4] (by intro x; cases x <;> simp)

/-- Colours of §3.2.3: white = `FF`, black = `BB`, grey = `B·`. -/
inductive Colour | white | black | grey
  deriving DecidableEq

namespace GNode

/-- The colour of a gadget node. -/
def colour : GNode → Colour
  | x0 | xb0 | x1 | xl | xbl => .white
  | v1A | x1BB | xlBB | xblBB | e2 | e4 => .black
  | _ => .grey

/-- Solid (old-route) edges of §3.2.3. The vertical paths are `v₂ᴬ, [x₀ block], [x̄₀ block], v₁ᴬ`
(the blocks in either order, `o = true` puts the `x̄₀` block first), `x₁^H, x₁^IN, x₁, x₁^BB` (inside
the clause gadget of the occurrence), `x̄_l^H, x̄_l^IN, x̄_l, x̄_l^BB`, `x_l^H, x_l^IN, x_l, x_l^BB`,
`v₁, v₂` and `v₃, v₄`. -/
def solidSucc (o : Bool) : GNode → Option GNode
  | v2A => if o then some xb0H else some x0H
  | x0H => some x0
  | x0 => if o then some v1A else some xb0H
  | xb0H => some xb0
  | xb0 => if o then some x0H else some v1A
  | x1H => some x1IN
  | x1IN => some x1
  | x1 => some x1BB
  | xlH => some xlIN
  | xlIN => some xl
  | xl => some xlBB
  | xblH => some xblIN
  | xblIN => some xbl
  | xbl => some xblBB
  | e1 => some e2
  | e3 => some e4
  | _ => none

/-- Dashed (new-route) edges of §3.2.3. -/
def dashedSucc : GNode → Option GNode
  | x0 => some x1IN        -- implication x₀ → x₁
  | x1BB => some x0H
  | x1 => some xlIN        -- implication x₁ → x_l
  | xlBB => some x1H
  | xb0 => some xblIN      -- implication x̄₀ → x̄_l
  | xblBB => some xb0H
  | v1A => some v2A        -- assignment clause (x₀ ∨ x̄₀)
  | xbl => some e1         -- exclusive clause (¬x_l ∨ ¬x̄_l)
  | xl => some e3
  | e2 => some xlH
  | e4 => some xblH
  | _ => none

/-- The second-round graph of the gadgets when the white nodes `a` with `T a` were updated in round 1
and all black nodes are updated in round 2 (grey nodes keep their old rules). -/
def step2 (o : Bool) (T : GNode → Bool) (a : GNode) : Option GNode :=
  match a.colour with
  | .white => if T a then dashedSucc a else solidSucc o a
  | .black => dashedSucc a
  | .grey => solidSucc o a

/-- Iterating `step2`. -/
def iter2 (o : Bool) (T : GNode → Bool) (a : GNode) (k : ℕ) : Option GNode :=
  (fun x => x.bind (step2 o T))^[k] (some a)

/-- An assignment of the five copies `x₀, x̄₀, x₁, x_l, x̄_l`. -/
def mkT (b0 bb0 b1 bl bbl : Bool) : GNode → Bool
  | x0 => b0
  | xb0 => bb0
  | x1 => b1
  | xl => bl
  | xbl => bbl
  | _ => false

theorem step2_congr (o : Bool) (T : GNode → Bool) :
    step2 o T = step2 o (mkT (T x0) (T xb0) (T x1) (T xl) (T xbl)) := by
  funext a; cases a <;> rfl

theorem iter2_congr (o : Bool) (T : GNode → Bool) :
    iter2 o T = iter2 o (mkT (T x0) (T xb0) (T x1) (T xl) (T xbl)) := by
  unfold iter2; rw [step2_congr]

theorem cycle_mkT : ∀ o b0 bb0 b1 bl bbl : Bool, ∃ a : GNode, ∃ k ∈ Finset.range 23,
    0 < k ∧ iter2 o (mkT b0 bb0 b1 bl bbl) a k = some a := by
  decide

end GNode

open GNode

/-- **Theorem 2 (⇒) of [LMS15] is false.** In the paper's gadget graph of a variable (with one
positive occurrence), whatever subset of the copies is updated in round 1 — in particular for the
copies set to true by any satisfying assignment — the second round (all `BB` nodes updated, grey nodes
not yet) contains a cycle. -/
theorem gadget_cycle (o : Bool) (T : GNode → Bool) :
    ∃ a : GNode, ∃ k, 0 < k ∧ iter2 o T a k = some a := by
  obtain ⟨a, k, -, hk, h⟩ := cycle_mkT o (T x0) (T xb0) (T x1) (T xl) (T xbl)
  exact ⟨a, k, hk, by rw [iter2_congr]; exact h⟩

/-- **Theorem 2 (⇒) of [LMS15], concrete failure.** Setting `x` true (copies `x₀, x₁, x_l` true,
`x̄₀, x̄_l` false) satisfies all clauses of `C′` that involve only copies of `x` (assignment, implications,
exclusive clause), yet the second round contains a cycle: the ring through `x₀` (16 steps, or 14 if
the `x̄₀` block comes first on the assignment path). -/
theorem theorem_2_false (o : Bool) :
    let T := mkT true false true true false
    ((T x0 || T xb0) && (!T x0 || T x1) && (!T x1 || T xl) && (!T xb0 || T xbl) &&
      !(T xl && T xbl)) = true ∧
    iter2 o T x0 (if o then 14 else 16) = some x0 := by
  cases o <;> decide

variable {V : Type*} [DecidableEq V]

/-- An instance contains the gadgets of one variable, with the colours required by §3.2.3, via the
injective map `g`. -/
structure Realizes (I : Instance V) (o : Bool) (g : GNode → V) : Prop where
  inj : Function.Injective g
  solid : ∀ a b, solidSucc o a = some b → I.out₁ (g a) = some (g b)
  dashed : ∀ a b, dashedSucc a = some b → I.out₂ (g a) = some (g b)
  white : ∀ a, a.colour = .white → I.IsFF (g a)
  black : ∀ a, a.colour = .black → I.IsBB (g a)
  grey : ∀ a, a.colour = .grey → g a ∈ I.toUpdate ∧ ¬ I.DashedFwd (g a)

namespace Realizes

variable {I : Instance V} {o : Bool} {g : GNode → V}

/-- The second-round state of the normal form: `FB ∪ S ∪ X` with `X` all black gadget nodes. -/
theorem step_of_step2 (hR : Realizes I o g) {S : Finset V} (hS : ∀ v ∈ S, I.IsFF v) {a b : GNode}
    (h : step2 o (fun c => decide (g c ∈ S)) a = some b) :
    I.Step (I.ofType I.IsFB ∪ S ∪ (Finset.univ.filter (fun c => c.colour = .black)).image g)
      (g a) (g b) := by
  unfold Instance.Step
  unfold step2 at h
  cases hc : a.colour with
  | white =>
    rw [hc] at h
    have hFF := hR.white a hc
    by_cases haS : g a ∈ S
    · simp only [haS, decide_true, ite_true] at h
      rw [I.fwd_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ haS))]
      exact hR.dashed a b h
    · simp only [haS, decide_false, Bool.false_eq_true, ite_false] at h
      rw [I.fwd_of_not_mem]
      · exact hR.solid a b h
      · intro h'
        rcases Finset.mem_union.1 h' with h' | h'
        rcases Finset.mem_union.1 h' with h' | h'
        · exact ((I.mem_ofType).1 h').2.2.2 hFF.2.2
        · exact haS h'
        · obtain ⟨c, hcb, hgc⟩ := Finset.mem_image.1 h'
          exact (hR.black c (Finset.mem_filter.1 hcb).2).2.1 (hgc ▸ hFF.2.1)
  | black =>
    rw [hc] at h
    rw [I.fwd_of_mem (Finset.mem_union_right _ (Finset.mem_image.2 ⟨a, by simp [hc], rfl⟩))]
    exact hR.dashed a b h
  | grey =>
    rw [hc] at h
    have hG := hR.grey a hc
    rw [I.fwd_of_not_mem]
    · exact hR.solid a b h
    · intro h'
      rcases Finset.mem_union.1 h' with h' | h'
      rcases Finset.mem_union.1 h' with h' | h'
      · exact hG.2 ((I.mem_ofType).1 h').2.2.1
      · exact hG.2 (hS _ h').2.1
      · obtain ⟨c, hcb, hgc⟩ := Finset.mem_image.1 h'
        have := hR.inj hgc
        subst this
        rw [(Finset.mem_filter.1 hcb).2] at hc; cases hc

theorem reach_of_iter2 (hR : Realizes I o g) {S : Finset V} (hS : ∀ v ∈ S, I.IsFF v) {a b : GNode}
    {k : ℕ} (h : iter2 o (fun c => decide (g c ∈ S)) a k = some b) :
    ReflTransGen
      (I.Step (I.ofType I.IsFB ∪ S ∪ (Finset.univ.filter (fun c => c.colour = .black)).image g))
      (g a) (g b) := by
  induction k generalizing b with
  | zero => unfold iter2 at h; cases h; exact ReflTransGen.refl
  | succ k ih =>
    unfold iter2 at h
    rw [Function.iterate_succ_apply'] at h
    cases hk : iter2 o (fun c => decide (g c ∈ S)) a k with
    | none => unfold iter2 at hk; rw [hk] at h; cases h
    | some c =>
      unfold iter2 at hk; rw [hk] at h
      exact (ih hk).tail (hR.step_of_step2 hS h)

theorem transGen_of_iter2 (hR : Realizes I o g) {S : Finset V} (hS : ∀ v ∈ S, I.IsFF v)
    {a b : GNode} {k : ℕ} (hk : 0 < k) (h : iter2 o (fun c => decide (g c ∈ S)) a k = some b) :
    TransGen
      (I.Step (I.ofType I.IsFB ∪ S ∪ (Finset.univ.filter (fun c => c.colour = .black)).image g))
      (g a) (g b) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  unfold iter2 at h
  rw [Function.iterate_succ_apply'] at h
  cases hj : iter2 o (fun c => decide (g c ∈ S)) a k with
  | none => unfold iter2 at hj; rw [hj] at h; cases h
  | some c =>
    have hj' := hj
    unfold iter2 at hj; rw [hj] at h
    exact TransGen.tail' (hR.reach_of_iter2 hS hj') (hR.step_of_step2 hS h)

end Realizes

/-- **The reduction of §3.2 fails.** Every instance that contains the paper's gadgets of one variable
(with one positive and no negative occurrence) with the colours required by §3.2.3 has no strongly
loop-free 3-round schedule. The instance that §3.2.4 builds for the satisfiable formula `x ∨ y ∨ z`
contains these gadgets for `x`, so the reduction maps it to a no-instance; the paper's claim
"the possibility of making the second round cycle-free in our instance is still equivalent to the
satisfiability of C′" is false. -/
theorem not_hasSLF_three_of_realizes {I : Instance V} {o : Bool} {g : GNode → V}
    (hR : Realizes I o g) : ¬ I.HasSLF 3 := by
  rw [Instance.hasSLF_three_iff]
  rintro ⟨S, hS, hX⟩
  have hlf := hX ((Finset.univ.filter (fun c => c.colour = .black)).image g) (by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hv
    exact hR.black c (Finset.mem_filter.1 hc).2)
  obtain ⟨a, k, hk, h⟩ := gadget_cycle o (fun c => decide (g c ∈ S))
  exact hlf (g a) (hR.transGen_of_iter2 hS hk h)

/-! ### The gadgets can be realized -/

/-- A 41-node instance containing the gadgets: old route `0, 1, …, 40`; nodes `1…11` play the role of
the paper's set `R` and the nodes after each vertical path are connectors. -/
def gadgetInstance : Instance ℕ where
  old := List.range 41
  new := [0, 18, 23, 28, 33, 36, 39, 14, 20, 1, 16, 25, 2, 21, 30, 3, 31, 37, 4, 26, 34, 5, 17, 12,
    6, 22, 13, 7, 32, 19, 8, 27, 15, 9, 35, 29, 10, 38, 24, 11, 40]
  nodup := List.nodup_range
  perm := by decide
  ne_nil := by decide
  head_eq := by decide
  getLast_eq := by decide

/-- The embedding of the gadgets into `gadgetInstance`. -/
def gadgetEmb : GNode → ℕ
  | .x0 => 14 | .xb0 => 16 | .x1 => 21 | .xl => 31 | .xbl => 26
  | .v1A => 17 | .x1BB => 22 | .xlBB => 32 | .xblBB => 27 | .e2 => 35 | .e4 => 38
  | .v2A => 12 | .x0H => 13 | .xb0H => 15 | .x1H => 19 | .x1IN => 20 | .xlH => 29
  | .xlIN => 30 | .xblH => 24 | .xblIN => 25 | .e1 => 34 | .e3 => 37

/-- Non-vacuity: the gadgets of §3.2.3, with the required colours, occur in a genuine instance. -/
theorem realizes_example : Realizes gadgetInstance false gadgetEmb where
  inj := by decide
  solid := by decide
  dashed := by decide
  white := by decide
  black := by decide
  grey := by decide

/-- Hence this instance has no strongly loop-free 3-round schedule. -/
theorem gadgetInstance_not_hasSLF_three : ¬ gadgetInstance.HasSLF 3 :=
  not_hasSLF_three_of_realizes realizes_example

end Podc.LoopFreeUpdates
