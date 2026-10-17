import Cslib.Computability.Distributed.Byzantine.LockStep.Cover

-- CSLib candidate: Cslib/Computability/Distributed/Byzantine/LockStep/Cover.lean (append to the
-- existing file)

/-!
# Double covers

Addition to `Cslib/Computability/Distributed/Byzantine/LockStep/Cover.lean`. Most FLM-style
covering arguments only need two copies of every party: node `(p, c)` is copy `c : Bool` of `p`,
and a *switching function* `sw p c q` says which copy of the sender `q` the node `(p, c)` listens
to (`none`: it hears nothing from `q`). Fully connected double covers have `sw p c q = some (c ⊕ e)`
for an edge "voltage" `e`.

* `CoverSystem.doubleCover sw xq`: the double cover with switching function `sw` and inputs `xq`.
* `CoverSystem.doubleCover_lift`: honest parties lifted to the copies `(p, ℓ p)` form a lift as
  soon as `sw q (ℓ q) p = some (ℓ p)` along honest edges.
-/

namespace Cslib.Byzantine.LockStep

namespace CoverSystem

variable {P I : Type*}

/-- The *double cover* with switching function `sw` and inputs `xq`: node `(p, c)` runs the code of
`p` with input `xq (p, c)` and listens, as messages from `q`, to the copy `sw p c q` of `q` (to
nobody if `sw p c q = none`). -/
def doubleCover (sw : P → Bool → P → Option Bool) (xq : P × Bool → I) :
    CoverSystem P I (P × Bool) where
  φ := Prod.fst
  nbr x q := (sw x.1 x.2 q).map fun c => (q, c)
  xq := xq

variable {sw : P → Bool → P → Option Bool} {xq : P × Bool → I}

/-- Node `(p, c)` runs the code of `p`. -/
@[simp] lemma doubleCover_φ (x : P × Bool) : (doubleCover sw xq).φ x = x.1 := rfl

/-- Node `(p, c)` listens to the copy `sw p c q` of `q`. -/
@[simp] lemma doubleCover_nbr (x : P × Bool) (q : P) :
    (doubleCover sw xq).nbr x q = (sw x.1 x.2 q).map fun c => (q, c) := rfl

/-- The inputs of a double cover. -/
@[simp] lemma doubleCover_xq (x : P × Bool) : (doubleCover sw xq).xq x = xq x := rfl

/-- In a double cover, a node listens to `q` only through a copy of `q`. -/
lemma doubleCover_φ_of_nbr_eq_some {x y : P × Bool} {q : P}
    (h : (doubleCover sw xq).nbr x q = some y) : (doubleCover sw xq).φ y = q := by
  simp only [doubleCover_nbr, Option.map_eq_some_iff] at h
  obtain ⟨c, -, rfl⟩ := h
  rfl

/-- **Lifts into a double cover.** The honest parties (outside `B`), each running as its copy
`(p, ℓ p)`, form a lift if along every honest edge `p → q` the copy `(q, ℓ q)` listens to the copy
`(p, ℓ p)`. -/
theorem doubleCover_lift {G : SimpleGraph P} {B : Set P} {ℓ : P → Bool}
    (hsw : ∀ p q, p ∉ B → q ∉ B → G.Adj p q → sw q (ℓ q) p = some (ℓ p)) :
    (doubleCover sw xq).Lift G B fun p => (p, ℓ p) where
  φ_σ _ _ := rfl
  nbr_σ p q hp hq hpq := by simp [hsw p q hp hq hpq]

end CoverSystem

end Cslib.Byzantine.LockStep
