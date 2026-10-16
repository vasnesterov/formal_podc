import Papers.PODC2025.TwoShotConsensusObjects.AlgC1Common

/-!
# Class `C₁.₅`: the decision rules of Algorithms 1 and 2 (Lemma 1)

Parameters of the algorithm (`Par`): process `a` plays the role of `p₀` (operations `f`, `f'`),
process `b` the role of `p₁` (operations `g`, `g'`), `O` starts in state `s`.
The decision rules `dec0` (Algorithm 1, lines 6–19), `dec1a` (Algorithm 2, lines 25–30) and
`dec1b` (lines 32–48) are proved correct (`core0`, `core1a`, `core1b`, the paper's Lemma 1): given
the facts the process has learned about the order of the operations on `O` (encoded as the
*role history* `h`, see `il`), the rule returns the role whose first operation was applied first.
-/

namespace TwoShotCons

open Cslib.SharedMemory C1Common

namespace C15Alg

/-- Parameters of the `C₁.₅` algorithm. -/
structure Par (O : ObjSpec) where
  /-- the process playing the role of `p₀` -/
  a : Fin 2
  /-- the process playing the role of `p₁` -/
  b : Fin 2
  /-- the initial state of `O` -/
  s : O.State
  /-- the operations of `p₀` -/
  f : O.Op
  f' : O.Op
  /-- the operations of `p₁` -/
  g : O.Op
  g' : O.Op

variable {O : ObjSpec} (P : Par O)

/-- The five properties of class `C₁.₅` for the parameters `P` (without the allowance
conditions). -/
def Good : Prop :=
  P.a ≠ P.b ∧
  Dist O P.s P.a [(P.a, P.f), (P.b, P.g)] [(P.b, P.g), (P.a, P.f)] ∧
  ¬ Dist O P.s P.b [(P.a, P.f), (P.b, P.g)] [(P.b, P.g), (P.a, P.f)] ∧
  DistBoth O P.s [(P.a, P.f), (P.b, P.g), (P.b, P.g'), (P.a, P.f')]
    [(P.b, P.g), (P.a, P.f), (P.b, P.g'), (P.a, P.f')] ∧
  DistBoth O P.s [(P.b, P.g), (P.b, P.g'), (P.a, P.f), (P.a, P.f')]
    [(P.a, P.f), (P.b, P.g), (P.b, P.g'), (P.a, P.f')] ∧
  (Dist O P.s P.a [(P.b, P.g), (P.b, P.g'), (P.a, P.f)] [(P.a, P.f)] ∨
    DistBoth O P.s [(P.b, P.g), (P.b, P.g'), (P.a, P.f), (P.a, P.f')]
      [(P.a, P.f), (P.b, P.g), (P.a, P.f'), (P.b, P.g')])

/-- The interleaving of operations on `O` described by a role history. -/
abbrev IL (h : List (Fin 2)) : List (Fin 2 × O.Op) := il O P.a P.b P.f P.f' P.g P.g' h

/-- The responses obtained by process `p` in the role history `h`. -/
abbrev V (h : List (Fin 2)) (p : Fin 2) : List O.Resp := view O P.s (IL P h) p

open Classical in
/-- Decision rule of `p₀` (Algorithm 1, lines 6–19): `r`, `r'` are the responses of `f`, `f'`,
`x` the value read from `Ret[1]`. Returns the role whose proposal is decided. -/
noncomputable def dec0 (r : O.Resp) (x : Option O.Resp) (r' : O.Resp) : Fin 2 :=
  match x with
  | none => if r = (O.δ P.s P.f).2 then 0 else 1
  | some _ =>
    if r ≠ (O.δ P.s P.f).2 then 1
    else if r = (O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).2 ∧
        r' = (O.δ (O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).1 P.f').2 then 1
    else 0

open Classical in
/-- Decision rule of `p₁` when its first read of `Ret[0]` returned `v ≠ ⊥` (Algorithm 2,
lines 25–30). -/
noncomputable def dec1a (v : O.Resp) : Fin 2 := if v = (O.δ P.s P.f).2 then 0 else 1

open Classical in
/-- Decision rule of `p₁` after its second read of `Ret[0]` returned `z` (Algorithm 2,
lines 32–48); `r`, `r'` are the responses of `g`, `g'`. -/
noncomputable def dec1b (r r' : O.Resp) (z : Option O.Resp) : Fin 2 :=
  match z with
  | some v =>
    if v ≠ (O.δ P.s P.f).2 then 1
    else if v = (O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).2 ∧ r' = (O.δ (O.δ P.s P.g).1 P.g').2
      then 1
    else 0
  | none =>
    if r = (O.δ (O.δ P.s P.f).1 P.g).2 ∧ r' = (O.δ (O.δ (O.δ P.s P.f).1 P.g).1 P.g').2 then 0
    else 1

/-- What `p₀` learned from its read of `Ret[1]` (between `f` and `f'`): if it read `⊥`, then
at some point `f` was applied but not `g'`; otherwise at some point `g` was applied but not `f'`. -/
def RF0 (x : Option O.Resp) (h : List (Fin 2)) : Prop :=
  match x with
  | none => Snap h fun h₁ => h₁.count 0 = 1 ∧ h₁.count 1 ≤ 1
  | some _ => Snap h fun h₁ => h₁.count 0 = 1 ∧ 1 ≤ h₁.count 1

/-- What `p₁` learned from its first read of `Ret[0]` (between `g` and `g'`). -/
def RF1 (y : Option O.Resp) (h : List (Fin 2)) : Prop :=
  match y with
  | none => Snap h fun h₁ => h₁.count 1 = 1 ∧ h₁.count 0 ≤ 1
  | some v => (V P h P.a).head? = some v ∧ Snap h fun h₁ => h₁.count 1 = 1 ∧ 1 ≤ h₁.count 0

/-- What `p₁` learned from its second read of `Ret[0]` (after `g'`). -/
def RF2 (z : Option O.Resp) (h : List (Fin 2)) : Prop :=
  match z with
  | none => Snap h fun h₁ => h₁.count 1 = 2 ∧ h₁.count 0 ≤ 1
  | some v => (V P h P.a).head? = some v

/-- The C₁.₅ properties as explicit (in)equalities between responses. -/
lemma good_explicit (hG : Good P) :
    (O.δ P.s P.f).2 ≠ (O.δ (O.δ P.s P.g).1 P.f).2 ∧
    (O.δ (O.δ P.s P.f).1 P.g).2 = (O.δ P.s P.g).2 ∧
    ((O.δ (O.δ P.s P.f).1 P.g).2 = (O.δ P.s P.g).2 →
      (O.δ (O.δ (O.δ P.s P.f).1 P.g).1 P.g').2 ≠ (O.δ (O.δ (O.δ P.s P.g).1 P.f).1 P.g').2) ∧
    ((O.δ P.s P.g).2 = (O.δ (O.δ P.s P.f).1 P.g).2 →
      (O.δ (O.δ P.s P.g).1 P.g').2 ≠ (O.δ (O.δ (O.δ P.s P.f).1 P.g).1 P.g').2) ∧
    ((O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).2 = (O.δ P.s P.f).2 →
      (O.δ (O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).1 P.f').2 ≠
        (O.δ (O.δ (O.δ (O.δ P.s P.f).1 P.g).1 P.g').1 P.f').2) ∧
    ((O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).2 ≠ (O.δ P.s P.f).2 ∨
      (((O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).2 = (O.δ P.s P.f).2 →
        (O.δ (O.δ (O.δ (O.δ P.s P.g).1 P.g').1 P.f).1 P.f').2 ≠
          (O.δ (O.δ (O.δ P.s P.f).1 P.g).1 P.f').2) ∧
       ((O.δ P.s P.g).2 = (O.δ (O.δ P.s P.f).1 P.g).2 →
        (O.δ (O.δ P.s P.g).1 P.g').2 ≠
          (O.δ (O.δ (O.δ (O.δ P.s P.f).1 P.g).1 P.f').1 P.g').2))) := by
  obtain ⟨hab, h1, h2, h3, h4, h5⟩ := hG
  have hba : P.b ≠ P.a := Ne.symm hab
  rw [distBoth_iff O hab] at h3 h4
  rw [distBoth_iff O hab] at h5
  obtain ⟨_, h3⟩ := h3
  obtain ⟨h4a, h4b⟩ := h4
  simp only [Dist, view, resps, List.filterMap, hab, hba, ite_true, ite_false,
    ne_eq, List.cons.injEq, not_and, not_not, and_true] at h1 h2 h3 h4a h4b h5
  refine ⟨h1, h2, h3, h4b, h4a, ?_⟩
  rcases h5 with h5 | ⟨h5a, h5b⟩
  · exact Or.inl h5
  · exact Or.inr ⟨h5a, h5b⟩

/-- **Lemma 1 for `p₀`**: the decision rule of Algorithm 1 returns the role whose first
operation was applied first to `O`. -/
lemma core0 (hG : Good P) (h : List (Fin 2)) (hc0 : h.count 0 = 2) (hc1 : h.count 1 ≤ 2)
    (r r' : O.Resp) (hV : V P h P.a = [r, r']) (x : Option O.Resp) (hx : RF0 x h) :
    h.head? = some (dec0 P r x r') := by
  obtain ⟨e1, e2, e3, e4, e4', e5⟩ := good_explicit P hG
  have hab := hG.1
  have hba := Ne.symm hab
  rcases hist_cases (by omega) hc1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hc0 hc1 <;>
  cases x <;> simp only [RF0] at hx <;>
  (try (exfalso; revert hx; simp only [Snap]; decide)) <;>
  simp [V, IL, il, ilAux, view, resps, hba] at hV <;> obtain ⟨rfl, rfl⟩ := hV <;>
  simp [dec0] <;> grind

/-- **Lemma 1 for `p₁`, first block** (Algorithm 2, lines 25–30): `p₁` read `v ≠ ⊥` in `Ret[0]`
between `g` and `g'`. -/
lemma core1a (hG : Good P) (h : List (Fin 2)) (hc1 : h.count 1 = 2) (hc0 : h.count 0 ≤ 2)
    (v : O.Resp) (hv : (V P h P.a).head? = some v)
    (hS : Snap h fun h₁ => h₁.count 1 = 1 ∧ 1 ≤ h₁.count 0) :
    h.head? = some (dec1a P v) := by
  obtain ⟨e1, e2, e3, e4, e4', e5⟩ := good_explicit P hG
  have hba := Ne.symm hG.1
  rcases hist_cases hc0 (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hc0 hc1 <;>
  (try (exfalso; revert hS; simp only [Snap]; decide)) <;>
  simp [V, IL, il, ilAux, view, resps, hba] at hv <;> subst hv <;>
  simp [dec1a] <;> grind

/-- **Lemma 1 for `p₁`, after the second read of `Ret[0]`** (Algorithm 2, lines 32–48): `p₁`
read `⊥` in `Ret[0]` between `g` and `g'`, then `z` after `g'`. -/
lemma core1b (hG : Good P) (h : List (Fin 2)) (hc1 : h.count 1 = 2) (hc0 : h.count 0 ≤ 2)
    (r r' : O.Resp) (hV : V P h P.b = [r, r'])
    (hS : Snap h fun h₁ => h₁.count 1 = 1 ∧ h₁.count 0 ≤ 1) (z : Option O.Resp)
    (hz : RF2 P z h) :
    h.head? = some (dec1b P r r' z) := by
  obtain ⟨e1, e2, e3, e4, e4', e5⟩ := good_explicit P hG
  have hab := hG.1
  have hba := Ne.symm hab
  rcases hist_cases hc0 (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hc0 hc1 <;>
  (try (exfalso; revert hS; simp only [Snap]; decide)) <;>
  cases z <;> simp only [RF2] at hz <;>
  (try (exfalso; revert hz; simp only [Snap]; decide)) <;>
  simp [V, IL, il, ilAux, view, resps, hab] at hV <;> obtain ⟨rfl, rfl⟩ := hV <;>
  (try simp [V, IL, il, ilAux, view, resps, hba] at hz) <;> (try subst hz) <;>
  simp [dec1b] <;> grind

end C15Alg

end TwoShotCons
