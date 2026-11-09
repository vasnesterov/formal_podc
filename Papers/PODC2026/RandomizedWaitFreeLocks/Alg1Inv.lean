import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1Model

/-!
# Algorithm 1: the invariant

One inductive invariant of reachable configurations (`Inv`).  It replaces the paper's
induction over the sequence of promotions (Lemma 4.3) and contains, in state form:

* Observation 4.1 (`e1`–`e4`: an active thunk is the value of `L`);
* Lemma 4.3 (`f1`–`f7`, `o1`–`o4`): a descriptor becomes the value of `L` only while its owner
  is inside lines 1–4 of the current call (`f4`), never twice (`f1`, `f3`), a promoted
  descriptor is never written to `R` again (`o1`, `o3`), and the owner returns `True` once its
  descriptor was promoted (`o2`, Observation 4.2);
* Lemma 4.5 (`g1`–`g3`): while the last value written to `R` is unpromoted, no process whose
  line 6 is not older than that write completes its second `HelpAndPromote()`;
* the auxiliary facts `ib`, `ij`, `ik` used for the case "a stale process promotes a descriptor
  read long ago" of Lemma 4.3(c);
* Observation 4.6 / Corollary 4.7 in rank form (`k1`, `k2`).
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

/-- The inductive invariant of Algorithm 1. -/
structure Inv (c : Cfg P D) : Prop where
  idle_iff : ∀ x, (c.loc x).pc = .idle ↔ (c.loc x).dsc = none
  own_dsc : ∀ x δ, (c.loc x).dsc = some δ → own δ = x
  act_iff : ∀ x, x ∈ c.act ↔ (c.loc x).pc.inAct = true
  C_eq : c.C = c.act.card
  lastW_le : c.lastW ≤ c.T
  lastChg_le : c.lastChg ≤ c.T
  eT_le : ∀ ω, c.eT ω ≤ c.T
  l6_le : ∀ x, ((c.loc x).pc.hap || (c.loc x).pc.post) = true → (c.loc x).l6 ≤ c.T
  a_bd : ∀ x, (c.loc x).pc.h24 = true → (c.loc x).l6 < (c.loc x).a ∧ (c.loc x).a ≤ c.T
  rb_bd : ∀ x i, (c.loc x).pc = .cas i → (c.loc x).a < (c.loc x).rb ∧ (c.loc x).rb ≤ c.T
  fT_bd : ∀ x ∈ c.act, 0 < (c.loc x).fT ∧ (c.loc x).fT ≤ c.T
  e1 : ∀ x i ω, ((c.loc x).pc = .exS i ∨ (c.loc x).pc = .exE i) → (c.loc x).w = some ω →
    c.L = some ω ∨ c.done ω = true
  e2 : ∀ x i ω, ((c.loc x).pc = .rdR i ∨ (c.loc x).pc = .cas i) → (c.loc x).w = some ω →
    c.done ω = true
  e3 : ∀ x ω, ((c.loc x).pc = .exS8 ∨ (c.loc x).pc = .exE8) → (c.loc x).dsc = some ω →
    c.L = some ω ∨ c.done ω = true
  e4 : ∀ ω, c.started ω = true → c.done ω = false → c.L = some ω
  f1 : ∀ ω, c.L = some ω → c.eT ω = c.lastChg ∧ c.eT ω ≠ 0
  f1' : c.L = none → c.lastChg = 0
  f2 : ∀ ω, c.eT ω ≠ 0 → c.L ≠ some ω → c.done ω = true
  f3 : ∀ x, (c.loc x).pc.h24 = true → c.eTo (c.loc x).w < (c.loc x).a ∧ c.everL (c.loc x).w
  f3c : ∀ x, (c.loc x).pc.h24 = true → c.lastChg < (c.loc x).a → c.L = (c.loc x).w
  f4 : ∀ x i, (c.loc x).pc = .cas i → c.L = (c.loc x).w → (c.loc x).d ≠ (c.loc x).w →
    ∃ δ, (c.loc x).d = some δ ∧ c.eT δ = 0 ∧ (c.loc (own δ)).dsc = some δ ∧
      (c.loc (own δ)).pc.hap = true
  f5 : ∀ δ, c.R = some δ → c.eT δ ≠ 0 → c.L = some δ
  f5' : c.R = none → c.L = none ∧ c.lastW = 0
  f6 : ∀ x i, (c.loc x).pc = .cas i → c.L = (c.loc x).w → (c.loc x).d ≠ (c.loc x).w →
    c.R ≠ (c.loc x).w
  f7 : ∀ δ, c.R = some δ → c.eT δ = 0 → (c.loc (own δ)).dsc = some δ ∧
    (c.loc (own δ)).pc.hap = true ∧ (c.loc (own δ)).l6 = c.lastW
  o1 : ∀ δ, c.eT δ ≠ 0 → c.retT δ = true ∨
    ((c.loc (own δ)).dsc = some δ ∧ ((c.loc (own δ)).pc.hap || (c.loc (own δ)).pc.post) = true)
  o2 : ∀ δ, c.eT δ ≠ 0 → (c.loc (own δ)).dsc = some δ →
    ((c.loc (own δ)).pc = .fad ∨ (c.loc (own δ)).pc = .ret) → c.done δ = true
  o3 : ∀ x δ, (c.loc x).dsc = some δ → c.retT δ = false
  o4 : ∀ δ, c.retT δ = true → c.done δ = true
  g1 : ∀ x δ, c.R = some δ → c.eT δ = 0 → ((c.loc x).pc.hap || (c.loc x).pc.post) = true →
    c.lastW ≤ (c.loc x).l6 → (c.loc x).pc.hap = true
  g2 : ∀ x δ, c.R = some δ → c.eT δ = 0 → (c.loc x).pc.hap2 = true →
    c.lastW ≤ (c.loc x).l6 → c.lastW < c.lastChg
  g3 : ∀ x δ, c.R = some δ → c.eT δ = 0 → (c.loc x).pc.h24₂ = true →
    c.lastW ≤ (c.loc x).l6 → c.L = (c.loc x).w
  ib : ∀ x i, (c.loc x).pc = .cas i → c.lastW < (c.loc x).rb → (c.loc x).d = c.R
  ij : ∀ x i δ, (c.loc x).pc = .cas i → c.L = (c.loc x).w → (c.loc x).d = some δ →
    (c.loc x).d ≠ (c.loc x).w → (c.loc (own δ)).pc.isCas = true →
    c.L = (c.loc (own δ)).w → (c.loc (own δ)).d ≠ (c.loc (own δ)).w
  ik : ∀ x i δ, (c.loc x).pc = .cas i → c.L = (c.loc x).w → (c.loc x).d = some δ →
    (c.loc x).d ≠ (c.loc x).w → (c.loc (own δ)).pc.h24₂ = true → c.L = (c.loc (own δ)).w
  k1 : ∀ x ∈ c.act, 1 + (c.act.filter (fun z => (c.loc z).fT < (c.loc x).fT)).card ≤ (c.loc x).b
  k2 : ∀ x ∈ c.act, ∀ z ∈ c.act, (c.loc x).fT = (c.loc z).fT → x = z

omit [DecidableEq P] [DecidableEq D] in
@[simp] lemma eTo_none (c : Cfg P D) : c.eTo none = 0 := rfl
omit [DecidableEq P] [DecidableEq D] in
@[simp] lemma eTo_some (c : Cfg P D) (δ : D) : c.eTo (some δ) = c.eT δ := rfl
omit [DecidableEq P] [DecidableEq D] in
@[simp] lemma everL_none (c : Cfg P D) : c.everL none := trivial
omit [DecidableEq P] [DecidableEq D] in
@[simp] lemma everL_some (c : Cfg P D) (δ : D) : c.everL (some δ) ↔ c.eT δ ≠ 0 := Iff.rfl

lemma inv_init : Inv own (init : Cfg P D) := by
  constructor <;> intros <;> simp_all [init, Loc.init, PC.inAct, PC.hap, PC.post, PC.h24,
    PC.hap2, PC.h24₂, PC.isCas]

end Podc.RandomizedWaitFreeLocks.Alg1
