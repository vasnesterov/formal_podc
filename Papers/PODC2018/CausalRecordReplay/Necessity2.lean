import Papers.PODC2018.CausalRecordReplay.Model2
import Papers.PODC2018.CausalRecordReplay.Completion

/-!
# Theorem 6.7: necessity of the RnR Model 2 record

R. L. Jones, M. S. Khan, N. H. Vaidya. *Optimal Record and Replay under Causal Consistency.*
PODC 2018; full version arXiv:1805.08804v2, Section 6.1 and Appendix C.

Theorem 6.7: for every good Model-2 record `R` of strongly causal views `V`, every cover
`o₁ ⋖ o₂` of `A_i(V)` that is not in `PO`, `SWO_i(V)` or `B_i(V)` is recorded: `(o₁, o₂) ∈ R_i`.

## The paper's construction is broken

The proof (Appendix C) swaps `e = (o₁, o₂)` using
`U_i = (A_i(V) \ {e}) ∪ {(o₂, o₁)} ∪ C_i(V, o₁, o₂)`, `U_m = A_m(V) ∪ C_i(V, o₁, o₂)` and
claims that `¬ B_i(V)` makes every `U_m` a partial order. This fails whenever `o₁` and `o₂` are
writes and `o₂` is a write of `i`: then `e` itself is in `C¹_i(V, o₁, o₂)` (take `w₃ = o₁`,
`w₄ = o₂`), so `U_i` contains both `e` and its reverse (`paper_U_has_cycle`). (`¬ B_i(V)` only
excludes cycles of `(A_i \ {e}) ∪ C_i`, which does not contain `(o₂, o₁)`.)

## The repaired construction

Write `A' = A_i(V) \ {e}` (transitive because `e` is a cover), `B_p = A_p(V)` for `p ≠ i` and
`B_i = A'` (`Brel`). Let `F` (`Frel`) be the least relation such that
* `(w₃, w₄) ∈ F` if `w₃ ≠ w₄` are writes, `w₄` a write of `i`, `w₃ ≤_{A'} o₂` and `o₁ ≤_{A'} w₄`;
* `(w₃, w₄) ∈ F` if `w₃ ≠ w₄` are writes, `(w₅, w₆) ∈ F`, `w₃ ≤_{B_p ∪ F} w₅`, `w₆ ≤_{B_p} w₄`
  where `p` is the process of `w₄`.
This is `C_i(V, o₁, o₂)` with `A_i` replaced by `A'` (in particular `F ⊆ C_i(V, o₁, o₂)`).
Then `U_m = (B_m ∪ F ∪ {(o₂, o₁) | m = i})⁺` (`Urel`) works when `o₂` is a write; when `o₂` is a
read we take `F = ∅` (as the paper does). Lemma C.5 completes `U` to strongly causal views that
reverse `e` in `V_i`, contradicting goodness.
-/

namespace Podc.CausalRecordReplay

open Relation

section Generic

variable {α : Type*}

theorem reflGen_mono' {r s : α → α → Prop} (h : ∀ a b, r a b → s a b) {a b : α}
    (hab : ReflGen r a b) : ReflGen s a b := by
  rcases hab with _ | hab
  · exact ReflGen.refl
  · exact ReflGen.single (h _ _ hab)

theorem reflGen_of_reflTransGen {r : α → α → Prop} (htr : TransRel r) {a b : α}
    (h : ReflTransGen r a b) : ReflGen r a b := by
  induction h with
  | refl => exact ReflGen.refl
  | tail _ hcd ih => exact ReflGen.single (reflGen_trans_left htr ih hcd)

theorem transGen_supp {r : α → α → Prop} {S : α → Prop} (h : ∀ x y, r x y → S x ∧ S y)
    {a b : α} (hab : TransGen r a b) : S a ∧ S b := by
  induction hab with
  | single h' => exact h _ _ h'
  | tail _ hcd ih => exact ⟨ih.1, (h _ _ hcd).2⟩

/-- Decomposition of a path of `B ∪ F` (`B` transitive) at its last `F`-edge. -/
theorem transGen_union_last {B F : α → α → Prop} (hB : TransRel B) {a b : α}
    (h : TransGen (fun x y => B x y ∨ F x y) a b) :
    B a b ∨ ∃ y z, ReflTransGen (fun x y => B x y ∨ F x y) a y ∧ F y z ∧ ReflGen B z b := by
  induction h with
  | single h =>
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨a, _, ReflTransGen.refl, h, ReflGen.refl⟩
  | @tail c d hac hcd ih =>
    rcases hcd with hcd | hcd
    · rcases ih with ih | ⟨y, z, h1, h2, h3⟩
      · exact Or.inl (hB ih hcd)
      · exact Or.inr ⟨y, z, h1, h2, ReflGen.single (reflGen_trans_left hB h3 hcd)⟩
    · exact Or.inr ⟨c, d, hac.to_reflTransGen, hcd, ReflGen.refl⟩

/-- Paths of `B ∪ F ∪ {(u, v)}`, where `B` is transitive and every `F`-target is an `F`-target
from `u`: either the path avoids `(u, v)`, or it reaches `u` and continues from `v` in `B`. -/
theorem transGen_crossing {B F : α → α → Prop} (hB : TransRel B) {u v : α}
    (hF : ∀ y z, F y z → F u z) {a b : α}
    (h : TransGen (fun x y => (B x y ∨ F x y) ∨ (x = u ∧ y = v)) a b) :
    TransGen (fun x y => B x y ∨ F x y) a b ∨
      (ReflTransGen (fun x y => B x y ∨ F x y) a u ∧ ReflGen B v b) := by
  induction h with
  | single h =>
    rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl (TransGen.single h)
    · exact Or.inr ⟨ReflTransGen.refl, ReflGen.refl⟩
  | @tail c d hac hcd ih =>
    rcases hcd with hcd | ⟨rfl, rfl⟩
    · rcases ih with ih | ⟨h1, h2⟩
      · exact Or.inl (TransGen.tail ih hcd)
      · rcases hcd with hcd | hcd
        · exact Or.inr ⟨h1, reflGen_trans hB h2 (ReflGen.single hcd)⟩
        · exact Or.inl (TransGen.tail' h1 (Or.inr (hF _ _ hcd)))
    · rcases ih with ih | ⟨h1, -⟩
      · exact Or.inr ⟨ih.to_reflTransGen, ReflGen.refl⟩
      · exact Or.inr ⟨h1, ReflGen.refl⟩

end Generic

variable {P Op X : Type*} {π : Program P Op X}

namespace Program

variable (π)

/-- `B_p` of the repaired construction: `A_p(V)`, except that `(o₁, o₂)` is removed from
`A_i(V)`. -/
def Brel (V : P → Op → Op → Prop) (i : P) (o₁ o₂ : Op) (p : P) (x y : Op) : Prop :=
  π.Arel V p x y ∧ ¬ (p = i ∧ x = o₁ ∧ y = o₂)

/-- The two closure rules defining `F` (Definition 6.4 with `A_i` replaced by `A_i \ {(o₁, o₂)}`). -/
def FClosed (V : P → Op → Op → Prop) (i : P) (o₁ o₂ : Op) (G : Op → Op → Prop) : Prop :=
  (∀ w₃ w₄, π.IsWrite w₃ → π.IsWrite w₄ → π.proc w₄ = i → w₃ ≠ w₄ →
      ReflGen (π.Brel V i o₁ o₂ i) w₃ o₂ → ReflGen (π.Brel V i o₁ o₂ i) o₁ w₄ → G w₃ w₄) ∧
  (∀ w₃ w₄ w₅ w₆, π.IsWrite w₃ → π.IsWrite w₄ → w₃ ≠ w₄ → G w₅ w₆ →
      ReflTransGen (fun x y => π.Brel V i o₁ o₂ (π.proc w₄) x y ∨ G x y) w₃ w₅ →
      ReflGen (π.Brel V i o₁ o₂ (π.proc w₄)) w₆ w₄ → G w₃ w₄)

/-- The relation `F` of the repaired construction: the least relation closed under `FClosed`. -/
def Frel (V : P → Op → Op → Prop) (i : P) (o₁ o₂ : Op) (x y : Op) : Prop :=
  ∀ G, π.FClosed V i o₁ o₂ G → G x y

/-- The generators of `U_m`: `B_m ∪ F ∪ {(o₂, o₁) | m = i}`. -/
def Hrel (V : P → Op → Op → Prop) (i : P) (o₁ o₂ : Op) (F : Op → Op → Prop) (m : P)
    (x y : Op) : Prop :=
  (π.Brel V i o₁ o₂ m x y ∨ F x y) ∨ (m = i ∧ x = o₂ ∧ y = o₁)

/-- The paper's (broken) `U_i = (A_i(V) \ {(o₁, o₂)}) ∪ {(o₂, o₁)} ∪ C_i(V, o₁, o₂)`. -/
def paperU (V : P → Op → Op → Prop) (i : P) (o₁ o₂ : Op) (x y : Op) : Prop :=
  (π.Arel V i x y ∧ ¬ (x = o₁ ∧ y = o₂)) ∨ (x = o₂ ∧ y = o₁) ∨ π.Crel true V i o₁ o₂ x y

variable {π}
variable {V : P → Op → Op → Prop} {i : P} {o₁ o₂ : Op}

/-- **The paper's construction fails.** If `o₁` and `o₂` are writes and `o₂` is a write of `i`,
the relation `U_i` of the proof of Theorem 6.7 contains both `(o₁, o₂)` (a pair of `C¹_i`) and
`(o₂, o₁)`, so it is not a partial order. -/
theorem paper_U_has_cycle (hV : π.StronglyCausal V) (hcov : Cov (π.Arel V i) o₁ o₂)
    (hw₁ : π.IsWrite o₁) (hw₂ : π.IsWrite o₂) (hi : π.proc o₂ = i) :
    π.paperU V i o₁ o₂ o₁ o₂ ∧ π.paperU V i o₁ o₂ o₂ o₁ ∧ HasCycle (π.paperU V i o₁ o₂) := by
  have hne : o₁ ≠ o₂ := fun h => (Arel_strictPO hV i).irrefl o₁ (h ▸ hcov.1)
  have h1 : π.paperU V i o₁ o₂ o₁ o₂ :=
    Or.inr (Or.inr ⟨0, hw₁, hw₂, hi, fun _ => hne, ReflGen.single hcov.1, ReflGen.single hcov.1⟩)
  have h2 : π.paperU V i o₁ o₂ o₂ o₁ := Or.inr (Or.inl ⟨rfl, rfl⟩)
  exact ⟨h1, h2, o₁, TransGen.tail (TransGen.single h1) h2⟩

/-! ### `B_p` -/

theorem Brel_arel {p : P} {x y : Op} (h : π.Brel V i o₁ o₂ p x y) : π.Arel V p x y := h.1

theorem Brel_trans (hcov : Cov (π.Arel V i) o₁ o₂) (p : P) : TransRel (π.Brel V i o₁ o₂ p) := by
  intro x y z hxy hyz
  refine ⟨Arel_trans hxy.1 hyz.1, ?_⟩
  rintro ⟨rfl, rfl, rfl⟩
  exact hcov.2 y hxy.1 hyz.1

theorem Brel_irrefl (hV : π.StronglyCausal V) (p : P) (x : Op) : ¬ π.Brel V i o₁ o₂ p x x :=
  fun h => (Arel_strictPO hV p).irrefl x h.1

theorem Brel_of_ne {p : P} (hp : p ≠ i) {x y : Op} (h : π.Arel V p x y) :
    π.Brel V i o₁ o₂ p x y :=
  ⟨h, fun h' => hp h'.1⟩

/-- The pairs of `B_p` ending at a write of `p` are `SWO(V)` pairs other than `(o₁, o₂)`. -/
theorem Brel_swo (hs : ¬ π.SWOi V i o₁ o₂) {a b : Op} (ha : π.IsWrite a) (hb : π.IsWrite b)
    (h : π.Brel V i o₁ o₂ (π.proc b) a b) : π.SWO V a b ∧ ¬ (a = o₁ ∧ b = o₂) := by
  have hsw := SWO_of_Arel_write h.1 ha hb rfl
  refine ⟨hsw, ?_⟩
  rintro ⟨rfl, rfl⟩
  exact hs ⟨hsw, fun hpi => h.2 ⟨hpi, rfl, rfl⟩⟩

theorem ne_of_cov (hV : π.StronglyCausal V) (hcov : Cov (π.Arel V i) o₁ o₂) : o₁ ≠ o₂ :=
  fun h => (Arel_strictPO hV i).irrefl o₁ (h ▸ hcov.1)

theorem not_reflGen_Brel (hV : π.StronglyCausal V) (hcov : Cov (π.Arel V i) o₁ o₂) :
    ¬ ReflGen (π.Brel V i o₁ o₂ i) o₁ o₂ := by
  rintro (_ | h)
  · exact ne_of_cov hV hcov rfl
  · exact h.2 ⟨rfl, rfl, rfl⟩

/-! ### The relation `F` -/

theorem Frel_closed : π.FClosed V i o₁ o₂ (π.Frel V i o₁ o₂) := by
  refine ⟨fun w₃ w₄ h3 h4 hi hne h1 h2 G hG => hG.1 w₃ w₄ h3 h4 hi hne h1 h2,
    fun w₃ w₄ w₅ w₆ h3 h4 hne h56 hp h64 G hG => hG.2 w₃ w₄ w₅ w₆ h3 h4 hne (h56 G hG) ?_ h64⟩
  exact reflTransGen_mono' (fun _ _ h => h.imp_right (fun h => h G hG)) hp

theorem Frel_base {w₃ w₄ : Op} (h3 : π.IsWrite w₃) (h4 : π.IsWrite w₄) (hi : π.proc w₄ = i)
    (hne : w₃ ≠ w₄) (h1 : ReflGen (π.Brel V i o₁ o₂ i) w₃ o₂)
    (h2 : ReflGen (π.Brel V i o₁ o₂ i) o₁ w₄) : π.Frel V i o₁ o₂ w₃ w₄ :=
  Frel_closed.1 w₃ w₄ h3 h4 hi hne h1 h2

theorem Frel_rule {w₃ w₄ w₅ w₆ : Op} (h3 : π.IsWrite w₃) (h4 : π.IsWrite w₄) (hne : w₃ ≠ w₄)
    (h56 : π.Frel V i o₁ o₂ w₅ w₆)
    (hp : ReflTransGen (fun x y => π.Brel V i o₁ o₂ (π.proc w₄) x y ∨ π.Frel V i o₁ o₂ x y) w₃ w₅)
    (h64 : ReflGen (π.Brel V i o₁ o₂ (π.proc w₄)) w₆ w₄) : π.Frel V i o₁ o₂ w₃ w₄ :=
  Frel_closed.2 w₃ w₄ w₅ w₆ h3 h4 hne h56 hp h64

/-- Induction principle for `F`. -/
theorem Frel_induction (Φ : Op → Op → Prop)
    (h0 : ∀ w₃ w₄, π.IsWrite w₃ → π.IsWrite w₄ → π.proc w₄ = i → w₃ ≠ w₄ →
      ReflGen (π.Brel V i o₁ o₂ i) w₃ o₂ → ReflGen (π.Brel V i o₁ o₂ i) o₁ w₄ → Φ w₃ w₄)
    (hs : ∀ w₃ w₄ w₅ w₆, π.IsWrite w₃ → π.IsWrite w₄ → w₃ ≠ w₄ → π.Frel V i o₁ o₂ w₅ w₆ →
      Φ w₅ w₆ →
      ReflTransGen (fun x y => π.Brel V i o₁ o₂ (π.proc w₄) x y ∨
        (π.Frel V i o₁ o₂ x y ∧ Φ x y)) w₃ w₅ →
      ReflGen (π.Brel V i o₁ o₂ (π.proc w₄)) w₆ w₄ → Φ w₃ w₄)
    {x y : Op} (h : π.Frel V i o₁ o₂ x y) : Φ x y := by
  refine (h (fun x y => π.Frel V i o₁ o₂ x y ∧ Φ x y) ⟨fun w₃ w₄ h3 h4 hi hne h1 h2 =>
    ⟨Frel_base h3 h4 hi hne h1 h2, h0 w₃ w₄ h3 h4 hi hne h1 h2⟩,
    fun w₃ w₄ w₅ w₆ h3 h4 hne h56 hp h64 => ⟨Frel_rule h3 h4 hne h56.1 ?_ h64,
      hs w₃ w₄ w₅ w₆ h3 h4 hne h56.1 h56.2 hp h64⟩⟩).2
  exact reflTransGen_mono' (fun _ _ h => h.imp_right And.left) hp

/-- Basic facts on `F`: its pairs are pairs of distinct writes, their targets `t` satisfy
`o₁ ≤_{A_i} t` and `t ≠ o₂`, and `F ⊆ C_i(V, o₁, o₂)`. -/
theorem Frel_props (hV : π.StronglyCausal V) (hcov : Cov (π.Arel V i) o₁ o₂)
    (hs : ¬ π.SWOi V i o₁ o₂) {x y : Op} (h : π.Frel V i o₁ o₂ x y) :
    π.IsWrite x ∧ π.IsWrite y ∧ x ≠ y ∧ ReflGen (π.Arel V i) o₁ y ∧ y ≠ o₂ ∧
      π.Crel true V i o₁ o₂ x y := by
  have hAt : TransRel (π.Arel V i) := (Arel_strictPO hV i).transitive
  refine Frel_induction (fun x y => π.IsWrite x ∧ π.IsWrite y ∧ x ≠ y ∧
      ReflGen (π.Arel V i) o₁ y ∧ y ≠ o₂ ∧ π.Crel true V i o₁ o₂ x y) ?_ ?_ h
  · intro w₃ w₄ h3 h4 hi hne h1 h2
    refine ⟨h3, h4, hne, reflGen_mono' (fun _ _ h => h.1) h2, ?_, 0, h3, h4, hi, fun _ => hne,
      reflGen_mono' (fun _ _ h => h.1) h2, reflGen_mono' (fun _ _ h => h.1) h1⟩
    rintro rfl
    exact not_reflGen_Brel hV hcov h2
  · rintro w₃ w₄ w₅ w₆ h3 h4 hne - ⟨-, h6, -, ho6, h6o, hC⟩ hp h64
    have hA4 : ReflGen (π.Arel V i) o₁ w₄ := by
      rcases h64 with _ | hb
      · exact ho6
      · exact reflGen_trans hAt ho6
          (ReflGen.single (SWO_sub_Arel i (SWO_of_Arel_write hb.1 h6 h4 rfl)))
    refine ⟨h3, h4, hne, hA4, ?_, ?_⟩
    · rintro rfl
      rcases h64 with _ | hb
      · exact h6o rfl
      have hsw := SWO_of_Arel_write hb.1 h6 h4 rfl
      rcases ho6 with _ | ho6
      · exact hs ⟨hsw, fun hpi => hb.2 ⟨hpi, rfl, rfl⟩⟩
      · exact hcov.2 w₆ ho6 (SWO_sub_Arel i hsw)
    · refine Crel_rule h3 h4 hne hC ?_ (reflGen_mono' (fun _ _ h => h.1) h64)
      exact reflTransGen_mono' (fun _ _ h => h.imp Brel_arel (fun h => h.2.2.2.2.2.2)) hp

/-- Every target of `F` is an `F`-target from `o₂` (when `o₂` is a write). -/
theorem Frel_from (hV : π.StronglyCausal V) (hcov : Cov (π.Arel V i) o₁ o₂)
    (hs : ¬ π.SWOi V i o₁ o₂) (hw₂ : π.IsWrite o₂) {x y : Op} (h : π.Frel V i o₁ o₂ x y) :
    π.Frel V i o₁ o₂ o₂ y := by
  refine Frel_induction (fun _ y => π.Frel V i o₁ o₂ o₂ y) ?_ ?_ h
  · intro w₃ w₄ h3 h4 hi hne h1 h2
    have hne' : o₂ ≠ w₄ :=
      fun h => (Frel_props hV hcov hs (Frel_base h3 h4 hi hne h1 h2)).2.2.2.2.1 h.symm
    exact Frel_base hw₂ h4 hi hne' ReflGen.refl h2
  · intro w₃ w₄ w₅ w₆ h3 h4 hne h56 h26 hp h64
    have hne' : o₂ ≠ w₄ := fun h => (Frel_props hV hcov hs (Frel_rule h3 h4 hne h56
      (reflTransGen_mono' (fun _ _ h => h.imp_right And.left) hp) h64)).2.2.2.2.1 h.symm
    exact Frel_rule hw₂ h4 hne' h26 ReflTransGen.refl h64

/-! ### The construction, for a general `F` -/

section Construction

variable (hV : π.StronglyCausal V) (hcov : Cov (π.Arel V i) o₁ o₂)
variable {F : Op → Op → Prop}

include hV hcov in
/-- Acyclicity of `U_m = (B_m ∪ F ∪ {(o₂, o₁) | m = i})⁺`, given acyclicity of `B_m ∪ F` and the
two properties of `F` used in the crossing argument. -/
theorem Hrel_acyclic (hF4 : ∀ y z, F y z → F o₂ z) (hF3 : ∀ y z, F y z → z ≠ o₂)
    (hacyc : ∀ m x, ¬ TransGen (fun a b => π.Brel V i o₁ o₂ m a b ∨ F a b) x x)
    (m : P) (x : Op) : ¬ TransGen (π.Hrel V i o₁ o₂ F m) x x := by
  intro hx
  by_cases hm : m = i
  · subst hm
    have hx' : TransGen (fun a b => (π.Brel V m o₁ o₂ m a b ∨ F a b) ∨ (a = o₂ ∧ b = o₁)) x x :=
      transGen_mono' (fun a b h => h.imp_right (fun h => h.2)) hx
    rcases transGen_crossing (Brel_trans hcov m) hF4 hx' with h | ⟨h1, h2⟩
    · exact hacyc m x h
    · -- a path `o₁ →⁺ o₂` in `B_i ∪ F`
      have h12 : ReflTransGen (fun a b => π.Brel V m o₁ o₂ m a b ∨ F a b) o₁ o₂ :=
        (reflTransGen_mono' (fun _ _ h => Or.inl h) h2.to_reflTransGen).trans h1
      rcases reflTransGen_iff_eq_or_transGen.mp h12 with h | h
      · exact ne_of_cov hV hcov h.symm
      rcases transGen_union_last (Brel_trans hcov m) h with h | ⟨y, z, -, hyz, hz⟩
      · exact h.2 ⟨rfl, rfl, rfl⟩
      · have hz' : π.Brel V m o₁ o₂ m z o₂ := reflGen_of_ne hz (hF3 y z hyz)
        exact hacyc m o₂ (TransGen.tail (TransGen.single (Or.inr (hF4 y z hyz))) (Or.inl hz'))
  · exact hacyc m x (transGen_mono' (fun a b h => h.resolve_right (fun h' => hm h'.1)) hx)

include hcov in
/-- A path of `U_{proc b}` either avoids `(o₂, o₁)`, or `b` is above `o₁` in `A' = B_i` after
reaching `o₂`. -/
theorem Hrel_path (hF4 : ∀ y z, F y z → F o₂ z) {m : P} {a b : Op}
    (h : TransGen (π.Hrel V i o₁ o₂ F m) a b) :
    TransGen (fun x y => π.Brel V i o₁ o₂ m x y ∨ F x y) a b ∨
      (m = i ∧ ReflTransGen (fun x y => π.Brel V i o₁ o₂ m x y ∨ F x y) a o₂ ∧
        ReflGen (π.Brel V i o₁ o₂ m) o₁ b) := by
  by_cases hm : m = i
  · subst hm
    rcases transGen_crossing (Brel_trans hcov m) hF4
      (transGen_mono' (fun a b h => h.imp_right (fun h => h.2)) h) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl (transGen_mono' (fun a b h => h.resolve_right (fun h' => hm h'.1)) h)

include hV hcov in
/-- The core of the proof of Theorem 6.7: if `U_m = (B_m ∪ F ∪ {(o₂, o₁) | m = i})⁺` is acyclic and
its `SCO` pairs lie in `(SWO(V) \ {(o₁, o₂)}) ∪ F`, then a record not containing `(o₁, o₂)`
is not good. -/
theorem not_good_of_construction [Finite Op] {R : P → Op → Op → Prop} (hR : π.IsRecord2 V R)
    (hgood : π.Good2 V R) (h₁ : π.Obs i o₁) (h₂ : π.Obs i o₂) (hpo : ¬ π.po o₁ o₂)
    (hdro : π.DRO (V i) o₁ o₂) (hnR : ¬ R i o₁ o₂)
    (hFw : ∀ x y, F x y → π.IsWrite x ∧ π.IsWrite y)
    (hacyc : ∀ m x, ¬ TransGen (π.Hrel V i o₁ o₂ F m) x x)
    (hsco : ∀ a b, π.IsWrite a → π.IsWrite b → TransGen (π.Hrel V i o₁ o₂ F (π.proc b)) a b →
      (π.SWO V a b ∧ ¬ (a = o₁ ∧ b = o₂)) ∨ F a b) : False := by
  set U : P → Op → Op → Prop := fun m => TransGen (π.Hrel V i o₁ o₂ F m) with hUdef
  have hUpo : ∀ m, IsStrictPO (U m) := fun m => ⟨hacyc m, fun h1 h2 => TransGen.trans h1 h2⟩
  have hUsupp : ∀ m a b, U m a b → π.Obs m a ∧ π.Obs m b := by
    intro m a b h
    refine transGen_supp (fun x y hxy => ?_) h
    rcases hxy with (hxy | hxy) | ⟨rfl, rfl, rfl⟩
    · exact Arel_obs hV hxy.1
    · exact ⟨π.write_obs (hFw x y hxy).1 m, π.write_obs (hFw x y hxy).2 m⟩
    · exact ⟨h₂, h₁⟩
  have hUpoOn : ∀ m a b, π.poOn m a b → U m a b := by
    intro m a b h
    refine TransGen.single (Or.inl (Or.inl ⟨Arel_of_po h.1 h.2.1 h.2.2, ?_⟩))
    rintro ⟨-, rfl, rfl⟩
    exact hpo h.1
  have hUsco : ∀ m a b, π.SCO U a b → U m a b := by
    rintro m a b ⟨ha, hb, hab⟩
    rcases hsco a b ha hb hab with ⟨hsw, hne⟩ | hF
    · exact TransGen.single (Or.inl (Or.inl ⟨SWO_sub_Arel m hsw, fun h => hne h.2⟩))
    · exact TransGen.single (Or.inl (Or.inr hF))
  obtain ⟨W, hW, hUW⟩ := π.lemma_C_5 U hUpo hUsupp hUpoOn hUsco
  obtain ⟨ex', hex'⟩ := π.exists_explains W hW.total
  have hRW : ∀ m a b, R m a b → W m a b := by
    intro m a b h
    refine hUW m a b (TransGen.single (Or.inl (Or.inl ⟨Arel_of_dro (hR m a b h), ?_⟩)))
    rintro ⟨rfl, rfl, rfl⟩
    exact hnR h
  have hdro' := hgood ex' W ⟨hex', hW⟩ hRW i
  have h12 : W i o₁ o₂ := ((congrFun (congrFun hdro' o₁) o₂).mpr hdro).1
  have h21 : W i o₂ o₁ := hUW i o₂ o₁ (TransGen.single (Or.inr ⟨rfl, rfl, rfl⟩))
  exact (hW.total i).asymm h12 h21

end Construction

/-- **Theorem 6.7.** Let `V` be views explaining a strongly causal execution and `R` a good
Model-2 record of `V`. If `(o₁, o₂) ∈ Â_i(V) \ (PO ∪ SWO_i(V) ∪ B_i(V))` for operations
`o₁, o₂ ∈ (∗,i,∗,∗) ∪ (w,∗,∗,∗)`, then `(o₁, o₂) ∈ R_i`. -/
theorem theorem_6_7 [Finite Op] {ex : Program.Execution Op} {V : P → Op → Op → Prop}
    (hV : π.SCCExplains ex V) {R : P → Op → Op → Prop} (hR : π.IsRecord2 V R)
    (hgood : π.Good2 V R) {i : P} {o₁ o₂ : Op} (h₁ : π.Obs i o₁) (h₂ : π.Obs i o₂)
    (hcov : Cov (π.Arel V i) o₁ o₂) (hpo : ¬ π.po o₁ o₂) (hs : ¬ π.SWOi V i o₁ o₂)
    (hb : ¬ π.B2 true V i o₁ o₂) : R i o₁ o₂ := by
  by_contra hnR
  have hSC := hV.2
  have hdro : π.DRO (V i) o₁ o₂ := by
    rcases Agen_of_cov hcov with h | h | h
    · exact h
    · exact absurd h hs
    · exact absurd h.1 hpo
  by_cases hw₂ : π.IsWrite o₂
  · -- `o₂` a write: the repaired construction with `F`
    have hF3 : ∀ y z, π.Frel V i o₁ o₂ y z → z ≠ o₂ :=
      fun y z h => (Frel_props hSC hcov hs h).2.2.2.2.1
    have hF4 : ∀ y z, π.Frel V i o₁ o₂ y z → π.Frel V i o₁ o₂ o₂ z :=
      fun y z h => Frel_from hSC hcov hs hw₂ h
    have hacycG : ∀ m x, ¬ TransGen (fun a b => π.Brel V i o₁ o₂ m a b ∨
        π.Frel V i o₁ o₂ a b) x x := by
      intro m x hx
      by_cases hm : m = i
      · subst hm
        refine hb ⟨hdro.2, hw₂, hdro, m, Or.inr ⟨rfl, x, transGen_mono' (fun a b h => ?_) hx⟩⟩
        rcases h with h | h
        · exact Or.inl ⟨h.1, fun h' => h.2 ⟨rfl, h'⟩⟩
        · exact Or.inr (Frel_props hSC hcov hs h).2.2.2.2.2
      · refine hb ⟨hdro.2, hw₂, hdro, m, Or.inl ⟨hm, x, transGen_mono' (fun a b h => ?_) hx⟩⟩
        rcases h with h | h
        · exact Or.inl h.1
        · exact Or.inr (Frel_props hSC hcov hs h).2.2.2.2.2
    have hacyc := Hrel_acyclic hSC hcov hF4 hF3 hacycG
    refine not_good_of_construction hSC hcov hR hgood h₁ h₂ hpo hdro hnR
      (fun x y h => ⟨(Frel_props hSC hcov hs h).1, (Frel_props hSC hcov hs h).2.1⟩) hacyc ?_
    intro a b ha hbw hab
    have hne : a ≠ b := by rintro rfl; exact hacyc _ a hab
    rcases Hrel_path hcov hF4 hab with h | ⟨hi, h1, h2⟩
    · rcases transGen_union_last (Brel_trans hcov _) h with h | ⟨y, z, hy, hyz, hz⟩
      · exact Or.inl (Brel_swo hs ha hbw h)
      · exact Or.inr (Frel_rule ha hbw hne hyz hy hz)
    · have hb2 : b ≠ o₂ := by rintro rfl; exact not_reflGen_Brel hSC hcov (hi ▸ h2)
      have hF : π.Frel V i o₁ o₂ o₂ b :=
        Frel_base hw₂ hbw hi (Ne.symm hb2) ReflGen.refl (hi ▸ h2)
      exact Or.inr (Frel_rule ha hbw hne hF h1 ReflGen.refl)
  · -- `o₂` a read of `i`: the construction with `F = ∅`
    have hpi : π.proc o₂ = i := h₂.resolve_right hw₂
    have hacycG : ∀ m x, ¬ TransGen (fun a b => π.Brel V i o₁ o₂ m a b ∨ False) x x := by
      intro m x hx
      exact Brel_irrefl hSC m x (of_transGen_of_trans (Brel_trans hcov m)
        (transGen_mono' (fun a b h => h.resolve_right id) hx))
    have hacyc := Hrel_acyclic (F := fun _ _ => False) hSC hcov (fun _ _ h => h)
      (fun _ _ h => h.elim) hacycG
    refine not_good_of_construction hSC hcov hR hgood h₁ h₂ hpo hdro hnR
      (fun _ _ h => h.elim) hacyc ?_
    intro a b ha hbw hab
    left
    have hbo : b ≠ o₂ := by rintro rfl; exact hw₂ hbw
    rcases Hrel_path (F := fun _ _ => False) hcov (fun _ _ h => h) hab with h | ⟨hi, h1, h2⟩
    · rcases transGen_union_last (Brel_trans hcov _) h with h | ⟨y, z, -, hyz, -⟩
      · exact Brel_swo hs ha hbw h
      · exact hyz.elim
    · refine ⟨?_, fun h => hbo h.2⟩
      have h1' : ReflGen (π.Arel V i) a o₂ := reflGen_mono' (fun _ _ h => h.1)
        (reflGen_of_reflTransGen (Brel_trans hcov _)
          (reflTransGen_mono' (fun _ _ h => h.resolve_right id) (hi ▸ h1)))
      rcases π.po_total (hpi.trans hi.symm) (Ne.symm hbo) with hp | hp
      · have hob : π.Arel V i o₂ b := Arel_of_po hp h₂ (π.write_obs hbw i)
        exact SWO_of_Arel_write (reflGen_trans_left (Arel_strictPO hSC i).transitive h1' hob)
          ha hbw hi
      · exfalso
        have hbo' : π.Arel V i b o₂ := Arel_of_po hp (π.write_obs hbw i) h₂
        rcases hi ▸ h2 with _ | h2
        · exact hpo hp
        · exact hcov.2 b h2.1 hbo'

end Program

end Podc.CausalRecordReplay
