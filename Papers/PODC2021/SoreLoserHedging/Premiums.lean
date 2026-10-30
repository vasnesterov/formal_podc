import Mathlib

/-!
# Premium formulas of the hedged multi-party swap (§7.1, Equations (1) and (2))

A swap digraph `G` on a finite vertex type; an arc `G.Adj u v` is a proposed transfer of an asset
from `u` to `v`. A *path* `(u₀, …, u_k)` follows the arcs, `(uᵢ, uᵢ₊₁)` (Figure 3b; the text of §7
writes `(uᵢ₊₁, uᵢ)`, which contradicts Figure 3b and every later use).

* `R q v` — Equation (1): the redemption premium that the head `w` of the path `q` deposits on
  the arc `(v, w)`; `q` is the path along which the premium distribution reached `w` (from `w` to
  the leader). If `v ∥ q` is a path (`v ∉ q`), `R q v = p + ∑_{(u,v) ∈ G} R (v ∥ q) u`; otherwise
  (`v ∥ q` a cycle, or `v` occurs inside `q`) `R q v = p`. The paper gives the recursion for
  every `v ∥ q` that is not a cycle; for `v` inside `q` it does not terminate, and conforming
  parties never extend such a `q` anyway, so we take `p` there.
* `Rlead L = ∑_{(u,L) ∈ G} R [L] u` — the leader's total redemption premium `R(Lᵢ)`.
* `Ein v` — Equation (2): the escrow premium `E(u, v)` on every arc entering `v` (it does not
  depend on `u`): `R(v)` if `v` is a leader, `∑_{(v,w) ∈ G} E(v, w)` otherwise. It is well defined
  because the leaders form a feedback vertex set.

`R` is defined with explicit fuel `card V - q.length` so that the kernel can evaluate it on
examples; `R_eq` is the defining equation.
-/

namespace Podc.SoreLoserHedging

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In-neighbours of `v`. -/
def inN (G : Digraph V) [DecidableRel G.Adj] (v : V) : Finset V := univ.filter (G.Adj · v)

/-- Out-neighbours of `v`. -/
def outN (G : Digraph V) [DecidableRel G.Adj] (v : V) : Finset V := univ.filter (G.Adj v ·)

@[simp] lemma mem_inN {G : Digraph V} [DecidableRel G.Adj] {u v : V} : u ∈ inN G v ↔ G.Adj u v := by
  simp [inN]

@[simp] lemma mem_outN {G : Digraph V} [DecidableRel G.Adj] {v w : V} :
    w ∈ outN G v ↔ G.Adj v w := by
  simp [outN]

section R

variable (G : Digraph V) [DecidableRel G.Adj] (p : ℕ)

/-- Fuelled version of Equation (1). -/
def Rf : ℕ → List V → V → ℕ
  | 0, _, _ => p
  | n + 1, q, v => if (v :: q).Nodup then p + ∑ u ∈ inN G v, Rf n (v :: q) u else p

/-- Equation (1) (redemption premium `Rᵢ(q, v)`), see the module docstring. The leader `i` is
the last vertex of `q`, so it is not a separate argument. -/
def R (q : List V) (v : V) : ℕ := Rf G p (Fintype.card V - q.length) q v

/-- The defining equation of `R` (Equation (1)). -/
lemma R_eq (q : List V) (v : V) :
    R G p q v = if (v :: q).Nodup then p + ∑ u ∈ inN G v, R G p (v :: q) u else p := by
  unfold R
  by_cases h : (v :: q).Nodup
  · have hl := h.length_le_card
    simp only [List.length_cons] at hl
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card V - q.length = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
      (by omega)).symm⟩
    have hn' : Fintype.card V - (v :: q).length = n := by simp; omega
    rw [hn]; simp only [Rf, h, if_true, hn']
  · simp only [h, if_false]
    cases Fintype.card V - q.length with
    | zero => rfl
    | succ n => simp [Rf, h]

lemma p_le_R (q : List V) (v : V) : p ≤ R G p q v := by
  rw [R_eq]; split_ifs <;> omega

/-- `R` on a non-extendable `v ∥ q` (a cycle back to the leader, or `v ∈ q`). -/
lemma R_of_mem {q : List V} {v : V} (h : v ∈ q) : R G p q v = p := by
  rw [R_eq]; simp [h]

/-- `R` on an extendable path: `R(q, v) = p + ∑_{(u,v)} R(v ∥ q, u)`. -/
lemma R_of_not_mem {q : List V} {v : V} (hq : q.Nodup) (h : v ∉ q) :
    R G p q v = p + ∑ u ∈ inN G v, R G p (v :: q) u := by
  rw [R_eq]; simp [h, hq]

/-- The leader's redemption premium `R(Lᵢ) = ∑_{(u, Lᵢ) ∈ G} Rᵢ(Lᵢ, u)`. -/
def Rlead (l : V) : ℕ := ∑ u ∈ inN G l, R G p [l] u

end R

section E

variable (G : Digraph V) [DecidableRel G.Adj] (L : Finset V)

/-- Arcs between followers. -/
def FolAdj (a b : V) : Prop := G.Adj a b ∧ a ∉ L ∧ b ∉ L

instance [DecidableRel G.Adj] : DecidableRel (FolAdj G L) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `L` is a feedback vertex set: there is no cycle consisting of followers only. -/
def IsFVS : Prop := ∀ v, ¬ Relation.TransGen (FolAdj G L) v v

/-- The recursion step of Equation (2): `w` is smaller than the follower `v` if `(v, w) ∈ G`. -/
def FolStep (w v : V) : Prop := G.Adj v w ∧ v ∉ L

variable {G L}

/-- A feedback vertex set certified by a rank that increases along follower arcs. -/
lemma isFVS_of_rank (f : V → ℕ) (h : ∀ a b, FolAdj G L a b → f a < f b) : IsFVS G L := by
  intro v hv
  have : ∀ a b, Relation.TransGen (FolAdj G L) a b → f a < f b := by
    intro a b hab
    induction hab with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact lt_irrefl _ (this v v hv)

lemma folStep_last {a b : V} (h : Relation.TransGen (FolStep G L) a b) : b ∉ L := by
  induction h with
  | single h => exact h.2
  | tail _ h _ => exact h.2

lemma folStep_folAdj {a b : V} (h : Relation.TransGen (FolStep G L) a b) (ha : a ∉ L) :
    Relation.TransGen (FolAdj G L) b a := by
  induction h with
  | single h => exact Relation.TransGen.single ⟨h.1, h.2, ha⟩
  | tail hab h ih => exact Relation.TransGen.head ⟨h.1, h.2, folStep_last hab⟩ ih

lemma folStep_wf (h : IsFVS G L) : WellFounded (FolStep G L) := by
  have htr : WellFounded (Relation.TransGen (FolStep G L)) := by
    haveI : IsTrans V (Relation.TransGen (FolStep G L)) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
    haveI : Std.Irrefl (Relation.TransGen (FolStep G L)) :=
      ⟨fun v hv => h v (folStep_folAdj hv (folStep_last hv))⟩
    exact Finite.wellFounded_of_trans_of_irrefl _
  exact Subrelation.wf (fun h => Relation.TransGen.single h) htr

variable (G L) (p : ℕ)

/-- Equation (2): the escrow premium `E(u, v)` on any arc `(u, v)` entering `v`
(well-founded recursion along follower arcs). -/
noncomputable def Ein (hL : IsFVS G L) : V → ℕ :=
  (folStep_wf hL).fix fun v IH =>
    if hv : v ∈ L then Rlead G p v
    else ∑ w ∈ (outN G v).attach, IH w.1 ⟨(mem_outN.1 w.2), hv⟩

variable {G L p}

/-- The defining equation of `Ein` (Equation (2)). -/
lemma Ein_eq (hL : IsFVS G L) (v : V) :
    Ein G L p hL v = if v ∈ L then Rlead G p v else ∑ w ∈ outN G v, Ein G L p hL w := by
  unfold Ein
  rw [WellFounded.fix_eq]
  split_ifs with hv
  · rfl
  · exact Finset.sum_attach (outN G v) (fun w => (folStep_wf hL).fix _ w)

end E

end Podc.SoreLoserHedging
