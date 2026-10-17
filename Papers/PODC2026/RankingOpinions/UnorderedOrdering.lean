import Cslib.Computability.Distributed.PopulationProtocols.Symmetrize
import Cslib.Computability.Distributed.PopulationProtocols.Schedules
import Cslib.Computability.Distributed.PopulationProtocols.Nondet
import Cslib.Foundations.Data.Nat.Descent
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation

/-!
# The Ordering protocol (Theorem 5.1)

Breitkopf, Dallot, El-Hayek, Schmid, *Ranking Opinions with Few States in Population Protocols*,
PODC 2026 (arXiv:2605.18707), Section 5.1 and Appendix 8.6.

Colors live in an arbitrary type `Col` with decidable equality (agents can only compare colors
for equality); labels live in `Fin k`. An agent stores its initial color `ic`, a leader bit `ld`
and a label `d`. Initially `ld = 1`, `d = 0`. The transition function (pseudocode of 8.6, `a` is
the initiator, `b` the responder; only `a` changes):

```
if ic_a = ic_b then
  if ld_a = 1 and ld_b = 1 then ld_a ← 0
  if ld_a = 0 and ld_b = 1 and d_a ≠ d_b then d_a ← d_b
else
  if d_a = d_b and ld_a = 1 and ld_b = 1 then d_a ← (d_a + 1) mod k
```

Results:
* `ordering_correct` (**Theorem 5.1**): if at most `k` colors occur, then under weak fairness for
  *ordered* pairs (`Execution.OrderedFair`) the configuration eventually never changes and
  contains a valid ordering: exactly one leader per color, and two agents have the same label
  iff they have the same color.
* `ordering_not_weaklyFair`: under weak fairness for *unordered* pairs (`Execution.WeaklyFair`)
  Theorem 5.1 fails (3 agents, 2 colors, `k = 2`): a non-leader only copies the label of its
  leader as the *initiator*, and the scheduler may always choose the other orientation.
* `orderingSymm_correct`: the symmetrized protocol (`Protocol.symm`) is correct under (unordered)
  weak fairness.
* `card_ordState`: `|Col| · 2 · k ≤ 2k²` states.

Proof: instead of the potential `R` of Lemmas 8.6–8.8 we use (after leader election) the set `S`
of labels used by leaders, which only grows, and then, once `S` is constant, the sum over the
leaders of the cyclic distance of their label to a fixed unused label, which strictly decreases at
every increment.
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Unordered

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {Col : Type*} [DecidableEq Col] {k : ℕ}

/-- Cyclic successor `d ↦ (d + 1) mod k` on `Fin k`. -/
def cyc (d : Fin k) : Fin k := ⟨(d.val + 1) % k, Nat.mod_lt _ (by have := d.isLt; omega)⟩

/-- Clockwise distance from `d` to `h`: `(h - d) mod k` (subtraction in `Fin k` is modular). -/
def dist (d h : Fin k) : ℕ := ((h - d : Fin k) : ℕ)

lemma dist_eq (d h : Fin k) : dist d h = (h.val + k - d.val) % k := by
  rw [dist, Fin.val_sub]
  congr 1
  have := d.isLt
  omega

lemma cyc_ne (hk : 2 ≤ k) (d : Fin k) : cyc d ≠ d := by
  intro h
  have h' := congrArg Fin.val h
  simp only [cyc] at h'
  have := d.isLt
  by_cases h1 : d.val + 1 = k
  · rw [h1, Nat.mod_self] at h'; omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h'; omega

lemma dist_cyc {d h : Fin k} (hdh : d ≠ h) : dist (cyc d) h + 1 = dist d h := by
  have hd := d.isLt; have hh := h.isLt
  have hne : d.val ≠ h.val := Fin.val_ne_of_ne hdh
  rw [dist_eq, dist_eq]
  unfold cyc
  simp only
  by_cases hk : d.val + 1 = k
  · rw [hk, Nat.mod_self]
    rw [show h.val + k - 0 = h.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hh]
    rw [show h.val + k - d.val = h.val + 1 by omega, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (show d.val + 1 < k by omega)]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [show h.val + k - (d.val + 1) = (h.val - d.val - 1) + k by omega,
        show h.val + k - d.val = (h.val - d.val) + k by omega, Nat.add_mod_right,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- States of Ordering: initial color, leader bit, label. -/
@[ext] structure OState (Col : Type*) (k : ℕ) where
  /-- The initial color. -/
  ic : Col
  /-- The leader bit. -/
  ld : Bool
  /-- The label. -/
  d : Fin k
  deriving DecidableEq

/-- `OState Col k ≃ Col × Bool × Fin k`. -/
def OState.equiv : OState Col k ≃ Col × Bool × Fin k where
  toFun s := (s.ic, s.ld, s.d)
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype Col] : Fintype (OState Col k) := Fintype.ofEquiv _ OState.equiv.symm

/-- **Theorem 5.1, state count**: Ordering uses `|Col| · 2 · k` states, i.e. at most `2k²` if
there are at most `k` colors. -/
theorem card_ordState [Fintype Col] : Fintype.card (OState Col k) = Fintype.card Col * 2 * k := by
  rw [Fintype.card_congr OState.equiv]; simp [Fintype.card_prod, mul_assoc]

theorem card_ordState_le [Fintype Col] (hC : Fintype.card Col ≤ k) :
    Fintype.card (OState Col k) ≤ 2 * k ^ 2 := by
  rw [card_ordState]
  calc Fintype.card Col * 2 * k ≤ k * 2 * k := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hC)
    _ = 2 * k ^ 2 := by ring

/-- The transition function of Ordering (pseudocode of Appendix 8.6). -/
def ordδ (p q : OState Col k) : OState Col k × OState Col k :=
  if p.ic = q.ic then
    let ld' := p.ld && !q.ld
    (⟨p.ic, ld', if ld' = false ∧ q.ld = true ∧ p.d ≠ q.d then q.d else p.d⟩, q)
  else
    (if p.d = q.d ∧ p.ld = true ∧ q.ld = true then ⟨p.ic, p.ld, cyc p.d⟩ else p, q)

/-- The Ordering protocol. -/
def ordering (Col : Type*) [DecidableEq Col] (k : ℕ) : Protocol (OState Col k) := ⟨ordδ⟩

/-- Initial configuration: `ld = 1`, `d = 0`, `ic` = input color. -/
def ordInit {A : Type*} (input : A → Col) (hk : 0 < k) : Config A (OState Col k) :=
  fun a => ⟨input a, true, ⟨0, hk⟩⟩

/-- A configuration contains a *valid ordering*: exactly one leader per color, and two agents
have the same label iff they have the same color. -/
def ValidOrdering {A : Type*} (C : Config A (OState Col k)) : Prop :=
  (∀ a, ∃! b, (C b).ic = (C a).ic ∧ (C b).ld = true) ∧
    ∀ a b, (C a).d = (C b).d ↔ (C a).ic = (C b).ic

/-! ### Basic properties of the transition function -/

@[simp] lemma ordδ_snd (p q : OState Col k) : (ordδ p q).2 = q := by
  unfold ordδ; split_ifs <;> rfl

@[simp] lemma ordδ_fst_ic (p q : OState Col k) : (ordδ p q).1.ic = p.ic := by
  unfold ordδ; split_ifs <;> rfl

lemma ordδ_fst_ld (p q : OState Col k) :
    (ordδ p q).1.ld = (p.ld && !(decide (p.ic = q.ic) && q.ld)) := by
  unfold ordδ; split_ifs with h1 h2 <;> simp_all

/-- The label of the initiator after an interaction. -/
lemma ordδ_fst_d (p q : OState Col k) :
    (ordδ p q).1.d = if p.ic = q.ic then (if (p.ld && !q.ld) = false ∧ q.ld = true then q.d else p.d)
      else if p.d = q.d ∧ p.ld = true ∧ q.ld = true then cyc p.d else p.d := by
  unfold ordδ
  split_ifs <;> simp_all

lemma ordδ_demote {p q : OState Col k} (hp : p.ld = true) (h : (ordδ p q).1.ld = false) :
    p.ic = q.ic ∧ q.ld = true := by
  rw [ordδ_fst_ld, hp] at h
  by_cases hc : p.ic = q.ic <;> cases hq : q.ld <;> simp_all

/-- When the leader bit of the initiator does not change, its label changes only by an increment
(leaders) or by copying the label of its leader (non-leaders). -/
lemma ordδ_d_change {p q : OState Col k} (hld : (ordδ p q).1.ld = p.ld)
    (hchg : (ordδ p q).1.d ≠ p.d) :
    (p.ld = true → p.ic ≠ q.ic ∧ q.ld = true ∧ p.d = q.d ∧ (ordδ p q).1.d = cyc p.d) ∧
    (p.ld = false → p.ic = q.ic ∧ q.ld = true ∧ (ordδ p q).1.d = q.d) := by
  obtain ⟨i1, l1, d1⟩ := p
  obtain ⟨i2, l2, d2⟩ := q
  rw [ordδ_fst_ld] at hld
  rw [ordδ_fst_d] at hchg ⊢
  simp only at hld hchg ⊢
  by_cases hc : i1 = i2
  · subst hc
    cases l1 <;> cases l2 <;> simp_all
  · cases l1 <;> cases l2 <;> simp_all

variable {A : Type*} [DecidableEq A] [Fintype A]

section Exec

variable (E : (ordering Col k).Execution A)

lemma cfg_succ_of_ne {t : ℕ} {x : A} (hx : x ≠ (E.sched t).1) :
    E.config (t + 1) x = E.config t x := by
  rw [E.step t]
  by_cases hxb : x = (E.sched t).2
  · subst hxb
    rw [interact_self_right _ _ (E.sched_ne t)]
    exact ordδ_snd _ _
  · exact interact_other _ _ hx hxb

lemma cfg_succ_init (t : ℕ) :
    E.config (t + 1) (E.sched t).1 =
      (ordδ (E.config t (E.sched t).1) (E.config t (E.sched t).2)).1 := by
  rw [E.step t, interact_self_left]; rfl

lemma ic_succ (t : ℕ) (x : A) : (E.config (t + 1) x).ic = (E.config t x).ic := by
  by_cases hx : x = (E.sched t).1
  · subst hx; rw [cfg_succ_init]; exact ordδ_fst_ic _ _
  · rw [cfg_succ_of_ne E hx]

lemma ic_eq (t : ℕ) (x : A) : (E.config t x).ic = (E.config 0 x).ic := by
  induction t with
  | zero => rfl
  | succ t ih => rw [ic_succ, ih]

lemma ld_succ_le (t : ℕ) (x : A) :
    (E.config (t + 1) x).ld = true → (E.config t x).ld = true := by
  by_cases hx : x = (E.sched t).1
  · subst hx; rw [cfg_succ_init, ordδ_fst_ld]; simp only [Bool.and_eq_true]; exact fun h => h.1
  · rw [cfg_succ_of_ne E hx]; exact id

/-- Every color class always contains a leader. -/
lemma exists_leader (h0 : ∀ x, (E.config 0 x).ld = true) (t : ℕ) (x : A) :
    ∃ y, (E.config t y).ic = (E.config t x).ic ∧ (E.config t y).ld = true := by
  induction t generalizing x with
  | zero => exact ⟨x, rfl, h0 x⟩
  | succ t ih =>
    obtain ⟨y, hy1, hy2⟩ := ih x
    set a := (E.sched t).1
    set b := (E.sched t).2
    by_cases hya : y = a
    · -- `y` is the initiator; if it is demoted, the responder is a leader of the same color
      by_cases hl : (E.config (t + 1) y).ld = true
      · exact ⟨y, by rw [ic_succ, ic_succ, hy1], hl⟩
      · have hd : (E.config t a).ic = (E.config t b).ic ∧ (E.config t b).ld = true := by
          rw [hya, cfg_succ_init] at hl
          exact ordδ_demote (hya ▸ hy2) (by simpa using hl)
        refine ⟨b, ?_, ?_⟩
        · rw [ic_succ, ic_succ, ← hy1, hya, hd.1]
        · rw [cfg_succ_of_ne E (Ne.symm (E.sched_ne t))]; exact hd.2
    · exact ⟨y, by rw [ic_succ, ic_succ, hy1], by rw [cfg_succ_of_ne E hya]; exact hy2⟩

/-- Number of leaders. -/
abbrev nLeaders (C : Config A (OState Col k)) : ℕ := numLeaders (fun s => s.ld) C

lemma nLeaders_succ_le (t : ℕ) : nLeaders (E.config (t + 1)) ≤ nLeaders (E.config t) :=
  Finset.card_le_card fun x => by simpa using ld_succ_le E t x

/-- **Lemma 8.5 (first part)**: the leader bits eventually never change. -/
lemma leaders_eventually_const : ∃ T, ∀ t ≥ T, ∀ x, (E.config t x).ld = (E.config T x).ld := by
  obtain ⟨T, -, hT⟩ := Nat.eventually_const_of_succ_le (f := fun t => nLeaders (E.config t))
    (N := 0) (fun t _ => nLeaders_succ_le E t)
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ t ht ih =>
    intro x
    have hsub : (univ.filter fun x => (E.config (t + 1) x).ld = true) ⊆
        univ.filter fun x => (E.config t x).ld = true :=
      fun y => by simpa using ld_succ_le E t y
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by have := hT t ht; have := hT (t + 1) (by omega); simp only [nLeaders, numLeaders] at *; omega)
    have := congrArg (fun s => x ∈ s) heq
    simp only [mem_filter, mem_univ, true_and, eq_iff_iff] at this
    rw [← ih x]
    cases h1 : (E.config (t + 1) x).ld <;> cases h2 : (E.config t x).ld <;> simp_all

/-- Leaders of the same color are unique once the leader bits are stable (Lemma 8.5). -/
lemma leader_unique (hE : E.OrderedFair) {T : ℕ}
    (hT : ∀ t ≥ T, ∀ x, (E.config t x).ld = (E.config T x).ld) {t : ℕ} (ht : T ≤ t) {a b : A}
    (ha : (E.config t a).ld = true) (hb : (E.config t b).ld = true)
    (hab : (E.config t a).ic = (E.config t b).ic) : a = b := by
  by_contra hne
  obtain ⟨s, hs, hsched⟩ := hE a b hne t
  have h1 := cfg_succ_init E s
  rw [hsched] at h1
  have := congrArg OState.ld h1
  rw [ordδ_fst_ld, hT (s + 1) (by omega), hT s (by omega), ← hT t ht, ha, ic_eq,
    ic_eq E s b, ← ic_eq E t a, ← ic_eq E t b, hab, hT s (by omega) b, ← hT t ht b, hb] at this
  simp at this

end Exec

/-! ### Labels of leaders -/

section Labels

variable (E : (ordering Col k).Execution A)

/-- The set of labels used by leaders. -/
def usedLabels (C : Config A (OState Col k)) : Finset (Fin k) :=
  (univ.filter fun x => (C x).ld = true).image fun x => (C x).d

/-- Once leader bits are constant, the initiator's label changes only by an increment, which
happens when it meets a leader of another color with the same label. -/
lemma label_change {T t : ℕ} (hT : ∀ t ≥ T, ∀ x, (E.config t x).ld = (E.config T x).ld)
    (ht : T ≤ t) (hchg : (E.config (t + 1) (E.sched t).1).d ≠ (E.config t (E.sched t).1).d) :
    ((E.config t (E.sched t).1).ld = true →
      (E.config t (E.sched t).1).ic ≠ (E.config t (E.sched t).2).ic ∧
      (E.config t (E.sched t).2).ld = true ∧
      (E.config t (E.sched t).1).d = (E.config t (E.sched t).2).d ∧
      (E.config (t + 1) (E.sched t).1).d = cyc (E.config t (E.sched t).1).d) ∧
    ((E.config t (E.sched t).1).ld = false →
      (E.config t (E.sched t).1).ic = (E.config t (E.sched t).2).ic ∧
      (E.config t (E.sched t).2).ld = true ∧
      (E.config (t + 1) (E.sched t).1).d = (E.config t (E.sched t).2).d) := by
  have hld : (E.config (t + 1) (E.sched t).1).ld = (E.config t (E.sched t).1).ld := by
    rw [hT (t + 1) (by omega), hT t ht]
  rw [cfg_succ_init] at hchg hld ⊢
  exact ordδ_d_change hld hchg

lemma usedLabels_mono {T t : ℕ} (hT : ∀ t ≥ T, ∀ x, (E.config t x).ld = (E.config T x).ld)
    (ht : T ≤ t) : usedLabels (E.config t) ⊆ usedLabels (E.config (t + 1)) := by
  intro l hl
  simp only [usedLabels, mem_image, mem_filter, mem_univ, true_and] at hl ⊢
  obtain ⟨x, hx, rfl⟩ := hl
  have hx' : (E.config (t + 1) x).ld = true := by rw [hT (t + 1) (by omega), ← hT t ht]; exact hx
  by_cases hxa : x = (E.sched t).1
  · by_cases hchg : (E.config (t + 1) (E.sched t).1).d = (E.config t (E.sched t).1).d
    · exact ⟨x, hx', by rw [hxa, hchg]⟩
    · obtain ⟨h1, h2, h3, -⟩ := (label_change E hT ht hchg).1 (hxa ▸ hx)
      refine ⟨(E.sched t).2, ?_, ?_⟩
      · rw [hT (t + 1) (by omega), ← hT t ht]; exact h2
      · rw [cfg_succ_of_ne E (Ne.symm (E.sched_ne t)), hxa, h3]
  · exact ⟨x, hx', by rw [cfg_succ_of_ne E hxa]⟩

/-- Sum of the distances of the leaders' labels to the label `h`. -/
def distSum (h : Fin k) (C : Config A (OState Col k)) : ℕ :=
  ∑ x ∈ univ.filter (fun x => (C x).ld = true), dist (C x).d h

end Labels

/-! ### Main theorem -/

/-- The colors present in the input. -/
def colors (input : A → Col) : Finset Col := univ.image input

/-- **Theorem 5.1** (Ordering solves the ordering problem), for weak fairness with ordered
pairs. If at most `k` colors occur, then eventually the configuration never changes and contains a
valid ordering (exactly one leader per color; same label iff same color). -/
theorem ordering_correct (input : A → Col) (hk : 0 < k) (hcol : (colors input).card ≤ k)
    (E : (ordering Col k).Execution A) (h0 : E.config 0 = ordInit input hk)
    (hE : E.OrderedFair) :
    ∃ T, ∀ t ≥ T, E.config t = E.config T ∧ ValidOrdering (E.config t) := by
  have hic : ∀ t x, (E.config t x).ic = input x := fun t x => by rw [ic_eq, h0]; rfl
  have hld0 : ∀ x, (E.config 0 x).ld = true := fun x => by rw [h0]; rfl
  -- Phase 1: leader election
  obtain ⟨T1, hT1⟩ := leaders_eventually_const E
  set lead : A → Prop := fun x => (E.config T1 x).ld = true with hlead_def
  have hldt : ∀ t ≥ T1, ∀ x, (E.config t x).ld = true ↔ lead x := fun t ht x => by
    rw [hT1 t ht]
  have hlead : ∀ x, ∃ y, input y = input x ∧ lead y := fun x => by
    obtain ⟨y, h1, h2⟩ := exists_leader E hld0 T1 x
    exact ⟨y, by rwa [hic, hic] at h1, h2⟩
  choose ℓ hℓc hℓl using hlead
  have huniq : ∀ a b, lead a → lead b → input a = input b → a = b :=
    fun a b ha hb hab => leader_unique E hE hT1 le_rfl ha hb (by rw [hic, hic, hab])
  have hℓself : ∀ x, lead x → ℓ x = x := fun x hx => huniq _ _ (hℓl x) hx (hℓc x)
  -- the set of leaders
  set L := univ.filter lead with hL
  have hLt : ∀ t ≥ T1, univ.filter (fun x => (E.config t x).ld = true) = L := fun t ht => by
    ext x; simp [hL, hldt t ht]
  have hLcard : L.card ≤ k := by
    refine le_trans ?_ hcol
    rw [colors, ← Finset.card_image_of_injOn (f := input) (s := L)]
    · exact card_le_card (image_subset_image (subset_univ _))
    · intro a ha b hb hab
      exact huniq a b (by simpa [hL] using ha) (by simpa [hL] using hb) hab
  -- Phase 2: the set of used labels grows, hence is eventually constant
  obtain ⟨T2, hT2le, hT2⟩ := Nat.eventually_const_of_le_succ
    (f := fun t => (usedLabels (E.config t)).card) (B := k) (N := T1)
    (fun t _ => (card_le_univ _).trans (by simp))
    (fun t ht => card_le_card (usedLabels_mono E hT1 ht))
  have hS : ∀ t ≥ T2, usedLabels (E.config t) = usedLabels (E.config T2) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      rw [← ih]; symm
      exact eq_of_subset_of_card_le (usedLabels_mono E hT1 (by omega))
        (by have := hT2 t ht; have := hT2 (t + 1) (by omega); omega)
  -- a change of a leader's label after `T2`
  have hchange : ∀ t ≥ T2, ∀ x, lead x → (E.config (t + 1) x).d ≠ (E.config t x).d →
      x = (E.sched t).1 ∧ (E.config (t + 1) x).d = cyc (E.config t x).d ∧
      (E.config t x).d ∈ usedLabels (E.config T2) ∧
      ∃ y, y ≠ x ∧ lead y ∧ (E.config t y).d = (E.config t x).d := by
    intro t ht x hx hne
    have hxa : x = (E.sched t).1 := by
      by_contra h; exact hne (by rw [cfg_succ_of_ne E h])
    subst hxa
    obtain ⟨h1, h2, h3, h4⟩ := (label_change E hT1 (by omega) hne).1 ((hldt t (by omega) _).2 hx)
    refine ⟨rfl, h4, ?_, (E.sched t).2, Ne.symm (E.sched_ne t), (hldt t (by omega) _).1 h2,
      h3.symm⟩
    rw [← hS t ht]
    simp only [usedLabels, mem_image, mem_filter, mem_univ, true_and]
    exact ⟨_, (hldt t (by omega) _).2 hx, rfl⟩
  -- Phase 3: leaders' labels are eventually constant
  obtain ⟨T3, hT3le, hT3⟩ : ∃ T3 ≥ T2, ∀ t ≥ T3, ∀ x, lead x →
      (E.config (t + 1) x).d = (E.config t x).d := by
    by_cases hfull : ∃ h, h ∉ usedLabels (E.config T2)
    · obtain ⟨h, hh⟩ := hfull
      have hsum : ∀ t ≥ T2, distSum h (E.config t) = ∑ x ∈ L, dist (E.config t x).d h :=
        fun t ht => by rw [distSum, hLt t (by omega)]
      have hle : ∀ t ≥ T2, ∀ x ∈ L, dist (E.config (t + 1) x).d h ≤ dist (E.config t x).d h ∧
          ((E.config (t + 1) x).d ≠ (E.config t x).d →
            dist (E.config (t + 1) x).d h < dist (E.config t x).d h) := by
        intro t ht x hx
        have hx' : lead x := by simpa [hL] using hx
        by_cases hne : (E.config (t + 1) x).d = (E.config t x).d
        · rw [hne]; exact ⟨le_rfl, fun h' => absurd rfl h'⟩
        · obtain ⟨-, h2, h3, -⟩ := hchange t ht x hx' hne
          have hdh : (E.config t x).d ≠ h := fun e => hh (e ▸ h3)
          have := dist_cyc hdh
          rw [h2]; exact ⟨by omega, fun _ => by omega⟩
      obtain ⟨T3, hT3le, hT3⟩ := Nat.eventually_const_of_succ_le
        (f := fun t => distSum h (E.config t)) (N := T2) (fun t ht => by
          rw [hsum t ht, hsum (t + 1) (by omega)]
          exact Finset.sum_le_sum fun x hx => (hle t ht x hx).1)
      refine ⟨T3, hT3le, fun t ht x hx => ?_⟩
      by_contra hne
      have hlt : distSum h (E.config (t + 1)) < distSum h (E.config t) := by
        rw [hsum t (by omega), hsum (t + 1) (by omega)]
        exact Finset.sum_lt_sum (fun y hy => (hle t (by omega) y hy).1)
          ⟨x, by simpa [hL] using hx, (hle t (by omega) x (by simpa [hL] using hx)).2 hne⟩
      have := hT3 t ht; have := hT3 (t + 1) (by omega); omega
    · push Not at hfull
      refine ⟨T2, le_rfl, fun t ht x hx => ?_⟩
      by_contra hne
      obtain ⟨-, -, -, y, hyx, hy, hyd⟩ := hchange t ht x hx hne
      -- all `k` labels are used by at most `k` leaders: leaders have distinct labels
      have hinj : Set.InjOn (fun x => (E.config t x).d) L := by
        have hcard : (L.image fun x => (E.config t x).d).card = L.card := by
          apply le_antisymm card_image_le
          refine le_trans hLcard (le_of_eq ?_)
          rw [← hLt t (by omega), ← usedLabels, hS t ht]
          rw [show usedLabels (E.config T2) = univ from eq_univ_of_forall hfull]
          simp
        exact Finset.card_image_iff.1 hcard
      exact hyx (hinj (by simpa [hL] using hy) (by simpa [hL] using hx) hyd)
  have hT3' : ∀ t ≥ T3, ∀ x, lead x → (E.config t x).d = (E.config T3 x).d := by
    intro t ht x hx
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hT3 t ht x hx, ih]
  -- leaders of different colors have different labels
  have hdist : ∀ a b, lead a → lead b → a ≠ b →
      (E.config T3 a).d ≠ (E.config T3 b).d := by
    intro a b ha hb hab hd
    have hcolab : input a ≠ input b := fun e => hab (huniq a b ha hb e)
    have hk2 : 2 ≤ k := by
      refine le_trans ?_ hcol
      have : ({input a, input b} : Finset Col) ⊆ colors input := by
        intro c hc; simp only [mem_insert, mem_singleton] at hc
        rcases hc with rfl | rfl <;> simp [colors]
      have h2 := card_le_card this
      rwa [card_pair hcolab] at h2
    obtain ⟨s, hs, hsched⟩ := hE a b hab T3
    have h1 := hT3 s hs a ha
    have h2 := cfg_succ_init E s
    rw [hsched] at h2
    simp only at h2
    rw [h2, ordδ_fst_d, ite_eq_right (by rw [hic, hic]; exact hcolab),
      ite_eq_left ⟨by rw [hT3' s hs a ha, hT3' s hs b hb, hd], (hldt s (by omega) a).2 ha,
        (hldt s (by omega) b).2 hb⟩] at h1
    exact cyc_ne hk2 _ h1
  -- Phase 4: non-leaders copy the label of their leader
  have hcopy : ∀ x, ∃ s ≥ T3, ∀ t ≥ s, (E.config t x).d = (E.config T3 (ℓ x)).d := by
    intro x
    by_cases hx : lead x
    · refine ⟨T3, le_rfl, fun t ht => ?_⟩
      rw [hℓself x hx]; exact hT3' t ht x hx
    · have hxℓ : x ≠ ℓ x := fun e => hx (e ▸ hℓl x)
      obtain ⟨s, hs, hsched⟩ := hE x (ℓ x) hxℓ T3
      have hxld : (E.config s x).ld = false := by
        cases h : (E.config s x).ld
        · rfl
        · exact absurd ((hldt s (by omega) x).1 h) hx
      refine ⟨s + 1, by omega, fun t ht => ?_⟩
      induction t, ht using Nat.le_induction with
      | base =>
        have h2 := cfg_succ_init E s
        rw [hsched] at h2; simp only at h2
        rw [h2, ordδ_fst_d, ite_eq_left (by rw [hic, hic, hℓc]), hxld,
          (hldt s (by omega) (ℓ x)).2 (hℓl x)]
        simp only [Bool.false_and, and_self, ite_true]
        exact hT3' s hs _ (hℓl x)
      | succ t ht ih =>
        by_cases hne : (E.config (t + 1) x).d = (E.config t x).d
        · rw [hne, ih]
        · have hxa : x = (E.sched t).1 := by
            by_contra h; exact hne (by rw [cfg_succ_of_ne E h])
          have hxld' : (E.config t x).ld = false := by
            cases h : (E.config t x).ld
            · rfl
            · exact absurd ((hldt t (by omega) x).1 h) hx
          subst hxa
          obtain ⟨h1, h2, h3⟩ := (label_change E hT1 (by omega) hne).2 hxld'
          have hb : (E.sched t).2 = ℓ (E.sched t).1 := by
            apply huniq _ _ ((hldt t (by omega) _).1 h2) (hℓl _)
            rw [hℓc, ← hic t, ← hic t, h1]
          rw [h3, hb, hT3' t (by omega) _ (hℓl _)]
  choose s hsT3 hs using hcopy
  set T4 := univ.sup s ⊔ T3 with hT4
  have hT4s : ∀ x, s x ≤ T4 := fun x => le_sup_of_le_left (Finset.le_sup (mem_univ x))
  have hd : ∀ t ≥ T4, ∀ x, (E.config t x).d = (E.config T3 (ℓ x)).d :=
    fun t ht x => hs x t (le_trans (hT4s x) ht)
  have hℓinj : ∀ x y, (E.config T3 (ℓ x)).d = (E.config T3 (ℓ y)).d → input x = input y := by
    intro x y hxy
    by_contra hne
    exact hdist (ℓ x) (ℓ y) (hℓl x) (hℓl y)
      (fun e => hne (by rw [← hℓc x, e, hℓc y])) hxy
  refine ⟨T4, fun t ht => ⟨?_, ?_, ?_⟩⟩
  · funext x
    ext
    · rw [hic, hic]
    · rw [hT1 t (by omega), hT1 T4 (by omega)]
    · rw [hd t ht, hd T4 le_rfl]
  · intro a
    refine ⟨ℓ a, ⟨by rw [hic, hic, hℓc], (hldt t (by omega) _).2 (hℓl a)⟩, ?_⟩
    rintro b ⟨hb1, hb2⟩
    rw [hic, hic] at hb1
    exact huniq _ _ ((hldt t (by omega) _).1 hb2) (hℓl a) (by rw [hb1, hℓc])
  · intro a b
    rw [hic, hic, hd t ht, hd t ht]
    constructor
    · exact hℓinj a b
    · intro hab
      have : ℓ a = ℓ b := huniq _ _ (hℓl a) (hℓl b) (by rw [hℓc, hℓc, hab])
      rw [this]

/-! ### The symmetrized protocol under (unordered) weak fairness -/

/-- **Theorem 5.1 for the symmetrized protocol**: every interaction applies the Ordering rules
with both role assignments (`Protocol.symm`). Then Theorem 5.1 holds under weak fairness for
unordered pairs (Definition 2.1 as formalized in `Execution.WeaklyFair`). -/
theorem orderingSymm_correct (input : A → Col) (hk : 0 < k) (hcol : (colors input).card ≤ k)
    (E : (ordering Col k).symm.Execution A) (h0 : E.config 0 = ordInit input hk)
    (hE : E.WeaklyFair) :
    ∃ T, ∀ t ≥ T, E.config t = E.config T ∧ ValidOrdering (E.config t) := by
  obtain ⟨T, hT⟩ := ordering_correct input hk hcol E.unfold (by rw [E.unfold_zero, h0])
    hE.unfold
  refine ⟨T, fun t ht => ?_⟩
  rw [← E.unfold_even t, ← E.unfold_even T]
  exact ⟨(hT _ (by omega)).1.trans (hT _ (by omega)).1.symm, (hT _ (by omega)).2⟩

/-! ### Counterexample under weak fairness for unordered pairs -/

/-- The cyclic part of the counterexample schedule. -/
def cexPairs : Fin 3 → Fin 3 × Fin 3 := ![(1, 0), (0, 2), (1, 2)]

/-- The counterexample schedule: `(0,1)` (agent 0 is demoted), `(1,2)` (agent 1 increments its
label), then forever `(1,0), (0,2), (1,2)`. -/
def cexSched (t : ℕ) : Fin 3 × Fin 3 :=
  match t with
  | 0 => (0, 1)
  | 1 => (1, 2)
  | t + 2 => cexPairs ⟨t % 3, Nat.mod_lt _ (by norm_num)⟩

lemma cexSched_ne (t : ℕ) : (cexSched t).1 ≠ (cexSched t).2 := by
  match t with
  | 0 => decide
  | 1 => decide
  | t + 2 =>
    simp only [cexSched]
    generalize (⟨t % 3, _⟩ : Fin 3) = i
    revert i; decide

/-- The counterexample input: agents 0, 1 have color 0, agent 2 has color 1; `k = 2`. -/
def cexInput : Fin 3 → Fin 2 := ![0, 0, 1]

/-- The counterexample execution. -/
def cexExec : (ordering (Fin 2) 2).Execution (Fin 3) :=
  Execution.ofSched _ (ordInit cexInput (by norm_num)) cexSched cexSched_ne

/-- The configuration reached after two steps, which never changes afterwards: agent 0 is a
non-leader with label 0, its leader (agent 1) has label 1, and agent 2 (other color) has label 0. -/
def cexStuck : Config (Fin 3) (OState (Fin 2) 2) :=
  ![⟨0, false, 0⟩, ⟨0, true, 1⟩, ⟨1, true, 0⟩]

lemma cexExec_stuck (t : ℕ) : cexExec.config (t + 2) = cexStuck := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show t + 1 + 2 = (t + 2) + 1 by omega, cexExec.step, ih]
    simp only [cexExec, Execution.ofSched, cexSched]
    generalize (⟨t % 3, _⟩ : Fin 3) = i
    revert i; decide

lemma cexSched_fair (a b : Fin 3) (hab : a ≠ b) (T : ℕ) :
    ∃ t ≥ T, cexSched t = (a, b) ∨ cexSched t = (b, a) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, cexPairs i = (a, b) ∨ cexPairs i = (b, a) := by
    revert a b; decide
  refine ⟨3 * T + i.val + 2, by omega, ?_⟩
  simp only [cexSched]
  have : (⟨(3 * T + i.val) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = i := by
    ext; simp only; omega
  rw [this]; exact hi

/-- **Theorem 5.1 fails under weak fairness for unordered pairs.** For `k = 2`, two colors and
three agents, there is a weakly fair execution (every unordered pair interacts infinitely often)
of Ordering in which, from time 2 on, the configuration never changes and is not a valid ordering:
agents 0 and 1 have the same color but different labels (and agents 0 and 2 have different
colors but the same label). -/
theorem ordering_not_weaklyFair :
    ∃ E : (ordering (Fin 2) 2).Execution (Fin 3),
      E.config 0 = ordInit cexInput (by norm_num) ∧ (colors cexInput).card ≤ 2 ∧
      E.WeaklyFair ∧ ∀ t ≥ 2, E.config t = cexStuck ∧ ¬ ValidOrdering (E.config t) := by
  refine ⟨cexExec, rfl, (card_le_univ _).trans (by simp), fun a b hab T => cexSched_fair a b hab T, fun t ht => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  rw [cexExec_stuck]
  refine ⟨rfl, fun h => ?_⟩
  have := (h.2 0 1).2 rfl
  exact absurd this (by decide)

end RankingOpinions.Unordered
