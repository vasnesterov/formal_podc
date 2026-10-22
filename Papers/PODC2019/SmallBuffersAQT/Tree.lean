import Mathlib
import Podc.Computability.Distributed.AQT.Basic

/-!
# Propositions 3.5 and B.3: PPTS and PTS on directed trees (Appendix B.2)

**Model.** A finite directed forest `T : DTree V` (each node has at most one parent, edges are
directed towards the root(s); acyclicity is witnessed by a depth function). `T.Lt u v` (`u ≺ v`):
`v` is a strict ancestor of `u`; `T.Le u v` (`u ≼ v`): ancestor-or-self. A configuration
`c : V → V → ℕ` stores `c u w` packets at node `u` with destination `w` (meaningful only for
`u ≺ w`). Every edge forwards at most one packet per round. A packet with source `a` and destination
`w` (`a ≺ w`) has the buffer `v` in its route iff `a ≼ v ≺ w`.

The adversary `A t a w` injects packets in round `t` at `a` with destination `w`; entries with
`¬ a ≺ w` are ignored. Packets injected in round `t` are added before the forwarding step of
round `t` (as in the paper); `exec` is the configuration after the injections of round `r`.

**Algorithm 6 (PPTS on trees), closed form.** Destinations `W` with a topological numbering
`idx` (`w ≺ w' → idx w < idx w'` on `W`, injective on `W`). Node `v` is activated for the
destination `w ∈ W` of largest index such that `v ≺ w` and some node `u ≼ v` holds at least two
packets with destination `w`; it then forwards one packet with destination `w` if it has one.
`alg6` is the loop of Algorithm 6 (with `Path(u, w)` excluding `w`) and `alg6_eq_act` shows it
equals this closed form; `alg6Incl_fwd_iff` shows that the paper's literal `Path(u, w)` (including
`w`) forwards the same packets. With `W = {r}` this is the generalized PTS (`act_single`).

**Badness.** `bad c v = Σ_{w ∈ W, v ≺ w} Σ_{u ≼ v} max(c u w - 1, 0)`. The paper (Appendix B.2)
sums over *all* destinations `k ∈ ⟨d⟩`, which also counts bad packets whose destination is not
above `v` (they never cross `v`); with that definition the invariant `B(v) ≤ ξ(v) + 1` fails
(e.g. three packets injected at a child `u` of `v` with destination `v`: `ξ(v) = 0`, `B(v) = 2`).
The restriction `v ≺ w` is the one of the path case (Definition 3.3).

**Main results.** `bad_step_le` (Lemma B.5, generalized), `bad_exec_le` (invariant (3)),
`prop_3_5`, `prop_3_5_depth` (Proposition 3.5), `prop_B_3` (Proposition B.3).
-/

namespace Podc.SmallBuffersAQT.Tree

open Finset Relation
open scoped Classical

/-- A finite directed forest, edges directed towards the roots (`parent v = none`). -/
structure DTree (V : Type*) where
  /-- The parent of a node (`none` for a root). -/
  parent : V → Option V
  /-- A depth function witnessing acyclicity. -/
  depth : V → ℕ
  depth_parent : ∀ v p, parent v = some p → depth p + 1 = depth v

variable {V : Type*}

namespace DTree

variable (T : DTree V)

/-- The edge relation `u → parent u`. -/
def Edge (u v : V) : Prop := T.parent u = some v

/-- `u ≺ v`: `v` is a strict ancestor of `u` (it lies on the path from `u` to the root). -/
def Lt (u v : V) : Prop := TransGen T.Edge u v

/-- `u ≼ v`: `v` is an ancestor of `u` or `u` itself. -/
def Le (u v : V) : Prop := ReflTransGen T.Edge u v

variable {T}

lemma rightUnique : Relator.RightUnique T.Edge := fun _ _ _ h1 h2 => by
  unfold Edge at h1 h2; rw [h1] at h2; exact Option.some_injective _ h2

lemma Lt.depth_lt {u v : V} (h : T.Lt u v) : T.depth v < T.depth u := by
  induction h with
  | single h => have := T.depth_parent _ _ h; omega
  | tail _ h ih => have := T.depth_parent _ _ h; omega

lemma lt_irrefl (u : V) : ¬ T.Lt u u := fun h => Nat.lt_irrefl _ h.depth_lt

lemma le_refl (u : V) : T.Le u u := ReflTransGen.refl

lemma Lt.le {u v : V} (h : T.Lt u v) : T.Le u v := h.to_reflTransGen

lemma le_iff_eq_or_lt {u v : V} : T.Le u v ↔ u = v ∨ T.Lt u v := by
  unfold Le Lt
  rw [reflTransGen_iff_eq_or_transGen]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h

lemma Le.trans {u v w : V} (h1 : T.Le u v) (h2 : T.Le v w) : T.Le u w :=
  ReflTransGen.trans h1 h2

lemma lt_of_le_of_lt {u v w : V} (h1 : T.Le u v) (h2 : T.Lt v w) : T.Lt u w :=
  TransGen.trans_right h1 h2

lemma lt_of_lt_of_le {u v w : V} (h1 : T.Lt u v) (h2 : T.Le v w) : T.Lt u w :=
  TransGen.trans_left h1 h2

lemma lt_of_parent {u p : V} (h : T.parent u = some p) : T.Lt u p := TransGen.single h

lemma Le.antisymm {u v : V} (h1 : T.Le u v) (h2 : T.Le v u) : u = v := by
  rcases le_iff_eq_or_lt.1 h1 with h | h
  · exact h
  · exact absurd (lt_of_lt_of_le h h2) (lt_irrefl u)

/-- If `u ≺ w` then the parent of `u` is `≼ w`. -/
lemma parent_le_of_lt {u p w : V} (hp : T.parent u = some p) (h : T.Lt u w) : T.Le p w := by
  obtain ⟨b, hb, hbw⟩ := TransGen.head'_iff.1 h
  have : b = p := rightUnique hb hp
  exact this ▸ hbw

/-- If `x ≺ u` then `x` lies below some child of `u`. -/
lemma exists_child_of_lt {x u : V} (h : T.Lt x u) : ∃ ch, T.parent ch = some u ∧ T.Le x ch := by
  obtain ⟨b, hb, hbu⟩ := TransGen.tail'_iff.1 h
  exact ⟨b, hbu, hb⟩

/-- The ancestors of a node form a chain. -/
lemma le_total_of_le {u a b : V} (ha : T.Le u a) (hb : T.Le u b) : T.Le a b ∨ T.Le b a :=
  ReflTransGen.total_of_right_unique rightUnique ha hb

lemma lt_total_of_lt {u a b : V} (ha : T.Lt u a) (hb : T.Lt u b) (hab : a ≠ b) :
    T.Lt a b ∨ T.Lt b a := by
  rcases le_total_of_le ha.le hb.le with h | h
  · exact Or.inl ((le_iff_eq_or_lt.1 h).resolve_left hab)
  · exact Or.inr ((le_iff_eq_or_lt.1 h).resolve_left (Ne.symm hab))

end DTree

/-- A configuration: `c u w` packets at node `u` with destination `w`. -/
abbrev Config (V : Type*) := V → V → ℕ

variable [Fintype V] (T : DTree V) (W : Finset V) (idx : V → ℕ)

/-! ### Algorithm 6 (PPTS on trees) -/

/-- The destinations `w ∈ W` for which `v` lies on a path `Path(u, w)` (from a node `u ≼ v` holding
a bad `w`-pseudo-buffer to `w`, excluding `w` itself). -/
noncomputable def cand (c : Config V) (v : V) : Finset V :=
  W.filter (fun w => T.Lt v w ∧ ∃ u, T.Le u v ∧ 2 ≤ c u w)

/-- Activation of Algorithm 6 (closed form): the candidate destination of largest index. -/
noncomputable def act (c : Config V) (v : V) : Option V :=
  if h : (cand T W c v).Nonempty then
    some (Classical.choose ((cand T W c v).exists_max_image idx h))
  else none

/-- One forwarding step of PPTS: every active node `u` (for destination `w`) holding a packet with
destination `w` forwards one such packet to its parent; packets arriving at their destination are
delivered. -/
noncomputable def step (c : Config V) : Config V := fun u w =>
  c u w - (if act T W idx c u = some w ∧ 1 ≤ c u w then 1 else 0) +
    (if T.Lt u w then
      #{ch | T.parent ch = some u ∧ act T W idx c ch = some w ∧ 1 ≤ c ch w} else 0)

/-- Injection of the packets of round `t`. -/
noncomputable def inject (A : ℕ → V → V → ℕ) (t : ℕ) (c : Config V) : Config V := fun u w =>
  c u w + if T.Lt u w then A t u w else 0

/-- The execution of PPTS against the adversary `A`: `exec r` is the configuration after the
injections of round `r` (before its forwarding step). -/
noncomputable def exec (A : ℕ → V → V → ℕ) : ℕ → Config V
  | 0 => inject T A 0 (fun _ _ => 0)
  | r + 1 => inject T A (r + 1) (step T W idx (exec A r))

/-- Number of packets injected in round `t` whose route contains the buffer `v`. -/
noncomputable def injAt (A : ℕ → V → V → ℕ) (v : V) (t : ℕ) : ℕ :=
  ∑ a, ∑ w, if T.Le a v ∧ T.Lt v w then A t a w else 0

/-- `(ρ, σ)`-bounded adversary on the tree (Definition 2.1): for every buffer `v` and every
interval of rounds `[s, t)`, at most `ρ (t - s) + σ` injected packets have `v` in their route. -/
def IsBounded (A : ℕ → V → V → ℕ) (ρ σ : ℝ) : Prop :=
  ∀ v s t, s ≤ t → (Cslib.AQT.seqCross (injAt T A v) s t : ℝ) ≤ ρ * ((t : ℝ) - s) + σ

/-- Badness `B(v)` (Definition B.4, multi-destination version): the number of bad packets at nodes
`u ≼ v` whose destination `w ∈ W` satisfies `v ≺ w` (bad packets that still have to cross `v`). -/
noncomputable def bad (c : Config V) (v : V) : ℕ :=
  ∑ w ∈ W.filter (T.Lt v ·), ∑ u ∈ univ.filter (T.Le · v), (c u w - 1)

/-- Occupancy of the buffer of `v`. -/
def occ (c : Config V) (v : V) : ℕ := ∑ w, c v w

/-! ### Lemma B.5: one forwarding step decreases every positive badness -/

section Step

variable {T W idx}

lemma mem_cand {c : Config V} {v w : V} :
    w ∈ cand T W c v ↔ w ∈ W ∧ T.Lt v w ∧ ∃ u, T.Le u v ∧ 2 ≤ c u w := by
  simp [cand]

lemma act_some {c : Config V} {v w : V} (h : act T W idx c v = some w) :
    w ∈ cand T W c v ∧ ∀ w' ∈ cand T W c v, idx w' ≤ idx w := by
  unfold act at h
  split_ifs at h with hne
  cases h
  exact Classical.choose_spec ((cand T W c v).exists_max_image idx hne)

lemma act_isSome {c : Config V} {v : V} (h : (cand T W c v).Nonempty) :
    ∃ w, act T W idx c v = some w := by
  unfold act; simp [h]

/-- The key structural fact: if `u` is active for `w` but none of its children is, then `u`
itself holds at least two packets with destination `w` (it is the start of an activated path). -/
lemma two_le_of_act (hinj : Set.InjOn idx W)
    (htop : ∀ w ∈ W, ∀ w' ∈ W, T.Lt w w' → idx w < idx w')
    {c : Config V} {u w : V} (hu : act T W idx c u = some w)
    (hch : ∀ ch, T.parent ch = some u → act T W idx c ch ≠ some w) : 2 ≤ c u w := by
  obtain ⟨hw, hmax⟩ := act_some hu
  obtain ⟨hwW, huw, x, hxu, hx⟩ := mem_cand.1 hw
  rcases DTree.le_iff_eq_or_lt.1 hxu with rfl | hxu'
  · exact hx
  obtain ⟨ch, hpch, hxch⟩ := DTree.exists_child_of_lt hxu'
  have hchw : T.Lt ch w := TransGen.head hpch huw
  have hwc : w ∈ cand T W c ch := mem_cand.2 ⟨hwW, hchw, x, hxch, hx⟩
  obtain ⟨w', hw'⟩ := act_isSome (idx := idx) ⟨w, hwc⟩
  obtain ⟨hw'c, hmax'⟩ := act_some hw'
  have h1 := hmax' w hwc
  have hne : w' ≠ w := fun h => hch ch hpch (h ▸ hw')
  obtain ⟨hw'W, hchw', y, hych, hy⟩ := mem_cand.1 hw'c
  have hu' : T.Le u w' := DTree.parent_le_of_lt hpch hchw'
  rcases DTree.le_iff_eq_or_lt.1 hu' with rfl | hlt
  · have := htop _ hw'W _ hwW huw; omega
  · have hc : w' ∈ cand T W c u :=
      mem_cand.2 ⟨hw'W, hlt, y, hych.trans (DTree.lt_of_parent hpch).le, hy⟩
    have h2 := hmax w' hc
    exact absurd (hinj hw'W hwW (by omega)) hne

/-- Per node and destination: `β⁺(u) + [u active for w] ≤ β(u) + #(children of u active for w)`. -/
lemma node_ineq (hinj : Set.InjOn idx W)
    (htop : ∀ w ∈ W, ∀ w' ∈ W, T.Lt w w' → idx w < idx w') (c : Config V) (u w : V) :
    (step T W idx c u w - 1) + (if act T W idx c u = some w then 1 else 0) ≤
      (c u w - 1) + ∑ ch, if T.parent ch = some u ∧ act T W idx c ch = some w then 1 else 0 := by
  set ac := ∑ ch, if T.parent ch = some u ∧ act T W idx c ch = some w then 1 else 0 with hac
  have harr : (if T.Lt u w then
      #{ch | T.parent ch = some u ∧ act T W idx c ch = some w ∧ 1 ≤ c ch w} else 0) ≤ ac := by
    split_ifs
    · rw [card_filter]
      exact sum_le_sum fun ch _ => by split_ifs <;> simp_all
    · exact Nat.zero_le _
  have hzero : ac = 0 → act T W idx c u = some w → 2 ≤ c u w := fun h0 hu =>
    two_le_of_act hinj htop hu fun ch hp ha => by
      have := (sum_eq_zero_iff.1 h0) ch (mem_univ _)
      simp [hp, ha] at this
  unfold step
  generalize (if T.Lt u w then
      #{ch | T.parent ch = some u ∧ act T W idx c ch = some w ∧ 1 ≤ c ch w} else 0) = arr at harr
  by_cases ha : act T W idx c u = some w
  · have h2 : ac = 0 → 2 ≤ c u w := fun h0 => hzero h0 ha
    by_cases h1 : 1 ≤ c u w <;> simp only [ha, h1, and_self, and_false, ite_true, ite_false] <;>
      omega
  · simp only [ha, false_and, ite_false]
    omega

/-- Telescoping over the subtree of `v`. -/
lemma sum_children_le (g : V → ℕ) (v : V) :
    (∑ u ∈ univ.filter (T.Le · v), ∑ ch, if T.parent ch = some u then g ch else 0) + g v ≤
      ∑ u ∈ univ.filter (T.Le · v), g u := by
  rw [sum_comm]
  have h : ∀ ch, (∑ u ∈ univ.filter (T.Le · v), if T.parent ch = some u then g ch else 0) =
      if ∃ p, T.parent ch = some p ∧ T.Le p v then g ch else 0 := by
    intro ch
    cases hp : T.parent ch with
    | none => simp
    | some p =>
      simp only [Option.some.injEq, exists_eq_left']
      rw [sum_ite_eq]
      simp
  rw [sum_congr rfl fun ch _ => h ch, ← sum_filter]
  have hv : v ∉ univ.filter (fun ch => ∃ p, T.parent ch = some p ∧ T.Le p v) := by
    simp only [mem_filter, mem_univ, true_and, not_exists, not_and]
    intro p hp hpv
    exact DTree.lt_irrefl v (DTree.lt_of_lt_of_le (DTree.lt_of_parent hp) hpv)
  rw [add_comm, ← sum_insert hv]
  refine sum_le_sum_of_subset fun x hx => ?_
  simp only [mem_insert, mem_filter, mem_univ, true_and] at hx ⊢
  rcases hx with rfl | ⟨p, hp, hpv⟩
  · exact DTree.le_refl x
  · exact ReflTransGen.head hp hpv

/-- Per destination `w`: the `w`-badness of `v` drops by one if `v` is active for `w`. -/
lemma dest_ineq (hinj : Set.InjOn idx W)
    (htop : ∀ w ∈ W, ∀ w' ∈ W, T.Lt w w' → idx w < idx w') (c : Config V) (v w : V) :
    (∑ u ∈ univ.filter (T.Le · v), (step T W idx c u w - 1)) +
        (if act T W idx c v = some w then 1 else 0) ≤
      ∑ u ∈ univ.filter (T.Le · v), (c u w - 1) := by
  have h1 := sum_le_sum fun u (_ : u ∈ univ.filter (T.Le · v)) => node_ineq hinj htop c u w
  rw [sum_add_distrib, sum_add_distrib] at h1
  have h2 := sum_children_le (T := T) (fun ch => if act T W idx c ch = some w then 1 else 0) v
  simp only [← ite_and] at h2
  omega

/-- **Lemma B.5** (generalized to Algorithm 6): after one forwarding step of PPTS,
`B⁺(v) ≤ max (B(v) - 1, 0)`. -/
theorem bad_step_le (hinj : Set.InjOn idx W)
    (htop : ∀ w ∈ W, ∀ w' ∈ W, T.Lt w w' → idx w < idx w') (c : Config V) (v : V) :
    bad T W (step T W idx c) v ≤ bad T W c v - 1 := by
  have h1 := sum_le_sum fun w (_ : w ∈ W.filter (T.Lt v ·)) => dest_ineq hinj htop c v w
  rw [sum_add_distrib] at h1
  change bad T W (step T W idx c) v + _ ≤ bad T W c v at h1
  rcases Nat.eq_zero_or_pos (bad T W c v) with h0 | hpos
  · omega
  · obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
    obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_sum_ne_zero hw0
    simp only [mem_filter, mem_univ, true_and] at hw hu
    obtain ⟨w0, hw0'⟩ := act_isSome (idx := idx) (c := c) (v := v)
      ⟨w, mem_cand.2 ⟨hw.1, hw.2, u, hu, by omega⟩⟩
    obtain ⟨hc, -⟩ := act_some hw0'
    obtain ⟨hw0W, hvw0, -⟩ := mem_cand.1 hc
    have h2 : 1 ≤ ∑ w ∈ W.filter (T.Lt v ·), (if act T W idx c v = some w then 1 else 0) := by
      refine le_trans ?_ (single_le_sum (f := fun w => if act T W idx c v = some w then 1 else 0)
        (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hw0W, hvw0⟩))
      simp [hw0']
    omega

end Step

/-! ### Injections, invariants and occupancy -/

section Run

variable {T W idx}

variable (T) in
/-- Well-formed configurations: every stored packet still has to move up the tree. -/
def WF (c : Config V) : Prop := ∀ u w, c u w ≠ 0 → T.Lt u w

variable (W) in
/-- All stored packets have destinations in `W`. -/
def DestIn (c : Config V) : Prop := ∀ u w, c u w ≠ 0 → w ∈ W

/-- Injections increase the badness of `v` by at most the number of new packets whose route
contains `v`. -/
lemma bad_inject_le (A : ℕ → V → V → ℕ) (t : ℕ) (c : Config V) (v : V) :
    bad T W (inject T A t c) v ≤ bad T W c v + injAt T A v t := by
  unfold bad inject
  have h1 : (∑ w ∈ W.filter (T.Lt v ·), ∑ u ∈ univ.filter (T.Le · v),
      (c u w + (if T.Lt u w then A t u w else 0) - 1)) ≤
      ∑ w ∈ W.filter (T.Lt v ·), ∑ u ∈ univ.filter (T.Le · v),
        ((c u w - 1) + (if T.Le u v ∧ T.Lt v w then A t u w else 0)) := by
    refine sum_le_sum fun w hw => sum_le_sum fun u hu => ?_
    simp only [mem_filter, mem_univ, true_and] at hw hu
    simp only [DTree.lt_of_le_of_lt hu hw.2, hu, hw.2, and_self, ite_true]
    omega
  refine h1.trans ?_
  simp only [sum_add_distrib]
  refine Nat.add_le_add_left ?_ _
  rw [sum_comm]
  unfold injAt
  refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _) |>.trans'
    (sum_le_sum fun u _ => ?_)
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

omit [Fintype V] in
lemma wf_inject (A : ℕ → V → V → ℕ) (t : ℕ) {c : Config V} (hc : WF T c) :
    WF T (inject T A t c) := by
  intro u w h
  unfold inject at h
  by_cases h' : c u w = 0
  · rw [h', zero_add] at h
    split_ifs at h with hh
    · exact hh
    · exact absurd rfl h
  · exact hc u w h'

omit [Fintype V] in
lemma destIn_inject {A : ℕ → V → V → ℕ} (hA : ∀ t a w, T.Lt a w → A t a w ≠ 0 → w ∈ W)
    (t : ℕ) {c : Config V} (hc : DestIn W c) : DestIn W (inject T A t c) := by
  intro u w h
  unfold inject at h
  by_cases h' : c u w = 0
  · rw [h', zero_add] at h
    split_ifs at h with hh
    · exact hA t u w hh h
    · exact absurd rfl h
  · exact hc u w h'

lemma wf_step {c : Config V} (hc : WF T c) : WF T (step T W idx c) := by
  intro u w h
  unfold step at h
  by_cases h' : c u w = 0
  · rw [h'] at h
    split_ifs at h with h1 h2 h2
    · exact h2
    · simp at h
    · exact h2
    · simp at h
  · exact hc u w h'

lemma destIn_step {c : Config V} (hc : DestIn W c) : DestIn W (step T W idx c) := by
  intro u w h
  unfold step at h
  by_cases h' : c u w = 0
  · rw [h'] at h
    have : #{ch | T.parent ch = some u ∧ act T W idx c ch = some w ∧ 1 ≤ c ch w} ≠ 0 := by
      split_ifs at h <;> omega
    obtain ⟨ch, hch⟩ := card_ne_zero.1 this
    simp only [mem_filter, mem_univ, true_and] at hch
    exact (mem_cand.1 (act_some hch.2.1).1).1
  · exact hc u w h'

lemma bad_zero (v : V) : bad T W (fun _ _ => 0) v = 0 := by simp [bad]

/-- A buffer holds at most one non-bad packet per destination `w ∈ W` with `v ≺ w`, plus bad
packets. -/
lemma occ_le (c : Config V) (hwf : WF T c) (hd : DestIn W c) (v : V) :
    occ c v ≤ #(W.filter (T.Lt v ·)) + bad T W c v := by
  have h1 : occ c v = ∑ w ∈ W.filter (T.Lt v ·), c v w := by
    unfold occ
    refine (sum_subset (subset_univ _) fun w _ hw => ?_).symm
    by_contra h
    exact hw (mem_filter.2 ⟨hd v w h, hwf v w h⟩)
  rw [h1, card_eq_sum_ones]
  unfold bad
  rw [← sum_add_distrib]
  refine sum_le_sum fun w _ => ?_
  have := single_le_sum (s := univ.filter (T.Le · v)) (f := fun u => c u w - 1)
    (fun _ _ => Nat.zero_le _)
    (mem_filter.2 ⟨mem_univ v, DTree.le_refl (T := T) v⟩)
  omega

lemma wf_exec (A : ℕ → V → V → ℕ) (r : ℕ) : WF T (exec T W idx A r) := by
  induction r with
  | zero => exact wf_inject A 0 (fun _ _ h => absurd rfl h)
  | succ r ih => exact wf_inject A _ (wf_step ih)

lemma destIn_exec {A : ℕ → V → V → ℕ} (hA : ∀ t a w, T.Lt a w → A t a w ≠ 0 → w ∈ W)
    (r : ℕ) : DestIn W (exec T W idx A r) := by
  induction r with
  | zero => exact destIn_inject hA 0 (fun _ _ h => absurd rfl h)
  | succ r ih => exact destIn_inject hA _ (destIn_step ih)

/-- The badness invariant (inequality (3) of the paper, tree version): after the injections of
round `r`, `B(v) ≤ ξ(v) + 1`, where `ξ(v)` is the excess of `v` after rounds `[0, r]`. -/
theorem bad_exec_le (hinj : Set.InjOn idx W)
    (htop : ∀ w ∈ W, ∀ w' ∈ W, T.Lt w w' → idx w < idx w') (A : ℕ → V → V → ℕ) {ρ : ℝ}
    (hρ : ρ ≤ 1) (v : V) (r : ℕ) :
    (bad T W (exec T W idx A r) v : ℝ) ≤ Cslib.AQT.seqExcess (injAt T A v) ρ (r + 1) + 1 := by
  induction r with
  | zero =>
    have h1 := bad_inject_le (T := T) (W := W) A 0 (fun _ _ => 0) v
    rw [bad_zero, zero_add] at h1
    have h2 := Cslib.AQT.seq_le_excess_succ (injAt T A v) ρ 0
    have h3 := Cslib.AQT.seqExcess_nonneg (injAt T A v) ρ 0
    have : (bad T W (exec T W idx A 0) v : ℝ) ≤ injAt T A v 0 := by
      exact_mod_cast h1
    linarith
  | succ r ih =>
    have h1 := bad_inject_le (T := T) (W := W) A (r + 1) (step T W idx (exec T W idx A r)) v
    have h2 := Cslib.AQT.seq_le_excess_succ (injAt T A v) ρ (r + 1)
    have h3 := bad_step_le hinj htop (exec T W idx A r) v
    have h4 := Cslib.AQT.seqExcess_nonneg (injAt T A v) ρ (r + 1)
    have h5 : (bad T W (step T W idx (exec T W idx A r)) v : ℝ) ≤
        Cslib.AQT.seqExcess (injAt T A v) ρ (r + 1) := by
      rcases Nat.eq_zero_or_pos (bad T W (exec T W idx A r) v) with h0 | h0
      · have : bad T W (step T W idx (exec T W idx A r)) v = 0 := by omega
        rw [this]; simpa using h4
      · have : bad T W (step T W idx (exec T W idx A r)) v + 1 ≤ bad T W (exec T W idx A r) v := by
          omega
        have : (bad T W (step T W idx (exec T W idx A r)) v : ℝ) + 1 ≤
            bad T W (exec T W idx A r) v := by exact_mod_cast this
        linarith
    have : (bad T W (exec T W idx A (r + 1)) v : ℝ) ≤
        bad T W (step T W idx (exec T W idx A r)) v + injAt T A v (r + 1) := by
      exact_mod_cast h1
    linarith

end Run

/-! ### Algorithm 6 as written: the loop over destinations

`loop S L` runs the loop of Algorithm 6 with the destinations listed in `L` in the order
`w_{d-1}, …, w_0` (decreasing index), where `S w` is the set `⋃_{u ∈ min(B_w)} Path(u, w)`:
`A_w = S w \ A`, `A ← A ∪ A_w`, and the nodes of `A_w` forward for `w`.

* `alg6`: `Path(u, w)` without its endpoint `w`; `alg6_eq_act` shows it equals the closed form
  `act`.
* `alg6Incl`: `Path(u, w)` including `w`, as literally defined in the paper ("the set of nodes on the
  unique path from `u` to `v`"). Then `w` activates its own (empty) `w`-pseudo-buffer; thanks to the
  topological order this never blocks a forwarding: `alg6Incl_fwd_iff` shows that, on well-formed
  configurations, both variants forward exactly the same packets. -/

section Loop

/-- `min(B_w)`: the nodes holding a bad `w`-pseudo-buffer with no such node strictly below. -/
noncomputable def minBad (c : Config V) (w : V) : Finset V :=
  univ.filter (fun u => 2 ≤ c u w ∧ ∀ x, 2 ≤ c x w → ¬ T.Lt x u)

/-- `Path(u, w)` without its endpoint `w`. -/
noncomputable def path (u w : V) : Finset V := univ.filter (fun x => T.Le u x ∧ T.Lt x w)

/-- `Path(u, w)` including its endpoint `w` (the paper's literal definition). -/
noncomputable def pathIncl (u w : V) : Finset V := univ.filter (fun x => T.Le u x ∧ T.Le x w)

/-- One iteration of the loop of Algorithm 6 (lines 3–5) with activation sets `S`; the state is the
set `A` of activated nodes and the destination each activated node forwards for. -/
noncomputable def loopStep (S : V → Finset V) (st : Finset V × (V → Option V)) (w : V) :
    Finset V × (V → Option V) :=
  (st.1 ∪ (S w \ st.1), fun v => if v ∈ S w \ st.1 then some w else st.2 v)

/-- The loop of Algorithm 6, destinations processed in the order of the list `L`. -/
noncomputable def loop (S : V → Finset V) (L : List V) : V → Option V :=
  (L.foldl (loopStep S) (∅, fun _ => none)).2

/-- Algorithm 6 with `Path(u, w)` excluding `w`. -/
noncomputable def alg6 (c : Config V) (L : List V) : V → Option V :=
  loop (fun w => (minBad T c w).biUnion fun u => path T u w) L

/-- Algorithm 6 with `Path(u, w)` including `w`. -/
noncomputable def alg6Incl (c : Config V) (L : List V) : V → Option V :=
  loop (fun w => (minBad T c w).biUnion fun u => pathIncl T u w) L

/-- The first `w` of `L` with `v ∈ S w`. -/
noncomputable def firstIn (S : V → Finset V) : List V → V → Option V
  | [], _ => none
  | w :: L, v => if v ∈ S w then some w else firstIn S L v

/-- The first destination of `L` whose activated paths contain `v`. -/
noncomputable def firstCond (c : Config V) : List V → V → Option V
  | [], _ => none
  | w :: L, v => if T.Lt v w ∧ ∃ u, T.Le u v ∧ 2 ≤ c u w then some w else firstCond c L v

variable {T} {idx}

lemma mem_biUnion_path (c : Config V) (v w : V) :
    v ∈ (minBad T c w).biUnion (fun u => path T u w) ↔
      T.Lt v w ∧ ∃ u, T.Le u v ∧ 2 ≤ c u w := by
  simp only [mem_biUnion, minBad, path, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨hu, -⟩, huv, hvw⟩
    exact ⟨hvw, u, huv, hu⟩
  · rintro ⟨hvw, u, huv, hu⟩
    have hne : (univ.filter (fun x => 2 ≤ c x w ∧ T.Le x v)).Nonempty :=
      ⟨u, mem_filter.2 ⟨mem_univ _, hu, huv⟩⟩
    obtain ⟨x, hx, hmax⟩ := exists_max_image _ T.depth hne
    simp only [mem_filter, mem_univ, true_and] at hx
    refine ⟨x, ⟨hx.1, fun y hy hyx => ?_⟩, hx.2, hvw⟩
    have := hmax y (mem_filter.2 ⟨mem_univ _, hy, (hyx.le).trans hx.2⟩)
    have := hyx.depth_lt
    omega

lemma mem_biUnion_pathIncl_of_ne (c : Config V) {v w : V} (hvw : v ≠ w) :
    v ∈ (minBad T c w).biUnion (fun u => pathIncl T u w) ↔
      v ∈ (minBad T c w).biUnion (fun u => path T u w) := by
  simp only [mem_biUnion, pathIncl, path, mem_filter, mem_univ, true_and]
  refine exists_congr fun u => and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [DTree.le_iff_eq_or_lt]
  simp [hvw]

omit [Fintype V] in
lemma foldl_loopStep (S : V → Finset V) (v : V) (L : List V) (A : Finset V) (f : V → Option V)
    (hf : ∀ x, x ∉ A → f x = none) :
    (L.foldl (loopStep S) (A, f)).2 v = if v ∈ A then f v else firstIn S L v := by
  induction L generalizing A f with
  | nil =>
    by_cases hA : v ∈ A
    · simp [hA]
    · simp [hA, hf v hA, firstIn]
  | cons w L ih =>
    simp only [List.foldl_cons, loopStep]
    rw [ih]
    swap
    · intro x hx
      simp only [mem_union, not_or] at hx
      simp only [hx.2, ite_false]
      exact hf x hx.1
    simp only [mem_union, mem_sdiff, firstIn]
    by_cases hA : v ∈ A <;> by_cases hc : v ∈ S w <;> simp [hA, hc]

omit [Fintype V] in
lemma loop_eq_firstIn (S : V → Finset V) (L : List V) : loop S L = firstIn S L := by
  funext v
  unfold loop
  rw [foldl_loopStep S v L ∅ _ (fun _ _ => rfl)]
  simp

lemma firstIn_eq_firstCond (c : Config V) (L : List V) (v : V) :
    firstIn (fun w => (minBad T c w).biUnion fun u => path T u w) L v = firstCond T c L v := by
  induction L with
  | nil => rfl
  | cons w L ih => simp only [firstIn, firstCond, mem_biUnion_path, ih]

lemma firstCond_some (c : Config V) {L : List V} (hL : L.Pairwise (fun a b => idx b < idx a))
    {v w : V} (h : firstCond T c L v = some w) :
    w ∈ L ∧ (T.Lt v w ∧ ∃ u, T.Le u v ∧ 2 ≤ c u w) ∧
      ∀ w' ∈ L, (T.Lt v w' ∧ ∃ u, T.Le u v ∧ 2 ≤ c u w') → idx w' ≤ idx w := by
  induction L with
  | nil => simp [firstCond] at h
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    simp only [firstCond] at h
    split_ifs at h with hc
    · cases h
      refine ⟨List.mem_cons_self .., hc, fun w' hw' _ => ?_⟩
      rcases List.mem_cons.1 hw' with rfl | hw'
      · exact le_rfl
      · exact (hL.1 w' hw').le
    · obtain ⟨h1, h2, h3⟩ := ih hL.2 h
      refine ⟨List.mem_cons_of_mem _ h1, h2, fun w' hw' hc' => ?_⟩
      rcases List.mem_cons.1 hw' with rfl | hw'
      · exact absurd hc' hc
      · exact h3 w' hw' hc'

lemma firstCond_none (c : Config V) {L : List V} {v : V} (h : firstCond T c L v = none) :
    ∀ w ∈ L, ¬ (T.Lt v w ∧ ∃ u, T.Le u v ∧ 2 ≤ c u w) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [firstCond] at h
    split_ifs at h with hc
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hc
    · exact ih h w hw

omit [Fintype V] in
lemma pairwise_inj {L : List V} (hL : L.Pairwise (fun a b => idx b < idx a)) :
    ∀ a ∈ L, ∀ b ∈ L, idx a = idx b → a = b := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.pairwise_cons] at hL
    intro a ha b hb hab
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · have := hL.1 b hb; omega
    · have := hL.1 a ha; omega
    · exact ih hL.2 a ha b hb hab

/-- The loop of Algorithm 6 (destinations listed by decreasing index) computes the closed-form
activation `act`. -/
theorem alg6_eq_act (c : Config V) {L : List V} (hL : L.Pairwise (fun a b => idx b < idx a)) :
    alg6 T c L = act T L.toFinset idx c := by
  funext v
  unfold alg6
  rw [loop_eq_firstIn, firstIn_eq_firstCond]
  have hinj := pairwise_inj hL
  by_cases hne : (cand T L.toFinset c v).Nonempty
  · obtain ⟨w0, hw0⟩ := act_isSome (idx := idx) hne
    rw [hw0]
    obtain ⟨hc0, hmax0⟩ := act_some hw0
    obtain ⟨hw0L, hcond0⟩ := (mem_cand.1 hc0) |> fun h => (⟨List.mem_toFinset.1 h.1, h.2⟩ :
      w0 ∈ L ∧ _)
    cases h : firstCond T c L v with
    | none => exact absurd hcond0 (firstCond_none c h w0 hw0L)
    | some w1 =>
      obtain ⟨hw1L, hcond1, hmax1⟩ := firstCond_some c hL h
      have h1 := hmax1 w0 hw0L hcond0
      have h2 := hmax0 w1 (mem_cand.2 ⟨List.mem_toFinset.2 hw1L, hcond1⟩)
      rw [hinj w1 hw1L w0 hw0L (by omega)]
  · unfold act
    simp only [hne, dite_false]
    cases h : firstCond T c L v with
    | none => rfl
    | some w1 =>
      obtain ⟨hw1L, hcond1, -⟩ := firstCond_some c hL h
      exact absurd ⟨w1, mem_cand.2 ⟨List.mem_toFinset.2 hw1L, hcond1⟩⟩ hne

omit [Fintype V] in
lemma firstIn_some {S : V → Finset V} {L : List V} {v w : V} (h : firstIn S L v = some w) :
    w ∈ L ∧ v ∈ S w := by
  induction L with
  | nil => simp [firstIn] at h
  | cons a L ih =>
    simp only [firstIn] at h
    split_ifs at h with hc
    · cases h; exact ⟨List.mem_cons_self .., hc⟩
    · obtain ⟨h1, h2⟩ := ih h; exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- The literal Algorithm 6 (`Path(u, w)` including `w`) forwards exactly the same packets as
`alg6` (and hence as the closed form `act`, by `alg6_eq_act`), on well-formed configurations and
for a topologically sorted list of destinations. -/
theorem alg6Incl_fwd_iff (c : Config V) (hwf : WF T c) {L : List V}
    (hL : L.Pairwise (fun a b => idx b < idx a))
    (htop : ∀ w ∈ L, ∀ w' ∈ L, T.Lt w w' → idx w < idx w') (v w : V) :
    (alg6Incl T c L v = some w ∧ 1 ≤ c v w) ↔ (alg6 T c L v = some w ∧ 1 ≤ c v w) := by
  unfold alg6Incl alg6
  rw [loop_eq_firstIn, loop_eq_firstIn]
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    have ih := ih hL.2 (fun x hx y hy => htop x (List.mem_cons_of_mem _ hx) y
      (List.mem_cons_of_mem _ hy))
    simp only [firstIn]
    by_cases hE : v ∈ (minBad T c a).biUnion fun u => path T u a
    · have hva : v ≠ a := by
        rintro rfl
        exact DTree.lt_irrefl _ ((mem_biUnion_path c v v).1 hE).1
      simp only [hE, (mem_biUnion_pathIncl_of_ne c hva).2 hE, ite_true]
    · simp only [hE, ite_false]
      by_cases hva : v = a
      · subst hva
        split_ifs with hI
        · constructor
          · rintro ⟨h1, h2⟩
            cases h1
            exact absurd (hwf v v (by omega)) (DTree.lt_irrefl v)
          · rintro ⟨h1, -⟩
            obtain ⟨hwL, hvw⟩ := firstIn_some h1
            have h3 := htop v (List.mem_cons_self ..) w (List.mem_cons_of_mem _ hwL)
              ((mem_biUnion_path c v w).1 hvw).1
            have h4 := hL.1 w hwL
            omega
        · exact ih
      · simp only [show v ∉ (minBad T c a).biUnion (fun u => pathIncl T u a) from
          fun h => hE ((mem_biUnion_pathIncl_of_ne c hva).1 h), ite_false]
        exact ih

end Loop

/-! ### Propositions 3.5 and B.3 -/

variable {T W idx}

/-- **Proposition 3.5** of [MPR19] (PPTS on directed trees, Algorithm 6): against a
`(ρ, σ)`-bounded adversary with `ρ ≤ 1` whose packets have destinations in `W` (numbered by a
topological order `idx`), every buffer `v` holds, in every round, at most
`#{w ∈ W : v ≺ w} + σ + 1` packets. -/
theorem prop_3_5 (hinj : Set.InjOn idx W)
    (htop : ∀ w ∈ W, ∀ w' ∈ W, T.Lt w w' → idx w < idx w') {A : ℕ → V → V → ℕ} {ρ σ : ℝ}
    (hA : IsBounded T A ρ σ) (hρ : ρ ≤ 1) (hW : ∀ t a w, T.Lt a w → A t a w ≠ 0 → w ∈ W)
    (r : ℕ) (v : V) :
    (occ (exec T W idx A r) v : ℝ) ≤ #(W.filter (T.Lt v ·)) + σ + 1 := by
  have h1 := occ_le (exec T W idx A r) (wf_exec A r) (destIn_exec hW r) v
  have h2 := bad_exec_le hinj htop A hρ v r
  have h3 := Cslib.AQT.seqExcess_le (hA v) (r + 1)
  have : (occ (exec T W idx A r) v : ℝ) ≤ #(W.filter (T.Lt v ·)) + bad T W (exec T W idx A r) v := by
    exact_mod_cast h1
  linarith

omit [Fintype V] in
/-- The destinations strictly above `v` form a chain. -/
lemma isChain_filter_lt (v : V) : IsChain T.Lt (↑(W.filter (T.Lt v ·)) : Set V) := by
  intro a ha b hb hab
  simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
  exact DTree.lt_total_of_lt ha.2 hb.2 hab

/-- **Proposition 3.5** of [MPR19], with the destination depth `d'`: if every chain (w.r.t. `≺`) of
destinations has at most `d'` elements (equivalently, every leaf-root path contains at most `d'`
destinations), every buffer holds at most `1 + d' + σ` packets. -/
theorem prop_3_5_depth (hinj : Set.InjOn idx W)
    (htop : ∀ w ∈ W, ∀ w' ∈ W, T.Lt w w' → idx w < idx w') {A : ℕ → V → V → ℕ} {ρ σ : ℝ}
    (hA : IsBounded T A ρ σ) (hρ : ρ ≤ 1) (hW : ∀ t a w, T.Lt a w → A t a w ≠ 0 → w ∈ W)
    {d' : ℕ} (hd' : ∀ C ⊆ W, IsChain T.Lt (C : Set V) → C.card ≤ d') (r : ℕ) (v : V) :
    (occ (exec T W idx A r) v : ℝ) ≤ 1 + d' + σ := by
  have h1 := prop_3_5 hinj htop hA hρ hW r v
  have h2 : (#(W.filter (T.Lt v ·)) : ℝ) ≤ d' := by
    exact_mod_cast hd' _ (filter_subset _ _) (isChain_filter_lt v)
  linarith

/-- With a single destination `r`, Algorithm 6 is the generalized PTS of Appendix B.2: it activates
every node `v ≺ r` such that some node `u ≼ v` is bad. -/
lemma act_single (c : Config V) (r v : V) :
    act T {r} idx c v = if T.Lt v r ∧ ∃ u, T.Le u v ∧ 2 ≤ c u r then some r else none := by
  by_cases h : (cand T {r} c v).Nonempty
  · obtain ⟨w, hw⟩ := act_isSome (idx := idx) h
    have hwr := (mem_cand.1 (act_some hw).1)
    rw [mem_singleton] at hwr
    obtain ⟨rfl, h2⟩ := hwr
    simp only [hw, h2, and_self, ite_true]
  · have h' : ¬ (T.Lt v r ∧ ∃ u, T.Le u v ∧ 2 ≤ c u r) := fun ⟨h1, h2⟩ =>
      h ⟨r, mem_cand.2 ⟨mem_singleton_self r, h1, h2⟩⟩
    unfold act
    simp only [h, h', dite_false, ite_false]

/-- **Proposition B.3** of [MPR19] (PTS on directed trees): if all packets have the same
destination `r` (the root in the paper; any node works), then against a `(ρ, σ)`-bounded adversary
with `ρ ≤ 1` every buffer holds at most `2 + σ` packets in every round. PTS is Algorithm 6 with
`W = {r}` (`act_single`). -/
theorem prop_B_3 {A : ℕ → V → V → ℕ} {ρ σ : ℝ} (hA : IsBounded T A ρ σ) (hρ : ρ ≤ 1) {r : V}
    (hr : ∀ t a w, T.Lt a w → A t a w ≠ 0 → w = r) (t : ℕ) (v : V) :
    (occ (exec T {r} idx A t) v : ℝ) ≤ 2 + σ := by
  have h := prop_3_5 (W := {r}) (idx := idx) (by simp) (fun w hw w' hw' h => by
      rw [mem_singleton] at hw hw'; subst hw hw'; exact absurd h (DTree.lt_irrefl _))
    hA hρ (fun t a w h1 h2 => mem_singleton.2 (hr t a w h1 h2)) t v
  have : (#(({r} : Finset V).filter (T.Lt v ·)) : ℝ) ≤ 1 := by
    exact_mod_cast (card_filter_le _ _).trans (card_singleton r).le
  linarith

/-! ### Non-vacuity -/

omit [Fintype V] in
/-- An adversary injecting at most one packet per round (in the whole network) is `(1, 0)`-bounded. -/
lemma isBounded_of_le_one [Fintype V] {T : DTree V} {A : ℕ → V → V → ℕ}
    (hA : ∀ t, ∑ a, ∑ w, A t a w ≤ 1) : IsBounded T A 1 0 := by
  intro v s t hst
  have h1 : Cslib.AQT.seqCross (injAt T A v) s t ≤ t - s := by
    unfold Cslib.AQT.seqCross
    calc ∑ u ∈ Ico s t, injAt T A v u ≤ ∑ _u ∈ Ico s t, 1 :=
          sum_le_sum fun u _ => le_trans (sum_le_sum fun a _ => sum_le_sum fun w _ => by
            split_ifs <;> simp) (hA u)
      _ = t - s := by simp
  have h2 : (Cslib.AQT.seqCross (injAt T A v) s t : ℝ) ≤ ((t - s : ℕ) : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_sub hst] at h2
  linarith

/-- The two-node path `0 → 1`. -/
def path2 : DTree (Fin 2) where
  parent v := if v = 0 then some 1 else none
  depth v := 1 - v.val
  depth_parent := by decide

/-- One packet per round from the leaf `0` to the root `1`. -/
def adv2 : ℕ → Fin 2 → Fin 2 → ℕ := fun _ a w => if a = 0 ∧ w = 1 then 1 else 0

/-- Non-vacuity of Proposition B.3: one packet per round from `0` to the root `1` of the two-node
path is a `(1, 0)`-bounded adversary, and PTS keeps every buffer at most `2`. -/
example (t : ℕ) (v : Fin 2) :
    (occ (exec path2 {1} Fin.val adv2 t) v : ℝ) ≤ 2 := by
  have h := prop_B_3 (T := path2) (idx := Fin.val) (A := adv2) (r := 1)
    (isBounded_of_le_one (fun _ => by simp [adv2, Fin.sum_univ_two, filter_eq'])) le_rfl
    (fun t a w _ h => by unfold adv2 at h; split_ifs at h with h' <;> simp_all) t v
  linarith

end Podc.SmallBuffersAQT.Tree
