import Papers.PODC2016.ConcurrentDSU.Defs

/-!
# Parent-pointer forests ordered by node ids

A parent function `m : E → E` is `Good` (w.r.t. the node ids `key`) if every node is a root
(`m a = a`) or has a parent of larger id (Lemma 3.1: "if x is not a root, x < x.parent; if x is
a root, x = x.parent"). Then following parents always reaches a root: `rootOf m a` (iterate
`card E` times). Two nodes are in the same tree (`same m a b`) iff they have the same root.

The two kinds of successful `Cas` of the algorithm:
* `rootOf_update_split` — a `Find` replaces the parent of `u` by a node `w` of the same tree with
  larger id: roots are unchanged;
* `rootOf_update_link` — `Unite` makes the root `u` a child of a node `v` with larger id: the
  tree of `u` is attached to the tree of `v`.

`Legal m m'` collects what every memory change of the algorithm satisfies (used to show that
local invariants of the other processes are stable).
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentDSU

variable {E : Type} [Fintype E] [DecidableEq E] (key : E → ℕ)

-- CSLib candidate (this file: parent-pointer forests ordered by ids)
/-- Lemma 3.1 (shape): every node is a root or its parent has a larger id. -/
def Good (m : E → E) : Prop := ∀ a, m a = a ∨ key a < key (m a)

/-- The root of the tree of `a` (follow parent pointers `card E` times). -/
def rootOf (m : E → E) (a : E) : E := m^[Fintype.card E] a

/-- `a` and `b` are in the same tree. -/
def same (m : E → E) (a b : E) : Prop := rootOf m a = rootOf m b

/-- Number of nodes with a larger id than `a` (a measure decreasing along parent pointers). -/
def hgt (a : E) : ℕ := (Finset.univ.filter (fun b => key a < key b)).card

variable {key}

lemma hgt_lt {a b : E} (h : key a < key b) : hgt key b < hgt key a := by
  unfold hgt
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨b, by simp [h], by simp⟩
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  omega

lemma hgt_le_card (a : E) : hgt key a ≤ Fintype.card E := by
  unfold hgt
  exact (Finset.card_filter_le _ _).trans (by simp)

section Iter

variable {m : E → E}

lemma iterate_fixed {r : E} (hr : m r = r) (j : ℕ) : m^[j] r = r := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, hr]

lemma key_le_iterate (hg : Good key m) (a : E) (j : ℕ) : key a ≤ key (m^[j] a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases hg (m^[j] a) with h | h
    · rw [h]; exact ih
    · omega

/-- Before the root is reached, ids strictly increase along the path. -/
lemma key_lt_iterate (hg : Good key m) (a : E) (N : ℕ) (hN : m (m^[N] a) ≠ m^[N] a) :
    ∀ i j, i < j → j ≤ N + 1 → key (m^[i] a) < key (m^[j] a) := by
  have hnf : ∀ i ≤ N, m (m^[i] a) ≠ m^[i] a := by
    intro i hi hfix
    apply hN
    have : m^[N] a = m^[N - i] (m^[i] a) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [this, iterate_fixed hfix, hfix]
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h1 : key (m^[j] a) < key (m (m^[j] a)) := by
      rcases hg (m^[j] a) with h | h
      · exact absurd h (hnf j (by omega))
      · exact h
    rcases Nat.lt_or_ge i j with h | h
    · exact (ih h (by omega)).trans h1
    · have : i = j := by omega
      subst this; exact h1

/-- After `card E` steps a root is reached. -/
lemma rootOf_fixed (hg : Good key m) (a : E) : m (rootOf m a) = rootOf m a := by
  by_contra hN
  have hlt := key_lt_iterate hg a (Fintype.card E) hN
  let f : Fin (Fintype.card E + 1) → E := fun i => m^[i.1] a
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f] at hij
    rcases lt_trichotomy i.1 j.1 with h | h | h
    · have := hlt i.1 j.1 h (by omega); rw [hij] at this; omega
    · exact Fin.ext h
    · have := hlt j.1 i.1 h (by omega); rw [hij] at this; omega
  have := Fintype.card_le_of_injective f hf
  simp at this

lemma rootOf_of_fixed {a : E} (ha : m a = a) : rootOf m a = a := iterate_fixed ha _

lemma rootOf_eq_of_iterate (hg : Good key m) {a r : E} {j : ℕ} (hj : m^[j] a = r)
    (hr : m r = r) : rootOf m a = r := by
  unfold rootOf
  rcases Nat.le_total j (Fintype.card E) with h | h
  · have : m^[Fintype.card E] a = m^[Fintype.card E - j] (m^[j] a) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    rw [this, hj, iterate_fixed hr]
  · have : m^[j] a = m^[j - Fintype.card E] (m^[Fintype.card E] a) := by
      rw [← Function.iterate_add_apply]; congr 1; omega
    have hf := rootOf_fixed hg a
    unfold rootOf at hf
    rw [this, iterate_fixed hf] at hj
    exact hj

lemma rootOf_apply (hg : Good key m) (a : E) : rootOf m (m a) = rootOf m a := by
  apply rootOf_eq_of_iterate hg (j := Fintype.card E) _ (rootOf_fixed hg a)
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  exact rootOf_fixed hg a

lemma rootOf_rootOf (hg : Good key m) (a : E) : rootOf m (rootOf m a) = rootOf m a :=
  rootOf_of_fixed (rootOf_fixed hg a)

lemma key_le_rootOf (hg : Good key m) (a : E) : key a ≤ key (rootOf m a) :=
  key_le_iterate hg a _

lemma key_lt_rootOf (hg : Good key m) {a : E} (ha : m a ≠ a) : key a < key (rootOf m a) := by
  rcases hg a with h | h
  · exact absurd h ha
  · rw [← rootOf_apply hg a]; exact lt_of_lt_of_le h (key_le_rootOf hg _)

lemma rootOf_eq_self_iff (hg : Good key m) {a : E} : rootOf m a = a ↔ m a = a := by
  constructor
  · intro h; have := rootOf_fixed hg a; rwa [h] at this
  · exact rootOf_of_fixed

lemma same_apply (hg : Good key m) (a : E) : same m (m a) a := rootOf_apply hg a

lemma same_root (hg : Good key m) (a : E) : same m (rootOf m a) a := rootOf_rootOf hg a

/-- Strong induction along increasing ids. -/
lemma induction_key {Q : E → Prop} (h : ∀ a, (∀ b, key a < key b → Q b) → Q a) (a : E) : Q a := by
  induction hn : hgt key a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    apply h
    intro b hb
    exact ih _ (hn ▸ hgt_lt hb) b rfl

end Iter

/-! ### The two kinds of successful `Cas` -/

section Updates

variable {m : E → E}

lemma good_update (hg : Good key m) {u w : E} (hk : key u < key w) :
    Good key (Function.update m u w) := by
  intro a
  by_cases ha : a = u
  · subst ha; right; simpa using hk
  · simp only [Function.update_of_ne ha]; exact hg a

/-- A `Find` changes the parent of `u` to a node `w` of the same tree with a larger id: all roots
stay the same. -/
lemma rootOf_update_split (hg : Good key m) {u w : E} (hk : key u < key w)
    (hw : rootOf m w = rootOf m u) (a : E) :
    rootOf (Function.update m u w) a = rootOf m a := by
  have hg' := good_update hg hk
  induction a using induction_key (key := key) with
  | _ a ih =>
    by_cases ha : a = u
    · subst ha
      rw [← rootOf_apply hg', Function.update_self, ih w hk, hw]
    · by_cases hf : m a = a
      · rw [rootOf_of_fixed hf, rootOf_of_fixed (by rwa [Function.update_of_ne ha])]
      · have hk' : key a < key (m a) := (hg a).resolve_left hf
        rw [← rootOf_apply hg', Function.update_of_ne ha, ih _ hk', rootOf_apply hg]

/-- `Unite` makes the root `u` a child of `v` (with a larger id): the nodes of the tree of `u`
get the root of `v`. -/
lemma rootOf_update_link (hg : Good key m) {u v : E} (hu : m u = u) (hk : key u < key v)
    (a : E) :
    rootOf (Function.update m u v) a = if rootOf m a = u then rootOf m v else rootOf m a := by
  have hg' := good_update hg hk
  have hv : rootOf m v ≠ u := by
    intro h; have := key_le_rootOf hg v; rw [h] at this; omega
  induction a using induction_key (key := key) with
  | _ a ih =>
    by_cases ha : a = u
    · subst ha
      rw [← rootOf_apply hg', Function.update_self, ih v hk, rootOf_of_fixed hu]
      simp [hv]
    · by_cases hf : m a = a
      · rw [rootOf_of_fixed hf, rootOf_of_fixed (by rwa [Function.update_of_ne ha])]
        simp [ha]
      · have hk' : key a < key (m a) := (hg a).resolve_left hf
        rw [← rootOf_apply hg', Function.update_of_ne ha, ih _ hk', rootOf_apply hg]

/-- After linking the root `u` (the root of `x`) below `v` (in the tree of `y`), "same tree" is
the old relation with the classes of `x` and `y` merged. -/
lemma same_update_link (hg : Good key m) {u v x y : E} (hu : m u = u) (hk : key u < key v)
    (hx : same m u x) (hy : same m v y) (a b : E) :
    same (Function.update m u v) a b ↔ joinRel (same m) x y a b := by
  unfold same joinRel
  rw [rootOf_update_link hg hu hk, rootOf_update_link hg hu hk]
  beta_reduce
  have hxu : rootOf m x = u := by unfold same at hx; rw [← hx, rootOf_of_fixed hu]
  have hyv : rootOf m y = rootOf m v := hy.symm
  have hv : rootOf m v ≠ u := by
    intro h; have := key_le_rootOf hg v; rw [h] at this; omega
  rw [hxu, hyv]
  by_cases ha : rootOf m a = u <;> by_cases hb : rootOf m b = u <;> simp only [ha, hb, ite_true,
    ite_false] <;> grind

end Updates

/-! ### Legal memory changes -/

/-- What every memory change of the algorithm satisfies: the result is `Good`, trees only merge,
non-roots stay non-roots, and parents only move to larger ids. -/
structure Legal (key : E → ℕ) (m m' : E → E) : Prop where
  good : Good key m'
  sameMono : ∀ a b, same m a b → same m' a b
  root : ∀ a, m' a = a → m a = a
  mono : ∀ a, m' a = m a ∨ key (m a) < key (m' a)

lemma Legal.refl {m : E → E} (hg : Good key m) : Legal key m m :=
  ⟨hg, fun _ _ h => h, fun _ h => h, fun _ => Or.inl rfl⟩

lemma Legal.split {m : E → E} (hg : Good key m) {u v w : E} (hmu : m u = v) (hk : key v < key w)
    (hku : key u < key w) (hw : rootOf m w = rootOf m v) :
    Legal key m (Function.update m u w) where
  good := good_update hg hku
  sameMono a b h := by
    unfold same at *
    rw [rootOf_update_split hg hku (by rw [hw, ← hmu, rootOf_apply hg]),
      rootOf_update_split hg hku (by rw [hw, ← hmu, rootOf_apply hg])]
    exact h
  root a h := by
    by_cases ha : a = u
    · subst ha; simp only [Function.update_self] at h; rw [h] at hku; omega
    · rwa [Function.update_of_ne ha] at h
  mono a := by
    by_cases ha : a = u
    · subst ha; right; simp only [Function.update_self, hmu]; exact hk
    · left; simp [Function.update_of_ne ha]

lemma Legal.link {m : E → E} (hg : Good key m) {u v : E} (hu : m u = u) (hk : key u < key v) :
    Legal key m (Function.update m u v) where
  good := good_update hg hk
  sameMono a b h := by
    unfold same at *
    rw [rootOf_update_link hg hu hk, rootOf_update_link hg hu hk, h]
  root a h := by
    by_cases ha : a = u
    · subst ha; simp only [Function.update_self] at h; rw [h] at hk; omega
    · rwa [Function.update_of_ne ha] at h
  mono a := by
    by_cases ha : a = u
    · subst ha; right; simp only [Function.update_self, hu]; exact hk
    · left; simp [Function.update_of_ne ha]

lemma Legal.nonroot {m m' : E → E} (h : Legal key m m') {a : E} (ha : m a ≠ a) : m' a ≠ a :=
  fun h' => ha (h.root a h')

/-- The memory potential: decreases with every change of a parent pointer. -/
def mpot (key : E → ℕ) (m : E → E) : ℕ := ∑ a, hgt key (m a)

lemma mpot_lt {m m' : E → E} (h : Legal key m m') (hne : m' ≠ m) : mpot key m' < mpot key m := by
  unfold mpot
  obtain ⟨a, ha⟩ : ∃ a, m' a ≠ m a := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  apply Finset.sum_lt_sum
  · intro b _
    rcases h.mono b with hb | hb
    · rw [hb]
    · exact (hgt_lt hb).le
  · refine ⟨a, Finset.mem_univ _, ?_⟩
    rcases h.mono a with hb | hb
    · exact absurd hb ha
    · exact hgt_lt hb

lemma mpot_le {m m' : E → E} (h : Legal key m m') : mpot key m' ≤ mpot key m := by
  by_cases hne : m' = m
  · rw [hne]
  · exact (mpot_lt h hne).le

end Podc.ConcurrentDSU
