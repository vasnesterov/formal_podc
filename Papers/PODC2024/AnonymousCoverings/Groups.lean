import Mathlib

/-!
# Group solvability (Section 3) and renaming from group snapshots (Section 6)

Processors receive *group identifiers* as inputs (several processors may share one). A task is a
set of valid partial output assignments from group identifiers to outputs. An *output sample* of an
outcome maps each participating group to the output of one of its members; an outcome
*group-solves* a task if every output sample is valid (Definition 3.4).

* `snapTask`: the snapshot task on groups; `renTask f`: adaptive renaming with parameter `f`.
* `example_3_2`: the outcome of Section 3.2 (groups `A = {1}`, `B = {2, 3}`, `C = {4}`; outputs
  `{A,B,C}`, `{A,B}`, `{B,C}`, `{A,B,C}`) group-solves the snapshot task although processors 2
  and 3 return incomparable sets.
* `renaming_of_groupSnapshot` (**Section 6**): applying the Bar-Noy–Dolev naming rule
  `name = z(z−1)/2 + rank(g, S)` (`z = |S|`, `rank` = position of the own group in the output `S`)
  to an outcome that group-solves the snapshot task yields an outcome that group-solves adaptive
  renaming with `n(n+1)/2` names (`n` = number of participating groups).
* `groupSnapshot_of_chain`: pairwise comparable outputs that contain the own group and only
  participating groups group-solve the snapshot task (this is what the algorithm of Section 5
  provides).
-/

namespace Podc.AnonymousCoverings

open Finset

/-- The outcome of an execution in which every participating processor terminated: the set of
participants, their groups (inputs) and outputs. -/
structure Outcome (P G O : Type*) where
  /-- Participating processors. -/
  part : Finset P
  /-- Group (input) of each processor. -/
  grp : P → G
  /-- Output of each processor. -/
  out : P → O

/-- A task on group identifiers: the valid partial output assignments. -/
def GTask (G O : Type*) := (G → Option O) → Prop

variable {P G O : Type*} [DecidableEq G]

/-- Participating groups. -/
def Outcome.groups (x : Outcome P G O) : Finset G := x.part.image x.grp

/-- An output sample (Section 3.2.1): defined exactly on the participating groups, and each value
is the output of a member of the group. -/
def Outcome.IsSample (x : Outcome P G O) (s : G → Option O) : Prop :=
  (∀ g, (s g).isSome ↔ g ∈ x.groups) ∧
    ∀ g o, s g = some o → ∃ p ∈ x.part, x.grp p = g ∧ x.out p = o

/-- **Definition 3.4.** The outcome group-solves `T` if every output sample is valid. -/
def Outcome.GroupSolves (x : Outcome P G O) (T : GTask G O) : Prop :=
  ∀ s, x.IsSample s → T s

/-- **Snapshot task** on groups: each sampled output contains its group, consists of
participating groups, and sampled outputs are related by containment. -/
def snapTask : GTask G (Finset G) := fun s =>
  (∀ g S, s g = some S → g ∈ S ∧ ∀ h ∈ S, (s h).isSome) ∧
    ∀ g g' S S', s g = some S → s g' = some S' → S ⊆ S' ∨ S' ⊆ S

/-- **Adaptive renaming** with parameter `f` (Definition 3.3 for groups): sampled names are
distinct and lie in `1..f n`, where `n` is the number of participating groups. -/
def renTask [Fintype G] (f : ℕ → ℕ) : GTask G ℕ := fun s =>
  (∀ g m, s g = some m → 1 ≤ m ∧ m ≤ f (univ.filter fun h => (s h).isSome).card) ∧
    ∀ g g' m, s g = some m → s g' = some m → g = g'

/-- Rank of `g` in `S`: the number of elements of `S` that are `≤ g`. -/
def rank [LinearOrder G] (g : G) (S : Finset G) : ℕ := (S.filter (· ≤ g)).card

/-- The Bar-Noy–Dolev name: block `z(z−1)/2 + 1 .. z(z+1)/2` for snapshots of size `z`. -/
def bdName [LinearOrder G] (S : Finset G) (g : G) : ℕ := S.card * (S.card - 1) / 2 + rank g S

theorem tri_succ (z : ℕ) : (z + 1) * z / 2 = z * (z - 1) / 2 + z := by
  rcases z with _ | z
  · simp
  · simp only [Nat.add_sub_cancel]
    have : (z + 1 + 1) * (z + 1) = (z + 1) * z + 2 * (z + 1) := by ring
    rw [this, Nat.add_mul_div_left _ _ (by norm_num)]

theorem tri_mono {a b : ℕ} (h : a ≤ b) : a * (a - 1) / 2 ≤ b * (b - 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (by omega))

/-- Names from different blocks differ. -/
theorem block_inj {z z' r r' : ℕ} (hr : 1 ≤ r ∧ r ≤ z) (hr' : 1 ≤ r' ∧ r' ≤ z')
    (h : z * (z - 1) / 2 + r = z' * (z' - 1) / 2 + r') : z = z' ∧ r = r' := by
  have key : ∀ {a b ra rb : ℕ}, 1 ≤ ra ∧ ra ≤ a → 1 ≤ rb ∧ rb ≤ b → a < b →
      a * (a - 1) / 2 + ra < b * (b - 1) / 2 + rb := by
    intro a b ra rb ha hb hab
    have h1 := tri_succ a
    have h2 := tri_mono (show a + 1 ≤ b by omega)
    simp only [Nat.add_sub_cancel] at h2
    rw [mul_comm (a + 1) a] at h1
    have : a * (a + 1) / 2 = (a + 1) * a / 2 := by rw [mul_comm]
    omega
  rcases lt_trichotomy z z' with hlt | heq | hgt
  · exact absurd h (ne_of_lt (key hr hr' hlt))
  · subst heq; exact ⟨rfl, by omega⟩
  · exact absurd h (ne_of_gt (key hr' hr hgt))

omit [DecidableEq G] in
theorem rank_pos [LinearOrder G] {g : G} {S : Finset G} (hg : g ∈ S) : 1 ≤ rank g S :=
  card_pos.2 ⟨g, mem_filter.2 ⟨hg, le_rfl⟩⟩

omit [DecidableEq G] in
theorem rank_le [LinearOrder G] (g : G) (S : Finset G) : rank g S ≤ S.card :=
  card_filter_le _ _

theorem rank_injOn [LinearOrder G] {g g' : G} {S : Finset G} (hg : g ∈ S) (hg' : g' ∈ S)
    (h : rank g S = rank g' S) : g = g' := by
  by_contra hne
  wlog hlt : g < g' generalizing g g'
  · exact this hg' hg h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have hsub : S.filter (· ≤ g) ⊂ S.filter (· ≤ g') := by
    refine ⟨fun x hx => ?_, fun hsub => ?_⟩
    · simp only [mem_filter] at hx ⊢; exact ⟨hx.1, hx.2.trans hlt.le⟩
    · have := hsub (mem_filter.2 ⟨hg', le_rfl⟩)
      simp only [mem_filter] at this
      exact absurd this.2 (not_le.2 hlt)
  exact absurd h (ne_of_lt (card_lt_card hsub))

/-- **Section 6 (renaming from a group solution of snapshot).** If an outcome group-solves the
snapshot task, the Bar-Noy–Dolev names group-solve adaptive renaming with `n(n+1)/2` names. -/
theorem renaming_of_groupSnapshot [Fintype G] [LinearOrder G] (x : Outcome P G (Finset G))
    (hx : x.GroupSolves snapTask) :
    (⟨x.part, x.grp, fun p => bdName (x.out p) (x.grp p)⟩ : Outcome P G ℕ).GroupSolves
      (renTask fun n => n * (n + 1) / 2) := by
  classical
  intro s ⟨hdom, hrep⟩
  have hex : ∀ g, (s g).isSome → ∃ p ∈ x.part, x.grp p = g ∧ s g = some (bdName (x.out p) g) := by
    intro g hg
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hg
    obtain ⟨p, hp, hpg, hpm⟩ := hrep g m hm
    simp only at hp hpg hpm
    subst hpg
    exact ⟨p, hp, rfl, by rw [hm, ← hpm]⟩
  choose rep hrep1 hrep2 hrep3 using hex
  let s₀ : G → Option (Finset G) := fun g => if h : (s g).isSome then some (x.out (rep g h)) else none
  have hs₀ : x.IsSample s₀ := by
    refine ⟨fun g => ?_, fun g S hS => ?_⟩
    · refine Iff.trans ?_ (hdom g)
      by_cases h : (s g).isSome <;> simp [s₀, h]
    · by_cases h : (s g).isSome
      · simp only [s₀, h, dite_true, Option.some.injEq] at hS
        exact ⟨rep g h, hrep1 g h, hrep2 g h, hS⟩
      · simp [s₀, h] at hS
  obtain ⟨hsnap1, hsnap2⟩ := hx s₀ hs₀
  have hget : ∀ g m, s g = some m → ∃ h : (s g).isSome,
      m = bdName (x.out (rep g h)) g ∧ s₀ g = some (x.out (rep g h)) := by
    intro g m hm
    have h : (s g).isSome := by simp [hm]
    refine ⟨h, ?_, by simp [s₀, h]⟩
    have := hrep3 g h
    rw [hm] at this
    exact Option.some.inj this
  refine ⟨fun g m hm => ?_, fun g g' m hm hm' => ?_⟩
  · obtain ⟨h, rfl, hS⟩ := hget g m hm
    obtain ⟨hgS, hdomS⟩ := hsnap1 g _ hS
    set S := x.out (rep g h)
    have hz : S.card ≤ (univ.filter fun h => (s h).isSome).card := by
      refine card_le_card fun h' hh' => ?_
      have := hdomS h' hh'
      by_cases hs : (s h').isSome
      · simp [hs]
      · simp [s₀, hs] at this
    have h1 := rank_pos hgS
    have h2 := rank_le g S
    have h3 := tri_succ S.card
    set n := (univ.filter fun h => (s h).isSome).card
    have h4 : (S.card + 1) * S.card / 2 ≤ n * (n + 1) / 2 := by
      rw [mul_comm n]
      exact Nat.div_le_div_right (Nat.mul_le_mul (Nat.add_le_add_right hz 1) hz)
    refine ⟨by unfold bdName; omega, ?_⟩
    unfold bdName; beta_reduce; omega
  · obtain ⟨h, hmS, hS⟩ := hget g m hm
    obtain ⟨h', hmS', hS'⟩ := hget g' m hm'
    set S := x.out (rep g h)
    set S' := x.out (rep g' h')
    have hgS := (hsnap1 g _ hS).1
    have hgS' := (hsnap1 g' _ hS').1
    obtain ⟨hc, hr⟩ := block_inj ⟨rank_pos hgS, rank_le g S⟩ ⟨rank_pos hgS', rank_le g' S'⟩
      (by unfold bdName at hmS hmS'; rw [← hmS, ← hmS'])
    have hSS : S = S' := by
      rcases hsnap2 g g' _ _ hS hS' with hsub | hsub
      · exact eq_of_subset_of_card_le hsub hc.ge
      · exact (eq_of_subset_of_card_le hsub hc.le).symm
    rw [← hSS] at hr hgS'
    exact rank_injOn hgS hgS' hr

/-- Pairwise comparable outputs that contain the own group and only participating groups
group-solve the snapshot task (the algorithm of Section 5 provides this stronger guarantee). -/
theorem groupSnapshot_of_chain (x : Outcome P G (Finset G))
    (hown : ∀ p ∈ x.part, x.grp p ∈ x.out p) (hpart : ∀ p ∈ x.part, x.out p ⊆ x.groups)
    (hchain : ∀ p ∈ x.part, ∀ q ∈ x.part, x.out p ⊆ x.out q ∨ x.out q ⊆ x.out p) :
    x.GroupSolves snapTask := by
  intro s ⟨hdom, hrep⟩
  refine ⟨fun g S hS => ?_, fun g g' S S' hS hS' => ?_⟩
  · obtain ⟨p, hp, rfl, rfl⟩ := hrep g S hS
    exact ⟨hown p hp, fun h hh => (hdom h).2 (hpart p hp hh)⟩
  · obtain ⟨p, hp, -, rfl⟩ := hrep g S hS
    obtain ⟨q, hq, -, rfl⟩ := hrep g' S' hS'
    exact hchain p hp q hq

/-- The outcome of the example in Section 3.2: processors `0,1,2,3` (the paper's 1–4) in groups
`A = 0`, `B = 1`, `C = 2`, with outputs `{A,B,C}`, `{A,B}`, `{B,C}`, `{A,B,C}`. -/
def example32 : Outcome (Fin 4) (Fin 3) (Finset (Fin 3)) :=
  ⟨univ, ![0, 1, 1, 2], ![{0, 1, 2}, {0, 1}, {1, 2}, {0, 1, 2}]⟩

/-- **Section 3.2 example.** The outcome group-solves the snapshot task, although the two members
of group `B` return incomparable sets. -/
theorem example_3_2 : example32.GroupSolves snapTask ∧
    ¬ (example32.out 1 ⊆ example32.out 2 ∨ example32.out 2 ⊆ example32.out 1) := by
  refine ⟨fun s ⟨hdom, hrep⟩ => ⟨fun g S hS => ?_, fun g g' S S' hS hS' => ?_⟩, by decide⟩
  · obtain ⟨p, -, rfl, rfl⟩ := hrep g S hS
    refine ⟨by fin_cases p <;> decide, fun h hh => (hdom h).2 ?_⟩
    have : example32.groups = univ := by decide
    rw [this]; exact mem_univ h
  · obtain ⟨p, -, hp, rfl⟩ := hrep g S hS
    obtain ⟨q, -, hq, rfl⟩ := hrep g' S' hS'
    -- two members of the same group never both appear; group `B` is sampled once
    by_cases hpq : example32.grp p = example32.grp q
    · have : g = g' := hp.symm.trans (hpq.trans hq)
      subst this
      rw [hS] at hS'
      obtain ⟨p', -, -, h1⟩ := hrep g _ hS
      have h2 : example32.out p = example32.out q := Option.some.inj hS'
      rw [h2]; exact Or.inl subset_rfl
    · fin_cases p <;> fin_cases q <;> simp_all (config := {decide := true}) [example32]

end Podc.AnonymousCoverings
