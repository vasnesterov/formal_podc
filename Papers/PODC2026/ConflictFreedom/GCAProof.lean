import Papers.PODC2026.ConflictFreedom.GCA

/-!
# Correctness of Algorithm 2 (Theorem 5.1)

Kuznetsov, Sutra and Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026,
Section 5 and Appendix A.4.

We prove that every reachable state of Algorithm 2 (`GCA.Reach`) satisfies the six properties of
generalized commit-adopt (`GCA.IsGCA`), and that the algorithm is wait-free.

The proof goes through an inductive invariant `GCA.Inv` (the snapshot objects contain exactly what
the participants wrote; the views are sub-views of the objects and pairwise comparable, as
snapshots of one-shot single-writer arrays are), from which each property follows by order theory
in the `GCADomain`. The paper's proofs of Adoption and Commitment contain wrong steps; the
arguments below are different (see the docstrings of `adoption_of_reach` and
`commitment_of_reach`).
-/

namespace Podc.ConflictFreedom

namespace GCA

open Classical

variable {n : ℕ} {T : Type*} [GCADomain T]

/-! ### Views -/

/-- Pointwise inclusion of views (`v ⊆ w`: every non-`⊥` entry of `v` is an entry of `w`). -/
def Sub {V : Type*} (v w : Fin n → Option V) : Prop := ∀ k x, v k = some x → w k = some x

theorem Sub.refl {V : Type*} (v : Fin n → Option V) : Sub v v := fun _ _ h => h

theorem Sub.trans {V : Type*} {u v w : Fin n → Option V} (h₁ : Sub u v) (h₂ : Sub v w) :
    Sub u w := fun k x h => h₂ k x (h₁ k x h)

theorem mem_vals {V : Type*} {v : Fin n → Option V} {x : V} : x ∈ vals v ↔ ∃ k, v k = some x := by
  simp [vals]

theorem vals_mono {V : Type*} {v w : Fin n → Option V} (h : Sub v w) : vals v ⊆ vals w := by
  intro x hx
  obtain ⟨k, hk⟩ := mem_vals.1 hx
  exact mem_vals.2 ⟨k, h k x hk⟩

/-- The number of non-`⊥` entries of a view. -/
noncomputable def sz {V : Type*} (v : Fin n → Option V) : ℕ :=
  (Finset.univ.filter fun k => (v k).isSome).card

theorem Sub.support_subset {V : Type*} {v w : Fin n → Option V} (h : Sub v w) :
    (Finset.univ.filter fun k => (v k).isSome) ⊆ (Finset.univ.filter fun k => (w k).isSome) := by
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
  simp [h k x hx]

theorem Sub.antisymm_of_sz {V : Type*} {v w : Fin n → Option V} (h : Sub v w)
    (hs : sz w ≤ sz v) : Sub w v := by
  have heq := Finset.eq_of_subset_of_card_le h.support_subset hs
  intro k x hx
  have hk : k ∈ (Finset.univ.filter fun k => (v k).isSome) := by rw [heq]; simp [hx]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
  rw [h k y hy] at hx
  rw [hy, hx]

theorem Sub.sz_lt {V : Type*} {v w : Fin n → Option V} (h : Sub v w) {k : Fin n}
    (hv : v k = none) (hw : (w k).isSome) : sz v < sz w :=
  Finset.card_lt_card ((Finset.ssubset_iff_of_subset h.support_subset).2
    ⟨k, by simp [hw], by simp [hv]⟩)

/-! ### Order theory of `co`, `candidate` and `beta` -/

theorem compat_pair_comm {x y : T} : Compat ({x, y} : Set T) ↔ Compat ({y, x} : Set T) := by
  rw [Set.pair_comm]

theorem compat_pair_of_le {x y z : T} (hx : x ≤ z) (hy : y ≤ z) : Compat ({x, y} : Set T) :=
  ⟨z, by simp [hx, hy]⟩

theorem compat_pair_self (x : T) : Compat ({x, x} : Set T) := compat_pair_of_le le_rfl le_rfl

theorem coEntry_le_self (v : Fin n → Option T) (a : T) : coEntry v a ≤ a :=
  Finset.inf'_le _ (Finset.mem_insert_self _ _)

theorem coEntry_le_of_not_compat {v : Fin n → Option T} {a b : T} (hb : b ∈ vals v)
    (hab : ¬ Compat ({a, b} : Set T)) : coEntry v a ≤ b :=
  Finset.inf'_le _ (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hb, hab⟩))

theorem le_coEntry {v : Fin n → Option T} {a x : T} (ha : x ≤ a) (hv : ∀ b ∈ vals v, x ≤ b) :
    x ≤ coEntry v a := by
  refine Finset.le_inf' _ _ fun b hb => ?_
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact ha
  · exact hv b (Finset.mem_filter.1 hb).1

theorem coEntry_eq_self {v : Fin n → Option T} {a : T} (h : ∀ b ∈ vals v, Compat ({a, b} : Set T)) :
    coEntry v a = a := by
  refine le_antisymm (coEntry_le_self v a) (Finset.le_inf' _ _ fun b hb => ?_)
  rcases Finset.mem_insert.1 hb with rfl | hb
  · exact le_rfl
  · exact absurd (h b (Finset.mem_filter.1 hb).1) (Finset.mem_filter.1 hb).2

theorem mem_vals_co {v : Fin n → Option T} {x : T} :
    x ∈ vals (co v) ↔ ∃ k a, v k = some a ∧ x = coEntry v a := by
  rw [mem_vals]
  constructor
  · rintro ⟨k, hk⟩
    simp only [co, Option.map_eq_some_iff] at hk
    obtain ⟨a, ha, rfl⟩ := hk
    exact ⟨k, a, ha, rfl⟩
  · rintro ⟨k, a, ha, rfl⟩
    exact ⟨k, by simp [co, ha]⟩

/-- The key compatibility fact (cf. Lemma A.4): for views `v ⊆ w`, every entry of `v^co` is
compatible with every entry of `w^co`. -/
theorem compat_co_co {v w : Fin n → Option T} (hvw : Sub v w) {x y : T} (hx : x ∈ vals (co v))
    (hy : y ∈ vals (co w)) : Compat ({x, y} : Set T) := by
  obtain ⟨k, a, ha, rfl⟩ := mem_vals_co.1 hx
  obtain ⟨l, b, hb, rfl⟩ := mem_vals_co.1 hy
  by_cases hab : Compat ({a, b} : Set T)
  · obtain ⟨z, hz⟩ := hab
    exact compat_pair_of_le ((coEntry_le_self v a).trans (hz a (by simp)))
      ((coEntry_le_self w b).trans (hz b (by simp)))
  · have haw : a ∈ vals w := vals_mono hvw (mem_vals.2 ⟨k, ha⟩)
    exact compat_pair_of_le (coEntry_le_self v a)
      (coEntry_le_of_not_compat haw (fun h => hab (compat_pair_comm.1 h)))

/-- `A_i^co` contains only compatible traces (Section 5). -/
theorem compat_vals_co (v : Fin n → Option T) : Compat ((vals (co v) : Finset T) : Set T) :=
  GCADomain.compat_of_pairwise _ fun _ hx _ hy => compat_co_co (Sub.refl v) hx hy

theorem isLUB_candidate (v : Fin n → Option T) :
    IsLUB ((vals (co v) : Finset T) : Set T) (candidate v) :=
  GCADomain.isLUB_lub _ (compat_vals_co v)

theorem le_candidate {v : Fin n → Option T} {x : T} (hx : x ∈ vals (co v)) : x ≤ candidate v :=
  (isLUB_candidate v).1 hx

theorem co_eq_self {v : Fin n → Option T}
    (h : ∀ a ∈ vals v, ∀ b ∈ vals v, Compat ({a, b} : Set T)) : co v = v := by
  funext k
  cases hk : v k with
  | none => simp [co, hk]
  | some a => simp [co, hk, coEntry_eq_self (h a (mem_vals.2 ⟨k, hk⟩))]

theorem compatFlag_eq_true {v : Fin n → Option T} : compatFlag v = true ↔ co v = v := by
  simp [compatFlag]

theorem le_candidate_of_co_eq {v : Fin n → Option T} (hv : co v = v) {a : T} (ha : a ∈ vals v) :
    a ≤ candidate v :=
  le_candidate (by rwa [hv])

/-- Monotonicity of the candidate on compatible views. -/
theorem candidate_mono {v w : Fin n → Option T} (hv : co v = v) (hw : co w = w) (hvw : Sub v w) :
    candidate v ≤ candidate w := by
  refine (isLUB_candidate v).2 fun x hx => ?_
  rw [Finset.mem_coe, hv] at hx
  exact le_candidate_of_co_eq hw (vals_mono hvw hx)

/-- Candidates of comparable views are compatible (Lemma A.4). -/
theorem candidate_compat {v w : Fin n → Option T} (hvw : Sub v w) :
    Compat ({candidate v, candidate w} : Set T) := by
  obtain ⟨z, hz⟩ := GCADomain.compat_of_pairwise (vals (co v) ∪ vals (co w)) (by
    intro x hx y hy
    rcases Finset.mem_union.1 hx with hx | hx <;> rcases Finset.mem_union.1 hy with hy | hy
    · exact compat_co_co (Sub.refl v) hx hy
    · exact compat_co_co hvw hx hy
    · exact compat_pair_comm.1 (compat_co_co hvw hy hx)
    · exact compat_co_co (Sub.refl w) hx hy)
  refine compat_pair_of_le ((isLUB_candidate v).2 fun x hx => hz x ?_)
    ((isLUB_candidate w).2 fun x hx => hz x ?_)
  · simp [Finset.mem_coe.1 hx]
  · simp [Finset.mem_coe.1 hx]

/-- A view whose non-`⊥` entries all equal `s` (and which has one) is compatible, with candidate
`s`. -/
theorem co_candidate_const {v : Fin n → Option T} {s : T} (h : ∀ k a, v k = some a → a = s)
    {k₀ : Fin n} (hk₀ : v k₀ = some s) : co v = v ∧ candidate v = s := by
  have hco : co v = v := co_eq_self fun a ha b hb => by
    obtain ⟨k, hk⟩ := mem_vals.1 ha
    obtain ⟨l, hl⟩ := mem_vals.1 hb
    rw [h k a hk, h l b hl]
    exact compat_pair_self s
  refine ⟨hco, le_antisymm ((isLUB_candidate v).2 fun x hx => ?_) ?_⟩
  · rw [Finset.mem_coe, hco] at hx
    obtain ⟨k, hk⟩ := mem_vals.1 hx
    exact (h k x hk).le
  · exact le_candidate_of_co_eq hco (mem_vals.2 ⟨k₀, hk₀⟩)

omit [GCADomain T] in
theorem mem_flagged {w : Fin n → Option (T × Bool)} {b : T} :
    b ∈ flagged w ↔ ∃ k, w k = some (b, true) := by
  simp only [flagged, Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine exists_congr fun k => ?_
  rcases w k with _ | ⟨b', _ | _⟩ <;> simp [eq_comm]

theorem beta_le {own : T} {w : Fin n → Option (T × Bool)} {b : T} (hb : b ∈ flagged w) :
    beta own w ≤ b := by
  rw [beta]
  split_ifs with h
  · exact Finset.inf'_le _ hb
  · exact absurd ⟨b, hb⟩ h

theorem le_beta {own x : T} {w : Fin n → Option (T × Bool)} (hf : ∀ b ∈ flagged w, x ≤ b)
    (ho : ¬ (flagged w).Nonempty → x ≤ own) : x ≤ beta own w := by
  rw [beta]
  split_ifs with h
  · exact Finset.le_inf' _ _ hf
  · exact ho h

/-! ### The steps of Algorithm 2 -/

theorem step_eq_zero {g : State n T} {i : Fin n} {l : Loc n T} (h : l.pc = 0) :
    g.step i l = ⟨Function.update g.A i (some l.inp), g.B,
      Function.update g.loc i (some { l with pc := 1 })⟩ := by
  simp [State.step, stepLoc, h]

theorem step_eq_one {g : State n T} {i : Fin n} {l : Loc n T} (h : l.pc = 1) :
    g.step i l = ⟨g.A, g.B, Function.update g.loc i (some { l with pc := 2, av := g.A })⟩ := by
  simp [State.step, stepLoc, h]

theorem step_eq_two {g : State n T} {i : Fin n} {l : Loc n T} (h : l.pc = 2) :
    g.step i l = ⟨g.A, Function.update g.B i (some (candidate l.av, compatFlag l.av)),
      Function.update g.loc i (some { l with pc := 3 })⟩ := by
  simp [State.step, stepLoc, h]

theorem step_eq_three {g : State n T} {i : Fin n} {l : Loc n T} (h : l.pc = 3) :
    g.step i l = ⟨g.A, g.B, Function.update g.loc i (some { l with pc := 4, bv := g.B })⟩ := by
  simp [State.step, stepLoc, h]

/-! ### The inductive invariant -/

/-- The inductive invariant of Algorithm 2: the snapshot objects contain exactly what the
participants wrote, the views are sub-views of the objects containing the own entry, and any
two views of the same object are comparable (snapshots of one-shot single-writer arrays). -/
structure Inv (g : State n T) : Prop where
  A_none : ∀ k, g.loc k = none → g.A k = none
  B_none : ∀ k, g.loc k = none → g.B k = none
  pc_le : ∀ k l, g.loc k = some l → l.pc ≤ 4
  A_eq : ∀ k l, g.loc k = some l → g.A k = if 1 ≤ l.pc then some l.inp else none
  B_eq : ∀ k l, g.loc k = some l →
    g.B k = if 3 ≤ l.pc then some (candidate l.av, compatFlag l.av) else none
  av_sub : ∀ k l, g.loc k = some l → 2 ≤ l.pc → Sub l.av g.A
  av_self : ∀ k l, g.loc k = some l → 2 ≤ l.pc → l.av k = some l.inp
  bv_sub : ∀ k l, g.loc k = some l → 4 ≤ l.pc → Sub l.bv g.B
  bv_self : ∀ k l, g.loc k = some l → 4 ≤ l.pc → (l.bv k).isSome
  av_cmp : ∀ k l k' l', g.loc k = some l → g.loc k' = some l' → 2 ≤ l.pc → 2 ≤ l'.pc →
    Sub l.av l'.av ∨ Sub l'.av l.av
  bv_cmp : ∀ k l k' l', g.loc k = some l → g.loc k' = some l' → 4 ≤ l.pc → 4 ≤ l'.pc →
    Sub l.bv l'.bv ∨ Sub l'.bv l.bv

omit [GCADomain T] in
theorem upd_some {loc : Fin n → Option (Loc n T)} {i k : Fin n} {l' m : Loc n T}
    (h : Function.update loc i (some l') k = some m) :
    (k = i ∧ m = l') ∨ (k ≠ i ∧ loc k = some m) := by
  by_cases hk : k = i
  · subst hk
    simp only [Function.update_self, Option.some.injEq] at h
    exact Or.inl ⟨rfl, h.symm⟩
  · rw [Function.update_of_ne hk] at h
    exact Or.inr ⟨hk, h⟩

omit [GCADomain T] in
theorem upd_none {loc : Fin n → Option (Loc n T)} {i k : Fin n} {l' : Loc n T}
    (h : Function.update loc i (some l') k = none) : k ≠ i ∧ loc k = none := by
  by_cases hk : k = i
  · subst hk
    simp at h
  · rw [Function.update_of_ne hk] at h
    exact ⟨hk, h⟩

/-- Writing a fresh entry preserves sub-views. -/
theorem Sub.update {V : Type*} {v w : Fin n → Option V} (h : Sub v w) {i : Fin n}
    (hi : w i = none) (x : V) : Sub v (Function.update w i (some x)) := by
  intro k y hk
  have := h k y hk
  by_cases hki : k = i
  · subst hki
    rw [hi] at this
    exact absurd this (by simp)
  · rwa [Function.update_of_ne hki]

theorem inv_init : Inv (State.init : State n T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.init]

theorem Inv.invoke {g : State n T} (hI : Inv g) {i : Fin n} (s : T) (hi : g.loc i = none) :
    Inv { g with loc := Function.update g.loc i (some (Loc.init s)) } := by
  constructor
  · intro k hk
    exact hI.A_none k (upd_none hk).2
  · intro k hk
    exact hI.B_none k (upd_none hk).2
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init]
    · exact hI.pc_le k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init, hI.A_none _ hi]
    · exact hI.A_eq k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init, hI.B_none _ hi]
    · exact hI.B_eq k m hk
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init] at h2
    · exact hI.av_sub k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init] at h2
    · exact hI.av_self k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init] at h2
    · exact hI.bv_sub k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init] at h2
    · exact hI.bv_self k m hk h2
  · intro k m k' m' hk hk' h1 h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init] at h1
    rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
    · simp [Loc.init] at h2
    exact hI.av_cmp k m k' m' hk hk' h1 h2
  · intro k m k' m' hk hk' h1 h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [Loc.init] at h1
    rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
    · simp [Loc.init] at h2
    exact hI.bv_cmp k m k' m' hk hk' h1 h2

theorem Inv.step0 {g : State n T} (hI : Inv g) {i : Fin n} {l : Loc n T} (hl : g.loc i = some l)
    (h0 : l.pc = 0) :
    Inv (⟨Function.update g.A i (some l.inp), g.B,
      Function.update g.loc i (some { l with pc := 1 })⟩ : State n T) := by
  have hAi : g.A i = none := by simpa [h0] using hI.A_eq i l hl
  have hBi : g.B i = none := by simpa [h0] using hI.B_eq i l hl
  constructor
  · intro k hk
    obtain ⟨hki, hk⟩ := upd_none hk
    simp only [Function.update_of_ne hki]
    exact hI.A_none k hk
  · intro k hk
    exact hI.B_none k (upd_none hk).2
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp
    · exact hI.pc_le k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨hki, hk⟩
    · simp
    · simp only [Function.update_of_ne hki]
      exact hI.A_eq k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [hBi]
    · exact hI.B_eq k m hk
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h2
    · exact (hI.av_sub k m hk h2).update hAi _
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h2
    · exact hI.av_self k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h2
    · exact hI.bv_sub k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h2
    · exact hI.bv_self k m hk h2
  · intro k m k' m' hk hk' h1 h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h1
    rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
    · simp at h2
    exact hI.av_cmp k m k' m' hk hk' h1 h2
  · intro k m k' m' hk hk' h1 h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h1
    rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
    · simp at h2
    exact hI.bv_cmp k m k' m' hk hk' h1 h2

theorem Inv.step1 {g : State n T} (hI : Inv g) {i : Fin n} {l : Loc n T} (hl : g.loc i = some l)
    (h1 : l.pc = 1) :
    Inv (⟨g.A, g.B, Function.update g.loc i (some { l with pc := 2, av := g.A })⟩ : State n T) := by
  have hAi : g.A i = some l.inp := by simpa [h1] using hI.A_eq i l hl
  have hBi : g.B i = none := by simpa [h1] using hI.B_eq i l hl
  constructor
  · intro k hk
    exact hI.A_none k (upd_none hk).2
  · intro k hk
    exact hI.B_none k (upd_none hk).2
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp
    · exact hI.pc_le k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [hAi]
    · exact hI.A_eq k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [hBi]
    · exact hI.B_eq k m hk
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact Sub.refl _
    · exact hI.av_sub k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact hAi
    · exact hI.av_self k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h2
    · exact hI.bv_sub k m hk h2
  · intro k m hk h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h2
    · exact hI.bv_self k m hk h2
  · intro k m k' m' hk hk' h1 h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk₀⟩ <;>
      rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk₀'⟩
    · exact Or.inl (Sub.refl _)
    · exact Or.inr (hI.av_sub _ _ hk₀' h2)
    · exact Or.inl (hI.av_sub _ _ hk₀ h1)
    · exact hI.av_cmp k m k' m' hk₀ hk₀' h1 h2
  · intro k m k' m' hk hk' h1 h2
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h1
    rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
    · simp at h2
    exact hI.bv_cmp k m k' m' hk hk' h1 h2

theorem Inv.step2 {g : State n T} (hI : Inv g) {i : Fin n} {l : Loc n T} (hl : g.loc i = some l)
    (h2 : l.pc = 2) :
    Inv (⟨g.A, Function.update g.B i (some (candidate l.av, compatFlag l.av)),
      Function.update g.loc i (some { l with pc := 3 })⟩ : State n T) := by
  have hAi : g.A i = some l.inp := by simpa [h2] using hI.A_eq i l hl
  have hBi : g.B i = none := by simpa [h2] using hI.B_eq i l hl
  have hl2 : 2 ≤ l.pc := h2.ge
  constructor
  · intro k hk
    exact hI.A_none k (upd_none hk).2
  · intro k hk
    obtain ⟨hki, hk⟩ := upd_none hk
    simp only [Function.update_of_ne hki]
    exact hI.B_none k hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp
    · exact hI.pc_le k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [hAi]
    · exact hI.A_eq k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨hki, hk⟩
    · simp
    · simp only [Function.update_of_ne hki]
      exact hI.B_eq k m hk
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have := hI.av_sub _ _ hl hl2; exact this
    · exact hI.av_sub k m hk h
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have := hI.av_self _ _ hl hl2; exact this
    · exact hI.av_self k m hk h
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h
    · exact (hI.bv_sub k m hk h).update hBi _
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h
    · exact hI.bv_self k m hk h
  · intro k m k' m' hk hk' h1 h1'
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk₀⟩ <;>
      rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk₀'⟩
    · exact Or.inl (Sub.refl _)
    · have := hI.av_cmp _ _ _ _ hl hk₀' hl2 h1'; exact this
    · have := hI.av_cmp _ _ _ _ hk₀ hl h1 hl2; exact this
    · exact hI.av_cmp k m k' m' hk₀ hk₀' h1 h1'
  · intro k m k' m' hk hk' h1 h1'
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp at h1
    rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
    · simp at h1'
    exact hI.bv_cmp k m k' m' hk hk' h1 h1'

theorem Inv.step3 {g : State n T} (hI : Inv g) {i : Fin n} {l : Loc n T} (hl : g.loc i = some l)
    (h3 : l.pc = 3) :
    Inv (⟨g.A, g.B, Function.update g.loc i (some { l with pc := 4, bv := g.B })⟩ : State n T) := by
  have hAi : g.A i = some l.inp := by simpa [h3] using hI.A_eq i l hl
  have hBi : g.B i = some (candidate l.av, compatFlag l.av) := by simpa [h3] using hI.B_eq i l hl
  have hl2 : 2 ≤ l.pc := by omega
  constructor
  · intro k hk
    exact hI.A_none k (upd_none hk).2
  · intro k hk
    exact hI.B_none k (upd_none hk).2
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp
    · exact hI.pc_le k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [hAi]
    · exact hI.A_eq k m hk
  · intro k m hk
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [hBi]
    · exact hI.B_eq k m hk
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have := hI.av_sub _ _ hl hl2; exact this
    · exact hI.av_sub k m hk h
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · have := hI.av_self _ _ hl hl2; exact this
    · exact hI.av_self k m hk h
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact Sub.refl _
    · exact hI.bv_sub k m hk h
  · intro k m hk h
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · simp [hBi]
    · exact hI.bv_self k m hk h
  · intro k m k' m' hk hk' h1 h1'
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk₀⟩ <;>
      rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk₀'⟩
    · exact Or.inl (Sub.refl _)
    · have := hI.av_cmp _ _ _ _ hl hk₀' hl2 h1'; exact this
    · have := hI.av_cmp _ _ _ _ hk₀ hl h1 hl2; exact this
    · exact hI.av_cmp k m k' m' hk₀ hk₀' h1 h1'
  · intro k m k' m' hk hk' h1 h1'
    rcases upd_some hk with ⟨rfl, rfl⟩ | ⟨-, hk₀⟩ <;>
      rcases upd_some hk' with ⟨rfl, rfl⟩ | ⟨-, hk₀'⟩
    · exact Or.inl (Sub.refl _)
    · exact Or.inr (hI.bv_sub _ _ hk₀' h1')
    · exact Or.inl (hI.bv_sub _ _ hk₀ h1)
    · exact hI.bv_cmp k m k' m' hk₀ hk₀' h1 h1'

theorem Inv.step {g : State n T} (hI : Inv g) {i : Fin n} {l : Loc n T} (hl : g.loc i = some l)
    (h4 : l.pc < 4) : Inv (g.step i l) := by
  rcases (by omega : l.pc = 0 ∨ l.pc = 1 ∨ l.pc = 2 ∨ l.pc = 3) with h | h | h | h
  · rw [step_eq_zero h]; exact hI.step0 hl h
  · rw [step_eq_one h]; exact hI.step1 hl h
  · rw [step_eq_two h]; exact hI.step2 hl h
  · rw [step_eq_three h]; exact hI.step3 hl h

theorem inv_of_reach {g : State n T} (h : Reach g) : Inv g := by
  induction h with
  | init => exact inv_init
  | invoke i s _ hi ih => exact ih.invoke s hi
  | step i l _ hl h4 ih => exact ih.step hl h4

/-! ### Consequences of the invariant -/

section Consequences

variable {g : State n T}

theorem Inv.A_some (hI : Inv g) {k : Fin n} {x : T} (h : g.A k = some x) :
    ∃ l, g.loc k = some l ∧ l.inp = x := by
  cases hk : g.loc k with
  | none => rw [hI.A_none k hk] at h; cases h
  | some l =>
    have := hI.A_eq k l hk
    rw [h] at this
    split_ifs at this
    · exact ⟨l, rfl, (Option.some.inj this).symm⟩

theorem Inv.B_some (hI : Inv g) {k : Fin n} {b : T} {c : Bool} (h : g.B k = some (b, c)) :
    ∃ l, g.loc k = some l ∧ 3 ≤ l.pc ∧ b = candidate l.av ∧ c = compatFlag l.av := by
  cases hk : g.loc k with
  | none => rw [hI.B_none k hk] at h; cases h
  | some l =>
    have := hI.B_eq k l hk
    rw [h] at this
    split_ifs at this with h3
    · simp only [Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨l, rfl, h3, this.1, this.2⟩

/-- Entries of a view of `A` are inputs of participants. -/
theorem Inv.av_entry (hI : Inv g) {j k : Fin n} {lj : Loc n T} (hj : g.loc j = some lj)
    (h2 : 2 ≤ lj.pc) {a : T} (ha : lj.av k = some a) : ∃ lk, g.loc k = some lk ∧ lk.inp = a :=
  hI.A_some (hI.av_sub j lj hj h2 k a ha)

theorem Inv.mem_inputs (hI : Inv g) {j : Fin n} {lj : Loc n T} (hj : g.loc j = some lj)
    (h2 : 2 ≤ lj.pc) {a : T} (ha : a ∈ vals lj.av) : a ∈ inputs g := by
  obtain ⟨k, hk⟩ := mem_vals.1 ha
  obtain ⟨lk, hlk, rfl⟩ := hI.av_entry hj h2 hk
  exact ⟨k, lk, hlk, rfl⟩

/-- Entries of a view of `B` are the candidates and flags written by participants. -/
theorem Inv.bv_entry (hI : Inv g) {j k : Fin n} {lj : Loc n T} (hj : g.loc j = some lj)
    (h4 : 4 ≤ lj.pc) {b : T} {c : Bool} (hb : lj.bv k = some (b, c)) :
    ∃ lk, g.loc k = some lk ∧ 3 ≤ lk.pc ∧ b = candidate lk.av ∧ c = compatFlag lk.av :=
  hI.B_some (hI.bv_sub j lj hj h4 k _ hb)

theorem Inv.B_of_pc (hI : Inv g) {k : Fin n} {lk : Loc n T} (hk : g.loc k = some lk)
    (h3 : 3 ≤ lk.pc) : g.B k = some (candidate lk.av, compatFlag lk.av) := by
  simpa [h3] using hI.B_eq k lk hk

/-- A returned process sees its own entry in its view of `B`. -/
theorem Inv.bv_own (hI : Inv g) {j : Fin n} {lj : Loc n T} (hj : g.loc j = some lj)
    (h4 : 4 ≤ lj.pc) : lj.bv j = some (candidate lj.av, compatFlag lj.av) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hI.bv_self j lj hj h4)
  have := hI.bv_sub j lj hj h4 j x hx
  rw [hI.B_of_pc hj (by omega), Option.some.injEq] at this
  rw [hx, this]

theorem output_fst (l : Loc n T) : l.output.1 = beta (candidate l.av) l.bv := rfl

theorem output_snd (l : Loc n T) :
    l.output.2 = commitFlag l.inp l.av l.bv (beta (candidate l.av) l.bv) := rfl

/-- Every output trace is below the candidate of some participant. -/
theorem Inv.output_le (hI : Inv g) {j : Fin n} {l : Loc n T} (h : Returned g j l) :
    ∃ k lk, g.loc k = some lk ∧ 2 ≤ lk.pc ∧ l.output.1 ≤ candidate lk.av := by
  obtain ⟨hj, h4⟩ := h
  rw [output_fst]
  by_cases hf : (flagged l.bv).Nonempty
  · obtain ⟨b, hb⟩ := hf
    obtain ⟨k, hk⟩ := mem_flagged.1 hb
    obtain ⟨lk, hlk, h3, rfl, -⟩ := hI.bv_entry hj h4.ge hk
    exact ⟨k, lk, hlk, by omega, beta_le hb⟩
  · exact ⟨j, l, hj, by omega, by simp [beta, hf]⟩

/-- All candidates of participants have a common upper bound (Lemma A.4). -/
theorem Inv.exists_ub_candidates (hI : Inv g) :
    ∃ z, ∀ k l, g.loc k = some l → 2 ≤ l.pc → candidate l.av ≤ z := by
  let C : Finset T := Finset.univ.biUnion fun k =>
    (g.loc k).elim ∅ fun l => if 2 ≤ l.pc then vals (co l.av) else ∅
  have hC : ∀ x ∈ C, ∃ k l, g.loc k = some l ∧ 2 ≤ l.pc ∧ x ∈ vals (co l.av) := by
    intro x hx
    obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hx
    cases h : g.loc k with
    | none => simp [h] at hk
    | some l =>
      rw [h] at hk
      simp only [Option.elim] at hk
      split_ifs at hk with h2
      · exact ⟨k, l, h, h2, hk⟩
      · simp at hk
  have hC' : ∀ k l, g.loc k = some l → 2 ≤ l.pc → vals (co l.av) ⊆ C := by
    intro k l h h2 x hx
    exact Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, by simp [h, h2, hx]⟩
  obtain ⟨z, hz⟩ := GCADomain.compat_of_pairwise C (by
    intro x hx y hy
    obtain ⟨k, l, hk, h2, hx⟩ := hC x hx
    obtain ⟨k', l', hk', h2', hy⟩ := hC y hy
    rcases hI.av_cmp k l k' l' hk hk' h2 h2' with h | h
    · exact compat_co_co h hx hy
    · exact compat_pair_comm.1 (compat_co_co h hy hx))
  exact ⟨z, fun k l hk h2 => (isLUB_candidate l.av).2 fun x hx => hz x (hC' k l hk h2 hx)⟩

end Consequences

/-! ### The six properties -/

section Properties

variable {g : State n T}

/-- Validity (property (1) of Section 4.2) holds in every reachable state. -/
theorem validity_of_reach (h : Reach g) : Validity g := by
  have hI := inv_of_reach h
  intro C supp hmono hsub i l hret c hc
  obtain ⟨k, lk, hk, h2, hle⟩ := hI.output_le hret
  have hc' := hsub _ (compat_vals_co lk.av) (hmono _ _ hle hc)
  simp only [Set.mem_iUnion] at hc'
  obtain ⟨x, hx, hcx⟩ := hc'
  obtain ⟨k', a, ha, rfl⟩ := mem_vals_co.1 hx
  have hca := hmono _ _ (coEntry_le_self _ _) hcx
  exact Set.mem_iUnion₂.2 ⟨a, hI.mem_inputs hk h2 (mem_vals.2 ⟨k', ha⟩), hca⟩

/-- Convergence (property (4) of Section 4.2) holds in every reachable state. -/
theorem convergence_of_reach (h : Reach g) : Convergence g := by
  have hI := inv_of_reach h
  obtain ⟨z, hz⟩ := hI.exists_ub_candidates
  refine ⟨z, ?_⟩
  rintro x ⟨j, l, hret, rfl⟩
  obtain ⟨k, lk, hk, h2, hle⟩ := hI.output_le hret
  exact hle.trans (hz k lk hk h2)

/-- A common prefix of the inputs is below every candidate. -/
theorem Inv.le_candidate_of_le_inputs (hI : Inv g) {x : T} (hx : ∀ y ∈ inputs g, x ≤ y)
    {k : Fin n} {lk : Loc n T} (hk : g.loc k = some lk) (h2 : 2 ≤ lk.pc) :
    x ≤ candidate lk.av := by
  have hself := hI.av_self k lk hk h2
  refine le_trans ?_ (le_candidate (mem_vals_co.2 ⟨k, lk.inp, hself, rfl⟩))
  exact le_coEntry (hx _ ⟨k, lk, hk, rfl⟩) fun b hb => hx b (hI.mem_inputs hk h2 hb)

/-- Common prefix (property (5) of Section 4.2) holds in every reachable state. -/
theorem commonPrefix_of_reach (h : Reach g) : CommonPrefix g := by
  have hI := inv_of_reach h
  intro x hx i l ⟨hi, h4⟩
  rw [output_fst]
  refine le_beta (fun b hb => ?_) fun _ => hI.le_candidate_of_le_inputs hx hi (by omega)
  obtain ⟨k, hk⟩ := mem_flagged.1 hb
  obtain ⟨lk, hlk, h3, rfl, -⟩ := hI.bv_entry hi h4.ge hk
  exact hI.le_candidate_of_le_inputs hx hlk (by omega)

/-- Weak agreement (property (6) of Section 4.2) holds in every reachable state. -/
theorem weakAgreement_of_reach (h : Reach g) : WeakAgreement g := by
  have hI := inv_of_reach h
  intro heq i l ⟨hi, h4⟩
  have hs : ∀ y ∈ inputs g, y = l.inp := fun y hy => heq y hy _ ⟨i, l, hi, rfl⟩
  have hcand : ∀ k lk, g.loc k = some lk → 2 ≤ lk.pc → candidate lk.av = l.inp := by
    intro k lk hk h2
    refine (co_candidate_const (s := l.inp) (fun k' a ha => ?_) (k₀ := k) ?_).2
    · exact hs a (hI.mem_inputs hk h2 (mem_vals.2 ⟨k', ha⟩))
    · rw [hI.av_self k lk hk h2, hs _ ⟨k, lk, hk, rfl⟩]
  rw [output_snd, commitFlag, decide_eq_true_iff]
  refine Or.inl ⟨fun k a ha => hs a (hI.mem_inputs hi (by omega) (mem_vals.2 ⟨k, ha⟩)),
    fun k b c hb => ?_⟩
  obtain ⟨lk, hlk, h3, rfl, -⟩ := hI.bv_entry hi h4.ge hb
  exact hcand k lk hlk (by omega)

/-- Adoption (property (2) of Section 4.2) holds in every reachable state: a committed trace is
extended by every output trace.

The argument differs from the paper's. If `i` committed because of the weak-agreement flag
`w_i`, its candidate and output are its input `s_i`, and every flagged candidate `b_z` is `≥ s_i`
(if `A_i ⊆ A_z` by monotonicity of candidates on compatible views, otherwise `A_z` only contains
`s_i`). Otherwise all entries of `B_i` are flagged and every `a_k ∈ A_i` with `a_k ≤ β_i` has an
entry in `B_i`; then every flagged candidate `b_z` seen by `j` is `≥ β_i`: either `z ∈ B_i`, or
`A_k ⊆ A_z` for some `k ∈ B_i` (monotonicity), or `A_z ⊆ A_k` for all `k ∈ B_i`, so that
`a_z ∈ A_i`, `a_z ≤ b_k` for all `k ∈ B_i`, `a_z ≤ β_i`, and the commit condition puts `z` into
`B_i` — a contradiction. -/
theorem adoption_of_reach (h : Reach g) : Adoption g := by
  have hI := inv_of_reach h
  intro i li j lj ⟨hi, hi4⟩ ⟨hj, hj4⟩ hc
  rw [output_snd, commitFlag, decide_eq_true_iff] at hc
  rw [output_fst, output_fst]
  have hown_i := hI.bv_own hi hi4.ge
  have hown_j := hI.bv_own hj hj4.ge
  rcases hc with ⟨hwa, hwb⟩ | ⟨hC1, hC2⟩
  · -- `i` committed because of the weak-agreement flag
    have hcand_i : candidate li.av = li.inp := hwb i _ _ hown_i
    have hco_i : co li.av = li.av :=
      (co_candidate_const hwa (hI.av_self i li hi (by omega))).1
    have hflag_i : compatFlag li.av = true := compatFlag_eq_true.2 hco_i
    have hβi : beta (candidate li.av) li.bv ≤ li.inp :=
      beta_le (mem_flagged.2 ⟨i, by rw [hown_i, hcand_i, hflag_i]⟩)
    refine hβi.trans (le_beta (fun b hb => ?_) fun hne => ?_)
    · obtain ⟨z, hz⟩ := mem_flagged.1 hb
      obtain ⟨lz, hlz, hz3, rfl, hfz⟩ := hI.bv_entry hj hj4.ge hz
      have hcoz : co lz.av = lz.av := compatFlag_eq_true.1 hfz.symm
      rcases hI.av_cmp i li z lz hi hlz (by omega) (by omega) with hs | hs
      · rw [← hcand_i]
        exact candidate_mono hco_i hcoz hs
      · have hall : ∀ k a, lz.av k = some a → a = li.inp := fun k a ha => hwa k a (hs k a ha)
        have hzs : lz.av z = some li.inp := by
          have := hI.av_self z lz hlz (by omega)
          rw [this, hall z _ this]
        exact (co_candidate_const hall hzs).2.symm.le
    · rcases hI.bv_cmp i li j lj hi hj hi4.ge hj4.ge with hs | hs
      · exact absurd ⟨li.inp, mem_flagged.2 ⟨i, by rw [hs i _ hown_i, hcand_i, hflag_i]⟩⟩ hne
      · exact (hwb j _ _ (hs j _ hown_j)).symm.le
  · -- `i` committed because of the commit condition of line 9
    have hfl : ∀ k b c, li.bv k = some (b, c) → c = true := by
      intro k b c hb
      cases c
      · exact absurd hb (hC2 k b)
      · rfl
    have hβ_le : ∀ k b c, li.bv k = some (b, c) → beta (candidate li.av) li.bv ≤ b := by
      intro k b c hb
      have := hfl k b c hb
      subst this
      exact beta_le (mem_flagged.2 ⟨k, hb⟩)
    have hne_i : (flagged li.bv).Nonempty :=
      ⟨candidate li.av, mem_flagged.2 ⟨i, by rw [hown_i, hfl _ _ _ hown_i]⟩⟩
    refine le_beta (fun b hb => ?_) fun hne => ?_
    · obtain ⟨z, hz⟩ := mem_flagged.1 hb
      obtain ⟨lz, hlz, hz3, rfl, hfz⟩ := hI.bv_entry hj hj4.ge hz
      have hcoz : co lz.av = lz.av := compatFlag_eq_true.1 hfz.symm
      cases hiz : li.bv z with
      | some y =>
        have h1 := hI.bv_sub i li hi hi4.ge z y hiz
        have h2 := hI.bv_sub j lj hj hj4.ge z _ hz
        rw [h1, Option.some.injEq] at h2
        subst h2
        exact hβ_le z _ _ hiz
      | none =>
        by_cases hex : ∃ k lk b c, g.loc k = some lk ∧ li.bv k = some (b, c) ∧ Sub lk.av lz.av
        · obtain ⟨k, lk, b, c, hlk, hb', hs⟩ := hex
          obtain ⟨lk', hlk', hk3, rfl, rfl⟩ := hI.bv_entry hi hi4.ge hb'
          have e : lk' = lk := Option.some.inj (hlk'.symm.trans hlk)
          subst e
          have hcok : co lk'.av = lk'.av := compatFlag_eq_true.1 (hfl _ _ _ hb')
          exact (hβ_le k _ _ hb').trans (candidate_mono hcok hcoz hs)
        · push Not at hex
          have hsub : ∀ k lk b c, g.loc k = some lk → li.bv k = some (b, c) →
              Sub lz.av lk.av := by
            intro k lk b c hlk hb'
            obtain ⟨lk', hlk', hk3, -, -⟩ := hI.bv_entry hi hi4.ge hb'
            have e : lk' = lk := Option.some.inj (hlk'.symm.trans hlk)
            subst e
            rcases hI.av_cmp k lk' z lz hlk' hlz (by omega) (by omega) with hs | hs
            · exact absurd hs (hex k lk' b c hlk' hb')
            · exact hs
          have hzself := hI.av_self z lz hlz (by omega)
          have hiz' : li.av z = some lz.inp := hsub i li _ _ hi hown_i z _ hzself
          have hle : lz.inp ≤ beta (candidate li.av) li.bv := by
            refine le_beta (fun b' hb' => ?_) fun h => absurd hne_i h
            obtain ⟨k, hk⟩ := mem_flagged.1 hb'
            obtain ⟨lk, hlk, hk3, rfl, hfk⟩ := hI.bv_entry hi hi4.ge hk
            exact le_candidate_of_co_eq (compatFlag_eq_true.1 hfk.symm)
              (mem_vals.2 ⟨z, hsub k lk _ _ hlk hk z _ hzself⟩)
          have := hC1 z _ hiz' hle
          simp [hiz] at this
    · rcases hI.bv_cmp i li j lj hi hj hi4.ge hj4.ge with hs | hs
      · exact absurd ⟨candidate li.av, mem_flagged.2 ⟨i, by
          rw [hs i _ hown_i, hfl _ _ _ hown_i]⟩⟩ hne
      · exact hβ_le j _ _ (hs j _ hown_j)

/-- Commitment (property (3) of Section 4.2) holds in every reachable state: if all inputs are
compatible and all participants have returned, some process commits an extension of its input.

The argument differs from the paper's. All views are compatible and all flags are raised; the
candidate `β₀` of a process `q` with a smallest view of `A` is the smallest candidate, and every
process that sees `q`'s entry in `B` outputs `β₀`. Among the processes `j` that see `q`'s entry and
have `s_j ≤ β₀` (`q` is one), take one with a largest view of `B`. If it did not commit, some
`a_k ≤ β₀` of `A_j` has no entry in `B_j`; then `k` also qualifies and has a strictly larger
view of `B` — a contradiction. -/
theorem commitment_of_reach (h : Reach g) : Commitment g := by
  have hI := inv_of_reach h
  rintro ⟨z0, hz0⟩ hall ⟨p, hp⟩
  have hpc : ∀ k lk, g.loc k = some lk → 2 ≤ lk.pc := fun k lk hk => by
    rw [hall k lk hk]; omega
  have hco : ∀ k lk, g.loc k = some lk → co lk.av = lk.av := by
    intro k lk hk
    exact co_eq_self fun a ha b hb => compat_pair_of_le
      (hz0 a (hI.mem_inputs hk (hpc k lk hk) ha)) (hz0 b (hI.mem_inputs hk (hpc k lk hk) hb))
  have hflag : ∀ k lk, g.loc k = some lk → compatFlag lk.av = true :=
    fun k lk hk => compatFlag_eq_true.2 (hco k lk hk)
  let avOf : Fin n → (Fin n → Option T) := fun k => ((g.loc k).map Loc.av).getD fun _ => none
  let bvOf : Fin n → (Fin n → Option (T × Bool)) :=
    fun k => ((g.loc k).map Loc.bv).getD fun _ => none
  have havOf : ∀ k lk, g.loc k = some lk → avOf k = lk.av := by
    intro k lk hk; simp [avOf, hk]
  have hbvOf : ∀ k lk, g.loc k = some lk → bvOf k = lk.bv := by
    intro k lk hk; simp [bvOf, hk]
  -- `q`: a participant with a smallest view of `A`
  obtain ⟨lp, hlp⟩ := Option.ne_none_iff_exists'.1 hp
  obtain ⟨q, hqP, hqmin⟩ := Finset.exists_min_image
    (Finset.univ.filter fun k => (g.loc k).isSome) (fun k => sz (avOf k)) ⟨p, by simp [hlp]⟩
  obtain ⟨lq, hlq⟩ := Option.isSome_iff_exists.1 (Finset.mem_filter.1 hqP).2
  have hq4 := hall q lq hlq
  have hqsub : ∀ k lk, g.loc k = some lk → Sub lq.av lk.av := by
    intro k lk hk
    rcases hI.av_cmp q lq k lk hlq hk (hpc q lq hlq) (hpc k lk hk) with hs | hs
    · exact hs
    · refine hs.antisymm_of_sz ?_
      have := hqmin k (by simp [hk])
      rwa [havOf q lq hlq, havOf k lk hk] at this
  have hβ0le : ∀ k lk, g.loc k = some lk → candidate lq.av ≤ candidate lk.av :=
    fun k lk hk => candidate_mono (hco q lq hlq) (hco k lk hk) (hqsub k lk hk)
  have hBq : g.B q = some (candidate lq.av, true) := by
    rw [hI.B_of_pc hlq (by omega), hflag q lq hlq]
  -- every process that sees `q`'s entry outputs `β₀ = candidate lq.av`
  have hβ : ∀ j lj, g.loc j = some lj → (lj.bv q).isSome →
      beta (candidate lj.av) lj.bv = candidate lq.av := by
    intro j lj hj hq
    have hj4 := hall j lj hj
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hq
    have := hI.bv_sub j lj hj hj4.ge q x hx
    rw [hBq, Option.some.injEq] at this
    subst this
    refine le_antisymm (beta_le (mem_flagged.2 ⟨q, hx⟩))
      (le_beta (fun b hb => ?_) fun _ => hβ0le j lj hj)
    obtain ⟨k, hk⟩ := mem_flagged.1 hb
    obtain ⟨lk, hlk, -, rfl, -⟩ := hI.bv_entry hj hj4.ge hk
    exact hβ0le k lk hlk
  let M0 := Finset.univ.filter fun j =>
    ∃ lj, g.loc j = some lj ∧ (lj.bv q).isSome ∧ lj.inp ≤ candidate lq.av
  have hqM : q ∈ M0 := by
    simp only [M0, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨lq, hlq, by rw [hI.bv_own hlq hq4.ge]; rfl, ?_⟩
    exact le_candidate_of_co_eq (hco q lq hlq) (mem_vals.2 ⟨q, hI.av_self q lq hlq (by omega)⟩)
  -- `j`: such a process with a largest view of `B`
  obtain ⟨j, hjM, hjmax⟩ := Finset.exists_max_image M0 (fun j => sz (bvOf j)) ⟨q, hqM⟩
  obtain ⟨lj, hj, hjq, hjinp⟩ := (Finset.mem_filter.1 hjM).2
  have hj4 := hall j lj hj
  have hβj := hβ j lj hj hjq
  refine ⟨j, lj, ⟨hj, hj4⟩, by rw [output_fst, hβj]; exact hjinp, ?_⟩
  rw [output_snd, commitFlag, decide_eq_true_iff]
  refine Or.inr ⟨fun k a ha hle => ?_, fun k b hb => ?_⟩
  · by_contra hk
    have hk' : lj.bv k = none := by simpa using hk
    obtain ⟨lk, hlk, rfl⟩ := hI.av_entry hj (by omega) ha
    have hk4 := hall k lk hlk
    have hkk := hI.bv_self k lk hlk hk4.ge
    have hs : Sub lj.bv lk.bv := by
      rcases hI.bv_cmp j lj k lk hj hlk hj4.ge hk4.ge with hs | hs
      · exact hs
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hkk
        rw [hs k x hx] at hk'
        cases hk'
    have hkM : k ∈ M0 := by
      simp only [M0, Finset.mem_filter, Finset.mem_univ, true_and]
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hjq
      exact ⟨lk, hlk, by rw [hs q x hx]; rfl, hle.trans hβj.le⟩
    have := hjmax k hkM
    simp only [hbvOf j lj hj, hbvOf k lk hlk] at this
    exact absurd (hs.sz_lt hk' hkk) (not_lt.2 this)
  · obtain ⟨lk, hlk, -, -, hc⟩ := hI.bv_entry hj hj4.ge hb
    rw [hflag k lk hlk] at hc
    cases hc

end Properties

/-! ### Theorem 5.1 -/

/-- Theorem 5.1 of [KST26]: Algorithm 2 implements generalized commit-adopt: every reachable
state satisfies the six GCA properties. -/
theorem isGCA_of_reach {g : State n T} (h : Reach g) : IsGCA g :=
  ⟨validity_of_reach h, adoption_of_reach h, commitment_of_reach h, convergence_of_reach h,
    commonPrefix_of_reach h, weakAgreement_of_reach h⟩

/-! ### Wait-freedom -/

/-- Every step of a participant that has not returned increments its program counter (whatever
the state of the shared objects), so it returns after `4 - pc` of its own steps. -/
theorem stepLoc_pc (A : Fin n → Option T) (B : Fin n → Option (T × Bool)) (i : Fin n)
    (l : Loc n T) (h : l.pc < 4) : (stepLoc A B i l).2.2.pc = l.pc + 1 := by
  rcases (by omega : l.pc = 0 ∨ l.pc = 1 ∨ l.pc = 2 ∨ l.pc = 3) with h | h | h | h <;>
    simp [stepLoc, h]

/-- Steps of other processes do not change the local state of `i`. -/
theorem step_loc_of_ne (g : State n T) {i j : Fin n} (l : Loc n T) (hij : i ≠ j) :
    (g.step j l).loc i = g.loc i := by
  simp [State.step, Function.update_of_ne hij]

theorem step_loc_self (g : State n T) (i : Fin n) (l : Loc n T) :
    (g.step i l).loc i = some (stepLoc g.A g.B i l).2.2 := by
  simp [State.step]

/-- `g'` results from `g` by `m` consecutive steps of process `i` alone. -/
def SoloSteps (i : Fin n) : ℕ → State n T → State n T → Prop
  | 0, g, g' => g' = g
  | m + 1, g, g' => ∃ l, g.loc i = some l ∧ l.pc < 4 ∧ SoloSteps i m (g.step i l) g'

/-- Wait-freedom: from any reachable state, a participant running alone returns after exactly
`4 - pc` steps of its own. -/
theorem wait_free {g : State n T} (h : Reach g) {i : Fin n} {l : Loc n T}
    (hl : g.loc i = some l) :
    ∃ g' l', SoloSteps i (4 - l.pc) g g' ∧ Reach g' ∧ Returned g' i l' := by
  have hle := (inv_of_reach h).pc_le i l hl
  generalize hm : 4 - l.pc = m
  induction m generalizing g l with
  | zero => exact ⟨g, l, rfl, h, hl, by omega⟩
  | succ m ih =>
    have h4 : l.pc < 4 := by omega
    have h' := Reach.step i l h hl h4
    have hl' := step_loc_self g i l
    obtain ⟨g', l', hs, hr, hret⟩ := ih h' hl'
      ((inv_of_reach h').pc_le i _ hl') (by rw [stepLoc_pc _ _ _ _ h4]; omega)
    exact ⟨g', l', ⟨l, hl, h4, hs⟩, hr, hret⟩

end GCA

end Podc.ConflictFreedom
