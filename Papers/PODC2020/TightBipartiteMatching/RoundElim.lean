import Papers.PODC2020.TightBipartiteMatching.Views

/-!
# Bipartite round elimination (§2.2)

* `Problem L`: a white constraint `W` and a black constraint `B` (sets of configurations, i.e.
  multisets of `Δ` labels).
* `Problem.WhiteIn d Pr t` / `Problem.BlackIn d Pr t`: `Pr` has a white (black) `t`-round algorithm
  on the 2-coloured `(d+1)`-regular tree, i.e. white (black) complexity `≤ t`.
* `univC` / `exC`: the universal and existential quantifier over configurations of sets of labels.
  `RB Pr` has the black constraint `univC Pr.B` and the white constraint `exC Pr.W`; `RW Pr` is dual.
  We use only **nonempty** sets of labels in the universal step (see `differencies.md`), and we do
  not perform the maximality simplification: both only make `R_B(Pr)` harder, so the round
  elimination theorem below is (slightly) stronger than the paper's Theorem 2.1, and every
  relaxation of it is in particular a relaxation of the paper's `R_B(Pr)` restricted to nonempty
  sets.
* `theorem_2_1`: the round elimination theorem (forward direction, the one used for lower
  bounds): white complexity `t + 1` for `Pr` implies black complexity `t` for `R_B(Pr)`.
  The paper states "black complexity `min{0, T − 1}`", which is a typo for `max{0, T − 1}`.
  The forward direction needs no edge symmetry breaking (cf. `Papers/PODC2019/AutomaticSpeedup`,
  where the *converse* fails).
* `Relax`: relaxations by a 0-round relabelling of the active side, and `relax_of_meaning`, the
  form in which the relaxations of Lemmas 4.1–4.3 are proved (each new label stands for a set of old
  labels; the universal configuration is enlarged label-wise).
-/

-- CSLib candidate (bipartite round elimination infrastructure)
namespace TightBipartiteMatching

variable {d : ℕ} {L L' : Type*}

/-- A bipartite locally checkable problem: white and black constraints. -/
structure Problem (L : Type*) where
  /-- The white constraint. -/
  W : Set (Multiset L)
  /-- The black constraint. -/
  B : Set (Multiset L)

namespace Problem

/-- Exchange the roles of white and black. -/
def swap (Pr : Problem L) : Problem L := ⟨Pr.B, Pr.W⟩

/-- `Pr` has a white algorithm with `t` rounds on the 2-coloured `(d+1)`-regular tree: white nodes
decide the labels of all edges. -/
def WhiteIn (d : ℕ) (Pr : Problem L) (t : ℕ) : Prop :=
  ∃ A : View d t → Fin (d + 1) → L, Solves A Pr.W Pr.B

/-- `Pr` has a black algorithm with `t` rounds. -/
def BlackIn (d : ℕ) (Pr : Problem L) (t : ℕ) : Prop :=
  ∃ A : View d t → Fin (d + 1) → L, Solves A Pr.B Pr.W

@[simp] theorem blackIn_swap (Pr : Problem L) (t : ℕ) : Pr.swap.BlackIn d t ↔ Pr.WhiteIn d t :=
  Iff.rfl

@[simp] theorem whiteIn_swap (Pr : Problem L) (t : ℕ) : Pr.swap.WhiteIn d t ↔ Pr.BlackIn d t :=
  Iff.rfl

theorem WhiteIn.mono {Pr : Problem L} {t t' : ℕ} (h : Pr.WhiteIn d t) (htt : t ≤ t') :
    Pr.WhiteIn d t' := Solves.mono htt h

theorem BlackIn.mono {Pr : Problem L} {t t' : ℕ} (h : Pr.BlackIn d t) (htt : t ≤ t') :
    Pr.BlackIn d t' := Solves.mono htt h

end Problem

/-- Universal quantifier: configurations of nonempty sets all of whose choices are in `C`. -/
def univC (C : Set (Multiset L)) : Set (Multiset (Set L)) :=
  {m | (∀ S ∈ m, S.Nonempty) ∧ ∀ m', Multiset.Rel (· ∈ ·) m' m → m' ∈ C}

/-- Existential quantifier: configurations of sets admitting a choice in `C`. -/
def exC (C : Set (Multiset L)) : Set (Multiset (Set L)) :=
  {m | ∃ m', Multiset.Rel (· ∈ ·) m' m ∧ m' ∈ C}

/-- `R_B(Pr)`: black constraint by the universal quantifier, white by the existential one. -/
def RB (Pr : Problem L) : Problem (Set L) := ⟨exC Pr.W, univC Pr.B⟩

/-- `R_W(Pr)`: white constraint by the universal quantifier, black by the existential one. -/
def RW (Pr : Problem L) : Problem (Set L) := ⟨univC Pr.W, exC Pr.B⟩

theorem mset_mem_univC {C : Set (Multiset L)} {n : ℕ} {g : Fin n → Set L} :
    mset g ∈ univC C ↔ (∀ k, (g k).Nonempty) ∧ ∀ f : Fin n → L, (∀ k, f k ∈ g k) → mset f ∈ C := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k => h1 _ (mem_mset.2 ⟨k, rfl⟩), fun f hf => h2 _ (rel_mset_of hf)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun S hS => ?_, fun m' hm' => ?_⟩
    · obtain ⟨k, rfl⟩ := mem_mset.1 hS; exact h1 k
    · obtain ⟨f, hf, rfl⟩ := rel_mset_iff.1 hm'; exact h2 f hf

theorem mset_mem_exC {C : Set (Multiset L)} {n : ℕ} {g : Fin n → Set L} :
    mset g ∈ exC C ↔ ∃ f : Fin n → L, (∀ k, f k ∈ g k) ∧ mset f ∈ C := by
  constructor
  · rintro ⟨m', hm', hC⟩
    obtain ⟨f, hf, rfl⟩ := rel_mset_iff.1 hm'
    exact ⟨f, hf, hC⟩
  · rintro ⟨f, hf, hC⟩
    exact ⟨_, rel_mset_of hf, hC⟩

/-! ### The round elimination theorem (forward direction) -/

/-- The derived algorithm: a passive node with radius-`t` view `U` outputs on port `k` the set of
all labels that its neighbour behind `k` could output on the connecting edge, over all extensions of
`U` to a radius-`(t + 2)` view. -/
def reAlg {t : ℕ} (A : View d (t + 1) → Fin (d + 1) → L) : View d t → Fin (d + 1) → Set L :=
  fun U k => {ℓ | ∃ U₂ : View d (t + 2), View.restrict (View.restrict U₂) = U ∧
    A (nbrView (t + 1) U₂ k) (U₂ k).port = ℓ}

/-- **Round elimination** (forward direction of Theorem 2.1 / [7, Thm 4.3], bipartite form): if `A`
solves `(Act, Pas)` in `t + 1` rounds with the active colour, then `reAlg A` solves
`(univC Pas, exC Act)` in `t` rounds with the other colour. -/
theorem re_forward {t : ℕ} {A : View d (t + 1) → Fin (d + 1) → L} {Act Pas : Set (Multiset L)}
    (h : Solves A Act Pas) : Solves (reAlg A) (univC Pas) (exC Act) := by
  classical
  refine ⟨fun U => mset_mem_univC.2 ⟨fun k => ?_, fun f hf => ?_⟩, fun V => ?_⟩
  · -- nonempty: extend `U` arbitrarily
    exact ⟨_, View.ext (View.ext U), by simp, rfl⟩
  · -- universal: glue the extensions chosen for the different ports
    choose U₂ hU₂ hf using hf
    let U' : View d (t + 2) := fun k => U₂ k k
    have hr : ∀ k, View.restrict (View.restrict U') k = U k := fun k => by
      rw [← hU₂ k]; rfl
    have hn : ∀ k, nbrView (t + 1) U' k = nbrView (t + 1) (U₂ k) k := fun k =>
      nbrView_congr rfl fun k' => (hr k').trans (congrFun (hU₂ k) k').symm
    have := h.2 U'
    simp only [hn] at this
    convert this using 2
    funext k
    exact (hf k).symm
  · -- existential: the true output is a valid choice
    refine mset_mem_exC.2 ⟨A V, fun k => ?_, h.1 V⟩
    set j := (V k).port
    let U₂ : View d (t + 2) := Fin.insertNth (α := fun _ => Br d (t + 2)) j
      (Br.mk k fun c => V (k.succAbove c)) fun c => Br.ext (t + 1) (Br.ext t ((V k).child c))
    refine ⟨U₂, ?_, ?_⟩
    · funext p
      cases t with
      | zero => exact Subsingleton.elim _ _
      | succ t =>
        rcases eq_or_ne p j with rfl | hp
        · simp only [View.restrict_apply, U₂, Fin.insertNth_apply_same, Br.restrict_mk]
          exact (nbrView_succ_apply_port V k).symm
        · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hp
          simp only [View.restrict_apply, U₂, Fin.insertNth_apply_succAbove, Br.restrict_ext,
            j, nbrView_succ_apply_succAbove]
    · have hU : U₂ j = Br.mk k fun c => V (k.succAbove c) := by simp [U₂]
      have hV : nbrView (t + 1) U₂ j = V := by
        funext p
        rcases eq_or_ne p k with rfl | hp
        · rw [show p = (U₂ j).port by simp [hU], nbrView_succ_apply_port]
          rw [Br.ext_iff']
          refine ⟨by simp [hU, j], ?_⟩
          funext c
          simp [U₂]
        · obtain ⟨c, rfl⟩ := Fin.exists_succAbove_eq hp
          rw [show k = (U₂ j).port by simp [hU], nbrView_succ_apply_succAbove]
          simp [hU]
      rw [hV, hU, Br.port_mk]

/-- **Theorem 2.1** (forward direction, used for all lower bounds). If `Pr` has white complexity at
most `t + 1`, then `R_B(Pr)` has black complexity at most `t`. -/
theorem theorem_2_1 {Pr : Problem L} {t : ℕ} (h : Pr.WhiteIn d (t + 1)) : (RB Pr).BlackIn d t := by
  obtain ⟨A, hA⟩ := h
  exact ⟨_, re_forward hA⟩

/-- **Theorem 2.1**, dual version: black complexity `t + 1` for `Pr` implies white complexity `t`
for `R_W(Pr)`. -/
theorem theorem_2_1_dual {Pr : Problem L} {t : ℕ} (h : Pr.BlackIn d (t + 1)) :
    (RW Pr).WhiteIn d t := by
  obtain ⟨A, hA⟩ := h
  exact ⟨_, re_forward hA⟩

/-! ### Relaxations -/

/-- `(Act', Pas')` is a relaxation of `(Act, Pas)` (for the active side): every active node can
relabel its own configuration in 0 rounds, so that any correct solution of `(Act, Pas)` becomes a
correct solution of `(Act', Pas')`. In the passive condition, the passive node's neighbour `k` holds
the configuration `G k` and is attached through its port `j k`. -/
def Relax (d : ℕ) (Act Pas : Set (Multiset L)) (Act' Pas' : Set (Multiset L')) : Prop :=
  ∃ ρ : (Fin (d + 1) → L) → Fin (d + 1) → L',
    (∀ g, mset g ∈ Act → mset (ρ g) ∈ Act') ∧
    ∀ (G : Fin (d + 1) → Fin (d + 1) → L) (j : Fin (d + 1) → Fin (d + 1)),
      (∀ k, mset (G k) ∈ Act) → mset (fun k => G k (j k)) ∈ Pas →
        mset (fun k => ρ (G k) (j k)) ∈ Pas'

theorem Solves.relax {t : ℕ} {A : View d t → Fin (d + 1) → L} {Act Pas : Set (Multiset L)}
    {Act' Pas' : Set (Multiset L')} (h : Solves A Act Pas) (hr : Relax d Act Pas Act' Pas') :
    ∃ A' : View d t → Fin (d + 1) → L', Solves A' Act' Pas' := by
  obtain ⟨ρ, h1, h2⟩ := hr
  exact ⟨fun V => ρ (A V), fun V => h1 _ (h.1 V),
    fun U => h2 (fun k => A (nbrView t U k)) (fun k => (U k).port) (fun k => h.1 _) (h.2 U)⟩

/-- `Pr'` is a black relaxation of `Pr`. -/
def Problem.BlackRelax (d : ℕ) (Pr : Problem L) (Pr' : Problem L') : Prop :=
  Relax d Pr.B Pr.W Pr'.B Pr'.W

/-- `Pr'` is a white relaxation of `Pr`. -/
def Problem.WhiteRelax (d : ℕ) (Pr : Problem L) (Pr' : Problem L') : Prop :=
  Relax d Pr.W Pr.B Pr'.W Pr'.B

theorem Problem.BlackIn.relax {Pr : Problem L} {Pr' : Problem L'} {t : ℕ} (h : Pr.BlackIn d t)
    (hr : Pr.BlackRelax d Pr') : Pr'.BlackIn d t := by
  obtain ⟨A, hA⟩ := h; exact hA.relax hr

theorem Problem.WhiteIn.relax {Pr : Problem L} {Pr' : Problem L'} {t : ℕ} (h : Pr.WhiteIn d t)
    (hr : Pr.WhiteRelax d Pr') : Pr'.WhiteIn d t := by
  obtain ⟨A, hA⟩ := h; exact hA.relax hr

/-- Relaxations of `R(Pr)` by *meanings*: each new label `ℓ'` stands for a set `φ ℓ'` of old labels.
If every universal configuration can be enlarged (port-wise) to the meaning of an allowed new
active configuration (`hA`), and every new passive configuration admitting a choice in the old
active constraint is allowed (`hP`), then we have a relaxation. This is how the paper proves
Lemmas 4.1–4.3 (via Lemma 2.4, Observations 2.2 and 2.5, and a renaming). -/
theorem relax_of_meaning [Inhabited L'] {Act Pas : Set (Multiset L)}
    {Act' Pas' : Set (Multiset L')} (φ : L' → Set L)
    (hA : ∀ g : Fin (d + 1) → Set L, mset g ∈ univC Pas →
      ∃ g' : Fin (d + 1) → L', mset g' ∈ Act' ∧ ∀ k, g k ⊆ φ (g' k))
    (hP : ∀ g' : Fin (d + 1) → L',
      (∃ f : Fin (d + 1) → L, (∀ k, f k ∈ φ (g' k)) ∧ mset f ∈ Act) → mset g' ∈ Pas') :
    Relax d (univC Pas) (exC Act) Act' Pas' := by
  classical
  let ρ : (Fin (d + 1) → Set L) → Fin (d + 1) → L' := fun g =>
    if h : mset g ∈ univC Pas then (hA g h).choose else fun _ => default
  have hρ : ∀ g, mset g ∈ univC Pas → mset (ρ g) ∈ Act' ∧ ∀ k, g k ⊆ φ (ρ g k) := by
    intro g h; simp only [ρ, h, ↓reduceDIte]; exact (hA g h).choose_spec
  refine ⟨ρ, fun g hg => (hρ g hg).1, fun G j hG hP0 => hP _ ?_⟩
  obtain ⟨f, hf, hfA⟩ := mset_mem_exC.1 hP0
  exact ⟨f, fun k => (hρ _ (hG k)).2 (j k) (hf k), hfA⟩

end TightBipartiteMatching
