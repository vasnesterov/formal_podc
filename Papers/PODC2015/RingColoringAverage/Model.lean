import Mathlib
import Cslib.Foundations.Data.Nat.LogStar

/-!
# The LOCAL model on rings with variable (per-node) radii

Model of [Feuilloley, *Brief Announcement: Average Complexity for the LOCAL Model*, PODC 2015].

* `IdRing`: an **oriented** ring with `n ≥ 3` nodes. Nodes sit at positions `v : ℤ` taken modulo
  `n`; node `v` carries the identifier `id v : ℕ`, `id` is `n`-periodic and injective modulo `n`.
  Node `v + 1` is the right neighbour of `v`.
* `IdRing.view R v : ℤ → ℕ`: the view of node `v`, `j ↦ id (v + j)`. Its restriction to
  `[-r, r]` is the information node `v` has gathered after `r` rounds (the ball of radius `r`;
  for `2r + 1 > n` the ball wraps around and the view repeats with period `n`).
* `Alg C`: a deterministic algorithm that does not know `n`. At radius `r` it either continues
  (`none`) or stops with output `c : C` (`some c`); the decision at radius `r` depends only on the
  view restricted to `[-r, r]` (`Alg.out_congr`).
* `Alg.rad f`: the radius at which the algorithm stops on view `f` (the paper's `r(v)`), and
  `Alg.output f` its output. `Alg.radAt R v`, `Alg.outAt R v` evaluate them at node `v` of `R`.
* `Alg.Valid A`: `A` stops at every node of every ring and its outputs form a proper colouring
  (adjacent nodes output different colours). With `C = Fin 3` this is a 3-colouring algorithm.
* `Alg.IsMinimal A` (paper, §3): `A` is valid and no valid algorithm uses at most the radius of
  `A` everywhere and a strictly smaller radius somewhere.

Orientation is a modelling choice that only strengthens lower bounds: an algorithm for unoriented
rings is in particular an algorithm for oriented rings with the same radii.
-/

namespace Podc.RingColoringAverage

/-- An oriented ring of `n ≥ 3` nodes at positions `ℤ` (modulo `n`) with pairwise distinct
natural identifiers. -/
structure IdRing where
  /-- Number of nodes. -/
  n : ℕ
  three_le : 3 ≤ n
  /-- Identifier of the node at position `v` (positions are taken modulo `n`). -/
  id : ℤ → ℕ
  periodic : Function.Periodic id n
  inj : ∀ i j, id i = id j → (n : ℤ) ∣ i - j

/-- `f` and `g` agree on the window `[-s, s]`. -/
def AgreeOn (s : ℕ) (f g : ℤ → ℕ) : Prop := ∀ j : ℤ, |j| ≤ s → f j = g j

theorem AgreeOn.mono {s t : ℕ} {f g : ℤ → ℕ} (h : AgreeOn t f g) (hst : s ≤ t) : AgreeOn s f g :=
  fun j hj => h j (hj.trans (by exact_mod_cast hst))

theorem AgreeOn.symm {s : ℕ} {f g : ℤ → ℕ} (h : AgreeOn s f g) : AgreeOn s g f :=
  fun j hj => (h j hj).symm

theorem AgreeOn.trans {s : ℕ} {f g h : ℤ → ℕ} (h₁ : AgreeOn s f g) (h₂ : AgreeOn s g h) :
    AgreeOn s f h :=
  fun j hj => (h₁ j hj).trans (h₂ j hj)

namespace IdRing

variable (R : IdRing)

/-- The view of node `v`: the identifier at offset `j` is `id (v + j)`. -/
def view (v : ℤ) : ℤ → ℕ := fun j => R.id (v + j)

@[simp] theorem view_apply (v j : ℤ) : R.view v j = R.id (v + j) := rfl

theorem n_pos : 0 < R.n := by have := R.three_le; omega

theorem id_add_mul (j m : ℤ) : R.id (j + m * R.n) = R.id j := by
  simpa using R.periodic.int_mul m j

theorem id_eq_iff {i j : ℤ} : R.id i = R.id j ↔ (R.n : ℤ) ∣ i - j := by
  refine ⟨R.inj i j, fun ⟨m, hm⟩ => ?_⟩
  have : i = j + m * R.n := by linarith
  rw [this, R.id_add_mul]

/-- Two identifiers at distance less than `n` are distinct. -/
theorem id_ne_of_lt {i j : ℤ} (hij : i ≠ j) (h : |i - j| < R.n) : R.id i ≠ R.id j := by
  intro he
  obtain ⟨m, hm⟩ := (R.id_eq_iff).1 he
  rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
  · have : (m : ℤ) * R.n ≤ -R.n := by nlinarith [R.n_pos]
    rw [abs_lt] at h; nlinarith
  · subst hm0; apply hij; linarith
  · have : (R.n : ℤ) ≤ (m : ℤ) * R.n := by nlinarith [R.n_pos]
    rw [abs_lt] at h; nlinarith

/-- A ring whose identifiers, read from position `0`, are the entries of a duplicate-free list
of length at least `3`. -/
noncomputable def ofList (l : List ℕ) (hl : l.Nodup) (h3 : 3 ≤ l.length) : IdRing where
  n := l.length
  three_le := h3
  id j := l.getD (j % l.length).toNat 0
  periodic j := by simp
  inj i j h := by
    have hn : (0 : ℤ) < l.length := by omega
    have hi0 := Int.emod_nonneg i hn.ne'
    have hj0 := Int.emod_nonneg j hn.ne'
    have hi1 := Int.emod_lt_of_pos i hn
    have hj1 := Int.emod_lt_of_pos j hn
    have hi : (i % l.length).toNat < l.length := by omega
    have hj : (j % l.length).toNat < l.length := by omega
    simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
    have := (hl.getElem_inj_iff).1 h
    have h' : i % l.length = j % l.length := by omega
    exact Int.ModEq.dvd h'.symm

theorem ofList_id (l : List ℕ) (hl : l.Nodup) (h3 : 3 ≤ l.length) (j : ℕ) (hj : j < l.length) :
    (ofList l hl h3).id j = l[j] := by
  have : ((j : ℤ) % (l.length : ℤ)).toNat = j := by
    rw [Int.emod_eq_of_lt (by omega) (by omega)]; simp
  simp [ofList, this, hj]

@[simp] theorem ofList_n (l : List ℕ) (hl : l.Nodup) (h3 : 3 ≤ l.length) :
    (ofList l hl h3).n = l.length := rfl

end IdRing

/-- A deterministic LOCAL algorithm on rings with outputs in `C`, not knowing `n`: at radius `r`
with view `f` it continues (`none`) or stops and outputs `c` (`some c`). The decision at radius
`r` depends only on the view restricted to `[-r, r]`. -/
structure Alg (C : Type*) where
  /-- Decision at radius `r` on view `f`. -/
  out : ℕ → (ℤ → ℕ) → Option C
  out_congr : ∀ r f g, AgreeOn r f g → out r f = out r g

namespace Alg

variable {C : Type*} (A : Alg C)

/-- The algorithm stops at some radius on view `f`. -/
def Stops (f : ℤ → ℕ) : Prop := ∃ r, (A.out r f).isSome

/-- The radius at which the algorithm stops on view `f` (the paper's `r(v)`; `0` if it never
stops, which does not happen for valid algorithms on views of ring nodes). -/
noncomputable def rad (f : ℤ → ℕ) : ℕ := sInf {r | (A.out r f).isSome}

/-- The output on view `f`. -/
noncomputable def output [Inhabited C] (f : ℤ → ℕ) : C := (A.out (A.rad f) f).getD default

/-- Radius of node `v` of ring `R`. -/
noncomputable def radAt (R : IdRing) (v : ℤ) : ℕ := A.rad (R.view v)

/-- Output of node `v` of ring `R`. -/
noncomputable def outAt [Inhabited C] (R : IdRing) (v : ℤ) : C := A.output (R.view v)

/-- A valid colouring algorithm (with colours `C`): it stops at every node of every ring and
adjacent nodes output distinct colours. -/
structure Valid [Inhabited C] : Prop where
  stops : ∀ (R : IdRing) (v : ℤ), A.Stops (R.view v)
  proper : ∀ (R : IdRing) (v : ℤ), A.outAt R v ≠ A.outAt R (v + 1)

/-- Paper, §3: `A` is *minimal* if it is valid and there is no valid algorithm `A'` that uses at
most the radius of `A` at every node of every ring and a strictly smaller one somewhere. -/
def IsMinimal [Inhabited C] : Prop :=
  A.Valid ∧ ∀ B : Alg C, B.Valid → (∀ R v, B.radAt R v ≤ A.radAt R v) →
    ∀ R v, B.radAt R v = A.radAt R v

variable {A}

theorem rad_spec {f : ℤ → ℕ} (h : A.Stops f) : (A.out (A.rad f) f).isSome :=
  Nat.sInf_mem (s := {r | (A.out r f).isSome}) h

theorem rad_le {f : ℤ → ℕ} {r : ℕ} (h : (A.out r f).isSome) : A.rad f ≤ r := Nat.sInf_le h

theorem out_eq_none_of_lt {f : ℤ → ℕ} {r : ℕ} (h : r < A.rad f) : A.out r f = none := by
  by_contra h'
  exact absurd (rad_le (Option.ne_none_iff_isSome.1 h')) (not_le.2 h)

theorem rad_le_iff {f : ℤ → ℕ} (h : A.Stops f) {t : ℕ} :
    A.rad f ≤ t ↔ ∃ s ≤ t, (A.out s f).isSome :=
  ⟨fun ht => ⟨_, ht, rad_spec h⟩, fun ⟨_, hs, h⟩ => (rad_le h).trans hs⟩

theorem lt_rad_iff {f : ℤ → ℕ} (h : A.Stops f) {t : ℕ} :
    t < A.rad f ↔ ∀ s ≤ t, A.out s f = none := by
  rw [← not_le, rad_le_iff h]; simp

/-- If `f` and `g` agree on `[-s, s]` and the algorithm stops on `f` within radius `s`, then it
stops on `g` at the same radius with the same output. -/
theorem rad_eq_of_agreeOn {f g : ℤ → ℕ} {s : ℕ} (hfg : AgreeOn s f g) (hf : A.Stops f)
    (hs : A.rad f ≤ s) : A.Stops g ∧ A.rad g = A.rad f ∧ A.out (A.rad g) g = A.out (A.rad f) f := by
  have key : ∀ t ≤ s, A.out t f = A.out t g := fun t ht => A.out_congr t f g (hfg.mono ht)
  have hg : A.Stops g := ⟨A.rad f, by rw [← key _ hs]; exact rad_spec hf⟩
  have h1 : A.rad g ≤ A.rad f := rad_le (by rw [← key _ hs]; exact rad_spec hf)
  have h2 : A.rad f ≤ A.rad g := rad_le (by rw [key _ (h1.trans hs)]; exact rad_spec hg)
  have he : A.rad g = A.rad f := le_antisymm h1 h2
  exact ⟨hg, he, by rw [he, key _ hs]⟩

theorem output_eq_of_agreeOn [Inhabited C] {f g : ℤ → ℕ} {s : ℕ} (hfg : AgreeOn s f g)
    (hf : A.Stops f) (hs : A.rad f ≤ s) : A.output g = A.output f := by
  obtain ⟨-, -, h⟩ := rad_eq_of_agreeOn hfg hf hs
  simp [output, h]

/-- If `f` and `g` agree on `[-s, s]` and the algorithm does not stop on `f` up to radius `s`,
it does not stop on `g` up to radius `s` either. -/
theorem out_eq_none_of_agreeOn {f g : ℤ → ℕ} {s : ℕ} (hfg : AgreeOn s f g)
    (hf : ∀ t ≤ s, A.out t f = none) : ∀ t ≤ s, A.out t g = none := fun t ht => by
  rw [← A.out_congr t f g (hfg.mono ht)]; exact hf t ht

/-- Relabel the outputs along `e`. -/
def map {D : Type*} (A : Alg C) (e : C → D) : Alg D where
  out r f := (A.out r f).map e
  out_congr r f g h := by rw [A.out_congr r f g h]

theorem rad_map {D : Type*} (e : C → D) (f : ℤ → ℕ) : (A.map e).rad f = A.rad f := by
  simp [rad, map]

theorem stops_map {D : Type*} (e : C → D) {f : ℤ → ℕ} : (A.map e).Stops f ↔ A.Stops f := by
  simp [Stops, map]

theorem output_map [Inhabited C] {D : Type*} [Inhabited D] (e : C → D) {f : ℤ → ℕ}
    (hf : A.Stops f) : (A.map e).output f = e (A.output f) := by
  have := rad_spec hf
  simp only [output, rad_map]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 this
  simp [map, hc]

/-- An injective relabelling of a valid colouring algorithm is valid (e.g. a 3-colouring
algorithm is a 4-colouring algorithm). -/
theorem Valid.map [Inhabited C] {D : Type*} [Inhabited D] {e : C → D} (he : Function.Injective e)
    (hA : A.Valid) : (A.map e).Valid where
  stops R v := (stops_map e).2 (hA.stops R v)
  proper R v := by
    simp only [outAt, output_map e (hA.stops R _)]
    exact fun h => hA.proper R v (he h)

end Alg

end Podc.RingColoringAverage
