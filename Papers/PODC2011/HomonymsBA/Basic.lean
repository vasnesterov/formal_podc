-- CSLib candidate: Cslib/Computability/Distributed/Homonyms/Basic.lean
import Papers.PODC2011.HomonymsBA.Model

/-!
# Byzantine agreement with homonyms: basic API

* `Run.st_transfer`: the indistinguishability principle (two runs that give a set of processes the
  same transitions give them the same states).
* Inclusions between models: synchronous runs are partially synchronous, restricted adversaries
  are unrestricted, innumerate algorithms are numerate (`Solvable.sync_of_psync`, …).
* `Solvable.mono_ids`: more identifiers never hurt (an algorithm for `ℓ` identifiers runs with
  `ℓ' ≥ ℓ` identifiers by merging identifiers through a surjection `Fin ℓ' → Fin ℓ`). This is the
  "it suffices to prove it for `ℓ = 3t`" step of Proposition 1.
-/

namespace Podc.HomonymsBA

open Finset

variable {ℓ : ℕ} {V M S : Type*} (A : Algorithm ℓ V M S)

namespace Run

variable {P : Type*} [Fintype P] (R : Run P ℓ V M)

/-- **Indistinguishability.** If, as long as the processes of `X` have the same states in `R` as
their images under `e` in `R'`, they also make the same transitions, then they have the same
states up to round `T`. -/
theorem st_transfer {Q : Type*} [Fintype Q] (R' : Run Q ℓ V M) (e : P → Q) (X : Set P) (T : ℕ)
    (h0 : ∀ p ∈ X, R.id p = R'.id (e p) ∧ R.inp p = R'.inp (e p))
    (hstep : ∀ r < T, (∀ p ∈ X, R.st A r p = R'.st A r (e p)) → ∀ p ∈ X,
      A.step (R.st A r p) (R.inbox A r p) = A.step (R'.st A r (e p)) (R'.inbox A r (e p))) :
    ∀ r ≤ T, ∀ p ∈ X, R.st A r p = R'.st A r (e p) := by
  intro r
  induction r with
  | zero => intro _ p hp; simp [(h0 p hp).1, (h0 p hp).2]
  | succ r ih =>
    intro hr p hp
    rw [st_succ, st_succ]
    exact hstep r (by omega) (ih (by omega)) p hp

/-- `st_transfer` for all rounds. -/
theorem st_transfer_all {Q : Type*} [Fintype Q] (R' : Run Q ℓ V M) (e : P → Q) (X : Set P)
    (h0 : ∀ p ∈ X, R.id p = R'.id (e p) ∧ R.inp p = R'.inp (e p))
    (hstep : ∀ r, (∀ p ∈ X, R.st A r p = R'.st A r (e p)) → ∀ p ∈ X,
      A.step (R.st A r p) (R.inbox A r p) = A.step (R'.st A r (e p)) (R'.inbox A r (e p))) :
    ∀ r, ∀ p ∈ X, R.st A r p = R'.st A r (e p) :=
  fun r => R.st_transfer A R' e X r h0 (fun r _ => hstep r) r le_rfl

lemma decides_of_st {Q : Type*} [Fintype Q] {R' : Run Q ℓ V M} {p : P} {q : Q}
    (h : ∀ r, R.st A r p = R'.st A r q) {v : V} : R.Decides A p v ↔ R'.Decides A q v := by
  simp [Decides, h]

open Classical in
lemma inbox_eq (r : ℕ) (p : P) : R.inbox A r p =
    (∑ q ∈ univ.filter (fun q => q ∉ R.byz ∧ ¬ R.drop r q p), R.msgFrom A (R.st A r q) q p) +
      R.adv r p := by
  unfold inbox inboxWith; congr

lemma mem_msgFrom {s : S} {q p : P} {x : Fin ℓ × M} :
    x ∈ R.msgFrom A s q p ↔ x.1 = R.id q ∧ A.send s (R.id p) = some x.2 := by
  obtain ⟨j, m⟩ := x
  unfold msgFrom
  rw [mem_oms]
  cases h : A.send s (R.id p) <;> simp [eq_comm]

/-- Synchronous admissible runs are partially synchronous admissible runs. -/
lemma Admissible.psync {t : ℕ} {π : Power} {R : Run P ℓ V M} (h : R.Admissible t .sync π) :
    R.Admissible t .psync π :=
  ⟨h.1, (fun h' => by cases h'), h.2.2⟩

/-- Restricted admissible runs are unrestricted admissible runs. -/
lemma Admissible.unrestricted {t : ℕ} {τ : Timing} {R : Run P ℓ V M}
    (h : R.Admissible t τ .restricted) : R.Admissible t τ .unrestricted :=
  ⟨h.1, h.2.1, fun h' => nomatch h'⟩

end Run

theorem Solves.sync {π : Power} {n t : ℕ} (h : Solves .psync π n t A) : Solves .sync π n t A :=
  fun P _ _ hP R hR => h P hP R hR.psync

theorem Solves.restricted {τ : Timing} {n t : ℕ} (h : Solves τ .unrestricted n t A) :
    Solves τ .restricted n t A :=
  fun P _ _ hP R hR => h P hP R hR.unrestricted

/-- Partially synchronous solvability implies synchronous solvability. -/
theorem Solvable.sync_of_psync {π κ n ℓ t V} (h : Solvable .psync π κ n ℓ t V) :
    Solvable .sync π κ n ℓ t V := by
  obtain ⟨M, S, A, hk, hA⟩ := h
  exact ⟨M, S, A, hk, hA.sync A⟩

/-- Solvability against unrestricted Byzantine processes implies it against restricted ones. -/
theorem Solvable.restricted_of_unrestricted {τ κ n ℓ t V} (h : Solvable τ .unrestricted κ n ℓ t V) :
    Solvable τ .restricted κ n ℓ t V := by
  obtain ⟨M, S, A, hk, hA⟩ := h
  exact ⟨M, S, A, hk, hA.restricted A⟩

/-- Innumerate solvability implies numerate solvability. -/
theorem Solvable.numerate_of_innumerate {τ π n ℓ t V} (h : Solvable τ π .innumerate n ℓ t V) :
    Solvable τ π .numerate n ℓ t V := by
  obtain ⟨M, S, A, -, hA⟩ := h
  exact ⟨M, S, A, trivial, hA⟩

/-! ### More identifiers never hurt -/

section Merge

variable {ℓ' : ℕ} (f : Fin ℓ' → Fin ℓ)

/-- Run `A` (for `ℓ` identifiers) with `ℓ'` identifiers, reading identifier `i` as `f i`. -/
def Algorithm.merge : Algorithm ℓ' V M S where
  init i v := A.init (f i) v
  send s j := A.send s (f j)
  step s m := A.step s (m.map fun x => (f x.1, x.2))
  decide := A.decide

lemma Algorithm.Innumerate.merge {A : Algorithm ℓ V M S} (hA : A.Innumerate) :
    (A.merge f).Innumerate := by
  intro s m m' h
  apply hA
  intro x
  simp only [Multiset.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => ⟨y, (h y).1 hy, e⟩, fun ⟨y, hy, e⟩ => ⟨y, (h y).2 hy, e⟩⟩

namespace Run

variable {P : Type*} [Fintype P]

/-- The run of `A` (with `ℓ` identifiers) corresponding to a run of `A.merge f`. -/
def unmerge (R : Run P ℓ' V M) : Run P ℓ V M where
  id p := f (R.id p)
  byz := R.byz
  inp := R.inp
  gst := R.gst
  drop := R.drop
  adv r p := (R.adv r p).map fun x => (f x.1, x.2)

omit [Fintype P] in
lemma multiset_map_finset_sum {ι α β : Type*} (g : α → β) (s : Finset ι) (F : ι → Multiset α) :
    (∑ i ∈ s, F i).map g = ∑ i ∈ s, (F i).map g :=
  map_sum (Multiset.mapAddMonoidHom g) F s

theorem st_unmerge (R : Run P ℓ' V M) : ∀ r, (R.unmerge f).st A r = R.st (A.merge f) r := by
  intro r
  induction r with
  | zero => rfl
  | succ r ih =>
    funext p
    rw [st_succ, st_succ, ih]
    change A.step _ _ = A.step _ _
    congr 1
    classical
    rw [inbox_eq, inbox_eq, Multiset.map_add, multiset_map_finset_sum, ih]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [msgFrom, unmerge, Algorithm.merge, oms]
    generalize A.send _ _ = o
    cases o <;> simp

lemma card_filter_map_fst {ι : Type*} [Fintype ι] [DecidableEq ι] (m : Multiset (ι × M))
    (j : Fin ℓ) (g : ι → Fin ℓ) :
    ((m.map fun x => (g x.1, x.2)).filter (·.1 = j)).card =
      ∑ j' ∈ univ.filter (g · = j), (m.filter (·.1 = j')).card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    rw [Multiset.map_cons, Multiset.filter_cons]
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib, ← ih]
    congr 1
    by_cases hx : g x.1 = j
    · rw [Finset.sum_eq_single_of_mem x.1 (by simp [hx])]
      · simp [hx]
      · intro b _ hb; simp [Ne.symm hb]
    · rw [Finset.sum_eq_zero]
      · simp [hx]
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have : x.1 ≠ b := fun e => hx (e ▸ hb)
        simp [this]

theorem admissible_unmerge {t : ℕ} {τ : Timing} {π : Power} (hf : Function.Surjective f)
    {R : Run P ℓ' V M} (hR : R.Admissible t τ π) : (R.unmerge f).Admissible t τ π := by
  classical
  obtain ⟨hv, hs, hr⟩ := hR
  refine ⟨⟨hf.comp hv.surj, hv.card_byz, ?_, hv.no_drop⟩, hs, ?_⟩
  · intro r p x hx
    simp only [unmerge, Multiset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨b, hb, e⟩ := hv.adv_id r p y hy
    exact ⟨b, hb, by simp [unmerge, e]⟩
  · intro hπ r p j
    have h1 := hr hπ
    have e1 : (((R.unmerge f).adv r p).filter (·.1 = j)).card =
        ∑ j' ∈ univ.filter (f · = j), ((R.adv r p).filter (·.1 = j')).card :=
      card_filter_map_fst _ j f
    have e2 : (R.byz.filter (fun b => f (R.id b) = j)).card =
        ∑ j' ∈ univ.filter (f · = j), (R.byz.filter (R.id · = j')).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun b => R.id b) (t := univ.filter (f · = j))]
      · refine Finset.sum_congr rfl fun j' hj' => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
        congr 1; ext b
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hb, -⟩, e⟩; exact ⟨hb, e⟩
        · rintro ⟨hb, e⟩; exact ⟨⟨hb, by rw [e, hj']⟩, e⟩
      · intro b hb
        rw [Finset.mem_coe, Finset.mem_filter] at hb
        simpa using hb.2
    show _ ≤ (R.byz.filter (fun b => f (R.id b) = j)).card
    rw [e1, e2]
    exact Finset.sum_le_sum fun j' _ => h1 r p j'

end Run

theorem Solves.merge {τ : Timing} {π : Power} {n t : ℕ} (hf : Function.Surjective f)
    (h : Solves τ π n t A) : Solves τ π n t (A.merge f) := by
  intro P _ _ hP R hR
  have hBA := h P hP (R.unmerge f) (Run.admissible_unmerge f hf hR)
  have hst := Run.st_unmerge A f R
  have hdec : ∀ p v, (R.unmerge f).Decides A p v ↔ R.Decides (A.merge f) p v := by
    intro p v; simp [Run.Decides, hst, Algorithm.merge]
  exact ⟨fun p hp => by simpa [hdec] using hBA.termination p hp,
    fun p hp q hq v w h1 h2 => hBA.agreement p hp q hq v w ((hdec _ _).2 h1) ((hdec _ _).2 h2),
    fun v hv p hp w h1 => hBA.validity v hv p hp w ((hdec _ _).2 h1)⟩

end Merge

/-- A surjection `Fin ℓ' → Fin ℓ` for `0 < ℓ ≤ ℓ'`. -/
def finCollapse {ℓ ℓ' : ℕ} (h0 : 0 < ℓ) (i : Fin ℓ') : Fin ℓ :=
  if h : i.val < ℓ then ⟨i.val, h⟩ else ⟨0, h0⟩

lemma finCollapse_surjective {ℓ ℓ' : ℕ} (h0 : 0 < ℓ) (h : ℓ ≤ ℓ') :
    Function.Surjective (finCollapse (ℓ' := ℓ') h0) := by
  intro j
  refine ⟨⟨j.val, by omega⟩, ?_⟩
  simp [finCollapse, j.isLt]

/-- **More identifiers never hurt**: solvability with `ℓ` identifiers implies solvability with
`ℓ' ≥ ℓ` identifiers, in every model. -/
theorem Solvable.mono_ids {τ π κ n ℓ t V} {ℓ' : ℕ} (h0 : 0 < ℓ) (hl : ℓ ≤ ℓ')
    (h : Solvable τ π κ n ℓ t V) : Solvable τ π κ n ℓ' t V := by
  obtain ⟨M, S, A, hk, hA⟩ := h
  refine ⟨M, S, A.merge (finCollapse h0), ?_, hA.merge A _ (finCollapse_surjective h0 hl)⟩
  cases κ with
  | numerate => trivial
  | innumerate => exact Algorithm.Innumerate.merge _ hk

end Podc.HomonymsBA
