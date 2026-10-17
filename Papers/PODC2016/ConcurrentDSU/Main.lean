import Papers.PODC2016.ConcurrentDSU.WaitFree

/-!
# Main results of Section 3 of Jayanti–Tarjan (PODC 2016)

* `lemma_3_1` — in every reachable configuration a non-root has a parent with a larger id
  (roots point to themselves by definition); every step either leaves the parent pointers
  unchanged, or *links* a root `a` below a node `b` of another tree with a larger id, or
  (in a `Find`) replaces the parent of a non-root `a` by a node of the same tree whose id is
  larger than that of the old parent (so the partition into trees is unchanged).
* `theorem_3_4` — the concurrent implementation (Algorithms 2 and 3 with any of the three `Find`s,
  Algorithms 1, 4, 5) is linearizable and wait-free.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentDSU

open Cslib.SharedMemory

variable {E : Type} [Fintype E] [DecidableEq E] {P : Type} [DecidableEq P]
variable {K : FindKind} {key : E → ℕ}

/-- The three possible effects of a step on the parent pointers. -/
def MemStep (key : E → ℕ) (m m' : E → E) : Prop :=
  m' = m ∨
  (∃ a b, m a = a ∧ key a < key b ∧ rootOf m b ≠ a ∧ m' = Function.update m a b) ∨
  (∃ a w, m a ≠ a ∧ key (m a) < key w ∧ rootOf m w = rootOf m a ∧ m' = Function.update m a w)

lemma fRes_memStep {m : E → E} (hg : Good key m) {s : E} {fs : FS E} (hf : FInv K key m s fs) :
    MemStep key m (fRes K fs m).2 := by
  cases fs with
  | tst u => exact Or.inl rfl
  | adv u => exact Or.inl rfl
  | rdP u i => exact Or.inl rfl
  | rdG u v i => exact Or.inl rfl
  | cas u v w i =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    show MemStep key m (if m u = v then Function.update m u w else m)
    split_ifs with hmu
    · right; right
      have hvu : v ≠ u := by
        intro h6'; subst h6'
        have hr : rootOf m w = v := by
          unfold same at h4 h3; rw [h4, h3, rootOf_of_fixed hmu]
        have := key_le_rootOf hg w; rw [hr] at this; omega
      refine ⟨u, w, by rw [hmu]; exact hvu, by rw [hmu]; exact h5, ?_, rfl⟩
      unfold same at h4; rw [h4, ← hmu, rootOf_apply hg]
    · exact Or.inl rfl

lemma tauRes_memStep (hkey : Function.Injective key) {m : E → E} (hg : Good key m)
    {o : DSUOp E} {l l' : Loc E} {m' : E → E} (hl : LocInv K key m (some o) l)
    (h : tauRes K key l m = some (l', m')) : MemStep key m m' := by
  have hroot : ∀ {a b : E}, key a < key b → rootOf m b ≠ a := fun {a b} hk hr => by
    have := key_le_rootOf hg b; rw [hr] at this; omega
  cases l with
  | idle => exact hl.elim
  | done r => simp [tauRes, act] at h
  | fu b fs v =>
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fRes_memStep hg hl.2.1
  | fv b u fs =>
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fRes_memStep hg hl.2.2
  | chk u v =>
    simp only [tauRes, act, ptr_read, Function.update_eq_self, Option.some.injEq,
      Prod.mk.injEq] at h
    exact Or.inl h.2.symm
  | lnk u v =>
    have hk : key u ≠ key v := fun h => hl.2.2.2 (hkey h)
    by_cases hlt : key u < key v
    · simp only [tauRes, act, hlt, ite_true, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      by_cases hr : m u = u
      · simp only [hr, ite_true]
        exact Or.inr (Or.inl ⟨u, v, hr, hlt, hroot hlt, rfl⟩)
      · simp only [hr, ite_false, Function.update_eq_self]; exact Or.inl rfl
    · have hlt' : key v < key u := by omega
      simp only [tauRes, act, hlt, ite_false, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      by_cases hr : m v = v
      · simp only [hr, ite_true]
        exact Or.inr (Or.inl ⟨v, u, hr, hlt', hroot hlt', rfl⟩)
      · simp only [hr, ite_false, Function.update_eq_self]; exact Or.inl rfl

/-- **Lemma 3.1.** In every reachable configuration, a node that is not a root has a parent
with a larger id. Every step leaves the parent pointers unchanged, or links a root `a` below a
node `b` (of larger id) of another tree, or replaces the parent of a non-root `a` by a node `w`
of the same tree with an id larger than that of the old parent. -/
theorem lemma_3_1 (hkey : Function.Injective key) {α : List (Label P (dsu E))}
    {C : Config (dsu E) (Ptr E) P (Loc E)} (h : (dsuImpl K key P).run α = some C) :
    (∀ x, C.mem x ≠ x → key x < key (C.mem x)) ∧
    ∀ ℓ C', (dsuImpl K key P).step C ℓ = some C' → MemStep key C.mem C'.mem := by
  have hI := linv_of_run hkey h
  refine ⟨fun x hx => (hI.good x).resolve_left hx, fun ℓ C' hs => ?_⟩
  cases ℓ with
  | inv p o => exact Or.inl (Impl.step_inv hs).2.2.2.2
  | ret p r => exact Or.inl (Impl.step_ret hs).2.2.1
  | tau p =>
    obtain ⟨hp, hres, -, -⟩ := step_tau_tauRes hs
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
    have hl := hI.loc p
    rw [ho] at hl
    exact tauRes_memStep hkey hI.good hl hres

/-- **Theorem 3.4.** The concurrent implementation of disjoint set union (Algorithms 2 and 3,
with `Find` by Algorithm 1, 4 or 5, linking by node ids) is linearizable and wait-free, for any
set of processes and any injective assignment of ids. -/
theorem theorem_3_4 (K : FindKind) (hkey : Function.Injective key) (P : Type) [DecidableEq P] :
    (dsuImpl K key P).Linearizable ∧ (dsuImpl K key P).WaitFree :=
  ⟨linearizable hkey, waitFree hkey⟩

end Podc.ConcurrentDSU
