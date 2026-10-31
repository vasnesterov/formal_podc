import Papers.PODC2017.MemoryAnonymousCoordination.ConsensusSteps

/-!
# Figure 2: the lock invariant

`Lock π n w C T` says that the value `w` is *locked* in the configuration `C`: from now on every
process that completes a collect adopts `w`, except the "token holders" `T`, each of which may
still write one value different from `w`:

* every process about to write a value `≠ w` is in `T`;
* every process `p ∉ T` in the middle of a collect has fewer than `n − |T|` entries with `val ≠ w`
  in its virtual view (entries read so far + current contents of the registers not yet read);
* fewer than `n − |T|` registers have `val ≠ w`.

The lock is preserved by every step (`lock_step`; `T` only shrinks), it is established when all
registers hold `(p, y)` and `p` starts a collect (`lock_establish`), and two locked values are
equal (`Lock.eq`): each forces at least `n` of the `2n − 1` registers to hold it.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Consensus

open Cslib.SharedMemory

variable {P V : Type} {m : ℕ} [DecidableEq V] [DecidableEq P] [Inhabited V]
  {n : ℕ} {sel : P → V → (Fin m → Option (P × V)) → Fin m} {π : P → Equiv.Perm (Fin m)}

/-- The value `w` is locked in `C`, with token holders `T` (see the module docstring). -/
structure Lock (π : P → Equiv.Perm (Fin m)) (n : ℕ) (w : V) (C : Cfg P V m) (T : Finset P) :
    Prop where
  writers : ∀ p x j b, C.loc p = .write x j b → x ≠ w → p ∈ T
  collectors : ∀ p x k view, C.loc p = .collect x k view → p ∉ T →
    nonW (mixed (π p) k view C.mem) w + T.card < n
  mem : nonW C.mem w + T.card < n

/-- Two locked values are equal. -/
lemma Lock.eq (hm : m + 1 = 2 * n) {C : Cfg P V m} {w w' : V} {T T' : Finset P}
    (h : Lock π n w C T) (h' : Lock π n w' C T') : w = w' :=
  eq_of_nonW_lt hm (f := C.mem) (by have := h.mem; omega) (by have := h'.mem; omega)

lemma startCollect_eq (h : 0 < m) (x : V) :
    (startCollect x : Loc P V m) = .collect x ⟨0, h⟩ (fun _ => none) := by
  simp [startCollect, h]

lemma pos_of_hm (hm : m + 1 = 2 * n) : 0 < m := by omega

lemma nonW_write_le {f g : Fin m → Option (P × V)} {w : V} {e : Option (P × V)} (j₀ : Fin m)
    (h : ∀ j, g j = f j ∨ (g j = e ∧ j = j₀)) :
    nonW g w ≤ nonW f w + (if val e = some w then 0 else 1) := by
  split_ifs with he
  · apply nonW_le; intro j
    rcases h j with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (by rw [h, he])
  · apply nonW_le_succ j₀; intro j hj
    rcases h j with h | ⟨-, h⟩
    · exact h
    · exact absurd h hj

/-- **The lock is preserved by every step.** -/
lemma lock_step (hm : m + 1 = 2 * n) {C C' : Cfg P V m} {ℓ : Label P (taskObj V V)} {w : V}
    {T : Finset P} (hL : Lock π n w C T) (h : (I n sel π).step C ℓ = some C') :
    ∃ T', Lock π n w C' T' := by
  have hm0 := pos_of_hm hm
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, hmem, hloc⟩ := inv_cases h
    refine ⟨T, ⟨?_, ?_, ?_⟩⟩
    · intro q x j b hq hx
      rw [hloc, Function.update_apply] at hq
      split_ifs at hq with hqp
      · simp [startCollect, hm0] at hq
      · exact hL.writers q x j b hq hx
    · intro q x k view hq hT
      rw [hloc, Function.update_apply] at hq
      split_ifs at hq with hqp
      · subst hqp
        simp only [startCollect, hm0, ↓reduceDIte] at hq
        obtain ⟨-, rfl, -⟩ := hq
        rw [hmem, mixed_zero _ _ _ _ rfl, nonW_comp]
        exact hL.mem
      · rw [hmem]; exact hL.collectors q x k view hq hT
    · rw [hmem]; exact hL.mem
  | ret p r =>
    obtain ⟨-, -, -, hmem, hloc⟩ := ret_cases h
    refine ⟨T, ⟨?_, ?_, ?_⟩⟩
    · intro q x j b hq hx
      rw [hloc, Function.update_apply] at hq
      split_ifs at hq with hqp
      · exact hL.writers q x j b hq hx
    · intro q x k view hq hT
      rw [hloc, Function.update_apply] at hq
      split_ifs at hq with hqp
      rw [hmem]; exact hL.collectors q x k view hq hT
    · rw [hmem]; exact hL.mem
  | tau p =>
    obtain ⟨-, -, hcase⟩ := tau_cases h
    rcases hcase with ⟨x, k, view, hl, hmem, hloc⟩ | ⟨x, j, b, hl, hmem, hloc⟩
    · -- a read
      refine ⟨T, ⟨?_, ?_, ?_⟩⟩
      · intro q x' j' b' hq hx
        rw [hloc, Function.update_apply] at hq
        split_ifs at hq with hqp
        · subst hqp
          by_contra hT
          simp only [afterRead] at hq
          split_ifs at hq with hk
          simp only [finish, Loc.write.injEq] at hq
          obtain ⟨rfl, -, -⟩ := hq
          apply hx
          apply adopt_of_nonW_lt hm
          rw [mixed_last _ _ _ _ hk]
          have := hL.collectors q x k view hl hT
          omega
        · exact hL.writers q x' j' b' hq hx
      · intro q x' k' view' hq hT
        rw [hloc, Function.update_apply] at hq
        split_ifs at hq with hqp
        · subst hqp
          simp only [afterRead] at hq
          split_ifs at hq with hk
          · simp only [Loc.collect.injEq] at hq
            obtain ⟨rfl, rfl, rfl⟩ := hq
            rw [hmem, mixed_read _ _ _ _ hk]
            exact hL.collectors q x k view hl hT
          · simp [finish] at hq
        · rw [hmem]; exact hL.collectors q x' k' view' hq hT
      · rw [hmem]; exact hL.mem
    · -- a write of `(p, x)`
      have hT : (T.erase p).card + (if val (some (p, x)) = some w then 0 else 1) ≤ T.card := by
        split_ifs with hx
        · simpa using Finset.card_erase_le
        · simp only [val_some, Option.some.injEq] at hx
          rw [Finset.card_erase_add_one (hL.writers p x j b hl hx)]
      have hmemle : nonW C'.mem w ≤
          nonW C.mem w + (if val (some (p, x)) = some w then 0 else 1) := by
        rw [hmem]
        apply nonW_write_le (π p j)
        intro i; simp only [Function.update_apply]; split_ifs with hi
        · exact Or.inr ⟨rfl, hi⟩
        · exact Or.inl rfl
      have hmem' := hL.mem
      refine ⟨T.erase p, ⟨?_, ?_, ?_⟩⟩
      · intro q x' j' b' hq hx
        rw [hloc, Function.update_apply] at hq
        split_ifs at hq with hqp
        · simp only [afterWrite] at hq
          split_ifs at hq; simp [startCollect_eq hm0] at hq
        · exact Finset.mem_erase.2 ⟨hqp, hL.writers q x' j' b' hq hx⟩
      · intro q x' k' view' hq hTq
        rw [hloc, Function.update_apply] at hq
        split_ifs at hq with hqp
        · subst hqp
          simp only [afterWrite] at hq
          split_ifs at hq with hb
          rw [startCollect_eq hm0] at hq
          simp only [Loc.collect.injEq] at hq
          obtain ⟨-, rfl, -⟩ := hq
          rw [mixed_zero _ _ _ _ rfl, nonW_comp]
          omega
        · have hqT : q ∉ T := fun h => hTq (Finset.mem_erase.2 ⟨hqp, h⟩)
          have h1 := hL.collectors q x' k' view' hq hqT
          have h2 : nonW (mixed (π q) k' view' C'.mem) w ≤
              nonW (mixed (π q) k' view' C.mem) w +
                (if val (some (p, x)) = some w then 0 else 1) := by
            rw [hmem]
            apply nonW_write_le ((π q).symm (π p j))
            intro i
            rcases mixed_write (π q) k' view' C.mem (π p j) (some (p, x)) i with h | ⟨h, hi⟩
            · exact Or.inl h
            · exact Or.inr ⟨h, by rw [← hi]; simp⟩
          omega
      · omega

/-- **Establishing the lock**: if all registers hold `(p, y)` and `p` is at the start of a
collect, then `y` is locked, with token holders all other processes. -/
lemma lock_establish [Fintype P] (hcard : Fintype.card P ≤ n) {C : Cfg P V m} {p : P} {x : V}
    {k : Fin m} {view : Fin m → Option (P × V)} (hl : C.loc p = .collect x k view)
    (hk : k.val = 0) {y : V} (hall : ∀ j, C.mem (π p j) = some (p, y)) :
    Lock π n y C (Finset.univ.erase p) := by
  have hc : (Finset.univ.erase p).card + 1 = Fintype.card P :=
    Finset.card_erase_add_one (Finset.mem_univ p)
  have h0' : nonW (fun j => C.mem (π p j)) y = 0 := nonW_eq_zero (fun j => by rw [hall j]; rfl)
  have h0 : nonW C.mem y = 0 := by rw [← nonW_comp _ (π p)]; exact h0'
  refine ⟨?_, ?_, ?_⟩
  · intro q x' j b hq _
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ q⟩
    rintro rfl; rw [hl] at hq; cases hq
  · intro q x' k' view' hq hT
    have hqp : q = p := by simpa using hT
    subst hqp
    rw [hl] at hq; simp only [Loc.collect.injEq] at hq; obtain ⟨-, rfl, -⟩ := hq
    rw [mixed_zero _ _ _ _ hk, nonW_comp]
    omega
  · omega

end Podc.MemoryAnonymousCoordination.Consensus
