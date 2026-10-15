import Papers.PODC2019.AnonymousMutex.Alg2Inv

/-!
# Theorem 3: Algorithm 2 satisfies mutual exclusion

A process in the critical section owns more than `m/2` registers (`LocInv` at pc `cs`), and the
sets of registers owned by different processes are disjoint.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ} {P : Type} [DecidableEq P]

lemma own_disjoint (ids : P → Id) (hid : Function.Injective ids) (C : Cfg Id m P) {p q : P}
    (hpq : p ≠ q) : Disjoint (own ids C p) (own ids C q) := by
  rw [Finset.disjoint_left]
  intro y hp hq
  simp only [own, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
  rw [hp] at hq
  exact hpq (hid (Option.some.inj hq))

/-- **Theorem 3** (Aghazadeh et al., PODC 2019): Algorithm 2 satisfies mutual exclusion, for
every number `m ≥ 1` of registers, all identifiers and all anonymity permutations. -/
theorem theorem_3 (ids : P → Id) (hid : Function.Injective ids) (π : P → Equiv.Perm (Fin m))
    (hm : 0 < m) : ((alg2 Id m).impl ids π).MutualExclusion := by
  rintro α ⟨C, hC⟩ hwf p q hp hq
  by_contra hpq
  obtain ⟨hL, hR, -⟩ := inv_of_run ids π hid hm hwf hC
  have hcs : ∀ r, InCS α r → m < 2 * (own ids C r).card := by
    intro r hr
    have hpc := ((hR r).2.2.1 hr).1
    have := (hL r).2
    rw [hpc] at this
    exact this
  have h1 := hcs p hp
  have h2 := hcs q hq
  have hdis := own_disjoint ids hid C hpq
  have hle : (own ids C p).card + (own ids C q).card ≤ m := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact (Finset.card_le_univ _).trans (by simp)
  omega

end AnonymousMutex.Alg2
