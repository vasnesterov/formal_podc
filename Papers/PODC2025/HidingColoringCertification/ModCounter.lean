import Papers.PODC2025.HidingColoringCertification.Model
import Papers.PODC2025.HidingColoringCertification.Graph

/-!
# An anonymous, strongly sound LCP for 2-colouring with counters modulo `M(N)`

Not in the paper: this is the LCP that refutes Theorem 4.2 (see `Theorem42.lean`).

Every node gets a counter `ℓ v ∈ ℕ`. With `M = modulus N = 5 (2N + 1)` (odd, and `> 2N ≥ 2n`),
a node accepts iff the counter of each of its neighbours is `ℓ v ± 1 (mod M)`.

* Completeness: a proper 2-colouring (`0/1`) is accepted on every bipartite graph.
* Strong soundness on every graph and for every labelling (`counterLCP_stronglySoundAll`): along
  a walk through accepting nodes the counter moves by `±1` per step, so a closed walk of length
  `L < M` has an integer displacement `z` with `|z| ≤ L`, `z ≡ L (mod 2)` and `M ∣ z`, hence
  `z = 0` and `L` is even. Closed walks of length `< 2n ≤ 2N < M` suffice for bipartiteness
  (`colorable_two_of_even_short_loops`).
* The decoder ignores identifiers (`counterLCP_anonymous`); certificates are `< M`, i.e.
  `O(log N) = O(log n)` bits.

The point is that the verifier knows `N ≥ n` (as in the paper's model) and can therefore choose
a modulus larger than the length of any cycle, while the accepting neighbourhood graph contains
odd cycles of length `≥ M` (`Theta.lean`).
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-- The modulus used by the counter LCP: odd, divisible by `5`, larger than `2N`. -/
def modulus (N : ℕ) : ℕ := 5 * (2 * N + 1)

instance (N : ℕ) : NeZero (modulus N) := ⟨by unfold modulus; omega⟩

lemma modulus_odd (N : ℕ) : Odd (modulus N) := by
  unfold modulus; exact Odd.mul (by decide) (by exact odd_two_mul_add_one N)

/-- Two counters are compatible modulo `M`. -/
def CounterStep (M a b : ℕ) : Prop := (b : ZMod M) = a + 1 ∨ (b : ZMod M) = a - 1

instance (M a b : ℕ) : Decidable (CounterStep M a b) := by unfold CounterStep; infer_instance

/-- The counter LCP. Admissible certificates on `n`-node graphs are the counters `< M(bound n)`. -/
def counterLCP (bound : ℕ → ℕ) : LCP ℕ where
  D μ := decide (∀ x ∈ μ.nbrs, CounterStep (modulus μ.N) μ.label x.label)
  sz n := {c | c < modulus (bound n)}

variable {bound : ℕ → ℕ}

lemma counterLCP_acc_iff (P : PortGraph) (ℓ : P.V → ℕ) (v : P.V) :
    (counterLCP bound).Acc P ℓ v ↔ ∀ w, P.G.Adj v w → CounterStep (modulus P.N) (ℓ v) (ℓ w) := by
  simp only [LCP.Acc, counterLCP, decide_eq_true_eq, PortGraph.mem_view_nbrs]
  constructor
  · intro h w hw; exact h _ ⟨w, hw, rfl⟩
  · rintro h _ ⟨w, hw, rfl⟩; exact h w hw

lemma counterLCP_anonymous : (counterLCP bound).Anonymous := by
  intro μ μ' h
  simp only [View.anon, AnonView.mk.injEq] at h
  obtain ⟨hN, hl, -, hn⟩ := h
  simp only [counterLCP]
  rw [hN, hl]
  congr 1
  apply propext
  constructor
  · intro H x hx
    obtain ⟨y, hy, hxy⟩ := Multiset.mem_map.1 (hn ▸ Multiset.mem_map_of_mem NbrInfo.anon hx)
    have : y.label = x.label := congrArg AnonNbrInfo.label hxy
    rw [← this]; exact H y hy
  · intro H x hx
    obtain ⟨y, hy, hxy⟩ := Multiset.mem_map.1 (hn.symm ▸ Multiset.mem_map_of_mem NbrInfo.anon hx)
    have : y.label = x.label := congrArg AnonNbrInfo.label hxy
    rw [← this]; exact H y hy

/-- Completeness on every bipartite graph (with any port and identifier assignment). -/
theorem counterLCP_complete : (counterLCP bound).Complete bound Bipartite := by
  intro P hP hbip
  obtain ⟨c⟩ := hbip
  refine ⟨fun v => (c v).val, fun v => ?_, fun v => ?_⟩
  · show (c v).val < modulus (bound _)
    have := (c v).isLt; unfold modulus; omega
  · rw [counterLCP_acc_iff]
    intro w hw
    have hne := c.valid hw
    have h2 : (c v).val < 2 := (c v).isLt
    have h2' : (c w).val < 2 := (c w).isLt
    have hne' : (c v).val ≠ (c w).val := fun h => hne (Fin.ext h)
    unfold CounterStep
    rcases (by omega : ((c v).val = 0 ∧ (c w).val = 1) ∨ ((c v).val = 1 ∧ (c w).val = 0))
      with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; simp
    · right; rw [h1, h2]; simp

/-- Integer displacement of the counter along a walk through accepting nodes. -/
lemma counter_displacement (P : PortGraph) (ℓ : P.V → ℕ) {a b}
    (p : ((counterLCP bound).accGraph P ℓ).Walk a b) :
    ∃ z : ℤ, (z : ZMod (modulus P.N)) = (ℓ b.1 : ZMod (modulus P.N)) - ℓ a.1 ∧
      z.natAbs ≤ p.length ∧ Even (z + p.length) := by
  induction p with
  | nil => exact ⟨0, by simp, by simp, by simp⟩
  | @cons a c b hac q ih =>
    obtain ⟨z, hz, hzl, hze⟩ := ih
    have hacc := (counterLCP_acc_iff P ℓ a.1).1 a.2 c.1 hac
    rcases hacc with h | h
    · refine ⟨z + 1, ?_, ?_, ?_⟩
      · push_cast; rw [hz, h]; ring
      · simp only [Walk.length_cons]; omega
      · simp only [Walk.length_cons]; push_cast
        rw [show z + 1 + ((q.length : ℤ) + 1) = (z + q.length) + 2 by ring]
        exact hze.add (by decide)
    · refine ⟨z - 1, ?_, ?_, ?_⟩
      · push_cast; rw [hz, h]; ring
      · simp only [Walk.length_cons]; omega
      · simp only [Walk.length_cons]; push_cast
        rw [show z - 1 + ((q.length : ℤ) + 1) = z + q.length by ring]
        exact hze

/-- **Strong soundness on every graph**: for every port graph and every labelling, the accepting
nodes induce a bipartite graph. -/
theorem counterLCP_stronglySoundAll : (counterLCP bound).StronglySoundAll 2 := by
  intro P ℓ
  apply colorable_two_of_even_short_loops
  intro u w hw
  obtain ⟨z, hz, hzl, hze⟩ := counter_displacement P ℓ w
  have hcard : Fintype.card {v // (counterLCP bound).Acc P ℓ v} ≤ P.N :=
    (Fintype.card_subtype_le _).trans P.card_le_N
  have hM : w.length < modulus P.N := by unfold modulus; omega
  rw [sub_self] at hz
  have hdvd : (modulus P.N : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hz
  have hz0 : z = 0 := by
    obtain ⟨k, hk⟩ := hdvd
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · exfalso
      have : z.natAbs ≥ modulus P.N := by
        rw [hk]; rw [Int.natAbs_mul]; simp only [Int.natAbs_natCast]
        have : k.natAbs ≥ 1 := by omega
        nlinarith
      omega
    · simp [hk, hk0]
    · exfalso
      have : z.natAbs ≥ modulus P.N := by
        rw [hk]; rw [Int.natAbs_mul]; simp only [Int.natAbs_natCast]
        have : k.natAbs ≥ 1 := by omega
        nlinarith
      omega
  rw [hz0, zero_add] at hze
  exact_mod_cast hze

end Podc.HidingColoringCertification
