import Papers.PODC2020.BezoutElection.Necessity
import Papers.PODC2020.BezoutElection.Alg2Main
import Papers.PODC2020.BezoutElection.Bezout

/-!
# Theorem 4 with the paper's parameters, and Corollaries 1–3 (tight bounds)

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Sections 5–6.

* `theorem_4`: for `m ≥ 1` registers, `n ≥ 1` processes and `d = gcd(m, n) ℓ ≤ n`, Algorithm 2
  with Bezout parameters (`u m = v n + gcd(m, n)`, `U = u ℓ`, `W = v ℓ`) is a symmetric
  read/write algorithm that terminates and elects exactly `d` processes, for every choice of the
  anonymity permutations.
* `corollary_1`, `corollary_2`, `corollary_3`: the characterizations. `rw = true` asks for a
  read/write algorithm, `rw = false` allows arbitrary read-modify-write accesses and snapshots.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

variable {Id : Type} [DecidableEq Id] {P : Type} [Fintype P] [DecidableEq P]

/-- Exact `d`-election is solvable by a symmetric algorithm on `m` anonymous registers
(read/write only if `rw`), for every choice of the anonymity permutations. -/
def ExactSolvable (rw : Bool) (m : ℕ) (ids : P → Id) (d : ℕ) : Prop :=
  ∃ (V S : Type) (_ : MulAction (Equiv.Perm Id) V) (_ : MulAction (Equiv.Perm Id) S)
    (A : SymAlg (elecObj Bool) Id m V S), A.Symmetric ∧ (rw = true → A.ReadWrite) ∧
      ∀ π, Terminates (A.impl ids π) ∧ ExactElection d (A.impl ids π)

/-- `d`-election is solvable by a symmetric algorithm on `m` anonymous registers (read/write
only if `rw`), for every choice of the anonymity permutations. -/
def DSolvable (rw : Bool) (m : ℕ) (ids : P → Id) (d : ℕ) : Prop :=
  ∃ (V S : Type) (_ : MulAction (Equiv.Perm Id) V) (_ : MulAction (Equiv.Perm Id) S)
    (A : SymAlg (elecObj Bool) Id m V S), A.Symmetric ∧ (rw = true → A.ReadWrite) ∧
      ∀ π, Terminates (A.impl ids π) ∧ DElection d (A.impl ids π)

/-- **Theorem 4** of Godard–Imbs–Raynal–Taubenfeld (PODC 2020), with the paper's parameters:
for `m ≥ 1`, `n ≥ 1` and `d = gcd(m, n) ℓ ≤ n`, Algorithm 2 (with `u m = v n + gcd(m, n)`,
`U = u ℓ`, `W = v ℓ`) is a symmetric read/write algorithm that, for every choice of the anonymity
permutations, terminates and elects exactly `d` processes. -/
theorem theorem_4 [Nonempty P] (m : ℕ) (hm : 1 ≤ m) (ids : P → Id) (hid : Function.Injective ids)
    (ℓ : ℕ) (hd : Nat.gcd m (Fintype.card P) * ℓ ≤ Fintype.card P) :
    ∃ u v : ℕ, u * m = v * Fintype.card P + Nat.gcd m (Fintype.card P) ∧
      let A := Alg2.alg2 Id m ⟨Fintype.card P, u * ℓ, v * ℓ⟩ (fun a L => decide (a ∈ L))
      A.Symmetric ∧ A.ReadWrite ∧ ∀ π, Terminates (A.impl ids π) ∧
        ExactElection (Nat.gcd m (Fintype.card P) * ℓ) (A.impl ids π) := by
  have hn : 1 ≤ Fintype.card P := Fintype.card_pos
  obtain ⟨u, v, -, huv⟩ := exists_bezout_nat m _ hm hn
  have hcount := bezout_count m _ u v ℓ huv
  refine ⟨u, v, huv, Alg2.alg2_symmetric _ _ (fun σ a L => by simp),
    Alg2.alg2_readWrite _ _, fun π => ⟨?_, ?_⟩⟩
  · exact Alg2.alg2_terminates _ _ ids hid rfl π (by simp; omega) (by simp; omega)
  · intro α hα h1 hall
    obtain ⟨L, hout, hL⟩ := Alg2.alg2_agreement _ _ ids hid rfl π (by omega)
      (by simp; omega) α hα h1
    obtain ⟨q₀⟩ := ‹Nonempty P›
    obtain ⟨hcard, hsub⟩ := hL ⟨q₀, hall q₀⟩
    simp only at hcard
    have himg : (elected α).image ids = L := by
      ext a
      simp only [elected, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨q, hq, rfl⟩
        have := hout q true hq
        simpa using this.symm
      · intro ha
        obtain ⟨q, rfl⟩ := hsub a ha
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (hall q)
        refine ⟨q, ?_, rfl⟩
        rw [hb, hout q b hb]; simp [ha]
    rw [← Finset.card_image_of_injective _ hid, himg]
    omega

omit [DecidableEq Id] in
lemma ExactSolvable.necessary {rw : Bool} {m : ℕ} {ids : P → Id} (hid : Function.Injective ids)
    {d : ℕ} (h : ExactSolvable rw m ids d) : Nat.gcd m (Fintype.card P) ∣ d := by
  obtain ⟨V, S, _, _, A, hA, -, hT⟩ := h
  exact theorem_1_2 hA ids hid d hT

omit [DecidableEq Id] in
lemma DSolvable.necessary {rw : Bool} {m : ℕ} {ids : P → Id} (hid : Function.Injective ids)
    {d : ℕ} (h : DSolvable rw m ids d) : Nat.gcd m (Fintype.card P) ≤ d := by
  obtain ⟨V, S, _, _, A, hA, -, hT⟩ := h
  exact theorem_1_1 hA ids hid d hT

lemma exactSolvable_of_dvd [Nonempty P] (rw : Bool) {m : ℕ} (hm : 1 ≤ m) {ids : P → Id}
    (hid : Function.Injective ids) {d : ℕ} (hdn : d ≤ Fintype.card P)
    (hdvd : Nat.gcd m (Fintype.card P) ∣ d) : ExactSolvable rw m ids d := by
  obtain ⟨ℓ, rfl⟩ := hdvd
  obtain ⟨u, v, -, hA, hrw, h⟩ := theorem_4 m hm ids hid ℓ hdn
  exact ⟨_, _, _, _, _, hA, fun _ => hrw, h⟩

/-- **Corollary 3**: for `m ≥ 1` and `1 ≤ d ≤ n`, exact `d`-election is solvable by a symmetric
algorithm on `m` anonymous read/write registers (`rw = true`), or read-modify-write registers
(`rw = false`), iff `gcd(m, n)` divides `d`. -/
theorem corollary_3 [Nonempty P] (rw : Bool) (m : ℕ) (hm : 1 ≤ m) (ids : P → Id)
    (hid : Function.Injective ids) (d : ℕ) (hdn : d ≤ Fintype.card P) :
    ExactSolvable rw m ids d ↔ Nat.gcd m (Fintype.card P) ∣ d :=
  ⟨ExactSolvable.necessary hid, exactSolvable_of_dvd rw hm hid hdn⟩

/-- **Corollary 2**: for `m ≥ 1`, `d`-election (at least one and at most `d` leaders) is
solvable by a symmetric algorithm on `m` anonymous read/write (or read-modify-write) registers iff
`gcd(m, n) ≤ d`. -/
theorem corollary_2 [Nonempty P] (rw : Bool) (m : ℕ) (hm : 1 ≤ m) (ids : P → Id)
    (hid : Function.Injective ids) (d : ℕ) :
    DSolvable rw m ids d ↔ Nat.gcd m (Fintype.card P) ≤ d := by
  refine ⟨DSolvable.necessary hid, fun hd => ?_⟩
  have hg : 1 ≤ Nat.gcd m (Fintype.card P) := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨V, S, i1, i2, A, hA, hrw, h⟩ := exactSolvable_of_dvd rw hm hid
    (Nat.gcd_le_right (n := Fintype.card P) m Fintype.card_pos) (dvd_refl _)
  refine ⟨V, S, i1, i2, A, hA, hrw, fun π => ⟨(h π).1, fun α hα h1 hall => ?_⟩⟩
  have := (h π).2 α hα h1 hall
  omega

/-- **Corollary 1**: for `m ≥ 1`, leader election is solvable by a symmetric algorithm on `m`
anonymous read/write (or read-modify-write) registers iff `gcd(m, n) = 1`. -/
theorem corollary_1 [Nonempty P] (rw : Bool) (m : ℕ) (hm : 1 ≤ m) (ids : P → Id)
    (hid : Function.Injective ids) :
    DSolvable rw m ids 1 ↔ Nat.gcd m (Fintype.card P) = 1 := by
  rw [corollary_2 rw m hm ids hid 1]
  have := Nat.gcd_pos_of_pos_left (Fintype.card P) hm
  omega

end BezoutElection
