import Papers.PODC2024.GlobalCertificationHashing.Model
import Papers.PODC2024.GlobalCertificationHashing.Hashing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.List.GetD

/-!
# The perfect-hashing scheme (Theorems 3 and 4)

Fix a finite target graph `H` on `W` (`n' = |W|`) and an identifier range `M` with `n ≤ M n`.
The certificate for a graph with `n` vertices is the number
`c = (2 ^ n - 1) + 2 ^ (n + 1) * (idx + |L_n| * code)`, i.e. the bit string
`1ⁿ 0 · idx · code`:
* `n` in unary (so the verifier can read it without knowing it),
* `idx`, the index of a hash function `h` in the hash list `L_n = fam M n` for `(n, M n)`,
* `code < n' ^ n`, the list `L` of the paper: the `n'`-ary digits of `code` are the vertices of `H`
  (via a fixed enumeration of `W`) assigned to the hash values `0, …, n - 1`.

Node `u` accepts iff the colour `L[h(Id u)]` is defined and is adjacent in `H` to `L[h(Id v)]` for
every neighbour `v`. The size is `n + 1 + ⌈log₂ |L_n|⌉ + n ⌈log₂ n'⌉`
(`certSize`), which is `≤ 10 (n log₂ n' + log₂ log₂ M(n))` (`certSize_le`).
-/

open Finset Real

namespace Podc.GlobalCertificationHashing

/-! ### The property -/

/-- "`G` admits a homomorphism to `H`". -/
def HomTo {W : Type} (H : SimpleGraph W) : GraphProperty := fun _ _ G => Nonempty (G →g H)

/-- Bipartiteness = proper 2-colourability. -/
def Bipartite : GraphProperty := fun _ _ G => G.Colorable 2

/-! ### Encoding of the certificate -/

/-- The unary length prefix: the position of the lowest zero bit. -/
noncomputable def decodeN (c : ℕ) : ℕ :=
  Nat.find (⟨c, Nat.testBit_lt_two_pow Nat.lt_two_pow_self⟩ : ∃ i, c.testBit i = false)

theorem decodeN_encode (n r : ℕ) : decodeN (2 ^ n - 1 + 2 ^ (n + 1) * r) = n := by
  have hmod : (2 ^ n - 1 + 2 ^ (n + 1) * r) % 2 ^ (n + 1) = 2 ^ n - 1 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    have : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ n)
    have : 0 < 2 ^ n := by positivity
    omega
  have hbit : ∀ i ≤ n, (2 ^ n - 1 + 2 ^ (n + 1) * r).testBit i = decide (i < n) := by
    intro i hi
    have := Nat.testBit_mod_two_pow (2 ^ n - 1 + 2 ^ (n + 1) * r) (n + 1) i
    rw [hmod, Nat.testBit_two_pow_sub_one] at this
    simp only [show i < n + 1 by omega, decide_true, Bool.true_and] at this
    exact this.symm
  unfold decodeN
  rw [Nat.find_eq_iff]
  refine ⟨by simpa using hbit n le_rfl, fun i hi => ?_⟩
  rw [hbit i hi.le]
  simpa using hi

theorem div_encode (n r : ℕ) : (2 ^ n - 1 + 2 ^ (n + 1) * r) / 2 ^ (n + 1) = r := by
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt, zero_add]
  have : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ n)
  have : 0 < 2 ^ n := by positivity
  omega

theorem encode_lt (n r : ℕ) : 2 ^ n - 1 + 2 ^ (n + 1) * r < 2 ^ (n + 1) * (r + 1) := by
  have : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ n)
  have : 0 < 2 ^ n := by positivity
  rw [mul_add, mul_one]
  omega

/-! ### The hash lists -/

/-- The hash list used for graphs with `n` vertices (Theorem 7 applied to `(n, M n)`). -/
noncomputable def fam (M : ℕ → ℕ) (n : ℕ) : List (ℕ → ℕ) :=
  (exists_hashList n (M n)).choose

theorem fam_spec (M : ℕ → ℕ) (n : ℕ) (hn : n ≤ M n) (S : Finset ℕ) (hS : ∀ x ∈ S, x < M n)
    (hc : S.card = n) : ∃ h ∈ fam M n, Set.InjOn h S ∧ ∀ x ∈ S, h x < n :=
  (exists_hashList n (M n)).choose_spec.1 hn S hS hc

theorem fam_length (M : ℕ → ℕ) (n : ℕ) :
    (fam M n).length ≤ max 1 ⌈(n : ℝ) * exp n * log (M n)⌉₊ :=
  (exists_hashList n (M n)).choose_spec.2

/-! ### The verifier -/

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- The vertex of `H` written at position `i` of the list encoded by `code` (its `i`-th digit in
base `n' = |W|`), if that digit is `< n'`. -/
noncomputable def col (code i : ℕ) : Option W :=
  if hi : code / Fintype.card W ^ i % Fintype.card W < Fintype.card W then
    some ((Fintype.equivFin W).symm ⟨_, hi⟩) else none

theorem col_eq {code i : ℕ} {w : W}
    (h : code / Fintype.card W ^ i % Fintype.card W = (Fintype.equivFin W w : ℕ)) :
    col (W := W) code i = some w := by
  unfold col
  rw [dite_eq_left (by rw [h]; exact (Fintype.equivFin W w).isLt)]
  congr 1
  rw [Equiv.symm_apply_eq]
  ext
  simp [h]

/-- The verification algorithm of the proof of Theorem 4. -/
noncomputable def verifier (M : ℕ → ℕ) : Verifier := fun idu nbrs c =>
  ∃ a, col (W := W) (c / 2 ^ (decodeN c + 1) / (fam M (decodeN c)).length)
      ((fam M (decodeN c)).getD (c / 2 ^ (decodeN c + 1) % (fam M (decodeN c)).length) id idu)
      = some a ∧
    ∀ j ∈ nbrs, ∃ b, col (W := W) (c / 2 ^ (decodeN c + 1) / (fam M (decodeN c)).length)
      ((fam M (decodeN c)).getD (c / 2 ^ (decodeN c + 1) % (fam M (decodeN c)).length) id j)
      = some b ∧ H.Adj a b

/-- The certificate size: `n + 1` bits for `n` in unary, `⌈log₂ |L_n|⌉` for the hash function,
`n ⌈log₂ n'⌉` for the list of vertices of `H`. -/
noncomputable def certSize (W : Type) [Fintype W] (M : ℕ → ℕ) (n : ℕ) : ℕ :=
  n + 1 + Nat.clog 2 (fam M n).length + n * Nat.clog 2 (Fintype.card W)

/-- **Soundness** (stronger than required): if all nodes accept a certificate under *any*
labelling `Id` (not even injective), then `G` has a homomorphism to `H`; as observed in the paper,
the hash function need not be perfect. -/
theorem sound {V : Type} {G : SimpleGraph V} {M : ℕ → ℕ} {Id : V → ℕ} {c : ℕ}
    (hacc : Accepts (verifier H M) G Id c) : Nonempty (G →g H) := by
  choose φ hφ using hacc
  refine ⟨⟨φ, fun {u v} huv => ?_⟩⟩
  obtain ⟨b, hb, hadj⟩ := (hφ u).2 (Id v) ⟨v, huv, rfl⟩
  rw [(hφ v).1] at hb
  cases hb
  exact hadj

/-- **Completeness**: if `φ : G →g H`, then for every identifier assignment there is an accepted
certificate of `certSize` bits. -/
theorem complete {M : ℕ → ℕ} (hM : ∀ n, n ≤ M n) {V : Type} [Fintype V] {G : SimpleGraph V}
    (φ : G →g H) {Id : V → ℕ} (hId : IsIdAssignment (M (Fintype.card V)) Id) :
    ∃ c < 2 ^ certSize W M (Fintype.card V), Accepts (verifier H M) G Id c := by
  classical
  set n := Fintype.card V with hn
  set n' := Fintype.card W
  set ι := Fintype.equivFin W
  -- a perfect hash function for the set of identifiers
  obtain ⟨h, hmem, hinj, hlt⟩ := fam_spec M n (hM n) (univ.image Id)
    (by simpa using hId.2) (by rw [card_image_of_injective _ hId.1, card_univ])
  let e : V → Fin n := fun v => ⟨h (Id v), hlt _ (mem_image_of_mem _ (mem_univ v))⟩
  have he : Function.Injective e := by
    intro u v huv
    apply hId.1
    exact hinj (by simp) (by simp) (congrArg Fin.val huv)
  let E : V ≃ Fin n := Equiv.ofBijective e
    ((Fintype.bijective_iff_injective_and_card e).mpr ⟨he, by rw [Fintype.card_fin]⟩)
  -- the list `L` of the paper, as a number `code < n' ^ n`
  let Lf : Fin n → Fin n' := fun i => ι (φ (E.symm i))
  let code : ℕ := finFunctionFinEquiv Lf
  set L := fam M n with hL
  obtain ⟨idx, hidx, hLidx⟩ := List.mem_iff_getElem.mp hmem
  set r := idx + L.length * code with hr
  refine ⟨2 ^ n - 1 + 2 ^ (n + 1) * r, ?_, ?_⟩
  · -- size
    have hcode : code < n' ^ n := (finFunctionFinEquiv Lf).isLt
    have hr1 : r + 1 ≤ L.length * n' ^ n := by
      calc r + 1 ≤ L.length + L.length * code := by omega
        _ = L.length * (code + 1) := by ring
        _ ≤ L.length * n' ^ n := Nat.mul_le_mul_left _ hcode
    have h2n : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right two_pos (Nat.le_succ n)
    have h2n0 : 0 < 2 ^ n := by positivity
    calc 2 ^ n - 1 + 2 ^ (n + 1) * r < 2 ^ (n + 1) * (r + 1) := encode_lt n r
      _ ≤ 2 ^ (n + 1) * (L.length * n' ^ n) := Nat.mul_le_mul_left _ hr1
      _ ≤ 2 ^ (n + 1) * (2 ^ Nat.clog 2 L.length * (2 ^ Nat.clog 2 n') ^ n) := by
          gcongr
          · exact Nat.le_pow_clog one_lt_two _
          · exact Nat.le_pow_clog one_lt_two _
      _ = 2 ^ certSize W M n := by
          simp only [certSize, ← hL, pow_add, ← pow_mul]; ring
  · -- acceptance
    have hdec : decodeN (2 ^ n - 1 + 2 ^ (n + 1) * r) = n := decodeN_encode n r
    have hdiv : (2 ^ n - 1 + 2 ^ (n + 1) * r) / 2 ^ (n + 1) = r := div_encode n r
    have hpos : 0 < L.length := by omega
    have hmod : r % L.length = idx := by
      rw [hr, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hidx]
    have hquot : r / L.length = code := by
      rw [hr, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hidx, zero_add]
    have hget : L.getD idx id = h := by rw [List.getD_eq_getElem L id hidx, hLidx]
    have hcol : ∀ v, col (W := W) code (h (Id v)) = some (φ v) := by
      intro v
      apply col_eq
      have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv Lf) (e v)
      rw [Equiv.symm_apply_apply] at this
      change code / n' ^ (e v : ℕ) % n' = _
      rw [← this]
      simp [Lf, E, Equiv.ofBijective_symm_apply_apply, ι]
    intro u
    simp only [verifier, hdec, hdiv, ← hL, hmod, hquot, hget]
    refine ⟨φ u, hcol u, ?_⟩
    rintro _ ⟨v, huv, rfl⟩
    exact ⟨φ v, hcol v, φ.map_adj huv⟩

/-- The perfect-hashing scheme is a global certification scheme for "homomorphism to `H`". -/
theorem isGlobalScheme_verifier {M : ℕ → ℕ} (hM : ∀ n, n ≤ M n) :
    IsGlobalScheme (HomTo H) M (certSize W M) (verifier H M) := by
  intro V _ G
  refine ⟨fun ⟨φ⟩ Id hId => complete H hM φ hId, fun hall => ?_⟩
  obtain ⟨c, -, hacc⟩ := hall (fun v => Fintype.equivFin V v)
    ⟨fun u v huv => (Fintype.equivFin V).injective (Fin.ext huv),
      fun v => (Fintype.equivFin V v).isLt.trans_le (hM _)⟩
  exact sound H hacc

end Podc.GlobalCertificationHashing
