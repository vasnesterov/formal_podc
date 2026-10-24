import Papers.PODC2014.PlanarMDSLowerBound.Grid
import Mathlib.Data.Finset.Sort

/-!
# Block-wise identifier assignments (proof of Lemma 1, part 1)

The grid `G` of the paper consists of `r` blocks of `m × m` nodes placed side by side: we take
`grid (r * m) m`, block `i` being the columns `[i m, (i + 1) m)`. Given pairwise disjoint sets
`Y i` of `M = m²` identifiers (`i < r`), `asgEquiv` assigns the identifiers of `Y i` to block `i`
*in increasing order by rows* (node `(i m + a, b)` gets the `(b m + a)`-th smallest element of
`Y i`), as in the paper.

For an internal node `v` of block `i` (`T ≤ a < m - T`, `T ≤ b < m - T`), the `k × k` region
around it (`k = 2T + 1`) lies in block `i`, and its identifiers are again placed in increasing
order by rows: `view_asg_internal` shows that `view T σ v = placement X` for the set `X ⊆ Y i` of
identifiers in the region, where `placement X` puts the `K = k²` elements of `X` in increasing
order by rows. This is the paper's observation "the identifiers of `X_v` are assigned in an
increasing order by rows".
-/

namespace Podc.PlanarMDSLowerBound

open Finset

/-- Lexicographic comparison of `q * m + a` for digits `a < m`. -/
lemma lex_lt_iff {m q₁ q₂ a₁ a₂ : ℕ} (h₁ : a₁ < m) (h₂ : a₂ < m) :
    q₁ * m + a₁ < q₂ * m + a₂ ↔ q₁ < q₂ ∨ (q₁ = q₂ ∧ a₁ < a₂) := by
  constructor
  · intro h
    rcases lt_trichotomy q₁ q₂ with hq | rfl | hq
    · exact Or.inl hq
    · exact Or.inr ⟨rfl, by omega⟩
    · have : (q₂ + 1) * m ≤ q₁ * m := Nat.mul_le_mul_right _ hq
      rw [Nat.add_mul, one_mul] at this
      omega
  · rintro (hq | ⟨rfl, ha⟩)
    · have : (q₁ + 1) * m ≤ q₂ * m := Nat.mul_le_mul_right _ hq
      rw [Nat.add_mul, one_mul] at this
      omega
    · omega

lemma digit_lt {m a b : ℕ} (ha : a < m) (hb : b < m) : b * m + a < m * m := by
  have : (b + 1) * m ≤ m * m := Nat.mul_le_mul_right _ hb
  rw [Nat.add_mul, one_mul] at this
  omega

/-- The `K = k²` elements of `X` placed in increasing order by rows into a `k × k` array
(`none` everywhere if `|X| ≠ K`). -/
noncomputable def placement {n : ℕ} (k : ℕ) (X : Finset (Fin n)) : Fin k → Fin k → Option (Fin n) :=
  if hX : X.card = k * k then
    fun i j => some (X.orderEmbOfFin hX ⟨j * k + i, digit_lt i.2 j.2⟩)
  else fun _ _ => none

section Blocks

variable {T m r : ℕ} (Y : ℕ → Finset (Fin (r * m * m))) (hY : ∀ i < r, (Y i).card = m * m)

private lemma blk_lt {p : GV (r * m) m} : (p.1 : ℕ) / m < r := by
  have hm : 0 < m := Nat.zero_lt_of_lt p.2.2
  exact (Nat.div_lt_iff_lt_mul hm).2 p.1.2

/-- The block assignment: node `(x, y)` of block `i = x / m` gets the `(y m + x mod m)`-th smallest
identifier of `Y i`. -/
noncomputable def asg (p : GV (r * m) m) : Fin (r * m * m) :=
  (Y ((p.1 : ℕ) / m)).orderEmbOfFin (hY _ blk_lt)
    ⟨(p.2 : ℕ) * m + (p.1 : ℕ) % m, digit_lt (Nat.mod_lt _ (Nat.zero_lt_of_lt p.2.2)) p.2.2⟩

lemma asg_mem (p : GV (r * m) m) : asg Y hY p ∈ Y ((p.1 : ℕ) / m) :=
  Finset.orderEmbOfFin_mem _ _ _

variable (hdisj : ∀ i j, i < r → j < r → i ≠ j → Disjoint (Y i) (Y j))

include hdisj in
private lemma orderEmb_eq_aux {i i' : ℕ} (hi : i < r) (hi' : i' < r) {t t' : Fin (m * m)}
    (h : (Y i).orderEmbOfFin (hY i hi) t = (Y i').orderEmbOfFin (hY i' hi') t') :
    i = i' ∧ t = t' := by
  by_cases hii : i = i'
  · subst hii
    exact ⟨rfl, ((Y i).orderEmbOfFin (hY i hi)).injective h⟩
  · exfalso
    have h1 := Finset.orderEmbOfFin_mem (Y i) (hY i hi) t
    have h2 := Finset.orderEmbOfFin_mem (Y i') (hY i' hi') t'
    rw [h] at h1
    exact Finset.disjoint_left.1 (hdisj i i' hi hi' hii) h1 h2

include hdisj in
lemma asg_injective : Function.Injective (asg Y hY) := by
  intro p q h
  obtain ⟨h1, h2⟩ := orderEmb_eq_aux Y hY hdisj (blk_lt (p := p)) (blk_lt (p := q)) h
  have hm : 0 < m := Nat.zero_lt_of_lt p.2.2
  have h2' := congrArg Fin.val h2
  simp only at h2'
  have hpm := Nat.mod_lt (p.1 : ℕ) hm
  have hqm := Nat.mod_lt (q.1 : ℕ) hm
  rcases (lex_lt_iff hpm hqm (q₁ := (p.2 : ℕ)) (q₂ := (q.2 : ℕ))).not.1 (by omega) |> not_or.1 with
    ⟨n1, n2⟩
  rcases (lex_lt_iff hqm hpm (q₁ := (q.2 : ℕ)) (q₂ := (p.2 : ℕ))).not.1 (by omega) |> not_or.1 with
    ⟨n3, n4⟩
  have e2 : (p.2 : ℕ) = q.2 := by omega
  have e1 : (p.1 : ℕ) % m = (q.1 : ℕ) % m := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact n2 ⟨e2, hlt⟩
    · exact n4 ⟨e2.symm, hlt⟩
  have := Nat.div_add_mod (p.1 : ℕ) m
  have := Nat.div_add_mod (q.1 : ℕ) m
  exact Prod.ext (Fin.ext (by rw [← Nat.div_add_mod (p.1 : ℕ) m, ← Nat.div_add_mod (q.1 : ℕ) m,
    h1, e1])) (Fin.ext e2)

include hdisj in
lemma asg_bijective : Function.Bijective (asg Y hY) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨asg_injective Y hY hdisj, by simp [Nat.mul_assoc]⟩

/-- The block assignment as an identifier assignment of the grid. -/
noncomputable def asgEquiv : GV (r * m) m ≃ Fin (r * m * m) :=
  Equiv.ofBijective _ (asg_bijective Y hY hdisj)

@[simp] lemma asgEquiv_apply (p : GV (r * m) m) : asgEquiv Y hY hdisj p = asg Y hY p := rfl

/-- The node `(i m + a, b)` of block `i`. -/
def node (i a b : ℕ) (hi : i < r) (ha : a < m) (hb : b < m) : GV (r * m) m :=
  (⟨i * m + a, by
    have : (i + 1) * m ≤ r * m := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, one_mul] at this; omega⟩, ⟨b, hb⟩)

lemma node_div {i a b : ℕ} {hi : i < r} {ha : a < m} {hb : b < m} :
    ((node (r := r) i a b hi ha hb).1 : ℕ) / m = i := by
  simp only [node]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt ha), Nat.div_eq_of_lt ha,
    zero_add]

lemma node_mod {i a b : ℕ} {hi : i < r} {ha : a < m} {hb : b < m} :
    ((node (r := r) i a b hi ha hb).1 : ℕ) % m = a := by
  simp only [node]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

lemma asg_node {i a b : ℕ} (hi : i < r) (ha : a < m) (hb : b < m) :
    asg Y hY (node i a b hi ha hb) =
      (Y i).orderEmbOfFin (hY i hi) ⟨b * m + a, digit_lt ha hb⟩ := by
  have e1 : ∀ (j : ℕ) (hj : j = i) (t t' : Fin (m * m)), (t : ℕ) = t' →
      (Y j).orderEmbOfFin (hY j (hj ▸ hi)) t = (Y i).orderEmbOfFin (hY i hi) t' := by
    rintro j rfl t t' htt; rw [Fin.ext htt]
  exact e1 _ node_div _ _ (by simp only [node_mod]; rfl)

lemma pt_node {i a b : ℕ} {hi : i < r} {ha : a < m} {hb : b < m} :
    pt (node (r := r) i a b hi ha hb) = (((i * m + a : ℕ) : ℤ), ((b : ℕ) : ℤ)) := rfl

/-- **The view of an internal node** (proof of Lemma 1): if `v = (i m + a, b)` is an internal node
of block `i`, then its view is `placement k X` for a `K`-subset `X ⊆ Y i`. -/
lemma view_asg_internal {i a b : ℕ} (hi : i < r) (ha : T ≤ a) (ha' : a + T < m) (hb : T ≤ b)
    (hb' : b + T < m) :
    ∃ X ⊆ Y i, X.card = (2 * T + 1) * (2 * T + 1) ∧
      view T (asgEquiv Y hY hdisj) (node i a b hi (by omega) (by omega)) =
        placement (2 * T + 1) X := by
  have hkpos : 0 < (2 * T + 1) := by omega
  -- the index map `φ : Fin ((2 * T + 1)*(2 * T + 1)) → Fin (m*m)`
  let φ : Fin ((2 * T + 1) * (2 * T + 1)) → Fin (m * m) := fun j =>
    ⟨(b + (j : ℕ) / (2 * T + 1) - T) * m + (a + (j : ℕ) % (2 * T + 1) - T),
      digit_lt (by have := Nat.mod_lt (j : ℕ) hkpos; omega)
        (by have := (Nat.div_lt_iff_lt_mul hkpos).2 j.2; omega)⟩
  have hφ : StrictMono φ := by
    intro j j' hjj
    have hj1 := Nat.mod_lt (j : ℕ) hkpos
    have hj2 := Nat.mod_lt (j' : ℕ) hkpos
    have hl : ((j : ℕ) / (2 * T + 1)) * (2 * T + 1) + (j : ℕ) % (2 * T + 1) < ((j' : ℕ) / (2 * T + 1)) * (2 * T + 1) + (j' : ℕ) % (2 * T + 1) := by
      rw [Nat.div_add_mod', Nat.div_add_mod']; exact hjj
    rw [lex_lt_iff hj1 hj2] at hl
    show (φ j : ℕ) < φ j'
    simp only [φ]
    rw [lex_lt_iff (by omega) (by omega)]
    generalize (j : ℕ) / (2 * T + 1) = q₁ at *
    generalize (j' : ℕ) / (2 * T + 1) = q₂ at *
    generalize (j : ℕ) % (2 * T + 1) = s₁ at *
    generalize (j' : ℕ) % (2 * T + 1) = s₂ at *
    omega
  let f : Fin ((2 * T + 1) * (2 * T + 1)) → Fin (r * m * m) := fun j => (Y i).orderEmbOfFin (hY i hi) (φ j)
  have hf : StrictMono f := ((Y i).orderEmbOfFin (hY i hi)).strictMono.comp hφ
  refine ⟨Finset.univ.image f, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.orderEmbOfFin_mem _ _ _
  · rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  · have hcard : (Finset.univ.image f).card = (2 * T + 1) * (2 * T + 1) := by
      rw [Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
    have huniq := Finset.orderEmbOfFin_unique hcard (f := f)
      (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) hf
    funext ci rj
    simp only [placement, hcard, dite_true]
    rw [← huniq]
    simp only [view, f]
    rw [idAt_eq_some]
    have hci := ci.2
    have hrj := rj.2
    have e1 : ((rj : ℕ) * (2 * T + 1) + ci) / (2 * T + 1) = rj := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hkpos, Nat.div_eq_of_lt ci.2, zero_add]
    have e2 : ((rj : ℕ) * (2 * T + 1) + ci) % (2 * T + 1) = ci := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ci.2]
    have hpa : a + ci - T < m := by omega
    have hpb : b + rj - T < m := by omega
    let p : GV (r * m) m := node i (a + ci - T) (b + rj - T) hi hpa hpb
    have hp : pt (node i a b hi (by omega : a < m) (by omega : b < m)) + (((ci : ℕ) : ℤ) - T, ((rj : ℕ) : ℤ) - T) =
        pt p := by
      simp only [pt_node, p, Prod.mk_add_mk, Prod.mk.injEq]
      constructor <;> push_cast <;> omega
    have hz : (asgEquiv Y hY hdisj).symm ((Y i).orderEmbOfFin (hY i hi)
        (φ ⟨(rj : ℕ) * (2 * T + 1) + ci, digit_lt ci.2 rj.2⟩)) = p := by
      rw [Equiv.symm_apply_eq, asgEquiv_apply, asg_node]
      congr 1
      ext
      simp only [φ, e1, e2]
    rw [hz, ← hp]
    rfl

end Blocks

end Podc.PlanarMDSLowerBound
