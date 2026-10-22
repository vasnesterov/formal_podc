import Mathlib

/-!
# The hierarchical partition of the path `⟨m^ℓ⟩` (Section 4.1 of the paper)

Nodes are written in base `m` with `ℓ` digits. A packet at node `i` with destination `w > i`
travels on a *segment* whose *level* `lv i w` is the most significant digit position in which `i`
and `w` differ (Definition 4.2); its *intermediate destination* is `xd i w = ⌊w / m^j⌋ m^j` for
`j = lv i w`. The pair `key i w = (lv i w, xd i w)` identifies the pseudo-buffer `L_{j,k}(i)` that
holds the packet (Definition 4.3: `k` is the index of `xd i w` among the intermediate destinations
of the level-`j` interval of `i`; we use the destination itself instead of its index).

`lvl j v = ⌊v / m^(j+1)⌋ m^(j+1)` is the left endpoint of the level-`j` interval containing `v`.
-/

namespace Podc.SmallBuffersAQT

variable (m ℓ : ℕ)

/-- The level `lv(i, w)` of the segment of a packet at `i` with destination `w`: the largest
digit position `j < ℓ` (base `m`) where `i` and `w` differ. -/
def lv (i w : ℕ) : ℕ := Nat.findGreatest (fun j => i / m ^ j ≠ w / m ^ j) ℓ

/-- The intermediate destination `x(i, w) = ⌊w / m^j⌋ m^j`, `j = lv(i, w)` (Definition 4.2). -/
def xd (i w : ℕ) : ℕ := w / m ^ lv m ℓ i w * m ^ lv m ℓ i w

/-- The pseudo-buffer of a packet at node `i` with destination `w`: (level, intermediate
destination). -/
def key (i w : ℕ) : ℕ × ℕ := (lv m ℓ i w, xd m ℓ i w)

/-- Left endpoint of the level-`j` interval containing `v`. -/
def lvl (j v : ℕ) : ℕ := v / m ^ (j + 1) * m ^ (j + 1)

variable {m ℓ}

lemma two_le_of_lt {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) : 2 ≤ m ∧ 1 ≤ ℓ := by
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    · rcases ℓ with _ | ℓ <;> simp at hw; omega
    · simp at hw; omega
  · refine ⟨h, ?_⟩
    rcases ℓ with _ | ℓ
    · simp at hw; omega
    · omega

lemma div_pow_eq_of_le {i w a b : ℕ} (h : i / m ^ a = w / m ^ a) (hab : a ≤ b) :
    i / m ^ b = w / m ^ b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

lemma div_pow_le_div_pow {i w : ℕ} (h : i ≤ w) (a : ℕ) : i / m ^ a ≤ w / m ^ a :=
  Nat.div_le_div_right h

/-- Characterization of the level. -/
lemma lv_spec {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) :
    lv m ℓ i w < ℓ ∧ i / m ^ lv m ℓ i w < w / m ^ lv m ℓ i w ∧
      i / m ^ (lv m ℓ i w + 1) = w / m ^ (lv m ℓ i w + 1) := by
  obtain ⟨hm, hℓ⟩ := two_le_of_lt hiw hw
  have hP0 : (fun j => i / m ^ j ≠ w / m ^ j) 0 := by simp; omega
  have hPℓ : ¬ (fun j => i / m ^ j ≠ w / m ^ j) ℓ := by
    simp only [ne_eq, not_not]
    rw [Nat.div_eq_of_lt (hiw.trans hw), Nat.div_eq_of_lt hw]
  have hspec := Nat.findGreatest_spec (P := fun j => i / m ^ j ≠ w / m ^ j) (Nat.zero_le ℓ) hP0
  have hle := Nat.findGreatest_le (P := fun j => i / m ^ j ≠ w / m ^ j) ℓ
  have hne : Nat.findGreatest (fun j => i / m ^ j ≠ w / m ^ j) ℓ ≠ ℓ := by
    intro h; rw [h] at hspec; exact hPℓ hspec
  refine ⟨lt_of_le_of_ne hle hne, lt_of_le_of_ne (div_pow_le_div_pow hiw.le _) hspec, ?_⟩
  by_contra hc
  exact Nat.findGreatest_is_greatest (P := fun j => i / m ^ j ≠ w / m ^ j) (Nat.lt_succ_self _)
    (lt_of_le_of_ne hle hne) hc

/-- Uniqueness: the level is the position characterized by `lv_spec`. -/
lemma lv_eq_of {i w j : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) (hj1 : i / m ^ (j + 1) = w / m ^ (j + 1))
    (hj : i / m ^ j ≠ w / m ^ j) : lv m ℓ i w = j := by
  obtain ⟨hlt, hne, heq⟩ := lv_spec hiw hw
  rcases lt_trichotomy (lv m ℓ i w) j with h | h | h
  · exact absurd (div_pow_eq_of_le heq h) hj
  · exact h
  · exact absurd (div_pow_eq_of_le hj1 h) hne.ne

lemma pow_pos' {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) (j : ℕ) : 0 < m ^ j :=
  pow_pos (by have := (two_le_of_lt hiw hw).1; omega) j

lemma lt_xd {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) : i < xd m ℓ i w := by
  obtain ⟨-, hne, -⟩ := lv_spec hiw hw
  have hp := pow_pos' hiw hw (lv m ℓ i w)
  unfold xd
  have := Nat.lt_div_mul_add (a := i) hp
  calc i < i / m ^ lv m ℓ i w * m ^ lv m ℓ i w + m ^ lv m ℓ i w := this
    _ = (i / m ^ lv m ℓ i w + 1) * m ^ lv m ℓ i w := by ring
    _ ≤ w / m ^ lv m ℓ i w * m ^ lv m ℓ i w := Nat.mul_le_mul_right _ hne

lemma xd_le (i w : ℕ) : xd m ℓ i w ≤ w := Nat.div_mul_le_self _ _

lemma dvd_xd (i w : ℕ) : m ^ lv m ℓ i w ∣ xd m ℓ i w := Dvd.intro_left _ rfl

lemma xd_div_succ {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) :
    xd m ℓ i w / m ^ (lv m ℓ i w + 1) = w / m ^ (lv m ℓ i w + 1) := by
  have hp := pow_pos' hiw hw (lv m ℓ i w)
  unfold xd
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hp]

lemma xd_div {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) :
    xd m ℓ i w / m ^ lv m ℓ i w = w / m ^ lv m ℓ i w := by
  have hp := pow_pos' hiw hw (lv m ℓ i w)
  unfold xd
  rw [Nat.mul_div_cancel _ hp]

/-- `i` and its intermediate destination lie in the same level-`lv` interval. -/
lemma div_succ_eq_xd {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) :
    i / m ^ (lv m ℓ i w + 1) = xd m ℓ i w / m ^ (lv m ℓ i w + 1) := by
  rw [xd_div_succ hiw hw]; exact (lv_spec hiw hw).2.2

/-- (K2) Moving one hop inside a segment keeps the pseudo-buffer. -/
lemma key_succ {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) (h : i + 1 < xd m ℓ i w) :
    key m ℓ (i + 1) w = key m ℓ i w := by
  obtain ⟨-, -, heq⟩ := lv_spec hiw hw
  have hp := pow_pos' hiw hw (lv m ℓ i w)
  have hxw := xd_le (m := m) (ℓ := ℓ) i w
  have hlv : lv m ℓ (i + 1) w = lv m ℓ i w := by
    refine lv_eq_of (by omega) hw ?_ ?_
    · apply le_antisymm
      · exact div_pow_le_div_pow (by omega) _
      · rw [← heq]; exact div_pow_le_div_pow (by omega) _
    · have : (i + 1) / m ^ lv m ℓ i w < w / m ^ lv m ℓ i w :=
        (Nat.div_lt_iff_lt_mul hp).2 h
      omega
  simp only [key, xd, hlv]

/-- (K3) At the intermediate destination the level strictly decreases. -/
lemma lv_xd_lt {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) (h : xd m ℓ i w < w) :
    lv m ℓ (xd m ℓ i w) w < lv m ℓ i w := by
  have hx := lt_xd hiw hw
  obtain ⟨-, hne, -⟩ := lv_spec h hw
  by_contra hc
  exact hne.ne (div_pow_eq_of_le (xd_div hiw hw) (not_lt.1 hc))

lemma lvl_le (j v : ℕ) : lvl m j v ≤ v := Nat.div_mul_le_self _ _

lemma lvl_mono (j : ℕ) {u v : ℕ} (h : u ≤ v) : lvl m j u ≤ lvl m j v :=
  Nat.mul_le_mul_right _ (Nat.div_le_div_right h)

lemma lvl_eq_self_of_dvd {j v : ℕ} (h : m ^ (j + 1) ∣ v) : lvl m j v = v := by
  unfold lvl; exact Nat.div_mul_cancel h

lemma lvl_lvl (j v : ℕ) : lvl m j (lvl m j v) = lvl m j v :=
  lvl_eq_self_of_dvd (Dvd.intro_left _ rfl)

lemma lvl_eq_of_div_eq {j u v : ℕ} (h : u / m ^ (j + 1) = v / m ^ (j + 1)) :
    lvl m j u = lvl m j v := by
  unfold lvl; rw [h]

/-- Nodes between the left endpoint of an interval and a node of it belong to it. -/
lemma lvl_eq_of_between {j a u v : ℕ} (ha : lvl m j v = a) (hau : a ≤ u) (huv : u ≤ v) :
    lvl m j u = a := by
  apply le_antisymm
  · rw [← ha]; exact lvl_mono j huv
  · have := lvl_mono (m := m) j hau
    rwa [← ha, lvl_lvl, ha] at this

/-- (K6) A multiple `x` of `m^λ` to the right of `p` is to the right of every `i` of the
level-`(λ-1)` interval (block of `m^λ` nodes) of `p`. -/
lemma lt_of_dvd_of_lt {lam p i x : ℕ} (hm : 0 < m) (hx : m ^ lam ∣ x) (hpx : p < x)
    (hpi : p / m ^ lam = i / m ^ lam) : i < x := by
  have hp : 0 < m ^ lam := pow_pos hm _
  obtain ⟨a, rfl⟩ := hx
  have h1 : p / m ^ lam < a := by
    rw [Nat.div_lt_iff_lt_mul hp]; linarith
  have h2 : i < (i / m ^ lam + 1) * m ^ lam := by
    have := Nat.lt_div_mul_add (a := i) hp; linarith
  rw [hpi] at h1
  calc i < (i / m ^ lam + 1) * m ^ lam := h2
    _ ≤ a * m ^ lam := Nat.mul_le_mul_right _ h1
    _ = m ^ lam * a := by ring

/-- (K7) A packet at `u` whose pseudo-buffer has level `j` and intermediate destination `x > i`
lies in the same level-`j` interval as every `i ∈ [u, x)`. -/
lemma div_eq_of_key {u w i : ℕ} (huw : u < w) (hw : w < m ^ ℓ) (hui : u ≤ i)
    (hix : i < xd m ℓ u w) : u / m ^ (lv m ℓ u w + 1) = i / m ^ (lv m ℓ u w + 1) := by
  apply le_antisymm (div_pow_le_div_pow hui _)
  rw [div_succ_eq_xd huw hw]
  exact div_pow_le_div_pow hix.le _

/-- The intermediate destination is a multiple of `m^(j+1)` for every level `j` below the current
one, i.e. it is the left endpoint of all lower-level intervals containing it. -/
lemma dvd_xd_of_lt {i w j : ℕ} (h : j < lv m ℓ i w) : m ^ (j + 1) ∣ xd m ℓ i w :=
  (pow_dvd_pow m h).trans (dvd_xd i w)

/-- The possible pseudo-buffers of node `i`: at most `ℓ m` of them. -/
lemma key_mem_image {i w : ℕ} (hiw : i < w) (hw : w < m ^ ℓ) :
    key m ℓ i w ∈ (Finset.range ℓ ×ˢ Finset.range m).image
      (fun p : ℕ × ℕ => (p.1, i / m ^ (p.1 + 1) * m ^ (p.1 + 1) + p.2 * m ^ p.1)) := by
  obtain ⟨hlt, -, heq⟩ := lv_spec hiw hw
  have hm := (two_le_of_lt hiw hw).1
  refine Finset.mem_image.2 ⟨(lv m ℓ i w, w / m ^ lv m ℓ i w % m), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨hlt, Nat.mod_lt _ (by omega)⟩
  · simp only [key, xd]
    congr 1
    rw [heq, pow_succ, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (w / m ^ lv m ℓ i w) m
    calc w / m ^ lv m ℓ i w / m * (m ^ lv m ℓ i w * m) + w / m ^ lv m ℓ i w % m * m ^ lv m ℓ i w
        = (m * (w / m ^ lv m ℓ i w / m) + w / m ^ lv m ℓ i w % m) * m ^ lv m ℓ i w := by ring
      _ = _ := by rw [this]

end Podc.SmallBuffersAQT
