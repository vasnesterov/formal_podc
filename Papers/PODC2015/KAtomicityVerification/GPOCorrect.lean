import Papers.PODC2015.KAtomicityVerification.GPO

/-!
# Correctness of GPO: Lemmas 4.2–4.5 and Theorem 4.10

Positions are measured from the right: `rpos st v` is the iteration (0-based) in which `v` was
placed, i.e. its distance from the right end of the final value order.
-/

set_option linter.unusedSectionVars false

namespace Podc.KAtomicityVerification

open Finset

variable {V R : Type*} [Fintype V] [LinearOrder V] [Fintype R]

/-- Position of `v` counted from the right end of the suffix `st.T` (`0` = rightmost). -/
def GState.rpos (st : GState V) (v : V) : ℕ := st.T.length - 1 - st.T.idxOf v

namespace History

variable (H : History V R)

variable {H}

/-! ### Elementary facts about one iteration -/

lemma choice_of_full {k : ℕ} {st : GState V} (hU : st.U.Nonempty) (hF : (fullIdx k st).Nonempty) :
    H.choice k st hU ∈ st.B ((fullIdx k st).min' hF) ∧
      ∀ u ∈ st.B ((fullIdx k st).min' hF), H.wf u ≤ H.wf (H.choice k st hU) := by
  unfold choice; rw [dite_eq_left hF]; exact H.pickMax_spec _ _

lemma choice_of_not_full {k : ℕ} {st : GState V} (hU : st.U.Nonempty)
    (hF : ¬ (fullIdx k st).Nonempty) :
    H.choice k st hU ∈ st.U ∧ ∀ u ∈ st.U, H.wf u ≤ H.wf (H.choice k st hU) := by
  unfold choice; rw [dite_eq_right hF]; exact H.pickMax_spec _ _

lemma choice_mem {k : ℕ} {st : GState V} (hU : st.U.Nonempty) (hBU : ∀ i, st.B i ⊆ st.U) :
    H.choice k st hU ∈ st.U := by
  by_cases hF : (fullIdx k st).Nonempty
  · exact hBU _ (choice_of_full hU hF).1
  · exact (choice_of_not_full hU hF).1

lemma rpos_lt {st : GState V} {v : V} (hv : v ∈ st.T) : st.rpos v < st.T.length := by
  unfold GState.rpos
  have := List.idxOf_lt_length_iff.2 hv
  omega

lemma rpos_next_self {k : ℕ} (st : GState V) (hU : st.U.Nonempty) :
    (H.next k st hU).rpos (H.choice k st hU) = st.T.length := by
  simp [GState.rpos, next]

lemma rpos_next_of_mem {k : ℕ} (st : GState V) (hU : st.U.Nonempty) {u : V}
    (huv : u ≠ H.choice k st hU) (hu : u ∈ st.T) :
    (H.next k st hU).rpos u = st.rpos u := by
  have := List.idxOf_lt_length_iff.2 hu
  simp only [GState.rpos, next, List.length_cons, List.idxOf_cons_ne _ (Ne.symm huv)]
  omega

/-! ### The invariant of successful iterations (contains Lemma 4.2) -/

/-- Invariant of every state reached without returning NO. `closed` is Lemma 4.2(b), `memT` is
Lemma 4.2(a); `topo` gives Lemma 4.3, `back`/`oblig` give Lemma 4.4. -/
structure Inv (k : ℕ) (st : GState V) : Prop where
  nodup : st.T.Nodup
  memT : ∀ v, v ∈ st.T ↔ v ∉ st.U
  BU : ∀ i, st.B i ⊆ st.U
  B0 : st.B 0 = ∅
  closed : ∀ i, ∀ v ∈ st.B i, ∀ v' ∈ st.U, H.EW v v' → v' ∈ st.B i
  card : ∀ i, (st.B i).card ≤ i
  topo : ∀ a b, H.EW a b → a ∈ st.T → b ∈ st.T ∧ st.rpos b < st.rpos a
  back : ∀ a b, a ∈ st.T → b ∈ st.T → H.ER a b → st.rpos b < st.rpos a + k
  oblig : ∀ a b, a ∈ st.T → b ∉ st.T → H.ER a b →
    st.T.length - st.rpos a ≤ k - 1 ∧
      ∀ j, j ≤ st.T.length - 1 - st.rpos a → b ∈ st.B (k - 1 - j)

lemma inv_init (k : ℕ) : H.Inv k GState.init where
  nodup := List.nodup_nil
  memT := by simp [GState.init]
  BU := by simp [GState.init]
  B0 := rfl
  closed := by simp [GState.init]
  card := by simp [GState.init]
  topo := by simp [GState.init]
  back := by simp [GState.init]
  oblig := by simp [GState.init]

/-- The chosen value never has an unplaced `G_W` successor (key step of Lemma 4.3). -/
lemma not_EW_choice {k : ℕ} {st : GState V} (hI : H.Inv k st) (hU : st.U.Nonempty) {b : V}
    (hb : b ∈ st.U) : ¬ H.EW (H.choice k st hU) b := by
  intro hvb
  have hlt : H.wf (H.choice k st hU) < H.wf b := lt_trans hvb (H.s_lt_f _)
  by_cases hF : (fullIdx k st).Nonempty
  · obtain ⟨hv, hmax⟩ := choice_of_full (H := H) hU hF
    have := hmax b (hI.closed _ _ hv b hb hvb)
    omega
  · have := (choice_of_not_full (H := H) hU hF).2 b hb
    omega

lemma mem_setW {U : Finset V} {v z : V} :
    z ∈ H.setW U v ↔ z ∈ U ∧ ∃ r : R, H.val r = z ∧ H.hb (.inl v) (.inr r) := by
  simp [setW]

lemma mem_setW' {U W : Finset V} {z : V} :
    z ∈ H.setW' U W ↔ z ∈ U ∧ ∃ y ∈ W, H.EW y z := by
  simp [setW']

lemma next_T {k : ℕ} (st : GState V) (hU : st.U.Nonempty) :
    (H.next k st hU).T = H.choice k st hU :: st.T := rfl

lemma next_U {k : ℕ} (st : GState V) (hU : st.U.Nonempty) :
    (H.next k st hU).U = st.U.erase (H.choice k st hU) := rfl

lemma next_B_zero {k : ℕ} (st : GState V) (hU : st.U.Nonempty) :
    (H.next k st hU).B 0 = ∅ := rfl

lemma next_B_gt {k : ℕ} (st : GState V) (hU : st.U.Nonempty) {i : ℕ} (hi : k - 1 < i) :
    (H.next k st hU).B i = ∅ := by
  simp only [next]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

lemma mem_next_B_lt {k : ℕ} (st : GState V) (hU : st.U.Nonempty) {i : ℕ} (hi1 : 1 ≤ i)
    (hi : i < k - 1) {z : V} :
    z ∈ (H.next k st hU).B i ↔ z ∈ st.B (i + 1) ∧ z ≠ H.choice k st hU := by
  simp only [next]
  rw [ite_eq_right (by omega), ite_eq_left hi]
  simp

lemma mem_next_B_top {k : ℕ} (hk : 2 ≤ k) (st : GState V) (hU : st.U.Nonempty) {z : V} :
    z ∈ (H.next k st hU).B (k - 1) ↔
      (z ∈ st.B (k - 1) ∨ z ∈ H.setW (st.U.erase (H.choice k st hU)) (H.choice k st hU) ∨
        z ∈ H.setW' (st.U.erase (H.choice k st hU))
          (H.setW (st.U.erase (H.choice k st hU)) (H.choice k st hU))) ∧
        z ≠ H.choice k st hU := by
  simp only [next]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp

/-- Membership in the new obligation sets `B'[i]`, `1 ≤ i ≤ k - 1`. -/
lemma next_B_sub {k : ℕ} (hk : 2 ≤ k) (st : GState V) (hU : st.U.Nonempty)
    (hBU : ∀ i, st.B i ⊆ st.U) {i : ℕ}
    (hi1 : 1 ≤ i) (hik : i ≤ k - 1) {z : V} (hz : z ∈ (H.next k st hU).B i) :
    z ≠ H.choice k st hU ∧ z ∈ st.U ∧
      ((i < k - 1 ∧ z ∈ st.B (i + 1)) ∨ (i = k - 1 ∧ (z ∈ st.B (k - 1) ∨
        z ∈ H.setW (st.U.erase (H.choice k st hU)) (H.choice k st hU) ∨
        z ∈ H.setW' (st.U.erase (H.choice k st hU))
          (H.setW (st.U.erase (H.choice k st hU)) (H.choice k st hU))))) := by
  rcases lt_or_eq_of_le hik with hlt | heq
  · rw [mem_next_B_lt st hU hi1 hlt] at hz
    exact ⟨hz.2, hBU _ hz.1, Or.inl ⟨hlt, hz.1⟩⟩
  · subst heq
    rw [mem_next_B_top hk] at hz
    refine ⟨hz.2, ?_, Or.inr ⟨rfl, hz.1⟩⟩
    rcases hz.1 with h | h | h
    · exact hBU _ h
    · exact mem_of_mem_erase ((mem_setW (H := H)).1 h).1
    · exact mem_of_mem_erase ((mem_setW' (H := H)).1 h).1

/-- One successful iteration preserves the invariant (Lemma 4.2 and the bookkeeping behind
Lemmas 4.3–4.4). -/
lemma inv_next {k : ℕ} (hk : 2 ≤ k) {st : GState V} (hI : H.Inv k st) (hU : st.U.Nonempty)
    (hO : ¬ Overfull k (H.next k st hU)) : H.Inv k (H.next k st hU) := by
  set v := H.choice k st hU with hv
  have hvU : v ∈ st.U := choice_mem hU hI.BU
  have hvT : v ∉ st.T := fun h => (hI.memT v).1 h hvU
  have hneT : ∀ u ∈ st.T, u ≠ v := fun u hu h => hvT (h ▸ hu)
  have hlen : (H.next k st hU).T.length = st.T.length + 1 := by simp [next_T]
  have hrv : (H.next k st hU).rpos v = st.T.length := rpos_next_self st hU
  have hru : ∀ u ∈ st.T, (H.next k st hU).rpos u = st.rpos u :=
    fun u hu => rpos_next_of_mem st hU (hneT u hu) hu
  have hmemT' : ∀ u, u ∈ (H.next k st hU).T ↔ u = v ∨ u ∈ st.T := by
    intro u; rw [next_T]; exact List.mem_cons
  have hmemU' : ∀ u, u ∈ (H.next k st hU).U ↔ u ≠ v ∧ u ∈ st.U := by
    intro u; rw [next_U]; exact Finset.mem_erase
  have hcardB : ∀ i, ((H.next k st hU).B i).card ≤ i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [next_B_zero]
    by_cases hik : i ≤ k - 1
    · by_contra h
      exact hO ⟨i, by simp; omega, by omega⟩
    · simp [next_B_gt st hU (show k - 1 < i by omega)]
  refine ⟨?nodup, ?memT, ?BU, ?B0, ?closed, hcardB, ?topo, ?back, ?oblig⟩
  case nodup => rw [next_T]; exact List.nodup_cons.2 ⟨hvT, hI.nodup⟩
  case memT =>
    intro u
    rw [hmemT', hmemU', hI.memT u]
    by_cases h : u = v <;> simp [h, hvU]
  case B0 => exact next_B_zero st hU
  case BU =>
    intro i z hz
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [next_B_zero] at hz
    by_cases hik : i ≤ k - 1
    · obtain ⟨h1, h2, -⟩ := next_B_sub hk st hU hI.BU hi0 hik hz
      exact (hmemU' z).2 ⟨h1, h2⟩
    · simp [next_B_gt st hU (show k - 1 < i by omega)] at hz
  case closed =>
    intro i z hz z' hz' hzz'
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp [next_B_zero] at hz
    by_cases hik : i ≤ k - 1
    swap
    · simp [next_B_gt st hU (show k - 1 < i by omega)] at hz
    obtain ⟨hz'v, hz'U⟩ := (hmemU' z').1 hz'
    obtain ⟨hzv, hzU, hz3⟩ := next_B_sub hk st hU hI.BU hi0 hik hz
    rcases lt_or_eq_of_le hik with hlt | heq
    · rw [mem_next_B_lt st hU hi0 hlt] at hz ⊢
      exact ⟨hI.closed _ z hz.1 z' hz'U hzz', hz'v⟩
    · subst heq
      rw [mem_next_B_top hk] at hz ⊢
      refine ⟨?_, hz'v⟩
      rcases hz.1 with h | h | h
      · exact Or.inl (hI.closed _ z h z' hz'U hzz')
      · exact Or.inr (Or.inr ((mem_setW' (H := H)).2 ⟨by rw [← next_U]; exact hz', z, h, hzz'⟩))
      · obtain ⟨-, y, hy, hyz⟩ := (mem_setW' (H := H)).1 h
        exact Or.inr (Or.inr ((mem_setW' (H := H)).2
          ⟨by rw [← next_U]; exact hz', y, hy, EW_trans hyz hzz'⟩))
  case topo =>
    intro a b hab ha
    rcases (hmemT' a).1 ha with rfl | ha
    · have hbU : b ∉ (H.next k st hU).U := by
        intro hb
        exact not_EW_choice hI hU ((hmemU' b).1 hb).2 hab
      have hb : b ∈ (H.next k st hU).T := by
        by_contra hb
        rw [hmemT', not_or] at hb
        exact hbU ((hmemU' b).2 ⟨hb.1, by
          by_contra h; exact hb.2 ((hI.memT b).2 h)⟩)
      refine ⟨hb, ?_⟩
      rcases (hmemT' b).1 hb with rfl | hbT
      · exact absurd hab (EW_irrefl _)
      · rw [hru b hbT, hrv]; exact rpos_lt hbT
    · obtain ⟨hbT, hlt⟩ := hI.topo a b hab ha
      refine ⟨(hmemT' b).2 (Or.inr hbT), ?_⟩
      rw [hru a ha, hru b hbT]; exact hlt
  case back =>
    intro a b ha hb hab
    rcases (hmemT' a).1 ha with rfl | ha <;> rcases (hmemT' b).1 hb with rfl | hb
    · exact absurd rfl hab.1
    · rw [hru b hb, hrv]; have := rpos_lt hb; omega
    · rw [hru a ha, hrv]
      have := (hI.oblig _ _ ha hvT hab).1
      have := rpos_lt ha
      omega
    · rw [hru a ha, hru b hb]; exact hI.back a b ha hb hab
  case oblig =>
    intro a b ha hb hab
    rw [hmemT', not_or] at hb
    obtain ⟨hbv, hbT⟩ := hb
    have hbU : b ∈ st.U := by by_contra h; exact hbT ((hI.memT b).2 h)
    have hbU' : b ∈ st.U.erase v := by simp [hbv, hbU]
    rw [hlen]
    rcases (hmemT' a).1 ha with rfl | ha
    · rw [hrv]
      refine ⟨by omega, fun j hj => ?_⟩
      have hj0 : j = 0 := by omega
      subst hj0
      rw [show k - 1 - 0 = k - 1 by omega, mem_next_B_top hk]
      obtain ⟨-, r, hr, hbr⟩ := hab
      exact ⟨Or.inr (Or.inl ((mem_setW (H := H)).2 ⟨hbU', r, hr, hbr⟩)), hbv⟩
    · rw [hru a ha]
      obtain ⟨hd, hB⟩ := hI.oblig a b ha hbT hab
      have hra := rpos_lt ha
      have hd' : st.T.length + 1 - st.rpos a ≤ k - 1 := by
        by_contra hcon
        have hb1 : b ∈ st.B 1 := by
          have := hB (k - 2) (by omega)
          rwa [show k - 1 - (k - 2) = 1 by omega] at this
        have hc1 := hI.card 1
        have hB1 : st.B 1 = {b} := by
          rw [Finset.card_le_one] at hc1
          ext u; simp only [mem_singleton]
          exact ⟨fun hu => hc1 u hu b hb1, fun h => h ▸ hb1⟩
        have h1F : 1 ∈ fullIdx k st := by
          rw [mem_fullIdx, hB1]; simp; omega
        have hF : (fullIdx k st).Nonempty := ⟨1, h1F⟩
        have hmin : (fullIdx k st).min' hF = 1 := by
          apply le_antisymm (min'_le _ _ h1F)
          have := min'_mem _ hF
          rw [mem_fullIdx] at this; exact this.1
        have := (choice_of_full (H := H) hU hF).1
        rw [hmin, hB1, mem_singleton] at this
        exact hbv this.symm
      refine ⟨hd', fun j hj => ?_⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [show k - 1 - 0 = k - 1 by omega, mem_next_B_top hk]
        exact ⟨Or.inl (by have := hB 0 (by omega); rwa [show k - 1 - 0 = k - 1 by omega] at this),
          hbv⟩
      · rw [mem_next_B_lt st hU (by omega) (by omega)]
        refine ⟨?_, hbv⟩
        have := hB (j - 1) (by omega)
        rwa [show k - 1 - (j - 1) = k - 1 - j + 1 by omega] at this

lemma inv_step {k : ℕ} (hk : 2 ≤ k) {st st' : GState V} (hI : H.Inv k st)
    (h : H.step k st = some st') : H.Inv k st' := by
  unfold step at h
  split_ifs at h with hU hO
  · cases h; exact inv_next hk hI hU hO
  · cases h; exact hI

lemma inv_run {k : ℕ} (hk : 2 ≤ k) : ∀ (n : ℕ) {st st' : GState V}, H.Inv k st →
    H.run k n st = some st' → H.Inv k st'
  | 0, st, st', hI, h => by cases h; exact hI
  | n + 1, st, st', hI, h => by
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    exact inv_run hk n (inv_step hk hI h1) h2

lemma card_run {k : ℕ} (hk : 2 ≤ k) : ∀ (n : ℕ) {st st' : GState V}, H.Inv k st →
    H.run k n st = some st' → st'.U.card = st.U.card - n
  | 0, st, st', hI, h => by cases h; rfl
  | n + 1, st, st', hI, h => by
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨s1, h1, h2⟩ := h
    have := card_run hk n (inv_step hk hI h1) h2
    rw [this]
    unfold step at h1
    split_ifs at h1 with hU hO
    · cases h1
      rw [next_U, card_erase_of_mem (choice_mem hU hI.BU)]
      omega
    · cases h1
      rw [not_nonempty_iff_eq_empty] at hU
      simp [hU]

/-- If GPO answers YES, the final state has placed every value and satisfies the invariant. -/
lemma final_of_gpo {k : ℕ} (hk : 2 ≤ k) (h : H.gpo k = true) :
    ∃ st, H.run k (Fintype.card V) GState.init = some st ∧ H.Inv k st ∧ st.U = ∅ := by
  unfold gpo at h
  obtain ⟨st, hst⟩ := Option.isSome_iff_exists.1 h
  refine ⟨st, hst, inv_run hk _ (inv_init k) hst, ?_⟩
  have := card_run hk _ (inv_init (H := H) k) hst
  simp [GState.init] at this
  exact this

/-- **Lemma 4.3** of [Golab–Li–López-Ortiz–Nishimura]. If GPO outputs YES, the constructed
sequence `T` is a topological ordering of `G_W`. -/
theorem lemma_4_3 {k : ℕ} (hk : 2 ≤ k) {st : GState V}
    (hst : H.run k (Fintype.card V) GState.init = some st) (hU : st.U = ∅) :
    H.IsTopoOrder st.T := by
  have hI := inv_run hk _ (inv_init (H := H) k) hst
  have hall : ∀ v, v ∈ st.T := fun v => (hI.memT v).2 (by simp [hU])
  refine ⟨hI.nodup, hall, fun i j hi hj h => ?_⟩
  have := (hI.topo _ _ h (hall _)).2
  simp only [GState.rpos, hI.nodup.idxOf_getElem] at this
  omega

/-- **Lemma 4.4** (list form). If GPO outputs YES, the constructed sequence `T` is a `k`-atomic
value order (the condition of Lemma 3.8). -/
theorem valueOrder_of_gpo {k : ℕ} (hk : 2 ≤ k) {st : GState V}
    (hst : H.run k (Fintype.card V) GState.init = some st) (hU : st.U = ∅) :
    H.IsKAtomicValueOrder k st.T := by
  have hI := inv_run hk _ (inv_init (H := H) k) hst
  have hT := lemma_4_3 hk hst hU
  refine ⟨hT.nodup, hT.complete, hT.topo, fun i j hi hj h => ?_⟩
  have := hI.back _ _ (hT.complete _) (hT.complete _) h
  simp only [GState.rpos, hI.nodup.idxOf_getElem] at this
  omega

/-- **Lemma 4.4** of [Golab–Li–López-Ortiz–Nishimura]. If GPO outputs YES then `H` is
`k`-atomic (for `k ≥ 2`, under Assumption 3.4). -/
theorem lemma_4_4 (hA : H.Assumption34) {k : ℕ} (hk : 2 ≤ k) (h : H.gpo k = true) :
    H.KAtomic k := by
  obtain ⟨st, hst, -, hU⟩ := final_of_gpo hk h
  exact (kAtomic_iff_exists_valueOrder hA (by omega)).2 ⟨st.T, valueOrder_of_gpo hk hst hU⟩

end History

end Podc.KAtomicityVerification
