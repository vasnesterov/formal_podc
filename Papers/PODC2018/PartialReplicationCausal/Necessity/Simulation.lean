import Papers.PODC2018.PartialReplicationCausal.Necessity.Phase

/-!
# Theorem 1: comparing two executions that differ by one extra update

Execution `E₁` has one extra update at index `b` (the second write `u_B` of `j`, right after `u_A`
at index `b - 1`); the update of index `a` of `E₂` has index `shift b a` in `E₁`.

* `LogSim b s₁ s₂`: the logs and applied sets correspond (up to `u_B`), and `u_B` depends on
  exactly what `u_A` depends on plus `u_A`. It is preserved by corresponding writes and by closes
  (which apply *all* updates sent to the closing replica), and implies that the causal dependency
  graphs of every replica differ only in `u_B` (`diffOnly_of_logSim`).
* `MdSim b w S s₁ s₂`: for the replicas of `S`, metadata and applied sets coincide, and pending
  updates carry the same metadata. It is preserved by writes, applies and closes of replicas of `S`
  that do not store the register `w` of `u_B` (the closes make the same choices).
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*} {X : ι → Set Reg} {A : Alg ι Reg M}

namespace T1

/-- Index map from the execution without the extra update `b` to the one with it. -/
def shift (b a : ℕ) : ℕ := if a < b then a else a + 1

section shift

variable {b : ℕ}

lemma shift_of_lt {a : ℕ} (h : a < b) : shift b a = a := by simp [shift, h]
lemma shift_of_ge {a : ℕ} (h : b ≤ a) : shift b a = a + 1 := by
  simp [shift, show ¬ a < b by omega]
lemma shift_ne (a : ℕ) : shift b a ≠ b := by unfold shift; split_ifs <;> omega
lemma shift_inj {a a' : ℕ} (h : shift b a = shift b a') : a = a' := by
  unfold shift at h; split_ifs at h <;> omega
lemma shift_lt_shift {a a' : ℕ} : shift b a < shift b a' ↔ a < a' := by
  unfold shift; split_ifs <;> omega
lemma shift_le_shift {a a' : ℕ} : shift b a ≤ shift b a' ↔ a ≤ a' := by
  unfold shift; split_ifs <;> omega
lemma exists_shift {c : ℕ} (h : c ≠ b) : ∃ a, shift b a = c := by
  by_cases hc : c < b
  · exact ⟨c, shift_of_lt hc⟩
  · exact ⟨c - 1, by rw [shift_of_ge (by omega)]; omega⟩
lemma shift_lt_iff {n a : ℕ} (hb : b ≤ n) : shift b a < n + 1 ↔ a < n := by
  unfold shift; split_ifs <;> omega
lemma shift_pred (hb : 0 < b) : shift b (b - 1) = b - 1 := shift_of_lt (by omega)

end shift

/-! ### Log-level simulation -/

/-- Log-level correspondence between `s₁` (with the extra update `b`) and `s₂`. -/
structure LogSim (b : ℕ) (s₁ s₂ : St ι Reg M) : Prop where
  n_eq : s₁.n = s₂.n + 1
  b_pos : 0 < b
  b_le : b ≤ s₂.n
  src : ∀ a < s₂.n, (s₁.log (shift b a)).src = (s₂.log a).src
  reg : ∀ a < s₂.n, (s₁.log (shift b a)).reg = (s₂.log a).reg
  lab : ∀ a < s₂.n, (s₁.log (shift b a)).lab = (s₂.log a).lab
  pre : ∀ a < s₂.n, ∀ c, shift b c ∈ (s₁.log (shift b a)).pre ↔ c ∈ (s₂.log a).pre
  pre_b : ∀ a < s₂.n, b ∈ (s₁.log (shift b a)).pre → b - 1 ∈ (s₁.log (shift b a)).pre
  preB : (s₁.log b).pre = insert (b - 1) (s₁.log (b - 1)).pre
  regB : (s₁.log b).reg = (s₁.log (b - 1)).reg
  app : ∀ r a, shift b a ∈ s₁.app r ↔ a ∈ s₂.app r
  app_b : ∀ r, b ∈ s₁.app r → b - 1 ∈ s₁.app r

namespace LogSim

variable {b : ℕ} {s₁ s₂ : St ι Reg M}

lemma shift_lt (h : LogSim b s₁ s₂) {a : ℕ} (ha : a < s₂.n) : shift b a < s₁.n := by
  rw [h.n_eq]; exact (shift_lt_iff h.b_le).2 ha

lemma lt_of_shift_lt (h : LogSim b s₁ s₂) {a : ℕ} (ha : shift b a < s₁.n) : a < s₂.n := by
  rw [h.n_eq] at ha; exact (shift_lt_iff h.b_le).1 ha

lemma b_lt (h : LogSim b s₁ s₂) : b < s₁.n := by have := h.b_le; have := h.n_eq; omega

lemma key_eq (h : LogSim b s₁ s₂) {a : ℕ} (ha : a < s₂.n) : key s₁ (shift b a) = key s₂ a := by
  simp only [key, h.src a ha, h.reg a ha, h.lab a ha]

/-- Logs unchanged, applied sets changed compatibly. -/
lemma of_app (h : LogSim b s₁ s₂) {s₁' s₂' : St ι Reg M} (hn₁ : s₁'.n = s₁.n)
    (hl₁ : s₁'.log = s₁.log) (hn₂ : s₂'.n = s₂.n) (hl₂ : s₂'.log = s₂.log)
    (happ : ∀ r a, shift b a ∈ s₁'.app r ↔ a ∈ s₂'.app r)
    (happ_b : ∀ r, b ∈ s₁'.app r → b - 1 ∈ s₁'.app r) : LogSim b s₁' s₂' := by
  refine ⟨?_, h.b_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, happ, happ_b⟩
  · rw [hn₁, hn₂]; exact h.n_eq
  · rw [hn₂]; exact h.b_le
  · rw [hl₁, hl₂, hn₂]; exact h.src
  · rw [hl₁, hl₂, hn₂]; exact h.reg
  · rw [hl₁, hl₂, hn₂]; exact h.lab
  · rw [hl₁, hl₂, hn₂]; exact h.pre
  · rw [hl₁, hn₂]; exact h.pre_b
  · rw [hl₁]; exact h.preB
  · rw [hl₁]; exact h.regB

lemma write (h : LogSim b s₁ s₂) (r : ι) (x : Reg) (ℓ : ℕ) :
    LogSim b (s₁.write A r x ℓ) (s₂.write A r x ℓ) := by
  have hn : shift b s₂.n = s₁.n := by rw [shift_of_ge h.b_le, h.n_eq]
  have hlt : ∀ a < s₂.n, shift b a < s₁.n := fun a ha => h.shift_lt ha
  have hb := h.b_lt
  have hb1 : b - 1 < s₁.n := by omega
  have cases : ∀ a < s₂.n + 1, a < s₂.n ∨ a = s₂.n := fun a ha => by omega
  refine ⟨by simp [h.n_eq], h.b_pos, by simp; have := h.b_le; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha), write_log_lt _ _ _ _ ha]; exact h.src a ha
    · rw [hn]; simp
  · intro a ha; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha), write_log_lt _ _ _ _ ha]; exact h.reg a ha
    · rw [hn]; simp
  · intro a ha; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha), write_log_lt _ _ _ _ ha]; exact h.lab a ha
    · rw [hn]; simp
  · intro a ha c; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha), write_log_lt _ _ _ _ ha]; exact h.pre a ha c
    · rw [hn]; simp only [write_log_n]; exact h.app r c
  · intro a ha; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha)]; exact h.pre_b a ha
    · rw [hn]; simp only [write_log_n]; exact h.app_b r
  · rw [write_log_lt _ _ _ _ hb, write_log_lt _ _ _ _ hb1]; exact h.preB
  · rw [write_log_lt _ _ _ _ hb, write_log_lt _ _ _ _ hb1]; exact h.regB
  · intro r' a
    rw [write_app, write_app]
    split_ifs
    · simp only [Set.mem_insert_iff, h.app r a, ← hn]
      exact or_congr ⟨fun h' => shift_inj h', fun h' => h' ▸ rfl⟩ Iff.rfl
    · exact h.app r' a
  · intro r' hr'
    rw [write_app] at hr' ⊢
    split_ifs at hr' ⊢
    · rcases hr' with h' | h'
      · omega
      · exact Set.mem_insert_of_mem _ (h.app_b _ h')
    · exact h.app_b _ hr'

lemma apply (h : LogSim b s₁ s₂) (r : ι) (a : ℕ) :
    LogSim b (s₁.apply A r (shift b a)) (s₂.apply A r a) := by
  refine h.of_app rfl rfl rfl rfl ?_ ?_
  · intro r' c
    rw [apply_app, apply_app]
    split_ifs
    · simp only [Set.mem_insert_iff, h.app r c]
      exact or_congr ⟨fun h' => shift_inj h', fun h' => h' ▸ rfl⟩ Iff.rfl
    · exact h.app r' c
  · intro r' hr'
    rw [apply_app] at hr' ⊢
    split_ifs at hr' ⊢
    · rcases hr' with h' | h'
      · exact absurd h'.symm (shift_ne a)
      · exact Set.mem_insert_of_mem _ (h.app_b _ h')
    · exact h.app_b _ hr'

lemma close [Fintype ι] (hA : Implements X A) (h : LogSim b s₁ s₂) (hs₁ : Reachable X A s₁)
    (hs₂ : Reachable X A s₂) (p : ι) : LogSim b (close X A p s₁) (close X A p s₂) := by
  refine h.of_app (close_n _) (close_log _) (close_n _) (close_log _) ?_ ?_
  · intro r a
    by_cases hr : r = p
    · subst hr
      rw [close_app_iff hA hs₁, close_app_iff hA hs₂]
      constructor
      · rintro ⟨h1, h2⟩
        have ha := h.lt_of_shift_lt h1
        exact ⟨ha, h.reg a ha ▸ h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h.shift_lt h1, (h.reg a h1).symm ▸ h2⟩
    · rw [close_app_ne _ hr, close_app_ne _ hr]; exact h.app r a
  · intro r hr'
    by_cases hr : r = p
    · subst hr
      rw [close_app_iff hA hs₁] at hr' ⊢
      exact ⟨by omega, h.regB ▸ hr'.2⟩
    · rw [close_app_ne _ hr] at hr' ⊢; exact h.app_b r hr'

lemma phase [Fintype ι] (hA : Implements X A) {c : ℕ} (L : List (ι × Reg))
    (hL : ∀ q ∈ L, q.2 ∈ X q.1) : ∀ {s₁ s₂ : St ι Reg M}, LogSim b s₁ s₂ → Reachable X A s₁ →
      Reachable X A s₂ → LabBound c s₁ → LabBound (c + 1) s₂ →
      LogSim b (phase X A c L s₁) (phase X A (c + 1) L s₂) := by
  induction L with
  | nil => intro s₁ s₂ h _ _ _ _; exact h
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    intro s₁ s₂ h hs₁ hs₂ hc₁ hc₂
    have hL' : ∀ q ∈ L, q.2 ∈ X q.1 := fun q hq => hL q (by simp [hq])
    have r1 := reach_phase (X := X) (A := A) c [(p, x)] (fun q hq => hL q (by simp_all)) s₁ hs₁ hc₁
    have r2 := reach_phase (X := X) (A := A) (c + 1) [(p, x)] (fun q hq => hL q (by simp_all))
      s₂ hs₂ hc₂
    simp only [phase_cons, phase_nil] at r1 r2
    rw [phase_cons, phase_cons]
    have hlab : c + s₁.n = c + 1 + s₂.n := by rw [h.n_eq]; ring
    rw [hlab] at r1 ⊢
    exact ih hL' (((h.close hA hs₁ hs₂ p).write p x _)) (Reachable.rtg hs₁ r1.1)
      (Reachable.rtg hs₂ r2.1) r1.2 r2.2

/-! #### Happened-before and causal pasts -/

lemma hb_fwd (h : LogSim b s₁ s₂) {a c : ℕ} (hac : HB s₂ a c) : HB s₁ (shift b a) (shift b c) := by
  induction hac with
  | single h' => exact hb_single (h.shift_lt h'.1) ((h.pre _ h'.1 _).2 h'.2)
  | tail _ h' ih => exact ih.tail ⟨h.shift_lt h'.1, (h.pre _ h'.1 _).2 h'.2⟩

lemma hb_back (h : LogSim b s₁ s₂) (hinv : Inv X s₁) {x y : ℕ} (hxy : HB s₁ x y) :
    ∀ y', y = shift b y' → (∀ x', x = shift b x' → HB s₂ x' y') ∧ (x = b → HB s₂ (b - 1) y') := by
  have hpb : shift b (b - 1) = b - 1 := shift_pred h.b_pos
  induction hxy using Relation.TransGen.head_induction_on with
  | @single x hR =>
    intro y' hy
    obtain ⟨hyn, hx⟩ := hR
    subst hy
    have hy' := h.lt_of_shift_lt hyn
    refine ⟨fun x' hx' => ?_, fun hxb => ?_⟩
    · subst hx'; exact hb_single hy' ((h.pre _ hy' _).1 hx)
    · subst hxb
      have := h.pre_b _ hy' hx
      rw [← hpb] at this
      exact hb_single hy' ((h.pre _ hy' _).1 this)
  | @head x z hR _ ih =>
    intro y' hy
    obtain ⟨hzn, hx⟩ := hR
    obtain ⟨ih1, ih2⟩ := ih y' hy
    by_cases hz : z = b
    · subst hz
      have hxb : x < z := hinv.pre_lt _ hzn _ hx
      have hih := ih2 rfl
      refine ⟨fun x' hx' => ?_, fun hxb' => by omega⟩
      rw [h.preB] at hx
      rcases hx with hx | hx
      · have : x' = z - 1 := by rw [hx, ← hpb] at hx'; exact (shift_inj hx').symm
        subst this; exact hih
      · have hz1 : z - 1 < s₂.n := by have := h.b_le; omega
        rw [← hpb, hx'] at hx
        exact (hb_single hz1 ((h.pre _ hz1 _).1 hx)).trans hih
    · obtain ⟨z', rfl⟩ := exists_shift hz
      have hz' := h.lt_of_shift_lt hzn
      have hih := ih1 z' rfl
      refine ⟨fun x' hx' => ?_, fun hxb => ?_⟩
      · subst hx'; exact hih.head ⟨hz', (h.pre _ hz' _).1 hx⟩
      · subst hxb
        have := h.pre_b _ hz' hx
        rw [← hpb] at this
        exact hih.head ⟨hz', (h.pre _ hz' _).1 this⟩

lemma hb_iff (h : LogSim b s₁ s₂) (hinv : Inv X s₁) (a c : ℕ) :
    HB s₁ (shift b a) (shift b c) ↔ HB s₂ a c :=
  ⟨fun h' => (h.hb_back hinv h' c rfl).1 a rfl, h.hb_fwd⟩

lemma hb_b (h : LogSim b s₁ s₂) {x : ℕ} : HB s₁ x b ↔ x = b - 1 ∨ HB s₁ x (b - 1) :=
  hb_insert h.b_lt (by have := h.b_lt; omega) h.preB

lemma cp_fwd (h : LogSim b s₁ s₂) {i : ι} {a : ℕ} (ha : a ∈ CP s₂ i) : shift b a ∈ CP s₁ i := by
  rcases ha with ha | ⟨c, hc, hac⟩
  · exact .inl ((h.app i a).2 ha)
  · exact .inr ⟨shift b c, (h.app i c).2 hc, h.hb_fwd hac⟩

lemma cp_back (h : LogSim b s₁ s₂) (hinv : Inv X s₁) {i : ι} {x : ℕ} (hx : x ∈ CP s₁ i)
    (hxb : x ≠ b) : ∃ a, x = shift b a ∧ a ∈ CP s₂ i := by
  obtain ⟨a, rfl⟩ := exists_shift hxb
  refine ⟨a, rfl, ?_⟩
  have hpb : shift b (b - 1) = b - 1 := shift_pred h.b_pos
  rcases hx with hx | ⟨y, hy, hxy⟩
  · exact .inl ((h.app i a).1 hx)
  · by_cases hyb : y = b
    · rw [hyb] at hy hxy
      have hb1 := h.app_b i hy
      rcases h.hb_b.1 hxy with hx | hx
      · have : a = b - 1 := shift_inj (hx.trans hpb.symm)
        subst this
        exact .inl ((h.app i _).1 (by rw [hpb]; exact hb1))
      · rw [← hpb] at hb1 hx
        exact .inr ⟨b - 1, (h.app i _).1 hb1, (h.hb_iff hinv _ _).1 hx⟩
    · obtain ⟨y', rfl⟩ := exists_shift hyb
      exact .inr ⟨y', (h.app i _).1 hy, (h.hb_iff hinv _ _).1 hxy⟩

/-- The causal dependency graphs of `i` in `s₁` and `s₂` differ only in the extra update `b`. -/
theorem diffOnly (h : LogSim b s₁ s₂) (hinv₁ : Inv X s₁) (hinv₂ : Inv X s₂) {i j k : ι}
    (hj : (s₁.log b).src = j) (hw : (s₁.log b).reg ∈ X j ∩ X k) : DiffOnly X s₁ s₂ i j k := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha hno
    by_cases hab : a = b
    · subst hab; exact ⟨hj, hw⟩
    · obtain ⟨a', rfl, ha'⟩ := h.cp_back hinv₁ ha hab
      exact absurd ⟨a', ha', (h.key_eq (hinv₂.cp_lt ha')).symm⟩ hno
  · intro c hc hno
    exact absurd ⟨shift b c, h.cp_fwd hc, h.key_eq (hinv₂.cp_lt hc)⟩ hno
  · intro a ha a' ha' c hc c' hc' hk hk'
    have hc2 := hinv₂.cp_lt hc
    have hc2' := hinv₂.cp_lt hc'
    have e1 : a = shift b c := by
      rw [← h.key_eq hc2] at hk
      exact hinv₁.lab_inj _ (hinv₁.cp_lt ha) _ (h.shift_lt hc2) (congrArg Prod.fst hk)
    have e2 : a' = shift b c' := by
      rw [← h.key_eq hc2'] at hk'
      exact hinv₁.lab_inj _ (hinv₁.cp_lt ha') _ (h.shift_lt hc2') (congrArg Prod.fst hk')
    subst e1 e2
    exact h.hb_iff hinv₁ _ _

end LogSim

/-- Causal dependency graphs of `i` in a state and an extension of it differ only in updates on
`e_jk`, if the extra causal past consists of such updates. -/
theorem diffOnly_of_ext {s₁ s₂ : St ι Reg M} (hinv₁ : Inv X s₁) (hinv₂ : Inv X s₂) (he : Ext s₁ s₂)
    {i j k : ι} (hsub : CP s₁ i ⊆ CP s₂ i)
    (hnew : ∀ a ∈ CP s₂ i, a ∉ CP s₁ i → (s₂.log a).src = j ∧ (s₂.log a).reg ∈ X j ∩ X k) :
    DiffOnly X s₁ s₂ i j k := by
  have hkey : ∀ a < s₁.n, key s₂ a = key s₁ a := fun a ha => by simp [key, he.log_eq a ha]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha hno
    exact absurd ⟨a, hsub ha, hkey a (hinv₁.cp_lt ha)⟩ hno
  · intro c hc hno
    refine hnew c hc fun hc1 => hno ⟨c, hc1, ?_⟩
    exact (hkey c (hinv₁.cp_lt hc1)).symm
  · intro a ha a' ha' c hc c' hc' hk hk'
    have h1 := hinv₁.cp_lt ha
    have h1' := hinv₁.cp_lt ha'
    rw [← hkey a h1] at hk
    rw [← hkey a' h1'] at hk'
    have e1 := hinv₂.lab_inj _ (lt_of_lt_of_le h1 he.n_le) _ (hinv₂.cp_lt hc) (congrArg Prod.fst hk)
    have e2 := hinv₂.lab_inj _ (lt_of_lt_of_le h1' he.n_le) _ (hinv₂.cp_lt hc')
      (congrArg Prod.fst hk')
    subst e1 e2
    exact (he.hb_iff hinv₁ h1').symm

/-! ### Metadata-level simulation -/

/-- Metadata-level correspondence on the replicas of `S`; `w` is the register of the extra update. -/
structure MdSim (b : ℕ) (w : Reg) (S : Set ι) (s₁ s₂ : St ι Reg M) : Prop where
  n_eq : s₁.n = s₂.n + 1
  b_le : b ≤ s₂.n
  src : ∀ a < s₂.n, (s₁.log (shift b a)).src = (s₂.log a).src
  reg : ∀ a < s₂.n, (s₁.log (shift b a)).reg = (s₂.log a).reg
  ts : ∀ r ∈ S, ∀ a < s₂.n, (s₂.log a).reg ∈ X r → a ∉ s₂.app r →
    (s₁.log (shift b a)).ts = (s₂.log a).ts
  md : ∀ r ∈ S, s₁.md r = s₂.md r
  app : ∀ r ∈ S, ∀ a, shift b a ∈ s₁.app r ↔ a ∈ s₂.app r
  regB : (s₁.log b).reg = w

namespace MdSim

variable {b : ℕ} {w : Reg} {S : Set ι} {s₁ s₂ : St ι Reg M}

lemma shift_lt (h : MdSim (X := X) b w S s₁ s₂) {a : ℕ} (ha : a < s₂.n) : shift b a < s₁.n := by
  rw [h.n_eq]; exact (shift_lt_iff h.b_le).2 ha

lemma lt_of_shift_lt (h : MdSim (X := X) b w S s₁ s₂) {a : ℕ} (ha : shift b a < s₁.n) :
    a < s₂.n := by
  rw [h.n_eq] at ha; exact (shift_lt_iff h.b_le).1 ha

lemma b_lt (h : MdSim (X := X) b w S s₁ s₂) : b < s₁.n := by
  have := h.b_le; have := h.n_eq; omega

lemma enabled_iff (h : MdSim (X := X) b w S s₁ s₂) {r : ι} (hr : r ∈ S) (a : ℕ) :
    Enabled X A s₁ r (shift b a) ↔ Enabled X A s₂ r a := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have ha := h.lt_of_shift_lt h1
    rw [h.src a ha] at h2 h5
    rw [h.reg a ha] at h3 h5
    rw [h.app r hr] at h4
    rw [h.md r hr, h.ts r hr a ha h3 h4] at h5
    exact ⟨ha, h2, h3, h4, h5⟩
  · rintro ⟨ha, h2, h3, h4, h5⟩
    refine ⟨h.shift_lt ha, ?_, ?_, ?_, ?_⟩
    · rwa [h.src a ha]
    · rwa [h.reg a ha]
    · rwa [h.app r hr]
    · rwa [h.src a ha, h.reg a ha, h.md r hr, h.ts r hr a ha h3 h4]

lemma not_enabled_b (h : MdSim (X := X) b w S s₁ s₂) {r : ι} (hw : w ∉ X r) :
    ¬ Enabled X A s₁ r b := fun he => hw (h.regB ▸ he.2.2.1)

lemma write (h : MdSim (X := X) b w S s₁ s₂) {r : ι} (hr : r ∈ S) (x : Reg) (ℓ₁ ℓ₂ : ℕ) :
    MdSim (X := X) b w S (s₁.write A r x ℓ₁) (s₂.write A r x ℓ₂) := by
  have hn : shift b s₂.n = s₁.n := by rw [shift_of_ge h.b_le, h.n_eq]
  have hlt : ∀ a < s₂.n, shift b a < s₁.n := fun a ha => h.shift_lt ha
  have cases : ∀ a < s₂.n + 1, a < s₂.n ∨ a = s₂.n := fun a ha => by omega
  refine ⟨by simp [h.n_eq], by simp; have := h.b_le; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha), write_log_lt _ _ _ _ ha]; exact h.src a ha
    · rw [hn]; simp
  · intro a ha; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha), write_log_lt _ _ _ _ ha]; exact h.reg a ha
    · rw [hn]; simp
  · intro r' hr' a ha hreg happ; simp only [write_n] at ha
    rcases cases a ha with ha | rfl
    · rw [write_log_lt _ _ _ _ (hlt a ha), write_log_lt _ _ _ _ ha]
      rw [write_log_lt _ _ _ _ ha] at hreg
      exact h.ts r' hr' a ha hreg (fun h' => happ (subset_write_app _ _ _ _ _ h'))
    · rw [hn]; simp [h.md r hr]
  · intro r' hr'
    rw [write_md, write_md]
    split_ifs with h'
    · rw [h.md r hr]
    · exact h.md r' hr'
  · intro r' hr' a
    rw [write_app, write_app]
    split_ifs with h'
    · subst h'
      simp only [Set.mem_insert_iff, h.app r' hr' a, ← hn]
      exact or_congr ⟨fun h' => shift_inj h', fun h' => h' ▸ rfl⟩ Iff.rfl
    · exact h.app r' hr' a
  · rw [write_log_lt _ _ _ _ h.b_lt]; exact h.regB

lemma apply (h : MdSim (X := X) b w S s₁ s₂) {r : ι} (hr : r ∈ S) {a : ℕ}
    (ha : Enabled X A s₂ r a) : MdSim (X := X) b w S (s₁.apply A r (shift b a)) (s₂.apply A r a) := by
  obtain ⟨ha1, -, ha3, ha4, -⟩ := ha
  refine ⟨h.n_eq, h.b_le, h.src, h.reg, ?_, ?_, ?_, h.regB⟩
  · intro r' hr' c hc hreg happ
    exact h.ts r' hr' c hc hreg (fun h' => happ (subset_apply_app _ _ _ _ h'))
  · intro r' hr'
    rw [apply_md, apply_md]
    split_ifs with h'
    · simp only [h.md r hr, h.src a ha1, h.reg a ha1, h.ts r hr a ha1 ha3 ha4]
    · exact h.md r' hr'
  · intro r' hr' c
    rw [apply_app, apply_app]
    split_ifs with h'
    · subst h'
      simp only [Set.mem_insert_iff, h.app r' hr' c]
      exact or_congr ⟨fun h' => shift_inj h', fun h' => h' ▸ rfl⟩ Iff.rfl
    · exact h.app r' hr' c

lemma stepMin (h : MdSim (X := X) b w S s₁ s₂) {r : ι} (hr : r ∈ S) (hw : w ∉ X r) :
    MdSim (X := X) b w S (stepMin X A r s₁) (stepMin X A r s₂) := by
  by_cases h2 : ∃ a, Enabled X A s₂ r a
  · have h1 : ∃ a, Enabled X A s₁ r a :=
      ⟨shift b (Nat.find h2), (h.enabled_iff hr _).2 (Nat.find_spec h2)⟩
    have heq : Nat.find h1 = shift b (Nat.find h2) := by
      apply le_antisymm (Nat.find_min' h1 ((h.enabled_iff hr _).2 (Nat.find_spec h2)))
      have hc := Nat.find_spec h1
      have hcb : Nat.find h1 ≠ b := fun e => h.not_enabled_b hw (e ▸ hc)
      obtain ⟨c', hc'⟩ := exists_shift hcb
      rw [← hc'] at hc ⊢
      exact shift_le_shift.2 (Nat.find_min' h2 ((h.enabled_iff hr _).1 hc))
    unfold T1.stepMin
    rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2), heq]
    exact h.apply hr (Nat.find_spec h2)
  · have h1 : ¬ ∃ a, Enabled X A s₁ r a := by
      rintro ⟨c, hc⟩
      have hcb : c ≠ b := fun e => h.not_enabled_b hw (e ▸ hc)
      obtain ⟨c', rfl⟩ := exists_shift hcb
      exact h2 ⟨c', (h.enabled_iff hr _).1 hc⟩
    push Not at h1 h2
    rw [stepMin_of_not _ h1, stepMin_of_not _ h2]
    exact h

lemma close (h : MdSim (X := X) b w S s₁ s₂) {r : ι} (hr : r ∈ S) (hw : w ∉ X r) :
    MdSim (X := X) b w S (close X A r s₁) (close X A r s₂) := by
  have key : ∀ m, MdSim (X := X) b w S ((T1.stepMin X A r)^[m] s₁) ((T1.stepMin X A r)^[m] s₂) := by
    intro m
    induction m with
    | zero => exact h
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ih.stepMin hr hw
  have hfix : (T1.stepMin X A r)^[s₂.n + 1] s₂ = T1.close X A r s₂ := by
    rw [Function.iterate_succ_apply']
    exact stepMin_of_not _ (close_noEnabled s₂)
  unfold T1.close
  rw [h.n_eq]
  have := key (s₂.n + 1)
  rwa [hfix] at this

lemma phase (L : List (ι × Reg)) (hL : ∀ q ∈ L, q.1 ∈ S ∧ w ∉ X q.1) (c₁ c₂ : ℕ) :
    ∀ {s₁ s₂ : St ι Reg M}, MdSim (X := X) b w S s₁ s₂ →
      MdSim (X := X) b w S (phase X A c₁ L s₁) (phase X A c₂ L s₂) := by
  induction L with
  | nil => intro s₁ s₂ h; exact h
  | cons q L ih =>
    obtain ⟨p, x⟩ := q
    intro s₁ s₂ h
    rw [phase_cons, phase_cons]
    obtain ⟨hp, hw⟩ := hL (p, x) (by simp)
    exact ih (fun q hq => hL q (by simp [hq])) ((h.close hp hw).write hp x _ _)

end MdSim

end T1

end Podc.PartialReplicationCausal.Necessity
