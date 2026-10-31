import Papers.PODC2018.PartialReplicationCausal.Necessity.Simulation

/-!
# Theorem 1: the three cases

`case1` (`e_ik`, `i` the issuer), `case2` (`e_ji`, `i` the receiver) and `case3` (an
`(i, e_jk)`-loop, after the loop has been turned into the lists of writes of the two phases).
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*} {X : ι → Set Reg} {A : Alg ι Reg M}

namespace T1

lemma Ext.cp_mono {s s' : St ι Reg M} (he : Ext s s') {i : ι} : CP s i ⊆ CP s' i := by
  rintro a (ha | ⟨b, hb, hab⟩)
  · exact .inl (he.app_sub i ha)
  · exact .inr ⟨b, he.app_sub i hb, he.hb hab⟩

lemma cp_write_self {s : St ι Reg M} (hinv : Inv X s) {r : ι} {x : Reg} {ℓ a : ℕ}
    (ha : a ∈ CP (s.write A r x ℓ) r) : a ∈ CP s r ∨ a = s.n := by
  have he := ext_write (A := A) s r x ℓ
  rcases ha with ha | ⟨c, hc, hac⟩
  · simp only [write_app_self, Set.mem_insert_iff] at ha
    rcases ha with rfl | ha
    · exact .inr rfl
    · exact .inl (.inl ha)
  · simp only [write_app_self, Set.mem_insert_iff] at hc
    rcases hc with rfl | hc
    · obtain ⟨-, d, hd, had⟩ := hb_cases hac
      simp only [write_log_n] at hd
      rcases had with rfl | had
      · exact .inl (.inl hd)
      · exact .inl (.inr ⟨d, hd, he.hb_back hinv had (hinv.app_lt _ _ hd)⟩)
    · exact .inl (.inr ⟨c, hc, he.hb_back hinv hac (hinv.app_lt _ _ hc)⟩)

lemma cp_apply_self {s : St ι Reg M} {r : ι} {u a : ℕ} (ha : a ∈ CP (s.apply A r u) r) :
    a ∈ CP s r ∨ a = u ∨ HB s a u := by
  rcases ha with ha | ⟨c, hc, hac⟩
  · simp only [apply_app_self, Set.mem_insert_iff] at ha
    rcases ha with rfl | ha
    · exact .inr (.inl rfl)
    · exact .inl (.inl ha)
  · rw [hb_apply] at hac
    simp only [apply_app_self, Set.mem_insert_iff] at hc
    rcases hc with rfl | hc
    · exact .inr (.inr hac)
    · exact .inl (.inr ⟨c, hc, hac⟩)

/-- Old updates (issued before `s₀`, which is quiescent) are never enabled. -/
lemma old_not_enabled {s₀ s : St ι Reg M} (hq : Quiescent X s₀) (he : Ext s₀ s) {k : ι} {a : ℕ}
    (ha : a < s₀.n) : ¬ Enabled X A s k a := by
  rintro ⟨-, -, hreg, happ, -⟩
  rw [he.log_eq a ha] at hreg
  exact happ (he.app_sub k (hq a ha k hreg))

lemma lab_step {s : St ι Reg M} {N : ℕ} (hN : ∀ a < s.n, (s.log a).lab < N) (j : ι) (x : Reg) :
    ∀ a < (s.write A j x N).n, ((s.write A j x N).log a).lab ≠ N + 1 := by
  intro a ha
  simp only [write_n] at ha
  rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
  · rw [write_log_lt _ _ _ _ ha]; have := hN a ha; omega
  · simp

/-- **Case 1** (`e_ik ∈ E_i`): `i` writes `y ∈ X_ik` twice. -/
theorem case1 [Fintype ι] (hA : Implements X A) {i k : ι} (hik : Adj X i k)
    {s₀ : St ι Reg M} (hs₀ : Reachable X A s₀) (hq : Quiescent X s₀)
    (hobl : Oblivious X A s₀ i i k) : False := by
  obtain ⟨hne, y, hyi, hyk⟩ := hik
  obtain ⟨N, hN⟩ := exists_lab_bound s₀
  set σ₁ := s₀.write A i y N with hσ₁
  set σ₂ := σ₁.write A i y (N + 1) with hσ₂
  have st₁ : Step X A s₀ σ₁ := Step.write _ _ _ _ hyi (fun a ha => (hN a ha).ne)
  have st₂ : Step X A σ₁ σ₂ := Step.write _ _ _ _ hyi (lab_step hN i y)
  have r₁ : Relation.ReflTransGen (Step X A) s₀ σ₁ := .single st₁
  have r₂ : Relation.ReflTransGen (Step X A) s₀ σ₂ := r₁.tail st₂
  have hs₂ := Reachable.rtg hs₀ r₂
  have hinv₀ := Reachable.inv hs₀
  have hinv₁ := Reachable.inv (Reachable.rtg hs₀ r₁)
  have hinv₂ := Reachable.inv hs₂
  have he : Ext s₀ σ₂ := (ext_write _ _ _ _).trans (ext_write _ _ _ _)
  have hdiff : DiffOnly X σ₁ σ₂ i i k := by
    refine diffOnly_of_ext hinv₁ hinv₂ (ext_write _ _ _ _) (Ext.cp_mono (ext_write _ _ _ _)) ?_
    intro a ha hna
    rcases cp_write_self hinv₁ ha with h | rfl
    · exact absurd h hna
    · simp [σ₂, hyi, hyk]
  have hmd : σ₁.md i = σ₂.md i := hobl σ₁ σ₂ r₁ r₂ hdiff
  have hn₁ : σ₁.n = s₀.n + 1 := rfl
  have e0 : σ₂.log s₀.n = ⟨i, y, N, σ₁.md i, s₀.app i⟩ := by
    rw [write_log_lt _ _ _ _ (show s₀.n < σ₁.n by simp [σ₁])]; simp [σ₁]
  have hw : A.write i (σ₁.md i) y = σ₁.md i := by
    have h := hmd.symm
    rwa [show σ₂.md i = A.write i (σ₁.md i) y from write_md_self _ _ _ _] at h
  have e1 : σ₂.log σ₁.n = ⟨i, y, N + 1, σ₁.md i, σ₁.app i⟩ := by
    rw [write_log_n, hw]
  have happk : σ₂.app k = s₀.app k := by
    rw [write_app_ne _ _ _ _ (Ne.symm hne), write_app_ne _ _ _ _ (Ne.symm hne)]
  have hmdk : σ₂.md k = s₀.md k := by
    rw [write_md_ne _ _ _ _ (Ne.symm hne), write_md_ne _ _ _ _ (Ne.symm hne)]
  have hnotk : ∀ a, s₀.n ≤ a → a ∉ σ₂.app k := fun a ha h =>
    by have := hinv₀.app_lt _ _ (happk ▸ h); omega
  by_cases hr : A.ready k (s₀.md k) i y (σ₁.md i)
  · have hen : Enabled X A σ₂ k σ₁.n :=
      ⟨by simp [σ₂], by rw [e1]; exact hne, by rw [e1]; exact hyk, hnotk _ (by omega),
        by rw [e1, hmdk]; exact hr⟩
    refine not_enabled_of_dep hA hs₂ (v' := s₀.n) (hb_single (by simp [σ₂]) ?_) (by rw [e0]; exact hyk)
      (hnotk _ le_rfl) (by omega) hen
    rw [e1]; simp [σ₁]
  · refine frozen hA hs₂ (r := k) (u := s₀.n) (fun a ha => ?_) (by simp [σ₂, σ₁])
      (by rw [e0]; exact hyk) (hnotk _ le_rfl) ?_
    · rcases Nat.lt_or_ge a s₀.n with h | h
      · exact old_not_enabled hq he h ha
      · have h1 := ha.1
        simp only [σ₂, σ₁, write_n] at h1
        obtain ⟨-, -, -, -, h5⟩ := ha
        rw [hmdk] at h5
        rcases (show a = s₀.n ∨ a = σ₁.n by omega) with rfl | rfl
        · rw [e0] at h5; exact hr h5
        · rw [e1] at h5; exact hr h5
    · intro a ha hab
      have hlt := hinv₂.hb_lt hab
      rw [he.log_eq a hlt] at ha
      exact he.app_sub k (hq a hlt k ha)

/-- **Case 2** (`e_ji ∈ E_i`): after `i` has applied a first update `u_P` of `j`, `j` writes
`u_A`, `u_B` on `y ∈ X_ji`; compare the states before and after `i` applies `u_A`. -/
theorem case2 [Fintype ι] (hA : Implements X A) {i j : ι} (hji : Adj X j i)
    {s₀ : St ι Reg M} (hs₀ : Reachable X A s₀) (hq : Quiescent X s₀)
    (hobl : Oblivious X A s₀ i j i) : False := by
  obtain ⟨hne, y, hyj, hyi⟩ := hji
  obtain ⟨N, hN⟩ := exists_lab_bound s₀
  have hinv₀ := Reachable.inv hs₀
  -- `j` writes `u_P`, `i` applies it
  set t₁ := s₀.write A j y N with ht₁
  have st₁ : Step X A s₀ t₁ := Step.write _ _ _ _ hyj (fun a ha => (hN a ha).ne)
  have hs₁ := Reachable.step hs₀ st₁
  have hinv₁ := Reachable.inv hs₁
  have hP : t₁.log s₀.n = ⟨j, y, N, A.write j (s₀.md j) y, s₀.app j⟩ := write_log_n _ _ _ _
  have happ₁ : t₁.app i = s₀.app i := write_app_ne _ _ _ _ (Ne.symm hne)
  have hen₁ : Enabled X A t₁ i s₀.n := by
    refine enabled_of_unique hA hs₁ (by simp [t₁]) (by rw [hP]; exact hyi) ?_ ?_ ?_
    · rw [happ₁]; exact fun h => lt_irrefl _ (hinv₀.app_lt _ _ h)
    · intro a ha hab
      have hlt := hinv₁.hb_lt hab
      rw [write_log_lt _ _ _ _ hlt] at ha
      rw [happ₁]; exact hq a hlt i ha
    · intro a hne' ha
      have hlt : a < s₀.n := by have := ha.1; simp [t₁] at this; omega
      exact old_not_enabled hq (ext_write _ _ _ _) hlt ha
  set t₂ := t₁.apply A i s₀.n with ht₂
  have st₂ : Step X A t₁ t₂ := Step.apply _ _ _ hen₁
  set t₃ := t₂.write A j y (N + 1) with ht₃
  have st₃ : Step X A t₂ t₃ := Step.write _ _ _ _ hyj (lab_step hN j y)
  set σ := t₃.write A j y (N + 2) with hσ
  have st₄ : Step X A t₃ σ := Step.write _ _ _ _ hyj (fun a ha => by
    simp only [t₃, t₂, t₁, write_n, apply_n] at ha
    rcases (show a < s₀.n ∨ a = s₀.n ∨ a = s₀.n + 1 by omega) with h | rfl | rfl
    · rw [write_log_lt _ _ _ _ (by simp [t₂, t₁]; omega), apply_log, write_log_lt _ _ _ _ h]
      have := hN a h; omega
    · rw [write_log_lt _ _ _ _ (by simp [t₂, t₁])]; simp [t₂, t₁]
    · show (t₃.log t₂.n).lab ≠ N + 2
      rw [write_log_n]; simp)
  have rσ : Relation.ReflTransGen (Step X A) s₀ σ :=
    ((((Relation.ReflTransGen.single st₁).tail st₂).tail st₃).tail st₄)
  have hsσ := Reachable.rtg hs₀ rσ
  have hinvσ := Reachable.inv hsσ
  have he : Ext s₀ σ := Ext.of_rtg rσ
  -- the updates
  have lP : σ.log s₀.n = t₁.log s₀.n := by
    have h1 : s₀.n < t₃.n := by simp [t₃, t₂, t₁]
    have h2 : s₀.n < t₂.n := by simp [t₂, t₁]
    rw [write_log_lt _ _ _ _ h1, write_log_lt _ _ _ _ h2]; rfl
  have lA : σ.log (s₀.n + 1) = ⟨j, y, N + 1, A.write j (t₂.md j) y, t₂.app j⟩ := by
    rw [write_log_lt _ _ _ _ (by simp [t₃, t₂, t₁])]; exact write_log_n _ _ _ _
  have lB : σ.log (s₀.n + 2) = ⟨j, y, N + 2, A.write j (t₃.md j) y, t₃.app j⟩ :=
    write_log_n _ _ _ _
  have happσ : σ.app i = insert s₀.n (s₀.app i) := by
    rw [write_app_ne _ _ _ _ (Ne.symm hne), write_app_ne _ _ _ _ (Ne.symm hne), apply_app_self,
      happ₁]
  have hnotσ : ∀ a, s₀.n + 1 ≤ a → a ∉ σ.app i := by
    intro a ha h
    rw [happσ] at h
    rcases h with rfl | h
    · omega
    · have := hinv₀.app_lt _ _ h; omega
  have hAB : HB σ (s₀.n + 1) (s₀.n + 2) := by
    refine hb_single (by simp [σ, t₃, t₂, t₁]) ?_
    rw [lB]; simp [t₃, t₂, t₁]
  have hBne : ¬ Enabled X A σ i (s₀.n + 2) :=
    not_enabled_of_dep hA hsσ hAB (by rw [lA]; exact hyi) (hnotσ _ le_rfl) (by omega)
  have hold : ∀ a ≤ s₀.n, (σ.log a).reg ∈ X i → a ∈ σ.app i := by
    intro a ha hreg
    rw [happσ]
    rcases (show a < s₀.n ∨ a = s₀.n by omega) with h | rfl
    · rw [he.log_eq a h] at hreg; exact Or.inr (hq a h i hreg)
    · exact Or.inl rfl
  have hdep : ∀ u ≤ s₀.n + 1, ∀ a, (σ.log a).reg ∈ X i → HB σ a u → a ∈ σ.app i := by
    intro u hu a ha hab
    exact hold a (by have := hinvσ.hb_lt hab; omega) ha
  -- `u_A` is enabled at `i`
  have hAen : Enabled X A σ i (s₀.n + 1) := by
    refine enabled_of_unique hA hsσ (by simp [σ, t₃, t₂, t₁]) (by rw [lA]; exact hyi)
      (hnotσ _ le_rfl) (hdep _ le_rfl) ?_
    intro a hne' ha
    have h1 := ha.1
    simp only [σ, t₃, t₂, t₁, write_n, apply_n] at h1
    rcases (show a < s₀.n ∨ a = s₀.n ∨ a = s₀.n + 2 by omega) with h | rfl | rfl
    · exact old_not_enabled hq he h ha
    · exact ha.2.2.2.1 (by rw [happσ]; exact Or.inl rfl)
    · exact hBne ha
  set σ' := σ.apply A i (s₀.n + 1) with hσ'
  have rσ' : Relation.ReflTransGen (Step X A) s₀ σ' := rσ.tail (Step.apply _ _ _ hAen)
  have hsσ' := Reachable.rtg hs₀ rσ'
  have hinvσ' := Reachable.inv hsσ'
  have hdiff : DiffOnly X σ σ' i j i := by
    refine diffOnly_of_ext hinvσ hinvσ' (ext_apply _ _ _) (Ext.cp_mono (ext_apply _ _ _)) ?_
    intro a ha hna
    rcases cp_apply_self ha with h | rfl | h
    · exact absurd h hna
    · rw [show σ'.log = σ.log from rfl, lA]; exact ⟨rfl, hyj, hyi⟩
    · exfalso; apply hna
      have hpre : (σ.log (s₀.n + 1)).pre = insert s₀.n (σ.log s₀.n).pre := by
        rw [lA, lP, hP]
        simp only [t₂, t₁]
        rw [apply_app_ne _ _ _ (by exact hne), write_app_self]
      have hn0i : s₀.n ∈ σ.app i := by rw [happσ]; exact Or.inl rfl
      rcases (hb_insert (by simp [σ, t₃, t₂, t₁]) (by simp [σ, t₃, t₂, t₁]; omega) hpre).1 h with
        rfl | h
      · exact .inl hn0i
      · exact .inr ⟨s₀.n, hn0i, h⟩
  have hmd : σ.md i = σ'.md i := hobl σ σ' rσ rσ' hdiff
  refine frozen hA hsσ' (r := i) (u := s₀.n + 2) (fun a ha => ?_) (by simp [σ', σ, t₃, t₂, t₁])
    (by simp only [σ', apply_log, lB]; exact hyi) ?_ ?_
  · have h1 := ha.1
    simp only [σ', σ, t₃, t₂, t₁, write_n, apply_n] at h1
    rcases (show a < s₀.n ∨ a = s₀.n ∨ a = s₀.n + 1 ∨ a = s₀.n + 2 by omega) with h | rfl | rfl | rfl
    · exact old_not_enabled hq (he.trans (ext_apply _ _ _)) h ha
    · exact ha.2.2.2.1 (by simp only [σ', apply_app_self]; rw [happσ]; simp)
    · exact ha.2.2.2.1 (by simp [σ'])
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ha
      simp only [σ', apply_log] at h2 h3 h5
      rw [← hmd] at h5
      exact hBne ⟨h1, h2, h3, fun h => h4 (subset_apply_app _ _ _ _ h), h5⟩
  · simp only [σ', apply_app_self, Set.mem_insert_iff, not_or]
    exact ⟨by omega, hnotσ _ (by omega)⟩
  · intro a ha hab
    rw [hb_apply] at hab
    have hlt := hinvσ.hb_lt hab
    simp only [σ', apply_log] at ha
    simp only [σ', apply_app_self, Set.mem_insert_iff]
    rcases (show a ≤ s₀.n ∨ a = s₀.n + 1 by omega) with h | rfl
    · exact Or.inr (hold a h ha)
    · exact Or.inl rfl

end T1

end Podc.PartialReplicationCausal.Necessity
