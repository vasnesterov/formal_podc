import Papers.PODC2018.PartialReplicationCausal.Necessity.Cases

/-!
# Theorem 1: the loop case

`case3` is stated for the lists of writes extracted from an `(i, e_jk)`-loop (see
`Theorem1.lean`): a register `w ∈ X_jk` not stored at `l₁, …, l_{s-1}`, a chain phase `Lc` (writes
at `j`, `r₂, …, r_t` on registers stored neither at `k` nor at the `l_p`) leading from `w` to `i`,
and the path phase `(i, y₀) :: Lr` along `l₁, …, l_{s-1}` whose last write is the first one on a
register of `X k`.
-/

namespace Podc.PartialReplicationCausal.Necessity

open Classical

variable {ι Reg M : Type*} {X : ι → Set Reg} {A : Alg ι Reg M}

namespace T1

/-- `j` writes `x` twice versus once: the initial log-level correspondence. -/
lemma logSim_base {s : St ι Reg M} {j : ι} {x : Reg} {ℓ ℓ' : ℕ}
    (hinv : Inv X (s.write A j x ℓ)) :
    LogSim (s.n + 1) ((s.write A j x ℓ).write A j x ℓ') (s.write A j x ℓ) := by
  set t := s.write A j x ℓ with ht
  have htn : t.n = s.n + 1 := rfl
  have hlt : ∀ a < t.n, (t.write A j x ℓ').log a = t.log a := fun a ha => write_log_lt _ _ _ _ ha
  have hsh : ∀ a < t.n, shift (s.n + 1) a = a := fun a ha => shift_of_lt (by omega)
  refine ⟨rfl, by omega, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; rw [hsh a ha, hlt a ha]
  · intro a ha; rw [hsh a ha, hlt a ha]
  · intro a ha; rw [hsh a ha, hlt a ha]
  · intro a ha c
    rw [hsh a ha, hlt a ha]
    by_cases hc : c < s.n + 1
    · rw [shift_of_lt hc]
    · rw [shift_of_ge (by omega)]
      constructor
      · intro h; have := hinv.pre_lt a ha _ h; omega
      · intro h; have := hinv.pre_lt a ha _ h; omega
  · intro a ha h
    rw [hsh a ha, hlt a ha] at h
    have := hinv.pre_lt a ha _ h; omega
  · show ((t.write A j x ℓ').log t.n).pre = insert (s.n + 1 - 1) ((t.write A j x ℓ').log (s.n + 1 - 1)).pre
    rw [write_log_n, show s.n + 1 - 1 = s.n from rfl, hlt _ (by omega), ht, write_log_n]
    simp
  · show ((t.write A j x ℓ').log t.n).reg = ((t.write A j x ℓ').log (s.n + 1 - 1)).reg
    rw [write_log_n, show s.n + 1 - 1 = s.n from rfl, hlt _ (by omega), ht, write_log_n]
  · intro r c
    rw [write_app]
    split_ifs with hr
    · subst hr
      by_cases hc : c < s.n + 1
      · rw [shift_of_lt hc]
        simp only [Set.mem_insert_iff]
        constructor
        · rintro (h | h)
          · exact absurd h (by omega)
          · exact h
        · exact Or.inr
      · rw [shift_of_ge (by omega)]
        simp only [Set.mem_insert_iff]
        constructor
        · rintro (h | h)
          · exact absurd h (by omega)
          · have := hinv.app_lt _ _ h; omega
        · intro h; have := hinv.app_lt _ _ h; omega
    · by_cases hc : c < s.n + 1
      · rw [shift_of_lt hc]
      · rw [shift_of_ge (by omega)]
        constructor
        · intro h; have := hinv.app_lt _ _ h; omega
        · intro h; have := hinv.app_lt _ _ h; omega
  · intro r hr
    rw [write_app] at hr ⊢
    split_ifs at hr ⊢ with hrj
    · subst hrj
      refine Set.mem_insert_of_mem _ ?_
      rw [ht, write_app_self]; exact Set.mem_insert _ _
    · have := hinv.app_lt _ _ hr; omega

/-- **Case 3** (an `(i, e_jk)`-loop), for the extracted lists of writes. -/
theorem case3 [Fintype ι] (hA : Implements X A) {i j k : ι} {s₀ : St ι Reg M}
    (hs₀ : Reachable X A s₀) (hq : Quiescent X s₀) (hobl : Oblivious X A s₀ i j k)
    (hjk : j ≠ k) (hik : i ≠ k) (hij : i ≠ j) {l : List ι} (hil : i ∉ l) (hkl : k ∉ l) (hjl : j ∉ l)
    {w : Reg} (hwj : w ∈ X j) (hwk : w ∈ X k) (hwl : ∀ p ∈ l, w ∉ X p)
    (Lc : List (ι × Reg))
    (hLc : ∀ q ∈ Lc, q.2 ∈ X q.1 ∧ q.2 ∉ X k ∧ (∀ p ∈ l, q.2 ∉ X p) ∧ q.1 ≠ i ∧ q.1 ≠ k ∧ q.1 ∉ l)
    {y₀ : Reg} (hy₀ : y₀ ∈ X i) (Lr : List (ι × Reg)) (hLr : ∀ q ∈ Lr, q.1 ∈ l ∧ q.2 ∈ X q.1)
    (La : List (ι × Reg)) (pf : ι) (xf : Reg) (hsplit : (i, y₀) :: Lr = La ++ [(pf, xf)])
    (hLa : ∀ q ∈ La, q.2 ∉ X k) (hxf : xf ∈ X k)
    (hlink : Linked X w (Lc ++ (i, y₀) :: Lr) k) : False := by
  obtain ⟨N, hN⟩ := exists_lab_bound s₀
  have hinv₀ := Reachable.inv hs₀
  -- the initial part: `j` writes `u_A` (and `u_B` in `E₁`), `k` applies `u_A`
  set t₀ := s₀.write A j w N with ht₀
  set t₁ := t₀.write A j w (N + 1) with ht₁
  have st₀ : Step X A s₀ t₀ := Step.write _ _ _ _ hwj (fun a ha => (hN a ha).ne)
  have st₁ : Step X A t₀ t₁ := Step.write _ _ _ _ hwj (lab_step hN j w)
  have hst₀ := Reachable.step hs₀ st₀
  have hinvt₀ := Reachable.inv hst₀
  have hlogA : t₀.log s₀.n = ⟨j, w, N, A.write j (s₀.md j) w, s₀.app j⟩ := write_log_n _ _ _ _
  have happk₀ : t₀.app k = s₀.app k := write_app_ne _ _ _ _ (Ne.symm hjk)
  have hen₀ : Enabled X A t₀ k s₀.n := by
    refine enabled_of_unique hA hst₀ (by simp [t₀]) (by rw [hlogA]; exact hwk) ?_ ?_ ?_
    · rw [happk₀]; exact fun h => lt_irrefl _ (hinv₀.app_lt _ _ h)
    · intro a ha hab
      have hlt := hinvt₀.hb_lt hab
      rw [write_log_lt _ _ _ _ hlt] at ha
      rw [happk₀]; exact hq a hlt k ha
    · intro a hne ha
      have hlt : a < s₀.n := by have := ha.1; simp [t₀] at this; omega
      exact old_not_enabled hq (ext_write _ _ _ _) hlt ha
  have hen₁ : Enabled X A t₁ k s₀.n := by
    obtain ⟨h1, h2, h3, h4, h5⟩ := hen₀
    have hl : t₁.log s₀.n = t₀.log s₀.n := write_log_lt _ _ _ _ h1
    refine ⟨by simp [t₁, t₀], by rw [hl]; exact h2, by rw [hl]; exact h3,
      by rw [write_app_ne _ _ _ _ (Ne.symm hjk)]; exact h4,
      by rw [hl, write_md_ne _ _ _ _ (Ne.symm hjk)]; exact h5⟩
  set init₂ := t₀.apply A k s₀.n with hinit₂
  set init₁ := t₁.apply A k s₀.n with hinit₁
  have r₂ : Relation.ReflTransGen (Step X A) s₀ init₂ :=
    (Relation.ReflTransGen.single st₀).tail (Step.apply _ _ _ hen₀)
  have r₁ : Relation.ReflTransGen (Step X A) s₀ init₁ :=
    ((Relation.ReflTransGen.single st₀).tail st₁).tail (Step.apply _ _ _ hen₁)
  have hsi₁ := Reachable.rtg hs₀ r₁
  have hsi₂ := Reachable.rtg hs₀ r₂
  have hlab₁ : LabBound N init₁ := by
    intro a ha
    simp only [init₁, t₁, t₀, apply_n, write_n] at ha ⊢
    rcases (show a < s₀.n ∨ a = s₀.n ∨ a = s₀.n + 1 by omega) with h | rfl | rfl
    · rw [apply_log, write_log_lt _ _ _ _ (by simp; omega), write_log_lt _ _ _ _ h]
      have := hN a h; omega
    · rw [apply_log, write_log_lt _ _ _ _ (by simp)]; simp
    · show (t₁.log t₀.n).lab < _
      rw [write_log_n]; simp
  have hlab₂ : LabBound (N + 1) init₂ := by
    intro a ha
    simp only [init₂, t₀, apply_n, write_n] at ha ⊢
    rcases (show a < s₀.n ∨ a = s₀.n by omega) with h | rfl
    · rw [apply_log, write_log_lt _ _ _ _ h]
      have := hN a h; omega
    · rw [apply_log]; (simp; omega)
  have hb : shift (s₀.n + 1) s₀.n = s₀.n := shift_of_lt (by omega)
  have hsim₀ : LogSim (s₀.n + 1) init₁ init₂ := by
    have := (logSim_base (s := s₀) (j := j) (x := w) (ℓ := N) (ℓ' := N + 1) hinvt₀).apply (A := A) k s₀.n
    rwa [hb] at this
  -- the chain phase and the closing of `i`
  have hLcX : ∀ q ∈ Lc, q.2 ∈ X q.1 := fun q hq => (hLc q hq).1
  obtain ⟨re₁, hlabe₁⟩ := reach_phase N Lc hLcX init₁ hsi₁ hlab₁
  obtain ⟨re₂, hlabe₂⟩ := reach_phase (N + 1) Lc hLcX init₂ hsi₂ hlab₂
  set e₁ := phase X A N Lc init₁ with he₁
  set e₂ := phase X A (N + 1) Lc init₂ with he₂
  have hse₁ := Reachable.rtg hsi₁ re₁
  have hse₂ := Reachable.rtg hsi₂ re₂
  set σ₁ := close X A i e₁ with hσ₁
  set σ₂ := close X A i e₂ with hσ₂
  have rσ₁ : Relation.ReflTransGen (Step X A) s₀ σ₁ := (r₁.trans re₁).trans (rtg_close _)
  have rσ₂ : Relation.ReflTransGen (Step X A) s₀ σ₂ := (r₂.trans re₂).trans (rtg_close _)
  have hinvσ₁ := Reachable.inv (Reachable.rtg hs₀ rσ₁)
  have hinvσ₂ := Reachable.inv (Reachable.rtg hs₀ rσ₂)
  have hsim : LogSim (s₀.n + 1) σ₁ σ₂ :=
    (hsim₀.phase hA Lc hLcX hsi₁ hsi₂ hlab₁ hlab₂).close hA hse₁ hse₂ i
  have hlogB₁ : init₁.log (s₀.n + 1) = ⟨j, w, N + 1, A.write j (t₀.md j) w, t₀.app j⟩ := by
    show t₁.log t₀.n = _; exact write_log_n _ _ _ _
  have hextσ₁ : Ext init₁ σ₁ := (ext_phase _ _ _).trans (ext_close _)
  have hlogB : σ₁.log (s₀.n + 1) = ⟨j, w, N + 1, A.write j (t₀.md j) w, t₀.app j⟩ := by
    rw [hextσ₁.log_eq _ (by simp [init₁, t₁, t₀]), hlogB₁]
  have hdiff : DiffOnly X σ₁ σ₂ i j k :=
    hsim.diffOnly hinvσ₁ hinvσ₂ (by rw [hlogB]) (by rw [hlogB]; exact ⟨hwj, hwk⟩)
  have hmdi : σ₁.md i = σ₂.md i := hobl _ _ rσ₁ rσ₂ hdiff
  -- metadata-level simulation from `σ₁, σ₂` on
  set S : Set ι := {r | r = i ∨ r ∈ l ∨ r = k} with hS
  have hLcne : ∀ r, r ∈ l ∨ r = k → ∀ q ∈ Lc, q.1 ≠ r := by
    rintro r (hr | rfl) q hq
    · exact fun h => (hLc q hq).2.2.2.2.2 (h ▸ hr)
    · exact (hLc q hq).2.2.2.2.1
  have hmd_init : ∀ r, r ∈ l ∨ r = k → init₁.md r = init₂.md r := by
    rintro r (hr | rfl)
    · have hrk : r ≠ k := fun h => hkl (h ▸ hr)
      have hrj : r ≠ j := fun h => hjl (h ▸ hr)
      rw [apply_md_ne _ _ _ hrk, apply_md_ne _ _ _ hrk, write_md_ne _ _ _ _ hrj]
    · rw [apply_md_self, apply_md_self, write_md_ne _ _ _ _ (Ne.symm hjk),
        show t₁.log = Function.update t₀.log t₀.n _ from rfl,
        Function.update_of_ne (show s₀.n ≠ t₀.n by simp [t₀])]
  have hmd_σ : ∀ r, r ∈ l ∨ r = k → σ₁.md r = σ₂.md r := by
    intro r hr
    have hri : r ≠ i := by
      rcases hr with hr | rfl
      · rintro rfl; exact hil hr
      · exact Ne.symm hik
    rw [close_md_ne _ hri, close_md_ne _ hri, (phase_frame _ _ _ (hLcne r hr)).1,
      (phase_frame _ _ _ (hLcne r hr)).1, hmd_init r hr]
  -- every update on a register of `X r`, `r ∈ S`, is applied at `r` in `σ₂`
  have hAA₀ : ∀ r, AllApplied (X := X) r s₀ := fun r a ha hreg => hq a ha r hreg
  have hAAi : AllApplied (X := X) i σ₂ := by
    intro a ha hreg
    rw [close_n] at ha; rw [close_log] at hreg
    exact close_all hA hse₂ a ha hreg
  have hAAl : ∀ r ∈ l, AllApplied (X := X) r σ₂ := by
    intro r hr
    have h0 : AllApplied (X := X) r init₂ :=
      ((hAA₀ r).write (Or.inl (hwl r hr))).ext_same (ext_apply _ _ _) rfl
    exact (h0.phase (fun q hq => Or.inl ((hLc q hq).2.2.1 r hr))).close
  have hAAk₀ : AllApplied (X := X) k init₂ := by
    intro a ha hreg
    have ha' : a < s₀.n + 1 := ha
    rw [hinit₂, apply_app_self, happk₀]
    rcases (show a < s₀.n ∨ a = s₀.n by omega) with h | rfl
    · right
      rw [hinit₂, apply_log, ht₀, write_log_lt _ _ _ _ h] at hreg
      exact hq a h _ hreg
    · exact Or.inl rfl
  have hAAke : AllApplied (X := X) k e₂ := hAAk₀.phase (fun q hq => Or.inl (hLc q hq).2.1)
  have hAAk : AllApplied (X := X) k σ₂ := hAAke.close
  have hS_i : i ∈ S := Or.inl rfl
  have hS_k : k ∈ S := Or.inr (Or.inr rfl)
  have hAA : ∀ r ∈ S, AllApplied (X := X) r σ₂ := by
    rintro r (h | h | h)
    · rw [h]; exact hAAi
    · exact hAAl r h
    · rw [h]; exact hAAk
  have hmdsim : MdSim (X := X) (s₀.n + 1) w S σ₁ σ₂ :=
    { n_eq := hsim.n_eq, b_le := hsim.b_le, src := hsim.src, reg := hsim.reg
      ts := fun r hr a ha hreg happ => absurd (hAA r hr a ha hreg) happ
      md := by
        rintro r (h | h)
        · rw [h]; exact hmdi
        · exact hmd_σ r h
      app := fun r _ => hsim.app r
      regB := by rw [hlogB] }
  -- the path phase
  have hLX : ∀ q ∈ Lc ++ (i, y₀) :: Lr, q.2 ∈ X q.1 := by
    intro q hq
    simp only [List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · exact (hLc q hq).1
    · exact hy₀
    · exact (hLr q hq).2
  have hLnk : ∀ q ∈ Lc ++ (i, y₀) :: Lr, q.1 ≠ k := by
    intro q hq
    simp only [List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · exact (hLc q hq).2.2.2.2.1
    · exact hik
    · exact fun h => hkl (h ▸ (hLr q hq).1)
  set ρ₁ := phase X A N (Lc ++ (i, y₀) :: Lr) init₁ with hρ₁
  set ρ₂ := phase X A (N + 1) (Lc ++ (i, y₀) :: Lr) init₂ with hρ₂
  have hρ₁' : ρ₁ = phase X A N Lr (σ₁.write A i y₀ (N + e₁.n)) := by
    rw [hρ₁, phase_append, phase_cons]
  have hρ₂' : ρ₂ = phase X A (N + 1) Lr (σ₂.write A i y₀ (N + 1 + e₂.n)) := by
    rw [hρ₂, phase_append, phase_cons]
  have hsimρ : MdSim (X := X) (s₀.n + 1) w S ρ₁ ρ₂ := by
    rw [hρ₁', hρ₂']
    exact (hmdsim.write hS_i y₀ _ _).phase Lr
      (fun q hq => ⟨Or.inr (Or.inl (hLr q hq).1), hwl _ (hLr q hq).1⟩) N (N + 1)
  -- in `E₂`, the last update is enabled at `k`
  have hen₂ : Enabled X A ρ₂ k (ρ₂.n - 1) := by
    have hmem : ∀ q ∈ La ++ [(pf, xf)], q.2 ∈ X q.1 ∧ q.1 ≠ k := by
      intro q hq
      rw [← hsplit] at hq
      exact ⟨hLX q (List.mem_append_right _ hq), hLnk q (List.mem_append_right _ hq)⟩
    have hLa' : ∀ q ∈ La, q.2 ∈ X q.1 ∧ q.2 ∉ X k :=
      fun q hq => ⟨(hmem q (List.mem_append_left _ hq)).1, hLa q hq⟩
    have hf := hmem (pf, xf) (by simp)
    have := last_enabled hA hse₂ hlabe₂ hAAke La pf xf hLa' hf.2 hf.1 hxf
    have heq : ρ₂ = phase X A (N + 1) (La ++ [(pf, xf)]) e₂ := by
      rw [← hsplit, hρ₂, phase_append]
    rw [heq]; exact this
  have hρ₂n : s₀.n + 2 ≤ ρ₂.n := by
    rw [hρ₂, phase_n, List.length_append, List.length_cons]
    show s₀.n + 2 ≤ s₀.n + 1 + _
    omega
  have hρ₁n : ρ₁.n = ρ₂.n + 1 := hsimρ.n_eq
  have hshift : shift (s₀.n + 1) (ρ₂.n - 1) = ρ₁.n - 1 := by
    rw [shift_of_ge (by omega)]; omega
  -- ... hence in `E₁` too
  have hen₁ρ : Enabled X A ρ₁ k (ρ₁.n - 1) := by
    rw [← hshift]; exact (hsimρ.enabled_iff hS_k _).2 hen₂
  -- but `u_B ↪` the last update and `u_B` is not applied at `k`
  have hcar := carrier (c := N) (b := s₀.n + 1) (t := k) hA (Lc ++ (i, y₀) :: Lr) init₁
    (s₀.n + 1) (by simp) hLX hsi₁ hlab₁ (by simp [init₁, t₁, t₀]) (.inl rfl)
    (by rw [hlogB₁]; exact hlink)
  have hHB : HB ρ₁ (s₀.n + 1) (ρ₁.n - 1) := hcar.1
  have hsρ₁ : Reachable X A ρ₁ := Reachable.rtg hsi₁ (reach_phase N _ hLX init₁ hsi₁ hlab₁).1
  have hregB : (ρ₁.log (s₀.n + 1)).reg ∈ X k := by
    rw [(ext_phase N _ init₁).log_eq _ (by simp [init₁, t₁, t₀]), hlogB₁]; exact hwk
  have hsafe := hA.1 _ (Reachable.step hsρ₁ (Step.apply _ _ _ hen₁ρ)) k (ρ₁.n - 1) (by simp)
    (s₀.n + 1) hregB (by rw [hb_apply]; exact hHB)
  simp only [apply_app_self, Set.mem_insert_iff] at hsafe
  rcases hsafe with h | h
  · omega
  · rw [(phase_frame _ _ _ hLnk).2, hinit₁, ht₁, apply_app_self,
      write_app_ne _ _ _ _ (Ne.symm hjk), happk₀] at h
    rcases h with h | h
    · omega
    · have := hinv₀.app_lt _ _ h; omega

end T1

end Podc.PartialReplicationCausal.Necessity
