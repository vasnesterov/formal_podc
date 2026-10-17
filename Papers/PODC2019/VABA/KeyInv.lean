import Papers.PODC2019.VABA.Safety

/-!
# VABA: keys and locks of honest parties (Lemmas 14–15)

The second invariant `KInv` describes `LOCK`, `KEY` and the proposals, and gives Lemma 15:
an honest party's proposal passes the external validation (`ex-bc-validation`) of every party that
is in the broadcast phase of the same view — the "key progress" property that makes the
protocol live.
-/

namespace VABA

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V} {s : Glob P V}

/-- The key/lock invariant. -/
structure KInv (C : Cfg P V) (s : Glob P V) : Prop where
  lock_spec : ∀ p, (s.loc p).lock ≠ 0 → Past (s.loc p) (s.loc p).lock ∧
      ∃ l v, s.rev (s.loc p).lock = some l ∧ QC C.Q s (.pb (s.loc p).lock l 2 v)
  key_spec : ∀ p, ((s.loc p).key.1 = 0 → (s.loc p).key.2 = C.input p) ∧
      ((s.loc p).key.1 ≠ 0 → Past (s.loc p) (s.loc p).key.1 ∧
        ∃ l, s.rev (s.loc p).key.1 = some l ∧ QC C.Q s (.pb (s.loc p).key.1 l 1 (s.loc p).key.2))
  prop_spec : ∀ p j, 1 ≤ j → j ≤ (s.loc p).view → ((s.loc p).prop j).1 < j ∧
      (((s.loc p).prop j).1 = 0 → ((s.loc p).prop j).2 = C.input p) ∧
      (((s.loc p).prop j).1 ≠ 0 → ∃ l, s.rev ((s.loc p).prop j).1 = some l ∧
        QC C.Q s (.pb ((s.loc p).prop j).1 l 1 ((s.loc p).prop j).2))
  prop_lock : ∀ p j0 j, j0 < j → j ≤ (s.loc p).view → ∀ l, (s.loc p).lead j0 = some l →
      ∀ h ∈ (s.loc p).exitR j0, h ∉ s.corrupt → ∀ v, (s.loc h).d j0 l 2 = some v →
      j0 ≤ ((s.loc p).prop j).1

omit [DecidableEq P] in
lemma kinv_init (C : Cfg P V) : KInv C (init C) where
  lock_spec := by simp [init]
  key_spec := by simp [init]
  prop_spec := by
    intro p j h1 h2
    simp only [init] at h2 ⊢
    simp; omega
  prop_lock := by simp [init]

/-- Transport of `KInv` along a step that keeps every local state except possibly that of `x`,
and changes the local state of `x` only in ways that are checked separately. -/
lemma kinv_of_frame {s' : Glob P V} (K : KInv C s) (I : Inv C s) (hm : Mono s s') (x : P)
    (hloc : ∀ q, q ≠ x → s'.loc q = s.loc q)
    (hd : ∀ q j, Past (s.loc q) j → (s'.loc q).d j = (s.loc q).d j)
    (hlock : (s'.loc x).lock ≠ 0 → Past (s'.loc x) (s'.loc x).lock ∧
      ∃ l v, s'.rev (s'.loc x).lock = some l ∧ QC C.Q s' (.pb (s'.loc x).lock l 2 v))
    (hkey : ((s'.loc x).key.1 = 0 → (s'.loc x).key.2 = C.input x) ∧
      ((s'.loc x).key.1 ≠ 0 → Past (s'.loc x) (s'.loc x).key.1 ∧
        ∃ l, s'.rev (s'.loc x).key.1 = some l ∧
          QC C.Q s' (.pb (s'.loc x).key.1 l 1 (s'.loc x).key.2)))
    (hprop : ∀ j, 1 ≤ j → j ≤ (s'.loc x).view → ((s'.loc x).prop j).1 < j ∧
      (((s'.loc x).prop j).1 = 0 → ((s'.loc x).prop j).2 = C.input x) ∧
      (((s'.loc x).prop j).1 ≠ 0 → ∃ l, s'.rev ((s'.loc x).prop j).1 = some l ∧
        QC C.Q s' (.pb ((s'.loc x).prop j).1 l 1 ((s'.loc x).prop j).2)))
    (hplock : ∀ j0 j, j0 < j → j ≤ (s'.loc x).view → ∀ l, (s'.loc x).lead j0 = some l →
      ∀ h ∈ (s'.loc x).exitR j0, h ∉ s'.corrupt → ∀ v, (s'.loc h).d j0 l 2 = some v →
      j0 ≤ ((s'.loc x).prop j).1) :
    KInv C s' := by
  refine ⟨fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_⟩
  · by_cases hp : p = x
    · subst hp; exact hlock
    · rw [hloc p hp]
      intro h0
      obtain ⟨h1, l, v, hl, hq⟩ := K.lock_spec p h0
      exact ⟨h1, l, v, hm.rev _ _ hl, QC_mono hm.tok hq⟩
  · by_cases hp : p = x
    · subst hp; exact hkey
    · rw [hloc p hp]
      obtain ⟨h1, h2⟩ := K.key_spec p
      refine ⟨h1, fun h0 => ?_⟩
      obtain ⟨h3, l, hl, hq⟩ := h2 h0
      exact ⟨h3, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
  · by_cases hp : p = x
    · subst hp; exact hprop
    · rw [hloc p hp]
      intro j hj1 hj2
      obtain ⟨h1, h2, h3⟩ := K.prop_spec p j hj1 hj2
      refine ⟨h1, h2, fun h0 => ?_⟩
      obtain ⟨l, hl, hq⟩ := h3 h0
      exact ⟨l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
  · by_cases hp : p = x
    · subst hp; exact hplock
    · rw [hloc p hp]
      intro j0 j hj0 hj l hl h hh hc v hv
      have hc' : h ∉ s.corrupt := fun h' => hc (hm.corrupt h')
      obtain ⟨hP, -⟩ := I.rcvd_spec p j0 h (I.exitR_sub p j0 hh) hc'
      rw [hd h j0 hP] at hv
      exact K.prop_lock p j0 j hj0 hj l hl h hh hc' v hv

/-- The acting party of an action. -/
def Act.actor : Act P V → P
  | .deliver p .. => p
  | .skipShare p _ => p
  | .invokeElect p => p
  | .electReturn p => p
  | .recvVC p .. => p
  | .recvQC p .. => p
  | .exitView p => p
  | .corrupt p => p
  | .byzSign p _ => p

omit [Fintype P] in
lemma eff_loc_ne (c : ℕ → P) (a : Act P V) (s : Glob P V) (q : P) (hq : q ≠ a.actor) :
    (eff c a s).loc q = s.loc q := by
  cases a with
  | deliver p k st v r => simp [eff, Act.actor] at hq ⊢; simp [hq]
  | skipShare => rfl
  | invokeElect p => simp [eff, Act.actor] at hq ⊢; simp [hq]
  | electReturn p => simp [eff, Act.actor] at hq ⊢; simp [hq]
  | recvVC p q' j b =>
    simp only [Act.actor] at hq; simp only [eff]; split
    · simp [hq]
    · rfl
  | recvQC p => simp [eff, Act.actor] at hq ⊢; simp [hq]
  | exitView p => simp [eff, Act.actor] at hq ⊢; simp [hq]
  | corrupt => rfl
  | byzSign => rfl

/-- Deliveries of views a party has left are frozen. -/
lemma eff_d_frozen (c : ℕ → P) (a : Act P V) (hE : Enabled C a s) (q : P) (j : ℕ)
    (hq : Past (s.loc q) j) : ((eff c a s).loc q).d j = (s.loc q).d j := by
  by_cases hqa : q = a.actor
  · cases a with
    | deliver p k st v r =>
      simp only [Act.actor] at hqa; subst hqa
      obtain ⟨-, hph, -⟩ := hE
      have : j ≠ (s.loc q).view := by
        rintro rfl; rcases hq with h | ⟨-, h⟩
        · omega
        · rw [hph] at h; exact absurd h (by decide)
      funext k' s'
      simp [eff, this]
    | skipShare => rfl
    | invokeElect p => simp only [Act.actor] at hqa; subst hqa; simp [eff]
    | electReturn p => simp only [Act.actor] at hqa; subst hqa; simp [eff]
    | recvVC p q' j' b =>
      simp only [Act.actor] at hqa; subst hqa; simp only [eff]; split
      · simp only [upd_loc, ite_true]; split_ifs <;> simp
      · rfl
    | recvQC p => simp only [Act.actor] at hqa; subst hqa; simp [eff]
    | exitView p => simp only [Act.actor] at hqa; subst hqa; simp [eff]
    | corrupt => rfl
    | byzSign => rfl
  · rw [eff_loc_ne c a s q hqa]

/-- `KInv` is preserved when the local state of the actor keeps view, phase, leaders, lock, key,
proposals and exit sets. -/
lemma kinv_of_same (K : KInv C s) (I : Inv C s) (c : ℕ → P) (a : Act P V) (hE : Enabled C a s)
    (hview : ((eff c a s).loc a.actor).view = (s.loc a.actor).view)
    (hph : ((eff c a s).loc a.actor).ph = .vc ↔ (s.loc a.actor).ph = .vc)
    (hlead : ((eff c a s).loc a.actor).lead = (s.loc a.actor).lead)
    (hlock : ((eff c a s).loc a.actor).lock = (s.loc a.actor).lock)
    (hkey : ((eff c a s).loc a.actor).key = (s.loc a.actor).key)
    (hprop : ((eff c a s).loc a.actor).prop = (s.loc a.actor).prop)
    (hexitR : ((eff c a s).loc a.actor).exitR = (s.loc a.actor).exitR) :
    KInv C (eff c a s) := by
  have hm := mono_eff c a s
  have hpast : ∀ i, Past ((eff c a s).loc a.actor) i ↔ Past (s.loc a.actor) i := by
    intro i; simp only [Past, hview, hph]
  set x := a.actor
  refine kinv_of_frame K I hm x (eff_loc_ne c a s) (eff_d_frozen c a hE) ?_ ?_ ?_ ?_
  · rw [hlock, hpast]
    intro h0
    obtain ⟨h1, l, v, hl, hq⟩ := K.lock_spec x h0
    exact ⟨h1, l, v, hm.rev _ _ hl, QC_mono hm.tok hq⟩
  · rw [hkey]
    obtain ⟨h1, h2⟩ := K.key_spec x
    refine ⟨h1, fun h0 => ?_⟩
    obtain ⟨h3, l, hl, hq⟩ := h2 h0
    exact ⟨(hpast _).mpr h3, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
  · rw [hprop, hview]
    intro j hj1 hj2
    obtain ⟨h1, h2, h3⟩ := K.prop_spec x j hj1 hj2
    refine ⟨h1, h2, fun h0 => ?_⟩
    obtain ⟨l, hl, hq⟩ := h3 h0
    exact ⟨l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
  · rw [hprop, hview, hlead, hexitR]
    intro j0 j hj0 hj l hl h hh hc v hv
    have hc' : h ∉ s.corrupt := fun h' => hc (hm.corrupt h')
    obtain ⟨hP, -⟩ := I.rcvd_spec x j0 h (I.exitR_sub x j0 hh) hc'
    rw [eff_d_frozen c a hE h j0 hP] at hv
    exact K.prop_lock x j0 j hj0 hj l hl h hh hc' v hv

lemma kinv_eff (K : KInv C s) (I : Inv C s) (c : ℕ → P) (a : Act P V) (hE : Enabled C a s) :
    KInv C (eff c a s) := by
  have hm := mono_eff c a s
  have hd := eff_d_frozen c a hE
  have hloc := eff_loc_ne c a s
  cases a with
  | deliver p k st v r =>
    exact kinv_of_same K I c _ hE (by simp [eff, Act.actor])
      (by simp [eff, Act.actor]) (by simp [eff, Act.actor]) (by simp [eff, Act.actor])
      (by simp [eff, Act.actor]) (by simp [eff, Act.actor]) (by simp [eff, Act.actor])
  | skipShare p j => exact kinv_of_same K I c _ hE rfl Iff.rfl rfl rfl rfl rfl rfl
  | corrupt p => exact kinv_of_same K I c _ hE rfl Iff.rfl rfl rfl rfl rfl rfl
  | byzSign p st => exact kinv_of_same K I c _ hE rfl Iff.rfl rfl rfl rfl rfl rfl
  | invokeElect p =>
    have hph := hE.2.1
    exact kinv_of_same K I c _ hE (by simp [eff, Act.actor]) (by simp [eff, Act.actor, hph])
      (by simp [eff, Act.actor]) (by simp [eff, Act.actor]) (by simp [eff, Act.actor])
      (by simp [eff, Act.actor]) (by simp [eff, Act.actor])
  | electReturn x =>
    obtain ⟨hx, hph, hrev⟩ := hE
    simp only [Act.actor] at hloc hd
    set M : Loc P V := { s.loc x with
        ph := .vc
        lead := Function.update (s.loc x).lead (s.loc x).view (s.rev (s.loc x).view) } with hM
    have hX : (eff c (.electReturn x) s).loc x = M := by simp [eff, M]
    have hpast : ∀ i, Past (s.loc x) i → Past M i := by
      intro i hi; simp only [Past, M] at hi ⊢
      rcases hi with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨h, trivial⟩
    refine kinv_of_frame K I hm x hloc hd ?_ ?_ ?_ ?_
    · rw [hX]
      intro h0
      obtain ⟨h1, l, v, hl, hq⟩ := K.lock_spec x h0
      exact ⟨hpast _ h1, l, v, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · obtain ⟨h1, h2⟩ := K.key_spec x
      rw [hX]
      refine ⟨h1, fun h0 => ?_⟩
      obtain ⟨h3, l, hl, hq⟩ := h2 h0
      exact ⟨hpast _ h3, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · rw [hX]
      intro j hj1 hj2
      obtain ⟨h1, h2, h3⟩ := K.prop_spec x j hj1 hj2
      refine ⟨h1, h2, fun h0 => ?_⟩
      obtain ⟨l, hl, hq⟩ := h3 h0
      exact ⟨l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · rw [hX]
      intro j0 j hj0 hj l hl h hh hc v hv
      simp only [M] at hj hl hh ⊢
      have hj0' : j0 ≠ (s.loc x).view := by omega
      rw [Function.update_of_ne hj0'] at hl
      have hc' : h ∉ s.corrupt := fun h' => hc (hm.corrupt h')
      obtain ⟨hP, -⟩ := I.rcvd_spec x j0 h (I.exitR_sub x j0 hh) hc'
      rw [hd h j0 hP] at hv
      exact K.prop_lock x j0 j hj0 hj l hl h hh hc' v hv
  | recvQC x j st v =>
    obtain ⟨hx, hst1, hst3, l, hl, hq⟩ := hE
    simp only [Act.actor] at hloc hd
    set M := proc j st (some v) (s.loc x) with hM
    have hX : (eff c (.recvQC x j st v) s).loc x = M := by simp [eff, M]
    have hpast : ∀ i, Past M i ↔ Past (s.loc x) i := by
      intro i; simp [Past, M]
    have hj1 : j ≠ 0 := by
      rintro rfl; have := (I.lead_spec x 0 l hl).2; rw [I.rev_zero] at this; simp at this
    have hrev := (I.lead_spec x j l hl)
    refine kinv_of_frame K I hm x hloc hd ?_ ?_ ?_ ?_
    · rw [hX]
      intro h0
      rw [hpast]
      rcases proc_lock_cases j st (some v) (s.loc x) with h | ⟨rfl, -, h⟩
      · rw [h] at h0 ⊢
        obtain ⟨h1, l, v, hl, hq⟩ := K.lock_spec x h0
        exact ⟨h1, l, v, hm.rev _ _ hl, QC_mono hm.tok hq⟩
      · rw [h]
        exact ⟨hrev.1, l, v, hm.rev _ _ hrev.2, QC_mono hm.tok hq⟩
    · rw [hX]
      rcases proc_key_cases j st (some v) (s.loc x) with h | ⟨rfl, hv, h⟩
      · rw [h]
        obtain ⟨h1, h2⟩ := K.key_spec x
        refine ⟨h1, fun h0 => ?_⟩
        obtain ⟨h3, l, hl, hq⟩ := h2 h0
        exact ⟨(hpast _).mpr h3, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
      · refine ⟨fun h0 => absurd (h.symm.trans h0) hj1, fun _ => ⟨?_, l, ?_, ?_⟩⟩
        · rw [hpast, h]; exact hrev.1
        · rw [h]; exact hm.rev _ _ hrev.2
        · rw [h, ← Option.some.inj hv]; exact QC_mono hm.tok hq
    · rw [hX]
      intro j' hj1' hj2
      simp only [M, proc_view, proc_prop] at hj2 ⊢
      obtain ⟨h1, h2, h3⟩ := K.prop_spec x j' hj1' hj2
      refine ⟨h1, h2, fun h0 => ?_⟩
      obtain ⟨l, hl, hq⟩ := h3 h0
      exact ⟨l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · rw [hX]
      intro j0 j' hj0 hj l' hl' h hh hc w hw
      simp only [M, proc_view, proc_prop, proc_lead, proc_exitR] at hj hl' hh ⊢
      have hc' : h ∉ s.corrupt := fun h' => hc (hm.corrupt h')
      obtain ⟨hP, -⟩ := I.rcvd_spec x j0 h (I.exitR_sub x j0 hh) hc'
      rw [hd h j0 hP] at hw
      exact K.prop_lock x j0 j' hj0 hj l' hl' h hh hc' w hw
  | recvVC x q j b =>
    obtain ⟨hx, hl0, hb⟩ := hE
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hl0
    simp only [Act.actor] at hloc hd
    set L' : Loc P V := { s.loc x with
      rcvd := Function.update (s.loc x).rcvd j (insert q ((s.loc x).rcvd j)) } with hL'
    set M := if b then procVC j l (s.loc q) L' else L' with hM
    have hX : (eff c (.recvVC x q j b) s).loc x = M := by
      simp only [eff, hl, upd_loc, ite_true]; rfl
    have hMview : M.view = (s.loc x).view := by rw [hM]; split_ifs <;> simp [L']
    have hMph : M.ph = (s.loc x).ph := by rw [hM]; split_ifs <;> simp [L']
    have hMlead : M.lead = (s.loc x).lead := by rw [hM]; split_ifs <;> simp [L']
    have hMprop : M.prop = (s.loc x).prop := by rw [hM]; split_ifs <;> simp [L']
    have hMexitR : M.exitR = (s.loc x).exitR := by rw [hM]; split_ifs <;> simp [L']
    have hpast : ∀ i, Past M i ↔ Past (s.loc x) i := by
      intro i; simp [Past, hMview, hMph]
    have hj1 : j ≠ 0 := by
      rintro rfl; have := (I.lead_spec x 0 l hl).2; rw [I.rev_zero] at this; simp at this
    have hrev := (I.lead_spec x j l hl)
    have hlock_cases : M.lock = (s.loc x).lock ∨ (∃ v, (s.loc q).d j l 3 = some v) ∧
        M.lock = j := by
      rw [hM]; split_ifs
      · rcases procVC_lock_cases j l (s.loc q) L' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨Option.isSome_iff_exists.mp h1, h2⟩
      · exact Or.inl rfl
    have hkey_cases : M.key = (s.loc x).key ∨ ((s.loc q).d j l 2 = some M.key.2 ∧
        M.key.1 = j) := by
      rw [hM]; split_ifs
      · exact procVC_key_cases j l (s.loc q) L'
      · exact Or.inl rfl
    refine kinv_of_frame K I hm x hloc hd ?_ ?_ ?_ ?_
    · rw [hX]
      intro h0
      rw [hpast]
      rcases hlock_cases with h | ⟨⟨v, hv⟩, h⟩
      · rw [h] at h0 ⊢
        obtain ⟨h1, l, v, hl, hq⟩ := K.lock_spec x h0
        exact ⟨h1, l, v, hm.rev _ _ hl, QC_mono hm.tok hq⟩
      · rw [h]
        have hq := (I.d_spec q j l 3 v hv).2.2 (by norm_num)
        exact ⟨hrev.1, l, v, hm.rev _ _ hrev.2, QC_mono hm.tok hq⟩
    · rw [hX]
      rcases hkey_cases with h | ⟨hv, h⟩
      · rw [h]
        obtain ⟨h1, h2⟩ := K.key_spec x
        refine ⟨h1, fun h0 => ?_⟩
        obtain ⟨h3, l, hl, hq⟩ := h2 h0
        exact ⟨(hpast _).mpr h3, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
      · have hq := (I.d_spec q j l 2 _ hv).2.2 (by norm_num)
        refine ⟨fun h0 => absurd (h.symm.trans h0) hj1, fun _ => ⟨?_, l, ?_, ?_⟩⟩
        · rw [hpast, h]; exact hrev.1
        · rw [h]; exact hm.rev _ _ hrev.2
        · rw [h]; exact QC_mono hm.tok hq
    · rw [hX, hMprop, hMview]
      intro j' hj1' hj2
      obtain ⟨h1, h2, h3⟩ := K.prop_spec x j' hj1' hj2
      refine ⟨h1, h2, fun h0 => ?_⟩
      obtain ⟨l, hl, hq⟩ := h3 h0
      exact ⟨l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · rw [hX, hMprop, hMview, hMlead, hMexitR]
      intro j0 j' hj0 hj l' hl' h hh hc w hw
      have hc' : h ∉ s.corrupt := fun h' => hc (hm.corrupt h')
      obtain ⟨hP, -⟩ := I.rcvd_spec x j0 h (I.exitR_sub x j0 hh) hc'
      rw [hd h j0 hP] at hw
      exact K.prop_lock x j0 j' hj0 hj l' hl' h hh hc' w hw
  | exitView x =>
    obtain ⟨hx, hph, hcard⟩ := hE
    simp only [Act.actor] at hloc hd
    have hX : (eff c (.exitView x) s).loc x = { s.loc x with
        view := (s.loc x).view + 1
        ph := .bc
        exitR := Function.update (s.loc x).exitR (s.loc x).view ((s.loc x).rcvd (s.loc x).view)
        prop := Function.update (s.loc x).prop ((s.loc x).view + 1) (s.loc x).key } := by
      simp [eff]
    have hpast : ∀ i, Past ((eff c (.exitView x) s).loc x) i ↔ Past (s.loc x) i := by
      intro i; rw [hX]; simp only [Past, hph]
      constructor
      · rintro (h | ⟨-, h⟩)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h, trivial⟩
        · exact absurd h (by decide)
      · rintro (h | ⟨h, -⟩)
        · left; omega
        · left; omega
    refine kinv_of_frame K I hm x hloc hd ?_ ?_ ?_ ?_
    · rw [hpast, hX]
      intro h0
      obtain ⟨h1, l, v, hl, hq⟩ := K.lock_spec x h0
      exact ⟨h1, l, v, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · rw [hpast, hX]
      obtain ⟨h1, h2⟩ := K.key_spec x
      refine ⟨h1, fun h0 => ?_⟩
      obtain ⟨h3, l, hl, hq⟩ := h2 h0
      exact ⟨h3, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · rw [hX]
      intro j hj1 hj2
      simp only at hj2 ⊢
      by_cases hj : j = (s.loc x).view + 1
      · subst hj
        rw [Function.update_self]
        obtain ⟨h1, h2⟩ := K.key_spec x
        refine ⟨?_, h1, fun h0 => ?_⟩
        · by_cases h0 : (s.loc x).key.1 = 0
          · omega
          · obtain ⟨h3, -⟩ := h2 h0
            rcases h3 with h3 | ⟨h3, -⟩ <;> omega
        · obtain ⟨-, l, hl, hq⟩ := h2 h0
          exact ⟨l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
      · rw [Function.update_of_ne hj]
        obtain ⟨h1, h2, h3⟩ := K.prop_spec x j hj1 (by omega)
        refine ⟨h1, h2, fun h0 => ?_⟩
        obtain ⟨l, hl, hq⟩ := h3 h0
        exact ⟨l, hm.rev _ _ hl, QC_mono hm.tok hq⟩
    · rw [hX]
      intro j0 j hj0 hj l hl h hh hc v hv
      simp only at hj hl hh ⊢
      have hc' : h ∉ s.corrupt := fun h' => hc (hm.corrupt h')
      have hh' : h ∈ (s.loc x).rcvd j0 := by
        rw [Function.update_apply] at hh
        split_ifs at hh with h0
        · subst h0; exact hh
        · exact I.exitR_sub x j0 hh
      obtain ⟨hP, l', hl', hvv⟩ := I.rcvd_spec x j0 h hh' hc'
      rw [hl] at hl'; cases hl'
      rw [hd h j0 hP] at hv
      by_cases hj' : j = (s.loc x).view + 1
      · subst hj'
        rw [Function.update_self]
        exact (hvv v).1 hv
      · rw [Function.update_of_ne hj']
        have hj0' : j0 ≠ (s.loc x).view := by omega
        rw [Function.update_of_ne hj0'] at hh
        exact K.prop_lock x j0 j hj0 (by omega) l hl h hh hc' v hv

/-- `KInv` holds in every reachable state. -/
theorem Reach.kinv {s : Glob P V} (h : Reach C s) : KInv C s := by
  induction h with
  | init => exact kinv_init C
  | @step s c a hR ih =>
    unfold VABA.step; split_ifs with hE
    · exact kinv_eff ih hR.inv c a hE
    · exact ih

/-- **Lemma 15** (key progress). If inputs are externally valid, then in every reachable state the
proposal of any party `q` for view `j` (its `KEY` at the end of view `j - 1`) passes the external
validation of every party `p` in the broadcast phase of view `j`. -/
theorem proposal_valid (hQ : Fintype.card P + C.f < 2 * C.Q) (hinput : ∀ p, C.valid (C.input p))
    (hR : Reach C s) {p q : P} (hph : (s.loc p).ph = .bc)
    (hj : (s.loc p).view ≤ (s.loc q).view) :
    Valid C s (s.loc p) q 1 ((s.loc q).prop (s.loc p).view).2
      ((s.loc q).prop (s.loc p).view).1 := by
  have I := hR.inv
  have K := hR.kinv
  set j := (s.loc p).view with hjdef
  have hj1 : 1 ≤ j := I.view_pos p
  obtain ⟨hrj, hr0, hrq⟩ := K.prop_spec q j hj1 hj
  simp only [Valid, ite_true]
  refine ⟨?_, ?_, ?_⟩
  · -- external validity of the proposed value
    by_cases h0 : ((s.loc q).prop j).1 = 0
    · rw [hr0 h0]; exact hinput q
    · obtain ⟨l, -, hqc⟩ := hrq h0
      obtain ⟨h, hh, ht⟩ := I.honest_signer hQ hqc
      rw [I.tok_pb h hh] at ht
      exact ((I.d_spec h _ l 1 _ ht).2.1 rfl).1
  · -- the key is at least the lock (Lemma 14)
    by_cases h0 : (s.loc p).lock = 0
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨hP, l, w, hl, hqc⟩ := K.lock_spec p h0
      set i := (s.loc p).lock
      have hij : i < j := by
        rcases hP with h | ⟨-, h⟩
        · exact h
        · rw [hph] at h; exact absurd h (by decide)
      have hi1 : 1 ≤ i := Nat.pos_of_ne_zero h0
      obtain ⟨h, hex, hsig, hc⟩ :=
        exists_honest_inter hQ (I.exitR_card q i hi1 (by omega)) hqc I.card_corrupt
      rw [mem_signers, I.tok_pb h hc] at hsig
      obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp (I.lead_some q i hi1 (Or.inl (by omega)))
      have : l' = l := by
        have := (I.lead_spec q i l' hl').2; rw [hl] at this; exact (Option.some.inj this).symm
      subst this
      exact K.prop_lock q i j hij hj l' hl' h hex hc w hsig
  · -- the key is a stage-1 certificate of a leader known to `p`
    by_cases h0 : ((s.loc q).prop j).1 = 0
    · exact Or.inl h0
    · right
      obtain ⟨l, hl, hqc⟩ := hrq h0
      obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp
        (I.lead_some p _ (Nat.pos_of_ne_zero h0) (Or.inl hrj))
      have : l' = l := by
        have := (I.lead_spec p _ l' hl').2; rw [hl] at this; exact (Option.some.inj this).symm
      subst this
      exact ⟨l', hl', hqc⟩

end VABA
