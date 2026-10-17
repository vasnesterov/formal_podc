import Papers.PODC2019.VABA.Basic

/-!
# VABA: the main state invariant

`Inv C s` collects the facts about reachable states used in the safety and progress proofs.
Except for the two `tok_*` fields, every field holds for *all* parties: only honest parties change
their local state, so the local state of a corrupted party stays as it was when it was corrupted.
-/

namespace VABA

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-- The invariant of reachable states. -/
structure Inv (C : Cfg P V) (s : Glob P V) : Prop where
  card_corrupt : s.corrupt.card ≤ C.f
  rev_zero : s.rev 0 = none
  /-- honest shares on broadcast statements are exactly the deliveries -/
  tok_pb : ∀ p, p ∉ s.corrupt → ∀ j k st v, s.tok p (.pb j k st v) ↔ (s.loc p).d j k st = some v
  /-- honest skip shares are sent only after `Q` completed broadcasts -/
  tok_skip : ∀ p, p ∉ s.corrupt → ∀ j, s.tok p (.skip j) → C.Q ≤ (completed C.Q s j).card
  view_pos : ∀ p, 1 ≤ (s.loc p).view
  /-- deliveries passed the external validation -/
  d_spec : ∀ p j k st v, (s.loc p).d j k st = some v → j ≤ (s.loc p).view ∧
      (st = 1 → C.valid v ∧ ((s.loc p).kv j k = 0 ∨ (0 < (s.loc p).kv j k ∧
        (s.loc p).kv j k < j ∧
        ∃ l, s.rev ((s.loc p).kv j k) = some l ∧ QC C.Q s (.pb ((s.loc p).kv j k) l 1 v)))) ∧
      (st ≠ 1 → QC C.Q s (.pb j k (st - 1) v))
  lead_spec : ∀ p i l, (s.loc p).lead i = some l → Past (s.loc p) i ∧ s.rev i = some l
  lead_some : ∀ p i, 1 ≤ i → Past (s.loc p) i → ((s.loc p).lead i).isSome
  /-- a view-change message of an honest sender was processed with its (frozen) content -/
  rcvd_spec : ∀ p j h, h ∈ (s.loc p).rcvd j → h ∉ s.corrupt → Past (s.loc h) j ∧
      ∃ l, (s.loc p).lead j = some l ∧ ∀ v,
        ((s.loc h).d j l 2 = some v → j ≤ (s.loc p).key.1) ∧
        ((s.loc h).d j l 3 = some v → j ≤ (s.loc p).lock) ∧
        ((s.loc h).d j l 4 = some v → v ∈ (s.loc p).decs)
  exitR_sub : ∀ p j, (s.loc p).exitR j ⊆ (s.loc p).rcvd j
  exitR_card : ∀ p j, 1 ≤ j → j < (s.loc p).view → C.Q ≤ ((s.loc p).exitR j).card
  /-- the key of a stage-1 delivery is at least every view whose exit set contains an honest
  party that delivered a lock in that view's leader broadcast -/
  kv_spec : ∀ p j k v, (s.loc p).d j k 1 = some v → ∀ j0 l, j0 < j →
      (s.loc p).lead j0 = some l → ∀ h ∈ (s.loc p).exitR j0, h ∉ s.corrupt →
      ∀ v', (s.loc h).d j0 l 3 = some v' → j0 ≤ (s.loc p).kv j k
  /-- decisions are backed by a stage-3 certificate of a leader -/
  decs_spec : ∀ p v, v ∈ (s.loc p).decs → ∃ j l, s.rev j = some l ∧ QC C.Q s (.pb j l 3 v)

omit [DecidableEq P] in
lemma inv_init (C : Cfg P V) : Inv C (init C) where
  card_corrupt := by simp [init]
  rev_zero := rfl
  tok_pb := by simp [init]
  tok_skip := by simp [init]
  view_pos := by simp [init]
  d_spec := by simp [init]
  lead_spec := by simp [init]
  lead_some := by simp [init, Past]; intros; omega
  rcvd_spec := by simp [init]
  exitR_sub := by simp [init]
  exitR_card := by simp [init]; omega
  kv_spec := by simp [init]
  decs_spec := by simp [init]

/-! ### Monotonicity of steps -/

section mono
omit [Fintype P] [DecidableEq P]

/-- Monotone parts of the state. -/
structure Mono (s s' : Glob P V) : Prop where
  corrupt : s.corrupt ⊆ s'.corrupt
  tok : ∀ p x, s.tok p x → s'.tok p x
  rev : ∀ i l, s.rev i = some l → s'.rev i = some l

lemma Mono.refl (s : Glob P V) : Mono s s := ⟨subset_rfl, fun _ _ h => h, fun _ _ h => h⟩

lemma Mono.trans {s s' s'' : Glob P V} (h : Mono s s') (h' : Mono s' s'') : Mono s s'' :=
  ⟨h.corrupt.trans h'.corrupt, fun p x hx => h'.tok p x (h.tok p x hx),
    fun i l hi => h'.rev i l (h.rev i l hi)⟩

variable [DecidableEq P] in
lemma mono_eff (c : ℕ → P) (a : Act P V) (s : Glob P V) : Mono s (eff c a s) := by
  cases a with
  | deliver p k st v r => exact ⟨subset_rfl, fun q x h => Or.inl h, fun _ _ h => h⟩
  | skipShare p j => exact ⟨subset_rfl, fun q x h => Or.inl h, fun _ _ h => h⟩
  | invokeElect p =>
    refine ⟨subset_rfl, fun _ _ h => h, fun i l h => ?_⟩
    simp only [eff]
    split_ifs with hi
    · rw [hi.1, hi.2] at h; simp at h
    · exact h
  | electReturn p => exact ⟨subset_rfl, fun _ _ h => h, fun _ _ h => h⟩
  | recvVC p q j b =>
    simp only [eff]; split
    · exact ⟨subset_rfl, fun _ _ h => h, fun _ _ h => h⟩
    · exact Mono.refl s
  | recvQC p j st v => exact ⟨subset_rfl, fun _ _ h => h, fun _ _ h => h⟩
  | exitView p => exact ⟨subset_rfl, fun _ _ h => h, fun _ _ h => h⟩
  | corrupt p => exact ⟨subset_insert _ _, fun _ _ h => h, fun _ _ h => h⟩
  | byzSign p st => exact ⟨subset_rfl, fun q x h => Or.inl h, fun _ _ h => h⟩

variable [Fintype P] [DecidableEq P] in
lemma mono_step (C : Cfg P V) (c : ℕ → P) (a : Act P V) (s : Glob P V) :
    Mono s (step C c a s) := by
  unfold step; split_ifs
  · exact mono_eff c a s
  · exact Mono.refl s

end mono

/-! ### Preservation, action by action -/

section preserve

variable {C : Cfg P V} {s : Glob P V}

lemma inv_corrupt (I : Inv C s) (x : P) (hE : Enabled C (.corrupt x) s) (c : ℕ → P) :
    Inv C (eff c (.corrupt x) s) := by
  obtain ⟨-, hlt⟩ := hE
  simp only [eff]
  refine
    { card_corrupt := (card_insert_le _ _).trans (by omega)
      rev_zero := I.rev_zero
      tok_pb := fun p hp => I.tok_pb p (fun h => hp (mem_insert_of_mem h))
      tok_skip := fun p hp => I.tok_skip p (fun h => hp (mem_insert_of_mem h))
      view_pos := I.view_pos
      d_spec := I.d_spec
      lead_spec := I.lead_spec
      lead_some := I.lead_some
      rcvd_spec := fun p j h hh hc => I.rcvd_spec p j h hh (fun h' => hc (mem_insert_of_mem h'))
      exitR_sub := I.exitR_sub
      exitR_card := I.exitR_card
      kv_spec := fun p j k v hv j0 l hj hl h hh hc =>
        I.kv_spec p j k v hv j0 l hj hl h hh (fun h' => hc (mem_insert_of_mem h'))
      decs_spec := I.decs_spec }

lemma inv_byzSign (I : Inv C s) (x : P) (st : Stmt P V) (hE : Enabled C (.byzSign x st) s)
    (c : ℕ → P) : Inv C (eff c (.byzSign x st) s) := by
  have hE' : x ∈ s.corrupt := hE
  have hm := mono_eff c (.byzSign x st) s
  simp only [eff] at hm ⊢
  refine
    { card_corrupt := I.card_corrupt
      rev_zero := I.rev_zero
      tok_pb := fun p hp j k st' v => ?_
      tok_skip := fun p hp j hj => ?_
      view_pos := I.view_pos
      d_spec := fun p j k st' v hv => ?_
      lead_spec := I.lead_spec
      lead_some := I.lead_some
      rcvd_spec := I.rcvd_spec
      exitR_sub := I.exitR_sub
      exitR_card := I.exitR_card
      kv_spec := I.kv_spec
      decs_spec := fun p v hv => ?_ }
  · have hpx : p ≠ x := fun h => hp (h ▸ hE')
    simp only [sign_tok, hpx, false_and, or_false, sign_loc]
    exact I.tok_pb p hp j k st' v
  · have hpx : p ≠ x := fun h => hp (h ▸ hE')
    simp only [sign_tok, hpx, false_and, or_false] at hj
    exact (I.tok_skip p hp j hj).trans (card_le_card (completed_mono hm.tok j))
  · obtain ⟨h1, h2, h3⟩ := I.d_spec p j k st' v hv
    refine ⟨h1, fun h => ?_, fun h => QC_mono hm.tok (h3 h)⟩
    obtain ⟨h4, h5⟩ := h2 h
    refine ⟨h4, h5.imp id (fun ⟨a, b, l, hl, hq⟩ => ⟨a, b, l, hl, QC_mono hm.tok hq⟩)⟩
  · obtain ⟨j, l, hl, hq⟩ := I.decs_spec p v hv
    exact ⟨j, l, hl, QC_mono hm.tok hq⟩

lemma inv_skipShare (I : Inv C s) (x : P) (j0 : ℕ) (hE : Enabled C (.skipShare x j0) s)
    (c : ℕ → P) : Inv C (eff c (.skipShare x j0) s) := by
  obtain ⟨hx, hcard⟩ := hE
  have hm := mono_eff c (.skipShare x j0) s
  simp only [eff] at hm ⊢
  refine
    { card_corrupt := I.card_corrupt
      rev_zero := I.rev_zero
      tok_pb := fun p hp j k st' v => ?_
      tok_skip := fun p hp j hj => ?_
      view_pos := I.view_pos
      d_spec := fun p j k st' v hv => ?_
      lead_spec := I.lead_spec
      lead_some := I.lead_some
      rcvd_spec := I.rcvd_spec
      exitR_sub := I.exitR_sub
      exitR_card := I.exitR_card
      kv_spec := I.kv_spec
      decs_spec := fun p v hv => ?_ }
  · simp only [sign_tok, sign_loc, reduceCtorEq, and_false, or_false]
    exact I.tok_pb p hp j k st' v
  · simp only [sign_tok, Stmt.skip.injEq] at hj
    rcases hj with hj | ⟨rfl, rfl⟩
    · exact (I.tok_skip p hp j hj).trans (card_le_card (completed_mono hm.tok j))
    · exact hcard.trans (card_le_card (completed_mono hm.tok _))
  · obtain ⟨h1, h2, h3⟩ := I.d_spec p j k st' v hv
    refine ⟨h1, fun h => ?_, fun h => QC_mono hm.tok (h3 h)⟩
    obtain ⟨h4, h5⟩ := h2 h
    refine ⟨h4, h5.imp id (fun ⟨a, b, l, hl, hq⟩ => ⟨a, b, l, hl, QC_mono hm.tok hq⟩)⟩
  · obtain ⟨j, l, hl, hq⟩ := I.decs_spec p v hv
    exact ⟨j, l, hl, QC_mono hm.tok hq⟩

lemma inv_deliver (I : Inv C s) (x k : P) (st : ℕ) (v : V) (r : ℕ)
    (hE : Enabled C (.deliver x k st v r) s) (c : ℕ → P) :
    Inv C (eff c (.deliver x k st v r) s) := by
  obtain ⟨hx, hph, hst1, hst4, hnone, hval, -⟩ := hE
  have hm := mono_eff c (.deliver x k st v r) s
  set L := s.loc x with hL
  set jx := L.view with hjx
  set L' : Loc P V := { L with
        d := fun j' k' s' => if j' = jx ∧ k' = k ∧ s' = st then some v else L.d j' k' s'
        kv := fun j' k' => if j' = jx ∧ k' = k ∧ st = 1 then r else L.kv j' k' } with hL'
  have heff : eff c (.deliver x k st v r) s = (s.sign x (.pb jx k st v)).upd x L' := rfl
  rw [heff] at hm ⊢
  -- frozen deliveries of past views
  have hfr : ∀ q j', Past (s.loc q) j' →
      (((s.sign x (.pb jx k st v)).upd x L').loc q).d j' = (s.loc q).d j' := by
    intro q j' hq
    simp only [upd_loc, sign_loc]
    split_ifs with hqx
    · subst hqx
      have : j' < jx := by
        rcases hq with hq | ⟨_, hq⟩
        · exact hq
        · rw [← hL, hph] at hq; exact absurd hq (by decide)
      funext k' s'
      simp only [L', show ¬ (j' = jx) from by omega, false_and, ite_false]
      rfl
    · rfl
  have hpast : ∀ q j', Past (((s.sign x (.pb jx k st v)).upd x L').loc q) j' ↔
      Past (s.loc q) j' := by
    intro q j'; simp only [upd_loc, sign_loc]; split_ifs with hqx
    · subst hqx; rfl
    · rfl
  refine
    { card_corrupt := I.card_corrupt
      rev_zero := I.rev_zero
      tok_pb := fun p hp j k' st' v' => ?_
      tok_skip := fun p hp j hj => ?_
      view_pos := fun p => ?_
      d_spec := fun p j k' st' v' hv => ?_
      lead_spec := fun p i l hl => ?_
      lead_some := fun p i hi hp => ?_
      rcvd_spec := fun p j h hh hc => ?_
      exitR_sub := fun p j => ?_
      exitR_card := fun p j hj1 hj2 => ?_
      kv_spec := fun p j k' v' hv j0 l hj0 hl h hh hc v'' hv'' => ?_
      decs_spec := fun p v' hv => ?_ }
  · -- tok_pb
    simp only [upd_corrupt, sign_corrupt] at hp
    simp only [sign_tok, upd_tok, upd_loc, sign_loc, Stmt.pb.injEq]
    by_cases hpx : p = x
    · subst hpx
      simp only [ite_true, L']
      by_cases hc : j = jx ∧ k' = k ∧ st' = st
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [and_self, ite_true, true_and, Option.some.injEq]
        rw [I.tok_pb p hp, ← hL, hnone]
        constructor
        · rintro (h | h); · simp at h
          · exact h.symm
        · intro h; exact Or.inr h.symm
      · rw [ite_eq_right hc, I.tok_pb p hp]
        constructor
        · rintro (h | ⟨-, h1, h2, h3, -⟩)
          · exact h
          · exact absurd ⟨h1, h2, h3⟩ hc
        · exact Or.inl
    · simp only [hpx, false_and, or_false, ite_false]
      exact I.tok_pb p hp j k' st' v'
  · -- tok_skip
    simp only [upd_corrupt, sign_corrupt] at hp
    simp only [upd_tok, sign_tok, reduceCtorEq, and_false, or_false] at hj
    exact (I.tok_skip p hp j hj).trans (card_le_card (completed_mono hm.tok j))
  · -- view_pos
    simp only [upd_loc, sign_loc]; split_ifs with hpx
    · subst hpx; exact I.view_pos p
    · exact I.view_pos p
  · -- d_spec
    simp only [upd_loc, sign_loc] at hv ⊢
    by_cases hpx : p = x
    · subst hpx
      simp only [ite_true, L'] at hv ⊢
      by_cases hc : j = jx ∧ k' = k ∧ st' = st
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [and_self, ite_true, Option.some.injEq] at hv
        subst hv
        refine ⟨le_rfl, fun h1 => ?_, fun h1 => ?_⟩
        · subst h1
          simp only [Valid, ite_true] at hval
          obtain ⟨hv1, hlock, hr⟩ := hval
          rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
          refine ⟨hv1, hr.imp id (fun ⟨l, hl, hq⟩ => ?_)⟩
          obtain ⟨hpast, hrev⟩ := I.lead_spec p r l hl
          have hrlt : r < jx := by
            rcases hpast with h | ⟨_, h⟩
            · exact h
            · rw [← hL, hph] at h; exact absurd h (by decide)
          have hr0 : 0 < r := by
            rcases Nat.eq_zero_or_pos r with h0 | h0
            · rw [h0, I.rev_zero] at hrev; simp at hrev
            · exact h0
          exact ⟨hr0, hrlt, l, hrev, QC_mono hm.tok hq⟩
        · simp only [Valid, h1, ite_false] at hval
          exact QC_mono hm.tok hval
      · rw [ite_eq_right hc] at hv
        obtain ⟨h1, h2, h3⟩ := I.d_spec p j k' st' v' hv
        refine ⟨h1, fun h => ?_, fun h => QC_mono hm.tok (h3 h)⟩
        have hkv : ¬ (j = jx ∧ k' = k ∧ st = 1) := by
          rintro ⟨a, b, c'⟩; exact hc ⟨a, b, by omega⟩
        rw [ite_eq_right hkv]
        obtain ⟨h4, h5⟩ := h2 h
        exact ⟨h4, h5.imp id (fun ⟨a, b, l, hl, hq⟩ => ⟨a, b, l, hl, QC_mono hm.tok hq⟩)⟩
    · simp only [hpx, ite_false] at hv ⊢
      obtain ⟨h1, h2, h3⟩ := I.d_spec p j k' st' v' hv
      refine ⟨h1, fun h => ?_, fun h => QC_mono hm.tok (h3 h)⟩
      obtain ⟨h4, h5⟩ := h2 h
      exact ⟨h4, h5.imp id (fun ⟨a, b, l, hl, hq⟩ => ⟨a, b, l, hl, QC_mono hm.tok hq⟩)⟩
  · -- lead_spec
    rw [hpast]
    simp only [upd_loc, sign_loc, upd_rev, sign_rev] at hl ⊢
    split_ifs at hl with hpx
    · subst hpx; exact I.lead_spec p i l hl
    · exact I.lead_spec p i l hl
  · -- lead_some
    rw [hpast] at hp
    simp only [upd_loc, sign_loc]
    split_ifs with hpx
    · subst hpx; exact I.lead_some p i hi hp
    · exact I.lead_some p i hi hp
  · -- rcvd_spec
    simp only [upd_corrupt, sign_corrupt] at hc
    have hh' : h ∈ (s.loc p).rcvd j := by
      simp only [upd_loc, sign_loc] at hh; split_ifs at hh with hpx
      · subst hpx; exact hh
      · exact hh
    obtain ⟨hP, l, hl, hv⟩ := I.rcvd_spec p j h hh' hc
    rw [hpast, hfr h j hP]
    refine ⟨hP, l, ?_, ?_⟩
    · simp only [upd_loc, sign_loc]; split_ifs with hpx
      · subst hpx; exact hl
      · exact hl
    · simp only [upd_loc, sign_loc]; split_ifs with hpx
      · subst hpx; exact hv
      · exact hv
  · -- exitR_sub
    simp only [upd_loc, sign_loc]; split_ifs with hpx
    · subst hpx; exact I.exitR_sub p j
    · exact I.exitR_sub p j
  · -- exitR_card
    simp only [upd_loc, sign_loc] at hj2 ⊢; split_ifs at hj2 ⊢ with hpx
    · subst hpx; exact I.exitR_card p j hj1 hj2
    · exact I.exitR_card p j hj1 hj2
  · -- kv_spec
    simp only [upd_corrupt, sign_corrupt] at hc
    have hh' : h ∈ (s.loc p).exitR j0 := by
      simp only [upd_loc, sign_loc] at hh; split_ifs at hh with hpx
      · subst hpx; exact hh
      · exact hh
    have hl' : (s.loc p).lead j0 = some l := by
      simp only [upd_loc, sign_loc] at hl; split_ifs at hl with hpx
      · subst hpx; exact hl
      · exact hl
    obtain ⟨hP, l2, hl2, hvv⟩ := I.rcvd_spec p j0 h (I.exitR_sub p j0 hh') hc
    rw [hl'] at hl2; cases hl2
    rw [hfr h j0 hP] at hv''
    simp only [upd_loc, sign_loc] at hv ⊢
    by_cases hpx : p = x
    · subst hpx
      simp only [ite_true, L'] at hv ⊢
      by_cases hc' : j = jx ∧ k' = k ∧ (1 : ℕ) = st
      · obtain ⟨rfl, rfl, hst⟩ := hc'
        simp only [and_self, ← hst, ite_true]
        simp only [Valid, ← hst, ite_true] at hval
        exact ((hvv v'').2.1 hv'').trans hval.2.1
      · rw [ite_eq_right hc'] at hv
        have hkv : ¬ (j = jx ∧ k' = k ∧ st = 1) := by
          rintro ⟨a, b, c'⟩; exact hc' ⟨a, b, c'.symm⟩
        rw [ite_eq_right hkv]
        exact I.kv_spec p j k' v' hv j0 l hj0 hl' h hh' hc v'' hv''
    · simp only [hpx, ite_false] at hv ⊢
      exact I.kv_spec p j k' v' hv j0 l hj0 hl' h hh' hc v'' hv''
  · -- decs_spec
    have hv' : v' ∈ (s.loc p).decs := by
      simp only [upd_loc, sign_loc] at hv; split_ifs at hv with hpx
      · subst hpx; exact hv
      · exact hv
    obtain ⟨j, l, hl, hq⟩ := I.decs_spec p v' hv'
    exact ⟨j, l, hl, QC_mono hm.tok hq⟩

/-- Generic preservation when only the local state of `x` changes, to `L'`, with the same view,
phase, leaders, deliveries, key views and exit sets, more received view-change messages, and
monotone `key`, `lock`, `decs`; the remaining obligations are `rcvd_spec` and `decs_spec` for `x`. -/
lemma inv_upd_local (I : Inv C s) (x : P) (L' : Loc P V)
    (hview : L'.view = (s.loc x).view) (hph : L'.ph = (s.loc x).ph)
    (hlead : L'.lead = (s.loc x).lead) (hd : L'.d = (s.loc x).d) (hkv : L'.kv = (s.loc x).kv)
    (hexitR : L'.exitR = (s.loc x).exitR) (hrcvd : ∀ j, (s.loc x).rcvd j ⊆ L'.rcvd j)
    (hrcvdx : ∀ j h, h ∈ L'.rcvd j → h ∉ s.corrupt → Past (s.loc h) j ∧
      ∃ l, L'.lead j = some l ∧ ∀ v,
        ((s.loc h).d j l 2 = some v → j ≤ L'.key.1) ∧
        ((s.loc h).d j l 3 = some v → j ≤ L'.lock) ∧
        ((s.loc h).d j l 4 = some v → v ∈ L'.decs))
    (hdecsx : ∀ v, v ∈ L'.decs → ∃ j l, s.rev j = some l ∧ QC C.Q s (.pb j l 3 v)) :
    Inv C (s.upd x L') := by
  have hpast : ∀ q j, Past ((s.upd x L').loc q) j ↔ Past (s.loc q) j := by
    intro q j; simp only [upd_loc]; split_ifs with hq
    · subst hq; simp only [Past, hview, hph]
    · rfl
  have hdq : ∀ q, ((s.upd x L').loc q).d = (s.loc q).d := by
    intro q; simp only [upd_loc]; split_ifs with hq
    · subst hq; exact hd
    · rfl
  refine
    { card_corrupt := I.card_corrupt
      rev_zero := I.rev_zero
      tok_pb := fun p hp j k st v => by rw [hdq]; exact I.tok_pb p hp j k st v
      tok_skip := I.tok_skip
      view_pos := fun p => ?_
      d_spec := fun p j k st v hv => ?_
      lead_spec := fun p i l hl => ?_
      lead_some := fun p i hi hp => ?_
      rcvd_spec := fun p j h hh hc => ?_
      exitR_sub := fun p j => ?_
      exitR_card := fun p j hj1 hj2 => ?_
      kv_spec := fun p j k v hv j0 l hj0 hl h hh hc v' hv' => ?_
      decs_spec := fun p v hv => ?_ }
  · simp only [upd_loc]; split_ifs with hp
    · subst hp; rw [hview]; exact I.view_pos p
    · exact I.view_pos p
  · rw [hdq] at hv
    have := I.d_spec p j k st v hv
    simp only [upd_loc, upd_rev]; split_ifs with hp
    · subst hp; rw [hview, hkv]; exact this
    · exact this
  · rw [hpast]
    simp only [upd_loc, upd_rev] at hl ⊢; split_ifs at hl with hp
    · subst hp; rw [hlead] at hl; exact I.lead_spec p i l hl
    · exact I.lead_spec p i l hl
  · rw [hpast] at hp
    simp only [upd_loc]; split_ifs with hp'
    · subst hp'; rw [hlead]; exact I.lead_some p i hi hp
    · exact I.lead_some p i hi hp
  · simp only [upd_corrupt] at hc
    rw [hpast, hdq]
    simp only [upd_loc] at hh ⊢; split_ifs at hh ⊢ with hp
    · subst hp; exact hrcvdx j h hh hc
    · exact I.rcvd_spec p j h hh hc
  · simp only [upd_loc]; split_ifs with hp
    · subst hp; rw [hexitR]; exact (I.exitR_sub p j).trans (hrcvd j)
    · exact I.exitR_sub p j
  · simp only [upd_loc] at hj2 ⊢; split_ifs at hj2 ⊢ with hp
    · subst hp; rw [hexitR]; rw [hview] at hj2; exact I.exitR_card p j hj1 hj2
    · exact I.exitR_card p j hj1 hj2
  · simp only [upd_corrupt] at hc
    rw [hdq] at hv'
    simp only [upd_loc] at hv hl hh ⊢; split_ifs at hv hl hh ⊢ with hp
    · subst hp; rw [hd] at hv; rw [hlead] at hl; rw [hexitR] at hh; rw [hkv]
      exact I.kv_spec p j k v hv j0 l hj0 hl h hh hc v' hv'
    · exact I.kv_spec p j k v hv j0 l hj0 hl h hh hc v' hv'
  · simp only [upd_loc, upd_rev] at hv ⊢; split_ifs at hv with hp
    · subst hp; exact hdecsx v hv
    · exact I.decs_spec p v hv

lemma inv_recvQC (I : Inv C s) (x : P) (j st : ℕ) (v : V) (hE : Enabled C (.recvQC x j st v) s)
    (c : ℕ → P) : Inv C (eff c (.recvQC x j st v) s) := by
  obtain ⟨hx, hst1, hst3, l, hl, hq⟩ := hE
  simp only [eff]
  apply inv_upd_local I x _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp)
  · intro j' h hh hc
    simp only [proc_rcvd, proc_lead] at hh ⊢
    obtain ⟨hP, l', hl', hv⟩ := I.rcvd_spec x j' h hh hc
    refine ⟨hP, l', hl', fun v' => ⟨fun h2 => ?_, fun h3 => ?_, fun h4 => ?_⟩⟩
    · exact ((hv v').1 h2).trans (proc_key_mono _ _ _ _)
    · exact ((hv v').2.1 h3).trans (proc_lock_mono _ _ _ _)
    · exact proc_decs_mono _ _ _ _ ((hv v').2.2 h4)
  · intro v' hv'
    rcases proc_decs_cases _ _ _ _ hv' with h | ⟨rfl, h⟩
    · exact I.decs_spec x v' h
    · cases h
      exact ⟨j, l, (I.lead_spec x j l hl).2, hq⟩

lemma inv_recvVC (I : Inv C s) (x q : P) (j : ℕ) (b : Bool) (hE : Enabled C (.recvVC x q j b) s)
    (c : ℕ → P) : Inv C (eff c (.recvVC x q j b) s) := by
  obtain ⟨hx, hl0, hb⟩ := hE
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hl0
  set L := s.loc x with hL
  set L' : Loc P V := { L with rcvd := Function.update L.rcvd j (insert q (L.rcvd j)) } with hL'
  have heff : eff c (.recvVC x q j b) s = s.upd x (if b then procVC j l (s.loc q) L' else L') := by
    simp only [eff, ← hL, hl]; rfl
  rw [heff]
  set M := if b then procVC j l (s.loc q) L' else L' with hM
  have hMview : M.view = L.view := by rw [hM]; split_ifs <;> simp [L']
  have hMph : M.ph = L.ph := by rw [hM]; split_ifs <;> simp [L']
  have hMlead : M.lead = L.lead := by rw [hM]; split_ifs <;> simp [L']
  have hMd : M.d = L.d := by rw [hM]; split_ifs <;> simp [L']
  have hMkv : M.kv = L.kv := by rw [hM]; split_ifs <;> simp [L']
  have hMexitR : M.exitR = L.exitR := by rw [hM]; split_ifs <;> simp [L']
  have hMrcvd : M.rcvd = L'.rcvd := by rw [hM]; split_ifs <;> simp
  have hMkey : L.key.1 ≤ M.key.1 := by
    rw [hM]; split_ifs
    · exact procVC_key_mono j l (s.loc q) L'
    · exact le_rfl
  have hMlock : L.lock ≤ M.lock := by
    rw [hM]; split_ifs
    · exact procVC_lock_mono j l (s.loc q) L'
    · exact le_rfl
  have hMdecs : L.decs ⊆ M.decs := by
    rw [hM]; split_ifs
    · exact procVC_decs_mono j l (s.loc q) L'
    · exact subset_rfl
  apply inv_upd_local I x M hMview hMph hMlead hMd hMkv hMexitR
  · intro j'; rw [hMrcvd]; simp only [L', Function.update_apply]; split_ifs with h
    · subst h; exact subset_insert _ _
    · exact subset_rfl
  · intro j' h hh hc
    rw [hMrcvd] at hh
    simp only [L', Function.update_apply] at hh
    rw [hMlead]
    by_cases hj : j' = j
    · subst hj
      simp only [ite_true, mem_insert] at hh
      rcases hh with rfl | hh
      · -- the new sender
        cases b with
        | false => simp only [Bool.false_eq_true, ite_false] at hb; exact absurd hb hc
        | true =>
          simp only [ite_true] at hb
          refine ⟨hb, l, hl, fun v => ⟨fun h2 => ?_, fun h3 => ?_, fun h4 => ?_⟩⟩
          · simp only [hM, ite_true]; exact procVC_key_of _ _ _ _ h2
          · simp only [hM, ite_true]; exact procVC_lock_of _ _ _ _ h3
          · simp only [hM, ite_true]; exact procVC_decs_of _ _ _ _ h4
      · obtain ⟨hP, l', hl', hv⟩ := I.rcvd_spec x j' h hh hc
        refine ⟨hP, l', hl', fun v => ⟨fun h2 => ?_, fun h3 => ?_, fun h4 => ?_⟩⟩
        · exact ((hv v).1 h2).trans hMkey
        · exact ((hv v).2.1 h3).trans hMlock
        · exact hMdecs ((hv v).2.2 h4)
    · simp only [hj, ite_false] at hh
      obtain ⟨hP, l', hl', hv⟩ := I.rcvd_spec x j' h hh hc
      refine ⟨hP, l', hl', fun v => ⟨fun h2 => ?_, fun h3 => ?_, fun h4 => ?_⟩⟩
      · exact ((hv v).1 h2).trans hMkey
      · exact ((hv v).2.1 h3).trans hMlock
      · exact hMdecs ((hv v).2.2 h4)
  · intro v hv
    cases b with
    | false => exact I.decs_spec x v (by simpa [hM, L'] using hv)
    | true =>
      simp only [hM, ite_true] at hv
      rcases procVC_decs_cases _ _ _ _ hv with h | h
      · exact I.decs_spec x v (by simpa [L'] using h)
      · obtain ⟨-, -, h3⟩ := I.d_spec q j l 4 v h
        exact ⟨j, l, (I.lead_spec x j l hl).2, h3 (by norm_num)⟩

lemma inv_invokeElect (I : Inv C s) (x : P) (hE : Enabled C (.invokeElect x) s) (c : ℕ → P) :
    Inv C (eff c (.invokeElect x) s) := by
  obtain ⟨hx, hph, -⟩ := hE
  have hm := mono_eff c (.invokeElect x) s
  set L := s.loc x with hL
  set jx := L.view with hjx
  set s' := eff c (.invokeElect x) s with hs'
  have hloc : ∀ q, s'.loc q = if q = x then { L with ph := .electing } else s.loc q := by
    intro q; simp only [s', eff, Function.update_apply]; rfl
  have hpast : ∀ q j, Past (s'.loc q) j ↔ Past (s.loc q) j := by
    intro q j; rw [hloc]; split_ifs with hq
    · subst hq; simp only [Past]; rw [← hL, hph]; simp
    · rfl
  have hdq : ∀ q, (s'.loc q).d = (s.loc q).d := by
    intro q; rw [hloc]; split_ifs with hq
    · subst hq; rfl
    · rfl
  have hcor : s'.corrupt = s.corrupt := rfl
  have htok : s'.tok = s.tok := rfl
  have hcompl : ∀ j, completed C.Q s' j = completed C.Q s j := fun _ => rfl
  refine
    { card_corrupt := I.card_corrupt
      rev_zero := ?_
      tok_pb := fun p hp j k st v => by rw [hdq]; exact I.tok_pb p hp j k st v
      tok_skip := fun p hp j hj => by rw [hcompl]; exact I.tok_skip p hp j hj
      view_pos := fun p => ?_
      d_spec := fun p j k st v hv => ?_
      lead_spec := fun p i l hl => ?_
      lead_some := fun p i hi hp => ?_
      rcvd_spec := fun p j h hh hc => ?_
      exitR_sub := fun p j => ?_
      exitR_card := fun p j hj1 hj2 => ?_
      kv_spec := fun p j k v hv j0 l hj0 hl h hh hc v' hv' => ?_
      decs_spec := fun p v hv => ?_ }
  · have h1 := I.view_pos x
    simp only [s', eff]
    rw [ite_eq_right (by omega)]; exact I.rev_zero
  · rw [hloc]; split_ifs with hp
    · subst hp; exact I.view_pos p
    · exact I.view_pos p
  · rw [hdq] at hv
    obtain ⟨h1, h2, h3⟩ := I.d_spec p j k st v hv
    have hvw : (s'.loc p).view = (s.loc p).view := by
      rw [hloc]; split_ifs with hp
      · subst hp; rfl
      · rfl
    have hkv : (s'.loc p).kv = (s.loc p).kv := by
      rw [hloc]; split_ifs with hp
      · subst hp; rfl
      · rfl
    rw [hvw, hkv]
    refine ⟨h1, fun h => ?_, fun h => QC_mono hm.tok (h3 h)⟩
    obtain ⟨h4, h5⟩ := h2 h
    exact ⟨h4, h5.imp id (fun ⟨a, b, l, hl, hq⟩ => ⟨a, b, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩)⟩
  · rw [hpast]
    have hl' : (s.loc p).lead i = some l := by
      rw [hloc] at hl; split_ifs at hl with hp
      · subst hp; exact hl
      · exact hl
    obtain ⟨h1, h2⟩ := I.lead_spec p i l hl'
    exact ⟨h1, hm.rev _ _ h2⟩
  · rw [hpast] at hp
    rw [hloc]; split_ifs with hp'
    · subst hp'; exact I.lead_some p i hi hp
    · exact I.lead_some p i hi hp
  · rw [hpast, hdq]
    have hh' : h ∈ (s.loc p).rcvd j := by
      rw [hloc] at hh; split_ifs at hh with hp
      · subst hp; exact hh
      · exact hh
    have := I.rcvd_spec p j h hh' hc
    rw [hloc]; split_ifs with hp
    · subst hp; exact this
    · exact this
  · rw [hloc]; split_ifs with hp
    · subst hp; exact I.exitR_sub p j
    · exact I.exitR_sub p j
  · rw [hloc] at hj2 ⊢; split_ifs at hj2 ⊢ with hp
    · subst hp; exact I.exitR_card p j hj1 hj2
    · exact I.exitR_card p j hj1 hj2
  · rw [hdq] at hv'
    rw [hloc] at hv hl hh ⊢; split_ifs at hv hl hh ⊢ with hp
    · subst hp; exact I.kv_spec p j k v hv j0 l hj0 hl h hh hc v' hv'
    · exact I.kv_spec p j k v hv j0 l hj0 hl h hh hc v' hv'
  · have hv' : v ∈ (s.loc p).decs := by
      rw [hloc] at hv; split_ifs at hv with hp
      · subst hp; exact hv
      · exact hv
    obtain ⟨j, l, hl, hq⟩ := I.decs_spec p v hv'
    exact ⟨j, l, hm.rev _ _ hl, QC_mono hm.tok hq⟩

lemma inv_electReturn (I : Inv C s) (x : P) (hE : Enabled C (.electReturn x) s) (c : ℕ → P) :
    Inv C (eff c (.electReturn x) s) := by
  obtain ⟨hx, hph, hrev⟩ := hE
  obtain ⟨lx, hlx⟩ := Option.isSome_iff_exists.mp hrev
  set L := s.loc x with hL
  set jx := L.view with hjx
  set L' : Loc P V := { L with ph := .vc, lead := Function.update L.lead jx (s.rev jx) } with hL'
  have heff : eff c (.electReturn x) s = s.upd x L' := rfl
  rw [heff]
  -- leaders of earlier views are unchanged
  have hlead_old : ∀ i, Past L i → L'.lead i = L.lead i := by
    intro i hi
    have : i ≠ jx := by
      rcases hi with h | ⟨_, h⟩
      · omega
      · rw [hph] at h; exact absurd h (by decide)
    simp [L', this]
  have hnotpast : ¬ Past L jx := by
    rintro (h | ⟨_, h⟩)
    · omega
    · rw [hph] at h; exact absurd h (by decide)
  have hpast_x : ∀ i, Past L' i ↔ Past L i ∨ i = jx := by
    intro i; simp only [Past, L']
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | ⟨_, h⟩) | h)
      · exact Or.inl h
      · rw [hph] at h; exact absurd h (by decide)
      · exact Or.inr ⟨h, trivial⟩
  have hpast : ∀ q i, Past (s.loc q) i → Past ((s.upd x L').loc q) i := by
    intro q i hq; simp only [upd_loc]; split_ifs with h
    · subst h; exact (hpast_x i).mpr (Or.inl hq)
    · exact hq
  have hdq : ∀ q, ((s.upd x L').loc q).d = (s.loc q).d := by
    intro q; simp only [upd_loc]; split_ifs with h
    · subst h; rfl
    · rfl
  refine
    { card_corrupt := I.card_corrupt
      rev_zero := I.rev_zero
      tok_pb := fun p hp j k st v => by rw [hdq]; exact I.tok_pb p hp j k st v
      tok_skip := I.tok_skip
      view_pos := fun p => ?_
      d_spec := fun p j k st v hv => ?_
      lead_spec := fun p i l hl => ?_
      lead_some := fun p i hi hp => ?_
      rcvd_spec := fun p j h hh hc => ?_
      exitR_sub := fun p j => ?_
      exitR_card := fun p j hj1 hj2 => ?_
      kv_spec := fun p j k v hv j0 l hj0 hl h hh hc v' hv' => ?_
      decs_spec := fun p v hv => ?_ }
  · simp only [upd_loc]; split_ifs with hp
    · subst hp; exact I.view_pos p
    · exact I.view_pos p
  · rw [hdq] at hv
    have := I.d_spec p j k st v hv
    simp only [upd_loc, upd_rev]; split_ifs with hp
    · subst hp; exact this
    · exact this
  · simp only [upd_loc, upd_rev] at hl ⊢; split_ifs at hl ⊢ with hp
    · subst hp
      by_cases hi : i = jx
      · subst hi
        simp only [L', Function.update_self] at hl
        exact ⟨(hpast_x _).mpr (Or.inr rfl), hl⟩
      · have hl' : L.lead i = some l := by simpa [L', Function.update_apply, hi] using hl
        obtain ⟨h1, h2⟩ := I.lead_spec p i l hl'
        exact ⟨(hpast_x i).mpr (Or.inl h1), h2⟩
    · exact I.lead_spec p i l hl
  · simp only [upd_loc] at hp ⊢; split_ifs at hp ⊢ with hp'
    · subst hp'
      rcases (hpast_x i).mp hp with h | h
      · rw [hlead_old i h]; exact I.lead_some p i hi h
      · subst h; simp [L', hlx]
    · exact I.lead_some p i hi hp
  · rw [hdq]
    simp only [upd_corrupt] at hc
    have hh' : h ∈ (s.loc p).rcvd j := by
      simp only [upd_loc] at hh; split_ifs at hh with hp
      · subst hp; exact hh
      · exact hh
    obtain ⟨hP, l, hl, hv⟩ := I.rcvd_spec p j h hh' hc
    refine ⟨hpast h j hP, l, ?_, ?_⟩
    · simp only [upd_loc]; split_ifs with hp
      · subst hp
        rw [hlead_old j (I.lead_spec p j l hl).1]; exact hl
      · exact hl
    · simp only [upd_loc]; split_ifs with hp
      · subst hp; exact hv
      · exact hv
  · simp only [upd_loc]; split_ifs with hp
    · subst hp; exact I.exitR_sub p j
    · exact I.exitR_sub p j
  · simp only [upd_loc] at hj2 ⊢; split_ifs at hj2 ⊢ with hp
    · subst hp; exact I.exitR_card p j hj1 hj2
    · exact I.exitR_card p j hj1 hj2
  · rw [hdq] at hv'
    simp only [upd_loc] at hv hl hh ⊢; split_ifs at hv hl hh ⊢ with hp
    · subst hp
      have hj := (I.d_spec p j k 1 v hv).1
      rw [← hL] at hj
      have hlt : j0 < jx := by omega
      have hl' : L.lead j0 = some l := by
        rw [← hlead_old j0 (Or.inl hlt)]; exact hl
      exact I.kv_spec p j k v hv j0 l hj0 hl' h hh hc v' hv'
    · exact I.kv_spec p j k v hv j0 l hj0 hl h hh hc v' hv'
  · simp only [upd_loc, upd_rev] at hv ⊢; split_ifs at hv with hp
    · subst hp; exact I.decs_spec p v hv
    · exact I.decs_spec p v hv

lemma inv_exitView (I : Inv C s) (x : P) (hE : Enabled C (.exitView x) s) (c : ℕ → P) :
    Inv C (eff c (.exitView x) s) := by
  obtain ⟨hx, hph, hcard⟩ := hE
  have heff : eff c (.exitView x) s = s.upd x { s.loc x with
        view := (s.loc x).view + 1
        ph := .bc
        exitR := Function.update (s.loc x).exitR (s.loc x).view ((s.loc x).rcvd (s.loc x).view)
        prop := Function.update (s.loc x).prop ((s.loc x).view + 1) (s.loc x).key } := rfl
  rw [heff]
  generalize hL' : ({ s.loc x with
        view := (s.loc x).view + 1
        ph := .bc
        exitR := Function.update (s.loc x).exitR (s.loc x).view ((s.loc x).rcvd (s.loc x).view)
        prop := Function.update (s.loc x).prop ((s.loc x).view + 1) (s.loc x).key } : Loc P V) = L'
  have hview' : L'.view = (s.loc x).view + 1 := by rw [← hL']
  have hph' : L'.ph = .bc := by rw [← hL']
  have hlead' : L'.lead = (s.loc x).lead := by rw [← hL']
  have hd' : L'.d = (s.loc x).d := by rw [← hL']
  have hkv' : L'.kv = (s.loc x).kv := by rw [← hL']
  have hrcvd' : L'.rcvd = (s.loc x).rcvd := by rw [← hL']
  have hkey' : L'.key = (s.loc x).key := by rw [← hL']
  have hlock' : L'.lock = (s.loc x).lock := by rw [← hL']
  have hdecs' : L'.decs = (s.loc x).decs := by rw [← hL']
  have hexit' : L'.exitR = Function.update (s.loc x).exitR (s.loc x).view
      ((s.loc x).rcvd (s.loc x).view) := by rw [← hL']
  have hpast_x : ∀ i, Past L' i ↔ Past (s.loc x) i := by
    intro i; simp only [Past, hview', hph', hph]
    constructor
    · rintro (h | ⟨-, h⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, trivial⟩
      · exact absurd h (by decide)
    · rintro (h | ⟨h, -⟩)
      · left; omega
      · left; omega
  have hpast : ∀ q i, Past ((s.upd x L').loc q) i ↔ Past (s.loc q) i := by
    intro q i; simp only [upd_loc]; split_ifs with h
    · subst h; exact hpast_x i
    · rfl
  have hdq : ∀ q, ((s.upd x L').loc q).d = (s.loc q).d := by
    intro q; simp only [upd_loc]; split_ifs with h
    · subst h; exact hd'
    · rfl
  have hexit_old : ∀ j, j < (s.loc x).view → L'.exitR j = (s.loc x).exitR j := by
    intro j hj; rw [hexit']; simp [show j ≠ (s.loc x).view by omega]
  refine
    { card_corrupt := I.card_corrupt
      rev_zero := I.rev_zero
      tok_pb := fun p hp j k st v => by rw [hdq]; exact I.tok_pb p hp j k st v
      tok_skip := I.tok_skip
      view_pos := fun p => ?_
      d_spec := fun p j k st v hv => ?_
      lead_spec := fun p i l hl => ?_
      lead_some := fun p i hi hp => ?_
      rcvd_spec := fun p j h hh hc => ?_
      exitR_sub := fun p j => ?_
      exitR_card := fun p j hj1 hj2 => ?_
      kv_spec := fun p j k v hv j0 l hj0 hl h hh hc v' hv' => ?_
      decs_spec := fun p v hv => ?_ }
  · simp only [upd_loc]; split_ifs with hp
    · rw [hview']; omega
    · exact I.view_pos p
  · rw [hdq] at hv
    obtain ⟨h1, h2, h3⟩ := I.d_spec p j k st v hv
    simp only [upd_loc, upd_rev]; split_ifs with hp
    · subst hp; rw [hview', hkv']; exact ⟨by omega, h2, h3⟩
    · exact ⟨h1, h2, h3⟩
  · rw [hpast]
    simp only [upd_loc, upd_rev] at hl ⊢; split_ifs at hl with hp
    · subst hp; rw [hlead'] at hl; exact I.lead_spec p i l hl
    · exact I.lead_spec p i l hl
  · rw [hpast] at hp
    simp only [upd_loc]; split_ifs with hp'
    · subst hp'; rw [hlead']; exact I.lead_some p i hi hp
    · exact I.lead_some p i hi hp
  · rw [hpast, hdq]
    simp only [upd_corrupt] at hc
    simp only [upd_loc] at hh ⊢; split_ifs at hh ⊢ with hp
    · subst hp; rw [hrcvd'] at hh; rw [hlead', hkey', hlock', hdecs']
      exact I.rcvd_spec p j h hh hc
    · exact I.rcvd_spec p j h hh hc
  · simp only [upd_loc]; split_ifs with hp
    · subst hp
      rw [hexit', hrcvd', Function.update_apply]; split_ifs with hj
      · subst hj; exact subset_rfl
      · exact I.exitR_sub p j
    · exact I.exitR_sub p j
  · simp only [upd_loc] at hj2 ⊢; split_ifs at hj2 ⊢ with hp
    · subst hp
      rw [hview'] at hj2
      by_cases hj : j = (s.loc p).view
      · rw [hexit', hj, Function.update_self]; exact hcard
      · rw [hexit_old j (by omega)]; exact I.exitR_card p j hj1 (by omega)
    · exact I.exitR_card p j hj1 hj2
  · rw [hdq] at hv'
    simp only [upd_loc] at hv hl hh ⊢; split_ifs at hv hl hh ⊢ with hp
    · subst hp
      rw [hd'] at hv; rw [hlead'] at hl; rw [hkv']
      have hj := (I.d_spec p j k 1 v hv).1
      rw [hexit_old j0 (by omega)] at hh
      exact I.kv_spec p j k v hv j0 l hj0 hl h hh hc v' hv'
    · exact I.kv_spec p j k v hv j0 l hj0 hl h hh hc v' hv'
  · simp only [upd_loc, upd_rev] at hv ⊢; split_ifs at hv with hp
    · subst hp; rw [hdecs'] at hv; exact I.decs_spec p v hv
    · exact I.decs_spec p v hv

lemma inv_eff (I : Inv C s) (a : Act P V) (hE : Enabled C a s) (c : ℕ → P) :
    Inv C (eff c a s) := by
  cases a with
  | deliver p k st v r => exact inv_deliver I p k st v r hE c
  | skipShare p j => exact inv_skipShare I p j hE c
  | invokeElect p => exact inv_invokeElect I p hE c
  | electReturn p => exact inv_electReturn I p hE c
  | recvVC p q j b => exact inv_recvVC I p q j b hE c
  | recvQC p j st v => exact inv_recvQC I p j st v hE c
  | exitView p => exact inv_exitView I p hE c
  | corrupt p => exact inv_corrupt I p hE c
  | byzSign p st => exact inv_byzSign I p st hE c

end preserve

/-- Every reachable state satisfies the invariant. -/
theorem Reach.inv {C : Cfg P V} {s : Glob P V} (h : Reach C s) : Inv C s := by
  induction h with
  | init => exact inv_init C
  | step c a _ ih =>
    unfold VABA.step; split_ifs with hE
    · exact inv_eff ih a hE c
    · exact ih

end VABA
