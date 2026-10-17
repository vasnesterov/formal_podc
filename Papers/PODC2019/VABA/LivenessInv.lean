import Papers.PODC2019.VABA.KeyInv

/-!
# VABA: auxiliary facts for the liveness proof

* Monotonicity of a single step: the position (view, phase) of a party never decreases,
  deliveries and received view-change messages are never forgotten, proposals of started views
  never change.
* `LInv`: revealed coins are backed by skip certificates, an electing party's coin is revealed,
  and a delivery of an honest proposer's message is that proposer's proposal.
-/

namespace VABA

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V} {s : Glob P V}

/-- Rank of a phase inside a view. -/
def Phase.rk : Phase → ℕ
  | .bc => 0
  | .electing => 1
  | .vc => 2

/-! ### Monotonicity of one step -/

section mono

/-- The position (view, phase) of every party never decreases. -/
lemma eff_pos_mono (c : ℕ → P) (a : Act P V) (hE : Enabled C a s) (p : P) :
    (s.loc p).view < ((eff c a s).loc p).view ∨
      ((s.loc p).view = ((eff c a s).loc p).view ∧
        (s.loc p).ph.rk ≤ ((eff c a s).loc p).ph.rk) := by
  by_cases hp : p = a.actor
  · cases a with
    | deliver x k st v r =>
      simp only [Act.actor] at hp; subst hp
      right; simp [eff]
    | skipShare => right; simp [eff]
    | invokeElect x =>
      simp only [Act.actor] at hp; subst hp
      right; simp [eff, hE.2.1, Phase.rk]
    | electReturn x =>
      simp only [Act.actor] at hp; subst hp
      right; simp [eff, hE.2.1, Phase.rk]
    | recvVC x q j b =>
      simp only [Act.actor] at hp; subst hp
      right; simp only [eff]; split
      · simp only [upd_loc, ite_true]; split_ifs <;> simp
      · simp
    | recvQC x =>
      simp only [Act.actor] at hp; subst hp
      right; simp [eff]
    | exitView x =>
      simp only [Act.actor] at hp; subst hp
      left; simp [eff]
    | corrupt => right; simp [eff]
    | byzSign => right; simp [eff]
  · rw [eff_loc_ne c a s p hp]; right; exact ⟨rfl, le_rfl⟩

/-- Deliveries are never forgotten. -/
lemma eff_d_mono (c : ℕ → P) (a : Act P V) (hE : Enabled C a s) {p : P} {i : ℕ} {k : P}
    {st : ℕ} {w : V} (h : (s.loc p).d i k st = some w) :
    ((eff c a s).loc p).d i k st = some w := by
  by_cases hp : p = a.actor
  · cases a with
    | deliver x k' st' v r =>
      simp only [Act.actor] at hp; subst hp
      obtain ⟨-, -, -, -, hnone, -⟩ := hE
      simp only [eff, upd_loc, ite_true]
      split_ifs with hc
      · obtain ⟨rfl, rfl, rfl⟩ := hc; rw [hnone] at h; simp at h
      · exact h
    | skipShare => exact h
    | invokeElect x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | electReturn x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | recvVC x q j b =>
      simp only [Act.actor] at hp; subst hp
      simp only [eff]; split
      · simp only [upd_loc, ite_true]; split_ifs <;> simpa using h
      · exact h
    | recvQC x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | exitView x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | corrupt => exact h
    | byzSign => exact h
  · rw [eff_loc_ne c a s p hp]; exact h

omit [Fintype P] in
/-- Received view-change messages are never forgotten. -/
lemma eff_rcvd_mono (c : ℕ → P) (a : Act P V) {p q : P} {i : ℕ}
    (h : q ∈ (s.loc p).rcvd i) : q ∈ ((eff c a s).loc p).rcvd i := by
  by_cases hp : p = a.actor
  · cases a with
    | deliver x k' st' v r => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | skipShare => exact h
    | invokeElect x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | electReturn x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | recvVC x q' j b =>
      simp only [Act.actor] at hp; subst hp
      simp only [eff]; split
      · have : q ∈ Function.update (s.loc p).rcvd j (insert q' ((s.loc p).rcvd j)) i := by
          rw [Function.update_apply]; split_ifs with hi
          · subst hi; exact mem_insert_of_mem h
          · exact h
        simp only [upd_loc, ite_true]; split_ifs <;> simpa using this
      · exact h
    | recvQC x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | exitView x => simp only [Act.actor] at hp; subst hp; simpa [eff] using h
    | corrupt => exact h
    | byzSign => exact h
  · rw [eff_loc_ne c a s p hp]; exact h

omit [Fintype P] in
/-- The proposal of a started view never changes. -/
lemma eff_prop_stable (c : ℕ → P) (a : Act P V) {q : P} {i : ℕ} (hi : i ≤ (s.loc q).view) :
    ((eff c a s).loc q).prop i = (s.loc q).prop i := by
  by_cases hp : q = a.actor
  · cases a with
    | deliver x k' st' v r => simp only [Act.actor] at hp; subst hp; simp [eff]
    | skipShare => rfl
    | invokeElect x => simp only [Act.actor] at hp; subst hp; simp [eff]
    | electReturn x => simp only [Act.actor] at hp; subst hp; simp [eff]
    | recvVC x q' j b =>
      simp only [Act.actor] at hp; subst hp
      simp only [eff]; split
      · simp only [upd_loc, ite_true]; split_ifs <;> simp
      · rfl
    | recvQC x => simp only [Act.actor] at hp; subst hp; simp [eff]
    | exitView x =>
      simp only [Act.actor] at hp; subst hp
      have : i ≠ (s.loc q).view + 1 := by omega
      simp [eff, Function.update_of_ne this]
    | corrupt => rfl
    | byzSign => rfl
  · rw [eff_loc_ne c a s q hp]

/-- A new delivery is a message that may have been sent. -/
lemma eff_d_new (c : ℕ → P) (a : Act P V) (hE : Enabled C a s) {p : P} {i : ℕ} {k : P}
    {st : ℕ} {w : V} (h : ((eff c a s).loc p).d i k st = some w) :
    (s.loc p).d i k st = some w ∨
      (k ∈ s.corrupt ∨ (i ≤ (s.loc k).view ∧ w = ((s.loc k).prop i).2)) := by
  by_cases hp : p = a.actor
  · cases a with
    | deliver x k' st' v r =>
      simp only [Act.actor] at hp; subst hp
      obtain ⟨-, -, -, -, -, -, hsent⟩ := hE
      simp only [eff, upd_loc, ite_true] at h
      split_ifs at h with hc
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        cases h
        right
        rcases hsent with h1 | ⟨h1, h2, -⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2⟩
      · exact Or.inl h
    | skipShare => exact Or.inl h
    | invokeElect x => simp only [Act.actor] at hp; subst hp; left; simpa [eff] using h
    | electReturn x => simp only [Act.actor] at hp; subst hp; left; simpa [eff] using h
    | recvVC x q j b =>
      simp only [Act.actor] at hp; subst hp
      left; simp only [eff] at h; split at h
      · simp only [upd_loc, ite_true] at h; split_ifs at h <;> simpa using h
      · exact h
    | recvQC x => simp only [Act.actor] at hp; subst hp; left; simpa [eff] using h
    | exitView x => simp only [Act.actor] at hp; subst hp; left; simpa [eff] using h
    | corrupt => exact Or.inl h
    | byzSign => exact Or.inl h
  · rw [eff_loc_ne c a s p hp] at h; exact Or.inl h

/-- A coin is revealed only by `invokeElect`, whose guard has the skip certificate. -/
lemma eff_rev_new (c : ℕ → P) (a : Act P V) (hE : Enabled C a s) {i : ℕ}
    (h : (eff c a s).rev i ≠ none) : s.rev i ≠ none ∨ QC C.Q s (.skip i) := by
  cases a with
  | invokeElect x =>
    simp only [eff] at h
    split_ifs at h with hi
    · right; rw [hi.1]; exact hE.2.2
    · exact Or.inl h
  | recvVC x q j b =>
    left; simp only [eff] at h; split at h
    · simpa using h
    · exact h
  | _ => left; simpa [eff] using h

end mono

/-! ### The liveness invariant -/

/-- Auxiliary invariant for liveness. -/
structure LInv (C : Cfg P V) (s : Glob P V) : Prop where
  /-- a revealed coin is backed by a skip certificate -/
  rev_qc : ∀ i, s.rev i ≠ none → QC C.Q s (.skip i)
  /-- the coin of the view of an electing party is revealed -/
  electing_rev : ∀ p, (s.loc p).ph = .electing → s.rev (s.loc p).view ≠ none
  /-- a delivered message of an honest proposer is its proposal -/
  d_prop : ∀ p i q st w, q ∉ s.corrupt → (s.loc p).d i q st = some w →
    i ≤ (s.loc q).view ∧ w = ((s.loc q).prop i).2

omit [DecidableEq P] in
lemma linv_init (C : Cfg P V) : LInv C (init C) where
  rev_qc := by simp [init]
  electing_rev := by simp [init]
  d_prop := by simp [init]

lemma linv_eff (L : LInv C s) (c : ℕ → P) (a : Act P V) (hE : Enabled C a s) :
    LInv C (eff c a s) := by
  have hm := mono_eff c a s
  refine ⟨fun i hi => ?_, fun p hp => ?_, fun p i q st w hq hw => ?_⟩
  · rcases eff_rev_new c a hE hi with h | h
    · exact QC_mono hm.tok (L.rev_qc i h)
    · exact QC_mono hm.tok h
  · have hold : ∀ i, s.rev i ≠ none → (eff c a s).rev i ≠ none := by
      intro i h
      rcases hx : s.rev i with _ | l
      · exact absurd hx h
      · rw [hm.rev i l hx]; simp
    by_cases hpa : p = a.actor
    · cases a with
      | invokeElect x =>
        simp only [Act.actor] at hpa; subst hpa
        simp only [eff, Function.update_self]
        split_ifs with hc
        · simp
        · intro h0; exact hc ⟨trivial, h0⟩
      | electReturn x =>
        simp only [Act.actor] at hpa; subst hpa
        simp [eff] at hp
      | exitView x =>
        simp only [Act.actor] at hpa; subst hpa
        simp [eff] at hp
      | deliver x k st v r =>
        simp only [Act.actor] at hpa; subst hpa
        simp only [eff, upd_loc, ite_true] at hp ⊢
        exact hold _ (L.electing_rev p hp)
      | recvQC x j st v =>
        simp only [Act.actor] at hpa; subst hpa
        simp only [eff, upd_loc, ite_true, proc_ph] at hp ⊢
        rw [proc_view]
        exact hold _ (L.electing_rev p hp)
      | recvVC x q j b =>
        simp only [Act.actor] at hpa; subst hpa
        have hvp : ((eff c (.recvVC p q j b) s).loc p).view = (s.loc p).view ∧
            ((eff c (.recvVC p q j b) s).loc p).ph = (s.loc p).ph := by
          simp only [eff]; split
          · simp only [upd_loc, ite_true]; split_ifs <;> simp
          · simp
        rw [hvp.1]; rw [hvp.2] at hp
        exact hold _ (L.electing_rev p hp)
      | skipShare x j => exact hold _ (L.electing_rev p hp)
      | corrupt x => exact hold _ (L.electing_rev p hp)
      | byzSign x st => exact hold _ (L.electing_rev p hp)
    · rw [eff_loc_ne c a s p hpa] at hp ⊢
      exact hold _ (L.electing_rev p hp)
  · have hq' : q ∉ s.corrupt := fun h => hq (hm.corrupt h)
    have hfin : i ≤ (s.loc q).view → w = ((s.loc q).prop i).2 →
        i ≤ ((eff c a s).loc q).view ∧ w = (((eff c a s).loc q).prop i).2 := by
      intro h1 h2
      refine ⟨?_, by rw [eff_prop_stable c a h1]; exact h2⟩
      rcases eff_pos_mono c a hE q with h | ⟨h, -⟩ <;> omega
    rcases eff_d_new c a hE hw with h | h | h
    · exact hfin (L.d_prop p i q st w hq' h).1 (L.d_prop p i q st w hq' h).2
    · exact absurd h hq'
    · exact hfin h.1 h.2

/-- `LInv` holds in every reachable state. -/
theorem Reach.linv {s : Glob P V} (h : Reach C s) : LInv C s := by
  induction h with
  | init => exact linv_init C
  | @step s c a hR ih =>
    unfold VABA.step; split_ifs with hE
    · exact linv_eff ih c a hE
    · exact ih

end VABA
