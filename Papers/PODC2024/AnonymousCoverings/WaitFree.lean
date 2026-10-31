import Papers.PODC2024.AnonymousCoverings.Snapshot

/-!
# Wait-freedom of the snapshot algorithm (Section 5.3.3)

`snapshot_live_false`: in every execution of Figure 3 (any termination level `L`, any number of
registers), no processor takes infinitely many non-idle steps. Hence (`snapshot_waitFree`) every
processor that is scheduled infinitely often terminates.

Proof (the paper's, made precise): suppose some processor is live. After stabilization (`exists_gst`)
the live processors whose stable view `M` is minimal read only from each other
(`readsOnlyFrom_minimal`), so every value they read is `(M, ℓ)` written by one of them; hence they
never reset their level and, by induction on `k`, eventually all of them have level `≥ k`. With
`k = L` they stop, contradicting liveness. (The paper invokes Theorem 4.8; only the existence of a
minimal stable view is needed.)
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R V : Type*} [Fintype P] [DecidableEq P] [DecidableEq R] [Fintype R] [Nonempty R]
  [DecidableEq V]

namespace Exec

variable {L : ℕ} {input : P → V} {e : Exec (P := P) (snapshot (R := R) (V := V) L)}

/-- The view hypotheses hold for Figure 3 (view = `SnapD.view`, register view = first
component). -/
theorem snap_viewSpec (he : e.cfg 0 = snapCfg input) :
    e.ViewSpec SnapD.view Prod.fst (univ.image input) := by
  set B := univ.image input
  have hinv : ∀ t, (∀ p, (e.loc t p).d.view ⊆ B ∧ ∀ r, ((e.loc t p).d.got r).1 ⊆ B) ∧
      (∀ r, (e.reg t r).val.1 ⊆ B) := by
    intro t
    induction t with
    | zero =>
      simp only [loc, reg, he, snapCfg, initCfg, snapInit]
      exact ⟨fun p => ⟨by simp [B], fun r => by simp⟩, fun r => by simp⟩
    | succ t ih =>
      refine ⟨fun p => ⟨?_, fun r => ?_⟩, fun r => ?_⟩
      · rcases e.snap_view_level_succ t p with ⟨h, -⟩ | ⟨-, r, -, S, -, -, -, h⟩
        · rw [h]; exact (ih.1 p).1
        · rw [h]
          simp only [SnapD.finish, snapshot, SnapD.unionRead]
          refine union_subset (ih.1 p).1 (Finset.sup_le fun r' _ => ?_)
          by_cases hrr : r' = r
          · subst hrr; simp [ih.2 r']
          · simp [Function.update_of_ne hrr, (ih.1 p).2 r']
      · rcases e.snap_got_succ t p r with h | ⟨-, h⟩
        · rw [h]; exact (ih.1 p).2 r
        · rw [h]; exact ih.2 r
      · by_cases hw : ∃ q, e.act t = .write q r
        · obtain ⟨q, hq⟩ := hw
          rw [(e.write_spec hq).2.2.2.1]; exact (ih.1 q).1
        · push Not at hw
          rw [e.reg_succ_of_not_write hw]; exact ih.2 r
  refine ⟨fun t p => e.snap_view_mono t p, fun t p => ((hinv t).1 p).1, fun d => rfl,
    fun t a r hl hr => ?_, fun r => by simp [reg, he, snapCfg, initCfg]⟩
  obtain ⟨S, hS, hrS, hpost⟩ := e.read_spec hr
  obtain ⟨c, hc, ⟨⟨rc, hrc⟩, hdone⟩, hnc⟩ := e.exists_completes_of_scanning hl _ t S hS le_rfl
  refine ⟨c + 1, by omega, ?_⟩
  obtain ⟨Sc, hSc, hrSc, hpostc⟩ := e.read_spec hrc
  have hu : insert rc Sc = univ := by
    by_contra hu
    rw [hpostc] at hdone; simp [hu] at hdone
  rw [hpostc]
  simp only [hu, ↓reduceIte, snapshot, SnapD.finish, SnapD.unionRead]
  refine subset_union_right.trans' (le_sup (f := fun r' => ((Function.update (e.loc c a).d.got rc
    (e.reg c rc).val) r').1) (mem_univ r) |>.trans' ?_)
  rcases Nat.eq_or_lt_of_le hc with heq | hlt
  · subst heq
    rw [hr] at hrc; cases hrc
    simp
  · obtain ⟨S', hS', hrS', hgot⟩ := e.snap_got_track hr (c := c)
      (fun t' h1 h2 => hnc t' (by omega) h2) c hlt le_rfl
    rw [hSc] at hS'; cases hS'
    have hne : r ≠ rc := fun h => hrSc (h ▸ hrS')
    simp [Function.update_of_ne hne, hgot]

omit [Fintype P] in
/-- The scan completed at `t` was started by a write of the same processor, and no scan of it
completed in between. -/
theorem snap_exists_scan_start (he : e.cfg 0 = snapCfg input) {t : ℕ} {a : P}
    (hc : e.Completes t a) :
    ∃ s < t, (∃ r, e.act s = .write a r) ∧ ∀ u, s < u → u ≤ t → (e.loc u a).scan ≠ none := by
  classical
  obtain ⟨⟨r, hr⟩, -⟩ := hc
  obtain ⟨S, hS, -⟩ := e.read_spec hr
  have h0 : (e.loc 0 a).scan = none := by simp [loc, he, snapCfg, initCfg]
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := Nat.exists_last_of_le (p := fun u => (e.loc u a).scan = none)
    (Nat.zero_le t) h0
  have hst : s < t := by
    rcases Nat.lt_or_ge s t with h | h
    · exact h
    · have : s = t := by omega
      rw [this, hS] at hs3; exact absurd hs3 (by simp)
  refine ⟨s, hst, ?_, fun u h1 h2 => hs4 u h1 h2⟩
  have hs5 : (e.loc (s + 1) a).scan ≠ none := hs4 (s + 1) (by omega) (by omega)
  obtain ⟨r', hr' | hr'⟩ := e.moves_of_scan_change (by rw [hs3]; exact hs5)
  · exact ⟨r', hr'⟩
  · obtain ⟨S', hS', -⟩ := e.read_spec hr'
    rw [hs3] at hS'; exact absurd hS' (by simp)

omit [Fintype P] in
/-- The level changes only at the end of a scan. -/
theorem snap_level_succ (t : ℕ) (a : P) :
    (e.loc (t + 1) a).d.level = (e.loc t a).d.level ∨ e.Completes t a := by
  rcases e.snap_view_level_succ t a with ⟨-, h⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

end Exec

open Exec in
/-- **Wait-freedom (Section 5.3.3).** In every execution of the snapshot algorithm, no processor
takes infinitely many non-idle steps. -/
theorem snapshot_live_false {L : ℕ} {input : P → V}
    (e : Exec (P := P) (snapshot (R := R) (V := V) L)) (he : e.cfg 0 = snapCfg input) (p : P) :
    ¬ e.Live p := by
  classical
  intro hp
  have hv := snap_viewSpec he
  obtain ⟨T₀, hst, -, hreg⟩ := exists_gst hv ⟨p, hp⟩
  set stab : P → Finset V := fun q => (e.loc T₀ q).d.view with hstab
  set Lv := univ.filter fun q => e.Live q
  have hL : Lv.Nonempty := ⟨p, by simp [Lv, hp]⟩
  obtain ⟨p₁, hp₁L, hp₁min⟩ := exists_min_image Lv (fun q => (stab q).card) hL
  have hp₁ : e.Live p₁ := by simpa [Lv] using hp₁L
  have min₁ : ∀ x, e.Live x → stab x ⊆ stab p₁ → stab x = stab p₁ := fun x hx hsub =>
    eq_of_subset_of_card_le hsub (hp₁min x (by simp [Lv, hx]))
  have hclosed := readsOnlyFrom_minimal hv hst hreg (stab p₁) min₁
  set S₁ := univ.filter fun q => e.Live q ∧ (e.loc T₀ q).d.view = stab p₁ with hS₁
  have hmem : ∀ q, q ∈ S₁ ↔ e.Live q ∧ stab q = stab p₁ := fun q => by simp [S₁, stab]
  -- levels of the members of `S₁` grow without bound
  have key : ∀ k, ∃ T ≥ T₀, ∀ t ≥ T, ∀ a ∈ S₁, k ≤ (e.loc t a).d.level := by
    intro k
    induction k with
    | zero => exact ⟨T₀, le_rfl, fun _ _ _ _ => Nat.zero_le _⟩
    | succ k ih =>
      obtain ⟨Tk, hTk0, hTk⟩ := ih
      -- every register is rewritten after `Tk`
      obtain ⟨T', hT'k, hT'⟩ := Nat.eventually_forall_of_finite (p := fun r m =>
        ∃ w, Tk ≤ w ∧ w < m ∧ ∃ q, e.act w = .write q r) (fun r => by
          obtain ⟨w, hw, hw'⟩ := e.exists_write_reg_of_live hp₁ r Tk
          exact ⟨w + 1, fun m hm => ⟨w, hw, by omega, p₁, hw'⟩⟩) Tk
      -- a scan of a member of `S₁` started after `T'` ends with level `≥ k + 1`
      have scan_up : ∀ a ∈ S₁, ∀ s c r₀, T' ≤ s → e.act s = .write a r₀ → e.Completes c a →
          s < c → (∀ u, s < u → u ≤ c → (e.loc u a).scan ≠ none) →
          k + 1 ≤ (e.loc (c + 1) a).d.level := by
        intro a ha s c r₀ hs hw hc hsc hnc
        obtain ⟨g, hg, d, hd, hdv, -, hdg⟩ := e.snap_scan_result hw hc hsc hnc
        have hva : d.view = stab p₁ := by
          rw [hdv, hst a s (by omega)]; exact ((hmem a).1 ha).2
        have hread : ∀ r, (d.got r).1 = stab p₁ ∧ k ≤ (d.got r).2 := by
          intro r
          obtain ⟨h1, h2, h3⟩ := hg r
          obtain ⟨b, hb, hwb⟩ := hclosed (g r) (by omega) a ha r h3
          obtain ⟨q, hq, hwq, hvq⟩ := hreg (g r) (by omega) r
          rw [hwb] at hwq; cases hwq
          obtain ⟨w, hw1, hw2, hw3, hw4⟩ := e.exists_last_write hwb (hv.h0 r)
          have hwT : Tk ≤ w := by
            by_contra hlt
            obtain ⟨w', hw'1, hw'2, q', hq'⟩ := hT' (g r) (by omega) r
            exact hw4 w' (by omega) hw'2 q' hq'
          rw [hdg r]
          refine ⟨by rw [hvq]; exact ((hmem b).1 hb).2, ?_⟩
          rw [← hw3, (e.write_spec hw2).2.2.2.1]
          exact hTk w hwT b hb
        rw [hd]
        simp only [SnapD.finish]
        have hall : ∀ r, (d.got r).1 = d.view := fun r => (hread r).1.trans hva.symm
        simp only [hall, implies_true, ↓reduceIte]
        simp only [SnapD.minLevel]
        have := le_inf' (s := univ) univ_nonempty (f := fun r => (d.got r).2) (fun r _ => (hread r).2)
        omega
      -- each member eventually stays at level `≥ k + 1`
      have each : ∀ a, ∃ T, ∀ t ≥ T, a ∈ S₁ → k + 1 ≤ (e.loc t a).d.level := by
        intro a
        by_cases ha : a ∈ S₁
        · have hla := ((hmem a).1 ha).1
          obtain ⟨s, hs, r₀, hr₀⟩ := e.exists_write_of_live hla T'
          obtain ⟨c, hc, hcc, hnc⟩ := e.exists_completes_after_write hla hr₀
          refine ⟨c + 1, fun t ht _ => ?_⟩
          induction t, ht using Nat.le_induction with
          | base => exact scan_up a ha s c r₀ hs hr₀ hcc hc hnc
          | succ t ht ih =>
            rcases e.snap_level_succ t a with h | h
            · rw [h]; exact ih
            · obtain ⟨s', hs', ⟨r', hr'⟩, hnc'⟩ := e.snap_exists_scan_start he h
              have hcs : c < s' := by
                by_contra hle
                exact hnc' (c + 1) (by omega) (by omega) hcc.2
              exact scan_up a ha s' t r' (by omega) hr' h hs' hnc'
        · exact ⟨0, fun _ _ h => absurd h ha⟩
      obtain ⟨T, hT, hT'⟩ := Nat.eventually_forall_of_finite each T'
      exact ⟨T, by omega, fun t ht a ha => hT' t ht a ha⟩
  obtain ⟨T, -, hT⟩ := key L
  obtain ⟨w, hw, r, hr⟩ := e.exists_write_of_live hp₁ T
  have hp₁S : p₁ ∈ S₁ := (hmem p₁).2 ⟨hp₁, rfl⟩
  exact (e.write_spec hr).2.2.1 (hT w hw p₁ hp₁S)

/-- **Wait-freedom (Section 5.3.3).** Every processor that is scheduled infinitely often
eventually terminates: it reaches level `≥ L` at the write label. -/
theorem snapshot_waitFree {L : ℕ} {input : P → V}
    (e : Exec (P := P) (snapshot (R := R) (V := V) L)) (he : e.cfg 0 = snapCfg input) (p : P)
    (hsched : ∀ T, ∃ t ≥ T, (e.act t).proc = p) :
    ∃ t, (e.loc t p).scan = none ∧ L ≤ (e.loc t p).d.level := by
  have hnl := snapshot_live_false e he p
  unfold Exec.Live at hnl
  push Not at hnl
  obtain ⟨T, hT⟩ := hnl
  obtain ⟨t, ht, hp⟩ := hsched T
  have hs := e.step t
  generalize ha : e.act t = a at hs hp
  cases a with
  | write q r => simp only [Act.proc] at hp; subst hp; exact absurd ha (hT t ht r).1
  | read q r => simp only [Act.proc] at hp; subst hp; exact absurd ha (hT t ht r).2
  | idle q => simp only [Act.proc] at hp; subst hp; exact ⟨t, hs.1, hs.2.1⟩

end Podc.AnonymousCoverings
