import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Compose

/-!
# Correctness of `SyncBA` (Theorems B.13 (rounds) and B.14)

`syncBA_correct`: against every authenticated static Byzantine adversary with `f ≤ t < n/2`
faults, `SyncBA` solves Byzantine agreement (termination, strong unanimity, agreement), and every
honest party has decided within `11(2f+1)` rounds if `f + k ≤ n` (i.e. `f ≤ ⌊(n-t-1)/2⌋`), and
within `11n + 3 + R_fb` rounds otherwise. The fallback `Afb` is a black box (`Fallback`).
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {Mf Sf : Type}
  {Afb : Protocol (Fin n) Bool Mf Bool} {Af : Auth (Fin n) Mf Sf}

-- CSLib candidate (message counting in the lock-step model)
/-- Honest messages of `p` in round `r` of a run (to parties other than itself). -/
noncomputable def sendsAt {I M O : Type} (alg : Protocol (Fin n) I M O) (s : Scenario (Fin n) I M)
    (r : ℕ) (p : Fin n) : ℕ :=
  (univ.filter fun q => q ≠ p ∧ (alg.send p (s.input p) (hist ⊤ alg s r p) q).isSome).card

/-- The black-box fallback protocol (Momose–Ren in the paper): an unforging authenticated
Byzantine agreement protocol for `t` faults in which honest parties decide within `Rfb` rounds,
and in which every honest party sends at most `mfb` messages in total, whatever the other parties
do (Theorem B.15: "even if not all honest parties join"). -/
structure Fallback (Afb : Protocol (Fin n) Bool Mf Bool) (Af : Auth (Fin n) Mf Sf) (t Rfb mfb : ℕ) :
    Prop where
  unforging : Afb.Unforging Af
  solves : SolvesAuthWithin ⊤ Afb Af (atMost t) noPre BA Rfb
  msgs : ∀ (s : Scenario (Fin n) Bool Mf) (p : Fin n), p ∉ s.byz →
    ∀ T, ∑ r ∈ range T, sendsAt Afb s r p ≤ mfb

lemma card_byzF (s : Scenario (Fin n) Bool (Msg n)) : (byzF s).card = s.byz.ncard := by
  classical
  have : byzF s = s.byz.toFinset := by ext q; simp [byzF]
  rw [this, Set.ncard_eq_toFinset_card']

lemma authValid_seqP {sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)}
    (hV : sc.AuthValid (G n) (syncBA π Afb) (Auth.seq auth Af)) :
    sc.AuthValid (G n) (seqP π Afb) (Auth.seq auth Af) := by
  intro r b q m hb hq hadj hm τ hτ
  rcases hV r b q m hb hq hadj hm τ hτ with h | h
  · exact Or.inl h
  · right
    obtain ⟨r', hr', p, hp, q', hadj', m', hm', hτ'⟩ := h
    exact ⟨r', hr', p, hp, q', hadj', m', by rw [← hist_syncBA]; exact hm', hτ'⟩

lemma good_scA {sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)} (hres : 2 * π.t < n)
    (hZ : sc.byz.ncard ≤ π.t) (hrel : sc.Reliable)
    (hV : sc.AuthValid (G n) (syncBA π Afb) (Auth.seq auth Af)) : Good π (scA sc) where
  rel := hrel.seqFst (R0 n)
  auth := (authValid_seqP hV).seqFst (G n) (stageA π) (R0 n) toB (stageB Afb)
  res := hres
  faults := by rw [card_byzF]; exact hZ

/-- The round bound of `SyncBA`: `11(2f+1)` if `f + k ≤ n`, else `11n + 3 + Rfb`. -/
def roundBound (π : Params n) (f Rfb : ℕ) : ℕ :=
  if f + π.k ≤ n then 11 * (2 * f + 1) else R0 n + Rfb

/-- **Correctness of `SyncBA`** (Theorems B.13 (rounds) and B.14 (agreement, validity)). -/
theorem syncBA_correct {Rfb mfb : ℕ} (hres : 2 * π.t < n) (hfb : Fallback Afb Af π.t Rfb mfb)
    (sc : Scenario (Fin n) Bool (Msg n ⊕ Mf)) (hZ : sc.byz.ncard ≤ π.t) (hrel : sc.Reliable)
    (hV : sc.AuthValid (G n) (syncBA π Afb) (Auth.seq auth Af)) :
    BA sc.input sc.honest (Decides (G n) (syncBA π Afb) sc) ∧
      TerminatesBy (G n) (syncBA π Afb) sc (roundBound π sc.byz.ncard Rfb) := by
  classical
  have hg := good_scA hres hZ hrel hV
  set s₁ := scA sc
  have hfeq : (byzF s₁).card = sc.byz.ncard := card_byzF s₁
  -- the honest decisions
  -- (I) someone honest has a commit at the end of the views
  by_cases hI : ∃ p, p ∉ sc.byz ∧ (S π s₁ (Rh n) p).commit.isSome
  · obtain ⟨p₀, hp₀, hc₀⟩ := hI
    obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.1 hc₀
    have hall : ∀ q, q ∉ sc.byz → ∃ c, (S π s₁ (R0 n) q).commit = some c := fun q hq =>
      Option.isSome_iff_exists.1
        (commit_mono_isSome hg (by unfold R0 Rh; omega) (commit_spread hg hp₀ hc₀ q hq))
    have hdec : ∀ q, q ∉ sc.byz → ∃ c, (S π s₁ (R0 n) q).commit = some c ∧
        Decides (G n) (syncBA π Afb) sc q c.1 := fun q hq => by
      obtain ⟨c, hc⟩ := hall q hq
      exact ⟨c, hc, (decides_of_commit le_rfl hc).1⟩
    refine ⟨⟨fun p hp => ?_, fun v hv p hp => ?_, fun p hp q hq v w hv hw => ?_⟩, ?_⟩
    · obtain ⟨c, -, hd⟩ := hdec p hp; exact ⟨_, hd⟩
    · obtain ⟨c, hc, hd⟩ := hdec p hp
      rwa [commit_valid hg v hv (sup_of_commit hg hp hc)] at hd
    · obtain ⟨c, hc, hd⟩ := hdec p hp
      obtain ⟨c', hc', hd'⟩ := hdec q hq
      rw [FirstSome.unique hv hd, FirstSome.unique hw hd']
      exact commit_agree hg hp hq hc hc'
    · intro p hp
      unfold roundBound
      split_ifs with hfk
      · rw [← hfeq] at hfk ⊢
        have h1 := all_commit hg hfk p hp
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h1
        have hle : 11 * (2 * (byzF s₁).card + 1) ≤ R0 n := by
          have := hg.res; have := hg.faults; unfold R0; omega
        exact ⟨_, le_rfl, _, (decides_of_commit hle hc).2⟩
      · obtain ⟨c, hc⟩ := hall p hp
        exact ⟨R0 n, by omega, _, (decides_of_commit le_rfl hc).2⟩
  -- (II) no honest party has a commit at the end of the views: everybody joins the fallback
  push_neg at hI
  have hnc : ∀ q, q ∉ sc.byz → (S π s₁ (Rh n) q).commit = none := fun q hq => by
    simpa using hI q hq
  have hfbs : ∀ q, q ∉ sc.byz → (S π s₁ (R0 n) q).fb.isSome := fun q hq => by
    rw [S_fb_R0]; exact fb_of_no_commit hg hnc q hq
  set s₂ := scB (π := π) sc
  have hin : ∀ q, q ∉ sc.byz → s₂.input q = some (finalValue π (S π s₁ (R0 n) q) (sc.input q)) :=
    fun q hq => by
      show seqInputs (G n) (stageA π) (R0 n) toB sc q = _
      rw [seqInputs_val, if_pos (hfbs q hq)]
  have hbyz : (bScen s₂).byz = sc.byz :=
    bScen_byz fun p hp => by rw [hin p hp]; rfl
  have hnb : ∀ q, q ∉ sc.byz → q ∉ (bScen s₂).byz := fun q hq => by rwa [hbyz]
  obtain ⟨hBA, hT⟩ := hfb.solves (bScen s₂) (by rw [hbyz]; exact hZ)
    (bScen_reliable (hrel.seqSnd (R0 n) _))
    (bScen_authValid (G n) ((authValid_seqP hV).seqSnd (G n) (stageA π) (R0 n) toB (stageB Afb)))
    trivial
  have hinB : ∀ q, q ∉ sc.byz → (bScen s₂).input q =
      finalValue π (S π s₁ (R0 n) q) (sc.input q) := fun q hq => by simp [bScen, hin q hq]
  -- decisions of parties without commit = decisions of `Afb`
  have hdB : ∀ q, q ∉ sc.byz → (S π s₁ (R0 n) q).commit = none → ∀ o,
      Decides (G n) (syncBA π Afb) sc q o ↔ Decides ⊤ Afb (bScen s₂) q o :=
    fun q hq hc o => (decides_iff_stageB hc (hfbs q hq) o).trans (decides_bScen _ _ (hnb q hq) o)
  have hterm : ∀ q, q ∉ sc.byz → ∃ r ≤ R0 n + Rfb, ∃ o,
      status (G n) (syncBA π Afb) sc r q = some o := by
    intro q hq
    rcases hcq : (S π s₁ (R0 n) q).commit with _ | c
    · obtain ⟨j, hj, o, ho⟩ := hT q (hnb q hq)
      refine ⟨R0 n + j, by omega, o, ?_⟩
      rw [status_syncBA_R0 hcq (hfbs q hq), status_bScen _ _ (hnb q hq)]; exact ho
    · exact ⟨R0 n, by omega, _, (decides_of_commit le_rfl hcq).2⟩
  have hround : TerminatesBy (G n) (syncBA π Afb) sc (roundBound π sc.byz.ncard Rfb) := by
    intro p hp
    unfold roundBound
    split_ifs with hfk
    · rw [← hfeq] at hfk ⊢
      have h1 := all_commit hg hfk p hp
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h1
      have hle : 11 * (2 * (byzF s₁).card + 1) ≤ R0 n := by
        have := hg.res; have := hg.faults; unfold R0; omega
      exact ⟨_, le_rfl, _, (decides_of_commit hle hc).2⟩
    · exact hterm p hp
  by_cases hIIa : ∃ p, p ∉ sc.byz ∧ (S π s₁ (R0 n) p).commit.isSome
  · -- (IIa) some honest party has a commit at the end of stage A
    obtain ⟨p₀, hp₀, hc₀⟩ := hIIa
    obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.1 hc₀
    have hfv := finalValue_eq_commit hg hnc hp₀ hc₀
    have hdec : ∀ q, q ∉ sc.byz → Decides (G n) (syncBA π Afb) sc q c₀.1 := by
      intro q hq
      rcases hcq : (S π s₁ (R0 n) q).commit with _ | c
      · rw [hdB q hq hcq]
        exact hBA.2.1 c₀.1 (fun q' hq' => by
          have hq'' : q' ∉ sc.byz := by rw [← hbyz]; exact hq'
          rw [hinB q' hq'']; exact hfv q' hq'')
          q (hnb q hq)
      · have := (decides_of_commit (Afb := Afb) le_rfl hcq).1
        rwa [commit_agree hg hq hp₀ hcq hc₀] at this
    refine ⟨⟨fun p hp => ⟨_, hdec p hp⟩, fun v hv p hp => ?_, fun p hp q hq v w hv hw => ?_⟩,
      hround⟩
    · rw [← commit_valid hg v hv (sup_of_commit hg hp₀ hc₀)]; exact hdec p hp
    · rw [FirstSome.unique hv (hdec p hp), FirstSome.unique hw (hdec q hq)]
  · -- (IIb) nobody honest has a commit: all decisions are those of `Afb`
    push_neg at hIIa
    have hnc0 : ∀ q, q ∉ sc.byz → (S π s₁ (R0 n) q).commit = none := fun q hq => by
      simpa using hIIa q hq
    refine ⟨⟨fun p hp => ?_, fun v hv p hp => ?_, fun p hp q hq v w hv hw => ?_⟩, hround⟩
    · obtain ⟨o, ho⟩ := hBA.1 p (hnb p hp)
      exact ⟨o, (hdB p hp (hnc0 p hp) o).2 ho⟩
    · refine (hdB p hp (hnc0 p hp) v).2 (hBA.2.1 v (fun q hq => ?_) p (hnb p hp))
      have hq' : q ∉ sc.byz := by rwa [← hbyz]
      rw [hinB q hq']
      exact finalValue_valid hg v hv hq'
    · exact hBA.2.2 p (hnb p hp) q (hnb q hq) v w ((hdB p hp (hnc0 p hp) v).1 hv)
        ((hdB q hq (hnc0 q hq) w).1 hw)

end Podc.FewToManyFaultsBA.Sync
