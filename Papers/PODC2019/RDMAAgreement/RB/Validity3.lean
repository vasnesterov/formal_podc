import Papers.PODC2019.RDMAAgreement.RB.Validity2
import Mathlib.Data.Finset.Union

/-!
# Algorithm 2 — Property (1), stage 3: every correct process writes an L2 proof

Once every correct process wrote its L1 proof for `(p,k)` (all valid for `m`, by distinct
authors, `≥ n − f ≥ f + 1` of them), a scan of the `L1Proof` slots started afterwards collects
them all, so the check of line 62 succeeds and the process writes a valid L2 proof.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- A scan of the `L1Proof` slots that has collected every correct process's L1 proof. -/
def FreshL (F : Finset P) (s : St P M) (r p : P) (k : ℕ) (i : P) (todo : Finset P)
    (acc : Finset (L1 P M)) : Prop :=
  (∀ j ∉ F, j ∉ todo → j ≠ i → ∃ π, s.mem ⟨.l1, j, k, p⟩ = .p1 π ∧ π ∈ acc) ∧
  (i ∉ F → ∀ v ∈ s.cand r p, v = s.mem ⟨.l1, i, k, p⟩)

def fresh3 (F : Finset P) (s : St P M) (r p : P) (k : ℕ) : Prop :=
  ∃ i todo acc, s.pc r p = .rdL1 i todo acc ∧ FreshL F s r p k i todo acc

open Classical in
noncomputable def mu4c (fresh : Prop) : PC P M → ℕ
  | .rdL2 _ todo => todo.card + 1 + Fintype.card P
  | .rdL1 _ todo _ => if fresh then todo.card + 1 else todo.card + 1 + 2 * Fintype.card P
  | _ => 0

noncomputable def mu4 (F : Finset P) (r p : P) (k : ℕ) (s : St P M) : ℕ :=
  mu4c (fresh3 F s r p k) (s.pc r p)

lemma mu4_eq {r p : P} {k : ℕ} {s : St P M} {c : PC P M} (h : s.pc r p = c) :
    mu4 F r p k s = mu4c (fresh3 F s r p k) c := by
  unfold mu4; rw [h]

/-- The L1 proofs in a value. -/
def l1Of : Val P M → Finset (L1 P M)
  | .p1 π => {π}
  | _ => ∅

/-- In stage 3 no correct process has a pending write to its `L1Proof[·,k,p]` slot. -/
lemma pendL1_empty {s : St P M} (IA : InvA F s) {j p : P} {k : ℕ} (hj : j ∉ F)
    (hph : s.phase j p = .wfl2) {v : Val P M} (hv : v ∈ s.pendW ⟨.l1, j, k, p⟩) : False := by
  rcases hv with ⟨p', q', hw⟩ | ⟨p', b, -, hr, -⟩
  · cases hc : s.pc p' q' <;> simp [hc, PC.wr] at hw
    obtain ⟨⟨h1, -, h3⟩, -⟩ := hw
    subst h1; subst h3
    have := (IA.thr _ hj q').ph .wfl1 (by simp [St.loc, hc, PC.ph])
    simp [St.loc, hph] at this
  · cases hr

/-- The L1 slot of a correct process in stage 3 holds an L1 proof valid for `m`. -/
lemma l1slot_valid {s : St P M} (IB : InvB F s) (IH : InvH F f s) {j p : P} {k : ℕ} {m : M}
    (hj : j ∉ F) (hp : p ∉ F) (hph : s.phase j p = .wfl2) (hk : s.key j p = k)
    (hbc : s.bc p k = some m) :
    ∃ π, s.mem ⟨.l1, j, k, p⟩ = .p1 π ∧ π.author = j ∧ L1Valid f p k m π := by
  obtain ⟨π, hm, ha, b, hb1, hb2, hcard, hall⟩ := IH.l1slot j hj p hph
  rw [hk] at hm hall
  refine ⟨π, hm, ha, hcard, ?_⟩
  obtain ⟨c, hc⟩ := Finset.card_pos.1 (by omega : 0 < π.copies.card)
  have hsig := (sigOK_p1.1 (by have := IB.reg.mem ⟨.l1, j, k, p⟩; rwa [hm] at this)).2 c hc
  have e := bc_of_sig IB hsig (by rw [hall c hc]; exact hp)
  rw [hall c hc, hbc] at e; cases e
  exact hall

/-- Stage 3. -/
theorem stage3 [Inhabited P] (hF : F.card ≤ f) (hn : 2 * f + 1 ≤ Fintype.card P)
    (e : Exec (M := M) F f) (hfair : e.Fair) {p r : P} {k T : ℕ} {m : M} (hp : p ∉ F)
    (hr : r ∉ F) (hbc : ∀ t ≥ T, (e.s t).bc p k = some m)
    (hall : ∀ j ∉ F, ∀ t ≥ T, (e.s t).phase j p = .wfl2 ∧ (e.s t).key j p = k) :
    ∃ t ≥ T, SlotOK f (e.s t) r k p := by
  have hnpos := Fintype.card_pos_iff.2 ⟨r⟩
  refine eventually_of_measure (q := p) e hfair hr (fun t => SlotOK f (e.s t) r k p)
    (fun t => mu4 F r p k (e.s t)) T fun t ht hG => ?_
  have hs := e.step t
  have IA := InvA.reach (e.reach t)
  have IA' := InvA.reach (e.reach (t + 1))
  have IB := InvB.reach (e.reach t)
  have IH := InvH.reach (e.reach t)
  have IE' := InvE.reach hF (e.reach (t + 1))
  have IH' := InvH.reach (e.reach (t + 1))
  obtain ⟨hph, hk⟩ := hall r hr t ht
  have hk1 := (hall r hr (t + 1) (by omega)).2
  have Tr := IA.thr r hr p
  -- the L1 slots of correct processes are stable
  have hstab : ∀ j ∉ F, (e.s (t + 1)).mem ⟨.l1, j, k, p⟩ = (e.s t).mem ⟨.l1, j, k, p⟩ := by
    intro j hj
    by_cases hjl : e.ℓ t = .thr j p
    · have hs' := hs; rw [hjl] at hs'
      rcases hs'.thrEffect.mem ⟨.l1, j, k, p⟩ with h | h
      · exact h
      · exact absurd (pendL1_empty IA hj (hall j hj t ht).1 (Or.inl ⟨j, p, h⟩)) id
    · exact hs.mem_own hj hjl (by simp)
  have hval : ∀ j ∉ F, ∃ π, (e.s t).mem ⟨.l1, j, k, p⟩ = .p1 π ∧ π.author = j ∧
      L1Valid f p k m π := fun j hj =>
    l1slot_valid IB IH hj hp (hall j hj t ht).1 (hall j hj t ht).2 (hbc t ht)
  -- a fresh read of a correct L1 slot returns the slot's (stable) value
  have frl : ∀ (E : ThrEffect (e.s t) (e.s (t + 1)) r p) (j : P), j ∉ F →
      ((e.s (t + 1)).pc r p).rd p ((e.s (t + 1)).key r p) = some ⟨.l1, j, k, p⟩ →
      ∀ v ∈ (e.s (t + 1)).cand r p, v = (e.s (t + 1)).mem ⟨.l1, j, k, p⟩ := by
    intro E j hj hrd v hv
    rcases E.cand_self _ hrd v hv with h | h
    · exact h
    · exact absurd (pendL1_empty IA' hj (hall j hj (t + 1) (by omega)).1 h) id
  by_cases hl : e.ℓ t = .thr r p
  · rw [hl] at hs
    have E := hs.thrEffect
    cases hs.tstep with
    | found i todo ρ m' hpc _ _ hpc' =>
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu4_eq hpc', mu4_eq hpc] <;> simp only [mu4c] <;>
        omega
    | next i j todo v hpc _ _ hj hpc' =>
      have := Finset.card_erase_of_mem hj
      have := Finset.card_pos.2 ⟨j, hj⟩
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu4_eq hpc', mu4_eq hpc] <;> simp only [mu4c] <;>
        omega
    | endS _ _ _ _ _ hph0 => exact absurd hph0 (by rw [hph]; simp)
    | endV _ _ _ _ _ _ hph0 => exact absurd hph0 (by rw [hph]; simp)
    | endL i j v hpc _ _ _ hpc' =>
      have hc := card_erase_univ (P := P) j
      have hfr : fresh3 F (e.s (t + 1)) r p k :=
        ⟨j, _, _, hpc', fun j' _ h1 h2 => absurd (Finset.mem_erase.2 ⟨h2, Finset.mem_univ _⟩) h1,
          fun hj => frl E j hj (by rw [hpc', hk1]; rfl)⟩
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu4_eq hpc', mu4_eq hpc] <;>
        simp only [mu4c, if_pos hfr] <;> omega
    | copy j ρ m' hpc hlast =>
      exfalso; have := hk1; rw [← hk] at this; simp [St.key] at this; omega
    | sndOk _ _ hpc =>
      exact absurd (Tr.ph .wfs (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | sndBad _ _ hpc =>
      exact absurd (Tr.ph .wfs (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | echo _ _ hpc =>
      exact absurd (Tr.ph .wfs (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | valNext _ _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | valOk _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | valBad _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | l1Done _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | l1Ok i acc v S m' hpc _ _ _ hpc' =>
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu4_eq hpc', mu4_eq hpc] <;> simp only [mu4c] <;>
        split_ifs <;> omega
    | l2Done j ρ hpc hpc' hk' _ hmem =>
      left
      obtain ⟨m', hm'⟩ := IH.wrL2 r hr p ρ hpc
      refine ⟨⟨ρ, m', by rw [← hk]; exact hmem, by rw [← hk]; exact hm'⟩, fun v hv => ?_⟩
      exact pend_l2_valid IE' IH' hr hv
    | l1Next i j todo acc v hpc hv hj hpc' =>
      have := Finset.card_erase_of_mem hj
      have := Finset.card_pos.2 ⟨j, hj⟩
      right
      by_cases hfr : fresh3 F (e.s t) r p k
      · obtain ⟨i0, todo0, acc0, hpc0, h1, h3⟩ := id hfr
        rw [hpc] at hpc0; cases hpc0
        have hfr' : fresh3 F (e.s (t + 1)) r p k := by
          refine ⟨j, _, _, hpc', fun j' hj' hj1 hj2 => ?_, fun hjF => frl E j hjF
            (by rw [hpc', hk1]; rfl)⟩
          rw [hstab j' hj']
          by_cases hji : j' = i
          · subst hji
            obtain ⟨π, hπ, -⟩ := hval j' hj'
            have hv' := h3 hj' v hv; rw [hπ] at hv'; subst hv'
            exact ⟨π, hπ, by simp [addL1]⟩
          · obtain ⟨π, hπ, hm⟩ := h1 j' hj' (fun hm => hj1 (Finset.mem_erase.2 ⟨hj2, hm⟩)) hji
            refine ⟨π, hπ, ?_⟩
            unfold addL1; split
            · exact Finset.mem_insert_of_mem hm
            · exact hm
        refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu4_eq hpc', mu4_eq hpc] <;>
          simp only [mu4c, if_pos hfr', if_pos hfr] <;> omega
      · refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu4_eq hpc', mu4_eq hpc] <;>
          simp only [mu4c, if_neg hfr] <;> (try split_ifs) <;> omega
    | l1Bad i j acc v hpc hv hbad hpc' =>
      right
      have hc := card_erase_univ (P := P) j
      by_cases hfr : fresh3 F (e.s t) r p k
      · exfalso
        obtain ⟨i0, todo0, acc0, hpc0, h1, h3⟩ := id hfr
        rw [hpc] at hpc0; cases hpc0
        have hin : ∀ j' ∉ F, ∃ π, (e.s t).mem ⟨.l1, j', k, p⟩ = .p1 π ∧ π ∈ addL1 v acc := by
          intro j' hj'
          by_cases hji : j' = i
          · subst hji
            obtain ⟨π, hπ, -⟩ := hval j' hj'
            have hv' := h3 hj' v hv; rw [hπ] at hv'; subst hv'
            exact ⟨π, hπ, by simp [addL1]⟩
          · obtain ⟨π, hπ, hm⟩ := h1 j' hj' (Finset.notMem_empty _) hji
            refine ⟨π, hπ, ?_⟩
            unfold addL1; split
            · exact Finset.mem_insert_of_mem hm
            · exact hm
        set S := (Finset.univ.filter (· ∉ F)).biUnion (fun j => l1Of ((e.s t).mem ⟨.l1, j, k, p⟩))
        refine hbad ⟨S, m, fun π hπ => ?_, ?_, fun π hπ => ?_⟩
        · obtain ⟨j', hj', hπ'⟩ := Finset.mem_biUnion.1 hπ
          obtain ⟨π', hπ'', hm⟩ := hin j' (by simpa using hj')
          rw [hπ''] at hπ'; simp [l1Of] at hπ'; rw [hπ']; exact hm
        · refine le_trans (card_correct_le hF hn) (Finset.card_le_card fun j' hj' => ?_)
          have hj'' : j' ∉ F := by simpa using hj'
          obtain ⟨π, hπ, ha, -⟩ := hval j' hj''
          refine Finset.mem_image.2 ⟨π, Finset.mem_biUnion.2 ⟨j', hj', by simp [hπ, l1Of]⟩, ha⟩
        · obtain ⟨j', hj', hπ'⟩ := Finset.mem_biUnion.1 hπ
          obtain ⟨π', hπ'', -, hvalid⟩ := hval j' (by simpa using hj')
          rw [hπ''] at hπ'; simp [l1Of] at hπ'; rw [hπ', hk]; exact hvalid
      · refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu4_eq hpc', mu4_eq hpc] <;>
          simp only [mu4c, PC.start, if_neg hfr] <;> omega
  · right
    refine ⟨fun h => absurd h hl, ?_⟩
    have hl' : (e.s (t + 1)).loc r p = (e.s t).loc r p := by
      by_cases hT : ∃ p' q', e.ℓ t = .thr p' q'
      · obtain ⟨p', q', he⟩ := hT
        rw [he] at hs hl
        exact hs.frame_thr.1 r p (by rintro ⟨rfl, rfl⟩; exact hl rfl)
      · push_neg at hT; exact (hs.frame_other hT).1 r p
    simp only [St.loc, Loc.mk.injEq] at hl'
    rw [mu4_eq (F := F) (k := k) hl'.1, mu4_eq (F := F) (k := k) (s := e.s t) rfl]
    by_cases hfr : fresh3 F (e.s t) r p k
    · have hfr' : fresh3 F (e.s (t + 1)) r p k := by
        obtain ⟨i, todo, acc, hpc0, h1, h3⟩ := id hfr
        refine ⟨i, todo, acc, by rw [hl'.1]; exact hpc0, fun j hj hj1 hj2 => ?_, fun hi v hv => ?_⟩
        · rw [hstab j hj]; exact h1 j hj hj1 hj2
        · rw [hstab i hi]
          rcases hs.cand_other hl hv with h | ⟨rr, e1, h | h⟩
          · exact h3 hi v h
          · rw [hpc0, hk] at e1; cases e1
            exact absurd (pendL1_empty IA' hi (hall i hi (t + 1) (by omega)).1 h) id
          · rw [hpc0, hk] at e1; cases e1; exact absurd h hi
      obtain ⟨i, todo, acc, hpc0, -⟩ := id hfr
      rw [hpc0]; simp only [mu4c, if_pos hfr', if_pos hfr]; exact le_rfl
    · cases hpc : (e.s t).pc r p <;> simp only [mu4c, if_neg hfr] <;> (try split_ifs) <;> omega

end Podc.RDMAAgreement.RB
