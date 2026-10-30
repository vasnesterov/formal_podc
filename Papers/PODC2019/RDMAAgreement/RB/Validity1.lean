import Papers.PODC2019.RDMAAgreement.RB.ValidityInv

/-!
# Algorithm 2 — Property (1), stage 1: every correct process echoes a correct broadcast

Setting: correct sender `p` broadcast `(k, m)`; no correct process ever delivers key `k` from `p`
(we argue by contradiction), so from some time `T` on every correct thread `(r,p)` works on key
`k`, and `Value[p,k,p]` is non-`⊥`. Then every correct `r` eventually leaves `WaitForSender`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- In a step of thread `(r,q)` that keeps its key, the key does not change by delivery. -/
lemma TStep.not_copy {s s' : St P M} {r q : P} {j : P} {ρ : L2 P M} {m : M}
    (hpc : s.pc r q = .wrCopy ρ m) (hlast : s'.last r q = s.last r q + 1)
    (hk : s'.key r q = s.key r q) : False := by
  simp [St.key] at hk; omega

open Classical in
/-- Measure for stage 1, as a function of the program counter. -/
noncomputable def mu1c (good : Prop) : PC P M → ℕ
  | .rdL2 _ todo => todo.card + 2
  | .rdSnd => if good then 1 else Fintype.card P + 2
  | _ => 0

/-- Measure for stage 1. -/
noncomputable def mu1 (r q : P) (s : St P M) : ℕ :=
  mu1c (∀ v ∈ s.cand r q, v ≠ .bot) (s.pc r q)

lemma mu1_eq {r q : P} {s : St P M} {c : PC P M} (h : s.pc r q = c) :
    mu1 r q s = mu1c (∀ v ∈ s.cand r q, v ≠ .bot) c := by
  unfold mu1; rw [h]

/-- Stage 1. -/
theorem stage1 [Inhabited P] (e : Exec (M := M) F f) (hfair : e.Fair) {p r : P} {k T : ℕ}
    (hp : p ∉ F) (hr : r ∉ F) (hkey : ∀ t ≥ T, (e.s t).key r p = k)
    (hmem : ∀ t ≥ T, (e.s t).mem ⟨.val, p, k, p⟩ ≠ .bot) :
    ∃ t ≥ T, (e.s t).phase r p ≠ .wfs := by
  refine eventually_of_measure (q := p) e hfair hr (fun t => (e.s t).phase r p ≠ .wfs)
    (fun t => mu1 r p (e.s t)) T fun t ht hG => ?_
  simp only [not_not] at hG
  have hs := e.step t
  have IA := InvA.reach (e.reach t)
  have IB := InvB.reach (e.reach t)
  have IC := InvC.reach (e.reach t)
  have IC' := InvC.reach (e.reach (t + 1))
  have hk := hkey t ht
  have hk1 := hkey (t + 1) (by omega)
  have Tr := IA.thr r hr p
  -- pending writes and current value of `Value[p,k,p]` are never `⊥` from `T` on
  have fresh : ∀ x ∈ ({(e.s (t + 1)).mem ⟨.val, p, k, p⟩} ∪ (e.s (t + 1)).pendW ⟨.val, p, k, p⟩ :
      Set (Val P M)), x ≠ .bot := by
    rintro x (hx | hx)
    · rw [Set.mem_singleton_iff.1 hx]; exact hmem (t + 1) (by omega)
    · rintro rfl; exact bot_not_mem_pendW _ _ hx
  by_cases hl : e.ℓ t = .thr r p
  · rw [hl] at hs
    have E := hs.thrEffect
    cases hs.tstep with
    | found i todo ρ m hpc _ _ hpc' =>
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu1_eq hpc', mu1_eq hpc] <;> simp [mu1c]
    | next i j todo v hpc _ _ hj hpc' =>
      have := Finset.card_erase_of_mem hj
      have := Finset.card_pos.2 ⟨j, hj⟩
      right
      refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu1_eq hpc', mu1_eq hpc] <;> simp only [mu1c] <;> omega
    | endS i v hpc _ _ _ hpc' hk' =>
      have hgood : ∀ v ∈ (e.s (t + 1)).cand r p, v ≠ .bot := fun v hv => by
        rcases E.cand_self ⟨.val, p, k, p⟩ (by rw [hpc', hk1]; rfl) v hv with h1 | h1
        · exact fresh v (Or.inl h1)
        · exact fresh v (Or.inr h1)
      right
      refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu1_eq hpc', mu1_eq hpc] <;>
        simp only [mu1c, if_pos hgood] <;> omega
    | endV _ _ _ _ _ _ hph0 => exact absurd hph0 (by rw [hG]; simp)
    | endL _ _ _ _ _ _ hph0 => exact absurd hph0 (by rw [hG]; simp)
    | copy j ρ m hpc hlast =>
      exfalso; have := hk1; rw [← hk] at this; simp [St.key] at this; omega
    | sndOk v c hpc _ _ _ _ hpc' =>
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu1_eq hpc', mu1_eq hpc] <;> simp only [mu1c] <;>
        split_ifs <;> omega
    | sndBad j v hpc hv hbad hpc' =>
      right
      have hn := card_erase_univ (P := P) j
      by_cases hgood : ∀ v ∈ (e.s t).cand r p, v ≠ .bot
      · exfalso
        rcases IC.good.cand r p _ (by rw [hpc, hk]; rfl) v hv rfl hp with h1 | ⟨b, rfl, hb⟩
        · exact hgood v hv h1
        · exact hbad ⟨_, rfl, hb.1, by rw [hk]; exact hb.2.1⟩
      · refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu1_eq hpc', mu1_eq hpc] <;>
          simp only [mu1c, PC.start, if_neg hgood] <;> omega
    | echo j b hpc hpc' hk' hph => exact Or.inl (by rw [hph]; simp)
    | valNext _ _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
    | valOk _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
    | valBad _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
    | l1Done _ _ hpc =>
      exact absurd (Tr.ph .wfl1 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
    | l1Next _ _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
    | l1Ok _ _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
    | l1Bad _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
    | l2Done _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hG])
  · right
    refine ⟨fun h => absurd h hl, ?_⟩
    have hl' : (e.s (t + 1)).loc r p = (e.s t).loc r p := by
      by_cases hT : ∃ p' q', e.ℓ t = .thr p' q'
      · obtain ⟨p', q', he⟩ := hT
        rw [he] at hs hl
        exact hs.frame_thr.1 r p (by rintro ⟨rfl, rfl⟩; exact hl rfl)
      · push_neg at hT; exact (hs.frame_other hT).1 r p
    simp only [St.loc, Loc.mk.injEq] at hl'
    unfold mu1; rw [hl'.1]
    cases hpc : (e.s t).pc r p with
    | rdSnd =>
      simp only [mu1c]
      by_cases hgood : ∀ v ∈ (e.s t).cand r p, v ≠ .bot
      · rw [if_pos hgood, if_pos]
        intro v hv
        rcases hs.cand_other hl hv with h1 | ⟨rr, e1, h1 | h1⟩
        · exact hgood v h1
        · rw [hpc, hk] at e1; cases e1; exact fresh v (Or.inr h1)
        · rw [hpc, hk] at e1; cases e1; exact absurd h1 hp
      · rw [if_neg hgood]; split_ifs <;> omega
    | _ => simp [mu1c]

end Podc.RDMAAgreement.RB
