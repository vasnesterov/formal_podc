import Papers.PODC2019.RDMAAgreement.RB.Validity1

/-!
# Algorithm 2 — Property (1), stage 2: every correct process writes an L1 proof

Once every correct process has echoed the correct sender's pair `b = (p,k,m)`, a scan of the
`Value` slots started afterwards sees `b` endorsed by every correct process (`≥ n − f ≥ f + 1`
copies) and nothing else for key `k` (unforgeability), so the check of line 50 succeeds.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- A scan of the `Value` slots (by thread `(r,p)`) that has seen every correct slot with `b`. -/
def FreshV (F : Finset P) (s : St P M) (r p : P) (b : Base P M) (i : P) (todo : Finset P)
    (acc : Finset (Copy P M)) : Prop :=
  (∀ j ∉ F, j ∉ todo → j ≠ i → (⟨j, b⟩ : Copy P M) ∈ acc) ∧ (∀ c ∈ acc, c.base = b) ∧
  (i ∉ F → ∀ v ∈ s.cand r p, v = .cp ⟨i, b⟩)

def fresh2 (F : Finset P) (s : St P M) (r p : P) (b : Base P M) : Prop :=
  ∃ i todo acc, s.pc r p = .rdVal i todo acc ∧ FreshV F s r p b i todo acc

open Classical in
noncomputable def mu2c (fresh : Prop) : PC P M → ℕ
  | .rdL2 _ todo => todo.card + 1 + Fintype.card P
  | .rdVal _ todo _ => if fresh then todo.card + 1 else todo.card + 1 + 2 * Fintype.card P
  | _ => 0

noncomputable def mu2 (F : Finset P) (r p : P) (b : Base P M) (s : St P M) : ℕ :=
  mu2c (fresh2 F s r p b) (s.pc r p)

lemma mu2_eq {r p : P} {b : Base P M} {s : St P M} {c : PC P M} (h : s.pc r p = c) :
    mu2 F r p b s = mu2c (fresh2 F s r p b) c := by
  unfold mu2; rw [h]

/-- At least `f + 1` correct processes. -/
lemma card_correct_le (hF : F.card ≤ f) (hn : 2 * f + 1 ≤ Fintype.card P) :
    f + 1 ≤ (Finset.univ.filter (· ∉ F) : Finset P).card := by
  have e : (Finset.univ.filter (· ∉ F) : Finset P) = Fᶜ := by ext; simp
  rw [e, Finset.card_compl]; have := F.card_le_univ; omega

/-- Endorsements by all correct processes of `b` give `f + 1` copies. -/
lemma card_copies (hF : F.card ≤ f) (hn : 2 * f + 1 ≤ Fintype.card P) {b : Base P M}
    {acc : Finset (Copy P M)} (h : ∀ j ∉ F, (⟨j, b⟩ : Copy P M) ∈ acc) : f + 1 ≤ acc.card := by
  refine le_trans (card_correct_le hF hn) (le_trans ?_ (Finset.card_le_card
    (s := (Finset.univ.filter (· ∉ F)).image (fun j => (⟨j, b⟩ : Copy P M))) ?_))
  · rw [Finset.card_image_of_injective _ (fun a a' h => by simpa using h)]
  · intro c hc
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
    exact h j (by simpa using hj)

/-- An accepted copy for a correct sender's key carries the sender's broadcast. -/
lemma addVal_base {s : St P M} (IB : InvB F s) {r p i : P} {k : ℕ} {m : M} {rr : Reg P}
    (hp : p ∉ F) (hbc : s.bc p k = some m) (hrd : (s.pc r p).rd p (s.key r p) = some rr)
    {v : Val P M} (hv : v ∈ s.cand r p) {acc : Finset (Copy P M)} {c : Copy P M}
    (hc : c ∈ addVal i p k v acc) : c ∈ acc ∨ (c = ⟨i, ⟨p, k, m⟩⟩ ∧ v = .cp c) := by
  unfold addVal at hc
  split at hc
  · rename_i c'
    split_ifs at hc with hcc
    · rcases Finset.mem_insert.1 hc with rfl | hc
      · right
        have hs := IB.cand_sig hrd hv
        have e := bc_of_sig IB hs (by rw [hcc.2.1]; exact hp)
        rw [hcc.2.1, hcc.2.2, hbc] at e
        refine ⟨?_, rfl⟩
        obtain ⟨sg, ⟨bs, bk, bm⟩⟩ := c
        simp only at hcc e ⊢; obtain ⟨rfl, rfl, rfl⟩ := hcc; cases e; rfl
      · exact Or.inl hc
    · exact Or.inl hc
  · exact Or.inl hc

/-- A fresh read of a correct `Value` slot after all echoes completed returns `b`. -/
lemma fresh_val {s s' : St P M} {r p j : P} {k : ℕ} {m : M} (E : ThrEffect s s' r p)
    (IB' : InvB F s') (IC' : InvC F s') (hp : p ∉ F) (hj : j ∉ F)
    (hbc : s'.bc p k = some m) (hecho : s'.echoT j p k ≠ none)
    (hrd : (s'.pc r p).rd p (s'.key r p) = some ⟨.val, j, k, p⟩) :
    ∀ v ∈ s'.cand r p, v = .cp ⟨j, ⟨p, k, m⟩⟩ := by
  intro v hv
  have hgood : v = .bot ∨ ∃ b', v = .cp ⟨j, b'⟩ ∧ canon s' j p k b' := by
    rcases E.cand_self _ hrd v hv with rfl | h
    · exact IC'.good.mem _ rfl hj
    · exact IC'.good.pend _ v h rfl hj
  rcases hgood with rfl | ⟨b', rfl, hc⟩
  · exfalso
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hecho
    rcases E.cand_self _ hrd _ hv with h | h
    · exact IC'.nb j hj p k e he h.symm
    · exact bot_not_mem_pendW _ _ h
  · obtain ⟨hb1, hb2⟩ := bc_of_canon IB' hj hp hc
    rw [hbc] at hb2; cases hb2; rw [hb1]

/-- Stage 2. -/
theorem stage2 [Inhabited P] (hF : F.card ≤ f) (hn : 2 * f + 1 ≤ Fintype.card P)
    (e : Exec (M := M) F f) (hfair : e.Fair) {p r : P} {k T : ℕ} {m : M} (hp : p ∉ F)
    (hr : r ∉ F) (hkey : ∀ t ≥ T, (e.s t).key r p = k)
    (hbc : ∀ t ≥ T, (e.s t).bc p k = some m)
    (hph1 : ∀ t ≥ T, (e.s t).phase r p ≠ .wfs)
    (hecho : ∀ j ∉ F, ∀ t ≥ T, (e.s t).echoT j p k ≠ none) :
    ∃ t ≥ T, (e.s t).phase r p = .wfl2 := by
  set b : Base P M := ⟨p, k, m⟩
  have hnpos := Fintype.card_pos_iff.2 ⟨r⟩
  refine eventually_of_measure (q := p) e hfair hr (fun t => (e.s t).phase r p = .wfl2)
    (fun t => mu2 F r p b (e.s t)) T fun t ht hG => ?_
  have hs := e.step t
  have IA := InvA.reach (e.reach t)
  have IB := InvB.reach (e.reach t)
  have IB' := InvB.reach (e.reach (t + 1))
  have IC' := InvC.reach (e.reach (t + 1))
  have hk := hkey t ht
  have hk1 := hkey (t + 1) (by omega)
  have Tr := IA.thr r hr p
  have hph : (e.s t).phase r p = .wfl1 := by
    have := hph1 t ht; cases h : (e.s t).phase r p <;> simp_all
  by_cases hl : e.ℓ t = .thr r p
  · rw [hl] at hs
    have E := hs.thrEffect
    have fv : ∀ j ∉ F, (e.s (t + 1)).pc r p = .rdVal j (Finset.univ.erase j) ∅ ∨
        (∃ todo acc, (e.s (t + 1)).pc r p = .rdVal j todo acc) →
        ∀ v ∈ (e.s (t + 1)).cand r p, v = .cp ⟨j, b⟩ := by
      intro j hj hpc'
      have hpc'' : ∃ todo acc, (e.s (t + 1)).pc r p = .rdVal j todo acc := by
        rcases hpc' with h | h
        · exact ⟨_, _, h⟩
        · exact h
      obtain ⟨todo, acc, hpc''⟩ := hpc''
      exact fresh_val E IB' IC' hp hj (hbc (t + 1) (by omega)) (hecho j hj (t + 1) (by omega))
        (by rw [hpc'', hk1]; rfl)
    cases hs.tstep with
    | found i todo ρ m' hpc _ _ hpc' =>
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu2_eq hpc', mu2_eq hpc] <;> simp only [mu2c] <;>
        omega
    | next i j todo v hpc _ _ hj hpc' =>
      have := Finset.card_erase_of_mem hj
      have := Finset.card_pos.2 ⟨j, hj⟩
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu2_eq hpc', mu2_eq hpc] <;> simp only [mu2c] <;>
        omega
    | endS _ _ _ _ _ hph0 => exact absurd hph0 (by rw [hph]; simp)
    | endL _ _ _ _ _ _ hph0 => exact absurd hph0 (by rw [hph]; simp)
    | endV i j v hpc _ _ _ hpc' =>
      have hc := card_erase_univ (P := P) j
      have hfr : fresh2 F (e.s (t + 1)) r p b :=
        ⟨j, _, _, hpc', fun j' _ h1 h2 => absurd (Finset.mem_erase.2 ⟨h2, Finset.mem_univ _⟩) h1,
          fun c hc => absurd hc (Finset.notMem_empty _),
          fun hj => fv j hj (Or.inl hpc')⟩
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu2_eq hpc', mu2_eq hpc] <;>
        simp only [mu2c, if_pos hfr] <;> omega
    | copy j ρ m' hpc hlast =>
      exfalso; have := hk1; rw [← hk] at this; simp [St.key] at this; omega
    | sndOk _ _ hpc =>
      exact absurd (Tr.ph .wfs (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | sndBad _ _ hpc =>
      exact absurd (Tr.ph .wfs (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | echo _ _ hpc =>
      exact absurd (Tr.ph .wfs (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | l1Done _ _ _ _ _ hph' => exact Or.inl hph'
    | l1Next _ _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | l1Ok _ _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | l1Bad _ _ _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | l2Done _ _ hpc =>
      exact absurd (Tr.ph .wfl2 (by simp [St.loc, hpc, PC.ph])) (by simp [St.loc, hph])
    | valOk i acc v b' hpc _ _ _ hpc' =>
      right; refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu2_eq hpc', mu2_eq hpc] <;> simp only [mu2c] <;>
        split_ifs <;> omega
    | valNext i j todo acc v hpc hv hj hpc' =>
      have := Finset.card_erase_of_mem hj
      have := Finset.card_pos.2 ⟨j, hj⟩
      right
      by_cases hfr : fresh2 F (e.s t) r p b
      · obtain ⟨i0, todo0, acc0, hpc0, h1, h2, h3⟩ := hfr
        rw [hpc] at hpc0; cases hpc0
        have hfr' : fresh2 F (e.s (t + 1)) r p b := by
          refine ⟨j, _, _, hpc', fun j' hj' hj1 hj2 => ?_, fun c hc => ?_,
            fun hjF => fv j hjF (Or.inr ⟨_, _, hpc'⟩)⟩
          · by_cases hji : j' = i
            · subst hji
              have hv' := h3 hj' v hv; subst hv'
              simp [addVal, b, hk]
            · exact subset_addVal _ _ _ _ _ (h1 j' hj' (fun hm => hj1
                (Finset.mem_erase.2 ⟨hj2, hm⟩)) hji)
          · have hc' : c ∈ addVal i p k v acc := by rw [← hk]; exact hc
            rcases addVal_base IB hp (hbc t ht) (by rw [hpc]; rfl) hv hc' with hc | ⟨rfl, -⟩
            · exact h2 c hc
            · rfl
        have hfr0 : fresh2 F (e.s t) r p b := ⟨i, todo, acc, hpc, h1, h2, h3⟩
        refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu2_eq hpc', mu2_eq hpc] <;>
          simp only [mu2c, if_pos hfr', if_pos hfr0] <;> omega
      · refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu2_eq hpc', mu2_eq hpc] <;>
          simp only [mu2c, if_neg hfr] <;> split_ifs <;> omega
    | valBad i j acc v hpc hv hbad hpc' =>
      right
      have hc := card_erase_univ (P := P) j
      by_cases hfr : fresh2 F (e.s t) r p b
      · exfalso
        obtain ⟨i0, todo0, acc0, hpc0, h1, h2, h3⟩ := hfr
        rw [hpc] at hpc0; cases hpc0
        have hall : ∀ j' ∉ F, (⟨j', b⟩ : Copy P M) ∈ addVal i p ((e.s t).key r p) v acc := by
          intro j' hj'
          by_cases hji : j' = i
          · subst hji
            have hv' := h3 hj' v hv; subst hv'
            simp [addVal, b, hk]
          · exact subset_addVal _ _ _ _ _ (h1 j' hj' (Finset.notMem_empty _) hji)
        refine hbad ⟨card_copies hF hn hall, b, fun c hc => ?_⟩
        have hc' : c ∈ addVal i p k v acc := by rw [← hk]; exact hc
        rcases addVal_base IB hp (hbc t ht) (by rw [hpc]; rfl) hv hc' with hc | ⟨rfl, -⟩
        · exact h2 c hc
        · rfl
      · refine ⟨fun _ => ?_, ?_⟩ <;> rw [mu2_eq hpc', mu2_eq hpc] <;>
          simp only [mu2c, PC.start, if_neg hfr] <;> omega
  · right
    refine ⟨fun h => absurd h hl, ?_⟩
    have hl' : (e.s (t + 1)).loc r p = (e.s t).loc r p := by
      by_cases hT : ∃ p' q', e.ℓ t = .thr p' q'
      · obtain ⟨p', q', he⟩ := hT
        rw [he] at hs hl
        exact hs.frame_thr.1 r p (by rintro ⟨rfl, rfl⟩; exact hl rfl)
      · push_neg at hT; exact (hs.frame_other hT).1 r p
    simp only [St.loc, Loc.mk.injEq] at hl'
    rw [mu2_eq (F := F) (b := b) hl'.1, mu2_eq (F := F) (b := b) (s := e.s t) rfl]
    by_cases hfr : fresh2 F (e.s t) r p b
    · have hfr' : fresh2 F (e.s (t + 1)) r p b := by
        obtain ⟨i, todo, acc, hpc0, h1, h2, h3⟩ := id hfr
        refine ⟨i, todo, acc, by rw [hl'.1]; exact hpc0, h1, h2, fun hi v hv => ?_⟩
        rcases hs.cand_other hl hv with h | ⟨rr, e1, h | h⟩
        · exact h3 hi v h
        · rw [hpc0, hk] at e1; cases e1
          rcases IC'.good.pend _ v h rfl hi with rfl | ⟨b', rfl, hc⟩
          · exact absurd h (bot_not_mem_pendW _ _)
          · obtain ⟨hb1, hb2⟩ := bc_of_canon IB' hi hp hc
            rw [hbc (t + 1) (by omega)] at hb2; cases hb2; rw [hb1]
        · rw [hpc0, hk] at e1; cases e1; exact absurd h hi
      obtain ⟨i, todo, acc, hpc0, -⟩ := id hfr
      rw [hpc0]; simp only [mu2c, if_pos hfr', if_pos hfr]; exact le_rfl
    · cases hpc : (e.s t).pc r p <;> simp only [mu2c, if_neg hfr] <;> (try split_ifs) <;> omega

end Podc.RDMAAgreement.RB
