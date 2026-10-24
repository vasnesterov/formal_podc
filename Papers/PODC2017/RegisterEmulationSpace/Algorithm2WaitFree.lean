import Papers.PODC2017.RegisterEmulationSpace.Algorithm2Inv

/-!
# Algorithm 2 is wait-free (proof of Theorem 3, liveness part)

`Alg2.WaitFree A δ f`: in every fair run with at most `f` crashed servers, every high-level
operation invoked by a correct client returns (no contention assumption). It implies
`Alg.ObstructionFree δ f Wr` for every `Wr`.

Proof. Suppose a correct client `c` never returns. The potential
`Ψ = cnt + 2|coverSet| + |q| + |rq| (+ 2|R c| while collecting for a write)` never increases while
`c` is busy and bounds the number `cnt` of low-level operations triggered by `c`; hence `c`
eventually stops triggering, then its pending operations eventually stop changing, so they are all on
crashed servers (fairness). The next step of `c` then finds its collect complete (all registers of
the correct servers responded) or `|wrSet| ≥ |R c| - f` (the registers of `R c` are on distinct
servers), so it moves on — and since it cannot trigger anything, it can only return or enter the
writing phase once, a contradiction.
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

/-- Wait freedom (Section 2), `f`-tolerant: in every fair run with at most `f` crashed servers,
every operation invoked by a correct client returns. -/
def WaitFree {L W : Type*} (A : Alg C B V W L) (δ : B → S) (f : ℕ) : Prop :=
  ∀ (ev : ℕ → Ev C V) (Fc : Set C) (Fs : Finset S), Fs.card ≤ f → A.Fair δ ev Fc ↑Fs →
    ∀ t c o, c ∉ Fc → ev t = .inv c o → (A.traj ev t).cur c = none →
      ∃ t' > t, (A.traj ev t').cur c = none

lemma WaitFree.obstructionFree {L W : Type*} {A : Alg C B V W L} {δ : B → S} {f : ℕ}
    (h : WaitFree A δ f) (Wr : Set C) : A.ObstructionFree δ f Wr :=
  fun ev Fc Fs hFs hfair _ t c o hc hev hcur _ => h ev Fc Fs hFs hfair t c o hc hev hcur

/-- An antitone sequence of naturals is eventually constant. -/
lemma eventually_const_of_antitone (g : ℕ → ℕ) (t₀ : ℕ) (h : ∀ t ≥ t₀, g (t + 1) ≤ g t) :
    ∃ T ≥ t₀, ∀ t ≥ T, g t = g T := by
  induction hk : g t₀ using Nat.strong_induction_on generalizing t₀ with
  | _ k ih =>
    have hle : ∀ t ≥ t₀, g t ≤ g t₀ := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => exact le_rfl
      | succ t ht ih' => exact (h t ht).trans ih'
    by_cases hc : ∀ t ≥ t₀, g t = g t₀
    · exact ⟨t₀, le_rfl, hc⟩
    · push Not at hc
      obtain ⟨t₁, ht₁, hne⟩ := hc
      have hlt : g t₁ < k := hk ▸ lt_of_le_of_ne (hle t₁ ht₁) hne
      obtain ⟨T, hT, hT'⟩ := ih _ hlt t₁ (fun t ht => h t (by omega)) rfl
      exact ⟨T, by omega, hT'⟩

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V)

/-- Effect of a step of `c` on `c` itself. -/
lemma doStep_self (X : Cfg C B V (ℕ × V) (Loc B V)) (c : C) :
    ∃ a l', ActSpec δ f (R c) (X.loc c) a l' ∧ ((alg δ f R v₀).doStep X c).loc c = l' ∧
      match a with
      | .trig b o => ((alg δ f R v₀).doStep X c).cnt c = X.cnt c + 1 ∧
          ((alg δ f R v₀).doStep X c).pend c = X.pend c ++ [⟨X.cnt c, b, o⟩] ∧
          ((alg δ f R v₀).doStep X c).cur c = X.cur c
      | .ret _ => ((alg δ f R v₀).doStep X c).cnt c = X.cnt c ∧
          ((alg δ f R v₀).doStep X c).pend c = X.pend c ∧
          ((alg δ f R v₀).doStep X c).cur c = none
      | .skip => ((alg δ f R v₀).doStep X c).cnt c = X.cnt c ∧
          ((alg δ f R v₀).doStep X c).pend c = X.pend c ∧
          ((alg δ f R v₀).doStep X c).cur c = X.cur c := by
  refine ⟨_, _, act_spec δ f R v₀ c (X.loc c), ?_⟩
  rw [doStep_eq]
  generalize ((alg δ f R v₀).act c (X.loc c)).1 = a
  rcases a with ⟨b, o⟩ | x | _
  · simp
  · rcases hcur : X.cur c with _ | o
    · simp [hcur]
    · simp
  · simp

/-- The potential of a client. -/
def pot (Rc : Finset B) (n : ℕ) (l : Loc B V) : ℕ :=
  n + 2 * #l.cov + #l.q + match l.mode with
    | .rd => #l.rq
    | .wc _ => #l.rq + 2 * #Rc
    | _ => 0

lemma pot_step {Rc : Finset B} {l l' : Loc B V} {a : Act B (ℕ × V) V} {P o}
    (hci : CI Rc f l P o) (hs : ActSpec δ f Rc l a l') (n : ℕ) :
    pot Rc (match a with | .trig _ _ => n + 1 | _ => n) l' ≤ pot Rc n l := by
  cases hs with
  | trigW b hb =>
    have := card_erase_of_mem hb
    have := card_pos.2 ⟨b, hb⟩
    simp only [pot]; omega
  | trigR b hq hc hb =>
    have := card_erase_of_mem hb
    have := card_pos.2 ⟨b, hb⟩
    simp only [pot]
    rcases hm : l.mode with _ | _ | _ | _ <;> simp [hm] at hc ⊢ <;> omega
  | retR hq hm hr hd => simp only [pot, hm]; omega
  | toWp v hq hm hr hd =>
    have h1 := card_sdiff_of_subset hci.pw_sub
    have h2 := card_le_card hci.pw_sub
    simp only [pot, hm, hq, hr, card_empty]; omega
  | retW hq hm hc => simp only [pot, hm]; omega
  | skip _ _ _ => exact le_rfl

lemma pot_recvRead (Rc : Finset B) (n : ℕ) (l : Loc B V) (b : B) (w : ℕ × V) :
    pot Rc n (recvRead l b w) = pot Rc n l := by
  unfold recvRead; split_ifs <;> rfl

lemma pot_recvWrite (Rc : Finset B) (n : ℕ) (l : Loc B V) (b : B) :
    pot Rc n (recvWrite l b) ≤ pot Rc n l := by
  unfold recvWrite; split_ifs with hb
  · have := card_erase_of_mem hb
    have := card_pos.2 ⟨b, hb⟩
    have := card_insert_le b l.q
    simp only [pot]; omega
  · exact le_rfl

section Run

variable {ev : ℕ → Ev C V} {c : C}


lemma traj_succ (t : ℕ) : (alg δ f R v₀).traj ev (t + 1) = (alg δ f R v₀).step ((alg δ f R v₀).traj ev t) (ev t) := rfl

/-- The potential never increases while `c` is busy. -/
lemma pot_traj_succ (t : ℕ) (hbusy : ((alg δ f R v₀).traj ev t).cur c ≠ none) :
    pot (R c) (((alg δ f R v₀).traj ev (t + 1)).cnt c) (((alg δ f R v₀).traj ev (t + 1)).loc c) ≤ pot (R c) (((alg δ f R v₀).traj ev t).cnt c) (((alg δ f R v₀).traj ev t).loc c) ∧
    ((alg δ f R v₀).traj ev t).cnt c ≤ ((alg δ f R v₀).traj ev (t + 1)).cnt c := by
  have hgi := gi_traj δ f R v₀ ev t
  rw [traj_succ δ f R v₀]
  rcases hev : ev t with ⟨d, o⟩ | d | ⟨d, n⟩
  · by_cases hcd : c = d
    · subst hcd; simp [Alg.doInv, hbusy]
    · obtain ⟨h1, h2, h3, h4⟩ := (alg δ f R v₀).doInv_other ((alg δ f R v₀).traj ev t) o hcd
      rw [Alg.step_inv, h2, h4]; exact ⟨le_rfl, le_rfl⟩
  · by_cases hcd : c = d
    · subst hcd
      obtain ⟨a, l', hs, hl, hrest⟩ := doStep_self δ f R v₀ ((alg δ f R v₀).traj ev t) c
      have hp := pot_step δ f (hgi.2 c) hs (((alg δ f R v₀).traj ev t).cnt c)
      simp only [Alg.step_step, hl]
      rcases a with ⟨b, o⟩ | x | _
      · rw [hrest.1]; exact ⟨hp, by omega⟩
      · rw [hrest.1]; exact ⟨hp, le_rfl⟩
      · rw [hrest.1]; exact ⟨hp, le_rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := (alg δ f R v₀).step_other ((alg δ f R v₀).traj ev t) (e := .step d) rfl hcd
      rw [h2, h4]; exact ⟨le_rfl, le_rfl⟩
  · by_cases hcd : c = d
    · subst hcd
      simp only [Alg.step_resp, Alg.doResp]
      split
      · exact ⟨le_rfl, le_rfl⟩
      · rename_i p hp
        unfold Alg.apply
        rcases hop : p.op with _ | w
        · simp [alg, hop, pot_recvRead]
        · simpa [alg, hop] using pot_recvWrite (R c) (((alg δ f R v₀).traj ev t).cnt c) (((alg δ f R v₀).traj ev t).loc c) p.reg
    · obtain ⟨h1, h2, h3, h4⟩ := (alg δ f R v₀).step_other ((alg δ f R v₀).traj ev t) (e := .resp d n) rfl hcd
      rw [h2, h4]; exact ⟨le_rfl, le_rfl⟩

/-- After `c` stops triggering, its pending operations only shrink. -/
lemma pend_traj_succ (t : ℕ) (hbusy : ((alg δ f R v₀).traj ev t).cur c ≠ none)
    (hcnt : ((alg δ f R v₀).traj ev (t + 1)).cnt c = ((alg δ f R v₀).traj ev t).cnt c) :
    (((alg δ f R v₀).traj ev (t + 1)).pend c = ((alg δ f R v₀).traj ev t).pend c ∧ (ev t ≠ .step c → ((alg δ f R v₀).traj ev (t + 1)).loc c = ((alg δ f R v₀).traj ev t).loc c) ∨
      (((alg δ f R v₀).traj ev (t + 1)).pend c).length < (((alg δ f R v₀).traj ev t).pend c).length) := by
  have hgi := gi_traj δ f R v₀ ev t
  rw [traj_succ δ f R v₀] at hcnt ⊢
  rcases hev : ev t with ⟨d, o⟩ | d | ⟨d, n⟩
  · rw [hev] at hcnt
    by_cases hcd : c = d
    · subst hcd; left; simp [Alg.doInv, hbusy]
    · obtain ⟨h1, h2, h3, h4⟩ := (alg δ f R v₀).doInv_other ((alg δ f R v₀).traj ev t) o hcd
      left; exact ⟨h1, fun _ => h2⟩
  · rw [hev] at hcnt
    by_cases hcd : c = d
    · subst hcd
      obtain ⟨a, l', hs, hl, hrest⟩ := doStep_self δ f R v₀ ((alg δ f R v₀).traj ev t) c
      simp only [Alg.step_step] at hcnt ⊢
      rcases a with ⟨b, o⟩ | x | _
      · rw [hrest.1] at hcnt; omega
      · exact Or.inl ⟨hrest.2.1, fun h => absurd rfl h⟩
      · exact Or.inl ⟨hrest.2.1, fun h => absurd rfl h⟩
    · obtain ⟨h1, h2, h3, h4⟩ := (alg δ f R v₀).step_other ((alg δ f R v₀).traj ev t) (e := .step d) rfl hcd
      left; exact ⟨h1, fun _ => h2⟩
  · by_cases hcd : c = d
    · subst hcd
      simp only [Alg.step_resp, Alg.doResp]
      split
      · left; exact ⟨rfl, fun _ => rfl⟩
      · rename_i p hp
        right
        rw [Alg.apply_pend_self, List.length_filter_lt_length_iff_exists]
        exact ⟨p, List.mem_of_find?_eq_some hp, by simp⟩
    · obtain ⟨h1, h2, h3, h4⟩ := (alg δ f R v₀).step_other ((alg δ f R v₀).traj ev t) (e := .resp d n) rfl hcd
      left; exact ⟨h1, fun _ => h2⟩

end Run

lemma pot_ge (Rc : Finset B) (n : ℕ) (l : Loc B V) : n ≤ pot Rc n l := by
  unfold pot; omega

/-- **Theorem 3 (liveness)**: Algorithm 2 is `f`-tolerant wait-free, provided every write set
consists of registers on distinct servers. -/
theorem waitFree (hinj : ∀ c, Set.InjOn δ ↑(R c)) : WaitFree (alg δ f R v₀) δ f := by
  intro ev Fc Fs hFs hfair t₀ c o hc hev hcur
  by_contra hcon
  push Not at hcon
  have hbusy : ∀ t ≥ t₀ + 1, ((alg δ f R v₀).traj ev t).cur c ≠ none := fun t ht => hcon t (by omega)
  -- the potential bounds the number of triggered operations
  set K := pot (R c) (((alg δ f R v₀).traj ev (t₀ + 1)).cnt c) (((alg δ f R v₀).traj ev (t₀ + 1)).loc c)
  have hpotle : ∀ t ≥ t₀ + 1,
      pot (R c) (((alg δ f R v₀).traj ev t).cnt c) (((alg δ f R v₀).traj ev t).loc c) ≤ K := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih => exact ((pot_traj_succ δ f R v₀ t (hbusy t ht)).1).trans ih
  have hcntK : ∀ t ≥ t₀ + 1, ((alg δ f R v₀).traj ev t).cnt c ≤ K :=
    fun t ht => (pot_ge _ _ _).trans (hpotle t ht)
  obtain ⟨T1, hT1, hT1'⟩ := eventually_const_of_antitone
    (fun t => K - ((alg δ f R v₀).traj ev t).cnt c) (t₀ + 1) (fun t ht => by
      have := (pot_traj_succ δ f R v₀ t (hbusy t ht)).2
      omega)
  have hcnt : ∀ t ≥ T1, ((alg δ f R v₀).traj ev (t + 1)).cnt c = ((alg δ f R v₀).traj ev t).cnt c := by
    intro t ht
    have h1 := hT1' t ht
    have h2 := hT1' (t + 1) (by omega)
    have h3 := hcntK t (by omega)
    have h4 := hcntK (t + 1) (by omega)
    omega
  -- then the pending operations eventually stop changing
  obtain ⟨T2, hT2, hT2'⟩ := eventually_const_of_antitone
    (fun t => (((alg δ f R v₀).traj ev t).pend c).length) T1 (fun t ht => by
      rcases pend_traj_succ δ f R v₀ t (hbusy t (by omega)) (hcnt t ht) with ⟨h, -⟩ | h
      · simp only [h, le_refl]
      · exact h.le)
  have hstab : ∀ t ≥ T2, ((alg δ f R v₀).traj ev (t + 1)).pend c = ((alg δ f R v₀).traj ev t).pend c ∧
      (ev t ≠ .step c → ((alg δ f R v₀).traj ev (t + 1)).loc c = ((alg δ f R v₀).traj ev t).loc c) := by
    intro t ht
    rcases pend_traj_succ δ f R v₀ t (hbusy t (by omega)) (hcnt t (by omega)) with h | h
    · exact h
    · have h1 := hT2' t ht
      have h2 := hT2' (t + 1) (by omega)
      omega
  have hpendc : ∀ t ≥ T2, ((alg δ f R v₀).traj ev t).pend c = ((alg δ f R v₀).traj ev T2).pend c := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [(hstab t ht).1, ih]
  have hcrash : ∀ t ≥ T2, ∀ p ∈ ((alg δ f R v₀).traj ev t).pend c, δ p.reg ∈ Fs := by
    intro t ht p hp
    rw [hpendc t ht] at hp
    by_contra hδ
    obtain ⟨t', ht', hp'⟩ := hfair.live T2 c p hc hp hδ
    exact hp' (by rw [hpendc t' (by omega)]; exact hp)
  -- every step of `c` after `T2` is the transition to the writing phase
  have hkey : ∀ t ≥ T2, ev t = .step c →
      (∃ v, (((alg δ f R v₀).traj ev t).loc c).mode = .wc v) ∧
        (((alg δ f R v₀).traj ev (t + 1)).loc c).mode = .wp := by
    intro t ht hevt
    have hci := (gi_traj δ f R v₀ ev t).2 c
    have hb := hbusy t (by omega)
    have hb' := hbusy (t + 1) (by omega)
    have hc' := hcnt t (by omega)
    obtain ⟨a, l', hs, hl, hrest⟩ := doStep_self δ f R v₀ ((alg δ f R v₀).traj ev t) c
    have hX : (alg δ f R v₀).traj ev (t + 1) = (alg δ f R v₀).doStep ((alg δ f R v₀).traj ev t) c := by
      rw [traj_succ, hevt]; rfl
    rw [hX] at hb' hc' ⊢
    cases hs with
    | trigW b hb'' => exact absurd (hrest.1 ▸ hc') (by omega)
    | trigR b _ _ _ => exact absurd (hrest.1 ▸ hc') (by omega)
    | retR _ _ _ _ => exact absurd hrest.2.2 hb'
    | retW _ _ _ => exact absurd hrest.2.2 hb'
    | toWp v _ hm _ _ => exact ⟨⟨v, hm⟩, by rw [hl]⟩
    | skip hq hcoll hwp =>
      exfalso
      set l := ((alg δ f R v₀).traj ev t).loc c
      have hidle : l.mode ≠ .idle := fun h => hb ((hci.mode.none_iff).2 h)
      by_cases hcl : l.mode.isColl
      · obtain ⟨hrq, hnd⟩ := hcoll hcl
        apply hnd
        unfold Done
        have hsub : Fsᶜ ⊆ univ.filter fun s => ∀ b, δ b = s → b ∈ l.got := by
          intro s hs
          simp only [mem_filter, mem_univ, true_and]
          intro b hb
          rcases hci.coll hcl b with h1 | h1 | ⟨p, hp, h2, h3⟩
          · rw [hrq] at h1; simp at h1
          · exact h1
          · have := hcrash t (by omega) p hp
            rw [h2, hb] at this
            exact absurd this (mem_compl.1 hs)
        have := card_le_card hsub
        rw [card_compl] at this
        omega
      have hm : l.mode = .wp := by
        rcases hm : l.mode <;> simp_all
      · apply hwp hm
        have hpart := hci.part
        rw [hq, union_empty] at hpart
        have h1 : #(R c) ≤ #l.pw + #l.wr := hpart ▸ card_union_le _ _
        have h2 : #l.pw ≤ #Fs := by
          rw [← card_image_of_injOn ((hinj c).mono (by exact_mod_cast hci.pw_sub))]
          refine card_le_card fun s hs => ?_
          obtain ⟨b, hb, rfl⟩ := mem_image.1 hs
          obtain ⟨p, hp, h2, -⟩ := (hci.pw b).1 hb
          exact h2 ▸ hcrash t (by omega) p hp
        omega
  obtain ⟨t1, ht1, hev1⟩ := hfair.sched c hc T2
  have hwp : ∀ t ≥ t1 + 1, (((alg δ f R v₀).traj ev t).loc c).mode = .wp := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact (hkey t1 ht1 hev1).2
    | succ t ht ih =>
      by_cases he : ev t = .step c
      · obtain ⟨⟨v, hv⟩, -⟩ := hkey t (by omega) he
        rw [ih] at hv; cases hv
      · rw [(hstab t (by omega)).2 he, ih]
  obtain ⟨t2, ht2, hev2⟩ := hfair.sched c hc (t1 + 1)
  obtain ⟨⟨v, hv⟩, -⟩ := hkey t2 (by omega) hev2
  rw [hwp t2 ht2] at hv; cases hv

/-- Wait freedom implies obstruction freedom. -/
theorem obstructionFree (hinj : ∀ c, Set.InjOn δ ↑(R c)) (Wr : Set C) :
    (alg δ f R v₀).ObstructionFree δ f Wr :=
  (waitFree δ f R v₀ hinj).obstructionFree Wr

end Podc.RegisterEmulationSpace.Alg2
