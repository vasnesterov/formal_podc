import Papers.PODC2014.DistributedUniversality.Progress

/-!
# Objects that progress forever (Lemma 6, Corollary 1, Theorem 4(a))
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode}

/-- Object `m` has commits in arbitrarily late rounds. -/
def Exec.InfCommits (e : Exec M n k) (m : Fin k) : Prop :=
  ∀ R, ∃ r, R ≤ r ∧ ∃ t v, CommAt (e.st t) r m v

/-- Pigeonhole over the rounds: at least `ℓ` objects have commits in infinitely many rounds. -/
theorem Exec.infCommits_set (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) (e : Exec M n k) :
    ∃ T : Finset (Fin k), M.ℓ ≤ T.card ∧ ∀ x ∈ T, e.InfCommits x := by
  classical
  refine ⟨Finset.univ.filter e.InfCommits, ?_, fun x hx => (Finset.mem_filter.1 hx).2⟩
  by_contra hlt
  have hfin : ∀ x, ¬ e.InfCommits x → ∃ R, ∀ r, R ≤ r → ∀ t v, ¬ CommAt (e.st t) r x v := by
    intro x hx
    unfold Exec.InfCommits at hx
    push Not at hx
    obtain ⟨R, hR⟩ := hx
    exact ⟨R, fun r hr t v hc => hR r hr t v hc⟩
  let Rf : Fin k → ℕ := fun x => if h : e.InfCommits x then 0 else (hfin x h).choose
  let R0 := max 1 (Finset.univ.sup Rf)
  obtain ⟨t, S, hS, hSx⟩ := e.round_commits hℓ hℓk (r := R0) (le_max_left _ _)
  have hsub : S ⊆ Finset.univ.filter e.InfCommits := by
    intro x hxS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hx
    obtain ⟨v, hv⟩ := hSx x hxS
    have hle : Rf x ≤ R0 := le_trans (Finset.le_sup (Finset.mem_univ x)) (le_max_right _ _)
    have := (hfin x hx).choose_spec R0 (by simpa [Rf, hx] using hle) t v
    exact this hv
  exact hlt (hS.trans (Finset.card_le_card hsub))

/-- **Lemma 6.** An object with commits in arbitrarily late rounds executes infinitely many
operations: its sequence of operations `G m` grows without bound. -/
theorem Exec.G_unbounded (hℓ : 1 ≤ M.ℓ) (hk : 0 < k) (hM : M.Good) (e : Exec M n k) {x : Fin k}
    (hx : e.InfCommits x) : ∀ N, ∃ t, N ≤ ((e.st t).G x).length := by
  classical
  -- choose a sequence of commit rounds, two apart
  let pick : ℕ → ℕ × ℕ × Op n := fun R =>
    ((hx R).choose, (hx R).choose_spec.2.choose, (hx R).choose_spec.2.choose_spec.choose)
  have hpick : ∀ R, R ≤ (pick R).1 ∧ CommAt (e.st (pick R).2.1) (pick R).1 x (pick R).2.2 :=
    fun R => ⟨(hx R).choose_spec.1, (hx R).choose_spec.2.choose_spec.choose_spec⟩
  let g : ℕ → ℕ × ℕ × Op n := fun a => Nat.rec (pick 1) (fun _ p => pick (p.1 + 2)) a
  have hg0 : g 0 = pick 1 := rfl
  have hgs : ∀ a, g (a + 1) = pick ((g a).1 + 2) := fun a => rfl
  have hgc : ∀ a, CommAt (e.st (g a).2.1) (g a).1 x (g a).2.2 := by
    intro a; cases a with
    | zero => rw [hg0]; exact (hpick 1).2
    | succ a => rw [hgs]; exact (hpick _).2
  have hg1 : ∀ a, 1 ≤ (g a).1 := by
    intro a; cases a with
    | zero => rw [hg0]; exact (hpick 1).1
    | succ a => rw [hgs]; have := (hpick ((g a).1 + 2)).1; omega
  have hgmono : ∀ a b, a < b → (g a).1 + 2 ≤ (g b).1 := by
    intro a b hab
    induction b with
    | zero => omega
    | succ b ih =>
      rw [hgs]
      have h1 := (hpick ((g b).1 + 2)).1
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h2 | rfl
      · have := ih h2; omega
      · omega
  intro N
  obtain ⟨i, hi⟩ := e.exists_correct
  obtain ⟨t1, ht1⟩ := e.round_unbounded hℓ hk hi ((Finset.range (N + 1)).sup (fun a => (g a).1) + 2)
  obtain ⟨t, htt1, htt2⟩ : ∃ t, t1 ≤ t ∧ (Finset.range (N + 1)).sup (fun a => (g a).2.1) ≤ t :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  refine ⟨t, ?_⟩
  obtain ⟨I, B, C, D⟩ := Reachable.invAll hM (e.reachable t)
  have hNR := Reachable.noRepeat hM (e.reachable t)
  have hri : ∀ a, a < N + 1 → (g a).1 + 2 ≤ ((e.st t).loc i).r := by
    intro a ha
    have h1 : (g a).1 ≤ (Finset.range (N + 1)).sup (fun a => (g a).1) :=
      Finset.le_sup (f := fun a => (g a).1) (Finset.mem_range.2 ha)
    have h2 := e.round_mono i htt1
    omega
  have hcomm : ∀ a, a < N + 1 → CommAt (e.st t) (g a).1 x (g a).2.2 := by
    intro a ha
    refine e.commAt_mono ?_ (hgc a)
    exact le_trans (Finset.le_sup (f := fun a => (g a).2.1) (Finset.mem_range.2 ha)) htt2
  have hunif : ∀ a, a < N + 1 → Unif (e.st t) (g a).1 x (g a).2.2 := by
    intro a ha
    exact I.unif_of_commAt hM (hcomm a ha) (I.finR_nonempty (i := i) x (hg1 a) (by have := hri a ha; omega))
  have hmem : ∀ a, a < N + 1 → (g a).2.2 ∈ (e.st t).G x := by
    intro a ha
    have := B.know i (g a).1 x _ (hunif a ha) (Or.inl (by have := hri a ha; omega))
    exact (B.hist_G i x).subset this
  have hinj : ∀ a b, a < N + 1 → b < N + 1 → (g a).2.2 = (g b).2.2 → a = b := by
    intro a b ha hb hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · obtain ⟨j, hj⟩ := I.commAt_prop (hcomm b hb)
      exact hNR _ _ _ _ hj _ _ (hgmono a b h1) (hunif a ha) hab.symm
    · obtain ⟨j, hj⟩ := I.commAt_prop (hcomm a ha)
      exact hNR _ _ _ _ hj _ _ (hgmono b a h1) (hunif b hb) hab
  have hcard : ((Finset.range (N + 1)).image (fun a => (g a).2.2)).card = N + 1 := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      exact hinj a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
  have hsub : (Finset.range (N + 1)).image (fun a => (g a).2.2) ⊆ ((e.st t).G x).toFinset := by
    intro o ho
    simp only [Finset.mem_image, Finset.mem_range] at ho
    obtain ⟨a, ha, rfl⟩ := ho
    exact List.mem_toFinset.2 (hmem a ha)
  have h3 := Finset.card_le_card hsub
  rw [hcard] at h3
  have h4 := List.toFinset_card_le ((e.st t).G x)
  omega

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s : St n k}

/-- Process `j` completes (returns) infinitely many operations on object `m`. -/
def Exec.CompletesInf (e : Exec M n k) (j : Fin n) (m : Fin k) : Prop :=
  ∀ N, ∃ c t, N ≤ c ∧ (e.st t).retAt j m c ≠ none

theorem Inv.ret_of_cnt (hI : Inv M s) {j : Fin n} {m : Fin k} {c : ℕ}
    (hc : c + 1 < (s.loc j).cnt m) : s.retAt j m c ≠ none := by
  rcases hI.D.ret_cnt j m c (by omega) with h1 | h1
  · exact h1
  · have := (hI.D.res_cnt j m c h1).1; omega

/-- From an unboundedly growing sequence of operations of an object, some process completes
infinitely many operations on it. -/
theorem Exec.completes_of_G (hM : M.Good) (e : Exec M n k) {x : Fin k}
    (hG : ∀ N, ∃ t, N ≤ ((e.st t).G x).length) : ∃ j, e.CompletesInf j x := by
  classical
  have hn : 0 < n := (e.act 0).proc.pos
  have hstep : ∀ N, ∃ j : Fin n, ∃ t, (e.st t).retAt j x N ≠ none := by
    intro N
    obtain ⟨t, ht⟩ := hG (n * (N + 2) + 1)
    have hI := Reachable.invAll hM (e.reachable t)
    set G := (e.st t).G x
    have hS : G.toFinset.card = G.length := List.toFinset_card_of_nodup (hI.B.G_nodup x)
    obtain ⟨j, -, hj⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := G.toFinset) (t := (Finset.univ : Finset (Fin n))) (f := Prod.fst) (n := N + 2)
      (fun _ _ => Finset.mem_univ _) (by simp; omega)
    set F := G.toFinset.filter (fun o => o.1 = j)
    have hinj : Set.InjOn Prod.snd (F : Set (Op n)) := by
      intro o1 h1 o2 h2 he
      simp only [Finset.coe_filter, Set.mem_setOf_eq, F] at h1 h2
      exact Prod.ext (h1.2.trans h2.2.symm) he
    have hcardF : (F.image Prod.snd).card = F.card := Finset.card_image_of_injOn hinj
    obtain ⟨c, hcF, hc⟩ : ∃ c ∈ F.image Prod.snd, N + 2 ≤ c := by
      by_contra hno
      push Not at hno
      have : F.image Prod.snd ⊆ Finset.range (N + 2) := fun c hc => Finset.mem_range.2 (hno c hc)
      have := Finset.card_le_card this
      simp at this; omega
    obtain ⟨o, hoF, rfl⟩ := Finset.mem_image.1 hcF
    simp only [Finset.mem_filter, List.mem_toFinset, F] at hoF
    obtain ⟨hoG, rfl⟩ := hoF
    obtain ⟨ti, hti⟩ := hI.C.v_G x o hoG
    have := hI.C.inv_cnt _ _ _ _ hti
    exact ⟨o.1, t, hI.ret_of_cnt (by omega)⟩
  choose J hJ using hstep
  obtain ⟨j, hj⟩ := Finite.exists_infinite_fiber J
  refine ⟨j, fun N => ?_⟩
  obtain ⟨N', hN', hge⟩ := (Set.infinite_coe_iff.1 hj).exists_gt N
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hN'
  obtain ⟨t, ht⟩ := hJ N'
  exact ⟨N', t, le_of_lt hge, hN' ▸ ht⟩

/-- **Lemma 6** and the progress part of **Theorem 4(a)**: in every infinite execution of the
construction with `(k, ℓ)`-SC objects (`ℓ = 1`: `k`-SC, Figure 1 / Figure 2), at least `ℓ` objects
execute infinitely many operations. -/
theorem lemma_6 (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) (hM : M.Good) (e : Exec M n k) :
    ∃ T : Finset (Fin k), M.ℓ ≤ T.card ∧ ∀ x ∈ T, ∀ N, ∃ t, N ≤ ((e.st t).G x).length := by
  obtain ⟨T, hT, hx⟩ := e.infCommits_set hℓ hℓk
  exact ⟨T, hT, fun x hxT => e.G_unbounded hℓ (by omega) hM (hx x hxT)⟩

/-- **Corollary 1** (non-blocking) and its `ℓ`-generalization (Theorem 4(a), "ℓ-non-blocking" of
Appendix G): in every infinite execution there are at least `ℓ` objects on each of which some
process completes infinitely many operations. -/
theorem corollary_1 (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) (hM : M.Good) (e : Exec M n k) :
    ∃ T : Finset (Fin k), M.ℓ ≤ T.card ∧ ∀ x ∈ T, ∃ j, e.CompletesInf j x := by
  obtain ⟨T, hT, hx⟩ := lemma_6 hℓ hℓk hM e
  exact ⟨T, hT, fun x hxT => e.completes_of_G hM (hx x hxT)⟩

end Podc.DistributedUniversality
