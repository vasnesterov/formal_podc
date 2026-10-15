import Papers.PODC2016.ComplexityHierarchy.CoreLemma

/-!
# Zhu's induction with packings: Lemmas 6.7 and 7.4 of EGSZ'16

For binary consensus algorithms over `MB R ℓ V`, with a packing capacity `k` such that
`ℓ ≤ k` and either `2ℓ ≤ k` or the algorithm uses single-location writes only:

* `exists_isBlock`: a `k`-packing of a set of covering processes yields a block (`IsBlock`) for
  the set of *fully packed* locations (uses Lemma 7.2, `fullyPacked_of_cov`);
* `zhu_induction` (Lemmas 6.7 / 7.4): if a set `Ps` of at least two processes is bivalent from a
  reachable configuration, a `Ps`-only execution reaches a configuration with a bivalent pair
  `Q ⊆ Ps` and a `k`-packing of the remaining processes `Ps \ Q`.

With `k = ℓ` and single-location writes, "there is an `ℓ`-packing of `Ps \ Q`" is exactly the
paper's "the configuration is at most `ℓ`-covered by `Ps \ Q`" (Section 6); with `k = 2ℓ` it is the
paper's Section 7 notion.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

variable {R V P L : Type} [DecidableEq P] [DecidableEq R] {ℓ : ℕ} {I : Impl BinCons (MB R ℓ V) P L}

/-- The locations fully `k`-packed by `Rs` in `C`. -/
def fullSet (I : Impl BinCons (MB R ℓ V) P L) (k : ℕ) (C : Config BinCons (MB R ℓ V) P L)
    (Rs : Finset P) : Set R :=
  {r | FullyPacked (I.MCovers C) k Rs r}

lemma length_filter_toList {α : Type} (T : Finset α) (g : α → Prop) [DecidablePred g] :
    (T.toList.filter (fun x => decide (g x))).length = (T.filter g).card := by
  rw [Finset.card_def, Finset.filter_val, ← Finset.coe_toList T, Multiset.filter_coe,
    Multiset.coe_card]

lemma le_length_wvals {C : Config BinCons (MB R ℓ V) P L} (T : Finset P) (g : P → Prop)
    [DecidablePred g] (r : R) (h : ∀ x ∈ T, g x → I.wOf C x r ≠ none) :
    (T.filter g).card ≤ (wvals (T.toList.map (I.wOf C)) r).length := by
  rw [← length_filter_toList, wvals, List.filterMap_map, List.length_filterMap_eq_countP,
    ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro x hx hgx
  simp only [decide_eq_true_eq] at hgx
  simp only [Function.comp_apply, Option.isSome_iff_ne_none]
  exact h x (Finset.mem_toList.1 hx) hgx

/-- A packing yields a block for the fully packed locations. -/
theorem exists_isBlock [Fintype R] {k : ℕ} (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k)
    (h2 : 2 * ℓ ≤ k ∨ I.SingleWrites) {C : Config BinCons (MB R ℓ V) P L} {Rs : Finset P}
    {π : P → R} (hπ : IsPacking (I.MCovers C) k Rs π) :
    ∃ T1 T2 : List P, IsBlock I C (fullSet I k C Rs) T1 T2 ∧ ∀ x ∈ T1 ++ T2, x ∈ Rs := by
  classical
  obtain ⟨T1, T2, h1, h2', hd, hf1, hf2, hcnt⟩ := exists_blocks hπ hk (ℓ := ℓ)
  have hmem : ∀ x ∈ T1.toList ++ T2.toList, x ∈ Rs := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact h1 (Finset.mem_toList.1 h)
    · exact h2' (Finset.mem_toList.1 h)
  have hfull : ∀ x ∈ T1.toList ++ T2.toList, FullyPacked (I.MCovers C) k Rs (π x) := by
    intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hf1 x (Finset.mem_toList.1 h)
    · exact hf2 x (Finset.mem_toList.1 h)
  -- a process packed into `r` writes `r`
  have hw : ∀ x ∈ Rs, ∀ r, π x = r → I.wOf C x r ≠ none := by
    intro x hx r e
    obtain ⟨w, hw, hr⟩ := hπ.1 x hx
    rw [hw.wOf_eq, ← e]; exact hr
  refine ⟨T1.toList, T2.toList, ⟨?_, fun x hx => ?_, fun x hx => ?_, fun r hr => ?_, ?_⟩, hmem⟩
  · exact (Finset.nodup_toList _).append (Finset.nodup_toList _) (by
      intro a ha hb
      exact Finset.disjoint_left.1 hd (Finset.mem_toList.1 ha) (Finset.mem_toList.1 hb))
  · obtain ⟨w, hw, -⟩ := hπ.1 x (hmem x hx); exact ⟨w, hw⟩
  · intro w k' hk' r hr
    have hcov : I.MCovers C x r := ⟨w, ⟨(hπ.1 x (hmem x hx)).choose_spec.1.1, k', hk'⟩, hr⟩
    exact fullyPacked_of_cov hπ (hmem x hx) (hfull x hx) hcov
  · have hc := (hcnt r (show FullyPacked _ _ _ r from hr)).1
    have hle := le_length_wvals (I := I) (C := C) T1 (fun x => π x = r) r
      (fun x hx e => hw x (h1 hx) r e)
    exact ⟨fun he => by rw [he, List.length_nil] at hle; omega, by omega⟩
  · rcases h2 with h2 | h2
    · right; intro r hr
      have hc := (hcnt r (show FullyPacked _ _ _ r from hr)).2
      have hle := le_length_wvals (I := I) (C := C) T2 (fun x => π x = r) r
        (fun x hx e => hw x (h2' hx) r e)
      exact ⟨fun he => by rw [he, List.length_nil] at hle; omega, by omega⟩
    · left; exact h2

/-! ### Inserting an undetectable solo run (the splicing step of Lemmas 6.7 / 7.4) -/

/-- `a` is a (multiple) assignment writing some location outside `Lset`. -/
def WritesOutside (Lset : Set R) (a : Action BinCons (MB R ℓ V) L) : Prop :=
  ∃ w k r, a = .access () (.write w) k ∧ w r ≠ none ∧ r ∉ Lset

lemma soloStep_mem_out {z : P} {W : Config BinCons (MB R ℓ V) P L} {Lset : Set R}
    (h : ¬ WritesOutside Lset (I.act z (W.loc z))) :
    ∀ r ∉ Lset, (I.soloStep z W).mem () r = W.mem () r := by
  intro r hr
  unfold soloStep
  split_ifs with hp
  · rfl
  obtain ⟨W', hW'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome W z hp)
  rw [hW', Option.getD_some]
  have hlab := I.nextLabel_proc W z
  have hst := nextLabel_isStep (I := I) W z
  cases hl : I.nextLabel W z with
  | inv q o => rw [hl] at hst; exact absurd hst (by simp [Label.IsStep])
  | ret q u => rw [hl] at hW'; rw [(step_ret hW').2.2.1]
  | tau q =>
    rw [hl] at hW' hlab
    simp only [Label.proc] at hlab; subst hlab
    rcases step_tau_cases hW' with ⟨r', k, -, hm⟩ | ⟨w, ⟨-, k, hk⟩, hm⟩
    · rw [hm]
    · rw [hm]
      have hwr : w r = none := by
        by_contra hne; exact h ⟨w, k, r, hk, hne, hr⟩
      simp [applyW, hwr]

lemma iterate_soloStep_mem_out (z : P) (W : Config BinCons (MB R ℓ V) P L) (Lset : Set R)
    (m : ℕ) (h : ∀ j < m, ¬ WritesOutside Lset (I.act z (((I.soloStep z)^[j] W).loc z))) :
    ∀ r ∉ Lset, ((I.soloStep z)^[m] W).mem () r = W.mem () r := by
  induction m with
  | zero => intro r _; rfl
  | succ m ih =>
    intro r hr
    rw [Function.iterate_succ_apply', soloStep_mem_out (h m (by omega)) r hr]
    exact ih (fun j hj => h j (by omega)) r hr

/-- **Splicing.** Let `z ∉ S` be pending in a reachable configuration `X`, let `T1` be the first
half of a block for `Lset` in `X` (with `T1 ⊆ S`), and let `S` be bivalent after the block write
`T1`. Then `z` can run solo until it covers a location outside `Lset`, and performing the block
write `T1` afterwards hides all of `z`'s steps from `S`. -/
theorem exists_splice (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF)
    {X X₁ : Config BinCons (MB R ℓ V) P L} (hX : I.Reach X) {z : P} (hz : X.pend z ≠ none)
    {S : Set P} (hzS : z ∉ S) {Lset : Set R} {T1 T2 : List P} (hB : IsBlock I X Lset T1 T2)
    (hT : ∀ x ∈ T1, x ∈ S) (h₁ : I.runFrom X (blockWrite T1) = some X₁) (hb : I.Bivalent S X₁) :
    ∃ Y Y₁, I.ReachBy {z} X Y ∧ I.runFrom Y (blockWrite T1) = some Y₁ ∧ AgreeOn S X₁ Y₁ ∧
      Y₁.loc z = Y.loc z ∧ Y₁.pend z = Y.pend z ∧ ∃ r₀ ∉ Lset, I.MCovers Y z r₀ := by
  classical
  have hX' := hX
  obtain ⟨α, hα, h1, -⟩ := hX'
  have hfin := hof α X z hα h1 hz
  obtain ⟨m, hbefore, hstop⟩ := I.exists_solo_until z X (WritesOutside Lset) hfin
  set Y := (I.soloStep z)^[m] X with hYdef
  have hrun : I.runFrom X (I.soloLabels z X m) = some Y := I.runFrom_soloLabels z X m
  have hsteps : Steps {z} (I.soloLabels z X m) := soloLabels_steps z X m
  have hYmem := iterate_soloStep_mem_out z X Lset m (fun j hj => (hbefore j hj).2)
  have hYoth : ∀ q ∈ S, X.loc q = Y.loc q ∧ X.pend q = Y.pend q := fun q hq =>
    have := I.iterate_soloStep_other (p := z) (q := q) (by rintro rfl; exact hzS hq) X m
    ⟨this.1.symm, this.2.symm⟩
  have hT1 : ∀ x ∈ T1, x ∈ T1 ++ T2 := fun x hx => by simp [hx]
  obtain ⟨X', Y₁, e1, hY₁, hag⟩ := I.block_agreeOn (S := S) (X := X) (Y := Y) T1
    (hB.nodup.sublist (List.sublist_append_left _ _)) hT (fun x hx => hB.poised x (hT1 x hx))
    (fun q hq => (hYoth q hq).1) (fun q hq => (hYoth q hq).2) (fun r => by
      by_cases hr : r ∈ Lset
      · exact Or.inr (hB.cnt1 r hr)
      · exact Or.inl (hYmem r hr).symm)
  rw [h₁] at e1; cases e1
  have hzT : ∀ ℓ' ∈ (blockWrite T1 : List (Label P BinCons)), ℓ'.proc ≠ z := by
    intro ℓ' hℓ' e
    simp only [blockWrite, List.mem_map] at hℓ'
    obtain ⟨x, hx, rfl⟩ := hℓ'
    exact hzS (e ▸ hT x hx)
  have hzY := I.runFrom_other hY₁ hzT
  by_cases hret : Y.pend z = none
  · -- `z` decided some `u`: contradiction with the bivalence of `S` after the block
    exfalso
    have hc := I.runFrom_counts hrun z 1 0 (Or.inr ⟨hz, rfl⟩)
    rw [I.opsOf_soloLabels] at hc
    simp only [hret, List.length_nil, Nat.add_zero, Nat.zero_add, true_and, ne_eq,
      not_true_eq_false, false_and, or_false] at hc
    obtain ⟨u, hu⟩ : ∃ u, u ∈ respsOf (I.soloLabels z X m) z := by
      match h : respsOf (I.soloLabels z X m) z with
      | [] => rw [h] at hc; simp at hc
      | x :: _ => exact ⟨x, by simp⟩
    have hnu : I.CanDecide S Y₁ (!u) := by
      have := canDecide_of_agreeOn hag (show I.CanDecide S X₁ (!u) by cases u; exacts [hb.2, hb.1])
      exact this
    have := hX.decides_canDecide_eq hS
      (Q := {z} ∪ S) (β := I.soloLabels z X m ++ blockWrite T1)
      ((hsteps.mono Set.subset_union_left).append
        ((steps_blockWrite hT).mono Set.subset_union_right))
      (by rw [I.runFrom_append_of_eq hrun, hY₁])
      ⟨z, List.mem_append_left _ (mem_respsOf_iff.1 hu)⟩ hnu
    cases u <;> simp at this
  · obtain ⟨w, k, r₀, hk, hr₀, hr₀L⟩ := hstop.resolve_left hret
    exact ⟨Y, Y₁, ⟨_, hsteps, hrun⟩, hY₁, hag, hzY.1, hzY.2, r₀, hr₀L, w, ⟨hret, k, hk⟩, hr₀⟩

/-! ### The induction -/

/-- **Lemmas 6.7 and 7.4** of Ellen–Gelashvili–Shavit–Zhu (Zhu's induction): if a set `Ps` of at
least two processes is bivalent from a reachable configuration `C`, then a `Ps`-only execution from
`C` reaches a configuration `C'` with a pair `Q ⊆ Ps` that is bivalent from `C'` and a `k`-packing
of the remaining processes `Ps \ Q` in `C'`. -/
theorem zhu_induction (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) [Fintype R]
    [Nonempty R] {k : ℕ} (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) (h2 : 2 * ℓ ≤ k ∨ I.SingleWrites) :
    ∀ n, 2 ≤ n → ∀ (Ps : Finset P), Ps.card = n → ∀ C, I.Reach C → I.Bivalent Ps C →
      ∃ C', I.ReachBy Ps C C' ∧ ∃ Q ⊆ Ps, Q.card = 2 ∧ I.Bivalent Q C' ∧
        ∃ π, IsPacking (I.MCovers C') k (Ps \ Q) π := by
  classical
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro Ps hPs C _ hb
    exact ⟨C, ReachBy.refl _ _, Ps, subset_rfl, hPs, hb, fun _ => Classical.arbitrary R,
      by simp, fun r => by simp [packCount]⟩
  | succ n hn ih =>
    intro Ps hPs C hC hb
    obtain ⟨D, hCD, q₀, hq₀, q₁, hq₁, hd₀, hd₁⟩ := hC.exists_two_deciders hS hof Ps hb
    have hD : I.Reach D := hC.reachBy hCD
    have hne : q₀ ≠ q₁ := by
      rintro rfl; have := hD.canDecide_self_unique hd₀ hd₁; simp at this
    obtain ⟨z, hzPs, hz0, hz1⟩ : ∃ z ∈ Ps, z ≠ q₀ ∧ z ≠ q₁ := by
      by_contra hc
      have hsub : Ps ⊆ {q₀, q₁} := by
        intro x hx
        by_contra hx'
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
        exact hc ⟨x, hx, hx'⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at this; omega
    set Ps' := Ps.erase z with hPs'def
    have hPs' : Ps'.card = n := by rw [Finset.card_erase_of_mem hzPs, hPs]; simp
    have hzPs' : z ∉ Ps' := Finset.notMem_erase z Ps
    have hPs'Ps : Ps' ⊆ Ps := Finset.erase_subset z Ps
    have hPs'PsS : (Ps' : Set P) ⊆ Ps := by simpa using hPs'Ps
    have hbD : I.Bivalent Ps' D := bivalent_of_canDecide (v := false)
      (by simpa [hPs'def] using And.intro hq₀ (Ne.symm hz0))
      (by simpa [hPs'def] using And.intro hq₁ (Ne.symm hz1)) hd₀ hd₁
    have hpendD := hD.pend_of_bivalent hS hbD
    -- stages of the construction
    let Good : Config BinCons (MB R ℓ V) P L → Finset P → (P → R) → Prop := fun X Q π =>
      I.ReachBy Ps' D X ∧ Q ⊆ Ps' ∧ Q.card = 2 ∧ I.Bivalent Q X ∧
        IsPacking (I.MCovers X) k (Ps' \ Q) π
    have hstep : ∀ X Q π, Good X Q π → ∃ (Xξ X₁ : Config BinCons (MB R ℓ V) P L)
        (T1 T2 : List P), I.ReachBy Ps' X Xξ ∧ IsBlock I Xξ (fullSet I k X (Ps' \ Q)) T1 T2 ∧
        (∀ x ∈ T1 ++ T2, x ∈ Ps') ∧ I.runFrom Xξ (blockWrite T1) = some X₁ ∧
        I.Bivalent Ps' X₁ ∧ ∃ X' Q' π', I.ReachBy Ps' X₁ X' ∧ Good X' Q' π' := by
      intro X Q π ⟨hDX, hQ, hQc, hbQ, hπ⟩
      have hX : I.Reach X := hD.reachBy hDX
      have hcoe : (↑Q ∪ ↑(Ps' \ Q) : Set P) = ↑Ps' := by
        rw [← Finset.coe_union, Finset.union_sdiff_of_subset hQ]
      have hfinish : ∀ {Xξ X₁ : Config BinCons (MB R ℓ V) P L} {T1 : List P}, I.ReachBy Ps' X Xξ →
          (∀ x ∈ T1, x ∈ Ps') → I.runFrom Xξ (blockWrite T1) = some X₁ → I.Bivalent Ps' X₁ →
          ∃ X' Q' π', I.ReachBy Ps' X₁ X' ∧ Good X' Q' π' := by
        intro Xξ X₁ T1 h1 hT h3 h4
        have hX₁ : I.ReachBy Ps' D X₁ := (hDX.trans h1).trans ⟨_, steps_blockWrite hT, h3⟩
        obtain ⟨X', hX', Q', hQ', hQ'c, hbQ', π', hπ'⟩ :=
          ih Ps' hPs' X₁ (hD.reachBy hX₁) h4
        exact ⟨X', Q', π', hX', hX₁.trans hX', hQ', hQ'c, hbQ', hπ'⟩
      by_cases hR : (Ps' \ Q).Nonempty
      · obtain ⟨p, hp⟩ := hR
        obtain ⟨T1, T2, hB, hT⟩ := exists_isBlock hℓ hk h2 hπ
        obtain ⟨ξ, Xξ, X₁, hξ, hXξ, hX₁, hb₁, -⟩ := key_lemma hS hof hX Finset.disjoint_sdiff
          hbQ hB hT hp
        rw [hcoe] at hb₁
        have hrξ : I.ReachBy Q X Xξ := ⟨ξ, hξ, hXξ⟩
        have hB' : IsBlock I Xξ (fullSet I k X (Ps' \ Q)) T1 T2 := hB.congr
          (fun x hx => ((hrξ.other (by simpa using (Finset.mem_sdiff.1 (hT x hx)).2)).1).symm)
          (fun x hx => ((hrξ.other (by simpa using (Finset.mem_sdiff.1 (hT x hx)).2)).2).symm)
        have hT' : ∀ x ∈ T1 ++ T2, x ∈ Ps' := fun x hx => (Finset.mem_sdiff.1 (hT x hx)).1
        have hrξ' : I.ReachBy Ps' X Xξ := hrξ.mono (by simpa using hQ)
        exact ⟨Xξ, X₁, T1, T2, hrξ', hB', hT', hX₁, hb₁,
          hfinish hrξ' (fun x hx => hT' x (by simp [hx])) hX₁ hb₁⟩
      · have hemp : Ps' \ Q = ∅ := Finset.not_nonempty_iff_eq_empty.1 hR
        have hnone : ∀ r, r ∉ fullSet I k X (Ps' \ Q) := by
          intro r hr
          have := hr π hπ
          rw [hemp] at this; simp [packCount] at this; omega
        have hb₁ : I.Bivalent Ps' X := hbQ.mono (by simpa using hQ)
        exact ⟨X, X, [], [], ReachBy.refl _ _,
          ⟨by simp, by simp, by simp, fun r hr => absurd hr (hnone r), Or.inr fun r hr =>
            absurd hr (hnone r)⟩, by simp, rfl, hb₁,
          hfinish (T1 := []) (ReachBy.refl _ _) (fun x hx => by simp at hx) rfl hb₁⟩
    -- the infinite sequence of stages
    obtain ⟨X₀, hDX₀, Q₀, hQ₀, hQ₀c, hbQ₀, π₀, hπ₀⟩ := ih Ps' hPs' D hD hbD
    let St := {s : Config BinCons (MB R ℓ V) P L × Finset P × (P → R) // Good s.1 s.2.1 s.2.2}
    have hstep' : ∀ s : St, ∃ (Xξ X₁ : Config BinCons (MB R ℓ V) P L) (T1 T2 : List P) (s' : St),
        I.ReachBy Ps' s.1.1 Xξ ∧ IsBlock I Xξ (fullSet I k s.1.1 (Ps' \ s.1.2.1)) T1 T2 ∧
        (∀ x ∈ T1 ++ T2, x ∈ Ps') ∧ I.runFrom Xξ (blockWrite T1) = some X₁ ∧
        I.Bivalent Ps' X₁ ∧ I.ReachBy Ps' X₁ s'.1.1 := by
      intro s
      obtain ⟨Xξ, X₁, T1, T2, h1, h2, h3, h4, h5, X', Q', π', h6, h7⟩ :=
        hstep s.1.1 s.1.2.1 s.1.2.2 s.2
      exact ⟨Xξ, X₁, T1, T2, ⟨(X', Q', π'), h7⟩, h1, h2, h3, h4, h5, h6⟩
    choose Xξf X₁f T1f T2f nxt hr1 hblk hTf hrun hbiv hr2 using hstep'
    let s₀ : St := ⟨(X₀, Q₀, π₀), hDX₀, hQ₀, hQ₀c, hbQ₀, hπ₀⟩
    let seq : ℕ → St := fun i => nxt^[i] s₀
    have hseq : ∀ i, seq (i + 1) = nxt (seq i) := fun i => Function.iterate_succ_apply' _ _ _
    have hnext : ∀ s : St, I.ReachBy Ps' s.1.1 (nxt s).1.1 := fun s =>
      ((hr1 s).trans ⟨_, steps_blockWrite (fun x hx => hTf s x (by simp [hx])), hrun s⟩).trans
        (hr2 s)
    have hlater : ∀ i j, i < j → I.ReachBy Ps' (X₁f (seq i)) (seq j).1.1 := by
      intro i j hij
      induction j, hij using Nat.le_induction with
      | base => rw [hseq]; exact hr2 _
      | succ j _ ihj => rw [hseq]; exact ihj.trans (hnext _)
    -- pigeonhole on the sets of fully packed locations
    let Lf : ℕ → Finset R := fun i =>
      Finset.univ.filter (fun r => r ∈ fullSet I k (seq i).1.1 (Ps' \ (seq i).1.2.1))
    obtain ⟨a, b, hab, hLab⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card (Finset R) + 1) => Lf i) (by simp)
    wlog hlt : (a : ℕ) < b generalizing a b
    · exact this b a hab.symm hLab.symm (by
        rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
        · exact absurd h hlt
        · exact h)
    have hLeq : fullSet I k (seq a).1.1 (Ps' \ (seq a).1.2.1) =
        fullSet I k (seq b).1.1 (Ps' \ (seq b).1.2.1) := by
      ext r
      have := congrArg (r ∈ ·) hLab
      simpa [Lf] using this
    -- splicing a solo run of `z` into stage `a`
    set sa := seq a
    have hDXξ : I.ReachBy Ps' D (Xξf sa) := sa.2.1.trans (hr1 sa)
    have hzξ : (Xξf sa).pend z ≠ none := by
      rw [(hDXξ.other (by simpa using hzPs')).2]; exact hpendD z
    obtain ⟨Y, Y₁, hY, hY₁, hag, hzl, hzp, r₀, hr₀, hcov⟩ := exists_splice hS hof
      (hD.reachBy hDXξ) hzξ (S := Ps') (by simpa using hzPs') (hblk sa)
      (fun x hx => hTf sa x (by simp [hx])) (hrun sa) (hbiv sa)
    obtain ⟨β, hβ, hβrun⟩ := hlater a b hlt
    obtain ⟨Z, hZ, hagZ⟩ := I.runFrom_agreeOn hag (fun ℓ' hℓ' => hβ.proc hℓ') hβrun
    have hzZ := I.runFrom_other hZ (hβ.proc_ne (by simpa using hzPs'))
    have hcovZ : I.MCovers Z z r₀ :=
      hcov.congr (by rw [hzZ.1, hzl]) (by rw [hzZ.2, hzp])
    have hgb := (seq b).2
    set Xb := (seq b).1.1 with hXb
    set Qb := (seq b).1.2.1 with hQbdef
    obtain ⟨hDXb, hQb, hQbc, hbQb, hπb⟩ := hgb
    have hbZ : I.Bivalent Qb Z := bivalent_of_agreeOn (hagZ.mono (by simpa using hQb)) hbQb
    have hr₀' : ¬ FullyPacked (I.MCovers Z) k (Ps' \ Qb) r₀ := by
      intro h
      apply hr₀
      rw [hLeq]
      show FullyPacked (I.MCovers Xb) k (Ps' \ Qb) r₀
      refine (fullyPacked_congr (fun x hx r => ?_)).1 h
      exact mCovers_iff_of_eq (I := I) (hagZ.loc x (by simpa using (Finset.mem_sdiff.1 hx).1)).symm
        (hagZ.pend x (by simpa using (Finset.mem_sdiff.1 hx).1)).symm r
    obtain ⟨σ, hσ, hσr⟩ : ∃ σ, IsPacking (I.MCovers Z) k (Ps' \ Qb) σ ∧
        packCount (Ps' \ Qb) σ r₀ < k := by
      by_contra hc
      apply hr₀'
      intro σ hσ
      have := hσ.2 r₀
      by_contra hne
      exact hc ⟨σ, hσ, lt_of_le_of_ne this hne⟩
    have hzQb : z ∉ Qb := fun h => hzPs' (hQb h)
    have hins := isPacking_insert hσ hσr (by simp [hzPs']) hcovZ
    have hset : insert z (Ps' \ Qb) = Ps \ Qb := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_sdiff, hPs'def, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨⟨-, hx⟩, hxQ⟩)
        · exact ⟨hzPs, hzQb⟩
        · exact ⟨hx, hxQ⟩
      · rintro ⟨hx, hxQ⟩
        by_cases hxz : x = z
        · exact Or.inl hxz
        · exact Or.inr ⟨⟨hxz, hx⟩, hxQ⟩
    rw [hset] at hins
    refine ⟨Z, ?_, Qb, hQb.trans hPs'Ps, hQbc, hbZ, _, hins⟩
    exact hCD.trans (((hDXξ.mono hPs'PsS).trans (hY.mono (by simpa using hzPs))).trans
      (ReachBy.of_steps ((steps_blockWrite (S := (Ps' : Set P)) (ps := T1f sa)
        (fun x hx => hTf sa x (by simp [hx]))).append hβ |>.mono
        hPs'PsS) (by rw [I.runFrom_append_of_eq hY₁, hZ])))

end Cslib.SharedMemory.ComplexityHierarchy
