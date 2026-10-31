import Papers.PODC2024.AnonymousCoverings.WaitFree

/-!
# Safety of the snapshot algorithm (Section 5.3)

**Theorem** (`snapshot_safety`, Section 5.3.2 of the paper): in every execution of the snapshot
algorithm (Figure 3) with `N` processors, at least `N` registers and termination level `L ≥ N - 1`,
the views of any two terminated processors are related by containment. The paper's setting
(`N` registers, `L = N`) is `snapshot_safety_paper`; `L = N - 1` is the claim of the paper's
footnote 4.

The paper's induction (Definition 5.1, Lemmas 5.2–5.8) does not go through as printed (see
`differencies.md`). We give a different, complete proof. Write `R_W(t)` (`regsW`) for the
registers whose view contains `W` at time `t`, `H_W(t)` (`procsW`) for the processors whose view
contains `W`, and call `W` *durable* at `t` (`Durable`) if `|R_W(t)| + |H_W(t)| > N`.

* **Persistence** (`durable_scan`): if `W` is durable at `t₀`, every scan that *starts* at or after
  `t₀` ends with a view containing `W`. (First-completing-scan counting argument: each register
  of `R_W(t₀)` must be overwritten by a distinct processor outside `H_W(t₀)` before that scan
  reads it.)
* **Chain** (`chain`): let `(y, s, c)` be a scan ending with view `W` and level `≥ k + 1`. If `W` is
  not durable at `s + 1`, some register is rewritten during the scan by a processor `x` with view
  `W`, and (if `k ≥ 1`) one of these processors performed a scan with view `W` and level `≥ k`
  entirely inside `(s, c)`; otherwise the last writers would all hold `W` at `s + 1` and be
  distinct, making `W` durable. Iterating collects distinct processors with view `W`; with
  `L ≥ N - 1` and one more processor that never has view `W`, the chain must reach a scan with
  view `W` at whose start `W` is durable.
* **Safety**: for incomparable terminated views `W`, `W'` we get scans with views `W`, `W'` at
  whose starts `W`, resp. `W'`, are durable. By persistence each starts before the other: absurd.
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R V : Type*} [DecidableEq P] [DecidableEq R] [Fintype R] [Nonempty R] [DecidableEq V]

namespace Exec

variable {L : ℕ} (e : Exec (P := P) (snapshot (R := R) (V := V) L))

/-- `y` performs the scan `(s, c]`: it writes at time `s`, completes the scan at time `c`, and is
scanning at every time in `(s, c]`. -/
def IsScan (y : P) (s c : ℕ) : Prop :=
  (∃ r₀, e.act s = .write y r₀) ∧ s < c ∧ e.Completes c y ∧
    ∀ t, s < t → t ≤ c → (e.loc t y).scan ≠ none

/-- `R_W(t)`: the registers whose view contains `W` at time `t`. -/
def regsW (W : Finset V) (t : ℕ) : Finset R :=
  univ.filter fun r => W ⊆ (e.reg t r).val.1

/-- `H_W(t)`: the processors whose view contains `W` at time `t`. -/
def procsW [Fintype P] (W : Finset V) (t : ℕ) : Finset P :=
  univ.filter fun x => W ⊆ (e.loc t x).d.view

/-- `W` is *durable* at `t`: more registers and processors contain `W` than there are
processors, i.e. `|R_W(t)| > |P \ H_W(t)|`. This is the paper's Definition 5.1 with `Q = P`,
except that scanning processors that have not yet read `R_W` are not exempted (a stronger
condition). -/
def Durable [Fintype P] (W : Finset V) (t : ℕ) : Prop :=
  Fintype.card P < (e.regsW W t).card + (e.procsW W t).card

/-! ### Basic facts about Figure 3 -/

theorem snap_view_mono_le {t t' : ℕ} (h : t ≤ t') (p : P) :
    (e.loc t p).d.view ⊆ (e.loc t' p).d.view := by
  induction t', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ t' _ ih => exact ih.trans (e.snap_view_mono t' p)

/-- A write stores the writer's view and level. -/
theorem snap_write_val {w : ℕ} {x : P} {r : R} (h : e.act w = .write x r) :
    (e.reg (w + 1) r).val = ((e.loc w x).d.view, (e.loc w x).d.level) := by
  rw [(e.write_spec h).2.2.2.1]; rfl

/-- If `r` is written during `[t, g)`, its content at `g` is the one stored by some write in
`[t, g)` (the last one). -/
theorem exists_last_write_before {t g : ℕ} {r : R}
    (h : ∃ w, t ≤ w ∧ w < g ∧ ∃ x, e.act w = .write x r) :
    ∃ w, t ≤ w ∧ w < g ∧ ∃ x, e.act w = .write x r ∧ e.reg (w + 1) r = e.reg g r := by
  induction g with
  | zero => obtain ⟨w, -, hw, -⟩ := h; omega
  | succ g ih =>
    by_cases hg : ∃ x, e.act g = .write x r
    · obtain ⟨x, hx⟩ := hg
      obtain ⟨w, hw1, hw2, -⟩ := h
      exact ⟨g, by omega, by omega, x, hx, rfl⟩
    · push Not at hg
      obtain ⟨w, hw1, hw2, x, hx⟩ := h
      have hwg : w ≠ g := by rintro rfl; exact hg x hx
      obtain ⟨w', h1, h2, x', h3, h4⟩ := ih ⟨w, hw1, by omega, x, hx⟩
      exact ⟨w', h1, by omega, x', h3, by rw [h4, e.reg_succ_of_not_write hg]⟩

/-- The scan started by a write ends before the processor is next at the write label. -/
theorem exists_isScan_of_write {w w' : ℕ} {x : P} {r : R} (hw : e.act w = .write x r)
    (hww : w < w') (h' : (e.loc w' x).scan = none) :
    ∃ c, w < c ∧ c < w' ∧ e.IsScan x w c := by
  have hs1 := e.scan_after_write hw
  have hne : w + 1 ≠ w' := by rintro rfl; rw [hs1] at h'; exact absurd h' (by simp)
  obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ :=
    Nat.exists_first_Ioc (Q := fun t => (e.loc t x).scan = none) (s := w + 1) (B := w')
      (by rw [hs1]; simp) ⟨w', by omega, le_rfl, h'⟩
  exact ⟨c, by omega, by omega, ⟨r, hw⟩, by omega, e.completes_of_scan_none hc3 hc4,
    fun t h1 h2 => hc5 t (by omega) h2⟩

/-- View and level are constant over a period without scan completions. -/
theorem snap_const_of_no_completes {x : P} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ c, a ≤ c → c < b → ¬ e.Completes c x) :
    (e.loc b x).d.view = (e.loc a x).d.view ∧ (e.loc b x).d.level = (e.loc a x).d.level := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ b hb ih =>
    obtain ⟨ih1, ih2⟩ := ih fun c h1 h2 => h c h1 (by omega)
    rcases e.snap_view_level_succ b x with ⟨h3, h4⟩ | ⟨hc, -⟩
    · exact ⟨h3.trans ih1, h4.trans ih2⟩
    · exact absurd hc (h b hb (by omega))

variable {e}

theorem IsScan.not_write {y : P} {s c : ℕ} (h : e.IsScan y s c) {w : ℕ} (h1 : s < w)
    (h2 : w ≤ c) (r : R) : e.act w ≠ .write y r :=
  fun hw => h.2.2.2 w h1 h2 (e.write_spec hw).1

/-- A processor completes at most one scan after a given write before its next write. -/
theorem IsScan.eq_of_start {y : P} {s c c' : ℕ} (h : e.IsScan y s c) (h' : e.IsScan y s c') :
    c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.2.2.2 (c + 1) (by have := h.2.1; omega) (by omega) h.2.2.1.2
  · exact h.2.2.2 (c' + 1) (by have := h'.2.1; omega) (by omega) h'.2.2.1.2

theorem IsScan.reads {y : P} {s c : ℕ} (h : e.IsScan y s c) :
    ∃ g : R → ℕ, (∀ r, s < g r ∧ g r ≤ c ∧ e.act (g r) = .read y r) ∧
      ∃ d : SnapD R V, (e.loc (c + 1) y).d = d.finish ∧ d.view = (e.loc s y).d.view ∧
        d.level = (e.loc s y).d.level ∧ ∀ r, d.got r = (e.reg (g r) r).val := by
  obtain ⟨⟨r₀, hw⟩, hsc, hc, hnc⟩ := h
  exact e.snap_scan_result hw hc hsc hnc

/-- Every value read by a scan is contained in the resulting view. -/
theorem IsScan.read_sub {y : P} {s c : ℕ} (h : e.IsScan y s c) :
    ∃ g : R → ℕ, (∀ r, s < g r ∧ g r ≤ c) ∧
      ∀ r, (e.reg (g r) r).val.1 ⊆ (e.loc (c + 1) y).d.view := by
  obtain ⟨g, hg, d, hd, -, -, hgot⟩ := h.reads
  refine ⟨g, fun r => ⟨(hg r).1, (hg r).2.1⟩, fun r => ?_⟩
  rw [hd, ← hgot r]
  simp only [SnapD.finish, SnapD.unionRead]
  exact (le_sup (f := fun r => (d.got r).1) (mem_univ r)).trans subset_union_right

/-- A scan ending with a positive level read the scanner's (unchanged) view in every register,
with level at least the new level minus one. -/
theorem IsScan.reads_of_level {y : P} {s c : ℕ} (h : e.IsScan y s c)
    (hl : 1 ≤ (e.loc (c + 1) y).d.level) :
    ∃ g : R → ℕ, (∀ r, s < g r ∧ g r ≤ c) ∧ (e.loc (c + 1) y).d.view = (e.loc s y).d.view ∧
      ∀ r, (e.reg (g r) r).val.1 = (e.loc s y).d.view ∧
        (e.loc (c + 1) y).d.level ≤ (e.reg (g r) r).val.2 + 1 := by
  obtain ⟨g, hg, d, hd, hv, -, hgot⟩ := h.reads
  have hall : ∀ r, (d.got r).1 = d.view := by
    by_contra hne
    rw [hd] at hl
    simp only [SnapD.finish, hne, ↓reduceIte] at hl
    omega
  refine ⟨g, fun r => ⟨(hg r).1, (hg r).2.1⟩, ?_, fun r => ⟨?_, ?_⟩⟩
  · rw [hd, ← hv]
    simp only [SnapD.finish, SnapD.unionRead]
    exact union_eq_left.2 (Finset.sup_le fun r _ => (hall r).le)
  · rw [← hgot r, hall r, hv]
  · rw [hd, ← hgot r]
    simp only [SnapD.finish, hall, implies_true, ↓reduceIte]
    have : d.minLevel ≤ (d.got r).2 := Finset.inf'_le _ (mem_univ r)
    omega

variable {input : P → V}

/-- The last scan before time `t` of a processor `x` that is at the write label with a positive
level at `t`: it ends with the view and level of `x` at `t`, it started with the same view, and
every earlier write of `x` is at or before its start. -/
theorem exists_last_scan (he : e.cfg 0 = snapCfg input) {x : P} {t : ℕ}
    (hl : 1 ≤ (e.loc t x).d.level) (hn : (e.loc t x).scan = none) :
    ∃ s c, e.IsScan x s c ∧ c < t ∧ (e.loc (c + 1) x).d.view = (e.loc t x).d.view ∧
      (e.loc (c + 1) x).d.level = (e.loc t x).d.level ∧
      (e.loc s x).d.view = (e.loc t x).d.view ∧
      ∀ w r, w < t → e.act w = .write x r → w ≤ s := by
  have hex : ∃ c, c < t ∧ e.Completes c x := by
    by_contra hno
    push Not at hno
    have := (e.snap_const_of_no_completes (Nat.zero_le t) fun c _ hc => hno c hc).2
    rw [this] at hl
    simp [loc, he, snapCfg, initCfg, snapInit] at hl
  obtain ⟨c₀, hc₀t, hc₀⟩ := hex
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ :=
    Nat.exists_last_of_le (p := fun c => e.Completes c x) (show c₀ ≤ t - 1 by omega) hc₀
  have hct : c < t := by omega
  obtain ⟨hv, hlv⟩ := e.snap_const_of_no_completes (show c + 1 ≤ t by omega)
    fun c' h1 h2 => hc4 c' (by omega) (by omega)
  obtain ⟨s, hsc, hws, hnc⟩ := Exec.snap_exists_scan_start he hc3
  have hscan : e.IsScan x s c := ⟨hws, hsc, hc3, hnc⟩
  obtain ⟨-, -, hvs, -⟩ := hscan.reads_of_level (by rw [← hlv]; exact hl)
  refine ⟨s, c, hscan, hct, hv.symm, hlv.symm, by rw [← hvs, hv], fun w r hw hwr => ?_⟩
  by_contra hsw
  push Not at hsw
  rcases Nat.lt_or_ge c w with hcw | hwc
  · obtain ⟨c', hc'1, hc'2, hc'3⟩ := e.exists_isScan_of_write hwr hw hn
    exact hc4 c' (by omega) (by omega) hc'3.2.2.1
  · exact hscan.not_write hsw hwc r hwr

/-! ### Persistence of durable views -/

/-- **Persistence.** If `W` is durable at `t₀`, then every scan that starts at or after `t₀` ends
with a view containing `W`. (The correct core of the paper's Lemma 5.2.) -/
theorem durable_scan [Fintype P] {W : Finset V} {t₀ : ℕ} (hB : e.Durable W t₀) :
    ∀ c y s, e.IsScan y s c → t₀ ≤ s → W ⊆ (e.loc (c + 1) y).d.view := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro y s hsc hts
  by_contra hW
  obtain ⟨g, hg, hsub⟩ := hsc.read_sub
  -- a processor that writes a value without `W` twice in `[t₀, c)` contradicts minimality
  have once : ∀ x w₁ w₂ r₁ r₂, t₀ ≤ w₁ → w₁ < w₂ → w₂ < c → e.act w₁ = .write x r₁ →
      e.act w₂ = .write x r₂ → ¬ W ⊆ (e.loc w₂ x).d.view → False := by
    intro x w₁ w₂ r₁ r₂ h1 h2 h3 hw₁ hw₂ hW₂
    obtain ⟨c₁, hc₁1, hc₁2, hc₁⟩ := e.exists_isScan_of_write hw₁ h2 (e.write_spec hw₂).1
    exact hW₂ ((ih c₁ (by omega) x w₁ hc₁ h1).trans (e.snap_view_mono_le (by omega) x))
  -- every register of `R_W(t₀)` is rewritten before it is read, by a processor outside `H_W(t₀)`
  have key : ∀ r ∈ e.regsW W t₀, ∃ x, x ∈ (e.procsW W t₀)ᶜ ∧
      ∃ w, t₀ ≤ w ∧ w < c ∧ e.act w = .write x r ∧ ¬ W ⊆ (e.loc w x).d.view := by
    intro r hr
    simp only [regsW, mem_filter, mem_univ, true_and] at hr
    have hgr := hg r
    have hex : ∃ w, t₀ ≤ w ∧ w < g r ∧ ∃ x, e.act w = .write x r := by
      by_contra hno
      push Not at hno
      have heq := e.reg_eq_of_no_write (show t₀ ≤ g r by omega)
        fun w h1 h2 p hp => hno w h1 h2 p hp
      exact hW (hr.trans (by rw [← heq]; exact hsub r))
    obtain ⟨w, hw1, hw2, x, hx, hreg⟩ := e.exists_last_write_before hex
    have hval : (e.loc w x).d.view = (e.reg (g r) r).val.1 := by
      rw [← hreg, e.snap_write_val hx]
    have hxW : ¬ W ⊆ (e.loc w x).d.view := fun h => hW (h.trans (hval ▸ hsub r))
    refine ⟨x, ?_, w, hw1, by omega, hx, hxW⟩
    simp only [procsW, mem_compl, mem_filter, mem_univ, true_and]
    exact fun h => hxW (h.trans (e.snap_view_mono_le hw1 x))
  have hcard : (e.regsW W t₀).card ≤ ((e.procsW W t₀)ᶜ).card := by
    refine card_le_card_of_forall_subsingleton
      (fun r x => ∃ w, t₀ ≤ w ∧ w < c ∧ e.act w = .write x r ∧ ¬ W ⊆ (e.loc w x).d.view)
      (fun r hr => key r hr) ?_
    rintro x - r₁ ⟨-, w₁, h1, h2, h3, h4⟩ r₂ ⟨-, w₂, h5, h6, h7, h8⟩
    rcases lt_trichotomy w₁ w₂ with hlt | heq | hlt
    · exact (once x w₁ w₂ r₁ r₂ h1 hlt h6 h3 h7 h8).elim
    · subst heq; rw [h3] at h7; cases h7; rfl
    · exact (once x w₂ w₁ r₂ r₁ h5 hlt h2 h7 h3 h4).elim
  rw [card_compl] at hcard
  unfold Durable at hB
  have := card_le_univ (e.procsW W t₀)
  omega

/-! ### The chain of nested scans -/

/-- One step of the chain. Let `(y, s, c)` be a scan ending with view `W`, at whose start `W` is
not durable. Then (1) some processor with view `W` writes during `(s, c)`; (2) if the scan ends
with level `≥ k + 2`, some processor with view `W` writing during `(s, c)` completed a scan with
view `W` and level `≥ k + 1` that lies inside `(s, c)`. -/
theorem chain_step [Fintype P] (hR : Fintype.card P ≤ Fintype.card R)
    (he : e.cfg 0 = snapCfg input) {W : Finset V} {y : P} {s c : ℕ} (hsc : e.IsScan y s c)
    (hW : (e.loc (c + 1) y).d.view = W) (hl : 1 ≤ (e.loc (c + 1) y).d.level)
    (hB : ¬ e.Durable W (s + 1)) :
    (∃ x w r, s < w ∧ w < c ∧ e.act w = .write x r ∧ (e.loc w x).d.view = W) ∧
    ∀ k, k + 2 ≤ (e.loc (c + 1) y).d.level →
      ∃ x w r s₁ c₁, s < w ∧ w < c ∧ e.act w = .write x r ∧ (e.loc w x).d.view = W ∧
        e.IsScan x s₁ c₁ ∧ s < s₁ ∧ c₁ < w ∧ (e.loc (c₁ + 1) x).d.view = W ∧
        k + 1 ≤ (e.loc (c₁ + 1) x).d.level := by
  classical
  obtain ⟨g, hg, hvs, hread⟩ := hsc.reads_of_level hl
  rw [hW] at hvs
  -- registers not rewritten during the scan already hold `W` at `s + 1`
  set D : Finset R := univ.filter fun r => ∃ w, s + 1 ≤ w ∧ w < g r ∧ ∃ x, e.act w = .write x r
    with hD
  have hnotD : ∀ r, r ∉ D → r ∈ e.regsW W (s + 1) := by
    intro r hr
    simp only [hD, mem_filter, mem_univ, true_and] at hr
    push Not at hr
    have heq := e.reg_eq_of_no_write (show s + 1 ≤ g r by have := (hg r).1; omega)
      fun w h1 h2 p hp => hr w h1 h2 p hp
    simp only [regsW, mem_filter, mem_univ, true_and]
    rw [← heq, (hread r).1, ← hvs]
  -- the last writer of a register of `D` has view `W` and the level read
  have hlast : ∀ r ∈ D, ∃ w, s + 1 ≤ w ∧ w < g r ∧ ∃ x, e.act w = .write x r ∧
      e.reg (w + 1) r = e.reg (g r) r := by
    intro r hr
    simp only [hD, mem_filter, mem_univ, true_and] at hr
    exact e.exists_last_write_before hr
  have hwval : ∀ r w x, e.act w = .write x r → e.reg (w + 1) r = e.reg (g r) r →
      (e.loc w x).d.view = W ∧ (e.loc (c + 1) y).d.level ≤ (e.loc w x).d.level + 1 := by
    intro r w x hx hreg
    have h1 := e.snap_write_val hx
    rw [hreg] at h1
    refine ⟨?_, ?_⟩
    · have := congrArg Prod.fst h1
      simp only at this
      rw [← this, (hread r).1, ← hvs]
    · have := congrArg Prod.snd h1
      simp only at this
      rw [← this]; exact (hread r).2
  have hy : y ∈ e.procsW W (s + 1) := by
    simp only [procsW, mem_filter, mem_univ, true_and]
    rw [hvs]; exact e.snap_view_mono s y
  have hyc : 1 ≤ (e.procsW W (s + 1)).card := card_pos.2 ⟨y, hy⟩
  have hDc := card_compl D
  have hreg : (Dᶜ).card ≤ (e.regsW W (s + 1)).card :=
    card_le_card fun r hr => hnotD r (mem_compl.1 hr)
  have hDR : D.card ≤ Fintype.card R := card_le_univ D
  refine ⟨?_, fun k hk => ?_⟩
  · -- a disturber exists, otherwise all registers hold `W` at `s + 1`
    by_contra hno
    apply hB
    have hD0 : D = ∅ := by
      refine eq_empty_of_forall_notMem fun r hr => hno ?_
      obtain ⟨w, hw1, hw2, x, hx, hreg⟩ := hlast r hr
      exact ⟨x, w, r, by omega, by have := (hg r).2; omega, hx, (hwval r w x hx hreg).1⟩
    have hD0' : D.card = 0 := by rw [hD0, card_empty]
    unfold Durable
    omega
  · by_contra hno
    apply hB
    -- a write in `[s + 1, g r)` storing the value read, whose writer's last scan starts after `s`,
    -- gives a nested scan
    have nest : ∀ r w x, s + 1 ≤ w → w < g r → e.act w = .write x r →
        e.reg (w + 1) r = e.reg (g r) r → ∀ s₁ c₁, e.IsScan x s₁ c₁ → s < s₁ → c₁ < w →
        (e.loc (c₁ + 1) x).d.view = (e.loc w x).d.view →
        (e.loc (c₁ + 1) x).d.level = (e.loc w x).d.level → False := by
      intro r w x hw1 hw2 hx hreg s₁ c₁ hsc₁ hs₁ hc₁ hv₁ hl₁
      obtain ⟨hvw, hlw⟩ := hwval r w x hx hreg
      exact hno ⟨x, w, r, s₁, c₁, by omega, by have := (hg r).2; omega, hx, hvw, hsc₁, hs₁,
        hc₁, by rw [hv₁, hvw], by omega⟩
    have hlevel : ∀ r w x, e.act w = .write x r → e.reg (w + 1) r = e.reg (g r) r →
        1 ≤ (e.loc w x).d.level := by
      intro r w x hx hreg
      have := (hwval r w x hx hreg).2
      omega
    have hcard : D.card ≤ ((e.procsW W (s + 1)).erase y).card := by
      refine card_le_card_of_forall_subsingleton
        (fun r x => ∃ w, s + 1 ≤ w ∧ w < g r ∧ e.act w = .write x r ∧
          e.reg (w + 1) r = e.reg (g r) r) (fun r hr => ?_) ?_
      · obtain ⟨w, hw1, hw2, x, hx, hreg⟩ := hlast r hr
        refine ⟨x, mem_erase.2 ⟨?_, ?_⟩, w, hw1, hw2, hx, hreg⟩
        · rintro rfl
          exact hsc.not_write (show s < w by omega) (by have := (hg r).2; omega) r hx
        · obtain ⟨s₁, c₁, hsc₁, hc₁, hv₁, hl₁, hvs₁, -⟩ :=
            e.exists_last_scan he (hlevel r w x hx hreg) (e.write_spec hx).1
          simp only [procsW, mem_filter, mem_univ, true_and]
          rcases Nat.lt_or_ge s s₁ with hlt | hle
          · exact (nest r w x hw1 hw2 hx hreg s₁ c₁ hsc₁ hlt hc₁ hv₁ hl₁).elim
          · rw [← (hwval r w x hx hreg).1, ← hvs₁]
            exact e.snap_view_mono_le (by omega) x
      · rintro x - r₁ ⟨-, w₁, h1, h2, h3, h4⟩ r₂ ⟨-, w₂, h5, h6, h7, h8⟩
        have aux : ∀ r₁ r₂ w₁ w₂, s + 1 ≤ w₁ → w₁ < w₂ → s + 1 ≤ w₂ → w₂ < g r₂ →
            e.act w₁ = .write x r₁ → e.act w₂ = .write x r₂ →
            e.reg (w₂ + 1) r₂ = e.reg (g r₂) r₂ → False := by
          intro r₁ r₂ w₁ w₂ h1 hlt h5 h6 h3 h7 h8
          obtain ⟨s₁, c₁, hsc₁, hc₁, hv₁, hl₁, -, hbefore⟩ :=
            e.exists_last_scan he (hlevel r₂ w₂ x h7 h8) (e.write_spec h7).1
          have := hbefore w₁ r₁ hlt h3
          exact nest r₂ w₂ x h5 h6 h7 h8 s₁ c₁ hsc₁ (by omega) hc₁ hv₁ hl₁
        rcases lt_trichotomy w₁ w₂ with hlt | heq | hlt
        · exact (aux r₁ r₂ w₁ w₂ h1 hlt h5 h6 h3 h7 h8).elim
        · subst heq; rw [h3] at h7; cases h7; rfl
        · exact (aux r₂ r₁ w₂ w₁ h5 hlt h1 h2 h7 h3 h4).elim
    rw [card_erase_of_mem hy] at hcard
    unfold Durable
    omega

/-- **Chain of nested scans.** Let `(y, s, c)` be a scan ending with view `W` and level
`≥ k + 1`, let `Y ∋ y` be processors that do not write during `(s, c)`, and `Z` processors, disjoint
from `Y`, that never have view `W`. If `N < |Y| + |Z| + k + 1`, then some scan ending with view
`W` starts at a time `s'` such that `W` is durable at `s' + 1`. -/
theorem chain [Fintype P] (hR : Fintype.card P ≤ Fintype.card R) (he : e.cfg 0 = snapCfg input)
    {W : Finset V} (Z : Finset P) (hZ : ∀ x ∈ Z, ∀ τ, (e.loc τ x).d.view ≠ W) :
    ∀ k (Y : Finset P) (y : P) (s c : ℕ), e.IsScan y s c → (e.loc (c + 1) y).d.view = W →
      k + 1 ≤ (e.loc (c + 1) y).d.level → y ∈ Y →
      (∀ x ∈ Y, ∀ w r, s < w → w < c → e.act w ≠ .write x r) → Disjoint Y Z →
      Fintype.card P < Y.card + Z.card + (k + 1) →
      ∃ y' s' c', e.IsScan y' s' c' ∧ (e.loc (c' + 1) y').d.view = W ∧ e.Durable W (s' + 1) := by
  intro k
  induction k with
  | zero =>
    intro Y y s c hsc hW hl hyY hY hYZ hcard
    by_cases hB : e.Durable W (s + 1)
    · exact ⟨y, s, c, hsc, hW, hB⟩
    obtain ⟨x, w, r, hw1, hw2, hx, hxW⟩ := (chain_step hR he hsc hW (by omega) hB).1
    have hxY : x ∉ Y := fun h => hY x h w r hw1 hw2 hx
    have hxZ : x ∉ Z := fun h => hZ x h w hxW
    have hd : Disjoint (insert x Y) Z := disjoint_insert_left.2 ⟨hxZ, hYZ⟩
    have := card_le_univ (insert x Y ∪ Z)
    rw [card_union_of_disjoint hd, card_insert_of_notMem hxY] at this
    omega
  | succ k ih =>
    intro Y y s c hsc hW hl hyY hY hYZ hcard
    by_cases hB : e.Durable W (s + 1)
    · exact ⟨y, s, c, hsc, hW, hB⟩
    obtain ⟨x, w, r, s₁, c₁, hw1, hw2, hx, hxW, hsc₁, hs₁, hc₁, hv₁, hl₁⟩ :=
      (chain_step hR he hsc hW (by omega) hB).2 k (by omega)
    have hxY : x ∉ Y := fun h => hY x h w r hw1 hw2 hx
    have hxZ : x ∉ Z := fun h => hZ x h w hxW
    refine ih (insert x Y) x s₁ c₁ hsc₁ hv₁ hl₁ (mem_insert_self x Y) ?_
      (disjoint_insert_left.2 ⟨hxZ, hYZ⟩) ?_
    · intro x' hx' w' r' h1 h2
      rcases mem_insert.1 hx' with rfl | hx'
      · exact hsc₁.not_write h1 h2.le r'
      · have := hsc₁.2.1
        exact hY x' hx' w' r' (by omega) (by omega)
    · rw [card_insert_of_notMem hxY]; omega

/-- A terminated processor (at the write label with level `≥ L`) never changes its state. -/
theorem snap_stopped_const {p : P} {t : ℕ} (hl : L ≤ (e.loc t p).d.level)
    (hs : (e.loc t p).scan = none) : ∀ t', t ≤ t' → e.loc t' p = e.loc t p := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => rfl
  | succ t' ht' ih =>
    rw [← ih]
    by_cases hm : e.Moves t' p
    · obtain ⟨r, hr | hr⟩ := hm
      · exact absurd (by rw [ih]; exact hl) (e.write_spec hr).2.2.1
      · obtain ⟨S, hS, -⟩ := e.read_spec hr
        rw [ih, hs] at hS; exact absurd hS (by simp)
    · exact e.loc_succ_of_not_moves hm

end Exec

open Exec

/-- **Safety of the snapshot algorithm (Section 5.3.2 of the paper; footnote 4 for `L = N - 1`).**
With `N` processors, at least `N` registers and termination level `L ≥ N - 1`, any two processors
that have terminated (are at the write label with level `≥ L`) have views related by
containment. -/
theorem snapshot_safety [Fintype P] {L : ℕ} (hR : Fintype.card P ≤ Fintype.card R)
    (hL : Fintype.card P ≤ L + 1) {input : P → V}
    (e : Exec (P := P) (snapshot (R := R) (V := V) L)) (he : e.cfg 0 = snapCfg input)
    (t : ℕ) (p q : P) (hp : L ≤ (e.loc t p).d.level) (hps : (e.loc t p).scan = none)
    (hq : L ≤ (e.loc t q).d.level) (hqs : (e.loc t q).scan = none) :
    (e.loc t p).d.view ⊆ (e.loc t q).d.view ∨ (e.loc t q).d.view ⊆ (e.loc t p).d.view := by
  by_contra hinc
  push Not at hinc
  obtain ⟨h1, h2⟩ := hinc
  have hpq : p ≠ q := by rintro rfl; exact h1 subset_rfl
  have hN : 2 ≤ Fintype.card P := by
    have := card_le_univ ({p, q} : Finset P)
    rwa [card_pair hpq] at this
  -- for each of the two views, a scan with that view at whose start the view is durable
  have aux : ∀ a b : P, a ≠ b → L ≤ (e.loc t a).d.level → (e.loc t a).scan = none →
      ¬ (e.loc t a).d.view ⊆ (e.loc t b).d.view → ¬ (e.loc t b).d.view ⊆ (e.loc t a).d.view →
      ∃ y s c, e.IsScan y s c ∧ (e.loc (c + 1) y).d.view = (e.loc t a).d.view ∧
        e.Durable (e.loc t a).d.view (s + 1) := by
    intro a b hab ha has hab1 hab2
    obtain ⟨s, c, hsc, -, hv, hlv, -, -⟩ := e.exists_last_scan he (by omega) has
    refine e.chain hR he {b} ?_ (L - 1) {a} a s c hsc hv (by omega) (mem_singleton_self a)
      ?_ (disjoint_singleton.2 hab) (by simp only [card_singleton]; omega)
    · intro x hx τ hτ
      rw [mem_singleton] at hx; subst hx
      rcases le_total τ t with hτt | hτt
      · have := e.snap_view_mono_le hτt x
        rw [hτ] at this; exact hab1 this
      · have := e.snap_view_mono_le hτt x
        rw [hτ] at this; exact hab2 this
    · intro x hx w r h1 h2
      rw [mem_singleton] at hx; subst hx
      exact hsc.not_write h1 h2.le r
  obtain ⟨y₁, s₁, c₁, hsc₁, hv₁, hB₁⟩ := aux p q hpq hp hps h1 h2
  obtain ⟨y₂, s₂, c₂, hsc₂, hv₂, hB₂⟩ := aux q p hpq.symm hq hqs h2 h1
  -- by persistence, each of the two scans starts before the other
  have hs₂ : s₂ ≤ s₁ := by
    by_contra hlt
    have := durable_scan hB₁ c₂ y₂ s₂ hsc₂ (by omega)
    rw [hv₂] at this; exact h1 this
  have hs₁ : s₁ ≤ s₂ := by
    by_contra hlt
    have := durable_scan hB₂ c₁ y₁ s₁ hsc₁ (by omega)
    rw [hv₁] at this; exact h2 this
  obtain rfl : s₁ = s₂ := le_antisymm hs₁ hs₂
  obtain rfl : y₁ = y₂ := by
    obtain ⟨r₁, hr₁⟩ := hsc₁.1
    obtain ⟨r₂, hr₂⟩ := hsc₂.1
    rw [hr₁] at hr₂
    injection hr₂
  obtain rfl : c₁ = c₂ := hsc₁.eq_of_start hsc₂
  exact h1 (by rw [← hv₁, ← hv₂])

/-- **Safety, as stated in the paper (Section 5.3.2)**: `N` processors, `N` registers,
termination level `N`; any two output views are related by containment. -/
theorem snapshot_safety_paper [Fintype P] (hR : Fintype.card R = Fintype.card P) {input : P → V}
    (e : Exec (P := P) (snapshot (R := R) (V := V) (Fintype.card P)))
    (he : e.cfg 0 = snapCfg input) (t : ℕ) (p q : P)
    (hp : Fintype.card P ≤ (e.loc t p).d.level) (hps : (e.loc t p).scan = none)
    (hq : Fintype.card P ≤ (e.loc t q).d.level) (hqs : (e.loc t q).scan = none) :
    (e.loc t p).d.view ⊆ (e.loc t q).d.view ∨ (e.loc t q).d.view ⊆ (e.loc t p).d.view :=
  snapshot_safety hR.ge (Nat.le_succ _) e he t p q hp hps hq hqs

/-- Safety for outputs taken at different times: a terminated processor keeps its view, so the
output of `p` (terminated at `t₁`) and the output of `q` (terminated at `t₂`) are comparable. -/
theorem snapshot_safety_outputs [Fintype P] {L : ℕ} (hR : Fintype.card P ≤ Fintype.card R)
    (hL : Fintype.card P ≤ L + 1) {input : P → V}
    (e : Exec (P := P) (snapshot (R := R) (V := V) L)) (he : e.cfg 0 = snapCfg input)
    (t₁ t₂ : ℕ) (p q : P) (hp : L ≤ (e.loc t₁ p).d.level) (hps : (e.loc t₁ p).scan = none)
    (hq : L ≤ (e.loc t₂ q).d.level) (hqs : (e.loc t₂ q).scan = none) :
    (e.loc t₁ p).d.view ⊆ (e.loc t₂ q).d.view ∨ (e.loc t₂ q).d.view ⊆ (e.loc t₁ p).d.view := by
  have h1 := e.snap_stopped_const hp hps (max t₁ t₂) (le_max_left _ _)
  have h2 := e.snap_stopped_const hq hqs (max t₁ t₂) (le_max_right _ _)
  have := snapshot_safety hR hL e he (max t₁ t₂) p q (by rw [h1]; exact hp) (by rw [h1]; exact hps)
    (by rw [h2]; exact hq) (by rw [h2]; exact hqs)
  rwa [h1, h2] at this

/-- Validity of the outputs: every view contains the processor's own input and consists of
inputs. -/
theorem snapshot_view_valid [Fintype P] {L : ℕ} {input : P → V}
    (e : Exec (P := P) (snapshot (R := R) (V := V) L)) (he : e.cfg 0 = snapCfg input)
    (t : ℕ) (p : P) :
    input p ∈ (e.loc t p).d.view ∧ (e.loc t p).d.view ⊆ univ.image input := by
  refine ⟨e.snap_view_mono_le (Nat.zero_le t) p ?_, (snap_viewSpec he).bound t p⟩
  simp [Exec.loc, he, snapCfg, initCfg, snapInit]

end Podc.AnonymousCoverings
