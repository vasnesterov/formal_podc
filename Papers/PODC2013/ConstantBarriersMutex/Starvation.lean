import Papers.PODC2013.ConstantBarriersMutex.Waiting

/-!
# Starvation freedom (Lemma 7, Claims 1 and 2 of the paper)

`starvation_freedom`: in every fair execution, a process in its entry section eventually enters
the critical section.

Proof (following the paper). Suppose `p` is starved. Let `S` be the set of processes that stay
in their entry section forever. For `q ∈ S`, the nodes on `q`'s path that hold `q` only
disappear after `q`'s barrier (`q` writes no more), and its leaf holds `q` forever; so the
highest level `levF q t` holding `q` is non-decreasing and eventually constant (Claim 1). Take a
time `T*` after which all these levels are constant, and `p₀ ∈ S` with the smallest level `k`.
* `k = 0`: the root holds `p₀` from `p₀`'s barrier on. By the waiting section (statement 25,
  `waiting_entry`), some process `g` enters the critical section after `p₀`'s barrier; its exit
  section reads the root and promotes `p₀` (`enters_of_read`) — a contradiction.
* `k ≥ 1`: the parent of `p₀`'s level-`k` node holds some `q ≠ p₀` at `T*`; let `t₀` be the
  last write to it before `T*`, by `q`. By TSO (writes are performed in program order), `p₀`'s
  write to its level-`k` node was performed before `t₀`, and that node holds `p₀` from then on.
  `q ∉ S` (its level would be `≤ k − 1`), so `q` enters the critical section after `t₀`, reads
  `p₀`'s level-`k` node (a child of `q`'s level-`(k−1)` node) in its exit section and promotes
  `p₀` — a contradiction (Claim 2).
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

open Classical

namespace Run

variable (r : Run h)

/-- `q` stays in its entry section from some time on. -/
def Stuck (q : Proc h) : Prop := ∃ T, ∀ t ≥ T, ((r.s t).pc q).Entry

/-- The node at level `l` on `q`'s path holds `q` at time `t`. -/
def hold (q : Proc h) (t l : ℕ) : Prop := (r.s t).mem.node (anc q l) = some q

/-- The highest level (smallest number) holding `q`, `h + 1` if none. -/
noncomputable def levF (q : Proc h) (t : ℕ) : ℕ :=
  if hx : ∃ l, l ≤ h ∧ r.hold q t l then Nat.find hx else h + 1

lemma levF_le {q : Proc h} {t l : ℕ} (hl : l ≤ h) (hh : r.hold q t l) : r.levF q t ≤ l := by
  unfold levF; rw [dif_pos ⟨l, hl, hh⟩]; exact Nat.find_min' _ ⟨hl, hh⟩

lemma levF_spec {q : Proc h} {t : ℕ} (hle : r.levF q t ≤ h) :
    r.hold q t (r.levF q t) ∧ ∀ l < r.levF q t, ¬ r.hold q t l := by
  unfold levF at hle ⊢
  split_ifs at hle ⊢ with hx
  · exact ⟨(Nat.find_spec hx).2, fun l hl hh => Nat.find_min hx hl ⟨by omega, hh⟩⟩
  · omega

variable {r}

/-! ### Small facts -/

lemma Run.door_exit_e23 {t : ℕ} {p : Proc h} (hD : ((r.s t).pc p).Door)
    (hnD : ¬ ((r.s (t + 1)).pc p).Door) : (r.s (t + 1)).pc p = .e23 := by
  by_cases he : r.ev t = .step p
  · have hs : r.s (t + 1) = (r.s t).stepProc p := by rw [r.next_eq, he]; rfl
    rw [hs] at hnD ⊢
    rcases Door_iff.1 hD with hpc | ⟨l, hpc⟩ | hpc
    · simp [Cfg.stepProc, hpc, Cfg.issue, PC.Door] at hnD
    · simp only [Cfg.stepProc, hpc, Cfg.issue] at hnD; split_ifs at hnD <;> simp [PC.Door] at hnD
    · by_cases hb : (r.s t).buf p = []
      · simp [Cfg.stepProc, hpc, Cfg.barrier, hb, Cfg.goto]
      · simp only [Cfg.stepProc, hpc] at hnD
        rw [barrier_flush hb, flush_pc, hpc] at hnD; simp [PC.Door] at hnD
  · rw [r.pc_succ_of_ne he] at hnD; exact absurd hD hnD

lemma apply_of_perf {t : ℕ} {p : Proc h} (hE : ((r.s t).pc p).Entry) (hp : 2 ≤ perf (r.s t) p) :
    (r.s t).mem.apply p = true := by
  have hI := r.inv t
  by_cases hd : ((r.s t).pc p).Door
  · exact (buf_door hI hd).2.2.2 hp
  · have hL := hI.loc p; unfold LI at hL
    cases hpc : (r.s t).pc p <;> simp only [hpc, PC.Entry, PC.Door] at hE hd hL <;>
      first | exact hL.2 | exact hE.elim | exact (hd trivial).elim

/-- Nodes never become empty again. -/
lemma node_some_persist {t t' i : ℕ} (htt : t ≤ t') (hs : (r.s t).mem.node i ≠ none) :
    (r.s t').mem.node i ≠ none := by
  induction t', htt using Nat.le_induction with
  | base => exact hs
  | succ t' _ ih =>
    by_cases hc : (r.s (t' + 1)).mem.node i = (r.s t').mem.node i
    · rw [hc]; exact ih
    · obtain ⟨q, b, -, hv, -⟩ := r.node_change hc; rw [hv]; simp

/-- Only `q` writes to its leaf, so once the leaf holds `q` it holds `q` forever. -/
lemma leaf_persist {q : Proc h} {t t' : ℕ} (htt : t ≤ t') (hh : r.hold q t h) : r.hold q t' h := by
  induction t', htt using Nat.le_induction with
  | base => exact hh
  | succ t' _ ih =>
    unfold hold at ih ⊢
    by_contra hc
    have hc' : (r.s (t' + 1)).mem.node (anc q h) ≠ (r.s t').mem.node (anc q h) := by
      rw [ih]; exact hc
    obtain ⟨q', b, hb, hv, -⟩ := r.node_change hc'
    have hmem : W.node (anc q h) q' ∈ (r.s t').buf q' := by rw [hb]; simp
    obtain ⟨-, ⟨l, hl, hal⟩, -⟩ := BW.buf_node (r.inv t') hmem
    have hlh := BW.anc_level_inj (p := q) (q := q') le_rfl hl hal
    subst hlh
    have := BW.anc_leaf_inj hal; subst this
    exact hc hv

/-- A function on `ℕ` that differs at `0` and `T` has a last change before `T`. -/
lemma last_change {α : Type*} (f : ℕ → α) {T : ℕ} (hne : f 0 ≠ f T) :
    ∃ t₀ < T, f t₀ ≠ f (t₀ + 1) ∧ ∀ t, t₀ < t → t ≤ T → f t = f T := by
  induction T with
  | zero => exact absurd rfl hne
  | succ T ih =>
    by_cases hc : f T = f (T + 1)
    · obtain ⟨t₀, h1, h2, h3⟩ := ih (by rw [hc]; exact hne)
      refine ⟨t₀, by omega, h2, fun t ht1 ht2 => ?_⟩
      rcases Nat.lt_or_ge t (T + 1) with hlt | hge
      · rw [h3 t ht1 (by omega), hc]
      · rw [show t = T + 1 by omega]
    · exact ⟨T, by omega, hc, fun t ht1 ht2 => by rw [show t = T + 1 by omega]⟩

/-- A monotone bounded sequence of naturals is eventually constant. -/
lemma eventually_const (f : ℕ → ℕ) {a B : ℕ} (hmono : ∀ t t', a ≤ t → t ≤ t' → f t ≤ f t')
    (hB : ∀ t, a ≤ t → f t ≤ B) : ∃ T ≥ a, ∀ t ≥ T, f t = f T := by
  suffices H : ∀ n a, B - f a ≤ n → (∀ t t', a ≤ t → t ≤ t' → f t ≤ f t') →
      (∀ t, a ≤ t → f t ≤ B) → ∃ T ≥ a, ∀ t ≥ T, f t = f T from H _ a le_rfl hmono hB
  intro n
  induction n with
  | zero =>
    intro a ha hm hb
    refine ⟨a, le_rfl, fun t ht => ?_⟩
    have := hm a t le_rfl ht; have := hb t ht; have := hb a le_rfl; omega
  | succ n ih =>
    intro a ha hm hb
    by_cases hc : ∀ t ≥ a, f t = f a
    · exact ⟨a, le_rfl, hc⟩
    · push_neg at hc
      obtain ⟨t₁, ht₁, hne⟩ := hc
      have hlt : f a < f t₁ := lt_of_le_of_ne (hm a t₁ le_rfl ht₁) (Ne.symm hne)
      obtain ⟨T, hT, hT'⟩ := ih t₁ (by have := hb t₁ ht₁; omega)
        (fun t t' h1 h2 => hm t t' (by omega) h2) (fun t h1 => hb t (by omega))
      exact ⟨T, by omega, hT'⟩

/-! ### Stuck processes -/

/-- Data of a stuck process: the start `σ` of its passage, the time `ta` its barrier completes. -/
lemma stuck_data (hf : r.Fair) {q : Proc h} (hq : r.Stuck q) :
    ∃ σ ta, σ ≤ ta ∧ perf (r.s σ) q = 0 ∧ (∀ t ≥ σ, ((r.s t).pc q).Entry) ∧
      (r.s ta).pc q = .e23 ∧ ∀ t ≥ ta, perf (r.s t) q = h + 3 ∧ ¬ ((r.s t).pc q).Door := by
  obtain ⟨T₀, hT₀⟩ := hq
  obtain ⟨σ, hσ, hp0, hEσ⟩ := r.passage_start (hT₀ T₀ le_rfl)
  have hE : ∀ t ≥ σ, ((r.s t).pc q).Entry := fun t ht => by
    rcases Nat.lt_or_ge t T₀ with h1 | h1
    · exact hEσ t ht (by omega)
    · exact hT₀ t h1
  obtain ⟨ta₀, hta₀, hnd⟩ := r.stuck_barrier hf (T := σ) hE
  have hex : ∃ t, σ ≤ t ∧ ¬ ((r.s t).pc q).Door := ⟨ta₀, hta₀, (hnd ta₀ le_rfl).1⟩
  set ta := Nat.find hex with hta
  have hta1 := (Nat.find_spec hex).1
  have hta2 := (Nat.find_spec hex).2
  have hσD : ((r.s σ).pc q).Door := by
    by_contra hc; unfold perf at hp0; rw [if_neg hc] at hp0; omega
  have hσlt : σ < ta := by
    rcases Nat.eq_or_lt_of_le hta1 with h1 | h1
    · rw [← h1] at hta2; exact absurd hσD hta2
    · exact h1
  have hprev : ((r.s (ta - 1)).pc q).Door := by
    by_contra hc
    exact Nat.find_min hex (show ta - 1 < ta by omega) ⟨by omega, hc⟩
  have h23 : (r.s ta).pc q = .e23 := by
    have := Run.door_exit_e23 (r := r) (t := ta - 1) hprev (by rw [Nat.sub_add_cancel (by omega)]; exact hta2)
    rwa [Nat.sub_add_cancel (by omega)] at this
  refine ⟨σ, ta, hσlt.le, hp0, hE, h23, fun t ht => ?_⟩
  have hnd' : ¬ ((r.s t).pc q).Door := by
    induction t, ht using Nat.le_induction with
    | base => exact hta2
    | succ t ht ih => exact r.not_door_succ (hE t (by omega)) ih
  exact ⟨by unfold perf; rw [if_neg hnd'], hnd'⟩

/-- The level structure of a stuck process after its barrier (Claim 1 of the paper). -/
lemma stuck_levels {q : Proc h} {σ ta : ℕ} (hσta : σ ≤ ta) (hp0 : perf (r.s σ) q = 0)
    (hE : ∀ t ≥ σ, ((r.s t).pc q).Entry) (hperf : ∀ t ≥ ta, perf (r.s t) q = h + 3) :
    (∀ t ≥ ta, r.hold q t h) ∧
    (∀ t t' l, ta ≤ t → t ≤ t' → l ≤ h → ¬ r.hold q t l → ¬ r.hold q t' l) ∧
    (∀ t ≥ ta, r.levF q t ≤ h) ∧
    (∀ t t', ta ≤ t → t ≤ t' → r.levF q t ≤ r.levF q t') := by
  have hleaf : ∀ t ≥ ta, r.hold q t h := by
    obtain ⟨tc, h1, h2, -, w, hw, hm⟩ := r.perf_cross (p := q) hσta
      (fun t ht _ => hE t ht) (d := dIdx h h) (by rw [hp0]; omega)
      (by rw [hperf ta le_rfl]; unfold dIdx; omega)
    have hc := r.node_of_cross (p := q) (l := h) le_rfl hw hm
    intro t ht; exact leaf_persist (by omega) hc
  have hpers : ∀ t t' l, ta ≤ t → t ≤ t' → l ≤ h → ¬ r.hold q t l → ¬ r.hold q t' l :=
    fun t t' l h1 h2 hl hn => r.node_ne_persist hl h2 (fun t'' a _ => hE t'' (by omega))
      (by rw [hperf t h1]; unfold dIdx; omega) hn
  have hle : ∀ t ≥ ta, r.levF q t ≤ h := fun t ht => r.levF_le le_rfl (hleaf t ht)
  refine ⟨hleaf, hpers, hle, fun t t' h1 h2 => ?_⟩
  have hs := (r.levF_spec (hle t' (by omega))).1
  apply r.levF_le (hle t' (by omega))
  by_contra hc
  exact hpers t t' _ h1 h2 (hle t' (by omega)) hc hs

/-- **Lemma 7 (starvation freedom).** In every fair execution of Algorithm 1 under TSO, a
process in its entry section eventually enters the critical section. -/
theorem starvation_freedom (hf : r.Fair) {p : Proc h} {T : ℕ} (hpE : ((r.s T).pc p).Entry) :
    ∃ t ≥ T, (r.s t).pc p = .cs := by
  by_contra H
  push_neg at H
  have hpS : r.Stuck p := ⟨T, r.entry_forever hpE H⟩
  -- data for all stuck processes
  have hdata : ∀ q, ∃ σ ta Ts, r.Stuck q → (σ ≤ ta ∧ ta ≤ Ts ∧ perf (r.s σ) q = 0 ∧
      (∀ t ≥ σ, ((r.s t).pc q).Entry) ∧ (r.s ta).pc q = .e23 ∧
      (∀ t ≥ ta, perf (r.s t) q = h + 3) ∧ ∀ t ≥ Ts, r.levF q t = r.levF q Ts) := by
    intro q
    by_cases hq : r.Stuck q
    · obtain ⟨σ, ta, h1, h2, h3, h4, h5⟩ := stuck_data hf hq
      obtain ⟨-, -, hle, hmono⟩ := stuck_levels h1 h2 h3 (fun t ht => (h5 t ht).1)
      obtain ⟨Ts, hTs, hTs'⟩ := eventually_const (r.levF q) (a := ta) (B := h)
        (fun t t' a b => hmono t t' a b) hle
      exact ⟨σ, ta, Ts, fun _ => ⟨h1, hTs, h2, h3, h4, fun t ht => (h5 t ht).1, hTs'⟩⟩
    · exact ⟨0, 0, 0, fun h' => absurd h' hq⟩
  choose σ ta Ts hD using hdata
  let S : Finset (Proc h) := Finset.univ.filter r.Stuck
  have hpSS : p ∈ S := by simp [S, hpS]
  let Tst : ℕ := Finset.univ.sup Ts
  have hTst : ∀ q, Ts q ≤ Tst := fun q => Finset.le_sup (f := Ts) (Finset.mem_univ q)
  obtain ⟨p₀, hp₀S, hmin⟩ := Finset.exists_min_image S (fun q => r.levF q Tst) ⟨p, hpSS⟩
  have hp₀ : r.Stuck p₀ := by simpa [S] using hp₀S
  obtain ⟨hσta, htaTs, hp0, hE0, h23, hperf0, hstab0⟩ := hD p₀ hp₀
  obtain ⟨hleaf0, hpers0, hle0, hmono0⟩ := stuck_levels hσta hp0 hE0 hperf0
  set k := r.levF p₀ Tst with hk
  have hkh : k ≤ h := hle0 Tst (by have := hTst p₀; omega)
  have hnocs : ∀ t ≥ σ p₀, (r.s t).pc p₀ ≠ .cs := fun t ht hc => by
    have := hE0 t ht; rw [hc] at this; simp [PC.Entry] at this
  have hstab : ∀ t ≥ Tst, r.levF p₀ t = k := fun t ht => by
    have h1 := hstab0 Tst (hTst p₀)
    rw [hstab0 t (by have := hTst p₀; omega), hk, h1]
  -- the node at level `k` holds `p₀` from any time after which its write is performed
  have hholdk : ∀ t₁, σ p₀ ≤ t₁ → dIdx h k < perf (r.s t₁) p₀ → ∀ t ≥ t₁, r.hold p₀ t k := by
    intro t₁ h1 h2 t ht
    by_contra hc
    have hn : ¬ r.hold p₀ (max t Tst) k := by
      rcases le_total t Tst with h3 | h3
      · rw [max_eq_right h3]
        exact r.node_ne_persist hkh h3 (fun t'' a _ => hE0 t'' (by omega))
          (lt_of_lt_of_le h2 (r.perf_mono (by omega) (fun t'' a b => hE0 t'' (by omega)))) hc
      · rw [max_eq_left h3]; exact hc
    have := (r.levF_spec (q := p₀) (hle0 (max t Tst) (by have := hTst p₀; omega))).1
    rw [hstab _ (le_max_right _ _)] at this
    exact hn this
  have happly : ∀ t ≥ σ p₀, 2 ≤ perf (r.s t) p₀ → (r.s t).mem.apply p₀ = true :=
    fun t ht h2 => apply_of_perf (hE0 t ht) h2
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the root holds `p₀` from its barrier on
    have hroot : ∀ t ≥ ta p₀, r.hold p₀ t 0 := by
      have := hholdk (ta p₀) hσta (by rw [hperf0 _ le_rfl]; unfold dIdx; omega)
      rw [hk0] at this; exact this
    obtain ⟨te, hte, hent⟩ := r.waiting_entry hf h23 (fun t ht => hnocs t (by omega))
    obtain ⟨g, hg1, hg2⟩ := r.ent_succ_entry hent
    have hgp : g ≠ p₀ := fun h' => hnocs (te + 1) (by omega) (h' ▸ hg2)
    rcases Nat.eq_zero_or_pos h with hh0 | hhpos
    · exact hgp (Fin.ext (by
        have h1 := g.isLt; have h2 := p₀.isLt
        have h3 : (2 : ℕ) ^ h = 1 := by rw [hh0, pow_zero]
        omega))
    obtain ⟨t, ht, hcs⟩ := r.enters_of_read hf (g := g) (p₀ := p₀) (t₁ := te + 1) (l := 0) (j := 0)
      hg2 hhpos (by norm_num) hgp
      (fun t ht => by
        have := hroot t (by omega); unfold hold at this
        rw [BW.anc_zero] at this; rw [BW.target_zero, BW.anc_zero]; exact this)
      (hE0 _ (by omega)) (happly _ (by omega) (by rw [hperf0 _ (by omega)]; omega))
    exact hnocs t (by omega) hcs
  · -- `k ≥ 1`: the parent of `p₀`'s level-`k` node
    set par := anc p₀ (k - 1) with hpar
    have hparT : (r.s Tst).mem.node par ≠ some p₀ := by
      have := (r.levF_spec (q := p₀) (hle0 Tst (by have := hTst p₀; omega))).2 (k - 1)
        (by rw [← hk]; omega)
      exact this
    -- `p₀` wrote the parent, so it is not empty at `Tst`
    obtain ⟨tp, -, htp, -, w, hw, hm⟩ := r.perf_cross (p := p₀) hσta
      (fun t ht _ => hE0 t ht) (d := dIdx h (k - 1)) (by rw [hp0]; omega)
      (by rw [hperf0 _ le_rfl]; unfold dIdx; omega)
    have hpw := r.node_of_cross (p := p₀) (l := k - 1) (by omega) hw hm
    have hnn : (r.s Tst).mem.node par ≠ none :=
      node_some_persist (t := tp + 1) (by have := hTst p₀; omega) (by rw [hpw]; simp)
    obtain ⟨q, hq⟩ : ∃ q, (r.s Tst).mem.node par = some q := Option.ne_none_iff_exists'.1 hnn
    have hqp : q ≠ p₀ := fun h' => hparT (h' ▸ hq)
    -- the last change of the parent before `Tst`
    have h0 : (r.s 0).mem.node par = none := by rw [r.init]; rfl
    obtain ⟨t₀, ht₀, hch, hconst⟩ := last_change (fun t => (r.s t).mem.node par) (T := Tst)
      (by rw [h0, hq]; simp)
    have hval : (r.s (t₀ + 1)).mem.node par = some q := by rw [hconst _ (by omega) (by omega), hq]
    obtain ⟨q', b, hb, hv, -, -⟩ := r.node_change (Ne.symm hch)
    rw [hval] at hv; cases hv
    have hmem : W.node par q ∈ (r.s t₀).buf q := by rw [hb]; simp
    obtain ⟨-, ⟨l', hl', hal⟩, hEq⟩ := BW.buf_node (r.inv t₀) hmem
    have hl'k : k - 1 = l' := BW.anc_level_inj (p := p₀) (q := q) (by omega) hl' hal
    subst hl'k
    -- by TSO, `p₀`'s level-`k` write was performed before `t₀ + 1`
    have hord : σ p₀ ≤ t₀ + 1 ∧ dIdx h (k - 1) < perf (r.s (t₀ + 1)) p₀ := by
      by_contra hc
      have hs : perf (r.s (max (σ p₀) (t₀ + 1))) p₀ ≤ dIdx h (k - 1) := by
        rcases le_total (σ p₀) (t₀ + 1) with h3 | h3
        · rw [max_eq_right h3]; have := not_and.1 hc h3; omega
        · rw [max_eq_left h3, hp0]; omega
      have hTT : ta p₀ ≤ Tst := by have := hTst p₀; omega
      have hlast : dIdx h (k - 1) < perf (r.s Tst) p₀ := by
        rw [hperf0 _ hTT]; unfold dIdx; omega
      obtain ⟨tq, htq1, htq2, -, w', hw', hm'⟩ := r.perf_cross (p := p₀)
        (t₁ := max (σ p₀) (t₀ + 1)) (t₂ := Tst) (by omega)
        (fun t ht _ => hE0 t (by omega)) hs hlast
      have hq2 := r.node_of_cross (p := p₀) (l := k - 1) (by omega) hw' hm'
      rw [hconst _ (by omega) (by omega), hq] at hq2
      exact hqp (Option.some_injective _ hq2)
    have hholdk' := hholdk (t₀ + 1) hord.1 (by unfold dIdx at hord ⊢; omega)
    -- `q` is not stuck
    have hqS : ¬ r.Stuck q := by
      intro hqs
      obtain ⟨-, -, -, hEq', -, hperfq, -⟩ := hD q hqs
      have hlev : r.levF q Tst ≤ k - 1 := r.levF_le (by omega) (by unfold hold; rw [← hal, hq])
      have := hmin q (by simp [S, hqs])
      omega
    -- so `q` enters the critical section after `t₀`
    obtain ⟨t₁, ht₁, hnE⟩ : ∃ t₁ ≥ t₀, ¬ ((r.s t₁).pc q).Entry := by
      by_contra hc; push_neg at hc; exact hqS ⟨t₀, hc⟩
    obtain ⟨t₂, ht₂, -, hcs₂⟩ := r.cs_of_leave_entry ht₁ hEq hnE
    obtain ⟨j, hj1, hj2, hjt⟩ := BW.anc_child p₀ (l := k - 1) (by omega)
    obtain ⟨t, ht, hcs⟩ := r.enters_of_read hf (g := q) (p₀ := p₀) (t₁ := t₂) (l := k - 1) (j := j)
      hcs₂ (by omega) hj2 hqp
      (fun t ht => by
        have := hholdk' t (by omega); unfold hold at this
        rw [← hal, hjt, show k - 1 + 1 = k by omega]; exact this)
      (hE0 _ (by omega))
      (happly _ (by omega) (by
        have := r.perf_mono (p := p₀) (t₁ := t₀ + 1) (t₂ := t₂) (by omega)
          (fun t'' a _ => hE0 t'' (by omega))
        unfold dIdx at hord; omega))
    exact hnocs t (by omega) hcs

end Run

end Podc.ConstantBarriersMutex
