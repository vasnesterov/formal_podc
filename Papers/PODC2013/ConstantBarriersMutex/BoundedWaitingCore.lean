import Papers.PODC2013.ConstantBarriersMutex.BoundedWaitingQueue

/-!
# Bounded waiting, part 3: Lemma 9 and the counting argument of Lemma 8

All results here are about an arbitrary run `r` in which every configuration satisfies the
invariant `Inv` (hypothesis `hI`; it is discharged by `Run.inv` in `BoundedWaiting.lean`).
-/

namespace Podc.ConstantBarriersMutex.BW

open Podc.ConstantBarriersMutex

variable {h : ℕ}

/-! ### Facts about runs -/

section run

variable (r : Run h) (hI : ∀ t, Inv (r.s t))
include hI

lemma enters_facts {x : Proc h} {t : ℕ} (he : Enters r x t) :
    r.ev t = .step x ∧ ((r.s t).pc x).Entry ∧ ∀ y, ¬ (r.s t).InCSX y := by
  have he' := he
  unfold Enters at he'; rw [r.step t] at he'
  obtain ⟨hev, hE, -⟩ := enters_cases (hI t) (r.ev t) he'.1 he'.2
  refine ⟨hev, hE, fun y hy => ?_⟩
  by_cases hyx : y = x
  · subst hyx; exact entry_not_incsx hE hy
  · have hy' : (r.s (t + 1)).InCSX y := by
      rw [r.step t, hev]
      simp only [Cfg.next, Cfg.InCSX, stepProc_pc_ne _ hyx, stepProc_buf_ne _ hyx]
      exact hy
    exact hyx (hI (t + 1) |>.uniq y x hy' (Or.inl he.2))

omit hI in
lemma read_of_pre {x : Proc h} {l j a u : ℕ} (hl : l < h) (hj : j ≤ 2) (hau : a ≤ u)
    (ha : PreRead l j ((r.s a).pc x)) (hu : ¬ PreRead l j ((r.s u).pc x)) :
    ∃ τ, a ≤ τ ∧ τ < u ∧ r.ev τ = .step x ∧ ∃ acc, (r.s τ).pc x = .x34 l j acc := by
  induction u, hau using Nat.le_induction with
  | base => exact absurd ha hu
  | succ u hau ih =>
    by_cases hp : PreRead l j ((r.s u).pc x)
    · rw [r.step u] at hu
      obtain ⟨he, acc, hpc⟩ := preRead_step (r.s u) (r.ev u) hl hj hp hu
      exact ⟨u, hau, by omega, he, acc, hpc⟩
    · obtain ⟨τ, h1, h2, h3⟩ := ih hp
      exact ⟨τ, h1, by omega, h3⟩

lemma done_start {p : Proc h} {l t : ℕ} (hd : Done (r.s t) p l) :
    ∃ a ≤ t, (r.s a).mem.node (anc p l) = some p ∧ ∀ u, a ≤ u → u ≤ t → Done (r.s u) p l := by
  induction t with
  | zero =>
    exfalso; obtain ⟨-, hR, -⟩ := hd
    rw [r.init] at hR; simp [Cfg.init, DoneRegion] at hR
  | succ t ih =>
    by_cases hd' : Done (r.s t) p l
    · obtain ⟨a, ha, hn, hall⟩ := ih hd'
      refine ⟨a, by omega, hn, fun u h1 h2 => ?_⟩
      rcases Nat.lt_or_ge u (t + 1) with h3 | h3
      · exact hall u h1 (by omega)
      · rw [show u = t + 1 by omega]; exact hd
    · refine ⟨t + 1, le_rfl, ?_, fun u h1 h2 => by rw [show u = t + 1 by omega]; exact hd⟩
      rw [r.step t] at hd ⊢
      exact Done.start (hI t) _ hd' hd

lemma done_extend {p : Proc h} {l a b : ℕ} (hd : Done (r.s a) p l)
    (hE : ∀ u, a ≤ u → u ≤ b → ((r.s u).pc p).Entry) :
    ∀ u, a ≤ u → u ≤ b → Done (r.s u) p l := by
  intro u hau hub
  induction u, hau using Nat.le_induction with
  | base => exact hd
  | succ u hau ih =>
    have := Done.step (hI u) (ih (by omega)) (r.ev u) (by rw [← r.step u]; exact hE _ (by omega) hub)
    rwa [← r.step u] at this

lemma node_some {X a : ℕ} {p : Proc h} (hn : (r.s a).mem.node X = some p) :
    ∀ τ, a ≤ τ → ∃ v, (r.s τ).mem.node X = some v := by
  intro τ haτ
  induction τ, haτ using Nat.le_induction with
  | base => exact ⟨p, hn⟩
  | succ τ _ ih =>
    obtain ⟨v, hv⟩ := ih
    rw [r.step τ]; exact node_some_step (hI τ) _ hv

lemma node_change {X a τ : ℕ} {p x : Proc h} (hn : (r.s a).mem.node X = some p) (haτ : a ≤ τ)
    (hx : (r.s τ).mem.node X = some x) (hxp : x ≠ p) :
    ∃ f, a ≤ f ∧ f < τ ∧ (∃ l ≤ h, X = anc x l) ∧ ((r.s (f + 1)).pc x).Entry ∧
      (r.s (f + 1)).mem.apply x = true := by
  induction τ, haτ using Nat.le_induction with
  | base => rw [hn] at hx; cases hx; exact absurd rfl hxp
  | succ τ haτ ih =>
    by_cases hτ : (r.s τ).mem.node X = some x
    · obtain ⟨f, h1, h2, h3⟩ := ih hτ
      exact ⟨f, h1, by omega, h3⟩
    · rw [r.step τ] at hx
      have := node_writer (hI τ) (r.ev τ) hτ hx
      rw [← r.step τ] at this
      exact ⟨τ, haτ, by omega, this⟩

lemma entry_persist {x : Proc h} {a b : ℕ} (hab : a ≤ b) (hE : ((r.s a).pc x).Entry)
    (ha : (r.s a).mem.apply x = true) (hn : ∀ t, a ≤ t → t < b → ¬ Enters r x t) :
    ((r.s b).pc x).Entry ∧ (r.s b).mem.apply x = true := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨hE, ha⟩
  | succ b hab ih =>
    obtain ⟨hE', ha'⟩ := ih (fun t h1 h2 => hn t h1 (by omega))
    have hcs : (r.s (b + 1)).pc x ≠ .cs := fun h => hn b hab (by omega) ⟨fun h' => by
      rw [h'] at hE'; simp [PC.Entry] at hE', h⟩
    refine ⟨?_, ?_⟩
    · have := entry_step (hI b) (r.ev b) hE' (by rw [← r.step b]; exact hcs)
      rwa [← r.step b] at this
    · have := apply_step (hI b) (r.ev b) hE' ha'
      rwa [← r.step b] at this

/-- After an entry into the critical section, the exit section performs the read number `j` of
statement 34 at level `l` before anybody enters the critical section again. -/
lemma read_before_next_entry {x y : Proc h} {g e l j : ℕ} (hl : l < h) (hj : j ≤ 2)
    (hg : (r.s g).pc x = .cs) (hge : g ≤ e) (he : Enters r y e) :
    ∃ τ, g ≤ τ ∧ τ < e ∧ r.ev τ = .step x ∧ ∃ acc, (r.s τ).pc x = .x34 l j acc := by
  have hpre : PreRead l j ((r.s g).pc x) := by rw [hg]; trivial
  have hnot : ¬ PreRead l j ((r.s e).pc x) := fun hp =>
    (enters_facts r hI he).2.2 x hp.incsx
  exact read_of_pre r hl hj hge hpre hnot

/-- The read of statement 34 at time `τ` by `g` (at level `l'`, read number `j'`) returns the
memory value `some x` with `x ≠ g`, and `x` is in the entry section with `apply[x] = true` at
`τ + 1`: then by the time `U` at which `g` has left its exit section, `x` has entered the critical
section or is in the promotion order. -/
lemma promote_read {g x : Proc h} {τ U l' j' : ℕ} {acc : List (Proc h)}
    (hev : r.ev τ = .step g) (hpc : (r.s τ).pc g = .x34 l' j' acc)
    (hv : (r.s τ).mem.node (target (anc g l') j') = some x) (hxg : x ≠ g)
    (hE : ((r.s (τ + 1)).pc x).Entry) (ha : (r.s (τ + 1)).mem.apply x = true)
    (hU : τ + 1 ≤ U) (hUn : ¬ (r.s U).InCSX g) :
    (∃ t, τ + 1 ≤ t ∧ t < U ∧ Enters r x t) ∨ x ∈ Q (r.s U) := by
  apply promote r hI hU _ hE ha hUn
  left
  rw [r.step τ, hev]
  simp only [Cfg.next, Cfg.stepProc, hpc, view_node_exit (hI τ) hpc, hv]
  split_ifs <;> simp only [goto_pc, Function.update_self, Pending] <;> exact mem_addCand_self hxg

omit hI in
/-- The program counter after a read of statement 34. -/
lemma pc_after_read {g : Proc h} {τ l' j' : ℕ} {acc : List (Proc h)}
    (hev : r.ev τ = .step g) (hpc : (r.s τ).pc g = .x34 l' j' acc) :
    ∃ acc', (j' < 2 ∧ (r.s (τ + 1)).pc g = .x34 l' (j' + 1) acc') ∨
      (2 ≤ j' ∧ (r.s (τ + 1)).pc g = .x35 l' acc') := by
  rw [r.step τ, hev]
  simp only [Cfg.next, Cfg.stepProc, hpc]
  split_ifs with hj
  · exact ⟨_, Or.inl ⟨hj, by simp; rfl⟩⟩
  · exact ⟨_, Or.inr ⟨by omega, by simp; rfl⟩⟩

end run

/-! ### Counting entries -/

open Classical in
/-- The number of entries of `q` into the critical section at steps `t ∈ [a, b)`. -/
noncomputable def cnt (r : Run h) (q : Proc h) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun t => Enters r q t)).card

lemma last_entry (r : Run h) (q : Proc h) {a b : ℕ} (hc : 0 < cnt r q a b) :
    ∃ e, a ≤ e ∧ e < b ∧ Enters r q e ∧ cnt r q a b ≤ cnt r q a e + 1 := by
  classical
  unfold cnt at hc ⊢
  set S := (Finset.Ico a b).filter (fun t => Enters r q t) with hS
  have hne : S.Nonempty := Finset.card_pos.1 hc
  set e := S.max' hne
  have he : e ∈ S := S.max'_mem hne
  rw [hS, Finset.mem_filter, Finset.mem_Ico] at he
  refine ⟨e, he.1.1, he.1.2, he.2, ?_⟩
  have hsub : S ⊆ insert e ((Finset.Ico a e).filter (fun t => Enters r q t)) := by
    intro t ht
    have hle : t ≤ e := S.le_max' t ht
    rw [hS, Finset.mem_filter, Finset.mem_Ico] at ht
    rcases Nat.lt_or_ge t e with h1 | h1
    · exact Finset.mem_insert_of_mem (by simp [ht.1.1, h1, ht.2])
    · rw [show t = e by omega]; exact Finset.mem_insert_self _ _
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

lemma first_entry (r : Run h) (q : Proc h) {a b : ℕ} (hc : 0 < cnt r q a b) :
    ∃ e, a ≤ e ∧ e < b ∧ Enters r q e := by
  obtain ⟨e, h1, h2, h3, -⟩ := last_entry r q hc
  exact ⟨e, h1, h2, h3⟩


/-! ### Lemma 9 -/

/-- Some process reads node `X` at statement 34 of its exit section at step `τ`. -/
def ReadsAt (r : Run h) (τ X : ℕ) : Prop :=
  ∃ g l' j' acc, l' < h ∧ r.ev τ = .step g ∧ (r.s τ).pc g = .x34 l' j' acc ∧
    target (anc g l') j' = X

lemma pos_height {p q : Proc h} (hpq : p ≠ q) : 0 < h := by
  by_contra h0
  have h0 : h = 0 := by omega
  subst h0
  exact hpq (Fin.ext (by have := p.isLt; have := q.isLt; simp at *; try omega))

section main

variable (r : Run h) (hI : ∀ t, Inv (r.s t)) {p q : Proc h} {t₁ t₂ : ℕ}
include hI

lemma not_enters_of_done {l t : ℕ} (hd : Done (r.s (t + 1)) p l) : ¬ Enters r p t := by
  intro he
  have := (hd.entry_apply (hI _)).1
  rw [he.2] at this; simp [PC.Entry] at this

/-- **Lemma 9** (TSO version, for a process `p` waiting during `[t₁, t₂]`). Let `e < t₂` be a
step at which `q` enters the critical section for at least the `(l + 2)`-th time since `t₁`
(i.e. `q` entered at least `l + 1` times during `[t₁, e)`). Then either `p` has been promoted
(it is in the promotion order) at some time `π ∈ [t₁, e]`, or some process reads the node
`n^l_p = anc p l` at statement 34 of its exit section at a step `τ < e` with `τ ≥ a`, where at
time `a` the node holds `p`, written by the doorway of `p`'s current passage (`Done` holds from
`a` to `t₂`; in the paper's notation `a ≥ t_l(P)`). -/
theorem lemma9 (hpq : p ≠ q) (hW : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Waiting) :
    ∀ l, l ≤ h → ∀ e, Enters r q e → e < t₂ → l + 1 ≤ cnt r q t₁ e →
      (∃ π, t₁ ≤ π ∧ π ≤ e ∧ p ∈ Q (r.s π)) ∨
      (∃ a τ, a ≤ τ ∧ τ < e ∧ (r.s a).mem.node (anc p l) = some p ∧
        (∀ u, a ≤ u → u ≤ t₂ → Done (r.s u) p l) ∧ ReadsAt r τ (anc p l)) := by
  have hentry : ∀ u, t₁ ≤ u → u ≤ t₂ → ((r.s u).pc p).Entry := by
    intro u h1 h2
    have := hW u h1 h2
    cases hpc : (r.s u).pc p <;> simp_all [PC.Waiting, PC.Entry]
  -- `Done` at level `l` on `[a, t₂]`, from the doorway of the current passage
  have hstart : ∀ l, l ≤ h → t₁ ≤ t₂ → ∃ a ≤ t₁, (r.s a).mem.node (anc p l) = some p ∧
      ∀ u, a ≤ u → u ≤ t₂ → Done (r.s u) p l := by
    intro l hl h12
    have hd := Done.of_waiting (hI t₁) (hW t₁ le_rfl h12) hl
    obtain ⟨a, hat, hn, hall⟩ := done_start r hI hd
    refine ⟨a, hat, hn, fun u h1 h2 => ?_⟩
    rcases le_or_gt u t₁ with h3 | h3
    · exact hall u h1 h3
    · exact done_extend r hI hd hentry u (by omega) h2
  have hh := pos_height hpq
  intro l
  induction l with
  | zero =>
    intro _ e he het hc
    obtain ⟨e₀, h1, h2, h3⟩ := first_entry r q (by omega : 0 < cnt r q t₁ e)
    obtain ⟨τ, hτ1, hτ2, hev, acc, hpc⟩ :=
      read_before_next_entry r hI hh (Nat.zero_le 2) h3.2 (by omega : e₀ + 1 ≤ e) he
    obtain ⟨a, hat, hn, hD⟩ := hstart 0 (Nat.zero_le h) (by omega)
    exact Or.inr ⟨a, τ, by omega, hτ2, hn, hD, q, 0, 0, acc, hh, hev, hpc,
      by simp [target, anc_zero]⟩
  | succ m ih =>
    intro hm e he het hc
    obtain ⟨e', h1, h2, h3, h4⟩ := last_entry r q (by omega : 0 < cnt r q t₁ e)
    rcases ih (by omega) e' h3 (by omega) (by omega) with
      ⟨π, hπ1, hπ2, hπ3⟩ | ⟨a, τ, haτ, hτe, hn, hD, g, l', j', acc, hl', hev, hpc, htg⟩
    · exact Or.inl ⟨π, hπ1, by omega, hπ3⟩
    obtain ⟨v, hv⟩ := node_some r hI hn τ haτ
    have hv' : (r.s τ).mem.node (target (anc g l') j') = some v := by rw [htg]; exact hv
    have hgn : ¬ (r.s e').InCSX g := (enters_facts r hI h3).2.2 g
    have hτe' : τ + 1 ≤ e' := hτe
    have hgcs : (r.s τ).InCSX g := Or.inr (Or.inl (by rw [hpc]; trivial))
    by_cases hvp : v = p
    · -- `g` reads `p` and promotes it
      subst hvp
      have hD1 := hD (τ + 1) (by omega) (by omega)
      have hvg : v ≠ g := fun h' => by
        subst h'; exact entry_not_incsx ((hD τ haτ (by omega)).entry_apply (hI τ)).1 hgcs
      obtain ⟨hE1, ha1⟩ := hD1.entry_apply (hI _)
      rcases promote_read r hI hev hpc hv' hvg hE1 ha1 hτe' hgn with ⟨t, ht1, ht2, ht3⟩ | hQ
      · exact absurd ht3 (not_enters_of_done r hI (hD (t + 1) (by omega) (by omega)))
      · exact Or.inl ⟨e', h1, by omega, hQ⟩
    -- `v ≠ p` overwrote the node after `a`
    obtain ⟨f, hf1, hf2, ⟨l'', hl'', hX⟩, hEf, haf⟩ := node_change r hI hn haτ hv hvp
    have hl''m : m = l'' := anc_level_inj (by omega) hl'' hX
    subst hl''m
    have hDf1 := (hD f hf1 (by omega)).succ (hI f) hm
    obtain ⟨a', ha'f, hn', hall'⟩ := done_start r hI hDf1
    have hD' : ∀ u, a' ≤ u → u ≤ t₂ → Done (r.s u) p (m + 1) := by
      intro u hu1 hu2
      rcases le_or_gt u f with hu3 | hu3
      · exact hall' u hu1 hu3
      · exact done_extend r hI hDf1
          (fun u' h1' h2' => ((hD u' (by omega) h2').entry_apply (hI _)).1) u (by omega) hu2
    obtain ⟨jc, hjc1, hjc2, hjc⟩ := anc_child p (show m < h by omega)
    have htv : target (anc v m) jc = anc p (m + 1) := by rw [← hX]; exact hjc
    suffices hs : ∃ τ', a' ≤ τ' ∧ τ' < e ∧ r.ev τ' = .step v ∧
        ∃ acc', (r.s τ').pc v = .x34 m jc acc' by
      obtain ⟨τ', h1', h2', h3', acc', h4'⟩ := hs
      exact Or.inr ⟨a', τ', h1', h2', hn', hD', v, m, jc, acc', by omega, h3', h4', htv⟩
    by_cases hvg : v = g
    · -- the reader read its own identifier: its next reads include `n^{m+1}_p`
      subst hvg
      have hlev := target_eq_anc (le_of_lt hl') (by omega : m ≤ h) (htg.trans hX)
      obtain ⟨acc', hpc'⟩ := pc_after_read r hev hpc
      have hpre : PreRead m jc ((r.s (τ + 1)).pc v) := by
        rcases hlev with ⟨rfl, rfl⟩ | ⟨-, hl'm⟩ <;> rcases hpc' with ⟨hj, hpc'⟩ | ⟨hj, hpc'⟩ <;>
          rw [hpc'] <;> simp [PreRead] <;> omega
      obtain ⟨τ', h1', h2', h3'⟩ :=
        read_of_pre r (by omega : m < h) hjc2 hτe' hpre (fun hp => hgn hp.incsx)
      exact ⟨τ', by omega, by omega, h3'⟩
    by_cases hent : ∃ g₀, f ≤ g₀ ∧ g₀ < τ ∧ Enters r v g₀
    · -- `v` completed a passage (and its exit section) before `τ`
      obtain ⟨g₀, hg1, hg2, hg3⟩ := hent
      have hnot : ¬ PreRead m jc ((r.s τ).pc v) := fun hp => hvg ((hI τ).uniq v g hp.incsx hgcs)
      obtain ⟨τ', h1', h2', h3'⟩ := read_of_pre r (by omega : m < h) hjc2
        (by omega : g₀ + 1 ≤ τ) (by rw [hg3.2]; trivial) hnot
      exact ⟨τ', by omega, by omega, h3'⟩
    · -- `v` is still in its entry section: `g` promotes it
      push Not at hent
      have hea := entry_persist r hI (a := f + 1) (b := τ + 1) (by omega) hEf haf (by
        intro t ht1 ht2 hen
        rcases Nat.lt_or_ge t τ with ht | ht
        · exact hent t (by omega) ht hen
        · have : t = τ := by omega
          subst this
          rw [(enters_facts r hI hen).1] at hev
          exact hvg (Ev.step.inj hev))
      have hfinish : ∀ g₀, τ + 1 ≤ g₀ → g₀ < e → Enters r v g₀ →
          ∃ τ', a' ≤ τ' ∧ τ' < e ∧ r.ev τ' = .step v ∧ ∃ acc', (r.s τ').pc v = .x34 m jc acc' := by
        intro g₀ hg1 hg2 hg3
        obtain ⟨τ', h1', h2', h3'⟩ :=
          read_before_next_entry r hI (by omega : m < h) hjc2 hg3.2 (by omega : g₀ + 1 ≤ e) he
        exact ⟨τ', by omega, h2', h3'⟩
      rcases promote_read r hI hev hpc hv' hvg hea.1 hea.2 hτe' hgn with ⟨g₀, hg1, hg2, hg3⟩ | hQ
      · exact hfinish g₀ hg1 (by omega) hg3
      · obtain ⟨g₀, hg1, hg2, hg3⟩ := fifo r hI hQ le_rfl h2 h3 he
        exact hfinish g₀ (by omega) hg2 hg3

/-- **Lemma 8** (core counting): while `p` waits during `[t₁, t₂]`, any other process `q` enters
the critical section at most `h + 2 = log n + 2` times at steps in `[t₁, t₂)`. -/
theorem bounded_waiting_core (hpq : p ≠ q)
    (hW : ∀ t, t₁ ≤ t → t ≤ t₂ → ((r.s t).pc p).Waiting) : cnt r q t₁ t₂ ≤ h + 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨e, he1, he2, he3, he4⟩ := last_entry r q (by omega : 0 < cnt r q t₁ t₂)
  obtain ⟨e', he1', he2', he3', he4'⟩ := last_entry r q (by omega : 0 < cnt r q t₁ e)
  have hnoent : ∀ t, t₁ ≤ t + 1 → t + 1 ≤ t₂ → ¬ Enters r p t := by
    intro t h1 h2 hen
    have := hW (t + 1) h1 h2; rw [hen.2] at this; simp [PC.Waiting] at this
  have key : ∃ π, t₁ ≤ π ∧ π ≤ e' ∧ p ∈ Q (r.s π) := by
    rcases lemma9 r hI hpq hW h le_rfl e' he3' (by omega) (by omega) with
      hl | ⟨a, τ, haτ, hτe, hn, hD, g, l', j', acc, hl', hev, hpc, htg⟩
    · exact hl
    obtain ⟨v, hv⟩ := node_some r hI hn τ haτ
    -- only `p` writes its leaf
    have hvp : v = p := by
      by_contra hvp
      obtain ⟨f, -, -, ⟨l'', hl'', hX⟩, -⟩ := node_change r hI hn haτ hv hvp
      have : h = l'' := anc_level_inj le_rfl hl'' hX
      subst this
      exact hvp (anc_leaf_inj hX).symm
    subst hvp
    have hv' : (r.s τ).mem.node (target (anc g l') j') = some v := by rw [htg]; exact hv
    have hgcs : (r.s τ).InCSX g := Or.inr (Or.inl (by rw [hpc]; trivial))
    have hvg : v ≠ g := fun h' => by
      subst h'; exact entry_not_incsx ((hD τ haτ (by omega)).entry_apply (hI τ)).1 hgcs
    obtain ⟨hE1, ha1⟩ := (hD (τ + 1) (by omega) (by omega)).entry_apply (hI _)
    rcases promote_read r hI hev hpc hv' hvg hE1 ha1 hτe ((enters_facts r hI he3').2.2 g) with
      ⟨t, ht1, ht2, ht3⟩ | hQ
    · exact absurd ht3 (not_enters_of_done r hI (hD (t + 1) (by omega) (by omega)))
    · exact ⟨e', he1', le_rfl, hQ⟩
  obtain ⟨π, hπ1, hπ2, hπ3⟩ := key
  obtain ⟨g₀, hg1, hg2, hg3⟩ := fifo r hI hπ3 hπ2 he2' he3' he3
  exact hnoent g₀ (by omega) (by omega) hg3

end main

end Podc.ConstantBarriersMutex.BW
