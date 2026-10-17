import Papers.PODC2015.CrashConsensusDigraph.AsyncCrash

/-!
# Algorithm WA (Wait-and-Average), Section 4.2

Algorithm WA proceeds in phases `p = 1, …, pend`. In phase `p` node `i` floods
`(vᵢ[p − 1], i, p)`; every message `(h, j, p)` received for the first time is recorded and
forwarded to all out-neighbours. With `heardᵢ[p]` the origins and `Rᵢ[p]` the (set of) values of
the recorded phase-`p` messages (including its own), `i` completes phase `p` as soon as
**Condition WAIT** holds: there is `Fᵢ ⊆ V − {i}`, `|Fᵢ| ≤ f`, with `reachᵢ(Fᵢ) ⊆ heardᵢ[p]`
(`Wait`). It then sets `vᵢ[p]` to the average of the set `Rᵢ[p]` and enters phase `p + 1`;
after phase `pend` it outputs `vᵢ[pend]`.

**Deviation from the literal pseudocode.** The paper's pseudocode resets `Rᵢ[p] := {vᵢ[p−1]}`,
`heardᵢ[p] := {i}` *on entering* phase `p`, so phase-`p` messages that arrived (and were
forwarded, hence will never be processed again) while `i` was still in phase `p − 1` are lost;
this can block a node forever even without crashes. We formalize the evident fix: the recorded
messages are kept per phase and never reset (`WS.heard`, `WS.R` are computed from the set `seen`
of recorded messages), and Condition WAIT is re-checked after every receipt and on entering a
phase (`advN`: the check-and-complete step `adv1` is iterated `pend + 1` times, enough to reach a
fixpoint).

The state is `WS`: current phase `ph` (`pend + 1` = finished), phase values `val` (`val 0` is
the input; `val q` is meaningful for `q < ph`), and `seen`.

This file also contains the *local* invariant `LI` of one node with respect to a global state,
and its preservation by the steps of the algorithm (`adv1_spec`, `advN_spec`, `recv_spec`,
`start_spec`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Local state of Algorithm WA. -/
structure WS (V : Type*) where
  /-- Current phase (`pend + 1` once finished). -/
  ph : ℕ
  /-- Phase values: `val 0` is the input, `val q` the value computed in phase `q`. -/
  val : ℕ → ℝ
  /-- Messages `(value, origin, phase)` recorded so far. -/
  seen : Finset (ℝ × V × ℕ)

/-- `heardᵢ[p]`: origins of the recorded phase-`p` messages. -/
noncomputable def WS.heard (s : WS V) (p : ℕ) : Finset V :=
  (s.seen.filter fun m => m.2.2 = p).image fun m => m.2.1

/-- `Rᵢ[p]`: the set of values of the recorded phase-`p` messages. -/
noncomputable def WS.R (s : WS V) (p : ℕ) : Finset ℝ :=
  (s.seen.filter fun m => m.2.2 = p).image fun m => m.1

/-- Average of a finite set of reals. -/
noncomputable def avg (S : Finset ℝ) : ℝ := (∑ x ∈ S, x) / S.card

/-- **Condition WAIT** for node `i` and heard set `H`. -/
def Wait (G : Digraph V) (f : ℕ) (i : V) (H : Finset V) : Prop :=
  ∃ F : Finset V, i ∉ F ∧ F.card ≤ f ∧ ∀ w, Reaches G F w i → w ∈ H

theorem Wait.self_mem {G : Digraph V} {f : ℕ} {i : V} {H : Finset V} (h : Wait G f i H) : i ∈ H := by
  obtain ⟨F, hi, -, hF⟩ := h
  exact hF i (Reaches.refl hi)

/-- Send `m` to every node (the model only transmits along edges of `G`). -/
noncomputable def bcast (m : ℝ × V × ℕ) : List (V × (ℝ × V × ℕ)) :=
  (univ : Finset V).toList.map fun b => (b, m)

theorem mem_bcast (m : ℝ × V × ℕ) (b : V) : (b, m) ∈ bcast m := by
  simp [bcast]

theorem snd_of_mem_bcast {m : ℝ × V × ℕ} {bm : V × (ℝ × V × ℕ)} (h : bm ∈ bcast m) : bm.2 = m := by
  simp only [bcast, List.mem_map] at h
  obtain ⟨b, -, rfl⟩ := h
  rfl

section Alg

variable (G : Digraph V) (f pend : ℕ)

open Classical in
/-- One check-and-complete step: if Condition WAIT holds in the current phase `p ≤ pend`,
compute `v[p]` and enter phase `p + 1` (flooding the own phase-`(p+1)` message if `p < pend`). -/
noncomputable def adv1 (i : V) (s : WS V) : WS V × List (V × (ℝ × V × ℕ)) :=
  if s.ph ≤ pend ∧ Wait G f i (s.heard s.ph) then
    if s.ph < pend then
      (⟨s.ph + 1, Function.update s.val s.ph (avg (s.R s.ph)),
        insert (avg (s.R s.ph), i, s.ph + 1) s.seen⟩, bcast (avg (s.R s.ph), i, s.ph + 1))
    else (⟨s.ph + 1, Function.update s.val s.ph (avg (s.R s.ph)), s.seen⟩, [])
  else (s, [])

/-- `k` check-and-complete steps. -/
noncomputable def advN (i : V) : ℕ → WS V → WS V × List (V × (ℝ × V × ℕ))
  | 0, s => (s, [])
  | k + 1, s => ((advN i k (adv1 G f pend i s).1).1,
      (adv1 G f pend i s).2 ++ (advN i k (adv1 G f pend i s).1).2)

/-- The initial state of a node with input `r` (phase 1, own message recorded). -/
def start0 (x : V) (r : ℝ) : WS V := ⟨1, fun _ => r, {(r, x, 1)}⟩

/-- **Algorithm WA** (with the fix described above), for phases `1, …, pend`. -/
noncomputable def wa : Algorithm V (ℝ × V × ℕ) (WS V) where
  start x r := ((advN G f pend x (pend + 1) (start0 x r)).1,
      bcast (r, x, 1) ++ (advN G f pend x (pend + 1) (start0 x r)).2)
  recv y s _ m := if m ∈ s.seen then (s, []) else
      ((advN G f pend y (pend + 1) ⟨s.ph, s.val, insert m s.seen⟩).1,
        bcast m ++ (advN G f pend y (pend + 1) ⟨s.ph, s.val, insert m s.seen⟩).2)
  out _ s := if pend < s.ph then some (s.val pend) else none

theorem wa_start (x : V) (r : ℝ) : (wa G f pend).start x r =
    ((advN G f pend x (pend + 1) (start0 x r)).1,
      bcast (r, x, 1) ++ (advN G f pend x (pend + 1) (start0 x r)).2) := rfl

theorem wa_recv (y : V) (s : WS V) (x : V) (m : ℝ × V × ℕ) : (wa G f pend).recv y s x m =
    if m ∈ s.seen then (s, []) else
      ((advN G f pend y (pend + 1) ⟨s.ph, s.val, insert m s.seen⟩).1,
        bcast m ++ (advN G f pend y (pend + 1) ⟨s.ph, s.val, insert m s.seen⟩).2) := rfl

theorem wa_out (x : V) (s : WS V) :
    (wa G f pend).out x s = if pend < s.ph then some (s.val pend) else none := rfl

end Alg

/-! ## The local invariant -/

/-- A recorded message `(h, j, p)` is *genuine* w.r.t. the global state `g`: `j` has entered
phase `p` and `h = vⱼ[p − 1]`. -/
def Genuine (g : V → WS V) (m : ℝ × V × ℕ) : Prop :=
  1 ≤ m.2.2 ∧ m.2.2 ≤ (g m.2.1).ph ∧ (g m.2.1).val (m.2.2 - 1) = m.1

/-- `s'` extends `s`: later phase, completed phase values unchanged, more recorded messages. -/
def Ext (s s' : WS V) : Prop := s.ph ≤ s'.ph ∧ (∀ q < s.ph, s'.val q = s.val q) ∧ s.seen ⊆ s'.seen

theorem Ext.refl (s : WS V) : Ext s s := ⟨le_rfl, fun _ _ => rfl, subset_rfl⟩

theorem Ext.trans {s₁ s₂ s₃ : WS V} (h₁ : Ext s₁ s₂) (h₂ : Ext s₂ s₃) : Ext s₁ s₃ :=
  ⟨h₁.1.trans h₂.1, fun q hq => (h₂.2.1 q (lt_of_lt_of_le hq h₁.1)).trans (h₁.2.1 q hq),
    h₁.2.2.trans h₂.2.2⟩

theorem Genuine.mono {g g' : V → WS V} (hg : ∀ j, Ext (g j) (g' j)) {m : ℝ × V × ℕ}
    (h : Genuine g m) : Genuine g' m := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2.trans (hg _).1, ?_⟩
  rw [(hg _).2.1 _ (by omega), h3]

theorem ext_update {g : V → WS V} {i : V} {s' : WS V} (h : Ext (g i) s') (j : V) :
    Ext (g j) (Function.update g i s' j) := by
  by_cases hj : j = i
  · subst hj; simpa using h
  · rw [Function.update_of_ne hj]; exact Ext.refl _

/-- The local invariant of node `i` in the global state `g`. -/
structure LI (G : Digraph V) (f pend : ℕ) (g : V → WS V) (inp : V → ℝ) (i : V) : Prop where
  ph_pos : 1 ≤ (g i).ph
  ph_le : (g i).ph ≤ pend + 1
  val0 : (g i).val 0 = inp i
  gen : ∀ m ∈ (g i).seen, Genuine g m
  own : ∀ p, 1 ≤ p → p ≤ (g i).ph → p ≤ pend → ((g i).val (p - 1), i, p) ∈ (g i).seen
  done : ∀ p, 1 ≤ p → p < (g i).ph → ∃ H : Finset V, Wait G f i H ∧
    (∀ j ∈ H, p - 1 < (g j).ph) ∧ (g i).val p = avg (H.image fun j => (g j).val (p - 1))

/-- `i` has no pending phase completion. -/
def Closed (G : Digraph V) (f pend : ℕ) (i : V) (s : WS V) : Prop :=
  ¬ (s.ph ≤ pend ∧ Wait G f i (s.heard s.ph))

variable {G : Digraph V} {f pend : ℕ}

theorem image_congr_val {H : Finset V} {g g' : V → WS V} {q : ℕ} (hH : ∀ j ∈ H, q < (g j).ph)
    (hg : ∀ j, Ext (g j) (g' j)) :
    (H.image fun j => (g' j).val q) = H.image fun j => (g j).val q :=
  Finset.image_congr fun j hj => (hg j).2.1 q (hH j hj)

/-- The local invariant is preserved when other nodes progress. -/
theorem LI.mono {g g' : V → WS V} {inp : V → ℝ} {i : V} (h : LI G f pend g inp i)
    (hg : ∀ j, Ext (g j) (g' j)) (hi : g' i = g i) : LI G f pend g' inp i where
  ph_pos := hi ▸ h.ph_pos
  ph_le := hi ▸ h.ph_le
  val0 := hi ▸ h.val0
  gen m hm := (h.gen m (hi ▸ hm)).mono hg
  own p h1 h2 h3 := hi ▸ h.own p h1 (hi ▸ h2) h3
  done p h1 h2 := by
    obtain ⟨H, hW, hH, hv⟩ := h.done p h1 (hi ▸ h2)
    refine ⟨H, hW, fun j hj => lt_of_lt_of_le (hH j hj) (hg j).1, ?_⟩
    rw [hi, hv, image_congr_val hH hg]

theorem mem_heard {s : WS V} {p : ℕ} {j : V} : j ∈ s.heard p ↔ ∃ h, (h, j, p) ∈ s.seen := by
  simp only [WS.heard, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨h, j', p'⟩, ⟨hm, rfl⟩, rfl⟩; exact ⟨h, hm⟩
  · rintro ⟨h, hm⟩; exact ⟨(h, j, p), ⟨hm, rfl⟩, rfl⟩

theorem mem_R {s : WS V} {p : ℕ} {h : ℝ} : h ∈ s.R p ↔ ∃ j, (h, j, p) ∈ s.seen := by
  simp only [WS.R, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨h', j, p'⟩, ⟨hm, rfl⟩, rfl⟩; exact ⟨j, hm⟩
  · rintro ⟨j, hm⟩; exact ⟨(h, j, p), ⟨hm, rfl⟩, rfl⟩

theorem heard_mono {s s' : WS V} (h : s.seen ⊆ s'.seen) (p : ℕ) : s.heard p ⊆ s'.heard p :=
  fun _ hj => mem_heard.mpr (by obtain ⟨x, hx⟩ := mem_heard.mp hj; exact ⟨x, h hx⟩)

/-- With genuine recorded messages, `Rᵢ[p]` is the set of phase-`(p−1)` values of `heardᵢ[p]`. -/
theorem R_eq_image {g : V → WS V} {s : WS V} (hgen : ∀ m ∈ s.seen, Genuine g m) (p : ℕ) :
    s.R p = (s.heard p).image fun j => (g j).val (p - 1) := by
  ext h
  rw [mem_R, mem_image]
  constructor
  · rintro ⟨j, hm⟩
    exact ⟨j, mem_heard.mpr ⟨h, hm⟩, (hgen _ hm).2.2⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨h', hm⟩ := mem_heard.mp hj
    have := (hgen _ hm).2.2
    simp only at this
    exact ⟨j, this ▸ hm⟩

/-- Specification of one check-and-complete step. -/
theorem adv1_spec {g : V → WS V} {inp : V → ℝ} {i : V} {s : WS V} (hgs : g i = s)
    (hLI : LI G f pend g inp i) :
    let r := adv1 G f pend i s
    Ext s r.1 ∧ LI G f pend (Function.update g i r.1) inp i ∧
      (∀ bm ∈ r.2, Genuine (Function.update g i r.1) bm.2) ∧
      (∀ m ∈ r.1.seen, m ∉ s.seen → ∀ b, (b, m) ∈ r.2) ∧
      ((r.1.ph = s.ph + 1) ∨ (r = (s, []) ∧ Closed G f pend i s)) := by
  intro r
  by_cases hc : s.ph ≤ pend ∧ Wait G f i (s.heard s.ph)
  swap
  · have hr : r = (s, []) := by simp only [r, adv1, hc, ↓reduceIte]
    rw [hr]
    have hu : Function.update g i s = g := by rw [← hgs, Function.update_eq_self]
    refine ⟨Ext.refl _, ?_, ?_, fun m hm hm' => absurd hm hm', Or.inr ⟨rfl, hc⟩⟩
    · show LI G f pend (Function.update g i s) inp i
      rw [hu]; exact hLI
    · intro bm hbm; simp at hbm
  set p := s.ph with hp
  set x := avg (s.R p) with hx
  have hp1 : 1 ≤ p := by rw [hp, ← hgs]; exact hLI.ph_pos
  have hval0 : s.val 0 = inp i := hgs ▸ hLI.val0
  have hown : ∀ q, 1 ≤ q → q ≤ s.ph → q ≤ pend → (s.val (q - 1), i, q) ∈ s.seen := by
    rw [← hgs]; exact hLI.own
  have hdone : ∀ q, 1 ≤ q → q < s.ph → ∃ H : Finset V, Wait G f i H ∧
      (∀ j ∈ H, q - 1 < (g j).ph) ∧ s.val q = avg (H.image fun j => (g j).val (q - 1)) := by
    rw [← hgs]; exact hLI.done
  -- the new state, uniformly
  set s' : WS V := ⟨p + 1, Function.update s.val p x,
    if p < pend then insert (x, i, p + 1) s.seen else s.seen⟩ with hs'
  set out : List (V × (ℝ × V × ℕ)) := if p < pend then bcast (x, i, p + 1) else [] with hout
  have hr : r = (s', out) := by
    simp only [r, adv1, s', out]
    split_ifs <;> rfl
  rw [hr]
  simp only
  have hext : Ext s s' := by
    refine ⟨by simp only [s']; omega, fun q hq => ?_, ?_⟩
    · simp only [s']; rw [Function.update_of_ne (by omega)]
    · simp only [s']; split_ifs
      · exact subset_insert _ _
      · exact subset_rfl
  set g' := Function.update g i s' with hg'
  have hgg' : ∀ j, Ext (g j) (g' j) := ext_update (hgs ▸ hext)
  have hg'i : g' i = s' := by simp [g']
  have hnew : Genuine g' (x, i, p + 1) := by
    refine ⟨by simp, by simp [hg'i, s'], ?_⟩
    simp [hg'i, s']
  have hgenS : ∀ m ∈ s.seen, Genuine g' m := fun m hm => (hLI.gen m (hgs ▸ hm)).mono hgg'
  have hseen' : ∀ m ∈ s'.seen, m ∈ s.seen ∨ (p < pend ∧ m = (x, i, p + 1)) := by
    intro m hm
    simp only [s'] at hm
    split_ifs at hm with hlt
    · rcases mem_insert.mp hm with h | h
      · exact Or.inr ⟨hlt, h⟩
      · exact Or.inl h
    · exact Or.inl hm
  refine ⟨hext, ?_, ?_, ?_, Or.inl rfl⟩
  · -- the local invariant
    refine ⟨by rw [hg'i]; simp only [s']; omega, by rw [hg'i]; simp only [s']; omega, ?_, ?_, ?_, ?_⟩
    · rw [hg'i]; simp only [s']; rw [Function.update_of_ne (by omega)]; exact hval0
    · intro m hm
      rw [hg'i] at hm
      rcases hseen' m hm with h | ⟨-, rfl⟩
      · exact hgenS m h
      · exact hnew
    · intro q h1 h2 h3
      rw [hg'i] at h2 ⊢
      simp only [s'] at h2
      by_cases hq : q = p + 1
      · subst hq
        have hlt : p < pend := by omega
        simp only [s', hlt, ↓reduceIte, Nat.add_sub_cancel, Function.update_self]
        exact mem_insert_self _ _
      · have := hown q h1 (by omega) h3
        simp only [s']
        rw [Function.update_of_ne (by omega)]
        split_ifs
        · exact mem_insert_of_mem this
        · exact this
    · intro q h1 h2
      rw [hg'i] at h2 ⊢
      simp only [s'] at h2
      by_cases hq : q = p
      · subst hq
        refine ⟨s.heard p, hc.2, fun j hj => ?_, ?_⟩
        · obtain ⟨h, hm⟩ := mem_heard.mp hj
          have := (hgenS _ hm).2.1
          simp only at this
          omega
        · simp only [s', Function.update_self, x]
          rw [R_eq_image hgenS]
      · obtain ⟨H, hW, hH, hv⟩ := hdone q h1 (by omega)
        refine ⟨H, hW, fun j hj => lt_of_lt_of_le (hH j hj) (hgg' j).1, ?_⟩
        simp only [s']
        rw [Function.update_of_ne (by omega), hv, image_congr_val hH hgg']
  · intro bm hbm
    simp only [out] at hbm
    split_ifs at hbm
    · rw [snd_of_mem_bcast hbm]; exact hnew
    · simp at hbm
  · intro m hm hm' b
    rcases hseen' m hm with h | ⟨hlt, rfl⟩
    · exact absurd h hm'
    · simp only [out, hlt, ↓reduceIte]; exact mem_bcast _ _

theorem advN_closed {i : V} {s : WS V} (h : Closed G f pend i s) :
    ∀ k, advN G f pend i k s = (s, []) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : adv1 G f pend i s = (s, []) := by
      unfold Closed at h
      simp only [adv1, h, ↓reduceIte]
    simp only [advN, h1, ih, List.append_nil]

/-- Specification of `k` check-and-complete steps. -/
theorem advN_spec {inp : V → ℝ} {i : V} (k : ℕ) :
    ∀ (g : V → WS V) (s : WS V), g i = s → LI G f pend g inp i →
    let r := advN G f pend i k s
    Ext s r.1 ∧ LI G f pend (Function.update g i r.1) inp i ∧
      (∀ bm ∈ r.2, Genuine (Function.update g i r.1) bm.2) ∧
      (∀ m ∈ r.1.seen, m ∉ s.seen → ∀ b, (b, m) ∈ r.2) ∧
      (r.1.ph = s.ph + k ∨ Closed G f pend i r.1) := by
  induction k with
  | zero =>
    intro g s hgs hLI
    show Ext s s ∧ LI G f pend (Function.update g i s) inp i ∧
      (∀ bm ∈ ([] : List (V × (ℝ × V × ℕ))), Genuine (Function.update g i s) bm.2) ∧
      (∀ m ∈ s.seen, m ∉ s.seen → ∀ b, (b, m) ∈ ([] : List (V × (ℝ × V × ℕ)))) ∧
      (s.ph = s.ph + 0 ∨ Closed G f pend i s)
    have hu : Function.update g i s = g := by rw [← hgs, Function.update_eq_self]
    rw [hu]
    exact ⟨Ext.refl _, hLI, by simp, fun m hm hm' => absurd hm hm', Or.inl rfl⟩
  | succ k ih =>
    intro g s hgs hLI
    obtain ⟨e1, l1, gen1, new1, ph1⟩ := adv1_spec hgs hLI
    set r1 := adv1 G f pend i s with hr1
    obtain ⟨e2, l2, gen2, new2, ph2⟩ := ih (Function.update g i r1.1) r1.1 (by simp) l1
    set r2 := advN G f pend i k r1.1 with hr2
    have hupd : Function.update (Function.update g i r1.1) i r2.1 = Function.update g i r2.1 := by
      simp
    rw [hupd] at l2 gen2
    show Ext s r2.1 ∧ LI G f pend (Function.update g i r2.1) inp i ∧
      (∀ bm ∈ r1.2 ++ r2.2, Genuine (Function.update g i r2.1) bm.2) ∧
      (∀ m ∈ r2.1.seen, m ∉ s.seen → ∀ b, (b, m) ∈ r1.2 ++ r2.2) ∧
      (r2.1.ph = s.ph + (k + 1) ∨ Closed G f pend i r2.1)
    refine ⟨e1.trans e2, l2, ?_, ?_, ?_⟩
    · intro bm hbm
      rcases List.mem_append.mp hbm with h | h
      · refine (gen1 bm h).mono fun j => ?_
        by_cases hj : j = i
        · subst hj; simpa using e2
        · simp [Function.update_of_ne hj, Ext.refl]
      · exact gen2 bm h
    · intro m hm hm' b
      by_cases h1 : m ∈ r1.1.seen
      · exact List.mem_append_left _ (new1 m h1 hm' b)
      · exact List.mem_append_right _ (new2 m hm h1 b)
    · rcases ph1 with h | ⟨h, hcl⟩
      · rcases ph2 with h' | h'
        · left; omega
        · right; exact h'
      · right
        have : r2 = (s, []) := by rw [hr2, h]; exact advN_closed hcl k
        rw [this]
        exact hcl

/-- After `pend + 1` steps, no phase completion is pending. -/
theorem advN_full {g : V → WS V} {inp : V → ℝ} {i : V} {s : WS V} (hgs : g i = s)
    (hLI : LI G f pend g inp i) :
    let r := advN G f pend i (pend + 1) s
    Ext s r.1 ∧ LI G f pend (Function.update g i r.1) inp i ∧
      (∀ bm ∈ r.2, Genuine (Function.update g i r.1) bm.2) ∧
      (∀ m ∈ r.1.seen, m ∉ s.seen → ∀ b, (b, m) ∈ r.2) ∧ Closed G f pend i r.1 := by
  obtain ⟨e, l, gen, new, ph⟩ := advN_spec (pend + 1) g s hgs hLI
  refine ⟨e, l, gen, new, ?_⟩
  rcases ph with h | h
  · exfalso
    have := l.ph_le
    simp only [Function.update_self] at this
    have := hLI.ph_pos
    rw [hgs] at this
    omega
  · exact h

/-- Specification of the receive step. -/
theorem recv_spec {g : V → WS V} {inp : V → ℝ} {i x : V} {m : ℝ × V × ℕ}
    (hLI : LI G f pend g inp i) (hcl : Closed G f pend i (g i)) (hm : Genuine g m) :
    let r := (wa G f pend).recv i (g i) x m
    Ext (g i) r.1 ∧ LI G f pend (Function.update g i r.1) inp i ∧
      (∀ bm ∈ r.2, Genuine (Function.update g i r.1) bm.2) ∧
      (∀ m' ∈ r.1.seen, m' ∉ (g i).seen → ∀ b, (b, m') ∈ r.2) ∧ Closed G f pend i r.1 ∧
      m ∈ r.1.seen := by
  intro r
  by_cases hs : m ∈ (g i).seen
  · have hr : r = (g i, []) := by
      show (wa G f pend).recv i (g i) x m = _
      rw [wa_recv]; simp only [hs, ↓reduceIte]
    rw [hr]
    have hu : Function.update g i (g i) = g := Function.update_eq_self _ _
    refine ⟨Ext.refl _, ?_, by simp, fun m hm hm' => absurd hm hm', hcl, hs⟩
    show LI G f pend (Function.update g i (g i)) inp i
    rw [hu]; exact hLI
  set s1 : WS V := ⟨(g i).ph, (g i).val, insert m (g i).seen⟩ with hs1
  have hr : r = ((advN G f pend i (pend + 1) s1).1, bcast m ++ (advN G f pend i (pend + 1) s1).2) := by
    show (wa G f pend).recv i (g i) x m = _
    rw [wa_recv]; simp only [hs, ↓reduceIte]; rfl
  rw [hr]
  have he1 : Ext (g i) s1 := ⟨le_rfl, fun _ _ => rfl, subset_insert _ _⟩
  set g1 := Function.update g i s1 with hg1
  have hg1i : g1 i = s1 := by simp [g1]
  have hgg1 : ∀ j, Ext (g j) (g1 j) := ext_update he1
  have l1 : LI G f pend g1 inp i := by
    refine ⟨by rw [hg1i]; exact hLI.ph_pos, by rw [hg1i]; exact hLI.ph_le,
      by rw [hg1i]; exact hLI.val0, ?_, ?_, ?_⟩
    · intro m' hm'
      rw [hg1i] at hm'
      rcases mem_insert.mp hm' with h | h
      · subst h; exact hm.mono hgg1
      · exact (hLI.gen m' h).mono hgg1
    · intro p h1 h2 h3
      rw [hg1i] at h2 ⊢
      exact mem_insert_of_mem (hLI.own p h1 h2 h3)
    · intro p h1 h2
      rw [hg1i] at h2 ⊢
      obtain ⟨H, hW, hH, hv⟩ := hLI.done p h1 h2
      exact ⟨H, hW, fun j hj => lt_of_lt_of_le (hH j hj) (hgg1 j).1, by
        rw [hv, image_congr_val hH hgg1]⟩
  obtain ⟨e2, l2, gen2, new2, cl2⟩ := advN_full hg1i l1
  set r2 := advN G f pend i (pend + 1) s1 with hr2
  have hupd : Function.update g1 i r2.1 = Function.update g i r2.1 := by simp [g1]
  rw [hupd] at l2 gen2
  refine ⟨he1.trans e2, l2, ?_, ?_, cl2, e2.2.2 (mem_insert_self _ _)⟩
  · intro bm hbm
    rcases List.mem_append.mp hbm with h | h
    · rw [snd_of_mem_bcast h]
      exact hm.mono (ext_update (he1.trans e2))
    · exact gen2 bm h
  · intro m' hm' hm'' b
    by_cases h1 : m' ∈ s1.seen
    · rcases mem_insert.mp h1 with h | h
      · subst h; exact List.mem_append_left _ (mem_bcast _ _)
      · exact absurd h hm''
    · exact List.mem_append_right _ (new2 m' hm' h1 b)

/-- Specification of the start step, w.r.t. any global state agreeing with the started state. -/
theorem start_spec {g : V → WS V} {inp : V → ℝ} {x : V}
    (hgx : g x = ((wa G f pend).start x (inp x)).1) :
    LI G f pend g inp x ∧ Closed G f pend x (g x) ∧
      (∀ bm ∈ ((wa G f pend).start x (inp x)).2, Genuine g bm.2) ∧
      (∀ m ∈ (g x).seen, ∀ b, (b, m) ∈ ((wa G f pend).start x (inp x)).2) := by
  rw [wa_start] at hgx ⊢
  set g0 := Function.update g x (start0 x (inp x)) with hg0
  have hg0x : g0 x = start0 x (inp x) := by simp [g0]
  have l0 : LI G f pend g0 inp x := by
    refine ⟨by rw [hg0x]; rfl, by rw [hg0x]; simp [start0], by rw [hg0x]; rfl, ?_, ?_, ?_⟩
    · intro m hm
      rw [hg0x] at hm
      simp only [start0, mem_singleton] at hm
      subst hm
      refine ⟨le_rfl, by rw [hg0x]; rfl, by rw [hg0x]; rfl⟩
    · intro p h1 h2 h3
      rw [hg0x] at h2 ⊢
      simp only [start0] at h2 ⊢
      obtain rfl : p = 1 := by omega
      simp
    · intro p h1 h2
      rw [hg0x] at h2
      simp only [start0] at h2
      omega
  obtain ⟨e, l, gen, new, cl⟩ := advN_full hg0x l0
  have hupd : Function.update g0 x (advN G f pend x (pend + 1) (start0 x (inp x))).1 = g := by
    rw [← hgx]; simp [g0]
  rw [hupd] at l gen
  refine ⟨l, hgx ▸ cl, ?_, ?_⟩
  · intro bm hbm
    rcases List.mem_append.mp hbm with h | h
    · rw [snd_of_mem_bcast h]
      refine ⟨le_rfl, ?_, ?_⟩
      · simp only; rw [hgx]; exact e.1
      · simp only; rw [hgx]; exact e.2.1 0 (by simp [start0])
    · exact gen bm h
  · intro m hm b
    rw [hgx] at hm
    by_cases h1 : m ∈ (start0 x (inp x)).seen
    · simp only [start0, mem_singleton] at h1
      subst h1
      exact List.mem_append_left _ (mem_bcast _ _)
    · exact List.mem_append_right _ (new m hm h1 b)

end CrashConsensusDigraph
