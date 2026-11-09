import Papers.PODC2016.OhRAMAtomicMemory.LivenessInv

/-!
# Executions of `proto`: per-step facts used by the liveness proof
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM.Liveness

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]
variable {Vr : Variant} {next : W → T → T} {v₀ : V}

namespace Ex

variable (e : (proto (R := R) (S := S) Vr next v₀).Exec)

/-- Local state of writer `w` at time `t`. -/
abbrev wl (w : W) (t : ℕ) : WLoc S T V := ((e.cfg t).loc (.wr w)).w
/-- Local state of reader `r` at time `t`. -/
abbrev rl (r : R) (t : ℕ) : RLoc S T V := ((e.cfg t).loc (.rd r)).r
/-- Local state of server `s` at time `t`. -/
abbrev sl (s : S) (t : ℕ) : SLoc W R S T V := ((e.cfg t).loc (.sv s)).s

lemma step_at {t : ℕ} {s : Step (Node W R S) (register V v₀) (Msg R T V) Empty}
    (hs : e.stp t = s) : (proto Vr next v₀).step (e.cfg t) s = some (e.cfg (t + 1), e.lbl t) := by
  rw [← hs]; exact e.step t

lemma rinv (t : ℕ) : RInv (e.cfg t) := rInv_of_reach (e.reach t)

lemma hinv (t : ℕ) : HInv (e.cfg t) (e.hist t) := hInv_of_reach (e.reach t)

/-- How the local state of `p` evolves in one step. -/
lemma loc_cases (t : ℕ) (p : Node W R S) :
    (e.cfg (t + 1)).loc p = (e.cfg t).loc p ∨
    (∃ o out, e.stp t = .inv p o ∧
      (proto Vr next v₀).invoke p o ((e.cfg t).loc p) = some ((e.cfg (t + 1)).loc p, out) ∧
      e.cfg (t + 1) = (e.cfg t).apply p ((e.cfg (t + 1)).loc p) out (e.cfg t).net) ∨
    (∃ src m out resp, e.stp t = .recv src p m ∧
      (proto Vr next v₀).receive p src m ((e.cfg t).loc p) =
        some ((e.cfg (t + 1)).loc p, out, resp)) := by
  rcases step_cases (e.step t) with ⟨hloc, -, -, -, -⟩ | ⟨q, o, l, out, hs, -, -, hinv, hC⟩ |
      ⟨src, dst, m, l, out, r, hs, -, -, hrec, hC, -⟩
  · exact Or.inl (congrFun hloc p)
  · by_cases hq : q = p
    · subst hq
      have hl : (e.cfg (t + 1)).loc q = l := by rw [hC]; simp [Config.apply]
      rw [hl]
      exact Or.inr (Or.inl ⟨o, out, hs, hinv, hC⟩)
    · left; rw [hC]; simp [Config.apply, Function.update_of_ne (Ne.symm hq)]
  · by_cases hq : dst = p
    · subst hq
      have hl : (e.cfg (t + 1)).loc dst = l := by rw [hC]; simp [Config.apply]
      rw [hl]
      exact Or.inr (Or.inr ⟨src, m, out, r, hs, hrec⟩)
    · left; rw [hC]; simp [Config.apply, Function.update_of_ne (Ne.symm hq)]

/-- A reception step. -/
lemma recv_at {t : ℕ} {src dst : Node W R S} {m : Msg R T V} (hs : e.stp t = .recv src dst m) :
    ∃ out resp, (proto Vr next v₀).receive dst src m ((e.cfg t).loc dst) =
        some ((e.cfg (t + 1)).loc dst, out, resp) ∧
      e.cfg (t + 1) = (e.cfg t).apply dst ((e.cfg (t + 1)).loc dst) out
        ((e.cfg t).net.erase (src, dst, m)) ∧ e.lbl t = resp.map (Label.ret dst) := by
  rcases step_cases (step_at e hs) with ⟨-, -, -, -, hne⟩ | ⟨q, o, l, out, hs', -⟩ |
      ⟨src', dst', m', l, out, r, hs', -, -, hrec, hC, hl⟩
  · exact absurd rfl (hne src dst m)
  · cases hs'
  · cases hs'
    have hl' : (e.cfg (t + 1)).loc dst = l := by rw [hC]; simp [Config.apply]
    rw [hl']
    exact ⟨out, r, hrec, hC, hl⟩

lemma mem_net_of_out {t : ℕ} {p : Node W R S} {l : Loc W R S T V}
    {out : Multiset (Node W R S × Msg R T V)} {net : Multiset (Node W R S × Node W R S × Msg R T V)}
    (hC : e.cfg (t + 1) = (e.cfg t).apply p l out net) {d : Node W R S} {m : Msg R T V}
    (hm : (d, m) ∈ out) : (p, d, m) ∈ (e.cfg (t + 1)).net := by
  rw [hC]
  exact Multiset.mem_add.2 (Or.inr (mem_outMsgs.2 ⟨rfl, hm⟩))

/-! ### Busy clients -/

lemma not_busy_zero (p : Node W R S) : ¬ Busy p ((e.cfg 0).loc p) := by
  rw [e.init]
  cases p <;> simp [Busy, Protocol.initCfg, proto, initLoc]

/-- If the operation pending at `T` never returns, `p` is busy from `T` on. -/
lemma busy_of_no_resp {p : Node W R S} {T : ℕ}
    (hpend : (respsOf (e.hist T) p).length < (opsOf (e.hist T) p).length)
    (H : ∀ t, (respsOf (e.hist t) p).length ≤ (respsOf (e.hist T) p).length) (t : ℕ)
    (ht : T ≤ t) : Busy p ((e.cfg t).loc p) := by
  rcases hinv e t p with ⟨-, hb⟩ | ⟨he, -⟩
  · exact hb
  · have h1 := Exec.ops_le e ht p
    have h2 := H t
    omega

lemma exists_last_false {P : ℕ → Prop} (h0 : ¬ P 0) {T : ℕ} (hT : P T) :
    ∃ t₀ < T, ¬ P t₀ ∧ ∀ t, t₀ < t → t ≤ T → P t := by
  induction T with
  | zero => exact absurd hT h0
  | succ T ih =>
    by_cases hP : P T
    · obtain ⟨t₀, ht₀, hn, hall⟩ := ih hP
      refine ⟨t₀, by omega, hn, fun t h1 h2 => ?_⟩
      rcases Nat.lt_or_ge t (T + 1) with h | h
      · exact hall t h1 (by omega)
      · obtain rfl : t = T + 1 := by omega
        exact hT
    · refine ⟨T, by omega, hP, fun t h1 h2 => ?_⟩
      obtain rfl : t = T + 1 := by omega
      exact hT

/-- A client becomes busy only by an invocation. -/
lemma invoke_of_busy {p : Node W R S} {t : ℕ} (h0 : ¬ Busy p ((e.cfg t).loc p))
    (h1 : Busy p ((e.cfg (t + 1)).loc p)) :
    ∃ o out, (proto Vr next v₀).invoke p o ((e.cfg t).loc p) = some ((e.cfg (t + 1)).loc p, out) ∧
      e.cfg (t + 1) = (e.cfg t).apply p ((e.cfg (t + 1)).loc p) out (e.cfg t).net := by
  rcases loc_cases e t p with h | ⟨o, out, -, hinv, hC⟩ | ⟨src, m, out, resp, -, hrec⟩
  · rw [h] at h1; exact absurd h1 h0
  · exact ⟨o, out, hinv, hC⟩
  · obtain ⟨hb1, hb2⟩ := receive_busy hrec
    cases resp with
    | none => exact absurd ((hb2 rfl).1 h1) h0
    | some v => exact absurd (hb1 rfl).1 h0

/-! ### Correct servers -/

open Classical in
/-- At least `|S|/2 + 1` servers are correct. -/
lemma card_correct {f : ℕ} (hres : ServerResilient e f) (hf : 2 * f < Fintype.card S) :
    maj S ≤ (Finset.univ.filter (fun s : S => e.Correct (.sv s))).card := by
  have hex : ∀ s : S, ∃ T, ¬ e.Correct (.sv s) → Node.sv s ∈ (e.cfg T).crashed := by
    intro s
    by_cases hs : e.Correct (.sv s)
    · exact ⟨0, fun h => absurd hs h⟩
    · simp only [Protocol.Exec.Correct, not_forall, not_not] at hs
      obtain ⟨T, hT⟩ := hs
      exact ⟨T, fun _ => hT⟩
  choose g hg using hex
  let B := Finset.univ.sup g
  have hsub : Finset.univ.filter (fun s : S => ¬ e.Correct (.sv s)) ⊆
      Finset.univ.filter (fun s : S => Node.sv s ∈ (e.cfg B).crashed) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact e.crashed_mono (Finset.le_sup (Finset.mem_univ s)) (hg s hs)
  have h1 := (Finset.card_le_card hsub).trans (hres B)
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
    (fun s => e.Correct (.sv s))
  simp only [Finset.card_univ] at h2
  simp only [maj]
  have := Nat.div_mul_le_self (Fintype.card S) 2
  omega

lemma card_le_length {A : List (S × T × V)} {P : S → Prop} [DecidablePred P]
    (h : ∀ s, P s → s ∈ A.map Prod.fst) :
    (Finset.univ.filter P).card ≤ A.length := by
  calc (Finset.univ.filter P).card ≤ (A.map Prod.fst).toFinset.card := by
        refine Finset.card_le_card fun s hs => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        exact List.mem_toFinset.2 (h s hs)
    _ ≤ (A.map Prod.fst).length := List.toFinset_card_le _
    _ = A.length := List.length_map _

/-! ### Writers -/

lemma wr_step {w : W} {t : ℕ} (hb : Busy (.wr w) ((e.cfg t).loc (.wr w)))
    (hb' : Busy (.wr w) ((e.cfg (t + 1)).loc (.wr w))) :
    (∃ ack', wl e w (t + 1) = { wl e w t with ack := ack' } ∧ (wl e w t).ack ⊆ ack' ∧
      ack'.length ≤ (wl e w t).ack.length + 1 ∧ (ack'.length ≠ maj S ∨ ack' = (wl e w t).ack) ∧
      ∀ s m, e.stp t = .recv (.sv s) (.wr w) m → ack' = (wRecord Vr s m (wl e w t)).ack) ∨
    (∃ val, (wl e w t).phase = .disc val ∧ (wl e w (t + 1)).phase = .upd ∧
      (wl e w (t + 1)).ack = [] ∧
      ∀ s, (Node.wr w, Node.sv s, Msg.writeRequest (wl e w (t + 1)).tag (wl e w (t + 1)).val
        (wl e w (t + 1)).op) ∈ (e.cfg (t + 1)).net) := by
  simp only [Busy] at hb hb'
  by_cases hrecv : ∃ s m, e.stp t = .recv (.sv s) (.wr w) m
  · obtain ⟨s, m, hs⟩ := hrecv
    obtain ⟨out, resp, hrec, hC, -⟩ := recv_at e hs
    obtain ⟨-, -, hx⟩ := receive_wr_sv hrec
    obtain ⟨ack', hrecd, hsub, hlen⟩ := wRecord_spec (Vr := Vr) s m (wl e w t)
    rw [hrecd] at hx
    rcases wWait_spec (R := R) (next := next) w { wl e w t with ack := ack' } with
      ⟨hne, hw⟩ | ⟨-, val, hph, hw⟩ | ⟨-, hph, hw⟩ <;> rw [hw] at hx <;>
      simp only [Prod.mk.injEq] at hx
    · obtain ⟨h1, -, -⟩ := hx
      left
      refine ⟨ack', h1, hsub, hlen, ?_, fun s' m' hs' => ?_⟩
      · rcases hne with hne | hne
        · exact Or.inl hne
        · exact absurd hne hb
      · rw [hs] at hs'
        simp only [Step.recv.injEq, Node.sv.injEq, true_and] at hs'
        obtain ⟨rfl, rfl⟩ := hs'
        rw [hrecd]
    · obtain ⟨h1, h2, -⟩ := hx
      replace h1 : wl e w (t + 1) = _ := h1
      right
      refine ⟨val, hph, by rw [h1], by rw [h1], fun s' => ?_⟩
      rw [h1]
      exact mem_net_of_out e hC (by rw [h2]; exact mem_bcast.2 ⟨s', rfl⟩)
    · obtain ⟨h1, -, -⟩ := hx
      exact absurd (by rw [h1]) hb'
  · push Not at hrecv
    have hsame : (e.cfg (t + 1)).loc (.wr w) = (e.cfg t).loc (.wr w) → ∃ ack',
        wl e w (t + 1) = { wl e w t with ack := ack' } ∧ (wl e w t).ack ⊆ ack' ∧
        ack'.length ≤ (wl e w t).ack.length + 1 ∧ (ack'.length ≠ maj S ∨ ack' = (wl e w t).ack) ∧
        ∀ s m, e.stp t = .recv (.sv s) (.wr w) m → ack' = (wRecord Vr s m (wl e w t)).ack := by
      intro h
      refine ⟨(wl e w t).ack, by simp only [wl, h], List.Subset.refl _, by omega, Or.inr rfl,
        fun s m hs => absurd hs (hrecv s m)⟩
    rcases loc_cases e t (.wr w) with h | ⟨o, out, -, hinv, -⟩ | ⟨src, m, out, resp, hs, hrec⟩
    · exact Or.inl (hsame h)
    · obtain ⟨val, -, hw, -, -⟩ := invoke_wr hinv
      exact absurd (wInvoke_spec hw).1 hb
    · obtain ⟨-, -, ⟨s, rfl, -⟩ | ⟨hl, -, -⟩⟩ := receive_wr hrec
      · exact absurd hs (hrecv s m)
      · exact Or.inl (hsame hl)

/-- A writer that stays in the phase `ph` from time `a` on (after resetting its acknowledgments)
keeps its tag, value and operation counter, and has fewer than `|S|/2 + 1` acknowledgments. -/
lemma wr_stage {w : W} {a : ℕ} {ph : WPhase V}
    (hb : ∀ t ≥ a, Busy (.wr w) ((e.cfg t).loc (.wr w)))
    (hph : ∀ t ≥ a, (wl e w t).phase = ph) (hack : (wl e w a).ack = []) :
    (∀ t ≥ a, (wl e w t).tag = (wl e w a).tag ∧ (wl e w t).op = (wl e w a).op ∧
      (wl e w t).val = (wl e w a).val ∧ (wl e w t).ack.length < maj S) ∧
    (∀ t ≥ a, (wl e w t).ack ⊆ (wl e w (t + 1)).ack ∧
      ∀ s m, e.stp t = .recv (.sv s) (.wr w) m →
        (wl e w (t + 1)).ack = (wRecord Vr s m (wl e w t)).ack) := by
  have hstep : ∀ t ≥ a, ∃ ack', wl e w (t + 1) = { wl e w t with ack := ack' } ∧
      (wl e w t).ack ⊆ ack' ∧ ack'.length ≤ (wl e w t).ack.length + 1 ∧
      (ack'.length ≠ maj S ∨ ack' = (wl e w t).ack) ∧
      ∀ s m, e.stp t = .recv (.sv s) (.wr w) m → ack' = (wRecord Vr s m (wl e w t)).ack := by
    intro t ht
    rcases wr_step e (hb t ht) (hb (t + 1) (by omega)) with h | ⟨val, h1, h2, -⟩
    · exact h
    · have h3 := hph t ht
      have h4 := hph (t + 1) (by omega)
      rw [h1] at h3; rw [h2] at h4
      rw [← h4] at h3; cases h3
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, rfl, rfl, by rw [hack]; exact one_le_maj S⟩
    | succ t ht ih =>
      obtain ⟨ack', h1, -, hlen, hne, -⟩ := hstep t ht
      rw [h1]
      refine ⟨ih.1, ih.2.1, ih.2.2.1, ?_⟩
      have := ih.2.2.2
      rcases hne with hne | hne
      · simp only; omega
      · simp only; rw [hne]; exact this
  · obtain ⟨ack', h1, hsub, -, -, hrecv⟩ := hstep t ht
    rw [h1]
    exact ⟨hsub, hrecv⟩

open Classical in
/-- A writer cannot stay forever in a phase in which every correct server's reply is
eventually accepted. -/
lemma wr_stage_false {w : W} {a : ℕ} {ph : WPhase V}
    (hb : ∀ t ≥ a, Busy (.wr w) ((e.cfg t).loc (.wr w)))
    (hph : ∀ t ≥ a, (wl e w t).phase = ph) (hack : (wl e w a).ack = [])
    (hcard : maj S ≤ (Finset.univ.filter (fun s : S => e.Correct (.sv s))).card)
    (hacc : ∀ s, e.Correct (.sv s) → ∃ t ≥ a, ∃ m, e.stp t = .recv (.sv s) (.wr w) m ∧
      ∃ tg v, (s, tg, v) ∈ (wRecord Vr s m (wl e w t)).ack) : False := by
  obtain ⟨hst1, hst2⟩ := wr_stage e hb hph hack
  have hmono : ∀ t ≥ a, ∀ t' ≥ t, (wl e w t).ack ⊆ (wl e w t').ack := by
    intro t ht t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact List.Subset.refl _
    | succ t' ht' ih => exact List.Subset.trans ih (hst2 t' (le_trans ht ht')).1
  obtain ⟨B, hB⟩ := Protocol.Exec.eventually_forall
    (Q := fun s b => e.Correct (.sv s) → s ∈ (wl e w b).ack.map Prod.fst) (by
      intro s
      by_cases hs : e.Correct (.sv s)
      · obtain ⟨t, ht, m, hst, tg, v, hmem⟩ := hacc s hs
        refine ⟨t + 1, fun b hb _ => ?_⟩
        have : (s, tg, v) ∈ (wl e w (t + 1)).ack := by rw [(hst2 t ht).2 s m hst]; exact hmem
        exact List.mem_map.2 ⟨_, hmono (t + 1) (by omega) b hb this, rfl⟩
      · exact ⟨0, fun _ _ h => absurd h hs⟩)
  have h1 := card_le_length (P := fun s : S => e.Correct (.sv s)) (A := (wl e w (max B a)).ack)
    (fun s hs => hB s _ (le_max_left _ _) hs)
  have h2 := (hst1 (max B a) (le_max_right _ _)).2.2.2
  omega

/-! ### Readers -/

lemma rd_step {r : R} {t : ℕ} (hp : (rl e r t).pending = true)
    (hp' : (rl e r (t + 1)).pending = true) :
    (rl e r (t + 1)).op = (rl e r t).op ∧ (rl e r t).ack ⊆ (rl e r (t + 1)).ack ∧
    (rl e r (t + 1)).ack.length ≤ (rl e r t).ack.length + 1 ∧
    ((rl e r (t + 1)).ack.length ≠ maj S ∨ (rl e r (t + 1)).ack = (rl e r t).ack) ∧
    ∀ s m, e.stp t = .recv (.sv s) (.rd r) m →
      (rl e r (t + 1)).ack = (rRecord Vr s m (rl e r t)).ack := by
  by_cases hrecv : ∃ s m, e.stp t = .recv (.sv s) (.rd r) m
  · obtain ⟨s, m, hs⟩ := hrecv
    obtain ⟨out, resp, hrec, -, -⟩ := recv_at e hs
    obtain ⟨-, -, -, hx⟩ := receive_rd_sv hrec
    obtain ⟨ack', relay', hrecd, hsub, hlen⟩ := rRecord_spec (Vr := Vr) s m (rl e r t)
    have hacc : ∀ s' m', e.stp t = .recv (.sv s') (.rd r) m' →
        (rRecord Vr s' m' (rl e r t)).ack = ack' := by
      intro s' m' hs'
      rw [hs] at hs'
      simp only [Step.recv.injEq, Node.sv.injEq, true_and] at hs'
      obtain ⟨rfl, rfl⟩ := hs'
      rw [hrecd]
    rw [hrecd] at hx
    rcases rWait_spec (Vr := Vr) (v₀ := v₀) { rl e r t with ack := ack', relay := relay' } with
      ⟨hne, hw⟩ | ⟨-, h1, -⟩
    · rw [hw] at hx
      simp only [Prod.mk.injEq] at hx
      obtain ⟨h1, -⟩ := hx
      replace h1 : rl e r (t + 1) = _ := h1
      rw [h1]
      exact ⟨rfl, hsub, hlen, Or.inl (hne hp), fun s' m' hs' => (hacc s' m' hs').symm⟩
    · simp only [Prod.ext_iff] at hx
      have h2 : rl e r (t + 1) = _ := hx.1.trans h1
      rw [h2] at hp'
      simp at hp'
  · push Not at hrecv
    have hsame : (e.cfg (t + 1)).loc (.rd r) = (e.cfg t).loc (.rd r) →
        (rl e r (t + 1)).op = (rl e r t).op ∧ (rl e r t).ack ⊆ (rl e r (t + 1)).ack ∧
        (rl e r (t + 1)).ack.length ≤ (rl e r t).ack.length + 1 ∧
        ((rl e r (t + 1)).ack.length ≠ maj S ∨ (rl e r (t + 1)).ack = (rl e r t).ack) ∧
        ∀ s m, e.stp t = .recv (.sv s) (.rd r) m →
          (rl e r (t + 1)).ack = (rRecord Vr s m (rl e r t)).ack := by
      intro h
      have h' : rl e r (t + 1) = rl e r t := by simp only [rl, h]
      rw [h']
      exact ⟨rfl, List.Subset.refl _, by omega, Or.inr rfl, fun s m hs => absurd hs (hrecv s m)⟩
    rcases loc_cases e t (.rd r) with h | ⟨o, out, -, hinv, -⟩ | ⟨src, m, out, resp, hs, hrec⟩
    · exact hsame h
    · obtain ⟨-, hr, -, -⟩ := invoke_rd hinv
      have := (rInvoke_spec hr).1
      rw [hp] at this
      cases this
    · obtain ⟨-, -, -, ⟨s, rfl, -⟩ | ⟨hl, -⟩⟩ := receive_rd hrec
      · exact absurd hs (hrecv s m)
      · exact hsame hl

lemma rd_stage {r : R} {a : ℕ} (hp : ∀ t ≥ a, (rl e r t).pending = true)
    (hack : (rl e r a).ack = []) :
    ∀ t ≥ a, (rl e r t).op = (rl e r a).op ∧ (rl e r t).ack.length < maj S := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact ⟨rfl, by rw [hack]; exact one_le_maj S⟩
  | succ t ht ih =>
    obtain ⟨h1, -, hlen, hne, -⟩ := rd_step e (hp t ht) (hp (t + 1) (by omega))
    refine ⟨h1.trans ih.1, ?_⟩
    have := ih.2
    rcases hne with hne | hne
    · omega
    · rw [hne]; exact this

lemma rop_le_succ (r : R) (t : ℕ) : (rl e r t).op ≤ (rl e r (t + 1)).op := by
  rcases loc_cases e t (.rd r) with h | ⟨o, out, -, hinv, -⟩ | ⟨src, m, out, resp, hs, hrec⟩
  · simp only [rl, h]; exact le_rfl
  · obtain ⟨-, hr, -, -⟩ := invoke_rd hinv
    obtain ⟨-, hl, -⟩ := rInvoke_spec hr
    simp only [rl, hl]; omega
  · simp only [rl, receive_rd_op hrec]; exact le_rfl

lemma rop_mono (r : R) : Monotone (fun t => (rl e r t).op) :=
  monotone_nat_of_le_succ (rop_le_succ e r)

/-! ### Servers -/

lemma sv_cases (t : ℕ) (s : S) :
    sl e s (t + 1) = sl e s t ∨
      ∃ src m out, e.stp t = .recv src (.sv s) m ∧
        (sl e s (t + 1), out) = sRecv Vr src m (sl e s t) := by
  rcases loc_cases e t (.sv s) with h | ⟨o, out, -, hinv, -⟩ | ⟨src, m, out, resp, hs, hrec⟩
  · left; simp only [sl, h]
  · simp [invoke_sv] at hinv
  · obtain ⟨-, -, -, hx⟩ := receive_sv hrec
    exact Or.inr ⟨src, m, out, hs, hx⟩

lemma sv_ops_le (s : S) (r : R) (t : ℕ) : (sl e s t).ops r ≤ (sl e s (t + 1)).ops r := by
  rcases sv_cases e t s with h | ⟨src, m, out, -, hx⟩
  · rw [h]
  · rcases sRecv_spec (Vr := Vr) src m (sl e s t) with
      ⟨r', k, -, -, he⟩ | ⟨sj, tg, v, r', k, -, -, he⟩ | ⟨w, tg, v, op, -, -, he⟩ |
      ⟨w, op, -, -, he⟩ | he <;> rw [he] at hx <;> simp only [Prod.ext_iff] at hx <;>
      rw [hx.1]
    · rw [sRelay_ops]
      split_ifs with hr
      · subst hr; exact le_max_left _ _
      · exact le_rfl
    · rw [(sWrite_spec (Vr := Vr)).1]

lemma sv_ops_mono (s : S) (r : R) : Monotone (fun t => (sl e s t).ops r) :=
  monotone_nat_of_le_succ (sv_ops_le e s r)

lemma sv_got_mono (s : S) (r : R) (t : ℕ) (h : (sl e s t).ops r = (sl e s (t + 1)).ops r) :
    (sl e s t).got r ⊆ (sl e s (t + 1)).got r := by
  rcases sv_cases e t s with h' | ⟨src, m, out, -, hx⟩
  · rw [h']
  · rcases sRecv_spec (Vr := Vr) src m (sl e s t) with
      ⟨r', k, -, -, he⟩ | ⟨sj, tg, v, r', k, -, -, he⟩ | ⟨w, tg, v, op, -, -, he⟩ |
      ⟨w, op, -, -, he⟩ | he <;> rw [he] at hx <;> simp only [Prod.ext_iff] at hx <;>
      rw [hx.1] at h ⊢
    · by_cases hr : r = r'
      · subst hr
        simp only [sRelay_ops, ite_true] at h
        rcases lt_trichotomy ((sl e s t).ops r) k with hk | hk | hk
        · rw [max_eq_right hk.le] at h; omega
        · rw [(sRelay_eq hk).2]; exact Finset.subset_insert _ _
        · rw [(sRelay_gt hk).2]
      · rw [(sRelay_ne hr).2]
    · rw [(sWrite_spec (Vr := Vr)).2.2.1]

lemma sv_relay {s sj : S} {t : ℕ} {tg : T} {v : V} {r : R} {k : ℕ}
    (hs : e.stp t = .recv (.sv sj) (.sv s) (.readRelay tg v r k)) (hk : (sl e s t).ops r ≤ k) :
    (sl e s (t + 1)).ops r = k ∧ sj ∈ (sl e s (t + 1)).got r := by
  obtain ⟨out, resp, hrec, -, -⟩ := recv_at e hs
  obtain ⟨-, -, -, hx⟩ := receive_sv hrec
  simp only [sRecv, Prod.ext_iff] at hx
  have h1 : sl e s (t + 1) = _ := hx.1
  rw [h1, sRelay_ops]
  simp only [ite_true]
  rw [max_eq_right hk]
  refine ⟨rfl, ?_⟩
  rcases lt_or_eq_of_le hk with hk | hk
  · rw [(sRelay_lt hk).2]; exact Finset.mem_singleton_self _
  · rw [(sRelay_eq hk).2]; exact Finset.mem_insert_self _ _

lemma sv_request {s : S} {t : ℕ} {r : R} {k : ℕ}
    (hs : e.stp t = .recv (.rd r) (.sv s) (.readRequest k)) (s' : S) :
    ∃ tg v, (Node.sv s, Node.sv s', Msg.readRelay tg v r k) ∈ (e.cfg (t + 1)).net := by
  obtain ⟨out, resp, hrec, hC, -⟩ := recv_at e hs
  obtain ⟨-, -, -, hx⟩ := receive_sv hrec
  simp only [sRecv, Prod.ext_iff] at hx
  refine ⟨(sl e s t).tag, (sl e s t).val, mem_net_of_out e hC ?_⟩
  rw [hx.2]
  exact Multiset.mem_add.2 (Or.inl (mem_bcast.2 ⟨s', rfl⟩))

lemma sv_discover {s : S} {t : ℕ} {w : W} {k : ℕ}
    (hs : e.stp t = .recv (.wr w) (.sv s) (.discover k)) :
    ∃ tg v, (Node.sv s, Node.wr w, Msg.discoverAck tg v k) ∈ (e.cfg (t + 1)).net := by
  obtain ⟨out, resp, hrec, hC, -⟩ := recv_at e hs
  obtain ⟨-, -, -, hx⟩ := receive_sv hrec
  simp only [sRecv, Prod.ext_iff] at hx
  refine ⟨(sl e s t).tag, (sl e s t).val, mem_net_of_out e hC ?_⟩
  rw [hx.2]
  exact Multiset.mem_singleton_self _

lemma sv_write {s : S} {t : ℕ} {w : W} {tg : T} {v : V} {k : ℕ}
    (hs : e.stp t = .recv (.wr w) (.sv s) (.writeRequest tg v k)) :
    (Node.sv s, Node.wr w, Msg.writeAck (sl e s (t + 1)).tag (sl e s (t + 1)).val k) ∈
        (e.cfg (t + 1)).net ∧
      (Vr.mw = false →
        (sl e s (t + 1)).tag = if (sl e s t).tag < tg then tg else (sl e s t).tag) := by
  obtain ⟨out, resp, hrec, hC, -⟩ := recv_at e hs
  obtain ⟨-, -, -, hx⟩ := receive_sv hrec
  simp only [sRecv, Prod.ext_iff] at hx
  have h1 : sl e s (t + 1) = _ := hx.1
  obtain ⟨-, -, -, h4, h5⟩ := sWrite_spec (Vr := Vr) (w := w) (t := tg) (v := v) (op := k)
    (L := sl e s t)
  refine ⟨mem_net_of_out e hC ?_, fun hmw => by rw [h1, h5 hmw]⟩
  rw [hx.2, h4, h1]
  exact Multiset.mem_singleton_self _

end Ex

end Podc.OhRAM.Liveness
