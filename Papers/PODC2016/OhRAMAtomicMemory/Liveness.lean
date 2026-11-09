import Papers.PODC2016.OhRAMAtomicMemory.LivenessExec

/-!
# Termination of OhSam, OhMam, OhSam', OhMam'

In every fair execution in which fewer than half of the servers crash (any number of clients may
crash), every operation of a correct client terminates (`proto_live`, and the corollaries
`theorem_5_live`, `theorem_12_live`, `theorem_16_live`, `theorem_22_live`).

* Reads (`Liveness.Ex.read_terminates`): the `readRequest` of a correct reader reaches every
  correct server, which relays it to all servers; a correct server `s'` eventually has the relays
  of all correct servers counted in `relays[r]` (the ghost `got[r]`), so `relays[r]` has reached
  `|S|/2 + 1` and `s'` has sent its `readAck` (`RInv.quorum`), which the reader eventually
  receives. With at least `|S|/2 + 1` correct servers, `|rAck|` would exceed `|S|/2 + 1` while the
  read is pending, but it grows one by one and the read returns when it equals `|S|/2 + 1`. The
  fast path of the revised protocol is not needed.
* Writes (`Liveness.Ex.write_terminates`): the same argument for the `discover` phase (MWMR) and
  the `writeRequest` phase. For the single writer, the `writeAck` of a correct server carries the
  writer's current tag because no tag in the system exceeds it (`TInv`).
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]
variable {Vr : Variant} {next : W → T → T} {v₀ : V}

namespace Liveness.Ex

variable (e : (proto (R := R) (S := S) Vr next v₀).Exec)

open Classical in
/-- Termination of reads. -/
theorem read_terminates (hf : e.Fair)
    (hcard : maj S ≤ (Finset.univ.filter (fun s : S => e.Correct (.sv s))).card)
    {r : R} (hr : e.Correct (.rd r)) {T : ℕ}
    (hpend : (respsOf (e.hist T) (.rd r)).length < (opsOf (e.hist T) (.rd r)).length) :
    ∃ t, (respsOf (e.hist T) (.rd r)).length < (respsOf (e.hist t) (.rd r)).length := by
  by_contra H
  push Not at H
  have hbusy := busy_of_no_resp e hpend H
  obtain ⟨t₀, ht₀, hn, hall⟩ := exists_last_false
    (P := fun t => Busy (.rd r) ((e.cfg t).loc (.rd r))) (not_busy_zero e _) (hbusy T le_rfl)
  have hp : ∀ t ≥ t₀ + 1, (rl e r t).pending = true := fun t ht => by
    rcases Nat.lt_or_ge T t with h | h
    · exact hbusy t h.le
    · exact hall t (by omega) h
  obtain ⟨o, out, hinv, hC⟩ := invoke_of_busy e hn (hp (t₀ + 1) le_rfl)
  obtain ⟨-, hrinv, -, -⟩ := invoke_rd hinv
  obtain ⟨-, hl, rfl⟩ := rInvoke_spec hrinv
  replace hl : rl e r (t₀ + 1) = _ := hl
  have hst := rd_stage e (a := t₀ + 1) hp (by rw [hl])
  have hop : ∀ t ≥ t₀ + 1, (rl e r t).op = (rl e r t₀).op + 1 := fun t ht => by
    rw [(hst t ht).1, hl]
  have hreq : ∀ s, (Node.rd r, Node.sv s, Msg.readRequest ((rl e r t₀).op + 1)) ∈
      (e.cfg (t₀ + 1)).net := fun s => mem_net_of_out e hC (mem_bcast.2 ⟨s, rfl⟩)
  -- every correct server `s'` eventually stays in `rAck`
  have hsrv : ∀ s', e.Correct (.sv s') → ∃ B, ∀ b ≥ B, s' ∈ (rl e r b).ack.map Prod.fst := by
    intro s' hs'
    obtain ⟨B₁, hB₁⟩ := Protocol.Exec.eventually_forall
      (Q := fun s b => e.Correct (.sv s) →
        (sl e s' b).ops r = (rl e r t₀).op + 1 ∧ s ∈ (sl e s' b).got r) (by
      intro s
      by_cases hs : e.Correct (.sv s)
      · obtain ⟨t₁, ht₁, hst₁⟩ := Exec.eventually_recv e hf hr hs (receive_isSome _ _ _) (hreq s)
        obtain ⟨tg, v, hrel⟩ := sv_request e hst₁ s'
        obtain ⟨t₂, ht₂, hst₂⟩ := Exec.eventually_recv e hf hs hs' (receive_isSome _ _ _) hrel
        have hle : ∀ b ≥ t₀ + 1, (sl e s' b).ops r ≤ (rl e r t₀).op + 1 := fun b hb => by
          have := (rinv e b).ops s' r
          simp only [rop] at this
          rw [← hop b hb]; exact this
        obtain ⟨h1, h2⟩ := sv_relay e hst₂ (hle t₂ (by omega))
        have hops : ∀ b ≥ t₂ + 1, (sl e s' b).ops r = (rl e r t₀).op + 1 := fun b hb =>
          le_antisymm (hle b (by omega)) (h1 ▸ sv_ops_mono e s' r hb)
        refine ⟨t₂ + 1, fun b hb _ => ⟨hops b hb, ?_⟩⟩
        induction b, hb using Nat.le_induction with
        | base => exact h2
        | succ b hb ih =>
          exact sv_got_mono e s' r b (by rw [hops b hb, hops (b + 1) (by omega)]) ih
      · exact ⟨0, fun _ _ h => absurd h hs⟩)
    have hops := (hB₁ s' B₁ le_rfl hs').1
    have hrel : maj S ≤ (sl e s' B₁).relays r := by
      calc maj S ≤ (Finset.univ.filter (fun s : S => e.Correct (.sv s))).card := hcard
        _ ≤ ((sl e s' B₁).got r).card := Finset.card_le_card (fun s hs => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
            exact (hB₁ s B₁ le_rfl hs).2)
        _ ≤ _ := (rinv e B₁).got s' r
    obtain ⟨tg, v, hsent⟩ := (rinv e B₁).quorum s' r hrel
    rw [hops] at hsent
    obtain ⟨t', -, hnet⟩ := Exec.exists_net_of_sent e hsent
    have hk' : (rl e r t₀).op + 1 ≤ (rl e r (t' + 1)).op := by
      have := (rinv e (t' + 1)).msg _ (Exec.net_sub_sent e _ hnet)
      simpa [MsgOK, rop] using this
    have ht'₀ : t₀ < t' + 1 := by
      by_contra hlt
      push Not at hlt
      have := rop_mono e r hlt
      simp only at this
      omega
    obtain ⟨t₃, ht₃, hst₃⟩ := Exec.eventually_recv e hf hs' hr (receive_isSome _ _ _) hnet
    have hmem : (s', tg, v) ∈ (rl e r (t₃ + 1)).ack := by
      rw [(rd_step e (hp t₃ (by omega)) (hp (t₃ + 1) (by omega))).2.2.2.2 s' _ hst₃]
      have := rRecord_readAck (R := R) (Vr := Vr) s' tg v (rl e r t₃)
      rwa [hop t₃ (by omega)] at this
    have hmono : ∀ b ≥ t₃ + 1, (s', tg, v) ∈ (rl e r b).ack := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact hmem
      | succ b hb ih =>
        exact (rd_step e (hp b (by omega)) (hp (b + 1) (by omega))).2.1 ih
    exact ⟨t₃ + 1, fun b hb => List.mem_map.2 ⟨_, hmono b hb, rfl⟩⟩
  obtain ⟨B, hB⟩ := Protocol.Exec.eventually_forall
    (Q := fun s b => e.Correct (.sv s) → s ∈ (rl e r b).ack.map Prod.fst) (by
      intro s
      by_cases hs : e.Correct (.sv s)
      · obtain ⟨B, hB⟩ := hsrv s hs
        exact ⟨B, fun b hb _ => hB b hb⟩
      · exact ⟨0, fun _ _ h => absurd h hs⟩)
  have h1 := card_le_length (P := fun s : S => e.Correct (.sv s))
    (A := (rl e r (max B (t₀ + 1))).ack) (fun s hs => hB s _ (le_max_left _ _) hs)
  have h2 := (hst (max B (t₀ + 1)) (le_max_right _ _)).2
  omega

lemma upd_forever {w : W} {a : ℕ} (hb : ∀ t ≥ a, Busy (.wr w) ((e.cfg t).loc (.wr w)))
    (hph : (wl e w a).phase = .upd) : ∀ t ≥ a, (wl e w t).phase = .upd := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hph
  | succ t ht ih =>
    rcases wr_step e (hb t ht) (hb (t + 1) (by omega)) with ⟨ack', h1, -⟩ | ⟨val, h1, -⟩
    · rw [h1]; exact ih
    · rw [ih] at h1; cases h1

open Classical in
/-- The `writeRequest` phase of a correct writer terminates. -/
lemma upd_stage_false (hf : e.Fair)
    (hcard : maj S ≤ (Finset.univ.filter (fun s : S => e.Correct (.sv s))).card)
    (hTI : Vr.mw = false → ∀ t, TInv (e.cfg t)) {w : W} (hw : e.Correct (.wr w)) {a : ℕ}
    (hb : ∀ t ≥ a, Busy (.wr w) ((e.cfg t).loc (.wr w))) (hph : (wl e w a).phase = .upd)
    (hack : (wl e w a).ack = [])
    (hreq : ∀ s, (Node.wr w, Node.sv s, Msg.writeRequest (wl e w a).tag (wl e w a).val
      (if Vr.mw then (wl e w a).op else 0)) ∈ (e.cfg a).net) : False := by
  have hph' := upd_forever e hb hph
  have hst := (wr_stage e hb hph' hack).1
  refine wr_stage_false e hb hph' hack hcard (fun s hs => ?_)
  obtain ⟨t₁, ht₁, h1⟩ := Exec.eventually_recv e hf hw hs (receive_isSome _ _ _) (hreq s)
  obtain ⟨h2, h3⟩ := sv_write e h1
  obtain ⟨t₂, ht₂, h4⟩ := Exec.eventually_recv e hf hs hw (receive_isSome _ _ _) h2
  refine ⟨t₂, by omega, _, h4, (sl e s (t₁ + 1)).tag, (sl e s (t₁ + 1)).val, ?_⟩
  obtain ⟨htag, hop, -, -⟩ := hst t₂ (by omega)
  cases hmw : Vr.mw
  · have hle : (sl e s t₁).tag ≤ (wl e w t₁).tag := (hTI hmw t₁).srv w s
    rw [(hst t₁ ht₁).1] at hle
    have htag' : (sl e s (t₁ + 1)).tag = (wl e w a).tag := by
      rw [h3 hmw]
      split_ifs with h
      · rfl
      · exact le_antisymm hle (not_lt.1 h)
    simp [wRecord, hmw, htag', htag, List.mem_insert_iff]
  · simp [wRecord, hmw, hop, List.mem_insert_iff]

open Classical in
/-- Termination of writes. -/
theorem write_terminates (hf : e.Fair)
    (hcard : maj S ≤ (Finset.univ.filter (fun s : S => e.Correct (.sv s))).card)
    (hTI : Vr.mw = false → ∀ t, TInv (e.cfg t)) {w : W} (hw : e.Correct (.wr w)) {T : ℕ}
    (hpend : (respsOf (e.hist T) (.wr w)).length < (opsOf (e.hist T) (.wr w)).length) :
    ∃ t, (respsOf (e.hist T) (.wr w)).length < (respsOf (e.hist t) (.wr w)).length := by
  by_contra H
  push Not at H
  have hbusy := busy_of_no_resp e hpend H
  obtain ⟨t₀, ht₀, hn, hall⟩ := exists_last_false
    (P := fun t => Busy (.wr w) ((e.cfg t).loc (.wr w))) (not_busy_zero e _) (hbusy T le_rfl)
  have hb : ∀ t ≥ t₀ + 1, Busy (.wr w) ((e.cfg t).loc (.wr w)) := fun t ht => by
    rcases Nat.lt_or_ge T t with h | h
    · exact hbusy t h.le
    · exact hall t (by omega) h
  obtain ⟨o, out, hinv, hC⟩ := invoke_of_busy e hn (hb (t₀ + 1) le_rfl)
  obtain ⟨val, -, hwinv, -, -⟩ := invoke_wr hinv
  obtain ⟨-, hc⟩ := wInvoke_spec hwinv
  rcases hc with ⟨hmw, hl, rfl⟩ | ⟨hmw, hl, rfl⟩
  · -- multi-writer: the `discover` phase ends
    replace hl : wl e w (t₀ + 1) = _ := hl
    have hdisc : ∃ t, t ≥ t₀ + 1 ∧ (wl e w t).phase ≠ .disc val := by
      by_contra hstay
      push Not at hstay
      have hst := (wr_stage e hb hstay (by rw [hl])).1
      refine wr_stage_false e hb hstay (by rw [hl]) hcard (fun s hs => ?_)
      obtain ⟨t₁, ht₁, h1⟩ := Exec.eventually_recv e hf hw hs (receive_isSome _ _ _)
        (mem_net_of_out e hC (mem_bcast.2 ⟨s, rfl⟩))
      obtain ⟨tg, v, h2⟩ := sv_discover e h1
      obtain ⟨t₂, ht₂, h3⟩ := Exec.eventually_recv e hf hs hw (receive_isSome _ _ _) h2
      refine ⟨t₂, by omega, _, h3, tg, v, ?_⟩
      have hop := (hst t₂ (by omega)).2.1
      rw [hl] at hop
      simp [wRecord, hmw, hop, List.mem_insert_iff]
    have hspec := Nat.find_spec hdisc
    have hne : Nat.find hdisc ≠ t₀ + 1 := fun h => by
      have := hspec.2
      rw [h, hl] at this
      exact this rfl
    obtain ⟨t, ht⟩ : ∃ t, Nat.find hdisc = t + 1 := ⟨Nat.find hdisc - 1, by omega⟩
    have htd : (wl e w t).phase = .disc val := by
      have := Nat.find_min hdisc (m := t) (by omega)
      push Not at this
      exact this (by omega)
    rcases wr_step e (hb t (by omega)) (hb (t + 1) (by omega)) with ⟨ack', h1, -⟩ |
      ⟨val', -, h2, h3, h4⟩
    · have := hspec.2
      rw [ht, h1] at this
      exact this htd
    · refine upd_stage_false e hf hcard hTI hw (a := t + 1) (fun t' ht' => hb t' (by omega)) h2 h3
        (fun s => ?_)
      simp only [hmw, ite_true]
      exact h4 s
  · -- single writer: the `writeRequest` phase starts at the invocation
    replace hl : wl e w (t₀ + 1) = _ := hl
    refine upd_stage_false e hf hcard hTI hw (a := t₀ + 1) hb (by rw [hl]) (by rw [hl])
      (fun s => ?_)
    rw [hl]
    simp only [hmw, Bool.false_eq_true, ite_false]
    exact mem_net_of_out e hC (mem_bcast.2 ⟨s, rfl⟩)

end Liveness.Ex

/-- Termination of the four algorithms: in every fair execution in which at most `f` servers
crash, `2f < |S|`, every operation invoked by a correct client returns. For the single-writer
protocols the writer's tags must not decrease (`ts ≤ ts + 1`) and there is one writer. -/
theorem proto_live (Vr : Variant) (next : W → T → T) (v₀ : V)
    (hlt : Vr.mw = false → ∀ w t, t ≤ next w t)
    (hsw : Vr.mw = false → ∀ w w' : W, w = w') {f : ℕ} (hf : 2 * f < Fintype.card S) :
    Live (proto (R := R) (S := S) Vr next v₀) f := by
  intro e hfair hres p hp T hpend
  have hcard := Liveness.Ex.card_correct e hres hf
  cases p with
  | sv s =>
    exfalso
    rcases Liveness.Ex.hinv e T (.sv s) with ⟨-, hb⟩ | ⟨he, -⟩
    · exact hb
    · omega
  | rd r => exact Liveness.Ex.read_terminates e hfair hcard hp hpend
  | wr w =>
    exact Liveness.Ex.write_terminates e hfair hcard
      (fun hmw t => Liveness.tInv_of_reach hmw (hsw hmw) (hlt hmw) (e.reach t)) hp hpend

variable (R S V) in
/-- Theorem 5 of [paper] (termination part): OhSam terminates when fewer than half of the
servers crash. -/
theorem theorem_5_live (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    Live (ohSam R S V v₀) f :=
  proto_live _ _ _ (fun _ _ t => Nat.le_succ t) (fun _ _ _ => rfl) hf

variable (W R S V) in
/-- Theorem 12 of [paper] (termination part): OhMam terminates when fewer than half of the
servers crash. -/
theorem theorem_12_live [LinearOrder W] (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    Live (ohMam W R S V v₀) f := by
  -- `convert` bridges the two `DecidableEq (Tag W)` instances (from `DecidableEq W` and from
  -- `LinearOrder W`)
  have := proto_live (W := W) (R := R) (S := S) (T := Tag W) (V := V) ⟨true, false, false⟩
    nextTag v₀
    (fun h => by cases h) (fun h => by cases h) hf
  unfold ohMam
  convert this

variable (R S V) in
/-- Theorem 16 of [paper] (termination part): OhSam' terminates when fewer than half of the
servers crash. -/
theorem theorem_16_live (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    Live (ohSam' R S V v₀) f :=
  proto_live _ _ _ (fun _ _ t => Nat.le_succ t) (fun _ _ _ => rfl) hf

variable (W R S V) in
/-- Theorem 22 of [paper] (termination part): OhMam' terminates when fewer than half of the
servers crash. -/
theorem theorem_22_live [LinearOrder W] (v₀ : V) {f : ℕ} (hf : 2 * f < Fintype.card S) :
    Live (ohMam' W R S V v₀) f := by
  -- `convert` bridges the two `DecidableEq (Tag W)` instances (from `DecidableEq W` and from
  -- `LinearOrder W`)
  have := proto_live (W := W) (R := R) (S := S) (T := Tag W) (V := V) ⟨true, true, false⟩
    nextTag v₀
    (fun h => by cases h) (fun h => by cases h) hf
  unfold ohMam'
  convert this

end Podc.OhRAM
