import Papers.PODC2016.OhRAMAtomicMemory.SafetyRecv

/-!
# Atomicity of OhSam, OhMam, OhSam' and OhMam'

Every reachable configuration of `proto Vr next v₀` satisfies the message invariant `CInv` and,
for some ghost data `(Wl, tok)`, the history invariant `Inv` (`inv_of_reach`). The invariant
gives the timestamp criterion `Cslib.SharedMemory.TSLin` (`Inv.tsLin`), hence linearizability
(`proto_linearizable`), for every variant, as soon as the tag generator `next` produces larger
tags (`hlt`), different writers produce different tags (`hinj`), and the single-writer write
protocol is only used with one writer (`hsw`). This gives the atomicity parts of Theorems 5, 12,
16 and 22.
-/

set_option linter.unusedSectionVars false

namespace Podc.OhRAM

open Cslib.SharedMemory Cslib.AsyncMP

variable {W R S T V : Type} [DecidableEq W] [DecidableEq R] [DecidableEq S] [Fintype S]
  [LinearOrder T] [OrderBot T] [DecidableEq V]

/-- Reachable configurations satisfy both invariants. -/
theorem inv_of_reach (Vr : Variant) (next : W → T → T) (v₀ : V)
    (hlt : ∀ w t, t < next w t) (hinj : ∀ w w' t t', next w t = next w' t' → w = w')
    (hsw : Vr.mw = false → ∀ w w' : W, w = w') {C : Cfg W R S T V} {h : Hist W R S V v₀}
    (hr : (proto Vr next v₀).Reach C h) :
    CInv Vr C ∧ ∃ Wl tok, Inv next v₀ h C Wl tok := by
  induction hr with
  | init => exact ⟨cinv_init, [], fun _ => ⊥, inv_init Vr⟩
  | step _ hs ih =>
    obtain ⟨IC, Wl, tok, I⟩ := ih
    refine ⟨IC.step hs, ?_⟩
    rcases step_cases hs with ⟨h1, h2, rfl, -⟩ | ⟨w, v, l, out, hw, rfl, rfl⟩ |
      ⟨r, l, out, hr', rfl, rfl⟩ | ⟨w, s, m, hx, rfl, rfl⟩ | ⟨r, s, m, hx, rfl, rfl⟩ |
      ⟨s, q, m, hx, rfl, rfl⟩
    · simp only [Option.toList_none, List.append_nil]
      exact ⟨Wl, tok, I.of_silent h1 h2⟩
    · simp only [Option.toList_some]
      cases hmw : Vr.mw
      · exact ⟨_, _, I.wInvoke_sw hmw hlt (hsw hmw) hw⟩
      · exact ⟨Wl, tok, I.wInvoke_mw hmw IC hw⟩
    · exact ⟨Wl, tok, I.rInvoke IC hr'⟩
    · exact I.wRecv hlt hinj IC hx
    · obtain ⟨tok', I'⟩ := I.rRecv hlt hinj IC hx
      exact ⟨Wl, tok', I'⟩
    · simp only [Option.toList_none, List.append_nil]
      exact ⟨Wl, tok, I.sRecv IC hx⟩

/-- **Lemmas 1, 6, 13, 17**: the tag of every server is non-decreasing along every step. -/
theorem server_tag_mono {Vr : Variant} {next : W → T → T} {v₀ : V} {C C' : Cfg W R S T V}
    {st : Step (Node W R S) (register V v₀) (Msg R T V) Empty}
    {ℓ : Option (Label (Node W R S) (register V v₀))}
    (hs : (proto Vr next v₀).step C st = some (C', ℓ)) (s : S) :
    (C.sl s).tag ≤ (C'.sl s).tag := by
  rcases step_cases hs with ⟨h1, -, -, -⟩ | ⟨w, v, l, out, -, rfl, -⟩ |
    ⟨r, l, out, -, rfl, -⟩ | ⟨w, s', m, -, rfl, -⟩ | ⟨r, s', m, -, rfl, -⟩ |
    ⟨s', q, m, -, rfl, -⟩
  · simp [Cfg.sl, h1]
  · simp
  · simp
  · simp
  · simp
  · rw [setS_sl]
    split_ifs with h
    · subst h; exact sRecv_tag_mono q m _
    · exact le_rfl

/-- The invariant gives the timestamp criterion of linearizability. -/
theorem Inv.tsLin {next : W → T → T} {v₀ : V} {h : Hist W R S V v₀} {C : Cfg W R S T V}
    {Wl : List (OpId (Node W R S))} {tok : OpId (Node W R S) → T}
    (hlt : ∀ w t, t < next w t) (hinj : ∀ w w' t t', next w t = next w' t' → w = w')
    (I : Inv next v₀ h C Wl tok) : TSLin h Wl tok where
  wellFormed := I.wf
  W_nodup := I.W_nodup
  W_write x hx := by
    obtain ⟨w, h1, h2, -⟩ := I.W_mem x hx
    rcases I.kind h2 with ⟨w', v, -, hv⟩ | ⟨r, h3, -⟩
    · exact ⟨v, hv⟩
    · rw [h1] at h3; cases h3
  W_complete := I.W_complete
  write_resp := I.write_resp
  W_inj a ha b hb hab := I.W_inj hinj ha hb hab
  W_pos x hx := I.W_pos hlt hx
  read_val x r hx hr := I.read_resp x r hx hr
  prec_W := I.prec_W
  prec_R := I.prec_R

/-- **Atomicity of the four algorithms.** Every history of `proto Vr next v₀` is linearizable,
provided tags grow (`hlt`: `ts + 1 > ts`, `⟨maxTS + 1, w⟩ > maxTag`), different writers create
different tags (`hinj`) and the single-writer write protocol has one writer (`hsw`). -/
theorem proto_linearizable (Vr : Variant) (next : W → T → T) (v₀ : V)
    (hlt : ∀ w t, t < next w t)
    (hinj : ∀ w w' t t', next w t = next w' t' → w = w')
    (hsw : Vr.mw = false → ∀ w w' : W, w = w') :
    (proto (R := R) (S := S) Vr next v₀).Linearizable := by
  intro C h hr
  obtain ⟨-, Wl, tok, I⟩ := inv_of_reach Vr next v₀ hlt hinj hsw hr
  exact (I.tsLin hlt hinj).exists_isLinearization

/-! ## The tags of OhMam -/

lemma nextTag_lt [LinearOrder W] (w : W) (t : Tag W) : t < nextTag w t := by
  cases t using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe x =>
    show (x : Tag W) < ((toLex ((ofLex x).1 + 1, w) : ℕ ×ₗ W) : Tag W)
    rw [WithBot.coe_lt_coe, Prod.Lex.lt_iff]
    exact Or.inl (by simp)

lemma nextTag_inj [LinearOrder W] {w w' : W} {t t' : Tag W} (h : nextTag w t = nextTag w' t') :
    w = w' := by
  have key : ∀ (w : W) (t : Tag W), ∃ n, nextTag w t = ((toLex (n, w) : ℕ ×ₗ W) : Tag W) := by
    intro w t
    cases t using WithBot.recBotCoe with
    | bot => exact ⟨1, rfl⟩
    | coe x => exact ⟨(ofLex x).1 + 1, rfl⟩
  obtain ⟨n, hn⟩ := key w t
  obtain ⟨n', hn'⟩ := key w' t'
  rw [hn, hn'] at h
  have := toLex.injective (WithBot.coe_injective h)
  exact (Prod.mk.inj this).2

/-! ## The four algorithms -/

variable (v₀ : V)

/-- **Theorem 5** of [Hadjistasi–Nicolaou–Schwarzmann] (atomicity part): OhSam implements an
atomic SWMR register. -/
theorem theorem_5 : (ohSam R S V v₀).Linearizable :=
  proto_linearizable _ _ v₀ (fun _ t => Nat.lt_succ_self t) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

/-- **Theorem 12** of [Hadjistasi–Nicolaou–Schwarzmann] (atomicity part): OhMam implements an
atomic MWMR register. -/
theorem theorem_12 [LinearOrder W] : (ohMam W R S V v₀).Linearizable := by
  have := proto_linearizable (W := W) (R := R) (S := S) (T := Tag W) ⟨true, false, false⟩ nextTag
    v₀ nextTag_lt (fun _ _ _ _ h => nextTag_inj h) (fun h => absurd h (by decide))
  convert this; rfl

/-- **Theorem 16** of [Hadjistasi–Nicolaou–Schwarzmann] (atomicity part): OhSam' implements an
atomic SWMR register. -/
theorem theorem_16 : (ohSam' R S V v₀).Linearizable :=
  proto_linearizable _ _ v₀ (fun _ t => Nat.lt_succ_self t) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ => rfl)

/-- **Theorem 22** of [Hadjistasi–Nicolaou–Schwarzmann] (atomicity part): OhMam' implements an
atomic MWMR register. -/
theorem theorem_22 [LinearOrder W] : (ohMam' W R S V v₀).Linearizable := by
  have := proto_linearizable (W := W) (R := R) (S := S) (T := Tag W) ⟨true, true, false⟩ nextTag
    v₀ nextTag_lt (fun _ _ _ _ h => nextTag_inj h) (fun h => absurd h (by decide))
  convert this; rfl

end Podc.OhRAM
