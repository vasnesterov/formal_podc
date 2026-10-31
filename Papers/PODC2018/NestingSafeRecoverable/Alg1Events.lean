import Papers.PODC2018.NestingSafeRecoverable.Alg1Local

/-!
# Algorithm 1: preservation of the invariant by invocations and crashes
-/

set_option linter.unusedSectionVars false

namespace Podc.NestingSafeRecoverable.Alg1

open Cslib.SharedMemory Cslib.SharedMemory.NRL

variable {P V : Type} [DecidableEq P] [DecidableEq V] {v₀ : V}
variable {C : (alg1 P V v₀).Cfg} {L : List (OpId P × RWOp V)} {G : Set V}

lemma _root_.Podc.NestingSafeRecoverable.Env1.of_append {α β : List (Label P (register V v₀))} (h : Env1 v₀ (α ++ β)) :
    Env1 v₀ α :=
  ⟨fun x hx => h.1 x (opOf_append_of_eq_some hx β), fun x y w hx hy =>
    h.2 x y w (opOf_append_of_eq_some hx β) (opOf_append_of_eq_some hy β)⟩

/-- An invocation. -/
theorem Inv.ev_inv (hI : Inv C L G) {p : P} {o : RWOp V}
    (henv : Env1 v₀ (N (C.ev (.inv p o)).hist)) : ∃ L', Inv (C.ev (.inv p o)) L' G := by
  rcases hs : C.st p with _ | y
  swap
  · rw [Alg.ev_inv_of_some C o hs]; exact ⟨L, hI⟩
  refine ⟨L, ?_⟩
  have hwf := hI.wf.ev (.inv p o); have hpe := hI.pend.ev (.inv p o)
  have he := Alg.ev_inv_of_none C o hs
  rw [he] at hwf hpe henv ⊢
  have hN : N (C.hist ++ [.inv p o]) = N C.hist ++ [.inv p o] := by simp
  rw [hN] at henv
  have hlen := hI.wf.pend p
  simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero] at hlen
  have hxL : curOp (N C.hist) p ∉ L.map Prod.fst := by
    intro hx
    have := hI.lin.mem_invoked hx
    simp only [Invoked] at this; omega
  have hop : opOf (N C.hist ++ [.inv p o]) (curOp (N C.hist) p) = some o := by
    rw [opOf_concat_inv]; simp [curOp, hlen]
  -- the argument of a new write is fresh
  have hfresh : ∀ w, o = .write w → ∀ y, opOf (N C.hist) y ≠ some (.write w) := by
    intro w hw y hy
    have := henv.2 y (curOp (N C.hist) p) w (opOf_append_of_eq_some hy _) (hw ▸ hop)
    subst this
    have := Invoked.of_opOf_eq_some hy
    simp only [Invoked] at this; omega
  refine ⟨hwf, hpe, ?_, hI.state, hI.gR, ?_, fun q => ?_, fun q => ?_⟩
  · rw [hN]; exact hI.lin.append_inv p o
  · intro w hw; rw [hN]
    rcases hI.gV w hw with h | ⟨y, hy⟩
    · exact Or.inl h
    · exact Or.inr ⟨y, opOf_append_of_eq_some hy _⟩
  · obtain ⟨h1, h2, h3⟩ := hI.sinv q
    refine ⟨h1, h2, fun c hc => ?_⟩
    obtain ⟨y, hy⟩ := h3 c hc
    rw [hN]; exact ⟨y, opOf_append_of_eq_some hy _⟩
  · rw [hN, curOp_append_inv]
    by_cases hq : q = p
    · subst hq
      change PInv (v₀ := v₀) L G (Rv C) (Sv C q) _ _
      simp only [Function.update_self]
      have hs0 : (Sv C q).1 = false := by have := hI.proc q; rw [hs] at this; exact this
      rcases o with _ | val
      · exact ⟨hs0, Or.inl ⟨rfl, hxL⟩⟩
      · have hval : val ∉ G := by
          intro hv
          rcases hI.gV val hv with h | ⟨y, hy⟩
          · exact henv.1 (curOp (N C.hist) q) (h ▸ hop)
          · exact hfresh val rfl y hy
        have hsv : Sv C q ≠ (false, some val) := by
          intro e
          obtain ⟨y, hy⟩ := (hI.sinv q).2.2 val e
          exact hfresh val rfl y hy
        refine ⟨⟨fun hx => absurd hx hxL, fun hl => ?_⟩, fun hx => absurd hx hxL,
          fun _ _ => hval, fun c hc => (by rw [hc] at hs0; cases hs0), ⟨hval, hsv⟩⟩
        rcases hl with hl | hl | ⟨c, hc, -⟩ | ⟨hl, -⟩
        · exact absurd hl hval
        · exact absurd hl hsv
        · rw [hc] at hs0; cases hs0
        · cases hl
    · simp only [Function.update_of_ne hq]; exact hI.proc q

/-- A crash (and the recovery) of `p`. -/
theorem Inv.ev_crash (hI : Inv C L G) (p : P) : ∃ L', Inv (C.ev (.crash p)) L' G := by
  rcases hs : C.st p with _ | ⟨o, pc, v⟩
  · rw [Alg.ev_crash_of_none C hs]; exact ⟨L, hI⟩
  have hwf := hI.wf.ev (.crash p); have hpe := hI.pend.ev (.crash p)
  have he := Alg.ev_crash_of_some C hs
  rw [he] at hwf hpe ⊢
  have hN : N (C.hist ++ [.crash p, .recover p]) = N C.hist := by simp
  have hst : ∀ q, q ≠ p → (Function.update C.st p
      (some (o, (alg1 P V v₀).recover p o pc)) q) = C.st q := fun q hq => by simp [hq]
  rcases o with _ | val
  · obtain ⟨hs0, hpc⟩ := hI.rInv hs
    rcases hpc with ⟨rfl, hx⟩ | ⟨rfl, hresp⟩
    · exact ⟨L, hI.frame hwf hpe hN rfl (fun _ _ => rfl) hst hI.lin rfl (LSame.rfl' _ _)
        (hI.sinv p) (by simp only [Function.update_self]; exact ⟨hs0, Or.inl ⟨rfl, hx⟩⟩)⟩
    · obtain ⟨L', h1, h2, h3, h4⟩ :=
        hI.retract hs (ObjSpec.mem_of_respIn_eq_some hresp) (Or.inl rfl)
      exact ⟨L', hI.frame hwf hpe hN rfl (fun _ _ => rfl) hst h1 h2 h3
        (hI.sinv p) (by simp only [Function.update_self]; exact ⟨hs0, Or.inl ⟨rfl, h4⟩⟩)⟩
  · have hw := hI.wInv hs
    obtain ⟨h1, h2, h3, h4, -⟩ := hw
    set x := curOp (N C.hist) p
    have hlin : ∀ pc' v' v'', LinW G (Rv C) (Sv C p) val .c11 v'' →
        LinW G (Rv C) (Sv C p) val pc' v' := by
      intro pc' v' v'' hl
      rcases hl with hl | hl | hl | ⟨hl, -⟩
      · exact Or.inl hl
      · exact Or.inr (Or.inl hl)
      · exact Or.inr (Or.inr (Or.inl hl))
      · cases hl
    by_cases hn : x ∈ L.map Prod.fst ∧ ¬ LinW G (Rv C) (Sv C p) val .c11 ⟨v₀, false, none⟩
    · have hval : val ∉ G := fun hv => hn.2 (Or.inl hv)
      obtain ⟨L', l1, l2, l3, l4⟩ := hI.retract hs hn.1 (Or.inr (h2 hn.1 hval))
      refine ⟨L', hI.frame hwf hpe hN rfl (fun _ _ => rfl) hst l1 l2 l3 (hI.sinv p) ?_⟩
      change PInv (v₀ := v₀) L' G (Rv C) (Sv C p) _ _
      simp only [Function.update_self]
      exact ⟨⟨fun hx => absurd hx l4, fun hl => absurd hl hn.2⟩, fun hx => absurd hx l4, h3, h4,
        trivial⟩
    · refine ⟨L, hI.frame hwf hpe hN rfl (fun _ _ => rfl) hst hI.lin rfl (LSame.rfl' _ _)
        (hI.sinv p) ?_⟩
      change PInv (v₀ := v₀) L G (Rv C) (Sv C p) _ _
      simp only [Function.update_self]
      refine ⟨⟨fun hx => ?_, fun hl => h1.2 (hlin _ _ _ hl)⟩, h2, h3, h4, trivial⟩
      by_contra hl; exact hn ⟨hx, hl⟩

end Podc.NestingSafeRecoverable.Alg1
