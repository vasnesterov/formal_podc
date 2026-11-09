/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Append
import Papers.PODC2019.ReconfigurableCommit.Steps1

/-!
# Preservation of the invariant: delivering `PREPARE` (lines 4–17)
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

theorem Inv.deliver_prepare (hI : Inv Pa st) {src dst : P} {t : T} {lo : Option Pl}
    (hm : Msg.prepare t lo ∈ st.sent src dst)
    (h : handle Pa st src dst (.prepare t lo) = some st') : Inv Pa st' := by
  cases hk : (st.loc dst).arr.findSlot t with
  | some k => exact hI.deliver_prepare_old hk h
  | none =>
    simp only [handle, hk] at h
    split_ifs at h with hlead
    cases h
    obtain ⟨hsh, l₀, hl₀, hlo⟩ := hI.m_prepare _ _ _ _ hm
    have hfind : ∀ k, ((st.loc dst).arr.ent k).map (·.1) ≠ some t := by
      intro k
      by_cases hkl : k ≤ (st.loc dst).arr.len
      · exact findSlot_none hk k hkl
      · have : ((st.loc dst).arr.ent k).isSome = false := by
          by_contra hc
          have := hI.loc_len dst k ((hI.loc_ent dst k).1 (by simpa [Option.isSome_iff_ne_none] using hc))
          omega
        cases hh : (st.loc dst).arr.ent k
        · simp
        · simp [hh] at this
    have hbase : ∀ (l' : Pl) (d' : Dec) (vi : Option (Finset ℕ × Finset ℕ × ℕ)),
        (l' = Pa.σ.eps ∧ d' = .abort ∨ l' = Pa.σ.proj l₀ (Pa.home dst)) →
        (vi = none → d' = .abort) →
        (∀ J₁ J₂ hl, vi = some (J₁, J₂, hl) →
          J₁ = slotsWhere (st.loc dst).arr ((st.loc dst).next + 1) (condL1 (st.loc dst).arr) ∧
          J₂ = slotsWhere (st.loc dst).arr ((st.loc dst).next + 1) (condL2 (st.loc dst).arr) ∧
          hl = st.hist.length ∧
          d' = (Pa.fs (Pa.home dst) (payloadsWhere (st.loc dst).arr ((st.loc dst).next + 1)
              (condL1 (st.loc dst).arr)) l').meet
            (Pa.gs (Pa.home dst) (payloadsWhere (st.loc dst).arr ((st.loc dst).next + 1)
              (condL2 (st.loc dst).arr)) l')) →
        Inv Pa (({ st.setLoc dst { st.loc dst with
          next := (st.loc dst).next + 1
          arr := { (st.loc dst).arr with
            ent := Function.update (st.loc dst).arr.ent ((st.loc dst).next + 1) (some (t, l', d'))
            phase := Function.update (st.loc dst).arr.phase ((st.loc dst).next + 1) .prepared
            len := max (st.loc dst).arr.len ((st.loc dst).next + 1) } } with
          elog := upd3 st.elog (Pa.home dst) ((st.loc dst).epoch (Pa.home dst))
            ((st.loc dst).next + 1) (some ((t, l', d'), (st.loc dst).epoch (Pa.home dst)))
          vinfo := upd3 st.vinfo (Pa.home dst) ((st.loc dst).epoch (Pa.home dst))
            ((st.loc dst).next + 1) vi } : State T Pl S P).send1 dst src
          (.prepareAck ((st.loc dst).epoch (Pa.home dst)) (Pa.home dst) ((st.loc dst).next + 1)
            t l' d')) := by
      intro l' d' vi hl hvn hvs
      have hI₁ := hI.appendSlot (p := dst) (t := t) (l' := l') (d' := d') (vi := vi) hlead hfind
        ⟨hsh, l₀, hl₀, hl.symm⟩ hvn hvs rfl
      have heq : ({ st.setLoc dst { st.loc dst with
          next := (st.loc dst).next + 1
          arr := { (st.loc dst).arr with
            ent := Function.update (st.loc dst).arr.ent ((st.loc dst).next + 1) (some (t, l', d'))
            phase := Function.update (st.loc dst).arr.phase ((st.loc dst).next + 1) .prepared
            len := max (st.loc dst).arr.len ((st.loc dst).next + 1) } } with
          elog := upd3 st.elog (Pa.home dst) ((st.loc dst).epoch (Pa.home dst))
            ((st.loc dst).next + 1) (some ((t, l', d'), (st.loc dst).epoch (Pa.home dst)))
          vinfo := upd3 st.vinfo (Pa.home dst) ((st.loc dst).epoch (Pa.home dst))
            ((st.loc dst).next + 1) vi } : State T Pl S P) =
          st.appendSlot dst ((st.loc dst).next + 1) { (st.loc dst).arr with
            ent := Function.update (st.loc dst).arr.ent ((st.loc dst).next + 1) (some (t, l', d'))
            phase := Function.update (st.loc dst).arr.phase ((st.loc dst).next + 1) .prepared
            len := max (st.loc dst).arr.len ((st.loc dst).next + 1) }
            (Pa.home dst) ((st.loc dst).epoch (Pa.home dst)) (t, l', d') vi := by
        unfold State.setLoc State.appendSlot
        simp only [State.mk.injEq, and_true, true_and]
        funext q
        by_cases hq : q = dst
        · subst hq; simp
        · simp [hq]
      rw [heq]
      refine hI₁.send_benign dst _ fun b m hb => ?_
      split_ifs at hb with hbq
      cases hb
      exact ⟨(st.loc dst).epoch (Pa.home dst), by simp [upd3_apply]⟩
    cases lo with
    | none =>
      exact hbase _ _ _ (Or.inl ⟨rfl, rfl⟩) (fun _ => rfl) (fun _ _ _ h => by cases h)
    | some l =>
      have hl : l = Pa.σ.proj l₀ (Pa.home dst) := by
        rcases hlo with h | h
        · cases h
        · exact Option.some.inj h
      exact hbase _ _ _ (Or.inr hl) (fun h => by cases h)
        (fun J₁ J₂ hl h => by
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, rfl, rfl⟩)

end Podc.ReconfigurableCommit
