import Podc.ContentOblivious.Model
import Papers.PODC2024.ContentObliviousLE.RingCounting

/-!
# Algorithm 1: quiescently stabilizing leader election on oriented rings (warm-up)

Frei, Gelles, Ghazy, Nolin, *Content-Oblivious Leader Election on Rings*, PODC 2024 (brief
announcement, Section 4) / arXiv 2405.03646, Section 3.1 (Lemmas 5–13) and Lemma 15.

Only CW pulses are used: sent on `Port1` (`true`), received on `Port0` (`false`). IDs are only
required to be positive, not distinct (Lemma 15): all nodes of maximal ID end up as `Leader`.
-/

namespace Podc.ContentOblivious.Alg1

open Podc.ContentOblivious Finset

/-- Local state: ID, `ρcw`, and the output variable. -/
structure S where
  id : ℕ
  rcw : ℕ
  leader : Bool

/-- Algorithm 1. Every node sends one CW pulse and relays every CW pulse except the one making
`ρcw = ID`. (No CCW pulse ever exists; such a pulse would be ignored.) -/
abbrev alg : Algo where
  State := S
  init i := (⟨i, 0, false⟩, fun q => if q then 1 else 0)
  recv s p := if p then (s, fun _ => 0) else
    (⟨s.id, s.rcw + 1, decide (s.rcw + 1 = s.id)⟩, fun q => if q ∧ s.rcw + 1 ≠ s.id then 1 else 0)
  leader s := s.leader

variable {n : ℕ} [NeZero n] {id : ZMod n → ℕ} {M : ℕ}

/-- Invariant: Lemma 5 and the bound of Corollary 13, plus agreement of the local state. -/
def Inv (id : ZMod n → ℕ) (M : ℕ) (c : Config (ZMod n) S) : Prop :=
  ∀ v, (c.st v).id = id v ∧ (c.st v).rcw = c.recvd (v, false) ∧
    (c.st v).leader = decide (c.recvd (v, false) = id v) ∧
    c.sent (v, true) = c.recvd (v, false) + (if c.recvd (v, false) < id v then 1 else 0) ∧
    c.sent (v, false) = 0 ∧ c.recvd (v, true) = 0 ∧ c.recvd (v, false) ≤ M

theorem reach_inv (hpos : ∀ v, 0 < id v) (hM : ∀ v, id v ≤ M) {c : Config (ZMod n) S}
    (h : Reach (oriented n) alg id c) : Inv id M c := by
  induction h with
  | refl =>
    intro v; have := hpos v
    simp [initCfg]
    exact ⟨decide_eq_false (Nat.ne_of_lt this), by simp [this]⟩
  | @tail b c' hr hs ih =>
    obtain ⟨v, j, -, -, hlt⟩ := hs
    intro u
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih u
    cases j with
    | true =>
      simp only [oriented_peer_true] at hlt
      rw [(ih v).2.2.2.2.2.1, (ih (v + 1)).2.2.2.2.1] at hlt; omega
    | false =>
      simp only [oriented_peer_false] at hlt
      by_cases hu : u = v
      · subst hu
        have hb : b.recvd (u, false) + 1 ≤ M := by
          have e := (ih (u - 1)).2.2.2.1; have := (ih (u - 1)).2.2.2.2.2.2; have := hM (u - 1)
          rw [e] at hlt; split_ifs at hlt <;> omega
        have e_st : (deliver alg b u false).st u =
            ⟨id u, b.recvd (u, false) + 1, decide (b.recvd (u, false) + 1 = id u)⟩ := by
          simp [deliver, h1, h2]
        have e_r0 : (deliver alg b u false).recvd (u, false) = b.recvd (u, false) + 1 := by
          simp [deliver]
        have e_r1 : (deliver alg b u false).recvd (u, true) = b.recvd (u, true) := by simp [deliver]
        have e_s1 : (deliver alg b u false).sent (u, true) =
            b.sent (u, true) + if b.recvd (u, false) + 1 ≠ id u then 1 else 0 := by
          simp [deliver, h1, h2]
        have e_s0 : (deliver alg b u false).sent (u, false) = b.sent (u, false) := by simp [deliver]
        rw [e_st, e_r0, e_r1, e_s1, e_s0]
        refine ⟨rfl, rfl, rfl, ?_, h5, h6, hb⟩
        rw [h4]; split_ifs <;> omega
      · simp [deliver, hu, h1, h2, h3, h4, h5, h6, h7]

/-- **Algorithm 1 / Corollary 12, Lemma 15.** Every execution is finite and sends at most `n·IDmax`
pulses; in every final configuration the network is quiescent, every node has sent and received
exactly `IDmax` pulses, and the nodes in state `Leader` are exactly those of maximal ID (a unique
leader when the maximal ID is unique). IDs need not be distinct. -/
theorem algorithm_1 (hpos : ∀ v, 0 < id v) {ℓ : ZMod n} (hℓ : ∀ v, id v ≤ id ℓ) :
    (¬ ∃ f : ℕ → Config (ZMod n) S, f 0 = initCfg alg id ∧
        ∀ k, Step (oriented n) alg (f k) (f (k + 1))) ∧
    (∀ c, Reach (oriented n) alg id c → totalSent c ≤ n * id ℓ) ∧
    (∀ c, Reach (oriented n) alg id c → Final (oriented n) alg c →
      Quiescent (oriented n) alg c ∧ (∀ v, c.recvd (v, false) = id ℓ ∧ c.sent (v, true) = id ℓ) ∧
      (∀ v, (c.st v).leader = true ↔ id v = id ℓ) ∧ totalSent c = n * id ℓ) := by
  have hle : ∀ c, Reach (oriented n) alg id c → totalSent c ≤ n * id ℓ := by
    intro c hr
    have h := reach_inv hpos hℓ hr
    rw [totalSent, sum_ports]
    calc ∑ v, (c.sent (v, false) + c.sent (v, true)) ≤ ∑ _v : ZMod n, id ℓ := by
          refine sum_le_sum fun v _ => ?_
          obtain ⟨-, -, -, h4, h5, -, h7⟩ := h v
          have := hℓ v
          rw [h4, h5]; split_ifs <;> omega
      _ = n * id ℓ := by simp [ZMod.card]
  refine ⟨no_infinite_execution hle, hle, fun c hr hfin => ?_⟩
  have h := reach_inv hpos hℓ hr
  have hq : Quiescent (oriented n) alg c := by
    intro x
    by_contra hne
    exact hfin x.1 x.2 ⟨rfl, rfl, lt_of_le_of_ne (hr.recvd_le x) hne⟩
  have hprof : Ring.Profile (fun v => c.recvd (v, false)) (fun v => c.sent (v, true)) id :=
    fun v => (h v).2.2.2.1
  have htight : ∀ v, c.recvd (v + 1, false) = c.sent (v, true) := by
    intro v; have := hq (v + 1, false); simpa using this
  have hall := hprof.eq_max_of_good (fun v => (htight v).le) (hprof.good_of_tight htight)
    (fun v => (h v).2.2.2.2.2.2) (ℓ := ℓ) rfl
  refine ⟨hq, hall, fun v => ?_, ?_⟩
  · rw [(h v).2.2.1, (hall v).1, decide_eq_true_iff, eq_comm]
  · rw [totalSent, sum_ports]
    simp [(h _).2.2.2.2.1, (hall _).2, ZMod.card]

end Podc.ContentOblivious.Alg1
