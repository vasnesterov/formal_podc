import Papers.PODC2025.MinimalistLE.Main
import Cslib.Computability.Distributed.SelfStabilization.StoneAge

/-!
# Remarks of the paper: randomness is necessary; Eq. (2) is necessary

* `deterministic_impossible` (§1.3, "On the use of randomness"): no deterministic uniform beeping
  protocol solves Eventual Leader Election on any graph with at least two nodes and no isolated node
  when all nodes start in the same state — all nodes stay in the same state forever.
* `triangle_no_leader` (§5, Discussion; necessity of `V ⊆ W_0` in Eq. (2)): on a triangle, starting
  with *all three nodes leaders* but one beeping (`B•`) and one frozen (`F•`), all leaders are
  eliminated by round 3 and there is no leader in any later round, for every coin field. So Lemma 9
  fails without the assumption that all nodes start waiting.
* `lemma19_fails_K2`, `lemma19_fails_P3` — Lemma 19, read per configuration, fails for `D = 1, 2`.
* `theorem2_ae_example` — non-vacuity: the hypotheses of `theorem2_ae` hold for the paper's initial
  configuration on the triangle with `p = 1/2`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory unitInterval

namespace MinimalistLE

section deterministic

/-- A deterministic uniform beeping protocol (the paper's `(Q_ℓ, Q_b, q_s, δ_⊥, δ_⊤)` with
deterministic transitions). -/
structure DetProtocol (Q : Type*) where
  beeping : Q → Bool
  start : Q
  δbot : Q → Q
  δtop : Q → Q

variable {V Q : Type*} (G : SimpleGraph V) (M : DetProtocol Q)

open Classical in
/-- A deterministic beeping protocol is a stone-age algorithm: a node only senses whether some
node of its closed neighbourhood beeps. -/
noncomputable def DetProtocol.toStoneAge (M : DetProtocol Q) : Cslib.StoneAge.Algorithm Q :=
  ⟨fun q S => if ∃ q' ∈ S, M.beeping q' then M.δtop q else M.δbot q⟩

/-- Synchronous execution of a deterministic beeping protocol, all nodes starting in `q_s`: the
stone-age execution under the synchronous schedule. -/
noncomputable def DetProtocol.run (M : DetProtocol Q) (G : SimpleGraph V) : ℕ → V → Q :=
  Cslib.StoneAge.run G M.toStoneAge (fun _ => M.start) Cslib.StoneAge.sync

theorem DetProtocol.run_zero (v : V) : M.run G 0 v = M.start := rfl

open Classical in
/-- One synchronous beeping round: a node hears a beep iff it or a neighbour beeps. -/
theorem DetProtocol.run_succ (t : ℕ) (v : V) : M.run G (t + 1) v =
    if M.beeping (M.run G t v) ∨ ∃ w, G.Adj v w ∧ M.beeping (M.run G t w)
    then M.δtop (M.run G t v) else M.δbot (M.run G t v) := by
  rw [DetProtocol.run, ((Cslib.StoneAge.isRun_run G _ _ _).succ_of_mem (Set.mem_univ v))]
  refine if_congr ?_ rfl rfl
  simp only [Cslib.StoneAge.mem_signal]
  constructor
  · rintro ⟨_, ⟨u, rfl | hu, rfl⟩, hb⟩
    · exact Or.inl hb
    · exact Or.inr ⟨u, hu, hb⟩
  · rintro (hb | ⟨w, hw, hb⟩)
    · exact ⟨_, ⟨v, Or.inl rfl, rfl⟩, hb⟩
    · exact ⟨_, ⟨w, Or.inr hw, rfl⟩, hb⟩

/-- Without isolated nodes, all nodes are always in the same state. -/
theorem DetProtocol.run_const (hiso : ∀ v, ∃ w, G.Adj v w) (t : ℕ) (v w : V) :
    M.run G t v = M.run G t w := by
  induction t generalizing v w with
  | zero => rfl
  | succ t ih =>
    have key : ∀ x, (M.beeping (M.run G t x) ∨ ∃ y, G.Adj x y ∧ M.beeping (M.run G t y)) ↔
        M.beeping (M.run G t v) = true := by
      intro x
      obtain ⟨y, hy⟩ := hiso x
      constructor
      · rintro (h | ⟨y', -, h⟩)
        · rwa [ih v x]
        · rwa [ih v y']
      · intro h; exact Or.inl (by rwa [ih x v])
    rw [M.run_succ G t v, M.run_succ G t w]
    split_ifs with h1 h2 h2
    · rw [ih v w]
    · exact absurd ((key w).2 ((key v).1 h1)) h2
    · exact absurd ((key v).2 ((key w).1 h2)) h1
    · rw [ih v w]

/-- **Randomness is necessary.** For every deterministic uniform beeping protocol and every set `L` of
"leader" states, on any graph with two distinct nodes and no isolated node, there is no round `T` and
node `u⋆` such that from `T` on `u⋆` is the only node in `L` (Definition 1 fails). -/
theorem deterministic_impossible (hiso : ∀ v, ∃ w, G.Adj v w) {a b : V} (hab : a ≠ b)
    (L : Set Q) : ¬ ∃ T u, ∀ t, T ≤ t → ∀ w, M.run G t w ∈ L ↔ w = u := by
  rintro ⟨T, u, h⟩
  have hu := (h T le_rfl u).2 rfl
  have ha := (h T le_rfl a).1 (by rwa [M.run_const G hiso T a u])
  have hb := (h T le_rfl b).1 (by rwa [M.run_const G hiso T b u])
  exact hab (ha.trans hb.symm)

end deterministic

section triangle

/-- The triangle. -/
abbrev K3 : SimpleGraph (Fin 3) := ⊤

/-- All three nodes are leaders, but node 0 is beeping and node 1 is frozen. -/
def badInit : Fin 3 → St := ![⟨.B, true⟩, ⟨.F, true⟩, ⟨.W, true⟩]

theorem badInit_all_leaders (v : Fin 3) : (badInit v).leader = true := by
  fin_cases v <;> rfl

/-- **Eq. (2) is necessary for Lemma 9.** From `badInit` there is no leader in round 3, whatever the
coins; hence none in any later round. -/
theorem triangle_no_leader (c : ℕ → Fin 3 → Bool) (t : ℕ) (ht : 3 ≤ t) (v : Fin 3) :
    (exec K3 badInit c t v).leader = false := by
  have h3 : ∀ v, (exec K3 badInit c 3 v).leader = false := by
    intro v
    fin_cases v <;>
      simp [exec, next, Heard, badInit, SimpleGraph.top_adj, Fin.exists_fin_succ]
  by_contra h
  exact absurd (h3 v) (by simpa using leader_anti ht (Bool.not_eq_false _ ▸ h))

/-- Non-vacuity of Theorem 2: the triangle with `p = 1/2` from the paper's initial configuration. -/
theorem theorem2_ae_example :
    ∀ᵐ ω ∂(coinP (ι := ℕ × Fin 3) ⟨1 / 2, by norm_num, by norm_num⟩),
      ∃ T, UniqueFrom K3 initAll T ω :=
  theorem2_ae SimpleGraph.connected_top goodInit_initAll _ (by norm_num) (by norm_num)

end triangle

section lemma19

/-! ### Lemma 19 fails per configuration for small `D`

Lemma 19 claims: if `u, v` are both leaders in round `t`, then with constant probability one of them
is eliminated before round `t + 2D + 1`. Read per configuration in round `t` (as its proof does), this
fails: on `K₂` (`D = 1`) with both nodes in `B•` in round `t = 1`, and on the path `0–1–2` (`D = 2`)
with the endpoints in `B•` in round `t = 1`, no elimination happens before round `t + 2D + 1`
(on `K₂` not even by round `t + 2D + 1 = 4`), for **every** coin field. -/

/-- The single edge `K₂` (`D = 1`). -/
abbrev K2 : SimpleGraph (Fin 2) := ⊤

/-- **Lemma 19 fails on `K₂`.** If both coins of round 0 are `true` (both nodes in `B•` in round
`t = 1`, an event of probability `p²`), both nodes are still leaders in round `4 = t + 2D + 2`,
whatever the later coins. -/
theorem lemma19_fails_K2 (c : ℕ → Fin 2 → Bool) (h0 : c 0 0 = true) (h1 : c 0 1 = true)
    (s : ℕ) (hs : s ≤ 4) (v : Fin 2) : (exec K2 initAll c s v).leader = true := by
  have e1 : exec K2 initAll c 1 = fun _ => ⟨.B, true⟩ := by
    funext w; fin_cases w <;> simp [exec, next, Heard, initAll, h0, h1]
  have e2 : exec K2 initAll c 2 = fun _ => ⟨.F, true⟩ := by
    funext w; rw [exec_succ, e1]; simp [next]
  have e3 : exec K2 initAll c 3 = fun _ => ⟨.W, true⟩ := by
    funext w; rw [exec_succ, e2]; simp [next]
  have e4 : ∀ w, (exec K2 initAll c 4 w).leader = true := by
    intro w; rw [exec_succ, e3]; simp only [next, Heard]; split_ifs with h <;> simp_all
  exact leader_anti hs (e4 v)

/-- The path `0 – 1 – 2` (`D = 2`). -/
def P3 : SimpleGraph (Fin 3) := SimpleGraph.fromRel fun a b => a.val + 1 = b.val

instance : DecidableRel P3.Adj := fun a b => by unfold P3; infer_instance

/-- **Lemma 19 fails on the path `0–1–2`.** If the round-0 coins are `true, false, true` (the
endpoints `u = 0`, `v = 2` in `B•` in round `t = 1`), both endpoints are still leaders in round
`5 = t + 2D`, whatever the later coins: no elimination before round `t + 2D + 1`. -/
theorem lemma19_fails_P3 (c : ℕ → Fin 3 → Bool) (h0 : c 0 0 = true) (h1 : c 0 1 = false)
    (h2 : c 0 2 = true) (s : ℕ) (hs : s ≤ 5) :
    (exec P3 initAll c s 0).leader = true ∧ (exec P3 initAll c s 2).leader = true := by
  have e1 : exec P3 initAll c 1 = ![⟨.B, true⟩, ⟨.W, true⟩, ⟨.B, true⟩] := by
    funext w; fin_cases w <;> simp [exec, next, Heard, initAll, h0, h1, h2]
  have e2 : exec P3 initAll c 2 = ![⟨.F, true⟩, ⟨.B, false⟩, ⟨.F, true⟩] := by
    funext w; rw [exec_succ, e1]
    fin_cases w <;> simp [next, Heard, P3, SimpleGraph.fromRel_adj, Fin.exists_fin_succ]
  have e3 : exec P3 initAll c 3 = ![⟨.W, true⟩, ⟨.F, false⟩, ⟨.W, true⟩] := by
    funext w; rw [exec_succ, e2]; fin_cases w <;> simp [next]
  have e4 : ∀ w : Fin 3, w ≠ 1 → (exec P3 initAll c 4 w).leader = true ∧
      (exec P3 initAll c 4 1) = ⟨.W, false⟩ := by
    intro w hw
    rw [exec_succ, e3]
    refine ⟨?_, by simp [next]⟩
    fin_cases w
    · simp only [next, Heard, P3, SimpleGraph.fromRel_adj]; split_ifs <;> simp_all [Fin.exists_fin_succ]
    · exact absurd rfl hw
    · simp only [next, Heard, P3, SimpleGraph.fromRel_adj]; split_ifs <;> simp_all [Fin.exists_fin_succ]
  have e5 : ∀ w : Fin 3, w ≠ 1 → (exec P3 initAll c 5 w).leader = true := by
    intro w hw
    obtain ⟨hl, h1'⟩ := e4 w hw
    rw [exec_succ]
    rcases hp : (exec P3 initAll c 4 w).phase
    · have hH : ¬ Heard P3 (exec P3 initAll c 4) w := by
        rintro ⟨x, hx, hxB⟩
        fin_cases w <;> fin_cases x <;> simp_all [P3, SimpleGraph.fromRel_adj]
      rw [next_of_W hp]
      simp only [hH, ↓reduceIte]
      split_ifs <;> simp_all
    · simp [hp, hl]
    · simp [hp, hl]
  exact ⟨leader_anti hs (e5 0 (by decide)), leader_anti hs (e5 2 (by decide))⟩

end lemma19

end MinimalistLE
