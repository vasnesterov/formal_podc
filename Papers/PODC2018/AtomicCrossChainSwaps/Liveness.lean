import Papers.PODC2018.AtomicCrossChainSwaps.Safety
import Papers.PODC2018.AtomicCrossChainSwaps.Pebble

/-!
# Liveness of the repaired protocol (Lemmas 4.5, 4.6, Theorem 4.7)

If nobody deviates, every arc is triggered. Phase One is the lazy pebble game (`Fired`): a vertex
that fired by round `k` has its leaving contracts in place at time `k + 1`. If all vertices fire by
round `K` and the base timeout satisfies `K + 2 ≤ B`, every leader can release its secret in time,
and the secrets then flow back along shortest paths (the eager game on the transpose): every arc is
triggered by time `K + 2 + d` when all distances are `≤ d`. With `K, d ≤ diam D - 1` this gives the
paper's bound `2 · diam(D) · Δ`, provided `B ≥ diam D + 1` (one `Δ` more than the paper's `diam D`).
-/

namespace AtomicSwap

namespace Setting

variable {V : Type*} [DecidableEq V] [Fintype V] {P : Setting V} {C : Finset V}
  {sch : ℕ → Moves V}

local notation "S" t => P.run C sch t

lemma publishes_con {t : ℕ} {u w : V} (hp : P.Publishes C t (S t) u) (h : P.D.Adj u w) :
    ((S (t + 1)).con u w).isSome := by
  cases h0 : (S t).con u w with
  | some c => simp [P.con_succ C sch h0]
  | none =>
    have := (P.con_succ_iff C sch (c := t + 1)).mpr (Or.inr ⟨h0, rfl, h, Or.inl hp⟩)
    simp [this]

lemma rel_origin {t : ℕ} {v : V} {r : ℕ} (h : (S t).rel v = some r) :
    r < t ∧ P.Releases C r (S r) v := by
  induction t with
  | zero => simp [St.init] at h
  | succ t ih =>
    rw [run_succ] at h
    simp only [step] at h
    cases h0 : (S t).rel v with
    | some r' =>
      rw [h0] at h; cases h
      exact ⟨by have := (ih h0).1; omega, (ih h0).2⟩
    | none =>
      rw [h0] at h
      simp only [Option.none_or] at h
      split_ifs at h with hr
      cases h
      exact ⟨by omega, hr⟩

/-- **Lemma 4.5 (Phase One).** With no deviators, a vertex that fired by round `k` of the lazy
pebble game has contracts on all its leaving arcs at time `k + 1`. -/
theorem con_of_fired : ∀ {k : ℕ} {u w : V}, Fired P.D (P.L : Set V) k u → P.D.Adj u w →
    ((P.run ∅ sch (k + 1)).con u w).isSome
  | 0, u, w, hu, h => publishes_con ⟨by simp, fun _ => rfl, fun h' => absurd hu h'⟩ h
  | k + 1, u, w, hu, h => by
    rcases hu with hu | hu
    · exact P.con_isSome_mono ∅ sch (Nat.le_succ _) (con_of_fired hu h)
    · by_cases huL : u ∈ P.L
      · exact P.con_isSome_mono ∅ sch (Nat.le_succ _)
          (con_of_fired (Fired.of_mem (L := (P.L : Set V)) (by simpa using huL)) h)
      · exact publishes_con ⟨by simp, fun h' => absurd h' huL,
          fun _ x hx => con_of_fired (hu x hx) hx⟩ h

variable (hfix : P.fixed = true) (hsch : P.ValidSched ∅ sch)
include hfix hsch

omit hsch in
/-- With no deviators, a leader whose in-neighbours fired by round `K` releases its secret in time
if `K + 2 ≤ B`: its own hashlock is unlocked on all entering arcs at time `K + 2`. -/
theorem release_in_time {K : ℕ} (hB : K + 2 ≤ P.B) {ℓ x : V} (hℓ : ℓ ∈ P.L)
    (hin : ∀ y, P.D.Adj y ℓ → Fired P.D (P.L : Set V) K y) (hx : P.D.Adj x ℓ) :
    ((P.run ∅ sch (K + 2)).unl x ℓ ℓ).isSome := by
  cases h0 : (P.run ∅ sch (K + 1)).rel ℓ with
  | some r =>
    obtain ⟨hr, hrel⟩ := rel_origin h0
    exact P.unl_isSome_mono ∅ sch (by omega) (releases_unl hfix hrel hx)
  | none =>
    have hrel : P.Releases ∅ (K + 1) (P.run ∅ sch (K + 1)) ℓ :=
      ⟨by simp, hℓ, h0, fun y hy => con_of_fired (hin y hy) hy, fun _ => hB⟩
    exact releases_unl hfix hrel hx

/-- **Lemma 4.6 (Phase Two).** With no deviators, if every vertex fired by round `K` and
`K + 2 ≤ B`, hashlock `ℓ` is unlocked on every arc entering a vertex at distance `≤ d` from `ℓ`
by time `K + 2 + d`. -/
theorem unl_of_reachIn {K : ℕ} (hK : ∀ v, Fired P.D (P.L : Set V) K v) (hB : K + 2 ≤ P.B)
    {ℓ : V} (hℓ : ℓ ∈ P.L) : ∀ (d : ℕ) {u v : V}, ReachIn P.D d v ℓ → P.D.Adj u v →
    ((P.run ∅ sch (K + 2 + d)).unl u v ℓ).isSome
  | 0, u, v, hv, huv => by
    obtain rfl : v = ℓ := hv.zero
    exact release_in_time hfix hB hℓ (fun y _ => hK y) huv
  | d + 1, u, v, hv, huv => by
    rcases Relation.relatesWithinSteps_succ_iff'.1 hv with hv | ⟨x, hvx, hx⟩
    · subst hv
      exact P.unl_isSome_mono ∅ sch (by omega)
        (release_in_time hfix hB hℓ (fun y _ => hK y) huv)
    · by_cases hℓv : ℓ = v
      · subst hℓv
        exact P.unl_isSome_mono ∅ sch (by omega)
          (release_in_time hfix hB hℓ (fun y _ => hK y) huv)
      have ih := unl_of_reachIn hK hB hℓ d hx hvx
      have := forward hfix hsch (by simp) hℓ hℓv hvx ih huv (con_of_fired (hK u) huv)
        (fun _ => by omega)
      have hmax : max (K + 2 + d) (K + 1) + 1 = K + 2 + (d + 1) := by omega
      rwa [hmax] at this

/-- **Theorem 4.7 (repaired protocol, explicit bound).** With no deviators, if every vertex fires
by round `K` of the lazy pebble game, all distances to leaders are `≤ d`, and `K + 2 ≤ B`, then
every arc is triggered by time `K + 2 + d`. -/
theorem liveness {K d : ℕ} (hK : ∀ v, Fired P.D (P.L : Set V) K v)
    (hd : ∀ v w, ReachIn P.D d v w) (hB : K + 2 ≤ P.B) {u v : V} (huv : P.D.Adj u v) :
    P.Trig (P.run ∅ sch (K + 2 + d)) u v :=
  fun ℓ hℓ => unl_of_reachIn hfix hsch hK hB hℓ d (hd v ℓ) huv

omit [DecidableEq V] hfix hsch in
lemma one_le_diam [Nontrivial V] {D : Digraph V} (hD : StronglyConnected D) : 1 ≤ diam D := by
  obtain ⟨u⟩ := (inferInstance : Nonempty V)
  obtain ⟨x, hx⟩ := exists_adj_from hD u
  have hp : IsPath D [u, x] := ⟨by simp, by simpa using hx, by simp⟩
  have := le_diam hp
  simpa using this

/-- **Theorem 4.7 (repaired protocol).** In a strongly connected swap digraph with a feedback
vertex set of leaders and base timeout `B ≥ diam D + 1`, if nobody deviates, every arc is
triggered within `2 · diam(D)` (in units of `Δ`). -/
theorem theorem_4_7 [Nontrivial V] (hD : StronglyConnected P.D) (hL : IsFVS P.D (P.L : Set V))
    (hB : diam P.D + 1 ≤ P.B) {u v : V} (huv : P.D.Adj u v) :
    P.Trig (P.run ∅ sch (2 * diam P.D)) u v := by
  have h1 := one_le_diam hD
  have := liveness hfix hsch (fired_diam hD hL) (reachIn_diam hD) (by omega) huv
  rwa [show diam P.D - 1 + 2 + (diam P.D - 1) = 2 * diam P.D by omega] at this

end Setting

end AtomicSwap
