import Papers.PODC2011.CoordinatedConsensusDynamic.Knowledge
import Papers.PODC2011.CoordinatedConsensusDynamic.Coordination

/-!
# Simultaneous consensus (Section 5) and Theorem 6.1

* Known `n`: no simultaneous consensus protocol decides before time `n - 1`
  (`simultaneous_lb_known`), and deciding at time `n - 1` is possible (`simKnown`).
* Unknown `n`: a simultaneous consensus protocol can only decide at time `t` if `t ≥ n`
  (`simultaneous_lb_unknown`), i.e. its decision time is an upper bound on the count; deciding at
  time `n` is possible (`simUnknown`, using the criterion of Lemma 3.1).
* Theorem 6.1: every `Δ`-coordinated consensus protocol has an execution in which no node decides
  before time `n - Δ - 1` (known `n`).
-/

namespace CoordCons

open DGraph Relation

/-- The complete graph on `{0, …, n-1}` in every round, constant input `b`, a-priori info `N`. -/
def complete (n : ℕ) (b : Bool) (N : ℕ) : DGraph Bool where
  V := Finset.range n
  input := fun _ => b
  N := N
  adj := fun _ x y => x < n ∧ y < n ∧ x ≠ y

theorem complete_valid {n : ℕ} (hn : 1 ≤ n) (b : Bool) (N : ℕ) : (complete n b N).Valid := by
  refine ⟨⟨0, by simp [complete]; omega⟩, fun r x y h => ?_, fun r x y h => ?_,
    fun r x h => h.2.2 rfl, fun r _ x hx y hy => ?_⟩
  · simp only [complete, Finset.mem_range]; exact ⟨h.1, h.2.1⟩
  · exact ⟨h.2.1, h.1, h.2.2.symm⟩
  · simp only [complete, Finset.mem_range] at hx hy
    by_cases hxy : x = y
    · subst hxy; exact ReflTransGen.refl
    · exact ReflTransGen.single ⟨hx, hy, hxy⟩

theorem complete_knownN {n : ℕ} (hn : 1 ≤ n) (b : Bool) : KnownN n (complete n b n) :=
  ⟨complete_valid hn b n, by simp [complete], rfl⟩

theorem complete_unknownN {n : ℕ} (hn : 1 ≤ n) (b : Bool) : UnknownN (complete n b 0) :=
  ⟨complete_valid hn b 0, rfl⟩

/-! ### Lower bounds -/

/-- **Section 5 (consequence of Theorem 5.1 (1))**: with `n` known a priori, no simultaneous
consensus protocol decides at any time `t ≤ n - 2`, in any execution. -/
theorem simultaneous_lb_known {n : ℕ} {D : Decision Bool} (hD : Consensus (KnownN n) D)
    (hC : Coordinated (KnownN n) 0 D) {G : DGraph Bool} (hG : KnownN n G) {t : ℕ}
    (ht : t + 2 ≤ n) : ∀ u ∈ G.V, D G u t = none :=
  no_simultaneous_decision hD hC hG
    (theorem_5_1_known ht hG (complete_knownN (by omega) false))
    (theorem_5_1_known ht hG (complete_knownN (by omega) true))
    (by simp [complete]) (by simp [complete])

/-- **Section 5 (consequence of Theorem 5.1 (2))**: with no a-priori knowledge of the count, a
simultaneous consensus protocol never decides at a time `t < n`; hence its decision time is an
upper bound on the count. -/
theorem simultaneous_lb_unknown {D : Decision Bool} (hD : Consensus UnknownN D)
    (hC : Coordinated UnknownN 0 D) {G : DGraph Bool} (hG : UnknownN G) {u t : ℕ}
    (hu : u ∈ G.V) (hdec : (D G u t).isSome) : G.V.card ≤ t := by
  by_contra hlt
  push Not at hlt
  have := no_simultaneous_decision hD hC hG
    (theorem_5_1_unknown (t := t) hG (complete_unknownN (n := t + 1) (by omega) false) (by omega)
      (by simp [complete]))
    (theorem_5_1_unknown (t := t) hG (complete_unknownN (n := t + 1) (by omega) true) (by omega)
      (by simp [complete]))
    (by simp [complete]) (by simp [complete]) u hu
  simp [this] at hdec

/-! ### Upper bounds -/

open Classical in
/-- Known `n`: at time `n - 1` decide whether some input is `1` (everybody knows all inputs). -/
noncomputable def simKnown : Decision Bool := fun G u t =>
  if G.N ≤ t + 1 then some (decide (∃ w, G.Reach w 0 u t ∧ G.input w = true)) else none

theorem simKnown_local : Local simKnown := by
  intro G H u t h
  have hex : (∃ w, G.Reach w 0 u t ∧ G.input w = true) ↔
      (∃ w, H.Reach w 0 u t ∧ H.input w = true) := by
    constructor
    · rintro ⟨w, hw, hi⟩; exact ⟨w, h.reach_iff.1 hw, h.input_eq hw ▸ hi⟩
    · rintro ⟨w, hw, hi⟩
      exact ⟨w, h.reach_iff.2 hw, (h.input_eq (h.reach_iff.2 hw)).symm ▸ hi⟩
  simp only [simKnown, h.N_eq]
  split_ifs
  · rw [decide_eq_decide.2 hex]
  · rfl

/-- In a valid execution, once `t ≥ n - 1` the rule computes "some input is `1`". -/
theorem exists_reach_iff {G : DGraph Bool} (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V)
    (ht : G.V.card ≤ t + 1) :
    (∃ w, G.Reach w 0 u t ∧ G.input w = true) ↔ ∃ w ∈ G.V, G.input w = true := by
  have hp := past_eq_V hG hu (t := t) (s := 0) (by omega)
  constructor
  · rintro ⟨w, hw, hi⟩; exact ⟨w, (hw.mem_iff hG).2 hu, hi⟩
  · rintro ⟨w, hw, hi⟩
    rw [← hp] at hw
    exact ⟨w, (mem_past.1 hw).2, hi⟩

theorem validity_of_decide {G : DGraph Bool} (hG : G.Valid) (v : Bool)
    (hv : decide (∃ w ∈ G.V, G.input w = true) = v) : ∃ w ∈ G.V, G.input w = v := by
  cases v with
  | true => simpa using hv
  | false =>
    simp only [decide_eq_false_iff_not, not_exists, not_and, Bool.not_eq_true] at hv
    obtain ⟨w, hw⟩ := hG.nonempty
    exact ⟨w, hw, hv w hw⟩

/-- The rule `simKnown` solves simultaneous consensus with known `n`, deciding exactly at time
`n - 1` (so the lower bound `simultaneous_lb_known` is tight). -/
theorem simKnown_spec (n : ℕ) :
    Consensus (KnownN n) simKnown ∧ Coordinated (KnownN n) 0 simKnown ∧
      ∀ G, KnownN n G → ∀ u t, ((simKnown G u t).isSome ↔ n ≤ t + 1) := by
  have hval : ∀ G : DGraph Bool, KnownN n G → ∀ u ∈ G.V, ∀ t, n ≤ t + 1 →
      simKnown G u t = some (decide (∃ w ∈ G.V, G.input w = true)) := by
    intro G hG u hu t ht
    simp only [simKnown, hG.2.2, if_pos ht]
    congr 1
    exact decide_eq_decide.2 (exists_reach_iff hG.1 hu (by rw [hG.2.1]; exact ht))
  have hiff : ∀ G : DGraph Bool, KnownN n G → ∀ u t, ((simKnown G u t).isSome ↔ n ≤ t + 1) := by
    intro G hG u t
    simp only [simKnown, hG.2.2]
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false (by simp) h
  refine ⟨⟨simKnown_local, ?_, ?_, ?_, ?_⟩, ?_, hiff⟩
  · intro G hG u hu t v h
    have ht : n ≤ t + 1 := (hiff G hG u t).1 (by simp [h])
    rw [hval G hG u hu t ht] at h
    rw [hval G hG u hu (t + 1) (by omega), h]
  · intro G hG u hu w hw t t' a b ha hb
    have ht : n ≤ t + 1 := (hiff G hG u t).1 (by simp [ha])
    have ht' : n ≤ t' + 1 := (hiff G hG w t').1 (by simp [hb])
    rw [hval G hG u hu t ht] at ha
    rw [hval G hG w hw t' ht'] at hb
    exact (Option.some.inj ha).symm.trans (Option.some.inj hb)
  · intro G hG u hu t v h
    have ht : n ≤ t + 1 := (hiff G hG u t).1 (by simp [h])
    rw [hval G hG u hu t ht] at h
    exact validity_of_decide hG.1 v (Option.some.inj h)
  · intro G hG u hu
    exact ⟨n, (hiff G hG u n).2 (by omega)⟩
  · intro G hG u hu t h w hw
    rw [hiff G hG u t] at h
    rw [hiff G hG w (t + 0)]
    exact h

open Classical in
/-- Unknown `n`: decide as soon as `past(u,t)(0) = past(u,t)(1)` (then `u` knows `n`) and
`t ≥ n`. -/
noncomputable def simUnknown : Decision Bool := fun G u t =>
  if (∀ w, G.Reach w 0 u t → G.Reach w 1 u t) ∧ {w | G.Reach w 0 u t}.ncard ≤ t then
    some (decide (∃ w, G.Reach w 0 u t ∧ G.input w = true)) else none

theorem simUnknown_local : Local simUnknown := by
  intro G H u t h
  have hex : (∃ w, G.Reach w 0 u t ∧ G.input w = true) ↔
      (∃ w, H.Reach w 0 u t ∧ H.input w = true) := by
    constructor
    · rintro ⟨w, hw, hi⟩; exact ⟨w, h.reach_iff.1 hw, h.input_eq hw ▸ hi⟩
    · rintro ⟨w, hw, hi⟩
      exact ⟨w, h.reach_iff.2 hw, (h.input_eq (h.reach_iff.2 hw)).symm ▸ hi⟩
  have hset : {w | G.Reach w 0 u t} = {w | H.Reach w 0 u t} := by
    ext w; exact h.reach_iff
  have hcl : (∀ w, G.Reach w 0 u t → G.Reach w 1 u t) ↔
      (∀ w, H.Reach w 0 u t → H.Reach w 1 u t) := by
    constructor
    · intro hc w hw; exact h.reach_iff.1 (hc w (h.reach_iff.2 hw))
    · intro hc w hw; exact h.reach_iff.2 (hc w (h.reach_iff.1 hw))
  simp only [simUnknown]
  by_cases hc : (∀ w, G.Reach w 0 u t → G.Reach w 1 u t) ∧ {w | G.Reach w 0 u t}.ncard ≤ t
  · rw [if_pos hc, if_pos ⟨hcl.1 hc.1, hset ▸ hc.2⟩, decide_eq_decide.2 hex]
  · rw [if_neg hc, if_neg (fun h => hc ⟨hcl.2 h.1, hset ▸ h.2⟩)]

/-- The test of `simUnknown` fires exactly at times `t ≥ n`. -/
theorem simUnknown_cond_iff {G : DGraph Bool} (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V) :
    ((∀ w, G.Reach w 0 u t → G.Reach w 1 u t) ∧ {w | G.Reach w 0 u t}.ncard ≤ t) ↔
      G.V.card ≤ t := by
  have hset : ∀ (h : ∀ w ∈ G.V, G.Reach w 0 u t), {w | G.Reach w 0 u t} = ↑G.V := by
    intro h; ext w
    exact ⟨fun hw => (hw.mem_iff hG).2 hu, fun hw => h w hw⟩
  constructor
  · rintro ⟨hc, hn⟩
    have h1 := reach_one_of_closed hG hu hc
    rw [hset (fun w hw => (h1 w hw).of_le (Nat.zero_le 1)), Set.ncard_coe_finset] at hn
    exact hn
  · intro ht
    have hp := past_eq_V hG hu (t := t) (s := 1) (by omega)
    have h1 : ∀ w ∈ G.V, G.Reach w 1 u t := fun w hw => (mem_past.1 (hp ▸ hw)).2
    refine ⟨fun w hw => h1 w ((hw.mem_iff hG).2 hu), ?_⟩
    rw [hset (fun w hw => (h1 w hw).of_le (Nat.zero_le 1)), Set.ncard_coe_finset]
    exact ht

/-- The rule `simUnknown` solves simultaneous consensus without knowledge of `n`, deciding
exactly at time `n` (so `simultaneous_lb_unknown` is tight). -/
theorem simUnknown_spec :
    Consensus UnknownN simUnknown ∧ Coordinated UnknownN 0 simUnknown ∧
      ∀ G, UnknownN G → ∀ u ∈ G.V, ∀ t, ((simUnknown G u t).isSome ↔ G.V.card ≤ t) := by
  have hiff : ∀ G : DGraph Bool, UnknownN G → ∀ u ∈ G.V, ∀ t,
      ((simUnknown G u t).isSome ↔ G.V.card ≤ t) := by
    intro G hG u hu t
    rw [← simUnknown_cond_iff hG.1 hu]
    simp only [simUnknown]
    split_ifs with h
    · exact iff_of_true rfl h
    · exact iff_of_false (by simp) h
  have hval : ∀ G : DGraph Bool, UnknownN G → ∀ u ∈ G.V, ∀ t, G.V.card ≤ t →
      simUnknown G u t = some (decide (∃ w ∈ G.V, G.input w = true)) := by
    intro G hG u hu t ht
    simp only [simUnknown, if_pos ((simUnknown_cond_iff hG.1 hu).2 ht)]
    congr 1
    exact decide_eq_decide.2 (exists_reach_iff hG.1 hu (by omega))
  refine ⟨⟨simUnknown_local, ?_, ?_, ?_, ?_⟩, ?_, hiff⟩
  · intro G hG u hu t v h
    have ht := (hiff G hG u hu t).1 (by simp [h])
    rw [hval G hG u hu t ht] at h
    rw [hval G hG u hu (t + 1) (by omega), h]
  · intro G hG u hu w hw t t' a b ha hb
    have ht := (hiff G hG u hu t).1 (by simp [ha])
    have ht' := (hiff G hG w hw t').1 (by simp [hb])
    rw [hval G hG u hu t ht] at ha
    rw [hval G hG w hw t' ht'] at hb
    exact (Option.some.inj ha).symm.trans (Option.some.inj hb)
  · intro G hG u hu t v h
    have ht := (hiff G hG u hu t).1 (by simp [h])
    rw [hval G hG u hu t ht] at h
    exact validity_of_decide hG.1 v (Option.some.inj h)
  · intro G hG u hu
    exact ⟨G.V.card, (hiff G hG u hu _).2 le_rfl⟩
  · intro G hG u hu t h w hw
    rw [hiff G hG u hu t] at h
    rw [hiff G hG w hw (t + 0)]
    exact h

/-! ### Theorem 6.1 -/

/-- **Theorem 6.1.** For every `Δ`-coordinated consensus protocol (known `n ≥ 1`) there is an
execution in which no node decides before time `n - Δ - 1`. -/
theorem theorem_6_1 {n Δ : ℕ} (hn : 1 ≤ n) {D : Decision Bool} (hD : Consensus (KnownN n) D)
    (hC : Coordinated (KnownN n) Δ D) :
    ∃ G, KnownN n G ∧ ∀ u ∈ G.V, ∀ t, (D G u t).isSome → n ≤ t + Δ + 1 := by
  by_contra hcon
  push Not at hcon
  -- in every execution all nodes have decided by time `n - 2`
  have hall : ∀ G, KnownN n G → ∀ w ∈ G.V, (D G w (n - 2)).isSome := by
    intro G hG w hw
    obtain ⟨u, hu, t, hdec, ht⟩ := hcon G hG
    have h := hC G hG u hu t hdec w hw
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
    rw [hD.stable_le hG hw (by omega : t + Δ ≤ n - 2) hb]
    rfl
  -- a simultaneous protocol deciding at time `n - 2`
  let D' : Decision Bool := fun G u s => if n ≤ s + 2 then D G u (n - 2) else none
  have hD' : Consensus (KnownN n) D' := by
    refine ⟨fun G H u s h => ?_, fun G hG u hu s v h => ?_, fun G hG u hu w hw s s' a b ha hb => ?_,
      fun G hG u hu s v h => ?_, fun G hG u hu => ⟨n, ?_⟩⟩
    · simp only [D']
      split_ifs with hs
      · exact hD.loc _ _ _ _ (h.mono (by omega))
      · rfl
    · simp only [D'] at h ⊢
      split_ifs at h with hs
      rw [if_pos (by omega)]; exact h
    · simp only [D'] at ha hb
      split_ifs at ha hb
      exact hD.agreement G hG u hu w hw _ _ a b ha hb
    · simp only [D'] at h
      split_ifs at h
      exact hD.validity G hG u hu _ v h
    · simp only [D', if_pos (show n ≤ n + 2 by omega)]
      exact hall G hG u hu
  have hC' : Coordinated (KnownN n) 0 D' := by
    intro G hG u hu s h w hw
    simp only [D'] at h ⊢
    by_cases hs : n ≤ s + 2
    · rw [if_pos (by omega)]; exact hall G hG w hw
    · rw [if_neg hs] at h; simp at h
  obtain ⟨u, hu, t, -, ht⟩ := hcon _ (complete_knownN hn false)
  have hnone := simultaneous_lb_known hD' hC' (complete_knownN hn false)
    (t := n - 2) (by omega) 0 (by simp [complete]; omega)
  simp only [D', if_pos (show n ≤ n - 2 + 2 by omega)] at hnone
  have := hall _ (complete_knownN hn false) 0 (by simp [complete]; omega)
  simp [hnone] at this

end CoordCons
