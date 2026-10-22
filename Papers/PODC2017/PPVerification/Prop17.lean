import Papers.PODC2017.PPVerification.Threshold

/-!
# Proposition 17: `P_thr` satisfies StrongConsensus

* `flowEq_val` (Proposition 23): the flow equations preserve `val`.
* `exists_leader_of_potReachVia`: the leaders form a `U`-trap for every `U`, so a configuration
  potentially reachable from one with a leader has a leader.
* `consensus_of_terminal` (Proposition 24): a terminal configuration with a leader and at least
  two agents is a consensus with output `val(C) < c`.
* `proposition_17`, `proposition_17_Pthr`.
-/

namespace Podc.PPVerification.Threshold

open Cslib.PopulationProtocol Cslib.TransitionSystem

variable {v : ℤ} (c : ℤ)

/-- Every transition of `P_thr` preserves the total value. -/
theorem val_post_eq_pre {t : Transition (St v)} (ht : t ∈ trans c) :
    (t.post.map valS).sum = (t.pre.map valS).sum := by
  rcases ht with ⟨-, h⟩ | ⟨-, h1, h2⟩
  · rw [h]
    simp only [Transition.post, Transition.pre, mainT, fV, gV, valS, Multiset.insert_eq_cons,
      Multiset.map_cons, Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton]
    ring
  · simp [Transition.post, Transition.pre, h1, h2]

/-- **Proposition 23.** If `(C, C', x)` satisfies the flow equations (with `x` supported on the
transitions of `P_thr`), then `val(C) = val(C')`. -/
theorem flowEq_val {C C' : Multiset (St v)} {x : Transition (St v) → ℕ}
    (hx : ∀ t, x t ≠ 0 → t ∈ trans c) (h : FlowEq C C' x) : val C' = val C := by
  unfold val
  rw [sum_map_eq_sum_count, sum_map_eq_sum_count]
  refine h.weight_eq _ fun t ht => ?_
  rw [Transition.sum_delta_mul, val_post_eq_pre c (hx t ht), sub_self]

/-- The leaders. -/
def leaders : Finset (St v) := Finset.univ.filter fun s => s.1 = true

/-- Leader indicator. -/
def wLead (s : St v) : ℤ := if s.1 = true then 1 else 0

/-- The leaders form a `U`-trap for every set `U` of transitions of `P_thr`. -/
theorem leaders_trap {U : Set (Transition (St v))} (hU : U ⊆ trans c) :
    IsUTrap U (leaders (v := v)) := by
  intro t htU ho
  obtain ⟨s, hs, hsL⟩ := ho
  rcases hU htU with ⟨hp, h⟩ | ⟨hp, h1, h2⟩
  · rw [h]
    exact ⟨(true, fV t.p.2.1 t.q.2.1, decide ((fV t.p.2.1 t.q.2.1 : ℤ) < c)),
      by simp [Transition.post, mainT], by simp [leaders]⟩
  · refine ⟨s, ?_, hsL⟩
    simp only [Transition.pre, Transition.post, h1, h2] at hs ⊢
    exact hs

theorem exists_leader_iff {C : Multiset (St v)} :
    (∃ s ∈ C, s.1 = true) ↔ 0 < (C.map wLead).sum := by
  constructor
  · rintro ⟨s, hs, hl⟩
    rw [← Multiset.cons_erase hs, Multiset.map_cons, Multiset.sum_cons]
    have : 0 ≤ ((C.erase s).map wLead).sum :=
      Multiset.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx; unfold wLead; split_ifs <;> norm_num
    simp [wLead, hl]; omega
  · intro h
    by_contra hcon
    push Not at hcon
    have : (C.map wLead).sum = 0 :=
      Multiset.sum_eq_zero fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx; simp [wLead, hcon y hy]
    omega

/-- A configuration potentially reachable from a configuration with a leader has a leader
(the paper's "the set of leaders forms a `U`-trap for every `U`", completed by the flow
equations when no transition of `U` moves an agent into the leaders). -/
theorem exists_leader_of_potReachVia {C C' : Multiset (St v)} {x : Transition (St v) → ℕ}
    (h : PotReachVia (trans c) C C' x) (hC : ∃ s ∈ C, s.1 = true) : ∃ s ∈ C', s.1 = true := by
  obtain ⟨hsupp, hflow, htrap, -⟩ := h
  have hU : {t | x t ≠ 0} ⊆ trans c := fun t ht => hsupp t ht
  by_cases hin : ∃ t, x t ≠ 0 ∧ t.Into (leaders (v := v))
  · obtain ⟨t, ht, hi⟩ := hin
    by_contra hcon
    push Not at hcon
    refine htrap _ (leaders_trap c hU) ?_ t ht hi
    by_contra hne
    obtain ⟨s, hs, hsL⟩ := mass_pos_iff.1 (Nat.pos_of_ne_zero hne)
    exact hcon s hs (by simpa [leaders] using hsL)
  · push Not at hin
    rw [exists_leader_iff] at hC ⊢
    have heq : (C'.map wLead).sum = (C.map wLead).sum := by
      rw [sum_map_eq_sum_count, sum_map_eq_sum_count]
      refine hflow.weight_eq _ fun t ht => ?_
      have hni := hin t ht
      have hno : ¬ t.OutOf (leaders (v := v)) := fun ho => hni (leaders_trap c hU t ht ho)
      have hz : ∀ M : Multiset (St v), (∀ s ∈ M, s ∉ leaders (v := v)) → (M.map wLead).sum = 0 :=
        fun M hM => Multiset.sum_eq_zero fun y hy => by
          obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hy
          have := hM s hs
          simp only [leaders, Finset.mem_filter, Finset.mem_univ, true_and] at this
          simp [wLead, this]
      rw [Transition.sum_delta_mul, hz _ fun s hs hL => hni ⟨s, hs, hL⟩,
        hz _ fun s hs hL => hno ⟨s, hs, hL⟩, sub_self]
    omega

/-- The value of a silent leader interaction: if `clamp(m + n) = m` and the leader `(1, m, o)` has
opinion `o = (m < c)` with `-v < c < v`, then `n ≤ 0` when `o` and `n ≥ 0` otherwise. -/
theorem sign_of_clamp_eq {m n : ℤ} (hm : -v ≤ m ∧ m ≤ v) (hcl : clampV v (m + n) = m)
    (hc : -v < c ∧ c < v) : (m < c → n ≤ 0) ∧ (c ≤ m → 0 ≤ n) := by
  unfold clampV at hcl
  constructor <;> intro h <;> omega

/-- **Proposition 24.** A terminal configuration `C` of `P_thr` with a leader and at least two
agents is a consensus configuration with output `val(C) < c`. In particular, two such
configurations with equal values have the same output. -/
theorem consensus_of_terminal (hc : |c| + 1 ≤ v) {C : Multiset (St v)}
    (hterm : Terminal (trans c) C) {p : St v} (hp : p ∈ C) (hpl : p.1 = true)
    (hcard : 2 ≤ Multiset.card C) : IsConsensus (fun s : St v => s.2.2) C (decide (val C < c)) := by
  have hcv : -v < c ∧ c < v := by
    have h1 := abs_le.1 (le_refl |c|); constructor <;> omega
  have hC : C = p ::ₘ C.erase p := (Multiset.cons_erase hp).symm
  -- every other agent interacts silently with the leader
  have hall : ∀ q ∈ C.erase p, q.1 = false ∧ fV p.2.1 q.2.1 = p.2.1 ∧
      decide ((fV p.2.1 q.2.1 : ℤ) < c) = p.2.2 ∧ decide ((fV p.2.1 q.2.1 : ℤ) < c) = q.2.2 := by
    intro q hq
    have hle : (mainT c p q).pre ≤ C := by
      rw [hC]
      simp only [Transition.pre, mainT, Multiset.insert_eq_cons]
      exact Multiset.cons_le_cons _ (Multiset.singleton_le.2 hq)
    have hs := mainT_silent c hpl
      (terminal_iff_forall_silent.1 hterm _ (mainT_mem c hpl) hle)
    exact ⟨hs.1, hs.2.1, hs.2.2.2.1, hs.2.2.2.2⟩
  obtain ⟨q₀, hq₀⟩ : ∃ q, q ∈ C.erase p := by
    apply Multiset.card_pos_iff_exists_mem.1
    have := Multiset.card_erase_add_one hp; omega
  obtain ⟨pl, ⟨m, hm⟩, o⟩ := p
  simp only at hpl hall
  have hm' : -v ≤ m ∧ m ≤ v := hm
  have ho : decide (m < c) = o := by
    have := hall q₀ hq₀
    rw [← this.2.2.1, this.2.1]
  -- the signs of the other values
  have hsign : ∀ q ∈ C.erase (pl, ⟨m, hm⟩, o), (m < c → valS q ≤ 0) ∧ (c ≤ m → 0 ≤ valS q) := by
    intro q hq
    have h := (hall q hq).2.1
    have h' : clampV v (m + (q.2.1 : ℤ)) = m := congrArg Subtype.val h
    exact sign_of_clamp_eq c hm' h' hcv
  have hval : val C = m + val (C.erase (pl, ⟨m, hm⟩, o)) := by
    conv_lhs => rw [hC]
    simp [val, valS]
  have hout : decide (val C < c) = o := by
    rw [← ho]
    by_cases hmc : m < c
    · have h0 : 0 ≤ ((C.erase (pl, ⟨m, hm⟩, o)).map fun q => -valS q).sum :=
        Multiset.sum_nonneg fun y hy => by
          obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hy; have := (hsign q hq).1 hmc; omega
      rw [Multiset.sum_map_neg] at h0
      have : val (C.erase (pl, ⟨m, hm⟩, o)) ≤ 0 := by unfold val; omega
      simp only [decide_eq_decide]; omega
    · have : 0 ≤ val (C.erase (pl, ⟨m, hm⟩, o)) :=
        Multiset.sum_nonneg fun y hy => by
          obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hy; exact (hsign q hq).2 (by omega)
      simp only [decide_eq_decide]; omega
  intro s hs
  rw [hout]
  rw [hC, Multiset.mem_cons] at hs
  rcases hs with rfl | hs
  · rfl
  · have := hall s hs
    show s.2.2 = o
    rw [← this.2.2.2, this.2.2.1]

/-- Every terminal configuration potentially reachable from an initial configuration `I(X)` of
`P_thr` is a consensus with output `val(I(X)) < c`. -/
theorem consensus_of_potReach {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) (hc : |c| + 1 ≤ v)
    {X : Multiset Λ} (hX : 2 ≤ Multiset.card X) {C' : Multiset (St v)}
    (hpot : PotReach (trans c) ((protocol c a ha).init X) C') (hterm : Terminal (trans c) C') :
    IsConsensus (fun s : St v => s.2.2) C' (decide (val ((protocol c a ha).init X) < c)) := by
  obtain ⟨x, hx⟩ := hpot
  have hcard : 2 ≤ Multiset.card C' := by
    rw [hx.2.1.card_eq, MProtocol.card_init]; exact hX
  obtain ⟨i, hi⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card X)
  have hlead : ∃ s ∈ (protocol c a ha).init X, s.1 = true :=
    ⟨_, Multiset.mem_map_of_mem _ hi, rfl⟩
  obtain ⟨p, hp, hpl⟩ := exists_leader_of_potReachVia c hx hlead
  have := consensus_of_terminal c hc hterm hp hpl hcard
  rwa [flowEq_val c hx.1 hx.2.1] at this

/-- **Proposition 17.** `P_thr` satisfies StrongConsensus (for every value bound `v ≥ |c| + 1`).
More precisely, every terminal configuration potentially reachable from `I(X)` is a consensus
with output `val(I(X)) < c` (`consensus_of_potReach`). -/
theorem proposition_17 {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) (hc : |c| + 1 ≤ v) :
    StrongConsensus (protocol c a ha) := by
  rintro C ⟨X, hX, rfl⟩
  exact ⟨_, fun C' hpot hterm => consensus_of_potReach c a ha hc hX hpot hterm⟩

/-- **Proposition 17** for the paper's `P_thr` (bound `vmax`). -/
theorem proposition_17_Pthr {Λ : Type*} [Fintype Λ] (a : Λ → ℤ) : StrongConsensus (Pthr c a) :=
  proposition_17 c a _ (le_vmax c a).1

/-- The value of the initial configuration is `∑ᵢ a(i) · X(i)`. -/
theorem val_init {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) (X : Multiset Λ) :
    val ((protocol c a ha).init X) = (X.map a).sum := by
  simp [val, MProtocol.init, protocol, valS, Multiset.map_map, Function.comp_def]

end Podc.PPVerification.Threshold
