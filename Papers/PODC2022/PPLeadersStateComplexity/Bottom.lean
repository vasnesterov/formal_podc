import Papers.PODC2022.PPLeadersStateComplexity.BottomAux

/-!
# Bottom configurations (Section 6 of Leroux)

Theorem 6.1: from any configuration one reaches, by short words, a configuration `α` whose
restriction `α|_Q` to some set `Q` is bottom with a small component, followed by a short word `w`
that keeps `α|_Q` and strictly increases every other place.

We prove it relative to a set `U` of *active* places (the net and the initial configuration
vanish outside `U`, and `d = |U|`); the paper's statement is the case `U = P`
(`theorem_6_1`). The relative form is what Section 8 uses (`U = P \ {i}`).
-/

namespace Podc.PPLeadersStateComplexity

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P]


/-! ### The two steps of the construction in the proof of Lemma 6.2 -/

/-- One step of the construction in the proof of Lemma 6.2. The places of `D = {p_1, …, p_n}`
hold at least `λ_n = s θ^(d-n) ‖T‖ + θ` agents (with `θ = λ_{n+1}`). Either some place
`p_{n+1} ∈ R_n = (U \ Q) \ D` reaches `θ` by a short word, keeping `θ` agents on `D` (third case
of the paper), or a short word reaches a configuration `ρ'` such that `ρ'|_{Q ∪ R_n}` is bottom
with a small component (second case). The paper's claim that the `T|_{Q'}`-reachability set of
`ρ_n|_{Q'}` is small is justified here via a shortest-path argument and Lemma 5.2. -/
theorem lemma_6_2_step {T : Finset (Trans P)} {U Q : Finset P} (hT : NetOn U T) (hQU : Q ⊆ U)
    {ρ ρn : Config P} (hbot : IsBottom (resNet Q T) (res Q ρ)) (hρn : Reach T ρ ρn)
    {D : Finset P} (hD : D ⊆ U \ Q) (hDlt : D.card < (U \ Q).card) {θ : ℕ}
    (hρD : ∀ p ∈ D, (component (resNet Q T) (res Q ρ)).ncard * θ ^ ((U \ Q).card - D.card) *
      netNorm T + θ ≤ ρn p) :
    (∃ w ρ' p, IsWord T w ∧ Run w ρn ρ' ∧
        w.length ≤ (component (resNet Q T) (res Q ρ)).ncard * θ ^ ((U \ Q).card - D.card) ∧
        p ∈ U \ Q ∧ p ∉ D ∧ θ ≤ ρ' p ∧ ∀ q ∈ D, θ ≤ ρ' q) ∨
    (∃ w ρ' Q', IsWord T w ∧ Run w ρn ρ' ∧
        w.length ≤ (component (resNet Q T) (res Q ρ)).ncard * θ ^ ((U \ Q).card - D.card) ∧
        Q ⊂ Q' ∧ Q' ⊆ U ∧ IsBottom (resNet Q' T) (res Q' ρ') ∧
        (component (resNet Q' T) (res Q' ρ')).ncard ≤
          (component (resNet Q T) (res Q ρ)).ncard * θ ^ ((U \ Q).card - D.card)) := by
  set C := component (resNet Q T) (res Q ρ) with hCdef
  set N := netNorm T with hN
  set R := (U \ Q) \ D with hRdef
  set B := C.ncard * θ ^ ((U \ Q).card - D.card) with hB
  have hRcard : R.card = (U \ Q).card - D.card := Finset.card_sdiff_of_subset hD
  set Q' := Q ∪ R with hQ'
  obtain ⟨hAfin, hAcard⟩ := ncard_box_le hbot.1 Q R θ
  rw [hRcard] at hAcard
  set A := {x : Config P | (∀ p, p ∉ Q → p ∉ R → x p = 0) ∧ res Q x ∈ C ∧ ∀ p ∈ R, x p < θ}
  have hQQ' : Q ⊆ Q' := Finset.subset_union_left
  have hreach : ∀ x, Reach (resNet Q' T) (res Q' ρn) x →
      (∀ p, p ∉ Q → p ∉ R → x p = 0) ∧ res Q x ∈ C := by
    intro x hx
    constructor
    · intro p hpQ hpR
      have hp : p ∉ Q' := by simp [hQ', hpQ, hpR]
      exact Reach.eq_zero_of_netOn (netOn_resNet Q' T) hx
        (fun q hq => res_apply_of_not_mem hq _) p hp
    · have h1 := hx.res Q
      rw [resNet_resNet_of_subset hQQ', res_res, Finset.inter_eq_left.2 hQQ'] at h1
      have h2 : Reach (resNet Q T) (res Q ρ) (res Q x) := (hρn.res Q).trans h1
      exact ⟨h2, hbot.2 _ h2⟩
  have hDQ' : ∀ p ∈ U, p ∉ Q' → p ∈ D := by
    intro p hpU hp
    simp only [hQ', hRdef, Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not] at hp
    exact hp.2 ⟨hpU, hp.1⟩
  have hRsub : R ⊆ U \ Q := Finset.sdiff_subset
  have hlift : ∀ (w' : List (Trans P)), w'.length ≤ B → ∀ p ∈ U, p ∉ Q' →
      w'.length * N ≤ ρn p := by
    intro w' hl p hpU hp
    have h1 := hρD p (hDQ' p hpU hp)
    have h2 : w'.length * N ≤ B * N := Nat.mul_le_mul_right _ hl
    omega
  by_cases hgood : ∃ γ, Reach (resNet Q' T) (res Q' ρn) γ ∧ ∃ p ∈ R, θ ≤ γ p
  · left
    obtain ⟨w', γ, hw', hr', ⟨p, hpR, hpθ⟩, hl⟩ := exists_short_path hAfin
      (fun x hx hng => by
        obtain ⟨h1, h2⟩ := hreach x hx
        push Not at hng
        exact ⟨h1, h2, hng⟩) hgood
    have hl' : w'.length ≤ B := hl.trans hAcard
    obtain ⟨w, ρ', hw, hlen, hr, hres, hge⟩ := lift_of_netOn hT hw' hr' (hlift w' hl')
    have hpR' := hpR
    simp only [hRdef, Finset.mem_sdiff] at hpR'
    refine ⟨w, ρ', p, hw, hr, hlen ▸ hl', Finset.mem_sdiff.2 hpR'.1, hpR'.2, ?_, fun q hq => ?_⟩
    · have := congrFun hres p
      rw [res_apply_of_mem (Finset.mem_union_right _ hpR)] at this
      omega
    · have hqU : q ∈ U := (Finset.mem_sdiff.1 (hD hq)).1
      have hqQ' : q ∉ Q' := by
        simp only [hQ', hRdef, Finset.mem_union, Finset.mem_sdiff, not_or, not_and, not_not]
        exact ⟨(Finset.mem_sdiff.1 (hD hq)).2, fun _ => hq⟩
      have h1 := hge q hqU hqQ'
      have h2 := hρD q hq
      have h3 : w'.length * netNorm T ≤ B * N := Nat.mul_le_mul_right _ hl'
      omega
  · right
    push Not at hgood
    set S := {x | Reach (resNet Q' T) (res Q' ρn) x} with hS
    have hSA : S ⊆ A := fun x hx => ⟨(hreach x hx).1, (hreach x hx).2, hgood x hx⟩
    have hSfin : S.Finite := hAfin.subset hSA
    have hScard : S.ncard ≤ B := (Set.ncard_le_ncard hSA hAfin).trans hAcard
    obtain ⟨β', hβ', hbot'⟩ := exists_reach_bottom hSfin
    obtain ⟨w', β'', hw', hr', hβ'', hl⟩ := exists_short_path (Good := (· = β')) hSfin
      (fun x hx _ => hx) ⟨β', hβ', rfl⟩
    subst hβ''
    have hl' : w'.length ≤ B := hl.trans hScard
    obtain ⟨w, ρ', hw, hlen, hr, hres, -⟩ := lift_of_netOn hT hw' hr' (hlift w' hl')
    have hcompS : component (resNet Q' T) β'' ⊆ S := fun x hx => hβ'.trans hx.1
    obtain ⟨p, hp⟩ : R.Nonempty := Finset.card_pos.1 (by omega)
    refine ⟨w, ρ', Q', hw, hr, hlen ▸ hl', ?_, ?_, ?_, ?_⟩
    · rw [Finset.ssubset_iff_of_subset hQQ']
      exact ⟨p, Finset.mem_union_right _ hp, (Finset.mem_sdiff.1 (hRsub hp)).2⟩
    · exact Finset.union_subset hQU (hRsub.trans Finset.sdiff_subset)
    · rw [hres]; exact ⟨hSfin.subset hcompS, hbot'⟩
    · rw [hres]; exact (Set.ncard_le_ncard hcompS hSfin).trans hScard

/-- The last step (`n = d`) of the construction in the proof of Lemma 6.2: once every place of
`U \ Q` holds more than `s ‖T‖∞ + ‖ρ‖∞` agents, a word of length `≤ s` brings the `Q`-part back
to `ρ|_Q` while all places of `U \ Q` stay above their value in `ρ`. -/
theorem lemma_6_2_last {T : Finset (Trans P)} {U Q : Finset P} (hT : NetOn U T)
    {ρ ρn : Config P} (hbot : IsBottom (resNet Q T) (res Q ρ)) (hρn : Reach T ρ ρn)
    (hρD : ∀ p ∈ U \ Q,
      (component (resNet Q T) (res Q ρ)).ncard * netNorm T + supNorm ρ + 1 ≤ ρn p) :
    ∃ w ρ', IsWord T w ∧ Run w ρn ρ' ∧ w.length ≤ (component (resNet Q T) (res Q ρ)).ncard ∧
      res Q ρ' = res Q ρ ∧ ∀ p ∈ U \ Q, ρ p < ρ' p := by
  set C := component (resNet Q T) (res Q ρ)
  have hRQ := hρn.res Q
  obtain ⟨w', γ, hw', hr', hγ, hl⟩ := exists_short_path (Good := (· = res Q ρ)) (A := C) hbot.1
    (fun x hx _ => ⟨hRQ.trans hx, hbot.2 _ (hRQ.trans hx)⟩) ⟨res Q ρ, hbot.2 _ hRQ, rfl⟩
  subst hγ
  have h4 := Nat.mul_le_mul_right (netNorm T) hl
  obtain ⟨w, ρ', hw, hlen, hr, hres, hge⟩ := lift_of_netOn hT hw' hr' (fun p hpU hp => by
    have := hρD p (Finset.mem_sdiff.2 ⟨hpU, hp⟩); omega)
  refine ⟨w, ρ', hw, hr, hlen ▸ hl, hres, fun p hp => ?_⟩
  obtain ⟨hpU, hpQ⟩ := Finset.mem_sdiff.1 hp
  have h1 := hge p hpU hpQ
  have h2 := hρD p hp
  have h3 := le_supNorm ρ p
  omega

/-- **Lemma 6.2** (relative to the active places `U`, `d = |U \ Q|`). -/
theorem lemma_6_2 {T : Finset (Trans P)} {U Q : Finset P} (hT : NetOn U T) (hQU : Q ⊆ U)
    {ρ : Config P} (hρ : ∀ p ∉ U, ρ p = 0) (hbot : IsBottom (resNet Q T) (res Q ρ)) :
    let s := (component (resNet Q T) (res Q ρ)).ncard
    let d := (U \ Q).card
    ∃ σ : List (Trans P), ∃ ρ' : Config P, IsWord T σ ∧ Run σ ρ ρ' ∧
      σ.length ≤ (1 + d * (1 + s * netNorm T + supNorm ρ) ^ (d ^ d)) * s ∧
      ((res Q ρ' = res Q ρ ∧ ∀ p ∈ U \ Q, ρ p < ρ' p) ∨
        (∃ Q' : Finset P, Q ⊂ Q' ∧ Q' ⊆ U ∧ IsBottom (resNet Q' T) (res Q' ρ') ∧
          (component (resNet Q' T) (res Q' ρ')).ncard ≤
            (1 + d * (1 + s * netNorm T + supNorm ρ) ^ (d ^ d)) * s)) := by
  have _ := hρ  -- `hρ` is not needed for Lemma 6.2 (kept for the interface)
  intro s d
  set N := netNorm T with hN
  set Λ := 1 + s * N + supNorm ρ with hΛ
  have hΛ' : s * N + 1 ≤ Λ := by omega
  have hΛ1 : 1 ≤ Λ := by omega
  set L := mu62 s N Λ (d - 1) ^ d with hL
  have hLΛ : L ≤ Λ ^ (d ^ d) := mu62_pow_le hΛ' d
  have hθL : ∀ k, k + 1 ≤ d → mu62 s N Λ k ^ (k + 1) ≤ L := by
    intro k hk
    calc mu62 s N Λ k ^ (k + 1) ≤ mu62 s N Λ (d - 1) ^ (k + 1) :=
          Nat.pow_le_pow_left (mu62_mono s N Λ (by omega)) _
      _ ≤ L := Nat.pow_le_pow_right (one_le_mu62 hΛ1 _) hk
  have hfin : ∀ x, x ≤ d * (L * s) → x ≤ (1 + d * Λ ^ (d ^ d)) * s := by
    intro x hx
    calc x ≤ d * (L * s) := hx
      _ ≤ d * (Λ ^ (d ^ d) * s) := by gcongr
      _ ≤ s + d * (Λ ^ (d ^ d) * s) := Nat.le_add_left _ _
      _ = (1 + d * Λ ^ (d ^ d)) * s := by ring
  suffices H : ∀ m n (τ : List (Trans P)) (ρn : Config P) (D : Finset P), n + m = d →
      IsWord T τ → Run τ ρ ρn → D ⊆ U \ Q → D.card = n → τ.length ≤ n * (L * s) →
      (∀ p ∈ D, mu62 s N Λ (d - n) ≤ ρn p) →
      ∃ σ : List (Trans P), ∃ ρ' : Config P, IsWord T σ ∧ Run σ ρ ρ' ∧
        σ.length ≤ (1 + d * Λ ^ (d ^ d)) * s ∧
        ((res Q ρ' = res Q ρ ∧ ∀ p ∈ U \ Q, ρ p < ρ' p) ∨
          (∃ Q' : Finset P, Q ⊂ Q' ∧ Q' ⊆ U ∧ IsBottom (resNet Q' T) (res Q' ρ') ∧
            (component (resNet Q' T) (res Q' ρ')).ncard ≤ (1 + d * Λ ^ (d ^ d)) * s)) by
    exact H d 0 [] ρ ∅ (zero_add d) (fun _ h => by simp at h) rfl (Finset.empty_subset _) rfl
      (by simp) (by simp)
  intro m
  induction m with
  | zero =>
    intro n τ ρn D hn hτ hr hD hDc hl hge
    have hDeq : D = U \ Q := Finset.eq_of_subset_of_card_le hD (by
      show d ≤ D.card
      omega)
    obtain ⟨w, ρ', hw, hrw, hlw, hres, hlt⟩ := lemma_6_2_last hT hbot ⟨τ, hτ, hr⟩
      (fun p hp => by
        have h := hge p (hDeq ▸ hp)
        have e : d - n = 0 := by omega
        rw [e, mu62_zero] at h
        show s * N + supNorm ρ + 1 ≤ ρn p
        omega)
    refine ⟨τ ++ w, ρ', hτ.append hw, hr.append hrw, ?_, Or.inl ⟨hres, hlt⟩⟩
    rw [List.length_append]
    have h1 : τ.length ≤ d * (Λ ^ (d ^ d) * s) :=
      hl.trans (by rw [show n = d by omega]; gcongr)
    have h2 : w.length ≤ s := hlw
    calc τ.length + w.length ≤ d * (Λ ^ (d ^ d) * s) + s := by omega
      _ = (1 + d * Λ ^ (d ^ d)) * s := by ring
  | succ m ih =>
    intro n τ ρn D hn hτ hr hD hDc hl hge
    subst hDc
    obtain ⟨k, hk⟩ : ∃ k, d - D.card = k + 1 := ⟨d - D.card - 1, by omega⟩
    have hkd : k + 1 ≤ d := by omega
    have hBL : s * mu62 s N Λ k ^ (k + 1) ≤ L * s := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ (hθL k hkd)
    have hlen : ∀ w : List (Trans P), w.length ≤ s * mu62 s N Λ k ^ (d - D.card) →
        (τ ++ w).length ≤ (D.card + 1) * (L * s) := by
      intro w hw
      rw [hk] at hw
      rw [List.length_append]
      calc τ.length + w.length ≤ D.card * (L * s) + L * s := by omega
        _ = (D.card + 1) * (L * s) := by ring
    rcases lemma_6_2_step (θ := mu62 s N Λ k) hT hQU hbot ⟨τ, hτ, hr⟩ hD
        (by show D.card < d; omega)
        (fun p hp => by
          have h := hge p hp
          rw [hk] at h
          show s * mu62 s N Λ k ^ (d - D.card) * N + mu62 s N Λ k ≤ ρn p
          rw [hk]; exact h) with
      ⟨w, ρ', p, hw, hrw, hlw, hpUQ, hpD, hpθ, hDθ⟩ |
        ⟨w, ρ', Q', hw, hrw, hlw, hQQ', hQ'U, hbot', hs'⟩
    · refine ih (D.card + 1) (τ ++ w) ρ' (insert p D) (by omega) (hτ.append hw) (hr.append hrw)
        (Finset.insert_subset hpUQ hD) (Finset.card_insert_of_notMem hpD) (hlen w hlw) ?_
      have e : d - (D.card + 1) = k := by omega
      rw [e]
      intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      exacts [hpθ, hDθ q hq]
    · refine ⟨τ ++ w, ρ', hτ.append hw, hr.append hrw, hfin _ ?_,
        Or.inr ⟨Q', hQQ', hQ'U, hbot', hfin _ ?_⟩⟩
      · exact (hlen w hlw).trans (Nat.mul_le_mul_right _ (by omega))
      · have : (component (resNet Q' T) (res Q' ρ')).ncard ≤ s * mu62 s N Λ k ^ (d - D.card) :=
          hs'
        rw [hk] at this
        calc _ ≤ L * s := this.trans hBL
          _ = 1 * (L * s) := (one_mul _).symm
          _ ≤ d * (L * s) := Nat.mul_le_mul_right _ (by omega)

/-- **Theorem 6.1** relative to the active places `U` (`d = |U|`). -/
theorem theorem_6_1_rel {T : Finset (Trans P)} {U : Finset P} (hT : NetOn U T) {ρ : Config P}
    (hρ : ∀ p ∉ U, ρ p = 0) :
    let d := U.card
    let b := (4 + 4 * netNorm T + 2 * supNorm ρ) ^ (d ^ d * (1 + (2 + d ^ d) ^ (d + 1)))
    ∃ σ w : List (Trans P), ∃ Q : Finset P, ∃ α β : Config P,
      Q ⊆ U ∧ IsWord T σ ∧ IsWord T w ∧ Run σ ρ α ∧ Run w α β ∧ res Q α = res Q β ∧
      (∀ p ∈ U \ Q, α p < β p) ∧ IsBottom (resNet Q T) (res Q α) ∧
      (component (resNet Q T) (res Q α)).ncard ≤ b ∧
      σ.length ≤ b ∧ w.length ≤ b ∧ d * supNorm α ≤ b ∧ d * supNorm β ≤ b := by
  intro d b
  set N := netNorm T with hN
  set R := supNorm ρ with hR
  set K := d ^ d with hK
  set h := 2 + K with hh
  set a := (1 + d) * (2 + 2 * N + R) ^ K with ha
  have hK1 : 1 ≤ K := one_le_pow_self' d
  have hbase : 2 + 2 * N + R ≤ (2 + 2 * N + R) ^ K := Nat.le_self_pow (by omega) _
  have hNa : (1 + d) * (1 + N) ≤ a := Nat.mul_le_mul_left _ (by omega)
  have ha1 : 1 ≤ a := le_trans (Nat.one_le_iff_ne_zero.2 (by positivity)) hNa
  have hNa' : 1 + N ≤ a := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hNa
  have hRa : R ≤ a := le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega) : _ ≤ a)
  have hab : a ≤ (4 + 4 * N + 2 * R) ^ K :=
    calc a ≤ 2 ^ K * (2 + 2 * N + R) ^ K :=
          Nat.mul_le_mul_right _ (one_add_le_two_pow_pow_self d)
      _ = (2 * (2 + 2 * N + R)) ^ K := (mul_pow _ _ _).symm
      _ = (4 + 4 * N + 2 * R) ^ K := by ring_nf
  have hh1 : ∀ i, 1 ≤ h ^ i := fun i => Nat.one_le_pow _ _ (by omega)
  have hhsucc : ∀ i, h ^ i * (K + 1) + h ^ i ≤ h ^ (i + 1) := fun i => by
    rw [pow_succ, hh]; ring_nf; omega
  have hX1 : ∀ j, 1 ≤ a ^ (h ^ j) := fun j => Nat.one_le_pow _ _ ha1
  have hXmono : ∀ i j, i ≤ j → a ^ (h ^ i) ≤ a ^ (h ^ j) := fun i j hij =>
    Nat.pow_le_pow_right ha1 (Nat.pow_le_pow_right (by omega) hij)
  have hgrow : ∀ i, (1 + N) * a ^ (h ^ i) ≤ a ^ (h ^ (i + 1)) := fun i =>
    calc (1 + N) * a ^ (h ^ i) ≤ a * a ^ (h ^ i) := Nat.mul_le_mul_right _ hNa'
      _ = a ^ (1 + h ^ i) := by rw [pow_add, pow_one]
      _ ≤ a ^ (h ^ (i + 1)) := Nat.pow_le_pow_right ha1 (by
          have := hhsucc i; have := hh1 i
          have : h ^ i ≤ h ^ i * (K + 1) := Nat.le_mul_of_pos_right _ (by omega)
          omega)
  have hfinb : ∀ j ≤ d + 1, ∀ c ≤ (1 + d) * (1 + N), c * a ^ (h ^ j) ≤ b := by
    intro j hj c hc
    calc c * a ^ (h ^ j) ≤ a * a ^ (h ^ (d + 1)) := Nat.mul_le_mul (hc.trans hNa) (hXmono _ _ hj)
      _ = a ^ (1 + h ^ (d + 1)) := by ring
      _ ≤ ((4 + 4 * N + 2 * R) ^ K) ^ (1 + h ^ (d + 1)) := Nat.pow_le_pow_left hab _
      _ = b := by rw [← pow_mul]
  have h1dN : 1 ≤ (1 + d) * (1 + N) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hdN : d * (1 + N) ≤ (1 + d) * (1 + N) := Nat.mul_le_mul_right _ (by omega)
  have hstep : ∀ i (s r d' : ℕ), d' ≤ d → s ≤ a ^ (h ^ i) → r ≤ (1 + N) * a ^ (h ^ i) →
      (1 + d' * (1 + s * N + r) ^ (d' ^ d')) * s ≤ a ^ (h ^ (i + 1)) := by
    intro i s r d' hd' hs hr
    calc _ ≤ a * (a ^ (h ^ i)) ^ (K + 1) := arith61_step (R := R) hd' (hX1 i) hs hr
      _ = a ^ (1 + h ^ i * (K + 1)) := by rw [← pow_mul, pow_add, pow_one]
      _ ≤ a ^ (h ^ (i + 1)) := Nat.pow_le_pow_right ha1 (by
          have := hhsucc i; have := hh1 i; omega)
  suffices H : ∀ m i (τ : List (Trans P)) (ρi : Config P) (Qi : Finset P), i + m = d + 1 →
      Qi ⊆ U → i ≤ Qi.card → IsWord T τ → Run τ ρ ρi → τ.length ≤ i * a ^ (h ^ i) →
      (∀ p ∉ U, ρi p = 0) → IsBottom (resNet Qi T) (res Qi ρi) →
      (component (resNet Qi T) (res Qi ρi)).ncard ≤ a ^ (h ^ i) →
      supNorm ρi ≤ (1 + N) * a ^ (h ^ i) →
      ∃ σ w : List (Trans P), ∃ Q : Finset P, ∃ α β : Config P,
        Q ⊆ U ∧ IsWord T σ ∧ IsWord T w ∧ Run σ ρ α ∧ Run w α β ∧ res Q α = res Q β ∧
        (∀ p ∈ U \ Q, α p < β p) ∧ IsBottom (resNet Q T) (res Q α) ∧
        (component (resNet Q T) (res Q α)).ncard ≤ b ∧
        σ.length ≤ b ∧ w.length ≤ b ∧ d * supNorm α ≤ b ∧ d * supNorm β ≤ b by
    obtain ⟨hb0, hc0⟩ := isBottom_resNet_empty T ρ
    refine H (d + 1) 0 [] ρ ∅ (zero_add _) (Finset.empty_subset _) (Nat.zero_le _)
      (fun _ h => by simp at h) rfl (by simp) hρ hb0 (by rw [hc0]; exact hX1 0) ?_
    calc supNorm ρ = R := rfl
      _ ≤ a := hRa
      _ = a ^ (h ^ 0) := by simp
      _ ≤ (1 + N) * a ^ (h ^ 0) := Nat.le_mul_of_pos_left _ (by omega)
  have hdU : U.card = d := rfl
  intro m
  induction m with
  | zero =>
    intro i τ ρi Qi hi hQU hcard
    have := Finset.card_le_card hQU
    omega
  | succ m ih =>
    intro i τ ρi Qi hi hQU hcard hτ hr hlen hz hbot hs hnorm
    have hiU : i ≤ d := hcard.trans (hdU ▸ Finset.card_le_card hQU)
    obtain ⟨σ', ρ', hσ', hr', hl', hcase⟩ := lemma_6_2 hT hQU hz hbot
    have hd' : (U \ Qi).card ≤ d := hdU ▸ Finset.card_le_card Finset.sdiff_subset
    have hB := hstep i _ _ _ hd' hs hnorm
    have hl'' : σ'.length ≤ a ^ (h ^ (i + 1)) := hl'.trans hB
    have hnorm' : supNorm ρ' ≤ (1 + N) * a ^ (h ^ (i + 1)) := by
      rw [supNorm_le_iff]
      intro p
      have h1 : ρ' p ≤ ρi p + σ'.length * N := hr'.le_add hσ'.supNorm_le p
      have h2 := le_supNorm ρi p
      have h3 : σ'.length * N ≤ N * a ^ (h ^ (i + 1)) := by
        rw [mul_comm N]; exact Nat.mul_le_mul_right _ hl''
      have h4 := hgrow i
      have h5 : (1 + N) * a ^ (h ^ (i + 1)) = a ^ (h ^ (i + 1)) + N * a ^ (h ^ (i + 1)) := by
        ring
      omega
    rcases hcase with ⟨heq, hlt⟩ | ⟨Q', hQQ', hQ'U, hbot', hs'⟩
    · refine ⟨τ, σ', Qi, ρi, ρ', hQU, hτ, hσ', hr, hr', heq.symm, hlt, hbot, ?_, ?_, ?_, ?_, ?_⟩
      · calc _ ≤ 1 * a ^ (h ^ i) := by rw [one_mul]; exact hs
          _ ≤ b := hfinb i (by omega) 1 h1dN
      · exact hlen.trans (hfinb i (by omega) i (by nlinarith))
      · calc _ ≤ 1 * a ^ (h ^ (i + 1)) := by rw [one_mul]; exact hl''
          _ ≤ b := hfinb (i + 1) (by omega) 1 h1dN
      · calc d * supNorm ρi ≤ d * ((1 + N) * a ^ (h ^ i)) := Nat.mul_le_mul_left _ hnorm
          _ = d * (1 + N) * a ^ (h ^ i) := by ring
          _ ≤ b := hfinb i (by omega) _ hdN
      · calc d * supNorm ρ' ≤ d * ((1 + N) * a ^ (h ^ (i + 1))) := Nat.mul_le_mul_left _ hnorm'
          _ = d * (1 + N) * a ^ (h ^ (i + 1)) := by ring
          _ ≤ b := hfinb (i + 1) (by omega) _ hdN
    · refine ih (i + 1) (τ ++ σ') ρ' Q' (by omega) hQ'U
        (by have := Finset.card_lt_card hQQ'; omega) (hτ.append hσ') (hr.append hr') ?_
        (Reach.eq_zero_of_netOn hT ⟨σ', hσ', hr'⟩ hz) hbot' (hs'.trans hB) hnorm'
      rw [List.length_append]
      have h1 : i * a ^ (h ^ i) ≤ i * a ^ (h ^ (i + 1)) :=
        Nat.mul_le_mul_left _ (hXmono _ _ (by omega))
      calc τ.length + σ'.length ≤ i * a ^ (h ^ (i + 1)) + a ^ (h ^ (i + 1)) := by omega
        _ = (i + 1) * a ^ (h ^ (i + 1)) := by ring

/-- **Theorem 6.1.** Let `T` be a `P`-Petri net, `ρ` a configuration, `d = |P|` and
`b = (4 + 4‖T‖∞ + 2‖ρ‖∞)^(d^d (1 + (2 + d^d)^(d+1)))`. There are words `σ, w ∈ T*`, a set of
places `Q` and configurations `α, β` with `ρ →σ α →w β`, `α|_Q = β|_Q`, `α(p) < β(p)` for
`p ∉ Q`, `α|_Q` is `T|_Q`-bottom with a component of at most `b` elements, and
`|σ|, |w|, d‖α‖∞, d‖β‖∞ ≤ b`. -/
theorem theorem_6_1 (T : Finset (Trans P)) (ρ : Config P) :
    let d := Fintype.card P
    let b := (4 + 4 * netNorm T + 2 * supNorm ρ) ^ (d ^ d * (1 + (2 + d ^ d) ^ (d + 1)))
    ∃ σ w : List (Trans P), ∃ Q : Finset P, ∃ α β : Config P,
      IsWord T σ ∧ IsWord T w ∧ Run σ ρ α ∧ Run w α β ∧ res Q α = res Q β ∧
      (∀ p ∉ Q, α p < β p) ∧ IsBottom (resNet Q T) (res Q α) ∧
      (component (resNet Q T) (res Q α)).ncard ≤ b ∧
      σ.length ≤ b ∧ w.length ≤ b ∧ d * supNorm α ≤ b ∧ d * supNorm β ≤ b := by
  obtain ⟨σ, w, Q, α, β, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    theorem_6_1_rel (U := Finset.univ) (T := T) (ρ := ρ)
      (fun _ _ p hp => absurd (Finset.mem_univ p) hp) (fun p hp => absurd (Finset.mem_univ p) hp)
  exact ⟨σ, w, Q, α, β, h1, h2, h3, h4, h5, fun p hp => h6 p (by simp [hp]), h7, h8, h9, h10,
    h11, h12⟩

end Podc.PPLeadersStateComplexity
