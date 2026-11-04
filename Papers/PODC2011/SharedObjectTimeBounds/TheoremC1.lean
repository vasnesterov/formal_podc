import Papers.PODC2011.SharedObjectTimeBounds.Setup

/-!
# Theorem C.1 of Chapter IV: strongly immediately non-self-commuting operations

`|OP| ≥ d + min {ε, u, d/3}` for every strongly immediately non-self-commuting operation type
(read-modify-write, dequeue, pop).

The runs of the thesis (`m = min {ε, u, d/3}`, operations `op'_1` of `p_i` and `op'_2` of `p_j`
with the arguments of the two non-commuting instances, after the prefix `ρ` executed by `p_i`):

* `R₁`: `p_j`'s clock is `m` behind; `p_i` invokes at `t`, `p_j` at `t + m` (same local time);
  delays `D1`: `i → *`, `j → i`, `k → j` take `d`; `j → k`, `k → i` take `d - m`.
* `R₁'`: as `R₁` without `p_j`'s operation (`alone_agree`: `p_i` cannot tell before `t + d + m`).
* `R₂`: `R₁` shifted by `-m` at `p_j`, chopped where the delay `j → i` became `d + m`, extended
  with delay `d - m` on `j → i` (`step2_agree`).
* `R₃`: `R₂` shifted by `+m` at `p_i`, chopped where `i → j` became `d - 2m`, extended with `d`
  (`step3_agree`).
* `R₃''`: as `R₃` without `p_i`'s operation (`alone_agree` with the roles of `i`, `j` swapped).

The `ρ`-phase of each run is a fresh admissible run (delays `d`), glued by history-obliviousness
(`restart`); this is the thesis's §IV.B.2.
-/

namespace Podc.SharedObjectTimeBounds

open Cslib.TimedMP

namespace C1

noncomputable section

variable {P I R M : Type*} [DecidableEq P]

/-- Delays: `d` during the `ρ`-phase (send time `< t`), then the pattern `D`. -/
def dl (d t : ℝ) (D : P → P → ℝ) : P → P → ℝ → ℝ := fun q r σ => if σ < t then d else D q r

/-- Delays of `R₁` (`j → k` and `k → i` take `d - m`, all others `d`). -/
def D1 (i j : P) (d m : ℝ) (q r : P) : ℝ :=
  if (q = j ∧ r ≠ i ∧ r ≠ j) ∨ (q ≠ i ∧ q ≠ j ∧ r = i) then d - m else d

/-- Delays of `R₂` (`i → j`, `j → i`, `k → i`, `k → j` take `d - m`, all others `d`). -/
def D2 (i j : P) (d m : ℝ) (q r : P) : ℝ :=
  if (q = i ∧ r = j) ∨ (q = j ∧ r = i) ∨ (q ≠ i ∧ q ≠ j ∧ (r = i ∨ r = j)) then d - m else d

/-- Offsets of `R₁`: the clock of `p_j` is `m` behind. -/
def off1 (j : P) (m : ℝ) (q : P) : ℝ := if q = j then -m else 0

/-- The scenario "`ρ`-phase at `p₀`, then `cont`", offsets `off`, delays `dl d t D`. -/
def scen (off : P → ℝ) (p₀ : P) (g : ℝ) (ρ : List (I × R)) (cont : List (Call P I))
    (d t : ℝ) (D : P → P → ℝ) : Scenario P I :=
  ⟨off, rhoCalls p₀ g ρ ++ cont, dl d t D⟩

theorem D1_eq (i j : P) (d m : ℝ) (q r : P) : D1 i j d m q r = d ∨ D1 i j d m q r = d - m := by
  unfold D1; split_ifs <;> simp

theorem dl_ge {d t γ : ℝ} {D : P → P → ℝ} (hd : γ ≤ d) (hD : ∀ q r, γ ≤ D q r) (q r : P)
    (σ : ℝ) : γ ≤ dl d t D q r σ := by
  unfold dl; split_ifs <;> simp_all

theorem dl_le {d t : ℝ} {D : P → P → ℝ} (hD : ∀ q r, D q r ≤ d) (q r : P) (σ : ℝ) :
    dl d t D q r σ ≤ d := by
  unfold dl; split_ifs <;> simp_all

theorem dl_of_ge {d t σ : ℝ} {D : P → P → ℝ} (h : t ≤ σ) (q r : P) : dl d t D q r σ = D q r := by
  unfold dl; simp [not_lt.mpr h]

theorem dl_of_lt {d t σ : ℝ} {D : P → P → ℝ} (h : σ < t) (q r : P) : dl d t D q r σ = d := by
  unfold dl; simp [h]

/-- Invocation events of `scen` in a window after the `ρ`-phase are those of `cont`. -/
theorem callEv_scen {off : P → ℝ} {p₀ : P} {g : ℝ} {ρ : List (I × R)} {cont : List (Call P I)}
    {d t : ℝ} {D : P → P → ℝ} {τ : ℝ} (hg : 0 < g) (hτ : ρ.length * g ≤ τ) (p : P)
    (e : ℝ × InEv P I M) (he : τ ≤ e.1 - off p) :
    e ∈ (scen off p₀ g ρ cont d t D).callEv p ↔
      ∃ c ∈ cont, c.p = p ∧ e = (c.t + off p, InEv.inv c.k c.a) := by
  simp only [Scenario.callEv, scen, List.mem_append, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc | hc, hp, rfl⟩
    · exfalso
      obtain ⟨-, hk, ht⟩ := mem_rhoCalls hc
      simp only [add_sub_cancel_right] at he
      have : ((c.k + 1 : ℕ) : ℝ) ≤ ρ.length := by exact_mod_cast hk
      push_cast at this
      rw [ht] at he; nlinarith
    · exact ⟨c, hc, hp, rfl⟩
  · rintro ⟨c, hc, hp, rfl⟩
    exact ⟨c, Or.inr hc, hp, rfl⟩

theorem off1_self (j : P) (m : ℝ) : off1 j m j = -m := by simp [off1]

theorem off1_ne {j q : P} (m : ℝ) (h : q ≠ j) : off1 j m q = 0 := by simp [off1, h]

/-- Step 1 (and Step 4, with `i` and `j` swapped): in `R₁` and `R₁'` the process `p_i` has the
same inputs before `t + d + m`, since the shortest path from `p_j` to `p_i` has length `d`. -/
theorem alone_agree [Finite P] (A : Algorithm P I R M) {i j p₀ : P} (hij : i ≠ j) {d m t g : ℝ}
    (hd : 0 < d) (hm0 : 0 ≤ m) (hm : 3 * m ≤ d) (ρ : List (I × R)) (a b : I)
    {H H' : P → Set (ℝ × InEv P I M)}
    (hH : IsRun A (scen (off1 j m) p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t + m, b⟩] d t
      (D1 i j d m)) H)
    (hH' : IsRun A (scen (off1 j m) p₀ g ρ [⟨i, ρ.length, t, a⟩] d t (D1 i j d m)) H') :
    ∀ e : ℝ × InEv P I M, e.1 < t + d + m → (e ∈ H i ↔ e ∈ H' i) := by
  set C : P → ℝ := fun p => if p = i then t + d + m else if p = j then t + m else t + d
  have hγ : (scen (off1 j m) p₀ g ρ [⟨i, ρ.length, t, a⟩] d t (D1 i j d m) :
      Scenario P I).MinDelay (d - m) := by
    refine ⟨by linarith, fun q r σ => dl_ge (by linarith) (fun q r => ?_) q r σ⟩
    rcases D1_eq i j d m q r with h | h <;> rw [h]; linarith
  have key := agree_of_cut A
    (scen (off1 j m) p₀ g ρ [⟨i, ρ.length, t, a⟩] d t (D1 i j d m))
    (scen (off1 j m) p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t + m, b⟩] d t (D1 i j d m))
    rfl hH' hH hγ C ?_ (fun _ _ _ _ => Or.inl rfl) ?_
  · intro e he
    have := key i e (by simp [scen, C, off1_ne m hij]; linarith)
    exact this.symm
  · intro p e he
    simp only [Scenario.callEv, scen, Set.mem_setOf_eq, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨c, hc, hp, rfl⟩
      exact ⟨c, by tauto, hp, rfl⟩
    · rintro ⟨c, hc, hp, rfl⟩
      refine ⟨c, ?_, hp, rfl⟩
      rcases hc with hc | hc | hc
      · exact Or.inl hc
      · exact Or.inr hc
      · exfalso; subst hc; subst hp
        simp only [scen, C, off1_self, if_neg (Ne.symm hij), if_true] at he
        linarith
  · have hC : ∀ q, t ≤ C q := fun q => by
      simp only [C]; split_ifs <;> linarith
    intro q r σ hσ
    simp only [scen]
    rw [dl_of_ge (le_trans (hC q) hσ)]
    simp only [C, D1] at hσ ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;> (try constructor) <;> linarith

/-- The `ρ`-only scenario with offsets `off` and all delays `d`. -/
def rho (off : P → ℝ) (p₀ : P) (g : ℝ) (ρ : List (I × R)) (d : ℝ) : Scenario P I :=
  ⟨off, rhoCalls p₀ g ρ, fun _ _ _ => d⟩

/-- A finished admissible run of the `ρ`-phase alone. -/
structure RhoRun (A : Algorithm P I R M) (d u ε : ℝ) (off : P → ℝ) (p₀ : P) (g : ℝ)
    (ρ : List (I × R)) (Tρ : ℝ) (Hr : P → Set (ℝ × InEv P I M)) : Prop where
  adm : (rho off p₀ g ρ d).Admissible d u ε
  run : IsRun A (rho off p₀ g ρ d) Hr
  wf : WF A (rho off p₀ g ρ d) Hr
  solo : SoloOps A (rho off p₀ g ρ d) Hr p₀ ρ
  fin : ∀ p, (∀ e ∈ Hr p, e.1 - off p < Tρ) ∧ ∀ o ∈ A.beh p (Hr p), o.1 - off p < Tρ

/-- Before clock time `t` a run of `scen` coincides with the run of its `ρ`-phase. -/
theorem agree_rho [Finite P] (A : Algorithm P I R M) {off : P → ℝ} {p₀ : P} {g : ℝ}
    {ρ : List (I × R)} {cont : List (Call P I)} {d t : ℝ} {D : P → P → ℝ} (hd : 0 < d)
    (hoff : ∀ p, off p ≤ 0) (hD : ∀ q r, -off r ≤ D q r) (hdo : ∀ r, -off r ≤ d)
    (hcont : ∀ c ∈ cont, t - off c.p ≤ c.t)
    {H Hr : P → Set (ℝ × InEv P I M)} (hH : IsRun A (scen off p₀ g ρ cont d t D) H)
    (hHr : IsRun A (rho off p₀ g ρ d) Hr) :
    ∀ p (e : ℝ × InEv P I M), e.1 < t → (e ∈ H p ↔ e ∈ Hr p) := by
  have hγ : (rho off p₀ g ρ d : Scenario P I).MinDelay d := ⟨hd, fun _ _ _ => le_rfl⟩
  have key := agree_of_cut A (rho off p₀ g ρ d) (scen off p₀ g ρ cont d t D) rfl hHr hH hγ
    (fun p => t - off p) ?_ ?_ ?_
  · intro p e he
    exact (key p e (by simp only [rho]; linarith)).symm
  · intro p e he
    simp only [Scenario.callEv, scen, rho, Set.mem_setOf_eq, List.mem_append]
    constructor
    · rintro ⟨c, hc, hp, rfl⟩; exact ⟨c, Or.inl hc, hp, rfl⟩
    · rintro ⟨c, hc | hc, hp, rfl⟩
      · exact ⟨c, hc, hp, rfl⟩
      · exfalso; have := hcont c hc; subst hp; simp only [rho] at he; linarith
  · intro q r σ hσ
    simp only [rho, scen, dl]
    split_ifs with h
    · exact Or.inl rfl
    · push_neg at h
      right; constructor <;> [linarith [hdo r]; linarith [hD q r]]
  · intro q r σ hσ
    simp only [rho, scen, dl]
    have := hoff q
    split_ifs with h
    · exfalso; linarith
    · constructor <;> [linarith [hdo r]; linarith [hD q r]]

theorem off1_le (j : P) {m : ℝ} (hm : 0 ≤ m) (q : P) : off1 j m q ≤ 0 := by
  unfold off1; split_ifs <;> linarith

theorem D1_ge (i j : P) (d m : ℝ) (hm0 : 0 ≤ m) (q r : P) : d - m ≤ D1 i j d m q r := by
  rcases D1_eq i j d m q r with h | h <;> rw [h] <;> linarith

theorem D1_le (i j : P) (d m : ℝ) (hm0 : 0 ≤ m) (q r : P) : D1 i j d m q r ≤ d := by
  rcases D1_eq i j d m q r with h | h <;> rw [h] <;> linarith

theorem D2_eq (i j : P) (d m : ℝ) (q r : P) : D2 i j d m q r = d ∨ D2 i j d m q r = d - m := by
  unfold D2; split_ifs <;> simp

theorem D2_ge (i j : P) (d m : ℝ) (hm0 : 0 ≤ m) (q r : P) : d - m ≤ D2 i j d m q r := by
  rcases D2_eq i j d m q r with h | h <;> rw [h] <;> linarith

theorem D2_le (i j : P) (d m : ℝ) (hm0 : 0 ≤ m) (q r : P) : D2 i j d m q r ≤ d := by
  rcases D2_eq i j d m q r with h | h <;> rw [h] <;> linarith

theorem off1_bounds (j : P) {m : ℝ} (hm : 0 ≤ m) (q : P) : -m ≤ off1 j m q ∧ off1 j m q ≤ 0 := by
  unfold off1; split_ifs <;> constructor <;> linarith

/-- Step 2 of the proof of Theorem C.1: `R₂` (shift `p_j` by `-m`, chop, extend with delay
`d - m` on `j → i`) agrees with `R₁` at `p_j` until `t + 2d - 2m ≥ t + d + m`. -/
theorem step2_agree [Finite P] (A : Algorithm P I R M) {d u ε : ℝ}
    (hHO : HistoryOblivious A d u ε) {i j p₀ : P} (hij : i ≠ j) {m t g Tρ : ℝ}
    (hd : 0 < d) (hm0 : 0 ≤ m) (hm : 3 * m ≤ d) (ρ : List (I × R))
    (hT : Tρ + d + m ≤ t) (htρ : ρ.length * g ≤ t) (hg : 0 < g) (a b : I)
    {Hr1 Hr2 : P → Set (ℝ × InEv P I M)}
    (hr1 : RhoRun A d u ε (off1 j m) p₀ g ρ Tρ Hr1) (hr2 : RhoRun A d u ε 0 p₀ g ρ Tρ Hr2)
    {H1 H2 : P → Set (ℝ × InEv P I M)}
    (hH1 : IsRun A (scen (off1 j m) p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t + m, b⟩] d t
      (D1 i j d m)) H1)
    (hH2 : IsRun A (scen 0 p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t, b⟩] d t
      (D2 i j d m)) H2) :
    ∀ o : ℝ × OutEv P R M, t ≤ o.1 → o.1 < t + 2 * d - 2 * m →
      (o ∈ A.beh j (H1 j) ↔ o ∈ A.beh j (H2 j)) := by
  set s1 := (scen (off1 j m) p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t + m, b⟩] d t
      (D1 i j d m) : Scenario P I) with hs1
  set s2 := (scen 0 p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t, b⟩] d t
      (D2 i j d m) : Scenario P I) with hs2
  set s := s1.shift (off1 j m) with hs
  have hHs : IsRun A s H1 := IsRun.shift A hH1 _
  have hsoff : ∀ p, s.off p = 0 := fun p => by simp [hs, Scenario.shift, hs1, scen]
  have hoff : s.off = s2.off := funext fun p => by rw [hsoff]; rfl
  have hsdel : ∀ q r σ, t ≤ σ →
      s.delay q r σ = D1 i j d m q r + off1 j m r - off1 j m q := by
    intro q r σ hσ
    simp only [hs, Scenario.shift, hs1, scen]
    rw [dl_of_ge]
    linarith [(off1_bounds j hm0 q).2]
  have hsdel_le : ∀ q r σ, s.delay q r σ ≤ d + m := by
    intro q r σ
    simp only [hs, Scenario.shift, hs1, scen]
    have := dl_le (d := d) (t := t) (fun q r => D1_le i j d m hm0 q r) q r (σ - off1 j m q)
    linarith [(off1_bounds j hm0 r).2, (off1_bounds j hm0 q).1]
  have hγ : s.MinDelay (d - 2 * m) := by
    refine ⟨by linarith, fun q r σ => ?_⟩
    simp only [hs, Scenario.shift, hs1, scen]
    have := dl_ge (d := d) (t := t) (γ := d - m) (by linarith)
      (fun q r => D1_ge i j d m hm0 q r) q r (σ - off1 j m q)
    linarith [(off1_bounds j hm0 r).1, (off1_bounds j hm0 q).2]
  set C : P → ℝ := fun p =>
    if p = i then t + d - m else if p = j then t + 2 * d - 2 * m else t + 2 * d - m with hC
  have key := restart A hHO s s2 hoff hHs hH2 hγ (rho (off1 j m) p₀ g ρ d) (rho 0 p₀ g ρ d)
    hr1.adm hr2.adm hr1.run hr2.run hr1.wf hr2.wf hr1.solo hr2.solo (fun _ => t)
    (agree_rho A hd (off1_le j hm0) (fun q r => by
        linarith [D1_ge i j d m hm0 q r, (off1_bounds j hm0 r).1])
      (fun r => by linarith [(off1_bounds j hm0 r).1])
      (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp [off1_ne m hij]
        · simp [off1_self])
      hH1 hr1.run)
    (agree_rho A hd (fun _ => le_rfl) (fun q r => by
        simp only [Pi.zero_apply, neg_zero]; linarith [D2_ge i j d m hm0 q r])
      (fun r => by simp only [Pi.zero_apply, neg_zero]; linarith)
      (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp)
      hH2 hr2.run)
    (fun p => ⟨fun e he => by
        have := (hr1.fin p).1 e he; linarith [(off1_bounds j hm0 p).2],
      fun o ho => by have := (hr1.fin p).2 o ho; linarith [(off1_bounds j hm0 p).2]⟩)
    (fun p => ⟨fun e he => by have := (hr2.fin p).1 e he; simp at this; linarith,
      fun o ho => by have := (hr2.fin p).2 o ho; simp at this; linarith⟩)
    (fun q r σ m' ho => by
      have h1 := (hr1.fin q).2 _ ho
      have := hsdel_le q r σ
      simp only at h1
      rw [hsoff, hsoff, sub_zero, sub_zero]
      linarith [(off1_bounds j hm0 q).2])
    (fun q r σ m' ho => by
      have h1 := (hr2.fin q).2 _ ho
      simp only [Pi.zero_apply, sub_zero] at h1
      have := dl_le (d := d) (t := t) (fun q r => D2_le i j d m hm0 q r) q r σ
      rw [hsoff, hsoff, sub_zero, sub_zero]
      simp only [hs2, scen] at this ⊢
      linarith)
    C ?_ ?_ ?_
  · intro o h1 h2
    exact key.2 j o h1 (by rw [hsoff]; simp only [hC, if_neg (Ne.symm hij), if_true]; linarith)
  · -- invocations
    intro p e h1 h2
    rw [Scenario.callEv_shift, hs1, hs2,
      callEv_scen hg htρ p e (by linarith [(off1_bounds j hm0 p).2]),
      callEv_scen hg htρ p e (by simp; linarith)]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Pi.zero_apply, add_zero]
    constructor
    · rintro ⟨c, rfl | rfl, rfl, rfl⟩
      · exact ⟨_, Or.inl rfl, rfl, by simp [off1_ne m hij]⟩
      · exact ⟨_, Or.inr rfl, rfl, by simp [off1_self]⟩
    · rintro ⟨c, rfl | rfl, rfl, rfl⟩
      · exact ⟨_, Or.inl rfl, rfl, by simp [off1_ne m hij]⟩
      · exact ⟨_, Or.inr rfl, rfl, by simp [off1_self]⟩
  · -- delays in the windows
    intro q r σ hσ hσC
    rw [hsoff, sub_zero] at hσ
    rw [hsdel q r σ hσ]
    have e2 : s2.delay q r σ = D2 i j d m q r := dl_of_ge hσ q r
    rw [e2]
    simp only [hC, D1, D2, off1] at hσC ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;>
      first | linarith | (right; constructor <;> linarith) | (constructor <;> linarith)
  · -- the cut is causally closed
    intro q r σ hσ
    have hCt : t ≤ C q := by simp only [hC]; split_ifs <;> linarith
    have hσt : t ≤ σ := le_trans hCt hσ
    rw [hsdel q r σ hσt]
    have e2 : s2.delay q r σ = D2 i j d m q r := dl_of_ge hσt q r
    rw [e2]
    simp only [hC, D1, D2, off1] at hσ ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;> (try constructor) <;> linarith

/-- Step 3 of the proof of Theorem C.1: `R₃` (shift `p_i` by `+m`, chop, extend with delay `d` on
`i → j`) agrees with `R₂` at `p_i` until clock time `t + 2d - 2m`. -/
theorem step3_agree [Finite P] (A : Algorithm P I R M) {d u ε : ℝ}
    (hHO : HistoryOblivious A d u ε) {i j p₀ : P} (hij : i ≠ j) {m t g Tρ : ℝ}
    (hd : 0 < d) (hm0 : 0 ≤ m) (hm : 3 * m ≤ d) (ρ : List (I × R))
    (hT : Tρ + d + 2 * m ≤ t) (htρ : ρ.length * g ≤ t) (hg : 0 < g) (a b : I)
    {Hr2 Hr3 : P → Set (ℝ × InEv P I M)}
    (hr2 : RhoRun A d u ε 0 p₀ g ρ Tρ Hr2) (hr3 : RhoRun A d u ε (off1 i m) p₀ g ρ Tρ Hr3)
    {H2 H3 : P → Set (ℝ × InEv P I M)}
    (hH2 : IsRun A (scen 0 p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t, b⟩] d t
      (D2 i j d m)) H2)
    (hH3 : IsRun A (scen (off1 i m) p₀ g ρ [⟨j, ρ.length, t, b⟩, ⟨i, ρ.length, t + m, a⟩] d t
      (D1 j i d m)) H3) :
    ∀ o : ℝ × OutEv P R M, t ≤ o.1 → o.1 < t + 2 * d - 2 * m →
      (o ∈ A.beh i (H2 i) ↔ o ∈ A.beh i (H3 i)) := by
  set s2 := (scen 0 p₀ g ρ [⟨i, ρ.length, t, a⟩, ⟨j, ρ.length, t, b⟩] d t
      (D2 i j d m) : Scenario P I) with hs2
  set s3 := (scen (off1 i m) p₀ g ρ [⟨j, ρ.length, t, b⟩, ⟨i, ρ.length, t + m, a⟩] d t
      (D1 j i d m) : Scenario P I) with hs3
  set s := s2.shift (fun q => -off1 i m q) with hs
  have hHs : IsRun A s H2 := IsRun.shift A hH2 _
  have hsoff : ∀ p, s.off p = off1 i m p := fun p => by simp [hs, Scenario.shift, hs2, scen]
  have hoff : s.off = s3.off := funext fun p => by rw [hsoff]; rfl
  have hob := off1_bounds i hm0
  have hsdel : ∀ q r σ, t - off1 i m q ≤ σ →
      s.delay q r σ = D2 i j d m q r - off1 i m r + off1 i m q := by
    intro q r σ hσ
    simp only [hs, Scenario.shift, hs2, scen]
    rw [dl_of_ge (by linarith)]
    ring
  have hsdel_le : ∀ q r σ, s.delay q r σ ≤ d + m := by
    intro q r σ
    simp only [hs, Scenario.shift, hs2, scen]
    have := dl_le (d := d) (t := t) (fun q r => D2_le i j d m hm0 q r) q r (σ - -off1 i m q)
    linarith [(hob r).1, (hob q).2]
  have hγ : s.MinDelay (d - 2 * m) := by
    refine ⟨by linarith, fun q r σ => ?_⟩
    simp only [hs, Scenario.shift, hs2, scen]
    have := dl_ge (d := d) (t := t) (γ := d - m) (by linarith)
      (fun q r => D2_ge i j d m hm0 q r) q r (σ - -off1 i m q)
    linarith [(hob r).2, (hob q).1]
  set C : P → ℝ := fun p =>
    if p = j then t + d - m else t + 2 * d - m with hC
  have key := restart A hHO s s3 hoff hHs hH3 hγ (rho 0 p₀ g ρ d) (rho (off1 i m) p₀ g ρ d)
    hr2.adm hr3.adm hr2.run hr3.run hr2.wf hr3.wf hr2.solo hr3.solo (fun _ => t)
    (agree_rho A hd (fun _ => le_rfl) (fun q r => by
        simp only [Pi.zero_apply, neg_zero]; linarith [D2_ge i j d m hm0 q r])
      (fun r => by simp only [Pi.zero_apply, neg_zero]; linarith)
      (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> simp)
      hH2 hr2.run)
    (agree_rho A hd (off1_le i hm0) (fun q r => by
        linarith [D1_ge j i d m hm0 q r, (hob r).1])
      (fun r => by linarith [(hob r).1])
      (fun c hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · simp [off1_ne m (Ne.symm hij)]
        · simp [off1_self])
      hH3 hr3.run)
    (fun p => ⟨fun e he => by have := (hr2.fin p).1 e he; simp at this; linarith,
      fun o ho => by have := (hr2.fin p).2 o ho; simp at this; linarith⟩)
    (fun p => ⟨fun e he => by
        have := (hr3.fin p).1 e he; linarith [(hob p).2],
      fun o ho => by have := (hr3.fin p).2 o ho; linarith [(hob p).2]⟩)
    (fun q r σ m' ho => by
      have h1 := (hr2.fin q).2 _ ho
      simp only [Pi.zero_apply, sub_zero] at h1
      have := hsdel_le q r (σ - s.off q)
      rw [hsoff, hsoff] at *
      linarith [(hob q).1, (hob r).2])
    (fun q r σ m' ho => by
      have h1 := (hr3.fin q).2 _ ho
      simp only at h1
      have := dl_le (d := d) (t := t) (fun q r => D1_le j i d m hm0 q r) q r (σ - s.off q)
      rw [hsoff, hsoff] at *
      simp only [hs3, scen] at this ⊢
      linarith [(hob r).2])
    C ?_ ?_ ?_
  · intro o h1 h2
    exact key.2 i o h1 (by rw [hsoff]; simp only [hC, if_neg hij, off1_self]; linarith)
  · -- invocations
    intro p e h1 h2
    rw [Scenario.callEv_shift, hs2, hs3,
      callEv_scen hg htρ p e (by simp; linarith),
      callEv_scen hg htρ p e (by linarith [(hob p).2])]
    simp only [List.mem_cons, List.not_mem_nil, or_false, Pi.zero_apply, add_zero]
    constructor
    · rintro ⟨c, rfl | rfl, rfl, rfl⟩
      · exact ⟨_, Or.inr rfl, rfl, by simp [off1_self]⟩
      · exact ⟨_, Or.inl rfl, rfl, by simp [off1_ne m (Ne.symm hij)]⟩
    · rintro ⟨c, rfl | rfl, rfl, rfl⟩
      · exact ⟨_, Or.inr rfl, rfl, by simp [off1_ne m (Ne.symm hij)]⟩
      · exact ⟨_, Or.inl rfl, rfl, by simp [off1_self]⟩
  · -- delays in the windows
    intro q r σ hσ hσC
    rw [hsoff] at hσ
    rw [hsdel q r σ hσ]
    have hσt : t ≤ σ := by linarith [(hob q).2]
    have e3 : s3.delay q r σ = D1 j i d m q r := dl_of_ge hσt q r
    rw [e3]
    simp only [hC, D1, D2, off1] at hσC hσ ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;>
      first | linarith | (right; constructor <;> linarith) | (constructor <;> linarith)
  · -- the cut is causally closed
    intro q r σ hσ
    have hCt : t + m ≤ C q := by simp only [hC]; split_ifs <;> linarith
    have hσt : t ≤ σ := by linarith
    rw [hsdel q r σ (by linarith [(hob q).1])]
    have e3 : s3.delay q r σ = D1 j i d m q r := dl_of_ge hσt q r
    rw [e3]
    simp only [hC, D1, D2, off1] at hσ ⊢
    by_cases hqi : q = i <;> by_cases hqj : q = j <;> by_cases hri : r = i <;>
      by_cases hrj : r = j <;> simp_all <;>
      first | linarith | (constructor <;> linarith)

theorem off1_skew (j : P) {m : ℝ} (hm : 0 ≤ m) (p q : P) : |off1 j m p - off1 j m q| ≤ m := by
  rw [abs_le]; unfold off1; split_ifs <;> constructor <;> linarith

/-- Existence, well-formedness and admissibility of the runs of `scen`. -/
theorem scen_run [Finite P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    {d u ε Bop g : ℝ} (hcor : Correct A legal d u ε) (hB : TimeBound A d u ε (fun _ => True) Bop)
    (hg : Bop < g) (hg0 : 0 < g) (hu : 0 ≤ u) {off : P → ℝ} (hoff : ∀ p q, |off p - off q| ≤ ε)
    {D : P → P → ℝ} (hD : ∀ q r, d - u ≤ D q r ∧ D q r ≤ d) {γ : ℝ} (hγ0 : 0 < γ) (hγd : γ ≤ d)
    (hγD : ∀ q r, γ ≤ D q r) {p₀ : P} {ρ : List (I × R)} {cont : List (Call P I)}
    (hcp : cont.Pairwise (fun c c' => c.p ≠ c'.p)) (hck : ∀ c ∈ cont, ρ.length ≤ c.k)
    (hct : ∀ c ∈ cont, ρ.length * g ≤ c.t) (t : ℝ) :
    ∃ H, IsRun A (scen off p₀ g ρ cont d t D) H ∧ WF A (scen off p₀ g ρ cont d t D) H ∧
      (scen off p₀ g ρ cont d t D).Admissible d u ε := by
  have hadm : (scen off p₀ g ρ cont d t D).Admissible d u ε := by
    refine ⟨fun q r σ => ?_, hoff⟩
    simp only [scen, dl]
    split_ifs
    · constructor <;> linarith
    · exact hD q r
  have hγ : (scen off p₀ g ρ cont d t D).MinDelay γ := ⟨hγ0, fun q r σ => dl_ge hγd hγD q r σ⟩
  obtain ⟨H, hH⟩ := exists_run A _ hγ
  exact ⟨H, hH, wf_rho_cont A hcor hB hg hg0 hcp hck hct _ rfl hadm hγ H hH, hadm⟩

/-- A `ρ`-only run. -/
theorem rho_run [Finite P] (A : Algorithm P I R M) {legal : List (I × R) → Prop}
    (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    {d u ε Bop g : ℝ} (hcor : Correct A legal d u ε) (hB : TimeBound A d u ε (fun _ => True) Bop)
    (hfin : FiniteRuns A d u ε) (hg : Bop < g) (hg0 : 0 < g) (hd : 0 < d) (hu : 0 ≤ u)
    {off : P → ℝ} (hoff : ∀ p q, |off p - off q| ≤ ε) (p₀ : P) {ρ : List (I × R)}
    (hρ : legal ρ) : ∃ T Hr, ∀ T', T ≤ T' → RhoRun A d u ε off p₀ g ρ T' Hr := by
  have hadm : (rho off p₀ g ρ d : Scenario P I).Admissible d u ε :=
    ⟨fun _ _ _ => by simp only [rho]; constructor <;> linarith, hoff⟩
  have hγ : (rho off p₀ g ρ d : Scenario P I).MinDelay d := ⟨hd, fun _ _ _ => le_rfl⟩
  obtain ⟨Hr, hHr⟩ := exists_run A _ hγ
  have hwf : WF A (rho off p₀ g ρ d) Hr :=
    wf_rho_cont A hcor hB hg hg0 (p₀ := p₀) (ρ := ρ) (cont := []) List.Pairwise.nil (by simp)
      (by simp) _ (by simp [rho]) hadm hγ Hr hHr
  obtain ⟨T, hT⟩ := hfin _ Hr hadm hHr hwf
  have hso := soloOps_rho A hpc hdet hcor hB hg hg0 hρ _ rfl hadm hHr hwf
  refine ⟨T, Hr, fun T' hT' => ⟨hadm, hHr, hwf, hso, fun p => ⟨fun e he => ?_, fun o ho => ?_⟩⟩⟩
  · have := (hT p).1 e he; exact lt_of_lt_of_le this hT'
  · have := (hT p).2 o ho; exact lt_of_lt_of_le this hT'

theorem perm_two {α : Type*} {a b : α} {L : List α} (h : L.Perm [a, b]) :
    L = [a, b] ∨ L = [b, a] := by
  have hl := h.length_eq
  match L, hl with
  | [x, y], _ =>
    have hx : x ∈ [a, b] := h.subset (by simp)
    have hy : y ∈ [a, b] := h.subset (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · have := List.singleton_perm_singleton.mp (List.perm_cons _ |>.mp h)
      subst this; left; rfl
    · left; rfl
    · right; rfl
    · have h' := h.trans (List.Perm.swap _ _ [])
      have := List.singleton_perm_singleton.mp (List.perm_cons _ |>.mp h')
      subst this; right; rfl

end

end C1


open C1 in
/-- **Theorem C.1 of Chapter IV** of the thesis (Wang–Welch–Lee, PODC 2011). For every strongly
immediately non-self-commuting operation type `OP` (read-modify-write, dequeue, pop), every
correct implementation in an `n`-process system (`n ≥ 2`; the thesis states `n ≥ 3`) with message
delays in `[d - u, d]` and clock skew at most `ε` satisfying the thesis's assumptions (bounded
operation time `Bop`, bounded quiescence, history-obliviousness) has
`|OP| ≥ d + min {ε, u, d/3}`: if every `OP` operation responds within `B`, then
`B ≥ d + min {ε, u, d/3}`. -/
theorem theorem_C1 [Fintype P] [DecidableEq P] (A : Algorithm P I R M)
    {legal : List (I × R) → Prop} (hpc : PrefixClosed legal) (hdet : Deterministic legal)
    {d u ε : ℝ} (hd : 0 < d) (hu : 0 ≤ u) (hε : 0 ≤ ε)
    (hcor : Correct A legal d u ε) {Bop : ℝ} (hBop : TimeBound A d u ε (fun _ => True) Bop)
    (hfin : FiniteRuns A d u ε) (hHO : HistoryOblivious A d u ε)
    (hn : 2 ≤ Fintype.card P) {OP : I → Prop} (hOP : StronglyImmNonSelfCommuting legal OP)
    {B : ℝ} (hB : TimeBound A d u ε OP B) :
    d + min ε (min u (d / 3)) ≤ B := by
  by_contra hlt
  push_neg at hlt
  set m := min ε (min u (d / 3)) with hmdef
  have hm0 : 0 ≤ m := le_min hε (le_min hu (by linarith))
  have hmε : m ≤ ε := min_le_left _ _
  have hmu : m ≤ u := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : 3 * m ≤ d := by
    have := (min_le_right ε _).trans (min_le_right u (d / 3)); linarith
  obtain ⟨i, j, hij⟩ : ∃ i j : P, i ≠ j := by
    obtain ⟨i, j, h⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
    exact ⟨i, j, h⟩
  obtain ⟨ρ, o1, o2, hop1, hop2, hl1, hl2, hn12, hn21⟩ := hOP
  have hρ : legal ρ := hpc ρ [o1] hl1
  have hl1' : legal (ρ ++ [(o1.1, o1.2)]) := by simpa using hl1
  have hl2' : legal (ρ ++ [(o2.1, o2.2)]) := by simpa using hl2
  set g := max Bop 0 + 1 with hgdef
  have hg0 : 0 < g := by have := le_max_right Bop 0; linarith
  have hgB : Bop < g := by have := le_max_left Bop 0; linarith
  set N := ρ.length with hN
  -- the three `ρ`-only runs
  have sk1 : ∀ p q, |off1 j m p - off1 j m q| ≤ ε := fun p q => (off1_skew j hm0 p q).trans hmε
  have sk3 : ∀ p q, |off1 i m p - off1 i m q| ≤ ε := fun p q => (off1_skew i hm0 p q).trans hmε
  have sk2 : ∀ p q, |(0 : P → ℝ) p - (0 : P → ℝ) q| ≤ ε := fun p q => by simpa using hε
  obtain ⟨T1, Hr1, hr1⟩ := rho_run A hpc hdet hcor hBop hfin hgB hg0 hd hu sk1 i hρ
  obtain ⟨T2, Hr2, hr2⟩ := rho_run A hpc hdet hcor hBop hfin hgB hg0 hd hu sk2 i hρ
  obtain ⟨T3, Hr3, hr3⟩ := rho_run A hpc hdet hcor hBop hfin hgB hg0 hd hu sk3 i hρ
  set Tρ := max (max T1 T2) T3 with hTρ
  have hT1 : T1 ≤ Tρ := (le_max_left _ _).trans (le_max_left _ _)
  have hT2 : T2 ≤ Tρ := (le_max_right _ _).trans (le_max_left _ _)
  have hT3 : T3 ≤ Tρ := le_max_right _ _
  set t := |Tρ| + N * g + d + 2 * m + 1 with htdef
  have hNg : 0 ≤ (N : ℝ) * g := by positivity
  have hT : Tρ + d + 2 * m ≤ t := by have := le_abs_self Tρ; linarith
  have htρ : (N : ℝ) * g ≤ t := by have := abs_nonneg Tρ; linarith
  -- delay bounds
  have hD1 : ∀ i j : P, ∀ q r, d - u ≤ D1 i j d m q r ∧ D1 i j d m q r ≤ d := fun i j q r =>
    ⟨by linarith [D1_ge i j d m hm0 q r], D1_le i j d m hm0 q r⟩
  have hD2 : ∀ q r, d - u ≤ D2 i j d m q r ∧ D2 i j d m q r ≤ d := fun q r =>
    ⟨by linarith [D2_ge i j d m hm0 q r], D2_le i j d m hm0 q r⟩
  have hγ0 : 0 < d - m := by linarith
  -- runs `R₁` and `R₁'`
  obtain ⟨H1, hH1, hw1, ha1⟩ := scen_run A hcor hBop hgB hg0 hu sk1 (hD1 i j) hγ0 (by linarith)
    (D1_ge i j d m hm0) (p₀ := i) (ρ := ρ)
    (cont := [⟨i, N, t, o1.1⟩, ⟨j, N, t + m, o2.1⟩]) (by simp [hij]) (by simp [hN])
    (by simp; constructor <;> linarith) t
  obtain ⟨H1', hH1', hw1', ha1'⟩ := scen_run A hcor hBop hgB hg0 hu sk1 (hD1 i j) hγ0
    (by linarith) (D1_ge i j d m hm0) (p₀ := i) (ρ := ρ) (cont := [⟨i, N, t, o1.1⟩]) (by simp [hN])
    (by simp [hN]) (by simp; linarith) t
  obtain ⟨rt1, ret1, hr1c, -, L1, hL1p, -, hL1l, -⟩ := contLin A hpc hdet hcor hBop hgB hg0 hρ
    (cont := [⟨i, N, t, o1.1⟩, ⟨j, N, t + m, o2.1⟩]) (by simp; constructor <;> linarith) _ rfl
    ha1 hH1 hw1
  obtain ⟨rt1', ret1', hr1c', -, L1', hL1p', -, hL1l', -⟩ := contLin A hpc hdet hcor hBop hgB hg0
    hρ (cont := [⟨i, N, t, o1.1⟩]) (by simp; linarith) _ rfl ha1' hH1' hw1'
  have mem1 : (⟨i, N, t, o1.1⟩ : Call P I) ∈ (scen (off1 j m) i g ρ
      [⟨i, N, t, o1.1⟩, ⟨j, N, t + m, o2.1⟩] d t (D1 i j d m)).calls := by simp [scen]
  have mem2 : (⟨j, N, t + m, o2.1⟩ : Call P I) ∈ (scen (off1 j m) i g ρ
      [⟨i, N, t, o1.1⟩, ⟨j, N, t + m, o2.1⟩] d t (D1 i j d m)).calls := by simp [scen]
  have mem1' : (⟨i, N, t, o1.1⟩ : Call P I) ∈ (scen (off1 j m) i g ρ
      [⟨i, N, t, o1.1⟩] d t (D1 i j d m)).calls := by simp [scen]
  -- Step 1.1: `op'_1 = op_1`
  have ret1'_c1 : ret1' ⟨i, N, t, o1.1⟩ = o1.2 := by
    rw [List.perm_singleton.mp hL1p'] at hL1l'
    exact hdet ρ o1.1 _ _ (by simpa using hL1l') hl1'
  have hB1 := hB _ H1 ha1 hH1 hw1 _ mem1 hop1 _ _ (hr1c _ mem1).2.1
  have ret1_c1 : ret1 ⟨i, N, t, o1.1⟩ = o1.2 := by
    have hag := alone_agree A hij hd hm0 hm3 ρ o1.1 o2.1 hH1 hH1'
    have h := (respAt_congr (s := scen (off1 j m) i g ρ [⟨i, N, t, o1.1⟩, ⟨j, N, t + m, o2.1⟩]
      d t (D1 i j d m)) (s' := scen (off1 j m) i g ρ [⟨i, N, t, o1.1⟩] d t (D1 i j d m)) rfl
      (T := t + d + m) (fun e he => hag e (by simpa [scen, off1_ne m hij] using he))
      (by simp only at hB1; linarith)).mp (hr1c _ mem1).2.1
    rw [← ret1'_c1]
    exact ((hr1c' _ mem1').2.2 _ _ h).2
  -- Step 1.2/1.3: `op'_2 ≠ op_2`
  set r2 := ret1 ⟨j, N, t + m, o2.1⟩ with hr2def
  have hr2ne : r2 ≠ o2.2 := by
    intro h
    rcases perm_two hL1p with h' | h' <;> rw [h'] at hL1l <;>
      simp only [List.map_cons, List.map_nil, ret1_c1, ← hr2def, h] at hL1l
    · exact hn12 (by simpa using hL1l)
    · exact hn21 (by simpa using hL1l)
  have hill2 : ¬ legal (ρ ++ [(o2.1, r2)]) := fun h => hr2ne (hdet ρ o2.1 _ _ h hl2')
  have hB2 := hB _ H1 ha1 hH1 hw1 _ mem2 hop2 _ _ (hr1c _ mem2).2.1
  have ht2 := (hr1c _ mem2).1
  -- run `R₂`
  obtain ⟨H2, hH2, hw2, ha2⟩ := scen_run A hcor hBop hgB hg0 hu sk2 hD2 hγ0 (by linarith)
    (D2_ge i j d m hm0) (p₀ := i) (ρ := ρ)
    (cont := [⟨i, N, t, o1.1⟩, ⟨j, N, t, o2.1⟩]) (by simp [hij]) (by simp [hN])
    (by simp; linarith) t
  obtain ⟨rt2, ret2, hr2c, -, L2, hL2p, -, hL2l, -⟩ := contLin A hpc hdet hcor hBop hgB hg0 hρ
    (cont := [⟨i, N, t, o1.1⟩, ⟨j, N, t, o2.1⟩]) (by simp; linarith) _ rfl ha2 hH2 hw2
  have mem21 : (⟨i, N, t, o1.1⟩ : Call P I) ∈ (scen 0 i g ρ
      [⟨i, N, t, o1.1⟩, ⟨j, N, t, o2.1⟩] d t (D2 i j d m)).calls := by simp [scen]
  have mem22 : (⟨j, N, t, o2.1⟩ : Call P I) ∈ (scen 0 i g ρ
      [⟨i, N, t, o1.1⟩, ⟨j, N, t, o2.1⟩] d t (D2 i j d m)).calls := by simp [scen]
  -- Step 2.1: `op''_2 = op'_2`
  have ret2_c2 : ret2 ⟨j, N, t, o2.1⟩ = r2 := by
    have hag := step2_agree A hHO hij hd hm0 hm3 ρ (by linarith) htρ hg0 o1.1 o2.1
      (hr1 Tρ hT1) (hr2 Tρ hT2) hH1 hH2
    have h1 := (hr1c _ mem2).2.1
    unfold RespAt at h1
    simp only [scen, off1_self] at h1 ht2 hB2
    have h2 := (hag _ (by simp only; linarith) (by simp only; linarith)).mp h1
    have h3 : RespAt A (scen 0 i g ρ [⟨i, N, t, o1.1⟩, ⟨j, N, t, o2.1⟩] d t (D2 i j d m)) H2
        ⟨j, N, t, o2.1⟩ (rt1 ⟨j, N, t + m, o2.1⟩ - m) r2 := by
      unfold RespAt; simp only [scen, Pi.zero_apply, add_zero]
      convert h2 using 2
    exact ((hr2c _ mem22).2.2 _ _ h3).2.symm
  -- Step 2.2: `op''_1 = op_1`
  have ret2_c1 : ret2 ⟨i, N, t, o1.1⟩ = o1.2 := by
    rcases perm_two hL2p with h' | h' <;> rw [h'] at hL2l <;>
      simp only [List.map_cons, List.map_nil, ret2_c2] at hL2l
    · exact hdet ρ o1.1 _ _ (hpc _ [(o2.1, r2)] (by simpa using hL2l)) hl1'
    · exact absurd (hpc _ [(o1.1, ret2 ⟨i, N, t, o1.1⟩)] (by simpa using hL2l)) hill2
  have hB21 := hB _ H2 ha2 hH2 hw2 _ mem21 hop1 _ _ (hr2c _ mem21).2.1
  have ht21 := (hr2c _ mem21).1
  -- runs `R₃` and `R₃''`
  obtain ⟨H3, hH3, hw3, ha3⟩ := scen_run A hcor hBop hgB hg0 hu sk3 (hD1 j i) hγ0 (by linarith)
    (D1_ge j i d m hm0) (p₀ := i) (ρ := ρ)
    (cont := [⟨j, N, t, o2.1⟩, ⟨i, N, t + m, o1.1⟩]) (by simp [Ne.symm hij]) (by simp [hN])
    (by simp; constructor <;> linarith) t
  obtain ⟨H3', hH3', hw3', ha3'⟩ := scen_run A hcor hBop hgB hg0 hu sk3 (hD1 j i) hγ0
    (by linarith) (D1_ge j i d m hm0) (p₀ := i) (ρ := ρ) (cont := [⟨j, N, t, o2.1⟩]) (by simp [hN])
    (by simp [hN]) (by simp; linarith) t
  obtain ⟨rt3, ret3, hr3c, -, L3, hL3p, -, hL3l, -⟩ := contLin A hpc hdet hcor hBop hgB hg0 hρ
    (cont := [⟨j, N, t, o2.1⟩, ⟨i, N, t + m, o1.1⟩]) (by simp; constructor <;> linarith) _ rfl
    ha3 hH3 hw3
  obtain ⟨rt3', ret3', hr3c', -, L3', hL3p', -, hL3l', -⟩ := contLin A hpc hdet hcor hBop hgB hg0
    hρ (cont := [⟨j, N, t, o2.1⟩]) (by simp; linarith) _ rfl ha3' hH3' hw3'
  have mem31 : (⟨i, N, t + m, o1.1⟩ : Call P I) ∈ (scen (off1 i m) i g ρ
      [⟨j, N, t, o2.1⟩, ⟨i, N, t + m, o1.1⟩] d t (D1 j i d m)).calls := by simp [scen]
  have mem32 : (⟨j, N, t, o2.1⟩ : Call P I) ∈ (scen (off1 i m) i g ρ
      [⟨j, N, t, o2.1⟩, ⟨i, N, t + m, o1.1⟩] d t (D1 j i d m)).calls := by simp [scen]
  have mem32' : (⟨j, N, t, o2.1⟩ : Call P I) ∈ (scen (off1 i m) i g ρ
      [⟨j, N, t, o2.1⟩] d t (D1 j i d m)).calls := by simp [scen]
  -- Step 3: `op'''_1 = op_1`
  have ret3_c1 : ret3 ⟨i, N, t + m, o1.1⟩ = o1.2 := by
    have hag := step3_agree A hHO hij hd hm0 hm3 ρ hT htρ hg0 o1.1 o2.1
      (hr2 Tρ hT2) (hr3 Tρ hT3) hH2 hH3
    have h1 := (hr2c _ mem21).2.1
    unfold RespAt at h1
    simp only [scen, Pi.zero_apply, add_zero] at h1 ht21 hB21
    have h2 := (hag _ (by simp only; linarith) (by simp only; linarith)).mp h1
    have h3 : RespAt A (scen (off1 i m) i g ρ [⟨j, N, t, o2.1⟩, ⟨i, N, t + m, o1.1⟩] d t
        (D1 j i d m)) H3 ⟨i, N, t + m, o1.1⟩ (rt2 ⟨i, N, t, o1.1⟩ + m) o1.2 := by
      unfold RespAt; simp only [scen, off1_self]
      rw [ret2_c1] at h2
      convert h2 using 2; ring
    exact ((hr3c _ mem31).2.2 _ _ h3).2.symm
  have hr3ne : ret3 ⟨j, N, t, o2.1⟩ ≠ o2.2 := by
    intro h
    rcases perm_two hL3p with h' | h' <;> rw [h'] at hL3l <;>
      simp only [List.map_cons, List.map_nil, ret3_c1, h] at hL3l
    · exact hn21 (by simpa using hL3l)
    · exact hn12 (by simpa using hL3l)
  -- Step 4: `op'''_2 = op_2`, a contradiction
  have ret3'_c2 : ret3' ⟨j, N, t, o2.1⟩ = o2.2 := by
    rw [List.perm_singleton.mp hL3p'] at hL3l'
    exact hdet ρ o2.1 _ _ (by simpa using hL3l') hl2'
  have hB3 := hB _ H3 ha3 hH3 hw3 _ mem32 hop2 _ _ (hr3c _ mem32).2.1
  apply hr3ne
  have hag := alone_agree A (Ne.symm hij) hd hm0 hm3 ρ o2.1 o1.1 hH3 hH3'
  have h := (respAt_congr (s := scen (off1 i m) i g ρ [⟨j, N, t, o2.1⟩, ⟨i, N, t + m, o1.1⟩]
    d t (D1 j i d m)) (s' := scen (off1 i m) i g ρ [⟨j, N, t, o2.1⟩] d t (D1 j i d m)) rfl
    (T := t + d + m) (fun e he => hag e (by simpa [scen, off1_ne m (Ne.symm hij)] using he))
    (by simp only at hB3; linarith)).mp (hr3c _ mem32).2.1
  rw [← ret3'_c2]
  exact ((hr3c' _ mem32').2.2 _ _ h).2

end Podc.SharedObjectTimeBounds
