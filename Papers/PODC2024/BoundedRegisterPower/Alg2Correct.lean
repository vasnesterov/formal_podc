import Papers.PODC2024.BoundedRegisterPower.Alg2Sim

/-!
# Correctness of Algorithm 2 (Lemma 5.8 of the full version)

Given a path system of length `L ≥ 1` for the task `Δ` and an ε-agreement black box `E` with
resolution `L` (`EBox`), Algorithm 2 solves `Δ` wait-free (`1`-resilient, two processes).
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

set_option linter.unusedSectionVars false

variable {In O : Type} {KE : Type} [DecidableEq KE] {VE : KE → Type}
  {Δ : (Bool → In) → (Bool → O) → Prop} {L B : ℕ}
  {E : Alg Bool KE VE Bool ℕ} {PS : PathSystem Δ L}

lemma vec_self (X : Bool → In) (p : Bool) : vec p (X p) (X (!p)) = X := by
  funext b; cases b <;> cases p <;> simp [vec]

/-- Choosing two entries from nodes at distance `≤ 1` of a path gives a node of the path. -/
lemma exists_node (P : ℕ → Bool → O) (hadj : ∀ m, m < L → ∃ b, P m (!b) = P (m + 1) (!b))
    (p : Bool) {dp dq : ℕ} (hp : dp < L) (hq : dq < L) (h1 : dp ≤ dq + 1) (h2 : dq ≤ dp + 1) :
    ∃ m, m < L ∧ P m p = P dp p ∧ P m (!p) = P dq (!p) := by
  rcases Nat.lt_trichotomy dp dq with h | rfl | h
  · obtain rfl : dq = dp + 1 := by omega
    obtain ⟨b, hb⟩ := hadj dp hp
    by_cases hbp : b = p
    · subst hbp; exact ⟨dp, hp, rfl, hb⟩
    · have : (!b) = p := by cases b <;> cases p <;> simp_all
      rw [this] at hb
      exact ⟨dp + 1, hq, hb.symm, rfl⟩
  · exact ⟨dp, hp, rfl, rfl⟩
  · obtain rfl : dp = dq + 1 := by omega
    obtain ⟨b, hb⟩ := hadj dq hq
    by_cases hbp : b = p
    · subst hbp; exact ⟨dq + 1, hp, rfl, hb.symm⟩
    · have : (!b) = p := by cases b <;> cases p <;> simp_all
      rw [this] at hb
      exact ⟨dq, hq, hb, rfl⟩

/-- Facts about a process that has decided in Algorithm 2. -/
lemma decided_facts (hE : EBox E L B) (hL : 1 ≤ L) {X : Bool → In} {σ : List Bool} {p : Bool}
    {c : O} (hc : ((alg2 E PS).run ((alg2 E PS).initCfg X) σ).out p = some c) :
    ∃ xo d xo2, ((alg2 E PS).run ((alg2 E PS).initCfg X) σ).loc p = .done (X p) xo d xo2 ∧
      d ≤ L ∧ (d = L → myIn xo = true) ∧ c = PS.path X (if myIn xo then !p else p) d p := by
  set C := (alg2 E PS).run ((alg2 E PS).initCfg X) σ
  obtain ⟨hI, hS⟩ := reach_ok (B := B) (PS := PS) hE X σ
  have hout := hI.out p
  have hx := hI.xOf_eq p
  rcases hs : C.loc p with ⟨x⟩ | ⟨x⟩ | ⟨x, xo, s⟩ | ⟨x, xo, d, xo2⟩ | ⟨x, xo, d, xo2⟩ <;>
    rw [hs] at hout hx <;> simp only [out2Of, xOf] at hout hx <;> rw [hc] at hout
  iterate 4 (· simp at hout)
  subst hx
  simp only [Option.some.injEq] at hout
  -- the `E`-decision of `p` (for any consistent `x'`)
  have hd : ∀ x', SimInputs C.loc x' → ∃ τ, SimRel E PS x' B C (E.run (E.initCfg x') τ) τ σ ∧
      (E.run (E.initCfg x') τ).out p = some d := by
    intro x' hx'
    obtain ⟨τ, h⟩ := hS x' hx'
    have := h.phase p
    rw [hs] at this
    exact ⟨τ, h, this⟩
  obtain ⟨τ, h, hdτ⟩ := hd _ (simInputs_canonX C.loc)
  have hx'p : canonX C.loc p = myIn xo := simInputs_canonX C.loc p xo (by rw [hs]; rfl)
  have hdL : d ≤ L := (hE.safe _ τ).1 p d hdτ
  have hone : d = L → myIn xo = true := by
    rintro rfl; rw [← hx'p]; exact hE.one _ τ p hdτ
  refine ⟨xo, d, xo2, rfl, hdL, hone, ?_⟩
  rw [hout]
  have hxo := hI.xo p xo (by rw [hs]; rfl)
  by_cases hd0 : d = 0
  · subst hd0
    have h0 := hE.zero _ τ p hdτ
    rw [hx'p] at h0
    rcases hxo with rfl | rfl
    · simp [myIn] at h0
    · simp only [out2, ite_true]
      rw [vec_self, PS.path_zero X p]
  · by_cases hdl : d < L
    · have := hI.xo2 p _ xo d xo2 (by rw [hs]; right; rfl) (Nat.pos_of_ne_zero hd0) hdl
      subst this
      simp only [out2, hd0, ite_false, hdl, ite_true]
      rw [vec_self]
    · obtain rfl : d = L := by omega
      have h1 := hE.one _ τ p hdτ
      rw [hx'p] at h1
      simp only [out2, hd0, ite_false, lt_irrefl, h1, ite_true]
      rw [PS.path_L, Bool.not_not]

/-- The case of Lemma 5.8 in which exactly one process `p` (the one that saw `⊥`) has
ε-agreement input `1`: both choose nodes of the path for the partial input missing `!p`. -/
lemma mixed_case (hL : 1 ≤ L) (X : Bool → In) (p : Bool) {dp dq : ℕ} (hdp : dp ≤ L) (hdq : dq < L)
    (h1 : dp ≤ dq + 1) (h2 : dq ≤ dp + 1) :
    ∃ Y, Δ X Y ∧ Y p = PS.path X (!p) dp p ∧ Y (!p) = PS.path X (!p) dq (!p) := by
  rcases Nat.lt_or_ge dp L with hp | hp
  · obtain ⟨m, hm, hm1, hm2⟩ := exists_node (PS.path X (!p)) (PS.adj X (!p)) p hp hdq h1 h2
    exact ⟨_, PS.legal X _ m hm, hm1, hm2⟩
  · obtain rfl : dp = L := by omega
    obtain rfl : dq = dp - 1 := by omega
    refine ⟨_, PS.legal X (!p) (dp - 1) (by omega), ?_, rfl⟩
    have := PS.last X (!p)
    rw [Bool.not_not] at this
    exact this

/-- **Lemma 5.8** (safety of Algorithm 2): in every finite execution the decisions extend to a
legal output vector. -/
theorem alg2_safe (hE : EBox E L B) (hL : 1 ≤ L) (X : Bool → In) (σ : List Bool) :
    taskOf Δ X ((alg2 E PS).run ((alg2 E PS).initCfg X) σ).out := by
  set C := (alg2 E PS).run ((alg2 E PS).initCfg X) σ
  obtain ⟨hI, hS⟩ := reach_ok (B := B) (PS := PS) hE X σ
  -- a single decided process
  have single : ∀ p c, C.out p = some c → ∃ Y, Δ X Y ∧ Y p = c := by
    intro p c hc
    obtain ⟨xo, d, xo2, -, hdL, hone, rfl⟩ := decided_facts (B := B) hE hL hc
    rcases Nat.lt_or_ge d L with h | h
    · exact ⟨_, PS.legal X _ d h, rfl⟩
    · obtain rfl : d = L := by omega
      obtain ⟨Y, hY, hYp⟩ := PS.cover X (!p)
      refine ⟨Y, hY, ?_⟩
      simp only [hone rfl, ↓reduceIte, PS.path_L]
      simpa using hYp
  -- the common projected `E` execution
  obtain ⟨τ, h⟩ := hS _ (simInputs_canonX C.loc)
  have hsafe := hE.safe (canonX C.loc) τ
  have hdec : ∀ p c, C.out p = some c → ∃ xo d, d ≤ L ∧ (d = L → myIn xo = true) ∧
      c = PS.path X (if myIn xo then !p else p) d p ∧ canonX C.loc p = myIn xo ∧
      xoOf (C.loc p) = some xo ∧
      (E.run (E.initCfg (canonX C.loc)) τ).out p = some d := by
    intro p c hc
    obtain ⟨xo, d, xo2, hs, hdL, hone, hcv⟩ := decided_facts (B := B) hE hL hc
    have hph := h.phase p
    rw [hs] at hph
    exact ⟨xo, d, hdL, hone, hcv, simInputs_canonX C.loc p xo (by rw [hs]; rfl),
      by rw [hs]; rfl, hph⟩
  rcases ht : C.out true with _ | c1 <;> rcases hf : C.out false with _ | c2
  · exact ⟨_, PS.legal X true 0 (by omega), fun b c hb => by cases b <;> simp_all⟩
  · obtain ⟨Y, hY, hYb⟩ := single false c2 hf
    exact ⟨Y, hY, fun b c hb => by cases b <;> simp_all⟩
  · obtain ⟨Y, hY, hYb⟩ := single true c1 ht
    exact ⟨Y, hY, fun b c hb => by cases b <;> simp_all⟩
  obtain ⟨xo1, d1, hd1, hone1, rfl, hx1, hxo1, hD1⟩ := hdec true c1 ht
  obtain ⟨xo2, d2, hd2, hone2, rfl, hx2, hxo2, hD2⟩ := hdec false _ hf
  have ha1 := hsafe.2.2 true false d1 d2 hD1 hD2
  have ha2 := hsafe.2.2 false true d2 d1 hD2 hD1
  suffices ∃ Y, Δ X Y ∧ Y true = PS.path X (if myIn xo1 then !true else true) d1 true ∧
      Y false = PS.path X (if myIn xo2 then !false else false) d2 false by
    obtain ⟨Y, hY, h1, h2⟩ := this
    exact ⟨Y, hY, fun b c hb => by cases b <;> simp_all⟩
  cases hm1 : myIn xo1 <;> cases hm2 : myIn xo2
  · -- both saw the other's input: ε-agreement validity gives `d1 = d2 = 0`
    have hall : ∀ q, canonX C.loc q = false := by
      intro q; cases q
      · rw [hx2, hm2]
      · rw [hx1, hm1]
    have v1 := hsafe.2.1 false hall true d1 hD1
    have v2 := hsafe.2.1 false hall false d2 hD2
    simp only [Bool.false_eq_true, ↓reduceIte] at v1 v2
    subst v1 v2
    refine ⟨_, PS.legal X true 0 (by omega), by simp, ?_⟩
    simp [PS.path_zero X false true]
  · -- process `false` saw `⊥`
    have hne : d1 ≠ L := fun e => by simpa [hm1] using hone1 e
    obtain ⟨Y, hY, h1, h2⟩ := mixed_case (PS := PS) hL X false hd2 (by omega) ha2 ha1
    exact ⟨Y, hY, by simpa using h2, by simpa using h1⟩
  · -- process `true` saw `⊥`
    have hne : d2 ≠ L := fun e => by simpa [hm2] using hone2 e
    obtain ⟨Y, hY, h1, h2⟩ := mixed_case (PS := PS) hL X true hd1 (by omega) ha1 ha2
    exact ⟨Y, hY, by simpa using h1, by simpa using h2⟩
  · -- both saw `⊥`: impossible
    exfalso
    have e1 : xo1 = none := by simpa [myIn] using hm1
    have e2 : xo2 = none := by simpa [myIn] using hm2
    subst e1 e2
    exact hI.notBoth true hxo1 hxo2

end Podc.BoundedRegisterPower

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

set_option linter.unusedSectionVars false

variable {In O : Type} {KE : Type} [DecidableEq KE] {VE : KE → Type}
  {Δ : (Bool → In) → (Bool → O) → Prop} {L B : ℕ}
  {E : Alg Bool KE VE Bool ℕ} {PS : PathSystem Δ L}

/-- Step complexity of Algorithm 2: a process that took `B + 3` steps has decided (`B` bounds the
steps of `E`). -/
theorem alg2_decides (hE : EBox E L B) (X : Bool → In) (σ : List Bool) (p : Bool)
    (hp : B + 3 ≤ σ.count p) :
    (((alg2 E PS).run ((alg2 E PS).initCfg X) σ).out p).isSome := by
  set C := (alg2 E PS).run ((alg2 E PS).initCfg X) σ
  obtain ⟨hI, hS⟩ := reach_ok (B := B) (PS := PS) hE X σ
  obtain ⟨τ, h⟩ := hS _ (simInputs_canonX C.loc)
  have hph := h.phase p
  have hout := hI.out p
  rcases hs : C.loc p with ⟨x⟩ | ⟨x⟩ | ⟨x, xo, s⟩ | ⟨x, xo, d, xo2⟩ | ⟨x, xo, d, xo2⟩ <;>
    rw [hs] at hph hout <;> simp only [PhaseOK] at hph
  · omega
  · omega
  · have := hE.bound (canonX C.loc) τ p (by omega)
    rw [hph.2.1] at this
    exact absurd this (by simp)
  · omega
  · rw [hout]; rfl

/-- **Algorithm 2 solves the task** wait-free (two processes, `1`-resilient), given a path system
of length `L ≥ 1` and an ε-agreement black box of resolution `L`. -/
theorem alg2_solves (hE : EBox E L B) (hL : 1 ≤ L) :
    (alg2 E PS).Solves 1 (taskOf Δ) :=
  ⟨fun X σ => alg2_safe hE hL X σ, fun X σ _ p hp =>
    Alg.termination_of_bound _ (B + 3) (fun X σ p h => alg2_decides hE X σ p h) X σ p hp⟩

end Podc.BoundedRegisterPower
