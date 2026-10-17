import Papers.PODC2022.HybridApproxAgreement.Map
import Papers.PODC2022.HybridApproxAgreement.Iteration

/-!
# `Π_AA` is not secure in the synchronous network: a counterexample to Theorem 3.1 (1)

`aaAlg tₛ tₐ Δ` is `Π_AA` with `S = 1` iteration (`S = ⌈log₂(δmax/ε)⌉ = 1`, e.g. `δmax = 1`,
`ε = 1/2`): run `Π_oBC` (`OBC.alg`) on the input and, on termination, output the value of lines 4–7
(`aaStep`) computed from the obtained `O`.

**Counterexample** (`n = 3`, `tₛ = 1`, `tₐ = 0`, so `0 ≤ tₐ < n/3 ≤ tₛ < n/2` and `2 tₛ + tₐ < n`;
`Δ = 1`; synchronous network with zero delay). Honest `P₀`, `P₁` have inputs `0`, `1`; `P₂` is
Byzantine. In the `Π_rBC` instance with sender `P₂`, `P₂` mounts the attack of `RBC.lean` (`propose 0`
to `P₀` and `propose 1` to `P₁`, both arriving at `2Δ`, and votes for both), so at `3Δ` `P₀` obtains
`(0, P₂)` and `P₁` obtains `(1, P₂)`; the honest instances deliver `(0, P₀)`, `(1, P₁)` to both.
`P₂` then reports to each honest party exactly that party's own `O`, so `P₂` is a witness for both
(each honest party has the witnesses `{itself, P₂}`, `n - tₛ = 2`), and both terminate at `4Δ + 1`
with `O₀ = {0, 1, 0}` and `O₁ = {0, 1, 1}`. Discarding `max(tₐ, k) = 1` value at each end gives
the outputs `0` and `1`: the honest parties do not get closer at all, `|0 - 1| = 1 > ε`.
(With `S > 1` iterations the same attack can be repeated in every iteration.)

The run is computed with Boolean values (by `decide`, `Run.st_eq_simStates`) and transferred to real
values with `Run.st_map` (`Π_oBC` only compares values for equality, `Map.lean`).

Sanity check (`aa_silent`): when everybody is honest, all parties output the same value.
-/

open Cslib.Byzantine.PartialSync

namespace HybridApproxAgreement.AA

variable {n : ℕ}

/-- `Π_AA` with one iteration, thresholds `tₛ`, `tₐ`, time unit `Δ`. -/
noncomputable def aaAlg (ts ta Δ : ℕ) : Algorithm (Fin n) (OBC.Msg n ℝ) (OBC.St n ℝ) ℝ ℝ where
  init := (OBC.alg Δ (n - ts)).init
  step := (OBC.alg Δ (n - ts)).step
  send := (OBC.alg Δ (n - ts)).send
  decide _ s := if s.phase = 3 then some (aaStep ts ta s.O) else none

/-- Signatures for `Π_oBC`: the tokens of the `Π_rBC` messages, tagged by the instance (the sender
of the instance signs proposals, voters sign votes); reports are unsigned (authenticated channels). -/
def auth : Auth (Fin n) (OBC.Msg n ℝ) (Fin n × RBC.Tok n ℝ) where
  signer
    | (s, .prop _) => s
    | (_, .vote p _) => p
  tokens
    | .inst s m => {x | x.1 = s ∧ x.2 ∈ (RBC.auth s).tokens m}
    | .report _ _ _ => ∅

/-! ### The attack, with Boolean values -/

/-- The Byzantine party `P₂`. -/
def byzB : Fin 3 → ℕ → Fin 3 → List (OBC.Msg 3 Bool) := fun _ τ p =>
  if τ = 2 then
    (if p = 0 then [.inst 2 (.propose false)] else if p = 1 then [.inst 2 (.propose true)] else [])
  else if τ = 3 then
    (if p = 0 then [.inst 2 (.vote 2 false)] else if p = 1 then [.inst 2 (.vote 2 true)] else [])
  else if τ = 4 then
    (if p = 0 then [.report 0 false 0, .report 1 true 1, .report 2 false 2]
     else if p = 1 then [.report 0 false 0, .report 1 true 1, .report 2 true 2] else [])
  else []

/-- The attack with Boolean values (`false` ↦ `0`, `true` ↦ `1`). -/
def attackB : Run (Fin 3) (OBC.Msg 3 Bool) Bool where
  faulty := {2}
  inp p := decide (p = 1)
  gst := 0
  byz := byzB
  dl _ τ _ := τ

theorem attackB_st (τ : ℕ) (p : Fin 3) :
    attackB.st (OBC.alg 1 2) τ p =
      (simStates (OBC.alg 1 2) attackB.inp (fun q => decide (q = 2)) byzB
        ((OBC.alg 1 2).init 0 false) τ).getD p ((OBC.alg 1 2).init 0 false) :=
  Run.st_eq_simStates _ (fun _ _ _ => rfl) (fun q => by simp [attackB]) _ τ p

theorem attackB_final :
    ((attackB.st (OBC.alg 1 2) 6 0).phase = 3 ∧
      (attackB.st (OBC.alg 1 2) 6 0).O = fun x => some (decide (x = 1))) ∧
    ((attackB.st (OBC.alg 1 2) 6 1).phase = 3 ∧
      (attackB.st (OBC.alg 1 2) 6 1).O = fun x => some (decide (x ≠ 0))) := by
  rw [attackB_st, attackB_st]; decide

theorem attackB_early : ∀ τ < 6, (attackB.st (OBC.alg 1 2) τ 0).phase ≠ 3 ∧
    (attackB.st (OBC.alg 1 2) τ 1).phase ≠ 3 := by
  intro τ hτ
  rw [attackB_st, attackB_st]
  interval_cases τ <;> decide

/-! ### Transfer to real values -/

/-- `false ↦ 0`, `true ↦ 1`. -/
def g (b : Bool) : ℝ := if b then 1 else 0

theorem g_injective : Function.Injective g := by
  intro a b h; cases a <;> cases b <;> simp_all [g]

/-- The attack with real values: inputs `0` (`P₀`, `P₂`) and `1` (`P₁`). -/
noncomputable def attack : Run (Fin 3) (OBC.Msg 3 ℝ) ℝ where
  faulty := {2}
  inp p := g (decide (p = 1))
  gst := 0
  byz q τ p := (byzB q τ p).map (OBC.Msg.map g)
  dl _ τ _ := τ

theorem aaAlg_init : (aaAlg (n := 3) 1 0 1).init = (OBC.alg 1 2).init := rfl
theorem aaAlg_step : (aaAlg (n := 3) 1 0 1).step = (OBC.alg 1 2).step := rfl
theorem aaAlg_send : (aaAlg (n := 3) 1 0 1).send = (OBC.alg 1 2).send := rfl

theorem attack_st (τ : ℕ) (p : Fin 3) :
    attack.st (aaAlg 1 0 1) τ p = (attackB.st (OBC.alg 1 2) τ p).map g := by
  have hinit : ∀ p v, (aaAlg (n := 3) 1 0 1).init p (g v) = OBC.St.map g ((OBC.alg 1 2).init p v) := by
    intro p v; rw [aaAlg_init]; exact OBC.init_map g_injective 1 2 p v
  have hstep : ∀ p s ib, (aaAlg (n := 3) 1 0 1).step p (OBC.St.map g s)
      (fun q => (ib q).map (OBC.Msg.map g)) = OBC.St.map g ((OBC.alg 1 2).step p s ib) := by
    intro p s ib; rw [aaAlg_step]; exact OBC.step_map g_injective 1 2 p s ib
  have hsend : ∀ p s q, (aaAlg (n := 3) 1 0 1).send p (OBC.St.map g s) q =
      ((OBC.alg 1 2).send p s q).map (OBC.Msg.map g) := by
    intro p s q; rw [aaAlg_send]; rfl
  exact Run.st_map (R := attackB) (R' := attack) (OBC.Msg.map g) (OBC.St.map g) g hinit hstep
    hsend rfl (fun _ => rfl) (fun _ _ _ => rfl) rfl τ p

theorem attack_valid : syncRuns 1 0 attack :=
  ⟨⟨by simp [attack], fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => by simp [attack]⟩, rfl⟩

/-- The Byzantine party only uses its own signatures (and unsigned reports). -/
theorem attack_authValid : attack.AuthValid auth (aaAlg 1 0 1) := by
  intro b hb τ r _ m hm x hx
  left
  simp only [attack, Finset.mem_singleton] at hb ⊢
  subst hb
  simp only [attack, byzB] at hm
  split_ifs at hm <;> simp [OBC.Msg.map, RBC.Msg.map] at hm <;>
    first
    | (subst hm; simp [auth, RBC.auth] at hx; obtain ⟨x1, x2⟩ := x; simp_all [auth])
    | (rcases hm with rfl | rfl | rfl <;> simp [auth] at hx)

/-! ### Computing the outputs -/

theorem kth_coe_sorted {l : List ℝ} (h : l.Pairwise (· ≤ ·)) (i : ℕ) :
    kth (l : Multiset ℝ) i = l.getD i 0 := by
  unfold kth
  congr 1
  exact List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _) h
    (Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _))

theorem recvVals_some (v : Fin 3 → ℝ) :
    recvVals (fun x => some (v x)) = ((([v 0, v 1, v 2] : List ℝ)) : Multiset ℝ) := by
  have : dom (fun x : Fin 3 => some (v x)) = Finset.univ := by ext; simp [dom]
  simp only [recvVals, this, Option.getD_some, Fin.univ_val_map]
  simp [List.ofFn_succ]

theorem aaStep_P0 : aaStep (P := Fin 3) 1 0 (fun x => some (g (decide (x = 1)))) = 0 := by
  have hV : recvVals (fun x : Fin 3 => some (g (decide (x = 1)))) = (([0, 0, 1] : List ℝ) : Multiset ℝ) := by
    rw [recvVals_some]
    simp only [g]
    norm_num
    exact List.Perm.swap 0 1 []
  unfold aaStep midTrim
  rw [hV]
  simp only [Multiset.coe_card, List.length_cons, List.length_nil, Fintype.card_fin]
  norm_num
  rw [kth_coe_sorted (by simp)]
  rfl

theorem aaStep_P1 : aaStep (P := Fin 3) 1 0 (fun x => some (g (decide (x ≠ 0)))) = 1 := by
  have hV : recvVals (fun x : Fin 3 => some (g (decide (x ≠ 0)))) = (([0, 1, 1] : List ℝ) : Multiset ℝ) := by
    rw [recvVals_some]
    simp only [g]
    norm_num
  unfold aaStep midTrim
  rw [hV]
  simp only [Multiset.coe_card, List.length_cons, List.length_nil, Fintype.card_fin]
  norm_num
  rw [kth_coe_sorted (by simp)]
  rfl

theorem attack_decide (τ : ℕ) (p : Fin 3) :
    (aaAlg 1 0 1).decide p (attack.st (aaAlg 1 0 1) τ p) =
      if (attackB.st (OBC.alg 1 2) τ p).phase = 3 then
        some (aaStep (P := Fin 3) 1 0 fun x => ((attackB.st (OBC.alg 1 2) τ p).O x).map g)
      else none := by
  rw [attack_st]; rfl

theorem attack_outputs_P0 : Outputs (aaAlg 1 0 1) attack 0 0 := by
  refine ⟨6, ?_, fun σ hσ => ?_⟩
  · rw [attack_decide]
    simp only [attackB_final.1.1, attackB_final.1.2, ↓reduceIte, Option.map_some, aaStep_P0]
  · rw [attack_decide]; simp [(attackB_early σ hσ).1]

theorem attack_outputs_P1 : Outputs (aaAlg 1 0 1) attack 1 1 := by
  refine ⟨6, ?_, fun σ hσ => ?_⟩
  · rw [attack_decide]
    simp only [attackB_final.2.1, attackB_final.2.2, ↓reduceIte, Option.map_some, aaStep_P1]
  · rw [attack_decide]; simp [(attackB_early σ hσ).2]

/-- The parameters: `δmax = 1`, `ε = 1/2` give `S = ⌈log₂(δmax/ε)⌉ = 1` iteration. -/
theorem S_eq_one : ⌈Real.logb 2 (1 / (1 / 2))⌉₊ = 1 := by
  norm_num [Real.logb_self_eq_one]

/-- **Theorem 3.1 (1) is false.** For `n = 3`, `tₛ = 1`, `tₐ = 0` (which satisfy
`0 ≤ tₐ < n/3 ≤ tₛ < n/2` and `2 tₛ + tₐ < n`), `Δ = 1`, `ε = 1/2` and inputs in `[0, δmax] = [0, 1]`
(so `S = 1`), `Π_AA` is not a `tₛ`-secure AA protocol in the synchronous network: in the run `attack`
(synchronous, one Byzantine party, unforgeability respected) the honest parties output `0` and `1`. -/
theorem theorem_3_1_sync_false :
    ¬ SecureAA auth (aaAlg (n := 3) 1 0 1) (1 / 2) (Set.Icc 0 1) (syncRuns 1 0) := by
  intro h
  have hin : ∀ p, attack.inp p ∈ Set.Icc (0 : ℝ) 1 := by
    intro p; simp only [attack, g]; split_ifs <;> norm_num
  have := h.agreement attack attack_valid attack_authValid hin 0 (by simp [attack])
    1 (by simp [attack]) 0 1 attack_outputs_P0 attack_outputs_P1
  norm_num at this

/-! ### Sanity check: a silent Byzantine party -/

/-- `P₂` Byzantine and silent, honest inputs `0` (`P₀`) and `1` (`P₁`), Boolean values. -/
def silentB : Run (Fin 3) (OBC.Msg 3 Bool) Bool := Run.quiet {2} fun p => decide (p = 1)

/-- The same with real values. -/
noncomputable def silent : Run (Fin 3) (OBC.Msg 3 ℝ) ℝ := Run.quiet {2} fun p => g (decide (p = 1))

theorem silentB_final : ∀ p ∈ ({0, 1} : Finset (Fin 3)),
    (silentB.st (OBC.alg 1 2) 6 p).phase = 3 ∧
      (silentB.st (OBC.alg 1 2) 6 p).O = ![some false, some true, none] := by
  intro p hp
  rw [Run.st_eq_simStates _ (fun _ _ _ => rfl) (bad := fun q => decide (q = 2))
    (fun q => by simp [silentB]) ((OBC.alg 1 2).init 0 false)]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> decide

theorem silent_st (τ : ℕ) (p : Fin 3) :
    silent.st (aaAlg 1 0 1) τ p = (silentB.st (OBC.alg 1 2) τ p).map g := by
  have hinit : ∀ p v, (aaAlg (n := 3) 1 0 1).init p (g v) = OBC.St.map g ((OBC.alg 1 2).init p v) := by
    intro p v; rw [aaAlg_init]; exact OBC.init_map g_injective 1 2 p v
  have hstep : ∀ p s ib, (aaAlg (n := 3) 1 0 1).step p (OBC.St.map g s)
      (fun q => (ib q).map (OBC.Msg.map g)) = OBC.St.map g ((OBC.alg 1 2).step p s ib) := by
    intro p s ib; rw [aaAlg_step]; exact OBC.step_map g_injective 1 2 p s ib
  exact Run.st_map (R := silentB) (R' := silent) (OBC.Msg.map g) (OBC.St.map g) g hinit hstep
    (fun _ _ _ => rfl) rfl (fun _ => rfl) (fun _ _ _ => rfl) rfl τ p

/-- With a silent Byzantine party, both honest parties output `1/2` (exact agreement, and in the
range `[0, 1]` of the honest inputs): the encoding of `Π_AA` terminates and behaves as intended. -/
theorem silent_decide (τ : ℕ) (p : Fin 3) :
    (aaAlg 1 0 1).decide p (silent.st (aaAlg 1 0 1) τ p) =
      if (silentB.st (OBC.alg 1 2) τ p).phase = 3 then
        some (aaStep (P := Fin 3) 1 0 fun x => ((silentB.st (OBC.alg 1 2) τ p).O x).map g)
      else none := by
  rw [silent_st]; rfl

theorem aaStep_silent :
    aaStep (P := Fin 3) 1 0 (fun x => ((![some false, some true, none] : Fin 3 → Option Bool) x).map g)
      = 1 / 2 := by
  have hO : (fun x => ((![some false, some true, none] : Fin 3 → Option Bool) x).map g) =
      (![some 0, some 1, none] : Fin 3 → Option ℝ) := by
    funext x; fin_cases x <;> simp [g]
  have hdom : dom (![some 0, some 1, none] : Fin 3 → Option ℝ) = {0, 1} := by
    ext x; fin_cases x <;> simp [dom]
  have hV : recvVals (![some 0, some 1, none] : Fin 3 → Option ℝ) =
      (([0, 1] : List ℝ) : Multiset ℝ) := by
    simp [recvVals, hdom]; rfl
  rw [hO]
  unfold aaStep midTrim
  rw [hV]
  simp only [Multiset.coe_card, List.length_cons, List.length_nil, Fintype.card_fin]
  norm_num
  rw [kth_coe_sorted (by simp), kth_coe_sorted (by simp)]
  norm_num

/-- With a silent Byzantine party, both honest parties output `1/2` (exact agreement, and in the
range `[0, 1]` of the honest inputs): the encoding of `Π_AA` terminates and behaves as intended. -/
theorem aa_silent : ∀ p ∈ ({0, 1} : Finset (Fin 3)),
    (aaAlg 1 0 1).decide p (silent.st (aaAlg 1 0 1) 6 p) = some (1 / 2) := by
  intro p hp
  obtain ⟨h1, h2⟩ := silentB_final p hp
  rw [silent_decide]
  simp only [h1, h2, ↓reduceIte, aaStep_silent]

end HybridApproxAgreement.AA
