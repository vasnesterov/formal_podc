import Papers.PODC2019.ComposableCRN.Automaton

/-!
# Small obliviously-computable gadgets

Building blocks used in §6 of Severson–Haley–Doty (PODC 2019), in particular in the proof of
Lemma 6.2:

* constants, projections and `x i - n` (via the leader-automaton construction
  `obliviouslyComputable_of_automaton`);
* the `k`-ary minimum, computed by the single reaction `X₁ + … + X_k → Y`
  (`obliviouslyComputable_min`);
* the gadget `c(a, b, w) = a + 1{w > j} · b`, computed by the reactions `A → Y` and
  `(j+1) W + B → (j+1) W + Y` (`obliviouslyComputable_add_ite`).

For the last two the CRNs have a leader species `L` that never reacts (the model of
`ObliviouslyComputable` requires a leader).
-/

set_option linter.unusedSectionVars false

namespace Podc.ComposableCRN

namespace Gadgets

/-- Species of the gadget CRNs: inputs `X i`, output `Y`, (unused) leader `L`. -/
inductive Sp (ι : Type) where
  | X (i : ι)
  | Y
  | L
  deriving DecidableEq

/-- `Sp ι ≃ ι ⊕ Bool`, for the `Fintype` instance. -/
def Sp.equiv (ι : Type) : Sp ι ≃ ι ⊕ Bool where
  toFun
    | .X i => .inl i
    | .Y => .inr true
    | .L => .inr false
  invFun
    | .inl i => .X i
    | .inr true => .Y
    | .inr false => .L
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with i | (_ | _) <;> rfl

instance (ι : Type) [Fintype ι] : Fintype (Sp ι) := Fintype.ofEquiv _ (Sp.equiv ι).symm

/-- The configuration with `x i` copies of `X i`, `y` copies of `Y` and `l` copies of `L`. -/
def mk {ι : Type} (x : ι → ℕ) (y l : ℕ) : Config (Sp ι) := fun s =>
  match s with
  | .X i => x i
  | .Y => y
  | .L => l

theorem init_eq {ι : Type} [Fintype ι] [DecidableEq ι] (C : FunCRN (Sp ι) ι) (hX : C.X = Sp.X)
    (hL : C.L = some Sp.L) (x : ι → ℕ) : C.init x = mk x 0 1 := by
  funext s
  cases s with
  | X i =>
    have := C.inputConf_X x i
    rw [hX] at this
    rw [FunCRN.init, Pi.add_apply, this]
    simp [FunCRN.leaderConf, hL, mk]
  | Y => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, hX, hL, mk]
  | L => simp [FunCRN.init, FunCRN.leaderConf, FunCRN.inputConf, hX, hL, mk]

/-- Stable computation from an inductive invariant `G x` of the configurations reachable from
`I_x`, from each of which a terminal configuration with output `f x` is reachable. -/
theorem stablyComputes_of_inv {S ι : Type} [DecidableEq S] [Fintype ι] (C : FunCRN S ι)
    (f : (ι → ℕ) → ℕ) (G : (ι → ℕ) → Config S → Prop) (hinit : ∀ x, G x (C.init x))
    (hstep : ∀ x D D', G x D → C.Step D D' → G x D')
    (hfin : ∀ x D, G x D → ∃ O, C.Reach D O ∧ O C.Y = f x ∧ C.Terminal O) :
    C.StablyComputes f := by
  intro x D hD
  have hG : G x D := by
    induction hD with
    | refl => exact hinit x
    | tail _ hs ih => exact hstep x _ _ ih hs
  obtain ⟨O, hO, hY, hT⟩ := hfin x D hG
  exact ⟨O, hO, hY, fun D' hD' => by rw [hT.reach_eq hD']⟩

/-! ### Minimum: `X₁ + … + X_k → Y` -/

section Min

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The reaction `X₁ + … + X_k → Y`. -/
def minR : Reaction (Sp κ) where
  reactants := mk (fun _ => 1) 0 0
  products := mk 0 1 0

/-- The CRN `{X₁ + … + X_k → Y}` with an unused leader. -/
def minCRN : FunCRN (Sp κ) κ where
  reactions := {minR}
  finite := Set.finite_singleton _
  X := .X
  Y := .Y
  L := some .L
  X_injective _ _ h := by cases h; rfl
  Y_ne_X _ := by simp
  L_ne_X := by simp
  L_ne_Y := by simp

/-- The configuration after the reaction fired `m` times. -/
def minGood (x : κ → ℕ) (m : ℕ) : Config (Sp κ) := mk (fun k => x k - m) m 1

theorem minR_apply {x : κ → ℕ} {m : ℕ} (hm : ∀ k, m < x k) :
    minGood x m - minR.reactants + minR.products = minGood x (m + 1) := by
  funext s
  cases s with
  | X k => have := hm k; simp [minGood, minR, mk]; omega
  | Y => simp [minGood, minR, mk]
  | L => simp [minGood, minR, mk]

theorem minCRN_step {x : κ → ℕ} {m : ℕ} {D : Config (Sp κ)}
    (h : (minCRN (κ := κ)).Step (minGood x m) D) : (∀ k, m < x k) ∧ D = minGood x (m + 1) := by
  obtain ⟨ρ, hρ, hle, rfl⟩ := h
  have hρ' : ρ = minR := hρ
  subst hρ'
  have hm : ∀ k, m < x k := fun k => by
    have := hle (.X k)
    simp [minGood, minR, mk] at this
    omega
  exact ⟨hm, minR_apply hm⟩

theorem minCRN_reach {x : κ → ℕ} (d : ℕ) {m : ℕ} (hm : ∀ k, m + d ≤ x k) :
    (minCRN (κ := κ)).Reach (minGood x m) (minGood x (m + d)) := by
  induction d with
  | zero => exact CRN.Reach.refl _
  | succ d ih =>
    have hm' : ∀ k, m + d < x k := fun k => by have := hm k; omega
    refine (ih fun k => (hm' k).le).tail ⟨minR, rfl, fun s => ?_, (minR_apply hm').symm⟩
    cases s with
    | X k => have := hm' k; simp [minGood, minR, mk]; omega
    | Y => simp [minGood, minR, mk]
    | L => simp [minGood, minR, mk]

theorem minCRN_stablyComputes [Nonempty κ] :
    (minCRN (κ := κ)).StablyComputes (fun y => Finset.univ.inf' Finset.univ_nonempty y) := by
  refine stablyComputes_of_inv _ _ (fun x D => ∃ m, (∀ k, m ≤ x k) ∧ D = minGood x m)
    (fun x => ⟨0, fun _ => Nat.zero_le _, ?_⟩) ?_ ?_
  · rw [init_eq minCRN rfl rfl]; funext s; cases s <;> simp [minGood, mk]
  · rintro x D D' ⟨m, -, rfl⟩ hs
    obtain ⟨hm, rfl⟩ := minCRN_step hs
    exact ⟨m + 1, hm, rfl⟩
  · rintro x D ⟨m, hm, rfl⟩
    set M := Finset.univ.inf' Finset.univ_nonempty x with hM
    have hle : ∀ k, M ≤ x k := fun k => Finset.inf'_le _ (Finset.mem_univ k)
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := κ)) x
    have hmM : m ≤ M := (Finset.le_inf'_iff _ _).mpr fun k _ => hm k
    refine ⟨minGood x M, ?_, rfl, ?_⟩
    · have := minCRN_reach (x := x) (m := m) (M - m) (fun k => by have := hle k; omega)
      rwa [Nat.add_sub_cancel' hmM] at this
    · rintro ρ hρ hρle
      have hρ' : ρ = minR := hρ
      subst hρ'
      have := hρle (.X k₀)
      simp [minGood, minR, mk, ← hM, ← hk₀] at this

theorem minCRN_outputOblivious : (minCRN (κ := κ)).OutputOblivious := by
  rintro ρ hρ
  have hρ' : ρ = minR := hρ
  subst hρ'
  rfl

end Min

/-! ### The gadget `a + 1{w > j} · b`: `A → Y`, `(j+1) W + B → (j+1) W + Y` -/

section AddIte

variable (j : ℕ)

/-- The reaction `A → Y` (`A = X 0`). -/
def aR : Reaction (Sp (Fin 3)) where
  reactants := Pi.single (.X 0) 1
  products := Pi.single .Y 1

/-- The catalytic reaction `(j+1) W + B → (j+1) W + Y` (`B = X 1`, `W = X 2`). -/
def bR : Reaction (Sp (Fin 3)) where
  reactants := Pi.single (.X 2) (j + 1) + Pi.single (.X 1) 1
  products := Pi.single (.X 2) (j + 1) + Pi.single .Y 1

/-- The CRN `{A → Y, (j+1) W + B → (j+1) W + Y}` with an unused leader. -/
def iteCRN : FunCRN (Sp (Fin 3)) (Fin 3) where
  reactions := {aR, bR j}
  finite := (Set.finite_singleton _).insert _
  X := .X
  Y := .Y
  L := some .L
  X_injective _ _ h := by cases h; rfl
  Y_ne_X _ := by simp
  L_ne_X := by simp
  L_ne_Y := by simp

/-- The configuration after `A → Y` fired `p` times and the catalytic reaction `q` times. -/
def iteGood (z : Fin 3 → ℕ) (p q : ℕ) : Config (Sp (Fin 3)) :=
  mk (fun i => z i - ![p, q, 0] i) (p + q) 1

variable {j}

theorem aR_apply {z : Fin 3 → ℕ} {p q : ℕ} :
    iteGood z p q - aR.reactants + aR.products = iteGood z (p + 1) q := by
  funext s
  cases s with
  | X i => fin_cases i <;> simp [iteGood, aR, mk, Nat.sub_sub]
  | Y => simp [iteGood, aR, mk]; omega
  | L => simp [iteGood, aR, mk]

theorem aR_le {z : Fin 3 → ℕ} {p q : ℕ} (hp : p < z 0) : aR.reactants ≤ iteGood z p q := by
  intro s
  cases s with
  | X i => fin_cases i <;> simp [iteGood, aR, mk]; omega
  | Y => simp [aR]
  | L => simp [aR]

theorem bR_apply {z : Fin 3 → ℕ} {p q : ℕ} (hw : j < z 2) :
    iteGood z p q - (bR j).reactants + (bR j).products = iteGood z p (q + 1) := by
  funext s
  cases s with
  | X i => fin_cases i <;> simp [iteGood, bR, mk] <;> omega
  | Y => simp [iteGood, bR, mk]; omega
  | L => simp [iteGood, bR, mk]

theorem bR_le {z : Fin 3 → ℕ} {p q : ℕ} (hq : q < z 1) (hw : j < z 2) :
    (bR j).reactants ≤ iteGood z p q := by
  intro s
  cases s with
  | X i => fin_cases i <;> simp [iteGood, bR, mk] <;> omega
  | Y => simp [bR]
  | L => simp [bR]

/-- The invariant of the reachable configurations. -/
def iteInv (j : ℕ) (z : Fin 3 → ℕ) (D : Config (Sp (Fin 3))) : Prop :=
  ∃ p q, p ≤ z 0 ∧ q ≤ z 1 ∧ (0 < q → j < z 2) ∧ D = iteGood z p q

theorem iteCRN_step {z : Fin 3 → ℕ} {D D' : Config (Sp (Fin 3))} (hD : iteInv j z D)
    (hs : (iteCRN j).Step D D') : iteInv j z D' := by
  obtain ⟨p, q, hp, hq, hw, rfl⟩ := hD
  obtain ⟨ρ, hρ, hle, rfl⟩ := hs
  rcases hρ with rfl | hρ
  · have := hle (.X 0)
    simp [iteGood, aR, mk] at this
    exact ⟨p + 1, q, by omega, hq, hw, aR_apply⟩
  · have hρ' : ρ = bR j := hρ
    subst hρ'
    have h1 := hle (.X 1)
    have h2 := hle (.X 2)
    simp [iteGood, bR, mk] at h1 h2
    exact ⟨p, q + 1, hp, by omega, fun _ => by omega, bR_apply (by omega)⟩

theorem iteCRN_reach_a {z : Fin 3 → ℕ} {p q : ℕ} (d : ℕ) (hp : p + d ≤ z 0) :
    (iteCRN j).Reach (iteGood z p q) (iteGood z (p + d) q) := by
  induction d with
  | zero => exact CRN.Reach.refl _
  | succ d ih =>
    have h1 : p + d < z 0 := by omega
    exact (ih h1.le).tail ⟨aR, .inl rfl, aR_le h1, aR_apply.symm⟩

theorem iteCRN_reach_b {z : Fin 3 → ℕ} {p q : ℕ} (d : ℕ) (hq : q + d ≤ z 1) (hw : j < z 2) :
    (iteCRN j).Reach (iteGood z p q) (iteGood z p (q + d)) := by
  induction d with
  | zero => exact CRN.Reach.refl _
  | succ d ih =>
    have h1 : q + d < z 1 := by omega
    exact (ih h1.le).tail ⟨bR j, .inr rfl, bR_le h1 hw, (bR_apply hw).symm⟩

theorem iteCRN_terminal (z : Fin 3 → ℕ) :
    (iteCRN j).Terminal (iteGood z (z 0) (if j < z 2 then z 1 else 0)) := by
  rintro ρ hρ hle
  rcases hρ with rfl | hρ
  · have := hle (.X 0)
    simp [iteGood, aR, mk] at this
  · have hρ' : ρ = bR j := hρ
    subst hρ'
    have h1 := hle (.X 1)
    have h2 := hle (.X 2)
    simp [iteGood, bR, mk] at h1 h2
    split_ifs at h1 h2 with hw <;> omega

theorem iteCRN_stablyComputes :
    (iteCRN j).StablyComputes (fun z => z 0 + if j < z 2 then z 1 else 0) := by
  refine stablyComputes_of_inv _ _ (iteInv j)
    (fun z => ⟨0, 0, Nat.zero_le _, Nat.zero_le _, by simp, ?_⟩)
    (fun z D D' hD hs => iteCRN_step hD hs) ?_
  · rw [init_eq (iteCRN j) rfl rfl]; funext s
    cases s with
    | X i => fin_cases i <;> simp [iteGood, mk]
    | Y => simp [iteGood, mk]
    | L => simp [iteGood, mk]
  · rintro z D ⟨p, q, hp, hq, hw, rfl⟩
    refine ⟨_, ?_, ?_, iteCRN_terminal z⟩
    · have ha := iteCRN_reach_a (j := j) (q := q) (z 0 - p) (by omega : p + (z 0 - p) ≤ z 0)
      rw [Nat.add_sub_cancel' hp] at ha
      refine ha.trans ?_
      by_cases hjw : j < z 2
      · have hb := iteCRN_reach_b (j := j) (p := z 0) (z 1 - q)
          (by omega : q + (z 1 - q) ≤ z 1) hjw
        rw [Nat.add_sub_cancel' hq] at hb
        simpa [hjw] using hb
      · have : q = 0 := by by_contra h; exact hjw (hw (by omega))
        subst this
        simpa [hjw] using CRN.Reach.refl _
    · simp [iteGood, mk, iteCRN]

theorem iteCRN_outputOblivious : (iteCRN j).OutputOblivious := by
  rintro ρ hρ
  rcases hρ with rfl | hρ
  · simp [aR, iteCRN]
  · have hρ' : ρ = bR j := hρ
    subst hρ'
    simp [bR, iteCRN]

end AddIte

end Gadgets

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Constants are obliviously-computable (used in §6, proof of Lemma 6.2). -/
theorem obliviouslyComputable_const (c : ℕ) : ObliviouslyComputable (fun _ : ι → ℕ => c) :=
  obliviouslyComputable_of_automaton (Q := Unit) _ (fun _ => ()) (fun _ _ => le_rfl)
    (fun _ _ _ _ => ⟨rfl, rfl⟩)

/-- Projections `x ↦ x i` are obliviously-computable (used in §6, proof of Lemma 6.2). -/
theorem obliviouslyComputable_proj (i : ι) : ObliviouslyComputable (fun x : ι → ℕ => x i) :=
  obliviouslyComputable_of_automaton (Q := Unit) _ (fun _ => ())
    (fun c k => by simp)
    (fun c c' _ k => ⟨by simp, rfl⟩)

/-- `x ↦ x i - n` (truncated subtraction) is obliviously-computable (used in §6, proof of
Lemma 6.2). -/
theorem obliviouslyComputable_sub_const (i : ι) (n : ℕ) :
    ObliviouslyComputable (fun x : ι → ℕ => x i - n) := by
  refine obliviouslyComputable_of_automaton (Q := Fin (n + 1)) _
    (fun x => ⟨min (x i) n, by omega⟩) (fun c k => ?_) (fun c c' hcc' k => ?_)
  · by_cases hk : k = i
    · subst hk; simp; omega
    · simp [Ne.symm hk]
  · have h' : min (c i) n = min (c' i) n := congrArg Fin.val hcc'
    by_cases hk : k = i
    · subst hk
      refine ⟨by simp; omega, Fin.ext ?_⟩
      simp; omega
    · simp [Ne.symm hk, h']

/-- The `k`-ary minimum is obliviously-computable, by the reaction `X₁ + … + X_k → Y`
(§6, proof of Lemma 6.2). -/
theorem obliviouslyComputable_min {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ] :
    ObliviouslyComputable (fun y : κ → ℕ => Finset.univ.inf' Finset.univ_nonempty y) :=
  ⟨Gadgets.Sp κ, inferInstance, inferInstance, Gadgets.minCRN, rfl,
    Gadgets.minCRN_outputOblivious, Gadgets.minCRN_stablyComputes⟩

/-- The gadget `c(a, b, w) = a + 1{w > j} · b` of §6 (proof of Lemma 6.2) is
obliviously-computable, by the reactions `A → Y` and `(j+1) W + B → (j+1) W + Y`. -/
theorem obliviouslyComputable_add_ite (j : ℕ) :
    ObliviouslyComputable (fun z : Fin 3 → ℕ => z 0 + if j < z 2 then z 1 else 0) :=
  ⟨Gadgets.Sp (Fin 3), inferInstance, inferInstance, Gadgets.iteCRN j, rfl,
    Gadgets.iteCRN_outputOblivious, Gadgets.iteCRN_stablyComputes⟩

end Podc.ComposableCRN
