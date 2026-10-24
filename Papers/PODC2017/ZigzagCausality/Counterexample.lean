import Papers.PODC2017.ZigzagCausality.Zigzag

/-!
# Theorem 4 (Visible Zigzag Theorem), necessity direction, is false

The network has four processes `i = 0`, `j = 1`, `k = 2`, `l = 3` and channels
`i → j`, `i → k`, `k → j`, `j → l`; all lower bounds are `1`, and
`U_ij = 2`, `U_ik = 1`, `U_kj = 1`, `U_jl = 2`. Processes follow a flooding full-information
protocol. Let `s` be a non-initial `i`-node (e.g. `i` received an external message) and
`θ₁ = ⟨s, i j l⟩`, `θ₂ = ⟨s, i k j l⟩`.

* `knows_prec` — in every run in which `s` appears, `timer(θ₁) ≤ timer(θ₂)`: the chain
  `i → k → j` reaches `j` exactly 2 time units after `s`, the direct message `i → j` after 1 or 2.
  If both arrive at the same time they arrive at the *same* `j`-node, so `θ₁ = θ₂`; otherwise
  `θ₁ ≤ s + 3 ≤ θ₂`. Hence `(R, r) ⊨ K_s(θ₁ --0--> θ₂)`.
* `wtZ_le_of_visible` — every `s`-visible zigzag pattern from `θ₁` to `θ₂` (in any run) has weight
  `≤ -1`: all its forks are rooted at `i`-nodes (the past of `s` contains only `i`-nodes, as `i` has
  no incoming channel), and the potential `φ⟨ρ, q⟩ = timer(ρ) + τ(q)` with
  `τ(ij) = 2, τ(ik) = 1, τ(ikj) = 2, τ(ijl) = 4, τ(ikjl) = 3` bounds every fork and junction.
* `theorem_4_necessity_false` — the counterexample, with a concrete run.

The knowledge comes from a case split over runs (the two chains merge at `j` or not), and neither
case yields a visible zigzag: the "`+1`" of non-joined forks at `j` is not observable by `s`.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

namespace Counterexample

open Sys

/-- Channels `0 → 1`, `0 → 2`, `2 → 1`, `1 → 3`. -/
def ch : Fin 4 → Fin 4 → Bool
  | 0, 1 => true
  | 0, 2 => true
  | 2, 1 => true
  | 1, 3 => true
  | _, _ => false

/-- Upper bounds: `U₀₁ = 2`, `U₁₃ = 2`, all others `1`. -/
def ub : Fin 4 → Fin 4 → ℕ
  | 0, 1 => 2
  | 1, 3 => 2
  | _, _ => 1

/-- The network. -/
def net : Net (Fin 4) where
  Chan i j := ch i j = true
  L _ _ := 1
  U := ub
  one_le_L _ _ _ := le_rfl
  L_le_U i j _ := by fin_cases i <;> fin_cases j <;> decide

/-- Local states of the counterexample (initial states and external messages are `Unit`, message
contents are natural numbers). -/
abbrev LS := LState (Fin 4) Unit ℕ Unit

instance : Countable LS := by
  refine Function.Injective.countable
    (f := fun ℓ : LS => (ℓ.init, ℓ.hist.map fun b => (b.msgs, b.ext))) ?_
  rintro ⟨a, h⟩ ⟨a', h'⟩ he
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, he⟩ := he
  have ha : a = a' := Subsingleton.elim _ _
  subst ha
  have : h = h' := by
    refine List.map_injective_iff.2 ?_ he
    rintro ⟨m, e⟩ ⟨m', e'⟩ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl
  rw [this]

/-- An injective encoding of local states into message contents. -/
noncomputable def enc : LS → ℕ := Classical.choose (Countable.exists_injective_nat LS)

theorem enc_injective : Function.Injective enc :=
  Classical.choose_spec (Countable.exists_injective_nat LS)

/-- The flooding full-information protocol on `net`. -/
noncomputable def γ : Sys (Fin 4) Unit ℕ Unit where
  net := net
  send i ℓ j := if ch i j = true then some (enc ℓ) else none
  G0 := Set.univ

theorem isFFIP : γ.IsFFIP := by
  refine ⟨?_, ?_⟩
  · intro i j j' ℓ ℓ' m h h'
    simp only [γ] at h h'
    split_ifs at h h'
    cases h; exact enc_injective (Option.some.inj h'.symm |>.symm ▸ rfl)
  · intro i ℓ j hc
    simp only [γ]
    rw [if_pos (show ch i j = true from hc)]; rfl

abbrev BN := BNode (Fin 4) Unit ℕ Unit
abbrev GN := GNode (Fin 4) Unit ℕ Unit

/-- `θ₁ = ⟨s, i j l⟩`. -/
def θ₁ (s : BN) : GN := ⟨s, [1, 3]⟩
/-- `θ₂ = ⟨s, i k j l⟩`. -/
def θ₂ (s : BN) : GN := ⟨s, [2, 1, 3]⟩

variable {r : Sched (Fin 4) Unit Unit}

/-- In a run, a non-initial node sends along each channel; delivery within the bounds. -/
theorem exists_recv (hr : γ.Valid r) {σ : BN} (ha : γ.appears r σ) (h0 : 0 < γ.timer r σ)
    {j : Fin 4} (hc : ch σ.1 j = true) : ∃ σ', γ.recv r σ j = some σ' ∧ σ'.1 = j ∧
      γ.appears r σ' ∧ γ.timer r σ + 1 ≤ γ.timer r σ' ∧
      γ.timer r σ' ≤ γ.timer r σ + ub σ.1 j := by
  obtain ⟨σ', h⟩ := Option.isSome_iff_exists.1 (recv_isSome_of_FFIP isFFIP ha h0 hc)
  have := recv_spec hr h
  exact ⟨σ', h, this.1, this.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem gbasic_one {σ σ' : BN} {j : Fin 4} (h : γ.recv r σ j = some σ') (ha : γ.appears r σ') :
    γ.gbasic r σ [j] = some σ' := by
  simp [h, ha]

/-- In every run in which the non-initial `i`-node `s` appears, `timer(θ₁) ≤ timer(θ₂)`. -/
theorem prec_of_appears {s : BN} (hs : s.1 = 0) (hr : γ.Valid r) (ha : γ.appears r s)
    (h0 : 0 < γ.timer r s) : γ.Prec r (θ₁ s) 0 (θ₂ s) := by
  obtain ⟨J, hJ, pJ, aJ, J1, J2⟩ := exists_recv hr ha h0 (j := 1) (by rw [hs]; rfl)
  obtain ⟨K, hK, pK, aK, K1, K2⟩ := exists_recv hr ha h0 (j := 2) (by rw [hs]; rfl)
  obtain ⟨KJ, hKJ, pKJ, aKJ, KJ1, KJ2⟩ := exists_recv hr aK (by omega) (j := 1) (by rw [pK]; rfl)
  obtain ⟨JL, hJL, pJL, aJL, JL1, JL2⟩ := exists_recv hr aJ (by omega) (j := 3) (by rw [pJ]; rfl)
  obtain ⟨KJL, hKJL, pKJL, aKJL, KJL1, KJL2⟩ :=
    exists_recv hr aKJ (by omega) (j := 3) (by rw [pKJ]; rfl)
  rw [hs] at J2 K2
  rw [pK] at KJ2
  rw [pJ] at JL2
  simp only [ub] at J2 K2 KJ2 JL2
  refine ⟨JL, KJL, ?_, ?_, ?_⟩
  · simp [basic, θ₁, hJ, hJL, aJL]
  · simp [basic, θ₂, hK, hKJ, hKJL, aKJL]
  · by_cases hJt : γ.timer r J = γ.timer r s + 2
    · have hJKJ : J = KJ := γ.eq_of_timer_eq r (by rw [pJ, pKJ]) aJ aKJ (by omega)
      subst hJKJ
      rw [hJL] at hKJL; cases hKJL
      simp
    · omega

/-- **The knowledge part of the counterexample**: `(R, r) ⊨ K_s(θ₁ --0--> θ₂)`. -/
theorem knows_prec {s : BN} (hs : s.1 = 0) (hne : s.2.hist ≠ []) :
    γ.Knows s (fun r' => γ.Prec r' (θ₁ s) 0 (θ₂ s)) := by
  intro r' hr' ha
  exact prec_of_appears hs hr' ha ((γ.timer_pos_iff r' ha).2 hne)

/-! ### No visible zigzag of weight `≥ 0` -/

/-- The past of an `i`-node (`i = 0`) contains only `i`-nodes: `i` has no incoming channel. -/
theorem HBStep_proc {b c : BN} (h : γ.HBStep r b c) (hc : c.1 = 0) : b.1 = 0 := by
  rcases h with ⟨-, -, he, -⟩ | ⟨j, hj⟩
  · rw [he, hc]
  · obtain ⟨⟨-, hch, -⟩, rfl⟩ := (γ.recv_eq_some r).1 hj
    simp only at hc
    subst hc
    change ch b.1 0 = true at hch
    revert hch; generalize b.1 = a; fin_cases a <;> decide

theorem HB_proc {τ σ : BN} (h : γ.HB r τ σ) (hσ : σ.1 = 0) : τ.1 = 0 := by
  induction h with
  | single hab => exact HBStep_proc hab hσ
  | tail _ hbc ih => exact ih (HBStep_proc hbc hσ)

/-- Channel paths. -/
def cp : Fin 4 → List (Fin 4) → Bool
  | _, [] => true
  | i, j :: q => ch i j && cp j q

theorem gbasic_cp {ρ τ : BN} {q : List (Fin 4)} (h : γ.gbasic r ρ q = some τ) :
    cp ρ.1 q = true := by
  induction q generalizing ρ with
  | nil => rfl
  | cons j q ih =>
    simp only [gbasic_cons] at h
    obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨-, hch, -⟩, rfl⟩ := (γ.recv_eq_some r).1 h1
    simp only [cp, Bool.and_eq_true]
    exact ⟨hch, ih h2⟩

/-- The six channel paths starting at `i`. -/
def S6 : List (List (Fin 4)) := [[], [1], [2], [2, 1], [1, 3], [2, 1, 3]]

theorem cp3 : ∀ q, cp 3 q = true → q = []
  | [], _ => rfl
  | a :: q, h => by
    simp only [cp, Bool.and_eq_true] at h
    revert h; fin_cases a <;> simp [ch]

theorem cp1 : ∀ q, cp 1 q = true → q = [] ∨ q = [3]
  | [], _ => Or.inl rfl
  | a :: q, h => by
    simp only [cp, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    fin_cases a <;> simp [ch] at h1
    simp [cp3 q h2]

theorem cp2 : ∀ q, cp 2 q = true → q = [] ∨ q = [1] ∨ q = [1, 3]
  | [], _ => Or.inl rfl
  | a :: q, h => by
    simp only [cp, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    fin_cases a <;> simp [ch] at h1
    rcases cp1 q h2 with rfl | rfl <;> simp

theorem cp0 : ∀ q, cp 0 q = true → q ∈ S6
  | [], _ => by simp [S6]
  | a :: q, h => by
    simp only [cp, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    fin_cases a <;> simp [ch] at h1
    · rcases cp1 q h2 with rfl | rfl <;> simp [S6]
    · rcases cp2 q h2 with rfl | rfl | rfl <;> simp [S6]

theorem S6_len : ∀ q ∈ S6, q.length ≤ 3 := by decide

/-- The potential on paths from `i`: a timing of the path tree that respects all bounds, in
which the two chains reach `j` at the same time without merging. -/
def τ : List (Fin 4) → ℤ
  | [1] => 2
  | [2] => 1
  | [2, 1] => 2
  | [1, 3] => 4
  | [2, 1, 3] => 3
  | _ => 0

theorem τ_split : ∀ q ∈ S6, ∀ n ∈ List.range 4,
    (net.Lp (lastP 0 (q.take n)) (q.drop n) : ℤ) ≤ τ q - τ (q.take n) ∧
      τ q - τ (q.take n) ≤ net.Up (lastP 0 (q.take n)) (q.drop n) := by
  decide

/-- The potential `φ⟨ρ, q⟩ = timer(ρ) + τ(q)`. -/
noncomputable def φ (r : Sched (Fin 4) Unit Unit) (θ : GN) : ℤ := γ.timer r θ.root + τ θ.path

theorem fork_bound {F : Fork (Fin 4) Unit ℕ Unit} (hF : γ.ForkIn r F) (h0 : F.base.root.1 = 0) :
    F.wt γ.net ≤ φ r F.head - φ r F.tail := by
  obtain ⟨σh, hh⟩ := Option.isSome_iff_exists.1 hF.1
  obtain ⟨σt, ht⟩ := Option.isSome_iff_exists.1 hF.2
  have c1 := gbasic_cp hh
  have c2 := gbasic_cp ht
  simp only [Fork.head, Fork.tail, GNode.ext_root, GNode.ext_path, h0] at c1 c2
  have m1 := cp0 _ c1
  have m2 := cp0 _ c2
  have l1 := S6_len _ m1
  have s1 := τ_split _ m1 F.base.path.length (List.mem_range.2 (by simp at l1; omega))
  have s2 := τ_split _ m2 F.base.path.length (List.mem_range.2 (by simp at l1; omega))
  simp only [List.take_left', List.drop_left'] at s1 s2
  simp only [Fork.wt, φ, Fork.head, Fork.tail, GNode.ext_root, GNode.ext_path, GNode.proc, h0]
  change (net.Lp _ _ : ℤ) - net.Up _ _ ≤ _
  omega

theorem S6_lastP : ∀ q ∈ S6, lastP 0 q = 0 → q = [] := by decide

theorem path_nil {θ : GN} {σ : BN} (h : γ.basic r θ = some σ) (hσ : σ.1 = 0)
    (hθ : θ.root.1 = 0) : θ.path = [] ∧ σ = θ.root := by
  have hc := gbasic_cp h
  rw [hθ] at hc
  have hp := γ.basic_proc r h
  rw [hσ, GNode.proc, hθ] at hp
  have hnil := S6_lastP _ (cp0 _ hc) hp.symm
  refine ⟨hnil, ?_⟩
  simp only [basic, hnil, gbasic_nil] at h
  split_ifs at h; cases h; rfl

theorem visible_root {s : BN} :
    ∀ {Z : List (Fork (Fin 4) Unit ℕ Unit)} {F}, γ.Visible r s (F :: Z) → γ.HB r F.base.root s
  | [], _, h => h
  | _ :: _, F, ⟨⟨τ, hτ, hHB⟩, _⟩ => (HB.of_gbasic (q := F.head.path) hτ).trans hHB

/-- Junctions of an `s`-visible zigzag are bounded by the potential. -/
theorem gap_bound {s : BN} (hs : s.1 = 0) {θ θ' : GN} {τ' : BN} (hτ : γ.basic r θ = some τ')
    (hHB : γ.HB r τ' s) (h0 : θ.root.1 = 0) (h0' : θ'.root.1 = 0) (hadj : γ.Adj r θ θ') :
    γ.gap r θ θ' ≤ φ r θ' - φ r θ := by
  obtain ⟨σ, σ', h1, h2, hp, ht⟩ := hadj
  rw [hτ] at h1; cases h1
  have hσ := HB_proc hHB hs
  obtain ⟨n1, e1⟩ := path_nil hτ hσ h0
  obtain ⟨n2, e2⟩ := path_nil h2 (hp ▸ hσ) h0'
  subst e1 e2
  simp only [φ, n1, n2]
  rw [gap, hτ, h2]
  split_ifs with he
  · rw [Option.some.inj he]; simp [τ]
  · have hne : θ.root ≠ θ'.root := fun e => he (by rw [e])
    have := γ.timer_lt_of_ne r hp (gbasic_appears γ r hτ).2 (gbasic_appears γ r h2).2 ht hne
    simp [τ]; omega

/-- Every `s`-visible zigzag pattern from `θ` to `θ'` has weight at most `φ θ' - φ θ`. -/
theorem wtZ_le_of_visible {s : BN} (hs : s.1 = 0) :
    ∀ {Z : List (Fork (Fin 4) Unit ℕ Unit)} {θ θ' : GN}, γ.IsZigzag r Z θ θ' →
      γ.Visible r s Z → γ.wtZ r Z ≤ φ r θ' - φ r θ
  | [], _, _, h, _ => h.elim
  | [F], _, _, ⟨hF, rfl, rfl⟩, hV => fork_bound hF (HB_proc hV hs)
  | F :: G :: Z, _, _, ⟨hF, rfl, hadj, hZ⟩, hV => by
      have hV' := hV
      obtain ⟨⟨τ', hτ, hHB⟩, hV⟩ := hV
      have r0 : F.base.root.1 = 0 := HB_proc (visible_root hV') hs
      have r1 : G.base.root.1 = 0 := HB_proc (visible_root hV) hs
      have b1 := fork_bound hF r0
      have b2 := gap_bound hs hτ hHB (θ' := G.tail) r0 r1 hadj
      have b3 := wtZ_le_of_visible hs hZ hV
      simp only [wtZ]
      omega

/-- No `s`-visible zigzag from `θ₁` to `θ₂` has weight `≥ 0` (in any run). -/
theorem no_visible_zigzag {s : BN} (hs : s.1 = 0) :
    ¬ ∃ Z, γ.IsZigzag r Z (θ₁ s) (θ₂ s) ∧ γ.Visible r s Z ∧ 0 ≤ γ.wtZ r Z := by
  rintro ⟨Z, hZ, hV, hw⟩
  have := wtZ_le_of_visible hs hZ hV
  simp [φ, θ₁, θ₂, τ] at this
  omega

/-! ### A concrete run -/

/-- The run: `i` receives an external message at time `1`; every message is delivered after one
time unit. -/
def r₀ : Sched (Fin 4) Unit Unit where
  g _ := ()
  dlv _ s _ := s + 1
  ext t p := if t = 1 ∧ p = 0 then {()} else ∅

theorem valid_r₀ : γ.Valid r₀ where
  init := Set.mem_univ _
  bounds i s j h := by
    have hc : ch i j = true := h.2.1
    refine ⟨le_rfl, ?_⟩
    change s + 1 ≤ s + ub i j
    have : 1 ≤ ub i j := by revert hc; fin_cases i <;> fin_cases j <;> decide
    omega
  ext_unique e t j t' j' h h' := by
    simp only [r₀] at h h'
    split_ifs at h h' with h1 h2 <;> simp_all

/-- The node `s`: process `i` after receiving the external message. -/
noncomputable def s₀ : BN := (0, γ.st r₀ 1 0)

theorem s₀_hist : s₀.2.hist ≠ [] := by
  have ha : γ.Active r₀ 0 (0 + 1) := by
    rw [active_succ_iff]
    rintro ⟨-, he⟩
    rw [batch_ext] at he
    simp [r₀] at he
  simp [s₀, γ.st_succ_of_active r₀ ha]

/-- The statement of **Theorem 4 (Visible Zigzag Theorem)** for a system `γ`: for every basic node
`σ` of a run `r` and σ-recognized nodes `θ₁, θ₂` of `r` with positive times,
`(R, r) ⊨ K_σ(θ₁ --x--> θ₂)` iff there is a σ-visible zigzag pattern from `θ₁` to `θ₂` in `r` of
weight `≥ x`. -/
def VisibleZigzagStatement {P S M E : Type*} [Finite P] (γ : Sys P S M E) : Prop :=
  ∀ (r : Sched P S E) (σ : BNode P S M E) (θ₁ θ₂ : GNode P S M E) (x : ℤ), γ.Valid r →
    γ.appears r σ → γ.Recognized r σ θ₁ → γ.Recognized r σ θ₂ → γ.appearsG r θ₁ →
    γ.appearsG r θ₂ → 0 < γ.timerG r θ₁ → 0 < γ.timerG r θ₂ →
    (γ.Knows σ (fun r' => γ.Prec r' θ₁ x θ₂) ↔
      ∃ Z, γ.IsZigzag r Z θ₁ θ₂ ∧ γ.Visible r σ Z ∧ x ≤ γ.wtZ r Z)

/-- **Theorem 4 is false** (its "only if" direction): in the flooding full-information system
`γ`, in the run `r₀`, `K_s(θ₁ --0--> θ₂)` holds at `s = s₀` but no `s`-visible zigzag pattern
from `θ₁` to `θ₂` has weight `≥ 0`. -/
theorem theorem_4_counterexample :
    γ.IsFFIP ∧ γ.Valid r₀ ∧ γ.appears r₀ s₀ ∧
    γ.Recognized r₀ s₀ (θ₁ s₀) ∧ γ.Recognized r₀ s₀ (θ₂ s₀) ∧
    γ.appearsG r₀ (θ₁ s₀) ∧ γ.appearsG r₀ (θ₂ s₀) ∧
    0 < γ.timerG r₀ (θ₁ s₀) ∧ 0 < γ.timerG r₀ (θ₂ s₀) ∧
    γ.Knows s₀ (fun r' => γ.Prec r' (θ₁ s₀) 0 (θ₂ s₀)) ∧
    ¬ ∃ Z, γ.IsZigzag r₀ Z (θ₁ s₀) (θ₂ s₀) ∧ γ.Visible r₀ s₀ Z ∧ 0 ≤ γ.wtZ r₀ Z := by
  have ha : γ.appears r₀ s₀ := γ.appears_st r₀ 1 0
  have h0 : 0 < γ.timer r₀ s₀ := (γ.timer_pos_iff r₀ ha).2 s₀_hist
  obtain ⟨σ₁, σ₂, h1, h2, -⟩ := prec_of_appears rfl valid_r₀ ha h0
  have t1 : γ.timer r₀ s₀ ≤ γ.timer r₀ σ₁ := (HB.of_gbasic h1).timer_le valid_r₀
  have t2 : γ.timer r₀ s₀ ≤ γ.timer r₀ σ₂ := (HB.of_gbasic h2).timer_le valid_r₀
  refine ⟨isFFIP, valid_r₀, ha, HB.refl ha, HB.refl ha, by simp [appearsG, h1],
    by simp [appearsG, h2], ?_, ?_, knows_prec rfl s₀_hist, no_visible_zigzag rfl⟩
  · rw [γ.timerG_of_basic r₀ h1]; omega
  · rw [γ.timerG_of_basic r₀ h2]; omega

/-- **Theorem 4 (Visible Zigzag Theorem) is false** for flooding full-information protocols. -/
theorem theorem_4_false : ∃ γ : Sys (Fin 4) Unit ℕ Unit, γ.IsFFIP ∧ ¬ VisibleZigzagStatement γ := by
  refine ⟨γ, isFFIP, fun H => ?_⟩
  obtain ⟨-, hr, ha, hR1, hR2, a1, a2, t1, t2, hK, hZ⟩ := theorem_4_counterexample
  exact hZ ((H r₀ s₀ _ _ 0 hr ha hR1 hR2 a1 a2 t1 t2).1 hK)

end Counterexample

end Podc.ZigzagCausality
