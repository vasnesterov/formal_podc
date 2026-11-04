import Papers.PODC2013.IncentiveTrees.TDRM
import Papers.PODC2013.IncentiveTrees.CDRM

/-!
# Theorem 4: TDRM satisfies every property except UGSA

The heart is USA (`tdrm_USA`).  Instead of the paper's "optimal partition" argument
(Lemmas 1–5), we prove by induction over the Sybil forest the invariant `sybil_bound`:
for a Sybil tree `s` of total Sybil contribution `m`, real attached weight `E`, and any
"ancestor weight" `α ≤ G(ℓ)` coming from Sybil ancestors of total contribution `ℓ`,
`V(s) + a α W(s) ≤ Q(m) + a α G(m) + a E G(m + ℓ)`,
where `V(s)` is the (scaled) total reward of the Sybils of `s`.  The right-hand side at
`α = ℓ = 0` is exactly the reward of the single node with contribution `m` (an ε-chain).
-/

set_option linter.unusedSectionVars false

namespace Podc.IncentiveTrees

open Chain

variable {a b lam μ φ : ℝ}

/-- The "inner" part of the TDRM reward: `Q(c) + a G(c) X`. -/
noncomputable def tdrmInner (a μ : ℝ) : Tree → ℝ
  | .node c ch => Qc a μ c + a * Gc a μ c * (ch.map (rctW a μ)).sum

theorem tdrm_eq_inner (T : Tree) :
    tdrm a b lam μ φ T = lam * b / μ * tdrmInner a μ T + φ * T.root := by
  obtain ⟨c, ch⟩ := T
  rw [tdrm_node]; rfl

section Basic

variable (ha : 0 ≤ a) (ha1 : a < 1) (hμ : 0 < μ)
include ha ha1 hμ

omit ha1 in
theorem rctW_nonneg : ∀ T : Tree, T.Nonneg → 0 ≤ rctW a μ T := by
  refine Tree.ind fun c ch ih hT => ?_
  rw [Tree.nonneg_node] at hT
  rw [rctW_node]
  have := Hc_nonneg ha hμ c hT.1
  have : 0 ≤ (ch.map (rctW a μ)).sum :=
    List.sum_nonneg (by simpa using fun t ht => ih t ht (hT.2 t ht))
  have := pow_nonneg ha (nOf μ c + 1)
  positivity

theorem sumRctW_nonneg (ch : List Tree) (h : ∀ t ∈ ch, t.Nonneg) :
    0 ≤ (ch.map (rctW a μ)).sum :=
  List.sum_nonneg (by simpa using fun t ht => rctW_nonneg ha hμ t (h t ht))

theorem tdrmInner_nonneg (T : Tree) (hT : T.Nonneg) : 0 ≤ tdrmInner a μ T := by
  obtain ⟨c, ch⟩ := T
  rw [Tree.nonneg_node] at hT
  have := Qc_nonneg ha hμ c hT.1
  have := Gc_nonneg ha hμ c hT.1
  have := sumRctW_nonneg ha ha1 hμ ch hT.2
  simp only [tdrmInner]
  positivity

/-- Budget invariant: `(1 - a) Σ_v inner(T_v) + a μ W(T) ≤ μ C(T)`. -/
theorem tdrmInner_budget : ∀ T : Tree, T.Nonneg →
    (1 - a) * ((T.subtrees).map (tdrmInner a μ)).sum + a * μ * rctW a μ T ≤ μ * T.total := by
  refine Tree.ind fun c ch ih hT => ?_
  rw [Tree.nonneg_node] at hT
  have hsum : (1 - a) * (((ch.map Tree.subtrees).flatten).map (tdrmInner a μ)).sum
      + a * μ * (ch.map (rctW a μ)).sum ≤ μ * (ch.map Tree.total).sum := by
    rw [sum_map_flatten_map, ← List.sum_map_mul_left, ← List.sum_map_mul_left,
      ← List.sum_map_mul_left, ← List.sum_map_add]
    exact List.sum_le_sum fun t ht => ih t ht (hT.2 t ht)
  have h1 := chain_budget ha ha1 hμ c hT.1
  have h2 := Gc_le ha ha1 hμ c hT.1
  have hX := sumRctW_nonneg ha ha1 hμ ch hT.2
  simp only [Tree.subtrees, Tree.total, List.map_cons, List.sum_cons, rctW_node,
    tdrmInner] at hsum ⊢
  set X := (ch.map (rctW a μ)).sum
  have h3 : a * ((1 - a) * Gc a μ c * X) ≤ a * (μ * (1 - a ^ (nOf μ c + 1)) * X) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hX) ha
  nlinarith

end Basic

/-! ## USA -/

/-- Scaled total reward of the Sybils of a Sybil tree: `Σ inner`. -/
noncomputable def Sybil.V (a μ : ℝ) : Sybil → ℝ
  | .node c s r => tdrmInner a μ (Sybil.toTree (.node c s r)) + (s.map (Sybil.V a μ)).sum

/-- Weight of the real subtrees attached to a Sybil tree. -/
noncomputable def Sybil.E (a μ : ℝ) (s : Sybil) : ℝ := (s.reals.map (rctW a μ)).sum

theorem Sybil.reward_tdrm : ∀ s : Sybil,
    s.reward (tdrm a b lam μ φ) = lam * b / μ * s.V a μ + φ * s.mass := by
  refine Sybil.ind fun c s r ih => ?_
  simp only [Sybil.reward, Sybil.V, Sybil.mass, tdrm_eq_inner]
  rw [List.map_congr_left ih, List.sum_map_add, List.sum_map_mul_left,
    List.sum_map_mul_left]
  simp [Sybil.toTree, Tree.root]
  ring

theorem Sybil.E_node (c : ℝ) (s : List Sybil) (r : List Tree) :
    (Sybil.node c s r).E a μ = (s.map (Sybil.E a μ)).sum + (r.map (rctW a μ)).sum := by
  simp [Sybil.E, Sybil.reals, List.sum_append, List.map_flatten, List.sum_flatten,
    Function.comp_def]
  rfl

theorem Sybil.rctW_toTree (c : ℝ) (s : List Sybil) (r : List Tree) :
    rctW a μ (Sybil.node c s r).toTree = Hc a μ c + a ^ (nOf μ c + 1) *
      ((s.map fun x => rctW a μ x.toTree).sum + (r.map (rctW a μ)).sum) := by
  rw [Sybil.toTree, rctW_node, List.map_append, List.sum_append, List.map_map]
  rfl

section USA

variable (ha : 0 ≤ a) (ha1 : a < 1) (hμ : 0 < μ)
include ha ha1 hμ

theorem Sybil.E_nonneg : ∀ s : Sybil, s.Nonneg → 0 ≤ s.E a μ := by
  refine Sybil.ind fun c s r ih hs => ?_
  rw [Sybil.nonneg_node] at hs
  rw [Sybil.E_node]
  have : 0 ≤ (s.map (Sybil.E a μ)).sum :=
    List.sum_nonneg (by simpa using fun x hx => ih x hx (hs.2.1 x hx))
  have := sumRctW_nonneg ha ha1 hμ r hs.2.2
  linarith

theorem Sybil.rctW_nonneg' (s : Sybil) (hs : s.Nonneg) : 0 ≤ rctW a μ s.toTree := by
  refine rctW_nonneg ha hμ _ ?_
  revert hs
  refine Sybil.ind (P := fun s => s.Nonneg → s.toTree.Nonneg) (fun c s r ih hs => ?_) s
  rw [Sybil.nonneg_node] at hs
  rw [Sybil.toTree, Tree.nonneg_node]
  refine ⟨hs.1, fun t ht => ?_⟩
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
    exact ih x hx (hs.2.1 x hx)
  · exact hs.2.2 t ht

/-- Merging the bounds of sibling Sybil trees (uses superadditivity of `Q + a α G`). -/
theorem merge_bound (α L : ℝ) (hL : 0 ≤ L) (_hα : 0 ≤ α) (hαμ : (1 - a) * α ≤ μ) (l : List Sybil)
    (hl : ∀ x ∈ l, x.Nonneg) :
    (l.map fun x => Qc a μ x.mass + a * α * Gc a μ x.mass +
        a * x.E a μ * Gc a μ (x.mass + L)).sum ≤
      Qc a μ (l.map Sybil.mass).sum + a * α * Gc a μ (l.map Sybil.mass).sum +
        a * (l.map (Sybil.E a μ)).sum * Gc a μ ((l.map Sybil.mass).sum + L) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil, zero_add, mul_zero, zero_mul, add_zero]
    have : Qc a μ 0 = 0 := by
      have := Qc_eq (a := a) hμ 0 0 le_rfl hμ.le; simpa [Qf, s] using this
    have h2 : Gc a μ 0 = 0 := by
      have := Gc_eq (a := a) hμ 0 0 le_rfl hμ.le; simpa [Gf, g] using this
    rw [this, h2]; simp
  | cons x l ih =>
    have hx := hl x (by simp)
    have hl' : ∀ y ∈ l, y.Nonneg := fun y hy => hl y (by simp [hy])
    have hm := Sybil.mass_nonneg x hx
    have hM : 0 ≤ (l.map Sybil.mass).sum :=
      List.sum_nonneg (by simpa using fun y hy => Sybil.mass_nonneg y (hl' y hy))
    have hE := Sybil.E_nonneg ha ha1 hμ x hx
    have hEl : 0 ≤ (l.map (Sybil.E a μ)).sum :=
      List.sum_nonneg (by simpa using fun y hy => Sybil.E_nonneg ha ha1 hμ y (hl' y hy))
    simp only [List.map_cons, List.sum_cons]
    have h1 := ih hl'
    have h2 := Qc_superadd ha ha1 hμ α hαμ x.mass (l.map Sybil.mass).sum hm hM
    have h3 : Gc a μ (x.mass + L) ≤ Gc a μ (x.mass + (l.map Sybil.mass).sum + L) :=
      Gc_mono ha ha1 hμ _ _ (by linarith) (by linarith)
    have h4 : Gc a μ ((l.map Sybil.mass).sum + L) ≤
        Gc a μ (x.mass + (l.map Sybil.mass).sum + L) :=
      Gc_mono ha ha1 hμ _ _ (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg ha hE),
      mul_le_mul_of_nonneg_left h4 (mul_nonneg ha hEl)]

omit ha ha1 hμ in
theorem tdrmInner_toTree (c : ℝ) (ss : List Sybil) (r : List Tree) :
    tdrmInner a μ (Sybil.node c ss r).toTree = Qc a μ c + a * Gc a μ c *
      ((ss.map fun x => rctW a μ x.toTree).sum + (r.map (rctW a μ)).sum) := by
  simp only [Sybil.toTree, tdrmInner, List.map_append, List.sum_append, List.map_map]
  rfl

/-- The key invariant (replaces Lemmas 1–5 of the paper). -/
theorem sybil_bound : ∀ s : Sybil, s.Nonneg → ∀ α ℓ : ℝ, 0 ≤ ℓ → 0 ≤ α → α ≤ Gc a μ ℓ →
    s.V a μ + a * α * rctW a μ s.toTree ≤
      Qc a μ s.mass + a * α * Gc a μ s.mass + a * s.E a μ * Gc a μ (s.mass + ℓ) := by
  refine Sybil.ind fun c ss r ih hs => ?_
  intro α ℓ hℓ hα hαG
  rw [Sybil.nonneg_node] at hs
  obtain ⟨hc, hss, hr⟩ := hs
  set N := nOf μ c + 1
  set α' := Gc a μ c + a ^ N * α
  have hAN := pow_nonneg ha N
  have hGc := Gc_nonneg ha hμ c hc
  have hα'0 : 0 ≤ α' := by positivity
  have hα'G : α' ≤ Gc a μ (c + ℓ) := by
    have := Gc_add_le ha ha1 hμ c ℓ hc hℓ
    have := mul_le_mul_of_nonneg_left hαG hAN
    linarith
  have hα'μ : (1 - a) * α' ≤ μ := by
    have := Gc_le' ha ha1 hμ (c + ℓ) (by linarith)
    have : (1 - a) * α' ≤ (1 - a) * Gc a μ (c + ℓ) :=
      mul_le_mul_of_nonneg_left hα'G (by linarith)
    linarith
  -- children
  have hchild : (ss.map fun x => x.V a μ + a * α' * rctW a μ x.toTree).sum ≤
      (ss.map fun x => Qc a μ x.mass + a * α' * Gc a μ x.mass +
        a * x.E a μ * Gc a μ (x.mass + (c + ℓ))).sum :=
    List.sum_le_sum fun x hx => ih x hx (hss x hx) α' (c + ℓ) (by linarith) hα'0 hα'G
  have hmerge := merge_bound ha ha1 hμ α' (c + ℓ) (by linarith) hα'0 hα'μ ss hss
  rw [List.sum_map_add, List.sum_map_mul_left] at hchild
  set M := (ss.map Sybil.mass).sum
  set SV := (ss.map (Sybil.V a μ)).sum
  set Xs := (ss.map fun x => rctW a μ x.toTree).sum
  set Xr := (r.map (rctW a μ)).sum
  set Es := (ss.map (Sybil.E a μ)).sum
  have hM : 0 ≤ M := List.sum_nonneg (by simpa using fun x hx => Sybil.mass_nonneg x (hss x hx))
  have hXr : 0 ≤ Xr := sumRctW_nonneg ha ha1 hμ r hr
  have hGM := Gc_nonneg ha hμ M hM
  have hV : (Sybil.node c ss r).V a μ = Qc a μ c + a * Gc a μ c * (Xs + Xr) + SV := by
    rw [Sybil.V, tdrmInner_toTree]
  have hW : rctW a μ (Sybil.node c ss r).toTree = Hc a μ c + a ^ N * (Xs + Xr) :=
    Sybil.rctW_toTree c ss r
  have hE : (Sybil.node c ss r).E a μ = Es + Xr := Sybil.E_node c ss r
  have hm : (Sybil.node c ss r).mass = c + M := by simp [Sybil.mass, M]
  rw [hV, hW, hE, hm]
  have q1 := Qc_add ha ha1 hμ c M hc hM
  have q2 := Hc_add_le ha ha1 hμ c M hc hM
  have q3 : Gc a μ (c + ℓ) ≤ Gc a μ (c + M + ℓ) := Gc_mono ha ha1 hμ _ _ (by linarith) (by linarith)
  have q4 : Gc a μ (M + (c + ℓ)) = Gc a μ (c + M + ℓ) := by ring_nf
  rw [q4] at hmerge
  have hEs : 0 ≤ Es :=
    List.sum_nonneg (by simpa using fun x hx => Sybil.E_nonneg ha ha1 hμ x (hss x hx))
  have t1 : a * α * (Hc a μ c + a ^ N * Gc a μ M) ≤ a * α * Gc a μ (c + M) :=
    mul_le_mul_of_nonneg_left q2 (mul_nonneg ha hα)
  have t2 : a * α' * Xr ≤ a * Gc a μ (c + M + ℓ) * Xr :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hα'G.trans q3) ha) hXr
  have e1 : a * α' * Gc a μ M = a * Gc a μ c * Gc a μ M + a * α * (a ^ N * Gc a μ M) := by
    simp only [α']; ring
  nlinarith

/-- USA for TDRM (the key part of Theorem 4). -/
theorem tdrm_USA (hb : 0 ≤ b) (hlam : 0 ≤ lam) : USA (tdrm a b lam μ φ) := by
  intro c F S hc hF hS hP hm
  have hG0 : Gc a μ 0 = 0 := by
    have := Gc_eq (a := a) hμ 0 0 le_rfl hμ.le; simpa [Gf, g] using this
  have h1 : (S.map (Sybil.V a μ)).sum ≤ (S.map fun x => Qc a μ x.mass + a * 0 * Gc a μ x.mass +
      a * x.E a μ * Gc a μ (x.mass + 0)).sum := by
    refine List.sum_le_sum fun x hx => ?_
    have := sybil_bound ha ha1 hμ x (hS x hx) 0 0 le_rfl le_rfl (by rw [hG0])
    simpa using this
  have h2 := merge_bound ha ha1 hμ 0 0 le_rfl le_rfl (by simpa using hμ.le) S hS
  have hE : (S.map (Sybil.E a μ)).sum = (F.map (rctW a μ)).sum := by
    rw [← (hP.map (rctW a μ)).sum_eq, sum_map_flatten_map]
    rfl
  rw [hE, hm] at h2
  simp only [mul_zero, zero_mul, add_zero] at h1 h2
  have hrew : (S.map (Sybil.reward (tdrm a b lam μ φ))).sum =
      lam * b / μ * (S.map (Sybil.V a μ)).sum + φ * (S.map Sybil.mass).sum := by
    rw [List.map_congr_left (fun x _ => Sybil.reward_tdrm x), List.sum_map_add,
      List.sum_map_mul_left, List.sum_map_mul_left]
  rw [hrew, hm, tdrm_node]
  have : 0 ≤ lam * b / μ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) this]

end USA

/-! ## The other properties -/

theorem rctW_joinLeaf (ha : 0 < a) (hμ : 0 < μ) {d : ℝ} (hd : 0 < d) {T T' : Tree}
    (hJ : Tree.JoinLeaf d T T') : rctW a μ T < rctW a μ T' := by
  induction hJ with
  | atNode c l₁ l₂ =>
    simp only [rctW_node, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
      List.map_nil, List.sum_nil, mul_zero, add_zero, Tree.leaf]
    have := Hc_pos ha.le hμ d hd
    have := pow_pos ha (nOf μ c + 1)
    nlinarith
  | inChild c l₁ l₂ t t' _ ih =>
    simp only [rctW_node, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    have := pow_pos ha (nOf μ c + 1)
    nlinarith

/-- Theorem 4 of [Lv–Moscibroda] (journal numbering; PODC Theorem 4.4):
TDRM with `0 < λ < Φ - φ`, `0 < b < 1 - a`, `0 < a`,
`μ > 0`, `0 ≤ φ` satisfies nonnegative rewards, the budget constraint, CCI, CSI, `φ`-RPC,
URO, PO and USA, but not UGSA. -/
theorem theorem_4 {Φ : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b < 1 - a) (hμ : 0 < μ)
    (hlam : 0 < lam) (hlamΦ : lam < Φ - φ) (hφ : 0 ≤ φ) :
    NonnegReward (tdrm a b lam μ φ) ∧ Budget (tdrm a b lam μ φ) Φ ∧ CCI (tdrm a b lam μ φ) ∧
      CSI (tdrm a b lam μ φ) ∧ RPC (tdrm a b lam μ φ) φ ∧ URO (tdrm a b lam μ φ) ∧
      PO (tdrm a b lam μ φ) ∧ USA (tdrm a b lam μ φ) ∧ ¬ UGSA (tdrm a b lam μ φ) := by
  have ha1 : a < 1 := by linarith
  have hK : 0 < lam * b / μ := by positivity
  have hURO : URO (tdrm a b lam μ φ) := by
    intro R c k hR hc hk
    set N1 := nOf μ 1 + 1
    have hH1 := Hc_pos ha.le hμ 1 one_pos
    have hGc := Gc_pos ha.le hμ ha c hc
    have hAN := pow_pos ha N1
    set K := lam * b / μ * a * Gc a μ c * a ^ N1 * Hc a μ 1
    have hKpos : 0 < K := by positivity
    set M := ⌈R / K⌉₊
    have hMK : R ≤ K * M := by
      have := Nat.le_ceil (R / K)
      rw [div_le_iff₀ hKpos] at this
      linarith
    have hleaf : rctW a μ (Tree.leaf 1) = Hc a μ 1 := by simp [rctW_node]
    refine ⟨.node 1 (List.replicate M (.leaf 1)) :: List.replicate (k - 1) (.leaf 1),
      by simp; omega, ?_, ?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · simp only [Tree.nonneg_node]
        refine ⟨zero_le_one, fun t ht => ?_⟩
        rw [List.eq_of_mem_replicate ht]; simp
      · rw [List.eq_of_mem_replicate ht]; simp
    · rw [tdrm_node]
      simp only [List.map_cons, List.sum_cons, List.map_replicate, List.sum_replicate,
        nsmul_eq_mul, hleaf]
      rw [rctW_node, List.map_replicate, List.sum_replicate, nsmul_eq_mul, hleaf]
      have hQ := Qc_nonneg ha.le hμ c hc.le
      have hH := Hc_nonneg ha.le hμ 1 zero_le_one
      have : 0 ≤ ((k - 1 : ℕ) : ℝ) * Hc a μ 1 := by positivity
      have : K * M ≤ lam * b / μ * (a * Gc a μ c * (Hc a μ 1 + a ^ N1 * (M * Hc a μ 1) +
          ((k - 1 : ℕ) : ℝ) * Hc a μ 1)) := by
        have h0 : 0 ≤ lam * b / μ * (a * Gc a μ c) := by positivity
        have : a ^ N1 * (M * Hc a μ 1) ≤ Hc a μ 1 + a ^ N1 * (M * Hc a μ 1) +
            ((k - 1 : ℕ) : ℝ) * Hc a μ 1 := by linarith
        have := mul_le_mul_of_nonneg_left this h0
        simp only [K]
        nlinarith
      nlinarith [mul_nonneg hK.le hQ, mul_nonneg hφ hc.le]
  refine ⟨?_, ?_, ?_, ?_, ?_, hURO, hURO.po, tdrm_USA ha.le ha1 hμ hb.le hlam.le, ?_⟩
  · -- nonnegative rewards
    intro T hT
    rw [tdrm_eq_inner]
    have := tdrmInner_nonneg ha.le ha1 hμ T hT
    obtain ⟨c, ch⟩ := T
    have hc := ((Tree.nonneg_node c ch).1 hT).1
    simp only [Tree.root]
    positivity
  · -- budget
    intro T hT
    have h1 := tdrmInner_budget ha.le ha1 hμ T hT
    have h2 := rctW_nonneg ha.le hμ T hT
    have h3 := Tree.total_nonneg T hT
    have hsum : ((T.subtrees).map (tdrm a b lam μ φ)).sum =
        lam * b / μ * ((T.subtrees).map (tdrmInner a μ)).sum + φ * T.total := by
      rw [List.map_congr_left (fun x _ => tdrm_eq_inner x), List.sum_map_add,
        List.sum_map_mul_left, List.sum_map_mul_left, ← Tree.sum_subtrees_root]
    rw [hsum]
    have hI : (1 - a) * ((T.subtrees).map (tdrmInner a μ)).sum ≤ μ * T.total := by
      nlinarith [mul_nonneg (mul_nonneg ha.le hμ.le) h2]
    -- (λ b / μ) Σ inner ≤ λ b / (1 - a) C ≤ λ C
    have h4 : (1 - a) * (lam * b / μ * ((T.subtrees).map (tdrmInner a μ)).sum) ≤
        (1 - a) * (lam * T.total) := by
      have := mul_le_mul_of_nonneg_left hI hK.le
      have e : lam * b / μ * (μ * T.total) = lam * b * T.total := by field_simp
      have : lam * b * T.total ≤ (1 - a) * (lam * T.total) := by
        have := mul_le_mul_of_nonneg_right hab.le (mul_nonneg hlam.le h3)
        nlinarith
      nlinarith
    have h5 := le_of_mul_le_mul_left h4 (by linarith)
    nlinarith
  · -- CCI
    intro c c' F hc hcc' hF
    rw [tdrm_node, tdrm_node]
    have hX := sumRctW_nonneg ha.le ha1 hμ F hF
    have q := Qc_add ha.le ha1 hμ c (c' - c) hc (by linarith)
    have q' := Qc_pos ha.le hμ (c' - c) (by linarith)
    have hG := Gc_mono ha.le ha1 hμ c c' hc hcc'.le
    have hGc := Gc_nonneg ha.le hμ c hc
    have hGd := Gc_nonneg ha.le hμ (c' - c) (by linarith)
    rw [add_sub_cancel] at q
    have : Qc a μ c < Qc a μ c' := by nlinarith [mul_nonneg (mul_nonneg ha.le hGc) hGd]
    have : a * Gc a μ c * (F.map (rctW a μ)).sum ≤ a * Gc a μ c' * (F.map (rctW a μ)).sum := by
      have := mul_le_mul_of_nonneg_left hG ha.le
      exact mul_le_mul_of_nonneg_right this hX
    nlinarith [mul_le_mul_of_nonneg_left hcc'.le hφ]
  · -- CSI
    rintro d ⟨c, ch⟩ T' hT hc hd hJ
    have hlt := rctW_joinLeaf ha hμ hd hJ
    obtain ⟨ch', rfl, -⟩ := Tree.joinLeaf_node hJ
    simp only [Tree.root] at hc
    rw [rctW_node, rctW_node] at hlt
    have hAN := pow_pos ha (nOf μ c + 1)
    have hX : (ch.map (rctW a μ)).sum < (ch'.map (rctW a μ)).sum := by
      by_contra h
      have h := not_lt.mp h
      nlinarith [mul_le_mul_of_nonneg_left h hAN.le]
    rw [tdrm_node, tdrm_node]
    have hG := Gc_pos ha.le hμ ha c hc
    have : a * Gc a μ c * (ch.map (rctW a μ)).sum < a * Gc a μ c * (ch'.map (rctW a μ)).sum :=
      mul_lt_mul_of_pos_left hX (by positivity)
    nlinarith
  · -- φ-RPC
    intro T hT
    rw [tdrm_eq_inner]
    have := tdrmInner_nonneg ha.le ha1 hμ T hT
    nlinarith [mul_nonneg hK.le this]
  · -- UGSA fails: the example at the end of Section 5
    intro hU
    have hQ1 : Qc a μ μ = μ ^ 2 := by
      have := Qc_eq (a := a) hμ 0 μ hμ.le le_rfl; simpa [Qf, s, g] using this
    have hG1 : Gc a μ μ = μ := by
      have := Gc_eq (a := a) hμ 0 μ hμ.le le_rfl; simpa [Gf, g] using this
    have hQ2 : Qc a μ (μ / 2) = μ ^ 2 / 4 := by
      have := Qc_eq (a := a) hμ 0 (μ / 2) (by positivity) (by linarith)
      simp [Qf, s, g] at this; rw [this]; ring
    have hG2 : Gc a μ (μ / 2) = μ / 2 := by
      have := Gc_eq (a := a) hμ 0 (μ / 2) (by positivity) (by linarith); simpa [Gf, g] using this
    have hH1 : rctW a μ (Tree.leaf μ) = μ := by
      obtain ⟨h1, h2⟩ := nOf_headOf_of hμ 0 μ hμ le_rfl
      simp only [CharP.cast_eq_zero, zero_mul, zero_add] at h1 h2
      simp [rctW_node, Hc, Hf, h1, h2, g]
    set k := ⌈1 / (lam * b * a)⌉₊ + 1
    have hk : 1 < lam * b * a * k := by
      have h0 : 0 < lam * b * a := by positivity
      have := Nat.le_ceil (1 / (lam * b * a))
      rw [div_le_iff₀ h0] at this
      simp only [k]; push_cast
      nlinarith
    set F := List.replicate k (Tree.leaf μ)
    have hF : ∀ t ∈ F, t.Nonneg := by
      intro t ht; rw [List.eq_of_mem_replicate ht]; simp [hμ.le]
    have hX : (F.map (rctW a μ)).sum = k * μ := by
      simp [F, List.map_replicate, List.sum_replicate, hH1]
    have := hU (μ / 2) F [Sybil.node μ [] F] (by positivity) hF
      (by simpa [hμ.le] using hF) (by simp [Sybil.reals]) (by simp [Sybil.mass]; linarith)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Sybil.reward, Sybil.mass, Sybil.toTree, List.nil_append] at this
    rw [tdrm_node, tdrm_node, hX, hQ1, hG1, hQ2, hG2] at this
    have e1 : lam * b / μ * (μ ^ 2 + a * μ * (k * μ)) = lam * b * μ * (1 + a * k) := by
      field_simp
    have e2 : lam * b / μ * (μ ^ 2 / 4 + a * (μ / 2) * (k * μ)) =
        lam * b * μ * (1 / 4 + a * k / 2) := by
      field_simp
    rw [e1, e2] at this
    have : μ * 1 < μ * (lam * b * a * k) := mul_lt_mul_of_pos_left hk hμ
    nlinarith [mul_nonneg hφ hμ.le, mul_pos (mul_pos hlam hb) hμ]

end Podc.IncentiveTrees
