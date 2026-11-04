import Papers.PODC2013.IncentiveTrees.Geometric
import Papers.PODC2013.IncentiveTrees.Impossibility
import Papers.PODC2013.IncentiveTrees.TDRMChain

/-!
# The TDRM mechanism (Algorithm 4) and its closed form

TDRM with parameters `λ, μ, a, b, φ` transforms the referral tree `T` into the
*reward computation tree* (RCT) `T'`: a participant `u` becomes a chain of
`N_u = ⌈C(u)/μ⌉` nodes, the head with contribution `C(u) - (N_u - 1) μ`, the others with `μ`;
the children of `u` hang below the tail of its chain.  Every RCT node `w` gets
`R'(w) = (λ/μ) C(w) Σ_{x ∈ T'_w} a^{dep_w(x)} b C(x) + φ C(w)`, and `R(u)` is the sum of `R'`
over the chain of `u`.  (For `C(u) = 0` we use a chain of one node of contribution `0`;
the paper's `N_u = 0` would be an empty chain.)

`tdrm_node` gives the closed form
`R(u) = (λ b / μ) (Q(C(u)) + a G(C(u)) X) + φ C(u)`, with `X` the sum of the depth-weighted
contributions of the RCTs of the children (`rctW`), and `Q, G, H` the chain functions of
`TDRMChain.lean`.
-/

namespace Podc.IncentiveTrees

open Chain

section Defs

variable (a b lam μ φ : ℝ)

/-- The contributions of the chain of a participant with contribution `c`, head first. -/
noncomputable def chainPieces (c : ℝ) : List ℝ := headOf μ c :: List.replicate (nOf μ c) μ

/-- A chain of RCT nodes with the given contributions (head first) whose tail has children
`kids`. -/
def mkChain : List ℝ → List Tree → Tree
  | [], kids => .node 0 kids
  | [p], kids => .node p kids
  | p :: q :: ps, kids => .node p [mkChain (q :: ps) kids]

/-- The reward computation tree. -/
noncomputable def rct : Tree → Tree
  | .node c ch => mkChain (chainPieces μ c) (ch.map rct)

/-- `R'(w)` for the RCT node at the root of `w`. -/
noncomputable def rPrime (w : Tree) : ℝ := lam / μ * w.root * (b * w.wsum a) + φ * w.root

/-- Sum of `R'` over the nodes of a chain. -/
noncomputable def chainReward : List ℝ → List Tree → ℝ
  | [], _ => 0
  | p :: ps, kids => rPrime a b lam μ φ (mkChain (p :: ps) kids) + chainReward ps kids

/-- Algorithm 4: the TDRM mechanism (`R(u) = Σ_{v ∈ CH_u} R'(v)`). -/
noncomputable def tdrm : Mechanism
  | .node c ch => chainReward a b lam μ φ (chainPieces μ c) (ch.map (rct μ))

/-- Depth-weighted contribution of the RCT of a tree. -/
noncomputable def rctW (T : Tree) : ℝ := (rct μ T).wsum a

end Defs

/-! ## Closed forms -/

section ClosedForm

variable {a b lam μ φ : ℝ}

/-- Head-seen weighted sum of a chain of pieces. -/
def Hl (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p + a * Hl a ps

/-- Tail-seen weighted sum of a chain of pieces. -/
def Gl (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * a ^ ps.length + Gl a ps

/-- Inner quadratic form of a chain of pieces. -/
def Ql (a : ℝ) : List ℝ → ℝ
  | [] => 0
  | p :: ps => p * Hl a (p :: ps) + Ql a ps

theorem wsum_mkChain (p : ℝ) (ps : List ℝ) (kids : List Tree) :
    (mkChain (p :: ps) kids).wsum a =
      Hl a (p :: ps) + a ^ (ps.length + 1) * (kids.map (Tree.wsum a)).sum := by
  induction ps generalizing p with
  | nil => simp [mkChain, Tree.wsum_node, Hl]
  | cons q ps ih =>
    rw [mkChain, Tree.wsum_node]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, ih,
      Hl, List.length_cons, pow_succ]
    ring

theorem root_mkChain (p : ℝ) (ps : List ℝ) (kids : List Tree) :
    (mkChain (p :: ps) kids).root = p := by
  cases ps <;> rfl

theorem chainReward_eq (p : ℝ) (ps : List ℝ) (kids : List Tree) :
    chainReward a b lam μ φ (p :: ps) kids =
      lam * b / μ * (Ql a (p :: ps) + a * Gl a (p :: ps) * (kids.map (Tree.wsum a)).sum) +
        φ * (p :: ps).sum := by
  induction ps generalizing p with
  | nil =>
    simp only [chainReward, rPrime, root_mkChain, wsum_mkChain, Ql, Hl, Gl]
    simp
    ring
  | cons q ps ih =>
    rw [chainReward, ih, rPrime, root_mkChain, wsum_mkChain]
    simp only [Ql, Gl, Hl, List.length_cons, List.sum_cons, pow_succ]
    ring

theorem Hl_replicate (n : ℕ) : Hl a (List.replicate n μ) = μ * g a n := by
  induction n with
  | zero => simp [Hl, g]
  | succ n ih => rw [List.replicate_succ, Hl, ih, g_succ']; ring

theorem Gl_replicate (n : ℕ) : Gl a (List.replicate n μ) = μ * g a n := by
  induction n with
  | zero => simp [Gl, g]
  | succ n ih => rw [List.replicate_succ, Gl, ih, g_succ, List.length_replicate]; ring

theorem Ql_replicate (n : ℕ) : Ql a (List.replicate n μ) = μ ^ 2 * s a n := by
  induction n with
  | zero => simp [Ql, s]
  | succ n ih =>
    rw [List.replicate_succ, Ql, ih, ← List.replicate_succ, Hl_replicate, s_succ]; ring

theorem Hl_pieces (c : ℝ) : Hl a (chainPieces μ c) = Hc a μ c := by
  simp [chainPieces, Hl, Hl_replicate, Hc, Hf]; ring

theorem Gl_pieces (c : ℝ) : Gl a (chainPieces μ c) = Gc a μ c := by
  simp [chainPieces, Gl, Gl_replicate, Gc, Gf]

theorem Ql_pieces (c : ℝ) : Ql a (chainPieces μ c) = Qc a μ c := by
  simp only [chainPieces, Ql, Hl, Hl_replicate, Ql_replicate, Qc, Qf]; ring

theorem sum_pieces (c : ℝ) : (chainPieces μ c).sum = c := by
  simp [chainPieces, headOf]

theorem rctW_node (c : ℝ) (ch : List Tree) :
    rctW a μ (.node c ch) = Hc a μ c + a ^ (nOf μ c + 1) * (ch.map (rctW a μ)).sum := by
  simp only [rctW, rct, chainPieces]
  rw [wsum_mkChain, ← chainPieces, Hl_pieces, List.length_replicate, List.map_map]
  rfl

/-- Closed form of TDRM: `R(u) = (λ b / μ) (Q(c) + a G(c) X) + φ c`. -/
theorem tdrm_node (c : ℝ) (ch : List Tree) :
    tdrm a b lam μ φ (.node c ch) =
      lam * b / μ * (Qc a μ c + a * Gc a μ c * (ch.map (rctW a μ)).sum) + φ * c := by
  simp only [tdrm, chainPieces]
  rw [chainReward_eq, ← chainPieces, Ql_pieces, Gl_pieces, sum_pieces, List.map_map]
  rfl

end ClosedForm

end Podc.IncentiveTrees
