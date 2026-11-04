import Mathlib

/-!
# Incentive Tree mechanisms: model and desirable properties

Formalization of the model of Lv–Moscibroda, *Fair and resilient Incentive Tree mechanisms*
(PODC 2013; journal version Distributed Computing 2016, whose numbering we use).

* A (weighted) referral tree is a rooted tree; every node is a participant with a contribution
  `C(u) ≥ 0`, its children are the participants it solicited (`Tree.node c children`).
* We only consider mechanisms with **subtree locality (SL)**: the reward of a participant `u`
  is `f T_u` for a function `f` of the subtree `T_u` rooted at `u`.  Such a mechanism is
  therefore just a function `f : Tree → ℝ` ("reward of the root of the given subtree").
  Every result of the paper we formalize is about SL mechanisms (Theorem 3 assumes SL, and the
  mechanisms of Theorems 1, 4, 5 are subtree-local).
* A **Sybil attack** of a participant `u` (with real children subtrees `F`) is a forest of
  Sybil identities (`Sybil`), each with a contribution, Sybil children and real children; every
  real child of `u` is attached to exactly one Sybil identity.  With SL, where the Sybil trees
  are attached in the rest of the referral tree does not matter, so a forest of Sybil trees
  describes every attack of the paper ("arbitrarily connected" Sybil nodes).
-/

namespace Podc.IncentiveTrees

/-- A weighted referral tree: a participant with contribution `c` and the subtrees of the
participants it solicited.  Children are kept in a list (an artefact of the encoding). -/
inductive Tree where
  | node (c : ℝ) (children : List Tree)

namespace Tree

/-- Contribution of the root participant. -/
def root : Tree → ℝ
  | node c _ => c

/-- The list of subtrees of the children. -/
def children : Tree → List Tree
  | node _ ch => ch

/-- `C(T)`: total contribution of the tree. -/
def total : Tree → ℝ
  | node c ch => c + (ch.map total).sum

/-- All contributions are nonnegative (`C(u) ≥ 0` in the paper). -/
def Nonneg : Tree → Prop
  | node c ch => 0 ≤ c ∧ ∀ t ∈ ch, Nonneg t

/-- The list of all subtrees `T_v`, one for every node `v` of the tree. -/
def subtrees : Tree → List Tree
  | node c ch => node c ch :: (ch.map subtrees).flatten

/-- Induction principle for trees: prove `P` for a node assuming it for all children. -/
theorem ind {P : Tree → Prop} (h : ∀ c ch, (∀ t ∈ ch, P t) → P (node c ch)) : ∀ T, P T := by
  intro T
  induction T using Tree.rec (motive_2 := fun l => ∀ t ∈ l, P t) with
  | node c ch ih => exact h c ch ih
  | nil => rename_i h; cases h
  | cons t l ih₁ ih₂ =>
    rename_i t' ht'
    rcases List.mem_cons.mp ht' with rfl | h
    exacts [ih₁, ih₂ _ h]

@[simp] theorem nonneg_node (c : ℝ) (ch : List Tree) :
    (node c ch).Nonneg ↔ 0 ≤ c ∧ ∀ t ∈ ch, t.Nonneg := by
  simp [Nonneg]

/-- A single participant without solicitees. -/
abbrev leaf (c : ℝ) : Tree := node c []

/-- `JoinLeaf d T T'`: `T'` is obtained from `T` by a new participant with contribution `d`
joining somewhere in `T` (as a new child of any node, at any position among its siblings). -/
inductive JoinLeaf (d : ℝ) : Tree → Tree → Prop
  | atNode (c : ℝ) (l₁ l₂ : List Tree) :
      JoinLeaf d (node c (l₁ ++ l₂)) (node c (l₁ ++ leaf d :: l₂))
  | inChild (c : ℝ) (l₁ l₂ : List Tree) (t t' : Tree) :
      JoinLeaf d t t' → JoinLeaf d (node c (l₁ ++ t :: l₂)) (node c (l₁ ++ t' :: l₂))

end Tree



/-- An SL reward mechanism: `f T` is the reward of the root participant of the (sub)tree `T`. -/
abbrev Mechanism := Tree → ℝ

/-- A Sybil identity of an attacker: its contribution, its Sybil children and the subtrees of
the real participants attached to it. -/
inductive Sybil where
  | node (c : ℝ) (sybils : List Sybil) (reals : List Tree)

namespace Sybil

/-- The referral (sub)tree rooted at a Sybil identity. -/
def toTree : Sybil → Tree
  | node c s r => .node c (s.map toTree ++ r)

/-- Total contribution of the Sybil identities. -/
def mass : Sybil → ℝ
  | node c s _ => c + (s.map mass).sum

/-- All real subtrees attached to Sybil identities. -/
def reals : Sybil → List Tree
  | node _ s r => (s.map reals).flatten ++ r

/-- Total reward of the Sybil identities under mechanism `f`. -/
def reward (f : Mechanism) : Sybil → ℝ
  | node c s r => f (toTree (node c s r)) + (s.map (reward f)).sum

/-- All contributions (Sybil and real) are nonnegative. -/
def Nonneg : Sybil → Prop
  | node c s r => 0 ≤ c ∧ (∀ x ∈ s, Nonneg x) ∧ ∀ t ∈ r, t.Nonneg

/-- Induction principle for Sybil trees. -/
theorem ind {P : Sybil → Prop} (h : ∀ c s r, (∀ x ∈ s, P x) → P (node c s r)) : ∀ S, P S := by
  intro S
  induction S using Sybil.rec (motive_2 := fun l => ∀ x ∈ l, P x) with
  | node c s r ih => exact h c s r ih
  | nil => rename_i h; cases h
  | cons t l ih₁ ih₂ =>
    rename_i t' ht'
    rcases List.mem_cons.mp ht' with rfl | h
    exacts [ih₁, ih₂ _ h]

@[simp] theorem nonneg_node (c : ℝ) (s : List Sybil) (r : List Tree) :
    (node c s r).Nonneg ↔ 0 ≤ c ∧ (∀ x ∈ s, x.Nonneg) ∧ ∀ t ∈ r, t.Nonneg := by
  simp [Nonneg]

end Sybil

/-! ## Desirable properties (Section 3) -/

section Properties

variable (f : Mechanism)

/-- Rewards are nonnegative reals (part of the definition of a reward mechanism, Section 2). -/
def NonnegReward : Prop := ∀ T : Tree, T.Nonneg → 0 ≤ f T

/-- Budget constraint (Section 2): `R(T) ≤ Φ · C(T)` for every referral tree. -/
def Budget (Φ : ℝ) : Prop :=
  ∀ T : Tree, T.Nonneg → ((T.subtrees).map f).sum ≤ Φ * T.total

/-- Continuing contribution incentive (CCI): increasing one's own contribution strictly
increases one's reward. -/
def CCI : Prop :=
  ∀ (c c' : ℝ) (F : List Tree), 0 ≤ c → c < c' → (∀ t ∈ F, t.Nonneg) →
    f (.node c F) < f (.node c' F)

/-- Continuing solicitation incentive (CSI): a new participant joining the subtree strictly
increases the reward.  (We require the new participant and `u` to contribute something; see
`differencies.md`.) -/
def CSI : Prop :=
  ∀ (d : ℝ) (T T' : Tree), T.Nonneg → 0 < T.root → 0 < d → Tree.JoinLeaf d T T' → f T < f T'

/-- `φ`-reward proportional to contribution (`φ`-RPC): `R(u) ≥ φ C(u)`. -/
def RPC (φ : ℝ) : Prop := ∀ T : Tree, T.Nonneg → φ * T.root ≤ f T

/-- Unbounded reward opportunity (URO): for every `R > 0`, `C(u) > 0` and `k ≥ 1` there are
`k` trees attached to `u` giving `R(u) ≥ R`. -/
def URO : Prop :=
  ∀ (R c : ℝ) (k : ℕ), 0 < R → 0 < c → 0 < k →
    ∃ F : List Tree, F.length = k ∧ (∀ t ∈ F, t.Nonneg) ∧ R ≤ f (.node c F)

/-- Profitable opportunity (PO), as described in words in Section 3.1: a participant with any
positive contribution has the opportunity to get *positive profit*, `R(u) > C(u)`. -/
def PO : Prop :=
  ∀ (c : ℝ) (k : ℕ), 0 < c → 0 < k →
    ∃ F : List Tree, F.length = k ∧ (∀ t ∈ F, t.Nonneg) ∧ c < f (.node c F)

/-- Profitable opportunity exactly as in the formal definition of Section 3.1:
`R(u) ≥ C(u)` (zero profit suffices). -/
def POWeak : Prop :=
  ∀ (c : ℝ) (k : ℕ), 0 < c → 0 < k →
    ∃ F : List Tree, F.length = k ∧ (∀ t ∈ F, t.Nonneg) ∧ c ≤ f (.node c F)

/-- Unprofitable Sybil attack (USA): a participant `u` with contribution `c` and real children
subtrees `F` cannot increase its reward by joining as a forest `S` of Sybil identities of the
same total contribution, whatever the shape of `S` and the distribution of `F` over it. -/
def USA : Prop :=
  ∀ (c : ℝ) (F : List Tree) (S : List Sybil), 0 ≤ c → (∀ t ∈ F, t.Nonneg) →
    (∀ s ∈ S, s.Nonneg) → (S.map Sybil.reals).flatten.Perm F → (S.map Sybil.mass).sum = c →
    (S.map (Sybil.reward f)).sum ≤ f (.node c F)

/-- Unprofitable generalized Sybil attack (UGSA): as USA, but the Sybil identities may
contribute more in total, and the comparison is on profit (reward minus contribution). -/
def UGSA : Prop :=
  ∀ (c : ℝ) (F : List Tree) (S : List Sybil), 0 ≤ c → (∀ t ∈ F, t.Nonneg) →
    (∀ s ∈ S, s.Nonneg) → (S.map Sybil.reals).flatten.Perm F → c ≤ (S.map Sybil.mass).sum →
    (S.map (Sybil.reward f)).sum - (S.map Sybil.mass).sum ≤ f (.node c F) - c

/-- UGSA subsumes USA (Section 3.2). -/
theorem UGSA.usa {f : Mechanism} (h : UGSA f) : USA f := by
  intro c F S hc hF hS hP hm
  have := h c F S hc hF hS hP hm.ge
  linarith

/-- URO implies PO (Section 3.1). -/
theorem URO.po {f : Mechanism} (h : URO f) : PO f := by
  intro c k hc hk
  obtain ⟨F, hl, hF, hR⟩ := h (2 * c) c k (by linarith) hc hk
  exact ⟨F, hl, hF, by linarith⟩

theorem PO.poWeak {f : Mechanism} (h : PO f) : POWeak f := by
  intro c k hc hk
  obtain ⟨F, hl, hF, hR⟩ := h c k hc hk
  exact ⟨F, hl, hF, hR.le⟩

end Properties

end Podc.IncentiveTrees
