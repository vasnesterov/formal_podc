import Papers.PODC2024.SSLeaderElectionDirected.Defs

/-!
# Algorithm C-MAI(D, ≺, I): minimum ancestors' input (Section 3)

Altisen, Cournier, Defalque, Devismes, *On Self-stabilizing Leader Election in Directed Networks*,
PODC 2024 (HAL hal-04434345v4).

Every process `p` has a constant input `I p ∈ D` (`D` totally ordered) and a key
`p.K = (p.M, p.d) ∈ D × [0..α]`, ordered lexicographically. Its only action is
`ReplaceKey :: BestKey(p) ≠ p.K → p.K ← BestKey(p)` where
`BestKey(p) = min ({(I p, 0)} ∪ {(q.M, q.d + 1) | q ∈ Γ⁻(p), q.d < α})`.

The goal is `p.K = (MinI(p), Mind(p))` (`target`): `MinI(p)` is the least input among the ancestors
of `p` and `Mind(p)` the distance from a closest ancestor with that input.

This file contains the definitions, the order on keys, and the properties of `MinI`/`Mind`
(Property 1). It also introduces `Run`: a sequence of key configurations in which, at each step, an
arbitrary set of processes `A t` executes `ReplaceKey` with respect to *time-dependent* inputs
`I t`. Plain executions of C-MAI are runs with constant inputs; layers of the composition
`PEL = E ∘ A ∘ MI` are runs whose inputs are eventually constant.
-/

set_option linter.unusedSectionVars false

open Cslib.SelfStabilization Relation

namespace Papers.PODC2024.SSLeaderElectionDirected

/-- A key `(M, d)`; keys are ordered lexicographically. -/
@[ext] structure Key (D : Type*) where
  /-- the estimated minimum input -/
  M : D
  /-- the estimated distance -/
  d : ℕ
deriving DecidableEq

namespace Key

variable {D : Type*} [LinearOrder D]

/-- The lexicographic encoding of a key. -/
def toLex' (k : Key D) : D ×ₗ ℕ := toLex (k.M, k.d)

theorem toLex'_injective : Function.Injective (toLex' (D := D)) := by
  intro a b h
  simp only [toLex', toLex_inj, Prod.mk.injEq] at h
  exact Key.ext h.1 h.2

instance : LinearOrder (Key D) := LinearOrder.lift' toLex' toLex'_injective

theorem le_iff {k k' : Key D} : k ≤ k' ↔ k.M < k'.M ∨ k.M = k'.M ∧ k.d ≤ k'.d :=
  Prod.Lex.toLex_le_toLex

theorem lt_iff {k k' : Key D} : k < k' ↔ k.M < k'.M ∨ k.M = k'.M ∧ k.d < k'.d :=
  Prod.Lex.toLex_lt_toLex

theorem lt_of_M_lt {k k' : Key D} (h : k.M < k'.M) : k < k' := lt_iff.mpr (Or.inl h)

theorem M_le_of_le {k k' : Key D} (h : k ≤ k') : k.M ≤ k'.M := by
  rcases le_iff.mp h with h | h
  · exact h.le
  · exact h.1.le

/-- The key `(M, d + 1)`, i.e. the key offered to successors. -/
def succ (k : Key D) : Key D := ⟨k.M, k.d + 1⟩

@[simp] theorem succ_M (k : Key D) : k.succ.M = k.M := rfl
@[simp] theorem succ_d (k : Key D) : k.succ.d = k.d + 1 := rfl

theorem lt_succ (k : Key D) : k < k.succ := lt_iff.mpr (Or.inr ⟨rfl, Nat.lt_succ_self _⟩)

theorem succ_le_succ {k k' : Key D} (h : k ≤ k') : k.succ ≤ k'.succ := by
  rcases le_iff.mp h with h | h
  · exact le_iff.mpr (Or.inl h)
  · exact le_iff.mpr (Or.inr ⟨h.1, by simp [h.2]⟩)

theorem succ_lt_succ {k k' : Key D} (h : k < k') : k.succ < k'.succ := by
  rcases lt_iff.mp h with h | h
  · exact lt_iff.mpr (Or.inl h)
  · exact lt_iff.mpr (Or.inr ⟨h.1, by simp [h.2]⟩)

theorem mk_le_mk {a b : D} {m n : ℕ} : (⟨a, m⟩ : Key D) ≤ ⟨b, n⟩ ↔ a < b ∨ a = b ∧ m ≤ n :=
  le_iff

theorem mk_lt_mk {a b : D} {m n : ℕ} : (⟨a, m⟩ : Key D) < ⟨b, n⟩ ↔ a < b ∨ a = b ∧ m < n :=
  lt_iff

end Key

/-- A local state of C-MAI: a key whose distance lies in `[0..α]`. -/
abbrev CState (D : Type*) (α : ℕ) := {k : Key D // k.d ≤ α}

namespace CMAI

variable {V : Type*} [Fintype V] (G : Digraph V) {D : Type*} [LinearOrder D]

open Classical in
/-- `KeySet(p) = {SelfKey(p)} ∪ {(q.M, q.d + 1) | q ∈ Γ⁻(p) ∧ q.d < α}`. -/
noncomputable def keySet (α : ℕ) (I : V → D) (K : V → Key D) (p : V) : Finset (Key D) :=
  insert ⟨I p, 0⟩ ((Finset.univ.filter fun q => G.Adj q p ∧ (K q).d < α).image fun q => (K q).succ)

/-- `BestKey(p) = min KeySet(p)`. -/
noncomputable def bestKey (α : ℕ) (I : V → D) (K : V → Key D) (p : V) : Key D :=
  (keySet G α I K p).min' (Finset.insert_nonempty _ _)

variable {G} {α : ℕ} {I : V → D} {K : V → Key D} {p : V}

theorem mem_keySet {k : Key D} :
    k ∈ keySet G α I K p ↔ k = ⟨I p, 0⟩ ∨ ∃ q, G.Adj q p ∧ (K q).d < α ∧ k = (K q).succ := by
  classical
  simp only [keySet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (h | ⟨q, ⟨h1, h2⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, h1, h2, rfl⟩
  · rintro (h | ⟨q, h1, h2, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, ⟨h1, h2⟩, rfl⟩

theorem selfKey_mem_keySet : (⟨I p, 0⟩ : Key D) ∈ keySet G α I K p :=
  mem_keySet.mpr (Or.inl rfl)

theorem succ_mem_keySet {q : V} (hq : G.Adj q p) (hd : (K q).d < α) :
    (K q).succ ∈ keySet G α I K p :=
  mem_keySet.mpr (Or.inr ⟨q, hq, hd, rfl⟩)

theorem bestKey_mem : bestKey G α I K p ∈ keySet G α I K p := Finset.min'_mem _ _

theorem bestKey_le {k : Key D} (hk : k ∈ keySet G α I K p) : bestKey G α I K p ≤ k :=
  Finset.min'_le _ _ hk

theorem le_bestKey {c : Key D} (h : ∀ k ∈ keySet G α I K p, c ≤ k) : c ≤ bestKey G α I K p :=
  Finset.le_min' _ _ _ h

theorem bestKey_le_selfKey : bestKey G α I K p ≤ ⟨I p, 0⟩ := bestKey_le selfKey_mem_keySet

theorem bestKey_d_le : (bestKey G α I K p).d ≤ α := by
  rcases mem_keySet.mp (bestKey_mem (G := G) (α := α) (I := I) (K := K) (p := p)) with h | ⟨q, -, hd, h⟩
  · rw [h]; exact Nat.zero_le _
  · rw [h]; simp only [Key.succ_d]; omega

/-- `bestKey` only depends on the input of `p` and on the keys of its predecessors. -/
theorem bestKey_congr {I' : V → D} {K' : V → Key D} (hI : I p = I' p)
    (hK : ∀ q, G.Adj q p → K q = K' q) : bestKey G α I K p = bestKey G α I' K' p := by
  have : keySet G α I K p = keySet G α I' K' p := by
    ext k
    simp only [mem_keySet, hI]
    constructor
    · rintro (h | ⟨q, hq, hd, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, hK q hq ▸ hd, by rw [hK q hq]⟩
    · rintro (h | ⟨q, hq, hd, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, (hK q hq).symm ▸ hd, by rw [hK q hq]⟩
  simp only [bestKey, this]

/-! ### `MinI` and `Mind` -/

variable (G)

open Classical in
/-- The ancestors of `p`. -/
noncomputable def ancs (p : V) : Finset V := Finset.univ.filter fun q => G.Reachable q p

theorem mem_ancs {q p : V} : q ∈ ancs G p ↔ G.Reachable q p := by
  classical
  simp [ancs]

theorem self_mem_ancs (p : V) : p ∈ ancs G p := (mem_ancs G).mpr (Digraph.Reachable.refl p)

/-- `MinI(p)`: the smallest input among the ancestors of `p`. -/
noncomputable def minI (I : V → D) (p : V) : D :=
  ((ancs G p).image I).min' ⟨I p, Finset.mem_image_of_mem I (self_mem_ancs G p)⟩

variable {G}

theorem minI_le {q p : V} (h : G.Reachable q p) : minI G I p ≤ I q :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem I ((mem_ancs G).mpr h))

theorem exists_minI (p : V) : ∃ q, G.Reachable q p ∧ I q = minI G I p := by
  obtain ⟨q, hq, h⟩ := Finset.mem_image.mp (Finset.min'_mem ((ancs G p).image I)
    ⟨I p, Finset.mem_image_of_mem I (self_mem_ancs G p)⟩)
  exact ⟨q, (mem_ancs G).mp hq, h⟩

theorem minI_le_self (p : V) : minI G I p ≤ I p := minI_le (Digraph.Reachable.refl p)

/-- `MinI` is antitone along ancestry. -/
theorem minI_mono {q p : V} (h : G.Reachable q p) : minI G I p ≤ minI G I q := by
  obtain ⟨r, hr, hrq⟩ := exists_minI (G := G) (I := I) q
  exact hrq ▸ minI_le (hr.trans h)

theorem exists_reach_minI (p : V) :
    ∃ n, ∃ q, I q = minI G I p ∧ RelatesWithinSteps G.Adj q p n := by
  obtain ⟨q, hq, hIq⟩ := exists_minI (G := G) (I := I) p
  obtain ⟨n, hn⟩ := Digraph.reachable_iff_exists_relatesWithinSteps.1 hq
  exact ⟨n, q, hIq, hn⟩

variable (G) in
open Classical in
/-- `Mind(p)`: the distance to `p` from a closest ancestor whose input is `MinI(p)`. -/
noncomputable def mind (I : V → D) (p : V) : ℕ := Nat.find (exists_reach_minI (G := G) (I := I) p)

variable (G) in
/-- The legitimate key of `p`: `(MinI(p), Mind(p))`. -/
noncomputable def target (I : V → D) (p : V) : Key D := ⟨minI G I p, mind G I p⟩

theorem mind_spec (p : V) : ∃ q, I q = minI G I p ∧ RelatesWithinSteps G.Adj q p (mind G I p) := by
  classical
  exact Nat.find_spec (exists_reach_minI (G := G) (I := I) p)

theorem mind_le {q p : V} {n : ℕ} (hq : I q = minI G I p) (h : RelatesWithinSteps G.Adj q p n) :
    mind G I p ≤ n := by
  classical
  exact Nat.find_min' (exists_reach_minI (G := G) (I := I) p) ⟨q, hq, h⟩

theorem mind_le_of_madLe (hα : MADLe G α) (p : V) : mind G I p ≤ α := by
  obtain ⟨q, hq, h⟩ := mind_spec (G := G) (I := I) p
  exact mind_le hq (hα q p h.reflTransGen)

theorem mind_eq_zero_iff {p : V} : mind G I p = 0 ↔ I p = minI G I p := by
  constructor
  · intro h
    obtain ⟨q, hq, hr⟩ := mind_spec (G := G) (I := I) p
    rw [h] at hr
    obtain rfl := RelatesWithinSteps.zero hr; exact hq
  · intro h
    exact Nat.le_zero.mp (mind_le h (RelatesWithinSteps.refl p))

theorem minI_lt_of_mind_pos {p : V} (h : 0 < mind G I p) : minI G I p < I p :=
  lt_of_le_of_ne (minI_le_self p) fun h' => by
    rw [(mind_eq_zero_iff (G := G)).mpr h'.symm] at h; exact lt_irrefl _ h

/-- Property 1: `(MinI(p), Mind(p)) ≤ (MinI(q), Mind(q) + 1)` for every predecessor `q` of `p`. -/
theorem target_le_succ_target {q p : V} (hq : G.Adj q p) :
    target G I p ≤ (target G I q).succ := by
  have hle := minI_mono (G := G) (I := I) (Digraph.Adj.reachable hq)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Key.lt_of_M_lt hlt |>.le
  · refine Key.le_iff.mpr (Or.inr ⟨heq, ?_⟩)
    obtain ⟨r, hr, hrq⟩ := mind_spec (G := G) (I := I) q
    exact mind_le (hr.trans heq.symm) (hrq.tail hq)

theorem selfKey_ge_target (p : V) : target G I p ≤ ⟨I p, 0⟩ := by
  rcases lt_or_eq_of_le (minI_le_self (G := G) (I := I) p) with h | h
  · exact (Key.lt_of_M_lt h).le
  · exact Key.le_iff.mpr (Or.inr ⟨h, (mind_eq_zero_iff (G := G)).mpr h.symm ▸ le_rfl⟩)

/-- A process at positive `Mind` has a predecessor with the same `MinI` one step closer. -/
theorem exists_pred_of_mind {p : V} {m : ℕ} (h : mind G I p = m + 1) :
    ∃ q, G.Adj q p ∧ minI G I q = minI G I p ∧ mind G I q = m := by
  obtain ⟨r, hr, hrp⟩ := mind_spec (G := G) (I := I) p
  rw [h] at hrp
  have hnot : ¬ RelatesWithinSteps G.Adj r p m := fun h' => by
    have := mind_le hr h'; omega
  obtain ⟨q, hrq, hqp⟩ := (relatesWithinSteps_succ_iff.1 hrp).resolve_left hnot
  have hmin : minI G I q = minI G I p := by
    apply le_antisymm _ (minI_mono (Digraph.Adj.reachable hqp))
    exact hr ▸ minI_le hrq.reflTransGen
  refine ⟨q, hqp, hmin, le_antisymm (mind_le (hr.trans hmin.symm) hrq) ?_⟩
  have := target_le_succ_target (G := G) (I := I) hqp
  rcases Key.le_iff.mp this with h' | h'
  · simp [target, hmin] at h'
  · simp only [target, Key.succ_d] at h'; omega

/-! ### Runs -/

variable (G) in
/-- A run of C-MAI with time-dependent inputs `I t`: at step `t` the processes of `A t` execute
`ReplaceKey` (a process that is not enabled does not change), the others keep their key. -/
structure Run (α : ℕ) (I : ℕ → V → D) (K : ℕ → V → Key D) (A : ℕ → Set V) : Prop where
  move : ∀ t p, p ∈ A t → K (t + 1) p = bestKey G α (I t) (K t) p
  stay : ∀ t p, p ∉ A t → K (t + 1) p = K t p

end CMAI

end Papers.PODC2024.SSLeaderElectionDirected
