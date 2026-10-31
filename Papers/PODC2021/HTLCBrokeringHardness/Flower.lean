/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Papers.PODC2021.HTLCBrokeringHardness.Model

/-!
# Flower graphs and the Knapsack construction (§4)

* `TxGraph.IsFlower`: a flower graph (§3): one broker `c` incident to every contract, with contracts
  to and from every other party; no other party is a broker, and every other party owns the assets
  of its outgoing contracts. In the flower graphs of the paper the broker starts with nothing
  (`flowerOwn`).
* `Knapsack`: a knapsack instance `K = (X, V, W)` with items `(vᵢ, wᵢ)`; `Knapsack.Satisfiable`.
* `flower K m c`: the flower graph `F` of Figure 2, steps (1)–(3.c), with `m` levels and
  `c` bitcoins on each contract `(yᵢ, b)`, `2 ≤ i ≤ m` (the paper takes `c = min_w(X) − 1` and
  `m = ⌈Σ_w(X)/min_w(X) − 1⌉ + 1`, see `paperFlower`).

Level `k : Fin (m+1)` of the construction is the pair `y_{k+1}, z_{k+1}` of the paper; the paper's
coin `C_i` is `Asset.C i`.
-/

namespace Podc.HTLCBrokeringHardness

open Finset

namespace TxGraph

variable {P E A : Type*} [DecidableEq P] [DecidableEq A] [DecidableEq E] [Fintype E]
  (G : TxGraph P E A)

/-- Initial endowment of a flower graph with broker `c`: every party other than `c` owns exactly the
assets of its outgoing contracts, the broker owns nothing. -/
def brokerOwn (c : P) (p : P) (a : A) : ℕ := if p = c then 0 else G.outTotal p a

/-- §3: `G` (with endowment `own`) is a *flower graph* with broker `c`. -/
def IsFlower (own : P → A → ℕ) (c : P) : Prop :=
  (∀ e, (G.src e = c ∨ G.dst e = c) ∧ G.src e ≠ G.dst e) ∧
  (∀ p, p ≠ c → (∃ e, G.src e = c ∧ G.dst e = p) ∧ ∃ e, G.src e = p ∧ G.dst e = c) ∧
  (∀ p, p ≠ c → ¬ G.IsBroker p) ∧
  (∀ p, p ≠ c → ∀ a, G.outTotal p a ≤ own p a)

end TxGraph

/-- A knapsack instance `K = (X, V, W)` with `n` items `xᵢ = (vᵢ, wᵢ)`. -/
structure Knapsack (n : ℕ) where
  /-- Values. -/
  v : Fin n → ℕ
  /-- Weights. -/
  w : Fin n → ℕ
  /-- Value target. -/
  V : ℕ
  /-- Weight capacity. -/
  W : ℕ

namespace Knapsack

variable {n : ℕ} (K : Knapsack n)

/-- `K` is satisfiable iff some subset `R` of the items has value `≥ V` and weight `≤ W`. -/
def Satisfiable : Prop :=
  ∃ R : Finset (Fin n), K.V ≤ ∑ i ∈ R, K.v i ∧ ∑ i ∈ R, K.w i ≤ K.W

/-- `Σ_w(X)`. -/
def totalW : ℕ := ∑ i, K.w i

/-- `min_w(X)` (`0` for the empty instance). -/
noncomputable def minW : ℕ := ⨅ i, K.w i

lemma minW_le (i : Fin n) : K.minW ≤ K.w i := ciInf_le (OrderBot.bddBelow _) i

/-- The number of levels chosen by the paper: `m = ⌈Σ_w(X) / min_w(X) − 1⌉ + 1`. -/
noncomputable def paperM : ℕ := ⌈(K.totalW : ℚ) / K.minW - 1⌉₊ + 1

end Knapsack

/-- Parties of the flower graph: broker `b`, supplier `s`, items `xᵢ`, and `y_{k+1}`, `z_{k+1}` for
level `k ∈ {0, …, m}`. -/
inductive Party (n m : ℕ)
  | b
  | s
  | x (i : Fin n)
  | y (k : Fin (m + 1))
  | z (k : Fin (m + 1))
  deriving DecidableEq, Fintype

/-- Assets: bitcoin `B`, coins `D`, `E`, and `C i` (the paper's `Cᵢ`, `1 ≤ i ≤ m`). -/
inductive Asset
  | B
  | D
  | E
  | C (i : ℕ)
  deriving DecidableEq

/-- Contracts of the flower graph (Figure 2). -/
inductive Edge (n m : ℕ)
  /-- `(s, b) = W B`. -/
  | fromS
  /-- `(b, s) = 2 D`. -/
  | toS
  /-- `(b, xᵢ) = wᵢ B`. -/
  | toX (i : Fin n)
  /-- `(xᵢ, b) = vᵢ E`. -/
  | fromX (i : Fin n)
  /-- `(b, y₁) = (V − 1) E`, `(b, y_{k+1}) = 3 C_k` for `k ≥ 1`. -/
  | toY (k : Fin (m + 1))
  /-- `(y_{k+1}, b) = 2 C_{k+1}` for `k < m`, `(y_{m+1}, b) = 1 D`. -/
  | fromY (k : Fin (m + 1))
  /-- `(y_{j+2}, b) = c B` for `j + 2 ∈ {2, …, m}`. -/
  | fromYB (j : Fin (m - 1))
  /-- `(b, z₁) = 1 E`, `(b, z_{k+1}) = 1 C_k` for `k ≥ 1`. -/
  | toZ (k : Fin (m + 1))
  /-- `(z_{k+1}, b) = 2 C_{k+1}` for `k < m`, `(z_{m+1}, b) = 1 D`. -/
  | fromZ (k : Fin (m + 1))
  deriving DecidableEq, Fintype

namespace Flower

variable {n m : ℕ}

/-- The level of the `y`-party that owns the bitcoin contract `fromYB j` (paper's `y_{j+2}`). -/
def ybLevel (j : Fin (m - 1)) : Fin (m + 1) := ⟨j + 1, by omega⟩

/-- Asset received by level `k`. -/
def inAsset (k : Fin (m + 1)) : Asset := if (k : ℕ) = 0 then .E else .C k

/-- Asset sent by level `k`. -/
def outAsset (k : Fin (m + 1)) : Asset := if (k : ℕ) = m then .D else .C (k + 1)

end Flower

open Flower

/-- The flower graph `F` of Figure 2 for the knapsack instance `K`, with `m` levels and `c` bitcoins on
each contract `(yᵢ, b)`, `2 ≤ i ≤ m`. -/
def flower {n : ℕ} (K : Knapsack n) (m c : ℕ) : TxGraph (Party n m) (Edge n m) Asset where
  src
    | .fromS => .s
    | .fromX i => .x i
    | .fromY k => .y k
    | .fromYB j => .y (ybLevel j)
    | .fromZ k => .z k
    | _ => .b
  dst
    | .toS => .s
    | .toX i => .x i
    | .toY k => .y k
    | .toZ k => .z k
    | _ => .b
  asset
    | .fromS => .B
    | .toS => .D
    | .toX _ => .B
    | .fromX _ => .E
    | .toY k => inAsset k
    | .fromY k => outAsset k
    | .fromYB _ => .B
    | .toZ k => inAsset k
    | .fromZ k => outAsset k
  amt
    | .fromS => K.W
    | .toS => 2
    | .toX i => K.w i
    | .fromX i => K.v i
    | .toY k => if (k : ℕ) = 0 then K.V - 1 else 3
    | .fromY k => if (k : ℕ) = m then 1 else 2
    | .fromYB _ => c
    | .toZ _ => 1
    | .fromZ k => if (k : ℕ) = m then 1 else 2

/-- The endowment of the flower graph: `b` owns nothing, everybody else what it sends. -/
def flowerOwn {n : ℕ} (K : Knapsack n) (m c : ℕ) : Party n m → Asset → ℕ :=
  (flower K m c).brokerOwn .b

/-- The construction exactly as in the paper: `c = min_w(X) − 1`, `m = ⌈Σ_w(X)/min_w(X) − 1⌉ + 1`. -/
noncomputable def paperFlower {n : ℕ} (K : Knapsack n) :
    TxGraph (Party n K.paperM) (Edge n K.paperM) Asset :=
  flower K K.paperM (K.minW - 1)

/-- The endowment of `paperFlower K`. -/
noncomputable def paperOwn {n : ℕ} (K : Knapsack n) : Party n K.paperM → Asset → ℕ :=
  flowerOwn K K.paperM (K.minW - 1)

namespace Flower

variable {n m c : ℕ} {K : Knapsack n}

lemma inAsset_ne_B (k : Fin (m + 1)) : inAsset k ≠ .B := by unfold inAsset; split_ifs <;> simp

lemma outAsset_ne_B (k : Fin (m + 1)) : outAsset k ≠ .B := by unfold outAsset; split_ifs <;> simp

lemma inAsset_ne_outAsset (k : Fin (m + 1)) : inAsset k ≠ outAsset k := by
  unfold inAsset outAsset; split_ifs <;> simp

/-- The construction is a flower graph with broker `b`. -/
theorem isFlower : (flower K m c).IsFlower (flowerOwn K m c) .b := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e; cases e <;> simp [flower]
  · intro p hp
    cases p with
    | b => exact absurd rfl hp
    | s => exact ⟨⟨.toS, rfl, rfl⟩, .fromS, rfl, rfl⟩
    | x i => exact ⟨⟨.toX i, rfl, rfl⟩, .fromX i, rfl, rfl⟩
    | y k => exact ⟨⟨.toY k, rfl, rfl⟩, .fromY k, rfl, rfl⟩
    | z k => exact ⟨⟨.toZ k, rfl, rfl⟩, .fromZ k, rfl, rfl⟩
  · rintro p hp ⟨e, e', hd, hs, ha⟩
    cases e <;> cases e' <;> simp [flower] at hd hs ha <;> subst_vars <;>
      simp_all [inAsset_ne_B, outAsset_ne_B, inAsset_ne_outAsset]
  · intro p hp a
    simp [flowerOwn, TxGraph.brokerOwn, hp]

lemma inAsset_eq_C {k : Fin (m + 1)} {i : ℕ} : inAsset k = .C i ↔ (k : ℕ) ≠ 0 ∧ (k : ℕ) = i := by
  unfold inAsset; split_ifs <;> simp_all

lemma outAsset_eq_C {k : Fin (m + 1)} {i : ℕ} : outAsset k = .C i ↔ (k : ℕ) ≠ m ∧ (k : ℕ) + 1 = i := by
  unfold outAsset; split_ifs <;> simp_all

lemma inAsset_eq_E {k : Fin (m + 1)} : inAsset k = .E ↔ (k : ℕ) = 0 := by
  unfold inAsset; split_ifs <;> simp_all

lemma outAsset_eq_D {k : Fin (m + 1)} : outAsset k = .D ↔ (k : ℕ) = m := by
  unfold outAsset; split_ifs <;> simp_all

@[simp] lemma inAsset_ne_D (k : Fin (m + 1)) : inAsset k ≠ .D := by unfold inAsset; split_ifs <;> simp

@[simp] lemma outAsset_ne_E (k : Fin (m + 1)) : outAsset k ≠ .E := by unfold outAsset; split_ifs <;> simp


/-! ### Field values of the contracts (simp lemmas) -/

@[simp] lemma src_fromS : (flower K m c).src .fromS = .s := rfl
@[simp] lemma dst_fromS : (flower K m c).dst .fromS = .b := rfl
@[simp] lemma asset_fromS : (flower K m c).asset .fromS = .B := rfl
@[simp] lemma amt_fromS :
    (flower K m c).amt .fromS = K.W := rfl
@[simp] lemma src_toS : (flower K m c).src .toS = .b := rfl
@[simp] lemma dst_toS : (flower K m c).dst .toS = .s := rfl
@[simp] lemma asset_toS : (flower K m c).asset .toS = .D := rfl
@[simp] lemma amt_toS :
    (flower K m c).amt .toS = 2 := rfl
@[simp] lemma src_toX (i : Fin n) : (flower K m c).src (.toX i) = .b := rfl
@[simp] lemma dst_toX (i : Fin n) : (flower K m c).dst (.toX i) = .x i := rfl
@[simp] lemma asset_toX (i : Fin n) : (flower K m c).asset (.toX i) = .B := rfl
@[simp] lemma amt_toX (i : Fin n) :
    (flower K m c).amt (.toX i) = K.w i := rfl
@[simp] lemma src_fromX (i : Fin n) : (flower K m c).src (.fromX i) = .x i := rfl
@[simp] lemma dst_fromX (i : Fin n) : (flower K m c).dst (.fromX i) = .b := rfl
@[simp] lemma asset_fromX (i : Fin n) : (flower K m c).asset (.fromX i) = .E := rfl
@[simp] lemma amt_fromX (i : Fin n) :
    (flower K m c).amt (.fromX i) = K.v i := rfl
@[simp] lemma src_toY (k : Fin (m + 1)) : (flower K m c).src (.toY k) = .b := rfl
@[simp] lemma dst_toY (k : Fin (m + 1)) : (flower K m c).dst (.toY k) = .y k := rfl
@[simp] lemma asset_toY (k : Fin (m + 1)) : (flower K m c).asset (.toY k) = inAsset k := rfl
@[simp] lemma amt_toY (k : Fin (m + 1)) :
    (flower K m c).amt (.toY k) = if (k : ℕ) = 0 then K.V - 1 else 3 := rfl
@[simp] lemma src_fromY (k : Fin (m + 1)) : (flower K m c).src (.fromY k) = .y k := rfl
@[simp] lemma dst_fromY (k : Fin (m + 1)) : (flower K m c).dst (.fromY k) = .b := rfl
@[simp] lemma asset_fromY (k : Fin (m + 1)) : (flower K m c).asset (.fromY k) = outAsset k := rfl
@[simp] lemma amt_fromY (k : Fin (m + 1)) :
    (flower K m c).amt (.fromY k) = if (k : ℕ) = m then 1 else 2 := rfl
@[simp] lemma src_fromYB (j : Fin (m - 1)) : (flower K m c).src (.fromYB j) = .y (ybLevel j) := rfl
@[simp] lemma dst_fromYB (j : Fin (m - 1)) : (flower K m c).dst (.fromYB j) = .b := rfl
@[simp] lemma asset_fromYB (j : Fin (m - 1)) : (flower K m c).asset (.fromYB j) = .B := rfl
@[simp] lemma amt_fromYB (j : Fin (m - 1)) :
    (flower K m c).amt (.fromYB j) = c := rfl
@[simp] lemma src_toZ (k : Fin (m + 1)) : (flower K m c).src (.toZ k) = .b := rfl
@[simp] lemma dst_toZ (k : Fin (m + 1)) : (flower K m c).dst (.toZ k) = .z k := rfl
@[simp] lemma asset_toZ (k : Fin (m + 1)) : (flower K m c).asset (.toZ k) = inAsset k := rfl
@[simp] lemma amt_toZ (k : Fin (m + 1)) :
    (flower K m c).amt (.toZ k) = 1 := rfl
@[simp] lemma src_fromZ (k : Fin (m + 1)) : (flower K m c).src (.fromZ k) = .z k := rfl
@[simp] lemma dst_fromZ (k : Fin (m + 1)) : (flower K m c).dst (.fromZ k) = .b := rfl
@[simp] lemma asset_fromZ (k : Fin (m + 1)) : (flower K m c).asset (.fromZ k) = outAsset k := rfl
@[simp] lemma amt_fromZ (k : Fin (m + 1)) :
    (flower K m c).amt (.fromZ k) = if (k : ℕ) = m then 1 else 2 := rfl

/-! ### Flows of the broker -/

variable (K m c) (S : Finset (Edge n m))

lemma inflow_B : (flower K m c).inflow S .b .B =
    (if Edge.fromS ∈ S then K.W else 0) + ∑ j, if Edge.fromYB j ∈ S then c else 0 := by
  unfold TxGraph.inflow
  rw [TxGraph.sum_filter_eq_of_iff (T := insert .fromS (univ.map ⟨Edge.fromYB, fun _ _ h => by cases h; rfl⟩))]
  · rw [sum_insert (by simp), sum_map]; rfl
  · intro e; cases e <;> simp [flower, outAsset_ne_B] <;> exact ⟨_, rfl⟩

lemma outflow_B : (flower K m c).outflow S .b .B = ∑ i, if Edge.toX i ∈ S then K.w i else 0 := by
  unfold TxGraph.outflow
  rw [TxGraph.sum_filter_eq_of_iff (T := univ.map ⟨Edge.toX, fun _ _ h => by cases h; rfl⟩)]
  · rw [sum_map]; rfl
  · intro e; cases e <;> simp [flower, inAsset_ne_B] <;> exact ⟨_, rfl⟩

lemma inflow_E : (flower K m c).inflow S .b .E = ∑ i, if Edge.fromX i ∈ S then K.v i else 0 := by
  unfold TxGraph.inflow
  rw [TxGraph.sum_filter_eq_of_iff (T := univ.map ⟨Edge.fromX, fun _ _ h => by cases h; rfl⟩)]
  · rw [sum_map]; rfl
  · intro e; cases e <;> simp [flower] <;> exact ⟨_, rfl⟩

lemma outflow_E : (flower K m c).outflow S .b .E =
    (if Edge.toY 0 ∈ S then K.V - 1 else 0) + (if Edge.toZ 0 ∈ S then 1 else 0) := by
  unfold TxGraph.outflow
  rw [TxGraph.sum_filter_eq_of_iff (T := {Edge.toY 0, Edge.toZ 0})]
  · rw [sum_pair (by simp)]; simp [flower]
  · intro e; cases e <;> simp [flower, inAsset_eq_E]

lemma inflow_C (k : Fin (m + 1)) (hk : (k : ℕ) ≠ m) : (flower K m c).inflow S .b (.C (k + 1)) =
    (if Edge.fromY k ∈ S then 2 else 0) + (if Edge.fromZ k ∈ S then 2 else 0) := by
  unfold TxGraph.inflow
  rw [TxGraph.sum_filter_eq_of_iff (T := {Edge.fromY k, Edge.fromZ k})]
  · rw [sum_pair (by simp)]; simp [flower, hk]
  · intro e; cases e <;> simp [flower, outAsset_eq_C] <;> (rw [Fin.ext_iff]; omega)

lemma outflow_C (k : Fin (m + 1)) (hk : (k : ℕ) ≠ 0) : (flower K m c).outflow S .b (.C k) =
    (if Edge.toY k ∈ S then 3 else 0) + (if Edge.toZ k ∈ S then 1 else 0) := by
  unfold TxGraph.outflow
  rw [TxGraph.sum_filter_eq_of_iff (T := {Edge.toY k, Edge.toZ k})]
  · have hk' : k ≠ 0 := by rintro rfl; simp at hk
    rw [sum_pair (by simp)]; simp [flower, hk']
  · intro e; cases e <;> simp [flower, inAsset_eq_C] <;> (rw [Fin.ext_iff]; simp only [Fin.val_zero] at *; omega)

lemma inflow_D : (flower K m c).inflow S .b .D =
    (if Edge.fromY (Fin.last m) ∈ S then 1 else 0) + (if Edge.fromZ (Fin.last m) ∈ S then 1 else 0) := by
  unfold TxGraph.inflow
  rw [TxGraph.sum_filter_eq_of_iff (T := {Edge.fromY (Fin.last m), Edge.fromZ (Fin.last m)})]
  · rw [sum_pair (by simp)]; simp [flower]
  · intro e; cases e <;> simp [flower, outAsset_eq_D] <;> (rw [Fin.ext_iff]; simp)

lemma outflow_D : (flower K m c).outflow S .b .D = if Edge.toS ∈ S then 2 else 0 := by
  unfold TxGraph.outflow
  rw [TxGraph.sum_filter_eq_of_iff (T := {Edge.toS})]
  · rw [sum_singleton]; rfl
  · intro e; cases e <;> simp [flower]

end Flower

end Podc.HTLCBrokeringHardness
