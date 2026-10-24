import Podc.Computability.Distributed.RateAllocation.MaxMinFair

/-!
# Clos networks and macro-switches (Section 2 of Ferreira–Atre–Sherry–Sobrinho, PODC 2024)

The Clos network `C_n` has `n` middle switches `M_m`, `2n` input switches `I_i`, `2n` output
switches `O_i`, and `n` source (destination) servers per input (output) switch. A server is a pair
`(i, j) : Fin (2n) × Fin n` (switch, server index), so `s_i^j` / `t_i^j` of the paper are
`(i - 1, j - 1)` here (all indices are 0-based). The links are

* `srcLink s` — from source server `s = (i, j)` to its input switch `I_i`;
* `up i m` — from `I_i` to `M_m`;
* `down m o` — from `M_m` to `O_o`;
* `dstLink t` — from output switch `O_o` to destination server `t = (o, j)`;

all of unit capacity. A collection of flows is a finite type `F` with a source and a destination
server for each flow (several flows may share a source–destination pair). A *routing* assigns to
each flow a middle switch, i.e. one of the `n` source–destination paths of `C_n`.

The macro-switch `MS_n` replaces the middle stage by infinite-capacity links between all input and
output switches; links of infinite capacity never constrain an allocation, so a flow of `MS_n`
traverses only its two server links (`macroSwitch`).
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

/-- A server: an input/output switch index in `Fin (2n)` and a server index in `Fin n`. -/
abbrev Server (n : ℕ) := Fin (2 * n) × Fin n

/-- A collection of flows in `C_n` / `MS_n`, indexed by `F`: each flow has a source server and a
destination server. -/
structure Flows (n : ℕ) (F : Type*) where
  /-- The source server `s_f` of each flow. -/
  src : F → Server n
  /-- The destination server `t_f` of each flow. -/
  dst : F → Server n

/-- The links of the Clos network `C_n`. -/
inductive Link (n : ℕ) where
  /-- The link `s I(s)` from a source server to its input switch. -/
  | srcLink (s : Server n)
  /-- The link `I_i M_m`. -/
  | up (i : Fin (2 * n)) (m : Fin n)
  /-- The link `M_m O_o`. -/
  | down (m : Fin n) (o : Fin (2 * n))
  /-- The link `O(t) t` from an output switch to a destination server. -/
  | dstLink (t : Server n)
  deriving DecidableEq, Fintype

variable {n : ℕ} {F : Type*}

/-- The Clos network `C_n` with routing `r` (flow `f` is assigned to middle switch `r f`):
flow `f` traverses `s_f I(s_f)`, `I(s_f) M_{r f}`, `M_{r f} O(t_f)`, `O(t_f) t_f`; all links have
unit capacity. -/
def clos (fl : Flows n F) (r : F → Fin n) : Network F (Link n) where
  path f := {.srcLink (fl.src f), .up (fl.src f).1 (r f), .down (r f) (fl.dst f).1,
    .dstLink (fl.dst f)}
  cap _ := 1

/-- The macro-switch `MS_n`: flow `f` traverses only its server links `s_f I(s_f)` and
`O(t_f) t_f` (the links between switches have infinite capacity and are omitted). -/
def macroSwitch (fl : Flows n F) : Network F (Link n) where
  path f := {.srcLink (fl.src f), .dstLink (fl.dst f)}
  cap _ := 1

/-- **Definition 2.4.** A lex-max-min fair allocation: the max-min fair allocation for some
routing `r` whose sorted vector is maximum over the max-min fair allocations of all routings. -/
def IsLexMaxMinFair [Fintype F] (fl : Flows n F) (r : F → Fin n) (a : F → ℝ) : Prop :=
  (clos fl r).IsMaxMinFair a ∧
    ∀ r' a', (clos fl r').IsMaxMinFair a' → sortedRates a' ≤ sortedRates a

/-- **Definition 2.5.** A throughput-max-min fair allocation: the max-min fair allocation for some
routing `r` whose throughput is maximum over the max-min fair allocations of all routings. -/
def IsThroughputMaxMinFair [Fintype F] (fl : Flows n F) (r : F → Fin n) (a : F → ℝ) : Prop :=
  (clos fl r).IsMaxMinFair a ∧
    ∀ r' a', (clos fl r').IsMaxMinFair a' → throughput a' ≤ throughput a

/-- **Definition 5.1.** A throughput-maximum-throughput allocation: a maximum-throughput
allocation for some routing `r` whose throughput is maximum over all routings. -/
def IsThroughputMaxThroughput [Fintype F] (fl : Flows n F) (r : F → Fin n) (a : F → ℝ) : Prop :=
  (clos fl r).IsMaxThroughput a ∧
    ∀ r' a', (clos fl r').IsMaxThroughput a' → throughput a' ≤ throughput a

/-- A matching in the bipartite multigraph `G^MS` (start nodes: sources, end nodes: destinations,
links: flows): a set of flows with pairwise distinct sources and pairwise distinct
destinations. -/
def IsMatching (fl : Flows n F) (S : Finset F) : Prop :=
  Set.InjOn fl.src (S : Set F) ∧ Set.InjOn fl.dst (S : Set F)

/-- A maximum matching of `G^MS`. -/
def IsMaximumMatching (fl : Flows n F) (S : Finset F) : Prop :=
  IsMatching fl S ∧ ∀ S' : Finset F, IsMatching fl S' → S'.card ≤ S.card

/-- The `0/1` allocation of a set of flows: rate `1` for the flows of `S`, rate `0` otherwise. -/
noncomputable def indicatorAlloc (S : Finset F) : F → ℝ :=
  fun f => by classical exact if f ∈ S then 1 else 0

section Basic

variable (fl : Flows n F)

@[simp] theorem clos_cap (r : F → Fin n) (ℓ : Link n) : (clos fl r).cap ℓ = 1 := rfl
@[simp] theorem macroSwitch_cap (ℓ : Link n) : (macroSwitch fl).cap ℓ = 1 := rfl

theorem mem_clos_path {r : F → Fin n} {f : F} {ℓ : Link n} :
    ℓ ∈ (clos fl r).path f ↔ ℓ = .srcLink (fl.src f) ∨ ℓ = .up (fl.src f).1 (r f) ∨
      ℓ = .down (r f) (fl.dst f).1 ∨ ℓ = .dstLink (fl.dst f) := by
  simp [clos]

theorem mem_macroSwitch_path {f : F} {ℓ : Link n} :
    ℓ ∈ (macroSwitch fl).path f ↔ ℓ = .srcLink (fl.src f) ∨ ℓ = .dstLink (fl.dst f) := by
  simp [macroSwitch]

theorem macroSwitch_path_subset (r : F → Fin n) (f : F) :
    (macroSwitch fl).path f ⊆ (clos fl r).path f := by
  intro ℓ hℓ
  rw [mem_macroSwitch_path] at hℓ
  rw [mem_clos_path]
  tauto

variable [Fintype F]

/-! ### Link loads -/

/-- Re-indexing a sum of `if P f then b f else 0` along an injective map onto all flows
satisfying `P`. -/
theorem sum_ite_eq_of_injective {ι : Type*} [Fintype ι] (P : F → Prop) [DecidablePred P]
    (b : F → ℝ) (e : ι → F) (he : Function.Injective e) (hall : ∀ f, P f → ∃ x, e x = f) :
    (∑ f, if P f then b f else 0) = ∑ x, if P (e x) then b (e x) else 0 := by
  classical
  rw [← Finset.sum_image (g := e) (f := fun f => if P f then b f else 0)
    (fun x _ y _ h => he h)]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun f _ hf => ?_
  rw [ite_eq_right]
  intro hP
  obtain ⟨x, rfl⟩ := hall f hP
  exact hf (Finset.mem_image_of_mem _ (Finset.mem_univ x))

section Loads

variable (a : F → ℝ) (r : F → Fin n)

theorem macroSwitch_load_srcLink (s : Server n) :
    (macroSwitch fl).load a (.srcLink s) = ∑ f, if fl.src f = s then a f else 0 := by
  rw [Network.load_eq_sum_ite]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [mem_macroSwitch_path, eq_comm]

theorem macroSwitch_load_dstLink (t : Server n) :
    (macroSwitch fl).load a (.dstLink t) = ∑ f, if fl.dst f = t then a f else 0 := by
  rw [Network.load_eq_sum_ite]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [mem_macroSwitch_path, eq_comm]

theorem macroSwitch_load_up (i : Fin (2 * n)) (m : Fin n) :
    (macroSwitch fl).load a (.up i m) = 0 := by
  rw [Network.load_eq_sum_ite]
  simp [mem_macroSwitch_path]

theorem macroSwitch_load_down (m : Fin n) (o : Fin (2 * n)) :
    (macroSwitch fl).load a (.down m o) = 0 := by
  rw [Network.load_eq_sum_ite]
  simp [mem_macroSwitch_path]

theorem clos_load_srcLink (s : Server n) :
    (clos fl r).load a (.srcLink s) = ∑ f, if fl.src f = s then a f else 0 := by
  rw [Network.load_eq_sum_ite]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [mem_clos_path, eq_comm]

theorem clos_load_dstLink (t : Server n) :
    (clos fl r).load a (.dstLink t) = ∑ f, if fl.dst f = t then a f else 0 := by
  rw [Network.load_eq_sum_ite]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [mem_clos_path, eq_comm]

theorem clos_load_up (i : Fin (2 * n)) (m : Fin n) :
    (clos fl r).load a (.up i m) = ∑ f, if (fl.src f).1 = i ∧ r f = m then a f else 0 := by
  rw [Network.load_eq_sum_ite]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [mem_clos_path, eq_comm]

theorem clos_load_down (m : Fin n) (o : Fin (2 * n)) :
    (clos fl r).load a (.down m o) = ∑ f, if r f = m ∧ (fl.dst f).1 = o then a f else 0 := by
  rw [Network.load_eq_sum_ite]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp [mem_clos_path, eq_comm]

end Loads

/-- An allocation feasible in the Clos network (for some routing) is feasible in the
macro-switch. -/
theorem Feasible.toMacroSwitch {r : F → Fin n} {a : F → ℝ} (h : (clos fl r).Feasible a) :
    (macroSwitch fl).Feasible a := by
  classical
  refine ⟨h.1, fun ℓ => le_trans ?_ (h.2 ℓ)⟩
  unfold Network.load
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun f hf => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      exact macroSwitch_path_subset fl r f hf)
    fun f _ _ => h.1 f

/-- The sorted vector of the max-min fair allocation in the macro-switch is at least that of every
allocation feasible in the Clos network (Section 2.3). -/
theorem sortedRates_le_of_clos {r : F → Fin n} {a b : F → ℝ}
    (ha : (macroSwitch fl).IsMaxMinFair a) (hb : (clos fl r).Feasible b) :
    sortedRates b ≤ sortedRates a :=
  ha.2 b (Feasible.toMacroSwitch fl hb)

end Basic

end Podc.DataCenterRouting
