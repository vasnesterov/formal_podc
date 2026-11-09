import Papers.PODC2017.FenceInsertionChain.Basic

/-!
# Straight-line programs, fence types and Lemma 2.1

The concrete setting of Section 2 of the paper: operations `x = read(l)`, `write(l, x)`,
`write(l, d)` with types `τ ∈ {r, w}`, programs `π = ⟨p, →⟩` with `→` an irreflexive subset of
the increasing order on positions, the four fence types `fence(a, b)` and multi-type fence
insertions `f : positions → 𝒫(F)`.

## Main statements

* `Program.lemma_2_1` — **Lemma 2.1**: the gap-wise union of optimal insertions of the four
  restricted programs `⟨p, →|rr⟩, …, ⟨p, →|ww⟩` is an optimal insertion of `⟨p, →⟩`;
  `Program.lemma_2_1_size`: the minimum sizes add up; `Program.lemma_2_1_single`: the version with
  single-type optima (Definition 2.2), which the rest of the paper uses.
* `Program.optFI_not_unique` — optima are not unique, so "`OptFI(π) = …`" must be read as "is an
  optimum".
* `MemModel.decomposition` — the paper's remark on memory models: categories that are provided for
  free are dropped, categories served by the same fence instruction are merged, and the
  decomposition still holds.
* `overlap_sum_gt_opt` — the decomposition fails once a category can be served by *several*
  instructions (as on ARMv8 / Power, outside the paper's model).
* Figures 1 and 2: `dekkerT1_opt`, `fig2_opt`, `fig2b_valid`.
-/

namespace Podc.FenceInsertionChain

open Finset

/-- The two operation types `r` and `w`. -/
inductive RW
  | r
  | w
  deriving DecidableEq, Repr

instance : Fintype RW := ⟨{.r, .w}, by intro x; cases x <;> simp⟩

theorem RW.univ_eq : (univ : Finset RW) = {.r, .w} := rfl

/-- The operations `O` over data `D`, locations `L` and local variables `X`. -/
inductive Op (D L X : Type*)
  /-- `x = read(l)` -/
  | read (x : X) (l : L)
  /-- `write(l, x)` -/
  | writeVar (l : L) (x : X)
  /-- `write(l, d)` -/
  | writeVal (l : L) (d : D)

namespace Op

variable {D L X : Type*}

/-- The type `τ` of an operation. -/
def τ : Op D L X → RW
  | read .. => .r
  | writeVar .. => .w
  | writeVal .. => .w

/-- The location `ℓ` accessed by an operation. -/
def loc : Op D L X → L
  | read _ l => l
  | writeVar l _ => l
  | writeVal l _ => l

end Op

/-- The fence types `fence(a, b)`, `a, b ∈ {r, w}`: `fence(a, b)` keeps an `a`-operation before
it ordered with a `b`-operation after it. -/
abbrev FenceType := RW × RW

/-- A program `π = ⟨p, →⟩`: a straight-line sequence of operations and an irreflexive subset of
the increasing order on positions (positions are `0, …, |p| - 1` here). -/
structure Program (D L X : Type*) where
  /-- The operations `p`. -/
  ops : List (Op D L X)
  /-- The required orders `→`. -/
  ord : Finset (Fin ops.length × Fin ops.length)
  /-- `→` is contained in the increasing order. -/
  ord_lt : ∀ x ∈ ord, x.1 < x.2

namespace Program

variable {D L X : Type*} (π : Program D L X)

/-- The category `(τ(p[i]), τ(p[j]))` of a required order `i → j`: the fence type it needs. -/
def cat (x : Fin π.ops.length × Fin π.ops.length) : FenceType :=
  (π.ops[x.1].τ, π.ops[x.2].τ)

/-- A (multi-type) fence insertion: for every `i → j` there is `n` with `i ≤ n < j` and
`fence(τ(p[i]), τ(p[j])) ∈ f(n)`. -/
def IsFenceIns (f : Fin π.ops.length → Finset FenceType) : Prop :=
  IsIns π.ord (fun x => some (π.cat x)) f

instance (f : Fin π.ops.length → Finset FenceType) : Decidable (π.IsFenceIns f) := by
  unfold IsFenceIns; infer_instance

/-- `f` is a minimum-size fence insertion of `π` (an `OptFI(π)`). -/
def IsOptFI (f : Fin π.ops.length → Finset FenceType) : Prop :=
  IsOptIns π.ord (fun x => some (π.cat x)) f

/-- The program `⟨p, →|c⟩`: only the required orders of category `c` (e.g. `→|wr`). -/
def restrict (c : FenceType) : Program D L X where
  ops := π.ops
  ord := π.ord.filter fun x => π.cat x = c
  ord_lt := fun x hx => π.ord_lt x (mem_filter.1 hx).1

theorem restrict_ord (c : FenceType) :
    (π.restrict c).ord = Podc.FenceInsertionChain.restrict π.ord (fun x => some (π.cat x)) c := by
  ext x
  simp [restrict, Podc.FenceInsertionChain.restrict]

theorem restrict_isOptFI_iff (c : FenceType) (f : Fin π.ops.length → Finset FenceType) :
    (π.restrict c).IsOptFI f ↔
      IsOptIns (Podc.FenceInsertionChain.restrict π.ord (fun x => some (π.cat x)) c)
        (fun x => some (π.cat x)) f := by
  unfold IsOptFI
  rw [restrict_ord]
  rfl

/-- **Lemma 2.1** (independence of fence types): `λn. OptFI(⟨p,→|rr⟩)(n) ∪ OptFI(⟨p,→|rw⟩)(n) ∪
OptFI(⟨p,→|wr⟩)(n) ∪ OptFI(⟨p,→|ww⟩)(n)` is an optimal fence insertion of `⟨p, →⟩`, for any choice
of the four optima. -/
theorem lemma_2_1 (g : FenceType → Fin π.ops.length → Finset FenceType)
    (hg : ∀ c, (π.restrict c).IsOptFI (g c)) :
    π.IsOptFI fun n => g (.r, .r) n ∪ g (.r, .w) n ∪ g (.w, .r) n ∪ g (.w, .w) n := by
  have h := isOptIns_biUnion fun c => (π.restrict_isOptFI_iff c (g c)).1 (hg c)
  have e : ∀ n, (univ.biUnion fun c => g c n) =
      g (.r, .r) n ∪ g (.r, .w) n ∪ g (.w, .r) n ∪ g (.w, .w) n := by
    intro n
    ext a
    simp only [mem_biUnion, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨⟨_ | _, _ | _⟩, h⟩ <;> simp_all
    · rintro (((h | h) | h) | h) <;> exact ⟨_, h⟩
  unfold IsOptFI
  simpa only [e] using h

/-- **Lemma 2.1** (sizes): the minimum size of a fence insertion of `⟨p, →⟩` is the sum of the
minimum sizes for the four restricted programs. -/
theorem lemma_2_1_size {f : Fin π.ops.length → Finset FenceType} (hf : π.IsOptFI f)
    (g : FenceType → Fin π.ops.length → Finset FenceType)
    (hg : ∀ c, (π.restrict c).IsOptFI (g c)) :
    size f = size (g (.r, .r)) + size (g (.r, .w)) + size (g (.w, .r)) + size (g (.w, .w)) := by
  rw [IsOptIns.size_eq_sum hf fun c => (π.restrict_isOptFI_iff c (g c)).1 (hg c)]
  simp [Fintype.sum_prod_type, RW.univ_eq, add_assoc]

/-- **Lemma 2.1** with single-type optima (Definition 2.2): if `F c` is a minimum single-type
fence insertion of `⟨p, →|c⟩` for each of the four fence types `c`, then placing `fence c` in the
gaps of `F c` is an optimal fence insertion of `⟨p, →⟩`, of size `∑ c, |F c|`. -/
theorem lemma_2_1_single (F : FenceType → Finset (Fin π.ops.length))
    (hF : ∀ c, IsOptIns1 (π.restrict c).ord (F c)) :
    π.IsOptFI (fun k => univ.filter fun c => k ∈ F c) ∧
      size (fun k => univ.filter fun c => k ∈ F c) = ∑ c, (F c).card :=
  isOptIns_of_isOptIns1 fun c => by have := hF c; rw [restrict_ord] at this; exact this

/-- Every program has an optimal fence insertion. -/
theorem exists_isOptFI : ∃ f, π.IsOptFI f := exists_isOptIns _ _ π.ord_lt

/-- An insertion of a program with a required order has at least one fence. -/
theorem one_le_size {f : Fin π.ops.length → Finset FenceType} (hf : π.IsFenceIns f)
    (hne : π.ord.Nonempty) : 1 ≤ size f := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨k, -, -, hk⟩ := hf x hx _ rfl
  exact (Finset.one_le_card.2 ⟨_, hk⟩).trans (Finset.single_le_sum (f := fun k => (f k).card)
    (fun _ _ => Nat.zero_le _) (mem_univ k))

/-- An insertion with one fence of a program with a required order is optimal. -/
theorem isOptFI_of_size_one {f : Fin π.ops.length → Finset FenceType} (hf : π.IsFenceIns f)
    (h1 : size f = 1) (hne : π.ord.Nonempty) : π.IsOptFI f :=
  ⟨hf, fun _ hg => h1 ▸ π.one_le_size hg hne⟩

/-! ### Memory models: categories provided for free, merged categories -/

section MemModel

variable {Φ : Type*} [DecidableEq Φ] [Fintype Φ] (fence : FenceType → Option Φ)

/-- A fence insertion for a memory model whose fence instruction for category `c` is `fence c`
(`none`: the memory model preserves category `c` without fences). -/
def IsFenceInsIn (f : Fin π.ops.length → Finset Φ) : Prop :=
  IsIns π.ord (fun x => fence (π.cat x)) f

/-- A minimum-size fence insertion for the memory model `fence`. -/
def IsOptFIIn (f : Fin π.ops.length → Finset Φ) : Prop :=
  IsOptIns π.ord (fun x => fence (π.cat x)) f

/-- The required orders whose category is served by the fence instruction `φ`: the union of the
categories that the paper's remark merges. -/
def mergedRestrict (φ : Φ) : Finset (Fin π.ops.length × Fin π.ops.length) :=
  π.ord.filter fun x => fence (π.cat x) = some φ

/-- The remark after Lemma 2.1: "in a memory model that implicitly provides a category of orders,
no fence insertion is needed for that category … if a memory model provides the same fence
instruction for two or more fence types, we merge the corresponding categories". The
decomposition of Lemma 2.1 still holds for the merged categories. -/
theorem decomposition_merged (g : Φ → Fin π.ops.length → Finset Φ)
    (hg : ∀ φ, IsOptIns (π.mergedRestrict fence φ) (fun x => fence (π.cat x)) (g φ)) :
    π.IsOptFIIn fence fun k => univ.biUnion fun φ => g φ k :=
  isOptIns_biUnion hg

/-- The merged decomposition with single-type optima. -/
theorem decomposition_merged_single (F : Φ → Finset (Fin π.ops.length))
    (hF : ∀ φ, IsOptIns1 (π.mergedRestrict fence φ) (F φ)) :
    π.IsOptFIIn fence (fun k => univ.filter fun φ => k ∈ F φ) ∧
      size (fun k => univ.filter fun φ => k ∈ F φ) = ∑ φ, (F φ).card :=
  isOptIns_of_isOptIns1 hF

end MemModel

end Program

/-! ### Examples: Figures 1 and 2 -/

/-- Thread `T1` of the Dekker example (Figure 1(a)): `write(l₁, 1); x₁ = read(l₂)`, `1 → 2`. -/
def dekkerT1 : Program ℕ ℕ ℕ where
  ops := [.writeVal 1 1, .read 1 2]
  ord := {(0, 1)}
  ord_lt := by decide

/-- Figure 1(b): `{1 ↦ {fence(w,r)}, 2 ↦ ∅}` is an optimal fence insertion. -/
theorem dekkerT1_opt : dekkerT1.IsOptFI fun k => if k.val = 0 then {(.w, .r)} else ∅ :=
  dekkerT1.isOptFI_of_size_one (by decide) (by decide) ⟨_, mem_singleton_self _⟩

/-- Figure 2(a): `write(l₁,1); write(l₂,2); x₁ = read(l₃); x₁ = read(l₄)`, `{1 → 3, 2 → 4}`. -/
def fig2 : Program ℕ ℕ ℕ where
  ops := [.writeVal 1 1, .writeVal 2 2, .read 1 3, .read 1 4]
  ord := {(0, 2), (1, 3)}
  ord_lt := by decide

/-- Figure 2(b): fences after the second and the third operation form a fence insertion of
size 2. -/
theorem fig2b_valid :
    fig2.IsFenceIns (fun k => if k.val = 1 ∨ k.val = 2 then {(.w, .r)} else ∅) ∧
      size (fun k : Fin 4 =>
        if k.val = 1 ∨ k.val = 2 then ({(.w, .r)} : Finset FenceType) else ∅) = 2 :=
  ⟨by decide, by decide⟩

/-- Figure 2(c): a single fence after the second operation is optimal. -/
theorem fig2_opt : fig2.IsOptFI fun k => if k.val = 1 then {(.w, .r)} else ∅ :=
  fig2.isOptFI_of_size_one (by decide) (by decide) ⟨_, mem_insert_self _ _⟩

/-- `write; write; read` with the single required order `1 → 3`. -/
def wwr : Program ℕ ℕ ℕ where
  ops := [.writeVal 1 1, .writeVal 2 2, .read 1 3]
  ord := {(0, 2)}
  ord_lt := by decide

/-- Optimal fence insertions are not unique, so `OptFI(π)` in Lemma 2.1 denotes *an* optimum. -/
theorem optFI_not_unique : ∃ f g : Fin wwr.ops.length → Finset FenceType,
    wwr.IsOptFI f ∧ wwr.IsOptFI g ∧ f ≠ g := by
  refine ⟨fun k => if k.val = 0 then {(.w, .r)} else ∅,
    fun k => if k.val = 1 then {(.w, .r)} else ∅,
    wwr.isOptFI_of_size_one (by decide) (by decide) ⟨_, mem_singleton_self _⟩,
    wwr.isOptFI_of_size_one (by decide) (by decide) ⟨_, mem_singleton_self _⟩, fun h => ?_⟩
  have := congrFun h ⟨0, by decide⟩
  simp at this

/-! ### Overlapping fence instructions (outside the paper's model) -/

/-- ARMv8-style fence instructions: `dmb ish` (`full`, all four categories), `dmb ishst` (`st`,
only `ww`) and `dmb ishld` (`ld`, `rr` and `rw`). -/
inductive ArmFence
  | full
  | st
  | ld
  deriving DecidableEq, Repr

/-- The categories each ARMv8-style fence instruction preserves. -/
def ArmFence.covers : ArmFence → Finset FenceType
  | .full => univ
  | .st => {(.w, .w)}
  | .ld => {(.r, .r), (.r, .w)}

/-- A fence insertion when fence instructions may cover several categories, and a category may be
covered by several instructions. -/
def Program.IsCovIns {D L X : Type*} (π : Program D L X) (f : Fin π.ops.length → Finset ArmFence) :
    Prop :=
  ∀ x ∈ π.ord, ∃ k, x.1 ≤ k ∧ k < x.2 ∧ ∃ φ ∈ f k, π.cat x ∈ φ.covers

/-- `write(l₁,1); write(l₂,2); x = read(l₁)` with `1 → 2` (category `ww`) and `1 → 3` (`wr`). -/
def wwrOverlap : Program ℕ ℕ ℕ where
  ops := [.writeVal 1 1, .writeVal 2 2, .read 1 3]
  ord := {(0, 1), (0, 2)}
  ord_lt := by decide

/-- With overlapping fence instructions the decomposition by categories fails: one `dmb ish` after
the first operation suffices, but the `ww` part and the `wr` part each need a fence, so the sum of
the per-category optima is at least `2`. This is the setting in which the follow-up paper (Taheri,
Pourdamghani, Lesani, DISC 2019) shows NP-hardness; it is outside the model of this paper, where
each fence type preserves exactly its own category. -/
theorem overlap_sum_gt_opt :
    wwrOverlap.IsCovIns (fun k => if k.val = 0 then {.full} else ∅) ∧
      size (fun k : Fin 3 => if k.val = 0 then ({.full} : Finset ArmFence) else ∅) = 1 ∧
      ∀ g h : Fin 3 → Finset ArmFence, (wwrOverlap.restrict (.w, .w)).IsCovIns g →
        (wwrOverlap.restrict (.w, .r)).IsCovIns h → 2 ≤ size g + size h := by
  refine ⟨?_, by decide, fun g h hg hh => ?_⟩
  · unfold Program.IsCovIns
    decide
  · have one : ∀ {c} (f : Fin 3 → Finset ArmFence), (wwrOverlap.restrict c).IsCovIns f →
        (wwrOverlap.restrict c).ord.Nonempty → 1 ≤ size f := by
      intro c f hf ⟨x, hx⟩
      obtain ⟨k, -, -, φ, hφ, -⟩ := hf x hx
      exact (Finset.one_le_card.2 ⟨_, hφ⟩).trans (Finset.single_le_sum (f := fun k => (f k).card)
        (fun _ _ => Nat.zero_le _) (mem_univ k))
    have h1 := one g hg ⟨((0 : Fin 3), (1 : Fin 3)), by decide⟩
    have h2 := one h hh ⟨((0 : Fin 3), (2 : Fin 3)), by decide⟩
    omega


end Podc.FenceInsertionChain
