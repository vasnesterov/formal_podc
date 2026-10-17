import Cslib.Foundations.Data.Finset.Quorum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

-- CSLib candidate: Cslib/Foundations/Data/Finset/Quorum.lean (append to the existing file)

/-!
# Quorum arithmetic and vote counting: correct members and honest votes

Additions to `Cslib/Foundations/Data/Finset/Quorum.lean`. A fault-tolerant protocol with a faulty
set `F` (a `Finset α`, or a `B : Set α` bounded through `Set.ncard`) constantly uses that

* at least `n - #F` processes are correct, and a set `s` has at least `#s - #F` correct members;
* a received vector `f` that agrees with the true values `g` on the correct senders counts every
  value `b` at least as often as the correct holders of `b`, and at most `#F` more often.

## Main statements

* `Finset.card_filter_notMem_univ`: `#{x | x ∉ F} = n - #F`; `Finset.card_sub_le_card_filter_notMem`:
  `n - f ≤ #{x | x ∉ F}` for `#F ≤ f`; `Finset.card_sub_card_le_card_filter_notMem`:
  `#s - #F ≤ #{x ∈ s | x ∉ F}`; `Finset.card_sub_card_le_of_forall_notMem`: a set containing every
  correct process (or, `Finset.card_sub_card_le_of_injective_of_forall_notMem`, the identifiers of
  every correct process) has at least `n - #F` members.
* `Set.ncard` versions for a faulty set `B : Set α`: `Finset.card_sub_ncard_le_card_filter_notMem`,
  `Finset.card_sub_le_card_filter_notMem_of_ncard_le`.
* `Finset.countEq_congr`, `Finset.countEq_eq_card`: congruence and the "everybody votes `b`" count.
* `Finset.card_sub_card_le_countEq` (and `Finset.card_sub_ncard_le_countEq`): if every correct member
  of `s` reports `b`, then `b` is reported at least `#s - #F` times.
* `Finset.card_filter_notMem_and_le_countEq`, `Finset.countEq_le_card_filter_notMem_and_add_card`:
  the count of `b` in a received vector agreeing with the truth on correct senders is between the
  number of correct holders of `b` and that number plus `#F`.
* `Finset.countEq_sub_card_le_countEq` (and `Finset.countEq_sub_ncard_le_countEq`): two vectors that
  agree on the correct members of `s` have counts differing by at most `#F`.
* `Finset.exists_sum_card_filter_exists_ne_zero_le`: double counting of sender–receiver pairs that
  ever exchange a message, against the number of messages sent up to some finite time.
-/

namespace Finset

/-! ### Correct members -/

section Correct

variable {α : Type*} [DecidableEq α] {S F : Finset α} {f : ℕ}

/-- A set `s` has at least `#s - #F` members outside `F`. -/
theorem card_sub_card_le_card_filter_notMem (s F : Finset α) : #s - #F ≤ #{x ∈ s | x ∉ F} :=
  filter_notMem_eq_sdiff (s := s) (t := F) ▸ le_card_sdiff F s

variable [Fintype α]

/-- The processes outside `F` form `Fᶜ`. -/
theorem filter_notMem_univ_eq_compl (F : Finset α) : ({x | x ∉ F} : Finset α) = Fᶜ := by
  ext; simp

/-- There are exactly `n - #F` processes outside `F`, `n = Fintype.card α`. -/
theorem card_filter_notMem_univ (F : Finset α) : #{x | x ∉ F} = Fintype.card α - #F := by
  rw [filter_notMem_univ_eq_compl, card_compl]

/-- There are at least `n - f` processes outside `F` when `#F ≤ f`. -/
theorem card_sub_le_card_filter_notMem (hF : #F ≤ f) : Fintype.card α - f ≤ #{x | x ∉ F} := by
  rw [card_filter_notMem_univ]; omega

/-- A set containing every process outside `F` has at least `n - #F` members. -/
theorem card_sub_card_le_of_forall_notMem (h : ∀ x ∉ F, x ∈ S) : Fintype.card α - #F ≤ #S :=
  card_compl F ▸ card_le_card fun x hx => h x (mem_compl.1 hx)

/-- A set containing the (injective) images of all processes outside `F`, e.g. their
identifiers, has at least `n - #F` members. -/
theorem card_sub_card_le_of_injective_of_forall_notMem {β : Type*} {T : Finset β} {g : α → β}
    (hg : Function.Injective g) (h : ∀ x ∉ F, g x ∈ T) : Fintype.card α - #F ≤ #T := by
  classical
  calc Fintype.card α - #F = #(Fᶜ.image g) := by rw [card_image_of_injective _ hg, card_compl]
    _ ≤ #T := card_le_card <| image_subset_iff.2 fun x hx => h x (mem_compl.1 hx)

end Correct

section Ncard

variable {α : Type*} (B : Set α) [DecidablePred (· ∈ B)] {f : ℕ}

/-- A set `s` has at least `#s - B.ncard` members outside `B`. -/
theorem card_sub_ncard_le_card_filter_notMem [Finite α] (s : Finset α) :
    #s - B.ncard ≤ #{x ∈ s | x ∉ B} := by
  have h₁ := card_filter_add_card_filter_not (s := s) (· ∈ B)
  have h₂ := card_filter_mem_le_ncard B s
  omega

variable {B}

/-- There are at least `n - f` processes outside `B` when `B.ncard ≤ f`. -/
theorem card_sub_le_card_filter_notMem_of_ncard_le [Fintype α] (hB : B.ncard ≤ f) :
    Fintype.card α - f ≤ #{x | x ∉ B} := by
  have := card_sub_ncard_le_card_filter_notMem B univ
  rw [card_univ] at this
  omega

end Ncard

/-! ### Counting votes with a faulty set -/

section Counting

variable {α β : Type*} [DecidableEq β] {s : Finset α} {f g : α → β} {b : β}

/-- `countEq` only depends on the reports of the members of `s`. -/
theorem countEq_congr (h : ∀ a ∈ s, f a = g a) (b : β) : s.countEq f b = s.countEq g b := by
  rw [countEq, countEq, filter_congr fun a ha => by rw [h a ha]]

/-- If every member of `s` reports `b`, then `b` is reported `#s` times. -/
theorem countEq_eq_card (h : ∀ a ∈ s, f a = b) : s.countEq f b = #s := by
  rw [countEq, filter_true_of_mem h]

section Finset

variable [DecidableEq α] {F : Finset α}

/-- If every member of `s` outside `F` reports `b`, then `b` is reported at least `#s - #F`
times. -/
theorem card_sub_card_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = b) : #s - #F ≤ s.countEq f b :=
  (le_card_sdiff F s).trans (card_sdiff_le_countEq h)

/-- If `f` agrees with `g` on the members of `s` outside `F`, then `f` reports `b` at least as
often as the members of `s` outside `F` hold `b` under `g`. -/
theorem card_filter_notMem_and_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = g a) (b : β) :
    #{a ∈ s | a ∉ F ∧ g a = b} ≤ s.countEq f b :=
  card_le_card fun a ha => by
    simp only [mem_filter] at ha ⊢
    exact ⟨ha.1, (h a ha.1 ha.2.1).trans ha.2.2⟩

/-- If `f` agrees with `g` on the members of `s` outside `F`, then `f` reports `b` at most `#F`
more often than the members of `s` outside `F` hold `b` under `g`. -/
theorem countEq_le_card_filter_notMem_and_add_card (h : ∀ a ∈ s, a ∉ F → f a = g a) (b : β) :
    s.countEq f b ≤ #{a ∈ s | a ∉ F ∧ g a = b} + #F := by
  refine (card_le_card fun a ha => ?_).trans (card_union_le _ _)
  rw [mem_filter] at ha
  by_cases haF : a ∈ F
  · exact mem_union_right _ haF
  · exact mem_union_left _ (mem_filter.2 ⟨ha.1, haF, (h a ha.1 haF).symm.trans ha.2⟩)

/-- Two vote vectors that agree on the members of `s` outside `F` have counts differing by at
most `#F`. -/
theorem countEq_sub_card_le_countEq (h : ∀ a ∈ s, a ∉ F → f a = g a) (b : β) :
    s.countEq f b - #F ≤ s.countEq g b := by
  have h₁ : s.countEq f b ≤ #{a ∈ s | a ∉ F ∧ f a = b} + #F :=
    countEq_le_card_filter_notMem_and_add_card (g := f) (fun _ _ _ => rfl) b
  have h₂ : #{a ∈ s | a ∉ F ∧ f a = b} ≤ s.countEq g b :=
    card_filter_notMem_and_le_countEq (fun a ha haF => (h a ha haF).symm) b
  omega

end Finset

section Ncard

variable [Finite α] {B : Set α} [DecidablePred (· ∈ B)]

/-- If every member of `s` outside `B` reports `b`, then `b` is reported at least
`#s - B.ncard` times. -/
theorem card_sub_ncard_le_countEq (h : ∀ a ∈ s, a ∉ B → f a = b) :
    #s - B.ncard ≤ s.countEq f b :=
  (card_sub_ncard_le_card_filter_notMem B s).trans <| card_le_card fun a ha => by
    rw [mem_filter] at ha ⊢
    exact ⟨ha.1, h a ha.1 ha.2⟩

/-- Two vote vectors that agree on the members of `s` outside `B` have counts differing by at
most `B.ncard`. -/
theorem countEq_sub_ncard_le_countEq (h : ∀ a ∈ s, a ∉ B → f a = g a) (b : β) :
    s.countEq f b - B.ncard ≤ s.countEq g b := by
  have h₁ := card_sub_ncard_le_card_filter_notMem B {a ∈ s | f a = b}
  refine h₁.trans (card_le_card fun a ha => ?_)
  simp only [mem_filter] at ha ⊢
  exact ⟨ha.1.1, (h a ha.1.1 ha.2).symm.trans ha.1.2⟩

end Ncard

end Counting

/-! ### Counting sender–receiver pairs -/

section Pairs

variable {α : Type*} [Fintype α] [DecidableEq α]

open Classical in
/-- **Counting sender–receiver pairs.** Let `f τ q p` be the number of messages that `q` sends
to `p` at time `τ`. If `X` and `Y` are disjoint, then up to some finite time `N` the members of `X`
send (to processes other than themselves) at least as many messages as there are pairs
`(q, p) ∈ X × Y` such that `q` sends something to `p` at some time. -/
theorem exists_sum_card_filter_exists_ne_zero_le (X Y : Finset α) (hXY : Disjoint X Y)
    (f : ℕ → α → α → ℕ) :
    ∃ N, ∑ p ∈ Y, #{q ∈ X | ∃ τ, f τ q p ≠ 0} ≤
      ∑ τ ∈ range N, ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), f τ q p := by
  let τ₀ : α × α → ℕ := fun qp => if hh : ∃ τ, f τ qp.1 qp.2 ≠ 0 then Classical.choose hh else 0
  let N := (univ : Finset (α × α)).sup τ₀ + 1
  refine ⟨N, ?_⟩
  have key : ∀ q p, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) ≤ ∑ τ ∈ range N, f τ q p := by
    intro q p
    split_ifs with hh
    · have hlt : τ₀ (q, p) < N := Nat.lt_succ_of_le (le_sup (f := τ₀) (mem_univ (q, p)))
      have hτ : τ₀ (q, p) = Classical.choose hh := by simp [τ₀, hh]
      calc 1 ≤ f (τ₀ (q, p)) q p := by
              rw [hτ]; exact Nat.one_le_iff_ne_zero.mpr (Classical.choose_spec hh)
        _ ≤ ∑ τ ∈ range N, f τ q p :=
              single_le_sum (f := fun τ => f τ q p) (fun _ _ => Nat.zero_le _) (mem_range.mpr hlt)
    · exact Nat.zero_le _
  calc ∑ p ∈ Y, #{q ∈ X | ∃ τ, f τ q p ≠ 0}
      = ∑ p ∈ Y, ∑ q ∈ X, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) := by
        refine sum_congr rfl fun p _ => ?_
        rw [card_eq_sum_ones, sum_filter]
    _ = ∑ q ∈ X, ∑ p ∈ Y, (if ∃ τ, f τ q p ≠ 0 then 1 else 0) := sum_comm
    _ ≤ ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), ∑ τ ∈ range N, f τ q p := by
        refine sum_le_sum fun q hq => ?_
        calc ∑ p ∈ Y, (if ∃ τ, f τ q p ≠ 0 then 1 else 0)
            ≤ ∑ p ∈ Y, ∑ τ ∈ range N, f τ q p := sum_le_sum fun p _ => key q p
          _ ≤ ∑ p ∈ univ.filter (· ≠ q), ∑ τ ∈ range N, f τ q p := by
              refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => Nat.zero_le _
              refine mem_filter.mpr ⟨mem_univ _, fun h => ?_⟩
              subst h
              exact disjoint_left.mp hXY hq hp
    _ = ∑ τ ∈ range N, ∑ q ∈ X, ∑ p ∈ univ.filter (· ≠ q), f τ q p := by
        rw [sum_comm (s := range N)]
        refine sum_congr rfl fun q _ => ?_
        rw [sum_comm (s := range N)]

end Pairs

end Finset
