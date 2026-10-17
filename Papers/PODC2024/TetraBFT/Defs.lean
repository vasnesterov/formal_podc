import Mathlib
import Cslib.Foundations.Data.Finset.Quorum

/-!
# TetraBFT: votes, reports, and the safety rules (Rules 1–4)

Yu, Losa, Wang, *TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT Consensus*,
PODC 2024 (arXiv:2405.02615v2), Section 3.

* A vote `⟨vote-k, v, val⟩` is a `Vote` with `phase = k ∈ {1,2,3,4}`.
* A *report* is the content of a `proof` (resp. `suggest`) message: the highest vote-1 (vote-2),
  the highest vote-1 (vote-2) for a value different from that of the highest one ("prev"), and the
  highest vote-4 (vote-3), each as a pair `(view, value)` (`none` = no such vote).
* `Claims rep x w` is Rule 4 (for proof messages) / Rule 2 (for suggest messages).
* `ShowsSafe n f withB S rep x v` is Rule 3 (`withB = true`, with item 2(b)iiiB) and Rule 1
  (`withB = false`): a node that has received reports `rep q` from the senders `q ∈ S` determines
  that `x` is safe in view `v`.
* `IsReport voted r a b rep`: `rep` is the *honest* report, for view `r`, of a node whose votes are
  `voted` (phase `a` for `hi`/`prev`, phase `b` for `top`), i.e. it lists the maximal votes cast in
  views `< r`. It is a relational specification, so that any implementation (e.g. the paper's
  constant-storage one) can be plugged in.
-/

namespace TetraBFT

open Finset

variable {P V : Type*}

/-- A vote `⟨vote-k, view, val⟩` with `phase = k`. -/
structure Vote (V : Type*) where
  phase : ℕ
  view : ℕ
  val : V
  deriving DecidableEq

/-- The content of a proof / suggest message (Section 3.1). -/
structure Report (V : Type*) where
  /-- Highest vote-1 (proof) / vote-2 (suggest): `(view, value)`. -/
  hi : Option (ℕ × V)
  /-- Highest vote-1 / vote-2 for a value different from the value of `hi`. -/
  prev : Option (ℕ × V)
  /-- Highest vote-4 (proof) / vote-3 (suggest). -/
  top : Option (ℕ × V)
  deriving DecidableEq

/-- **Rules 2 and 4.** The report claims that `x` is safe at view `w`:
(1) `w = 0`, (2) the highest vote is for `x` in a view `≥ w`, or (3) the second-highest vote
(for a different value) is in a view `≥ w`. -/
def Claims (rep : Report V) (x : V) (w : ℕ) : Prop :=
  w = 0 ∨ (∃ u, rep.hi = some (u, x) ∧ w ≤ u) ∨ (∃ u y, rep.prev = some (u, y) ∧ w ≤ u)

/-- Items 2(b)(i)–(ii) of Rules 1/3 for one member of the quorum: its highest vote-3/vote-4 is
in a view `< w`, or in view `w` for value `x`. -/
def TopOK (rep : Report V) (x : V) (w : ℕ) : Prop :=
  ∀ u y, rep.top = some (u, y) → u < w ∨ (u = w ∧ y = x)

/-- A blocking set (`≥ f + 1` senders) all claiming that `x` is safe at `w`. -/
def Blocking (f : ℕ) (S : Finset P) (rep : P → Report V) (x : V) (w : ℕ) : Prop :=
  ∃ B ⊆ S, f + 1 ≤ B.card ∧ ∀ q ∈ B, Claims (rep q) x w

/-- **Rule 1** (`withB = false`) and **Rule 3** (`withB = true`). A node that received the
reports `rep q` of the senders `q ∈ S` (for view `v`) determines that `x` is safe in view `v` iff
`v = 0` or there is a quorum `Q ⊆ S` such that either (a) no member of `Q` reports a vote-3/4, or
(b) there is a view `w < v` with (i)–(ii) every member's highest vote-3/4 is below `w` or at `w`
for `x`, and (iii)A a blocking set claims `x` safe at `w`, or (iii)B (Rule 3 only) two blocking
sets claim two different values safe at views `w ≤ w₁ < w₂ < v`. -/
def ShowsSafe (n f : ℕ) (withB : Bool) (S : Finset P) (rep : P → Report V) (x : V) (v : ℕ) :
    Prop :=
  v = 0 ∨ ∃ Q ⊆ S, n - f ≤ Q.card ∧
    ((∀ q ∈ Q, (rep q).top = none) ∨
     ∃ w < v, (∀ q ∈ Q, TopOK (rep q) x w) ∧
       (Blocking f S rep x w ∨
        (withB = true ∧ ∃ x₁ x₂ w₁ w₂, x₁ ≠ x₂ ∧ w ≤ w₁ ∧ w₁ < w₂ ∧ w₂ < v ∧
          Blocking f S rep x₁ w₁ ∧ Blocking f S rep x₂ w₂)))

/-- Rule 1 (leader, on suggest messages). -/
abbrev Rule1 (n f : ℕ) (S : Finset P) (rep : P → Report V) (x : V) (v : ℕ) : Prop :=
  ShowsSafe n f false S rep x v

/-- Rule 3 (all nodes, on proof messages). -/
abbrev Rule3 (n f : ℕ) (S : Finset P) (rep : P → Report V) (x : V) (v : ℕ) : Prop :=
  ShowsSafe n f true S rep x v

/-- `rep` is the honest report, for view `r`, of a node whose cast votes are `voted`: `hi`
(phase `a`), `prev` (phase `a`, different value) and `top` (phase `b`) are maximal among the votes
of views `< r`. -/
structure IsReport (voted : Vote V → Prop) (r a b : ℕ) (rep : Report V) : Prop where
  hi_sound : ∀ u y, rep.hi = some (u, y) → u < r ∧ voted ⟨a, u, y⟩
  hi_max : ∀ u y, u < r → voted ⟨a, u, y⟩ → ∃ u' y', rep.hi = some (u', y') ∧ u ≤ u'
  prev_sound : ∀ u y, rep.prev = some (u, y) →
    u < r ∧ voted ⟨a, u, y⟩ ∧ ∃ u' y', rep.hi = some (u', y') ∧ y ≠ y' ∧ u ≤ u'
  prev_max : ∀ u y u' y', u < r → voted ⟨a, u, y⟩ → rep.hi = some (u', y') → y ≠ y' →
    ∃ u'' y'', rep.prev = some (u'', y'') ∧ u ≤ u''
  top_sound : ∀ u y, rep.top = some (u, y) → u < r ∧ voted ⟨b, u, y⟩
  top_max : ∀ u y, u < r → voted ⟨b, u, y⟩ → ∃ u' y', rep.top = some (u', y') ∧ u ≤ u'

/-! ### Soundness and completeness of honest claims -/

/-- **Soundness of an honest claim** (used in Lemma 8): an honest claim that `x` is safe at
`w > 0` is backed by a phase-`a` vote for `x` in a view in `[w, r)`, or by two phase-`a` votes for
different values in views in `[w, r)`. -/
theorem IsReport.claims_sound {voted : Vote V → Prop} {r a b : ℕ} {rep : Report V}
    (h : IsReport voted r a b rep) {x : V} {w : ℕ} (hc : Claims rep x w) (hw : w ≠ 0) :
    (∃ u, w ≤ u ∧ u < r ∧ voted ⟨a, u, x⟩) ∨
    (∃ u₁ y₁ u₂ y₂, w ≤ u₁ ∧ u₁ < r ∧ w ≤ u₂ ∧ u₂ < r ∧ y₁ ≠ y₂ ∧ u₁ ≤ u₂ ∧
      voted ⟨a, u₁, y₁⟩ ∧ voted ⟨a, u₂, y₂⟩) := by
  rcases hc with h0 | ⟨u, hu, hwu⟩ | ⟨u, y, hu, hwu⟩
  · exact absurd h0 hw
  · obtain ⟨hur, hv⟩ := h.hi_sound u x hu
    exact Or.inl ⟨u, hwu, hur, hv⟩
  · obtain ⟨hur, hv, u', y', hhi, hyy, huu⟩ := h.prev_sound u y hu
    obtain ⟨hu'r, hv'⟩ := h.hi_sound u' y' hhi
    exact Or.inr ⟨u, y, u', y', hwu, hur, le_trans hwu huu, hu'r, hyy, huu, hv, hv'⟩

/-- **Lemma 1** (on reports): a node that cast a phase-`a` vote for `x` in view `u < r` claims, in
its honest report for view `r`, that `x` is safe at every view `w ≤ u`. -/
theorem IsReport.claims_of_voted {voted : Vote V → Prop} {r a b : ℕ} {rep : Report V}
    (h : IsReport voted r a b rep) {x : V} {u w : ℕ} (hur : u < r) (hv : voted ⟨a, u, x⟩)
    (hwu : w ≤ u) : Claims rep x w := by
  obtain ⟨u', y', hhi, huu'⟩ := h.hi_max u x hur hv
  by_cases hxy : x = y'
  · subst hxy
    exact Or.inr (Or.inl ⟨u', hhi, le_trans hwu huu'⟩)
  · obtain ⟨u'', y'', hprev, huu''⟩ := h.prev_max u x u' y' hur hv hhi hxy
    exact Or.inr (Or.inr ⟨u'', y'', hprev, le_trans hwu huu''⟩)

/-! ### Quorum arithmetic

Generic quorum facts are in `Cslib.Foundations.Data.Finset.Quorum` (`Finset.exists_mem_notMem_of_card_le_of_lt`,
`Cslib.Quorum.exists_mem_inter_notMem_of_three_mul_lt`). -/

section Quorum

variable [Fintype P] [DecidableEq P]

/-- The correct members of a quorum form a blocking set. -/
theorem card_correct_quorum {f : ℕ} (hn : 3 * f < Fintype.card P) {F Q : Finset P}
    (hF : F.card ≤ f) (hQ : Fintype.card P - f ≤ Q.card) : f + 1 ≤ (Q.filter (· ∉ F)).card := by
  have h1 := card_filter_add_card_filter_not (s := Q) (fun q => q ∉ F)
  have h2 : (Q.filter fun q => ¬ q ∉ F).card ≤ F.card :=
    card_le_card fun q hq => by simp only [mem_filter, not_not] at hq; exact hq.2
  omega

end Quorum

end TetraBFT
