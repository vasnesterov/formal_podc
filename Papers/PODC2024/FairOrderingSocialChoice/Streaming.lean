import Papers.PODC2024.FairOrderingSocialChoice.RankedPairs

/-!
# Streaming Ranked Pairs (Section 5, Algorithm 3)

Ordering votes are finite lists (Def. 2.2); `σ' ` *extends* `σ` if every `σ i` is a prefix of
`σ' i`. At any time, the algorithm sees the current votes `σ : ι → List α`.

* `V σ`: transactions on which every replica has voted; `Partial σ u`: voted by some but not all.
* `cnt σ a b`: number of replicas whose vote has `a` before `b` (the weight of Def. 3.2, times `n`).
* The *streamed ordering graph* (Def. 5.7) has an extra vertex `v̂` (`none : Option α`), edges
  `(τ, v̂)` for all `τ ∈ V σ` and `(v̂, τ)` iff some partially-voted transaction precedes `τ` in
  some vote (`FutIn σ τ`). Both are indeterminate from the start.
* `InR σ a x` (`x ∈ R_a`: `w(x, a) = 0`) and `InP σ b x` (`x ∈ P_b`: `w(x, b) = 1`) (Def. 5.5);
  `U σ (a, b) = (V \ (R_a ∪ P_b)) ∪ {v̂}`.
* `dec σ tb e ∈ {acc, rej, ind}`: Algorithm 3's decision on the edge `e` between transactions of
  `V σ`. Edges are processed in decreasing weight, ties broken by a fixed global injective rule
  `tb` (`key`). An edge is rejected if `H|U` has a determinate path back, accepted (determinate) if
  `H|U` has no path back at all, and indeterminate otherwise; accepted and indeterminate edges are
  added to `H`.
* `output σ tb`: the transactions output (see below), ordered by `detLt` (determinate edges).

## Output rule (repaired)

Algorithm 3 outputs "the topological sort of `H` (determinate edges only), up to but not including
the first transaction bordering an indeterminate edge". Literally, *every* `τ ∈ V` borders the
indeterminate edge `(τ, v̂)` added at initialization, so the output would always be empty. We read
"bordering" as: incident to an indeterminate edge between two transactions, or the target of the
edge `(v̂, τ)` (`Clean`). For a clean `τ`, all edges between `τ` and other transactions are
determinate, so the clean transactions that precede every non-clean one in the topological order
are well defined: `output σ tb = {x | Clean x ∧ ∀ dirty y, detLt x y}`.

## Main results

* `observation_5_4`, `lemma_5_6`: Ranked Pairs on a complete profile always chooses weight-1 edges;
  chosen paths from `b` to `a` avoid `R_a ∪ P_b`.
* `dec_mono`: decisions are stable under extension of the votes (the core of Lemma 5.8 and
  Corollary 5.9; the paper's one-line proof of Corollary 5.9 does not argue this).
* `lemma_5_8`: determinate decisions agree with non-streaming Ranked Pairs on any counterfactual
  completion of the votes (with the same tie-breaking rule).
* `theorem_5_10`: the output is an initial segment of Ranked Pairs' output on any completion.
* `corollary_5_9`: Algorithm 3 is monotonic.
-/

namespace Podc.FairOrderingSocialChoice.Streaming

open Finset Relation RP

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-! ### Votes as lists -/

/-- `a` precedes `b` in the vote `l`. -/
def Before (l : List α) (a b : α) : Prop := b ∈ l ∧ l.idxOf a < l.idxOf b

theorem Before.mem_left {l : List α} {a b : α} (h : Before l a b) : a ∈ l :=
  List.idxOf_lt_length_iff.1 (h.2.trans (List.idxOf_lt_length_of_mem h.1))

theorem Before.irrefl (l : List α) (a : α) : ¬ Before l a a := fun h => lt_irrefl _ h.2

theorem Before.trans {l : List α} {a b c : α} (h₁ : Before l a b) (h₂ : Before l b c) :
    Before l a c := ⟨h₂.1, h₁.2.trans h₂.2⟩

theorem Before.asymm {l : List α} {a b : α} (h₁ : Before l a b) (h₂ : Before l b a) : False :=
  lt_asymm h₁.2 h₂.2

theorem Before.total {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    Before l a b ∨ Before l b a := by
  rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h | h | h
  · exact Or.inl ⟨hb, h⟩
  · exact absurd ((List.idxOf_inj ha).1 h) hab
  · exact Or.inr ⟨ha, h⟩

/-- Order between transactions already in a prefix does not change when the vote is extended. -/
theorem before_prefix_iff {l l' : List α} (h : l <+: l') {a b : α} (hb : b ∈ l) :
    Before l' a b ↔ Before l a b := by
  have hb' : l'.idxOf b = l.idxOf b := (h.idxOf_eq_of_mem hb).symm
  constructor
  · rintro ⟨-, hlt⟩
    have ha : a ∈ l := (h.mem_iff_idxOf_lt_length a).2
      (hlt.trans_le (hb' ▸ (List.idxOf_lt_length_of_mem hb).le))
    refine ⟨hb, ?_⟩
    rw [h.idxOf_eq_of_mem ha, h.idxOf_eq_of_mem hb]; exact hlt
  · intro hab
    refine ⟨h.subset hb, ?_⟩
    rw [← h.idxOf_eq_of_mem hab.mem_left, ← h.idxOf_eq_of_mem hb]; exact hab.2

/-! ### The streamed ordering graph -/

/-- Transactions on which every replica has voted. -/
def V (σ : ι → List α) : Set α := {x | ∀ i, x ∈ σ i}

/-- Transactions voted on by some but not all replicas. -/
def Partial (σ : ι → List α) (x : α) : Prop := (∃ i, x ∈ σ i) ∧ x ∉ V σ

/-- Number of replicas whose vote puts `a` before `b`. -/
noncomputable def cnt (σ : ι → List α) (a b : α) : ℕ := by
  classical exact #{i | Before (σ i) a b}

/-- `w(v̂, b) = 1` in the streamed ordering graph (Def. 5.7): some partially-voted transaction
precedes `b` in some vote. -/
def FutIn (σ : ι → List α) (b : α) : Prop := ∃ u, Partial σ u ∧ ∃ i, Before (σ i) u b

/-- `x ∈ R_a` (Def. 5.5): no replica puts `x` before `a`. -/
def InR (σ : ι → List α) (a x : α) : Prop := x ≠ a ∧ cnt σ x a = 0

/-- `x ∈ P_b` (Def. 5.5): every replica puts `x` before `b`. -/
def InP (σ : ι → List α) (b x : α) : Prop := x ≠ b ∧ cnt σ x b = Fintype.card ι

/-- `U_{a,b} = (V \ (R_a ∪ P_b)) ∪ {v̂}`; the vertex `v̂` is `none`. -/
def U (σ : ι → List α) (e : α × α) : Option α → Prop
  | none => True
  | some x => x ∈ V σ ∧ ¬ InR σ e.1 x ∧ ¬ InP σ e.2 x

/-- Processing order: decreasing weight, ties broken by the fixed rule `tb`. -/
noncomputable def key (σ : ι → List α) (tb : α × α → ℕ) (e : α × α) : ℕ ×ₗ ℕ :=
  toLex (Fintype.card ι - cnt σ e.1 e.2, tb e)

/-- Status of an edge in Algorithm 3. -/
inductive Decision
  | acc
  | rej
  | ind
  deriving DecidableEq

open Decision

/-- Edges of `H` (accepted or indeterminate) present when `e` is processed, given the decisions
`d` on earlier edges, together with the initial edges at `v̂`. -/
def edgeH (σ : ι → List α) (tb : α × α → ℕ) (e : α × α) (d : α × α → Decision) :
    Option α → Option α → Prop
  | some a, some b => key σ tb (a, b) < key σ tb e ∧ d (a, b) ≠ rej
  | some a, none => a ∈ V σ
  | none, some b => b ∈ V σ ∧ FutIn σ b
  | none, none => False

/-- Determinate edges of `H` present when `e` is processed. -/
def detH (σ : ι → List α) (tb : α × α → ℕ) (e : α × α) (d : α × α → Decision) :
    Option α → Option α → Prop
  | some a, some b => key σ tb (a, b) < key σ tb e ∧ d (a, b) = acc
  | _, _ => False

/-- A relation restricted to vertices satisfying `P`. -/
def restr {γ : Type*} (P : γ → Prop) (R : γ → γ → Prop) (x y : γ) : Prop := P x ∧ P y ∧ R x y

/-- Pairs of distinct fully-voted transactions: the edges Algorithm 3 iterates over. -/
def IsEdge (σ : ι → List α) (e : α × α) : Prop := e.1 ∈ V σ ∧ e.2 ∈ V σ ∧ e.1 ≠ e.2

open Classical in
/-- One step of Algorithm 3 on the edge `e = (τᵢ, τⱼ)`. -/
noncomputable def step (σ : ι → List α) (tb : α × α → ℕ) (e : α × α) (d : α × α → Decision) :
    Decision :=
  if IsEdge σ e then
    if ReflTransGen (restr (U σ e) (detH σ tb e d)) (some e.2) (some e.1) then rej
    else if ReflTransGen (restr (U σ e) (edgeH σ tb e d)) (some e.2) (some e.1) then ind
    else acc
  else rej

/-- **Algorithm 3**: the decision on each edge, by well-founded recursion on the processing
order. -/
noncomputable def dec (σ : ι → List α) (tb : α × α → ℕ) : α × α → Decision :=
  (InvImage.wf (key σ tb) wellFounded_lt).fix fun e rec =>
    step σ tb e fun e' => if h : key σ tb e' < key σ tb e then rec e' h else rej

variable {σ σ' σc : ι → List α} {tb : α × α → ℕ}

theorem step_congr {e : α × α} {d d' : α × α → Decision}
    (h : ∀ e', key σ tb e' < key σ tb e → d e' = d' e') : step σ tb e d = step σ tb e d' := by
  have h1 : edgeH σ tb e d = edgeH σ tb e d' := by
    funext x y
    cases x <;> cases y <;> simp only [edgeH]
    exact propext ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h _ h₁ ▸ h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, (h _ h₁).symm ▸ h₂⟩⟩
  have h2 : detH σ tb e d = detH σ tb e d' := by
    funext x y
    cases x <;> cases y <;> simp only [detH]
    exact propext ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h _ h₁ ▸ h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, (h _ h₁).symm ▸ h₂⟩⟩
  unfold step; rw [h1, h2]

theorem dec_eq (e : α × α) : dec σ tb e = step σ tb e (dec σ tb) := by
  unfold dec
  rw [WellFounded.fix_eq]
  apply step_congr
  intro e' he'
  simp only [he', dite_true]

theorem dec_of_not_isEdge {e : α × α} (h : ¬ IsEdge σ e) : dec σ tb e = rej := by
  rw [dec_eq]; unfold step; simp [h]

theorem isEdge_of_dec_ne_rej {e : α × α} (h : dec σ tb e ≠ rej) : IsEdge σ e := by
  by_contra h'; exact h (dec_of_not_isEdge h')

theorem dec_eq_rej_iff {e : α × α} (he : IsEdge σ e) :
    dec σ tb e = rej ↔
      ReflTransGen (restr (U σ e) (detH σ tb e (dec σ tb))) (some e.2) (some e.1) := by
  rw [dec_eq]; unfold step
  simp only [he, ite_true]
  split_ifs with h1 h2 <;> simp_all

theorem dec_eq_acc_iff {e : α × α} (he : IsEdge σ e) :
    dec σ tb e = acc ↔
      ¬ ReflTransGen (restr (U σ e) (edgeH σ tb e (dec σ tb))) (some e.2) (some e.1) := by
  rw [dec_eq]; unfold step
  simp only [he, ite_true]
  split_ifs with h1 h2 <;> simp_all
  -- a determinate path is in particular a path of `H`
  refine ReflTransGen.mono (fun x y hxy => ?_) _ _ h1
  obtain ⟨hx, hy, h⟩ := hxy
  refine ⟨hx, hy, ?_⟩
  cases x <;> cases y <;> simp_all [detH, edgeH]

/-! ### Counting -/

section Counting

theorem cnt_eq_card_iff {a b : α} : cnt σ a b = Fintype.card ι ↔ ∀ i, Before (σ i) a b := by
  classical
  unfold cnt
  rw [← card_univ, card_filter_eq_iff]; simp

theorem cnt_eq_zero_iff {a b : α} : cnt σ a b = 0 ↔ ∀ i, ¬ Before (σ i) a b := by
  classical
  unfold cnt
  rw [card_filter_eq_zero_iff]; simp

theorem cnt_le (a b : α) : cnt σ a b ≤ Fintype.card ι := by
  classical unfold cnt; exact card_filter_le _ _

theorem cnt_add_cnt {a b : α} (ha : a ∈ V σ) (hb : b ∈ V σ) (hab : a ≠ b) :
    cnt σ a b + cnt σ b a = Fintype.card ι := by
  classical
  unfold cnt
  rw [← card_union_of_disjoint]
  · convert card_univ (α := ι)
    ext i; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
    exact Before.total (ha i) (hb i) hab
  · rw [disjoint_filter]; intro i _ h h'; exact h.asymm h'

theorem cnt_eq_zero_iff_of_mem {a b : α} (ha : a ∈ V σ) (hb : b ∈ V σ) (hab : a ≠ b) :
    cnt σ a b = 0 ↔ cnt σ b a = Fintype.card ι := by
  have := cnt_add_cnt ha hb hab; omega

end Counting

/-! ### Weight-1 and weight-0 edges -/

/-- Algorithm 3 accepts every edge of weight 1 (determinately). -/
theorem dec_of_cnt_full {a b : α} (he : IsEdge σ (a, b)) (h : cnt σ a b = Fintype.card ι) :
    dec σ tb (a, b) = acc := by
  rw [dec_eq_acc_iff he]
  intro hp
  rcases hp.cases_tail with h' | ⟨c, -, hc⟩
  · exact he.2.2 (Option.some_injective _ h')
  · exact hc.2.1.2.2 ⟨he.2.2, h⟩

/-- Algorithm 3 rejects every edge of weight 0. -/
theorem dec_of_cnt_zero [Nonempty ι] {a b : α} (he : IsEdge σ (a, b)) (h : cnt σ a b = 0) :
    dec σ tb (a, b) = rej := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hba : cnt σ b a = Fintype.card ι := (cnt_eq_zero_iff_of_mem he.1 he.2.1 he.2.2).1 h
  rw [dec_eq_rej_iff he]
  refine ReflTransGen.single ⟨⟨he.2.1, ?_, ?_⟩, ⟨he.1, ?_, ?_⟩, ?_, ?_⟩
  · rintro ⟨-, h'⟩; dsimp only at h'; omega
  · rintro ⟨h', -⟩; exact h' rfl
  · rintro ⟨h', -⟩; exact h' rfl
  · rintro ⟨-, h'⟩; dsimp only at h'; omega
  · show toLex (_, _) < toLex (_, _)
    simp only [hba, h, Nat.sub_self, Nat.sub_zero]
    exact Prod.Lex.toLex_lt_toLex.2 (Or.inl hn)
  · exact dec_of_cnt_full ⟨he.2.1, he.1, he.2.2.symm⟩ hba

/-! ### Paths through `Option α` -/

omit [DecidableEq α] in
/-- A path whose steps all go between `some`-vertices projects to `α`. -/
theorem path_somes {R : Option α → Option α → Prop} {Q : α → α → Prop}
    (hnone : ∀ y, ¬ R none y) (hQ : ∀ a b, R (some a) (some b) → Q a b) {u v : α}
    (h : ReflTransGen R (some u) (some v)) : ReflTransGen Q u v := by
  suffices H : ∀ x, ReflTransGen R x (some v) → ∀ u, x = some u → ReflTransGen Q u v from
    H _ h u rfl
  intro x hx
  induction hx using ReflTransGen.head_induction_on with
  | refl => intro u hu; cases hu; exact .refl
  | head hxw hw ih =>
    intro u hu
    subst hu
    rename_i w
    cases w with
    | none =>
      rcases hw.cases_head with h' | ⟨c, hc, -⟩
      · cases h'
      · exact absurd hc (hnone c)
    | some b => exact .head (hQ _ _ hxw) (ih b rfl)

/-- Annotate a path with "reachable from the start and reaching the end". -/
theorem path_annot {β : Type*} {R : β → β → Prop} {b a : β} (h : ReflTransGen R b a) :
    ReflTransGen (fun x y => R x y ∧ ReflTransGen R b x ∧ ReflTransGen R y a) b a := by
  suffices H : ∀ c, ReflTransGen R c a → ReflTransGen R b c →
      ReflTransGen (fun x y => R x y ∧ ReflTransGen R b x ∧ ReflTransGen R y a) c a from
    H b h .refl
  intro c hc
  induction hc using ReflTransGen.head_induction_on with
  | refl => intro _; exact .refl
  | head hcd hda ih => intro hbc; exact .head ⟨hcd, hbc, hda⟩ (ih (hbc.tail hcd))

/-! ### Stability under extension (core of Lemma 5.8 and Corollary 5.9) -/

section Mono

variable (hpre : ∀ i, σ i <+: σ' i)
include hpre

omit [Fintype ι] [DecidableEq α] in
theorem V_mono : V σ ⊆ V σ' := fun _ hx i => (hpre i).subset (hx i)

theorem cnt_eq_of_mem {a b : α} (hb : b ∈ V σ) : cnt σ' a b = cnt σ a b := by
  classical
  unfold cnt
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact before_prefix_iff (hpre i) (hb i)

theorem key_eq_of_mem {e : α × α} (hb : e.2 ∈ V σ) : key σ' tb e = key σ tb e := by
  unfold key; rw [cnt_eq_of_mem hpre hb]

omit [Fintype ι] in
theorem futIn_of_new {y b : α} (hy : y ∉ V σ) (hb : b ∈ V σ) {i : ι} (h : Before (σ' i) y b) :
    FutIn σ b := by
  have h' := (before_prefix_iff (hpre i) (hb i)).1 h
  exact ⟨y, ⟨⟨i, h'.mem_left⟩, hy⟩, i, h'⟩

omit [Fintype ι] in
theorem futIn_back {b : α} (hb : b ∈ V σ) (h : FutIn σ' b) : FutIn σ b := by
  obtain ⟨u, ⟨-, hu⟩, i, hi⟩ := h
  exact futIn_of_new hpre (fun h => hu (V_mono hpre h)) hb hi

theorem U_iff {e : α × α} (he : IsEdge σ e) {x : α} (hx : x ∈ V σ) :
    U σ' e (some x) ↔ U σ e (some x) := by
  simp only [U, InR, InP, cnt_eq_of_mem hpre he.1, cnt_eq_of_mem hpre he.2.1]
  exact ⟨fun h => ⟨hx, h.2⟩, fun h => ⟨V_mono hpre hx, h.2⟩⟩

open Classical in
/-- Vertices of the streamed graph of an extension `σ'` mapped to that of `σ`: transactions not
fully voted on in `σ` collapse into the future vertex `v̂`. -/
noncomputable def collapse (σ : ι → List α) : Option α → Option α
  | some x => if x ∈ V σ then some x else none
  | none => none

/-- **Stability.** If the votes `σ'` extend `σ`, every determinate decision of Algorithm 3 on
`σ` (accept or reject an edge between transactions of `V σ`) is taken again on `σ'`. -/
theorem dec_mono [Nonempty ι] : ∀ e : α × α, e.1 ∈ V σ → e.2 ∈ V σ →
    (dec σ tb e = acc → dec σ' tb e = acc) ∧ (dec σ tb e = rej → dec σ' tb e = rej) := by
  intro e
  induction e using (InvImage.wf (key σ tb) wellFounded_lt).induction with
  | _ e ih =>
  intro h1 h2
  by_cases hne : e.1 = e.2
  · have h₁ : ¬ IsEdge σ e := fun h => h.2.2 hne
    have h₂ : ¬ IsEdge σ' e := fun h => h.2.2 hne
    simp [dec_of_not_isEdge h₁, dec_of_not_isEdge h₂]
  have he : IsEdge σ e := ⟨h1, h2, hne⟩
  have he' : IsEdge σ' e := ⟨V_mono hpre h1, V_mono hpre h2, hne⟩
  have hkey : key σ' tb e = key σ tb e := key_eq_of_mem hpre h2
  have IH : ∀ p q, p ∈ V σ → q ∈ V σ → key σ tb (p, q) < key σ tb e →
      (dec σ tb (p, q) = acc → dec σ' tb (p, q) = acc) ∧
        (dec σ tb (p, q) = rej → dec σ' tb (p, q) = rej) :=
    fun p q hp hq hlt => ih (p, q) hlt hp hq
  -- determinate paths of `σ` are determinate paths of `σ'`
  have hA : ReflTransGen (restr (U σ e) (detH σ tb e (dec σ tb))) (some e.2) (some e.1) →
      ReflTransGen (restr (U σ' e) (detH σ' tb e (dec σ' tb))) (some e.2) (some e.1) := by
    apply ReflTransGen.mono
    rintro x y ⟨hx, hy, hxy⟩
    cases x <;> cases y <;> simp only [detH] at hxy
    rename_i p q
    have hpq : IsEdge σ (p, q) := isEdge_of_dec_ne_rej (by rw [hxy.2]; decide)
    refine ⟨(U_iff hpre he hpq.1).2 hx, (U_iff hpre he hpq.2.1).2 hy, ?_,
      (IH p q hpq.1 hpq.2.1 hxy.1).1 hxy.2⟩
    rw [key_eq_of_mem hpre hpq.2.1, hkey]; exact hxy.1
  -- paths of `σ'` collapse to paths of `σ`
  have hU : ∀ z, U σ' e z → U σ e (collapse σ z) := by
    rintro (_ | z) hz
    · trivial
    · simp only [collapse]
      split_ifs with hzV
      · exact (U_iff hpre he hzV).1 hz
      · trivial
  have hB : ReflTransGen (restr (U σ' e) (edgeH σ' tb e (dec σ' tb))) (some e.2) (some e.1) →
      ReflTransGen (restr (U σ e) (edgeH σ tb e (dec σ tb))) (some e.2) (some e.1) := by
    intro h
    have := ReflTransGen.lift' (collapse σ)
      (p := restr (U σ e) (edgeH σ tb e (dec σ tb))) ?_ _ _ h
    · have c1 : collapse σ (some e.1) = some e.1 := by simp [collapse, h1]
      have c2 : collapse σ (some e.2) = some e.2 := by simp [collapse, h2]
      simpa only [Function.onFun, c1, c2] using this
    rintro x y ⟨hx, hy, hxy⟩
    show ReflTransGen _ (collapse σ x) (collapse σ y)
    suffices collapse σ x = collapse σ y ∨
        edgeH σ tb e (dec σ tb) (collapse σ x) (collapse σ y) by
      rcases this with h | h
      · rw [h]
      · exact .single ⟨hU x hx, hU y hy, h⟩
    cases x <;> cases y
    · simp [edgeH] at hxy
    · rename_i q
      obtain ⟨-, hfut⟩ := hxy
      simp only [collapse]
      split_ifs with hq
      · exact Or.inr ⟨hq, futIn_back hpre hq hfut⟩
      · exact Or.inl rfl
    · rename_i p
      simp only [collapse]
      split_ifs with hp
      · exact Or.inr hp
      · exact Or.inl rfl
    · rename_i p q
      obtain ⟨hlt, hrej⟩ := hxy
      have hpq : IsEdge σ' (p, q) := isEdge_of_dec_ne_rej hrej
      simp only [collapse]
      split_ifs with hp hq hq
      · right
        have hlt' : key σ tb (p, q) < key σ tb e := by
          rw [← key_eq_of_mem hpre hq, ← hkey]; exact hlt
        exact ⟨hlt', fun h => hrej ((IH p q hp hq hlt').2 h)⟩
      · exact Or.inr hp
      · right
        refine ⟨hq, ?_⟩
        have hne0 : cnt σ' p q ≠ 0 := fun h0 => hrej (dec_of_cnt_zero hpq h0)
        obtain ⟨i, hi⟩ : ∃ i, Before (σ' i) p q := by
          by_contra hc
          push Not at hc
          exact hne0 (cnt_eq_zero_iff.2 hc)
        exact futIn_of_new hpre hp hq hi
      · exact Or.inl rfl
  constructor
  · intro hacc
    rw [dec_eq_acc_iff he] at hacc
    rw [dec_eq_acc_iff he']
    exact fun h => hacc (hB h)
  · intro hrej
    rw [dec_eq_rej_iff he] at hrej
    rw [dec_eq_rej_iff he']
    exact hA hrej

end Mono

/-! ### Complete profiles: the non-streaming Ranked Pairs -/

section Complete

/-- All replicas have voted on the same (finite) set of transactions: the counterfactual input of
Lemma 5.8, on which non-streaming Ranked Pairs runs on the set `V σc`. -/
def Complete (σc : ι → List α) : Prop := ∀ i j x, x ∈ σc i → x ∈ σc j

theorem key_injective (σ : ι → List α) (htb : Function.Injective tb) :
    Function.Injective (key σ tb) := fun _ _ h =>
  htb (congrArg (fun p : ℕ ×ₗ ℕ => (ofLex p).2) h)

/-- The Ranked Pairs output on a complete profile, as `RP.rpLt`. -/
abbrev rpOut (σc : ι → List α) (tb : α × α → ℕ) : α → α → Prop := rpLt (V σc) (key σc tb)

/-- Ranked Pairs' accepted edges on `σc`. -/
abbrev rpAcc (σc : ι → List α) (tb : α × α → ℕ) (a b : α) : Prop :=
  accepted (V σc) (key σc tb) (a, b)

theorem rpOut_irrefl (htb : Function.Injective tb) (x : α) : ¬ rpOut σc tb x x :=
  rpLt_irrefl (fun _ _ _ _ _ _ h => key_injective σc htb h) x

variable (hc : Complete σc)
include hc

omit [Fintype ι] in
theorem not_futIn (b : α) : ¬ FutIn σc b := by
  rintro ⟨u, ⟨⟨i, hi⟩, hu⟩, -⟩
  exact hu fun j => hc i j u hi

omit hc in
theorem transGen_before {l : List α} {x y : α} (h : TransGen (Before l) x y) : Before l x y := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact ih.trans h

omit hc in
/-- **Observation 5.4.** On a complete profile, Ranked Pairs chooses every edge of weight 1. -/
theorem observation_5_4 [Nonempty ι] {a b : α} (ha : a ∈ V σc) (hb : b ∈ V σc)
    (h : cnt σc a b = Fintype.card ι) : rpAcc σc tb a b := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine accepted_of_acyclic (U := fun x y => cnt σc x y = Fintype.card ι) ?_ ha hb h ?_
  · intro x hx
    have : TransGen (Before (σc i₀)) x x :=
      tg_mono (fun _ _ h => cnt_eq_card_iff.1 h i₀) hx
    exact Before.irrefl _ _ (transGen_before this)
  · intro x y hxy
    have h1 := hxy.1
    have h2 := cnt_le (σ := σc) x y
    simp only [key, h, Nat.sub_self] at h1
    rcases Prod.Lex.toLex_lt_toLex.1 h1 with h1 | ⟨h1, -⟩
    · omega
    · simp only at h1 ⊢; omega

omit hc in
/-- **Lemma 5.6.** If Ranked Pairs chooses all edges of a path from `b` to `a` (on a complete
profile), no transaction on the path is in `R_a` or `P_b`. -/
theorem lemma_5_6 [Nonempty ι] (htb : Function.Injective tb) {a b x : α}
    (h₁ : ReflTransGen (rpAcc σc tb) b x) (h₂ : ReflTransGen (rpAcc σc tb) x a) :
    ¬ InR σc a x ∧ ¬ InP σc b x := by
  constructor
  · rintro ⟨hxa, h0⟩
    have hxa' : rpOut σc tb x a := by
      rcases reflTransGen_iff_eq_or_transGen.1 h₂ with h | h
      · exact absurd h.symm hxa
      · exact h
    obtain ⟨hxV, haV⟩ := mem_of_rpLt hxa'
    have := observation_5_4 (tb := tb) haV hxV
      ((cnt_eq_zero_iff_of_mem hxV haV hxa).1 h0)
    exact rpOut_irrefl htb x (hxa'.tail this)
  · rintro ⟨hxb, hn⟩
    have hbx : rpOut σc tb b x := by
      rcases reflTransGen_iff_eq_or_transGen.1 h₁ with h | h
      · exact absurd h hxb
      · exact h
    obtain ⟨hbV, hxV⟩ := mem_of_rpLt hbx
    exact rpOut_irrefl htb b (hbx.tail (observation_5_4 hxV hbV hn))

/-- On a complete profile, Algorithm 3 never leaves an edge indeterminate and coincides with
non-streaming Ranked Pairs (same processing order). -/
theorem dec_complete [Nonempty ι] (htb : Function.Injective tb) :
    ∀ e : α × α, (dec σc tb e = acc ↔ accepted (V σc) (key σc tb) e) ∧ dec σc tb e ≠ ind := by
  intro e
  induction e using (InvImage.wf (key σc tb) wellFounded_lt).induction with
  | _ e ih =>
  by_cases he : IsEdge σc e
  swap
  · rw [dec_of_not_isEdge he]
    refine ⟨⟨fun h => (by cases h), fun h => absurd (mem_of_accepted h) he⟩, by decide⟩
  obtain ⟨a, b⟩ := e
  -- earlier decisions are accept/reject and agree with Ranked Pairs
  have IH : ∀ p q, key σc tb (p, q) < key σc tb (a, b) →
      (dec σc tb (p, q) ≠ rej ↔ rpAcc σc tb p q) ∧ (dec σc tb (p, q) = acc ↔ rpAcc σc tb p q) := by
    intro p q hlt
    obtain ⟨h1, h2⟩ := ih (p, q) hlt
    refine ⟨?_, h1⟩
    show _ ↔ accepted _ _ (p, q)
    rw [← h1]
    rcases hd : dec σc tb (p, q) <;> simp_all
  have hpath1 : ReflTransGen (restr (U σc (a, b)) (edgeH σc tb (a, b) (dec σc tb))) (some b)
      (some a) → ReflTransGen (before (V σc) (key σc tb) (a, b)) b a := by
    apply path_somes
    · rintro (_ | y) ⟨-, -, h⟩
      · exact h
      · exact not_futIn hc y h.2
    · rintro p q ⟨-, -, hlt, hne⟩
      exact ⟨hlt, (IH p q hlt).1.1 hne⟩
  have hpath2 : ReflTransGen (before (V σc) (key σc tb) (a, b)) b a →
      ReflTransGen (restr (U σc (a, b)) (detH σc tb (a, b) (dec σc tb))) (some b) (some a) := by
    intro h
    have h' := path_annot h
    refine ReflTransGen.lift some (fun x y hxy => ?_) _ _ h'
    obtain ⟨hB, hbx, hya⟩ := hxy
    have hacc : rpAcc σc tb x y := hB.2
    have hmem := mem_of_accepted hacc
    have toAcc : ∀ {u v}, ReflTransGen (before (V σc) (key σc tb) (a, b)) u v →
        ReflTransGen (rpAcc σc tb) u v := fun h => rtg_mono (fun _ _ h => h.2) h
    have L1 := lemma_5_6 htb (toAcc hbx) (toAcc (hya.head hB))
    have L2 := lemma_5_6 htb (toAcc (hbx.tail hB)) (toAcc hya)
    exact ⟨⟨hmem.1, L1⟩, ⟨hmem.2.1, L2⟩, hB.1, (IH x y hB.1).2.2 hacc⟩
  have hdet_any : ReflTransGen (restr (U σc (a, b)) (detH σc tb (a, b) (dec σc tb))) (some b)
      (some a) → ReflTransGen (restr (U σc (a, b)) (edgeH σc tb (a, b) (dec σc tb))) (some b)
      (some a) := by
    apply ReflTransGen.mono
    rintro (_ | x) (_ | y) ⟨hx, hy, h⟩ <;> simp only [detH] at h
    exact ⟨hx, hy, h.1, by rw [h.2]; decide⟩
  have hacc_iff : rpAcc σc tb a b ↔ ¬ ReflTransGen (before (V σc) (key σc tb) (a, b)) b a := by
    rw [rpAcc, accepted_iff]
    exact ⟨fun h => h.2.2.2, fun h => ⟨he.1, he.2.1, he.2.2, h⟩⟩
  constructor
  · rw [dec_eq_acc_iff he]
    show _ ↔ rpAcc σc tb a b
    rw [hacc_iff]
    exact ⟨fun h h' => h (hdet_any (hpath2 h')), fun h h' => h (hpath1 h')⟩
  · intro hind
    by_cases hdet : ReflTransGen (restr (U σc (a, b)) (detH σc tb (a, b) (dec σc tb))) (some b)
        (some a)
    · rw [(dec_eq_rej_iff he).2 hdet] at hind; cases hind
    · have : dec σc tb (a, b) = acc :=
        (dec_eq_acc_iff he).2 fun h => hdet (hpath2 (hpath1 h))
      rw [this] at hind; cases hind

end Complete

/-- **Lemma 5.8** of [Ramseyer–Goel]. Let `σc` be any counterfactual completion of the current
votes `σ` (every replica eventually votes on the same finite set of transactions, extending its
current vote). Whenever Algorithm 3 accepts an edge determinately (resp. rejects it), the
non-streaming Ranked Pairs on `σc` with the same tie-breaking rule accepts (resp. rejects) it. -/
theorem lemma_5_8 [Nonempty ι] (htb : Function.Injective tb) (hpre : ∀ i, σ i <+: σc i)
    (hc : Complete σc) {a b : α} (ha : a ∈ V σ) (hb : b ∈ V σ) :
    (dec σ tb (a, b) = acc → rpAcc σc tb a b) ∧ (dec σ tb (a, b) = rej → ¬ rpAcc σc tb a b) := by
  have hm := dec_mono hpre (tb := tb) (a, b) ha hb
  have hcpl := dec_complete hc htb (a, b)
  refine ⟨fun h => hcpl.1.1 (hm.1 h), fun h hacc => ?_⟩
  have := hcpl.1.2 hacc
  rw [hm.2 h] at this; cases this

/-! ### The output of Algorithm 3 -/

/-- A transaction is *clean* (does not border an indeterminate edge): every replica has voted on
it, it is not the target of an edge `(v̂, τ)`, and every edge between it and another transaction
is determinate. (Edges `(τ, v̂)` are ignored; see the module docstring.) -/
def Clean (σ : ι → List α) (tb : α × α → ℕ) (x : α) : Prop :=
  x ∈ V σ ∧ ¬ FutIn σ x ∧ ∀ y, dec σ tb (x, y) ≠ ind ∧ dec σ tb (y, x) ≠ ind

/-- The order given by the determinate (accepted) edges. -/
def detLt (σ : ι → List α) (tb : α × α → ℕ) : α → α → Prop :=
  TransGen fun a b => dec σ tb (a, b) = acc

/-- The output of Algorithm 3: the clean transactions that come before every non-clean one in the
topological order of the determinate edges, ordered by `detLt`. -/
def output (σ : ι → List α) (tb : α × α → ℕ) : Set α :=
  {x | Clean σ tb x ∧ ∀ y ∈ V σ, ¬ Clean σ tb y → detLt σ tb x y}

/-- A clean transaction is comparable with every other fully-voted transaction. -/
theorem detLt_comparable {x y : α} (hx : Clean σ tb x) (hy : y ∈ V σ) (hxy : x ≠ y) :
    detLt σ tb x y ∨ detLt σ tb y x := by
  have he : IsEdge σ (x, y) := ⟨hx.1, hy, hxy⟩
  rcases hd : dec σ tb (x, y)
  · exact Or.inl (.single hd)
  · right
    have hp := (dec_eq_rej_iff he).1 hd
    have := path_somes (Q := fun a b => dec σ tb (a, b) = acc)
      (fun y h => by obtain ⟨-, -, h⟩ := h; cases y <;> exact h)
      (fun a b h => h.2.2.2) hp
    rcases reflTransGen_iff_eq_or_transGen.1 this with h | h
    · exact absurd h hxy
    · exact h
  · exact absurd hd (hx.2.2 y).1

/-- Transactions not yet fully voted on come after a clean transaction in every vote. -/
theorem cnt_new_full (hpre : ∀ i, σ i <+: σ' i) {x y : α} (hx : x ∈ V σ) (hfx : ¬ FutIn σ x)
    (hy' : ∀ i, y ∈ σ' i) (hy : y ∉ V σ) : cnt σ' x y = Fintype.card ι := by
  rw [cnt_eq_card_iff]
  intro i
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  by_cases hyi : y ∈ σ i
  · rcases Before.total (hx i) hyi hxy with h | h
    · exact (before_prefix_iff (hpre i) hyi).2 h
    · exact absurd ⟨y, ⟨⟨i, hyi⟩, hy⟩, i, h⟩ hfx
  · refine ⟨hy' i, ?_⟩
    rw [← (hpre i).idxOf_eq_of_mem (hx i)]
    have h1 := List.idxOf_lt_length_of_mem (hx i)
    have h2 : ¬ (σ' i).idxOf y < (σ i).length := fun h =>
      hyi (((hpre i).mem_iff_idxOf_lt_length y).2 h)
    omega

/-- **Theorem 5.10** of [Ramseyer–Goel]. On any counterfactual completion `σc` of the current
votes, the output of Algorithm 3 is an initial segment of the output of non-streaming Ranked Pairs
(with the same tie-breaking rule): it is a down-set of Ranked Pairs' order, ordered the same way. -/
theorem theorem_5_10 [Nonempty ι] (htb : Function.Injective tb) (hpre : ∀ i, σ i <+: σc i)
    (hc : Complete σc) :
    output σ tb ⊆ V σc ∧
      (∀ x ∈ output σ tb, ∀ y, rpOut σc tb y x → y ∈ output σ tb) ∧
      ∀ x ∈ output σ tb, ∀ y ∈ output σ tb, (detLt σ tb x y ↔ rpOut σc tb x y) := by
  have hdet : ∀ {x y}, detLt σ tb x y → rpOut σc tb x y := fun h =>
    tg_mono (r := fun a b => dec σ tb (a, b) = acc) (fun p q (hpq : dec σ tb (p, q) = acc) =>
      have he : IsEdge σ (p, q) := isEdge_of_dec_ne_rej (by rw [hpq]; decide)
      (lemma_5_8 htb hpre hc he.1 he.2.1).1 hpq) h
  have hnew : ∀ {x y}, Clean σ tb x → y ∈ V σc → y ∉ V σ → rpOut σc tb x y := by
    intro x y hx hy hyV
    have hxc := V_mono hpre hx.1
    have hxy : x ≠ y := fun h => hyV (h ▸ hx.1)
    exact .single (observation_5_4 hxc hy (cnt_new_full hpre hx.1 hx.2.1 hy hyV))
  refine ⟨fun x hx => V_mono hpre hx.1.1, ?_, ?_⟩
  · intro x hx y hyx
    have hyc := (mem_of_rpLt hyx).1
    have hne : y ≠ x := by rintro rfl; exact rpOut_irrefl htb y hyx
    by_cases hyV : y ∈ V σ
    swap
    · exact absurd (hyx.trans (hnew hx.1 hyc hyV)) (rpOut_irrefl htb y)
    by_cases hyC : Clean σ tb y
    swap
    · exact absurd ((hdet (hx.2 y hyV hyC)).trans hyx) (rpOut_irrefl htb x)
    rcases detLt_comparable hx.1 hyV hne.symm with h | h
    · exact absurd ((hdet h).trans hyx) (rpOut_irrefl htb x)
    · exact ⟨hyC, fun z hz hzc => h.trans (hx.2 z hz hzc)⟩
  · intro x hx y hy
    refine ⟨hdet, fun h => ?_⟩
    have hne : x ≠ y := by rintro rfl; exact rpOut_irrefl htb x h
    rcases detLt_comparable hx.1 hy.1.1 hne with h' | h'
    · exact h'
    · exact absurd (h.trans (hdet h')) (rpOut_irrefl htb x)

/-- Every list of votes has a counterfactual completion: each replica appends the transactions it
has not voted on yet. -/
theorem exists_completion (σ : ι → List α) : ∃ σc, (∀ i, σ i <+: σc i) ∧ Complete σc := by
  classical
  let L : List α := (univ.biUnion fun i => (σ i).toFinset).toList
  refine ⟨fun i => σ i ++ L.filter (fun x => x ∉ σ i), fun i => List.prefix_append _ _, ?_⟩
  intro i j x hx
  have hxL : x ∈ L := by
    rcases List.mem_append.1 hx with h | h
    · simp only [L, Finset.mem_toList, Finset.mem_biUnion, mem_univ, true_and,
        List.mem_toFinset]
      exact ⟨i, h⟩
    · exact (List.mem_filter.1 h).1
  by_cases hj : x ∈ σ j
  · exact List.mem_append_left _ hj
  · exact List.mem_append_right _ (List.mem_filter.2 ⟨hxL, by simpa using hj⟩)

/-- Clean transactions stay clean when the votes are extended. -/
theorem clean_mono [Nonempty ι] (hpre : ∀ i, σ i <+: σ' i) {x : α} (hx : Clean σ tb x) :
    Clean σ' tb x := by
  refine ⟨V_mono hpre hx.1, fun h => hx.2.1 (futIn_back hpre hx.1 h), fun y => ?_⟩
  by_cases hyV' : y ∈ V σ'
  swap
  · rw [dec_of_not_isEdge (fun h => hyV' h.2.1), dec_of_not_isEdge (fun h => hyV' h.1)]
    decide
  by_cases hyV : y ∈ V σ
  · have hstab : ∀ e : α × α, e.1 ∈ V σ → e.2 ∈ V σ → dec σ tb e ≠ ind → dec σ' tb e ≠ ind := by
      intro e h1 h2 hne
      have hm := dec_mono hpre (tb := tb) e h1 h2
      rcases hd : dec σ tb e
      · rw [hm.1 hd]; decide
      · rw [hm.2 hd]; decide
      · exact absurd hd hne
    exact ⟨hstab _ hx.1 hyV (hx.2.2 y).1, hstab _ hyV hx.1 (hx.2.2 y).2⟩
  · have hxy : x ≠ y := fun h => hyV (h ▸ hx.1)
    have hn := cnt_new_full hpre hx.1 hx.2.1 hyV' hyV
    have hacc : dec σ' tb (x, y) = acc := dec_of_cnt_full ⟨V_mono hpre hx.1, hyV', hxy⟩ hn
    have hrej : dec σ' tb (y, x) = rej := dec_of_cnt_zero ⟨hyV', V_mono hpre hx.1, hxy.symm⟩
      ((cnt_eq_zero_iff_of_mem hyV' (V_mono hpre hx.1) hxy.symm).2 hn)
    rw [hacc, hrej]; decide

/-- **Corollary 5.9** of [Ramseyer–Goel] (monotonicity, Def. 5.1). If every vote of `σ'` extends
the corresponding vote of `σ`, the output on `σ'` extends the output on `σ`: it contains it, the
output on `σ` is an initial segment (down-set) of it, and the two orders agree on it. -/
theorem corollary_5_9 [Nonempty ι] (htb : Function.Injective tb) (hpre : ∀ i, σ i <+: σ' i) :
    output σ tb ⊆ output σ' tb ∧
      (∀ x ∈ output σ tb, ∀ y ∈ output σ' tb, detLt σ' tb y x → y ∈ output σ tb) ∧
      ∀ x ∈ output σ tb, ∀ y ∈ output σ tb, (detLt σ tb x y ↔ detLt σ' tb x y) := by
  have hsub : output σ tb ⊆ output σ' tb := by
    intro x hx
    refine ⟨clean_mono hpre hx.1, fun z hz hzc => ?_⟩
    by_cases hzV : z ∈ V σ
    · have hzc' : ¬ Clean σ tb z := fun h => hzc (clean_mono hpre h)
      exact tg_mono (r := fun a b => dec σ tb (a, b) = acc)
        (fun p q (hpq : dec σ tb (p, q) = acc) =>
        have he : IsEdge σ (p, q) := isEdge_of_dec_ne_rej (by rw [hpq]; decide)
        (dec_mono hpre (tb := tb) (p, q) he.1 he.2.1).1 hpq) (hx.2 z hzV hzc')
    · have hxz : x ≠ z := fun h => hzV (h ▸ hx.1.1)
      exact .single (dec_of_cnt_full ⟨V_mono hpre hx.1.1, hz, hxz⟩
        (cnt_new_full hpre hx.1.1 hx.1.2.1 hz hzV))
  obtain ⟨σc, hpc, hc⟩ := exists_completion σ'
  have hpre' : ∀ i, σ i <+: σc i := fun i => (hpre i).trans (hpc i)
  have T := theorem_5_10 htb hpre' hc
  have T' := theorem_5_10 htb hpc hc
  refine ⟨hsub, fun x hx y hy hyx => T.2.1 x hx y ((T'.2.2 y hy x (hsub hx)).1 hyx), ?_⟩
  intro x hx y hy
  rw [T.2.2 x hx y hy, T'.2.2 x (hsub hx) y (hsub hy)]

/-- Non-vacuity: once every replica has voted on the same set of transactions, Algorithm 3 (with
the repaired output rule) outputs all of them. -/
theorem output_complete [Nonempty ι] (htb : Function.Injective tb) (hc : Complete σc) :
    output σc tb = V σc := by
  have hclean : ∀ x ∈ V σc, Clean σc tb x := fun x hx =>
    ⟨hx, not_futIn hc x, fun y => ⟨(dec_complete hc htb _).2, (dec_complete hc htb _).2⟩⟩
  ext x
  exact ⟨fun h => h.1.1, fun hx => ⟨hclean x hx, fun y hy hyc => absurd (hclean y hy) hyc⟩⟩

/-- A tie-breaking rule exists for countable transaction sets (e.g. `α = ℕ`). -/
example : Function.Injective (fun e : ℕ × ℕ => Nat.pair e.1 e.2) := fun e e' h => by
  have := Nat.pair_eq_pair.1 h; exact Prod.ext this.1 this.2

end Podc.FairOrderingSocialChoice.Streaming
