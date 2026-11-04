import Papers.PODC2011.SharedObjectTimeBounds.TheoremD1

/-!
# Examples: the hypotheses of Theorems C.1, D.1, E.1 on concrete objects

Sequential specifications given by deterministic state machines (`smLegal`). We check

* read-modify-write is strongly immediately non-self-commuting (`rmw_strongly`, Theorem C.1);
* register writes satisfy the hypotheses of Theorem D.1 including the repaired `LastRevealing`
  (`write_lastRevealing`);
* enqueue/peek on a queue satisfy the hypotheses of Theorem E.1 (`queue_E1_hyps`);
* push/peek on a stack do **not** satisfy them, contrary to the claim of §IV.E and Table III
  (`stack_push_peek_not_E1`);
* the "test-and-reset" register (`TR`): writes satisfy the thesis's own hypothesis of Theorem D.1
  (permutations with different last writes are not equivalent, `tr_nonEquiv`) but no fixed query
  sequence reveals the last write in the way the runs of the thesis's proof need: for every query
  sequence there are answers compatible, for every `z`, with a permutation whose last element is
  not `z` (`tr_answers`), so `LastRevealing` fails (`tr_not_lastRevealing`).
-/

namespace Podc.SharedObjectTimeBounds

/-- The sequential specification of a deterministic state machine. -/
def smLegal {S I R : Type*} (δ : S → I → S × R) : S → List (I × R) → Prop
  | _, [] => True
  | s, o :: l => (δ s o.1).2 = o.2 ∧ smLegal δ (δ s o.1).1 l

/-- The state after a sequence (ignoring return values). -/
def smState {S I R : Type*} (δ : S → I → S × R) : S → List (I × R) → S
  | s, [] => s
  | s, o :: l => smState δ (δ s o.1).1 l

section SM

variable {S I R : Type*} (δ : S → I → S × R)

theorem smLegal_append : ∀ (s : S) (l₁ l₂ : List (I × R)),
    smLegal δ s (l₁ ++ l₂) ↔ smLegal δ s l₁ ∧ smLegal δ (smState δ s l₁) l₂
  | s, [], l₂ => by simp [smLegal, smState]
  | s, o :: l₁, l₂ => by
    simp only [List.cons_append, smLegal, smState, smLegal_append _ l₁ l₂, and_assoc]

theorem smLegal_prefixClosed (s₀ : S) : PrefixClosed (smLegal δ s₀) :=
  fun l₁ l₂ h => ((smLegal_append δ s₀ l₁ l₂).mp h).1

theorem smLegal_deterministic (s₀ : S) : Deterministic (smLegal δ s₀) := by
  intro ρ a r r' h h'
  rw [smLegal_append] at h h'
  simp only [smLegal, and_true] at h h'
  exact h.2.symm.trans h'.2

end SM

/-! ## Read-modify-write -/

/-- A read-modify-write register on `ℕ`: `rmw v` writes `v` and returns the old value. -/
def rmwδ (s : ℕ) (v : ℕ) : ℕ × ℕ := (v, s)

theorem rmw_strongly : StronglyImmNonSelfCommuting (smLegal rmwδ 0) (fun _ => True) :=
  ⟨[], (1, 0), (2, 0), trivial, trivial, by simp [smLegal, rmwδ], by simp [smLegal, rmwδ],
    by simp [smLegal, rmwδ], by simp [smLegal, rmwδ]⟩

/-! ## Read/write register and Theorem D.1 -/

/-- Register operations. -/
inductive RegOp (V : Type*) where
  | write (v : V)
  | read

/-- A register: `write v` returns `none`, `read` returns `some` of the value. -/
def regδ {V : Type*} (s : V) : RegOp V → V × Option V
  | .write v => (v, none)
  | .read => (s, some s)

theorem write_selfCommuting {V : Type*} (s₀ : V) :
    ImmSelfCommuting (smLegal regδ s₀) (fun a => ∃ v, a = RegOp.write v) := by
  rintro ⟨ρ, o₁, o₂, ⟨v₁, h₁⟩, ⟨v₂, h₂⟩, l₁, l₂, h⟩
  obtain ⟨a₁, r₁⟩ := o₁; obtain ⟨a₂, r₂⟩ := o₂
  simp only at h₁ h₂; subst h₁ h₂
  simp only [smLegal_append, smLegal, regδ, and_true] at l₁ l₂ h
  tauto

/-- Writes of `k` distinct values: one read after them reveals the last one. -/
theorem write_lastRevealing {k : ℕ} (hk : 0 < k) :
    LastRevealing (smLegal (regδ (V := Fin k)) ⟨0, hk⟩) hk []
      (fun i => (RegOp.write i, none)) := by
  refine ⟨[RegOp.read], fun σ σ' rs hrs h h' => ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, rs = [r] := by
    match rs, hrs with
    | [r], _ => exact ⟨r, rfl⟩
  have hlast : ∀ (τ : Equiv.Perm (Fin k)) (s : Fin k),
      smState regδ s (permSeq (fun i => (RegOp.write i, (none : Option (Fin k)))) τ) =
        τ ⟨k - 1, by omega⟩ := by
    intro τ s
    have key : ∀ (l : List (Fin k)) (s : Fin k) (hl : l ≠ []),
        smState regδ s (l.map fun i => (RegOp.write i, (none : Option (Fin k)))) =
          l.getLast hl := by
      intro l
      induction l with
      | nil => intro _ h; exact absurd rfl h
      | cons a l ih =>
        intro s _
        cases l with
        | nil => simp [smState, regδ]
        | cons b l =>
          rw [show smState regδ s (List.map (fun i => (RegOp.write i, (none : Option (Fin k))))
              (a :: b :: l)) = smState regδ s (List.map (fun i => (RegOp.write i,
              (none : Option (Fin k)))) (b :: l)) from rfl, ih s (by simp)]
          simp
    rw [permSeq_eq, key _ s (by simp; omega), List.getLast_ofFn]
  simp only [List.nil_append, smLegal_append, List.zip_cons_cons, List.zip_nil_right, smLegal,
    regδ, and_true] at h h'
  rw [hlast] at h h'
  exact Option.some_injective _ (h.2.trans h'.2.symm)

/-! ## Queues and stacks and Theorem E.1 -/

/-- Operations of a queue / stack with `peek`. -/
inductive QOp where
  | put (n : ℕ)
  | peek

/-- A queue: `put` enqueues at the back, `peek` returns the head. -/
def queueδ (s : List ℕ) : QOp → List ℕ × Option ℕ
  | .put n => (s ++ [n], none)
  | .peek => (s, s.head?)

/-- A stack: `put` pushes on top, `peek` returns the top. -/
def stackδ (s : List ℕ) : QOp → List ℕ × Option ℕ
  | .put n => (n :: s, none)
  | .peek => (s, s.head?)

/-- `put` (enqueue / push) is immediately self-commuting in both objects. -/
theorem put_selfCommuting (δ : List ℕ → QOp → List ℕ × Option ℕ)
    (hδ : ∀ s n, (δ s (.put n)).2 = none) (s₀ : List ℕ) :
    ImmSelfCommuting (smLegal δ s₀) (fun a => ∃ n, a = QOp.put n) := by
  rintro ⟨ρ, o₁, o₂, ⟨n₁, h₁⟩, ⟨n₂, h₂⟩, l₁, l₂, h⟩
  obtain ⟨a₁, r₁⟩ := o₁; obtain ⟨a₂, r₂⟩ := o₂
  simp only at h₁ h₂; subst h₁ h₂
  simp only [smLegal_append, smLegal, hδ, and_true] at l₁ l₂ h
  tauto

/-- `peek` is a (non-mutating) pure accessor in both objects. -/
theorem peek_nonMutator (δ : List ℕ → QOp → List ℕ × Option ℕ)
    (hδ : ∀ s, (δ s .peek).1 = s) (s₀ : List ℕ) :
    NonMutator (smLegal δ s₀) (fun a => a = QOp.peek) := by
  rintro ρ ⟨a, r⟩ rfl h
  rw [smLegal_append] at h
  have hs : smState δ s₀ (ρ ++ [(QOp.peek, r)]) = smState δ s₀ ρ := by
    have : ∀ s (l : List (QOp × Option ℕ)) o, smState δ s (l ++ [o]) =
        (δ (smState δ s l) o.1).1 := by
      intro s l o
      induction l generalizing s with
      | nil => rfl
      | cons x l ih => exact ih _
    rw [this, hδ]
  constructor <;> intro ρ₃ h₃ <;> rw [smLegal_append] at h₃ ⊢
  · exact ⟨h.1, by rw [← hs]; exact h₃.2⟩
  · refine ⟨?_, by rw [hs]; exact h₃.2⟩
    rw [smLegal_append]; exact ⟨h₃.1, h.2⟩

/-- Enqueue/peek satisfy the hypotheses A, B, C of Theorem E.1. -/
theorem queue_E1_hyps :
    let legal := smLegal queueδ []
    let o₁ := (QOp.put 1, (none : Option ℕ))
    let o₂ := (QOp.put 2, (none : Option ℕ))
    (¬ (legal ([] ++ [o₁, (QOp.peek, some 1)]) ↔ legal ([] ++ [o₂, o₁, (QOp.peek, some 1)]))) ∧
    (¬ (legal ([] ++ [o₂, (QOp.peek, some 2)]) ↔ legal ([] ++ [o₁, o₂, (QOp.peek, some 2)]))) ∧
    (¬ (legal ([] ++ [o₁, o₂, (QOp.peek, some 1)]) ↔
      legal ([] ++ [o₂, o₁, (QOp.peek, some 1)]))) := by
  simp [smLegal, queueδ]

/-- Push/peek on a stack never satisfy hypotheses A and C of Theorem E.1 together (the thesis
claims that Theorem E.1 applies to push and peek). -/
theorem stack_push_peek_not_E1 (ρ : List (QOp × Option ℕ)) (o₁ o₂ a₁ a₃ : QOp × Option ℕ)
    (h₁ : ∃ n, o₁.1 = QOp.put n) (h₂ : ∃ n, o₂.1 = QOp.put n)
    (hC : ¬ (smLegal stackδ [] (ρ ++ [o₁, o₂, a₃]) ↔ smLegal stackδ [] (ρ ++ [o₂, o₁, a₃]))) :
    smLegal stackδ [] (ρ ++ [o₁, a₁]) ↔ smLegal stackδ [] (ρ ++ [o₂, o₁, a₁]) := by
  obtain ⟨r₁, n₁, rfl⟩ : ∃ r n, o₁ = (QOp.put n, r) := by
    obtain ⟨n, hn⟩ := h₁; exact ⟨o₁.2, n, by rw [← hn]⟩
  obtain ⟨r₂, n₂, rfl⟩ : ∃ r n, o₂ = (QOp.put n, r) := by
    obtain ⟨n, hn⟩ := h₂; exact ⟨o₂.2, n, by rw [← hn]⟩
  obtain ⟨a, r⟩ := a₁
  obtain ⟨b, r₃⟩ := a₃
  simp only [smLegal_append, smLegal, stackδ] at hC ⊢
  by_cases hρ : smLegal stackδ [] ρ
  · by_cases e1 : r₁ = none <;> by_cases e2 : r₂ = none
    · subst e1 e2; cases a <;> simp [hρ]
    all_goals (exfalso; apply hC; simp [hρ, e1, e2, eq_comm])
  · simp [hρ]

/-! ## The test-and-reset register: the gap in the proof of Theorem D.1 -/

/-- Operations: `W a` writes `a`; `T a` tests whether the value is `a` and resets it. -/
inductive TROp where
  | W (a : Fin 3)
  | T (a : Fin 3)

/-- Test-and-reset register (`none` = reset). -/
def trδ (s : Option (Fin 3)) : TROp → Option (Fin 3) × Bool
  | .W a => (some a, false)
  | .T a => (none, decide (s = some a))

/-- The three writes. -/
def trOps : Fin 3 → TROp × Bool := fun i => (TROp.W i, false)

theorem tr_state_perm (σ : Equiv.Perm (Fin 3)) (s : Option (Fin 3)) :
    smLegal trδ s (permSeq trOps σ) ∧ smState trδ s (permSeq trOps σ) = some (σ 2) := by
  simp [permSeq, List.ofFn_succ, smLegal, smState, trδ, trOps]

/-- The thesis's hypothesis of Theorem D.1 holds for the writes of the test-and-reset register:
permutations with different last writes are not equivalent. -/
theorem tr_nonEquiv (σ σ' : Equiv.Perm (Fin 3)) (h : σ 2 ≠ σ' 2) :
    ¬ Equivalent (smLegal trδ none) ([] ++ permSeq trOps σ) ([] ++ permSeq trOps σ') := by
  rintro ⟨h1, -⟩
  have := h1 [(TROp.T (σ 2), true)] (by
    rw [smLegal_append]; refine ⟨(tr_state_perm σ none).1, ?_⟩
    rw [List.nil_append, (tr_state_perm σ none).2]; simp [smLegal, trδ])
  rw [smLegal_append, List.nil_append, (tr_state_perm σ' none).2] at this
  simp [smLegal, trδ] at this
  exact h this.2.symm

/-- Outputs of the test-and-reset register from state `s`. -/
def trOuts : Option (Fin 3) → List TROp → List Bool
  | _, [] => []
  | s, a :: l => (trδ s a).2 :: trOuts (trδ s a).1 l

theorem trOuts_legal : ∀ (s : Option (Fin 3)) (α : List TROp),
    smLegal trδ s (α.zip (trOuts s α))
  | _, [] => by simp [smLegal]
  | s, a :: l => by simp [trOuts, smLegal, trOuts_legal _ l]

/-- **The runs of the proof of Theorem D.1 do not force a contradiction.** For every query
sequence `α` there are answers `rs` such that for every `z` some permutation of the writes whose
last write is not `z` is consistent with them. (In the shifted run `R₂^z`, if `|OP| > (1 - 2/k) u`, the
only real-time constraint on the writes is that `z` precedes `z + 1 mod k`, so `z` is not last; since the state
after the writes depends only on the last write, a permutation with last write `σ 2` and `z` before `z + 1`
exists as well.) -/
theorem tr_answers (α : List TROp) : ∃ rs : List Bool, rs.length = α.length ∧
    ∀ z : Fin 3, ∃ σ : Equiv.Perm (Fin 3), σ 2 ≠ z ∧
      smLegal trδ none ([] ++ permSeq trOps σ ++ α.zip rs) := by
  -- the answers from initial state `some c` do not depend on `c` as long as `c ≠ a` when the
  -- first query is `T a`
  have hlen : ∀ s (α : List TROp), (trOuts s α).length = α.length := by
    intro s α; induction α generalizing s <;> simp_all [trOuts]
  have hperm : ∀ c : Fin 3, ∃ σ : Equiv.Perm (Fin 3), σ 2 = c :=
    fun c => ⟨Equiv.swap c 2, by simp⟩
  have legal_of : ∀ (σ : Equiv.Perm (Fin 3)) (rs : List Bool),
      rs = trOuts (some (σ 2)) α → smLegal trδ none ([] ++ permSeq trOps σ ++ α.zip rs) := by
    intro σ rs hrs
    rw [List.nil_append, smLegal_append, (tr_state_perm σ none).2, hrs]
    exact ⟨(tr_state_perm σ none).1, trOuts_legal _ _⟩
  -- pick a forbidden value `a` (the first query's argument if it is a test)
  obtain ⟨a, ha⟩ : ∃ a : Fin 3, ∀ c, c ≠ a → trOuts (some c) α = trOuts (some (a + 1)) α := by
    match α with
    | [] => exact ⟨0, fun _ _ => rfl⟩
    | TROp.W b :: l => exact ⟨0, fun _ _ => rfl⟩
    | TROp.T b :: l =>
      refine ⟨b, fun c hc => ?_⟩
      have : b + 1 ≠ b := by fin_cases b <;> decide
      simp [trOuts, trδ, hc, this]
  refine ⟨trOuts (some (a + 1)) α, hlen _ _, fun z => ?_⟩
  obtain ⟨c, hca, hcz⟩ : ∃ c : Fin 3, c ≠ a ∧ c ≠ z := by
    fin_cases a <;> fin_cases z <;> decide
  obtain ⟨σ, hσ⟩ := hperm c
  exact ⟨σ, hσ ▸ hcz, legal_of σ _ (by rw [hσ, ha c hca])⟩

/-- Hence the thesis's hypothesis of Theorem D.1 does not imply the repaired `LastRevealing`. -/
theorem tr_not_lastRevealing :
    ¬ LastRevealing (smLegal trδ none) (k := 3) (by norm_num) [] trOps := by
  rintro ⟨α, hα⟩
  obtain ⟨rs, hl, h⟩ := tr_answers α
  obtain ⟨σ, hσ, h1⟩ := h 0
  obtain ⟨σ', hσ', h2⟩ := h (σ 2)
  exact hσ' (hα σ σ' rs hl h1 h2).symm

end Podc.SharedObjectTimeBounds
