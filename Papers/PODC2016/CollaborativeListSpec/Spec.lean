import Papers.PODC2016.CollaborativeListSpec.Model

/-!
# Abstract executions and the list specifications (Section 3)

* `AbsWF h vis` is Definition 4 (causal abstract execution) for the `do` events `h` of an
  execution, identified by their positions (the paper instruments events with unique ids; the
  execution and its abstract execution share them, which is how compliance, Definition 5, is
  built in). We do not require the linearization `H` itself: for finite executions an acyclic
  transitive `vis` containing the replica order always has one (a topological sort). On the
  hypothesis side (lower bound) this only makes the hypothesis weaker; on the conclusion side
  (RGA) we use `vis ⊆ <`, so `H` = the order of the execution works.
* `ListCond`, `Strong`, `Weak` are Definitions 7 and 8; `EventualVisibility` is Definition 9.
* `Satisfies` is Definition 6, relative to a class `Adm` of admitted executions (causal
  broadcast, user assumptions). `UserOK` collects the user assumptions of Section 3: inserted
  elements are unique, deleted elements occur in the response of the preceding operation of the
  same replica.
* `PushBased` is Definition 13.
-/

namespace Podc.CollaborativeListSpec

/-- The list operations of Section 3. -/
inductive LOp (U : Type) where
  | ins (a : U) (k : ℕ)
  | del (a : U)
  | read
  deriving DecidableEq

/-- `≤vis`. -/
def VisLe (vis : ℕ → ℕ → Prop) (i j : ℕ) : Prop := i = j ∨ vis i j

/-- **Definition 4** (causal abstract execution), on positions. -/
structure AbsWF {Rep Op Val : Type} (h : ℕ → Option (Rep × Op × Val)) (vis : ℕ → ℕ → Prop) :
    Prop where
  dom : ∀ i j, vis i j → (h i).isSome ∧ (h j).isSome
  ro : ∀ i j a b, i < j → h i = some a → h j = some b → a.1 = b.1 → vis i j
  trans : ∀ i j k, vis i j → vis j k → vis i k
  irrefl : ∀ i, ¬ vis i i

section Spec

variable {Rep U : Type} (h : ℕ → Option (Rep × LOp U × List U)) (vis : ℕ → ℕ → Prop)

/-- `elems(A)`. -/
def elems : Set U := {a | ∃ p r k w, h p = some (r, .ins a k, w)}

/-- An insertion of `a` is `≤vis` the event at `p`. -/
def InsVis (p : ℕ) (a : U) : Prop := ∃ q r k w, VisLe vis q p ∧ h q = some (r, .ins a k, w)

/-- A deletion of `a` is `≤vis` the event at `p`. -/
def DelVis (p : ℕ) (a : U) : Prop := ∃ q r w, VisLe vis q p ∧ h q = some (r, .del a, w)

/-- Condition 1 of Definition 7. -/
def ListCond (lo : U → U → Prop) : Prop :=
  ∀ p r op w, h p = some (r, op, w) →
    -- (a)
    (∀ a, a ∈ w ↔ InsVis h vis p a ∧ ¬ DelVis h vis p a) ∧
    -- (b)
    w.Pairwise lo ∧
    -- (c)
    (∀ a k, op = .ins a k → w[min k (w.length - 1)]? = some a)

/-- **Definition 7** (strong list specification `A_strong`). -/
def Strong : Prop :=
  ∃ lo : U → U → Prop, (∀ a b, lo a b → a ∈ elems h ∧ b ∈ elems h) ∧ ListCond h vis lo ∧
    (∀ a b c, lo a b → lo b c → lo a c) ∧ (∀ a, ¬ lo a a) ∧
    (∀ a ∈ elems h, ∀ b ∈ elems h, a ≠ b → lo a b ∨ lo b a)

/-- **Definition 8** (weak list specification `A_weak`). -/
def Weak : Prop :=
  ∃ lo : U → U → Prop, (∀ a b, lo a b → a ∈ elems h ∧ b ∈ elems h) ∧ ListCond h vis lo ∧
    (∀ a, ¬ lo a a) ∧
    ∀ p r op w, h p = some (r, op, w) →
      (∀ a ∈ w, ∀ b ∈ w, ∀ c ∈ w, lo a b → lo b c → lo a c) ∧
      (∀ a ∈ w, ∀ b ∈ w, a ≠ b → lo a b ∨ lo b a)

/-- **Definition 9** (eventual visibility). -/
def EventualVisibility : Prop :=
  ∀ e r op w, h e = some (r, op, w) → op ≠ .read → {e' | (h e').isSome ∧ ¬ vis e e'}.Finite

variable {h vis}

theorem ListCond.mem_elems {lo : U → U → Prop} (hc : ListCond h vis lo) {p r op w}
    (hp : h p = some (r, op, w)) {a : U} (ha : a ∈ w) : a ∈ elems h := by
  obtain ⟨q, r', k, w', -, hq⟩ := (((hc p r op w hp).1 a).1 ha).1
  exact ⟨q, r', k, w', hq⟩

/-- `A_strong ⊆ A_weak`. -/
theorem Strong.weak (hs : Strong h vis) : Weak h vis := by
  obtain ⟨lo, hdom, hc, htr, hirr, htot⟩ := hs
  refine ⟨lo, hdom, hc, hirr, fun p r op w hp => ⟨fun a _ b _ c _ => htr a b c, ?_⟩⟩
  intro a ha b hb hab
  exact htot a (hc.mem_elems hp ha) b (hc.mem_elems hp hb) hab

end Spec

/-! ### Executions of list protocols -/

section Exec

variable {Rep U Q M : Type} [DecidableEq Rep] (P : Protocol Rep (LOp U) (List U) Q M)

/-- Inserted elements are unique (assumption of Section 3). -/
def UniqueIns (α : List (Act Rep (LOp U))) : Prop :=
  ∀ (p q : ℕ) (r r' : Rep) (a : U) (k k' : ℕ), α[p]? = some (.doOp r (.ins a k)) →
    α[q]? = some (.doOp r' (.ins a k')) → p = q

/-- Users delete only elements in the response of the preceding operation on the same replica
(assumption of Section 3). -/
def DelOK (α : List (Act Rep (LOp U))) : Prop :=
  ∀ (p : ℕ) (r : Rep) (a : U), α[p]? = some (.doOp r (.del a)) →
    ∃ q < p, ∃ op v, P.hist α q = some (r, op, v) ∧ a ∈ v ∧
      ∀ q', q < q' → q' < p → ∀ op', α[q']? ≠ some (.doOp r op')

/-- The user assumptions of Section 3. -/
def UserOK (α : List (Act Rep (LOp U))) : Prop := UniqueIns α ∧ DelOK P α

/-- **Definition 6**: every admitted well-formed execution complies with an abstract execution
in the specification `S`. -/
def Satisfies (S : (ℕ → Option (Rep × LOp U × List U)) → (ℕ → ℕ → Prop) → Prop)
    (Adm : List (Act Rep (LOp U)) → Prop) : Prop :=
  ∀ α, P.WF α → Adm α → ∃ vis, AbsWF (P.hist α) vis ∧ S (P.hist α) vis

/-- Happens-before restricted to `do` events: the visibility relation of push-based protocols. -/
def visHB (α : List (Act Rep (LOp U))) (i j : ℕ) : Prop := HB α i j ∧ IsDo α i ∧ IsDo α j

/-- **Definition 13** (push-based protocols), for the specification `S` and the class `Adm` of
admitted executions (the paper: causal broadcast). -/
structure PushBased (S : (ℕ → Option (Rep × LOp U × List U)) → (ℕ → ℕ → Prop) → Prop)
    (Adm : List (Act Rep (LOp U)) → Prop) : Prop where
  ins : ∀ α, P.WF α → Adm α → ∀ p r a k, α[p]? = some (.doOp r (.ins a k)) → P.Pending α p r
  del : ∀ α, P.WF α → Adm α → ∀ p r a, α[p]? = some (.doOp r (.del a)) →
    (¬ ∃ q r', HB α q p ∧ α[q]? = some (.doOp r' (.del a))) → P.Pending α p r
  spec : ∀ α, P.WF α → Adm α → S (P.hist α) (visHB α)

variable {P}

theorem hist_eq_some {α : List (Act Rep (LOp U))} {p : ℕ} {r : Rep} {op : LOp U} {v : List U}
    (h : P.hist α p = some (r, op, v)) :
    α[p]? = some (.doOp r op) ∧ v = P.resp r (P.stBefore α p r) op := by
  unfold Protocol.hist at h
  split at h
  · rename_i r' op' h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨h', rfl⟩
  · cases h

theorem hist_of_getElem? {α : List (Act Rep (LOp U))} {p : ℕ} {r : Rep} {op : LOp U}
    (h : α[p]? = some (.doOp r op)) :
    P.hist α p = some (r, op, P.resp r (P.stBefore α p r) op) := by
  simp [Protocol.hist, h]

theorem hist_isSome_iff {α : List (Act Rep (LOp U))} {p : ℕ} : (P.hist α p).isSome ↔ IsDo α p := by
  constructor
  · intro h
    obtain ⟨⟨r, op, v⟩, hv⟩ := Option.isSome_iff_exists.1 h
    exact ⟨r, op, (hist_eq_some hv).1⟩
  · rintro ⟨r, op, h⟩; simp [hist_of_getElem? h]

/-- Happens-before on `do` events is a causal abstract execution (Definition 4). -/
theorem visHB_absWF (α : List (Act Rep (LOp U))) : AbsWF (P.hist α) (visHB α) where
  dom i j h := ⟨hist_isSome_iff.2 h.2.1, hist_isSome_iff.2 h.2.2⟩
  ro i j a b hij ha hb hab := by
    obtain ⟨ha', -⟩ := hist_eq_some (P := P) (show P.hist α i = some (a.1, a.2.1, a.2.2) from ha)
    obtain ⟨hb', -⟩ := hist_eq_some (P := P) (show P.hist α j = some (b.1, b.2.1, b.2.2) from hb)
    exact ⟨HB.of_rep hij ha' hb' (by simpa using hab), ⟨_, _, ha'⟩, ⟨_, _, hb'⟩⟩
  trans i j k h₁ h₂ := ⟨h₁.1.trans h₂.1, h₁.2.1, h₂.2.2⟩
  irrefl i h := HB.irrefl i h.1

theorem visHB_lt {α : List (Act Rep (LOp U))} {i j : ℕ} (h : visHB α i j) : i < j := h.1.lt

/-- A push-based protocol satisfies its specification. -/
theorem PushBased.satisfies {S : (ℕ → Option (Rep × LOp U × List U)) → (ℕ → ℕ → Prop) → Prop}
    {Adm : List (Act Rep (LOp U)) → Prop} (h : PushBased P S Adm) : Satisfies P S Adm :=
  fun α hwf hadm => ⟨visHB α, visHB_absWF α, h.spec α hwf hadm⟩

/-- Push-based for a class of executions implies push-based for a smaller class. -/
theorem PushBased.mono {S : (ℕ → Option (Rep × LOp U × List U)) → (ℕ → ℕ → Prop) → Prop}
    {Adm Adm' : List (Act Rep (LOp U)) → Prop} (h : PushBased P S Adm)
    (hA : ∀ α, Adm' α → Adm α) : PushBased P S Adm' where
  ins α hwf ha := h.ins α hwf (hA α ha)
  del α hwf ha := h.del α hwf (hA α ha)
  spec α hwf ha := h.spec α hwf (hA α ha)

/-- Push-based for `A_strong` implies push-based for `A_weak`. -/
theorem PushBased.weak {Adm : List (Act Rep (LOp U)) → Prop} (h : PushBased P Strong Adm) :
    PushBased P Weak Adm where
  ins := h.ins
  del := h.del
  spec α hwf ha := (h.spec α hwf ha).weak

end Exec

end Podc.CollaborativeListSpec
