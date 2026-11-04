import Papers.PODC2015.DAPInvisibleReads.Commute

/-!
# The histories of the executions behind `H_WRTO` (Figure 1)

The executions used in the proofs of Theorems 1 and 2 consist of *blocks*: a process invokes an
operation, takes internal steps and returns a response. This file computes the transactional
bookkeeping of such executions and shows that they violate RTO (resp. WRTO):

* `E = R₄(y) · [W₃(y) c₃] · [W₂(x) c₂] · R₄(x) c₄`, where `T₄ = (a,0)` reads `y` and `x`,
  `T₃ = (c,0)` writes `y`, `T₂ = (b,0)` writes `x`. If `R₄(x)` returns `T₂`'s value, the history is
  `H_WRTO` and it does not preserve RTO (`not_preservesRTO_E`): `T₃ ≺RTO T₂ →wr T₄ →rw T₃`.
* `E' = [W₂(x) c₂] · R₄(y) · [W₃(y) c₃] · R₄(x) c₄`. If `R₄(x)` returns the initial value, the
  history does not preserve WRTO (`not_preservesWRTO_E'`): `T₂ ≺WRTO T₄ →rw T₂`.
-/

namespace Podc.DAPInvisibleReads

open Cslib.SharedMemory

variable {X V P : Type} [DecidableEq P]

/-- A block: `p` invokes `o`, takes the internal steps `β`, and returns `r`. -/
def Blk (p : P) (o : TOp X V) (β : List (Lbl P X V)) (r : Option V) : List (Lbl P X V) :=
  .inv p o :: β ++ [.ret p r]

/-- `β` consists of internal steps of `p`. -/
def Taus (p : P) (β : List (Lbl P X V)) : Prop := ∀ ℓ ∈ β, ℓ = .tau p

lemma projP_append (h₁ h₂ : List (Lbl P X V)) (p : P) :
    projP (h₁ ++ h₂) p = projP h₁ p ++ projP h₂ p := by simp [projP]

lemma foldl_taus {q : P} {β : List (Lbl P X V)} (hβ : Taus q β) (s : PState X V) :
    β.foldl PState.step s = s := by
  induction β generalizing s with
  | nil => rfl
  | cons ℓ β ih =>
    rw [hβ ℓ (by simp)]
    exact ih (fun ℓ' h => hβ ℓ' (by simp [h])) _

lemma foldl_projP_blk {q : P} {o : TOp X V} {β : List (Lbl P X V)} {r : Option V}
    (hβ : Taus q β) (p : P) (s : PState X V) :
    (projP (Blk q o β r) p).foldl PState.step s =
      if q = p then (s.step (.inv q o)).step (.ret q r) else s := by
  have hf : projP β p = if q = p then β else [] := by
    split_ifs with h
    · subst h; exact List.filter_eq_self.2 (fun ℓ hℓ => by simp [hβ ℓ hℓ, Label.proc])
    · exact List.filter_eq_nil_iff.2 (fun ℓ hℓ => by simp [hβ ℓ hℓ, Label.proc, h])
  simp only [Blk, projP] at hf ⊢
  simp only [List.cons_append, List.filter_cons, List.filter_append, hf]
  split_ifs with h <;> simp_all [Label.proc, foldl_taus hβ]

lemma pstate_eq_foldl (h : List (Lbl P X V)) (p : P) :
    pstate h p = (projP h p).foldl PState.step PState.init := rfl

/-- Records of finished transactions (the bookkeeping after a finished transaction). -/
lemma txRec_of_done {h : List (Lbl P X V)} {p : P} {t : TxRec X V}
    (hs : pstate h p = ⟨[t], TxRec.empty⟩) (k : ℕ) :
    txRec h (p, k) = if k = 0 then t else TxRec.empty := by
  simp only [txRec, hs]
  rcases k with _ | _ | k <;> simp

lemma txRec_of_init {h : List (Lbl P X V)} {p : P} (hs : pstate h p = PState.init) (k : ℕ) :
    txRec h (p, k) = TxRec.empty := by
  simp only [txRec, hs, PState.init]
  rcases k with _ | k <;> simp

lemma txRec_of_cur {h : List (Lbl P X V)} {p : P} {t : TxRec X V}
    (hs : pstate h p = ⟨[], t⟩) (k : ℕ) :
    txRec h (p, k) = if k = 0 then t else TxRec.empty := by
  simp only [txRec, hs]
  rcases k with _ | k <;> simp

lemma not_began_empty {h : List (Lbl P X V)} {T : TxId P} (hT : txRec h T = TxRec.empty) :
    ¬ Began h T := by
  simp [Began, hT, TxRec.empty]

lemma not_committed_empty {h : List (Lbl P X V)} {T : TxId P} (hT : txRec h T = TxRec.empty) :
    ¬ Committed h T := by
  simp [Committed, hT, TxRec.empty]

lemma not_vOrd [DecidableEq X] {h : List (Lbl P X V)} {z : X} {T₀ : TxId P} (hc : ∀ T, CWriter h z T ↔ T = T₀)
    (T T' : TxId P) : ¬ VOrd h z T T' := by
  rintro ⟨h1, h2, h₁, h₂, -, hc1, hc2⟩
  rw [hc] at h1 h2; subst h1 h2; exact hc2 hc1

lemma nextV_none [DecidableEq X] {h : List (Lbl P X V)} {z : X} {T₀ : TxId P} (hc : ∀ T, CWriter h z T ↔ T = T₀) :
    NextV h z none T₀ := ⟨(hc T₀).2 rfl, fun ⟨T'', hT⟩ => not_vOrd hc _ _ hT⟩

/-! ### The scenario -/

section Scenario

variable [DecidableEq X] (v₀ : X → V) {a b c : P} {x y : X} {v₁ w r₁ r₂ s₁ s₂ u : V}
  {βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂ : List (Lbl P X V)}

/-- `T₄`'s first read: `R₄(y)` returns the initial value. -/
def bA (a : P) (y : X) (βa₁ : List (Lbl P X V)) : List (Lbl P X V) :=
  Blk a (.read y) βa₁ (some (v₀ y))

/-- `T₃ = W₃(y) c₃`. -/
def bC (c : P) (y : X) (v₁ r₁ r₂ : V) (βc₁ βc₂ : List (Lbl P X V)) : List (Lbl P X V) :=
  Blk c (.write y v₁) βc₁ (some r₁) ++ Blk c .tryC βc₂ (some r₂)

/-- `T₂ = W₂(x) c₂`. -/
def bB (b : P) (x : X) (v₁ s₁ s₂ : V) (βb₁ βb₂ : List (Lbl P X V)) : List (Lbl P X V) :=
  Blk b (.write x v₁) βb₁ (some s₁) ++ Blk b .tryC βb₂ (some s₂)

/-- The rest of `T₄`: `R₄(x) c₄`. -/
def bR (a : P) (x : X) (w u : V) (βa₂ βa₃ : List (Lbl P X V)) : List (Lbl P X V) :=
  Blk a (.read x) βa₂ (some w) ++ Blk a .tryC βa₃ (some u)

/-- The record of `T₄`. -/
def recA (x y : X) (y0 w u : V) : TxRec X V :=
  ⟨[(.read y, some y0), (.read x, some w), (.tryC, some u)], none⟩

/-- The record of `T₃`. -/
def recC (y : X) (v₁ r₁ r₂ : V) : TxRec X V := ⟨[(.write y v₁, some r₁), (.tryC, some r₂)], none⟩

/-- The record of `T₂`. -/
def recB (x : X) (v₁ s₁ s₂ : V) : TxRec X V := ⟨[(.write x v₁, some s₁), (.tryC, some s₂)], none⟩

variable (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (ha₁ : Taus a βa₁) (ha₂ : Taus a βa₂) (ha₃ : Taus a βa₃) (hc₁ : Taus c βc₁) (hc₂ : Taus c βc₂)
  (hb₁ : Taus b βb₁) (hb₂ : Taus b βb₂)

include hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ in
/-- The bookkeeping of any interleaving of the blocks that keeps the order of each process. -/
lemma pstate_full {h : List (Lbl P X V)}
    (hp : ∀ p, projP h p = projP (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bR a x w u βa₂ βa₃) p) (p : P) :
    pstate h p = if p = a then ⟨[recA x y (v₀ y) w u], TxRec.empty⟩
      else if p = c then ⟨[recC y v₁ r₁ r₂], TxRec.empty⟩
      else if p = b then ⟨[recB x v₁ s₁ s₂], TxRec.empty⟩
      else PState.init := by
  rw [pstate_eq_foldl, hp]
  simp only [bA, bC, bB, bR, projP_append, List.foldl_append, foldl_projP_blk ha₁,
    foldl_projP_blk ha₂, foldl_projP_blk ha₃, foldl_projP_blk hc₁, foldl_projP_blk hc₂,
    foldl_projP_blk hb₁, foldl_projP_blk hb₂]
  have nab := Ne.symm hab; have nac := Ne.symm hac; have nbc := Ne.symm hbc
  by_cases hpa : p = a
  · subst hpa
    simp [hab, hac, nab, nac, PState.step, PState.init, endsTx, recA, TxRec.empty]
  by_cases hpc : p = c
  · subst hpc
    simp [hpa, Ne.symm hpa, hbc, nbc, PState.step, PState.init, endsTx, recC, TxRec.empty]
  by_cases hpb : p = b
  · subst hpb
    simp [hpa, Ne.symm hpa, hpc, Ne.symm hpc, PState.step, PState.init, endsTx, recB, TxRec.empty]
  simp [Ne.symm hpa, Ne.symm hpb, Ne.symm hpc, hpa, hpb, hpc]

include hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ in
/-- The transactions of such a history. -/
lemma txRec_full {h : List (Lbl P X V)}
    (hp : ∀ p, projP h p = projP (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bR a x w u βa₂ βa₃) p) (T : TxId P) :
    txRec h T = if T = (a, 0) then recA x y (v₀ y) w u
      else if T = (c, 0) then recC y v₁ r₁ r₂
      else if T = (b, 0) then recB x v₁ s₁ s₂
      else TxRec.empty := by
  obtain ⟨p, k⟩ := T
  have hs := pstate_full v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hp p
  by_cases hpa : p = a
  · subst hpa; simp only [if_pos rfl] at hs
    rw [txRec_of_done hs]; rcases k with _ | k <;> simp [hac, hab]
  by_cases hpc : p = c
  · subst hpc; simp only [if_neg hpa, if_pos rfl] at hs
    rw [txRec_of_done hs]; rcases k with _ | k <;> simp [hpa, hbc]
  by_cases hpb : p = b
  · subst hpb; simp only [if_neg hpa, if_neg hpc, if_pos rfl] at hs
    rw [txRec_of_done hs]; rcases k with _ | k <;> simp [hpa, hpc]
  simp only [if_neg hpa, if_neg hpc, if_neg hpb] at hs
  rw [txRec_of_init hs]; simp [hpa, hpb, hpc]

omit [DecidableEq X] in
lemma writesOf_recA (x y : X) (y0 w u : V) : writesOf (recA x y y0 w u).ops = [] := rfl

include hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ in
/-- The only version of `x` besides the initial one is `T₂`'s. -/
lemma cwriter_full {h : List (Lbl P X V)} (hxy : x ≠ y)
    (hp : ∀ p, projP h p = projP (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bR a x w u βa₂ βa₃) p) (T : TxId P) :
    (CWriter h x T ↔ T = (b, 0)) ∧ (CWriter h y T ↔ T = (c, 0)) := by
  have ht := txRec_full v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hp
  have hba : (b, 0) ≠ (a, 0) := by simp [Ne.symm hab]
  have hca : (c, 0) ≠ (a, 0) := by simp [Ne.symm hac]
  have hcb : (c, 0) ≠ (b, 0) := by simp [Ne.symm hbc]
  by_cases h1 : T = (a, 0)
  · subst h1
    simp [CWriter, wval, ht, recA, writesOf, hba, hca, hab, hac]
  by_cases h2 : T = (c, 0)
  · subst h2
    simp [CWriter, Committed, wval, ht, h1, recC, writesOf, hxy, Ne.symm hxy, hcb]
  by_cases h3 : T = (b, 0)
  · subst h3
    simp [CWriter, Committed, wval, ht, h1, h2, recB, writesOf, hxy, Ne.symm hcb]
  simp [CWriter, Committed, ht, h1, h2, h3, TxRec.empty]

/-- `E = R₄(y) · W₃(y) c₃ · W₂(x) c₂ · R₄(x) c₄` (the execution of Figure 1). -/
def execE (a b c : P) (x y : X) (v₁ w r₁ r₂ s₁ s₂ u : V)
    (βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂ : List (Lbl P X V)) : List (Lbl P X V) :=
  bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++ bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bR a x w u βa₂ βa₃

/-- `E' = W₂(x) c₂ · R₄(y) · W₃(y) c₃ · R₄(x) c₄`. -/
def execE' (a b c : P) (x y : X) (v₁ w r₁ r₂ s₁ s₂ u : V)
    (βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂ : List (Lbl P X V)) : List (Lbl P X V) :=
  bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++ bR a x w u βa₂ βa₃

omit [DecidableEq X] in
lemma projP_comm {l₁ l₂ : List (Lbl P X V)} {q₁ q₂ : P} (hq : q₁ ≠ q₂)
    (h₁ : ∀ ℓ ∈ l₁, ℓ.proc = q₁) (h₂ : ∀ ℓ ∈ l₂, ℓ.proc = q₂) (p : P) :
    projP l₁ p ++ projP l₂ p = projP l₂ p ++ projP l₁ p := by
  by_cases hp : p = q₁
  · subst hp
    have : projP l₂ p = [] := List.filter_eq_nil_iff.2 (fun ℓ hℓ => by simp [h₂ ℓ hℓ, Ne.symm hq])
    simp [this]
  · have : projP l₁ p = [] := List.filter_eq_nil_iff.2 (fun ℓ hℓ => by simp [h₁ ℓ hℓ, Ne.symm hp])
    simp [this]

omit [DecidableEq X] in
lemma proc_blk {q : P} {o : TOp X V} {β : List (Lbl P X V)} {r : Option V} (hβ : Taus q β) :
    ∀ ℓ ∈ Blk q o β r, ℓ.proc = q := by
  intro ℓ hℓ
  simp only [Blk, List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton] at hℓ
  rcases hℓ with rfl | hℓ | hℓ
  · rfl
  · rw [hβ ℓ hℓ]; rfl
  · simp only [List.not_mem_nil, or_false] at hℓ; subst hℓ; rfl

omit [DecidableEq X] in
lemma projP_of_proc {l : List (Lbl P X V)} {q : P} (hl : ∀ ℓ ∈ l, ℓ.proc = q) (p : P) :
    projP l p = if q = p then l else [] := by
  split_ifs with h
  · subst h; exact List.filter_eq_self.2 (fun ℓ hℓ => by simp [hl ℓ hℓ])
  · exact List.filter_eq_nil_iff.2 (fun ℓ hℓ => by simp [hl ℓ hℓ, h])

lemma proc_append {l₁ l₂ : List (Lbl P X V)} {q : P} (h₁ : ∀ ℓ ∈ l₁, ℓ.proc = q)
    (h₂ : ∀ ℓ ∈ l₂, ℓ.proc = q) : ∀ ℓ ∈ l₁ ++ l₂, ℓ.proc = q := by
  intro ℓ hℓ; rcases List.mem_append.1 hℓ with h | h <;> [exact h₁ ℓ h; exact h₂ ℓ h]

include hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ in
/-- **`H_WRTO` does not preserve RTO**: if `R₄(x)` returns the value written by `T₂`, then
`T₃ ≺RTO T₂ →wr T₄ →rw T₃` is a cycle. -/
theorem not_preservesRTO_execE (hxy : x ≠ y) :
    ¬ PreservesRTO v₀ (execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  set h := execE v₀ a b c x y v₁ v₁ r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂
  have hp : ∀ p, projP h p = projP (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bR a x v₁ u βa₂ βa₃) p := fun _ => rfl
  have ht := txRec_full v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hp
  have hcw := cwriter_full v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy hp
  have hba : (b, 0) ≠ (a, 0) := by simp [Ne.symm hab]
  have hca : (c, 0) ≠ (a, 0) := by simp [Ne.symm hac]
  have hcb : (c, 0) ≠ (b, 0) := by simp [Ne.symm hbc]
  intro H
  -- `T₃ ≺RTO T₂`
  have hrto : RTO h (c, 0) (b, 0) := by
    refine ⟨Or.inl (by simp [ht, hba, hcb, Ne.symm hcb, hbc, recB]), bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂,
      bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bR a x v₁ u βa₂ βa₃, by simp [h, execE], ?_, ?_⟩
    · have hs : pstate (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂) c =
          ⟨[recC y v₁ r₁ r₂], TxRec.empty⟩ := by
        simp [pstate_eq_foldl, bA, bC, projP_append, foldl_projP_blk ha₁, foldl_projP_blk hc₁,
          foldl_projP_blk hc₂, hac, PState.step, PState.init, endsTx, recC, TxRec.empty]
      simp [Committed, txRec_of_done hs, recC]
    · have hs : pstate (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂) b = PState.init := by
        simp [pstate_eq_foldl, bA, bC, projP_append, foldl_projP_blk ha₁, foldl_projP_blk hc₁,
          foldl_projP_blk hc₂, hab, hbc, Ne.symm hbc]
      exact not_began_empty (txRec_of_init hs 0)
  refine H _ _ hrto (Relation.TransGen.head (b := (a, 0)) (Or.inl ?_)
    (Relation.TransGen.single (Or.inl ?_)))
  · -- `T₂ →wr T₄`
    refine Or.inl ⟨hba, ((hcw (b, 0)).1.2 rfl).1, x, v₁, ?_, ?_⟩
    · simp [Reads, ht, recA]
    · simp [wval, ht, hba, hcb, Ne.symm hcb, hbc, recB, writesOf]
  · -- `T₄ →rw T₃`
    refine Or.inr (Or.inr ⟨Ne.symm hca, y, v₀ y, none, ?_, rfl, by simp, ?_⟩)
    · simp [Reads, ht, recA]
    · exact nextV_none (fun T => (hcw T).2)

include hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ in
/-- If `R₄(x)` returns the initial value in `E'` (where `T₂` committed before `T₄` began), then
`T₂ ≺WRTO T₄ →rw T₂` is a cycle. -/
theorem not_preservesWRTO_execE' (hxy : x ≠ y) :
    ¬ PreservesWRTO v₀
      (execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  set h := execE' v₀ a b c x y v₁ (v₀ x) r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂
  have pA : ∀ ℓ ∈ bA v₀ a y βa₁, ℓ.proc = a := proc_blk ha₁
  have pB : ∀ ℓ ∈ bB b x v₁ s₁ s₂ βb₁ βb₂, ℓ.proc = b :=
    proc_append (proc_blk hb₁) (proc_blk hb₂)
  have pC : ∀ ℓ ∈ bC c y v₁ r₁ r₂ βc₁ βc₂, ℓ.proc = c :=
    proc_append (proc_blk hc₁) (proc_blk hc₂)
  have hp : ∀ p, projP h p = projP (bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++
      bB b x v₁ s₁ s₂ βb₁ βb₂ ++ bR a x (v₀ x) u βa₂ βa₃) p := by
    intro p
    simp only [h, execE', projP_append, projP_of_proc pA, projP_of_proc pB, projP_of_proc pC]
    by_cases h1 : a = p
    · subst h1; simp [Ne.symm hab, Ne.symm hac]
    · by_cases h2 : b = p
      · subst h2; simp [h1, Ne.symm hbc]
      · simp [h1, h2]
  have ht := txRec_full v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hp
  have hcw := cwriter_full v₀ hab hac hbc ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ hxy hp
  have hba : (b, 0) ≠ (a, 0) := by simp [Ne.symm hab]
  intro H
  have hdsg : DSG v₀ h (a, 0) (b, 0) := by
    refine Or.inr (Or.inr ⟨Ne.symm hba, x, v₀ x, none, ?_, rfl, by simp, ?_⟩)
    · simp [Reads, ht, recA]
    · exact nextV_none (fun T => (hcw T).1)
  have hrto : RTO h (b, 0) (a, 0) := by
    refine ⟨Or.inl (by simp [ht, recA]), bB b x v₁ s₁ s₂ βb₁ βb₂,
      bA v₀ a y βa₁ ++ bC c y v₁ r₁ r₂ βc₁ βc₂ ++ bR a x (v₀ x) u βa₂ βa₃, by simp [h, execE'],
      ?_, ?_⟩
    · have hs : pstate (bB b x v₁ s₁ s₂ βb₁ βb₂) b = ⟨[recB x v₁ s₁ s₂], TxRec.empty⟩ := by
        simp [pstate_eq_foldl, bB, projP_append, foldl_projP_blk hb₁, foldl_projP_blk hb₂,
          PState.step, PState.init, endsTx, recB, TxRec.empty]
      simp [Committed, txRec_of_done hs, recB]
    · have hs : pstate (bB b x v₁ s₁ s₂ βb₁ βb₂) a = PState.init := by
        simp [pstate_eq_foldl, bB, projP_append, foldl_projP_blk hb₁, foldl_projP_blk hb₂,
          Ne.symm hab]
      exact not_began_empty (txRec_of_init hs 0)
  exact H _ _ ⟨hrto, Or.inr hdsg⟩ (Relation.TransGen.single (Or.inl hdsg))

omit [DecidableEq P] [DecidableEq X] in
lemma filterMap_writeInv_blk {q : P} {o : TOp X V} {β : List (Lbl P X V)} {r : Option V}
    (hβ : Taus q β) : (Blk q o β r).filterMap writeInv = (writeInv (.inv q o : Lbl P X V)).toList := by
  have : β.filterMap writeInv = [] :=
    List.filterMap_eq_nil_iff.2 (fun ℓ hℓ => by rw [hβ ℓ hℓ]; rfl)
  have hr : writeInv (.ret q r : Lbl P X V) = none := rfl
  cases h : writeInv (.inv q o : Lbl P X V) <;>
    simp [Blk, List.filterMap_append, h, hr, this]

omit [DecidableEq P] [DecidableEq X] in
include ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ in
/-- With `v₁` different from the initial values of `x` and `y`, the written values of `E` are
unique. -/
lemma uniqueWrites_execE (hxy : x ≠ y) (hx : v₁ ≠ v₀ x) (hy : v₁ ≠ v₀ y) :
    UniqueWrites v₀ (execE v₀ a b c x y v₁ w r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  simp only [UniqueWrites, execE, bA, bB, bC, bR, List.filterMap_append,
    filterMap_writeInv_blk ha₁, filterMap_writeInv_blk ha₂, filterMap_writeInv_blk ha₃,
    filterMap_writeInv_blk hc₁, filterMap_writeInv_blk hc₂, filterMap_writeInv_blk hb₁,
    filterMap_writeInv_blk hb₂, writeInv]
  simp [Ne.symm hxy, hx, hy]

omit [DecidableEq P] [DecidableEq X] in
include ha₁ ha₂ ha₃ hc₁ hc₂ hb₁ hb₂ in
/-- The written values of `E'` are unique (as for `E`). -/
lemma uniqueWrites_execE' (hxy : x ≠ y) (hx : v₁ ≠ v₀ x) (hy : v₁ ≠ v₀ y) :
    UniqueWrites v₀ (execE' v₀ a b c x y v₁ w r₁ r₂ s₁ s₂ u βa₁ βa₂ βa₃ βc₁ βc₂ βb₁ βb₂) := by
  simp only [UniqueWrites, execE', bA, bB, bC, bR, List.filterMap_append,
    filterMap_writeInv_blk ha₁, filterMap_writeInv_blk ha₂, filterMap_writeInv_blk ha₃,
    filterMap_writeInv_blk hc₁, filterMap_writeInv_blk hc₂, filterMap_writeInv_blk hb₁,
    filterMap_writeInv_blk hb₂, writeInv]
  simp [hxy, hx, hy]

end Scenario

end Podc.DAPInvisibleReads
