import Papers.PODC2020.IntermediateValueLin.Canonical
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The concurrent CountMin sketch (Section 5 of Rinberg–Keidar)

Rinberg, Keidar, *Intermediate Value Linearizability: A Quantitative Correctness Criterion*,
PODC 2020, full version arXiv:2006.12889, Section 5.

* `CMOp E`: the operations `update a` and `query a` of a CountMin sketch over the elements `E`.
* `cmSpec h`: the sequential CountMin sketch `CM(c⃗)` of Algorithm 1 for the hash functions
  `h i : E → Fin w`, `i : Fin d` (the hash functions are what the coin flip vector `c⃗`
  determines). The state is the `d × w` matrix of counters, initially `0`; `update a` increments
  `c[i][hᵢ(a)]` for every row `i` and returns the dummy response `0`; `query a` returns
  `min_i c[i][hᵢ(a)]` (`⨅ i, …`; for the degenerate `d = 0` this is `0`).
* `cmIface E`: the interface object of the implementations (operations `CMOp E`, responses `ℕ`,
  one dummy state). All implementations `pcm h` share it, so their histories have the same type,
  whatever the hash functions.
* `cell`: the base objects, one atomic counter per cell `(i, j) : Fin d × Fin w`, with the
  primitives `inc` (increment) and `read`.
* `pcm h` (the paper's `PCM(c⃗)`): Algorithm 1 run concurrently. `update a` increments the cells
  `c[i][hᵢ(a)]` for `i = 0, …, d - 1`, one access each, then returns; `query a` reads the cells
  `c[i][hᵢ(a)]` one by one, keeping the running minimum, and returns it.

Main results:
* `pcm_sandwich` (strong form of **Lemma 1**): in every execution `α` of `pcm h`, every completed
  instance gets a response between the responses that `cmSpec h` assigns to it in the canonical
  skeleton linearizations `H₁ = canon (!isUpdate) α` (queries at invocation, updates at
  response) and `H₂ = canon isUpdate α` (updates at invocation, queries at response). These two
  linearizations depend only on the skeleton `α?` (`canon_skel`), so they are the same for all
  hash functions.
* `pcm_ivl` (**Lemma 1**): `pcm h` is an IVL implementation of `cmSpec h`.
* `example2_not_lin`, `pcm_not_linearizable` (**Example 2**): the execution of Example 2 is an
  execution of `pcm hEx` (for the hash functions of the example) that is not linearizable with
  respect to `cmSpec hEx`.
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

/-! ## The sequential CountMin sketch -/

/-- Operations of a CountMin sketch over the elements `E`. -/
inductive CMOp (E : Type) where
  /-- `update(a)`: record one occurrence of `a`. -/
  | update (a : E)
  /-- `query(a)`: estimate the number of occurrences of `a`. -/
  | query (a : E)
  deriving DecidableEq

/-- Updates are linearized at their invocation in `H₂` and at their response in `H₁`. -/
def CMOp.isUpdate {E : Type} : CMOp E → Bool
  | .update _ => true
  | .query _ => false

@[simp] lemma CMOp.isUpdate_update {E : Type} (a : E) : (CMOp.update a).isUpdate = true := rfl
@[simp] lemma CMOp.isUpdate_query {E : Type} (a : E) : (CMOp.query a).isUpdate = false := rfl

variable {E : Type} [DecidableEq E] {d w : ℕ}

/-- The sequential CountMin sketch `CM(c⃗)` (Algorithm 1) for the hash functions
`h i : E → Fin w`, `i : Fin d`: a `d × w` matrix of counters initialized to `0`; `update a`
increments `c[i][hᵢ(a)]` for every `i` and returns the dummy `0`; `query a` returns
`min_i c[i][hᵢ(a)]`. -/
noncomputable abbrev cmSpec (h : Fin d → E → Fin w) : QSpec (CMOp E) ℕ where
  State := Fin d → Fin w → ℕ
  init := fun _ _ => 0
  δ c
    | .update a => (fun i j => c i j + if h i a = j then 1 else 0, 0)
    | .query a => (c, ⨅ i, c i (h i a))

/-- The interface object of the concurrent implementations: the operations of a CountMin sketch
with responses in `ℕ`, and a dummy state (the specifications are given separately by `cmSpec h`).
-/
abbrev cmIface (E : Type) : ObjSpec where
  State := Unit
  Op := CMOp E
  Resp := ℕ
  init := ()
  δ _ _ := ((), 0)

/-- Primitives of an atomic counter. -/
inductive CellOp where
  /-- Atomically increment the counter. -/
  | inc
  /-- Read the counter. -/
  | read
  deriving DecidableEq

/-- An atomic counter (a cell of the matrix): `inc` increments it (dummy response `0`), `read`
returns its value. -/
abbrev cell : ObjSpec where
  State := ℕ
  Op := CellOp
  Resp := ℕ
  init := 0
  δ s
    | .inc => (s + 1, 0)
    | .read => (s, s)

/-- Local states of a process running Algorithm 1. -/
inductive CMLoc (E : Type) where
  /-- No pending operation. -/
  | idle
  /-- Running `update a`; the next row to increment is `k`. -/
  | upd (a : E) (k : ℕ)
  /-- Running `query a`; the next row to read is `k`, `m` is the minimum read so far
  (`none` = `∞`). -/
  | qry (a : E) (k : ℕ) (m : Option ℕ)
  deriving DecidableEq

/-- The running minimum of a query (line 10 of Algorithm 1), `none` standing for `∞`. -/
def minWith : Option ℕ → ℕ → ℕ
  | none, v => v
  | some u, v => min u v

/-- `PCM(c⃗)`: Algorithm 1 run concurrently by processes `P`, from one atomic counter per cell
`(i, j) : Fin d × Fin w`. `update a` increments `c[i][hᵢ(a)]` for `i = 0, …, d - 1` (one atomic
access each) and returns; `query a` reads `c[i][hᵢ(a)]` for `i = 0, …, d - 1`, keeping the
running minimum, and returns it. -/
def pcm (h : Fin d → E → Fin w) (P : Type) :
    Impl (cmIface E) (fun _ : Fin d × Fin w => cell) P (CMLoc E) where
  memInit _ := 0
  locInit _ := .idle
  invoke _ _
    | .update a => .upd a 0
    | .query a => .qry a 0 none
  act _
    | .idle => .ret 0 .idle
    | .upd a k =>
      if hk : k < d then .access (⟨k, hk⟩, h ⟨k, hk⟩ a) .inc (fun _ => .upd a (k + 1))
      else .ret 0 .idle
    | .qry a k m =>
      if hk : k < d then
        .access (⟨k, hk⟩, h ⟨k, hk⟩ a) .read (fun v => .qry a (k + 1) (some (minWith m v)))
      else .ret (m.getD 0) .idle

/-- All operations are allowed in `pcm h` (needed to evaluate executions with `Impl.crun`). -/
instance (h : Fin d → E → Fin w) (P : Type) (p : P) (o : CMOp E) :
    Decidable ((pcm h P).allowed p o) :=
  isTrue trivial

@[simp] lemma cmSpec_update (h : Fin d → E → Fin w) (c : Fin d → Fin w → ℕ) (a : E) :
    (cmSpec h).δ c (.update a) = (fun i j => c i j + if h i a = j then 1 else 0, 0) := rfl

@[simp] lemma cmSpec_query (h : Fin d → E → Fin w) (c : Fin d → Fin w → ℕ) (a : E) :
    (cmSpec h).δ c (.query a) = (c, ⨅ i, c i (h i a)) := rfl

/-! ## Lemma 1: `PCM` is IVL -/

section Lemma1

variable {P : Type} [DecidableEq P] (h : Fin d → E → Fin w)

/-! Auxiliary definitions and the invariant (namespace `CM`). -/

namespace CM

/-- The matrix of counters after the sequential history `L` of `cmSpec h`. -/
noncomputable def cnt (L : List (OpId P × CMOp E)) : Fin d → Fin w → ℕ :=
  (cmSpec h).obj.runOps (cmSpec h).init (L.map Prod.snd)

lemma runOps_le (c : Fin d → Fin w → ℕ) (os : List (CMOp E)) (i : Fin d) (j : Fin w) :
    c i j ≤ (cmSpec h).obj.runOps c os i j := by
  induction os generalizing c with
  | nil => exact le_rfl
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    refine le_trans ?_ (ih _)
    cases o <;> simp

lemma cnt_append (L M : List (OpId P × CMOp E)) :
    cnt h (L ++ M) = (cmSpec h).obj.runOps (cnt h L) (M.map Prod.snd) := by
  simp only [cnt, List.map_append]; exact ObjSpec.runOps_append _ _ _ _

lemma cnt_le_append (L M : List (OpId P × CMOp E)) (i : Fin d) (j : Fin w) :
    cnt h L i j ≤ cnt h (L ++ M) i j := by
  rw [cnt_append]; exact runOps_le h _ _ i j

lemma cnt_concat_update (L : List (OpId P × CMOp E)) (x : OpId P) (a : E) (i : Fin d)
    (j : Fin w) : cnt h (L ++ [(x, .update a)]) i j = cnt h L i j + if h i a = j then 1 else 0 := by
  rw [cnt_append]; rfl

lemma cnt_concat_query (L : List (OpId P × CMOp E)) (x : OpId P) (a : E) :
    cnt h (L ++ [(x, .query a)]) = cnt h L := by
  rw [cnt_append]; rfl

/-- The paper's `H₁`: queries linearized at their invocation, updates at their response. -/
abbrev H₁ (α : List (Label P (cmIface E))) : List (OpId P × CMOp E) :=
  canon (fun o : CMOp E => !o.isUpdate) α

/-- The paper's `H₂`: updates linearized at their invocation, queries at their response. -/
abbrev H₂ (α : List (Label P (cmIface E))) : List (OpId P × CMOp E) :=
  canon (fun o : CMOp E => o.isUpdate) α

/-- The processes that took a step in `α`. -/
def procs (α : List (Label P (cmIface E))) : Finset P := (α.map Label.proc).toFinset

lemma procs_concat (α : List (Label P (cmIface E))) (ℓ : Label P (cmIface E)) :
    procs (α ++ [ℓ]) = insert ℓ.proc (procs α) := by
  ext q; simp [procs]

/-- Increments already performed by a pending update in local state `l`, per cell. -/
def done : CMLoc E → Fin d → Fin w → ℕ
  | .upd a k, i, j => if i.val < k ∧ h i a = j then 1 else 0
  | _, _, _ => 0

/-- All increments of a pending update in local state `l`, per cell. -/
def todo : CMLoc E → Fin d → Fin w → ℕ
  | .upd a _, i, j => if h i a = j then 1 else 0
  | _, _, _ => 0

lemma done_le_todo (l : CMLoc E) (i : Fin d) (j : Fin w) : done h l i j ≤ todo h l i j := by
  cases l with
  | upd a k => simp only [done, todo]; split_ifs <;> simp_all
  | _ => exact le_rfl

lemma sum_update_insert {X : Type} (S : Finset P) (f : P → X) (q : P) (x : X) (g : X → ℕ)
    (hq : q ∉ S → g (f q) = 0) :
    ∑ p ∈ insert q S, g (Function.update f q x p) + g (f q) = ∑ p ∈ S, g (f p) + g x := by
  have hcongr : ∀ T : Finset P, q ∉ T →
      ∑ p ∈ T, g (Function.update f q x p) = ∑ p ∈ T, g (f p) := fun T hT =>
    Finset.sum_congr rfl fun p hp => by
      rw [Function.update_of_ne (by rintro rfl; exact hT hp)]
  by_cases hS : q ∈ S
  · rw [Finset.insert_eq_of_mem hS, ← Finset.add_sum_erase S _ hS,
      ← Finset.add_sum_erase S _ hS, hcongr _ (Finset.notMem_erase q S)]
    simp only [Function.update_self]; omega
  · rw [Finset.sum_insert hS, hcongr S hS, hq hS, Function.update_self]; omega

/-- The invariant of a pending query `query a` in local state `qry a k m`: `c₁` is the matrix of
`H₁` when the query was invoked, `c₂` the current matrix of `H₂`. The running minimum `m` is
`∞` (`none`) iff no cell has been read yet; it is at most the `H₂`-value of every cell read so
far, and at least the `H₁`-value of some cell. -/
def QryOK (c₁ c₂ : Fin d → Fin w → ℕ) (a : E) (k : ℕ) (m : Option ℕ) : Prop :=
  (m = none ↔ k = 0) ∧ ∀ v, m = some v →
    (∀ i : Fin d, i.val < k → v ≤ c₂ i (h i a)) ∧ ∃ i, c₁ i (h i a) ≤ v

lemma QryOK.mono {c₁ c₂ c₂' : Fin d → Fin w → ℕ} {a : E} {k : ℕ} {m : Option ℕ}
    (hc : ∀ i j, c₂ i j ≤ c₂' i j) (hq : QryOK h c₁ c₂ a k m) : QryOK h c₁ c₂' a k m :=
  ⟨hq.1, fun v hv => ⟨fun i hi => le_trans ((hq.2 v hv).1 i hi) (hc _ _), (hq.2 v hv).2⟩⟩

/-- The sandwich at the end of a query: the response `m.getD 0` is between the minima over the
rows of `c₁` and `c₂`. -/
lemma QryOK.sandwich {c₁ c₂ : Fin d → Fin w → ℕ} {a : E} {k : ℕ} {m : Option ℕ}
    (hq : QryOK h c₁ c₂ a k m) (hk : ¬ k < d) :
    (⨅ i, c₁ i (h i a)) ≤ m.getD 0 ∧ m.getD 0 ≤ ⨅ i, c₂ i (h i a) := by
  cases m with
  | none =>
    have hd : d = 0 := by have := hq.1.1 rfl; omega
    subst hd
    simp
  | some v =>
    obtain ⟨h2, i₀, h1⟩ := hq.2 v rfl
    have : Nonempty (Fin d) := ⟨i₀⟩
    refine ⟨le_trans (ciInf_le (OrderBot.bddBelow _) i₀) h1, ?_⟩
    exact le_ciInf fun i => h2 i (by omega)

/-- Configurations of `pcm h`. -/
abbrev CMCfg (d w : ℕ) (E P : Type) :=
  Config (cmIface E) (fun _ : Fin d × Fin w => cell) P (CMLoc E)

/-- The per-process part of the invariant: the local state matches the pending operation, and a
pending query satisfies `QryOK` with respect to the matrix of `H₁` at its invocation and the
current matrix of `H₂`. -/
def ProcOK (α : List (Label P (cmIface E))) (C : CMCfg d w E P) (p : P) : Prop :=
  (C.pend p = none → C.loc p = .idle) ∧
  (∀ a, C.pend p = some (.update a) → ∃ k, C.loc p = .upd a k) ∧
  (∀ a, C.pend p = some (.query a) → ∃ k m, C.loc p = .qry a k m ∧
    ∃ β γ, α = β ++ Label.inv p (CMOp.query a) :: γ ∧ opsOf γ p = [] ∧
      QryOK h (cnt h (H₁ β)) (cnt h (H₂ α)) a k m)

/-- The invariant behind Lemma 1. Every cell holds the number of `H₁`-updates hashing to it plus
the increments already done by pending updates; `H₂` additionally contains all increments of the
pending updates. -/
structure PInv (α : List (Label P (cmIface E))) (C : CMCfg d w E P) : Prop where
  out : ∀ p, p ∉ procs α → C.loc p = .idle
  proc : ∀ p, ProcOK h α C p
  mem : ∀ i j, @Eq ℕ (C.mem (i, j)) (cnt h (H₁ α) i j + ∑ p ∈ procs α, done h (C.loc p) i j)
  gap : ∀ i j, cnt h (H₂ α) i j = cnt h (H₁ α) i j + ∑ p ∈ procs α, todo h (C.loc p) i j
  resp : ∀ x r, respOf α x = some r → ∃ r₁ r₂, tau (cmSpec h) (H₁ α) x = some r₁ ∧
    tau (cmSpec h) (H₂ α) x = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂

variable {h}

lemma PInv.cnt₁_le {α : List (Label P (cmIface E))} {C : CMCfg d w E P} (hI : PInv h α C)
    (i : Fin d) (j : Fin w) : cnt h (H₁ α) i j ≤ C.mem (i, j) := by
  rw [hI.mem]; exact Nat.le_add_right _ _

lemma PInv.le_cnt₂ {α : List (Label P (cmIface E))} {C : CMCfg d w E P} (hI : PInv h α C)
    (i : Fin d) (j : Fin w) : C.mem (i, j) ≤ cnt h (H₂ α) i j := by
  rw [hI.mem, hI.gap]
  exact Nat.add_le_add_left (Finset.sum_le_sum fun p _ => done_le_todo h _ i j) _

variable (h) in
lemma pinv_init : PInv h [] (pcm h P).initCfg := by
  refine ⟨fun _ _ => rfl, fun p => ⟨fun _ => rfl, ?_, ?_⟩, fun i j => ?_, fun i j => ?_, ?_⟩
  · intro a ha; simp [Impl.initCfg] at ha
  · intro a ha; simp [Impl.initCfg] at ha
  · simp [Impl.initCfg, pcm, procs, cnt]; rfl
  · simp [procs]
  · intro x r hx; simp [respOf] at hx

lemma tau_concat_of_eq_some {f : CMOp E → Bool} {α : List (Label P (cmIface E))}
    {ℓ : Label P (cmIface E)} {x : OpId P} {r : ℕ}
    (hx : tau (cmSpec h) (canon f α) x = some r) :
    tau (cmSpec h) (canon f (α ++ [ℓ])) x = some r := by
  rw [canon_concat, tau]; exact ObjSpec.respIn_append_of_eq_some hx _

lemma cnt_canon_le_append (f : CMOp E → Bool) (α β : List (Label P (cmIface E))) (i : Fin d)
    (j : Fin w) : cnt h (canon f α) i j ≤ cnt h (canon f (α ++ β)) i j := by
  rw [canon_append]; exact cnt_le_append h _ _ i j

lemma cnt₂_mono (α : List (Label P (cmIface E))) (ℓ : Label P (cmIface E)) (i : Fin d)
    (j : Fin w) : cnt h (H₂ α) i j ≤ cnt h (H₂ (α ++ [ℓ])) i j := by
  simp only [H₂, canon_concat]; exact cnt_le_append h _ _ i j

lemma procOK_other {α : List (Label P (cmIface E))} {C C' : CMCfg d w E P}
    {ℓ : Label P (cmIface E)} {q : P} (hs : (pcm h P).step C ℓ = some C') (hq : ℓ.proc ≠ q)
    (hok : ProcOK h α C q) : ProcOK h (α ++ [ℓ]) C' q := by
  obtain ⟨hl, hp⟩ := Impl.step_other hs hq
  refine ⟨fun h0 => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · rw [hl]; exact hok.1 (hp ▸ h0)
  · rw [hl]; exact hok.2.1 a (hp ▸ ha)
  · obtain ⟨k, m, hloc, β, γ, hα, hγ, hQ⟩ := hok.2.2 a (hp ▸ ha)
    refine ⟨k, m, hl ▸ hloc, β, γ ++ [ℓ], by simp [hα], ?_, hQ.mono h (cnt₂_mono α ℓ)⟩
    rw [opsOf_append, hγ, opsOf_cons, Label.invOf_eq_none_of_proc_ne hq]; rfl

lemma resp_of_eq {α : List (Label P (cmIface E))} {C : CMCfg d w E P} (hI : PInv h α C)
    (ℓ : Label P (cmIface E)) {x : OpId P} {r : ℕ} (hx : respOf α x = some r) :
    ∃ r₁ r₂, tau (cmSpec h) (H₁ (α ++ [ℓ])) x = some r₁ ∧
      tau (cmSpec h) (H₂ (α ++ [ℓ])) x = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂ := by
  obtain ⟨r₁, r₂, h1, h2, h3, h4⟩ := hI.resp x r hx
  exact ⟨r₁, r₂, tau_concat_of_eq_some h1, tau_concat_of_eq_some h2, h3, h4⟩

lemma pinv_step_inv {α : List (Label P (cmIface E))} {C C' : CMCfg d w E P} {p : P}
    {o : CMOp E} (hI : PInv h α C) (hs : (pcm h P).step C (.inv p o) = some C') :
    PInv h (α ++ [.inv p o]) C' := by
  obtain ⟨hpn, -, hpend', hloc', hmem'⟩ := Impl.step_inv hs
  have hlocp : C.loc p = .idle := (hI.proc p).1 hpn
  have hS : procs (α ++ [.inv p o]) = insert p (procs α) := procs_concat α _
  have hresp : ∀ x (r : ℕ), respOf (α ++ [.inv p o]) x = some r → ∃ r₁ r₂,
      tau (cmSpec h) (H₁ (α ++ [.inv p o])) x = some r₁ ∧
      tau (cmSpec h) (H₂ (α ++ [.inv p o])) x = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂ := by
    intro x r hx
    rw [respOf_append_of_not_ret (by simp)] at hx
    exact resp_of_eq hI _ hx
  have hout : ∀ q, q ∉ procs (α ++ [.inv p o]) → C'.loc q = .idle := by
    intro q hq
    rw [hS, Finset.mem_insert, not_or] at hq
    rw [hloc', Function.update_of_ne hq.1]; exact hI.out q hq.2
  have hsum := fun (L' : CMLoc E) (g : CMLoc E → ℕ) (hg : g .idle = 0) =>
    sum_update_insert (procs α) C.loc p L' g (fun _ => by rw [hlocp, hg])
  cases o with
  | update a =>
    have hL : C'.loc = Function.update C.loc p (.upd a 0) := by rw [hloc', hlocp]; rfl
    have h1 : H₁ (α ++ [.inv p (.update a)]) = H₁ α := by simp [H₁, canon_concat, canonEnt]
    have h2 : H₂ (α ++ [.inv p (.update a)]) =
        H₂ α ++ [((p, (opsOf α p).length), .update a)] := by
      simp [H₂, canon_concat, canonEnt]
    refine ⟨hout, fun q => ?_, fun i j => ?_, fun i j => ?_, hresp⟩
    · by_cases hq : q = p
      · subst hq
        refine ⟨fun h0 => by simp [hpend'] at h0, fun a' ha' => ⟨0, ?_⟩,
          fun a' ha' => by simp [hpend'] at ha'⟩
        simp only [hpend', Function.update_self, Option.some.injEq, CMOp.update.injEq] at ha'
        subst ha'; rw [hL, Function.update_self]
      · exact procOK_other hs (Ne.symm hq) (hI.proc q)
    · have := hsum (.upd a 0) (fun l => done h l i j) rfl
      have h0 : done h (.upd a 0) i j = 0 := by simp [done]
      have h0' : done h (C.loc p) i j = 0 := by rw [hlocp]; rfl
      rw [h0, h0', add_zero, add_zero] at this
      rw [hmem', hI.mem, hS, h1, hL, this]
    · have := hsum (.upd a 0) (fun l => todo h l i j) rfl
      have h0' : todo h (C.loc p) i j = 0 := by rw [hlocp]; rfl
      have h0 : todo h (.upd a 0) i j = if h i a = j then 1 else 0 := rfl
      rw [h0', add_zero] at this
      rw [hS, h1, hL, h2, cnt_concat_update, this, hI.gap, h0, add_assoc]
  | query a =>
    have hL : C'.loc = Function.update C.loc p (.qry a 0 none) := by rw [hloc', hlocp]; rfl
    have h1 : H₁ (α ++ [.inv p (.query a)]) =
        H₁ α ++ [((p, (opsOf α p).length), .query a)] := by
      simp [H₁, canon_concat, canonEnt]
    have h2 : H₂ (α ++ [.inv p (.query a)]) = H₂ α := by simp [H₂, canon_concat, canonEnt]
    refine ⟨hout, fun q => ?_, fun i j => ?_, fun i j => ?_, hresp⟩
    · by_cases hq : q = p
      · subst hq
        refine ⟨fun h0 => by simp [hpend'] at h0, fun a' ha' => by simp [hpend'] at ha',
          fun a' ha' => ?_⟩
        simp only [hpend', Function.update_self, Option.some.injEq, CMOp.query.injEq] at ha'
        subst ha'
        refine ⟨0, none, by rw [hL, Function.update_self], α, [], rfl, rfl, ?_⟩
        exact ⟨by simp, fun v hv => by cases hv⟩
      · exact procOK_other hs (Ne.symm hq) (hI.proc q)
    · have := hsum (.qry a 0 none) (fun l => done h l i j) rfl
      have h0' : done h (C.loc p) i j = 0 := by rw [hlocp]; rfl
      have h0 : done h (.qry a 0 none) i j = 0 := rfl
      rw [h0, h0', add_zero, add_zero] at this
      rw [hmem', hI.mem, hS, h1, hL, cnt_concat_query, this]
    · have := hsum (.qry a 0 none) (fun l => todo h l i j) rfl
      have h0' : todo h (C.loc p) i j = 0 := by rw [hlocp]; rfl
      have h0 : todo h (.qry a 0 none) i j = 0 := rfl
      rw [h0, h0', add_zero, add_zero] at this
      rw [hS, h1, hL, h2, cnt_concat_query, hI.gap, this]

lemma done_succ (a : E) (k : ℕ) (hk : k < d) (i : Fin d) (j : Fin w) :
    done h (.upd a (k + 1)) i j =
      done h (.upd a k) i j +
        if (i, j) = ((⟨k, hk⟩, h ⟨k, hk⟩ a) : Fin d × Fin w) then 1 else 0 := by
  simp only [done, Prod.mk.injEq]
  by_cases hi : i = ⟨k, hk⟩
  · subst hi
    by_cases hj : h ⟨k, hk⟩ a = j
    · subst hj; simp
    · simp [hj, Ne.symm hj]
  · have : i.val ≠ k := fun h' => hi (Fin.ext h')
    have hi' : (i.val < k + 1 ↔ i.val < k) := by omega
    simp [hi, hi']

lemma QryOK.step {c₁ c₂ : Fin d → Fin w → ℕ} {a : E} {k : ℕ} {m : Option ℕ}
    (hq : QryOK h c₁ c₂ a k m) (hk : k < d) (v : ℕ) (h1 : c₁ ⟨k, hk⟩ (h ⟨k, hk⟩ a) ≤ v)
    (h2 : v ≤ c₂ ⟨k, hk⟩ (h ⟨k, hk⟩ a)) : QryOK h c₁ c₂ a (k + 1) (some (minWith m v)) := by
  refine ⟨by simp, fun v' hv' => ?_⟩
  simp only [Option.some.injEq] at hv'
  subst hv'
  cases m with
  | none =>
    have hk0 := hq.1.1 rfl
    subst hk0
    refine ⟨fun i hi => ?_, ⟨0, hk⟩, h1⟩
    have : i = ⟨0, hk⟩ := Fin.ext (by show i.val = 0; omega)
    subst this; exact h2
  | some u =>
    obtain ⟨hu2, i₀, hu1⟩ := hq.2 u rfl
    simp only [minWith]
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · exact le_trans (min_le_left _ _) (hu2 i hi)
      · have : i = ⟨k, hk⟩ := Fin.ext hi
        subst this; exact le_trans (min_le_right _ _) h2
    · rcases le_total u v with huv | huv
      · exact ⟨i₀, by rw [min_eq_left huv]; exact hu1⟩
      · exact ⟨⟨k, hk⟩, by rw [min_eq_right huv]; exact h1⟩

lemma pinv_step_tau {α : List (Label P (cmIface E))} {C C' : CMCfg d w E P} {p : P}
    (hI : PInv h α C) (hs : (pcm h P).step C (.tau p) = some C') :
    PInv h (α ++ [.tau p]) C' := by
  have hs0 := hs
  obtain ⟨hpne, -, i₀, o₀, k₀, hact, -⟩ := Impl.step_tau hs
  have hS : procs (α ++ [.tau p]) = insert p (procs α) := procs_concat α _
  have h1 : H₁ (α ++ [.tau p]) = H₁ α := by simp [H₁, canon_concat, canonEnt]
  have h2 : H₂ (α ++ [.tau p]) = H₂ α := by simp [H₂, canon_concat, canonEnt]
  have hresp : ∀ x (r : ℕ), respOf (α ++ [.tau p]) x = some r → ∃ r₁ r₂,
      tau (cmSpec h) (H₁ (α ++ [.tau p])) x = some r₁ ∧
      tau (cmSpec h) (H₂ (α ++ [.tau p])) x = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂ := by
    intro x r hx
    rw [respOf_append_of_not_ret (by simp)] at hx
    exact resp_of_eq hI _ hx
  have hsum := fun (L' : CMLoc E) (g : CMLoc E → ℕ) (hg : g .idle = 0) =>
    sum_update_insert (procs α) C.loc p L' g (fun hn => by rw [hI.out p hn, hg])
  have hother : ∀ q, q ≠ p → ProcOK h (α ++ [.tau p]) C' q := fun q hq =>
    procOK_other hs0 (Ne.symm hq) (hI.proc q)
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpne
  cases o with
  | update a =>
    obtain ⟨k, hk⟩ := (hI.proc p).2.1 a ho
    by_cases hkd : k < d
    · have hact' : (pcm h P).act p (C.loc p) =
          .access (⟨k, hkd⟩, h ⟨k, hkd⟩ a) .inc (fun _ => .upd a (k + 1)) := by
        rw [hk]; simp [pcm, hkd]
      rw [Impl.step_tau_eq_some hpne hact', Option.some.injEq] at hs
      subst hs
      refine ⟨fun q hq => ?_, fun q => ?_, fun i j => ?_, fun i j => ?_, hresp⟩
      · rw [hS, Finset.mem_insert, not_or] at hq
        simp only [Function.update_of_ne hq.1]; exact hI.out q hq.2
      · by_cases hq : q = p
        · subst hq
          refine ⟨fun h0 => by simp [ho] at h0, fun a' ha' => ⟨k + 1, ?_⟩,
            fun a' ha' => by simp [ho] at ha'⟩
          simp only [ho, Option.some.injEq, CMOp.update.injEq] at ha'
          subst ha'; simp
        · exact hother q hq
      · have := hsum (.upd a (k + 1)) (fun l => done h l i j) rfl
        have hd := done_succ (h := h) a k hkd i j
        have hm := hI.mem i j
        have hmemij : @Eq ℕ (Function.update C.mem (⟨k, hkd⟩, h ⟨k, hkd⟩ a)
            ((cell.δ (C.mem (⟨k, hkd⟩, h ⟨k, hkd⟩ a)) .inc).1) (i, j))
            (C.mem (i, j) +
              if (i, j) = ((⟨k, hkd⟩, h ⟨k, hkd⟩ a) : Fin d × Fin w) then 1 else 0) := by
          rw [Function.update_apply]; split_ifs with hij
          · rw [hij]
          · rfl
        rw [hk] at this
        rw [hS, h1]
        dsimp only
        change @Eq ℕ (Function.update C.mem _ _ (i, j)) _
        rw [hmemij]
        omega
      · have := hsum (.upd a (k + 1)) (fun l => todo h l i j) rfl
        rw [hk] at this
        have ht : todo h (.upd a (k + 1)) i j = todo h (.upd a k) i j := rfl
        rw [hS, h1, h2, hI.gap]
        dsimp only
        omega
    · have hact' : (pcm h P).act p (C.loc p) = .ret 0 .idle := by rw [hk]; simp [pcm, hkd]
      rw [hact'] at hact; cases hact
  | query a =>
    obtain ⟨k, m, hk, β, γ, hαβ, hγ, hQ⟩ := (hI.proc p).2.2 a ho
    by_cases hkd : k < d
    · set c : Fin d × Fin w := (⟨k, hkd⟩, h ⟨k, hkd⟩ a) with hc
      have hact' : (pcm h P).act p (C.loc p) =
          .access c .read (fun v => .qry a (k + 1) (some (minWith m v))) := by
        rw [hk]; simp [pcm, hkd, c]
      rw [Impl.step_tau_eq_some hpne hact', Option.some.injEq] at hs
      subst hs
      have hmemeq : Function.update C.mem c (cell.δ (C.mem c) .read).1 = C.mem :=
        Function.update_eq_self _ _
      have h00 : ∀ (g : CMLoc E → ℕ), g .idle = 0 → (∀ a k m, g (.qry a k m) = 0) →
          ∑ q ∈ procs (α ++ [.tau p]),
            g (Function.update C.loc p (.qry a (k + 1) (some (minWith m (C.mem c)))) q) =
          ∑ q ∈ procs α, g (C.loc q) := by
        intro g hg hq
        have := hsum (.qry a (k + 1) (some (minWith m (C.mem c)))) g hg
        rw [hk, hq, hq, add_zero, add_zero] at this
        rw [hS, this]
      refine ⟨fun q hq => ?_, fun q => ?_, fun i j => ?_, fun i j => ?_, hresp⟩
      · rw [hS, Finset.mem_insert, not_or] at hq
        simp only [Function.update_of_ne hq.1]; exact hI.out q hq.2
      · by_cases hq : q = p
        · subst hq
          refine ⟨fun h0 => by simp [ho] at h0, fun a' ha' => by simp [ho] at ha',
            fun a' ha' => ?_⟩
          simp only [ho, Option.some.injEq, CMOp.query.injEq] at ha'
          subst ha'
          refine ⟨k + 1, some (minWith m (C.mem c)), by simp, β, γ ++ [.tau q], by simp [hαβ],
            ?_, ?_⟩
          · simp [hγ]
          · rw [h2]
            refine hQ.step hkd _ ?_ (hI.le_cnt₂ _ _)
            refine le_trans ?_ (hI.cnt₁_le _ _)
            rw [hαβ]
            exact cnt_canon_le_append _ _ _ _ _
        · exact hother q hq
      · dsimp only
        rw [hmemeq, hI.mem, h1, h00 (fun l => done h l i j) rfl (fun _ _ _ => rfl)]
      · dsimp only
        rw [h1, h2, hI.gap, h00 (fun l => todo h l i j) rfl (fun _ _ _ => rfl)]
    · have hact' : (pcm h P).act p (C.loc p) = .ret (m.getD 0) .idle := by
        rw [hk]; simp [pcm, hkd]
      rw [hact'] at hact; cases hact

lemma pinv_step_ret {α : List (Label P (cmIface E))} {C C' : CMCfg d w E P} {p : P} {r : ℕ}
    (hrun : (pcm h P).run α = some C) (hI : PInv h α C)
    (hs : (pcm h P).step C (.ret p r) = some C') : PInv h (α ++ [.ret p r]) C' := by
  have hwf : WellFormed (α ++ [.ret p r]) :=
    Impl.Valid.wellFormed _ ⟨C', by rw [Impl.run_concat, hrun]; exact hs⟩
  obtain ⟨hpne, hpend', hmem', l, hact, hloc'⟩ := Impl.step_ret hs
  have hS : procs (α ++ [.ret p r]) = insert p (procs α) := procs_concat α _
  have hsum := fun (g : CMLoc E → ℕ) (hg : g .idle = 0) =>
    sum_update_insert (procs α) C.loc p l g (fun hn => by rw [hI.out p hn, hg])
  have hother : ∀ q, q ≠ p → ProcOK h (α ++ [.ret p r]) C' q := fun q hq =>
    procOK_other hs (Ne.symm hq) (hI.proc q)
  have hout : ∀ q, q ∉ procs (α ++ [.ret p r]) → C'.loc q = .idle := by
    intro q hq
    rw [hS, Finset.mem_insert, not_or] at hq
    rw [hloc', Function.update_of_ne hq.1]; exact hI.out q hq.2
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hpne
  obtain ⟨-, hnc, hop⟩ := (pcm h P).run_pend_curOp hrun ho
  have hcounts := (pcm h P).run_pend_counts hrun hpne
  have hlin := fun f => isSkelLin_canon (A := cmIface E) f hwf
  have hcomp : Completed (α ++ [.ret p r]) (curOp α p) := by
    rw [completed_append_ret]; exact Or.inr rfl
  cases o with
  | update a =>
    obtain ⟨k, hk⟩ := (hI.proc p).2.1 a ho
    have hkd : ¬ k < d := by
      intro hkd; rw [hk] at hact; simp [pcm, hkd] at hact
    have hact' : (pcm h P).act p (C.loc p) = .ret 0 .idle := by rw [hk]; simp [pcm, hkd]
    rw [hact'] at hact
    obtain ⟨rfl, rfl⟩ : 0 = r ∧ CMLoc.idle = l := by simpa using hact
    have h1 : H₁ (α ++ [.ret p 0]) = H₁ α ++ [(curOp α p, .update a)] := by
      simp [H₁, canon_concat, canonEnt, hop]
    have h2 : H₂ (α ++ [.ret p 0]) = H₂ α := by simp [H₂, canon_concat, canonEnt, hop]
    refine ⟨hout, fun q => ?_, fun i j => ?_, fun i j => ?_, ?_⟩
    · by_cases hq : q = p
      · subst hq
        refine ⟨fun _ => by rw [hloc', Function.update_self], fun a' ha' => by simp [hpend'] at ha',
          fun a' ha' => by simp [hpend'] at ha'⟩
      · exact hother q hq
    · have := hsum (fun l => done h l i j) rfl
      rw [hk] at this
      have hd : done h (.upd a k) i j = if h i a = j then 1 else 0 := by
        have : i.val < k := by omega
        simp [done, this]
      have h0 : done h .idle i j = 0 := rfl
      have hm := hI.mem i j
      rw [hmem', hS, h1, hloc', cnt_concat_update]
      change @Eq ℕ _ _
      omega
    · have := hsum (fun l => todo h l i j) rfl
      rw [hk] at this
      have hd : todo h (.upd a k) i j = if h i a = j then 1 else 0 := rfl
      have h0 : todo h .idle i j = 0 := rfl
      have hg := hI.gap i j
      rw [hS, h1, h2, hloc', cnt_concat_update]
      omega
    · intro y r' hy
      rw [respOf_append_ret] at hy
      split_ifs at hy with hyx
      · simp only [Option.some.injEq] at hy
        subst hy hyx
        obtain ⟨r₂, hr₂⟩ := Option.isSome_iff_exists.1
          ((hlin (fun o : CMOp E => o.isUpdate)).tau_isSome (cmSpec h) hcomp)
        refine ⟨0, r₂, ?_, hr₂, le_rfl, Nat.zero_le _⟩
        exact tau_canon_of_ret (β := α) (γ := []) (cmSpec h) (fun o : CMOp E => !o.isUpdate)
          hwf hop rfl
      · exact resp_of_eq hI _ hy
  | query a =>
    obtain ⟨k, m, hk, β, γ, hαβ, hγ, hQ⟩ := (hI.proc p).2.2 a ho
    have hkd : ¬ k < d := by
      intro hkd; rw [hk] at hact; simp [pcm, hkd] at hact
    have hact' : (pcm h P).act p (C.loc p) = .ret (m.getD 0) .idle := by
      rw [hk]; simp [pcm, hkd]
    rw [hact'] at hact
    obtain ⟨rfl, rfl⟩ : m.getD 0 = r ∧ CMLoc.idle = l := by simpa using hact
    have h1 : H₁ (α ++ [.ret p (m.getD 0)]) = H₁ α := by
      simp [H₁, canon_concat, canonEnt, hop]
    have h2 : H₂ (α ++ [.ret p (m.getD 0)]) = H₂ α ++ [(curOp α p, .query a)] := by
      simp [H₂, canon_concat, canonEnt, hop]
    have h00 : ∀ (g : CMLoc E → ℕ), g .idle = 0 → (∀ a k m, g (.qry a k m) = 0) →
        ∑ q ∈ procs (α ++ [.ret p (m.getD 0)]), g (Function.update C.loc p .idle q) =
        ∑ q ∈ procs α, g (C.loc q) := by
      intro g hg hq
      have := hsum g hg
      rw [hk, hq, hg, add_zero, add_zero] at this
      rw [hS, this]
    refine ⟨hout, fun q => ?_, fun i j => ?_, fun i j => ?_, ?_⟩
    · by_cases hq : q = p
      · subst hq
        refine ⟨fun _ => by rw [hloc', Function.update_self], fun a' ha' => by simp [hpend'] at ha',
          fun a' ha' => by simp [hpend'] at ha'⟩
      · exact hother q hq
    · rw [hmem', hloc', h1, h00 (fun l => done h l i j) rfl (fun _ _ _ => rfl)]
      exact hI.mem i j
    · rw [hloc', h1, h2, cnt_concat_query, h00 (fun l => todo h l i j) rfl (fun _ _ _ => rfl)]
      exact hI.gap i j
    · intro y r' hy
      rw [respOf_append_ret] at hy
      split_ifs at hy with hyx
      · simp only [Option.some.injEq] at hy
        subst hy hyx
        have hlen : (opsOf β p).length = (respsOf α p).length := by
          have := congrArg (fun α => (opsOf α p).length) hαβ
          simp only [opsOf_append, opsOf_cons, hγ] at this
          simp at this
          omega
        have ht₁ : tau (cmSpec h) (H₁ (α ++ [.ret p (m.getD 0)])) (curOp α p) =
            some (⨅ i, cnt h (H₁ β) i (h i a)) := by
          have hsplit : α ++ [.ret p (m.getD 0)] =
              β ++ .inv p (.query a) :: (γ ++ [.ret p (m.getD 0)]) := by simp [hαβ]
          rw [hsplit] at hwf ⊢
          rw [curOp, ← hlen]
          exact tau_canon_of_inv (cmSpec h) (fun o : CMOp E => !o.isUpdate) hwf rfl
        have ht₂ : tau (cmSpec h) (H₂ (α ++ [.ret p (m.getD 0)])) (curOp α p) =
            some (⨅ i, cnt h (H₂ α) i (h i a)) :=
          tau_canon_of_ret (β := α) (γ := []) (cmSpec h) (fun o : CMOp E => o.isUpdate) hwf hop rfl
        obtain ⟨hl, hr⟩ := hQ.sandwich h hkd
        exact ⟨_, _, ht₁, ht₂, hl, hr⟩
      · exact resp_of_eq hI _ hy

variable (h) in
/-- The invariant holds in every reachable configuration. -/
lemma pinv_of_run {α : List (Label P (cmIface E))} {C : CMCfg d w E P}
    (hrun : (pcm h P).run α = some C) : PInv h α C := by
  refine (pcm h P).run_induction (Q := fun α C => PInv h α C) (pinv_init h) ?_ hrun
  intro α C ℓ C' hα hI hs
  cases ℓ with
  | inv p o => exact pinv_step_inv hI hs
  | tau p => exact pinv_step_tau hI hs
  | ret p r => exact pinv_step_ret hα hI hs

end CM

open CM

/-- **Lemma 1** of [Rinberg–Keidar], strong form (the paper's proof). In every execution `α` of
`PCM(c⃗)`, every instance that returns `r` gets, in the sequential CountMin sketch `CM(c⃗)`, a
response `r₁ ≤ r` in the canonical skeleton linearization `H₁` (queries linearized at their
invocation, updates at their response) and a response `r₂ ≥ r` in `H₂` (updates at their
invocation, queries at their response). `H₁` and `H₂` depend only on the skeleton of `α`
(`canon_skel`), not on the hash functions. -/
theorem pcm_sandwich {α : List (Label P (cmIface E))} (hα : (pcm h P).Valid α)
    (x : OpId P) (r : ℕ) (hx : respOf α x = some r) :
    ∃ r₁ r₂, tau (cmSpec h) (canon (fun o : CMOp E => !o.isUpdate) α) x = some r₁ ∧
      tau (cmSpec h) (canon (fun o : CMOp E => o.isUpdate) α) x = some r₂ ∧ r₁ ≤ r ∧ r ≤ r₂ := by
  obtain ⟨C, hC⟩ := hα
  exact (pinv_of_run h hC).resp x r hx

variable (P) in
/-- **Lemma 1** of [Rinberg–Keidar]: `PCM(c⃗)` is an IVL implementation of the CountMin sketch
`CM(c⃗)`. -/
theorem pcm_ivl : (pcm h P).IVLFor (cmSpec h) := fun _ hα =>
  ⟨_, _, isSkelLin_canon _ hα.wellFormed, isSkelLin_canon _ hα.wellFormed, pcm_sandwich h hα⟩

end Lemma1

end Podc.IntermediateValueLin
