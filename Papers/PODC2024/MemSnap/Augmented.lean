import Papers.PODC2024.MemSnap.Defs
import Podc.Computability.Distributed.SharedMemory.MetaConfig

/-!
# Algorithm 2: the meta-configuration tracking augmentation of MemSnap

The augmentation adds two ghost variables, which do not influence the algorithm:

* `x̂_π` (`Ghost.xh`): the value of `X` when `π` invoked its current `observe`/`update`;
* `P` (`Ghost.PP`): the meta-configuration, a set of possibilities (`Poss`: an abstract state
  `(val, snap)` and, for each process, `⊥` or the response of its linearized current operation).

The update rules of `P` are those of Algorithm 2:
* line 1 (`X ← X + 1`, here the write of `X`): every subset `S ⊆ UnLin(p)` of not yet linearized
  updaters may linearize, in any order `α`, just before the click:
  `P ← {p' | ∃ p ∈ P, ∃ S ⊆ UnLin(p), ∃ α ∈ Perm(S), TransitionsOK(p, α · σ, p')}`;
* line 4: `P ← {p' | ∃ p ∈ P, p.σ = ⊥ ∧ TransitionsOK(p, σ, p')}`;
* line 7: `P ← P ∪ {p' | ∃ p ∈ P, p.π = ⊥ ∧ TransitionsOK(p, π, p')}`;
* lines 2, 5, 8 (returns): `P ← Filter(P, π, r)`.

`arun α` runs the augmented algorithm along the execution `α`; its first component is the
configuration of Algorithm 1 (`arun_fst`, `exists_arun`).

**Soundness of the augmentation** (`tracked_of_mem_PP`): every possibility in `P` is realized by
a linearization of the execution so far (`Poss.Tracked`). This is the content of the remark of
Section 6.1 that "the augmentation in Algorithm 2 indeed satisfies the two rules laid out in the
Jayanti et al. paper"; with the tracker theorem `Poss.linearizable_of_tracked` it reduces
linearizability of Algorithm 1 to the invariant `P ≠ ∅`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemSnap

open Cslib.SharedMemory

variable {W : ObjSpec} {K : Type} [DecidableEq K] {v₀ : K → W.State}
variable {P : Type} [DecidableEq P] {σ : P}

/-- Configurations of MemSnap. -/
abbrev Cfg (W : ObjSpec) (K : Type) [DecidableEq K] (v₀ : K → W.State) (P : Type) :=
  Config (checkpointable W K v₀) (base W K v₀) P (Loc W K)

/-- Possibilities for the checkpointable object. -/
abbrev CPoss (W : ObjSpec) (K : Type) [DecidableEq K] (v₀ : K → W.State) (P : Type) :=
  Poss (checkpointable W K v₀) P

/-- Labels of executions of MemSnap. -/
abbrev CLabel (W : ObjSpec) (K : Type) [DecidableEq K] (v₀ : K → W.State) (P : Type) :=
  Label P (checkpointable W K v₀)

/-- The value of the scan counter `X`. -/
abbrev Cfg.X (C : Cfg W K v₀ P) : ℕ := C.mem .X

/-- The pair `B[j]`. -/
abbrev Cfg.B (C : Cfg W K v₀ P) (j : K) : W.State × ℕ := C.mem (.B j)

/-- The word `A[j]`. -/
abbrev Cfg.A (C : Cfg W K v₀ P) (j : K) : W.State := C.mem (.A j)

/-- `pc_π ∈ [6, 8]`: the process executes an `update` (including the `forward` called at line 6). -/
def Loc.IsUpd : Loc W K → Prop
  | .f9 _ (some _) _ => True
  | .f10 _ (some _) _ _ => True
  | .f11 _ (some _) _ _ _ => True
  | .f12 _ (some _) _ _ _ _ => True
  | .u7 _ _ => True
  | .u8 _ => True
  | _ => False

variable (σ) in
/-- Definition 6.1: `UnLin(p)`, the updaters executing an update that is not linearized in `p`. -/
def UnLin (C : Cfg W K v₀ P) (p : CPoss W K v₀ P) : Set P :=
  {π | π ≠ σ ∧ (C.loc π).IsUpd ∧ p.fl π = none}

/-- Definition 6.2: `TransitionsOK(p, l, p')` — `l` is a sequence of distinct active processes not
linearized in `p`, and `p'` results from `p` by applying their operations in the order `l`. -/
def TransOK (C : Cfg W K v₀ P) (p : CPoss W K v₀ P) (l : List P) (p' : CPoss W K v₀ P) : Prop :=
  l.Nodup ∧ (∀ π ∈ l, C.pend π ≠ none ∧ p.fl π = none) ∧ p' = p.linSeq C.pend l

/-- `Filter(P, π, r)`. -/
def filt (PP : Set (CPoss W K v₀ P)) (π : P) (r : CResp W) : Set (CPoss W K v₀ P) :=
  {p' | ∃ p ∈ PP, p.fl π = some r ∧ p' = p.clear π}

variable (W K v₀ P) in
/-- The ghost variables of Algorithm 2. -/
structure Ghost where
  /-- `x̂_π`. -/
  xh : P → ℕ
  /-- The meta-configuration `P`. -/
  PP : Set (CPoss W K v₀ P)

variable (σ) in
/-- The augmentation: how a step `ℓ` from configuration `C` changes the ghost variables. -/
def augStep (C : Cfg W K v₀ P) : CLabel W K v₀ P → Ghost W K v₀ P → Ghost W K v₀ P
  | .inv π o, G => match o with
    | .click => G
    | _ => { G with xh := Function.update G.xh π C.X }
  | .tau π, G => match C.loc π with
    | .c1w _ => { G with PP := {p' | ∃ p ∈ G.PP, ∃ l : List P,
        (∀ π' ∈ l, π' ∈ UnLin σ C p) ∧ TransOK C p (l ++ [π]) p'} }
    | .o4 _ => { G with PP := {p' | ∃ p ∈ G.PP, p.fl π = none ∧ TransOK C p [π] p'} }
    | .u7 _ _ => { G with PP := G.PP ∪ {p' | ∃ p ∈ G.PP, p.fl π = none ∧ TransOK C p [π] p'} }
    | _ => G
  | .ret π r, G => { G with PP := filt G.PP π r }

variable (W K v₀ P) in
/-- Initial ghost: `P = {p₀}`. -/
def ginit : Ghost W K v₀ P := ⟨fun _ => 0, {Poss.init}⟩

variable (σ) in
/-- Running the augmented algorithm from a configuration with ghost. -/
noncomputable def arunFrom :
    Cfg W K v₀ P × Ghost W K v₀ P → List (CLabel W K v₀ P) → Option (Cfg W K v₀ P × Ghost W K v₀ P)
  | c, [] => some c
  | c, ℓ :: α => ((memSnap W K v₀ σ).step c.1 ℓ).bind
      (fun C' => arunFrom (C', augStep σ c.1 ℓ c.2) α)

variable (σ) in
/-- Algorithm 2 run along the execution `α`. -/
noncomputable def arun (α : List (CLabel W K v₀ P)) : Option (Cfg W K v₀ P × Ghost W K v₀ P) :=
  arunFrom σ ((memSnap W K v₀ σ).initCfg, ginit W K v₀ P) α

lemma arunFrom_append (c : Cfg W K v₀ P × Ghost W K v₀ P) (α β : List (CLabel W K v₀ P)) :
    arunFrom σ c (α ++ β) = (arunFrom σ c α).bind (fun c' => arunFrom σ c' β) := by
  induction α generalizing c with
  | nil => simp [arunFrom]
  | cons ℓ α ih =>
    simp only [List.cons_append, arunFrom, ih]
    cases (memSnap W K v₀ σ).step c.1 ℓ <;> simp

lemma arun_concat (α : List (CLabel W K v₀ P)) (ℓ : CLabel W K v₀ P) :
    arun σ (α ++ [ℓ]) = (arun σ α).bind (fun c =>
      ((memSnap W K v₀ σ).step c.1 ℓ).map (fun C' => (C', augStep σ c.1 ℓ c.2))) := by
  simp only [arun, arunFrom_append]
  congr 1; funext c
  simp only [arunFrom]
  cases (memSnap W K v₀ σ).step c.1 ℓ <;> simp

/-- Induction principle for the augmented algorithm. -/
lemma arun_induction {Q : List (CLabel W K v₀ P) → Cfg W K v₀ P → Ghost W K v₀ P → Prop}
    (h0 : Q [] (memSnap W K v₀ σ).initCfg (ginit W K v₀ P))
    (hs : ∀ α C G ℓ C', arun σ α = some (C, G) → Q α C G →
      (memSnap W K v₀ σ).step C ℓ = some C' → Q (α ++ [ℓ]) C' (augStep σ C ℓ G))
    {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}
    (h : arun σ α = some (C, G)) : Q α C G := by
  induction α using List.reverseRecOn generalizing C G with
  | nil => simp only [arun, arunFrom, Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h; exact h0
  | append_singleton α ℓ ih =>
    rw [arun_concat] at h
    cases hα : arun σ α with
    | none => simp [hα] at h
    | some c =>
      obtain ⟨C₀, G₀⟩ := c
      simp only [hα, Option.bind_some] at h
      cases hst : (memSnap W K v₀ σ).step C₀ ℓ with
      | none => simp [hst] at h
      | some C' =>
        simp only [hst, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hs α C₀ G₀ ℓ C' hα (ih hα) hst

/-- The configuration component of Algorithm 2 is the configuration of Algorithm 1. -/
lemma arun_fst {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}
    (h : arun σ α = some (C, G)) : (memSnap W K v₀ σ).run α = some C :=
  arun_induction (Q := fun α C _ => (memSnap W K v₀ σ).run α = some C) rfl
    (fun α C G ℓ C' _ hr hst => by rw [Impl.run_concat, hr]; exact hst) h

/-- Every execution of Algorithm 1 is the projection of a run of Algorithm 2. -/
lemma exists_arun {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P}
    (h : (memSnap W K v₀ σ).run α = some C) : ∃ G, arun σ α = some (C, G) := by
  induction α using List.reverseRecOn generalizing C with
  | nil => exact ⟨ginit W K v₀ P, by simp only [Impl.run_nil, Option.some.injEq] at h; subst h; rfl⟩
  | append_singleton α ℓ ih =>
    rw [Impl.run_concat] at h
    cases hα : (memSnap W K v₀ σ).run α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some] at h
      obtain ⟨G₀, hG⟩ := ih hα
      exact ⟨augStep σ C₀ ℓ G₀, by rw [arun_concat, hG]; simp [h]⟩

/-- **Soundness of the augmentation.** Every possibility in the meta-configuration `P` of
Algorithm 2 corresponds to a linearization of the execution so far. -/
theorem tracked_of_mem_PP {α : List (CLabel W K v₀ P)} {C : Cfg W K v₀ P} {G : Ghost W K v₀ P}
    (h : arun σ α = some (C, G)) : ∀ p ∈ G.PP, Poss.Tracked α p := by
  refine arun_induction (Q := fun α _ G => ∀ p ∈ G.PP, Poss.Tracked α p) ?_ ?_ h
  · intro p hp
    simp only [ginit, Set.mem_singleton_iff] at hp
    subst hp; exact Poss.tracked_init
  · intro α C G ℓ C' hα ih hst
    have hrun := arun_fst hα
    cases ℓ with
    | inv π o =>
      intro p hp
      cases o <;> exact (ih p hp).append_inv _ _
    | tau π =>
      intro p' hp'
      simp only [augStep] at hp'
      split at hp'
      · obtain ⟨p, hp, l, -, hnd, hl, rfl⟩ := hp'
        exact ((ih p hp).linSeq hrun hnd hl).append_tau π
      · obtain ⟨p, hp, -, hnd, hl, rfl⟩ := hp'
        exact ((ih p hp).linSeq hrun hnd hl).append_tau π
      · rcases hp' with hp' | ⟨p, hp, -, hnd, hl, rfl⟩
        · exact (ih p' hp').append_tau π
        · exact ((ih p hp).linSeq hrun hnd hl).append_tau π
      · exact (ih p' hp').append_tau π
    | ret π r =>
      intro p' hp'
      obtain ⟨p, hp, hfl, rfl⟩ := hp'
      exact (ih p hp).append_ret hrun (Impl.step_ret hst).1 hfl

end Podc.MemSnap
