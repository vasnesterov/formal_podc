import Papers.PODC2019.StrongLinSnapshots.SnapDefs
import Cslib.Computability.Distributed.SharedMemory.LinPoints

/-!
# Algorithm 3: the simulation invariant

Linearization points (R-1, R-2 of the paper): an `SLscan` at its last `R.DRead` (line 49); an
`SLupdate_p(x)` at the first linearization point of an `SLscan` that returns a vector with `x`
in entry `p` while the update is pending, or at its own `R.DWrite` (line 45), whichever comes
first. Updates linearized at the same step precede the scan and are ordered by process id
(U-2, U-3).

Invariant (with `S` atomic, the paper's "interpreted value" of `S` is its actual value):

* `g1`: every entry `S[p]` equals the abstract entry `Q[p]`, unless `p` has executed line 43 of
  an update that is not yet linearized; `g1'`: after line 43 of `update(x)`, `S[p] = x`;
  `g2`: a linearized pending update `update(x)` of `p` has `Q[p] = x`.
* `rf`: a scanner `q` that read `s₁` on line 47 sees `R = s₁` as long as its ABA flag is clear.
* `good` (the core of Lemmas 19–22): if a scanner `q` read `s₁` on line 47 and `ℓ = s₁` on line
  48 and no `R.DWrite` happened since its line 47, then for every `p`: `S[p] = ℓ[p]` unless `p`
  is after line 43 of an unlinearized update, and `Q[p] = ℓ[p]` unless `p` has a pending
  unlinearized `update(ℓ[p])`. Hence linearizing those updates at the scan's line 49 makes the
  abstract state equal to `ℓ`, the scan's response.
-/

namespace Podc.StrongLinSnapshots.Snap

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- Configurations. -/
abbrev Cfg (n : ℕ) := Config (snapObj n) (B n) (Fin n) (PC n)
/-- Executions. -/
abbrev Exec (n : ℕ) := List (Label (Fin n) (snapObj n))
/-- Linearizations. -/
abbrev LinT (n : ℕ) := List (OpId (Fin n) × SnapOp n)

/-- The value of the pending `SLupdate`, if any. -/
def updVal : PC n → Option ℕ
  | .u43 x | .u44 x | .u45 x _ => some x
  | _ => none

/-- After line 43 of an `SLupdate`. -/
def PostU : PC n → Prop
  | .u44 _ | .u45 _ _ => True
  | _ => False

instance (pc : PC n) : Decidable (PostU pc) := by cases pc <;> unfold PostU <;> infer_instance

lemma updVal_of_postU {pc : PC n} (h : PostU pc) : ∃ x, updVal pc = some x := by
  cases pc <;> simp_all [PostU, updVal]

/-- The current operation of `p` is linearized. -/
def Lp (α : Exec n) (Lin : LinT n) (p : Fin n) : Prop := curOp α p ∈ Lin.map Prod.fst

instance (α : Exec n) (Lin : LinT n) (p : Fin n) : Decidable (Lp α Lin p) := by
  unfold Lp; infer_instance

/-- The abstract state. -/
abbrev Q (Lin : LinT n) : Vec n := linState (A := snapObj n) Lin

/-- The contents of `S`. -/
abbrev Sv (C : Cfg n) : Vec n := C.mem .S

/-- The contents of `R` (vector and ABA flags). -/
abbrev Rv (C : Cfg n) : Vec n × (Fin n → Bool) := C.mem .R

/-- The key property of a successful scan view `l`. -/
def Good (α : Exec n) (C : Cfg n) (Lin : LinT n) (l : Vec n) : Prop :=
  ∀ p, (Sv C p = l p ∨ (PostU (C.loc p) ∧ ¬ Lp α Lin p)) ∧
    (Q Lin p = l p ∨ (updVal (C.loc p) = some (l p) ∧ ¬ Lp α Lin p))

/-- Status of a process. -/
def St (α : Exec n) (C : Cfg n) (Lin : LinT n) (p : Fin n) : Prop :=
  match C.loc p with
  | .idle => C.pend p = none
  | .u43 x | .u44 x | .u45 x _ => C.pend p ≠ none ∧ opOf α (curOp α p) = some (.update p x)
  | .uRet => C.pend p ≠ none ∧ Lp α Lin p ∧ ∃ x, opOf α (curOp α p) = some (.update p x)
  | .s47 | .s48 _ | .s49 _ _ | .s51 _ => C.pend p ≠ none ∧ ¬ Lp α Lin p ∧
      opOf α (curOp α p) = some .scan
  | .sRet v => C.pend p ≠ none ∧ (snapObj n).respIn (snapObj n).init Lin (curOp α p) = some v

/-- The simulation invariant. -/
structure Inv (α : Exec n) (C : Cfg n) (Lin : LinT n) : Prop where
  lin : IsLinearization α Lin
  st : ∀ p, St α C Lin p
  g1 : ∀ p, Sv C p = Q Lin p ∨ (PostU (C.loc p) ∧ ¬ Lp α Lin p)
  g1' : ∀ p x, updVal (C.loc p) = some x → PostU (C.loc p) → Sv C p = x
  g2 : ∀ p x, updVal (C.loc p) = some x → Lp α Lin p → Q Lin p = x
  rf : ∀ q s1, (C.loc q = .s48 s1 ∨ ∃ l, C.loc q = .s49 s1 l) → (Rv C).2 q = false →
    (Rv C).1 = s1
  good : ∀ q s1 l, C.loc q = .s49 s1 l → (Rv C).2 q = false → s1 = l → Good α C Lin l

/-! ## Auxiliary lemmas -/

/-- A linearized update gets the constant response. -/
lemma respIn_update {α : Exec n} {Lin : LinT n} (hL : IsLinearization α Lin) {y : OpId (Fin n)}
    {i : Fin n} {x : ℕ} (hy : y ∈ Lin.map Prod.fst) (ho : opOf α y = some (.update i x)) :
    (snapObj n).respIn (snapObj n).init Lin y = some (fun _ => 0) := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 ((ObjSpec.respIn_isSome_iff (A := snapObj n) (q := (snapObj n).init)).2 hy)
  obtain ⟨L₁, L₂, o, hs, hr'⟩ := ObjSpec.exists_split_of_respIn_eq_some hr
  have hmem : (y, o) ∈ Lin := by rw [hs]; simp
  have := hL.op_eq _ hmem
  rw [ho] at this
  cases this
  rw [hr, ← hr']

lemma runOps_updates (q : Vec n) (l : Vec n) (rs : List (Fin n)) :
    (snapObj n).runOps q (rs.map fun r => SnapOp.update r (l r)) =
      fun r => if r ∈ rs then l r else q r := by
  induction rs generalizing q with
  | nil => rfl
  | cons u rs ih =>
    rw [List.map_cons, ObjSpec.runOps_cons, ih]
    funext r
    by_cases hr : r ∈ rs
    · simp [hr]
    · by_cases hu : r = u
      · subst hu; simp
      · simp [hr, hu]

@[simp] lemma Lp_tau (α : Exec n) (Lin : LinT n) (q r : Fin n) :
    Lp (α ++ [.tau q]) Lin r ↔ Lp α Lin r := by simp [Lp]

/-- Transfer of the status of a process whose local state and pending operation are unchanged. -/
lemma St.transfer {α α' : Exec n} {C C' : Cfg n} {Lin M : LinT n} {r : Fin n}
    (h : St α C Lin r) (hloc : C'.loc r = C.loc r) (hpend : C'.pend r = C.pend r)
    (hcur : curOp α' r = curOp α r)
    (hop : ∀ o, opOf α (curOp α r) = some o → opOf α' (curOp α r) = some o)
    (hM : updVal (C.loc r) = none → curOp α r ∉ M.map Prod.fst) : St α' C' (Lin ++ M) r := by
  unfold St Lp at h ⊢
  rw [hloc, hpend, hcur]
  cases hc : C.loc r <;> rw [hc] at h hM <;> dsimp only at h ⊢
  · exact h
  all_goals first
    | exact ⟨h.1, hop _ h.2⟩
    | exact ⟨h.1, by rw [List.map_append]; exact List.mem_append_left _ h.2.1,
        let ⟨x, hx⟩ := h.2.2; ⟨x, hop _ hx⟩⟩
    | exact ⟨h.1, by
        rw [List.map_append, List.mem_append, not_or]; exact ⟨h.2.1, hM rfl⟩, hop _ h.2.2⟩
    | exact ⟨h.1, ObjSpec.respIn_append_of_eq_some h.2 _⟩

lemma curOp_fst (α : Exec n) (p : Fin n) : (curOp α p).1 = p := rfl

lemma curOp_inj {α : Exec n} {p q : Fin n} (h : curOp α p = curOp α q) : p = q :=
  congrArg Prod.fst h

/-- The part of `Good` about one process. -/
def Clause (α : Exec n) (C : Cfg n) (Lin : LinT n) (l : Vec n) (p : Fin n) : Prop :=
  (Sv C p = l p ∨ (PostU (C.loc p) ∧ ¬ Lp α Lin p)) ∧
    (Q Lin p = l p ∨ (updVal (C.loc p) = some (l p) ∧ ¬ Lp α Lin p))

lemma good_iff {α : Exec n} {C : Cfg n} {Lin : LinT n} {l : Vec n} :
    Good α C Lin l ↔ ∀ p, Clause α C Lin l p := Iff.rfl

/-- Frame lemma: a step of `p` that changes only `p`'s local state (and pending operation), at
most clears `p`'s ABA flag in `R`, and linearizes nothing. -/
lemma Inv.frame {α α' : Exec n} {C C' : Cfg n} {Lin : LinT n} {p : Fin n}
    (hI : Inv α C Lin) (hlin : IsLinearization α' Lin)
    (hloc : ∀ r, r ≠ p → C'.loc r = C.loc r) (hpend : ∀ r, r ≠ p → C'.pend r = C.pend r)
    (hS : Sv C' = Sv C)
    (hR : (∀ q, (Rv C').2 q = true) ∨
      ((Rv C').1 = (Rv C).1 ∧ ∀ q, q ≠ p → (Rv C').2 q = (Rv C).2 q))
    (hcur : ∀ r, r ≠ p → curOp α' r = curOp α r)
    (hop : ∀ x o, opOf α x = some o → opOf α' x = some o)
    (hst : St α' C' Lin p)
    (hg1 : Sv C p = Q Lin p ∨ (PostU (C'.loc p) ∧ ¬ Lp α' Lin p))
    (hg1' : ∀ x, updVal (C'.loc p) = some x → PostU (C'.loc p) → Sv C p = x)
    (hg2 : ∀ x, updVal (C'.loc p) = some x → Lp α' Lin p → Q Lin p = x)
    (hrf : ∀ s1, (C'.loc p = .s48 s1 ∨ ∃ l, C'.loc p = .s49 s1 l) → (Rv C').2 p = false →
      (Rv C).1 = s1)
    (hgood : ∀ s1 l, C'.loc p = .s49 s1 l → (Rv C').2 p = false → s1 = l → Good α C Lin l)
    (hcl : ∀ l, Clause α C Lin l p → Clause α' C' Lin l p) :
    Inv α' C' Lin := by
  have hLp : ∀ r, r ≠ p → (Lp α' Lin r ↔ Lp α Lin r) := fun r hr => by
    unfold Lp; rw [hcur r hr]
  have hgood' : ∀ l, Good α C Lin l → Good α' C' Lin l := by
    intro l h r
    by_cases hr : r = p
    · subst hr; exact hcl l (h r)
    · have := h r
      show Clause _ _ _ _ _
      unfold Clause at this ⊢; rw [hS, hloc r hr, hLp r hr]; exact this
  refine ⟨hlin, fun r => ?_, fun r => ?_, fun r x => ?_, fun r x => ?_, fun q s1 hq hf => ?_,
    fun q s1 l hq hf he => ?_⟩
  · by_cases hr : r = p
    · subst hr; exact hst
    · have h := hI.st r
      unfold St Lp at h ⊢
      rw [hloc r hr, hpend r hr, hcur r hr]
      split at h <;> first
        | exact h
        | exact ⟨h.1, hop _ _ h.2⟩
        | exact ⟨h.1, h.2.1, let ⟨x, hx⟩ := h.2.2; ⟨x, hop _ _ hx⟩⟩
        | exact ⟨h.1, h.2.1, hop _ _ h.2.2⟩
  · rw [hS]
    by_cases hr : r = p
    · subst hr; exact hg1
    · rw [hloc r hr, hLp r hr]; exact hI.g1 r
  · rw [hS]
    by_cases hr : r = p
    · subst hr; exact hg1' x
    · rw [hloc r hr]; exact hI.g1' r x
  · by_cases hr : r = p
    · subst hr; exact hg2 x
    · rw [hloc r hr, hLp r hr]; exact hI.g2 r x
  · rcases hR with hall | ⟨hR1, hR2⟩
    · rw [hall q] at hf; exact absurd hf (by simp)
    by_cases hqp : q = p
    · subst hqp; rw [hR1]; exact hrf s1 hq hf
    · rw [hloc q hqp] at hq; rw [hR2 q hqp] at hf; rw [hR1]; exact hI.rf q s1 hq hf
  · rcases hR with hall | ⟨hR1, hR2⟩
    · rw [hall q] at hf; exact absurd hf (by simp)
    by_cases hqp : q = p
    · subst hqp; exact hgood' l (hgood s1 l hq hf he)
    · rw [hloc q hqp] at hq; rw [hR2 q hqp] at hf
      exact hgood' l (hI.good q s1 l hq hf he)

end Podc.StrongLinSnapshots.Snap
