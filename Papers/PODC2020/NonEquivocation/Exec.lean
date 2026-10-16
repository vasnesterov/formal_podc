import Papers.PODC2020.NonEquivocation.Model

/-!
# Full-information executions with imitating faulty processes ("worlds")

To construct message maps for lower bounds we use a family of executions indexed by *worlds*
`W` (`ExecSys`): in world `w`, process `y` has input `input w y`; towards everybody it does not
omit to, `y` relays truthfully what it received **in world `nb w y`** (a non-faulty `y` has
`nb w y = w`); `om w r y x` says that in world `w` the round-`r` messages of `y` to `x` are omitted.

* `ExecSys.σ_cons_cons`: the defining recursion.
* `ExecSys.wne_of`: if faulty processes are the only ones that imitate another world or omit, the
  message map of every world lies in the weak non-equivocation fault model (an imitating process
  reports the *same* value to everybody it does not omit: it never equivocates).
* `ExecSys.σ_eq_of_rel`: an FLM-style indistinguishability principle — if a relation between pairs of
  worlds (seen by a process `x`) is closed under "who `x` listens to", then `x` has the same view in
  related worlds.

-- CSLib candidate (together with `Model.lean`): a reusable model of the PSL message-map framework.
-/

namespace NonEquivocation

variable {W P V : Type*}

/-- A system of full-information executions indexed by worlds `W`. -/
structure ExecSys (W P V : Type*) where
  /-- Private values. -/
  input : W → P → Option V
  /-- `nb w y`: the world whose (truthful) behaviour `y` exhibits in world `w`. -/
  nb : W → P → W
  /-- `om w r y x`: in world `w`, `y` omits its round-`r` messages to `x`. -/
  om : W → ℕ → P → P → Prop

namespace ExecSys

variable [OmitVal V] (E : ExecSys W P V)

open Classical

/-- The message map of world `w`. -/
noncomputable def σ : W → MsgMap P V
  | _, [] => none
  | w, [y] => E.input w y
  | w, x :: y :: l => if E.om w (l.length + 1) y x then none else some (rep (σ (E.nb w y) (y :: l)))

@[simp] lemma σ_nil (w : W) : E.σ w [] = none := by simp [σ]

@[simp] lemma σ_single (w : W) (y : P) : E.σ w [y] = E.input w y := by simp [σ]

lemma σ_cons_cons (w : W) (x y : P) (l : List P) :
    E.σ w (x :: y :: l) =
      if E.om w (l.length + 1) y x then none else some (rep (E.σ (E.nb w y) (y :: l))) := by
  rw [σ]

/-- Faulty processes are the only ones that imitate other worlds or omit. -/
def Honest (w : W) (F : Finset P) : Prop :=
  ∀ y, y ∉ F → E.nb w y = w ∧ ∀ r x, ¬ E.om w r y x

lemma nonFaulty_of {w : W} {F : Finset P} (h : E.Honest w F) (k : ℕ) (S : Finset P) :
    NonFaulty k S F (E.σ w) := by
  intro q _ hq p _ l _ _ _
  simp only [σ_cons_cons, (h q hq).2, (h q hq).1, ↓reduceIte]

lemma weakNE (w : W) (k : ℕ) (S : Finset P) : WeakNE k S (E.σ w) := by
  intro p _ r _ r' _ l _ _ _ _ h₁ h₂
  rw [σ_cons_cons] at h₁ h₂ ⊢
  rw [σ_cons_cons]
  split_ifs at h₁ h₂ ⊢ <;> simp_all

lemma wne_of [Fintype P] {w : W} {F : Finset P} (h : E.Honest w F) (k : ℕ) :
    wne k F (E.σ w) :=
  ⟨E.nonFaulty_of h k _, E.weakNE w k _⟩

/-- Closure condition for an indistinguishability relation `R w w' x` ("`x` cannot distinguish `w`
from `w'`"): same input, same omissions towards `x`, and every process `x` listens to either imitates
the same world in both, or is itself related. -/
def IsBisim (R : W → W → P → Prop) : Prop :=
  ∀ w w' x, R w w' x → E.input w x = E.input w' x ∧
    ∀ y r, (E.om w r y x ↔ E.om w' r y x) ∧
      (¬ E.om w r y x → E.nb w y = E.nb w' y ∨ R (E.nb w y) (E.nb w' y) y)

theorem σ_eq_of_rel {R : W → W → P → Prop} (hR : E.IsBisim R) :
    ∀ (l : List P) (x : P) (w w' : W), R w w' x → E.σ w (x :: l) = E.σ w' (x :: l) := by
  intro l
  induction l with
  | nil => intro x w w' h; simpa using (hR w w' x h).1
  | cons y l ih =>
    intro x w w' h
    obtain ⟨-, hy⟩ := hR w w' x h
    obtain ⟨hom, hnb⟩ := hy y (l.length + 1)
    rw [σ_cons_cons, σ_cons_cons]
    by_cases ho : E.om w (l.length + 1) y x
    · simp only [ho, hom.1 ho, ↓reduceIte]
    · have ho' : ¬ E.om w' (l.length + 1) y x := fun h' => ho (hom.2 h')
      simp only [ho, ho', ↓reduceIte]
      rcases hnb ho with he | hr
      · rw [he]
      · rw [ih y _ _ hr]

theorem view_eq_of_rel {R : W → W → P → Prop} (hR : E.IsBisim R) {w w' : W} {x : P}
    (h : R w w' x) (k : ℕ) : view k (E.σ w) x = view k (E.σ w') x := by
  funext l
  simp only [view, E.σ_eq_of_rel hR l x w w' h]

end ExecSys

end NonEquivocation
