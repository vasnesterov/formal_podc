import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Recoverable

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Recoverable/Safety.lean

/-!
# Safety, ranks and ghost invariants in the crash-recovery model

Tools to prove that an algorithm of `Cslib.SharedMemory.Recoverable` solves (recoverable or
wait-free) consensus:

* `AdmB b`: all executions (`b = true`, recoverable consensus) or crash-free ones (`b = false`,
  wait-free consensus); `solves_admB_true_iff`, `solves_admB_false_iff`;
* `Ranked A`: a rank of local states decreasing at every access (loop-free code); with it,
  progress (recoverable wait-freedom) is automatic (`prog_of_rank`);
* `Safe A Good Adm`: agreement and validity for the input vectors satisfying `Good` (e.g. *team
  consensus*: inputs constant on teams); `Safe.solves`;
* `safe_of_ghost`: safety from an invariant with a ghost component that records the decided value
  (outputs of different incarnations of a process are never all present in one configuration, so
  an invariant on configurations alone does not give agreement under crashes).
-/

namespace Cslib.SharedMemory.Recoverable

open Cslib.SharedMemory

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ}

/-- Admissible executions: all of them (`b = true`) or the crash-free ones (`b = false`). -/
def AdmB (b : Bool) (γ : List (Ev n)) : Prop := b = true ∨ CrashFree γ

lemma admB_true : AdmB (n := n) true = fun _ => True := by
  funext γ; simp [AdmB]

lemma admB_false : AdmB (n := n) false = CrashFree := by
  funext γ; simp [AdmB]

lemma solves_admB_true_iff (A : Alg n T) : Solves A (AdmB true) ↔ RecConsensus A := by
  rw [admB_true]; rfl

lemma solves_admB_false_iff (A : Alg n T) : Solves A (AdmB false) ↔ WFConsensus A := by
  rw [admB_false]; rfl

/-- The local states can be ranked so that every access strictly decreases the rank. -/
def Ranked (A : Alg n T) : Prop :=
  ∃ rank : A.L → ℕ, ∀ l i o (κ : (T i).Resp → A.L) r, A.act l = .access i o κ → rank (κ r) < rank l

/-- Agreement and validity for the inputs satisfying `Good`, on the admissible executions. -/
structure Safe (A : Alg n T) (Good : (Fin n → Bool) → Prop) (Adm : List (Ev n) → Prop) :
    Prop where
  agree : ∀ x, Good x → ∀ γ, Adm γ → ∀ v w, Dec (initCfg A x) γ v → Dec (initCfg A x) γ w →
    v = w
  valid : ∀ x, Good x → ∀ γ, Adm γ → ∀ v, Dec (initCfg A x) γ v → ∃ p, x p = v

/-- Safety and a rank give a consensus algorithm. -/
theorem Safe.solves {A : Alg n T} {Adm : List (Ev n) → Prop} (hS : Safe A (fun _ => True) Adm)
    (hR : Ranked A) : Solves A Adm := by
  obtain ⟨rank, hrank⟩ := hR
  exact ⟨fun x => hS.agree x trivial, fun x => hS.valid x trivial,
    fun x e p N _ hinf hN => prog_of_rank rank hrank _ e p N hinf hN⟩

/-- A consensus algorithm is safe. -/
theorem Solves.safe {A : Alg n T} {Adm : List (Ev n) → Prop} (h : Solves A Adm)
    (Good : (Fin n → Bool) → Prop) : Safe A Good Adm :=
  ⟨fun x _ => h.agree x, fun x _ => h.valid x⟩

/-- Decisions in an execution extended by one event. -/
lemma Dec.concat_cases {A : Alg n T} {C : Cfg A} {γ : List (Ev n)} {e : Ev n} {v : Bool}
    (h : Dec C (γ ++ [e]) v) : Dec C γ v ∨ ∃ p, (run C (γ ++ [e])).Out p v := by
  rcases Dec.append_cases h with h | ⟨k, hk, p, hp⟩
  · exact Or.inl h
  · simp at hk
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
    · left; exact ⟨γ.length, le_rfl, p, by simpa using hp⟩
    · right; exact ⟨p, by rw [run_append]; simpa using hp⟩

/-- **Safety from a ghost invariant.** `Inv x C g` relates configurations to ghost values `g`
whose component `dec g` is the decided value (if any). Every step (and every crash, if crashes
are admissible) preserves the invariant for some new ghost value without changing a decided
value; output states output the decided value; decided values are inputs. -/
theorem safe_of_ghost {A : Alg n T} {G : Type} (b : Bool) (Good : (Fin n → Bool) → Prop)
    (Inv : (Fin n → Bool) → Cfg A → G → Prop) (dec : G → Option Bool)
    (hinit : ∀ x, Good x → ∃ g, Inv x (initCfg A x) g)
    (hstep : ∀ x, Good x → ∀ C g p, Inv x C g →
      ∃ g', Inv x (C.stepP p) g' ∧ ∀ d, dec g = some d → dec g' = some d)
    (hcrash : b = true → ∀ x, Good x → ∀ C g p, Inv x C g →
      ∃ g', Inv x (C.next (.crash p)) g' ∧ ∀ d, dec g = some d → dec g' = some d)
    (hout : ∀ x C g p w, Inv x C g → C.Out p w → dec g = some w)
    (hvalid : ∀ x, Good x → ∀ C g d, Inv x C g → dec g = some d → ∃ q, x q = d) :
    Safe A Good (AdmB b) := by
  have key : ∀ x, Good x → ∀ γ : List (Ev n), AdmB b γ →
      ∃ g, Inv x (run (initCfg A x) γ) g ∧ ∀ v, Dec (initCfg A x) γ v → dec g = some v := by
    intro x hx γ
    induction γ using List.reverseRecOn with
    | nil =>
      intro _
      obtain ⟨g, hg⟩ := hinit x hx
      refine ⟨g, by simpa using hg, fun v hv => ?_⟩
      obtain ⟨k, hk, p, hp⟩ := hv
      simp at hk; subst hk
      exact hout x _ g p v hg (by simpa using hp)
    | append_singleton γ e ih =>
      intro hadm
      have hadm' : AdmB b γ := by
        rcases hadm with h | h
        · exact Or.inl h
        · exact Or.inr h.of_append_left
      obtain ⟨g, hg, hdec⟩ := ih hadm'
      obtain ⟨g', hg', hmono⟩ : ∃ g', Inv x (run (initCfg A x) (γ ++ [e])) g' ∧
          ∀ d, dec g = some d → dec g' = some d := by
        rw [run_concat]
        rcases e with p | p
        · exact hstep x hx _ g p hg
        · have hb : b = true := by
            rcases hadm with h | h
            · exact h
            · exact absurd (by simp) (h p)
          exact hcrash hb x hx _ g p hg
      refine ⟨g', hg', fun v hv => ?_⟩
      rcases Dec.concat_cases hv with h | ⟨p, hp⟩
      · exact hmono v (hdec v h)
      · exact hout x _ g' p v hg' hp
  refine ⟨fun x hx γ hγ v w hv hw => ?_, fun x hx γ hγ v hv => ?_⟩
  · obtain ⟨g, -, hd⟩ := key x hx γ hγ
    have h1 := hd v hv
    rw [hd w hw] at h1
    exact (Option.some.inj h1).symm
  · obtain ⟨g, hg, hd⟩ := key x hx γ hγ
    exact hvalid x hx _ g v hg (hd v hv)

end Cslib.SharedMemory.Recoverable
