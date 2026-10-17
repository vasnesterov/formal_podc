import Papers.PODC2020.AsyncApproxBCDirected.Main
import Papers.PODC2020.AsyncApproxBCDirected.Literal

/-!
# Non-vacuity of the round model

* `RoundExec.faultFree G f x` — for every graph, every `f` and all state values `x`, the
  fault-free round in which every message has already been delivered at time `0` satisfies all
  hypotheses of `RoundExec`.
* `Exec.faultFree` — under 3-reach (`n ≥ 2`), for all inputs there is a whole fault-free
  execution `Exec` of the algorithm (outputs chained over the rounds).
* `K4`: the complete graph on 4 nodes with `f = 1` satisfies 3-reach, so `theorem4_sufficiency`
  and the counterexample `never_verifyLit` apply to an actual execution.
-/

open Finset

set_option linter.unusedSectionVars false

namespace AsyncApproxBCDirected

open Cslib.ApproxConsensus Cslib.ApproxConsensus.Async

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} {f : ℕ}

/-- Prefixes of redundant paths are redundant. -/
theorem IsRedundant.of_append_singleton {p : List V} {v : V} (h : IsRedundant G (p ++ [v]))
    (hp : p ≠ []) : IsRedundant G p := by
  obtain ⟨p₁, p₂, a, q, b, h₁, h₂, he⟩ := h
  -- a simple path minus its last node is simple
  have pre : ∀ {l : List V} {x y z : V}, IsSimplePath G (l ++ [z]) x y → l ≠ [] →
      ∃ w, IsSimplePath G l x w := by
    intro l x y z hl hne
    obtain ⟨⟨hh, -, hc⟩, hn⟩ := hl
    refine ⟨l.getLast hne, ⟨⟨?_, List.getLast?_eq_some_getLast hne, hc.left_of_append⟩,
      (List.nodup_append.mp hn).1⟩⟩
    rw [List.head?_append] at hh
    cases l with
    | nil => exact absurd rfl hne
    | cons c l => simpa using hh
  rcases List.eq_nil_or_concat p₂.tail with ht | ⟨t₀, w, ht⟩
  · rw [ht, List.append_nil] at he
    subst he
    obtain ⟨w, hw⟩ := pre h₁ hp
    exact hw.isRedundant
  · rw [List.concat_eq_append] at ht
    rw [ht, ← List.append_assoc] at he
    obtain ⟨hp', -⟩ := List.append_inj' he.symm rfl
    have h₂' : p₂ = q :: (t₀ ++ [w]) := by rw [← ht, ← h₂.eq_cons]
    rw [h₂'] at h₂
    obtain ⟨w', hw'⟩ := pre (l := q :: t₀) h₂ (List.cons_ne_nil _ _)
    exact ⟨p₁, q :: t₀, a, q, w', h₁, hw', by simpa using hp'.symm⟩

/-- The value carried by a path in a fault-free round: the input of its initial node. -/
def pathVal (x : V → ℝ) : List V → ℝ
  | [] => 0
  | s :: _ => x s

theorem pathVal_append {x : V → ℝ} {p : List V} (hp : p ≠ []) (l : List V) :
    pathVal x (p ++ l) = pathVal x p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons s _ => rfl

/-- The redundant paths ending at `v`. -/
noncomputable def redPaths (G : Digraph V) (v : V) : Finset (List V) :=
  ((List.finite_length_le V (2 * Fintype.card V)).subset
    (t := {p | IsRedundant G p ∧ p.getLast? = some v}) fun _ hp => hp.1.length_le).toFinset

theorem mem_redPaths {v : V} {p : List V} :
    p ∈ redPaths G v ↔ IsRedundant G p ∧ p.getLast? = some v := by
  simp [redPaths]

/-- The `COMPLETE` entries of the fault-free round (all delivered at time `0`). -/
noncomputable def ffCR (G : Digraph V) (f : ℕ) (M : V → ℕ → Finset (Msg V)) (v : V) :
    Finset (V × List V × Finset (Msg V) × Finset V) :=
  (((Set.finite_univ (α := V)).prod ((finite_simplePaths (fun p : List V => p.Nodup)
    fun _ h => h).prod (Set.finite_univ (α := Finset V)))).image
      (fun e : V × List V × Finset V => (e.1, e.2.1, mcMsg G M e.1 e.2.2, e.2.2))
    |>.subset (t := {e | ∃ c p F', IsSimplePath G p c v ∧ c ∉ F' ∧ F'.card ≤ f ∧
      e = (c, p, mcMsg G M c F', F')}) (by
      rintro _ ⟨c, p, F', hp, -, -, rfl⟩
      exact ⟨(c, p, F'), ⟨Set.mem_univ _, hp.2, Set.mem_univ _⟩, rfl⟩)).toFinset

namespace RoundExec

/-- The value messages of the fault-free round. -/
noncomputable def ffM (G : Digraph V) (x : V → ℝ) (v : V) (_ : ℕ) : Finset (Msg V) :=
  (redPaths G v).image fun p => (pathVal x p, p)

theorem mem_ffM {x : V → ℝ} {v : V} {t : ℕ} {m : Msg V} :
    m ∈ ffM G x v t ↔ IsRedundant G m.2 ∧ m.2.getLast? = some v ∧ m.1 = pathVal x m.2 := by
  simp only [ffM, mem_image, mem_redPaths]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨m.2, ⟨h1, h2⟩, Prod.ext h3.symm rfl⟩

theorem ff_mcAt {x : V → ℝ} {c : V} {F' : Finset V} :
    MCAt G (ffM G x) c F' 0 := by
  refine ⟨fun m hm m' hm' hh => ?_, fun p hp hpA hpl => ⟨pathVal x p, ?_⟩⟩
  · rw [(mem_ffM.mp (mem_excl.mp hm).1).2.2, (mem_ffM.mp (mem_excl.mp hm').1).2.2]
    rcases hm2 : m.2 with _ | ⟨s, l⟩ <;> rcases hm2' : m'.2 with _ | ⟨s', l'⟩ <;>
      rw [hm2, hm2'] at hh <;> simp_all [pathVal]
  · exact mem_excl.mpr ⟨mem_ffM.mpr ⟨hp, hpl, rfl⟩, hpA⟩

theorem ff_sent {x : V → ℝ} {c : V} {F' : Finset V} (hc : c ∉ F') (hF' : F'.card ≤ f) :
    Sent G f (ffM G x) c F' := ⟨hc, hF', 0, ff_mcAt⟩

theorem ff_mcTime {x : V → ℝ} {c : V} {F' : Finset V} : mcTime G (ffM G x) c F' = 0 := by
  classical
  have hex : ∃ t, MCAt G (ffM G x) c F' t := ⟨0, ff_mcAt⟩
  simp only [mcTime, hex, dite_true]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' hex ff_mcAt)

/-- **Non-vacuity**: the fault-free round with all messages delivered satisfies every hypothesis
of `RoundExec`, for every graph, every `f` and all state values. -/
noncomputable def faultFree (G : Digraph V) (f : ℕ) (x : V → ℝ) : RoundExec G f where
  F := ∅
  card_F := by simp
  x := x
  M := ffM G x
  acc := pathVal x
  CR v _ := ffCR G f (ffM G x) v
  idx _ F' := (Fintype.equivFin (Finset V) F' : ℕ)
  M_mono _ _ _ _ := le_rfl
  M_last v _ t m hm := (mem_ffM.mp hm).2.1
  M_first v _ t y p hm := mem_ffM.mpr ⟨(mem_ffM.mp hm).1, (mem_ffM.mp hm).2.1, rfl⟩
  M_honest v _ t y p hm _ := (mem_ffM.mp hm).2.2
  acc_self s _ := rfl
  acc_snoc p q w hp _ := pathVal_append (by rintro rfl; simp at hp) [w]
  M_src v _ t y p q hm hp _ := by
    have hne : p ≠ [] := by rintro rfl; simp at hp
    exact ⟨0, mem_ffM.mpr ⟨(mem_ffM.mp hm).1.of_append_singleton hne, hp, rfl⟩⟩
  M_live_self s _ := ⟨0, mem_ffM.mpr ⟨isSimplePath_singleton.isRedundant, by simp, rfl⟩⟩
  M_live v _ p q hp _ _ _ hred _ := by
    have hne : p ≠ [] := by rintro rfl; simp at hp
    exact ⟨0, mem_ffM.mpr ⟨hred, by simp, (pathVal_append hne _).symm⟩⟩
  CR_mono _ _ _ _ := le_rfl
  CR_honest v _ t c p Mc F' hm _ := by
    simp only [ffCR, Set.Finite.mem_toFinset] at hm
    obtain ⟨c', p', F'', hp, hc, hF, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    exact ⟨hp.1.1, ff_sent hc hF, rfl, by rw [ff_mcTime]; exact Nat.zero_le _⟩
  CR_fifo v _ t c p Mc F' F'' hm _ hs _ := by
    simp only [ffCR, Set.Finite.mem_toFinset] at hm ⊢
    obtain ⟨c', p', F''', hp, -, -, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, -, -⟩ := he
    exact ⟨c, p, F'', hp, hs.1, hs.2.1, rfl⟩
  CR_live v _ c p F' hs hp _ := by
    refine ⟨0, ?_⟩
    simp only [ffCR, Set.Finite.mem_toFinset]
    exact ⟨c, p, F', hp, hs.1, hs.2.1, rfl⟩
  idx_inj _ _ F₁ F₂ _ _ h := (Fintype.equivFin (Finset V)).injective (Fin.ext h)

end RoundExec

/-- The fault-free states of round `r` (outputs chosen among the possible ones). -/
noncomputable def ffStates (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) (x₀ : V → ℝ) :
    ℕ → V → ℝ
  | 0 => x₀
  | r + 1 => fun v => Classical.choose
      ((RoundExec.faultFree G f (ffStates hG hn x₀ r)).output_exists hG hn (v := v)
        (by simp [RoundExec.faultFree]))

/-- **Non-vacuity of `Exec`**: under 3-reach with `n ≥ 2`, for all inputs there is a (fault-free)
execution of the algorithm. -/
noncomputable def Exec.faultFree (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V)
    (x₀ : V → ℝ) : Exec G f where
  R r := RoundExec.faultFree G f (ffStates hG hn x₀ r)
  F := ∅
  F_eq _ := rfl
  next r v _ := Classical.choose_spec
    ((RoundExec.faultFree G f (ffStates hG hn x₀ r)).output_exists hG hn (v := v)
      (by simp [RoundExec.faultFree]))

theorem Exec.faultFree_x0 (hG : ThreeReach G f) (hn : 2 ≤ Fintype.card V) (x₀ : V → ℝ) :
    (Exec.faultFree hG hn x₀).x 0 = x₀ := rfl

/-- The complete graph on 4 nodes tolerates `f = 1`. -/
theorem threeReach_K4 : ThreeReach (⊤ : Digraph (Fin 4)) 1 :=
  threeReach_top_iff.mpr (Or.inr (by simp))

/-- The counterexample to the literal algorithm applies to an actual execution: in the fault-free
round on `K₄` with `f = 1`, no node ever passes the literal `Verify`. -/
example (x : Fin 4 → ℝ) (v : Fin 4) (Fv : Finset (Fin 4)) (hvF : v ∉ Fv) (t : ℕ) :
    ¬ (RoundExec.faultFree ⊤ 1 x).VerifyLit v Fv t :=
  RoundExec.never_verifyLit _ threeReach_K4 (by simp) le_rfl (by simp [RoundExec.faultFree]) Fv
    hvF t

end AsyncApproxBCDirected
