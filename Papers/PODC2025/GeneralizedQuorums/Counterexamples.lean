import Papers.PODC2025.GeneralizedQuorums.Main
import Papers.PODC2025.GeneralizedQuorums.Examples

/-!
# Boundary cases

* `theorem_2_false_of_chain`: Theorem 2 needs a *non-trivial* object. Lattice agreement over a
  chain (e.g. `ℕ`) is solved without any communication by returning one's own proposal
  (`echoAlg`), which is safe and wait-free everywhere; yet the fail-prone system "either of two
  processes may crash" admits no generalized quorum system. The paper's proof silently assumes two
  incomparable elements (and two distinct values for registers, snapshots and consensus; the same
  algorithm shows that these hypotheses are needed too).
* `Uf_not_unique`: `U_f` depends on the quorum system, not only on `F`, so "U_f is the largest set
  of processes for which termination can be guaranteed" (§4, after Theorem 2) has to be read
  relative to the quorum system constructed in the proof.
-/

namespace Podc.GeneralizedQuorums

open Cslib.ChannelFailures Cslib.SharedMemory

/-! ### Trivial value domains -/

/-- Return one's own proposal immediately. -/
def echoAlg (P V : Type) : Algorithm P (laObj V) Unit Unit where
  init _ := ()
  handle _ i _ := match i with
    | .invoke x => ((), [], some x)
    | _ => ((), [], none)

variable {P : Type} [DecidableEq P]

omit [DecidableEq P] in
lemma respOut_none (p : P) {A : ObjSpec} (o : Option A.Op) : respOut p o none = [] := by
  cases o <;> rfl

lemma echo_step_labels {V : Type} (C : Config P (laObj V) Unit Unit) (e : Event P (laObj V)) :
    ∀ p y, Label.ret p y ∈ ((echoAlg P V).step C e).2 →
      Label.inv p y ∈ ((echoAlg P V).step C e).2 := by
  intro p y h
  cases e with
  | invoke q x =>
    simp only [Algorithm.step] at h ⊢
    split at h
    · simp at h
    · rename_i hp
      simp [Config.apply, echoAlg, respOut] at h ⊢
      exact h
  | tick q c =>
    simp only [Algorithm.step, Config.apply, echoAlg] at h
    rw [respOut_none] at h; simp at h
  | deliver a q =>
    simp only [Algorithm.step] at h
    split at h
    · simp at h
    · simp only [Config.apply, echoAlg] at h
      rw [respOut_none] at h; simp at h

lemma echo_hist {V : Type} (C : Config P (laObj V) Unit Unit) (E : List (Event P (laObj V))) :
    ∀ p y, Label.ret p y ∈ (echoAlg P V).hist C E → Label.inv p y ∈ (echoAlg P V).hist C E := by
  induction E generalizing C with
  | nil => simp
  | cons e E ih =>
    intro p y h
    simp only [Algorithm.hist_cons, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (echo_step_labels C e p y h)
    · exact Or.inr (ih _ p y h)

/-- Over a chain, returning one's own proposal satisfies lattice agreement. -/
theorem echoAlg_safe (V : Type) [LinearOrder V] : (echoAlg P V).Satisfies (laSafe V) := by
  intro E _
  refine ⟨fun p q y y' _ _ => le_total y y', fun p y h => ⟨y, echo_hist _ E p y h, le_rfl⟩,
    fun p y h z hz => hz p y (echo_hist _ E p y h)⟩

/-- Returning one's own proposal is wait-free under every failure pattern. -/
theorem echoAlg_waitFree (V : Type) (f : FailurePattern P) (T : Set P) :
    (echoAlg P V).WaitFree f T := by
  intro ev _ p _ t₀ o he hpend
  refine ⟨t₀, le_rfl, o, ?_⟩
  simp only [Algorithm.labAt, he, Algorithm.step, hpend]
  simp [Config.apply, echoAlg, respOut]

/-- The fail-prone system on two processes where either one may crash. -/
def fOne (b : Bool) : FailurePattern Bool := ⟨{b}, ∅⟩

lemma no_GQS_fOne : ¬ ∃ R W : Set (Set Bool), IsGQS (Set.range fOne) R W := by
  rintro ⟨R, W, hQ⟩
  obtain ⟨w₁, -, r₁, hr₁, -, -, hr₁c, -⟩ := hQ.availability (fOne true) ⟨true, rfl⟩
  obtain ⟨w₂, hw₂, r₂, -, -, hw₂c, -, -⟩ := hQ.availability (fOne false) ⟨false, rfl⟩
  obtain ⟨x, hxr, hxw⟩ := hQ.consistency r₁ hr₁ w₂ hw₂
  have h1 := hr₁c x hxr
  have h2 := hw₂c x hxw
  simp [fOne] at h1 h2
  cases x <;> simp_all

/-- **Theorem 2 fails for lattice agreement over a chain** (the paper assumes, in its proof, two
incomparable elements): `echoAlg` over `ℕ` is safe and `(F, τ)`-wait-free with `τ(f)` the
(non-empty) set of correct processes, but `F = {either process crashes}` has no generalized
quorum system. -/
theorem theorem_2_false_of_chain :
    (echoAlg Bool ℕ).Satisfies (laSafe ℕ) ∧
      (echoAlg Bool ℕ).WaitFreeOn (Set.range fOne) (fun f => (f.procs)ᶜ) ∧
      (∀ f ∈ Set.range fOne, ((f.procs)ᶜ : Set Bool).Nonempty) ∧
      ¬ ∃ R W : Set (Set Bool), IsGQS (Set.range fOne) R W := by
  refine ⟨echoAlg_safe ℕ, fun f _ => echoAlg_waitFree ℕ f _, ?_, no_GQS_fOne⟩
  rintro f ⟨b, rfl⟩
  exact ⟨!b, by cases b <;> simp [fOne]⟩

/-! ### `U_f` depends on the quorum system -/

/-- Two processes; only the channel `0 → 1` is reliable. -/
def fDir : FailurePattern (Fin 2) := ⟨∅, {(1, 0)}⟩

lemma fDir_reach01 : fDir.Reach 0 1 := reach_of_edge ⟨by simp [fDir], by simp [fDir], by simp [fDir]⟩

lemma fDir_not_reach10 : ¬ fDir.Reach 1 0 := by
  refine not_reach_of_closed (S := {1}) ?_ rfl (by decide)
  intro a b he ha
  simp only [Set.mem_singleton_iff] at ha ⊢
  subst ha
  fin_cases b
  · exact absurd he.2.2 (by simp [fDir])
  · rfl

/-- **`U_f` is not determined by `F`.** For `F = {fDir}` both `({{0}}, {{0}})` and
`({{0, 1}}, {{1}})` are generalized quorum systems, with `U_f = {0}` and `U_f = {1}`
respectively. -/
theorem Uf_not_unique :
    IsGQS {fDir} {{0}} {{0}} ∧ IsGQS {fDir} {{0, 1}} {{1}} ∧
      0 ∈ Uf {{0}} {{0}} fDir ∧ 1 ∉ Uf {{0}} {{0}} fDir ∧
      1 ∈ Uf {{0, 1}} {{1}} fDir ∧ 0 ∉ Uf {{0, 1}} {{1}} fDir := by
  have r00 : fDir.Reach 0 0 := reach_refl (by simp [fDir])
  have r11 : fDir.Reach 1 1 := reach_refl (by simp [fDir])
  have hc : ∀ x : Fin 2, x ∉ fDir.procs := fun x => by simp [fDir]
  have hav0 : Available fDir {0} := by rintro u rfl v rfl; exact r00
  have hre0 : ReachableFrom fDir {0} {0} :=
    ⟨fun w _ => hc w, fun r _ => hc r, by rintro r rfl w rfl; exact r00⟩
  have hav1 : Available fDir {1} := by rintro u rfl v rfl; exact r11
  have hre1 : ReachableFrom fDir {1} {0, 1} := ⟨fun w _ => hc w, fun r _ => hc r, by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro r (rfl | rfl) w rfl
    · exact fDir_reach01
    · exact r11⟩
  have hU0 : U {{0}} {{0}} fDir = {0} := by
    ext x; simp only [U, Set.mem_sUnion, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨rfl, -⟩, hx⟩; exact hx
    · rintro rfl; exact ⟨{0}, ⟨rfl, hav0, {0}, rfl, hre0⟩, rfl⟩
  have hU1 : U {{0, 1}} {{1}} fDir = {1} := by
    ext x; simp only [U, Set.mem_sUnion, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, ⟨rfl, -⟩, hx⟩; exact hx
    · rintro rfl; exact ⟨{1}, ⟨rfl, hav1, {0, 1}, rfl, hre1⟩, rfl⟩
  refine ⟨⟨by rintro r rfl w rfl; exact ⟨0, by simp⟩, by
      rintro f rfl; exact ⟨{0}, rfl, {0}, rfl, hav0, hre0⟩⟩,
    ⟨by rintro r rfl w rfl; exact ⟨1, by simp⟩, by
      rintro f rfl; exact ⟨{1}, rfl, {0, 1}, rfl, hav1, hre1⟩⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨0, by rw [hU0]; rfl, r00, r00⟩
  · rintro ⟨u, hu, -, h⟩
    rw [hU0] at hu; subst hu; exact fDir_not_reach10 h
  · exact ⟨1, by rw [hU1]; rfl, r11, r11⟩
  · rintro ⟨u, hu, h, -⟩
    rw [hU1] at hu; subst hu; exact fDir_not_reach10 h

end Podc.GeneralizedQuorums
