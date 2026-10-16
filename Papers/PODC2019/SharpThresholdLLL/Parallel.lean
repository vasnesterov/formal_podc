import Papers.PODC2019.SharpThresholdLLL.Process

/-!
# Parallel execution of the process (the combinatorial core of Corollaries 1.2 and 1.4)

The distributed algorithms of Corollaries 1.2 and 1.4 run the sequential process in parallel.
In each phase, several *groups* act at the same time. Each group fixes its own variables one
after another (a sequential run from the common state at the start of the phase). The groups'
*regions* (sets of events) are pairwise disjoint, and every variable of a group affects only
events in the group's region. For Corollary 1.2, a group is a single variable (edge) of the
current edge-colour class. For Corollary 1.4, a group is a node `v` of the current colour of a
2-hop colouring, with region `N[v]`.

The paper's argument is: "Since Theorem 1.3 works for any order and due to the local nature of
the fixing and bookkeeping ...". We make it precise.

* `condProb_congr`: `Pr[E_t | ·]` depends only on the variables of `E_t`.
* `Run.transport`: a run can be replayed from any state that agrees with its start state on
  what the run reads.
* `phase_run`: the merged result of a parallel phase is reached by a sequential run, the
  concatenation of the groups' runs. Hence every execution of a valid schedule is an execution
  of the sequential process, and Theorem 1.3 applies (`schedule_correct`).
* `corollary_1_2_core` and `corollary_1_4_core`: the phase schedules built from a conflict-free
  colouring of the variables (Corollary 1.2) or from a 2-hop colouring of the dependency graph
  (Corollary 1.4) can always be executed. Every execution fixes all variables and avoids all bad
  events, and the number of phases is the number of colours.

The round complexity bounds (`O(d + log* n)` and `O(d² + log* n)`) also need the cited
colouring algorithms ([PR01], [FHK16]) and a LOCAL implementation of each phase. These are not
formalized.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SharpThresholdLLL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)] {V : Type} [Fintype V] [DecidableEq V]

@[ext] lemma State.ext' {s s' : State ι α V} (h1 : s.σ = s'.σ) (h2 : s.φ = s'.φ) : s = s' := by
  cases s; cases s'; simp_all

namespace Instance

variable (I : Instance ι α V)

/-! ## Locality of conditional probabilities -/

lemma condProb_update_of_not_mem (σ : ∀ i, Option (α i)) {t : V} {i : ι} (hi : i ∉ I.vbl t)
    (o : Option (α i)) :
    I.condProb (Function.update σ i o) t = I.condProb (Function.update σ i none) t := by
  cases o with
  | none => rfl
  | some a =>
    have : Function.update σ i (some a) =
        Function.update (Function.update σ i none) i (some a) := by simp
    rw [this, I.condProb_fix_of_not_mem _ (by simp) hi]

/-- `Pr[E_t | ·]` depends only on the values of the variables of `E_t`. -/
theorem condProb_congr {σ σ' : ∀ i, Option (α i)} {t : V} (h : ∀ i ∈ I.vbl t, σ i = σ' i) :
    I.condProb σ t = I.condProb σ' t := by
  classical
  suffices key : ∀ S : Finset ι, ∀ σ : ∀ i, Option (α i), (∀ i ∉ S, σ i = σ' i) →
      (∀ i ∈ S, i ∉ I.vbl t) → I.condProb σ t = I.condProb σ' t by
    apply key (univ.filter fun i => i ∉ I.vbl t) σ
    · intro i hi; simp only [mem_filter, mem_univ, true_and, not_not] at hi; exact h i hi
    · intro i hi; exact (mem_filter.1 hi).2
  intro S
  induction S using Finset.induction_on with
  | empty => intro σ hσ _; congr 1; funext i; exact hσ i (by simp)
  | insert i S hiS ih =>
    intro σ hσ hS
    have hi : i ∉ I.vbl t := hS i (mem_insert_self i S)
    have e : I.condProb σ t = I.condProb (Function.update σ i (σ' i)) t := by
      rw [I.condProb_update_of_not_mem σ hi, ← I.condProb_update_of_not_mem σ hi (σ i),
        Function.update_eq_self]
    rw [e]
    apply ih
    · intro k hk
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki]; exact hσ k (by simp [hki, hk])
    · intro k hk; exact hS k (mem_insert_of_mem hk)

/-! ## Runs -/

/-- A sequential run of the process fixing the variables of `l` in this order. -/
inductive Run (p : ℝ) : State ι α V → List ι → State ι α V → Prop
  | nil (s : State ι α V) : Run p s [] s
  | cons {s s₁ s₂ : State ι α V} {j : ι} {l : List ι} :
      I.Step p j s s₁ → Run p s₁ l s₂ → Run p s (j :: l) s₂

variable {I}

lemma Run.append {p : ℝ} {s s₁ s₂ : State ι α V} {l₁ l₂ : List ι} (h₁ : I.Run p s l₁ s₁)
    (h₂ : I.Run p s₁ l₂ s₂) : I.Run p s (l₁ ++ l₂) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact Run.cons hs (ih h₂)

lemma Run.reflTransGen {p : ℝ} {s s' : State ι α V} {l : List ι} (h : I.Run p s l s') :
    Relation.ReflTransGen (fun a b => ∃ j, I.Step p j a b) s s' := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | cons hs _ ih => exact Relation.ReflTransGen.head ⟨_, hs⟩ ih

lemma Run.sigma_frame {p : ℝ} {s s' : State ι α V} {l : List ι} (h : I.Run p s l s') :
    ∀ i ∉ l, s'.σ i = s.σ i := by
  induction h with
  | nil => intro i _; rfl
  | cons hs _ ih =>
    intro i hi
    obtain ⟨-, ⟨a, -, hσ⟩, -⟩ := hs
    have hij : i ≠ _ := fun e => hi (by rw [e]; exact List.mem_cons_self)
    rw [ih i (fun h => hi (List.mem_cons_of_mem _ h)), hσ, Function.update_of_ne hij]

lemma Run.phi_frame {p : ℝ} {s s' : State ι α V} {l : List ι} (h : I.Run p s l s')
    {R : Set V} (hR : ∀ j ∈ l, ∀ t ∈ I.evs j, t ∈ R) : ∀ u ∉ R, ∀ v, s'.φ u v = s.φ u v := by
  induction h with
  | nil => intro u _ v; rfl
  | cons hs _ ih =>
    intro u hu v
    obtain ⟨-, -, hframe, -⟩ := hs
    rw [ih (fun j hj => hR j (List.mem_cons_of_mem _ hj)) u hu v]
    exact hframe u v fun h' => hu (hR _ List.mem_cons_self u h'.1)

/-- Fixed variables stay fixed, and the variables of a run are fixed at its end. -/
lemma Run.fixed {p : ℝ} {s s' : State ι α V} {l : List ι} (h : I.Run p s l s') :
    ∀ i, (i ∈ l ∨ s.σ i ≠ none) → s'.σ i ≠ none := by
  induction h with
  | nil => intro i hi; exact hi.resolve_left (by simp)
  | @cons s s₁ s₂ j l hs _ ih =>
    intro i hi
    obtain ⟨hj, ⟨a, -, hσ⟩, -⟩ := hs
    apply ih
    by_cases hij : i = j
    · subst hij; right; rw [hσ]; simp
    · rcases hi with hi | hi
      · left; simpa [hij] using hi
      · right; rw [hσ, Function.update_of_ne hij]; exact hi

/-! ## Transport of runs -/

/-- `s` and `z` agree on the variables `W` and on the bookkeeping rows of the events `R`. -/
def Agree (W : Set ι) (R : Set V) (s z : State ι α V) : Prop :=
  (∀ i ∈ W, s.σ i = z.σ i) ∧ ∀ t ∈ R, ∀ u, s.φ t u = z.φ t u

/-- What a run on the variables `l` inside the region `R` reads: the variables of `l` and of the
events in `R`. -/
def readVars (I : Instance ι α V) (l : List ι) (R : Set V) : Set ι :=
  {i | i ∈ l ∨ ∃ t ∈ R, i ∈ I.vbl t}

open scoped Classical in
/-- Replay the effect of a step `s → s'` on variable `j` on another state `z`. -/
noncomputable def applyStep (I : Instance ι α V) (j : ι) (s' z : State ι α V) : State ι α V :=
  ⟨Function.update z.σ j (s'.σ j),
    fun u v => if u ∈ I.evs j ∧ v ∈ I.evs j then s'.φ u v else z.φ u v⟩

/-- **Locality of a step.** A step `s → s'` on `X_j` stays valid from any state `z` that agrees
with `s` on the variables of the events of `X_j` and on their bookkeeping rows. -/
theorem Step.transport {p : ℝ} {j : ι} {s s' z : State ι α V} (hstep : I.Step p j s s')
    (hσ : ∀ t ∈ I.evs j, ∀ i ∈ I.vbl t, s.σ i = z.σ i)
    (hφ : ∀ t ∈ I.evs j, ∀ u, s.φ t u = z.φ t u) (hj : z.σ j = none) :
    I.Step p j z (I.applyStep j s' z) := by
  classical
  obtain ⟨-, ⟨a, ha, hσ'⟩, hframe, hpair, hloc⟩ := hstep
  have hs'j : s'.σ j = some a := by rw [hσ']; simp
  refine ⟨hj, ⟨a, ha, by simp [applyStep, hs'j]⟩, ?_, ?_, ?_⟩
  · intro u v huv; simp [applyStep, huv]
  · intro u hu v hv huv
    simp only [applyStep, hu, hv, and_self, ↓reduceIte]
    exact hpair u hu v hv huv
  · intro t ht
    have hc : I.condProb (I.applyStep j s' z).σ t = I.condProb s'.σ t := by
      apply I.condProb_congr
      intro i hi
      simp only [applyStep]
      by_cases hij : i = j
      · subst hij; simp [hs'j]
      · rw [Function.update_of_ne hij, hσ', Function.update_of_ne hij]
        exact (hσ t ht i hi).symm
    have hp : ∏ u ∈ I.dep t, (I.applyStep j s' z).φ t u = ∏ u ∈ I.dep t, s'.φ t u := by
      apply prod_congr rfl
      intro u _
      simp only [applyStep]
      by_cases hu : u ∈ I.evs j
      · simp [ht, hu]
      · simp only [ht, hu, and_false, ↓reduceIte]
        rw [← hφ t ht u]
        exact (hframe t u fun h => hu h.2).symm
    rw [hc, hp]; exact hloc t ht

lemma Agree.mono {W W' : Set ι} {R : Set V} {s z : State ι α V} (h : Agree W R s z)
    (hW : W' ⊆ W) : Agree W' R s z := ⟨fun i hi => h.1 i (hW hi), h.2⟩

/-- **Transport of runs.** A run from `s` inside region `R` can be replayed from any `z`
agreeing with `s` on what the run reads. The replayed run ends in a state that agrees with the
original end state on what the run reads, and that coincides with `z` elsewhere. -/
theorem Run.transport {p : ℝ} {s s' : State ι α V} {l : List ι} (hrun : I.Run p s l s')
    {R : Set V} (hR : ∀ j ∈ l, ∀ t ∈ I.evs j, t ∈ R) {z : State ι α V}
    (hag : Agree (I.readVars l R) R s z) :
    ∃ z', I.Run p z l z' ∧ Agree (I.readVars l R) R s' z' ∧ (∀ i ∉ l, z'.σ i = z.σ i) ∧
      (∀ u ∉ R, ∀ v, z'.φ u v = z.φ u v) := by
  classical
  induction hrun generalizing z with
  | nil s => exact ⟨z, Run.nil z, hag, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | @cons s s₁ s₂ j l hs hrest ih =>
    have hRj : ∀ t ∈ I.evs j, t ∈ R := hR j List.mem_cons_self
    have hRl : ∀ k ∈ l, ∀ t ∈ I.evs k, t ∈ R := fun k hk => hR k (List.mem_cons_of_mem _ hk)
    obtain ⟨hj, ⟨a, -, hσ⟩, hframe, -, -⟩ := id hs
    have hjW : j ∈ I.readVars (j :: l) R := Or.inl List.mem_cons_self
    have hzj : z.σ j = none := (hag.1 j hjW).symm.trans hj
    have hstep' := Step.transport hs
      (fun t ht i hi => hag.1 i (Or.inr ⟨t, hRj t ht, hi⟩)) (fun t ht => hag.2 t (hRj t ht)) hzj
    set z₁ := I.applyStep j s₁ z
    have hs₁j : s₁.σ j = some a := by rw [hσ]; simp
    -- agreement after one step
    have hag₁ : Agree (I.readVars (j :: l) R) R s₁ z₁ := by
      refine ⟨fun i hi => ?_, fun t ht u => ?_⟩
      · simp only [z₁, applyStep]
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij, hσ, Function.update_of_ne hij]; exact hag.1 i hi
      · simp only [z₁, applyStep]
        by_cases h : t ∈ I.evs j ∧ u ∈ I.evs j
        · simp [h]
        · simp only [h, ↓reduceIte]; rw [hframe t u h]; exact hag.2 t ht u
    have hsub : I.readVars l R ⊆ I.readVars (j :: l) R := by
      intro i hi; rcases hi with hi | hi
      · exact Or.inl (List.mem_cons_of_mem _ hi)
      · exact Or.inr hi
    obtain ⟨z', hrun', hag', hσfr, hφfr⟩ := ih hRl (hag₁.mono hsub)
    refine ⟨z', Run.cons hstep' hrun', ⟨fun i hi => ?_, hag'.2⟩, fun i hi => ?_, fun u hu v => ?_⟩
    · by_cases hil : i ∈ l
      · exact hag'.1 i (Or.inl hil)
      · rcases hi with hi | hi
        · rw [hrest.sigma_frame i hil, hσfr i hil]; exact hag₁.1 i (Or.inl hi)
        · exact hag'.1 i (Or.inr hi)
    · have hij : i ≠ j := fun e => hi (e ▸ List.mem_cons_self)
      rw [hσfr i (fun h => hi (List.mem_cons_of_mem _ h))]
      simp [z₁, applyStep, Function.update_of_ne hij]
    · rw [hφfr u hu v]
      have : ¬ (u ∈ I.evs j ∧ v ∈ I.evs j) := fun h => hu (hRj u h.1)
      simp [z₁, applyStep, this]

/-! ## Parallel phases -/

/-- A group of a parallel phase: its variables (fixed in this order), its region, and the state
its run reaches from the common start state. -/
structure Group (ι : Type) (α : ι → Type) (V : Type) where
  vars : List ι
  region : Set V
  out : State ι α V

open scoped Classical in
/-- Overlay the changes of group `g` on `base`. -/
noncomputable def overlay (base : State ι α V) (g : Group ι α V) : State ι α V :=
  ⟨fun i => if i ∈ g.vars then g.out.σ i else base.σ i,
    fun u v => if u ∈ g.region then g.out.φ u v else base.φ u v⟩

/-- The result of a parallel phase: all groups' changes merged into the start state. -/
noncomputable def merge (s : State ι α V) : List (Group ι α V) → State ι α V
  | [] => s
  | g :: gs => overlay (merge s gs) g

/-- The variables of a phase, in a sequential order realising it. -/
def phaseVars : List (Group ι α V) → List ι
  | [] => []
  | g :: gs => phaseVars gs ++ g.vars

/-- A valid parallel phase from state `s`. Each group's run starts at `s` and stays inside its
region, the regions are pairwise disjoint, and no variable belongs to two groups. -/
structure ValidPhase (I : Instance ι α V) (p : ℝ) (s : State ι α V) (G : List (Group ι α V)) :
    Prop where
  run : ∀ g ∈ G, I.Run p s g.vars g.out
  region : ∀ g ∈ G, ∀ j ∈ g.vars, ∀ t ∈ I.evs j, t ∈ g.region
  disj : G.Pairwise fun g g' => Disjoint g.region g'.region ∧ ∀ j ∈ g.vars, j ∉ g'.vars

lemma merge_sigma (s : State ι α V) (G : List (Group ι α V)) (i : ι)
    (hi : ∀ g ∈ G, i ∉ g.vars) : (merge s G).σ i = s.σ i := by
  classical
  induction G with
  | nil => rfl
  | cons g gs ih =>
    simp only [merge, overlay, hi g List.mem_cons_self, ↓reduceIte]
    exact ih fun g' hg' => hi g' (List.mem_cons_of_mem _ hg')

lemma merge_phi (s : State ι α V) (G : List (Group ι α V)) (u : V)
    (hu : ∀ g ∈ G, u ∉ g.region) (v : V) : (merge s G).φ u v = s.φ u v := by
  classical
  induction G with
  | nil => rfl
  | cons g gs ih =>
    simp only [merge, overlay, hu g List.mem_cons_self, ↓reduceIte]
    exact ih fun g' hg' => hu g' (List.mem_cons_of_mem _ hg')

/-- **A parallel phase is a sequential run.** The merged result of a valid phase is reached
from the start state by the concatenation of the groups' runs. -/
theorem phase_run {p : ℝ} {s : State ι α V} {G : List (Group ι α V)} (h : I.ValidPhase p s G) :
    I.Run p s (phaseVars G) (merge s G) := by
  classical
  induction G with
  | nil => exact Run.nil s
  | cons g gs ih =>
    have hgs : I.ValidPhase p s gs := ⟨fun g' hg' => h.run g' (List.mem_cons_of_mem _ hg'),
      fun g' hg' => h.region g' (List.mem_cons_of_mem _ hg'), (List.pairwise_cons.1 h.disj).2⟩
    have hdisj := (List.pairwise_cons.1 h.disj).1
    have hrun := h.run g List.mem_cons_self
    have hR := h.region g List.mem_cons_self
    -- the merged state of the other groups agrees with `s` on what `g` reads
    have hag : Agree (I.readVars g.vars g.region) g.region s (merge s gs) := by
      refine ⟨fun i hi => (merge_sigma s gs i fun g' hg' hig' => ?_).symm,
        fun t ht u => (merge_phi s gs t (fun g' hg' htg' => ?_) u).symm⟩
      · rcases hi with hi | ⟨t, ht, hit⟩
        · exact (hdisj g' hg').2 i hi hig'
        · have := h.region g' (List.mem_cons_of_mem _ hg') i hig' t (I.mem_evs.2 hit)
          exact Set.disjoint_left.1 (hdisj g' hg').1 ht this
      · exact Set.disjoint_left.1 (hdisj g' hg').1 ht htg'
    obtain ⟨z', hrun', hag', hσfr, hφfr⟩ := hrun.transport hR hag
    have heq : z' = overlay (merge s gs) g := by
      apply State.ext'
      · funext i
        simp only [overlay]
        by_cases hi : i ∈ g.vars
        · simp only [hi, ↓reduceIte]; exact (hag'.1 i (Or.inl hi)).symm
        · simp only [hi, ↓reduceIte]; exact hσfr i hi
      · funext u v
        simp only [overlay]
        by_cases hu : u ∈ g.region
        · simp only [hu, ↓reduceIte]; exact (hag'.2 u hu v).symm
        · simp only [hu, ↓reduceIte]; exact hφfr u hu v
    rw [merge, phaseVars, ← heq]
    exact (ih hgs).append hrun'

/-! ## Schedules -/

/-- An execution of a sequence of valid parallel phases. -/
inductive RunPhases (I : Instance ι α V) (p : ℝ) :
    State ι α V → List (List (Group ι α V)) → State ι α V → Prop
  | nil (s : State ι α V) : RunPhases I p s [] s
  | cons {s s' : State ι α V} {G : List (Group ι α V)} {Gs : List (List (Group ι α V))} :
      I.ValidPhase p s G → RunPhases I p (merge s G) Gs s' → RunPhases I p s (G :: Gs) s'

lemma mem_phaseVars {G : List (Group ι α V)} {g : Group ι α V} (hg : g ∈ G) {j : ι}
    (hj : j ∈ g.vars) : j ∈ phaseVars G := by
  induction G with
  | nil => simp at hg
  | cons g' gs ih =>
    rcases List.mem_cons.1 hg with rfl | hg
    · simp [phaseVars, hj]
    · simp [phaseVars, ih hg]

lemma RunPhases.run {p : ℝ} {s s' : State ι α V} {Gs : List (List (Group ι α V))}
    (h : I.RunPhases p s Gs s') : ∃ l, I.Run p s l s' ∧ ∀ G ∈ Gs, ∀ g ∈ G, ∀ j ∈ g.vars, j ∈ l := by
  induction h with
  | nil s => exact ⟨[], Run.nil s, by simp⟩
  | @cons s s' G Gs hG _ ih =>
    obtain ⟨l, hl, hmem⟩ := ih
    refine ⟨phaseVars G ++ l, (I.phase_run hG).append hl, ?_⟩
    intro G' hG' g hg j hj
    rcases List.mem_cons.1 hG' with rfl | hG'
    · apply List.mem_append_left
      clear hl hmem hG
      exact mem_phaseVars hg hj
    · exact List.mem_append_right _ (hmem G' hG' g hg j hj)

/-- **Correctness of every parallel schedule** (rank `≤ 3`, `p · 2^d < 1`). Every execution of
valid parallel phases from the initial state reaches a state reachable by the sequential
process. Its variables (those of all groups) are fixed, and if this covers all variables, no
bad event occurs. -/
theorem schedule_correct {p : ℝ} {d : ℕ} (hrank : ∀ j, (I.evs j).card ≤ 3)
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1)
    {s' : State ι α V} {Gs : List (List (Group ι α V))} (h : I.RunPhases p init Gs s') :
    I.Reachable p s' ∧ (∀ G ∈ Gs, ∀ g ∈ G, ∀ j ∈ g.vars, s'.σ j ≠ none) ∧
      ∀ x : ∀ i, α i, (∀ i, s'.σ i = some (x i)) → ∀ v, ¬ I.bad v x := by
  obtain ⟨l, hl, hmem⟩ := h.run
  have hreach : I.Reachable p s' := hl.reflTransGen
  refine ⟨hreach, fun G hG g hg j hj => hl.fixed j (Or.inl (hmem G hG g hg j hj)), ?_⟩
  exact (I.theorem_1_3 hrank hp hd hpd).2.1 s' hreach

/-! ## Existence of executions -/

lemma exists_run {p : ℝ} (hstep : ∀ s, I.Reachable p s → ∀ j, s.σ j = none →
    ∃ s', I.Step p j s s') :
    ∀ (l : List ι) (s : State ι α V), I.Reachable p s → l.Nodup → (∀ j ∈ l, s.σ j = none) →
      ∃ s', I.Run p s l s' := by
  intro l
  induction l with
  | nil => intro s _ _ _; exact ⟨s, Run.nil s⟩
  | cons j l ih =>
    intro s hs hnd hnone
    obtain ⟨s₁, hs₁⟩ := hstep s hs j (hnone j List.mem_cons_self)
    have hreach₁ : I.Reachable p s₁ := Relation.ReflTransGen.tail hs ⟨j, hs₁⟩
    obtain ⟨hj, ⟨a, -, hσ⟩, -⟩ := id hs₁
    obtain ⟨s₂, h₂⟩ := ih s₁ hreach₁ (List.nodup_cons.1 hnd).2 (fun k hk => by
      have hkj : k ≠ j := fun e => (List.nodup_cons.1 hnd).1 (by rw [← e]; exact hk)
      rw [hσ, Function.update_of_ne hkj]; exact hnone k (List.mem_cons_of_mem _ hk))
    exact ⟨s₂, Run.cons hs₁ h₂⟩

/-- A *schedule*: a list of phases, each a list of groups `(variables, region)`. -/
abbrev Schedule (ι : Type) (V : Type) := List (List (List ι × Set V))

/-- A schedule is *valid* if within each phase the regions are pairwise disjoint, each group's
variables affect only events of its region, and over the whole schedule every variable appears
exactly once. -/
structure ValidSchedule (I : Instance ι α V) (S : Schedule ι V) : Prop where
  region : ∀ P ∈ S, ∀ g ∈ P, ∀ j ∈ g.1, ∀ t ∈ I.evs j, t ∈ g.2
  disj : ∀ P ∈ S, P.Pairwise fun g g' => Disjoint g.2 g'.2
  nodup : (S.flatMap fun P => P.flatMap Prod.fst).Nodup
  cover : ∀ j, ∃ P ∈ S, ∃ g ∈ P, j ∈ g.1

/-- The skeleton (variables and regions) of an execution. -/
def skeleton (Gs : List (List (Group ι α V))) : Schedule ι V :=
  Gs.map fun G => G.map fun g => (g.vars, g.region)

/-- **Every valid schedule can be executed, and every execution succeeds** (rank `≤ 3`,
`p · 2^d < 1`). There is an execution following the schedule. Every execution following the
schedule ends with all variables fixed to an assignment avoiding all bad events. -/
theorem valid_schedule_correct {p : ℝ} {d : ℕ} (hrank : ∀ j, (I.evs j).card ≤ 3)
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1)
    {S : Schedule ι V} (hS : I.ValidSchedule S) :
    (∃ Gs s', skeleton Gs = S ∧ I.RunPhases p init Gs s') ∧
      ∀ Gs s', skeleton Gs = S → I.RunPhases p init Gs s' →
        ∃ x : ∀ i, α i, (∀ i, s'.σ i = some (x i)) ∧ ∀ v, ¬ I.bad v x := by
  classical
  have hstep := (I.theorem_1_3 hrank hp hd hpd).1
  constructor
  · -- build the execution phase by phase
    suffices key : ∀ (S' : Schedule ι V) (s : State ι α V), I.Reachable p s →
        (∀ P ∈ S', ∀ g ∈ P, ∀ j ∈ g.1, ∀ t ∈ I.evs j, t ∈ g.2) →
        (∀ P ∈ S', P.Pairwise fun g g' => Disjoint g.2 g'.2) →
        (S'.flatMap fun P => P.flatMap Prod.fst).Nodup →
        (∀ P ∈ S', ∀ g ∈ P, ∀ j ∈ g.1, s.σ j = none) →
        ∃ Gs s', skeleton Gs = S' ∧ I.RunPhases p s Gs s' by
      exact key S init Relation.ReflTransGen.refl hS.region hS.disj hS.nodup
        (fun _ _ _ _ _ _ => rfl)
    intro S'
    induction S' with
    | nil => intro s _ _ _ _ _; exact ⟨[], s, rfl, RunPhases.nil s⟩
    | cons P S' ih =>
      intro s hs hreg hdisj hnd hnone
      -- every group of `P` runs from `s`
      have hndP : (P.flatMap Prod.fst).Nodup := (List.nodup_append.1
        (by simpa [List.flatMap_cons] using hnd)).1
      have hndP' := List.nodup_flatMap.1 hndP
      have hgroup : ∀ g ∈ P, ∃ o, I.Run p s g.1 o := by
        intro g hg
        exact exists_run hstep g.1 s hs (hndP'.1 g hg) (hnone P List.mem_cons_self g hg)
      have : Nonempty (State ι α V) := ⟨⟨fun _ => none, fun _ _ => 0⟩⟩
      choose! out hout using hgroup
      let G : List (Group ι α V) := P.map fun g => ⟨g.1, g.2, out g⟩
      have hvalid : I.ValidPhase p s G := by
        refine ⟨?_, ?_, ?_⟩
        · intro g' hg'
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
          exact hout g hg
        · intro g' hg'
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
          exact hreg P List.mem_cons_self g hg
        · rw [List.pairwise_map]
          have hpw := hdisj P List.mem_cons_self
          have hpw2 := hndP'.2
          refine List.Pairwise.and hpw ?_
          refine hpw2.imp ?_
          intro g g' h j hj hj'
          exact List.disjoint_left.1 h hj hj'
      have hrun := I.phase_run hvalid
      have hreach' : I.Reachable p (merge s G) :=
        Relation.ReflTransGen.trans hs hrun.reflTransGen
      have hndrest : (S'.flatMap fun P => P.flatMap Prod.fst).Nodup :=
        (List.nodup_append.1 (by simpa [List.flatMap_cons] using hnd)).2.1
      have hdisjrest := (List.nodup_append.1 (by simpa [List.flatMap_cons] using hnd)).2.2
      obtain ⟨Gs, s', hsk, hrp⟩ := ih (merge s G) hreach'
        (fun P' hP' => hreg P' (List.mem_cons_of_mem _ hP'))
        (fun P' hP' => hdisj P' (List.mem_cons_of_mem _ hP')) hndrest
        (by
          intro P' hP' g hg j hj
          rw [merge_sigma]
          · exact hnone P' (List.mem_cons_of_mem _ hP') g hg j hj
          · intro g' hg' hjg'
            obtain ⟨g'', hg'', rfl⟩ := List.mem_map.1 hg'
            have h1 : j ∈ P.flatMap Prod.fst := List.mem_flatMap.2 ⟨g'', hg'', hjg'⟩
            have h2 : j ∈ S'.flatMap fun P => P.flatMap Prod.fst :=
              List.mem_flatMap.2 ⟨P', hP', List.mem_flatMap.2 ⟨g, hg, hj⟩⟩
            exact hdisjrest j h1 j h2 rfl)
      refine ⟨G :: Gs, s', ?_, RunPhases.cons hvalid hrp⟩
      simp only [skeleton, List.map_cons] at hsk ⊢
      rw [hsk]
      simp only [G, List.map_map, List.cons.injEq, and_true]
      conv_rhs => rw [← List.map_id P]
      rfl
  · intro Gs s' hsk hrp
    obtain ⟨hreach, hfixed, hgood⟩ := I.schedule_correct hrank hp hd hpd hrp
    have hall : ∀ i, s'.σ i ≠ none := by
      intro i
      obtain ⟨P, hP, g, hg, hi⟩ := hS.cover i
      rw [← hsk] at hP
      obtain ⟨G, hG, rfl⟩ := List.mem_map.1 hP
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      exact hfixed G hG g' hg' i hi
    let x : ∀ i, α i := fun i => (s'.σ i).get (Option.ne_none_iff_isSome.1 (hall i))
    have hx : ∀ i, s'.σ i = some (x i) := fun i => by simp [x]
    exact ⟨x, hx, hgood x hx⟩

end Instance

end SharpThresholdLLL
