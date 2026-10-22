import Podc.Computability.Distributed.DistributedAutomata.Simulation
import Cslib.Foundations.Data.OmegaSequence.Flatten
import Cslib.Computability.Distributed.SelfStabilization.Daemon

-- CSLib candidate: Cslib/Computability/Distributed/DistributedAutomata/Fairness.lean

/-!
# Constructing fair schedules

* `flat ls`: concatenation of an infinite sequence of nonempty lists (CSLib's
  `ωSequence.flatten`), with `runFrom_flat_block`: the run over a block is `runList`.
* `prepend l σ` with `IsFair.prepend` and `runFrom_prepend`: fairness does not depend on finite
  prefixes.
* `exists_fair`: fair schedules exist for every scheduler (on nonempty finite graphs).
* `exists_fair_frequently`: if from every configuration reachable from `C₀` some configuration
  satisfying `P` is reachable, then some fair run from `C₀` visits `P` infinitely often (for both
  fairness notions). This is the standard construction behind "a pseudo-stochastic run rejects iff
  a stably rejecting configuration is reachable".
* `exists_fair_of_liftable`: a schedule of liftable selections (independent sets for exclusive
  selection) can be realised by an adversarially fair schedule with the same eventual behaviour.
* `Automaton.accepts_iff`: under the consistency condition, acceptance can be read off any fair run.
* Bridge to CSLib's daemon / stone-age framework: `step_eq_stepSet` (a step is a daemon step
  `Cslib.SelfStabilization.stepSet` of the atomic-state algorithm `C v ↦ δ (C v) (view β G C v)`),
  `IsFair.stoneAgeFair` (fair schedules are weakly fair, `Cslib.StoneAge.Fair`).
-/

namespace Cslib.DistributedAutomata

open Set

variable {Λ Q V : Type*}

section Flat

variable {α : Type*} [Inhabited α]

/-- Concatenation of an infinite sequence of lists (meaningful when all lists are nonempty). -/
noncomputable def flat (ls : ℕ → List α) : ℕ → α := fun n => ωSequence.flatten ⟨ls⟩ n

/-- The position at which block `k` starts in `flat ls`. -/
def blockStart (ls : ℕ → List α) (k : ℕ) : ℕ := ωSequence.cumLen ⟨ls⟩ k

variable {ls : ℕ → List α}

omit [Inhabited α] in
@[simp] lemma blockStart_zero : blockStart ls 0 = 0 := rfl

omit [Inhabited α] in
lemma blockStart_succ (k : ℕ) : blockStart ls (k + 1) = blockStart ls k + (ls k).length := rfl

lemma flat_blockStart_add (hpos : ∀ k, 0 < (ls k).length) {k i : ℕ} (hi : i < (ls k).length) :
    flat ls (blockStart ls k + i) = (ls k)[i] :=
  ωSequence.flatten_get_add (ls := ⟨ls⟩) hi hpos

omit [Inhabited α] in
lemma blockStart_strictMono (hpos : ∀ k, 0 < (ls k).length) : StrictMono (blockStart ls) :=
  ωSequence.cumLen_strictMono (ls := ⟨ls⟩) hpos

omit [Inhabited α] in
lemma le_blockStart (hpos : ∀ k, 0 < (ls k).length) (k : ℕ) : k ≤ blockStart ls k :=
  (blockStart_strictMono hpos).id_le k

omit [Inhabited α] in
lemma exists_block (hpos : ∀ k, 0 < (ls k).length) (t : ℕ) :
    ∃ k, blockStart ls k ≤ t ∧ t < blockStart ls (k + 1) :=
  ⟨Nat.segment (blockStart ls) t,
    Nat.segment_lower_bound (blockStart_strictMono hpos) rfl t,
    Nat.segment_upper_bound (blockStart_strictMono hpos) rfl t⟩

lemma flat_mem (hpos : ∀ k, 0 < (ls k).length) (t : ℕ) : ∃ k, flat ls t ∈ ls k := by
  obtain ⟨k, h₁, h₂⟩ := exists_block hpos t
  have hi : t - blockStart ls k < (ls k).length := by rw [blockStart_succ] at h₂; omega
  refine ⟨k, ?_⟩
  have := flat_blockStart_add hpos hi
  rw [Nat.add_sub_cancel' h₁] at this
  rw [this]
  exact List.getElem_mem hi

end Flat

section Runs

variable (M : Machine Λ Q) (G : SimpleGraph V)

lemma runFrom_flat_block {ls : ℕ → List (Set V)} (hpos : ∀ k, 0 < (ls k).length) (C : V → Q)
    (k j : ℕ) (hj : j ≤ (ls k).length) :
    runFrom M G C (flat ls) (blockStart ls k + j) =
      runList M G (runFrom M G C (flat ls) (blockStart ls k)) ((ls k).take j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← Nat.add_assoc, runFrom_succ, ih (by omega), flat_blockStart_add hpos (by omega),
      ← List.take_concat_get' _ _ (by omega), runList_concat]

lemma runFrom_flat_blockStart_succ {ls : ℕ → List (Set V)} (hpos : ∀ k, 0 < (ls k).length)
    (C : V → Q) (k : ℕ) :
    runFrom M G C (flat ls) (blockStart ls (k + 1)) =
      runList M G (runFrom M G C (flat ls) (blockStart ls k)) (ls k) := by
  rw [blockStart_succ, runFrom_flat_block M G hpos C k _ le_rfl, List.take_length]

/-- Prefixing a schedule with a finite list of selections. -/
def prepend {α : Type*} (l : List α) (σ : ℕ → α) : ℕ → α :=
  fun t => if h : t < l.length then l[t] else σ (t - l.length)

lemma runFrom_prepend (C : V → Q) (l : List (Set V)) (σ : ℕ → Set V) (t : ℕ) :
    runFrom M G C (prepend l σ) (l.length + t) = runFrom M G (runList M G C l) σ t := by
  rw [runFrom_add]
  congr 1
  · rw [runFrom_eq_runList]
    congr 1
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, prepend]
    simp at h₁
    simp [h₁]
  · funext s
    simp [prepend]

lemma IsFair.prepend {κ : Selection} {φ : Fairness} {σ : ℕ → Set V} (h : IsFair κ φ σ)
    {l : List (Set V)} (hl : ∀ S ∈ l, κ.Permitted S) : IsFair κ φ (prepend l σ) := by
  obtain ⟨hperm, hnode, hps⟩ := h
  refine ⟨fun t => ?_, fun v N => ?_, fun hφ w hw N => ?_⟩
  · unfold DistributedAutomata.prepend
    split_ifs with ht
    · exact hl _ (List.getElem_mem ht)
    · exact hperm _
  · obtain ⟨t, ht, hv⟩ := hnode v N
    refine ⟨t + l.length, by omega, ?_⟩
    simpa [DistributedAutomata.prepend] using hv
  · obtain ⟨t, ht, hw'⟩ := hps hφ w hw N
    refine ⟨t + l.length, by omega, fun i hi => ?_⟩
    have := hw' i hi
    simp only [DistributedAutomata.prepend]
    rw [dite_cond_eq_false (by simp; omega)]
    rw [← this]; congr 1; omega

end Runs

section Exists

lemma Selection.exists_permitted_mem (κ : Selection) (v : V) : ∃ S : Set V, κ.Permitted S ∧ v ∈ S :=
  match κ with
  | .liberal => ⟨univ, trivial, trivial⟩
  | .exclusive => ⟨{v}, ⟨v, rfl⟩, rfl⟩
  | .synchronous => ⟨univ, rfl, trivial⟩

/-- An enumeration of all finite sequences of permitted selections. -/
lemma exists_enum [Finite V] (κ : Selection) :
    ∃ e : ℕ → List (Set V), (∀ n, ∀ S ∈ e n, κ.Permitted S) ∧
      ∀ w : List (Set V), (∀ S ∈ w, κ.Permitted S) → ∃ n, e n = w := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (List {S : Set V // κ.Permitted S})
  refine ⟨fun n => (f n).map Subtype.val, ?_, ?_⟩
  · intro n S hS
    obtain ⟨⟨S', h⟩, -, rfl⟩ := List.mem_map.1 hS
    exact h
  · intro w hw
    obtain ⟨n, hn⟩ := hf (w.pmap Subtype.mk hw)
    exact ⟨n, by simp [hn, List.map_pmap]⟩

/-- A flattened schedule whose `k`-th block starts with the `k.unpair.1`-th permitted sequence is
fair. -/
lemma isFair_flat (κ : Selection) (φ : Fairness) (e : ℕ → List (Set V))
    (he : ∀ w : List (Set V), (∀ S ∈ w, κ.Permitted S) → ∃ n, e n = w)
    (ls : ℕ → List (Set V)) (hpos : ∀ k, 0 < (ls k).length)
    (hperm : ∀ k, ∀ S ∈ ls k, κ.Permitted S)
    (hpre : ∀ k, ∃ l, ls k = e k.unpair.1 ++ l) : IsFair κ φ (flat ls) := by
  have hocc : ∀ w : List (Set V), (∀ S ∈ w, κ.Permitted S) →
      ∀ N, ∃ t ≥ N, ∀ i (h : i < w.length), flat ls (t + i) = w[i] := by
    intro w hw N
    obtain ⟨n, rfl⟩ := he w hw
    obtain ⟨l, hl⟩ := hpre (Nat.pair n N)
    rw [Nat.unpair_pair] at hl
    refine ⟨blockStart ls (Nat.pair n N),
      (Nat.right_le_pair n N).trans (le_blockStart hpos _), fun i hi => ?_⟩
    have hi' : i < (ls (Nat.pair n N)).length := by rw [hl]; simp; omega
    rw [flat_blockStart_add hpos hi']
    simp only [hl]
    exact List.getElem_append_left hi
  refine ⟨fun t => ?_, fun v N => ?_, fun _ => hocc⟩
  · obtain ⟨k, hk⟩ := flat_mem hpos t
    exact hperm k _ hk
  · obtain ⟨S, hS, hv⟩ := κ.exists_permitted_mem v
    obtain ⟨t, ht, h⟩ := hocc [S] (by simpa using hS) N
    refine ⟨t, ht, ?_⟩
    have := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at this
    rw [this]; exact hv

lemma Selection.exists_permitted [Nonempty V] (κ : Selection) : ∃ S : Set V, κ.Permitted S :=
  let ⟨S, h, _⟩ := κ.exists_permitted_mem (Classical.arbitrary V); ⟨S, h⟩

/-- Fair schedules exist. -/
theorem exists_fair [Finite V] [Nonempty V] (κ : Selection) (φ : Fairness) :
    ∃ σ : ℕ → Set V, IsFair κ φ σ := by
  obtain ⟨e, he₁, he₂⟩ := exists_enum (V := V) κ
  obtain ⟨S₀, hS₀⟩ := κ.exists_permitted (V := V)
  refine ⟨_, isFair_flat κ φ e he₂ (fun k => e k.unpair.1 ++ [S₀]) (fun k => by simp)
    (fun k S hS => ?_) (fun k => ⟨_, rfl⟩)⟩
  rcases List.mem_append.1 hS with h | h
  · exact he₁ _ S h
  · simp at h; exact h ▸ hS₀

variable (M : Machine Λ Q) (G : SimpleGraph V)

/-- If every configuration reachable from `C₀` can reach a configuration satisfying `P`, some fair
run from `C₀` visits `P` infinitely often. -/
theorem exists_fair_frequently [Finite V] [Nonempty V] (κ : Selection) (φ : Fairness)
    (P : (V → Q) → Prop) (C₀ : V → Q)
    (h : ∀ C, Reach M G κ C₀ C → ∃ D, Reach M G κ C D ∧ P D) :
    ∃ σ, IsFair κ φ σ ∧ ∀ N, ∃ t ≥ N, P (runFrom M G C₀ σ t) := by
  classical
  obtain ⟨e, he₁, he₂⟩ := exists_enum (V := V) κ
  obtain ⟨S₀, hS₀⟩ := κ.exists_permitted (V := V)
  let g : (V → Q) → List (Set V) := fun C =>
    if hC : ∃ l : List (Set V), (∀ S ∈ l, κ.Permitted S) ∧ P (runList M G C l) then hC.choose
    else []
  have hg : ∀ C, ∀ S ∈ g C, κ.Permitted S := by
    intro C S hS
    simp only [g] at hS
    split_ifs at hS with hC
    · exact hC.choose_spec.1 S hS
    · simp at hS
  let e' : ℕ → List (Set V) := fun k => e k.unpair.1 ++ [S₀]
  have he' : ∀ k, ∀ S ∈ e' k, κ.Permitted S := by
    intro k S hS
    rcases List.mem_append.1 hS with h | h
    · exact he₁ _ S h
    · simp at h; exact h ▸ hS₀
  let X : ℕ → V → Q := fun k => Nat.rec C₀ (fun k Xk => runList M G (runList M G Xk (e' k))
    (g (runList M G Xk (e' k)))) k
  let ls : ℕ → List (Set V) := fun k => e' k ++ g (runList M G (X k) (e' k))
  have hpos : ∀ k, 0 < (ls k).length := fun k => by simp [ls, e']
  have hperm : ∀ k, ∀ S ∈ ls k, κ.Permitted S := by
    intro k S hS
    rcases List.mem_append.1 hS with h | h
    exacts [he' k S h, hg _ S h]
  have hX : ∀ k, runFrom M G C₀ (flat ls) (blockStart ls k) = X k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [runFrom_flat_blockStart_succ M G hpos, ih, runList_append]
  have hreach : ∀ k, Reach M G κ C₀ (X k) := by
    intro k
    induction k with
    | zero => exact Reach.refl κ C₀
    | succ k ih =>
      exact (ih.trans ⟨_, he' k, rfl⟩).trans ⟨_, hg _, rfl⟩
  have hP : ∀ k, P (X (k + 1)) := by
    intro k
    have hY : Reach M G κ C₀ (runList M G (X k) (e' k)) := (hreach k).trans ⟨_, he' k, rfl⟩
    obtain ⟨D, ⟨l, hl, rfl⟩, hD⟩ := h _ hY
    have hC : ∃ l : List (Set V), (∀ S ∈ l, κ.Permitted S) ∧
        P (runList M G (runList M G (X k) (e' k)) l) := ⟨l, hl, hD⟩
    show P (runList M G (runList M G (X k) (e' k)) (g (runList M G (X k) (e' k))))
    simp only [g, dite_cond_eq_true (eq_true hC)]
    exact hC.choose_spec.2
  refine ⟨flat ls, isFair_flat κ φ e he₂ ls hpos hperm (fun k => ⟨_, List.append_assoc _ _ _⟩),
    fun N => ⟨blockStart ls (N + 1), (Nat.le_succ N).trans (le_blockStart hpos _), ?_⟩⟩
  rw [hX]
  exact hP N

lemma runList_toList_singletons [Finite V] (C : V → Q) {S : Set V} (hind : G.IsIndepSet S)
    (j : ℕ) :
    runList M G C (((toFinite S).toFinset.toList.map fun v => ({v} : Set V)).take j) =
      step M G C {v | v ∈ (toFinite S).toFinset.toList.take j} := by
  rw [← List.map_take, runList_singletons M G C _ ((Finset.nodup_toList _).sublist
    (List.take_sublist _ _))]
  intro a ha b hb hab
  have ha' := List.mem_of_mem_take ha
  have hb' := List.mem_of_mem_take hb
  simp only [Finset.mem_toList, Finite.mem_toFinset] at ha' hb'
  exact hind ha' hb' (G.ne_of_adj hab) hab

/-- A schedule of liftable selections that selects every node infinitely often can be realised by
an adversarially fair schedule of `κ` with the same eventual behaviour. -/
theorem exists_fair_of_liftable [Finite V] (κ : Selection) (R : ℕ → Set V)
    (hR : ∀ t, κ.Liftable G (R t)) (hfair : ∀ v N, ∃ t ≥ N, v ∈ R t) (C : V → Q) :
    ∃ σ, IsFair κ .adversarial σ ∧
      ∀ Z : Set Q, EventuallyIn Z (runFrom M G C σ) ↔ EventuallyIn Z (runFrom M G C R) := by
  cases κ with
  | liberal => exact ⟨R, ⟨fun _ => trivial, hfair, fun h => by cases h⟩, fun _ => Iff.rfl⟩
  | synchronous => exact ⟨R, ⟨hR, hfair, fun h => by cases h⟩, fun _ => Iff.rfl⟩
  | exclusive =>
    classical
    let L : ℕ → List V := fun k => (toFinite (R k)).toFinset.toList
    let ls : ℕ → List (Set V) := fun k => (L k).map fun v => {v}
    have hmemL : ∀ k v, v ∈ L k ↔ v ∈ R k := fun k v => by simp [L]
    have hpos : ∀ k, 0 < (ls k).length := by
      intro k
      obtain ⟨v, hv⟩ := (hR k).2
      simp only [ls, List.length_map]
      exact List.length_pos_of_mem ((hmemL k v).2 hv)
    have hstart : ∀ k, runFrom M G C (flat ls) (blockStart ls k) = runFrom M G C R k := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [runFrom_flat_blockStart_succ M G hpos, ih, runFrom_succ]
        have := runList_toList_singletons M G (runFrom M G C R k) (hR k).1 (ls k).length
        rw [List.take_length] at this
        rw [this]
        congr 1; ext v
        show v ∈ (L k).take (ls k).length ↔ v ∈ R k
        rw [show (ls k).length = (L k).length by simp [ls], List.take_length, hmemL]
    have hblock : ∀ k j, j ≤ (ls k).length →
        runFrom M G C (flat ls) (blockStart ls k + j) =
          step M G (runFrom M G C R k) {v | v ∈ (L k).take j} := by
      intro k j hj
      rw [runFrom_flat_block M G hpos C k j hj, hstart]
      exact runList_toList_singletons M G _ (hR k).1 j
    refine ⟨flat ls, ⟨fun t => ?_, fun v N => ?_, fun h => by cases h⟩, fun Z => ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := flat_mem hpos t
      obtain ⟨v, -, hv⟩ := List.mem_map.1 hk
      exact ⟨v, hv.symm⟩
    · obtain ⟨k, hk, hv⟩ := hfair v N
      obtain ⟨i, hi, hvi⟩ := List.getElem_of_mem ((hmemL k v).2 hv)
      have hi' : i < (ls k).length := by simpa [ls] using hi
      refine ⟨blockStart ls k + i, hk.trans ((le_blockStart hpos k).trans (Nat.le_add_right _ _)),
        ?_⟩
      rw [flat_blockStart_add hpos hi']
      simp [ls, hvi]
    · rintro ⟨t₀, ht₀⟩
      refine ⟨t₀, fun k hk v => ?_⟩
      rw [← hstart]
      exact ht₀ _ (hk.trans (le_blockStart hpos k)) v
    · rintro ⟨k₀, hk₀⟩
      refine ⟨blockStart ls k₀, fun t ht v => ?_⟩
      obtain ⟨k, h₁, h₂⟩ := exists_block hpos t
      have hkk : k₀ ≤ k := by
        by_contra hlt
        have := (blockStart_strictMono hpos).monotone (show k + 1 ≤ k₀ by omega)
        omega
      have hj : t - blockStart ls k ≤ (ls k).length := by rw [blockStart_succ] at h₂; omega
      have := hblock k _ hj
      rw [Nat.add_sub_cancel' h₁] at this
      rw [this]
      rcases step_mem_or M G (runFrom M G C R k) {x | x ∈ (L k).take (t - blockStart ls k)} (R k)
        (fun x hx => (hmemL k x).1 (List.mem_of_mem_take hx)) v with h | h
      · rw [h]; exact hk₀ k hkk v
      · rw [h, ← runFrom_succ]; exact hk₀ (k + 1) (by omega) v

end Exists

section Consistency

variable {A : Automaton Λ Q}

lemma not_eventuallyIn_both [Nonempty V] {Y N : Set Q} (hd : Disjoint Y N) {r : ℕ → V → Q}
    (hY : EventuallyIn Y r) (hN : EventuallyIn N r) : False := by
  obtain ⟨t₁, h₁⟩ := hY
  obtain ⟨t₂, h₂⟩ := hN
  let v := Classical.arbitrary V
  exact hd.ne_of_mem (h₁ (max t₁ t₂) (le_max_left _ _) v) (h₂ (max t₁ t₂) (le_max_right _ _) v) rfl

lemma LGraph.Admissible.nonempty {k : ℕ∞} {G : LGraph Λ} (hG : G.Admissible k) : Nonempty G.V := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hG.three_le
  rw [Nat.card_of_isEmpty] at this
  omega

/-- Under the consistency condition, `A` accepts `G` iff a given fair run is accepting. -/
theorem Automaton.accepts_iff {k : ℕ∞} (hA : A.Consistent k) {G : LGraph Λ} (hG : G.Admissible k)
    {σ : ℕ → Set G.V} (hσ : A.FairSchedule G σ) :
    A.Accepts G ↔ EventuallyIn A.M.Y (A.run G σ) := by
  have := hG.nonempty
  refine ⟨fun ⟨σ', hσ', hacc⟩ => ?_, fun h => ⟨σ, hσ, h⟩⟩
  rcases hA G hG with h | h
  · exact h σ hσ
  · exact (not_eventuallyIn_both A.M.disjoint hacc (h σ' hσ')).elim

/-- Under the consistency condition, `A` rejects `G` iff a given fair run is rejecting. -/
theorem Automaton.not_accepts_iff {k : ℕ∞} (hA : A.Consistent k) {G : LGraph Λ}
    (hG : G.Admissible k) {σ : ℕ → Set G.V} (hσ : A.FairSchedule G σ) :
    ¬ A.Accepts G ↔ EventuallyIn A.M.N (A.run G σ) := by
  have := hG.nonempty
  rw [A.accepts_iff hA hG hσ]
  rcases hA G hG with h | h
  · exact ⟨fun h' => (h' (h σ hσ)).elim,
      fun h' h'' => not_eventuallyIn_both A.M.disjoint h'' h'⟩
  · exact ⟨fun _ => h σ hσ, fun h' h'' => not_eventuallyIn_both A.M.disjoint h'' h'⟩

/-- Every fair run is accepting or rejecting. -/
theorem Automaton.eventuallyIn_or {k : ℕ∞} (hA : A.Consistent k) {G : LGraph Λ}
    (hG : G.Admissible k) {σ : ℕ → Set G.V} (hσ : A.FairSchedule G σ) :
    EventuallyIn A.M.Y (A.run G σ) ∨ EventuallyIn A.M.N (A.run G σ) := by
  by_cases h : A.Accepts G
  · exact Or.inl ((A.accepts_iff hA hG hσ).1 h)
  · exact Or.inr ((A.not_accepts_iff hA hG hσ).1 h)

end Consistency

section Bridge

/-- A step of a distributed machine is a daemon step (`Cslib.SelfStabilization.stepSet`) of the
atomic-state algorithm in which a node moves according to its state and its cut-off view. -/
lemma step_eq_stepSet (M : Machine Λ Q) (G : SimpleGraph V) (C : V → Q) (S : Set V) :
    step M G C S = SelfStabilization.stepSet (fun C v => M.δ (C v) (view M.β G C v)) S C := by
  funext v; simp [step, SelfStabilization.stepSet]

/-- Fair schedules activate every node infinitely often (`Cslib.StoneAge.Fair`). -/
lemma IsFair.stoneAgeFair {κ : Selection} {φ : Fairness} {σ : ℕ → Set V} (h : IsFair κ φ σ) :
    StoneAge.Fair σ :=
  fun v t => let ⟨s, hs, hv⟩ := h.2.1 v t; ⟨s, hs, hv⟩

end Bridge

end Cslib.DistributedAutomata
