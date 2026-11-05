import Papers.PODC2013.MessageAdversariesVsFD.Tasks
import Papers.PODC2013.MessageAdversariesVsFD.StronglyCorrect
import Cslib.Computability.Distributed.DynamicNetworks.Chain

/-!
# Counterexamples to Figure 1, Theorem 2 and Lemma 2 (three processes)

Processes are `Fin 3`; the paper's `p₁, p₂, p₃` are `0, 1, 2`. Solvability is the paper's
(Section 2.4): in `SMP_n[adv : AD]` every process must compute an output (`Solvable`).

* `tseen_solvable_tour`: `Tseen ∈ SMP_3[adv : TOUR]` (one round: one of `p₁`, `p₂` hears the
  other), hence `Tseen ∈ SMP_3[adv : SOURCE, TOUR]`.
* `tseen_not_solvable`: `Tseen ∉ SMP_3[adv : SOURCE, QUORUM]`: if only `p₃`'s messages are
  delivered (a pattern satisfying SOURCE and QUORUM), `p₁` never learns `p₂`'s input and vice
  versa, so both must output `alone`.
* Consequently (`not_quorum_stronger_than_tour`, `not_source_quorum_stronger_than_source_tour`)
  the arrows `SMP_n[adv : QUORUM] → SMP_n[adv : TOUR]` and
  `SMP_n[adv : SOURCE, QUORUM] → SMP_n[adv : SOURCE, TOUR]` of Figure 1, and the Conclusion's claim
  "`SMP_n[adv : QUORUM]` is stronger than `SMP_n[adv : TOUR]`", fail for `n = 3`.
* `tcons_not_solvable`: consensus between `p₁` and `p₂` (`Tcons`, `p₃` a helper) is not solvable
  in `SMP_3[adv : SOURCE, TOUR, QUORUM]`. `Tcons` is solvable in `ARW_{3,2}[Ω]` and in
  `AMP_{3,2}[Σ, Ω]` (standard, not formalized here: `p₁`, `p₂`, `p₃` run Ω-based consensus and
  `p₁`, `p₂` decide its value). Since `SOURCE ∩ TOUR ∩ QUORUM` is contained in both
  `SOURCE ∩ TOUR` and `SOURCE ∩ QUORUM`, `Tcons` is solvable in neither `SMP_3[adv : SOURCE, TOUR]`
  nor `SMP_3[adv : SOURCE, QUORUM]`: this refutes the inclusion
  `ARW_{n,n-1}[Ω] ⊆ SMP_n[adv : SOURCE, TOUR]` of Theorem 2 (Lemma 2) under the paper's semantics,
  and likewise any inclusion of `AMP_{n,n-1}[Σ, Ω]` into these models.
  The proof is a Santoro–Widmayer bivalence argument over the patterns `P*`: in every round `p₃`
  sends to everybody and hears nobody, and between `p₁` and `p₂` the adversary lets through
  `p₁ → p₂` (`G₀`), both messages (`Gb`), or `p₂ → p₁` (`G₁`). Every such pattern satisfies
  SOURCE (`s = p₃`), TOUR and QUORUM (`pat_N3_subset`). Successors via `G₀` and `Gb` look the
  same to `p₂` (extend with `G₁` forever), successors via `Gb` and `G₁` look the same to `p₁`
  (extend with `G₀` forever), so a bivalent prefix always has a bivalent successor; the initial
  prefix with inputs `(0, 1)` is bivalent; the limit pattern contradicts termination of `p₁`.
* `tcons_solvable_none`: non-vacuity, `Tcons ∈ SMP_3[adv : ∅]`.
-/

namespace Podc.MessageAdversariesVsFD

open Cslib.HeardOf

/-! ## Generic facts about runs and first outputs -/

section Generic

variable {P X Y σ : Type}

namespace Alg

variable (A : Alg P X Y σ)

/-- A process that decides has an output. -/
theorem output_isSome {x : P → X} {p : ℕ → Graph P} {i : P} (h : A.Decided x p i) :
    (A.output x p i).isSome := by
  unfold output; rw [dite_eq_left h]; exact Nat.find_spec h

/-- The output of `i` only depends on its states up to a round where it has an output. -/
theorem output_eq_of_prefix {x x' : P → X} {p p' : ℕ → Graph P} {i : P} {t : ℕ}
    (hrun : ∀ k ≤ t, A.run x p k i = A.run x' p' k i) (ht : (A.out (A.run x p t i)).isSome) :
    A.output x' p' i = A.output x p i := by
  have h : A.Decided x p i := ⟨t, ht⟩
  have h' : A.Decided x' p' i := ⟨t, by rw [← hrun t le_rfl]; exact ht⟩
  have hle : Nat.find h ≤ t := Nat.find_min' h ht
  have hle' : Nat.find h' ≤ Nat.find h :=
    Nat.find_min' h' (by rw [← hrun _ hle]; exact Nat.find_spec h)
  have hge : Nat.find h ≤ Nat.find h' :=
    Nat.find_min' h (by rw [hrun _ (hle'.trans hle)]; exact Nat.find_spec h')
  unfold output
  rw [dite_eq_left h, dite_eq_left h', le_antisymm hle' hge, hrun _ hle]

/-- The output of `i` only depends on its trajectory. -/
theorem output_eq_of_run_eq {x x' : P → X} {p p' : ℕ → Graph P} {i : P}
    (hrun : ∀ k, A.run x p k i = A.run x' p' k i) : A.output x p i = A.output x' p' i := by
  by_cases h : A.Decided x p i
  · obtain ⟨t, ht⟩ := h
    exact (A.output_eq_of_prefix (fun k _ => hrun k) ht).symm
  · have h' : ¬ A.Decided x' p' i := fun ⟨t, ht⟩ => h ⟨t, by rw [hrun]; exact ht⟩
    unfold output; rw [dite_eq_right h, dite_eq_right h']

/-- A process with no output initially and an output after round 1 outputs it. -/
theorem output_eq_one {x : P → X} {p : ℕ → Graph P} {i : P}
    (h0 : A.out (A.run x p 0 i) = none) (h1 : (A.out (A.run x p 1 i)).isSome) :
    A.output x p i = A.out (A.run x p 1 i) := by
  have h : A.Decided x p i := ⟨1, h1⟩
  have : Nat.find h = 1 :=
    (Nat.find_eq_iff h).2 ⟨h1, fun n hn => by interval_cases n; simp [h0]⟩
  unfold output; rw [dite_eq_left h, this]

end Alg

/-- Two patterns that coincide before round `t`, give the agents of `S` the same in-neighbours
in round `t`, and are constantly `H` afterwards, where `S` is closed in `H`: the agents of `S`
have the same trajectories. -/
theorem conf_eq_of_split {α τ : Type} {step : StepFn α τ} (C : α → τ) {q q' : ℕ → Graph α}
    {t : ℕ} {S : Set α} {H : Graph α} (hpre : ∀ k < t, q k = q' k)
    (ht : ∀ i ∈ S, SameIn (q t) (q' t) i) (hq : ∀ k, t < k → q k = H)
    (hq' : ∀ k, t < k → q' k = H) (hcl : ∀ i ∈ S, ∀ j, Hears H i j → j ∈ S) :
    ∀ k, ∀ i ∈ S, conf step C q k i = conf step C q' k i := by
  have hle : ∀ k ≤ t, conf step C q k = conf step C q' k :=
    fun k hk => conf_congr C (fun m hm => hpre m (by omega))
  have h1 : ∀ i ∈ S, conf step C q (t + 1) i = conf step C q' (t + 1) i := fun i hi => by
    rw [conf_succ, conf_succ, hle t le_rfl]
    exact next_eq_of_agree (ht i hi) (fun _ _ => rfl)
  intro k i hi
  rcases le_or_gt k t with hk | hk
  · rw [hle k hk]
  · obtain ⟨s, rfl⟩ : ∃ s, k = t + 1 + s := ⟨k - (t + 1), by omega⟩
    rw [conf_add C q (t + 1) s, conf_add C q' (t + 1) s]
    have hH : ∀ m, shift (t + 1) q' m = H := fun m => hq' _ (by omega)
    have hs : shift (t + 1) q = shift (t + 1) q' :=
      funext fun m => by rw [hH]; exact hq _ (by omega)
    rw [hs]
    exact conf_agree (p := shift (t + 1) q') (p' := shift (t + 1) q') S
      (fun _ _ _ => SameIn.refl _ _)
      (fun m i hi j hj => hcl i hi j (by rwa [hH] at hj)) h1 s i hi

end Generic


namespace Counterexample

/-! ## The three round graphs of the patterns `P*` -/

/-- Round graph: process `2` sends to everybody, process `0` sends to `1`, nothing else. -/
def G₀ : Graph (Fin 3) := fun j i => j = 2 ∨ (j = 0 ∧ i = 1)

/-- Round graph: process `2` sends to everybody, `0` and `1` hear each other. -/
def Gb : Graph (Fin 3) := fun j i => j = 2 ∨ (j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0)

/-- Round graph: process `2` sends to everybody, process `1` sends to `0`, nothing else. -/
def G₁ : Graph (Fin 3) := fun j i => j = 2 ∨ (j = 1 ∧ i = 0)

/-- The round graphs the adversary of the patterns `P*` may choose from. -/
def N3 : Set (Graph (Fin 3)) := {G₀, Gb, G₁}

/-- Process `2`'s messages are always delivered. -/
theorem N3_hears_two : ∀ G ∈ N3, ∀ i, Hears G i 2 := by
  rintro G (rfl | rfl | rfl) i <;> simp [Hears, G₀, Gb, G₁]

/-- Process `2` hears nobody but itself. -/
theorem N3_deaf_two : ∀ G ∈ N3, ∀ j, Hears G 2 j → j = 2 := by
  rintro G (rfl | rfl | rfl) j <;> simp only [Hears, G₀, Gb, G₁] <;> decide +revert

/-- The graphs of `N3` satisfy TOUR. -/
theorem N3_tour : ∀ G ∈ N3, ∀ i j : Fin 3, i ≠ j → G i j ∨ G j i := by
  rintro G (rfl | rfl | rfl) <;> simp only [G₀, Gb, G₁] <;> decide

/-- `G₀` and `Gb` look the same to processes `1` and `2`. -/
theorem sameIn_G₀_Gb : ∀ i ∈ ({1, 2} : Set (Fin 3)), SameIn G₀ Gb i := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SameIn, Hears, G₀, Gb]; decide

/-- `Gb` and `G₁` look the same to processes `0` and `2`. -/
theorem sameIn_Gb_G₁ : ∀ i ∈ ({0, 2} : Set (Fin 3)), SameIn Gb G₁ i := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SameIn, Hears, G₁, Gb]; decide

/-- In `G₁`, processes `1` and `2` only hear each other. -/
theorem closed_G₁ :
    ∀ i ∈ ({1, 2} : Set (Fin 3)), ∀ j, Hears G₁ i j → j ∈ ({1, 2} : Set (Fin 3)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Hears, G₁]; decide

/-- In `G₀`, processes `0` and `2` only hear each other. -/
theorem closed_G₀ :
    ∀ i ∈ ({0, 2} : Set (Fin 3)), ∀ j, Hears G₀ i j → j ∈ ({0, 2} : Set (Fin 3)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Hears, G₀]; decide

/-- Every pattern `P*` satisfies SOURCE, TOUR and QUORUM. -/
theorem pat_N3_subset : Pat N3 ⊆ (SOURCE ∩ TOUR ∩ QUORUM : Adversary (Fin 3)) := by
  intro q hq
  have hs : ∀ t, ∀ i, Hears (q t) i 2 := fun t => N3_hears_two _ (hq t)
  refine ⟨⟨⟨2, 0, fun t _ => hs t⟩, fun t i j hij => N3_tour _ (hq t) i j hij⟩,
    fun i j t t' => ⟨2, hs t i, hs t' j⟩, ⟨2, mem_SC_of_source (r₀ := 0) fun t _ => hs t⟩⟩

/-- `G₀ ∈ N3`. -/
theorem G₀_mem : G₀ ∈ N3 := Or.inl rfl
/-- `Gb ∈ N3`. -/
theorem Gb_mem : Gb ∈ N3 := Or.inr (Or.inl rfl)
/-- `G₁ ∈ N3`. -/
theorem G₁_mem : G₁ ∈ N3 := Or.inr (Or.inr rfl)

/-! ## Bivalence argument -/

/-- The pattern that follows `p` in rounds `≤ t` (graphs `p 0, …, p (t-1)`), then has graph `G`
in round `t + 1`, then `H` forever. -/
def ext (p : ℕ → Graph (Fin 3)) (t : ℕ) (G H : Graph (Fin 3)) : ℕ → Graph (Fin 3) :=
  fun k => if k < t then p k else if k = t then G else H

/-- `ext` follows `p` before round `t`. -/
theorem ext_lt {p : ℕ → Graph (Fin 3)} {t : ℕ} {G H : Graph (Fin 3)} {k : ℕ} (hk : k < t) :
    ext p t G H k = p k := by simp [ext, hk]

/-- `ext` uses `G` at index `t`. -/
theorem ext_self {p : ℕ → Graph (Fin 3)} {t : ℕ} {G H : Graph (Fin 3)} : ext p t G H t = G := by
  simp [ext]

/-- `ext` uses `H` after index `t`. -/
theorem ext_gt {p : ℕ → Graph (Fin 3)} {t : ℕ} {G H : Graph (Fin 3)} {k : ℕ} (hk : t < k) :
    ext p t G H k = H := by simp [ext, show ¬ k < t by omega, show k ≠ t by omega]

/-- `ext` preserves the patterns `P*`. -/
theorem ext_mem {p : ℕ → Graph (Fin 3)} (hp : p ∈ Pat N3) (t : ℕ) {G H : Graph (Fin 3)}
    (hG : G ∈ N3) (hH : H ∈ N3) : ext p t G H ∈ Pat N3 := by
  intro k; unfold ext; split_ifs
  · exact hp k
  · exact hG
  · exact hH

/-- Changing one round graph within `N3` preserves the patterns `P*`. -/
theorem update_mem {p : ℕ → Graph (Fin 3)} (hp : p ∈ Pat N3) (t : ℕ) {G : Graph (Fin 3)}
    (hG : G ∈ N3) : Function.update p t G ∈ Pat N3 := by
  intro k
  by_cases hk : k = t
  · subst hk; simpa using hG
  · rw [Function.update_of_ne hk]; exact hp k

/-- `ext p t G H` extends the prefix `Function.update p t G` of length `t + 1`. -/
theorem ext_eq_update {p : ℕ → Graph (Fin 3)} {t : ℕ} {G H : Graph (Fin 3)} :
    ∀ k < t + 1, ext p t G H k = Function.update p t G k := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · rw [ext_lt hk, Function.update_of_ne hk.ne]
  · rw [ext_self, Function.update_self]

section Bivalence

variable {σ : Type} (A : Alg (Fin 3) Bool Bool σ)

/-- Value `v` can still be decided (by process `0`) from the prefix of `p` of length `t`. -/
def CanDec (x : Fin 3 → Bool) (p : ℕ → Graph (Fin 3)) (t : ℕ) (v : Bool) : Prop :=
  ∃ q ∈ Pat N3, (∀ k < t, q k = p k) ∧ A.output x q 0 = some v

/-- The prefix of `p` of length `t` is bivalent. -/
def Biv (x : Fin 3 → Bool) (p : ℕ → Graph (Fin 3)) (t : ℕ) : Prop := ∀ v, CanDec A x p t v

variable {A} (hA : A.Solves (SOURCE ∩ TOUR ∩ QUORUM) Tcons)
include hA

/-- In every pattern `P*`, processes `0` and `1` output the same valid value. -/
theorem spec (x : Fin 3 → Bool) {q : ℕ → Graph (Fin 3)} (hq : q ∈ Pat N3) :
    ∃ v, A.output x q 0 = some v ∧ A.output x q 1 = some v ∧ (v = x 0 ∨ v = x 1) := by
  obtain ⟨hdec, O, ⟨hO1, hO2⟩, hOk⟩ := hA x trivial q (pat_N3_subset hq)
  obtain ⟨y0, hy0⟩ := Option.isSome_iff_exists.1 (A.output_isSome (hdec 0))
  obtain ⟨y1, hy1⟩ := Option.isSome_iff_exists.1 (A.output_isSome (hdec 1))
  exact ⟨O 0, by rw [hy0, hOk 0 y0 hy0], by rw [hy1, hO1, hOk 1 y1 hy1], hO2⟩

/-- Successors via `G₀` and `Gb`, continued with `G₁` forever, are indistinguishable for
process `1` (which then hears only itself and `2`). -/
theorem out_G₀_Gb (x : Fin 3 → Bool) {p : ℕ → Graph (Fin 3)} (hp : p ∈ Pat N3) (t : ℕ) :
    A.output x (ext p t G₀ G₁) 0 = A.output x (ext p t Gb G₁) 0 := by
  obtain ⟨v, h0, h1, -⟩ := spec hA x (ext_mem hp t G₀_mem G₁_mem)
  obtain ⟨v', h0', h1', -⟩ := spec hA x (ext_mem hp t Gb_mem G₁_mem)
  have : A.output x (ext p t G₀ G₁) 1 = A.output x (ext p t Gb G₁) 1 :=
    A.output_eq_of_run_eq fun k => conf_eq_of_split _ (S := {1, 2}) (H := G₁)
      (fun k hk => by rw [ext_lt hk, ext_lt hk]) (by rw [ext_self, ext_self]; exact sameIn_G₀_Gb)
      (fun k hk => ext_gt hk) (fun k hk => ext_gt hk) closed_G₁ k 1 (by simp)
  rw [h0, h0', ← h1, ← h1', this]

omit hA in
/-- Successors via `Gb` and `G₁`, continued with `G₀` forever, are indistinguishable for
process `0` (which then hears only itself and `2`). -/
theorem out_Gb_G₁ (x : Fin 3 → Bool) {p : ℕ → Graph (Fin 3)} (t : ℕ) :
    A.output x (ext p t Gb G₀) 0 = A.output x (ext p t G₁ G₀) 0 :=
  A.output_eq_of_run_eq fun k => conf_eq_of_split _ (S := {0, 2}) (H := G₀)
    (fun k hk => by rw [ext_lt hk, ext_lt hk]) (by rw [ext_self, ext_self]; exact sameIn_Gb_G₁)
    (fun k hk => ext_gt hk) (fun k hk => ext_gt hk) closed_G₀ k 0 (by simp)

/-- A prefix that is not bivalent is univalent. -/
theorem uni_of_not_biv {x : Fin 3 → Bool} {p : ℕ → Graph (Fin 3)} {t : ℕ}
    (h : ¬ Biv A x p t) :
    ∃ v, ∀ q ∈ Pat N3, (∀ k < t, q k = p k) → A.output x q 0 = some v := by
  obtain ⟨w, hw⟩ : ∃ w, ¬ CanDec A x p t w := not_forall.1 h
  refine ⟨!w, fun q hq hpre => ?_⟩
  obtain ⟨u, hu, -⟩ := spec hA x hq
  rw [hu]
  cases u <;> cases w <;> simp_all [CanDec]

/-- From a bivalent prefix, some one-round extension is bivalent. -/
theorem biv_step (x : Fin 3 → Bool) {p : ℕ → Graph (Fin 3)} (hp : p ∈ Pat N3) {t : ℕ}
    (hb : Biv A x p t) : ∃ G ∈ N3, Biv A x (Function.update p t G) (t + 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, h₀⟩ := uni_of_not_biv hA (hcon G₀ G₀_mem)
  obtain ⟨vb, hb'⟩ := uni_of_not_biv hA (hcon Gb Gb_mem)
  obtain ⟨v₁, h₁⟩ := uni_of_not_biv hA (hcon G₁ G₁_mem)
  have e1 : v₀ = vb := by
    have := out_G₀_Gb hA x hp t
    rw [h₀ _ (ext_mem hp t G₀_mem G₁_mem) ext_eq_update,
      hb' _ (ext_mem hp t Gb_mem G₁_mem) ext_eq_update] at this
    exact Option.some_injective _ this
  have e2 : vb = v₁ := by
    have := out_Gb_G₁ (A := A) x (p := p) t
    rw [hb' _ (ext_mem hp t Gb_mem G₀_mem) ext_eq_update,
      h₁ _ (ext_mem hp t G₁_mem G₀_mem) ext_eq_update] at this
    exact Option.some_injective _ this
  obtain ⟨q, hq, hpre, hout⟩ := hb (!v₀)
  have hq' : ∀ G, q t = G → ∀ k < t + 1, q k = Function.update p t G k := by
    intro G hqt k hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne hk.ne, hpre k hk]
    · rw [Function.update_self, hqt]
  rcases hq t with h | h | h
  · rw [h₀ q hq (hq' _ h)] at hout; cases v₀ <;> simp at hout
  · rw [hb' q hq (hq' _ h), ← e1] at hout; cases v₀ <;> simp at hout
  · rw [h₁ q hq (hq' _ h), ← e2, ← e1] at hout; cases v₀ <;> simp at hout

/-- The input vector `(0, 1, 0)`. -/
abbrev x₀ : Fin 3 → Bool := ![false, true, false]

/-- The initial configuration with inputs `(0, 1)` is bivalent. -/
theorem biv_init : Biv A x₀ (fun _ => G₀) 0 := by
  intro v
  cases v
  · refine ⟨fun _ => G₀, const_mem_pat G₀_mem, fun k hk => absurd hk (Nat.not_lt_zero _), ?_⟩
    have hrun : ∀ k, A.run x₀ (fun _ => G₀) k 0 = A.run ![false, false, false] (fun _ => G₀) k 0 :=
      fun k => conf_agree {0, 2} (fun _ _ _ => SameIn.refl _ _) (fun _ => closed_G₀)
        (by rintro i (rfl | rfl) <;> rfl) k 0 (by simp)
    rw [A.output_eq_of_run_eq hrun]
    obtain ⟨v, h0, -, hv⟩ := spec hA ![false, false, false] (const_mem_pat G₀_mem)
    rw [h0]; simp at hv; rw [hv]
  · refine ⟨fun _ => G₁, const_mem_pat G₁_mem, fun k hk => absurd hk (Nat.not_lt_zero _), ?_⟩
    have hrun : ∀ k, A.run x₀ (fun _ => G₁) k 1 = A.run ![true, true, false] (fun _ => G₁) k 1 :=
      fun k => conf_agree {1, 2} (fun _ _ _ => SameIn.refl _ _) (fun _ => closed_G₁)
        (by rintro i (rfl | rfl) <;> rfl) k 1 (by simp)
    obtain ⟨u, hu0, hu1, -⟩ := spec hA x₀ (const_mem_pat G₁_mem)
    obtain ⟨v, -, h1, hv⟩ := spec hA ![true, true, false] (const_mem_pat G₁_mem)
    rw [hu0, ← hu1, A.output_eq_of_run_eq hrun, h1]; simp at hv; rw [hv]

end Bivalence

end Counterexample

open Counterexample

/-- **Consensus between `p₁` and `p₂` is impossible in `SMP_3[adv : SOURCE, TOUR, QUORUM]`**
(every process must output). This refutes Theorem 2 / Lemma 2 of the paper under its own
semantics (`SOURCE ∩ TOUR ∩ QUORUM` is contained in `SOURCE ∩ TOUR` and in
`SOURCE ∩ QUORUM`): `Tcons` is solvable in `ARW_{3,2}[Ω]` and `AMP_{3,2}[Σ, Ω]` (with `p₃` as
helper).
Proof: bivalence (Santoro–Widmayer) over the patterns `P*`, where `p₃` broadcasts and hears
nobody, and in every round the adversary lets `p₁ → p₂`, `p₂ → p₁`, or both, through. -/
theorem tcons_not_solvable : ¬ Solvable (SOURCE ∩ TOUR ∩ QUORUM : Adversary (Fin 3)) Tcons := by
  rintro ⟨σ, A, hA⟩
  obtain ⟨s, Cs, h0, hadm, hmv, hinv⟩ := Cslib.HeardOf.Chain.exists_seq_of_step
    (Γ := (ℕ → Graph (Fin 3)) × ℕ) (M := Graph (Fin 3))
    (fun G c => (Function.update c.1 c.2 G, c.2 + 1)) N3
    (fun c => c.1 ∈ Pat N3 ∧ Biv A x₀ c.1 c.2) (fun _ => 0) 1
    (by
      rintro ⟨p, t⟩ ⟨hp, hb⟩
      obtain ⟨G, hG, hb'⟩ := biv_step hA x₀ hp hb
      exact ⟨G, hG, ⟨update_mem hp t hG, hb'⟩, by simp⟩)
    ((fun _ => G₀), 0) ⟨const_mem_pat G₀_mem, biv_init hA⟩
  have hCs : ∀ t, (Cs t).2 = t ∧ ∀ k < t, (Cs t).1 k = s k := by
    intro t
    induction t with
    | zero => simp [h0]
    | succ t ih =>
      rw [hmv]
      refine ⟨by simp [ih.1], fun k hk => ?_⟩
      simp only [ih.1]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [Function.update_of_ne hk.ne, ih.2 k hk]
      · rw [Function.update_self]
  have hs : s ∈ Pat N3 := hadm
  obtain ⟨v, hv, -⟩ := spec hA x₀ hs
  obtain ⟨t₀, ht₀⟩ : A.Decided x₀ s 0 := (hA x₀ trivial s (pat_N3_subset hs)).1 0
  have hb := (hinv (t₀ + 1)).1.2
  rw [(hCs _).1] at hb
  obtain ⟨q, hq, hpre, hout⟩ := hb (!v)
  have hrun : ∀ k ≤ t₀, A.run x₀ s k 0 = A.run x₀ q k 0 := fun k hk =>
    congrFun (conf_congr _ fun m hm => by rw [hpre m (by omega), (hCs _).2 m (by omega)]) 0
  rw [A.output_eq_of_prefix hrun ht₀, hv] at hout
  cases v <;> simp at hout

/-! ## `Tseen` is solvable in `SMP_3[adv : TOUR]` -/

namespace Counterexample

/-- Transition of the one-round algorithm for `Tseen`: a state is (own input, output). Process
`0` (resp. `1`) outputs the pair of inputs if it hears `1` (resp. `0`), else `alone`; process
`2` outputs `alone`. -/
def tseenStep : StepFn (Fin 3) (Bool × Option Seen) := fun i m =>
  let own := (m i).elim false Prod.fst
  (own, some (if i = 0 then (m 1).elim .alone (fun s => .pair own s.1)
    else if i = 1 then (m 0).elim .alone (fun s => .pair s.1 own) else .alone))

/-- The one-round algorithm for `Tseen`. -/
def tseenAlg : Alg (Fin 3) Bool Seen (Bool × Option Seen) where
  init _ b := (b, none)
  step := tseenStep
  out s := s.2

/-- The output of the `Tseen` algorithm is computed in round 1. -/
theorem tseenAlg_output (x : Fin 3 → Bool) (p : ℕ → Graph (Fin 3)) (i : Fin 3) :
    tseenAlg.output x p i = (tseenStep i (msgs (p 0) (fun j => (x j, none)) i)).2 :=
  tseenAlg.output_eq_one rfl (by simp [Alg.run, conf, next, tseenAlg, tseenStep])

open Classical in
/-- Output of process `0` of the `Tseen` algorithm. -/
theorem tseenAlg_output_zero (x : Fin 3 → Bool) (p : ℕ → Graph (Fin 3)) :
    tseenAlg.output x p 0 = some (if p 0 1 0 then .pair (x 0) (x 1) else .alone) := by
  rw [tseenAlg_output]; by_cases h : p 0 1 0 <;> simp [tseenStep, msgs, Hears, h]

open Classical in
/-- Output of process `1` of the `Tseen` algorithm. -/
theorem tseenAlg_output_one (x : Fin 3 → Bool) (p : ℕ → Graph (Fin 3)) :
    tseenAlg.output x p 1 = some (if p 0 0 1 then .pair (x 0) (x 1) else .alone) := by
  rw [tseenAlg_output]; by_cases h : p 0 0 1 <;> simp [tseenStep, msgs, Hears, h]

end Counterexample

/-- `Tseen` is solvable in `SMP_3[adv : TOUR]`: in round 1, one of `p₁`, `p₂` hears the other. -/
theorem tseen_solvable_tour : Solvable (TOUR : Adversary (Fin 3)) Tseen := by
  refine ⟨_, tseenAlg, fun x _ p hp => ⟨fun i => ⟨1, by simp [Alg.run, conf, next, tseenAlg,
    tseenStep]⟩, fun i => (tseenAlg.output x p i).getD .alone, ?_, fun i y h => by simp [h]⟩⟩
  have h01 : p 0 0 1 ∨ p 0 1 0 := hp 0 0 1 (by decide)
  simp only [Tseen, Set.mem_ofPred_eq, tseenAlg_output_zero, tseenAlg_output_one,
    Option.getD_some]
  refine ⟨by split_ifs <;> simp [Seen.Ok], by split_ifs <;> simp [Seen.Ok], ?_⟩
  rcases h01 with h | h
  · right; simp [h]
  · left; simp [h]

/-- `Tseen` is solvable in `SMP_3[adv : SOURCE, TOUR]`. -/
theorem tseen_solvable_source_tour : Solvable (SOURCE ∩ TOUR : Adversary (Fin 3)) Tseen :=
  tseen_solvable_tour.mono Set.inter_subset_right

/-! ## `Tseen` is not solvable in `SMP_3[adv : SOURCE, QUORUM]` -/

namespace Counterexample

/-- Only the messages of process `2` are delivered (to everybody, in every round). -/
def pSrc : ℕ → Graph (Fin 3) := fun _ j _ => j = 2

/-- `pSrc` satisfies SOURCE (`s = 2`) and QUORUM. -/
theorem pSrc_mem : pSrc ∈ (SOURCE ∩ QUORUM : Adversary (Fin 3)) := by
  have hs : ∀ t i, Hears (pSrc t) i 2 := fun t i => Or.inr rfl
  exact ⟨⟨2, 0, fun t _ => hs t⟩, fun i j t t' => ⟨2, hs t i, hs t' j⟩,
    ⟨2, mem_SC_of_source (r₀ := 0) fun t _ => hs t⟩⟩

end Counterexample

/-- `Tseen` is not solvable in `SMP_3[adv : SOURCE, QUORUM]` (every process must output): when
only `p₃`'s messages are delivered, `p₁` cannot learn `p₂`'s input and vice versa, so both must
output `alone`. -/
theorem tseen_not_solvable : ¬ Solvable (SOURCE ∩ QUORUM : Adversary (Fin 3)) Tseen := by
  rintro ⟨σ, A, hA⟩
  have hagree : ∀ (i : Fin 3) (x x' : Fin 3 → Bool), x i = x' i → x 2 = x' 2 →
      A.output x pSrc i = A.output x' pSrc i := fun i x x' hi h2 =>
    A.output_eq_of_run_eq fun k => conf_agree {i, 2} (fun _ _ _ => SameIn.refl _ _)
      (fun t k hk j hj => by
        rcases hj with rfl | h
        · exact hk
        · simp only [pSrc] at h; simp [h])
      (by rintro k (rfl | rfl) <;> simp [hi, h2]) k i (by simp)
  have okOf : ∀ x i y, A.output x pSrc i = some y → i ≠ 2 → Seen.Ok x y := fun x i y h hi => by
    obtain ⟨-, O, ⟨h0, h1, -⟩, hOk⟩ := hA x trivial pSrc pSrc_mem
    rw [← hOk i y h]
    fin_cases i
    exacts [h0, h1, absurd rfl hi]
  let x : Fin 3 → Bool := fun _ => false
  have key : ∀ i : Fin 3, i ≠ 2 → A.output x pSrc i = some .alone := by
    intro i hi2
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (A.output_isSome ((hA x trivial _ pSrc_mem).1 i))
    rw [hy]
    cases y with
    | alone => rfl
    | pair a b =>
      exfalso
      let x' : Fin 3 → Bool := fun j => decide (j ≠ i ∧ j ≠ 2)
      have h1 := okOf x i _ hy hi2
      have h2 := okOf x' i _ (by rw [← hagree i x x' (by simp [x, x']) (by simp [x, x']), hy]) hi2
      fin_cases i <;> simp_all [Seen.Ok, x, x']
  obtain ⟨-, O, ⟨-, -, hne⟩, hOk⟩ := hA x trivial pSrc pSrc_mem
  rw [hOk 0 _ (key 0 (by decide)), hOk 1 _ (key 1 (by decide))] at hne
  simp at hne

/-! ## Corollaries: the hierarchy of Figure 1 fails -/

/-- The arrow `SMP_n[adv : QUORUM] → SMP_n[adv : TOUR]` of Figure 1 (and the Conclusion's claim
that `SMP_n[adv : QUORUM]` is stronger than `SMP_n[adv : TOUR]`) fails for `n = 3`: `Tseen` is
solvable with TOUR but not with QUORUM. -/
theorem not_quorum_stronger_than_tour :
    ¬ ∀ T : Task (Fin 3) Bool Seen, Solvable TOUR T → Solvable QUORUM T := fun h =>
  tseen_not_solvable ((h Tseen tseen_solvable_tour).mono Set.inter_subset_right)

/-- The arrow `SMP_n[adv : SOURCE, QUORUM] → SMP_n[adv : SOURCE, TOUR]` of Figure 1 fails for
`n = 3`: `Tseen` is solvable with SOURCE and TOUR but not with SOURCE and QUORUM. -/
theorem not_source_quorum_stronger_than_source_tour :
    ¬ ∀ T : Task (Fin 3) Bool Seen,
      Solvable (SOURCE ∩ TOUR) T → Solvable (SOURCE ∩ QUORUM) T := fun h =>
  tseen_not_solvable (h Tseen tseen_solvable_source_tour)

/-! ## Non-vacuity: `Tcons` without message losses -/

namespace Counterexample

/-- One-round algorithm for `Tcons` without message losses: everybody outputs the input of `p₁`
received in round 1. -/
def consAlg : Alg (Fin 3) Bool Bool (Bool × Option Bool) where
  init _ b := (b, none)
  step _ m := ((m 0).elim false Prod.fst, some ((m 0).elim false Prod.fst))
  out s := s.2

end Counterexample

/-- `Tcons` is solvable in `SMP_3[adv : ∅]` (non-vacuity of the task and of `Solvable`). -/
theorem tcons_solvable_none : Solvable (advNone : Adversary (Fin 3)) Tcons := by
  refine ⟨_, consAlg, fun x _ p hp => ?_⟩
  have hout : ∀ i, consAlg.output x p i = some (x 0) := fun i => by
    rw [consAlg.output_eq_one rfl (by simp [Alg.run, conf, next, consAlg])]
    simp [Alg.run, conf, next, consAlg, msgs, Hears, hp 0 0 i]
  exact ⟨fun i => ⟨1, by simp [Alg.run, conf, next, consAlg]⟩, fun _ => x 0,
    ⟨rfl, Or.inl rfl⟩, fun i y h => by rw [hout] at h; exact Option.some_injective _ h⟩

end Podc.MessageAdversariesVsFD
