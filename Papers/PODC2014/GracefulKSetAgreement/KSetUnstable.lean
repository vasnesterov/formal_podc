import Papers.PODC2014.GracefulKSetAgreement.LossyLink

/-!
# `k`-set agreement is impossible under `VSRC(⌈k/2⌉ + 1, ∞)` (Theorems 8 and 9)

**Theorem 9.** For `1 < k < n` (and at least `k + 1` possible input values) no algorithm solves
`k`-set agreement under `VSRC(⌈k/2⌉ + 1, ∞)`, even if from some round on the communication graph
is constant with a single root component. **Theorem 8** (`VSRC(k, ∞)`) follows since
`⌈k/2⌉ + 1 ≤ k` for `k ≥ 2`.

## The construction

Processes `0, …, k` are split into `γ` groups `{a g, b g}` (`a g = b g` for a singleton group):
if `k` is even, group `0` is the singleton `{0}` and the others are pairs; if `k` is odd, all groups
are pairs. All other processes are never in a group. Given phase boundaries
`0 = T 0 ≤ T 1 ≤ … ≤ T γ` and words `w g`, the communication graph of round `t` (`phaseG`) is:
* group `g` is a **lossy link** with letter `w g t` in rounds `t < T g`,
* group `g` is **deaf** (both members hear nobody) in rounds `T g ≤ t < T (g + 1)`,
* afterwards, and always for the processes outside the groups, a process is **released**: it
  hears everybody.

In phase `j` (rounds `T j ≤ t < T (j + 1)`) the root components are `{a j}`, `{b j}` and one root
component per lossy group `g > j`: at most `|group 0| + γ - 1 ≤ ⌈k/2⌉ + 1` of them, every one a
clique of size `≤ 2` (so every vertex-stable root component is `D`-bounded for every `D ≥ 1`).
From round `T γ` on the graph is complete: a single root component, `H`-network-bounded for every
`H ≥ 1` (`phaseG_good`, `mem_thm9Adv`).

The words and boundaries are chosen group by group (`pair_cover`): for horizon `L = T g`, the
finite-horizon lossy-link lemma (`exists_lossy_disagree`, Lemma 17) yields a word of length `L`
after which the two members, deaf from `L` on, decide two different values; validity forces these
to be their two inputs, and `T (g + 1)` is the time by which both have decided. Since group `g` is
closed until `T (g + 1)`, its members behave exactly as in the lossy-link pattern
(`conf_eq_of_family`), so all `k + 1` inputs are decided in the final run.

The paper's proof uses Lemma 17 in its "∃ r'" form; this does not give a bad run *of the required
length* `L = T g` (fixed by the earlier phases). The fixed-horizon form fills this gap.
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

variable {P : Type}

/-- The communication graphs are eventually constant, and the final graph has a single root
component (the restriction "`G^r = G` for `r ≥ r_ST`, `G` with a single root" of Theorem 9). -/
def EvConstSingleRoot : Set (ℕ → Graph P) :=
  {ρ | ∃ r G, (∀ t ≥ r, ρ t = G) ∧ ∃! R, IsRootComp G R}

/-- The message adversary of Theorem 9: `VSRC(m, ∞)` restricted to eventually constant graphs with
a single root component. -/
def thm9Adv (D H m : ℕ) : Set (ℕ → Graph P) := VSRCkInf D H m ∩ EvConstSingleRoot

/-! ### Rounds with few clique root components -/

/-- `R` is a clique of `G`. -/
def IsClique (G : Graph P) (R : Set P) : Prop := ∀ p ∈ R, ∀ q ∈ R, p ≠ q → G p q

/-- A round graph with at most `m` root components, all cliques: witnessed by a finite family of
clique root components from which every process is reachable in at most one step. -/
def GoodRound (m : ℕ) (G : Graph P) : Prop :=
  ∃ 𝓡 : Set (Set P), 𝓡.Finite ∧ 𝓡.ncard ≤ m ∧ (∀ R ∈ 𝓡, IsRootComp G R ∧ IsClique G R) ∧
    ∀ v, ∃ R ∈ 𝓡, ∃ u ∈ R, u = v ∨ G u v

theorem GoodRound.roots {m : ℕ} {G : Graph P} (h : GoodRound m G) :
    (∀ R, IsRootComp G R → IsClique G R) ∧ {R | IsRootComp G R}.ncard ≤ m := by
  obtain ⟨𝓡, hfin, hcard, hR, hreach⟩ := h
  have hsub : {R | IsRootComp G R} ⊆ 𝓡 := fun S hS =>
    isRootComp_mem_of_reach (fun R hR' => (hR R hR').1) (fun v => by
      obtain ⟨R, hR', u, hu, huv⟩ := hreach v
      refine ⟨R, hR', u, hu, ?_⟩
      rcases huv with rfl | huv
      · exact .rfl
      · exact Digraph.Adj.reachable (G := Digraph.mk G) huv) hS
  exact ⟨fun R hR' => (hR R (hsub hR')).2, (Set.ncard_le_ncard hsub hfin).trans hcard⟩

theorem journey_of_clique {ρ : ℕ → Graph P} {R : Set P} {x D : ℕ} (hD : 1 ≤ D)
    (h : IsClique (ρ x) R) {p q : P} (hp : p ∈ R) (hq : q ∈ R) : Journey ρ x p (x + D) q := by
  by_cases hpq : p = q
  · subst hpq; exact Journey.self (by omega)
  · exact (Journey.single (E := ρ) (h p hp q hq hpq)).trans (Journey.self (by omega))

/-- **Membership in the adversary of Theorem 9.** Every round has at most `m` root components, all
cliques, and from round `T` on the graph is a constant `Gf` with a root component `R` from which
every process is reached in one step. -/
theorem mem_thm9Adv {m D H : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H) {ρ : ℕ → Graph P}
    (hgood : ∀ t, GoodRound m (ρ t)) {T : ℕ} {Gf : Graph P} {R : Set P}
    (htail : ∀ t, T ≤ t → ρ t = Gf) (hR : IsRootComp Gf R)
    (hreach : ∀ v, ∃ u ∈ R, u = v ∨ Gf u v) : ρ ∈ thm9Adv D H m := by
  have huniq : ∀ S, IsRootComp Gf S → S = R := by
    intro S hS
    obtain ⟨v, hv⟩ := hS.nonempty
    obtain ⟨u, hu, huv⟩ := hreach v
    have huS : u ∈ S := by
      rcases huv with rfl | huv
      · exact hv
      · exact hS.closed v hv u huv
    exact (hR.eq_of_mem hS hu huS).symm
  refine ⟨⟨fun t => (hgood t).roots.2, fun R' a b hV => ?_, T, {R}, by simp, by simpa using hm,
    fun R' hR' t ht => ?_, fun x hx q => ?_, fun t ht R' hR' => ?_⟩, T, Gf, htail, R, hR,
    fun S hS => huniq S hS⟩
  · unfold DBounded
    by_cases hab : b + 1 < a + D
    · exact Or.inl hab
    · refine Or.inr fun x hax hxb p hp q hq => journey_of_clique hD ?_ hp hq
      exact (hgood x).roots.1 R' (hV x hax (by omega))
  · rw [Set.mem_singleton_iff] at hR'; subst hR'; rw [htail t ht]; exact hR
  · obtain ⟨u, hu, huq⟩ := hreach q
    refine ⟨R, rfl, u, hu, ?_⟩
    rcases huq with rfl | huq
    · exact Journey.self (by omega)
    · exact (Journey.single (E := ρ) (by rw [htail x hx]; exact huq)).trans
        (Journey.self (by omega))
  · rw [htail t ht] at hR'; exact huniq R' hR'

/-! ### Building blocks: stars, complete graphs, lossy and deaf groups -/

/-- The star from `c`: `c` hears nobody, everybody else hears everybody. -/
def starG (c : P) : Graph P := fun _ v => v ≠ c

/-- The complete graph. -/
def completeG : Graph P := fun _ _ => True

theorem clique_singleton (G : Graph P) (c : P) : IsClique G {c} := by
  rintro p rfl q rfl h; exact absurd rfl h

theorem deaf_root {G : Graph P} {c : P} (h : Deaf G c) : IsRootComp G {c} ∧ IsClique G {c} :=
  ⟨isRootComp_singleton_iff.mpr h, clique_singleton G c⟩

theorem star_root (c : P) : IsRootComp (starG c) {c} :=
  isRootComp_singleton_iff.mpr fun _ hj => absurd rfl hj

theorem star_reach (c v : P) : ∃ u ∈ ({c} : Set P), u = v ∨ starG c u v := by
  by_cases h : v = c
  · exact ⟨c, rfl, Or.inl h.symm⟩
  · exact ⟨c, rfl, Or.inr h⟩

theorem goodRound_star {m : ℕ} (hm : 1 ≤ m) (c : P) : GoodRound m (starG c) := by
  refine ⟨{{c}}, Set.finite_singleton _, by simpa using hm, fun R hR => ?_,
    fun v => ⟨{c}, rfl, star_reach c v⟩⟩
  rw [Set.mem_singleton_iff] at hR; subst hR
  exact ⟨star_root c, clique_singleton _ c⟩

theorem complete_root [Nonempty P] : IsRootComp (completeG : Graph P) Set.univ :=
  isRootComp_iff.mpr ⟨Set.univ_nonempty, fun _ _ _ _ => trivial,
    fun _ _ _ _ => Digraph.Adj.reachable (G := Digraph.mk completeG) trivial⟩

theorem goodRound_complete [Nonempty P] {m : ℕ} (hm : 1 ≤ m) :
    GoodRound m (completeG : Graph P) := by
  refine ⟨{Set.univ}, Set.finite_singleton _, by simpa using hm, fun R hR => ?_,
    fun v => ⟨Set.univ, rfl, v, trivial, Or.inl rfl⟩⟩
  rw [Set.mem_singleton_iff] at hR; subst hR
  exact ⟨complete_root, fun _ _ _ _ _ => trivial⟩

/-- The root component of a lossy-link round between `a` and `b`. -/
def lroot (a b : P) : Lk → Set P
  | .hearA => {b}
  | .hearB => {a}
  | .both => {a, b}

/-- A group `{a, b}` whose in-edges are those of a lossy-link round contains exactly one root
component, a clique, which reaches both members in at most one step. -/
theorem lroot_spec {G : Graph P} {a b : P} {ℓ : Lk}
    (hin : ∀ u v, (v = a ∨ v = b) → (G u v ↔ linkG a b ℓ u v)) :
    IsRootComp G (lroot a b ℓ) ∧ IsClique G (lroot a b ℓ) ∧
      ∀ v, (v = a ∨ v = b) → ∃ u ∈ lroot a b ℓ, u = v ∨ G u v := by
  cases ℓ with
  | hearA =>
    refine ⟨isRootComp_singleton_iff.mpr fun j hj => ?_, clique_singleton _ _, fun v hv => ?_⟩
    · rcases (hin j b (Or.inr rfl)).1 hj with ⟨-, h, -⟩ | ⟨-, -, h⟩
      · exact h
      · exact h.elim
    · rcases hv with rfl | rfl
      · exact ⟨b, rfl, Or.inr ((hin b v (Or.inl rfl)).2 (Or.inl ⟨rfl, rfl, trivial⟩))⟩
      · exact ⟨v, rfl, Or.inl rfl⟩
  | hearB =>
    refine ⟨isRootComp_singleton_iff.mpr fun j hj => ?_, clique_singleton _ _, fun v hv => ?_⟩
    · rcases (hin j a (Or.inl rfl)).1 hj with ⟨-, -, h⟩ | ⟨-, h, -⟩
      · exact h.elim
      · exact h
    · rcases hv with rfl | rfl
      · exact ⟨v, rfl, Or.inl rfl⟩
      · exact ⟨a, rfl, Or.inr ((hin a v (Or.inr rfl)).2 (Or.inr ⟨rfl, rfl, trivial⟩))⟩
  | both =>
    have hab : G a b := (hin a b (Or.inr rfl)).2 (Or.inr ⟨rfl, rfl, trivial⟩)
    have hba : G b a := (hin b a (Or.inl rfl)).2 (Or.inl ⟨rfl, rfl, trivial⟩)
    refine ⟨isRootComp_pair hab hba fun u z hz h => (linkG_mem ((hin u z hz).1 h)).1,
      fun p hp q hq hpq => ?_, fun v hv => ⟨v, by simp only [lroot, Set.mem_insert_iff, Set.mem_singleton_iff]; exact hv,
        Or.inl rfl⟩⟩
    simp only [lroot, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact hab
    · exact hba
    · exact absurd rfl hpq

/-- One round in which only the group `{a, b}` is closed (a lossy link with letter `ℓ`) and every
other process hears everybody. -/
def soloG (a b : P) (ℓ : Lk) : Graph P := fun u v => linkG a b ℓ u v ∨ (v ≠ a ∧ v ≠ b)

theorem goodRound_solo {m : ℕ} (hm : 1 ≤ m) (a b : P) (ℓ : Lk) : GoodRound m (soloG a b ℓ) := by
  have hin : ∀ u v, (v = a ∨ v = b) → (soloG a b ℓ u v ↔ linkG a b ℓ u v) := by
    intro u v hv
    refine ⟨fun h => h.resolve_right fun ⟨h1, h2⟩ => ?_, Or.inl⟩
    rcases hv with rfl | rfl
    · exact h1 rfl
    · exact h2 rfl
  obtain ⟨hR, hc, hreach⟩ := lroot_spec hin
  refine ⟨{lroot a b ℓ}, Set.finite_singleton _, by simpa using hm, fun R hR' => ?_, fun v => ?_⟩
  · rw [Set.mem_singleton_iff] at hR'; subst hR'; exact ⟨hR, hc⟩
  · by_cases hv : v = a ∨ v = b
    · obtain ⟨u, hu, h⟩ := hreach v hv
      exact ⟨_, rfl, u, hu, h⟩
    · obtain ⟨u, hu⟩ := hR.nonempty
      exact ⟨_, rfl, u, hu, Or.inr (Or.inr ⟨fun h => hv (Or.inl h), fun h => hv (Or.inr h)⟩)⟩

/-- The pattern used to show that the members of a lossy-link group decide: the group `{a, b}` is
a lossy link (word `w`) until round `L`, everybody else hears everybody; from round `L` on the
star from `c`. -/
def soloPat (a b : P) (w : ℕ → Lk) (L : ℕ) (c : P) : ℕ → Graph P :=
  fun t => if t < L then soloG a b (w t) else starG c

theorem soloPat_mem {m D H : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H) (a b : P) (w : ℕ → Lk)
    (L : ℕ) (c : P) : soloPat a b w L c ∈ thm9Adv D H m := by
  refine mem_thm9Adv hm hD hH (fun t => ?_) (T := L) (fun t ht => ?_) (star_root c) (star_reach c)
  · unfold soloPat
    split_ifs
    · exact goodRound_solo hm _ _ _
    · exact goodRound_star hm c
  · simp [soloPat, show ¬ t < L by omega]

/-- In `soloPat a b w L c` the process `c ∈ {a, b}` behaves exactly as in the lossy-link pattern
`lossyPat a b w L`. -/
theorem conf_soloPat_eq {σ : Type} (step : StepFn P σ) (C : P → σ) {a b c : P} (hc : c = a ∨ c = b)
    (w : ℕ → Lk) (L t : ℕ) :
    conf step C (soloPat a b w L c) t c = conf step C (lossyPat a b w L) t c := by
  refine conf_eq_of_family step (fun t => {v | v = c ∨ (t ≤ L ∧ (v = a ∨ v = b))})
    (fun _ _ => rfl) ?_ ?_ t c (Or.inl rfl)
  · intro t i hi j
    simp only [Set.mem_ofPred_eq] at hi
    by_cases ht : t < L
    · have hi' : i = a ∨ i = b := by
        rcases hi with rfl | ⟨-, h⟩
        · exact hc
        · exact h
      simp only [Hears, soloPat, lossyPat, ht, ite_true, true_and, soloG]
      constructor
      · rintro (h | h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr h
        · rcases hi' with rfl | rfl
          · exact absurd rfl h1
          · exact absurd rfl h2
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · have hi' : i = c := by
        rcases hi with h | ⟨h, -⟩
        · exact h
        · omega
      subst hi'
      simp [Hears, soloPat, lossyPat, ht, starG]
  · intro t i hi j hj
    simp only [Set.mem_ofPred_eq] at hi ⊢
    by_cases ht : t < L
    · have hi' : i = a ∨ i = b := by
        rcases hi with rfl | ⟨-, h⟩
        · exact hc
        · exact h
      simp only [Hears, soloPat, ht, ite_true, soloG] at hj
      rcases hj with rfl | h | ⟨h1, h2⟩
      · exact Or.inr ⟨by omega, hi'⟩
      · exact Or.inr ⟨by omega, (linkG_mem h).1⟩
      · rcases hi' with rfl | rfl
        · exact absurd rfl h1
        · exact absurd rfl h2
    · have hi' : i = c := by
        rcases hi with h | ⟨h, -⟩
        · exact h
        · omega
      subst hi'
      simp only [Hears, soloPat, ht, ite_false, starG] at hj
      rcases hj with rfl | h
      · exact Or.inl rfl
      · exact absurd rfl h

/-- A lossy-link group is closed. -/
theorem lossyPat_closed {a b : P} {w : ℕ → Lk} {L t : ℕ} {i j : P} (hi : i = a ∨ i = b)
    (h : Hears (lossyPat a b w L t) i j) : j = a ∨ j = b := by
  rcases h with rfl | ⟨-, h⟩
  · exact hi
  · exact (linkG_mem h).1

/-! ### One lossy-link group -/

section Pair

variable {V σ : Type} {A : Alg P V σ} {k D H m : ℕ}

/-- The members of a lossy-link group decide (by termination in `soloPat`). -/
theorem lossy_term (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H) (hA : A.SolvesKSet k (thm9Adv D H m))
    (x : P → V) {a b c : P} (hc : c = a ∨ c = b) (w : ℕ → Lk) (L : ℕ) :
    ∃ v, A.DecC (A.initC x) (lossyPat a b w L) c v := by
  obtain ⟨v, t, ht⟩ := (hA x _ (soloPat_mem hm hD hH a b w L c)).2.2 c
  refine ⟨v, t, ?_⟩
  unfold Alg.run at ht
  rwa [conf_soloPat_eq _ _ hc] at ht

/-- The members of a lossy-link group decide one of their two inputs. -/
theorem lossy_valid (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H) (hA : A.SolvesKSet k (thm9Adv D H m))
    (x : P → V) {a b c : P} (hc : c = a ∨ c = b) (w : ℕ → Lk) (L : ℕ) {v : V}
    (h : A.DecC (A.initC x) (lossyPat a b w L) c v) : v = x a ∨ v = x b := by
  classical
  let x' : P → V := fun j => if j = a ∨ j = b then x j else x a
  have h' : A.Decides x' (soloPat a b w L c) c v := by
    obtain ⟨t, ht⟩ := h
    refine ⟨t, ?_⟩
    unfold Alg.run
    rw [conf_soloPat_eq _ _ hc]
    rw [conf_agree (C := A.initC x') (C' := A.initC x) {j | j = a ∨ j = b} (fun _ _ _ => SameIn.refl _ _)
      (fun _ i hi j hj => lossyPat_closed hi hj)
      (fun i hi => by simp [Alg.initC, x', show i = a ∨ i = b from hi]) t c hc]
    exact ht
  obtain ⟨j, hj⟩ := (hA x' _ (soloPat_mem hm hD hH a b w L c)).2.1 c v h'
  simp only [x'] at hj
  split_ifs at hj with hj'
  · rcases hj' with rfl | rfl
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm
  · exact Or.inl hj.symm

/-- A member that is deaf in the lossy link decides its own input. -/
theorem lossy_deafA (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H) (hA : A.SolvesKSet k (thm9Adv D H m))
    (x : P → V) {a b : P} (hab : a ≠ b) (L : ℕ) :
    A.DecC (A.initC x) (lossyPat a b (fun _ => .hearB) L) a (x a) := by
  obtain ⟨t, ht⟩ := A.decides_own_of_deaf hA x (soloPat_mem hm hD hH a b (fun _ => .hearB) L a)
    (i := a) (fun t => by
      unfold soloPat
      split_ifs
      · rintro j ((⟨-, -, h⟩ | ⟨h, -, -⟩) | ⟨h, -⟩)
        · exact h.elim
        · exact absurd h hab
        · exact absurd rfl h
      · intro j hj; exact absurd rfl hj)
  refine ⟨t, ?_⟩
  unfold Alg.run at ht
  rwa [conf_soloPat_eq _ _ (Or.inl rfl)] at ht

theorem lossy_deafB (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H) (hA : A.SolvesKSet k (thm9Adv D H m))
    (x : P → V) {a b : P} (hab : a ≠ b) (L : ℕ) :
    A.DecC (A.initC x) (lossyPat a b (fun _ => .hearA) L) b (x b) := by
  obtain ⟨t, ht⟩ := A.decides_own_of_deaf hA x (soloPat_mem hm hD hH a b (fun _ => .hearA) L b)
    (i := b) (fun t => by
      unfold soloPat
      split_ifs
      · rintro j ((⟨h, -, -⟩ | ⟨-, -, h⟩) | ⟨-, h⟩)
        · exact absurd h.symm hab
        · exact h.elim
        · exact absurd rfl h
      · intro j hj; exact absurd rfl hj)
  refine ⟨t, ?_⟩
  unfold Alg.run at ht
  rwa [conf_soloPat_eq _ _ (Or.inr rfl)] at ht

/-- **One phase of Theorem 9.** For every horizon `L` there is a word of length `L` such that,
if the group `{a, b}` is a lossy link until `L` and deaf afterwards, both inputs of the group are
decided (by members of the group) by some time `t₀`. For a pair this is Lemma 17
(`exists_lossy_disagree`). -/
theorem pair_cover (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H) (hA : A.SolvesKSet k (thm9Adv D H m))
    (x : P → V) {a b : P} (hx : a ≠ b → x a ≠ x b) (L : ℕ) :
    ∃ w t₀, ∀ i, (i = a ∨ i = b) → ∃ j, (j = a ∨ j = b) ∧
      A.dec (A.run x (lossyPat a b w L) t₀ j) = some (x i) := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨v, t, ht⟩ := lossy_term hm hD hH hA x (Or.inl rfl) (fun _ => .both) L
    have hv := lossy_valid hm hD hH hA x (Or.inl rfl) (fun _ => .both) L ⟨t, ht⟩
    have hv' : v = x a := hv.elim id id
    refine ⟨fun _ => .both, t, fun i hi => ⟨a, Or.inl rfl, ?_⟩⟩
    have : i = a := hi.elim id id
    subst this hv'
    exact ht
  · obtain ⟨w, v, v', hne, ⟨t, ht⟩, ⟨t', ht'⟩⟩ := exists_lossy_disagree A hab L (A.initC x) (hx hab)
      (lossy_deafA hm hD hH hA x hab L) (lossy_deafB hm hD hH hA x hab L)
      (fun w => ⟨lossy_term hm hD hH hA x (Or.inl rfl) w L,
        lossy_term hm hD hH hA x (Or.inr rfl) w L⟩)
    have hv := lossy_valid hm hD hH hA x (Or.inl rfl) w L ⟨t, ht⟩
    have hv' := lossy_valid hm hD hH hA x (Or.inr rfl) w L ⟨t', ht'⟩
    have h1 := A.dec_conf_mono ht (le_max_left t t')
    have h2 := A.dec_conf_mono ht' (le_max_right t t')
    have hxab := hx hab
    refine ⟨w, max t t', fun i hi => ?_⟩
    unfold Alg.run
    rcases hi with rfl | rfl
    · by_cases hva : v = x i
      · exact ⟨i, Or.inl rfl, hva ▸ h1⟩
      · have : v' = x i := by
          rcases hv with h | h
          · exact absurd h hva
          · rcases hv' with h' | h'
            · exact h'
            · exact absurd (h.trans h'.symm) hne
        exact ⟨b, Or.inr rfl, this ▸ h2⟩
    · by_cases hva : v = x i
      · exact ⟨a, Or.inl rfl, hva ▸ h1⟩
      · have : v' = x i := by
          rcases hv with h | h
          · rcases hv' with h' | h'
            · exact absurd (h.trans h'.symm) hne
            · exact h'
          · exact absurd h hva
        exact ⟨i, Or.inr rfl, this ▸ h2⟩

end Pair

/-! ### The phase construction -/

section Phases

variable (γ : ℕ) (a b : ℕ → P) (T : ℕ → ℕ) (w : ℕ → ℕ → Lk)

/-- `v` is released at time `t`: every group containing `v` has finished its deaf phase. -/
def Released (t : ℕ) (v : P) : Prop := ∀ g < γ, (v = a g ∨ v = b g) → T (g + 1) ≤ t

/-- The communication graph of round `t` of the construction of Theorem 9: group `g` is a lossy
link (letter `w g t`) in rounds `t < T g`, deaf in rounds `T g ≤ t < T (g + 1)`, and released
(hears everybody) afterwards; processes outside the groups are always released. -/
def phaseG (t : ℕ) : Graph P := fun u v =>
  Released γ a b T t v ∨ ∃ g < γ, t < T g ∧ linkG (a g) (b g) (w g t) u v

variable {γ a b T w}

/-- The groups are pairwise disjoint. -/
def GroupsDisjoint (γ : ℕ) (a b : ℕ → P) : Prop :=
  ∀ g < γ, ∀ g' < γ, ∀ u, (u = a g ∨ u = b g) → (u = a g' ∨ u = b g') → g = g'

/-- Before its release, a member of group `g` hears exactly what the lossy-link pattern of the
group prescribes. -/
theorem phaseG_in (hdist : GroupsDisjoint γ a b) {g : ℕ} (hg : g < γ) {v : P}
    (hv : v = a g ∨ v = b g) {t : ℕ} (ht : t < T (g + 1)) (u : P) :
    phaseG γ a b T w t u v ↔ t < T g ∧ linkG (a g) (b g) (w g t) u v := by
  constructor
  · rintro (hr | ⟨g', hg', ht', hl⟩)
    · exact absurd (hr g hg hv) (by omega)
    · obtain rfl := hdist g' hg' g hg v (linkG_mem hl).2 hv
      exact ⟨ht', hl⟩
  · exact fun h => Or.inr ⟨g, hg, h⟩

/-- After the last phase the graph is complete. -/
theorem phaseG_tail (hmono : Monotone T) {t : ℕ} (ht : T γ ≤ t) :
    phaseG γ a b T w t = completeG := by
  funext u v
  exact propext ⟨fun _ => trivial, fun _ => Or.inl fun g hg _ =>
    (hmono (show g + 1 ≤ γ by omega)).trans ht⟩

/-- **Every round of the construction has at most `m` root components, all cliques.** -/
theorem phaseG_good [Nonempty P] {m : ℕ} (hm : 1 ≤ m) (hdist : GroupsDisjoint γ a b)
    (hT0 : T 0 = 0) (hmono : Monotone T) (hγm : γ ≤ m) (h0m : a 0 ≠ b 0 → γ + 1 ≤ m) (t : ℕ) :
    GoodRound m (phaseG γ a b T w t) := by
  classical
  by_cases htγ : T γ ≤ t
  · rw [phaseG_tail hmono htγ]; exact goodRound_complete hm
  push Not at htγ
  -- the current phase `j`
  obtain ⟨j, hj1, hj0, hjγ⟩ : ∃ j, t < T (j + 1) ∧ T j ≤ t ∧ j < γ := by
    have hγ : γ ≠ 0 := by rintro rfl; omega
    have hex : ∃ j, t < T (j + 1) := ⟨γ - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
      · rw [h, hT0]; omega
      · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
        rw [Nat.sub_add_cancel h] at this
        omega
    · have := Nat.find_min' hex (show t < T (γ - 1 + 1) by rwa [Nat.sub_add_cancel (by omega)])
      omega
  have hrel : ∀ v g, g < γ → g < j → (v = a g ∨ v = b g) → Released γ a b T t v := by
    intro v g hg hgj hv g' hg' hv'
    obtain rfl := hdist g hg g' hg' v hv hv'
    exact (hmono (show g + 1 ≤ j by omega)).trans hj0
  have hdeaf : ∀ v, (v = a j ∨ v = b j) → Deaf (phaseG γ a b T w t) v := by
    intro v hv u hu
    have := ((phaseG_in hdist hjγ hv hj1 u).1 hu).1
    omega
  have hlossy : ∀ g, j < g → g < γ → ∀ u v, (v = a g ∨ v = b g) →
      (phaseG γ a b T w t u v ↔ linkG (a g) (b g) (w g t) u v) := by
    intro g hjg hg u v hv
    have h1 : t < T g := lt_of_lt_of_le hj1 (hmono (show j + 1 ≤ g by omega))
    rw [phaseG_in hdist hg hv (lt_of_lt_of_le h1 (hmono (Nat.le_succ g)))]
    exact ⟨fun h => h.2, fun h => ⟨h1, h⟩⟩
  refine ⟨{{a j}, {b j}} ∪ (fun g => lroot (a g) (b g) (w g t)) '' Set.Ioo j γ,
    ((Set.finite_singleton _).insert _).union ((Set.finite_Ioo j γ).image _), ?_, ?_, ?_⟩
  · have hpair : ({{a j}, {b j}} : Set (Set P)).ncard ≤ if a j = b j then 1 else 2 := by
      split_ifs with h
      · rw [h]; simp
      · exact (Set.ncard_insert_le _ _).trans (by simp)
    have himg : ((fun g => lroot (a g) (b g) (w g t)) '' Set.Ioo j γ).ncard ≤ γ - j - 1 := by
      refine (Set.ncard_image_le (Set.finite_Ioo j γ)).trans ?_
      rw [← Finset.coe_Ioo, Set.ncard_coe_finset, Nat.card_Ioo]
    refine (Set.ncard_union_le _ _).trans ((add_le_add hpair himg).trans ?_)
    split_ifs with h
    · omega
    · by_cases hj : j = 0
      · subst hj; have := h0m h; omega
      · omega
  · intro R hR
    rcases hR with hR | ⟨g, ⟨hjg, hgγ⟩, rfl⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hR
      rcases hR with rfl | rfl
      · exact deaf_root (hdeaf _ (Or.inl rfl))
      · exact deaf_root (hdeaf _ (Or.inr rfl))
    · obtain ⟨h1, h2, -⟩ := lroot_spec (hlossy g hjg hgγ)
      exact ⟨h1, h2⟩
  · intro v
    by_cases hv : ∃ g < γ, v = a g ∨ v = b g
    · obtain ⟨g, hg, hv⟩ := hv
      rcases lt_trichotomy g j with hgj | rfl | hgj
      · exact ⟨{a j}, by simp, a j, rfl, Or.inr (Or.inl (hrel v g hg hgj hv))⟩
      · rcases hv with rfl | rfl
        · exact ⟨{a g}, by simp, _, rfl, Or.inl rfl⟩
        · exact ⟨{b g}, by simp, _, rfl, Or.inl rfl⟩
      · obtain ⟨u, hu, h⟩ := (lroot_spec (hlossy g hgj hg)).2.2 v hv
        exact ⟨_, Or.inr ⟨g, ⟨hgj, hg⟩, rfl⟩, u, hu, h⟩
    · exact ⟨{a j}, by simp, a j, rfl, Or.inr (Or.inl fun g hg hv' => absurd ⟨g, hg, hv'⟩ hv)⟩

end Phases

/-! ### The generic impossibility argument -/

section Generic

variable {V σ : Type}

/-- **Theorem 9, generic form.** Let `γ` disjoint groups `{a g, b g}` (`a g = b g` allowed) with
`γ ≤ m`, and `γ + 1 ≤ m` if the first group is a pair, and inputs that differ inside each pair.
If `A` solves `k`-set agreement under `VSRC(m, ∞)` restricted to eventually constant graphs with a
single root, then some run of this adversary decides all inputs of all groups. -/
theorem thm9_cover [Nonempty P] {k D H m : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (A : Alg P V σ) (hA : A.SolvesKSet k (thm9Adv D H m)) (γ : ℕ) (a b : ℕ → P)
    (hdist : GroupsDisjoint γ a b) (hγm : γ ≤ m) (h0m : a 0 ≠ b 0 → γ + 1 ≤ m) (x : P → V)
    (hx : ∀ g < γ, a g ≠ b g → x (a g) ≠ x (b g)) :
    ∃ ρ ∈ thm9Adv D H m, ∀ g < γ, ∀ i, (i = a g ∨ i = b g) → ∃ j, A.Decides x ρ j (x i) := by
  -- the per-group choice of word and decision time, for every horizon `L`
  have hpc : ∀ g L, ∃ (w : ℕ → Lk) (t₀ : ℕ), g < γ → ∀ i, (i = a g ∨ i = b g) →
      ∃ j, (j = a g ∨ j = b g) ∧
        A.dec (A.run x (lossyPat (a g) (b g) w L) t₀ j) = some (x i) := by
    intro g L
    by_cases hg : g < γ
    · obtain ⟨w, t₀, h⟩ := pair_cover hm hD hH hA x (hx g hg) L
      exact ⟨w, t₀, fun _ => h⟩
    · exact ⟨fun _ => .both, 0, fun h => absurd h hg⟩
  choose W TT hW using hpc
  -- the phase boundaries: `T (g + 1)` is when group `g` has decided
  let T : ℕ → ℕ := fun g => Nat.rec 0 (fun g Tg => max Tg (TT g Tg)) g
  have hT : ∀ g, T (g + 1) = max (T g) (TT g (T g)) := fun _ => rfl
  have hmono : Monotone T := monotone_nat_of_le_succ fun g => (hT g).symm ▸ le_max_left _ _
  let w : ℕ → ℕ → Lk := fun g => W g (T g)
  refine ⟨phaseG γ a b T w, ?_, fun g hg i hi => ?_⟩
  · exact mem_thm9Adv hm hD hH (phaseG_good hm hdist rfl hmono hγm h0m)
      (fun t ht => phaseG_tail hmono ht) complete_root (fun v => ⟨v, trivial, Or.inl rfl⟩)
  · obtain ⟨j, hj, hdec⟩ := hW g (T g) hg i hi
    refine ⟨j, T (g + 1), ?_⟩
    have hdec' := A.dec_conf_mono hdec (show TT g (T g) ≤ T (g + 1) from (hT g) ▸ le_max_right _ _)
    unfold Alg.run
    -- group `g` behaves as in its lossy-link pattern until `T (g + 1)`
    rw [conf_eq_of_family A.step (fun t => {v | t ≤ T (g + 1) ∧ (v = a g ∨ v = b g)})
      (C' := A.initC x) (ρ' := lossyPat (a g) (b g) (w g) (T g)) (fun _ _ => rfl) ?_ ?_
      (T (g + 1)) j ⟨le_rfl, hj⟩]
    · exact hdec'
    · rintro t v ⟨ht, hv⟩ u
      simp only [Hears]
      rw [phaseG_in hdist hg hv (by omega)]
      rfl
    · rintro t v ⟨ht, hv⟩ u (rfl | hu)
      · exact ⟨by omega, hv⟩
      · rw [phaseG_in hdist hg hv (by omega)] at hu
        exact ⟨by omega, (linkG_mem hu.2).1⟩

end Generic

/-! ### Theorems 9 and 8 -/

/-- `1` if `k` is even (then the first group is the singleton `{0}`), `0` if `k` is odd. -/
def par (k : ℕ) : ℕ := if k % 2 = 0 then 1 else 0

/-- The number of groups: `⌈(k + 1)/2⌉`. -/
def ngr (k : ℕ) : ℕ := (k + 1 + par k) / 2

/-- First member of group `g` (process `2g - par k`). -/
def memA (n k : ℕ) (hkn : k < n) (g : ℕ) : Fin n := ⟨min (2 * g - par k) k, by omega⟩

/-- Second member of group `g` (process `2g + 1 - par k`). -/
def memB (n k : ℕ) (hkn : k < n) (g : ℕ) : Fin n := ⟨min (2 * g + 1 - par k) k, by omega⟩

theorem par_cases (k : ℕ) : (par k = 1 ∧ k % 2 = 0) ∨ (par k = 0 ∧ k % 2 = 1) := by
  unfold par; split_ifs <;> omega

/-- **Theorem 9** of the paper. For `1 < k < n` (with at least `k + 1` possible input values),
no algorithm solves `k`-set agreement under `VSRC(⌈k/2⌉ + 1, ∞)` with any `D, H ≥ 1`, even if the
communication graph is constant with a single root component from some round on. -/
theorem theorem9 {n k D H : ℕ} (_hk : 1 < k) (hkn : k < n) (hD : 1 ≤ D) (hH : 1 ≤ H)
    {V σ : Type} (emb : Fin (k + 1) ↪ V) (A : Alg (Fin n) V σ) :
    ¬ A.SolvesKSet k (VSRCkInf D H ((k + 1) / 2 + 1) ∩
      {ρ | ∃ r G, (∀ t ≥ r, ρ t = G) ∧ ∃! R, IsRootComp G R}) := by
  intro hA
  have hm : 1 ≤ (k + 1) / 2 + 1 := by omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let x : Fin n → V := fun i => if h : i.val < k + 1 then emb ⟨i.val, h⟩ else emb ⟨0, by omega⟩
  have hxinj : ∀ i j : Fin n, i.val ≤ k → j.val ≤ k → x i = x j → i = j := by
    intro i j hi hj h
    simp only [x, show i.val < k + 1 by omega, show j.val < k + 1 by omega, ↓reduceDIte] at h
    exact Fin.ext (by simpa using emb.injective h)
  have hpc := par_cases k
  have hdist : GroupsDisjoint (ngr k) (memA n k hkn) (memB n k hkn) := by
    intro g hg g' hg' u hu hu'
    unfold ngr at hg hg'
    rcases hu with rfl | rfl <;> rcases hu' with h | h <;>
      · rw [Fin.ext_iff] at h; simp only [memA, memB] at h; omega
  obtain ⟨ρ, hρ, hcov⟩ := thm9_cover hm hD hH A hA (ngr k) (memA n k hkn) (memB n k hkn) hdist
    (by unfold ngr; omega)
    (fun h => by
      unfold ngr
      by_contra hc
      exact h (Fin.ext (by simp only [memA, memB]; omega)))
    x (fun g hg hab hx => hab (hxinj _ _ (by simp only [memA]; omega)
      (by simp only [memB]; omega) hx))
  have := (hA x ρ hρ).1 (Finset.univ.map emb) (by
    intro v hv
    obtain ⟨i', -, rfl⟩ := Finset.mem_map.mp hv
    have hi' := i'.isLt
    have hg : (i'.val + par k) / 2 < ngr k := by unfold ngr; omega
    obtain ⟨j, hj⟩ := hcov _ hg ⟨i'.val, by omega⟩ (by
      rw [Fin.ext_iff, Fin.ext_iff]; simp only [memA, memB]; omega)
    refine ⟨j, ?_⟩
    simpa [x, show i'.val ≤ k by omega] using hj)
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- **Theorem 8** of the paper. For `1 < k < n` (with at least `k + 1` possible input values),
no algorithm solves `k`-set agreement under `VSRC(k, ∞)` with any `D, H ≥ 1`. -/
theorem theorem8 {n k D H : ℕ} (hk : 1 < k) (hkn : k < n) (hD : 1 ≤ D) (hH : 1 ≤ H)
    {V σ : Type} (emb : Fin (k + 1) ↪ V) (A : Alg (Fin n) V σ) :
    ¬ A.SolvesKSet k (VSRCkInf D H k) := fun hA =>
  theorem9 hk hkn hD hH emb A (hA.mono fun _ hρ => VSRCkInf_mono (by omega) hρ.1)

end Podc.GracefulKSetAgreement
