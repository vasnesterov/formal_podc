import Papers.PODC2014.GracefulKSetAgreement.Bivalence

/-!
# Theorem 4: no consensus under `VSRC(H − 1)` (Section 4.2)

We instantiate the generic bivalence argument (`not_solvesConsensus_of_chain_isolation`) with a
product message adversary `ProdAdv (famT4 H a)` that is contained in `VSRC(H − 1)`:

* in the rounds `1, …, H − 1` (indices `< H − 1`, the stability window `J`) the adversary may
  choose any graph with the single root component `{a}` (`RootedAt a`);
* afterwards any graph whose single root component has at most two processes and from which every
  other process hears directly (`FamF`, "fast" graphs; they make every VSRC of length `≥ H`
  `H`-network-bounded, and every root a clique, i.e. `D`-bounded for any `D ≥ 1`).

Both families are connected by single-process changes (Lemma 10: `chain_rootedAt`, `chain_famF`,
via stars). The adversary strategy of Lemma 9 (`iso_famT4`): from a round after `J`, make some
`q ≠ p` the eternal single root (`star q`); during `J`, if `p ≠ a` keep `a` the root forever, and if
`p = a` spread `a`'s information along a line `a → c₁ → ⋯ → c_{H−1} → q` for the rest of `J` and
then make the distant process `q` the eternal root. The line needs `H + 1` processes.

This differs from the paper's proof, which fixes `J` anywhere, lets the round graphs be arbitrary
(not ensuring property (ii) of Definition 12 for the forever-bivalent run), and isolates a process
`q` that Definition 13 requires to be reached (see `README.md`).
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

variable {P V σ : Type}

section Graphs

/-- The star from `u`: every other process hears exactly `u`. -/
def star (u : P) : Graph P := fun w z => w = u ∧ z ≠ u

/-- Graphs whose unique root component is `{a}`: `a` is deaf and reaches everybody. -/
def RootedAt (a : P) : Set (Graph P) := {G | Deaf G a ∧ ∀ w, (Digraph.mk G).Reachable a w}

/-- `{u, v}` (possibly `u = v`) has no in-neighbours from outside and is linked both ways. -/
def SmallRoot (G : Graph P) (u v : P) : Prop :=
  (∀ w z, (z = u ∨ z = v) → G w z → w = u ∨ w = v) ∧ (u ≠ v → G u v ∧ G v u)

/-- Every process outside `{u, v}` hears `u` or `v` directly. -/
def Fast (G : Graph P) (u v : P) : Prop := ∀ w, w ≠ u → w ≠ v → G u w ∨ G v w

/-- Fast graphs with a root component of at most two processes. -/
def FamF : Set (Graph P) := {G | ∃ u v, SmallRoot G u v ∧ Fast G u v}

/-- Use `G'` for the in-edges of the processes of `T` and `G` for the others. -/
def mix [DecidableEq P] (G G' : Graph P) (T : Finset P) : Graph P :=
  fun w z => if z ∈ T then G' w z else G w z

theorem chainStep_of_eq_off {F : Set (Graph P)} {G G' : Graph P} (hG : G ∈ F) (hG' : G' ∈ F)
    (i : P) (h : ∀ j, j ≠ i → ∀ w, w ≠ j → (G w j ↔ G' w j)) : ChainStep F G G' :=
  ⟨hG, hG', i, fun j hj w => by
    unfold Hears
    by_cases hw : w = j
    · simp [hw]
    · rw [h j hj w hw]⟩

theorem chainStep_symm {F : Set (Graph P)} {G G' : Graph P} (h : ChainStep F G G') :
    ChainStep F G' G :=
  ⟨h.2.1, h.1, h.2.2.elim fun i hi => ⟨i, fun j hj => (hi j hj).symm⟩⟩

theorem chain_symm {F : Set (Graph P)} {G G' : Graph P}
    (h : Relation.ReflTransGen (ChainStep F) G G') : Relation.ReflTransGen (ChainStep F) G' G :=
  by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact Relation.ReflTransGen.head (chainStep_symm hs) ih

/-- Changing the in-neighbourhoods one process at a time. -/
theorem chain_of_mix [DecidableEq P] {F : Set (Graph P)} {G G' : Graph P} (W : Finset P)
    (h : ∀ T ⊆ W, mix G G' T ∈ F) : Relation.ReflTransGen (ChainStep F) G (mix G G' W) := by
  induction W using Finset.induction_on with
  | empty =>
    have : mix G G' ∅ = G := by funext w z; simp [mix]
    rw [this]
  | @insert b W hb ih =>
    refine (ih fun T hT => h T (hT.trans (Finset.subset_insert _ _))).tail ?_
    refine chainStep_of_eq_off (h W (Finset.subset_insert _ _)) (h _ le_rfl) b fun j hj w => ?_
    simp [mix, hj]

theorem mix_univ [Fintype P] [DecidableEq P] (G G' : Graph P) : mix G G' Finset.univ = G' := by
  funext w z; simp [mix]

theorem star_mem_rootedAt (a : P) : star a ∈ RootedAt a := by
  refine ⟨fun w h => absurd rfl h.2, fun w => ?_⟩
  by_cases hw : w = a
  · subst hw; exact .rfl
  · exact Digraph.Adj.reachable (G := Digraph.mk (star a)) ⟨rfl, hw⟩

theorem mix_star_mem_rootedAt [DecidableEq P] {a : P} {G : Graph P} (hG : G ∈ RootedAt a)
    (T : Finset P) : mix G (star a) T ∈ RootedAt a := by
  refine ⟨fun w hw => ?_, fun w => ?_⟩
  · unfold mix at hw
    split_ifs at hw
    · exact absurd rfl hw.2
    · exact hG.1 w hw
  · induction hG.2 w with
    | refl => exact .rfl
    | @tail y z _ hyz ih =>
      by_cases hz : z ∈ T
      · by_cases hza : z = a
        · subst hza; exact .rfl
        · exact Digraph.Adj.reachable (G := Digraph.mk (mix G (star a) T))
            (by simp [mix, hz, star, hza])
      · exact ih.tail (G := Digraph.mk (mix G (star a) T)) (by simpa [mix, hz] using hyz)

/-- **Lemma 10 for `RootedAt a`.** -/
theorem chain_rootedAt [Fintype P] [DecidableEq P] {a : P} {G G' : Graph P}
    (hG : G ∈ RootedAt a) (hG' : G' ∈ RootedAt a) :
    Relation.ReflTransGen (ChainStep (RootedAt a)) G G' := by
  have h1 := chain_of_mix (F := RootedAt a) (G := G) (G' := star a) Finset.univ
    fun T _ => mix_star_mem_rootedAt hG T
  have h2 := chain_of_mix (F := RootedAt a) (G := G') (G' := star a) Finset.univ
    fun T _ => mix_star_mem_rootedAt hG' T
  rw [mix_univ] at h1 h2
  exact h1.trans (chain_symm h2)

theorem star_mem_famF (u : P) : star u ∈ FamF :=
  ⟨u, u, ⟨fun w z hz h => by rcases hz with rfl | rfl <;> exact absurd rfl h.2,
    fun h => absurd rfl h⟩, fun w hw _ => Or.inl ⟨rfl, hw⟩⟩

/-- **Lemma 10 for `FamF`**, first step: a fast graph with root `{u, v}` is connected to `star u`. -/
theorem chain_famF_star [Fintype P] [DecidableEq P] {G : Graph P} {u v : P}
    (hr : SmallRoot G u v) (hf : Fast G u v) :
    Relation.ReflTransGen (ChainStep FamF) G (star u) := by
  let W : Finset P := Finset.univ.filter fun z => z ≠ u ∧ z ≠ v
  have hmix : ∀ T ⊆ W, mix G (star u) T ∈ FamF := by
    intro T hT
    have hTuv : ∀ z ∈ T, z ≠ u ∧ z ≠ v := fun z hz => by simpa [W] using hT hz
    refine ⟨u, v, ⟨fun w z hz h => ?_, fun huv => ?_⟩, fun w hwu hwv => ?_⟩
    · have hzT : z ∉ T := fun hzT => by
        rcases hz with rfl | rfl
        · exact (hTuv _ hzT).1 rfl
        · exact (hTuv _ hzT).2 rfl
      simp only [mix, hzT, ite_false] at h
      exact hr.1 w z hz h
    · have huT : u ∉ T := fun h => (hTuv u h).1 rfl
      have hvT : v ∉ T := fun h => (hTuv v h).2 rfl
      simpa [mix, huT, hvT] using hr.2 huv
    · by_cases hwT : w ∈ T
      · left; simp [mix, hwT, star, hwu]
      · simpa [mix, hwT] using hf w hwu hwv
  refine (chain_of_mix W hmix).tail (chainStep_of_eq_off (hmix W le_rfl) (star_mem_famF u) u
    fun j hj w hwj => ?_)
  by_cases hjW : j ∈ W
  · simp [mix, hjW]
  · have hjv : j = v := by by_contra h; exact hjW (by simp [W, hj, h])
    subst hjv
    simp only [mix, hjW, ite_false, star]
    constructor
    · intro h
      rcases hr.1 w j (Or.inr rfl) h with rfl | rfl
      · exact ⟨rfl, hj⟩
      · exact absurd rfl hwj
    · rintro ⟨rfl, -⟩; exact (hr.2 (Ne.symm hj)).1

end Graphs

/-- `u ↔ v`, and everybody else hears `u`. -/
def zig (u v : P) : Graph P := fun w z => (w = u ∧ z ≠ u) ∨ (w = v ∧ z = u)

theorem zig_mem_famF {u v : P} (huv : u ≠ v) : zig u v ∈ FamF := by
  refine ⟨u, v, ⟨fun w z hz h => ?_, fun _ => ⟨Or.inl ⟨rfl, Ne.symm huv⟩, Or.inr ⟨rfl, rfl⟩⟩⟩,
    fun w hwu _ => Or.inl (Or.inl ⟨rfl, hwu⟩)⟩
  rcases hz with rfl | rfl
  · rcases h with ⟨-, h⟩ | ⟨rfl, -⟩
    · exact absurd rfl h
    · exact Or.inr rfl
  · rcases h with ⟨rfl, -⟩ | ⟨-, h⟩
    · exact Or.inl rfl
    · exact absurd h (Ne.symm huv)

theorem zig_eq_symm_off {u v : P} (huv : u ≠ v) (T : Finset P) [DecidableEq P] :
    mix (zig u v) (zig v u) T ∈ FamF := by
  refine ⟨u, v, ⟨fun w z hz h => ?_, fun _ => ⟨?_, ?_⟩⟩, fun w hwu hwv => ?_⟩
  · unfold mix at h
    split_ifs at h
    · rcases hz with rfl | rfl <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
    · rcases hz with rfl | rfl <;> rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  · unfold mix; split_ifs <;> simp [zig, Ne.symm huv]
  · unfold mix; split_ifs <;> simp [zig, huv]
  · unfold mix; split_ifs
    · right; simp [zig, hwv]
    · left; simp [zig, hwu]

/-- **Lemma 10 for `FamF`**, second step: stars are connected. -/
theorem chain_star_star [Fintype P] [DecidableEq P] (u v : P) :
    Relation.ReflTransGen (ChainStep FamF) (star u) (star v) := by
  by_cases huv : u = v
  · subst huv; exact .refl
  have h1 : ChainStep FamF (star u) (zig u v) :=
    chainStep_of_eq_off (star_mem_famF u) (zig_mem_famF huv) u fun j hj w _ => by
      simp [star, zig, hj]
  have h2 := chain_of_mix (F := FamF) (G := zig u v) (G' := zig v u) Finset.univ
    fun T _ => zig_eq_symm_off huv T
  rw [mix_univ] at h2
  have h3 : ChainStep FamF (zig v u) (star v) :=
    chainStep_of_eq_off (zig_mem_famF (Ne.symm huv)) (star_mem_famF v) v fun j hj w _ => by
      simp [star, zig, hj]
  exact (Relation.ReflTransGen.single h1).trans (h2.tail h3)

/-- **Lemma 10 for `FamF`.** -/
theorem chain_famF [Fintype P] [DecidableEq P] {G G' : Graph P} (hG : G ∈ FamF)
    (hG' : G' ∈ FamF) : Relation.ReflTransGen (ChainStep FamF) G G' := by
  obtain ⟨u, v, hr, hf⟩ := hG
  obtain ⟨u', v', hr', hf'⟩ := hG'
  exact ((chain_famF_star hr hf).trans (chain_star_star u u')).trans
    (chain_symm (chain_famF_star hr' hf'))

/-- The root components of a graph of `RootedAt a`. -/
theorem isRootComp_rootedAt {a : P} {G : Graph P} (hG : G ∈ RootedAt a) (R : Set P) :
    IsRootComp G R ↔ R = {a} := by
  have ha : IsRootComp G {a} := isRootComp_singleton_iff.mpr hG.1
  refine ⟨fun hR => ?_, fun h => h ▸ ha⟩
  have := isRootComp_mem_of_reach (𝓡 := {{a}}) (fun R hR => by rw [Set.mem_singleton_iff.mp hR]; exact ha)
    (fun v => ⟨{a}, rfl, a, rfl, hG.2 v⟩) hR
  exact Set.mem_singleton_iff.mp this

theorem isRootComp_small {G : Graph P} {u v : P} (hr : SmallRoot G u v) : IsRootComp G {u, v} := by
  by_cases huv : u = v
  · subst huv
    rw [Set.pair_eq_singleton, isRootComp_singleton_iff]
    intro w hw
    rcases hr.1 w u (Or.inl rfl) hw with h | h <;> exact h
  · exact isRootComp_pair (hr.2 huv).1 (hr.2 huv).2 hr.1

/-- The root components of a graph of `FamF`. -/
theorem isRootComp_famF {G : Graph P} {u v : P} (hr : SmallRoot G u v) (hf : Fast G u v)
    (R : Set P) : IsRootComp G R ↔ R = {u, v} := by
  refine ⟨fun hR => ?_, fun h => h ▸ isRootComp_small hr⟩
  have := isRootComp_mem_of_reach (𝓡 := {{u, v}})
    (fun R hR => by rw [Set.mem_singleton_iff.mp hR]; exact isRootComp_small hr)
    (fun w => by
      refine ⟨{u, v}, rfl, ?_⟩
      by_cases hwu : w = u
      · exact ⟨u, by simp, by rw [hwu]⟩
      by_cases hwv : w = v
      · exact ⟨v, by simp, by rw [hwv]⟩
      rcases hf w hwu hwv with h | h
      · exact ⟨u, by simp, Digraph.Adj.reachable (G := Digraph.mk G) h⟩
      · exact ⟨v, by simp, Digraph.Adj.reachable (G := Digraph.mk G) h⟩) hR
  exact Set.mem_singleton_iff.mp this

/-! ### The adversary of Theorem 4 -/

/-- The round families: `RootedAt a` in the first `H − 1` rounds, `FamF` afterwards. -/
def famT4 (H : ℕ) (a : P) (t : ℕ) : Set (Graph P) := if t < H - 1 then RootedAt a else FamF

theorem star_mem_famT4 (H : ℕ) (a : P) (t : ℕ) : star a ∈ famT4 H a t := by
  unfold famT4; split_ifs
  · exact star_mem_rootedAt a
  · exact star_mem_famF a

theorem chain_famT4 [Fintype P] [DecidableEq P] (H : ℕ) (a : P) (t : ℕ) :
    ∀ G ∈ famT4 H a t, ∀ G' ∈ famT4 H a t,
      Relation.ReflTransGen (ChainStep (famT4 H a t)) G G' := by
  intro G hG G' hG'
  unfold famT4 at *
  split_ifs at * with h
  · exact chain_rootedAt hG hG'
  · exact chain_famF hG hG'

/-- The line `e 0 → e 1 → ⋯ → e H`; the other processes hear `e 0`. -/
def line {H : ℕ} (e : Fin (H + 1) ↪ P) : Graph P :=
  fun w z => (∃ i : Fin H, w = e i.castSucc ∧ z = e i.succ) ∨ (z ∉ Set.range e ∧ w = e 0)

theorem line_mem_rootedAt {H : ℕ} (e : Fin (H + 1) ↪ P) : line e ∈ RootedAt (e 0) := by
  refine ⟨fun w hw => ?_, fun z => ?_⟩
  · rcases hw with ⟨i, -, hi⟩ | ⟨h, -⟩
    · exact absurd (e.injective hi) (Fin.succ_ne_zero i).symm
    · exact absurd ⟨0, rfl⟩ h
  · by_cases hz : z ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hz
      induction j using Fin.induction with
      | zero => exact .rfl
      | succ i ih => exact ih.tail (G := Digraph.mk (line e)) (Or.inl ⟨i, rfl, rfl⟩)
    · exact Digraph.Adj.reachable (G := Digraph.mk (line e)) (Or.inr ⟨hz, rfl⟩)

theorem not_journey_of_deaf {τ : ℕ → Graph P} {q : P} (hq : ∀ s w, ¬ τ s w q) {p : P}
    (hpq : p ≠ q) (s : ℕ) : ¬ Journey τ 0 p s q := fun h => hpq (Journey.eq_of_no_in hq h)

theorem star_deaf (q : P) (s : ℕ) (w : P) : ¬ (fun _ : ℕ => star q) s w q := fun h => h.2 rfl

/-- **The adversary strategy of Lemma 9** for `famT4`: some `q ≠ p` never hears from `p`. -/
theorem iso_famT4 {H : ℕ} (hH : 1 ≤ H) (e : Fin (H + 1) ↪ P) (t : ℕ) (p : P) :
    ∃ q, q ≠ p ∧ ∃ τ : ℕ → Graph P, (∀ s, τ s ∈ famT4 H (e 0) (t + s)) ∧
      ∀ s, ¬ Journey τ 0 p s q := by
  classical
  by_cases hp : p = e 0
  · subst hp
    have hlast : (Fin.last H) ≠ 0 := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    refine ⟨e (Fin.last H), fun h => hlast (e.injective h), ?_⟩
    let L := H - 1 - t
    refine ⟨fun s => if s < L then line e else star (e (Fin.last H)), fun s => ?_, fun s hj => ?_⟩
    · unfold famT4
      by_cases hs : s < L
      · simp only [hs, ite_true, show t + s < H - 1 by omega]
        exact line_mem_rootedAt e
      · simp only [hs, ite_false, show ¬ t + s < H - 1 by omega]
        exact star_mem_famF _
    · have := hj.of_inv (P := fun s z => z ≠ e (Fin.last H) ∧
          (s ≤ L → ∀ j : Fin (H + 1), z = e j → j.val ≤ s))
        ⟨fun h => hlast (e.injective h).symm, fun _ j hj => by
          rw [← e.injective hj]; simp⟩
        (fun s' a b _ _ ha hab => by
          rcases hab with rfl | hab
          · exact ⟨ha.1, fun hs j hj => le_trans (ha.2 (by omega) j hj) (by omega)⟩
          · by_cases hs : s' < L
            · simp only [hs, ite_true] at hab
              rcases hab with ⟨i, rfl, rfl⟩ | ⟨hb, -⟩
              · have hi := ha.2 hs.le _ rfl
                simp only [Fin.val_castSucc] at hi
                refine ⟨fun h => ?_, fun _ j hj => ?_⟩
                · have := congrArg Fin.val (e.injective h); simp at this; omega
                · rw [← e.injective hj]; simp; omega
              · exact ⟨fun h => hb ⟨_, h.symm⟩, fun _ j hj => absurd ⟨j, hj.symm⟩ hb⟩
            · simp only [hs, ite_false] at hab
              exact ⟨hab.2, fun h => absurd h (by omega)⟩)
      exact this.1 rfl
  · refine ⟨e 0, Ne.symm hp, fun _ => star (e 0), fun s => star_mem_famT4 H (e 0) _,
      not_journey_of_deaf (star_deaf (e 0)) hp⟩

/-- The product adversary of Theorem 4 is contained in `VSRC(H − 1)` (Definition 12). -/
theorem prodAdv_famT4_subset {H : ℕ} (hH : 2 ≤ H) (a : P) :
    ProdAdv (famT4 H a) ⊆ VSRCd H (H - 1) := by
  intro ρ hρ
  refine ⟨fun t => ?_, fun R a' b hR => ?_, 0, {a}, fun t _ ht => ?_, Or.inl (by omega)⟩
  · have := hρ t
    unfold famT4 at this
    split_ifs at this
    · exact ⟨{a}, (isRootComp_rootedAt this _).mpr rfl, fun R hR => (isRootComp_rootedAt this R).mp hR⟩
    · obtain ⟨u, v, hr, hf⟩ := this
      exact ⟨{u, v}, (isRootComp_famF hr hf _).mpr rfl, fun R hR => (isRootComp_famF hr hf R).mp hR⟩
  · by_cases hlen : b + 1 < a' + H
    · exact Or.inl hlen
    right
    intro x hx hxb q
    have ht0 := hρ (x + H - 1)
    unfold famT4 at ht0
    simp only [show ¬ (x + H - 1 < H - 1) by omega, ↓reduceIte] at ht0
    obtain ⟨u, v, hr, hf⟩ := ht0
    have hRuv := (isRootComp_famF hr hf R).mp (hR (x + H - 1) (by omega) (by omega))
    refine ⟨R, rfl, ?_⟩
    by_cases hqu : q = u
    · exact ⟨u, by simp [hRuv], hqu ▸ Journey.self (by omega)⟩
    by_cases hqv : q = v
    · exact ⟨v, by simp [hRuv], hqv ▸ Journey.self (by omega)⟩
    have hx' : x + H = (x + H - 1) + 1 := by omega
    rcases hf q hqu hqv with h | h
    · refine ⟨u, by simp [hRuv], ?_⟩
      rw [hx']
      exact .step (Journey.self (by omega)) (Or.inr h)
    · refine ⟨v, by simp [hRuv], ?_⟩
      rw [hx']
      exact .step (Journey.self (by omega)) (Or.inr h)
  · have := hρ t
    unfold famT4 at this
    simp only [show t < H - 1 by omega, ↓reduceIte] at this
    exact (isRootComp_rootedAt this _).mpr rfl

/-- An embedding of `Fin (H + 1)` into a type with at least `H + 1` elements. -/
noncomputable def finEmb [Fintype P] {H : ℕ} (hn : H + 1 ≤ Fintype.card P) : Fin (H + 1) ↪ P :=
  (Fin.castLEEmb hn).trans (Fintype.equivFin P).symm.toEmbedding

/-- **Theorem 4** of [BRSSW]: there is no algorithm that solves consensus under the message
adversary `VSRC(H − 1)` (Definition 12 with `d = H − 1`), for `2 ≤ H ≤ n − 1`. Proved for the
product sub-adversary `ProdAdv (famT4 H a)`. -/
theorem theorem4 [Fintype P] [DecidableEq P] {H : ℕ} (hH : 2 ≤ H)
    (hn : H + 1 ≤ Fintype.card P) {v₀ v₁ : V} (hv : v₀ ≠ v₁) (A : Alg P V σ) :
    ¬ A.SolvesConsensus (VSRCd H (H - 1)) := by
  let e := finEmb hn
  have : Nonempty P := ⟨e 0⟩
  intro hA
  exact not_solvesConsensus_of_chain_isolation (famT4 H (e 0)) (chain_famT4 H (e 0))
    (iso_famT4 (by omega) e) hv A (hA.mono (prodAdv_famT4_subset hH (e 0)))


/-! ### Definition 13, Definition 14 and Lemma 8 -/

/-- **Definition 13** (almost `H − 1`-network-bounded `[a, b]`-VSRC), literally: either
`|I| < H − 1`, or for every `x ∈ [a, b − H + 2]` there is a *unique* process `q` with
`cd_x(p, q) ≤ H` for all `p ∈ R`, while all other processes `q'` have `cd_x(p, q') ≤ H − 1`. -/
def AlmostBounded (H : ℕ) (ρ : ℕ → Graph P) (R : Set P) (a b : ℕ) : Prop :=
  b + 1 < a + (H - 1) ∨ ∀ x, a ≤ x → x + H ≤ b + 2 →
    ∃ q, ((∀ p ∈ R, Journey ρ x p (x + H) q) ∧
        ∀ q', (∀ p ∈ R, Journey ρ x p (x + H) q') → q' = q) ∧
      ∀ q', q' ≠ q → ∀ p ∈ R, Journey ρ x p (x + (H - 1)) q'

/-- **Definition 14**, the message adversary `VSRC'(H − 1)`. -/
def VSRCPrime (H : ℕ) : Set (ℕ → Graph P) := {ρ |
  (∀ t, ∃! R, IsRootComp (ρ t) R) ∧
  (∀ R a b, IsVSRC ρ R a b → HNetBounded H ρ {R} a b) ∧
  ∃ a R, IsVSRC ρ R a (a + H - 2) ∧ AlmostBounded H ρ R a (a + H - 2)}

/-- Definition 13 is unsatisfiable for windows of length `H − 1` with two or more processes:
every `q' ≠ q` also satisfies `cd ≤ H`, contradicting the uniqueness of `q`. -/
theorem not_almostBounded {H : ℕ} (hH : 1 ≤ H) {q₁ q₂ : P} (h12 : q₁ ≠ q₂) (ρ : ℕ → Graph P)
    (R : Set P) (a : ℕ) : ¬ AlmostBounded H ρ R a (a + H - 2) := by
  rintro (h | h)
  · omega
  obtain ⟨q, ⟨-, huniq⟩, hothers⟩ := h a le_rfl (by omega)
  have key : ∀ q', q' ≠ q → q' = q := fun q' hq' =>
    huniq q' fun p hp => (hothers q' hq' p hp).mono_right (by omega)
  by_cases h1 : q₁ = q
  · exact h12 (h1.trans (key q₂ (fun h => h12 (h1.trans h.symm))).symm)
  · exact h1 (key q₁ h1)

/-- `VSRC'(H − 1)` is empty as soon as there are two processes. -/
theorem vsrcPrime_eq_empty {H : ℕ} (hH : 1 ≤ H) {q₁ q₂ : P} (h12 : q₁ ≠ q₂) :
    (VSRCPrime H : Set (ℕ → Graph P)) = ∅ := by
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, a, R, -, hR⟩
  exact not_almostBounded hH h12 ρ R a hR

/-- **Theorem 4, first claim ("no algorithm solves consensus under `VSRC'(H − 1)`"), is false as
stated**: since `VSRC'(H − 1) = ∅`, every algorithm solves consensus under it. -/
theorem theorem4_prime_false {H : ℕ} (hH : 1 ≤ H) {q₁ q₂ : P} (h12 : q₁ ≠ q₂)
    (A : Alg P V σ) : A.SolvesConsensus (VSRCPrime H) := by
  intro x ρ hρ
  rw [vsrcPrime_eq_empty hH h12] at hρ
  exact hρ.elim

/-- The constant star from `a` is feasible for `VSRC(d)` (with any `H ≥ 1`, `d ≥ 1`). -/
theorem const_star_mem_VSRCd {H d : ℕ} (hH : 2 ≤ H) (a : P) :
    (fun _ => star a) ∈ (VSRCd H d : Set (ℕ → Graph P)) := by
  have hmem := prodAdv_famT4_subset (H := H) hH a (fun t => star_mem_famT4 _ a t)
  refine ⟨hmem.1, hmem.2.1, 0, {a}, fun t _ _ => ?_, Or.inr fun x _ _ q => ⟨{a}, rfl, a, rfl, ?_⟩⟩
  · exact (isRootComp_rootedAt (star_mem_rootedAt a) _).mpr rfl
  · by_cases hq : q = a
    · exact hq ▸ Journey.self (by omega)
    · exact (Journey.single (E := fun _ => star a) (t := x) ⟨rfl, hq⟩).mono_right (by omega)

/-- **Lemma 8 (`VSRC'(H − 1) ⩾ VSRC(H)`) is false**: `VSRC(H)` is non-empty while
`VSRC'(H − 1)` is empty (with at least two processes). -/
theorem lemma8_false {H : ℕ} (hH : 2 ≤ H) {q₁ q₂ : P} (h12 : q₁ ≠ q₂) :
    ¬ (VSRCd H H : Set (ℕ → Graph P)) ⊆ VSRCPrime H := fun h => by
  have := h (const_star_mem_VSRCd hH q₁)
  rw [vsrcPrime_eq_empty (by omega) h12] at this
  exact this

end Podc.GracefulKSetAgreement
