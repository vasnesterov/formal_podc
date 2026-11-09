import Papers.PODC2014.GracefulKSetAgreement.Consensus

/-!
# Theorem 7: no `k`-set agreement under `VSRC(k, min{n − k, H} − 1)`

Following the paper, `k − 1` processes `D` are isolated forever (singleton root components that
decide their own, pairwise distinct, inputs), and the remaining `n − k + 1` processes `D̄` must then
solve consensus among themselves under the adversary of Theorem 4 with `H' = min{n − k, H}`
(the reduction of the generic Theorem 6 of [7]; here done directly with the restricted algorithm
`Alg.restrict`, Definition "A|D̄" of the paper).

The case `k = 1` is included (`D = ∅`); unlike the paper (which drops item (ii) of Definition 15
for `k = 1`), all runs used here satisfy item (ii) for every `D ≥ 1`: every root component of every
round is a clique of at most two processes.
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

variable {P V σ : Type} [DecidableEq P]

/-- The processes outside `Dset` (the paper's `D̄`). -/
abbrev Rest (Dset : Finset P) := {i : P // i ∉ Dset}

/-- A graph on `D̄`, seen in the whole system (the processes of `D` are isolated). -/
def emb (Dset : Finset P) (G : Graph (Rest Dset)) : Graph P :=
  fun w z => ∃ (hw : w ∉ Dset) (hz : z ∉ Dset), G ⟨w, hw⟩ ⟨z, hz⟩

/-- The restricted algorithm `A|D̄`: the processes of `D̄` run `A` and never receive messages
from `D`. -/
def Alg.restrict (A : Alg P V σ) (Dset : Finset P) : Alg (Rest Dset) V σ where
  init i y := A.init i.1 y
  step i m := A.step i.1 (fun j => if h : j ∈ Dset then none else m ⟨j, h⟩)
  dec := A.dec
  dec_stable i m s v hm hs := A.dec_stable i.1 _ s v (by simp [i.2, hm]) hs

theorem run_emb (A : Alg P V σ) (Dset : Finset P) (x : P → V) (ρ : ℕ → Graph (Rest Dset))
    (t : ℕ) (i : Rest Dset) :
    A.run x (fun s => emb Dset (ρ s)) t i.1 = (A.restrict Dset).run (fun j => x j.1) ρ t i := by
  induction t generalizing i with
  | zero => rfl
  | succ t ih =>
    simp only [Alg.run, conf_succ, next] at ih ⊢
    change A.step i.1 _ = A.step i.1 _
    congr 1
    funext j
    by_cases hj : j ∈ Dset
    · have : ¬ Hears (emb Dset (ρ t)) i.1 j := by
        rintro (h | ⟨hw, -⟩)
        · exact i.2 (h ▸ hj)
        · exact hw hj
      simp [msgs, this, hj]
    · have hiff : Hears (emb Dset (ρ t)) i.1 j ↔ Hears (ρ t) i ⟨j, hj⟩ := by
        unfold Hears emb
        constructor
        · rintro (h | ⟨_, _, h⟩)
          · left; exact Subtype.ext h
          · right; exact h
        · rintro (h | h)
          · left; exact congrArg Subtype.val h
          · right; exact ⟨hj, i.2, h⟩
      simp only [msgs, hj, dite_false]
      by_cases hh : Hears (ρ t) i ⟨j, hj⟩
      · simp only [hiff.mpr hh, hh, ↓reduceIte, ← ih ⟨j, hj⟩]
      · simp only [show ¬ Hears (emb Dset (ρ t)) i.1 j from fun h => hh (hiff.mp h), hh,
          ↓reduceIte]

/-! ### Root components of embedded graphs -/

omit [DecidableEq P] in
theorem reachable_emb {Dset : Finset P} {G : Graph (Rest Dset)} {u v : Rest Dset}
    (h : (Digraph.mk G).Reachable u v) : (Digraph.mk (emb Dset G)).Reachable u.1 v.1 := by
  induction h with
  | refl => exact .rfl
  | tail _ hyz ih => exact ih.tail (G := Digraph.mk (emb Dset G)) ⟨_, _, hyz⟩

omit [DecidableEq P] in
theorem isRootComp_emb {Dset : Finset P} {G : Graph (Rest Dset)} {R : Set (Rest Dset)}
    (hR : IsRootComp G R) : IsRootComp (emb Dset G) (Subtype.val '' R) := by
  rw [isRootComp_iff] at hR ⊢
  obtain ⟨hne, hcl, hsc⟩ := hR
  refine ⟨hne.image _, fun v hv w hwv => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨v', hv', rfl⟩ := hv
    obtain ⟨hw, hz, h⟩ := hwv
    exact ⟨⟨w, hw⟩, hcl v' hv' _ h, rfl⟩
  · obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact reachable_emb (hsc a' ha' b' hb')

omit [DecidableEq P] in
theorem isRootComp_emb_singleton {Dset : Finset P} (G : Graph (Rest Dset)) {d : P}
    (hd : d ∈ Dset) : IsRootComp (emb Dset G) {d} :=
  isRootComp_singleton_iff.mpr fun _ ⟨_, hz, _⟩ => absurd hd hz

/-- The root components of an embedded graph whose root component `R` reaches everybody. -/
theorem isRootComp_emb_mem {Dset : Finset P} {G : Graph (Rest Dset)} {R : Set (Rest Dset)}
    (hR : IsRootComp G R) (hreach : ∀ v, ∃ u ∈ R, (Digraph.mk G).Reachable u v) {S : Set P}
    (hS : IsRootComp (emb Dset G) S) :
    S ∈ ((fun d => ({d} : Set P)) '' (Dset : Set P)) ∪ {Subtype.val '' R} := by
  refine isRootComp_mem_of_reach (fun R' hR' => ?_) (fun v => ?_) hS
  · rcases hR' with ⟨d, hd, rfl⟩ | hR'
    · exact isRootComp_emb_singleton G hd
    · rw [Set.mem_singleton_iff.mp hR']; exact isRootComp_emb hR
  · by_cases hv : v ∈ Dset
    · exact ⟨{v}, Or.inl ⟨v, hv, rfl⟩, v, rfl, .rfl⟩
    · obtain ⟨u, hu, huv⟩ := hreach ⟨v, hv⟩
      exact ⟨_, Or.inr rfl, u.1, ⟨u, hu, rfl⟩, reachable_emb huv⟩

omit [DecidableEq P] in
theorem ncard_roots_le [Fintype P] {Dset : Finset P} (R : Set (Rest Dset)) :
    (((fun d => ({d} : Set P)) '' (Dset : Set P)) ∪ {Subtype.val '' R}).ncard ≤ Dset.card + 1 := by
  refine (Set.ncard_union_le _ _).trans ?_
  rw [Set.ncard_singleton]
  have := Set.ncard_image_le (f := fun d => ({d} : Set P)) (s := (Dset : Set P)) (Set.toFinite _)
  rw [Set.ncard_coe_finset] at this
  omega

/-- Root components that are cliques make every VSRC `D`-bounded (`D ≥ 1`). -/
theorem dBounded_of_clique {ρ : ℕ → Graph P} {D : ℕ} (hD : 1 ≤ D)
    (hcl : ∀ t R, IsRootComp (ρ t) R → ∀ p ∈ R, ∀ q ∈ R, p ≠ q → ρ t p q) :
    ∀ R a b, IsVSRC ρ R a b → DBounded D ρ R a b := by
  intro R a b hR
  right
  intro x hax hxb p hp q hq
  by_cases hpq : p = q
  · exact hpq ▸ Journey.self (by omega)
  · exact (Journey.single (hcl x R (hR x hax (by omega)) p hp q hq hpq)).mono_right (by omega)

/-- In the embedded rounds of `famT4`, every root component is a clique. -/
theorem clique_emb_famT4 {Dset : Finset P} {H : ℕ} {a : Rest Dset} {t : ℕ}
    {G : Graph (Rest Dset)} (hG : G ∈ famT4 H a t) (R : Set P)
    (hR : IsRootComp (emb Dset G) R) : ∀ p ∈ R, ∀ q ∈ R, p ≠ q → emb Dset G p q := by
  unfold famT4 at hG
  split_ifs at hG
  · have hmem := isRootComp_emb_mem ((isRootComp_rootedAt hG _).mpr rfl)
      (fun v => ⟨a, rfl, hG.2 v⟩) hR
    rcases hmem with ⟨d, -, rfl⟩ | hmem
    · intro p hp q hq hpq; simp_all
    · rw [Set.mem_singleton_iff.mp hmem]
      intro p hp q hq hpq; simp_all
  · obtain ⟨u, v, hr, hf⟩ := hG
    have hmem := isRootComp_emb_mem ((isRootComp_famF hr hf _).mpr rfl) (fun w => by
      by_cases hwu : w = u
      · exact ⟨u, by simp, by rw [hwu]⟩
      by_cases hwv : w = v
      · exact ⟨v, by simp, by rw [hwv]⟩
      rcases hf w hwu hwv with h | h
      · exact ⟨u, by simp, Digraph.Adj.reachable (G := Digraph.mk G) h⟩
      · exact ⟨v, by simp, Digraph.Adj.reachable (G := Digraph.mk G) h⟩) hR
    rcases hmem with ⟨d, -, rfl⟩ | hmem
    · intro p hp q hq hpq; simp_all
    · rw [Set.mem_singleton_iff.mp hmem]
      rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩ hpq
      have hpq' : p' ≠ q' := fun h => hpq (congrArg _ h)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp' hq'
      have huv : u ≠ v := fun h => by
        rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp_all
      refine ⟨p'.2, q'.2, ?_⟩
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
      · exact absurd rfl hpq'
      · exact (hr.2 huv).1
      · exact (hr.2 huv).2
      · exact absurd rfl hpq'

/-- The embedded adversary of Theorem 4 on `D̄` lies in `VSRC(k, min{n − k, H} − 1)` (strong
reading), with the processes of `D` as perpetually stable singleton root components. -/
theorem emb_mem_VSRCkAll [Fintype P] {Dset : Finset P} {k D H H' : ℕ} (hDk : Dset.card + 1 = k)
    (hD : 1 ≤ D) (hH' : 2 ≤ H') (hHH : H' ≤ H) (a : Rest Dset) {ρ : ℕ → Graph (Rest Dset)}
    (hρ : ρ ∈ ProdAdv (famT4 H' a)) :
    (fun s => emb Dset (ρ s)) ∈ (VSRCkAll D H k (H' - 1) : Set (ℕ → Graph P)) := by
  -- the root components of each round
  have hroots : ∀ t, ∃ R : Set (Rest Dset), ∀ S, IsRootComp (emb Dset (ρ t)) S →
      S ∈ ((fun d => ({d} : Set P)) '' (Dset : Set P)) ∪ {Subtype.val '' R} := by
    intro t
    have hG := hρ t
    unfold famT4 at hG
    split_ifs at hG
    · exact ⟨{a}, fun S hS => isRootComp_emb_mem ((isRootComp_rootedAt hG _).mpr rfl)
        (fun v => ⟨a, rfl, hG.2 v⟩) hS⟩
    · obtain ⟨u, v, hr, hf⟩ := hG
      refine ⟨{u, v}, fun S hS => isRootComp_emb_mem ((isRootComp_famF hr hf _).mpr rfl)
        (fun w => ?_) hS⟩
      by_cases hwu : w = u
      · exact ⟨u, by simp, by rw [hwu]⟩
      by_cases hwv : w = v
      · exact ⟨v, by simp, by rw [hwv]⟩
      rcases hf w hwu hwv with h | h
      · exact ⟨u, by simp, Digraph.Adj.reachable (G := Digraph.mk (ρ t)) h⟩
      · exact ⟨v, by simp, Digraph.Adj.reachable (G := Digraph.mk (ρ t)) h⟩
  let S0 : Set (Set P) := ((fun d => ({d} : Set P)) '' (Dset : Set P)) ∪ {Subtype.val '' {a}}
  have hwin : ∀ t, t < H' - 1 → ∀ R, IsRootComp (emb Dset (ρ t)) R ↔ R ∈ S0 := by
    intro t ht R
    have hG := hρ t
    unfold famT4 at hG
    simp only [ht, ↓reduceIte] at hG
    refine ⟨fun hR => isRootComp_emb_mem ((isRootComp_rootedAt hG _).mpr rfl)
        (fun v => ⟨a, rfl, hG.2 v⟩) hR, fun hR => ?_⟩
    rcases hR with ⟨d, hd, rfl⟩ | hR
    · exact isRootComp_emb_singleton _ hd
    · rw [Set.mem_singleton_iff.mp hR]; exact isRootComp_emb ((isRootComp_rootedAt hG _).mpr rfl)
  refine ⟨fun t => ?_, dBounded_of_clique hD fun t R hR => clique_emb_famT4 (hρ t) R hR,
    0, S0, ?_, ?_, fun R hR t _ ht => (hwin t (by omega) R).mpr hR, Or.inl (by omega),
    fun t _ ht R hR => (hwin t (by omega) R).mp hR⟩
  · obtain ⟨R, hR⟩ := hroots t
    exact (Set.ncard_le_ncard (fun S hS => hR S hS) (Set.toFinite _)).trans
      ((ncard_roots_le R).trans hDk.le)
  · exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, Or.inr rfl⟩
  · exact (ncard_roots_le {a}).trans hDk.le

/-! ### The reduction -/

theorem exists_inj_avoid {k : ℕ} (hV : ∃ f : Fin (k + 1) → V, Function.Injective f) (u u' : V)
    (Dset : Finset P) (hD : Dset.card + 1 = k) :
    ∃ c : P → V, Set.InjOn c Dset ∧ ∀ d ∈ Dset, c d ≠ u ∧ c d ≠ u' := by
  classical
  obtain ⟨f, hf⟩ := hV
  let W : Finset V := ((Finset.univ.image f).erase u).erase u'
  have hW : Dset.card ≤ W.card := by
    have h1 : (Finset.univ.image f).card = k + 1 := by
      rw [Finset.card_image_of_injective _ hf]; simp
    have h2 := Finset.pred_card_le_card_erase (s := Finset.univ.image f) (a := u)
    have h3 := Finset.pred_card_le_card_erase (s := (Finset.univ.image f).erase u) (a := u')
    simp only [W]; omega
  obtain ⟨e⟩ : Nonempty (Dset ↪ W) := Function.Embedding.nonempty_of_card_le (by simpa using hW)
  refine ⟨fun p => if h : p ∈ Dset then (e ⟨p, h⟩).1 else u, fun p hp q hq hpq => ?_,
    fun d hd => ?_⟩
  · simp only [Finset.mem_coe] at hp hq
    simp only [hp, hq, dite_true] at hpq
    exact congrArg Subtype.val (e.injective (Subtype.ext hpq))
  · simp only [hd, dite_true]
    have := (e ⟨d, hd⟩).2
    simp only [W, Finset.mem_erase] at this
    exact ⟨this.2.1, this.1⟩

/-- **The reduction of Theorem 7** (Theorem 6 of [7] in this instance): if `A` solves `k`-set
agreement under an adversary containing the embedded runs, then `A|D̄` solves consensus among
`D̄`. -/
theorem restrict_solvesConsensus [Fintype P] {k : ℕ} (hV : ∃ f : Fin (k + 1) → V, Function.Injective f)
    {Dset : Finset P} (hDk : Dset.card + 1 = k) {Adv : Set (ℕ → Graph P)}
    {Adv' : Set (ℕ → Graph (Rest Dset))} (hsub : ∀ ρ ∈ Adv', (fun s => emb Dset (ρ s)) ∈ Adv)
    (q₀ : Rest Dset) (A : Alg P V σ) (hA : A.SolvesKSet k Adv) :
    (A.restrict Dset).SolvesConsensus Adv' := by
  classical
  intro y ρ hρ
  have hρ' := hsub ρ hρ
  -- extend inputs
  let ext : (P → V) → P → V := fun c p => if h : p ∈ Dset then c p else y ⟨p, h⟩
  have hext : ∀ c, (fun j : Rest Dset => ext c j.1) = y := fun c => by
    funext j; simp [ext, j.2]
  have hdec : ∀ c i v, (A.restrict Dset).Decides y ρ i v ↔ A.Decides (ext c) (fun s => emb Dset (ρ s)) i.1 v := by
    intro c i v
    unfold Alg.Decides
    simp only [run_emb, hext]
    rfl
  refine ⟨fun S hS => ?_, fun i v hv => ?_, fun i => ?_⟩
  · by_contra hcard
    push Not at hcard
    obtain ⟨u, hu, u', hu', huu⟩ := Finset.one_lt_card.mp hcard
    obtain ⟨c, hcinj, hcav⟩ := exists_inj_avoid hV u u' Dset hDk
    let x := ext c
    -- the processes of `D` decide their inputs `c d`
    have hD : ∀ d ∈ Dset, A.Decides x (fun s => emb Dset (ρ s)) d (c d) := by
      intro d hd
      have := A.decides_own_of_deaf hA x hρ' (i := d) (fun t w h => absurd hd h.2.1)
      simpa [x, ext, hd] using this
    obtain ⟨i, hi⟩ := hS u hu
    obtain ⟨i', hi'⟩ := hS u' hu'
    let S' : Finset V := Dset.image c ∪ {u, u'}
    have hS' := (hA x _ hρ').1 S' (by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
        exact ⟨d, hD d hd⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact ⟨i.1, (hdec c i _).mp hi⟩
        · exact ⟨i'.1, (hdec c i' _).mp hi'⟩)
    have hdisj : Disjoint (Dset.image c) {u, u'} := by
      rw [Finset.disjoint_left]
      intro v hv hv'
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv'
      rcases hv' with h | h
      · exact (hcav d hd).1 h
      · exact (hcav d hd).2 h
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hcinj,
      Finset.card_pair huu] at hS'
    omega
  · obtain ⟨j, hj⟩ := (hA (ext fun _ => y q₀) _ hρ').2.1 i.1 v ((hdec _ i v).mp hv)
    by_cases hjD : j ∈ Dset
    · exact ⟨q₀, by simpa [ext, hjD] using hj⟩
    · exact ⟨⟨j, hjD⟩, by simpa [ext, hjD] using hj⟩
  · obtain ⟨v, hv⟩ := (hA (ext fun _ => y q₀) _ hρ').2.2 i.1
    exact ⟨v, (hdec _ i v).mpr hv⟩

/-- **Theorem 7** of [BRSSW]: for `1 ≤ k < n − 1`, no algorithm solves `k`-set agreement under
`VSRC(k, min{n − k, H} − 1)` (Definition 15, strong reading, any `D ≥ 1`, `H ≥ 2`), even if `k − 1`
root components are vertex-stable all the time. Needs `|V| > k`. -/
theorem theorem7 {n k D H : ℕ} (hk : 1 ≤ k) (hkn : k + 2 ≤ n) (hD : 1 ≤ D) (hH : 2 ≤ H)
    (hV : ∃ f : Fin (k + 1) → V, Function.Injective f) (A : Alg (Fin n) V σ) :
    ¬ A.SolvesKSet k (VSRCkAll D H k (min (n - k) H - 1) ∩
      {ρ | ∃ D₀ : Finset (Fin n), D₀.card = k - 1 ∧ ∀ t, ∀ d ∈ D₀, IsRootComp (ρ t) {d}}) := by
  intro hA
  let Dset : Finset (Fin n) := Finset.univ.filter fun i => i.val < k - 1
  have hDcard : Dset.card = k - 1 := by
    have : Dset = (Finset.range (k - 1)).attachFin (fun m hm => by
        simp at hm; omega) := by
      ext i; simp [Dset]
    rw [this, Finset.card_attachFin, Finset.card_range]
  have hDk : Dset.card + 1 = k := by omega
  let H' := min (n - k) H
  have hrest : Fintype.card (Rest Dset) = n - k + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hDcard, Fintype.card_fin]; omega
  have hH'n : H' + 1 ≤ Fintype.card (Rest Dset) := by rw [hrest]; omega
  let e := finEmb hH'n
  have : Nonempty (Rest Dset) := ⟨e 0⟩
  have hv := hV
  obtain ⟨f, hf⟩ := hv
  have hsub : ∀ ρ ∈ ProdAdv (famT4 H' (e 0)), (fun s => emb Dset (ρ s)) ∈
      (VSRCkAll D H k (min (n - k) H - 1) ∩
        {ρ : ℕ → Graph (Fin n) | ∃ D₀ : Finset (Fin n), D₀.card = k - 1 ∧
          ∀ t, ∀ d ∈ D₀, IsRootComp (ρ t) {d}}) :=
    fun ρ hρ => ⟨emb_mem_VSRCkAll hDk hD (by omega) (by omega) (e 0) hρ, Dset, hDcard,
      fun t d hd => isRootComp_emb_singleton _ hd⟩
  have hcons := restrict_solvesConsensus hV hDk hsub (e 0) A hA
  exact not_solvesConsensus_of_chain_isolation (famT4 H' (e 0)) (chain_famT4 H' (e 0))
    (iso_famT4 (by omega) e) (v₀ := f 0) (v₁ := f 1)
    (fun h => absurd (hf h) (by simp [Fin.ext_iff]; omega)) _ hcons

/-- Theorem 7 for the literal (weak) reading of item (iii) of Definition 15. -/
theorem theorem7_weak {n k D H : ℕ} (hk : 1 ≤ k) (hkn : k + 2 ≤ n) (hD : 1 ≤ D) (hH : 2 ≤ H)
    (hV : ∃ f : Fin (k + 1) → V, Function.Injective f) (A : Alg (Fin n) V σ) :
    ¬ A.SolvesKSet k (VSRCk D H k (min (n - k) H - 1)) := fun h =>
  theorem7 hk hkn hD hH hV A (h.mono fun _ hρ => VSRCkAll_subset _ _ _ _ hρ.1)

end Podc.GracefulKSetAgreement
