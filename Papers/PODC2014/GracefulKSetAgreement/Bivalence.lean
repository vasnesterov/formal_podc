import Papers.PODC2014.GracefulKSetAgreement.Model

/-!
# A generic bivalence argument for consensus under product message adversaries

This is the skeleton of the proof of Theorem 4 (Lemmas 9 and 10 and the induction on rounds), in a
form that makes the admissibility of the constructed runs explicit. The message adversary is a
*product* `ProdAdv Fam`: in round `t + 1` the adversary may choose any graph of `Fam t`,
independently of the other rounds. Two properties of the families suffice for consensus to be
impossible:

* **connectivity** (Lemma 10): any two graphs of `Fam t` are joined by a chain of graphs of `Fam t`
  in which consecutive graphs differ only in the in-neighbourhood of one process (`OneChange`);
* **isolation** (the adversary strategy of Lemma 9): for every round `t` and process `p` there is a
  process `q ≠ p` and an admissible continuation from round `t` in which no information from `p`
  ever reaches `q`.

`not_solvesConsensus_of_chain_isolation`: under these two properties, with at least two input
values, no algorithm solves consensus. The proof follows the paper: valency (`Val`), Lemma 9
(`exists_mem_val_inter`), an initial bivalent configuration (`exists_biv_init`), preservation of
bivalence (`exists_biv_succ`), and a forever-bivalent admissible run, contradicting termination.

-- CSLib candidate (generic bivalence for product message adversaries).
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

variable {P V σ : Type}

/-- `G` and `G'` differ at most in the in-neighbourhood of one process. -/
def OneChange (G G' : Graph P) : Prop := ∃ i, ∀ j, j ≠ i → SameIn G G' j

/-- The product message adversary: in round `t + 1` any graph of `Fam t`. -/
def ProdAdv (Fam : ℕ → Set (Graph P)) : Set (ℕ → Graph P) := {ρ | ∀ t, ρ t ∈ Fam t}

/-- Consecutive graphs of a chain inside `F`. -/
def ChainStep (F : Set (Graph P)) (G G' : Graph P) : Prop := G ∈ F ∧ G' ∈ F ∧ OneChange G G'

namespace Bivalence

variable (A : Alg P V σ) (Fam : ℕ → Set (Graph P))

/-- The valency of the configuration `C` at time `t`: the values decided in admissible
continuations. -/
def Val (t : ℕ) (C : P → σ) : Set V :=
  {v | ∃ τ : ℕ → Graph P, (∀ s, τ s ∈ Fam (t + s)) ∧ ∃ i s, A.dec (conf A.step C τ s i) = some v}

/-- `C` is reachable at time `t` by an admissible prefix. -/
def Reach (t : ℕ) (C : P → σ) : Prop :=
  ∃ x ρ, (∀ s < t, ρ s ∈ Fam s) ∧ A.run x ρ t = C

/-- Bivalence. -/
def Biv (t : ℕ) (C : P → σ) : Prop := ∃ v w, v ∈ Val A Fam t C ∧ w ∈ Val A Fam t C ∧ v ≠ w

variable {A Fam}

theorem reach_ext {t : ℕ} {C : P → σ} (hC : Reach A Fam t C) {τ : ℕ → Graph P}
    (hτ : ∀ s, τ s ∈ Fam (t + s)) :
    ∃ x ρ, ρ ∈ ProdAdv Fam ∧ ∀ s, conf A.step C τ s = A.run x ρ (t + s) := by
  obtain ⟨x, ρ₀, hρ₀, rfl⟩ := hC
  refine ⟨x, splice ρ₀ t τ, fun k => ?_, fun s => ?_⟩
  · unfold splice
    split_ifs with hk
    · exact hρ₀ k hk
    · have := hτ (k - t); rwa [Nat.add_sub_cancel' (by omega)] at this
  · show _ = conf A.step (A.initC x) (splice ρ₀ t τ) (t + s)
    rw [conf_splice]; rfl

theorem reach_succ {t : ℕ} {C : P → σ} (hC : Reach A Fam t C) {G : Graph P} (hG : G ∈ Fam t) :
    Reach A Fam (t + 1) (next A.step G C) := by
  obtain ⟨x, ρ₀, hρ₀, rfl⟩ := hC
  refine ⟨x, Function.update ρ₀ t G, fun s hs => ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · rw [Function.update_of_ne (by omega)]; exact hρ₀ s hs
    · rw [Function.update_self]; exact hG
  · rw [Alg.run, conf_succ, Function.update_self]
    congr 1
    exact conf_congr _ fun k hk => Function.update_of_ne (by omega) _ _

theorem val_succ {t : ℕ} {C : P → σ} {v : V} (hv : v ∈ Val A Fam t C) :
    ∃ G ∈ Fam t, v ∈ Val A Fam (t + 1) (next A.step G C) := by
  obtain ⟨τ, hτ, i, s, hs⟩ := hv
  refine ⟨τ 0, by simpa using hτ 0, shift 1 τ, fun s' => ?_, i, s, ?_⟩
  · have := hτ (1 + s'); rwa [← Nat.add_assoc] at this
  · have h := A.dec_conf_mono hs (Nat.le_succ s)
    rw [show s.succ = 1 + s by omega, conf_add] at h
    exact h

theorem reach_init (x : P → V) : Reach A Fam 0 (A.initC x) :=
  ⟨x, fun _ _ _ => False, fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩

variable (hA : A.SolvesConsensus (ProdAdv Fam))
include hA

theorem agree_of_reach {t : ℕ} {C : P → σ} (hC : Reach A Fam t C) {τ : ℕ → Graph P}
    (hτ : ∀ s, τ s ∈ Fam (t + s)) {i j : P} {s s' : ℕ} {v w : V}
    (hi : A.dec (conf A.step C τ s i) = some v) (hj : A.dec (conf A.step C τ s' j) = some w) :
    v = w := by
  classical
  obtain ⟨x, ρ, hρ, hrun⟩ := reach_ext hC hτ
  by_contra hvw
  have := (hA x ρ hρ).1 {v, w} (by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact ⟨i, t + s, by rw [← hrun]; exact hi⟩
    · exact ⟨j, t + s', by rw [← hrun]; exact hj⟩)
  rw [Finset.card_pair hvw] at this
  omega

theorem term_of_reach {t : ℕ} {C : P → σ} (hC : Reach A Fam t C) {τ : ℕ → Graph P}
    (hτ : ∀ s, τ s ∈ Fam (t + s)) (i : P) : ∃ s v, A.dec (conf A.step C τ s i) = some v := by
  obtain ⟨x, ρ, hρ, hrun⟩ := reach_ext hC hτ
  obtain ⟨v, T, hT⟩ := (hA x ρ hρ).2.2 i
  refine ⟨T, v, ?_⟩
  rw [hrun]
  exact A.dec_conf_mono hT (by omega)

/-- **Lemma 9 (core).** Two reachable configurations at the same time that differ only in the
state of `p` share a value of their valencies: the adversary isolates some `q ≠ p` from `p`. -/
theorem exists_mem_val_inter
    (hiso : ∀ t p, ∃ q, q ≠ p ∧ ∃ τ : ℕ → Graph P, (∀ s, τ s ∈ Fam (t + s)) ∧
      ∀ s, ¬ Journey τ 0 p s q)
    {t : ℕ} {C₁ C₂ : P → σ} (h₁ : Reach A Fam t C₁) (_h₂ : Reach A Fam t C₂) (p : P)
    (hC : ∀ i, i ≠ p → C₁ i = C₂ i) : ∃ u, u ∈ Val A Fam t C₁ ∧ u ∈ Val A Fam t C₂ := by
  obtain ⟨q, hqp, τ, hτ, hj⟩ := hiso t p
  have heq : ∀ s, conf A.step C₁ τ s q = conf A.step C₂ τ s q := fun s =>
    conf_eq_of_not_journey A.step τ {p} (fun i hi => hC i hi) s q
      (fun p' hp' => by rw [Set.mem_singleton_iff] at hp'; subst hp'; exact hj s)
  obtain ⟨s, u, hu⟩ := term_of_reach hA h₁ hτ q
  exact ⟨u, ⟨τ, hτ, q, s, hu⟩, ⟨τ, hτ, q, s, heq s ▸ hu⟩⟩

theorem val_nonempty (hiso : ∀ t p, ∃ q, q ≠ p ∧ ∃ τ : ℕ → Graph P, (∀ s, τ s ∈ Fam (t + s)) ∧
      ∀ s, ¬ Journey τ 0 p s q) [Nonempty P]
    {t : ℕ} {C : P → σ} (hC : Reach A Fam t C) : ∃ v, v ∈ Val A Fam t C := by
  obtain ⟨q, -, τ, hτ, -⟩ := hiso t (Classical.arbitrary P)
  obtain ⟨s, v, hv⟩ := term_of_reach hA hC hτ q
  exact ⟨v, τ, hτ, q, s, hv⟩

/-- **Bivalence is preserved** (the induction step of Theorem 4, via Lemmas 10 and 9). -/
theorem exists_biv_succ
    (hchain : ∀ t, ∀ G ∈ Fam t, ∀ G' ∈ Fam t, Relation.ReflTransGen (ChainStep (Fam t)) G G')
    (hiso : ∀ t p, ∃ q, q ≠ p ∧ ∃ τ : ℕ → Graph P, (∀ s, τ s ∈ Fam (t + s)) ∧
      ∀ s, ¬ Journey τ 0 p s q)
    {t : ℕ} {C : P → σ} (hC : Reach A Fam t C) (hB : Biv A Fam t C) :
    ∃ G ∈ Fam t, Biv A Fam (t + 1) (next A.step G C) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨v, w, hv, hw, hvw⟩ := hB
  obtain ⟨G₁, hG₁, hv₁⟩ := val_succ hv
  obtain ⟨G₂, hG₂, hw₂⟩ := val_succ hw
  have key : ∀ G, Relation.ReflTransGen (ChainStep (Fam t)) G₁ G →
      v ∈ Val A Fam (t + 1) (next A.step G C) := by
    intro G hG
    induction hG with
    | refl => exact hv₁
    | @tail b c _ hstep ih =>
      obtain ⟨hb, hc, i, hi⟩ := hstep
      obtain ⟨u, hub, huc⟩ := exists_mem_val_inter hA hiso (reach_succ hC hb) (reach_succ hC hc) i
        (fun j hj => next_eq_of_agree (hi j hj) fun _ _ => rfl)
      have hnb := hcon b hb
      have : u = v := by
        by_contra huv
        exact hnb ⟨u, v, hub, ih, huv⟩
      exact this ▸ huc
  exact hcon G₂ hG₂ ⟨v, w, key G₂ (hchain t G₁ hG₁ G₂ hG₂), hw₂, hvw⟩

/-- The valency of an initial configuration consists of inputs (validity). -/
theorem val_init_subset (x : P → V) {v : V} (hv : v ∈ Val A Fam 0 (A.initC x)) : ∃ j, x j = v := by
  obtain ⟨τ, hτ, i, s, hs⟩ := hv
  exact (hA x τ (fun k => by simpa using hτ k)).2.1 i v ⟨s, hs⟩

/-- **Initial bivalence** (base case of Theorem 4). -/
theorem exists_biv_init [Fintype P] [Nonempty P]
    (hiso : ∀ t p, ∃ q, q ≠ p ∧ ∃ τ : ℕ → Graph P, (∀ s, τ s ∈ Fam (t + s)) ∧
      ∀ s, ¬ Journey τ 0 p s q)
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) : ∃ x : P → V, Biv A Fam 0 (A.initC x) := by
  classical
  let e := Fintype.equivFin P
  let X : ℕ → P → V := fun m i => if (e i).val < m then v₁ else v₀
  by_contra hcon
  push Not at hcon
  have hnb : ∀ m, ∀ a b, a ∈ Val A Fam 0 (A.initC (X m)) → b ∈ Val A Fam 0 (A.initC (X m)) →
      a = b := fun m a b ha hb => by
    by_contra hab; exact hcon (X m) ⟨a, b, ha, hb, hab⟩
  have h0 : v₀ ∈ Val A Fam 0 (A.initC (X 0)) := by
    obtain ⟨u, hu⟩ := val_nonempty hA hiso (reach_init (X 0))
    obtain ⟨j, hj⟩ := val_init_subset hA _ hu
    simp [X] at hj
    exact hj ▸ hu
  have hstep : ∀ m, v₀ ∈ Val A Fam 0 (A.initC (X m)) → v₀ ∈ Val A Fam 0 (A.initC (X (m + 1))) := by
    intro m hm
    by_cases hmN : m < Fintype.card P
    · obtain ⟨u, hu₁, hu₂⟩ := exists_mem_val_inter hA hiso (reach_init (X m))
        (reach_init (X (m + 1))) (e.symm ⟨m, hmN⟩) (fun i hi => by
          have : (e i).val ≠ m := fun h => hi (by
            rw [← e.symm_apply_apply i]; congr 1; exact Fin.ext h)
          simp only [Alg.initC, X]
          congr 1
          split_ifs <;> first | rfl | omega)
      exact (hnb m u v₀ hu₁ hm) ▸ hu₂
    · have : X (m + 1) = X m := by
        funext i; simp only [X]
        have := (e i).isLt
        split_ifs <;> first | rfl | omega
      rw [this]; exact hm
  have hall : ∀ m, v₀ ∈ Val A Fam 0 (A.initC (X m)) := fun m => by
    induction m with
    | zero => exact h0
    | succ m ih => exact hstep m ih
  obtain ⟨j, hj⟩ := val_init_subset hA _ (hall (Fintype.card P))
  simp only [X, (e j).isLt, ite_true] at hj
  exact hv hj.symm

end Bivalence

open Bivalence in
/-- **Generic impossibility of consensus** (the proof scheme of Theorem 4): under a product
message adversary whose round families are chain-connected (Lemma 10) and allow isolating some
`q ≠ p` from any `p` (Lemma 9), no algorithm solves consensus, provided there are two input
values. -/
theorem not_solvesConsensus_of_chain_isolation [Fintype P] [Nonempty P]
    (Fam : ℕ → Set (Graph P))
    (hchain : ∀ t, ∀ G ∈ Fam t, ∀ G' ∈ Fam t, Relation.ReflTransGen (ChainStep (Fam t)) G G')
    (hiso : ∀ t p, ∃ q, q ≠ p ∧ ∃ τ : ℕ → Graph P, (∀ s, τ s ∈ Fam (t + s)) ∧
      ∀ s, ¬ Journey τ 0 p s q)
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) (A : Alg P V σ) : ¬ A.SolvesConsensus (ProdAdv Fam) := by
  intro hA
  obtain ⟨x₀, hx₀⟩ := exists_biv_init hA hiso hv
  let B : ℕ → Type := fun t => {C : P → σ // Reach A Fam t C ∧ Biv A Fam t C}
  have hs : ∀ t (C : B t), ∃ G ∈ Fam t, Reach A Fam (t + 1) (next A.step G C.1) ∧
      Biv A Fam (t + 1) (next A.step G C.1) := fun t C => by
    obtain ⟨G, hG, hb⟩ := exists_biv_succ hA hchain hiso C.2.1 C.2.2
    exact ⟨G, hG, reach_succ C.2.1 hG, hb⟩
  let g : ∀ t, B t → Graph P := fun t C => Classical.choose (hs t C)
  have hg : ∀ t (C : B t), g t C ∈ Fam t ∧ Reach A Fam (t + 1) (next A.step (g t C) C.1) ∧
      Biv A Fam (t + 1) (next A.step (g t C) C.1) := fun t C => Classical.choose_spec (hs t C)
  let c : ∀ t, B t := fun t => Nat.rec (motive := B) ⟨A.initC x₀, reach_init x₀, hx₀⟩
    (fun t C => ⟨next A.step (g t C) C.1, (hg t C).2⟩) t
  let ρ : ℕ → Graph P := fun t => g t (c t)
  have hρ : ρ ∈ ProdAdv Fam := fun t => (hg t (c t)).1
  have hrun : ∀ t, A.run x₀ ρ t = (c t).1 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [Alg.run, conf_succ, ← Alg.run, ih]
  obtain ⟨v, T, hT⟩ := (hA x₀ ρ hρ).2.2 (Classical.arbitrary P)
  rw [hrun] at hT
  obtain ⟨a, b, ⟨τa, hτa, ia, sa, ha⟩, ⟨τb, hτb, ib, sb, hb⟩, hab⟩ := (c T).2.2
  have h1 := agree_of_reach hA (c T).2.1 hτa (s := 0) (by simpa using hT) ha
  have h2 := agree_of_reach hA (c T).2.1 hτb (s := 0) (by simpa using hT) hb
  exact hab (h1.symm.trans h2)

end Podc.GracefulKSetAgreement
