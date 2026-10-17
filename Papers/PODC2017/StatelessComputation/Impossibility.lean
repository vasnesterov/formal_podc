import Papers.PODC2017.StatelessComputation.Model

/-!
# Theorem 3.1: two stable labelings rule out label (n-1)-stabilization

Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017, Section 3.

**Theorem 3.1.** No stateless protocol with at least two distinct stable labelings is label
`(n-1)`-stabilizing.

We follow the paper's valency argument on the space of states `(ℓ, c)` (labeling, countdown
vector), restricted to the subspace `H` of countdowns whose increasing rearrangement dominates
`(1, 2, …, r-1, r, r)` (`r = n - 1`). The paper's proof needs repairs (see `differencies.md`):

* valency ("attractor regions") is taken with respect to paths *inside* `H`; then Lemma 3.2's
  single-node activation (which leaves `H`) is replaced by an application of Lemma 3.3;
* the paper claims that the `H`-successors of a state are *all* activation sets `T` with
  `|T| ≥ 2` (containing the node with countdown `1`); this is false (e.g. `r = 4`,
  countdowns `(2,2,4,4,4)`, `T` = two of the nodes with countdown `4`). What is true, and
  suffices, is that the admissible sets are **upward closed** (`Good.mono`, `cd_mono_set`), so any
  two of them are connected through `univ` by single-node insertions;
* Lemma 3.3 is stated with valency w.r.t. `H`-paths, which every `r`-fair execution from an
  arbitrary labeling with a countdown `≤ r` is (`hpath_fair`).

The countdown `c v` is the number of steps within which node `v` must still be activated.
`Good r c` encodes "sorted `c` dominates `(1, …, r-1, r, r)`" as
`∀ k < r, #{v | c v ≤ k} ≤ k` (plus `c ≤ r`).
-/

namespace StatelessComputation
namespace Impossibility

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Countdown vectors -/

/-- Countdown update after activating `T`. -/
def cd (r : ℕ) (c : V → ℕ) (T : Finset V) : V → ℕ := fun v => if v ∈ T then r else c v - 1

/-- The countdowns of the restricted state space `H` (sorted `c` dominates `(1,…,r-1,r,r)`). -/
def Good (r : ℕ) (c : V → ℕ) : Prop :=
  (∀ v, c v ≤ r) ∧ ∀ k < r, (univ.filter fun v => c v ≤ k).card ≤ k

omit [DecidableEq V] in
lemma Good.pos {r : ℕ} {c : V → ℕ} (h : Good r c) (hr : 0 < r) (v : V) : 1 ≤ c v := by
  by_contra hv
  have h0 := h.2 0 hr
  have hmem : v ∈ univ.filter fun v => c v ≤ 0 := by simp; omega
  have := Finset.card_pos.2 ⟨v, hmem⟩
  omega

omit [DecidableEq V] in
lemma Good.mono {r : ℕ} {a b : V → ℕ} (ha : Good r a) (hab : ∀ v, a v ≤ b v)
    (hb : ∀ v, b v ≤ r) : Good r b :=
  ⟨hb, fun k hk => (card_le_card (fun v hv => by
    simp only [mem_filter, mem_univ, true_and] at hv ⊢; exact (hab v).trans hv)).trans
    (ha.2 k hk)⟩

omit [Fintype V] in
lemma cd_le {r : ℕ} {c : V → ℕ} (hc : ∀ v, c v ≤ r) (T : Finset V) (v : V) : cd r c T v ≤ r := by
  unfold cd; split_ifs <;> have := hc v <;> omega

omit [Fintype V] in
lemma cd_mono_set {r : ℕ} {c : V → ℕ} (hc : ∀ v, c v ≤ r) {T T' : Finset V} (h : T ⊆ T')
    (v : V) : cd r c T v ≤ cd r c T' v := by
  unfold cd
  by_cases hv : v ∈ T
  · simp [hv, h hv]
  · simp only [hv, ite_false]; split_ifs <;> have := hc v <;> omega

omit [Fintype V] in
lemma cd_mono {r : ℕ} {a b : V → ℕ} (hab : ∀ v, a v ≤ b v) (T : Finset V) (v : V) :
    cd r a T v ≤ cd r b T v := by
  unfold cd; split_ifs <;> have := hab v <;> omega

lemma good_cd_univ (r : ℕ) (c : V → ℕ) : Good r (cd r c univ) := by
  refine ⟨fun v => by simp [cd], fun k hk => ?_⟩
  have : (univ.filter fun v => cd r c univ v ≤ k) = ∅ := by
    ext v
    simp only [mem_filter, mem_univ, true_and, cd, ite_true, Finset.notMem_empty, iff_false]
    omega
  simp [this]

/-- The key counting step of Lemma 3.3: activating `j` together with a node `j'` of minimal
countdown among the others keeps the countdown in `H`. -/
lemma good_cd_pair {r : ℕ} (hn : Fintype.card V = r + 1) {c : V → ℕ} (hc : Good r c)
    {j j' : V} (hjj : j' ≠ j) (hmin : ∀ v, v ≠ j → c j' ≤ c v) : Good r (cd r c {j, j'}) := by
  refine ⟨cd_le hc.1 _, fun k hk => ?_⟩
  set A := univ.filter fun v => c v ≤ k + 1 with hA
  have hsub : (univ.filter fun v => cd r c {j, j'} v ≤ k) ⊆ A \ {j, j'} := by
    intro v hv
    rw [mem_filter] at hv
    simp only [cd] at hv
    split_ifs at hv with hvT
    · omega
    · simp only [mem_sdiff, hA, mem_filter, mem_univ, true_and]; exact ⟨by omega, hvT⟩
  refine (card_le_card hsub).trans ?_
  by_cases hkr : k + 1 < r
  · have hAk : A.card ≤ k + 1 := hc.2 (k + 1) hkr
    by_cases hw : c j ≤ k + 1 ∨ c j' ≤ k + 1
    · obtain ⟨w, hwA, hwT⟩ : ∃ w ∈ A, w ∈ ({j, j'} : Finset V) := by
        rcases hw with hw | hw
        · exact ⟨j, by simp [hA, hw], by simp⟩
        · exact ⟨j', by simp [hA, hw], by simp⟩
      have : A \ {j, j'} ⊆ A.erase w := fun v hv => by
        rw [mem_sdiff] at hv
        exact mem_erase.2 ⟨fun h => hv.2 (h ▸ hwT), hv.1⟩
      have h2 := card_le_card this
      rw [card_erase_of_mem hwA] at h2
      omega
    · push Not at hw
      have : A \ {j, j'} = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
        rw [mem_sdiff, mem_insert, mem_singleton, not_or] at hv
        have h1 : c v ≤ k + 1 := by simpa [hA] using hv.1
        have := hmin v hv.2.1
        omega
      simp [this]
  · have hk' : k + 1 = r := by omega
    have : A \ {j, j'} ⊆ ({j, j'} : Finset V)ᶜ := fun v hv => by
      rw [mem_sdiff] at hv; exact mem_compl.2 hv.2
    refine (card_le_card this).trans ?_
    rw [card_compl, card_pair hjj.symm]
    omega

/-- Existence of a partner `j' ≠ j` of minimal countdown among the nodes other than `j`. -/
lemma exists_partner (hn : 2 ≤ Fintype.card V) (c : V → ℕ) (j : V) :
    ∃ j', j' ≠ j ∧ ∀ v, v ≠ j → c j' ≤ c v := by
  have hne : (univ.erase j).Nonempty := by
    rw [← card_pos, card_erase_of_mem (mem_univ j), card_univ]; omega
  obtain ⟨j', hj', hmin⟩ := (univ.erase j).exists_min_image c hne
  exact ⟨j', (mem_erase.1 hj').1, fun v hv => hmin v (mem_erase.2 ⟨hv, mem_univ v⟩)⟩

/-- The partner of `j` w.r.t. countdown `c` (some `j' ≠ j` with minimal `c j'`). -/
noncomputable def partner (hn : 2 ≤ Fintype.card V) (c : V → ℕ) (j : V) : V :=
  (exists_partner hn c j).choose

lemma partner_ne (hn : 2 ≤ Fintype.card V) (c : V → ℕ) (j : V) : partner hn c j ≠ j :=
  (exists_partner hn c j).choose_spec.1

lemma partner_min (hn : 2 ≤ Fintype.card V) (c : V → ℕ) (j : V) :
    ∀ v, v ≠ j → c (partner hn c j) ≤ c v :=
  (exists_partner hn c j).choose_spec.2

/-! ### The restricted state graph `H` -/

variable {L X Y : Type*} {G : Digraph V} (P : Protocol G L X Y) (x : V → X) (r : ℕ)

/-- States: a labeling and a countdown vector. -/
abbrev State (G : Digraph V) (L : Type*) := Labeling G L × (V → ℕ)

/-- The successor of `s` when `T` is activated. -/
def succ (s : State G L) (T : Finset V) : State G L := (P.step x s.1 T, cd r s.2 T)

/-- An edge of `H`. -/
def HStep (s s' : State G L) : Prop :=
  Good r s.2 ∧ ∃ T, Good r (cd r s.2 T) ∧ s' = succ P x r s T

/-- Reachability in `H`. -/
def Reach : State G L → State G L → Prop := Relation.ReflTransGen (HStep P x r)

/-- An infinite path in `H`, with activation sets `T`. -/
def HPath (s : ℕ → State G L) (T : ℕ → Finset V) : Prop :=
  ∀ t, Good r (s t).2 ∧ s (t + 1) = succ P x r (s t) (T t)

/-- The valency of a state: the stable labelings reachable from it in `H`. -/
def val (s : State G L) : Set (Labeling G L) :=
  {m | P.IsStable x m ∧ ∃ s', Reach P x r s s' ∧ s'.1 = m}

variable {P x r}

lemma HPath.reach {s : ℕ → State G L} {T : ℕ → Finset V} (h : HPath P x r s T) (t : ℕ) :
    Reach P x r (s 0) (s t) := by
  induction t with
  | zero => exact Relation.ReflTransGen.refl
  | succ t ih =>
    refine ih.tail ⟨(h t).1, T t, ?_, (h t).2⟩
    have := (h (t + 1)).1
    rw [(h t).2] at this
    exact this

lemma HPath.run_eq {s : ℕ → State G L} {T : ℕ → Finset V} (h : HPath P x r s T) (t : ℕ) :
    (s t).1 = P.run x (s 0).1 T t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [(h t).2, Protocol.run_succ, ← ih]; rfl

-- CSLib candidate: countdown-graph encoding of `r`-fair schedules.
/-- Every path in `H` is an `r`-fair schedule (with `n = r + 1` nodes). -/
lemma HPath.fair (hn : Fintype.card V = r + 1) (hr : 1 ≤ r) {s : ℕ → State G L}
    {T : ℕ → Finset V} (h : HPath P x r s T) : IsRFair r T := by
  refine ⟨fun t => ?_, fun t v => ?_⟩
  · by_contra hT
    rw [Finset.not_nonempty_iff_eq_empty] at hT
    have hg := (h (t + 1)).1.2 (r - 1) (by omega)
    have hall : (univ.filter fun v => (s (t + 1)).2 v ≤ r - 1) = univ := by
      ext v
      simp only [mem_filter, mem_univ, true_and, iff_true]
      rw [(h t).2]
      simp only [succ, cd, hT, Finset.notMem_empty, ite_false]
      have := (h t).1.1 v; omega
    rw [hall, card_univ] at hg
    omega
  · by_contra hv
    push Not at hv
    simp only [Finset.mem_coe] at hv
    have key : ∀ k, k ≤ r → (s (t + k)).2 v = (s t).2 v - k := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [← add_assoc, (h (t + k)).2]
        simp only [succ, cd, hv (t + k) (by omega) (by omega), ite_false]
        rw [ih (by omega)]; omega
    have h1 := (h (t + r)).1.pos (by omega) v
    have h2 := key r le_rfl
    have h3 := (h t).1.1 v
    omega

/-- Two subsingleton sets with a common element are equal. -/
lemma _root_.Set.Subsingleton.eq_of_mem {α : Type*} {A B : Set α} (hA : A.Subsingleton)
    (hB : B.Subsingleton) {z : α} (hzA : z ∈ A) (hzB : z ∈ B) : A = B := by
  rw [hA.eq_singleton_of_mem hzA, hB.eq_singleton_of_mem hzB]

/-- Bivalent states. -/
def Biv (P : Protocol G L X Y) (x : V → X) (r : ℕ) (s : State G L) : Prop :=
  ∃ m₁ m₂, m₁ ∈ val P x r s ∧ m₂ ∈ val P x r s ∧ m₁ ≠ m₂

variable (hloop : ∀ v, ¬ G.Adj v v) (hn : Fintype.card V = r + 1) (hr : 1 ≤ r)
  (hstab : ∀ ℓ0 σ, IsRFair r σ → Converges (P.run x ℓ0 σ))
include hn hr hstab

/-- Under `r`-stabilization, every path in `H` eventually stays at a stable labeling. -/
lemma HPath.converges {s : ℕ → State G L} {T : ℕ → Finset V} (h : HPath P x r s T) :
    ∃ t0 m, P.IsStable x m ∧ ∀ t, t0 ≤ t → (s t).1 = m := by
  obtain ⟨m, t0, hm⟩ := converges_iff.1 (hstab _ _ (h.fair hn hr))
  have hm' : ∀ t, t0 ≤ t → (s t).1 = m := fun t ht => by rw [h.run_eq]; exact hm t ht
  refine ⟨t0, m, fun i w => ?_, hm'⟩
  obtain ⟨u, hu1, -, hu3⟩ := (h.fair hn hr).2 t0 i
  have e1 := hm' (u + 1) (by omega)
  rw [(h u).2] at e1
  simp only [succ] at e1
  rw [hm' u hu1] at e1
  have := congrArg (fun ℓ => ℓ ⟨(i, w.1), w.2⟩) e1
  rwa [Protocol.step_of_mem P x (by exact hu3)] at this

omit hn hr hstab in
lemma reach_of_stable {s s' : State G L} (hs : P.IsStable x s.1) (h : Reach P x r s s') :
    s'.1 = s.1 := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨-, T, -, rfl⟩ := hst
    simp only [succ]; rw [← ih] at hs ⊢; exact Protocol.IsStable.step_eq P x hs T

omit hn hr hstab in
lemma val_subset_of_stable {s : State G L} (hs : P.IsStable x s.1) : val P x r s ⊆ {s.1} :=
  fun _ ⟨_, _, hr, he⟩ => by rw [← he, reach_of_stable hs hr]; rfl

omit hn hr hstab in
lemma val_mono {s s' : State G L} (h : Reach P x r s s') : val P x r s' ⊆ val P x r s :=
  fun _ ⟨hm, s'', h', he⟩ => ⟨hm, s'', h.trans h', he⟩

/-- Valencies are nonempty (run synchronously from `s`). -/
lemma val_nonempty {s : State G L} (hs : Good r s.2) : (val P x r s).Nonempty := by
  let seq : ℕ → State G L := fun t => (fun s => succ P x r s univ)^[t] s
  have hseq : HPath P x r seq (fun _ => univ) := by
    intro t
    refine ⟨?_, Function.iterate_succ_apply' _ _ _⟩
    cases t with
    | zero => exact hs
    | succ t =>
      simp only [seq, Function.iterate_succ_apply']
      exact good_cd_univ r _
  obtain ⟨t0, m, hm, hmt⟩ := hseq.converges hn hr hstab
  exact ⟨m, hm, seq t0, hseq.reach t0, hmt t0 le_rfl⟩

include hloop

/-- Lemma 3.3 (repaired): two states of `H` whose labelings differ only on the outgoing arcs
of one node `j`, with pointwise smaller countdown on the left, have a common reachable stable
labeling. -/
lemma common_val {ℓ ℓ' : Labeling G L} {a b : V → ℕ} (ha : Good r a) (hb : Good r b)
    (hab : ∀ v, a v ≤ b v) {j : V} (hdiff : ∀ e : Arc G, ℓ e ≠ ℓ' e → e.1.1 = j) :
    ∃ m, m ∈ val P x r (ℓ, a) ∧ m ∈ val P x r (ℓ', b) := by
  have hn2 : 2 ≤ Fintype.card V := by omega
  -- the joint sequence (state 1, state 2, distinguished node)
  let nxt : State G L × State G L × V → State G L × State G L × V := fun p =>
    let j' := partner hn2 p.1.2 p.2.2
    (succ P x r p.1 {p.2.2, j'}, succ P x r p.2.1 {p.2.2, j'}, j')
  let seq : ℕ → State G L × State G L × V := fun t => nxt^[t] ((ℓ, a), (ℓ', b), j)
  have hseq : ∀ t, seq (t + 1) = nxt (seq t) := fun t => Function.iterate_succ_apply' _ _ _
  let Inv : State G L × State G L × V → Prop := fun p =>
    Good r p.1.2 ∧ Good r p.2.1.2 ∧ (∀ v, p.1.2 v ≤ p.2.1.2 v) ∧
      ∀ e : Arc G, p.1.1 e ≠ p.2.1.1 e → e.1.1 = p.2.2
  have hinv : ∀ t, Inv (seq t) := by
    intro t
    induction t with
    | zero => exact ⟨ha, hb, hab, hdiff⟩
    | succ t ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      rw [hseq]
      set p := seq t
      have hne := partner_ne hn2 p.1.2 p.2.2
      have hg : Good r (cd r p.1.2 {p.2.2, partner hn2 p.1.2 p.2.2}) :=
        good_cd_pair hn h1 hne (partner_min hn2 _ _)
      refine ⟨hg, hg.mono (cd_mono h3 _) (cd_le h2.1 _), cd_mono h3 _, ?_⟩
      intro e he
      simp only [nxt, succ] at he ⊢
      by_cases heT : e.1.1 ∈ ({p.2.2, partner hn2 p.1.2 p.2.2} : Finset V)
      · rw [Protocol.step_of_mem P x heT, Protocol.step_of_mem P x heT] at he
        rcases mem_insert.1 heT with hj | hj
        · exfalso
          have hin : inLab p.1.1 e.1.1 = inLab p.2.1.1 e.1.1 := by
            funext w
            by_contra hw
            have h5 : w.1 = e.1.1 := (h4 _ hw).trans hj.symm
            have hw2 := w.2
            rw [h5] at hw2
            exact hloop _ hw2
          rw [hin] at he
          exact he rfl
        · exact mem_singleton.1 hj
      · rw [Protocol.step_of_not_mem P x heT, Protocol.step_of_not_mem P x heT] at he
        exact absurd (mem_insert.2 (Or.inl (h4 e he))) heT
  -- both components are `H`-paths
  let T : ℕ → Finset V := fun t => {(seq t).2.2, partner hn2 (seq t).1.2 (seq t).2.2}
  have hp1 : HPath P x r (fun t => (seq t).1) T := fun t =>
    ⟨(hinv t).1, by show (seq (t + 1)).1 = _; rw [hseq]⟩
  have hp2 : HPath P x r (fun t => (seq t).2.1) T := fun t =>
    ⟨(hinv t).2.1, by show (seq (t + 1)).2.1 = _; rw [hseq]⟩
  obtain ⟨t1, m1, hm1, ht1⟩ := hp1.converges hn hr hstab
  obtain ⟨t2, m2, hm2, ht2⟩ := hp2.converges hn hr hstab
  set t := max t1 t2
  have e1 : (seq t).1.1 = m1 := ht1 t (le_max_left _ _)
  have e1' : (seq (t + 1)).1.1 = m1 := ht1 (t + 1) (by omega)
  have e2 : (seq t).2.1.1 = m2 := ht2 t (le_max_right _ _)
  have e2' : (seq (t + 1)).2.1.1 = m2 := ht2 (t + 1) (by omega)
  have hm : m1 = m2 := by
    funext e
    by_contra he
    have d1 := (hinv t).2.2.2 e (by rw [e1, e2]; exact he)
    have d2 := (hinv (t + 1)).2.2.2 e (by rw [e1', e2']; exact he)
    rw [hseq] at d2
    exact partner_ne hn2 (seq t).1.2 (seq t).2.2 (d2.symm.trans d1)
  refine ⟨m1, ⟨hm1, (seq t).1, hp1.reach t, e1⟩, ⟨hm1, (seq t).2.1, hp2.reach t, ?_⟩⟩
  rw [e2, hm]

/-- Lemma 3.2 (repaired): some state of `H` is bivalent. -/
lemma exists_biv {ℓ₁ ℓ₂ : Labeling G L} (h₁ : P.IsStable x ℓ₁) (h₂ : P.IsStable x ℓ₂)
    (hne : ℓ₁ ≠ ℓ₂) : ∃ s : State G L, Good r s.2 ∧ Biv P x r s := by
  by_contra hcon
  push Not at hcon
  have huni : ∀ s : State G L, Good r s.2 → (val P x r s).Subsingleton := by
    intro s hs m₁ hm₁ m₂ hm₂
    by_contra h
    exact hcon s hs ⟨m₁, m₂, hm₁, hm₂, h⟩
  let full : V → ℕ := fun _ => r
  have hfull : Good r full := by
    have : full = cd r full univ := by funext v; simp [cd, full]
    rw [this]; exact good_cd_univ r _
  let hyb : Finset (V × V) → Labeling G L := fun S e => if e.1 ∈ S then ℓ₁ e else ℓ₂ e
  have key : ∀ S, val P x r (hyb S, full) = val P x r (hyb ∅, full) := by
    intro S
    induction S using Finset.induction_on with
    | empty => rfl
    | insert e S he ih =>
      rw [← ih]
      obtain ⟨m, hm1, hm2⟩ := common_val (P := P) (x := x) hloop hn hr hstab
        (ℓ := hyb (insert e S)) (ℓ' := hyb S) hfull hfull (fun _ => le_rfl) (j := e.1)
        (fun e' he' => by
          simp only [hyb, mem_insert] at he'
          by_cases h : e'.1 = e
          · rw [h]
          · simp [h] at he')
      exact (huni _ hfull).eq_of_mem (huni _ hfull) hm1 hm2
  have k1 := key univ
  have hu : hyb univ = ℓ₁ := by funext e; simp [hyb]
  have he : hyb ∅ = ℓ₂ := by funext e; simp [hyb]
  rw [hu, he] at k1
  have v1 : ℓ₁ ∈ val P x r (ℓ₁, full) := ⟨h₁, _, Relation.ReflTransGen.refl, rfl⟩
  rw [k1] at v1
  exact hne (val_subset_of_stable (s := (ℓ₂, full)) h₂ v1)

omit hloop in
/-- Lemma 3.4: some bivalent state of `H` has only non-bivalent `H`-successors. -/
lemma exists_critical {s0 : State G L} (hs0 : Good r s0.2) (hb0 : Biv P x r s0) :
    ∃ s : State G L, Good r s.2 ∧ Biv P x r s ∧
      ∀ T, Good r (cd r s.2 T) → ¬ Biv P x r (succ P x r s T) := by
  by_contra hcon
  push Not at hcon
  -- choose a bivalent successor forever
  have hch : ∀ s : {s : State G L // Good r s.2 ∧ Biv P x r s},
      ∃ T, Good r (cd r s.1.2 T) ∧ Biv P x r (succ P x r s.1 T) :=
    fun s => hcon s.1 s.2.1 s.2.2
  choose Tf hTf using hch
  let nxt : {s : State G L // Good r s.2 ∧ Biv P x r s} →
      {s : State G L // Good r s.2 ∧ Biv P x r s} :=
    fun s => ⟨succ P x r s.1 (Tf s), (hTf s).1, (hTf s).2⟩
  let seq : ℕ → {s : State G L // Good r s.2 ∧ Biv P x r s} :=
    fun t => nxt^[t] ⟨s0, hs0, hb0⟩
  have hp : HPath P x r (fun t => (seq t).1) (fun t => Tf (seq t)) := fun t =>
    ⟨(seq t).2.1, by simp only [seq, Function.iterate_succ_apply']; rfl⟩
  obtain ⟨t0, m, hm, hmt⟩ := hp.converges hn hr hstab
  obtain ⟨m₁, m₂, h₁, h₂, h12⟩ := (seq t0).2.2
  have hs : P.IsStable x (seq t0).1.1 := by rw [hmt t0 le_rfl]; exact hm
  have := val_subset_of_stable (r := r) hs
  exact h12 ((this h₁).trans (this h₂).symm)

/-- **Theorem 3.1** (core): under the hypotheses of this section, a protocol that is label
`r`-stabilizing for `r = n - 1` (in the sense `hstab`) has at most one stable labeling. -/
theorem stable_unique {ℓ₁ ℓ₂ : Labeling G L} (h₁ : P.IsStable x ℓ₁) (h₂ : P.IsStable x ℓ₂) :
    ℓ₁ = ℓ₂ := by
  by_contra hne
  obtain ⟨s0, hs0, hb0⟩ := exists_biv hloop hn hr hstab h₁ h₂ hne
  obtain ⟨s, hs, ⟨m₁, m₂, hm₁, hm₂, h12⟩, hcrit⟩ := exists_critical hn hr hstab hs0 hb0
  -- successors are univalent
  have huni : ∀ T, Good r (cd r s.2 T) → (val P x r (succ P x r s T)).Subsingleton := by
    intro T hT a ha b hb
    by_contra h
    exact hcrit T hT ⟨a, b, ha, hb, h⟩
  -- the labeling of `s` is not stable
  have hns : ¬ P.IsStable x s.1 := fun h => h12 ((val_subset_of_stable h hm₁).trans
    (val_subset_of_stable h hm₂).symm)
  -- every element of `val s` lies in the valency of some admissible successor
  have hsplit : ∀ m ∈ val P x r s, ∃ T, Good r (cd r s.2 T) ∧ m ∈ val P x r (succ P x r s T) := by
    rintro m ⟨hm, s', hr', he⟩
    rcases Relation.ReflTransGen.cases_head hr' with h | ⟨s'', ⟨-, T, hT, rfl⟩, h''⟩
    · subst h; exact absurd (he ▸ hm) hns
    · exact ⟨T, hT, hm, s', h'', he⟩
  -- all admissible successors have the valency of the synchronous successor
  have hall : ∀ k T, (univ \ T).card = k → Good r (cd r s.2 T) →
      val P x r (succ P x r s T) = val P x r (succ P x r s univ) := by
    intro k
    induction k with
    | zero =>
      intro T hk _
      have : T = univ := by
        rw [card_eq_zero, sdiff_eq_empty_iff_subset] at hk
        exact eq_univ_of_forall fun v => hk (mem_univ v)
      rw [this]
    | succ k ih =>
      intro T hk hT
      obtain ⟨v, hv⟩ : (univ \ T).Nonempty := by rw [← card_pos]; omega
      have hvT : v ∉ T := (mem_sdiff.1 hv).2
      have hT' : Good r (cd r s.2 (insert v T)) :=
        hT.mono (cd_mono_set hs.1 (subset_insert v T)) (cd_le hs.1 _)
      have hk' : (univ \ insert v T).card = k := by
        have : univ \ insert v T = (univ \ T).erase v := by
          ext w; simp only [mem_sdiff, mem_univ, true_and, mem_insert, mem_erase]; tauto
        rw [this, card_erase_of_mem hv]; omega
      rw [← ih _ hk' hT']
      obtain ⟨m, hm1, hm2⟩ := common_val (P := P) (x := x) hloop hn hr hstab
        (ℓ := P.step x s.1 T) (ℓ' := P.step x s.1 (insert v T)) hT hT'
        (cd_mono_set hs.1 (subset_insert v T)) (j := v) (fun e he => by
          by_contra hev
          apply he
          by_cases heT : e.1.1 ∈ T
          · rw [Protocol.step_of_mem P x heT, Protocol.step_of_mem P x (mem_insert_of_mem heT)]
          · rw [Protocol.step_of_not_mem P x heT, Protocol.step_of_not_mem P x (by
              simp only [mem_insert, not_or]; exact ⟨hev, heT⟩)])
      exact (huni T hT).eq_of_mem (huni _ hT') hm1 hm2
  have hval : ∀ T, Good r (cd r s.2 T) →
      val P x r (succ P x r s T) = val P x r (succ P x r s univ) :=
    fun T hT => hall _ T rfl hT
  obtain ⟨T₁, hT₁, hm₁'⟩ := hsplit m₁ hm₁
  obtain ⟨T₂, hT₂, hm₂'⟩ := hsplit m₂ hm₂
  rw [hval T₁ hT₁] at hm₁'
  rw [hval T₂ hT₂] at hm₂'
  exact h12 (huni univ (good_cd_univ r _) hm₁' hm₂')

end Impossibility

open Impossibility

variable {V : Type*} [Fintype V] [DecidableEq V] {L X Y : Type*} {G : Digraph V}

/-- **Theorem 3.1** of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17]. On a digraph without
self-loops with `n` nodes, if a stateless protocol has two distinct stable labelings for some
input `x`, then there is an initial labeling and an `(n-1)`-fair schedule under which the
labeling sequence does not converge. -/
theorem exists_nonconvergent_run (hloop : ∀ v, ¬ G.Adj v v) (P : Protocol G L X Y) (x : V → X)
    {ℓ₁ ℓ₂ : Labeling G L} (h₁ : P.IsStable x ℓ₁) (h₂ : P.IsStable x ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    ∃ ℓ0 σ, IsRFair (Fintype.card V - 1) σ ∧ ¬ Converges (P.run x ℓ0 σ) := by
  -- two distinct labelings need an arc, hence two distinct nodes
  obtain ⟨e, he⟩ : ∃ e : Arc G, ℓ₁ e ≠ ℓ₂ e := by
    by_contra h; push Not at h; exact hne (funext h)
  have hn2 : 2 ≤ Fintype.card V := by
    have hne' : e.1.1 ≠ e.1.2 := fun h => hloop e.1.1 (h ▸ e.2)
    calc 2 = ({e.1.1, e.1.2} : Finset V).card := (Finset.card_pair hne').symm
      _ ≤ _ := Finset.card_le_univ _
  by_contra hcon
  push Not at hcon
  exact hne (stable_unique hloop (by omega) (by omega) hcon h₁ h₂)

/-- **Theorem 3.1**: no stateless protocol (on a digraph without self-loops) with two distinct
stable labelings is label `(n-1)`-stabilizing, nor label `r`-stabilizing for any `r ≥ n - 1`. -/
theorem not_labelStabilizing (hloop : ∀ v, ¬ G.Adj v v) (P : Protocol G L X Y) (x : V → X)
    {ℓ₁ ℓ₂ : Labeling G L} (h₁ : P.IsStable x ℓ₁) (h₂ : P.IsStable x ℓ₂) (hne : ℓ₁ ≠ ℓ₂)
    {r : ℕ} (hr : Fintype.card V - 1 ≤ r) : ¬ LabelStabilizing r P := by
  rintro ⟨-, hlab⟩
  obtain ⟨ℓ0, σ, hσ, hnc⟩ := exists_nonconvergent_run hloop P x h₁ h₂ hne
  exact hnc (hlab x ℓ0 σ (hσ.mono hr))

end StatelessComputation
