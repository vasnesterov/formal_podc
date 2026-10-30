import Papers.PODC2026.TreesNetworkSizeKnowledge.Padding
import Papers.PODC2026.TreesNetworkSizeKnowledge.Surgery

/-!
# Theorem 1: `k`-hierarchical 2½-colouring needs `Ω(n)` rounds without knowledge of `n`

Theorem 1 of *The Distributed Complexity Landscape on Trees Depends on the Knowledge About the
Network Size* (Balliu, Brandt, Kuhn, Olivetti, Picavet, Schmid; PODC 2026).

* `alternation`: on a path of same-level nodes whose lower-level neighbours all decline, a valid
  solution is either all `D` or a proper 2-colouring.
* `claim`: the induction of the proof: in every host, every node of an embedded level-`(j+1)`
  component outputs `D` (properties 3 and 4 of the paper), provided the algorithm is fast on trees
  of the sizes `N_j` chosen in the proof.
* `theorem1`: the theorem.
-/

namespace Podc.TreesNetworkSizeKnowledge

open SimpleGraph

/-- Swap the two colours. -/
def Label.swap : Label → Label
  | .B => .W
  | .W => .B
  | c => c

lemma Label.swap_iterate_mem {c : Label} (hc : c ≠ .D) (hc' : c ≠ .E) (n : ℕ) :
    Label.swap^[n] c ≠ .D ∧ Label.swap^[n] c ≠ .E := by
  induction n with
  | zero => exact ⟨hc, hc'⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    revert ih
    cases Label.swap^[n] c <;> simp [Label.swap]

lemma Label.swap_iterate_succ_ne {c : Label} (hc : c ≠ .D) (hc' : c ≠ .E) (n : ℕ) :
    Label.swap^[n + 1] c ≠ Label.swap^[n] c := by
  rw [Function.iterate_succ_apply']
  have := Label.swap_iterate_mem hc hc' n
  revert this
  cases Label.swap^[n] c <;> simp [Label.swap]

section Alternation

variable {k : ℕ} {I : Inst} {o : ℕ → Label} (hI : IsHierColoring k I o)

include hI

lemma ne_E_of_low {i x : ℕ} (hik : i ≤ k) (hx : InLevel I.G I.V i x)
    (hlow : ∀ u i', i' < i → InLevel I.G I.V i' u → I.G.Adj x u → o u = .D) : o x ≠ .E := by
  intro hE
  obtain ⟨u, i', hi', hu, hadj, hne⟩ := hI.exempt i hik x hx hE
  exact hne (hlow u i' hi' hu hadj)

/-- One step of the alternation along adjacent same-level nodes. -/
lemma alt_step {i x y : ℕ} (hik : i ≤ k) (hx : InLevel I.G I.V i x) (hy : InLevel I.G I.V i y)
    (hadj : I.G.Adj x y)
    (hlowx : ∀ u i', i' < i → InLevel I.G I.V i' u → I.G.Adj x u → o u = .D)
    (hlowy : ∀ u i', i' < i → InLevel I.G I.V i' u → I.G.Adj y u → o u = .D) :
    (o x = .D → o y = .D) ∧ (o x ≠ .D → o y = (o x).swap) := by
  have hxE := ne_E_of_low hI hik hx hlowx
  have hyE := ne_E_of_low hI hik hy hlowy
  constructor
  · intro hxD
    by_contra hyD
    have hcol : o y = .W ∨ o y = .B := by cases h : o y <;> simp_all
    exact (hI.color i hik y x hy hx hadj.symm hcol).2 hxD
  · intro hxD
    have hcol : o x = .W ∨ o x = .B := by cases h : o x <;> simp_all
    have h := hI.color i hik x y hx hy hadj hcol
    cases hox : o x <;> cases hoy : o y <;> simp_all [Label.swap]

/-- On a path of level-`i` nodes whose lower-level neighbours all output `D`, the outputs are
all `D` or alternate between `B` and `W`. -/
lemma alternation {i : ℕ} (hik : i ≤ k) (p : ℕ → ℕ) (hi : ℕ)
    (hlev : ∀ t ≤ hi, InLevel I.G I.V i (p t)) (hadj : ∀ t < hi, I.G.Adj (p t) (p (t + 1)))
    (hlow : ∀ t ≤ hi, ∀ u i', i' < i → InLevel I.G I.V i' u → I.G.Adj (p t) u → o u = .D) :
    (∀ a ≤ hi, o (p a) = .D → ∀ t ≤ hi, o (p t) = .D) ∧
    (∀ a ≤ hi, o (p a) ≠ .D → o (p a) ≠ .E ∧
      ∀ n, a + n ≤ hi → o (p (a + n)) = Label.swap^[n] (o (p a))) := by
  have step := fun t (ht : t < hi) => alt_step hI hik (hlev t ht.le) (hlev (t + 1) ht)
    (hadj t ht) (hlow t ht.le) (hlow (t + 1) ht)
  have stepb := fun t (ht : t < hi) => alt_step hI hik (hlev (t + 1) ht) (hlev t ht.le)
    (hadj t ht).symm (hlow (t + 1) ht) (hlow t ht.le)
  constructor
  · intro a ha hD t ht
    have up : ∀ n, a + n ≤ hi → o (p (a + n)) = .D := by
      intro n
      induction n with
      | zero => intro _; exact hD
      | succ n ih => intro h; exact (step (a + n) (by omega)).1 (ih (by omega))
    have down : ∀ n, n ≤ a → o (p (a - n)) = .D := by
      intro n
      induction n with
      | zero => intro _; simpa using hD
      | succ n ih =>
        intro h
        have := (stepb (a - (n + 1)) (by omega)).1
        rw [show a - (n + 1) + 1 = a - n by omega] at this
        exact this (ih (by omega))
    rcases le_total a t with h | h
    · have := up (t - a) (by omega); rwa [show a + (t - a) = t by omega] at this
    · have := down (a - t) (by omega); rwa [show a - (a - t) = t by omega] at this
  · intro a ha hD
    refine ⟨ne_E_of_low hI hik (hlev a ha) (hlow a ha), ?_⟩
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro h
      have hn := ih (by omega)
      have hne : o (p (a + n)) ≠ .D := by
        rw [hn]
        exact (Label.swap_iterate_mem hD (ne_E_of_low hI hik (hlev a ha) (hlow a ha)) n).1
      rw [Function.iterate_succ_apply', ← hn]
      exact (step (a + n) (by omega)).2 hne

end Alternation

/-! ### The induction -/

section Claim

variable {A : Alg Label} (hA : A.IsLocal) {k : ℕ} {ℓ : ℕ → ℕ} (hℓ : ∀ i, 100 ≤ ℓ i)
  {N : ℕ → ℕ} (hsize : ∀ j, j ≤ k → ∀ top, (comp ℓ j top).V.card ≤ N j)
  (hrun : ∀ j, 1 ≤ j → j ≤ k → ∀ I : Inst, I.MaxDegLE 3 → I.V.card = N j → ∀ v ∈ I.V,
    A.time I v ≤ ℓ j / 10)
  (hcorr : ∀ I : Inst, I.MaxDegLE 3 → IsHierColoring k I (A.out I))

include hA hℓ hsize hrun hcorr

/-- The inductive step: properties 3 and 4 for a level-`(j+1)` component, assuming the claim for
the attached level-`j` components in every host. -/
theorem claim_step (j : ℕ) (hj : j + 1 ≤ k)
    (hchild : ∀ {H : RTree} {hl : ℕ → ℕ} {ι : ℕ → ℕ}, HostOK H hl → Emb ℓ H hl j false ι →
      ∀ y ∈ (comp ℓ j false).V, A.out H.toInst (ι y) = .D)
    {top : Bool} {H : RTree} {hl : ℕ → ℕ} {ι : ℕ → ℕ} (hH : HostOK H hl)
    (hE : Emb ℓ H hl (j + 1) top ι) :
    ∀ x ∈ (comp ℓ (j + 1) top).V, A.out H.toInst (ι x) = .D := by
  have hℓ2 : ∀ i, 2 ≤ ℓ i := fun i => by have := hℓ i; omega
  set m := ℓ (j + 1) with hm_def
  have hm : 100 ≤ m := hℓ _
  set T := m / 10 with hT
  have hTm : 10 * T ≤ m := by omega
  have hTm' : m < 10 * T + 10 := by omega
  -- the path in `H`
  set p : ℕ → ℕ := fun t => ι (Nat.pair 0 t) with hp
  have hI := hcorr H.toInst hH.maxDeg
  have hlevH := hH.inLevel_iff
  -- Step A: the attached components decline
  have hchildD : ∀ {H' : RTree}, HostOK H' hl → ∀ {t b : ℕ}, t < m → b < 2 →
      HasBr m top t b → 0 ∈ (comp ℓ j false).V →
      Emb ℓ H' hl j false (ι ∘ Nat.pair (2 * t + b + 1)) →
      A.out H'.toInst (ι (Nat.pair (2 * t + b + 1) 0)) = .D :=
    fun hH' _ _ _ _ _ h0 hE' => hchild hH' hE' 0 h0
  -- levels of path nodes
  have hpathLev : ∀ t < m, InLevel H.graph H.V (j + 1) (p t) :=
    fun t ht => (hlevH _ _).2 ⟨hE.mem _ (path_mem ℓ j top ht), hE.lev_path' ht⟩
  -- lower-level neighbours of path nodes decline (in `H`)
  have hlow : ∀ t ≤ m - 1, ∀ u i', i' < j + 1 → InLevel H.graph H.V i' u →
      H.graph.Adj (p t) u → A.out H.toInst u = .D := by
    intro t ht u i' hi' hu hadj
    have hlu := ((hlevH _ _).1 hu).2
    rcases (hE.path_adj_iff (by omega) u).1 hadj with
      ⟨-, rfl⟩ | ⟨-, htop, rfl⟩ | ⟨h1, rfl⟩ | ⟨b, hb, hbr, h0, rfl⟩
    · rw [hE.lev_path' (by omega)] at hlu; omega
    · have := hE.lev_par_root htop; omega
    · rw [hE.lev_path' h1] at hlu; omega
    · exact hchildD hH (by omega) hb hbr h0 (hE.child (by omega) hb hbr h0)
  have halt := alternation hI (i := j + 1) hj p (m - 1) (fun t ht => hpathLev t (by omega))
    (fun t ht => (hE.path_adj_iff (by omega) _).2 (Or.inr (Or.inr (Or.inl ⟨by omega, rfl⟩))))
    hlow
  set a := T + 1
  by_cases hD : A.out H.toInst (p a) = .D
  · -- all path nodes decline, hence the whole component does
    have hall := halt.1 a (by omega) hD
    intro x hx
    rcases (mem_V ℓ j top).1 hx with ⟨t, ht, rfl⟩ | ⟨t, ht, b, hb, hbr, y, hy, rfl⟩
    · exact hall t (by omega)
    · exact hchild hH (hE.child ht hb hbr (zero_mem_of_mem hy)) y hy
  · -- the parity surgery gives a contradiction
    exfalso
    obtain ⟨hDE, halt2⟩ := halt.2 a (by omega) hD
    set s := 2 * T + 3
    set b := 3 * T + 5
    have hs1 : 1 ≤ s := by omega
    have hs2 : s + 1 < m := by omega
    have hbm : b < m := by omega
    have hpb : A.out H.toInst (p b) = Label.swap^[b - a] (A.out H.toInst (p a)) := by
      have := halt2 (b - a) (by omega); rwa [show a + (b - a) = b by omega] at this
    -- `u = p a` and `v = p b` terminate within `T` rounds (property 3)
    have htime : ∀ t, T + 1 ≤ t → t < m → A.time H.toInst (p t) ≤ T :=
      fun t h1 h2 => time_le_of_pad hA hℓ2 (hrun (j + 1) (by omega) hj) (hsize (j + 1) hj top)
        hH hE h1 h2
    set Ĥ := hatTree hE hs1 hs2
    have hĤ : HostOK Ĥ hl := hostOK_hat hH hE hs1 hs2
    have hÎ := hcorr Ĥ.toInst hĤ.maxDeg
    have hlevĤ := hĤ.inLevel_iff
    have hpĤ : ∀ t < m, t ≠ s → p t ∈ Ĥ.V := by
      intro t ht hts
      refine (hat_V hE hs1 hs2).2 ⟨hE.mem _ (path_mem ℓ j top ht), fun h => ?_⟩
      rcases (mem_remSet).1 h with h | ⟨y0, -, h⟩ <;> have := Nat.pair_eq_pair.1 (hE.inj h) <;>
        omega
    -- outputs of `u` and `v` are the same in `H` and `Ĝ`
    have hsame : ∀ t, T + 1 ≤ t → t < m → (t + T + 1 < s ∨ s + 1 + T < t) →
        A.out Ĥ.toInst (p t) = A.out H.toInst (p t) := by
      intro t h1 h2 h3
      have hloc := hA H.toInst Ĥ.toInst (p t) T (hE.mem _ (path_mem ℓ j top h2))
        (hpĤ t h2 (by omega)) (gAgree_hat hE hs1 hs2 h2 (by omega) h3)
      exact (hloc.2 (htime t h1 h2)).symm
    have hua := hsame a le_rfl (by omega) (Or.inl (by omega))
    have hvb := hsame b (by omega) hbm (Or.inr (by omega))
    -- the path of `Ĝ`
    set q : ℕ → ℕ := fun t => if t < s then p t else p (t + 1) with hq
    have hqidx : ∀ t, q t = p (if t < s then t else t + 1) := by
      intro t; simp only [hq]; split_ifs <;> rfl
    have hqLev : ∀ t ≤ m - 2, InLevel Ĥ.graph Ĥ.V (j + 1) (q t) := by
      intro t ht
      rw [hqidx]
      refine (hlevĤ _ _).2 ⟨hpĤ _ (by split_ifs <;> omega) (by split_ifs <;> omega),
        hE.lev_path' (by split_ifs <;> omega)⟩
    have hpadj : ∀ t, t + 1 < m → H.graph.Adj (p t) (p (t + 1)) :=
      fun t ht => (hE.path_adj_iff (by omega) _).2 (Or.inr (Or.inr (Or.inl ⟨ht, rfl⟩)))
    have hpR : ∀ t, t < m → t ≠ s → p t ∉ remSet ℓ j ι s :=
      fun t ht hts => ((hat_V hE hs1 hs2).1 (hpĤ t ht hts)).2
    have hqadj : ∀ t < m - 2, Ĥ.graph.Adj (q t) (q (t + 1)) := by
      intro t ht
      simp only [hq]
      by_cases h1 : t + 1 < s
      · rw [ite_eq_left (by omega), ite_eq_left h1]
        exact hat_adj_of_adj hE hs1 hs2 (hpadj t (by omega)) (hpR t (by omega) (by omega))
          (hpR _ (by omega) (by omega))
      · by_cases h2 : t + 1 = s
        · rw [ite_eq_left (by omega), ite_eq_right (by omega)]
          have e1 : t = s - 1 := by omega
          rw [e1, show s - 1 + 1 + 1 = s + 1 by omega]
          exact (hat_adj_z1 hE hs1 hs2 _).2 (Or.inr rfl)
        · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          exact hat_adj_of_adj hE hs1 hs2 (hpadj (t + 1) (by omega))
            (hpR _ (by omega) (by omega)) (hpR _ (by omega) (by omega))
    have hqlow : ∀ t ≤ m - 2, ∀ u i', i' < j + 1 → InLevel Ĥ.graph Ĥ.V i' u →
        Ĥ.graph.Adj (q t) u → A.out Ĥ.toInst u = .D := by
      intro t ht u i' hi' hu hadj
      have hlu := ((hlevĤ _ _).1 hu).2
      set t' := if t < s then t else t + 1 with ht'
      have ht'm : t' < m := by simp only [ht']; split_ifs <;> omega
      have ht's : t' ≠ s := by simp only [ht']; split_ifs <;> omega
      rw [hqidx] at hadj
      rcases hat_adj_cases hE hs1 hs2 hadj with hadj | ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rcases (hE.path_adj_iff ht'm u).1 hadj with
          ⟨-, rfl⟩ | ⟨-, htop, rfl⟩ | ⟨h1, rfl⟩ | ⟨b', hb, hbr, h0, rfl⟩
        · rw [hE.lev_path' (by omega)] at hlu; omega
        · have := hE.lev_par_root htop; omega
        · rw [hE.lev_path' h1] at hlu; omega
        · exact hchildD hĤ ht'm hb hbr h0 (emb_hat_child hE hs1 hs2 ht'm ht's hb hbr h0)
      · rw [hE.lev_path' hs2] at hlu; omega
      · rw [hE.lev_path' (by omega)] at hlu; omega
    have haltĤ := alternation hÎ (i := j + 1) hj q (m - 2) hqLev hqadj hqlow
    have hqa : q a = p a := by simp only [hq]; rw [ite_eq_left (by omega)]
    have hqb : q (b - 1) = p b := by
      simp only [hq]; rw [ite_eq_right (by omega), show b - 1 + 1 = b by omega]
    have hDĤ : A.out Ĥ.toInst (q a) ≠ .D := by rw [hqa, hua]; exact hD
    have hpb' := (haltĤ.2 a (by omega) hDĤ).2 (b - 1 - a) (by omega)
    rw [show a + (b - 1 - a) = b - 1 by omega, hqb, hqa, hua, hvb, hpb,
      show b - a = (b - 1 - a) + 1 by omega] at hpb'
    exact Label.swap_iterate_succ_ne hD hDE _ hpb'

/-- The claim of the proof of Theorem 1 (properties 3 and 4, for every level and every host). -/
theorem claim : ∀ j, j + 1 ≤ k → ∀ {top : Bool} {H : RTree} {hl : ℕ → ℕ} {ι : ℕ → ℕ},
    HostOK H hl → Emb ℓ H hl (j + 1) top ι →
    ∀ x ∈ (comp ℓ (j + 1) top).V, A.out H.toInst (ι x) = .D := by
  intro j
  induction j with
  | zero =>
    intro hj top H hl ι hH hE
    exact claim_step hA hℓ hsize hrun hcorr 0 hj (fun _ _ y hy => by simp at hy) hH hE
  | succ j ih =>
    intro hj top H hl ι hH hE
    exact claim_step hA hℓ hsize hrun hcorr (j + 1) hj
      (fun hH' hE' => ih (by omega) hH' hE') hH hE

end Claim

/-! ### Choice of the parameters and the theorem -/

section Params

variable (g : ℕ → ℕ → ℕ) (C : ℕ)

/-- `L_j = ℓ₁ ⋯ ℓ_j` for the path lengths chosen in the proof. -/
def Lseq : ℕ → ℕ
  | 0 => 1
  | j + 1 => Lseq j * (g (C * Lseq j - 1) (100 * C * Lseq j) / (C * Lseq j))

/-- The path lengths `ℓ_{j+1} = ⌊N_{j+1} / (c₂ L_j)⌋` (and `ℓ 0 = 100`, unused). -/
def ellOf : ℕ → ℕ
  | 0 => 100
  | j + 1 => g (C * Lseq g C j - 1) (100 * C * Lseq g C j) / (C * Lseq g C j)

/-- The sizes `N_{j+1} = f(1/(20 c₂ L_j), 100 c₂ L_j)` of the proof. -/
def NOf : ℕ → ℕ
  | 0 => 0
  | j + 1 => g (C * Lseq g C j - 1) (100 * C * Lseq g C j)

variable {g C} (hg : ∀ D n₀, n₀ < g D n₀) (hC : 1 ≤ C)
include hg hC

lemma Lseq_pos_ell : ∀ j, 1 ≤ Lseq g C j ∧ 100 ≤ ellOf g C (j + 1)
  | 0 => by
    refine ⟨le_rfl, ?_⟩
    simp only [ellOf, Lseq, mul_one]
    rw [Nat.le_div_iff_mul_le (by omega)]
    have := hg (C * 1 - 1) (100 * C * 1); simp only [mul_one] at this; omega
  | j + 1 => by
    obtain ⟨h1, h2⟩ := Lseq_pos_ell j
    have hL : 1 ≤ Lseq g C (j + 1) := by
      simp only [Lseq]
      have : ellOf g C (j + 1) = g (C * Lseq g C j - 1) (100 * C * Lseq g C j) / (C * Lseq g C j) :=
        rfl
      rw [← this]; nlinarith
    refine ⟨hL, ?_⟩
    simp only [ellOf]
    have hCL : 0 < C * Lseq g C (j + 1) := by positivity
    rw [Nat.le_div_iff_mul_le hCL]
    have := hg (C * Lseq g C (j + 1) - 1) (100 * C * Lseq g C (j + 1)); nlinarith

lemma ellOf_ge : ∀ i, 100 ≤ ellOf g C i
  | 0 => le_rfl
  | j + 1 => (Lseq_pos_ell hg hC j).2

omit hg hC in
lemma Lprod_ellOf : ∀ j, Lprod (ellOf g C) j = Lseq g C j
  | 0 => rfl
  | j + 1 => by rw [Lprod_succ, Lprod_ellOf j]; rfl

end Params

/-- **Theorem 1** of [Balliu, Brandt, Kuhn, Olivetti, Picavet, Schmid, PODC 2026]. In the
deterministic LOCAL model where nodes have unique identifiers that are arbitrary natural numbers and
know nothing about `n` (`Alg.IsLocal`), every algorithm solving `k`-hierarchical 2½-colouring
(`k > 0`) on all trees of maximum degree `Δ ≥ 3` needs `Ω(n)` rounds (Knuth's `Ω`): there are
`ε > 0` and `n₀` such that for every `n > n₀` some `n`-node tree of maximum degree `3` has a node
that runs for at least `εn` rounds. -/
theorem theorem1 (k : ℕ) (hk : 0 < k) (A : Alg Label) (hA : A.IsLocal) (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (hcorr : ∀ I : Inst, I.MaxDegLE Δ → IsHierColoring k I (A.out I)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ n > n₀, ∃ I : Inst, I.V.card = n ∧ I.MaxDegLE 3 ∧
      ∃ v ∈ I.V, ε * n ≤ A.time I v := by
  by_contra hcon
  -- the contradiction hypothesis: `A` is fast on infinitely many sizes, for every `ε`
  have hfast : ∀ D n₀ : ℕ, ∃ n > n₀, ∀ I : Inst, I.V.card = n → I.MaxDegLE 3 →
      ∀ v ∈ I.V, 20 * (D + 1) * A.time I v < n := by
    intro D n₀
    by_contra h
    push Not at h
    apply hcon
    refine ⟨1 / (20 * (D + 1)), by positivity, n₀, fun n hn => ?_⟩
    obtain ⟨I, h1, h2, v, hv, h3⟩ := h n hn
    refine ⟨I, h1, h2, v, hv, ?_⟩
    have h3' : (n : ℝ) ≤ 20 * (D + 1) * A.time I v := by exact_mod_cast h3
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    linarith
  choose g hg hgI using hfast
  have hcorr' : ∀ I : Inst, I.MaxDegLE 3 → IsHierColoring k I (A.out I) :=
    fun I h => hcorr I fun v => (h v).trans hΔ
  set C := 3 ^ k with hCdef
  have hC : 1 ≤ C := Nat.one_le_pow _ _ (by norm_num)
  set ℓ := ellOf g C
  set N := NOf g C
  have hℓ : ∀ i, 100 ≤ ℓ i := ellOf_ge hg hC
  have hℓ2 : ∀ i, 2 ≤ ℓ i := fun i => by have := hℓ i; omega
  have hL := Lseq_pos_ell hg hC
  have hsize : ∀ j, j ≤ k → ∀ top, (comp ℓ j top).V.card ≤ N j := by
    intro j hj top
    cases j with
    | zero => simp
    | succ j =>
      have h1 := card_comp_le ℓ (fun i => by have := hℓ i; omega) (j + 1) top
      rw [Lprod_ellOf, Lseq] at h1
      have h3 : 3 ^ (j + 1) ≤ C := Nat.pow_le_pow_right (by norm_num) hj
      have h4 := Nat.div_mul_le_self (g (C * Lseq g C j - 1) (100 * C * Lseq g C j))
        (C * Lseq g C j)
      calc (comp ℓ (j + 1) top).V.card
          ≤ 3 ^ (j + 1) * (Lseq g C j * (g (C * Lseq g C j - 1) (100 * C * Lseq g C j) /
              (C * Lseq g C j))) := h1
        _ ≤ C * (Lseq g C j * (g (C * Lseq g C j - 1) (100 * C * Lseq g C j) /
              (C * Lseq g C j))) := Nat.mul_le_mul_right _ h3
        _ = g (C * Lseq g C j - 1) (100 * C * Lseq g C j) / (C * Lseq g C j) *
              (C * Lseq g C j) := by ring
        _ ≤ N (j + 1) := h4
  have hrun : ∀ j, 1 ≤ j → j ≤ k → ∀ I : Inst, I.MaxDegLE 3 → I.V.card = N j → ∀ v ∈ I.V,
      A.time I v ≤ ℓ j / 10 := by
    intro j hj1 _ I hI hIN v hv
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hj1
    have hD : C * Lseq g C j - 1 + 1 = C * Lseq g C j := by
      have := (hL j).1; have : 1 ≤ C * Lseq g C j := by nlinarith
      omega
    have h1 := hgI (C * Lseq g C j - 1) (100 * C * Lseq g C j) I hIN hI v hv
    rw [hD] at h1
    set n := g (C * Lseq g C j - 1) (100 * C * Lseq g C j)
    set d := C * Lseq g C j
    have hdpos : 0 < d := by omega
    have h2 : n < d * (n / d + 1) := by
      have := Nat.lt_div_mul_add hdpos (a := n); nlinarith
    have h3 : 20 * A.time I v < n / d + 1 := by
      have : d * (20 * A.time I v) < d * (n / d + 1) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_left this
    show A.time I v ≤ (n / d) / 10
    omega
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le' hk
  have hG := hostOK_top hℓ2 k'
  have hEG := emb_top hℓ2 k'
  have hout := claim hA hℓ hsize hrun hcorr' k' le_rfl hG hEG 0 (zero_mem ℓ k' true
    (fun i => by have := hℓ i; omega))
  have hI := hcorr' _ hG.maxDeg
  refine hI.top_ne_D 0 ?_ hout
  exact (hG.inLevel_iff _ _).2 ⟨zero_mem ℓ k' true (fun i => by have := hℓ i; omega),
    lev_zero ℓ k' true⟩

end Podc.TreesNetworkSizeKnowledge
