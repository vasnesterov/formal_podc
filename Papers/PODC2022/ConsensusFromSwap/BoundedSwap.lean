import Papers.PODC2022.ConsensusFromSwap.BinarySwap
import Podc.Foundations.Data.Finset.SumUpdate

/-!
# Readable swap objects with domain size `b`: `(n − 2)/(3b + 1)` objects are necessary
(Section 5.2)

Lemma 20 and Theorem 22 of Ovens (PODC 2022): every obstruction-free binary consensus algorithm
for `n` processes from readable swap objects with values in a set `D` of size `b` uses at least
`(n − 2)/(3b + 1)` objects (`theorem22`: `n − 2 ≤ (3b + 1) · #objects`).

`Inv20` is the statement of Lemma 20 for a configuration `C`, the forbidden-value functions
`f`, `g` and the list `cs` of pairs (covering process, covered object) (the paper's `S_i`).
-/

namespace ConsensusFromSwap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] [Fintype ι] {D : Type} [DecidableEq D] [Fintype D] {d₀ : D}
  {P : Type} [DecidableEq P] {A : Alg (fun _ : ι => rswapObj D d₀) P Bool}

/-- The potential `∑_B (2·|f(B)| + |g(B)|)` of Lemma 20 (d). -/
def wt (f g : ι → Finset D) : ℕ := ∑ x, (2 * (f x).card + (g x).card)

lemma wt_insert_f {f g : ι → Finset D} {B : ι} {v : D} (hv : v ∉ f B) :
    wt (fun x => if x = B then insert v (f x) else f x) g = wt f g + 2 := by
  have := Fintype.sum_add_eq_sum_add_of_eq_off (f := fun x => 2 * (f x).card + (g x).card)
    (g := fun x => 2 * ((if x = B then insert v (f x) else f x)).card + (g x).card) B
    (fun x hx => by simp [hx])
  simp only [ite_true, Finset.card_insert_of_notMem hv] at this
  simp only [wt]
  omega

lemma wt_insert_g {f g : ι → Finset D} (B : ι) (v : D) :
    wt f g + (if v ∈ g B then 0 else 1) =
      wt f (fun x => if x = B then insert v (g x) else g x) := by
  have := Fintype.sum_add_eq_sum_add_of_eq_off (f := fun x => 2 * (f x).card + (g x).card)
    (g := fun x => 2 * (f x).card + ((if x = B then insert v (g x) else g x)).card) B
    (fun x hx => by simp [hx])
  simp only [ite_true] at this
  simp only [wt]
  by_cases hv : v ∈ g B
  · rw [Finset.insert_eq_of_mem hv] at this; simp only [hv, ite_true]; omega
  · rw [Finset.card_insert_of_notMem hv] at this; simp only [hv, ite_false]; omega

lemma wt_le (f g : ι → Finset D) : wt f g ≤ 3 * Fintype.card D * Fintype.card ι := by
  unfold wt
  calc ∑ x, (2 * (f x).card + (g x).card) ≤ ∑ _x : ι, 3 * Fintype.card D :=
        Finset.sum_le_sum (fun x _ => by
          have := (f x).card_le_univ; have := (g x).card_le_univ; omega)
    _ = 3 * Fintype.card D * Fintype.card ι := by simp [mul_comm]

/-- The properties (a)–(f) of Lemma 20 at stage `i`. -/
structure Inv20 (C₀ : Cfg A) (q₀ q₁ : P) (ps : List P) (i : ℕ) (C : Cfg A) (f g : ι → Finset D)
    (cs : List (P × ι)) : Prop where
  reach : Reach C₀ C
  /-- (a) `Q` is bivalent. -/
  biv : Biv {q₀, q₁} C
  /-- (b) `S_i` covers `|S_i|` objects. -/
  cov : Covering C cs
  objs_nd : (cs.map Prod.snd).Nodup
  procs : ∀ c ∈ cs, c.1 ∈ ps.take i
  /-- (c) the covering processes swap non-forbidden values. -/
  swp : ∀ c ∈ cs, ∃ w k, A.act (C.loc c.1) = .access c.2 (RSOp.swap w) k ∧ w ∉ f c.2 ∧
    w ∉ g c.2
  /-- (d) the potential. -/
  wt_ge : i ≤ wt f g + cs.length
  /-- (e) an object taking a value of `f` makes `Q` univalent. -/
  fe : ∀ lam : List P, (∀ r ∈ lam, r ∈ RS q₀ q₁ ps i) → ∀ x,
    (∃ l₁ l₂, lam = l₁ ++ l₂ ∧ (run C l₁).mem x ∈ f x) → ¬ Biv {q₀, q₁} (run C lam)
  /-- (f) a process of `P_i` poised to swap a value of `g` makes `Q` univalent. -/
  gf : ∀ lam : List P, (∀ r ∈ lam, r ∈ RS q₀ q₁ ps i) → ∀ r ∈ ps.drop i, ∀ x w k,
    A.act ((run C lam).loc r) = .access x (RSOp.swap w) k → w ∈ g x →
    ¬ Biv {q₀, q₁} (run C lam)

section Lemma20

variable {C₀ : Cfg A} (hS : Setting C₀) {q₀ q₁ : P} (hq : q₀ ≠ q₁) {ps : List P}
  (hnd : (q₀ :: q₁ :: ps).Nodup)
include hS hq hnd

lemma lemma20_zero (hb : Biv {q₀, q₁} C₀) : Inv20 C₀ q₀ q₁ ps 0 C₀ (fun _ => ∅) (fun _ => ∅) []
    where
  reach := Reach.refl C₀
  biv := hb
  cov := ⟨by simp, by simp⟩
  objs_nd := by simp
  procs := by simp
  swp := by simp
  wt_ge := by simp
  fe := by simp
  gf := by simp

set_option maxHeartbeats 1000000 in
/-- The induction step of **Lemma 20** of [Ovens 2022]. -/
theorem lemma20_step {i : ℕ} (hi : i < ps.length) {C : Cfg A} {f g : ι → Finset D}
    {cs : List (P × ι)} (I : Inv20 C₀ q₀ q₁ ps i C f g cs) :
    ∃ C' f' g' cs', Inv20 C₀ q₀ q₁ ps (i + 1) C' f' g' cs' := by
  classical
  set Q : Set P := {q₀, q₁} with hQdef
  set p := ps[i] with hpdef
  set R := RS q₀ q₁ ps (i + 1) with hRdef
  set RI := RS q₀ q₁ ps i with hRIdef
  have hRi : RI = insert p R := RS_succ hi
  have hpR : p ∉ R := not_mem_RS_succ hnd hi
  have hQR : Q ⊆ R := Q_sub_RS _
  have hRsub : R ⊆ RI := RS_mono (Nat.le_succ i)
  have hcsR : ∀ c ∈ cs, c.1 ∉ RI := fun c hc => not_mem_RS_of_take hnd (I.procs c hc)
  have hbR : ∀ r ∈ RI, r ∉ block cs := by
    intro r hr hrb
    obtain ⟨x, hx⟩ := mem_block.1 hrb
    exact hcsR _ hx hr
  have hQb : ∀ q ∈ Q, q ∉ block cs := fun q hq => hbR q (Q_sub_RS i hq)
  have hpRi : p ∈ RI := by rw [hRi]; exact Set.mem_insert _ _
  have hpb : p ∉ block cs := hbR p hpRi
  have hpQ : p ∉ Q := fun h => hpR (hQR h)
  have hpq : p ≠ q₀ ∧ p ≠ q₁ := ⟨fun h => hpQ (by simp [Q, h]), fun h => hpQ (by simp [Q, h])⟩
  have hRiR : ∀ l : List P, (∀ r ∈ l, r ∈ R) → ∀ r ∈ l, r ∈ RI :=
    fun l hl r hr => hRsub (hl r hr)
  have hQRi : ∀ l : List P, (∀ r ∈ l, r ∈ Q) → ∀ r ∈ l, r ∈ RI :=
    fun l hl r hr => Q_sub_RS i (hl r hr)
  have happ : ∀ l₁ l₂ : List P, (∀ r ∈ l₁, r ∈ RI) → (∀ r ∈ l₂, r ∈ RI) →
      ∀ r ∈ l₁ ++ l₂, r ∈ RI := by
    intro l₁ l₂ h1 h2 r hr
    rcases List.mem_append.1 hr with hr | hr
    exacts [h1 r hr, h2 r hr]
  have hpRi' : ∀ r ∈ [p], r ∈ RI := by simp [hpRi]
  have hlocRI : ∀ (E : Cfg A) (l : List P), (∀ r ∈ l, r ∈ RI) → ∀ c ∈ cs,
      (run E l).loc c.1 = E.loc c.1 := fun E l hl c hc =>
    run_loc_other _ _ (by rintro r hr rfl; exact hcsR c hc (hl _ hr))
  have hplocQ : ∀ (E : Cfg A) (l : List P), (∀ r ∈ l, r ∈ Q) → (run E l).loc p = E.loc p :=
    fun E l hl => run_loc_other _ _ (by rintro r hr rfl; exact hpQ (hl _ hr))
  have hpdrop : p ∈ ps.drop i := by
    rw [List.drop_eq_getElem_cons hi]; exact List.mem_cons_self
  have hpcs : p ∉ cs.map Prod.fst := hpb
  -- `C' = C_i β_i` and Lemma 14
  set C' := run C (block cs) with hC'def
  have hC' : Reach C₀ C' := I.reach.run _
  have hlp : C.loc p = C'.loc p := (run_block_loc_other C cs hpb).symm
  obtain ⟨j, ha, B, o, k, hpa, hbc⟩ := lemma14 hS hQR hpR I.reach hC' I.biv hlp
  set F := run C' (solo p j) with hFdef
  set v := F.mem B with hvdef
  obtain ⟨αj, hαj, hbj, hindj⟩ := ha j le_rfl
  have hαjR : ∀ r ∈ αj, r ∈ RI := by rw [hRi]; exact hαj
  set C₁ := run C αj with hC₁def
  have hpC₁ : A.act (C₁.loc p) = .access B o k := by rw [hindj.2]; exact hpa
  have hC₁ : Reach C₀ C₁ := I.reach.run αj
  have hlocC₁ : ∀ c ∈ cs, C₁.loc c.1 = C.loc c.1 := hlocRI C αj hαjR
  -- the covered objects have non-forbidden values in `C'`
  have hC'cov : ∀ c ∈ cs, C'.mem c.2 ∉ f c.2 ∧ C'.mem c.2 ∉ g c.2 := by
    intro c hc
    obtain ⟨w, k', hw, hwf, hwg⟩ := I.swp c hc
    rw [hC'def, block_mem_swap I.cov I.objs_nd hc hw]
    exact ⟨hwf, hwg⟩
  -- Claim 21
  have claim21 : ∀ t ≤ j, ∀ x w k', A.act ((run C' (solo p t)).loc p) =
      .access x (RSOp.swap w) k' → w ∉ f x ∧ w ∉ g x := by
    intro t ht x w k' hk'
    obtain ⟨αt, hαt, hbt, hindt⟩ := ha t ht
    have hαtR : ∀ r ∈ αt, r ∈ RI := by rw [hRi]; exact hαt
    have hpt : A.act ((run C αt).loc p) = .access x (RSOp.swap w) k' := by
      rw [hindt.2]; exact hk'
    refine ⟨fun hwf => ?_, fun hwg => I.gf αt hαtR p hpdrop x w k' hpt hwg hbt⟩
    obtain ⟨γ, hγ, hbγ⟩ := lemma13 hS hq (I.reach.run αt) hbt (cs := [(p, x)])
      ⟨by simp, by simpa using covers_of_swap hpt⟩ (by simpa using hpq)
    have hpγ : A.act ((run (run C αt) γ).loc p) = .access x (RSOp.swap w) k' := by
      rw [hplocQ _ _ hγ]; exact hpt
    refine I.fe (αt ++ γ ++ [p]) (happ _ _ (happ _ _ hαtR (hQRi γ hγ)) hpRi') x
      ⟨αt ++ γ ++ [p], [], by simp, ?_⟩ ?_
    · rw [run_concat, run_append, step_swap_mem_self hpγ]; exact hwf
    · simpa [run_append, block] using hbγ
  -- values of objects after `δ_j` that are forbidden were already there in `C'`
  have hforb : ∀ x, F.mem x ∈ f x ∨ F.mem x ∈ g x → F.mem x = C'.mem x := by
    intro x hx
    by_contra hne
    obtain ⟨t, ht, k', hk'⟩ := exists_swap_solo C' p x j hne
    have := claim21 t (by omega) x _ k' hk'
    rcases hx with hx | hx
    · exact this.1 hx
    · exact this.2 hx
  have hXf : ∀ lam : List P, (∀ r ∈ lam, r ∈ R) → ∀ x,
      (∃ l₁ l₂, lam = l₁ ++ l₂ ∧ (run C₁ l₁).mem x ∈ f x) → ¬ Biv Q (run C₁ lam) := by
    intro lam hlam x ⟨l₁, l₂, hl, hx⟩
    have := I.fe (αj ++ lam) (happ _ _ hαjR (hRiR lam hlam)) x
      ⟨αj ++ l₁, l₂, by rw [hl]; simp, by rw [run_append]; exact hx⟩
    rwa [run_append] at this
  have hXg : ∀ lam : List P, (∀ r ∈ lam, r ∈ R) → ∀ r ∈ ps.drop (i + 1), ∀ x w k',
      A.act ((run C₁ lam).loc r) = .access x (RSOp.swap w) k' → w ∈ g x →
      ¬ Biv Q (run C₁ lam) := by
    intro lam hlam r hr x w k' hk' hw
    have := I.gf (αj ++ lam) (happ _ _ hαjR (hRiR lam hlam)) r
      (by rw [← List.drop_drop] at hr; exact List.mem_of_mem_drop hr) x w k'
      (by rw [run_append]; exact hk') hw
    rwa [run_append] at this
  set cs₀ := cs.filter (fun c => c.2 ≠ B) with hcs₀
  have hcs₀sub : ∀ c ∈ cs₀, c ∈ cs ∧ c.2 ≠ B := by
    intro c hc
    simpa [hcs₀] using hc
  have hcs₀len : cs.length ≤ cs₀.length + 1 := length_filter_ne I.objs_nd B
  have hcs₀nd : (cs₀.map Prod.snd).Nodup :=
    I.objs_nd.sublist (List.Sublist.map _ List.filter_sublist)
  have hcs₀fst : (cs₀.map Prod.fst).Nodup :=
    I.cov.1.sublist (List.Sublist.map _ List.filter_sublist)
  have hcovC₁ : ∀ c ∈ cs₀, C₁.Covers c.1 c.2 := fun c hc =>
    (I.cov.2 c (hcs₀sub c hc).1).of_loc (hlocC₁ c (hcs₀sub c hc).1)
  have hprocs₀ : ∀ c ∈ cs₀, c.1 ∈ ps.take (i + 1) :=
    fun c hc => take_sub_take_succ (I.procs c (hcs₀sub c hc).1)
  by_cases hd : ((rswapObj D d₀).δ v o).1 = v
  · -- Case 1: `d` does not change `B`: add `v` to `f(B)`
    have hvf : v ∉ f B := by
      intro hvf
      have hFC : F.mem B = C'.mem B := hforb B (Or.inl hvf)
      by_cases hcov : ∃ c ∈ cs, c.2 = B
      · obtain ⟨c, hc, rfl⟩ := hcov
        exact (hC'cov c hc).1 (by rw [← hFC]; exact hvf)
      · push Not at hcov
        have hCB : C.mem B = v := by
          rw [← run_block_mem_other I.cov hcov, ← hC'def, ← hFC]
        exact I.fe [] (by simp) B ⟨[], [], rfl, by simpa [hCB] using hvf⟩ (by simpa using I.biv)
    refine ⟨C₁, fun x => if x = B then insert v (f x) else f x, g, cs₀, ⟨hC₁, hbj,
      ⟨hcs₀fst, hcovC₁⟩, hcs₀nd, hprocs₀, ?_, ?_, ?_, ?_⟩⟩
    · intro c hc
      obtain ⟨hc', hcB⟩ := hcs₀sub c hc
      obtain ⟨w, k', hw, hwf, hwg⟩ := I.swp c hc'
      exact ⟨w, k', by rw [hlocC₁ c hc']; exact hw, by simpa [hcB] using hwf, hwg⟩
    · rw [wt_insert_f hvf]
      have := I.wt_ge
      omega
    · intro lam hlam x ⟨l₁, l₂, hl, hx⟩
      by_cases hxB : x = B
      · subst hxB
        simp only [ite_true, Finset.mem_insert] at hx
        rcases hx with hx | hx
        · exact (hbc αj hαj hbj hindj lam hlam).2 hd ⟨l₁, l₂, hl, hx⟩
        · exact hXf lam hlam x ⟨l₁, l₂, hl, hx⟩
      · simp only [hxB, ite_false] at hx
        exact hXf lam hlam x ⟨l₁, l₂, hl, hx⟩
    · exact hXg
  · -- Case 2: `d = Swap(B, v')` with `v' ≠ v`: add `v` to `g(B)`, `p` replaces/joins `S_i`
    obtain ⟨v', k₂, hpa2, hv'⟩ : ∃ v' k₂, A.act (C₁.loc p) = .access B (RSOp.swap v') k₂ ∧
        v' ≠ v := by
      cases o with
      | read => exact absurd rfl hd
      | swap w => exact ⟨w, k, hpC₁, hd⟩
    have hpaF : A.act (F.loc p) = .access B (RSOp.swap v') k₂ := by
      rw [← hindj.2]; exact hpa2
    have hv'fg := claim21 j le_rfl B v' k₂ hpaF
    refine ⟨C₁, f, fun x => if x = B then insert v (g x) else g x, (p, B) :: cs₀,
      ⟨hC₁, hbj, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, hXf, ?_⟩⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun h => hpcs (List.Sublist.subset (List.Sublist.map _ List.filter_sublist) h),
        hcs₀fst⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact covers_of_swap hpa2
      · exact hcovC₁ c hc
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun h => ?_, hcs₀nd⟩
      obtain ⟨c, hc, hcB⟩ := List.mem_map.1 h
      exact (hcs₀sub c hc).2 hcB
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact getElem_mem_take_succ hi
      · exact hprocs₀ c hc
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · refine ⟨v', k₂, hpa2, hv'fg.1, ?_⟩
        simp only [ite_true, Finset.mem_insert, not_or]
        exact ⟨hv', hv'fg.2⟩
      · obtain ⟨hc', hcB⟩ := hcs₀sub c hc
        obtain ⟨w, k', hw, hwf, hwg⟩ := I.swp c hc'
        exact ⟨w, k', by rw [hlocC₁ c hc']; exact hw, hwf, by simpa [hcB] using hwg⟩
    · -- the potential
      have hw := wt_insert_g (f := f) (g := g) B v
      have hI := I.wt_ge
      simp only [List.length_cons]
      by_cases hcov : ∃ c ∈ cs, c.2 = B
      · obtain ⟨c, hc, hcB⟩ := hcov
        have hvg : v ∉ g B := by
          intro hvg
          have hFC : F.mem B = C'.mem B := hforb B (Or.inr hvg)
          have h2 := (hC'cov c hc).2
          rw [hcB] at h2
          exact h2 (by rw [← hFC]; exact hvg)
        simp only [hvg, ite_false] at hw
        omega
      · push Not at hcov
        have : cs₀ = cs := List.filter_eq_self.2 (fun c hc => by simpa using hcov c hc)
        rw [this]
        omega
    · intro lam hlam r hr x w k' hk' hw
      by_cases hwg : w ∈ g x
      · exact hXg lam hlam r hr x w k' hk' hwg
      · have hxB : x = B := by by_contra h; simp [h, hwg] at hw
        subst hxB
        have hwv : w = v := by
          simp only [ite_true, Finset.mem_insert] at hw
          tauto
        subst hwv
        intro hbH
        have hrR : r ∈ R := Or.inr (Or.inr hr)
        have hrQ : r ∉ Q := by
          intro h
          simp only [List.nodup_cons, List.mem_cons] at hnd
          have hrps : r ∈ ps := List.mem_of_mem_drop hr
          rcases h with rfl | rfl
          · exact hnd.1 (Or.inr hrps)
          · exact hnd.2.1 hrps
        have hrp : r ≠ p := fun h => hpR (h ▸ hrR)
        set H := run C₁ lam with hHdef
        have hpH : A.act (H.loc p) = .access x (RSOp.swap v') k₂ := by
          rw [hHdef, run_loc_other _ _ (by rintro r' hr' rfl; exact hpR (hlam _ hr'))]
          exact hpa2
        obtain ⟨γ, hγ, hbγ⟩ := lemma13 hS hq (hC₁.run lam) hbH (cs := [(p, x)])
          ⟨by simp, by simpa using covers_of_swap hpH⟩ (by simpa using hpq)
        set H' := run H γ with hH'def
        have hpH' : A.act (H'.loc p) = .access x (RSOp.swap v') k₂ := by
          rw [hH'def, hplocQ _ _ hγ]; exact hpH
        have hrH' : A.act (H'.loc r) = .access x (RSOp.swap (F.mem x)) k' := by
          rw [hH'def, run_loc_other _ _ (by rintro r' hr' rfl; exact hrQ (hγ _ hr'))]
          exact hk'
        -- `r`'s swap is overwritten by `p`'s swap
        have hag : AgreeOn Q (H'.step p) ((H'.step r).step p) := by
          have hpH'r : A.act ((H'.step r).loc p) = .access x (RSOp.swap v') k₂ := by
            rw [H'.step_loc_other (Ne.symm hrp)]; exact hpH'
          refine ⟨?_, fun q hq' => ?_⟩
          · funext y
            rw [step_swap_mem hpH', step_swap_mem hpH'r, step_swap_mem hrH']
            split_ifs <;> rfl
          · have hqp : q ≠ p := fun h => hpQ (h ▸ hq')
            have hqr : q ≠ r := fun h => hrQ (h ▸ hq')
            rw [H'.step_loc_other hqp, (H'.step r).step_loc_other hqp, H'.step_loc_other hqr]
        have hb1 : Biv Q ((H'.step r).step p) := by
          rw [← hag.biv_iff le_rfl]
          simpa [hH'def, run_append, block] using hbγ
        have hlam' : ∀ r' ∈ lam ++ γ ++ [r], r' ∈ R := by
          intro r' hr'
          simp only [List.mem_append, List.mem_singleton] at hr'
          rcases hr' with (h | h) | rfl
          · exact hlam r' h
          · exact hQR (hγ r' h)
          · exact hrR
        have hmem : (run C₁ (lam ++ γ ++ [r])).mem x = F.mem x := by
          rw [run_concat, run_append, ← hHdef, ← hH'def, step_swap_mem_self hrH']
        have := (hbc αj hαj hbj hindj (lam ++ γ ++ [r]) hlam').1 hmem
        apply this
        rw [← hC₁def, run_concat, run_concat, run_append, ← hHdef, ← hH'def]
        exact hb1

/-- **Lemma 20** of [Ovens 2022]. -/
theorem lemma20 (hb : Biv {q₀, q₁} C₀) :
    ∀ i ≤ ps.length, ∃ C f g cs, Inv20 C₀ q₀ q₁ ps i C f g cs := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨C₀, _, _, [], lemma20_zero hS hq hnd hb⟩
  | succ i ih =>
    intro hi
    obtain ⟨C, f, g, cs, I⟩ := ih (by omega)
    exact lemma20_step hS hq hnd (by omega) I

end Lemma20

lemma Inv20.le {C₀ : Cfg A} {q₀ q₁ : P} {ps : List P} {i : ℕ} {C : Cfg A}
    {f g : ι → Finset D} {cs : List (P × ι)} (I : Inv20 C₀ q₀ q₁ ps i C f g cs) :
    i ≤ (3 * Fintype.card D + 1) * Fintype.card ι := by
  have h1 := wt_le f g
  have h2 : cs.length ≤ Fintype.card ι := by
    have := I.objs_nd.length_le_card
    simpa using this
  have := I.wt_ge
  nlinarith

/-- **Theorem 22** of [Ovens 2022]: every obstruction-free binary consensus algorithm for `n`
processes from readable swap objects with domain `D` of size `b` uses at least
`(n − 2)/(3b + 1)` objects: `n − 2 ≤ (3b + 1) · #objects`. -/
theorem theorem22 [Fintype P] (hA : SolvesSetAgreement A 1 Set.univ)
    (hof : ObstructionFree A Set.univ) :
    Fintype.card P - 2 ≤ (3 * Fintype.card D + 1) * Fintype.card ι := by
  classical
  by_cases hn : Fintype.card P < 2
  · omega
  push Not at hn
  obtain ⟨q₀, q₁, hq⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card P)
  set ps := ((Finset.univ.erase q₀).erase q₁).toList
  have hlen : ps.length = Fintype.card P - 2 := by
    simp only [ps, Finset.length_toList]
    rw [Finset.card_erase_of_mem (by simp [Ne.symm hq]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ]
    omega
  have hnd : (q₀ :: q₁ :: ps).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, ps, Finset.mem_toList, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.nodup_toList _⟩
    · rintro (h | ⟨-, h, -⟩)
      · exact hq h
      · exact h rfl
    · rintro ⟨h, -⟩; exact h rfl
  let x : P → Bool := fun p => decide (p = q₁)
  have hx0 : x q₀ = false := by simp [x, hq]
  have hx1 : x q₁ = true := by simp [x]
  have hS := setting_of hA hof (x := x) (fun _ => trivial)
  have hb := obs12 hA.validity_univ hof hx0 hx1
  obtain ⟨C, f, g, cs, I⟩ := lemma20 hS hq hnd hb ps.length le_rfl
  have h2 := I.le
  omega

end ConsensusFromSwap
