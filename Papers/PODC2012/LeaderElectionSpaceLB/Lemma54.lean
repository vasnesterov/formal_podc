import Papers.PODC2012.LeaderElectionSpaceLB.Claim53
import Papers.PODC2012.LeaderElectionSpaceLB.Arith

/-!
# Lemma 5.4: the round-based covering construction

We run the construction on a set `Act` of `N` *active* processes (the paper: all `n` processes;
restricting to a subset lets us handle `n` that are not powers of two). The partition
`(Q₁, …, Q_m)` of `Act` with representatives `q_j ∈ Q_j` is encoded by a map `g` sending every
active process to the representative of its group; `reps` is the set of representatives.
-/

namespace Podc.LeaderElectionSpaceLB

set_option linter.unusedSectionVars false

open Classical

variable {P Reg V L : Type*} [DecidableEq P] [DecidableEq Reg]

namespace Alg

variable (A : Alg P Reg V L)

/-- The number of processes of `S` that cover `r` in `C`. -/
noncomputable def cnt (C : Config P Reg V L) (S : Finset P) (r : Reg) : ℕ :=
  (S.filter (fun q => A.Covers C q r)).card

/-- The data of Lemma 5.4 after round `k` (for `N` active processes `Act`): an execution `E_k`
from an initial configuration, in which only active processes take steps, and a partition of
`Act` into groups (`g p` = representative of the group of `p`, `reps` = the representatives),
such that in the final configuration `C_k`:
(a) every representative covers some register;
(b) no register is covered by more than `N - k` representatives;
(c) a register on which some process is visible is covered by exactly `N - k` representatives;
(d) every group is closed w.r.t. `≡_{E_k}` (if `p` sees `q` then they are in the same group);
(e) there are at least `f N k` groups. -/
structure Stage (Act : Finset P) (N k : ℕ) where
  /-- The initial configuration. -/
  C₀ : Config P Reg V L
  /-- The execution `E_k`. -/
  es : List (P × L)
  init : A.IsInit C₀
  valid : A.Valid C₀ es
  onlyAct : ∀ e ∈ es, e.1 ∈ Act
  /-- Representative of the group of each active process. -/
  g : P → P
  /-- The representatives `q_1, …, q_m`. -/
  reps : Finset P
  reps_sub : reps ⊆ Act
  g_mem : ∀ p ∈ Act, g p ∈ reps
  g_rep : ∀ q ∈ reps, g q = q
  cover : ∀ q ∈ reps, ∃ r, A.Covers (A.run C₀ es) q r
  cnt_le : ∀ r, A.cnt (A.run C₀ es) reps r ≤ N - k
  cnt_vis : ∀ r, (A.run C₀ es).wr r ≠ none → A.cnt (A.run C₀ es) reps r = N - k
  closed : ∀ p q, A.SeesIn C₀ es p q → g p = g q
  card : f N k ≤ reps.card

/-! ### Counting -/

lemma cnt_le_card (C : Config P Reg V L) (S : Finset P) (r : Reg) : A.cnt C S r ≤ S.card :=
  Finset.card_filter_le _ _

/-- If every process of `S` covers a register of `T` and every register is covered by at most
`c` processes of `S`, then `|S| ≤ c |T|`. -/
lemma card_le_mul (C : Config P Reg V L) (S : Finset P) (T : Finset Reg) (c : ℕ)
    (hcov : ∀ q ∈ S, ∃ r ∈ T, A.Covers C q r) (hc : ∀ r, A.cnt C S r ≤ c) :
    S.card ≤ c * T.card := by
  have hsub : S ⊆ T.biUnion (fun r => S.filter (fun q => A.Covers C q r)) := by
    intro q hq
    obtain ⟨r, hr, hc⟩ := hcov q hq
    exact Finset.mem_biUnion.2 ⟨r, hr, Finset.mem_filter.2 ⟨hq, hc⟩⟩
  calc S.card ≤ (T.biUnion (fun r => S.filter (fun q => A.Covers C q r))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ r ∈ T, (S.filter (fun q => A.Covers C q r)).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ T, c := Finset.sum_le_sum (fun r _ => hc r)
    _ = c * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- If every register of `T` is covered by at least `c` processes of `S`, then `c |T| ≤ |S|`. -/
lemma mul_le_card (C : Config P Reg V L) (S : Finset P) (T : Finset Reg) (c : ℕ)
    (hc : ∀ r ∈ T, c ≤ A.cnt C S r) : c * T.card ≤ S.card := by
  have hdisj : (T : Set Reg).PairwiseDisjoint (fun r => S.filter (fun q => A.Covers C q r)) := by
    intro r _ r' _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq hq'
    exact hne (A.covers_unique (Finset.mem_filter.1 hq).2 (Finset.mem_filter.1 hq').2)
  calc c * T.card = ∑ _r ∈ T, c := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ r ∈ T, (S.filter (fun q => A.Covers C q r)).card := Finset.sum_le_sum hc
    _ = (T.biUnion (fun r => S.filter (fun q => A.Covers C q r))).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := Finset.card_le_card (Finset.biUnion_subset.2 (fun r _ => Finset.filter_subset _ _))

/-! ### Base case -/

lemma wr_none_of_no_writes {C : Config P Reg V L} (h : ∀ r, C.wr r = none) {es : List (P × L)}
    (hw : ¬ A.WritesIn C es Set.univ) (r : Reg) : (A.run C es).wr r = none := by
  rw [(A.run_mem_of_not_writesIn C es r (fun h' => hw (A.writesIn_mono (by simp) h'))).2, h r]

lemma no_sees_of_no_writes {C : Config P Reg V L} (h : ∀ r, C.wr r = none) {es : List (P × L)}
    (hw : ¬ A.WritesIn C es Set.univ) (p q : P) : ¬ A.SeesIn C es p q := by
  induction es generalizing C with
  | nil => exact id
  | cons e es ih =>
    rw [writesIn_cons, not_or] at hw
    rintro (⟨-, r, -, hr⟩ | hs)
    · rw [h r] at hr; cases hr
    · refine ih (fun r => ?_) hw.2 hs
      have : ∀ v, A.act (C.loc e.1) ≠ .write r v := fun v hv => hw.1 ⟨r, v, hv, trivial⟩
      rw [(A.apply_mem_other C e r this).2, h r]

/-- In the base case, a process running solo from a configuration reached by reads only must
write before it returns (otherwise it would win, and so would a second process running solo
afterwards — by Claim 5.2). -/
lemma solo_writes (hLE : A.IsLeaderElection) (hST : A.SoloTerminating)
    {C₀ : Config P Reg V L} (h0 : A.IsInit C₀) {es : List (P × L)} (hv : A.Valid C₀ es)
    (hnw : ¬ A.WritesIn C₀ es Set.univ) (p q : P) (hpq : p ≠ q) {ρ : List (P × L)}
    (hvρ : A.Valid (A.run C₀ es) ρ)
    (hfin : A.Finished (A.run (A.run C₀ es) ρ) p) :
    A.WritesIn (A.run C₀ es) ρ Set.univ := by
  by_contra hw
  have hnw' : ¬ A.WritesIn C₀ (es ++ ρ) Set.univ := by
    rw [writesIn_append, not_or]; exact ⟨hnw, hw⟩
  have hv' : A.Valid C₀ (es ++ ρ) := (A.valid_append _ _ _).2 ⟨hv, hvρ⟩
  have hreach : A.Reachable (A.run C₀ (es ++ ρ)) := ⟨C₀, _, h0, hv', rfl⟩
  obtain ⟨ρq, hρq, hvρq, hfinq⟩ := hST _ hreach q
  have hv'' : A.Valid C₀ (es ++ ρ ++ ρq) := (A.valid_append _ _ _).2 ⟨hv', hvρq⟩
  have hwr : ∀ r, (A.run C₀ (es ++ ρ)).wr r = none := A.wr_none_of_no_writes h0.2.2 hnw'
  have hsees : ∀ a b, A.SeesIn C₀ (es ++ ρ ++ ρq) a b → a = q ∧ b = q := by
    intro a b h
    rcases (A.seesIn_append _ _ _ a b).1 h with h | h
    · exact absurd h (A.no_sees_of_no_writes h0.2.2 hnw' a b)
    · have := A.seesIn_of_visible {q} ρq _ (fun r p' hp' => by rw [hwr r] at hp'; cases hp')
        (fun e he => hρq e he) a b h
      exact ⟨this.1, this.2⟩
  have hfinp : A.Finished (A.run C₀ (es ++ ρ ++ ρq)) p := by
    rw [A.run_append]
    refine (A.finished_run hvρq ?_).1
    rw [A.run_append]; exact hfin
  have hfinq' : A.Finished (A.run C₀ (es ++ ρ ++ ρq)) q := by rw [A.run_append]; exact hfinq
  obtain ⟨⟨w1, hw1, hwon1⟩, -⟩ := A.claim_5_2 hLE h0 hv'' {p} ⟨p, rfl⟩
    (fun a b h ha => by
      have := hsees a b h
      exact absurd (ha.symm.trans this.1) hpq)
    (fun x hx => by rw [hx]; exact hfinp)
  obtain ⟨⟨w2, hw2, hwon2⟩, -⟩ := A.claim_5_2 hLE h0 hv'' {q} ⟨q, rfl⟩
    (fun a b h _ => (hsees a b h).2) (fun x hx => by rw [hx]; exact hfinq')
  have := (hLE C₀ _ h0 hv'' Set.univ (fun _ _ => trivial)).1 w1 trivial w2 trivial hwon1 hwon2
  rw [hw1, hw2] at this
  exact hpq this

/-- Base case construction: the processes of `ps` run solo one after the other, each until it
is poised to write for the first time. -/
lemma base_aux (hLE : A.IsLeaderElection) (hST : A.SoloTerminating)
    {C₀ : Config P Reg V L} (h0 : A.IsInit C₀) (two : ∀ p : P, ∃ q, q ≠ p) :
    ∀ ps : List P, ∃ es, A.Valid C₀ es ∧ (∀ e ∈ es, e.1 ∈ ps) ∧
      ¬ A.WritesIn C₀ es Set.univ ∧ ∀ p ∈ ps, ∃ r, A.Covers (A.run C₀ es) p r := by
  intro ps
  induction ps with
  | nil => exact ⟨[], trivial, by simp, id, by simp⟩
  | cons p ps ih =>
    obtain ⟨es, hv, hmem, hnw, hcov⟩ := ih
    have hreach : A.Reachable (A.run C₀ es) := ⟨C₀, es, h0, hv, rfl⟩
    obtain ⟨ρ, hρ, hvρ, hfin⟩ := hST _ hreach p
    obtain ⟨q, hq⟩ := two p
    have hw := A.solo_writes hLE hST h0 hv hnw p q hq.symm hvρ hfin
    obtain ⟨ρ₁, ρ₂, rfl, hno, e, he, r, -, hc⟩ := A.exists_prefix_cover Set.univ ρ _ hw
    have hvρ₁ : A.Valid (A.run C₀ es) ρ₁ := ((A.valid_append _ _ _).1 hvρ).1
    refine ⟨es ++ ρ₁, (A.valid_append _ _ _).2 ⟨hv, hvρ₁⟩, ?_, ?_, ?_⟩
    · intro e' he'
      rcases List.mem_append.1 he' with he' | he'
      · exact List.mem_cons_of_mem _ (hmem e' he')
      · rw [hρ e' (List.mem_append_left _ he')]; exact List.mem_cons_self
    · rw [writesIn_append, not_or]; exact ⟨hnw, hno⟩
    · intro p' hp'
      rw [A.run_append]
      by_cases hpp : p' = p
      · subst hpp
        rw [hρ e he] at hc
        exact ⟨r, hc⟩
      · have hp'ps : p' ∈ ps := by
          rcases List.mem_cons.1 hp' with h | h
          · exact absurd h hpp
          · exact h
        obtain ⟨r', hr'⟩ := hcov p' hp'ps
        exact ⟨r', A.covers_run_of_not_mem hr'
          (fun e' he' h' => hpp (h'.symm.trans (hρ e' (List.mem_append_left _ he'))))⟩

/-- Lemma 5.4, base case `k = 0`. -/
lemma stage_zero (hLE : A.IsLeaderElection) (hST : A.SoloTerminating)
    (Act : Finset P) (N : ℕ) (hN : Act.card = N) (two : ∀ p : P, ∃ q, q ≠ p) :
    Nonempty (A.Stage Act N 0) := by
  -- an initial configuration
  choose l hl using A.init_nonempty
  let C₀ : Config P Reg V L := ⟨l, A.v₀, fun _ => none⟩
  have h0 : A.IsInit C₀ := ⟨hl, fun _ => rfl, fun _ => rfl⟩
  obtain ⟨es, hv, hmem, hnw, hcov⟩ := A.base_aux hLE hST h0 two Act.toList
  exact ⟨{
    C₀ := C₀, es := es, init := h0, valid := hv
    onlyAct := fun e he => Finset.mem_toList.1 (hmem e he)
    g := id, reps := Act, reps_sub := subset_rfl, g_mem := fun p hp => hp
    g_rep := fun _ _ => rfl
    cover := fun q hq => hcov q (Finset.mem_toList.2 hq)
    cnt_le := fun r => by rw [← hN]; exact A.cnt_le_card _ _ _
    cnt_vis := fun r h => absurd (A.wr_none_of_no_writes h0.2.2 hnw r) h
    closed := fun p q h => absurd h (A.no_sees_of_no_writes h0.2.2 hnw p q)
    card := by simp [hN] }⟩

/-! ### Induction step -/

section Step

variable [Fintype Reg]

/-- Lemma 5.4, induction step from round `k` to round `k + 1` (for `k + 2 ≤ N`). -/
lemma stage_succ (hLE : A.IsLeaderElection) (hST : A.SoloTerminating) [Fintype P]
    {Act : Finset P} {N k : ℕ} (hk : k + 2 ≤ N) (S : A.Stage Act N k) :
    Nonempty (A.Stage Act N (k + 1)) := by
  set C := A.run S.C₀ S.es with hC
  -- `R`: registers covered by exactly `N - k` representatives
  set R : Finset Reg := Finset.univ.filter (fun r => A.cnt C S.reps r = N - k) with hRdef
  have hRmem : ∀ r, r ∈ R ↔ A.cnt C S.reps r = N - k := by simp [hRdef]
  by_cases hRe : R = ∅
  · -- nothing to do in this round
    refine ⟨{ S with
      cnt_le := fun r => ?_
      cnt_vis := fun r h => ?_
      card := ?_ }⟩
    · show A.cnt C S.reps r ≤ N - (k + 1)
      have h1 : A.cnt C S.reps r ≤ N - k := S.cnt_le r
      have h2 : A.cnt C S.reps r ≠ N - k := fun h => by
        have := (hRmem r).2 h; rw [hRe] at this; simp at this
      omega
    · have := (hRmem r).2 (S.cnt_vis r h); rw [hRe] at this; simp at this
    · exact (f_succ_le (by omega)).trans S.card
  have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.2 hRe
  obtain ⟨r0, hr0⟩ := hRne
  -- choose the representatives `q_{i_j}` covering the registers of `R`
  have hpos : ∀ r ∈ R, (S.reps.filter (fun q => A.Covers C q r)).Nonempty := by
    intro r hr
    rw [← Finset.card_pos]
    have := (hRmem r).1 hr; unfold cnt at this; omega
  obtain ⟨d0, hd0⟩ := hpos r0 hr0
  have hW : ∀ r, ∃ q, r ∈ R → q ∈ S.reps ∧ A.Covers C q r := fun r =>
    if h : r ∈ R then (let ⟨q, hq⟩ := hpos r h; ⟨q, fun _ => Finset.mem_filter.1 hq⟩)
    else ⟨d0, fun h' => absurd h' h⟩
  choose W hW using hW
  have hWinj : Set.InjOn W R := fun r hr r' hr' h =>
    A.covers_unique (hW r hr).2 (h ▸ (hW r' hr').2)
  set chosen := R.image W with hchosen
  have hchosen_sub : chosen ⊆ S.reps := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hq
    exact (hW r hr).1
  -- a chosen representative covers only its own register
  have hch_cov : ∀ q ∈ chosen, ∀ r, A.Covers C q r → r ∈ R ∧ q = W r := by
    intro q hq r hc
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hq
    have := A.covers_unique (hW r' hr').2 hc
    subst this; exact ⟨hr', rfl⟩
  set Q : Set P := {p | p ∈ Act ∧ S.g p ∈ chosen} with hQdef
  -- `R'`: registers covered by exactly `N - k - 1` representatives
  set R' : Finset Reg := Finset.univ.filter (fun r => A.cnt C S.reps r = N - k - 1) with hR'def
  have hR'mem : ∀ r, r ∈ R' ↔ A.cnt C S.reps r = N - k - 1 := by simp [hR'def]
  -- a representative not chosen is not in `Q`
  have hrep_notQ : ∀ q ∈ S.reps, q ∉ chosen → q ∉ Q := by
    intro q hq hnc hQ
    exact hnc (S.g_rep q hq ▸ hQ.2)
  have hWQ : ∀ r ∈ R, W r ∈ Q := by
    intro r hr
    refine ⟨S.reps_sub (hW r hr).1, ?_⟩
    rw [S.g_rep _ (hW r hr).1]; exact Finset.mem_image_of_mem W hr
  -- apply Claim 5.3
  have hsees_act : ∀ p q, A.SeesIn S.C₀ S.es p q → p ∈ Act ∧ q ∈ Act := by
    intro p q h
    exact A.seesIn_of_visible (↑Act) S.es S.C₀
      (fun r p hp => by rw [S.init.2.2 r] at hp; cases hp) S.onlyAct p q h
  have hQclosed : A.Closed S.C₀ S.es Q := by
    rw [A.closed_iff]
    intro p q h
    obtain ⟨hp, hq⟩ := hsees_act p q h
    have := S.closed p q h
    simp only [hQdef, Set.mem_ofPred_eq, this]
    exact ⟨fun h' => ⟨hq, h'.2⟩, fun h' => ⟨hp, h'.2⟩⟩
  have hvis : ∀ r ∉ R, C.wr r = none := by
    intro r hr
    by_contra h
    exact hr ((hRmem r).2 (S.cnt_vis r h))
  have hQbar : ∀ r ∈ R ∪ R', ∃ p ∉ Q, A.Covers C p r := by
    intro r hr
    rcases Finset.mem_union.1 hr with hr | hr
    · have hcard := (hRmem r).1 hr
      have h1 : 1 < (S.reps.filter (fun q => A.Covers C q r)).card := by
        unfold cnt at hcard; omega
      obtain ⟨q', hq', hne⟩ := Finset.exists_mem_ne h1 (W r)
      rw [Finset.mem_filter] at hq'
      refine ⟨q', fun hQ => hne ?_, hq'.2⟩
      by_contra hne'
      have hc : q' ∈ chosen := by
        have := hQ.2; rwa [S.g_rep q' hq'.1] at this
      exact hne' (hch_cov q' hc r hq'.2).2
    · have hcard := (hR'mem r).1 hr
      have h1 : 0 < (S.reps.filter (fun q => A.Covers C q r)).card := by
        unfold cnt at hcard; omega
      obtain ⟨q', hq'⟩ := Finset.card_pos.1 h1
      rw [Finset.mem_filter] at hq'
      refine ⟨q', fun hQ => ?_, hq'.2⟩
      have hc : q' ∈ chosen := by
        have := hQ.2; rwa [S.g_rep q' hq'.1] at this
      have := (hRmem r).1 (hch_cov q' hc r hq'.2).1
      omega
  have hQcov : ∀ r ∈ R, ∃ q ∈ Q, A.Covers C q r := fun r hr => ⟨W r, hWQ r hr, (hW r hr).2⟩
  obtain ⟨β, hβQ, hvβ, hwβ, hsβ⟩ :=
    A.claim_5_3 hLE hST S.init S.valid R R' ⟨r0, hr0⟩ hvis Q hQclosed hQbar hQcov
  -- the longest prefix without a write outside `R ∪ R'`
  obtain ⟨β₁, β₂, rfl, hno, e, he, rn, hrn, hcn⟩ :=
    A.exists_prefix_cover {r | r ∉ R ∪ R'} β C hwβ
  set qn := e.1
  have hqnQ : qn ∈ Q := hβQ e he
  have hvβ₁ : A.Valid C β₁ := ((A.valid_append _ _ _).1 hvβ).1
  have hβ₁Q : ∀ e ∈ β₁, e.1 ∈ Q := fun e he => hβQ e (List.mem_append_left _ he)
  set C' := A.run C β₁ with hC'
  -- representatives that are not chosen keep their state
  have hkeep : ∀ q, q ∉ Q → ∀ r, (A.Covers C' q r ↔ A.Covers C q r) := by
    intro q hq r
    unfold Covers
    rw [A.run_loc_of_not_mem C β₁ q (fun e he h => hq (h ▸ hβ₁Q e he))]
  set reps' := insert qn (S.reps \ chosen) with hreps'
  have hqn_notin : qn ∉ S.reps \ chosen := by
    intro h
    rw [Finset.mem_sdiff] at h
    exact hrep_notQ qn h.1 h.2 hqnQ
  -- counting in the new configuration
  have hcnt_old : ∀ r, ((S.reps \ chosen).filter (fun q => A.Covers C' q r)).card =
      A.cnt C S.reps r - (if r ∈ R then 1 else 0) := by
    intro r
    have hfe : (S.reps \ chosen).filter (fun q => A.Covers C' q r) =
        (S.reps.filter (fun q => A.Covers C q r)) \ chosen := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, (hkeep q (hrep_notQ q h1 h2) r).1 h3⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩
        exact ⟨⟨h1, h2⟩, (hkeep q (hrep_notQ q h1 h2) r).2 h3⟩
    rw [hfe, Finset.card_sdiff]
    unfold cnt
    congr 1
    split_ifs with hr
    · rw [Finset.card_eq_one]
      refine ⟨W r, ?_⟩
      ext q
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hc, -, hcov⟩; exact (hch_cov q hc r hcov).2
      · rintro rfl; exact ⟨Finset.mem_image_of_mem W hr, (hW r hr).1, (hW r hr).2⟩
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro q hq
      simp only [Finset.mem_inter, Finset.mem_filter] at hq
      exact hr (hch_cov q hq.1 r hq.2.2).1
  have hcnt_new : ∀ r, A.cnt C' reps' r ≤
      A.cnt C S.reps r - (if r ∈ R then 1 else 0) + (if A.Covers C' qn r then 1 else 0) := by
    intro r
    have ho := hcnt_old r
    unfold cnt at ho ⊢
    rw [← ho, hreps', Finset.filter_insert]
    by_cases h : A.Covers C' qn r
    · simp only [h, ite_true]; exact Finset.card_insert_le _ _
    · simp only [h, ite_false, add_zero]; exact le_rfl
  have hcnt_RR' : ∀ r ∈ R ∪ R', A.cnt C' reps' r = N - (k + 1) := by
    intro r hr
    have hnc : ¬ A.Covers C' qn r := fun h => hrn (by
      rw [A.covers_unique hcn h]; exact hr)
    unfold cnt
    rw [hreps', Finset.filter_insert, ite_eq_right hnc, hcnt_old r]
    rcases Finset.mem_union.1 hr with hr | hr
    · rw [ite_eq_left hr, (hRmem r).1 hr]; omega
    · have h1 := (hR'mem r).1 hr
      have hr' : r ∉ R := fun h => by have := (hRmem r).1 h; omega
      rw [ite_eq_right hr', h1]; omega
  -- the new stage
  have hvall : A.Valid S.C₀ (S.es ++ β₁) := (A.valid_append _ _ _).2 ⟨S.valid, hvβ₁⟩
  have hrun : A.run S.C₀ (S.es ++ β₁) = C' := A.run_append _ _ _
  refine ⟨{
    C₀ := S.C₀
    es := S.es ++ β₁
    init := S.init
    valid := hvall
    onlyAct := fun e he => ?_
    g := fun p => if p ∈ Q then qn else S.g p
    reps := reps'
    reps_sub := ?_
    g_mem := ?_
    g_rep := ?_
    cover := ?_
    cnt_le := ?_
    cnt_vis := ?_
    closed := ?_
    card := ?_ }⟩
  · rcases List.mem_append.1 he with he | he
    · exact S.onlyAct e he
    · exact (hβ₁Q e he).1
  · intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact hqnQ.1
    · exact S.reps_sub (Finset.mem_sdiff.1 hq).1
  · intro p hp
    by_cases hpQ : p ∈ Q
    · simp only [ite_eq_left hpQ]; exact Finset.mem_insert_self _ _
    · simp only [ite_eq_right hpQ]
      refine Finset.mem_insert_of_mem (Finset.mem_sdiff.2 ⟨S.g_mem p hp, fun h => hpQ ⟨hp, h⟩⟩)
  · intro q hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · simp only [ite_eq_left hqnQ]
    · have := Finset.mem_sdiff.1 hq
      simp only [ite_eq_right (hrep_notQ q this.1 this.2)]
      exact S.g_rep q this.1
  · intro q hq
    rw [hrun]
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact ⟨rn, hcn⟩
    · have := Finset.mem_sdiff.1 hq
      obtain ⟨r, hr⟩ := S.cover q this.1
      exact ⟨r, (hkeep q (hrep_notQ q this.1 this.2) r).2 hr⟩
  · intro r
    rw [hrun]
    by_cases hr : r ∈ R ∪ R'
    · rw [hcnt_RR' r hr]
    · have h1 := hcnt_new r
      have h2 : A.cnt C S.reps r ≤ N - k := S.cnt_le r
      have h3 : A.cnt C S.reps r ≠ N - k := fun h => hr (Finset.mem_union_left _ ((hRmem r).2 h))
      have h4 : A.cnt C S.reps r ≠ N - k - 1 :=
        fun h => hr (Finset.mem_union_right _ ((hR'mem r).2 h))
      have h5 : r ∉ R := fun h => hr (Finset.mem_union_left _ h)
      rw [ite_eq_right h5] at h1
      split_ifs at h1 <;> omega
  · intro r hw
    rw [hrun] at hw ⊢
    by_cases hr : r ∈ R ∪ R'
    · exact hcnt_RR' r hr
    · exfalso
      have hnw : ¬ A.WritesIn C β₁ {r} := fun h => hno (A.writesIn_mono (by simpa using hr) h)
      rw [(A.run_mem_of_not_writesIn C β₁ r hnw).2] at hw
      exact hr (Finset.mem_union_left _ ((hRmem r).2 (S.cnt_vis r hw)))
  · intro p q h
    rcases (A.seesIn_append _ _ _ p q).1 h with h | h
    · obtain ⟨hp, hq⟩ := hsees_act p q h
      have hg := S.closed p q h
      have hiff : p ∈ Q ↔ q ∈ Q := by
        simp only [hQdef, Set.mem_ofPred_eq, hg]
        exact ⟨fun h' => ⟨hq, h'.2⟩, fun h' => ⟨hp, h'.2⟩⟩
      by_cases hpQ : p ∈ Q
      · simp only [ite_eq_left hpQ, ite_eq_left (hiff.1 hpQ)]
      · simp only [ite_eq_right hpQ, ite_eq_right (fun h => hpQ (hiff.2 h)), hg]
    · have hp : p ∈ Q := by
        obtain ⟨e, he, rfl⟩ := A.seesIn_mem h; exact hβ₁Q e he
      have hq : q ∈ Q := hsβ p q ((A.seesIn_append _ _ _ p q).2 (Or.inl h)) hp
      simp only [ite_eq_left hp, ite_eq_left hq]
  · -- (e): `m_{k+1} = m_k - |R| + 1 ≥ f(k+1)`
    have hcard' : reps'.card = S.reps.card - R.card + 1 := by
      rw [hreps', Finset.card_insert_of_notMem hqn_notin, Finset.card_sdiff_of_subset hchosen_sub,
        hchosen, Finset.card_image_of_injOn hWinj]
    have hRle : (N - k) * R.card ≤ S.reps.card :=
      A.mul_le_card C S.reps R (N - k) (fun r hr => ((hRmem r).1 hr).ge)
    have hRdiv : R.card ≤ S.reps.card / (N - k) :=
      (Nat.le_div_iff_mul_le (by omega)).2 (by rw [mul_comm]; exact hRle)
    have hmono := step_mono (N - k) S.card
    have hdl := Nat.div_le_self S.reps.card (N - k)
    rw [hcard', f_succ]
    omega

/-- **Lemma 5.4.** For a leader election algorithm with nondeterministic solo-termination and a
set `Act` of `N ≥ 2` processes, for every `k ∈ {0, …, N-1}` there is a stage `k` of the covering
construction (`Stage`: an execution `E_k`, a partition of `Act` into groups with representatives,
satisfying (a)–(d), and at least `f N k` groups, which is what (e) is used for). -/
theorem lemma_5_4 (hLE : A.IsLeaderElection) (hST : A.SoloTerminating) [Fintype P]
    (Act : Finset P) (N : ℕ) (hN : Act.card = N) (hN2 : 2 ≤ N) :
    ∀ k, k ≤ N - 1 → Nonempty (A.Stage Act N k) := by
  have two : ∀ p : P, ∃ q, q ≠ p := by
    intro p
    have : 1 < Fintype.card P := lt_of_lt_of_le (by omega) (hN ▸ Finset.card_le_univ Act)
    exact Fintype.exists_ne_of_one_lt_card this p
  intro k
  induction k with
  | zero => intro _; exact A.stage_zero hLE hST Act N hN two
  | succ k ih =>
    intro hk
    obtain ⟨S⟩ := ih (by omega)
    exact A.stage_succ hLE hST (by omega) S

/-- Lemma 5.4(d) in the paper's form: every group `{p ∈ Act | g p = q}` is closed w.r.t.
`≡_{E_k}`. -/
lemma Stage.group_closed {Act : Finset P} {N k : ℕ} (S : A.Stage Act N k) (q : P) :
    A.Closed S.C₀ S.es {p | p ∈ Act ∧ S.g p = q} := by
  rw [A.closed_iff]
  intro p p' h
  obtain ⟨hp, hp'⟩ := A.seesIn_of_visible (↑Act) S.es S.C₀
    (fun r x hx => by rw [S.init.2.2 r] at hx; cases hx) S.onlyAct p p' h
  have := S.closed p p' h
  simp only [Set.mem_ofPred_eq, this]
  exact ⟨fun h' => ⟨hp', h'.2⟩, fun h' => ⟨hp, h'.2⟩⟩

end Step

end Alg

end Podc.LeaderElectionSpaceLB
