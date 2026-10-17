import Papers.PODC2025.LanguageDecidability.CounterAInv
import Papers.PODC2025.LanguageDecidability.CounterAWords

/-!
# Lemma 5.3: weak eventual counters are weakly decidable

Castañeda, Rodríguez, PODC 2025, Section 5.1.

`lemma_5_3`: the corrected algorithm of Figure 5 (`wecAlg`, see `CounterDefs.lean`) weakly-all
decides `WEC_COUNT` (with the intended reading of property (3)); with Lemma 4.2,
`WEC_COUNT ∈ WD` (`wec_mem_WD`).

The proof follows the paper, using the invariant of `CounterAInv.lean`:
* `x ∈ WEC`: the flag is never set (`not_viol_of_mem`), eventually `INCS` sums to the number `S`
  of `inc`s, every read returns `S`, and `prev_incs = S`, so every process eventually reports
  `YES` forever (`wec_finite`);
* `x ∉ WEC` (`wec_infinite`): (a) an ill-typed operation or a violation of (1)/(2) sets the flag
  of its process forever; (b) infinitely many `inc`s make `curr_incs` unbounded, so every
  process sees `prev_incs < curr_incs` infinitely often (`no_infinite_of_unbounded`);
  (c) otherwise some process has infinitely many reads returning a value `≠ S`.
-/

namespace Podc2025.LanguageDecidability.Counter

open Podc2025.LanguageDecidability

variable {n : ℕ}

/-! ### Word lemmas -/

section word

variable {x : CWord n} {p : Fin n}

lemma lastRead_succ_cases (k : ℕ) : lastRead x p (k + 1) = lastRead x p k ∨
    ∃ v, x k = ⟨p, .inr (.val v)⟩ ∧ lastRead x p (k + 1) = v := by
  rcases hxk : x k with ⟨q, v | w⟩
  · left; simp only [lastRead, hxk]; split_ifs <;> rfl
  · by_cases hq : q = p
    · subst hq
      cases w with
      | ack => left; simp [lastRead, hxk, newRead]
      | val v => right; exact ⟨v, rfl, by simp [lastRead, hxk, newRead]⟩
    · left; simp [lastRead, hxk, hq]

lemma lastRead_spec : ∀ k, lastRead x p k = 0 ∨ ∃ j < k, x j = ⟨p, .inr (.val (lastRead x p k))⟩
  | 0 => Or.inl rfl
  | k + 1 => by
    rcases lastRead_succ_cases (x := x) (p := p) k with h | ⟨v, hv, h⟩
    · rw [h]
      rcases lastRead_spec k with h' | ⟨j, hj, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨j, by omega, h'⟩
    · exact Or.inr ⟨k, by omega, by rw [h, hv]⟩

lemma incs_monotone (x : CWord n) : Monotone (incs x) :=
  monotone_nat_of_le_succ fun k => by simp only [incs]; omega

lemma incs_const {N k : ℕ} (hk : N ≤ k) (h : ∀ m, N ≤ m → ¬ IsInc (x m)) : incs x k = incs x N := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => simp [incs, ih, h k hk]

lemma cnt_pos_exists {k : ℕ} (h : 0 < cnt x p k) : ∃ j < k, (x j).1 = p := by
  by_contra hc
  push Not at hc
  have := cnt_eq_of_no (x := x) (p := p) (Nat.zero_le k) (fun m _ hm => hc m hm)
  simp [cnt] at this; omega

/-- In a well-formed word, every response has an invocation, the last invocation of its process. -/
lemma exists_invAt (wf : WF x) {r : ℕ} {w : CRes} (h : x r = ⟨p, .inr w⟩) :
    ∃ i, invAt x r i ∧ x i = ⟨p, .inl (lastInv x p r)⟩ := by
  classical
  have hodd := wf_seq_inr wf h
  obtain ⟨j₀, hj₀, hpj₀⟩ := cnt_pos_exists (x := x) (p := p) (k := r)
    (by rcases Nat.eq_zero_or_pos (cnt x p r) with h0 | h0
        · rw [h0] at hodd; exact absurd ⟨0, rfl⟩ hodd
        · exact h0)
  set i := Nat.findGreatest (fun j => (x j).1 = p) (r - 1) with hi
  have hpi : (x i).1 = p := Nat.findGreatest_spec (P := fun j => (x j).1 = p) (by omega) hpj₀
  have hir : i < r := by have := Nat.findGreatest_le (P := fun j => (x j).1 = p) (r - 1); omega
  have hnp : ∀ m, i < m → m < r → (x m).1 ≠ p := fun m h1 h2 =>
    Nat.findGreatest_is_greatest h1 (by omega)
  have hinv : invAt x r i := ⟨hir, by rw [h, hpi], fun m h1 h2 => by rw [h]; exact hnp m h1 h2⟩
  have hcnt : cnt x p r = cnt x p i + 1 := by
    rw [cnt_eq_of_no (show i + 1 ≤ r by omega) (fun m h1 h2 => hnp m (by omega) h2), cnt_succ]
    simp [hpi]
  rcases hxi : x i with ⟨q, v | w'⟩
  · rw [hxi] at hpi; simp only at hpi; subst hpi
    refine ⟨i, hinv, ?_⟩
    have e1 := (const_of_noP (x := x) (p := q) (show i + 1 ≤ r by omega)
      (fun m h1 h2 => hnp m (by omega) h2)).2.1
    rw [e1, (succ_of_inv hxi).2.1]; exact hxi
  · exfalso
    rw [hxi] at hpi; simp only at hpi; subst hpi
    have := wf_seq_inr wf hxi
    rw [hcnt, Nat.even_add_one] at hodd
    exact hodd this

lemma lastRead_mono_of (h : ∀ j, ¬ viol x p j) : Monotone (lastRead x p) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rcases lastRead_succ_cases (x := x) (p := p) k with e | ⟨v, hv, e⟩
  · rw [e]
  · rw [e]
    by_contra hlt; push Not at hlt
    exact h k ⟨.val v, hv, Or.inr (by simp [readBad, hlt])⟩

/-- Under (1), (2) and well-typedness, no response is a violation. -/
lemma not_viol_of_mem (wf : WF x) (ty : Typed x) (w1 : WEC1 x) (w2 : WEC2 x) (j : ℕ) :
    ¬ viol x p j := by
  rintro ⟨w, hw, hv⟩
  obtain ⟨i, hi, hxi⟩ := exists_invAt wf hw
  rcases hv with hv | hv
  · rcases ty j i p w hw hi with ⟨h1, rfl⟩ | ⟨h1, v, rfl⟩
    · rw [hxi] at h1; simp only [Sigma.mk.injEq, heq_eq_eq, Sum.inl.injEq, true_and] at h1
      rw [h1] at hv; simp [illTyped] at hv
    · rw [hxi] at h1; simp only [Sigma.mk.injEq, heq_eq_eq, Sum.inl.injEq, true_and] at h1
      rw [h1] at hv; simp [illTyped] at hv
  · obtain ⟨v, hwv, hv'⟩ := readBad_iff.1 hv
    clear hv; subst hwv
    rcases hv' with hv | hv
    · exact absurd (w1 j p v hw) (by omega)
    · rcases lastRead_spec (x := x) (p := p) j with h0 | ⟨j', hj', hj'x⟩
      · omega
      · exact absurd (w2 j j' p v _ hj' hj'x hw) (by omega)

/-- Conversely, if no response is a violation, then (1), (2) and well-typedness hold. -/
lemma props_of_not_viol (wf : WF x) (h : ∀ p j, ¬ viol x p j) : Typed x ∧ WEC1 x ∧ WEC2 x := by
  refine ⟨fun r i p w hw hi => ?_, fun r p v hw => ?_, fun r r' p v v' hlt hr' hr => ?_⟩
  · obtain ⟨i', hi', hxi'⟩ := exists_invAt wf hw
    rw [invAt_unique hi hi'] at *
    have hn : illTyped (lastInv x p r) w = false := by
      by_contra hc; exact h p r ⟨w, hw, Or.inl (by simpa using hc)⟩
    rw [hxi']
    cases hl : lastInv x p r <;> cases w <;> rw [hl] at hn <;> simp_all [illTyped]
  · by_contra hc; push Not at hc
    exact h p r ⟨.val v, hw, Or.inr (by simp [readBad, hc])⟩
  · have hm := lastRead_mono_of (h p) (show r' + 1 ≤ r by omega)
    rw [(succ_of_res hr').1] at hm
    simp only [newRead] at hm
    by_contra hc; push Not at hc
    exact h p r ⟨.val v, hr, Or.inr (by simp [readBad]; omega)⟩

end word

/-! ### Executions of `wecAlg` -/

variable {s : ℕ → CEv n} {x : CWord n} {ι : ℕ → ℕ}

lemma eq_recv_of_sym {e : CEv n} {p : Fin n} {w : CRes} (h : e.sym = some ⟨p, .inr w⟩) :
    e = .recv p w := by
  rcases e with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w'⟩ | ⟨q, w'⟩ <;> simp only [Ev.sym, reduceCtorEq,
    Option.some.injEq] at h
  · simp at h
  · rw [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp at h; subst h; rfl

lemma post_of_outs {t : ℕ} {p : Fin n} {d : Verdict}
    (h : (wecAlg (n := n)).outs s t = some (p, d)) : ∃ w, s t = .post p w := by
  rcases hst : s t with ⟨q, v⟩ | ⟨q, v⟩ | ⟨q, w⟩ | ⟨q, w⟩
  · rw [outs_pre _ _ hst] at h; simp at h
  · rw [outs_of_sym _ _ (by rw [hst]; rfl)] at h; simp at h
  · rw [outs_of_sym _ _ (by rw [hst]; rfl)] at h; simp at h
  · rw [outs_post_eq hst] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain rfl := h.1; exact ⟨w, rfl⟩

/-- With finitely many (`S`) `inc`s, eventually `INCS` sums to `S`. -/
lemma sumMem_eventually (hs : IsExec s) (hx : IsInput s x ι) {S : ℕ} (h : FinIncs x S) :
    ∃ T₀, ∀ t, T₀ ≤ t → sumMem s t = S := by
  obtain ⟨N, hN, hninc⟩ := h
  refine ⟨ι N, fun t ht => ?_⟩
  have hK : N ≤ symCount s t := by
    have := symCount_mono s ht; rwa [hx.symCount_iota] at this
  rw [sumMem_eq hs hx fun p hp => ?_, incs_const hK hninc, hN]
  obtain ⟨t', ht', hst'⟩ := hs.exists_send hp
  have hsome : (s t').sym.isSome = true := by rw [hst']; rfl
  have hxk := hx.sym_eq hsome
  rw [hst'] at hxk; simp only [Ev.sym, Option.some.injEq] at hxk
  exact hninc _ (hK.trans (symCount_mono s ht')) (by rw [← hxk]; rfl)

/-- If `curr_incs` is unbounded, every process reports `NO` infinitely often. -/
lemma no_infinite_of_unbounded (hs : IsExec s) (hx : IsInput s x ι)
    (hub : ∀ B, ∃ t, B ≤ sumMem s t) (p : Fin n) :
    (NoSet ((wecAlg (n := n)).outs s) p).Infinite := by
  intro hfin
  obtain ⟨T, hT⟩ := finite_iff_eventually.1 hfin
  set B₀ := (locAt s T p).prevIncs
  have hyes : ∀ t, T ≤ t → ∀ w, s t = .post p w → sumMem s t ≤ (locAt s t p).prevIncs := by
    intro t ht w hw
    obtain ⟨r, -, -, -, d, hd, hdno⟩ := post_verdict hs hx hw
    by_contra hc; push Not at hc
    exact hT t ht (by simp only [NoSet, Set.mem_ofPred_eq, hd, (hdno.2 (Or.inr (Or.inr hc)))])
  have hle : ∀ t, T ≤ t → (locAt s t p).prevIncs ≤ B₀ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih =>
      by_cases hp : ∃ w, s t = .post p w
      · obtain ⟨w, hw⟩ := hp
        rw [prevIncs_post hw]; exact (hyes t ht w hw).trans ih
      · push Not at hp; rw [prevIncs_of_ne hp]; exact ih
  obtain ⟨t, ht⟩ := hub (B₀ + 1)
  obtain ⟨t', ht', w, hw⟩ := hs.fair p (max t T)
  have h1 := sumMem_mono hs hx (show t ≤ t' by omega)
  have h2 := (hyes t' (by omega) w hw).trans (hle t' (by omega))
  omega

/-- First half of the proof of Lemma 5.3: `x ∈ WEC` implies that every process reports `NO`
finitely often. -/
theorem wec_finite (hs : IsExec s) (hx : IsInput s x ι) (hxL : x ∈ WEC) (p : Fin n) :
    (NoSet ((wecAlg (n := n)).outs s) p).Finite := by
  obtain ⟨wf, ty, w1, w2, S, hfin, N₂, hN₂⟩ := hxL
  have hnb : ∀ k, ¬ bad x p k := fun k ⟨j, _, hj⟩ => not_viol_of_mem wf ty w1 w2 j hj
  obtain ⟨T₀, hT₀⟩ := sumMem_eventually hs hx hfin
  obtain ⟨N, -, hninc⟩ := hfin
  -- a late `read` of `p`, returning `S`
  obtain ⟨j₀, hj₀N, hj₀⟩ : ∃ j₀, N₂ ≤ j₀ ∧ x j₀ = ⟨p, .inr (.val S)⟩ := by
    obtain ⟨j₁, hj₁, hpj₁⟩ := wf.reliable p N
    obtain ⟨j, hj, w, hw⟩ := wf.exists_res p (max (j₁ + 1) N₂)
    obtain ⟨i, hi, hxi⟩ := exists_invAt wf hw
    have hij : j₁ ≤ i := by
      by_contra hc; push Not at hc
      exact hi.2.2 j₁ hc (by omega) (by rw [hpj₁, hw])
    rcases ty j i p w hw hi with ⟨h1, -⟩ | ⟨-, v, rfl⟩
    · exact absurd (by rw [h1]; rfl) (hninc i (by omega))
    · exact ⟨j, by omega, by rw [hw, hN₂ j p v (by omega) hw]⟩
  have hlr : ∀ k, j₀ < k → lastRead x p k = S := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [(succ_of_res hj₀).1]; rfl
    | succ k hk ih =>
      rcases lastRead_succ_cases (x := x) (p := p) k with e | ⟨v, hv, e⟩
      · rw [e, ih]
      · rw [e]; exact hN₂ k p v (by omega) hv
  obtain ⟨t₁, ht₁, w₁, hw₁⟩ := hs.fair p T₀
  have hprev : ∀ t, t₁ + 1 ≤ t → (locAt s t p).prevIncs = S := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [prevIncs_post hw₁, hT₀ t₁ ht₁]
    | succ t ht ih =>
      by_cases hp : ∃ w, s t = .post p w
      · obtain ⟨w, hw⟩ := hp; rw [prevIncs_post hw, hT₀ t (by omega)]
      · push Not at hp; rw [prevIncs_of_ne hp, ih]
  rw [finite_iff_eventually]
  refine ⟨max (t₁ + 1) (ι j₀ + 1), fun t ht hno => ?_⟩
  simp only [NoSet, Set.mem_ofPred_eq] at hno
  obtain ⟨w, hw⟩ := post_of_outs hno
  obtain ⟨r, -, -, hnp, d, hd, hdno⟩ := post_verdict hs hx hw
  rw [hno, Option.some.injEq, Prod.mk.injEq] at hd
  have hrj : j₀ ≤ r := by
    by_contra hc; push Not at hc
    exact hnp j₀ hc (hx.lt_symCount (by omega)) (by rw [hj₀])
  rcases hdno.1 hd.2.symm with h | h | h
  · exact hnb _ h
  · exact h (by rw [hlr _ (by omega), hT₀ t (by omega)])
  · rw [hprev t (by omega), hT₀ t (by omega)] at h; exact lt_irrefl _ h

/-- Second half of the proof of Lemma 5.3: `x ∉ WEC` implies that some process reports `NO`
infinitely often. -/
theorem wec_infinite (hs : IsExec s) (hx : IsInput s x ι) (hxL : x ∉ WEC) :
    ∃ p, (NoSet ((wecAlg (n := n)).outs s) p).Infinite := by
  have wf : WF x := wf_of_exec hs (hasInput_iff.2 ⟨ι, hx⟩)
  by_cases hb : ∃ p j, viol x p j
  · -- (a): a safety violation sets the flag forever
    obtain ⟨p, j, hj⟩ := hb
    refine ⟨p, infinite_iff_frequently.2 fun N => ?_⟩
    obtain ⟨t, ht, w, hw⟩ := hs.fair p (max N (ι j + 1))
    obtain ⟨r, -, -, hnp, d, hd, hdno⟩ := post_verdict hs hx hw
    have hjr : j ≤ r := by
      by_contra hc; push Not at hc
      exact hnp j hc (hx.lt_symCount (by omega)) (viol_proc hj)
    refine ⟨t, by omega, ?_⟩
    simp only [NoSet, Set.mem_ofPred_eq, hd, (hdno.2 (Or.inl ⟨j, by omega, hj⟩))]
  push Not at hb
  obtain ⟨ty, w1, w2⟩ := props_of_not_viol wf hb
  have h3 : ¬ WEC3 x := fun h3 => hxL ⟨wf, ty, w1, w2, h3⟩
  by_cases hf : ∃ S, FinIncs x S
  · -- (c): infinitely many reads return a value different from `S`
    obtain ⟨S, hfin⟩ := hf
    have hev : ¬ EvReads x S := fun h => h3 ⟨S, hfin, h⟩
    obtain ⟨T₀, hT₀⟩ := sumMem_eventually hs hx hfin
    obtain ⟨p, hp⟩ : ∃ p, ∀ N, ∃ r, N ≤ r ∧ ∃ v, x r = ⟨p, .inr (.val v)⟩ ∧ v ≠ S := by
      by_contra hc; push Not at hc
      choose N hN using hc
      exact hev ⟨∑ p, N p, fun r p v hr hxr =>
        hN p r (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)) hr)
          v hxr⟩
    refine ⟨p, infinite_iff_frequently.2 fun N => ?_⟩
    obtain ⟨r, hr, v, hxr, hvS⟩ := hp (max N T₀)
    have hrecv : s (ι r) = .recv p (.val v) := eq_recv_of_sym (by rw [hx.sym r, hxr])
    have hph : phs s (ι r + 1) p = .got (.val v) := by rw [phs_succ, hrecv]; simp
    obtain ⟨t, ht, hst⟩ := hs.exists_post hph
    have hιr : r ≤ ι r := hx.mono.id_le r
    obtain ⟨r', -, hxr', -, d, hd, hdno⟩ := post_verdict hs hx hst
    refine ⟨t, by omega, ?_⟩
    have : lastRead x p (r' + 1) ≠ sumMem s t := by
      rw [(succ_of_res hxr').1, hT₀ t (by omega)]; exact hvS
    simp only [NoSet, Set.mem_ofPred_eq, hd, (hdno.2 (Or.inr (Or.inl this)))]
  · -- (b): infinitely many `inc`s
    have hinc : ∀ N, ∃ m, N ≤ m ∧ IsInc (x m) := by
      intro N; by_contra hc; push Not at hc
      exact hf ⟨incs x N, N, rfl, hc⟩
    have hunb : ∀ B, ∃ k, B ≤ incs x k := by
      intro B
      induction B with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ B ih =>
        obtain ⟨k, hk⟩ := ih
        obtain ⟨m, hm, hm'⟩ := hinc k
        refine ⟨m + 1, ?_⟩
        have := incs_monotone x hm
        simp only [incs, hm', ite_true]; omega
    refine ⟨(x 0).1, no_infinite_of_unbounded hs hx (fun B => ?_) _⟩
    obtain ⟨k, hk⟩ := hunb B
    refine ⟨ι k, le_trans hk ?_⟩
    have := incs_le_sumMem hs hx (ι k)
    rwa [hx.symCount_iota] at this

/-- **Lemma 5.3** (main part): the corrected algorithm of Figure 5 weakly-all decides
`WEC_COUNT`. -/
theorem lemma_5_3 : WeakAllDecides (wecAlg (n := n)) WEC := by
  intro s x hs hx
  obtain ⟨ι, hι⟩ := hasInput_iff.1 hx
  refine ⟨fun hxL p => wec_finite hs hι hxL p, fun h => by_contra fun hxL => ?_⟩
  obtain ⟨p, hp⟩ := wec_infinite hs hι hxL
  exact hp (h p)

/-- **Lemma 5.3**: `WEC_COUNT ∈ WD` (via Lemma 4.2). -/
theorem wec_mem_WD : WD (WEC : Set (CWord n)) := ⟨_, lemma_4_2 lemma_5_3⟩

/-! ### Lemma 5.2: `WEC_COUNT, SEC_COUNT ∉ SD` -/

section SD

variable {I O : Fin n → Type}

/-- The argument of the proof of Lemma 5.2: if a well-formed word `x ∉ L` has arbitrarily long
prefixes that extend to words of `L`, then `L` is not strongly decidable. (In the canonical
execution of `x` some process reports `NO` at some step; the canonical execution of an extension
in `L` of a long enough prefix of `x` has the same first steps.) -/
theorem not_SD_of_extend {L : Set (Word I O)} (hL : IsDistLang L) {x : Word I O} (wf : WF x)
    (hx : x ∉ L) (hext : ∀ k, ∃ y ∈ L, ∀ m < k, y m = x m) : ¬ SD L := by
  rintro ⟨V, hV⟩
  have h1 : ¬ PSD (V.outs (canon x)) := fun h =>
    hx ((hV _ _ (isExec_canon wf) (hasInput_canon x)).2 h)
  simp only [PSD, not_forall, ← Set.nonempty_iff_ne_empty] at h1
  obtain ⟨p, t, ht⟩ := h1
  obtain ⟨y, hy, hyx⟩ := hext (t + 1)
  have hc : ∀ t' < 2 * (t + 1), canon y t' = canon x t' := canon_congr hyx
  have ho := outs_congr V hc t (by omega)
  have h2 : PSD (V.outs (canon y)) := (hV _ _ (isExec_canon (hL y hy)) (hasInput_canon y)).1 hy
  have := h2 p
  rw [Set.eq_empty_iff_forall_notMem] at this
  exact this t (by simp only [NoSet, Set.mem_ofPred_eq] at ht ⊢; rw [ho]; exact ht)

/-- **Lemma 5.2** (corrected word): for `n ≥ 2`, `WEC_COUNT ∉ SD`. -/
theorem wec_not_SD (hn2 : 1 < n) : ¬ SD (WEC : Set (CWord n)) := by
  have hn : 0 < n := by omega
  refine not_SD_of_extend isDistLang_WEC (cw_wf hn gBad) (cw_bad_not_mem hn2) fun k =>
    ⟨cw hn (gGood k), (cw_good_mem hn k).1, fun m hm => cw_good_agree hn k m (by omega)⟩

/-- **Lemma 5.2** (corrected word, proved directly — it does not follow from
`SEC_COUNT ⊆ WEC_COUNT`): for `n ≥ 2`, `SEC_COUNT ∉ SD`. -/
theorem sec_not_SD (hn2 : 1 < n) : ¬ SD (SEC : Set (CWord n)) := by
  have hn : 0 < n := by omega
  refine not_SD_of_extend isDistLang_SEC (cw_wf hn gBad) (fun h => cw_bad_not_mem hn2 h.1)
    fun k => ⟨cw hn (gGood k), cw_good_mem hn k, fun m hm => cw_good_agree hn k m (by omega)⟩

/-- **Lemma 5.2**: for `n ≥ 2`, `WEC_COUNT, SEC_COUNT ∉ SD`. -/
theorem lemma_5_2 (hn2 : 1 < n) :
    ¬ SD (WEC : Set (CWord n)) ∧ ¬ SD (SEC : Set (CWord n)) :=
  ⟨wec_not_SD hn2, sec_not_SD hn2⟩

end SD

/-! ### `SEC_COUNT` is not real-time oblivious (Table 1) -/

/-- For `n ≥ 2`, `SEC_COUNT` is not real-time oblivious: in the word where `p₀` increments and
then all processes read `1`, moving the first read of `p₁` before the `inc` of `p₀` violates
property (4). -/
theorem sec_not_rto (hn2 : 1 < n) : ¬ RTO (SEC : Set (CWord n)) := by
  intro hR
  have hn : 0 < n := by omega
  set x := cw hn (gGood 0) with hxdef
  have hx : x ∈ SEC := cw_good_mem hn 0
  have e0 : x 0 = ⟨⟨0, hn⟩, .inl .inc⟩ := cw_zero hn _
  have e4 : x 4 = ⟨⟨1 % n, Nat.mod_lt _ hn⟩, .inl .read⟩ := cw_read hn _ 1
  have e5 : x 5 = ⟨⟨1 % n, Nat.mod_lt _ hn⟩, .inr (.val 1)⟩ := cw_val hn _ 1
  have hf : ∀ m, (x m).1 = (opA hn (gGood 0) (m / 2)).1 := fun m => seqW_fst m
  set P0 : Fin n := ⟨0, hn⟩
  set P1 : Fin n := ⟨1 % n, Nat.mod_lt _ hn⟩
  have hP : P0 ≠ P1 := by
    intro h; have := congrArg Fin.val h; simp [P0, P1, Nat.mod_eq_of_lt hn2] at this
  have f0 : (x 0).1 = P0 := by rw [e0]
  have f1 : (x 1).1 = P0 := hf 1
  have f2 : (x 2).1 = P0 := by rw [hf 2]; simp [opA, P0]
  have f3 : (x 3).1 = P0 := by rw [hf 3]; simp [opA, P0]
  have f4 : (x 4).1 = P1 := by rw [e4]
  have f5 : (x 5).1 = P1 := by rw [e5]
  have hpfx : pfx x 6 = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl
  have h := hR x hx 6 [x 4, x 5, x 0, x 1, x 2, x 3] (fun p => by
    rw [hpfx]
    simp only [proj, List.filter_cons, f0, f1, f2, f3, f4, f5, List.filter_nil]
    by_cases h0 : P0 = p <;> by_cases h1 : P1 = p
    · exact absurd (h0.trans h1.symm) hP
    all_goals simp [h0, h1])
  set y := app [x 4, x 5, x 0, x 1, x 2, x 3] (shift x 6)
  have hy1 : y 1 = ⟨P1, .inr (.val 1)⟩ := by
    rw [show y 1 = x 5 from app_lt (by simp)]; exact e5
  have hy0 : y 0 = x 4 := app_lt (by simp)
  have h4 := h.2 1 P1 1 hy1
  have : incs y 1 = 0 := by
    simp only [incs, hy0, e4]; rfl
  omega

/-- `SEC_COUNT ∉ SD` (also from Theorem 5.2). -/
theorem sec_not_SD' (hn2 : 1 < n) : ¬ SD (SEC : Set (CWord n)) :=
  fun h => sec_not_rto hn2 (rto_of_SD isDistLang_SEC h)

/-- `SEC_COUNT ∉ WD` (Table 1; via Theorem 5.2). -/
theorem sec_not_WD (hn2 : 1 < n) : ¬ WD (SEC : Set (CWord n)) :=
  fun h => sec_not_rto hn2 (rto_of_WD isDistLang_SEC h)

/-! ### Theorem 5.1 -/

/-- **Theorem 5.1**: `SD ⊂ WD` (for counter words with `n ≥ 2` processes): every strongly
decidable language is weakly decidable, and `WEC_COUNT` is weakly but not strongly decidable. -/
theorem thm_5_1 (hn2 : 1 < n) :
    (∀ L : Set (CWord n), SD L → WD L) ∧ ∃ L : Set (CWord n), WD L ∧ ¬ SD L :=
  ⟨fun L h => (thm_4_1 L).2.2.1 ((thm_4_1 L).1 h), WEC, wec_mem_WD, wec_not_SD hn2⟩

/-- Non-vacuity: `SEC_COUNT` (hence `WEC_COUNT`) is nonempty. -/
theorem sec_nonempty (hn : 0 < n) : (SEC : Set (CWord n)).Nonempty := ⟨_, cw_good_mem hn 0⟩

end Podc2025.LanguageDecidability.Counter
