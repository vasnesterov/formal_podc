import Papers.PODC2025.LanguageDecidability.Canonical

/-!
# Theorem 5.2: decidable languages are real-time oblivious

For every decidability predicate `P` (of the report trace) and every algorithm `V`, if `V`
`P`-decides a distributed language `L`, then `L` is real-time oblivious (`thm_5_2`). In
particular every language in `SD` or `WD` (or `WAD`, `WOD`) is real-time oblivious
(`rto_of_SD`, `rto_of_WD`, …).

Proof: by `rto_iff_swapClosed` it suffices to transpose two adjacent symbols `x k`, `x (k+1)`
of different processes. The execution `vari x k` has input `x` and the send/receive events of
these symbols adjacent; transposing them (`swapSched`) gives an execution with input
`swapAt x k` and exactly the same configurations and reports. The paper's proof moves a whole
block of `pᵢ`'s steps and then one event; here the reordered execution is built directly.
-/

namespace Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type} {R : Type}

lemma phs_congr_from {s s' : ℕ → Ev I O} {T : ℕ} (h0 : phs s T = phs s' T)
    (h : ∀ t, T ≤ t → s t = s' t) : ∀ t, T ≤ t → phs s t = phs s' t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact h0
  | succ t ht ih => simp only [phs]; rw [ih, h t ht]

theorem isExec_vari {x : Word I O} (wf : WF x) {k : ℕ} (hk : (x k).1 ≠ (x (k + 1)).1) :
    IsExec (vari x k) where
  valid t := by
    rcases Nat.lt_or_ge t (2 * k) with h | h
    · rw [phs_congr (s' := canon x) (T := 2 * k) (fun t ht => vari_out x k t (by omega)) t h.le,
        vari_out x k t (by omega)]
      exact (isExec_canon wf).valid t
    rcases Nat.lt_or_ge t (2 * k + 4) with h' | h'
    · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ t = 2 * k + j := ⟨t - 2 * k, by omega, by omega⟩
      exact (vari_seg wf hk).1 j hj
    · have h4 : phs (vari x k) (2 * (k + 2)) = phs (canon x) (2 * (k + 2)) := by
        rw [phs_canon wf, show 2 * (k + 2) = 2 * k + 4 by ring]; exact (vari_seg wf hk).2
      rw [phs_congr_from h4 (fun t ht => vari_out x k t (by omega)) t (by omega),
        vari_out x k t (by omega)]
      exact (isExec_canon wf).valid t
  fair p N := by
    obtain ⟨m, hm, w, hw⟩ := wf.exists_res p (N + k + 2)
    refine ⟨2 * m + 1, by omega, w, ?_⟩
    rw [vari_out x k _ (by omega), canon_odd, hw]; rfl

/-- Positions of the input symbols in `vari x k`. -/
def ioPosV (x : Word I O) (k m : ℕ) : ℕ :=
  if m = k then 2 * k + ioOff (x k) (x (k + 1))
  else if m = k + 1 then 2 * k + ioOff (x k) (x (k + 1)) + 1 else ioPos x m

lemma ioPosV_bounds (x : Word I O) (k m : ℕ) :
    (m < k → ioPosV x k m < 2 * m + 2) ∧ (k + 1 < m → 2 * m ≤ ioPosV x k m) ∧
      2 * k ≤ ioPosV x k k ∧ ioPosV x k (k + 1) < 2 * k + 4 ∧
      ioPosV x k (k + 1) = ioPosV x k k + 1 := by
  have := ioOff_le (x k) (x (k + 1))
  refine ⟨fun h => ?_, fun h => ?_, ?_, ?_, ?_⟩
  · simp only [ioPosV, if_neg (show m ≠ k by omega), if_neg (show m ≠ k + 1 by omega)]
    exact (ioPos_lt x m).2
  · simp only [ioPosV, if_neg (show m ≠ k by omega), if_neg (show m ≠ k + 1 by omega)]
    exact (ioPos_lt x m).1
  · simp [ioPosV]
  · simp [ioPosV]; omega
  · simp [ioPosV]

theorem hasInput_vari {x : Word I O} (k : ℕ) :
    StrictMono (ioPosV x k) ∧ (∀ t, (vari x k t).sym.isSome → ∃ m, ioPosV x k m = t) ∧
      ∀ m, (vari x k (ioPosV x k m)).sym = some (x m) := by
  have hb := ioPosV_bounds x k
  have hoff := ioOff_le (x k) (x (k + 1))
  refine ⟨strictMono_nat_of_lt_succ fun m => ?_, fun t ht => ?_, fun m => ?_⟩
  · rcases lt_trichotomy (m + 1) k with h | h | h
    · have := (hb m).1 (by omega); have := (hb (m + 1)).1 h
      simp only [ioPosV, if_neg (show m ≠ k by omega), if_neg (show m ≠ k + 1 by omega),
        if_neg (show m + 1 ≠ k by omega), if_neg (show m + 1 ≠ k + 1 by omega)]
      have := ioPos_lt x m; have := ioPos_lt x (m + 1); omega
    · subst h; have := (hb m).1 (by omega); have := (hb (m + 1)).2.2.1; omega
    · rcases (show m = k ∨ k + 1 ≤ m by omega) with h' | h'
      · subst h'; have := (hb m).2.2.2.2; omega
      rcases h'.eq_or_lt with h' | h'
      · subst h'; have := (hb (k + 1)).2.2.2.1; have := (hb (k + 1 + 1)).2.1 (by omega); omega
      · have := (hb (m + 1)).2.1 (by omega)
        simp only [ioPosV, if_neg (show m ≠ k by omega), if_neg (show m ≠ k + 1 by omega),
          if_neg (show m + 1 ≠ k by omega), if_neg (show m + 1 ≠ k + 1 by omega)]
        have := ioPos_lt x m; have := ioPos_lt x (m + 1); omega
  · by_cases hin : 2 * k ≤ t ∧ t < 2 * k + 4
    · obtain ⟨j, hj, rfl⟩ : ∃ j, j < 4 ∧ t = 2 * k + j := ⟨t - 2 * k, by omega, by omega⟩
      rw [vari_in x k j hj] at ht
      rcases varEv_sym hj ht with rfl | rfl
      · exact ⟨k, by simp [ioPosV]⟩
      · exact ⟨k + 1, by simp [ioPosV]; omega⟩
    · rw [vari_out x k t hin] at ht
      have h := canon_sym_isSome ht
      have := ioPos_lt x (t / 2)
      refine ⟨t / 2, ?_⟩
      simp only [ioPosV, if_neg (show t / 2 ≠ k by omega), if_neg (show t / 2 ≠ k + 1 by omega), h]
  · have ek : ioPosV x k k = 2 * k + ioOff (x k) (x (k + 1)) := by simp [ioPosV]
    have ek1 : ioPosV x k (k + 1) = 2 * k + (ioOff (x k) (x (k + 1)) + 1) := by
      simp [ioPosV]; ring
    by_cases h1 : m = k
    · subst h1; rw [ek, vari_in x m _ (by omega)]; exact (varEv_ioOff _ _).1
    by_cases h2 : m = k + 1
    · subst h2; rw [ek1, vari_in x k _ (by omega)]; exact (varEv_ioOff _ _).2
    · have := ioPos_lt x m
      simp only [ioPosV, if_neg h1, if_neg h2]
      rw [vari_out x k _ (by omega)]; exact canon_ioPos x m

/-- The key lemma: every `P`-decidable language is closed under transposing two adjacent
symbols of different processes (in words of the language). -/
theorem swapClosed_of_decides {L : Set (Word I O)} {P : (ℕ → Option (Fin n × R)) → Prop}
    {V : Alg n I O R} (hV : Decides V L P) {x : Word I O} (wf : WF x) (hx : x ∈ L) {k : ℕ}
    (hk : (x k).1 ≠ (x (k + 1)).1) : swapAt x k ∈ L := by
  obtain ⟨hmono, hcov, hsym⟩ := hasInput_vari (x := x) k
  have hb := ioPosV_bounds x k 0
  set t₀ := ioPosV x k k
  have h1 : (vari x k t₀).sym.isSome := by rw [hsym k]; rfl
  have h2 : (vari x k (t₀ + 1)).sym.isSome := by rw [← hb.2.2.2.2, hsym (k + 1)]; rfl
  have hp : (vari x k t₀).proc ≠ (vari x k (t₀ + 1)).proc := by
    have e1 : vari x k t₀ = varEv (x k) (x (k + 1)) (ioOff (x k) (x (k + 1))) := by
      rw [← vari_in x k _ (by have := ioOff_le (x k) (x (k + 1)); omega)]; simp [t₀, ioPosV]
    have e2 : vari x k (t₀ + 1) = varEv (x k) (x (k + 1)) (ioOff (x k) (x (k + 1)) + 1) := by
      rw [← vari_in x k _ (by have := ioOff_le (x k) (x (k + 1)); omega)]
      simp [t₀, ioPosV]; ring_nf
    rw [e1, e2, (varEv_proc _ _).1, (varEv_proc _ _).2]; exact hk
  have hE := isExec_vari wf hk
  have hE' := hE.swapSched h1 h2 hp
  have hin : HasInput (vari x k) x := ⟨_, hmono, hcov, hsym⟩
  have hin' : HasInput (swapSched (vari x k) t₀) (swapAt x k) :=
    HasInput.swapSched hmono hcov hsym rfl hb.2.2.2.2
  have hP : P (V.outs (vari x k)) := (hV _ _ hE hin).1 hx
  rw [← outs_swapSched V h1 h2] at hP
  exact (hV _ _ hE' hin').2 hP

/-- **Theorem 5.2**: for every decidability predicate `P`, every `P`-decidable distributed
language is real-time oblivious. -/
theorem thm_5_2 {L : Set (Word I O)} (hL : IsDistLang L) {P : (ℕ → Option (Fin n × R)) → Prop}
    (hdec : PDecidable P L) : RTO L := by
  obtain ⟨V, hV⟩ := hdec
  exact rto_of_swapClosed fun x hx k hk => swapClosed_of_decides hV (hL x hx) hx hk

theorem rto_of_SD {L : Set (Word I O)} (hL : IsDistLang L) (h : SD L) : RTO L :=
  thm_5_2 hL h

theorem rto_of_WAD {L : Set (Word I O)} (hL : IsDistLang L) (h : WAD L) : RTO L :=
  thm_5_2 hL h

theorem rto_of_WOD {L : Set (Word I O)} (hL : IsDistLang L) (h : WOD L) : RTO L :=
  thm_5_2 hL h

/-- A weakly deciding algorithm also weakly-all decides. -/
theorem WeaklyDecides.weakAllDecides {V : Alg n I O Verdict} {L : Set (Word I O)}
    (h : WeaklyDecides V L) : WeakAllDecides V L := by
  intro s x hs hx
  refine ⟨(h s x hs hx).1, fun hfin => by_contra fun hxL => ?_⟩
  exact (h s x hs hx).2 hxL (x 0).1 (hfin (x 0).1)

theorem rto_of_WD {L : Set (Word I O)} (hL : IsDistLang L) (h : WD L) : RTO L := by
  obtain ⟨V, hV⟩ := h
  exact thm_5_2 hL ⟨V, hV.weakAllDecides⟩

end Podc2025.LanguageDecidability
