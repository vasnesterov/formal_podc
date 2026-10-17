import Papers.PODC2025.LanguageDecidability.Model

/-!
# Canonical executions (Claim 3.1) and the swap variant used for Theorem 5.2

* `canon x` — the sequential execution of the proof of Claim 3.1: for the `k`-th symbol of `x`,
  if it is an invocation `v` of `p`, then `p` runs Lines 01–03 (`pre`, `send`); if it is a
  response `w` of `p`, then `p` runs Lines 04–06 (`recv`, `post`). Slots `2k`, `2k+1`.
  `isExec_canon`, `hasInput_canon` (Claim 3.1).
* `canon x` is causal: its first `2k` steps only depend on the first `k` symbols of `x`
  (`canon_congr`, and `run_congr`/`outs_congr` in general).
* `vari x k` — the same, except that the slots `2k … 2k+3` of the symbols `k` and `k+1` (of
  different processes) are reordered so that their send/receive events are adjacent.
-/

namespace Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type} {R : Type}

/-! ### Causality -/

lemma phs_congr {s s' : ℕ → Ev I O} {T : ℕ} (h : ∀ t < T, s t = s' t) :
    ∀ t ≤ T, phs s t = phs s' t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => simp only [phs]; rw [ih (by omega), h t (by omega)]

lemma run_congr (V : Alg n I O R) {s s' : ℕ → Ev I O} {T : ℕ} (h : ∀ t < T, s t = s' t) :
    ∀ t ≤ T, V.run s t = V.run s' t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => simp only [Alg.run]; rw [ih (by omega), h t (by omega)]

lemma outs_congr (V : Alg n I O R) {s s' : ℕ → Ev I O} {T : ℕ} (h : ∀ t < T, s t = s' t) :
    ∀ t < T, V.outs s t = V.outs s' t := by
  intro t ht
  simp only [Alg.outs]; rw [run_congr V h t ht.le, h t ht]

/-! ### The canonical execution -/

/-- First event of the segment of a symbol. -/
def ev0 : Sym I O → Ev I O
  | ⟨p, .inl v⟩ => .pre p v
  | ⟨p, .inr w⟩ => .recv p w

/-- Second event of the segment of a symbol. -/
def ev1 : Sym I O → Ev I O
  | ⟨p, .inl v⟩ => .send p v
  | ⟨p, .inr w⟩ => .post p w

/-- The canonical sequential execution with input `x` (proof of Claim 3.1). -/
def canon (x : Word I O) (t : ℕ) : Ev I O := if t % 2 = 0 then ev0 (x (t / 2)) else ev1 (x (t / 2))

lemma canon_even (x : Word I O) (k : ℕ) : canon x (2 * k) = ev0 (x k) := by
  simp [canon]

lemma canon_odd (x : Word I O) (k : ℕ) : canon x (2 * k + 1) = ev1 (x k) := by
  simp [canon, Nat.add_mod]; congr 2; omega

lemma canon_congr {x y : Word I O} {k : ℕ} (h : ∀ m < k, x m = y m) :
    ∀ t < 2 * k, canon x t = canon y t := by
  intro t ht
  simp only [canon]; rw [h (t / 2) (by omega)]

/-- Program counters of the canonical execution at the start of a segment. -/
def phInv (x : Word I O) (k : ℕ) : Phases I O :=
  fun p => if Even (cnt x p k) then .idle else .waiting

lemma wf_seq_inl {x : Word I O} (wf : WF x) {k : ℕ} {p : Fin n} {v : I p}
    (h : x k = ⟨p, .inl v⟩) : Even (cnt x p k) := by
  have := wf.seq k; rw [h] at this; simpa using this

lemma wf_seq_inr {x : Word I O} (wf : WF x) {k : ℕ} {p : Fin n} {w : O p}
    (h : x k = ⟨p, .inr w⟩) : ¬ Even (cnt x p k) := by
  have := wf.seq k; rw [h] at this; simpa using this

lemma cnt_succ_ne {x : Word I O} {k : ℕ} {q : Fin n} (h : (x k).1 ≠ q) :
    cnt x q (k + 1) = cnt x q k := by
  simp [cnt_succ, h]

lemma cnt_succ_eq {x : Word I O} {k : ℕ} : cnt x (x k).1 (k + 1) = cnt x (x k).1 k + 1 := by
  simp [cnt_succ]

lemma phInv_succ {x : Word I O} (wf : WF x) (k : ℕ) :
    phStep (phStep (phInv x k) (ev0 (x k))) (ev1 (x k)) = phInv x (k + 1) := by
  rcases hxk : x k with ⟨p, v | w⟩
  · have he := wf_seq_inl wf hxk
    funext q
    by_cases hq : q = p
    · subst hq
      have := @cnt_succ_eq _ _ _ x k; rw [hxk] at this
      simp [ev0, ev1, phInv, this, he, Nat.even_add_one]
    · have := @cnt_succ_ne _ _ _ x k q (by rw [hxk]; exact Ne.symm hq)
      simp only [ev0, ev1]
      rw [phStep_of_ne (by simpa using hq), phStep_of_ne (by simpa using hq)]
      simp [phInv, this]
  · have he := wf_seq_inr wf hxk
    funext q
    by_cases hq : q = p
    · subst hq
      have := @cnt_succ_eq _ _ _ x k; rw [hxk] at this
      simp [ev0, ev1, phInv, this, he, Nat.even_add_one]
    · have := @cnt_succ_ne _ _ _ x k q (by rw [hxk]; exact Ne.symm hq)
      simp only [ev0, ev1]
      rw [phStep_of_ne (by simpa using hq), phStep_of_ne (by simpa using hq)]
      simp [phInv, this]

lemma phs_canon {x : Word I O} (wf : WF x) : ∀ k, phs (canon x) (2 * k) = phInv x k
  | 0 => by funext p; simp [phs, phInv, cnt]
  | k + 1 => by
    have h1 : phs (canon x) (2 * (k + 1)) =
        phStep (phStep (phs (canon x) (2 * k)) (canon x (2 * k))) (canon x (2 * k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; rfl
    rw [h1, phs_canon wf k, canon_even, canon_odd, phInv_succ wf]

lemma enabled_seg {x : Word I O} (wf : WF x) (k : ℕ) :
    Enabled (phInv x k) (ev0 (x k)) ∧
      Enabled (phStep (phInv x k) (ev0 (x k))) (ev1 (x k)) := by
  rcases hxk : x k with ⟨p, v | w⟩
  · have he := wf_seq_inl wf hxk
    simp [ev0, ev1, phInv, he]
  · have he := wf_seq_inr wf hxk
    simp [ev0, ev1, phInv, he]

lemma cnt_eq_of_no {x : Word I O} {p : Fin n} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ m, a ≤ m → m < b → (x m).1 ≠ p) : cnt x p b = cnt x p a := by
  induction hab with
  | refl => rfl
  | step hle ih =>
    rw [cnt_succ, if_neg (h _ hle (Nat.lt_succ_self _)), ih (fun m h1 h2 => h m h1 (by omega))]
    rfl

/-- In a well-formed word, every process has infinitely many responses. -/
lemma WF.exists_res {x : Word I O} (wf : WF x) (p : Fin n) (N : ℕ) :
    ∃ m, N ≤ m ∧ ∃ w, x m = ⟨p, .inr w⟩ := by
  obtain ⟨m₁, hm₁, hp₁⟩ := wf.reliable p N
  have key : ∀ m, (x m).1 = p → ¬ Even (cnt x p m) → ∃ w, x m = ⟨p, .inr w⟩ := by
    intro m hm hodd
    rcases hxm : x m with ⟨q, v | w⟩
    · rw [hxm] at hm; simp at hm; subst hm; exact absurd (wf_seq_inl wf hxm) hodd
    · rw [hxm] at hm; simp at hm; subst hm; exact ⟨w, rfl⟩
  by_cases hodd : Even (cnt x p m₁)
  · have hex : ∃ m, m₁ + 1 ≤ m ∧ (x m).1 = p := wf.reliable p (m₁ + 1)
    classical
    let m₂ := Nat.find hex
    have hm₂ : m₁ + 1 ≤ m₂ ∧ (x m₂).1 = p := Nat.find_spec hex
    have hmin : ∀ m, m₁ + 1 ≤ m → m < m₂ → (x m).1 ≠ p := fun m h1 h2 h3 =>
      Nat.find_min hex h2 ⟨h1, h3⟩
    have hc : cnt x p m₂ = cnt x p m₁ + 1 := by
      rw [cnt_eq_of_no hm₂.1 hmin, cnt_succ, if_pos hp₁]
    refine ⟨m₂, by omega, key m₂ hm₂.2 ?_⟩
    rw [hc, Nat.even_add_one]; exact not_not.2 hodd
  · exact ⟨m₁, hm₁, key m₁ hp₁ hodd⟩

/-- **Claim 3.1**: the canonical schedule is a fair failure-free execution. -/
theorem isExec_canon {x : Word I O} (wf : WF x) : IsExec (canon x) where
  valid t := by
    obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
    · rw [phs_canon wf, canon_even]; exact (enabled_seg wf k).1
    · have : phs (canon x) (2 * k + 1) = phStep (phs (canon x) (2 * k)) (canon x (2 * k)) := rfl
      rw [this, phs_canon wf, canon_even, canon_odd]; exact (enabled_seg wf k).2
  fair p N := by
    obtain ⟨m, hm, w, hw⟩ := wf.exists_res p N
    exact ⟨2 * m + 1, by omega, w, by rw [canon_odd, hw]; rfl⟩

/-- Position of the send/receive event of the `k`-th symbol in the canonical execution. -/
def ioPos (x : Word I O) (k : ℕ) : ℕ := 2 * k + if (x k).2.isLeft then 1 else 0

lemma ioPos_lt (x : Word I O) (k : ℕ) : 2 * k ≤ ioPos x k ∧ ioPos x k < 2 * k + 2 := by
  unfold ioPos; split_ifs <;> omega

lemma sym_ev0 (a : Sym I O) : (ev0 a).sym = if a.2.isLeft then none else some a := by
  rcases a with ⟨p, v | w⟩ <;> rfl

lemma sym_ev1 (a : Sym I O) : (ev1 a).sym = if a.2.isLeft then some a else none := by
  rcases a with ⟨p, v | w⟩ <;> rfl

lemma canon_ioPos (x : Word I O) (k : ℕ) : (canon x (ioPos x k)).sym = some (x k) := by
  unfold ioPos
  split_ifs with h
  · rw [canon_odd, sym_ev1, if_pos h]
  · rw [add_zero, canon_even, sym_ev0, if_neg h]

lemma canon_sym_isSome {x : Word I O} {t : ℕ} (h : (canon x t).sym.isSome) :
    ioPos x (t / 2) = t := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t = 2 * k ∨ t = 2 * k + 1 := ⟨t / 2, by omega⟩
  · rw [canon_even, sym_ev0] at h
    have hk : 2 * k / 2 = k := by omega
    split_ifs at h with h'
    · simp at h
    · rw [hk]; simp [ioPos, h']
  · rw [canon_odd, sym_ev1] at h
    have hk : (2 * k + 1) / 2 = k := by omega
    split_ifs at h with h'
    · rw [hk]; simp [ioPos, h']
    · simp at h

/-- **Claim 3.1**: the input of the canonical execution is `x`. -/
theorem hasInput_canon (x : Word I O) : HasInput (canon x) x := by
  refine ⟨ioPos x, strictMono_nat_of_lt_succ fun k => ?_, fun t ht => ⟨t / 2, canon_sym_isSome ht⟩,
    canon_ioPos x⟩
  have h1 := ioPos_lt x k; have h2 := ioPos_lt x (k + 1); omega

/-! ### The swap variant -/

/-- Four events indexed by `0, 1, 2, 3`. -/
def pick4 (e₀ e₁ e₂ e₃ : Ev I O) : ℕ → Ev I O
  | 0 => e₀
  | 1 => e₁
  | 2 => e₂
  | _ => e₃

/-- The reordered segments of two consecutive symbols `a`, `b` (of different processes): their
send/receive events are adjacent, at offsets `ioOff a b` and `ioOff a b + 1`. -/
def varEv : Sym I O → Sym I O → ℕ → Ev I O
  | ⟨p, .inl v⟩, ⟨q, .inl v'⟩ => pick4 (.pre p v) (.pre q v') (.send p v) (.send q v')
  | ⟨p, .inl v⟩, ⟨q, .inr w'⟩ => pick4 (.pre p v) (.send p v) (.recv q w') (.post q w')
  | ⟨p, .inr w⟩, ⟨q, .inl v'⟩ => pick4 (.pre q v') (.recv p w) (.send q v') (.post p w)
  | ⟨p, .inr w⟩, ⟨q, .inr w'⟩ => pick4 (.recv p w) (.recv q w') (.post p w) (.post q w')

/-- Offset of the first of the two adjacent send/receive events in `varEv`. -/
def ioOff : Sym I O → Sym I O → ℕ
  | ⟨_, .inl _⟩, ⟨_, .inl _⟩ => 2
  | ⟨_, .inl _⟩, ⟨_, .inr _⟩ => 1
  | ⟨_, .inr _⟩, ⟨_, .inl _⟩ => 1
  | ⟨_, .inr _⟩, ⟨_, .inr _⟩ => 0

lemma ioOff_le (a b : Sym I O) : ioOff a b ≤ 2 := by
  rcases a with ⟨p, v | w⟩ <;> rcases b with ⟨q, v' | w'⟩ <;> simp [ioOff]

lemma varEv_ioOff (a b : Sym I O) : (varEv a b (ioOff a b)).sym = some a ∧
    (varEv a b (ioOff a b + 1)).sym = some b := by
  rcases a with ⟨p, v | w⟩ <;> rcases b with ⟨q, v' | w'⟩ <;>
    simp [varEv, ioOff, pick4, Ev.sym]

lemma varEv_proc (a b : Sym I O) : (varEv a b (ioOff a b)).proc = a.1 ∧
    (varEv a b (ioOff a b + 1)).proc = b.1 := by
  rcases a with ⟨p, v | w⟩ <;> rcases b with ⟨q, v' | w'⟩ <;>
    simp [varEv, ioOff, pick4, Ev.proc]

lemma varEv_sym {a b : Sym I O} {j : ℕ} (hj : j < 4) (h : (varEv a b j).sym.isSome) :
    j = ioOff a b ∨ j = ioOff a b + 1 := by
  rcases a with ⟨p, v | w⟩ <;> rcases b with ⟨q, v' | w'⟩ <;>
    interval_cases j <;> simp_all [varEv, ioOff, pick4, Ev.sym]

/-- The execution `canon x` with the segments of the symbols `k` and `k + 1` reordered. -/
def vari (x : Word I O) (k : ℕ) (t : ℕ) : Ev I O :=
  if 2 * k ≤ t ∧ t < 2 * k + 4 then varEv (x k) (x (k + 1)) (t - 2 * k) else canon x t

lemma vari_in (x : Word I O) (k j : ℕ) (hj : j < 4) :
    vari x k (2 * k + j) = varEv (x k) (x (k + 1)) j := by
  simp [vari, hj]

lemma vari_out (x : Word I O) (k t : ℕ) (ht : ¬ (2 * k ≤ t ∧ t < 2 * k + 4)) :
    vari x k t = canon x t := by
  simp [vari, ht]

/-- The four reordered events are enabled and lead to the same program counters as the
canonical execution. -/
lemma vari_seg {x : Word I O} (wf : WF x) {k : ℕ} (hk : (x k).1 ≠ (x (k + 1)).1) :
    (∀ j < 4, Enabled (phs (vari x k) (2 * k + j)) (vari x k (2 * k + j))) ∧
      phs (vari x k) (2 * k + 4) = phInv x (k + 2) := by
  have h0 : phs (vari x k) (2 * k) = phInv x k := by
    rw [phs_congr (s' := canon x) (T := 2 * k) (fun t ht => vari_out x k t (by omega)) _ le_rfl,
      phs_canon wf]
  have hs1 : phs (vari x k) (2 * k + 1) = phStep (phs (vari x k) (2 * k)) (vari x k (2 * k)) := rfl
  have hs2 : phs (vari x k) (2 * k + 2) =
    phStep (phs (vari x k) (2 * k + 1)) (vari x k (2 * k + 1)) := rfl
  have hs3 : phs (vari x k) (2 * k + 3) =
    phStep (phs (vari x k) (2 * k + 2)) (vari x k (2 * k + 2)) := rfl
  have hs4 : phs (vari x k) (2 * k + 4) =
    phStep (phs (vari x k) (2 * k + 3)) (vari x k (2 * k + 3)) := rfl
  have e0 : vari x k (2 * k) = varEv (x k) (x (k + 1)) 0 := by
    simpa using vari_in x k 0 (by norm_num)
  have e1 := vari_in x k 1 (by norm_num)
  have e2 := vari_in x k 2 (by norm_num)
  have e3 := vari_in x k 3 (by norm_num)
  have hc1 := @cnt_succ_eq _ _ _ x k
  have hc2 : cnt x (x (k + 1)).1 (k + 2) = cnt x (x (k + 1)).1 (k + 1) + 1 :=
    @cnt_succ_eq _ _ _ x (k + 1)
  have hn1 : ∀ q, (x k).1 ≠ q → cnt x q (k + 1) = cnt x q k := fun q h => cnt_succ_ne h
  have hn2 : ∀ q, (x (k + 1)).1 ≠ q → cnt x q (k + 2) = cnt x q (k + 1) :=
    fun q h => cnt_succ_ne h
  have hq := hn1 _ hk
  rcases hxk : x k with ⟨p, v | w⟩ <;> rcases hxk1 : x (k + 1) with ⟨q, v' | w'⟩ <;>
    simp only [hxk, hxk1] at e0 e1 e2 e3 hc1 hc2 hn1 hn2 hk hq <;>
  · first | have ha := wf_seq_inl wf hxk | have ha := wf_seq_inr wf hxk
    first | have hb := wf_seq_inl wf hxk1 | have hb := wf_seq_inr wf hxk1
    rw [hq] at hb
    refine ⟨fun j hj => ?_, ?_⟩
    · interval_cases j
      · rw [add_zero, h0, e0]
        simp [varEv, pick4, phInv, ha, hb]
      · rw [hs1, h0, e0, e1]
        simp [varEv, pick4, phInv, ha, hb, hk, Ne.symm hk, phStep_of_ne]
      · rw [hs2, hs1, h0, e0, e1, e2]
        simp [varEv, pick4, phInv, ha, hb, hk, Ne.symm hk, phStep_of_ne]
      · rw [hs3, hs2, hs1, h0, e0, e1, e2, e3]
        simp [varEv, pick4, phInv, ha, hb, hk, Ne.symm hk, phStep_of_ne]
    · rw [hs4, hs3, hs2, hs1, h0, e0, e1, e2, e3]; funext r
      by_cases hr : r = p
      · subst hr
        simp [varEv, pick4, phInv, hk, hc1, hn2 _ (Ne.symm hk), Nat.even_add_one, ha,
          phStep_of_ne, Ne.symm hk]
      by_cases hr' : r = q
      · subst hr'
        simp [varEv, pick4, phInv, hk, hc2, Nat.even_add_one, hb, hq, phStep_of_ne, Ne.symm hk]
      · simp [varEv, pick4, phInv, hr, hr', hn1 r (Ne.symm hr), hn2 r (Ne.symm hr'),
          phStep_of_ne]

end Podc2025.LanguageDecidability
