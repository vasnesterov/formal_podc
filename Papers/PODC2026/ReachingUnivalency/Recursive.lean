import Papers.PODC2026.ReachingUnivalency.Corrected

/-!
# Reaching Univalency — the recursive protocol (Fig. 3) and Theorem 1

The recursion of ε-RPK: on `n > 2` processors, one level of `RPK.lean` whose committee instances
are themselves executions of the protocol on the committees (re-indexed by `Fin |C r|`); on
`n ≤ 2` processors a base protocol `P` (everybody adopts the input of processor `0`; with
`f < n(1/3 - ε) < 1` there are no faults there).

`Outcome T1 smp n F out` says that `out : inputs → outputs` is the input/output behaviour of an
execution of the recursive protocol (step-1 threshold `T1`, sampling choice `smp m` on `m`
processors) on `n` processors with Byzantine set `F`, for *some* behaviour of the Byzantine
processors at every level of the recursion. The Byzantine behaviour inside a committee may depend
on everything (we allow a different committee execution for every value vector).

* `outcome_epsBA` — **Theorem 1 (corrected protocol), correctness**: with step-1 threshold
  `2/3 - ε/4` and samplings that are `(δ, γ m)`-good at every size `m` (`δ ≤ ε/8`, `60 γ < ε`),
  every execution with `f < n(1/3 - ε)` solves ε-BA.
* `outcome_exists` — every size and Byzantine set has executions (non-vacuity).
* `msgs_le` — the message count recursion `M(n) = 6kn + M(⌈n/2⌉) + M(⌊n/2⌋)` gives
  `M(n) ≤ 6kn·⌈log₂ n⌉ + n`, i.e. `O(n log n)` messages of `O(1)` bits for fixed `ε`.
-/

namespace ReachingUnivalency.RPK

open Finset

/-- Committees of the recursion on `n` processors: the first `⌈n/2⌉` processors and the rest. -/
def comms (n : ℕ) : Fin 2 → Finset (Fin n) := fun r =>
  if r = 0 then univ.filter fun i => i.val < (n + 1) / 2 else univ.filter fun i => ¬ i.val < (n + 1) / 2

/-- Re-indexing of committee `r` by `Fin |C r|`. -/
def emb (n : ℕ) (r : Fin 2) (i : Fin (comms n r).card) : Fin n := (comms n r).orderEmbOfFin rfl i

lemma emb_mem {n : ℕ} {r : Fin 2} (i : Fin (comms n r).card) : emb n r i ∈ comms n r :=
  orderEmbOfFin_mem _ _ _

lemma emb_injective (n : ℕ) (r : Fin 2) : Function.Injective (emb n r) :=
  ((comms n r).orderEmbOfFin rfl).injective

lemma exists_emb {n : ℕ} {r : Fin 2} {p : Fin n} (hp : p ∈ comms n r) : ∃ i, emb n r i = p := by
  have : p ∈ Set.range ((comms n r).orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hp
  exact this

lemma comms_split (n : ℕ) : CommitteeSplit (comms n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [comms, Fin.isValue, ↓reduceIte, one_ne_zero]
    rw [disjoint_filter]; intro _ _ h1 h2; exact h2 h1
  · simp only [comms, Fin.isValue, ↓reduceIte, one_ne_zero]
    exact filter_union_filter_not_eq _ _
  all_goals
    simp only [comms, Fin.isValue, ↓reduceIte, one_ne_zero]
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), Fin.card_filter_val_lt, card_univ,
      Fintype.card_fin]
    omega

lemma card_comms (n : ℕ) (r : Fin 2) : (comms n r).card = if r = 0 then (n + 1) / 2 else n / 2 := by
  fin_cases r
  · simp only [comms, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.card_filter_val_lt]; omega
  · simp only [comms, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    rw [filter_not, card_sdiff_of_subset (filter_subset _ _), Fin.card_filter_val_lt, card_univ,
      Fintype.card_fin]
    omega

/-- `e : Fin m → Fin n` re-indexes the committee `C`: it is injective with range `C`. -/
def IsIndexing {n m : ℕ} (C : Finset (Fin n)) (e : Fin m → Fin n) : Prop :=
  Function.Injective e ∧ ∀ p, p ∈ C ↔ ∃ i, e i = p

lemma emb_isIndexing (n : ℕ) (r : Fin 2) : IsIndexing (comms n r) (emb n r) :=
  ⟨emb_injective n r, fun _ => ⟨exists_emb, by rintro ⟨i, rfl⟩; exact emb_mem i⟩⟩

/-- Byzantine members of a committee, re-indexed by `e`. -/
def subF {n m : ℕ} (e : Fin m → Fin n) (F : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter fun i => e i ∈ F

lemma card_subF {n m : ℕ} {C : Finset (Fin n)} {e : Fin m → Fin n} (he : IsIndexing C e)
    (F : Finset (Fin n)) : (subF e F).card = (C ∩ F).card := by
  rw [subF, ← card_map ⟨e, he.1⟩]
  congr 1
  ext p
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_inter]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨(he.2 _).mpr ⟨i, rfl⟩, hi⟩
  · rintro ⟨hp, hpF⟩
    obtain ⟨i, rfl⟩ := (he.2 p).mp hp
    exact ⟨i, hpF, rfl⟩

lemma card_eq_of_isIndexing {n m : ℕ} {C : Finset (Fin n)} {e : Fin m → Fin n}
    (he : IsIndexing C e) : m = C.card := by
  have := card_subF he C
  rw [inter_self] at this
  rw [← this, subF, filter_true_of_mem fun i _ => (he.2 _).mpr ⟨i, rfl⟩, card_univ,
    Fintype.card_fin]

/-- ε-BA of a committee execution, transported back to the committee inside `Fin n`. -/
lemma epsBAOn_of_sub {n m : ℕ} {C : Finset (Fin n)} {e : Fin m → Fin n} (he : IsIndexing C e)
    {ε : ℚ} {F : Finset (Fin n)} {vals out : Fin n → Bool}
    {o : Fin m → Bool} (h : EpsBA ε (subF e F) (vals ∘ e) o)
    (hout : ∀ i, out (e i) = o i) : EpsBAOn C ε F vals out := by
  obtain ⟨X, v, hX, hXc, hagr, hval⟩ := h
  have hinj := he.1
  have hm := card_eq_of_isIndexing he
  refine ⟨X.map ⟨e, hinj⟩, v, ?_, ?_, ?_, fun x hx => hval x ?_⟩
  · intro p hp
    simp only [mem_map, Function.Embedding.coeFn_mk] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    have := hX hi
    simp only [mem_sdiff, mem_univ, true_and, subF, mem_filter] at this
    exact mem_sdiff.mpr ⟨(he.2 _).mpr ⟨i, rfl⟩, this⟩
  · rw [card_map]; simpa [hm] using hXc
  · intro p hp hpX
    obtain ⟨i, rfl⟩ := (he.2 p).mp (mem_sdiff.mp hp).1
    rw [hout]
    refine hagr i (by simp [subF, (mem_sdiff.mp hp).2]) fun hi => hpX ?_
    exact mem_map.mpr ⟨i, hi, rfl⟩
  · have e' : (((univ \ subF e F).filter fun i => (vals ∘ e) i ≠ x).map
        ⟨e, hinj⟩) = (C \ F).filter fun p => vals p ≠ x := by
      ext p
      simp only [mem_map, mem_filter, mem_sdiff, mem_univ, true_and, subF,
        Function.comp_apply, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨i, ⟨hi, hv⟩, rfl⟩; exact ⟨⟨(he.2 _).mpr ⟨i, rfl⟩, hi⟩, hv⟩
      · rintro ⟨⟨hp, hpF⟩, hv⟩
        obtain ⟨i, rfl⟩ := (he.2 p).mp hp
        exact ⟨i, ⟨hpF, hv⟩, rfl⟩
    rw [← e', card_map] at hx
    simpa [hm] using hx

variable (T1 : ℚ) {k : ℕ} (smp : (m : ℕ) → Sampling m k)

/-- Input/output behaviours of executions of the recursive protocol. -/
inductive Outcome : (n : ℕ) → Finset (Fin n) → ((Fin n → Bool) → Fin n → Bool) → Prop
  /-- Base protocol on `n ≤ 2` processors: without faults everybody outputs processor `0`'s
  input; with faults (never within the fault bound) anything. -/
  | base {n : ℕ} {F : Finset (Fin n)} {out : (Fin n → Bool) → Fin n → Bool} :
      n ≤ 2 → (F = ∅ → ∀ (h : 0 < n) inp p, out inp p = inp ⟨0, h⟩) → Outcome n F out
  /-- One level of ε-RPK whose committee instances are executions of the protocol on the
  committees, re-indexed by `e r : Fin (m r) → Fin n` (possibly a different execution for every
  vector of values). -/
  | step {n : ℕ} (adv : Adversary n) (m : Fin 2 → ℕ) (e : (r : Fin 2) → Fin (m r) → Fin n)
      (o : (r : Fin 2) → (Fin n → Bool) → (Fin (m r) → Bool) → Fin (m r) → Bool) :
      2 < n → (∀ r, IsIndexing (comms n r) (e r)) →
      (∀ r vals, Outcome (m r) (subF (e r) adv.F) (o r vals)) →
      (∀ r vals i, adv.comm r vals (e r i) = o r vals (vals ∘ e r) i) →
      Outcome n adv.F (output T1 (smp n) adv)

/-- **Theorem 1 (corrected protocol), correctness.** Let `ε ∈ (0, 1/3)`, `δ ≤ ε/8`, `60γ < ε`,
and let the sampling choice on every size `m > 2` be `(δ, γm)`-good. Then every
execution of the recursive ε-RPK with step-1 threshold `2/3 - ε/4` on `n ≥ 1` processors with
`f < n(1/3 - ε)` Byzantine processors solves ε-BA. -/
theorem outcome_epsBA {ε δ γ : ℚ} (hε : 0 < ε) (hε3 : ε < 1/3) (hk : 0 < k) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ ε/8) (hγε : 60 * γ < ε)
    (hsmp : ∀ m : ℕ, 2 < m → SamplingGood δ (γ * m) (smp m) (comms m))
    {n : ℕ} {F : Finset (Fin n)} {out : (Fin n → Bool) → Fin n → Bool}
    (h : Outcome (T1c ε) smp n F out) (hn : 0 < n) (hF : ((F.card : ℕ) : ℚ) < n * (1/3 - ε))
    (inp : Fin n → Bool) : EpsBA ε F inp (out inp) := by
  induction h with
  | @base n F out hn2 hbase =>
    -- no faults: `f < n(1/3 - ε) ≤ 2/3`
    have hF0 : F = ∅ := by
      rw [← card_eq_zero]
      have : (n : ℚ) ≤ 2 := by exact_mod_cast hn2
      have : ((F.card : ℕ) : ℚ) < 1 := by nlinarith
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    subst hF0
    have hb := hbase rfl hn inp
    have hnq : (0 : ℚ) < n := by exact_mod_cast hn
    have hnε : (0 : ℚ) < n * ε := mul_pos hnq hε
    refine ⟨∅, inp ⟨0, hn⟩, by simp, by simpa using hnε, fun p _ _ => hb p, fun x hx => ?_⟩
    by_contra hne
    have hmem : (⟨0, hn⟩ : Fin n) ∈ (univ \ (∅ : Finset (Fin n))).filter fun p => inp p ≠ x := by
      simp [hne]
    have h1 : (1 : ℚ) ≤ (((univ \ ∅).filter fun p => inp p ≠ x).card : ℕ) := by
      exact_mod_cast card_pos.mpr ⟨_, hmem⟩
    have : (n : ℚ) ≤ 2 := by exact_mod_cast hn2
    simp only [card_univ, Fintype.card_fin] at hx
    nlinarith
  | @step n adv m e o hn2 he _ hcomm ih =>
    have hsplit := comms_split n
    have hcard : ∀ r, (n : ℚ) / 3 ≤ (comms n r).card := by
      intro r
      rw [card_comms]
      have h3 : 3 ≤ n := hn2
      split_ifs
      · have : n ≤ 3 * ((n + 1) / 2) := by omega
        have : (n : ℚ) ≤ 3 * (((n + 1) / 2 : ℕ) : ℚ) := by exact_mod_cast this
        linarith
      · have : n ≤ 3 * (n / 2) := by omega
        have : (n : ℚ) ≤ 3 * ((n / 2 : ℕ) : ℚ) := by exact_mod_cast this
        linarith
    have hnq : (0 : ℚ) < n := by exact_mod_cast hn
    refine lemma6_corrected_sampling (δ := δ) (M := γ * n) hk hn hε hε3 hδ0 hδ hF hsplit
      (fun r => ?_) (by nlinarith) (fun r vals hb => ?_) (hsmp n hn2) inp
    · have := hcard r
      nlinarith
    · -- the committee instance is an execution on fewer processors within its fault bound
      have hm := card_eq_of_isIndexing (he r)
      have hpos : 0 < m r := by
        have := hcard r
        have : (0 : ℚ) < (comms n r).card := by linarith
        rw [hm]; exact_mod_cast this
      have hb' : (((subF (e r) adv.F).card : ℕ) : ℚ) < (m r : ℕ) * (1/3 - ε) := by
        rw [card_subF (he r), hm]; exact hb
      exact epsBAOn_of_sub (he r) (ih r vals hpos hb' (vals ∘ e r)) (hcomm r vals)

/-- **Non-vacuity**: for every size and every Byzantine set the recursive protocol has executions
(e.g. Byzantine processors stay silent at every level). -/
theorem outcome_exists (n : ℕ) (F : Finset (Fin n)) : ∃ out, Outcome T1 smp n F out := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ 2
    · refine ⟨fun inp _ => if h : 0 < n then inp ⟨0, h⟩ else false, Outcome.base hn ?_⟩
      intro _ h inp p
      simp [h]
    · push Not at hn
      have hlt : ∀ r, (comms n r).card < n := by
        intro r; rw [card_comms]; split_ifs <;> omega
      choose o ho using fun r : Fin 2 => ih _ (hlt r) (subF (emb n r) F)
      classical
      let adv : Adversary n :=
        { F := F, byzVal := fun _ _ _ => none, byzResp := fun _ _ _ => none,
          byzComm := fun _ _ _ => none, tie := fun _ _ => false,
          comm := fun r vals q =>
            if h : ∃ i, emb n r i = q then o r (vals ∘ emb n r) h.choose else false }
      refine ⟨_, Outcome.step (n := n) adv (fun r => (comms n r).card) (emb n) (fun r _ => o r) hn
        (emb_isIndexing n) (fun r _ => ho r) ?_⟩
      intro r vals i
      have h : ∃ j, emb n r j = emb n r i := ⟨i, rfl⟩
      simp only [adv, h, ↓reduceDIte]
      rw [emb_injective n r h.choose_spec]

/-- Number of messages of the recursive protocol with `k` samples: each of the 6 sampling steps
of a level costs one message per sample (`6kn`), plus the two recursive calls; the base protocol
on `n ≤ 2` processors uses at most `n` messages. Each message carries a value in `{0, 1, ⊥}`. -/
def msgs (k : ℕ) (n : ℕ) : ℕ :=
  if n ≤ 2 then n else 6 * k * n + msgs k ((n + 1) / 2) + msgs k (n / 2)
termination_by n
decreasing_by all_goals omega

/-- **Complexity of Theorem 1**: `M(n) ≤ 6kn⌈log₂ n⌉ + n`, i.e. `O(n log n)` for fixed `ε`. -/
theorem msgs_le (k n : ℕ) : msgs k n ≤ 6 * k * n * Nat.clog 2 n + n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [msgs]
    split_ifs with hn
    · omega
    · push Not at hn
      have ha := ih ((n + 1) / 2) (by omega)
      have hb := ih (n / 2) (by omega)
      have hL : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := Nat.clog_of_two_le (by norm_num) (by omega)
      have hmono : Nat.clog 2 (n / 2) ≤ Nat.clog 2 ((n + 1) / 2) := Nat.clog_mono_right 2 (by omega)
      have hsum : (n + 1) / 2 + n / 2 = n := by omega
      set L := Nat.clog 2 ((n + 1) / 2)
      have hb' : msgs k (n / 2) ≤ 6 * k * (n / 2) * L + n / 2 :=
        hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hmono) _)
      rw [hL]
      calc 6 * k * n + msgs k ((n + 1) / 2) + msgs k (n / 2)
          ≤ 6 * k * n + (6 * k * ((n + 1) / 2) * L + (n + 1) / 2) +
            (6 * k * (n / 2) * L + n / 2) := by omega
        _ = 6 * k * n * (L + 1) + n := by
          have : 6 * k * ((n + 1) / 2) * L + 6 * k * (n / 2) * L = 6 * k * n * L := by
            rw [← Nat.add_mul, ← Nat.mul_add, hsum]
          rw [Nat.mul_add, mul_one]
          omega

end ReachingUnivalency.RPK
