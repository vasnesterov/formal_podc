import Papers.PODC2016.ComplexityHierarchy.BufferAlg
import Papers.PODC2016.ComplexityHierarchy.RacingCounters

/-!
# Consensus from `⌈n/ℓ⌉` ℓ-buffers (Theorem 6.3 of Ellen–Gelashvili–Shavit–Zhu, PODC 2016)

[EGSZ16] F. Ellen, R. Gelashvili, N. Shavit, L. Zhu, *A Complexity-Based Hierarchy for
Multiprocessor Synchronization*, PODC 2016 (arXiv 1607.06139), Section 6.1.

The processes are split into `k` groups of at most `ℓ` processes; group `g` uses the `ℓ`-buffer
`g` as a history object (Lemma 6.1, `BufferAlg.lean`) to which its members append their
increments. The racing-counters algorithm (Lemma 3.1) is run on the `m`-component counter whose
component `v` is the number of `v`-increments in all histories; a `scan` is an obstruction-free
*double collect* of the `k` histories.

The algorithm is flattened (CSLib has no composition theorem): `BufCons.alg` inlines the
history-object operations of Lemma 6.1 (`HistBuf.recon`) and the double collect into the
racing-counters algorithm. Helper definitions live in the namespace `BufCons`.

## Main results

* `BufCons.alg_safe`: agreement and (strong) validity in every finite execution (one-shot or not),
  for any grouping with at most `ℓ` processes per buffer and threshold `n ≥ |P|`.
* `BufCons.alg_obstructionFree`: CSLib's `Impl.ObstructionFree`.
* `theorem_6_3`: Theorem 6.3 — `⌈n/ℓ⌉` initially empty `ℓ`-buffers suffice for obstruction-free
  `m`-valued consensus among `n = |P|` processes (`ℓ ≥ 1`).

## Proof idea

The invariant `BufCons.CInv` combines Lemma 6.1's per-buffer invariant (`GoodW`, so that every
read reconstructs the full history, `recon_correct`) with the racing-counters agreement invariant,
stated for *virtual* phases `BufCons.vph`: a process in the middle of a double collect whose
previous collect `c₁` still matches everything read so far and all buffers not yet re-read
(`BufCons.Valid`) is treated as having already performed an atomic scan returning `c₁`
(linearized when the current collect started). Validity can only be lost (never regained), which
only removes processes from the decided/"bad" sets (`AgreeV.mono`); it is gained only when a
collect ends and the memory equals the new `c₁`, which is exactly an atomic scan
(`AgreeV.scan`).

## Deviations from the paper

* The paper composes Lemma 6.2 (single-writer registers from a history object), the
  double-collect snapshot and Lemma 3.1. We skip the register layer: a process appends its
  increments (tagged `(p, seq, v)`) to its group's history object and the counts are read off the
  histories; this is the same information as the paper's per-process registers.
* Double collect: the first "previous collect" is empty; after a failed comparison the current
  collect becomes the previous one.
* If a scan returns all-zero counts the process promotes its own input (instead of an arbitrary
  `argmax`); this simplifies the validity invariant and never happens (a process scans only after
  its own increment).
* As in `RacingCounters.lean`: ties in `argmax` broken arbitrarily, decision threshold `n = |P|`,
  re-invoking a decided process returns its decision.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

namespace BufCons

open Cslib.SharedMemory Impl HistBuf

/-! ### Virtual phases and the agreement invariant -/

section Agree

variable {m : ℕ} {P : Type} [Fintype P]

/-- Agreement invariant of the racing-counters algorithm, stated for *virtual* phases `ph`
(`RacingPhase`) and counter values `c`: either nobody has decided, or everybody who decided
decided `v`, and `c_v` leads every other component by more than the number of processes that may
still increment a component other than `v`. -/
def AgreeV (ph : P → RacingPhase m) (c : Fin m → ℕ) : Prop :=
  (∀ q w, ph q ≠ .done w) ∨ ∃ v, (∀ q w, ph q = .done w → w = v) ∧
    ∀ u, u ≠ v → c u + (Finset.univ.filter (fun q => badB v (ph q) = true)).card < c v

lemma AgreeV.mono {ph ph' : P → RacingPhase m} {c : Fin m → ℕ} (h : AgreeV ph c)
    (hdone : ∀ q w, ph' q = .done w → ph q = .done w)
    (hbad : ∀ q v, badB v (ph' q) = true → badB v (ph q) = true) : AgreeV ph' c := by
  rcases h with h | ⟨v, hv, hc⟩
  · exact Or.inl fun q w hq => h q w (hdone q w hq)
  · refine Or.inr ⟨v, fun q w hq => hv q w (hdone q w hq), fun u hu => ?_⟩
    have := hc u hu
    have : (Finset.univ.filter (fun q => badB v (ph' q) = true)).card ≤
        (Finset.univ.filter (fun q => badB v (ph q) = true)).card :=
      Finset.card_le_card fun q => by simpa using hbad q v
    omega

/-- A process about to promote `w` increments `c_w` and stops being able to increment. -/
lemma AgreeV.inc [DecidableEq P] {ph ph' : P → RacingPhase m} {c : Fin m → ℕ}
    (h : AgreeV ph c) {p : P} {w : Fin m} (hp : ph p = .promote w)
    (hp' : ∀ v, badB v (ph' p) = false) (hpd : ∀ w', ph' p ≠ .done w')
    (hdone : ∀ q, q ≠ p → ∀ w, ph' q = .done w → ph q = .done w)
    (hbad : ∀ q, q ≠ p → ∀ v, badB v (ph' q) = true → badB v (ph q) = true) :
    AgreeV ph' (Function.update c w (c w + 1)) := by
  rcases h with h | ⟨v, hv, hc⟩
  · refine Or.inl fun q w' hq => ?_
    by_cases hqp : q = p
    · subst hqp; exact hpd w' hq
    · exact h q w' (hdone q hqp w' hq)
  · refine Or.inr ⟨v, fun q w' hq => ?_, fun u hu => ?_⟩
    · by_cases hqp : q = p
      · subst hqp; exact absurd hq (hpd w')
      · exact hv q w' (hdone q hqp w' hq)
    · have hsub : Finset.univ.filter (fun q => badB v (ph' q) = true) ⊆
          (Finset.univ.filter (fun q => badB v (ph q) = true)).erase p := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        by_cases hqp : q = p
        · subst hqp; rw [hp' v] at hq; cases hq
        · simpa [hqp] using hbad q hqp v hq
      have hcard := Finset.card_le_card hsub
      have hc' := hc u hu
      by_cases hwv : w = v
      · subst hwv
        have : (Finset.univ.filter (fun q => badB w (ph' q) = true)).card ≤
            (Finset.univ.filter (fun q => badB w (ph q) = true)).card :=
          hcard.trans (Finset.card_erase_le)
        simp only [Function.update_self, Function.update_of_ne hu]
        omega
      · have hpmem : p ∈ Finset.univ.filter (fun q => badB v (ph q) = true) := by
          simp [hp, badB, hwv]
        rw [Finset.card_erase_of_mem hpmem] at hcard
        have hpos : 0 < (Finset.univ.filter (fun q => badB v (ph q) = true)).card :=
          Finset.card_pos.2 ⟨p, hpmem⟩
        rw [Function.update_of_ne (Ne.symm hwv)]
        by_cases huw : u = w
        · subst huw; simp only [Function.update_self]; omega
        · rw [Function.update_of_ne huw]; omega

variable [NeZero m]

/-- The value promoted after a scan with counts `c` (input `inp` if all counts are `0`). -/
noncomputable def pv (c : Fin m → ℕ) (inp : Fin m) : Fin m :=
  by classical exact if c = 0 then inp else argmax c

/-- The (virtual) phase after a scan with counts `c`. -/
noncomputable def scanRes (n : ℕ) (c : Fin m → ℕ) (inp : Fin m) : RacingPhase m :=
  if Lead n c (argmax c) then .done (argmax c) else .promote (pv c inp)

/-- A scan: a process in (virtual) phase `scan` moves to `scanRes n c inp` where `c` are the
current counts. -/
lemma AgreeV.scan [DecidableEq P] {ph ph' : P → RacingPhase m} {c : Fin m → ℕ} {n : ℕ}
    (h : AgreeV ph c) (hn : Fintype.card P ≤ n) {p : P} {inp : Fin m}
    (hp : ph p = .scan) (hp' : ph' p = scanRes n c inp)
    (hother : ∀ q, q ≠ p → ph' q = ph q) : AgreeV ph' c := by
  have hdone : ∀ q, q ≠ p → ∀ w, ph' q = .done w → ph q = .done w :=
    fun q hq w h => by rwa [hother q hq] at h
  rcases h with h | ⟨v, hv, hc⟩
  · unfold scanRes at hp'
    split_ifs at hp' with hL
    · refine Or.inr ⟨argmax c, fun q w hq => ?_, fun u hu => ?_⟩
      · by_cases hqp : q = p
        · subst hqp; rw [hp'] at hq; cases hq; rfl
        · exact absurd (hdone q hqp w hq) (h q w)
      · have hsub : Finset.univ.filter (fun q => badB (argmax c) (ph' q) = true) ⊆
            Finset.univ.erase p := by
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          rintro rfl; rw [hp'] at hq; simp [badB] at hq
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at h1
        have h2 := hL u hu
        have h3 : 0 < Fintype.card P := Fintype.card_pos_iff.2 ⟨p⟩
        omega
    · refine Or.inl fun q w hq => ?_
      by_cases hqp : q = p
      · subst hqp; rw [hp'] at hq; cases hq
      · exact h q w (hdone q hqp w hq)
  · have hmax : ∀ u, u ≠ v → c u < c v := fun u hu => by have := hc u hu; omega
    have ha : argmax c = v := argmax_eq hmax
    have hpv : pv c inp = v := by
      unfold pv
      split_ifs with h0
      · by_contra hne
        have := hmax inp hne
        simp [h0] at this
      · exact ha
    have hpv' : ph' p = .done v ∨ ph' p = .promote v := by
      rw [hp']; unfold scanRes; rw [ha, hpv]; split_ifs <;> simp
    refine Or.inr ⟨v, fun q w hq => ?_, fun u hu => ?_⟩
    · by_cases hqp : q = p
      · subst hqp; rcases hpv' with h' | h' <;> rw [h'] at hq <;> cases hq; rfl
      · exact hv q w (hdone q hqp w hq)
    · have hsub : Finset.univ.filter (fun q => badB v (ph' q) = true) ⊆
          Finset.univ.filter (fun q => badB v (ph q) = true) := by
        intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        by_cases hqp : q = p
        · subst hqp; rcases hpv' with h' | h' <;> rw [h'] at hq <;> simp [badB] at hq
        · rwa [hother q hqp] at hq
      have := Finset.card_le_card hsub
      have := hc u hu
      omega

end Agree

/-! ### The algorithm -/

section Alg

variable {P : Type} {m k : ℕ}

/-- Tagged increments `(process, sequence number, value)` stored in the histories. -/
abbrev CTag (P : Type) (m : ℕ) := Tag P (Fin m)

/-- Values written to the buffers. -/
abbrev CEntry (P : Type) (m : ℕ) := Entry P (Fin m)

/-- The base objects: `k` `ℓ`-buffers. -/
abbrev CB (ℓ : ℕ) (P : Type) (m k : ℕ) : Fin k → ObjSpec := fun _ => bufferSpec ℓ (CEntry P m)

/-- Program counter. -/
inductive CPh (P : Type) (m k : ℕ) where
  /-- Not invoked yet. -/
  | idle
  /-- About to promote `w`: read the own group's buffer (`get-history` of the `append`). -/
  | prom (w : Fin m)
  /-- About to promote `w`: write `(h, (p, seq, w))` to the own group's buffer. -/
  | promW (w : Fin m) (h : List (CTag P m))
  /-- Double collect: about to read buffer `i` of the current collect `acc`, the previous collect
  being `c₁`. -/
  | col (i : ℕ) (c₁ acc : Fin k → List (CTag P m))
  /-- Decided `w`. -/
  | done (w : Fin m)

/-- Local state. -/
structure CLoc (P : Type) (m k : ℕ) where
  /-- Program counter. -/
  ph : CPh P m k
  /-- Number of own appends (sequence number of the tags). -/
  seq : ℕ
  /-- The own input. -/
  inp : Fin m

/-- The empty collect. -/
def emp : Fin k → List (CTag P m) := fun _ => []

/-- Counts of a collect: `cnt c v` is the number of `v`-increments in all histories. -/
def cnt (c : Fin k → List (CTag P m)) (v : Fin m) : ℕ :=
  ∑ g, (c g).countP (fun t => decide (t.2.2 = v))

variable [NeZero m]

/-- The actual phase after a successful scan with counts `c`. -/
noncomputable def scanPh (n : ℕ) (c : Fin m → ℕ) (inp : Fin m) : CPh P m k :=
  if Lead n c (argmax c) then .done (argmax c) else .prom (pv c inp)

variable [DecidableEq P]

/-- The local state after reading `b` from buffer `i` during a collect. -/
noncomputable def colNext (ℓ n : ℕ) (i : ℕ) (hi : i < k) (c₁ acc : Fin k → List (CTag P m))
    (b : List (CEntry P m)) (l : CLoc P m k) : CLoc P m k :=
  let acc' := Function.update acc ⟨i, hi⟩ (recon ℓ b)
  if i + 1 < k then ⟨.col (i + 1) c₁ acc', l.seq, l.inp⟩
  else if acc' = c₁ then ⟨scanPh n (cnt c₁) l.inp, l.seq, l.inp⟩
  else ⟨.col 0 acc' emp, l.seq, l.inp⟩

/-- **The algorithm of Theorem 6.3**: racing counters over `k` `ℓ`-buffers, threshold `n`;
process `p` appends its increments to the history object in buffer `grp p`. -/
noncomputable def alg (ℓ n : ℕ) (grp : P → Fin k) :
    Impl (taskObj (Fin m) (Fin m)) (CB ℓ P m k) P (CLoc P m k) where
  memInit _ := []
  locInit _ := ⟨.idle, 0, default⟩
  invoke _ l o := match l.ph with
    | .idle => ⟨.prom o, l.seq, o⟩
    | _ => l
  act p l := match l.ph with
    | .idle => .ret (default : Fin m) l
    | .prom w => .access (grp p) .read (fun b => ⟨.promW w (recon ℓ b), l.seq, l.inp⟩)
    | .promW w h => .access (grp p) (.write (h, (p, l.seq, w)))
        (fun _ => ⟨.col 0 emp emp, l.seq + 1, l.inp⟩)
    | .col i c₁ acc => if hi : i < k then .access ⟨i, hi⟩ .read (fun b => colNext ℓ n i hi c₁ acc b l)
        else .ret (default : Fin m) l
    | .done w => .ret w l

end Alg

/-! ### Steps -/

section Steps

variable {P : Type} {m k : ℕ} [NeZero m] [DecidableEq P] {ℓ n : ℕ} {grp : P → Fin k}

/-- Configurations of `alg`. -/
abbrev CCfg (ℓ : ℕ) (P : Type) (m k : ℕ) [NeZero m] :=
    Config (taskObj (Fin m) (Fin m)) (CB ℓ P m k) P (CLoc P m k)

/-- Labels of `alg`. -/
abbrev CLbl (P : Type) (m : ℕ) [NeZero m] := Label P (taskObj (Fin m) (Fin m))

lemma step_prom {C : CCfg ℓ P m k} {p : P} {w : Fin m} (hp : C.pend p ≠ none)
    (hph : (C.loc p).ph = .prom w) :
    (alg ℓ n grp).step C (.tau p) = some ⟨Function.update C.loc p
      ⟨.promW w (recon ℓ (C.mem (grp p))), (C.loc p).seq, (C.loc p).inp⟩, C.pend, C.mem⟩ := by
  simp [Impl.step, hp, alg, hph]

lemma step_promW {C : CCfg ℓ P m k} {p : P} {w : Fin m} {h : List (CTag P m)}
    (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .promW w h) :
    (alg ℓ n grp).step C (.tau p) = some ⟨Function.update C.loc p
      ⟨.col 0 emp emp, (C.loc p).seq + 1, (C.loc p).inp⟩, C.pend,
      Function.update C.mem (grp p) (bufWrite ℓ (h, (p, (C.loc p).seq, w)) (C.mem (grp p)))⟩ := by
  simp [Impl.step, hp, alg, hph]

lemma step_col {C : CCfg ℓ P m k} {p : P} {i : ℕ} {c₁ acc : Fin k → List (CTag P m)}
    (hp : C.pend p ≠ none) (hph : (C.loc p).ph = .col i c₁ acc) (hi : i < k) :
    (alg ℓ n grp).step C (.tau p) = some ⟨Function.update C.loc p
      (colNext ℓ n i hi c₁ acc (C.mem ⟨i, hi⟩) (C.loc p)), C.pend, C.mem⟩ := by
  simp [Impl.step, hp, alg, hph, hi]

end Steps

/-! ### The invariant -/

section Inv

variable {P : Type} {m k : ℕ} [NeZero m] [DecidableEq P] {ℓ n : ℕ} {grp : P → Fin k}

/-- The current counts: number of `v`-increments in all (ghost) histories `W`. -/
def ctrW (W : Fin k → List (CEntry P m)) : Fin m → ℕ := cnt (fun g => (W g).map Prod.snd)

/-- The double collect of a process at index `i` (previous collect `c₁`, current partial collect
`acc`) is still *valid*: it has matched `c₁` so far and the buffers not yet read still hold `c₁`.
Then `c₁` is an atomic snapshot of all histories, taken when the current collect started. -/
def Valid (W : Fin k → List (CEntry P m)) (i : ℕ) (c₁ acc : Fin k → List (CTag P m)) : Prop :=
  (∀ g : Fin k, g.val < i → acc g = c₁ g) ∧ (∀ g : Fin k, i ≤ g.val → (W g).map Prod.snd = c₁ g)

open Classical in
/-- The *virtual* racing-counters phase of a process: a valid double collect counts as an atomic
scan already performed (linearized when the current collect started). -/
noncomputable def vph (n : ℕ) (W : Fin k → List (CEntry P m)) (l : CLoc P m k) : RacingPhase m :=
  match l.ph with
  | .idle => .idle
  | .prom w => .promote w
  | .promW w _ => .promote w
  | .col i c₁ acc => if Valid W i c₁ acc then scanRes n (cnt c₁) l.inp else .scan
  | .done w => .done w

variable [Fintype P]

/-- The members of group `g`. -/
def members (grp : P → Fin k) (g : Fin k) : Finset P := Finset.univ.filter (fun p => grp p = g)

/-- The invariant of `alg` (`W g`: all writes to buffer `g` so far, a ghost variable). -/
structure CInv (ℓ n : ℕ) (grp : P → Fin k) (α : List (CLbl P m)) (C : CCfg ℓ P m k)
    (W : Fin k → List (CEntry P m)) : Prop where
  good : ∀ g, GoodW (members grp g) Prod.fst (W g)
  mem : ∀ g, C.mem g = (W g).reverse.take ℓ
  seq : ∀ g, ∀ e ∈ W g, e.2.2.1 < (C.loc e.2.1).seq
  idle : ∀ q, (C.loc q).ph = .idle → opsOf α q = [] ∧ C.pend q = none
  inp : ∀ q, (C.loc q).ph ≠ .idle → HasInput α (C.loc q).inp
  ph_val : ∀ q w, ((C.loc q).ph = .prom w ∨ (∃ h, (C.loc q).ph = .promW w h) ∨
    (C.loc q).ph = .done w) → HasInput α w
  w_val : ∀ g, ∀ e ∈ W g, HasInput α e.2.2.2
  wr : ∀ q w h, (C.loc q).ph = .promW w h → h <+: (W (grp q)).map Prod.snd ∧
    ∀ j (hj : j < (W (grp q)).length), (W (grp q))[j].2.1 = q → j < h.length
  col : ∀ q i c₁ acc, (C.loc q).ph = .col i c₁ acc → i < k ∧
    ∀ g, c₁ g <+: (W g).map Prod.snd ∧ (g.val < i → acc g <+: (W g).map Prod.snd)
  resp : ∀ q (w : Fin m), w ∈ respsOf α q → (C.loc q).ph = .done w
  agree : AgreeV (fun q => vph n W (C.loc q)) (ctrW W)

end Inv

/-! ### Auxiliary lemmas -/

section Aux

variable {P : Type} {m k : ℕ} [NeZero m] [DecidableEq P] {ℓ n : ℕ} {grp : P → Fin k}

lemma cnt_append (c : Fin k → List (CTag P m)) (g : Fin k) (t : CTag P m) (v : Fin m) :
    cnt (Function.update c g (c g ++ [t])) v = cnt c v + if t.2.2 = v then 1 else 0 := by
  unfold cnt
  have : ∀ g', (Function.update c g (c g ++ [t]) g').countP (fun t => decide (t.2.2 = v)) =
      (c g').countP (fun t => decide (t.2.2 = v)) + if g' = g ∧ t.2.2 = v then 1 else 0 := by
    intro g'
    by_cases hg : g' = g
    · subst hg; simp [List.countP_append]
    · simp [hg]
  simp only [this, Finset.sum_add_distrib]
  congr 1
  by_cases ht : t.2.2 = v
  · simp [ht]
  · simp [ht]

lemma ctrW_append (W : Fin k → List (CEntry P m)) (g : Fin k) (e : CEntry P m) :
    ctrW (Function.update W g (W g ++ [e])) = Function.update (ctrW W) e.2.2.2 (ctrW W e.2.2.2 + 1) := by
  funext v
  have h1 : (fun g' => (Function.update W g (W g ++ [e]) g').map Prod.snd) =
      Function.update (fun g' => (W g').map Prod.snd) g ((W g).map Prod.snd ++ [e.2]) := by
    funext g'
    by_cases hg : g' = g
    · subst hg; simp
    · simp [Function.update_of_ne hg]
  unfold ctrW
  rw [h1, cnt_append (fun g' => (W g').map Prod.snd) g e.2 v]
  by_cases hv : v = e.2.2.2
  · subst hv; simp
  · rw [Function.update_of_ne hv]; simp [Ne.symm hv]

lemma exists_of_cnt_pos {c : Fin k → List (CTag P m)} {W : Fin k → List (CEntry P m)} {v : Fin m}
    (h : 0 < cnt c v) (hpre : ∀ g, c g <+: (W g).map Prod.snd) :
    ∃ g, ∃ e ∈ W g, e.2.2.2 = v := by
  unfold cnt at h
  obtain ⟨g, -, hg⟩ := Finset.exists_lt_of_sum_lt (by simpa using h :
    ∑ _i : Fin k, 0 < ∑ g, (c g).countP (fun t => decide (t.2.2 = v)))
  obtain ⟨t, ht, htv⟩ := List.countP_pos_iff.1 hg
  have := (hpre g).subset ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 this
  exact ⟨g, e, he, by simpa using htv⟩

lemma valid_step {W : Fin k → List (CEntry P m)} {i : ℕ} (hi : i < k)
    {c₁ acc : Fin k → List (CTag P m)} :
    Valid W (i + 1) c₁ (Function.update acc ⟨i, hi⟩ ((W ⟨i, hi⟩).map Prod.snd)) ↔
      Valid W i c₁ acc := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · have := h1 g (by omega)
      rwa [Function.update_of_ne (by intro h; subst h; simp at hg)] at this
    · rcases Nat.eq_or_lt_of_le hg with h | h
      · have := h1 g (by omega)
        have hgi : g = ⟨i, hi⟩ := Fin.ext h.symm
        subst hgi
        simpa using this
      · exact h2 g h
  · rintro ⟨h1, h2⟩
    refine ⟨fun g hg => ?_, fun g hg => h2 g (by omega)⟩
    by_cases hgi : g = ⟨i, hi⟩
    · subst hgi; simpa using h2 _ le_rfl
    · rw [Function.update_of_ne hgi]
      exact h1 g (by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hg with h | h
        · exact h
        · exact absurd (Fin.ext h) hgi)

lemma valid_last {W : Fin k → List (CEntry P m)} {i : ℕ} (hi : i < k) (hk : ¬ i + 1 < k)
    {c₁ acc : Fin k → List (CTag P m)} :
    Function.update acc ⟨i, hi⟩ ((W ⟨i, hi⟩).map Prod.snd) = c₁ ↔ Valid W i c₁ acc := by
  rw [← valid_step hi]
  constructor
  · intro h; rw [h]; exact ⟨fun _ _ => rfl, fun g hg => by have := g.isLt; omega⟩
  · rintro ⟨h1, -⟩; funext g; exact h1 g (by have := g.isLt; omega)

lemma valid_zero {W : Fin k → List (CEntry P m)} {c₁ acc : Fin k → List (CTag P m)} :
    Valid W 0 c₁ acc ↔ ∀ g, (W g).map Prod.snd = c₁ g :=
  ⟨fun h g => h.2 g (Nat.zero_le _), fun h => ⟨fun _ hg => absurd hg (Nat.not_lt_zero _),
    fun g _ => h g⟩⟩

/-- After an append to buffer `g`, a collect can only become invalid. -/
lemma valid_of_append {W : Fin k → List (CEntry P m)} {g : Fin k} {e : CEntry P m} {i : ℕ}
    {c₁ acc : Fin k → List (CTag P m)} (hpre : c₁ g <+: (W g).map Prod.snd)
    (h : Valid (Function.update W g (W g ++ [e])) i c₁ acc) : Valid W i c₁ acc := by
  refine ⟨h.1, fun g' hg' => ?_⟩
  have := h.2 g' hg'
  by_cases hgg : g' = g
  · subst hgg
    rw [Function.update_self] at this
    have := hpre.length_le
    rw [← h.2 g' hg'] at this
    simp at this
  · rwa [Function.update_of_ne hgg] at this

lemma vph_scanPh (W : Fin k → List (CEntry P m)) (c : Fin m → ℕ) (inp : Fin m) (s : ℕ)
    (inp' : Fin m) : vph n W ⟨scanPh (P := P) n c inp, s, inp'⟩ = scanRes n c inp := by
  unfold scanPh scanRes
  split_ifs <;> rfl

lemma vph_of_append (W : Fin k → List (CEntry P m)) (g : Fin k) (e : CEntry P m)
    (l : CLoc P m k)
    (hpre : ∀ i c₁ acc, l.ph = .col i c₁ acc → c₁ g <+: (W g).map Prod.snd) :
    vph n (Function.update W g (W g ++ [e])) l = vph n W l ∨
      vph n (Function.update W g (W g ++ [e])) l = .scan := by
  rcases l with ⟨ph, s, inp⟩
  cases ph with
  | col i c₁ acc =>
    simp only [vph]
    by_cases hv : Valid (Function.update W g (W g ++ [e])) i c₁ acc
    · left
      simp only [hv, valid_of_append (hpre i c₁ acc rfl) hv, ↓reduceIte]
    · right; simp only [hv, ↓reduceIte]
  | _ => left; rfl

end Aux

/-! ### Preservation of the invariant: invocations and responses -/

section PreserveInvRet

variable {P : Type} {m k : ℕ} [NeZero m] [DecidableEq P] [Fintype P] {ℓ n : ℕ} {grp : P → Fin k}
  {α : List (CLbl P m)} {C C' : CCfg ℓ P m k} {W : Fin k → List (CEntry P m)}

lemma hasInput_append_iff_of_ops {α β : List (CLbl P m)} (h : ∀ q, opsOf (α ++ β) q = opsOf α q)
    (w : Fin m) : HasInput (α ++ β) w ↔ HasInput α w := by
  simp only [HasInput, inputs, h]

lemma cinv_init : CInv ℓ n grp ([] : List (CLbl P m)) (alg ℓ n grp).initCfg
    (fun _ => ([] : List (CEntry P m))) where
  good _ := ⟨fun j hj => by simp at hj, fun j j' _ hj' => by simp at hj', by simp, by simp⟩
  mem _ := by simp [Impl.initCfg, alg]
  seq _ e he := by simp at he
  idle _ _ := ⟨rfl, rfl⟩
  inp q h := by simp [Impl.initCfg, alg] at h
  ph_val q w h := by simp [Impl.initCfg, alg] at h
  w_val _ e he := by simp at he
  wr q w h hq := by simp [Impl.initCfg, alg] at hq
  col q i c₁ acc hq := by simp [Impl.initCfg, alg] at hq
  resp q w hw := by cases hw
  agree := Or.inl fun q w => by simp [Impl.initCfg, alg, vph]

lemma cinv_inv (hI : CInv ℓ n grp α C W) {p : P} {o : Fin m}
    (h : (alg ℓ n grp).step C (.inv p o) = some C') : CInv ℓ n grp (α ++ [.inv p o]) C' W := by
  obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
  have hops : ∀ q, q ≠ p → opsOf (α ++ [.inv p o]) q = opsOf α q := by
    intro q hq; simp [Label.invOf, Ne.symm hq]
  have hresps : ∀ q, respsOf (α ++ [.inv p o]) q = respsOf α q := by intro q; simp [Label.retOf]
  have hin : ∀ w, HasInput α w → HasInput (α ++ [.inv p o]) w := fun w h => h.append _
  -- the new local state of `p`
  have key : ∀ q, (C'.loc q = C.loc q ∧ (q = p → (C.loc p).ph ≠ .idle)) ∨
      (q = p ∧ (C.loc p).ph = .idle ∧ C'.loc p = ⟨.prom o, (C.loc p).seq, o⟩) := by
    intro q
    by_cases hq : q = p
    · subst hq
      rw [hloc, Function.update_self]
      rcases hph : (C.loc q).ph with _ | w | ⟨w, hh⟩ | ⟨i, c₁, acc⟩ | w <;> simp [alg, hph]
    · left; rw [hloc, Function.update_of_ne hq]; exact ⟨rfl, fun h => absurd h hq⟩
  have hseq : ∀ q, (C'.loc q).seq = (C.loc q).seq := by
    intro q; rcases key q with ⟨h, -⟩ | ⟨rfl, -, h⟩ <;> rw [h]
  have hpin : (C.loc p).ph = .idle → HasInput (α ++ [.inv p o]) o := by
    intro hid
    refine ⟨p, ?_⟩
    simp only [inputs]
    rw [opsOf_append, (hI.idle p hid).1]
    simp [opsOf, Label.invOf]
    rfl
  have hvidle : ∀ (W : Fin k → List (CEntry P m)) (l : CLoc P m k), l.ph = .idle →
      vph n W l = .idle := by
    intro W l hl; simp [vph, hl]
  refine ⟨hI.good, fun g => by rw [hmem]; exact hI.mem g,
    fun g e he => by rw [hseq]; exact hI.seq g e he, ?_, ?_, ?_,
    fun g e he => hin _ (hI.w_val g e he), ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases key q with ⟨h, hne⟩ | ⟨rfl, -, h⟩
    · rw [h] at hq
      have hqp : q ≠ p := fun e => hne e (e ▸ hq)
      rw [hops q hqp, hpend, Function.update_of_ne hqp]
      exact hI.idle q hq
    · rw [h] at hq; cases hq
  · intro q hq
    rcases key q with ⟨h, -⟩ | ⟨rfl, hid, h⟩
    · rw [h] at hq ⊢; exact hin _ (hI.inp q hq)
    · rw [h]; exact hpin hid
  · intro q w hq
    rcases key q with ⟨h, -⟩ | ⟨rfl, hid, h⟩
    · rw [h] at hq; exact hin _ (hI.ph_val q w hq)
    · rw [h] at hq
      simp only [CPh.prom.injEq, reduceCtorEq, exists_false, or_false] at hq
      subst hq; exact hpin hid
  · intro q w hh hq
    rcases key q with ⟨h, -⟩ | ⟨rfl, -, h⟩
    · rw [h] at hq; exact hI.wr q w hh hq
    · rw [h] at hq; cases hq
  · intro q i c₁ acc hq
    rcases key q with ⟨h, -⟩ | ⟨rfl, -, h⟩
    · rw [h] at hq; exact hI.col q i c₁ acc hq
    · rw [h] at hq; cases hq
  · intro q w hw
    rw [hresps] at hw
    rcases key q with ⟨h, -⟩ | ⟨rfl, hid, -⟩
    · rw [h]; exact hI.resp q w hw
    · have := hI.resp q w hw; rw [hid] at this; cases this
  · refine hI.agree.mono (fun q w hq => ?_) (fun q v hq => ?_)
    · rcases key q with ⟨h, -⟩ | ⟨rfl, -, h⟩
      · simpa only [h] using hq
      · simp only [h, vph] at hq; cases hq
    · rcases key q with ⟨h, -⟩ | ⟨rfl, hid, h⟩
      · simpa only [h] using hq
      · simp only [hvidle _ _ hid]; rfl

lemma cinv_ret (hI : CInv ℓ n grp α C W) {p : P} {r : Fin m}
    (h : (alg ℓ n grp).step C (.ret p r) = some C') : CInv ℓ n grp (α ++ [.ret p r]) C' W := by
  obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
  have hdone : (C.loc p).ph = .done r ∧ l = C.loc p := by
    rcases hph : (C.loc p).ph with _ | w | ⟨w, hh⟩ | ⟨i, c₁, acc⟩ | w
    · exact absurd (hI.idle p hph).2 h0
    · simp [alg, hph] at hact
    · simp [alg, hph] at hact
    · have hi := (hI.col p i c₁ acc hph).1
      simp [alg, hph, hi] at hact
    · simp only [alg, hph] at hact
      injection hact with h1 h2
      exact ⟨by rw [h1], h2.symm⟩
  have hl : C'.loc = C.loc := by rw [hloc, hdone.2, Function.update_eq_self]
  have hops : ∀ q, opsOf (α ++ [.ret p r]) q = opsOf α q := by intro q; simp [opsOf, Label.invOf]
  have hin : ∀ w, HasInput (α ++ [.ret p r]) w ↔ HasInput α w :=
    hasInput_append_iff_of_ops hops
  refine ⟨hI.good, fun g => by rw [hmem]; exact hI.mem g, fun g e he => by
    rw [hl]; exact hI.seq g e he, fun q hq => ?_, fun q hq => ?_, fun q w hq => ?_,
    fun g e he => (hin _).2 (hI.w_val g e he), fun q w hh hq => ?_, fun q i c₁ acc hq => ?_,
    fun q w hw => ?_, ?_⟩
  · rw [hl] at hq
    refine ⟨by rw [hops]; exact (hI.idle q hq).1, ?_⟩
    by_cases hqp : q = p
    · subst hqp; rw [hdone.1] at hq; cases hq
    · rw [hpend, Function.update_of_ne hqp]; exact (hI.idle q hq).2
  · rw [hl] at hq ⊢; exact (hin _).2 (hI.inp q hq)
  · rw [hl] at hq; exact (hin _).2 (hI.ph_val q w hq)
  · rw [hl] at hq; exact hI.wr q w hh hq
  · rw [hl] at hq; exact hI.col q i c₁ acc hq
  · rw [hl]
    by_cases hqp : q = p
    · subst hqp
      rw [respsOf_append] at hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hI.resp q w hw
      · have hr : Label.retOf q (Label.ret q r : CLbl P m) = some r := by
          simp [Label.retOf]; rfl
        simp only [respsOf, List.filterMap_cons, hr, List.filterMap_nil] at hw
        rw [List.mem_singleton.1 hw]; exact hdone.1
    · have : respsOf (α ++ [.ret p r]) q = respsOf α q := by
        simp [respsOf, Label.retOf, Ne.symm hqp]
      rw [this] at hw; exact hI.resp q w hw
  · rw [hl]; exact hI.agree

end PreserveInvRet

/-! ### Preservation of the invariant: internal steps -/

section PreserveTau

variable {P : Type} {m k : ℕ} [NeZero m] [DecidableEq P] [Fintype P] {ℓ n : ℕ} {grp : P → Fin k}
  {α : List (CLbl P m)} {C : CCfg ℓ P m k} {W : Fin k → List (CEntry P m)}

lemma ops_tau (α : List (CLbl P m)) (p q : P) : opsOf (α ++ [.tau p]) q = opsOf α q := by
  simp [opsOf, Label.invOf]

lemma resps_tau (α : List (CLbl P m)) (p q : P) : respsOf (α ++ [.tau p]) q = respsOf α q := by
  simp [respsOf, Label.retOf]

lemma hasInput_tau (α : List (CLbl P m)) (p : P) (w : Fin m) :
    HasInput (α ++ [.tau p]) w ↔ HasInput α w :=
  hasInput_append_iff_of_ops (ops_tau α p) w

/-- A read step of `p` (memory and histories unchanged) that moves `p` to the local state `l'`
preserves the invariant, provided `l'` satisfies the per-process conditions. -/
lemma cinv_read (hI : CInv ℓ n grp α C W) {p : P} (l' : CLoc P m k)
    (hseq : l'.seq = (C.loc p).seq) (hidle : l'.ph ≠ .idle) (hinp : HasInput α l'.inp)
    (hval : ∀ w, (l'.ph = .prom w ∨ (∃ h, l'.ph = .promW w h) ∨ l'.ph = .done w) →
      HasInput α w)
    (hwr : ∀ w h, l'.ph = .promW w h → h <+: (W (grp p)).map Prod.snd ∧
      ∀ j (hj : j < (W (grp p)).length), (W (grp p))[j].2.1 = p → j < h.length)
    (hcol : ∀ i c₁ acc, l'.ph = .col i c₁ acc → i < k ∧
      ∀ g, c₁ g <+: (W g).map Prod.snd ∧ (g.val < i → acc g <+: (W g).map Prod.snd))
    (hresp : ∀ (w : Fin m), w ∈ respsOf α p → l'.ph = .done w)
    (hagree : AgreeV (fun q => vph n W (Function.update C.loc p l' q)) (ctrW W)) :
    CInv ℓ n grp (α ++ [.tau p]) ⟨Function.update C.loc p l', C.pend, C.mem⟩ W := by
  have hl : ∀ q, q ≠ p → Function.update C.loc p l' q = C.loc q :=
    fun q hq => Function.update_of_ne hq _ _
  refine ⟨hI.good, hI.mem, fun g e he => ?_, fun q hq => ?_, fun q hq => ?_, fun q w hq => ?_,
    fun g e he => (hasInput_tau α p _).2 (hI.w_val g e he), fun q w h hq => ?_,
    fun q i c₁ acc hq => ?_, fun q w hw => ?_, hagree⟩
  · have := hI.seq g e he
    dsimp only
    by_cases hq : e.2.1 = p
    · rw [hq] at this ⊢; rw [Function.update_self, hseq]; exact this
    · rw [hl _ hq]; exact this
  · dsimp only at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; exact absurd hq hidle
    · rw [hl q hqp] at hq; rw [ops_tau]; exact hI.idle q hq
  · dsimp only at hq ⊢
    rw [hasInput_tau]
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self]; exact hinp
    · rw [hl q hqp] at hq ⊢; exact hI.inp q hq
  · dsimp only at hq ⊢
    rw [hasInput_tau]
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; exact hval w hq
    · rw [hl q hqp] at hq; exact hI.ph_val q w hq
  · dsimp only at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; exact hwr w h hq
    · rw [hl q hqp] at hq; exact hI.wr q w h hq
  · dsimp only at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; exact hcol i c₁ acc hq
    · rw [hl q hqp] at hq; exact hI.col q i c₁ acc hq
  · dsimp only
    rw [resps_tau] at hw
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self]; exact hresp w hw
    · rw [hl q hqp]; exact hI.resp q w hw

lemma recon_mem (hI : CInv ℓ n grp α C W) (hgrp : ∀ g, (members grp g).card ≤ ℓ) (g : Fin k) :
    recon ℓ (C.mem g) = (W g).map Prod.snd := by
  rw [hI.mem g]; exact recon_correct (hI.good g) (hgrp g)

lemma cinv_prom (hI : CInv ℓ n grp α C W) (hgrp : ∀ g, (members grp g).card ≤ ℓ) {p : P}
    {w : Fin m} (hph : (C.loc p).ph = .prom w) :
    CInv ℓ n grp (α ++ [.tau p]) ⟨Function.update C.loc p
      ⟨.promW w (recon ℓ (C.mem (grp p))), (C.loc p).seq, (C.loc p).inp⟩, C.pend, C.mem⟩ W := by
  rw [recon_mem hI hgrp]
  refine cinv_read hI _ rfl (by simp) (hI.inp p (by rw [hph]; simp)) (fun w' hw' => ?_)
    (fun w' h hw' => ?_) (fun i c₁ acc h => by simp at h) (fun w' hw => ?_) ?_
  · rcases hw' with h | ⟨h, h'⟩ | h
    · cases h
    · injection h' with h1 h2; subst h1; exact hI.ph_val p _ (Or.inl hph)
    · cases h
  · simp only [CPh.promW.injEq] at hw'
    rw [← hw'.2]
    exact ⟨List.prefix_refl _, fun j hj _ => by simpa using hj⟩
  · have := hI.resp p w' hw; rw [hph] at this; cases this
  · have : (fun q => vph n W (Function.update C.loc p
        ⟨.promW w ((W (grp p)).map Prod.snd), (C.loc p).seq, (C.loc p).inp⟩ q)) =
        fun q => vph n W (C.loc q) := by
      funext q
      by_cases hq : q = p
      · subst hq; rw [Function.update_self]; simp [vph, hph]
      · rw [Function.update_of_ne hq]
    rw [this]; exact hI.agree

/-- The value decided or promoted after a successful scan is an input. -/
lemma hasInput_scanPh (hI : CInv ℓ n grp α C W) (hn1 : 1 ≤ n) {c₁ : Fin k → List (CTag P m)}
    (hpre : ∀ g, c₁ g <+: (W g).map Prod.snd) {inp : Fin m} (hinp : HasInput α inp) {w : Fin m}
    (hw : scanPh (P := P) (k := k) n (cnt c₁) inp = .done w ∨
      scanPh (P := P) (k := k) n (cnt c₁) inp = .prom w) : HasInput α w := by
  have key : ∀ u, 0 < cnt c₁ u → HasInput α u := by
    intro u hu
    obtain ⟨g, e, he, rfl⟩ := exists_of_cnt_pos hu hpre
    exact hI.w_val g e he
  unfold scanPh at hw
  split_ifs at hw with hL
  · simp only [CPh.done.injEq, or_false] at hw
    subst hw
    by_cases hpos : 0 < cnt c₁ (argmax (cnt c₁))
    · exact key _ hpos
    · have : ∀ u, u = argmax (cnt c₁) := by
        intro u; by_contra hu; have := hL u hu; omega
      rw [← this inp]; exact hinp
  · simp only [CPh.prom.injEq, false_or] at hw
    subst hw
    unfold pv
    split_ifs with h0
    · exact hinp
    · apply key
      obtain ⟨u, hu⟩ : ∃ u, cnt c₁ u ≠ 0 := by
        by_contra hc; push Not at hc; exact h0 (funext hc)
      have := le_argmax (cnt c₁) u
      omega

lemma cinv_col (hI : CInv ℓ n grp α C W) (hgrp : ∀ g, (members grp g).card ≤ ℓ)
    (hn : Fintype.card P ≤ n) {p : P} {i : ℕ} {c₁ acc : Fin k → List (CTag P m)}
    (hph : (C.loc p).ph = .col i c₁ acc) (hi : i < k) :
    CInv ℓ n grp (α ++ [.tau p]) ⟨Function.update C.loc p
      (colNext ℓ n i hi c₁ acc (C.mem ⟨i, hi⟩) (C.loc p)), C.pend, C.mem⟩ W := by
  have hn1 : 1 ≤ n := le_trans (Fintype.card_pos_iff.2 ⟨p⟩) hn
  obtain ⟨-, hpre⟩ := hI.col p i c₁ acc hph
  set acc' := Function.update acc ⟨i, hi⟩ ((W ⟨i, hi⟩).map Prod.snd) with hacc'
  have hpre' : ∀ g : Fin k, g.val < i + 1 → acc' g <+: (W g).map Prod.snd := by
    intro g hg
    by_cases hgi : g = ⟨i, hi⟩
    · subst hgi; simp [acc']
    · rw [hacc', Function.update_of_ne hgi]
      exact (hpre g).2 (by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hg with h | h
        · exact h
        · exact absurd (Fin.ext h) hgi)
  have hcn : colNext ℓ n i hi c₁ acc (C.mem ⟨i, hi⟩) (C.loc p) =
      if i + 1 < k then ⟨.col (i + 1) c₁ acc', (C.loc p).seq, (C.loc p).inp⟩
      else if acc' = c₁ then ⟨scanPh n (cnt c₁) (C.loc p).inp, (C.loc p).seq, (C.loc p).inp⟩
      else ⟨.col 0 acc' emp, (C.loc p).seq, (C.loc p).inp⟩ := by
    simp only [colNext, recon_mem hI hgrp, acc']
  have hinp := hI.inp p (by rw [hph]; simp)
  have hresp : ∀ (w : Fin m), w ∈ respsOf α p → False := by
    intro w hw; have := hI.resp p w hw; rw [hph] at this; cases this
  rw [hcn]
  split_ifs with hk hacc
  · -- middle of a collect
    refine cinv_read hI _ rfl (by simp) hinp (fun w h => by simp at h) (fun w h h' => by simp at h')
      (fun i' c₁' acc'' h => ?_) (fun w hw => (hresp w hw).elim) ?_
    · simp only [CPh.col.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hk, fun g => ⟨(hpre g).1, hpre' g⟩⟩
    · have : (fun q => vph n W (Function.update C.loc p
          ⟨.col (i + 1) c₁ acc', (C.loc p).seq, (C.loc p).inp⟩ q)) =
          fun q => vph n W (C.loc q) := by
        funext q
        by_cases hq : q = p
        · subst hq
          rw [Function.update_self]
          have hv := valid_step (W := W) hi (c₁ := c₁) (acc := acc)
          rw [← hacc'] at hv
          simp only [vph, hph]
          by_cases hvv : Valid W i c₁ acc
          · simp only [hvv, hv.2 hvv, ↓reduceIte]
          · simp only [hvv, mt hv.1 hvv, ↓reduceIte]
        · rw [Function.update_of_ne hq]
      rw [this]; exact hI.agree
  · -- successful double collect
    have hval : Valid W i c₁ acc := (valid_last hi hk).1 hacc
    refine cinv_read hI _ rfl (by unfold scanPh; split_ifs <;> simp) hinp (fun w h => ?_)
      (fun w h h' => by unfold scanPh at h'; split_ifs at h')
      (fun i' c₁' acc'' h => by unfold scanPh at h; split_ifs at h)
      (fun w hw => (hresp w hw).elim) ?_
    · refine hasInput_scanPh hI hn1 (fun g => (hpre g).1) hinp ?_
      rcases h with h | ⟨h', h⟩ | h
      · exact Or.inr h
      · unfold scanPh at h; split_ifs at h
      · exact Or.inl h
    · have : (fun q => vph n W (Function.update C.loc p
          ⟨scanPh n (cnt c₁) (C.loc p).inp, (C.loc p).seq, (C.loc p).inp⟩ q)) =
          fun q => vph n W (C.loc q) := by
        funext q
        by_cases hq : q = p
        · subst hq
          rw [Function.update_self, vph_scanPh]
          simp only [vph, hph, hval, ↓reduceIte]
        · rw [Function.update_of_ne hq]
      rw [this]; exact hI.agree
  · -- failed double collect: start a new one with `c₁ := acc'`
    have hnval : ¬ Valid W i c₁ acc := fun h => hacc ((valid_last hi hk).2 h)
    refine cinv_read hI _ rfl (by simp) hinp (fun w h => by simp at h) (fun w h h' => by simp at h')
      (fun i' c₁' acc'' h => ?_) (fun w hw => (hresp w hw).elim) ?_
    · simp only [CPh.col.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨by omega, fun g => ⟨hpre' g (by have := g.isLt; omega), fun h => absurd h (by omega)⟩⟩
    · have hold : vph n W (C.loc p) = .scan := by simp [vph, hph, hnval]
      by_cases hv : Valid W 0 acc' emp
      · have hctr : cnt acc' = ctrW W := by
          unfold ctrW; congr 1; funext g; exact ((valid_zero.1 hv) g).symm
        refine hI.agree.scan hn hold (p := p) (inp := (C.loc p).inp) ?_ ?_
        · simp only [Function.update_self, vph, hv, ↓reduceIte, hctr]
        · intro q hq; simp only [Function.update_of_ne hq]
      · have : (fun q => vph n W (Function.update C.loc p
            ⟨.col 0 acc' emp, (C.loc p).seq, (C.loc p).inp⟩ q)) =
            fun q => vph n W (C.loc q) := by
          funext q
          by_cases hq : q = p
          · subst hq
            rw [Function.update_self, hold]
            simp only [vph, hv, ↓reduceIte]
          · rw [Function.update_of_ne hq]
        rw [this]; exact hI.agree

lemma cinv_promW (hI : CInv ℓ n grp α C W) {p : P} {w : Fin m} {h : List (CTag P m)}
    (hph : (C.loc p).ph = .promW w h) :
    CInv ℓ n grp (α ++ [.tau p]) ⟨Function.update C.loc p
      ⟨.col 0 emp emp, (C.loc p).seq + 1, (C.loc p).inp⟩, C.pend,
      Function.update C.mem (grp p) (bufWrite ℓ (h, (p, (C.loc p).seq, w)) (C.mem (grp p)))⟩
      (Function.update W (grp p) (W (grp p) ++ [(h, (p, (C.loc p).seq, w))])) := by
  set g := grp p with hg
  set e : CEntry P m := (h, (p, (C.loc p).seq, w)) with he
  set W' := Function.update W g (W g ++ [e]) with hW'
  set l' : CLoc P m k := ⟨.col 0 emp emp, (C.loc p).seq + 1, (C.loc p).inp⟩ with hl'
  obtain ⟨hwpre, hword⟩ := hI.wr p w h hph
  have hl : ∀ q, q ≠ p → Function.update C.loc p l' q = C.loc q :=
    fun q hq => Function.update_of_ne hq _ _
  have hnotin : e.2 ∉ (W g).map Prod.snd := by
    intro hm
    obtain ⟨e', he', hee⟩ := List.mem_map.1 hm
    have := hI.seq g e' he'
    rw [hee] at this
    exact lt_irrefl _ this
  have hWg : ∀ g', W' g' = if g' = g then W g ++ [e] else W g' := by
    intro g'; by_cases hgg : g' = g
    · subst hgg; simp [hW']
    · simp [hW', hgg]
  have hmemW : ∀ g' e', e' ∈ W' g' → e' ∈ W g' ∨ (g' = g ∧ e' = e) := by
    intro g' e' he'
    rw [hWg] at he'
    split_ifs at he' with hgg
    · rcases List.mem_append.1 he' with h1 | h1
      · left; rw [hgg]; exact h1
      · right; exact ⟨hgg, List.mem_singleton.1 h1⟩
    · left; exact he'
  have hprefix : ∀ g', (W g').map Prod.snd <+: (W' g').map Prod.snd := by
    intro g'; rw [hWg]; split_ifs with hgg
    · subst hgg; rw [List.map_append]; exact List.prefix_append _ _
    · exact List.prefix_refl _
  have hinp := hI.inp p (by rw [hph]; simp)
  have hwin : HasInput α w := hI.ph_val p w (Or.inr (Or.inl ⟨h, hph⟩))
  refine ⟨fun g' => ?_, fun g' => ?_, fun g' e' he' => ?_, fun q hq => ?_, fun q hq => ?_,
    fun q w' hq => ?_, fun g' e' he' => ?_, fun q w' h' hq => ?_, fun q i c₁ acc hq => ?_,
    fun q w' hw => ?_, ?_⟩
  · -- good
    rw [hWg]; split_ifs with hgg
    · subst hgg
      refine (hI.good _).append hwpre (fun j hj hown => hword j hj hown) ?_ hnotin
      simp [members, g]
    · exact hI.good g'
  · -- mem
    dsimp only
    by_cases hgg : g' = g
    · subst hgg
      rw [Function.update_self, hI.mem, hW', Function.update_self]
      simp only [bufWrite, List.reverse_append, List.reverse_singleton, List.singleton_append]
      exact take_append_take [e] _ ℓ
    · rw [Function.update_of_ne hgg, hI.mem, hW', Function.update_of_ne hgg]
  · -- seq
    dsimp only
    rcases hmemW g' e' he' with he' | ⟨rfl, rfl⟩
    · have := hI.seq g' e' he'
      by_cases hq : e'.2.1 = p
      · rw [hq] at this ⊢; rw [Function.update_self]; dsimp only [l']; omega
      · rw [hl _ hq]; exact this
    · simp [e, l']
  · -- idle
    dsimp only at hq ⊢
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; simp [l'] at hq
    · rw [hl q hqp] at hq; rw [ops_tau]; exact hI.idle q hq
  · -- inp
    dsimp only at hq ⊢
    rw [hasInput_tau]
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self]; exact hinp
    · rw [hl q hqp] at hq ⊢; exact hI.inp q hq
  · -- ph_val
    dsimp only at hq
    rw [hasInput_tau]
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; simp [l'] at hq
    · rw [hl q hqp] at hq; exact hI.ph_val q w' hq
  · -- w_val
    rw [hasInput_tau]
    rcases hmemW g' e' he' with he' | ⟨-, rfl⟩
    · exact hI.w_val g' e' he'
    · exact hwin
  · -- wr
    dsimp only at hq
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; simp [l'] at hq
    · rw [hl q hqp] at hq
      obtain ⟨h1, h2⟩ := hI.wr q w' h' hq
      refine ⟨h1.trans (hprefix _), fun j hj hjq => ?_⟩
      by_cases hgq : grp q = g
      · have hj' : j < (W (grp q)).length + 1 := by
          have := hj; simp only [hWg, hgq, ↓reduceIte] at this; simpa [hgq] using this
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj'' | hj''
        · refine h2 j hj'' ?_
          have : (W' (grp q))[j] = (W (grp q))[j] := by
            simp only [hW', hgq, Function.update_self]
            rw [List.getElem_append_left (by rw [← hgq]; exact hj'')]
          rw [← this]; exact hjq
        · exfalso
          have : (W' (grp q))[j] = e := by
            simp only [hW', hgq, Function.update_self]
            rw [List.getElem_append_right (by rw [← hgq]; omega)]
            simp [hgq, hj'']
          rw [this] at hjq
          exact hqp hjq.symm
      · have : W' (grp q) = W (grp q) := by simp only [hWg, hgq, ↓reduceIte]
        have hj2 : j < (W (grp q)).length := by rw [← this]; exact hj
        refine h2 j hj2 ?_
        have : (W' (grp q))[j] = (W (grp q))[j] := by simp only [this]
        rw [← this]; exact hjq
  · -- col
    dsimp only at hq
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq
      simp only [l', CPh.col.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      exact ⟨by have := (grp q).isLt; omega, fun g' => ⟨by simp [emp], fun h => absurd h (by omega)⟩⟩
    · rw [hl q hqp] at hq
      obtain ⟨h1, h2⟩ := hI.col q i c₁ acc hq
      exact ⟨h1, fun g' => ⟨(h2 g').1.trans (hprefix g'), fun hg' => ((h2 g').2 hg').trans (hprefix g')⟩⟩
  · -- resp
    dsimp only
    rw [resps_tau] at hw
    by_cases hqp : q = p
    · subst hqp; have := hI.resp q w' hw; rw [hph] at this; cases this
    · rw [hl q hqp]; exact hI.resp q w' hw
  · -- agree
    have hctr : ctrW W' = Function.update (ctrW W) w (ctrW W w + 1) := ctrW_append W g e
    rw [hctr]
    have hscan : vph n W' l' = .scan := by
      have : ¬ Valid W' 0 emp emp := by
        intro hv
        have := (valid_zero.1 hv) g
        simp [hWg, emp] at this
      simp [vph, l', this]
    refine hI.agree.inc (p := p) (w := w) (by simp [vph, hph]) (fun v => ?_) (fun w' => ?_)
      (fun q hq w' hw' => ?_) (fun q hq v hv => ?_)
    · simp only [Function.update_self, hscan, badB]
    · simp only [Function.update_self, hscan]; exact fun h => by cases h
    · simp only [hl q hq] at hw' ⊢
      rcases vph_of_append (n := n) W g e (C.loc q)
          (fun i c₁ acc h => ((hI.col q i c₁ acc h).2 g).1) with h' | h'
      · rw [← h']; exact hw'
      · rw [h'] at hw'; cases hw'
    · simp only [hl q hq] at hv ⊢
      rcases vph_of_append (n := n) W g e (C.loc q)
          (fun i c₁ acc h => ((hI.col q i c₁ acc h).2 g).1) with h' | h'
      · rw [← h']; exact hv
      · rw [h'] at hv; simp [badB] at hv

lemma cinv_tau (hI : CInv ℓ n grp α C W) (hgrp : ∀ g, (members grp g).card ≤ ℓ)
    (hn : Fintype.card P ≤ n) {p : P} {C' : CCfg ℓ P m k}
    (h : (alg ℓ n grp).step C (.tau p) = some C') : ∃ W', CInv ℓ n grp (α ++ [.tau p]) C' W' := by
  have h0 := (Impl.step_tau h).1
  rcases hph : (C.loc p).ph with _ | w | ⟨w, hh⟩ | ⟨i, c₁, acc⟩ | w
  · exact absurd (hI.idle p hph).2 h0
  · rw [step_prom h0 hph] at h; cases h; exact ⟨W, cinv_prom hI hgrp hph⟩
  · rw [step_promW h0 hph] at h; cases h; exact ⟨_, cinv_promW hI hph⟩
  · have hi := (hI.col p i c₁ acc hph).1
    rw [step_col h0 hph hi] at h; cases h; exact ⟨W, cinv_col hI hgrp hn hph hi⟩
  · simp [Impl.step, h0, alg, hph] at h

theorem cinv_run (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n)
    {α : List (CLbl P m)} {C : CCfg ℓ P m k} (h : (alg ℓ n grp).run α = some C) :
    ∃ W, CInv ℓ n grp α C W := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom, Option.some.injEq] at h; subst h
    exact ⟨_, cinv_init⟩
  | append_singleton α lab ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (alg ℓ n grp).runFrom (alg ℓ n grp).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      obtain ⟨W, hI⟩ := ih hα
      cases lab with
      | inv p o => exact ⟨W, cinv_inv hI h⟩
      | tau p => exact cinv_tau hI hgrp hn h
      | ret p r => exact ⟨W, cinv_ret hI h⟩

/-- Agreement and validity hold in every finite execution of `alg`. -/
theorem alg_safe (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n)
    (α : List (CLbl P m)) (hα : (alg ℓ n grp).Valid α) :
    (consensus P (Fin m)).Δ (inputs α) (outputs α) := by
  obtain ⟨C, hC⟩ := hα
  obtain ⟨W, hI⟩ := cinv_run hgrp hn hC
  have hout : ∀ q (w : (taskObj (Fin m) (Fin m)).Resp), outputs α q = some w →
      (C.loc q).ph = .done w :=
    fun q w h => hI.resp q w (List.mem_of_head? h)
  have hv : ∀ q w, (C.loc q).ph = .done w → vph n W (C.loc q) = .done w :=
    fun q w h => by simp [vph, h]
  refine ⟨fun p q x y hx hy => ?_, fun p y hy => hI.ph_val p y (Or.inr (Or.inr (hout p y hy)))⟩
  rcases hI.agree with hA | ⟨v, hvv, -⟩
  · exact absurd (hv p x (hout p x hx)) (hA p x)
  · rw [hvv p x (hv p x (hout p x hx)), hvv q y (hv q y (hout q y hy))]

end PreserveTau

/-! ### Obstruction-freedom -/

section OF

variable {P : Type} {m k : ℕ} [NeZero m] [DecidableEq P] [Fintype P] {ℓ n : ℕ} {grp : P → Fin k}

/-- The local state at the end of a solo collect round started at index `i`. -/
noncomputable def roundLoc (n : ℕ) (W : Fin k → List (CEntry P m)) (i : ℕ)
    (c₁ acc : Fin k → List (CTag P m)) (l : CLoc P m k) : CLoc P m k := by
  classical
  exact
    let acc' : Fin k → List (CTag P m) := fun g => if g.val < i then acc g else (W g).map Prod.snd
    if acc' = c₁ then ⟨scanPh n (cnt c₁) l.inp, l.seq, l.inp⟩ else ⟨.col 0 acc' emp, l.seq, l.inp⟩

lemma soloStep_tau {C C' : CCfg ℓ P m k} {p : P} (hp : C.pend p ≠ none)
    (hnl : (alg ℓ n grp).nextLabel C p = .tau p) (h : (alg ℓ n grp).step C (.tau p) = some C') :
    (alg ℓ n grp).soloStep p C = C' := by
  simp [Impl.soloStep, hp, hnl, h]

/-- A solo collect round. -/
lemma solo_round (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) {p : P}
    {W : Fin k → List (CEntry P m)} (d : ℕ) :
    ∀ (i : ℕ), i < k → k = i + 1 + d → ∀ (α : List (CLbl P m)) (C : CCfg ℓ P m k)
      (c₁ acc : Fin k → List (CTag P m)), (alg ℓ n grp).run α = some C → CInv ℓ n grp α C W →
      C.pend p ≠ none → (C.loc p).ph = .col i c₁ acc →
      ∃ α' C', (alg ℓ n grp).run α' = some C' ∧ CInv ℓ n grp α' C' W ∧ C'.pend = C.pend ∧
        ((alg ℓ n grp).soloStep p)^[d + 1] C = C' ∧ C'.loc p = roundLoc n W i c₁ acc (C.loc p) := by
  induction d with
  | zero =>
    intro i hi hk α C c₁ acc hR hI hp hph
    have hstep := step_col (n := n) (grp := grp) hp hph hi
    refine ⟨_, _, by rw [Impl.run_append_of_eq _ hR, Impl.runFrom_singleton]; exact hstep,
      cinv_col hI hgrp hn hph hi, rfl, ?_, ?_⟩
    · rw [zero_add, Function.iterate_one]
      exact soloStep_tau hp (by simp [Impl.nextLabel, alg, hph, hi]) hstep
    · simp only [Function.update_self, colNext, roundLoc, recon_mem hI hgrp]
      have hk' : ¬ i + 1 < k := by omega
      have hacc : Function.update acc ⟨i, hi⟩ ((W ⟨i, hi⟩).map Prod.snd) =
          fun g : Fin k => if g.val < i then acc g else (W g).map Prod.snd := by
        funext g
        by_cases hg : g.val < i
        · rw [Function.update_of_ne (by intro h; subst h; simp at hg)]
          simp only [hg, ↓reduceIte]
        · have : g = ⟨i, hi⟩ := Fin.ext (by have := g.isLt; simp only; omega)
          subst this; simp
      simp only [hk', ↓reduceIte, hacc]
  | succ d ih =>
    intro i hi hk α C c₁ acc hR hI hp hph
    have hstep := step_col (n := n) (grp := grp) hp hph hi
    have hk' : i + 1 < k := by omega
    set acc' := Function.update acc ⟨i, hi⟩ ((W ⟨i, hi⟩).map Prod.snd) with hacc'
    set C₁ : CCfg ℓ P m k := ⟨Function.update C.loc p
      (colNext ℓ n i hi c₁ acc (C.mem ⟨i, hi⟩) (C.loc p)), C.pend, C.mem⟩ with hC₁
    have hR₁ : (alg ℓ n grp).run (α ++ [.tau p]) = some C₁ := by
      rw [Impl.run_append_of_eq _ hR, Impl.runFrom_singleton]; exact hstep
    have hI₁ := cinv_col hI hgrp hn hph hi
    have hloc₁ : C₁.loc p = ⟨.col (i + 1) c₁ acc', (C.loc p).seq, (C.loc p).inp⟩ := by
      simp only [hC₁, Function.update_self, colNext, recon_mem hI hgrp, hk', ↓reduceIte, acc']
    obtain ⟨α', C', hR', hI', hpend', hit, hloc'⟩ :=
      ih (i + 1) hk' (by omega) _ C₁ c₁ acc' hR₁ hI₁ hp (by rw [hloc₁])
    refine ⟨α', C', hR', hI', hpend', ?_, ?_⟩
    · rw [Function.iterate_succ_apply,
        soloStep_tau hp (by simp [Impl.nextLabel, alg, hph, hi]) hstep]
      exact hit
    · rw [hloc', hloc₁]
      simp only [roundLoc]
      have : (fun g : Fin k => if g.val < i + 1 then acc' g else (W g).map Prod.snd) =
          fun g : Fin k => if g.val < i then acc g else (W g).map Prod.snd := by
        funext g
        by_cases hg : g.val < i
        · simp only [show g.val < i + 1 by omega, hg, ↓reduceIte, hacc']
          rw [Function.update_of_ne (by intro h; subst h; simp at hg)]
        · simp only [hg, ↓reduceIte]
          by_cases hg' : g.val = i
          · have : g = ⟨i, hi⟩ := Fin.ext hg'
            subst this; simp [acc']
          · simp only [show ¬ g.val < i + 1 by omega, ↓reduceIte]
      simp only [this]

/-- The good configurations for solo runs: reachable, with the invariant for the ghost `W`. -/
def Good (ℓ n : ℕ) (grp : P → Fin k) (C : CCfg ℓ P m k) (W : Fin k → List (CEntry P m)) : Prop :=
  ∃ α, (alg ℓ n grp).run α = some C ∧ CInv ℓ n grp α C W

/-- Two solo collect rounds starting at index `0` produce an atomic scan of the current counts. -/
lemma solo_two_rounds (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) {p : P}
    {W : Fin k → List (CEntry P m)} {C : CCfg ℓ P m k} (hG : Good ℓ n grp C W)
    (hp : C.pend p ≠ none) {c₁ acc : Fin k → List (CTag P m)}
    (hph : (C.loc p).ph = .col 0 c₁ acc) :
    ∃ t C', Good ℓ n grp C' W ∧ C'.pend = C.pend ∧ ((alg ℓ n grp).soloStep p)^[t] C = C' ∧
      C'.loc p = ⟨scanPh n (ctrW W) (C.loc p).inp, (C.loc p).seq, (C.loc p).inp⟩ := by
  obtain ⟨α, hR, hI⟩ := hG
  have hk : 0 < k := (hI.col p 0 c₁ acc hph).1
  obtain ⟨α₁, C₁, hR₁, hI₁, hpend₁, hit₁, hloc₁⟩ :=
    solo_round (n := n) hgrp hn (k - 1) 0 hk (by omega) α C c₁ acc hR hI hp hph
  have htags : ∀ a : Fin k → List (CTag P m),
      (fun g : Fin k => if g.val < 0 then a g else (W g).map Prod.snd) =
      fun g => (W g).map Prod.snd := by intro a; funext g; simp
  have hctr : ∀ c : Fin k → List (CTag P m), (fun g => (W g).map Prod.snd) = c →
      cnt c = ctrW W := by intro c h; rw [← h]; rfl
  simp only [roundLoc, htags] at hloc₁
  split_ifs at hloc₁ with heq
  · exact ⟨k - 1 + 1, C₁, ⟨α₁, hR₁, hI₁⟩, hpend₁, hit₁, by rw [hloc₁, hctr c₁ heq]⟩
  · have hp₁ : C₁.pend p ≠ none := by rw [hpend₁]; exact hp
    obtain ⟨α₂, C₂, hR₂, hI₂, hpend₂, hit₂, hloc₂⟩ :=
      solo_round (n := n) hgrp hn (k - 1) 0 hk (by omega) α₁ C₁ _ emp hR₁ hI₁ hp₁
        (by rw [hloc₁])
    simp only [roundLoc, htags, ↓reduceIte, hloc₁] at hloc₂
    refine ⟨(k - 1 + 1) + (k - 1 + 1), C₂, ⟨α₂, hR₂, hI₂⟩, by rw [hpend₂, hpend₁], ?_,
      by rw [hloc₂, hctr _ rfl]⟩
    rw [Function.iterate_add_apply, hit₁, hit₂]

/-- A solo collect round from any index ends with some scan result. -/
lemma solo_col (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) {p : P}
    {W : Fin k → List (CEntry P m)} {C : CCfg ℓ P m k} (hG : Good ℓ n grp C W)
    (hp : C.pend p ≠ none) {i : ℕ} {c₁ acc : Fin k → List (CTag P m)}
    (hph : (C.loc p).ph = .col i c₁ acc) :
    ∃ t C' c, Good ℓ n grp C' W ∧ C'.pend = C.pend ∧ ((alg ℓ n grp).soloStep p)^[t] C = C' ∧
      C'.loc p = ⟨scanPh n c (C.loc p).inp, (C.loc p).seq, (C.loc p).inp⟩ := by
  obtain ⟨α, hR, hI⟩ := hG
  have hik : i < k := (hI.col p i c₁ acc hph).1
  obtain ⟨α₁, C₁, hR₁, hI₁, hpend₁, hit₁, hloc₁⟩ :=
    solo_round (n := n) hgrp hn (k - 1 - i) i hik (by omega) α C c₁ acc hR hI hp hph
  simp only [roundLoc] at hloc₁
  split_ifs at hloc₁ with heq
  · exact ⟨_, C₁, _, ⟨α₁, hR₁, hI₁⟩, hpend₁, hit₁, hloc₁⟩
  · have hp₁ : C₁.pend p ≠ none := by rw [hpend₁]; exact hp
    obtain ⟨t₂, C₂, hG₂, hpend₂, hit₂, hloc₂⟩ :=
      solo_two_rounds hgrp hn ⟨α₁, hR₁, hI₁⟩ hp₁ (by rw [hloc₁])
    refine ⟨t₂ + (k - 1 - i + 1), C₂, _, hG₂, by rw [hpend₂, hpend₁], ?_, by rw [hloc₂, hloc₁]⟩
    rw [Function.iterate_add_apply, hit₁, hit₂]

/-- A solo `promote w` (append to the own history, then two collect rounds). -/
lemma solo_prom (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) {p : P}
    {W : Fin k → List (CEntry P m)} {C : CCfg ℓ P m k} (hG : Good ℓ n grp C W)
    (hp : C.pend p ≠ none) {w : Fin m} (hph : (C.loc p).ph = .prom w) :
    ∃ t C' W', Good ℓ n grp C' W' ∧ C'.pend = C.pend ∧ ((alg ℓ n grp).soloStep p)^[t] C = C' ∧
      (C'.loc p).ph = scanPh n (ctrW W') (C.loc p).inp ∧ (C'.loc p).inp = (C.loc p).inp ∧
      ctrW W' = Function.update (ctrW W) w (ctrW W w + 1) := by
  obtain ⟨α, hR, hI⟩ := hG
  have hs₁ := step_prom (n := n) (grp := grp) hp hph
  set C₁ : CCfg ℓ P m k := ⟨Function.update C.loc p
      ⟨.promW w (recon ℓ (C.mem (grp p))), (C.loc p).seq, (C.loc p).inp⟩, C.pend, C.mem⟩
  have hR₁ : (alg ℓ n grp).run (α ++ [.tau p]) = some C₁ := by
    rw [Impl.run_append_of_eq _ hR, Impl.runFrom_singleton]; exact hs₁
  have hI₁ : CInv ℓ n grp (α ++ [.tau p]) C₁ W := cinv_prom hI hgrp hph
  have hph₁ : (C₁.loc p).ph = .promW w (recon ℓ (C.mem (grp p))) := by simp [C₁]
  set C₂ : CCfg ℓ P m k := ⟨Function.update C₁.loc p
      ⟨.col 0 emp emp, (C₁.loc p).seq + 1, (C₁.loc p).inp⟩, C₁.pend,
      Function.update C₁.mem (grp p) (bufWrite ℓ (recon ℓ (C.mem (grp p)),
        (p, (C₁.loc p).seq, w)) (C₁.mem (grp p)))⟩ with hC₂
  have hs₂ : (alg ℓ n grp).step C₁ (.tau p) = some C₂ :=
    step_promW (n := n) (grp := grp) (C := C₁) hp hph₁
  have hR₂ : (alg ℓ n grp).run (α ++ [.tau p] ++ [.tau p]) = some C₂ := by
    rw [Impl.run_append_of_eq _ hR₁, Impl.runFrom_singleton]; exact hs₂
  have hI₂ := cinv_promW hI₁ hph₁
  have hph₂ : (C₂.loc p).ph = .col 0 emp emp := by simp [C₂]
  obtain ⟨t, C', hG', hpend', hit, hloc'⟩ :=
    solo_two_rounds (n := n) hgrp hn ⟨_, hR₂, hI₂⟩ hp hph₂
  have hinp₂ : (C₂.loc p).inp = (C.loc p).inp := by simp [C₂, C₁]
  refine ⟨t + 2, C', _, hG', by rw [hpend'], ?_, by rw [hloc', hinp₂], by rw [hloc', hinp₂],
    ctrW_append _ _ _⟩
  rw [Function.iterate_add_apply]
  have h1 : (alg ℓ n grp).soloStep p C = C₁ :=
    soloStep_tau hp (by simp [Impl.nextLabel, alg, hph]) hs₁
  have h2 : (alg ℓ n grp).soloStep p C₁ = C₂ :=
    soloStep_tau hp (by simp [Impl.nextLabel, alg, hph₁]) hs₂
  rw [show ((alg ℓ n grp).soloStep p)^[2] C = C₂ by
    rw [Function.iterate_succ_apply, Function.iterate_one, h1, h2]]
  exact hit

lemma solo_done {p : P} {C : CCfg ℓ P m k} (hp : C.pend p ≠ none) {w : Fin m}
    (hph : (C.loc p).ph = .done w) : ((alg ℓ n grp).soloStep p C).pend p = none := by
  simp only [Impl.soloStep, Impl.nextLabel, Impl.step, hp, alg, hph, ↓reduceIte]
  split_ifs with h
  · simp
  · exact absurd rfl h

lemma pv_of_ne_zero {c : Fin m → ℕ} (hc : c ≠ 0) (inp : Fin m) : pv c inp = argmax c := by
  unfold pv; simp [hc]

lemma ne_zero_update (c : Fin m → ℕ) (w : Fin m) :
    Function.update c w (c w + 1) ≠ 0 := by
  intro h; have := congrFun h w; simp at this

/-- Running solo from `promote w` where `w` leads by `k₀` with `n ≤ k₀ + j`, `p` returns. -/
lemma solo_lead (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) (p : P)
    (j : ℕ) : ∀ (C : CCfg ℓ P m k) (W : Fin k → List (CEntry P m)) (k₀ : ℕ) (w : Fin m),
      Good ℓ n grp C W → C.pend p ≠ none → (C.loc p).ph = .prom w → Lead k₀ (ctrW W) w →
      n ≤ k₀ + j → ∃ t, (((alg ℓ n grp).soloStep p)^[t] C).pend p = none := by
  induction j with
  | zero =>
    intro C W k₀ w hG hp hph hL hk
    obtain ⟨t, C', W', hG', hpend', hit, hph', -, hctr⟩ := solo_prom hgrp hn hG hp hph
    have hL1 : Lead (k₀ + 1) (ctrW W') w := by rw [hctr]; exact hL.inc
    have hp' : C'.pend p ≠ none := by rw [hpend']; exact hp
    rw [scanPh, hL1.argmax_eq] at hph'
    simp only [hL1.mono (by omega : n ≤ k₀ + 1), ↓reduceIte] at hph'
    exact ⟨1 + t, by rw [Function.iterate_add_apply, hit]; exact solo_done hp' hph'⟩
  | succ j ih =>
    intro C W k₀ w hG hp hph hL hk
    obtain ⟨t, C', W', hG', hpend', hit, hph', -, hctr⟩ := solo_prom hgrp hn hG hp hph
    have hL1 : Lead (k₀ + 1) (ctrW W') w := by rw [hctr]; exact hL.inc
    have hp' : C'.pend p ≠ none := by rw [hpend']; exact hp
    have hnz : ctrW W' ≠ 0 := by rw [hctr]; exact ne_zero_update _ _
    rw [scanPh, hL1.argmax_eq, pv_of_ne_zero hnz, hL1.argmax_eq] at hph'
    split_ifs at hph' with hLn
    · exact ⟨1 + t, by rw [Function.iterate_add_apply, hit]; exact solo_done hp' hph'⟩
    · obtain ⟨t', ht'⟩ := ih C' W' (k₀ + 1) w hG' hp' hph' hL1 (by omega)
      exact ⟨t' + t, by rw [Function.iterate_add_apply, hit]; exact ht'⟩

lemma solo_from_scan (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) {p : P}
    {C : CCfg ℓ P m k} {W : Fin k → List (CEntry P m)} (hG : Good ℓ n grp C W)
    (hp : C.pend p ≠ none) (hnz : ctrW W ≠ 0) {inp : Fin m}
    (hph : (C.loc p).ph = scanPh n (ctrW W) inp) :
    ∃ t, (((alg ℓ n grp).soloStep p)^[t] C).pend p = none := by
  rw [scanPh, pv_of_ne_zero hnz] at hph
  split_ifs at hph
  · exact ⟨1, solo_done hp hph⟩
  · exact solo_lead hgrp hn p n C W 0 _ hG hp hph (lead_zero_argmax _) (by omega)

lemma solo_from_prom (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) {p : P}
    {C : CCfg ℓ P m k} {W : Fin k → List (CEntry P m)} (hG : Good ℓ n grp C W)
    (hp : C.pend p ≠ none) {w : Fin m} (hph : (C.loc p).ph = .prom w) :
    ∃ t, (((alg ℓ n grp).soloStep p)^[t] C).pend p = none := by
  obtain ⟨t, C', W', hG', hpend', hit, hph', -, hctr⟩ := solo_prom hgrp hn hG hp hph
  have hp' : C'.pend p ≠ none := by rw [hpend']; exact hp
  have hnz : ctrW W' ≠ 0 := by rw [hctr]; exact ne_zero_update _ _
  obtain ⟨t', ht'⟩ := solo_from_scan hgrp hn hG' hp' hnz hph'
  exact ⟨t' + t, by rw [Function.iterate_add_apply, hit]; exact ht'⟩

/-- `alg` is obstruction-free (if `|P| ≤ n` and every group has at most `ℓ` members). -/
theorem alg_obstructionFree (hgrp : ∀ g, (members grp g).card ≤ ℓ) (hn : Fintype.card P ≤ n) :
    (alg (m := m) ℓ n grp).ObstructionFree := by
  intro C p hR hp
  obtain ⟨α, hα⟩ := hR
  obtain ⟨W, hI⟩ := cinv_run hgrp hn hα
  have hG : Good ℓ n grp C W := ⟨α, hα, hI⟩
  rcases hph : (C.loc p).ph with _ | w | ⟨w, hh⟩ | ⟨i, c₁, acc⟩ | w
  · exact absurd (hI.idle p hph).2 hp
  · exact solo_from_prom hgrp hn hG hp hph
  · obtain ⟨C₁, hs, hI₁, hph₁⟩ : ∃ C₁, (alg ℓ n grp).step C (.tau p) = some C₁ ∧
        CInv ℓ n grp (α ++ [.tau p]) C₁
          (Function.update W (grp p) (W (grp p) ++ [(hh, (p, (C.loc p).seq, w))])) ∧
        (C₁.loc p).ph = .col 0 emp emp :=
      ⟨_, step_promW hp hph, cinv_promW hI hph, by simp⟩
    have hR₁ : (alg ℓ n grp).run (α ++ [.tau p]) = some C₁ := by
      rw [Impl.run_append_of_eq _ hα, Impl.runFrom_singleton]; exact hs
    have hpend₁ : C₁.pend = C.pend := (Impl.step_tau hs).2.1
    have hp₁ : C₁.pend p ≠ none := by rw [hpend₁]; exact hp
    have h1 := soloStep_tau hp (by simp [Impl.nextLabel, alg, hph]) hs
    obtain ⟨t, C', hG', hpend', hit, hloc'⟩ :=
      solo_two_rounds (n := n) hgrp hn ⟨_, hR₁, hI₁⟩ hp₁ hph₁
    have hp' : C'.pend p ≠ none := by rw [hpend']; exact hp₁
    have hnz : ctrW (Function.update W (grp p) (W (grp p) ++ [(hh, (p, (C.loc p).seq, w))])) ≠ 0 := by
      rw [ctrW_append]; exact ne_zero_update _ _
    obtain ⟨t', ht'⟩ := solo_from_scan hgrp hn hG' hp' hnz (by rw [hloc'])
    refine ⟨t' + t + 1, ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, h1, hit]
    exact ht'
  · obtain ⟨t, C', c, hG', hpend', hit, hloc'⟩ := solo_col hgrp hn hG hp hph
    have hp' : C'.pend p ≠ none := by rw [hpend']; exact hp
    have hph' : (C'.loc p).ph = scanPh n c (C.loc p).inp := by rw [hloc']
    unfold scanPh at hph'
    split_ifs at hph'
    · exact ⟨1 + t, by rw [Function.iterate_add_apply, hit]; exact solo_done hp' hph'⟩
    · obtain ⟨t', ht'⟩ := solo_from_prom hgrp hn hG' hp' hph'
      exact ⟨t' + t, by rw [Function.iterate_add_apply, hit]; exact ht'⟩
  · exact ⟨1, solo_done hp hph⟩

end OF

end BufCons

/-! ### Theorem 6.3 -/

section Main

open BufCons

/-- The grouping of `n = |P|` processes into `⌈n/ℓ⌉` groups of at most `ℓ`. -/
noncomputable def ceilGrp (P : Type) [Fintype P] (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (p : P) :
    Fin ((Fintype.card P + ℓ - 1) / ℓ) :=
  ⟨(Fintype.equivFin P p : ℕ) / ℓ, by
    have h1 := (Fintype.equivFin P p).isLt
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have h2 := Nat.mod_add_div (Fintype.card P + ℓ - 1) ℓ
    have h3 := Nat.mod_lt (Fintype.card P + ℓ - 1) (show ℓ > 0 by omega)
    have : (Fintype.card P + ℓ - 1) / ℓ * ℓ = ℓ * ((Fintype.card P + ℓ - 1) / ℓ) := by ring
    omega⟩

lemma ceilGrp_card {P : Type} [Fintype P] [DecidableEq P] (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (g : Fin ((Fintype.card P + ℓ - 1) / ℓ)) : (members (ceilGrp P ℓ hℓ) g).card ≤ ℓ := by
  have : (members (ceilGrp P ℓ hℓ) g).card ≤ (Finset.Ico (g.val * ℓ) (g.val * ℓ + ℓ)).card := by
    apply Finset.card_le_card_of_injOn (fun p => (Fintype.equivFin P p : ℕ))
    · intro p hp
      simp only [members, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        ceilGrp, Fin.ext_iff] at hp
      simp only [Finset.coe_Ico, Set.mem_Ico]
      have h2 := Nat.mod_add_div (Fintype.equivFin P p : ℕ) ℓ
      have h3 := Nat.mod_lt (Fintype.equivFin P p : ℕ) (show ℓ > 0 by omega)
      rw [hp, mul_comm] at h2
      constructor <;> omega
    · intro p _ q _ h
      exact (Fintype.equivFin P).injective (Fin.ext h)
  simpa using this

/-- **Theorem 6.3** of [EGSZ16]: obstruction-free `m`-valued consensus among `n = |P|` processes
can be solved using `⌈n/ℓ⌉` `ℓ`-buffers (`ℓ ≥ 1`), all initially empty. Agreement and validity
hold in every execution (`BufCons.alg_safe`); obstruction-freedom is CSLib's
`Impl.ObstructionFree`. Together with `theorem_6_8` (`n - 1 ≤ ℓ · #buffers`) this is tight up to
one buffer. -/
theorem theorem_6_3 (m : ℕ) [NeZero m] (P : Type) [DecidableEq P] [Fintype P] (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) :
    ∃ (V L : Type) (I : Impl (taskObj (Fin m) (Fin m))
        (fun _ : Fin ((Fintype.card P + ℓ - 1) / ℓ) => bufferSpec ℓ V) P L),
      (∀ g, I.memInit g = []) ∧ (∀ p v, I.allowed p v) ∧ I.Solves (consensus P (Fin m)) ∧
        I.ObstructionFree :=
  ⟨CEntry P m, CLoc P m _, alg ℓ (Fintype.card P) (ceilGrp P ℓ hℓ), fun _ => rfl,
    fun _ _ => trivial, fun α hα _ => alg_safe (ceilGrp_card ℓ hℓ) le_rfl α hα,
    alg_obstructionFree (ceilGrp_card ℓ hℓ) le_rfl⟩

end Main

end Cslib.SharedMemory.ComplexityHierarchy
