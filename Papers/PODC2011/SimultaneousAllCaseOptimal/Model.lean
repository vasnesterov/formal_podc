import Cslib.Computability.Distributed.SyncCrash.Model
import Mathlib

/-!
# Model of Herlihy–Moses–Tuttle, *Transforming worst-case optimal solutions for simultaneous
tasks into all-case optimal solutions* (PODC 2011), §2

* Synchronous message passing with crash failures (§2.1): CSLib's `Cslib.SyncCrash` model. A run
  (`Cslib.SyncCrash.Run P I`) is an input vector plus a crash pattern (crash round `c ≥ 1`, the set
  `reach p` of processes still reached in the crashing round); `Run.Admissible t` = at most `t`
  crashes. Protocols are CSLib's deterministic history-based lock-step protocols
  (`Cslib.Byzantine.LockStep.Protocol P I M O`): the local state of `p` at time `m` is its input
  and the list of inboxes of rounds `1, …, m` (`Cslib.SyncCrash.state`). The run of a protocol is
  determined by the protocol, the input vector and the failure pattern (`r = A[ı, F]`).
* Decisions (§2.2): `A.decide p x h` is the content of `p`'s output register; `p` *decides `d` at
  time `m`* (`Decides`) iff `p` is alive at time `m`, the register holds `d` at time `m` and was
  empty before (the first write).
* Decision tasks (`Task`), solving a task (`Solves`), the simultaneous version (`SolvesSim`), and
  solving within `k` rounds (`SolvesWithin`).
* Truncated failure patterns (`Run.trunc`) and the key consequence for simultaneous protocols:
  if some process decides at time `k`, every process alive at time `k` decides at time `k`
  (`SolvesSim.decides_of_alive`). This fact is used silently in the paper's proofs of Lemma 1,
  Theorem 3 and Lemma 4.
* Exposed failures and the waste `W(F)` (§4).
-/

namespace Podc.SimultaneousAllCaseOptimal

open Cslib.SyncCrash Cslib.Byzantine.LockStep

variable {P I M O : Type}

/-! ### Decisions -/

/-- `p` decides `d` at time `m` of `r`: the first write to its output register happens at time `m`
(and `p` is alive then). -/
def Decides (A : Protocol P I M O) (r : Run P I) (p : P) (m : ℕ) (d : O) : Prop :=
  DecidesAt A r p m d ∧ ∀ m' < m, A.decide p (r.input p) (hist A r m' p) = none

/-- The raw content of `p`'s output register at time `m` (meaningful while `p` is alive). -/
noncomputable abbrev raw (A : Protocol P I M O) (r : Run P I) (p : P) (m : ℕ) : Option O :=
  A.decide p (r.input p) (hist A r m p)

lemma decides_iff {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} {d : O} :
    Decides A r p m d ↔ r.Alive p m ∧ raw A r p m = some d ∧ ∀ m' < m, raw A r p m' = none := by
  unfold Decides; rw [decidesAt_iff]; tauto

lemma Decides.alive {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} {d : O}
    (h : Decides A r p m d) : r.Alive p m := (decides_iff.1 h).1

lemma Decides.raw_eq {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} {d : O}
    (h : Decides A r p m d) : raw A r p m = some d := (decides_iff.1 h).2.1

lemma Decides.raw_lt {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} {d : O}
    (h : Decides A r p m d) {m' : ℕ} (hm : m' < m) : raw A r p m' = none := (decides_iff.1 h).2.2 m' hm

/-- The first decision is unique. -/
lemma Decides.unique {A : Protocol P I M O} {r : Run P I} {p : P} {m m' : ℕ} {d d' : O}
    (h : Decides A r p m d) (h' : Decides A r p m' d') : m = m' ∧ d = d' := by
  have hm : m = m' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := h'.raw_lt hlt; rw [h.raw_eq] at this; simp at this
    · have := h.raw_lt hlt; rw [h'.raw_eq] at this; simp at this
  subst hm
  refine ⟨rfl, ?_⟩
  have := h.raw_eq.symm.trans h'.raw_eq
  simpa using this

/-- If the register of an alive process is nonempty at time `m`, the process has decided by `m`. -/
lemma exists_decides_of_raw {A : Protocol P I M O} {r : Run P I} {p : P} {m : ℕ} {d : O}
    (ha : r.Alive p m) (h : raw A r p m = some d) : ∃ m' ≤ m, ∃ d', Decides A r p m' d' := by
  classical
  have hex : ∃ j, (raw A r p j).isSome ∧ j ≤ m := ⟨m, by simp [h], le_rfl⟩
  let j := Nat.find hex
  have hj : (raw A r p j).isSome ∧ j ≤ m := Nat.find_spec hex
  obtain ⟨d', hd'⟩ := Option.isSome_iff_exists.1 hj.1
  refine ⟨j, hj.2, d', decides_iff.2 ⟨ha.mono hj.2, hd', fun m' hm' => ?_⟩⟩
  have := Nat.find_min hex hm'
  simp only [not_and, Option.isSome_iff_ne_none, ne_eq, not_not] at this
  by_contra hc
  exact this hc (le_trans hm'.le hj.2)

/-! ### Decision tasks -/

/-- A decision task (§2.2): a set `inputs` of input vectors and a relation `rel` between input
and output vectors. -/
structure Task (P I O : Type) where
  /-- The allowed input vectors (`I` of the paper; "complete" if it is all of `I₁ × ⋯ × Iₙ`). -/
  inputs : Set (P → I)
  /-- `(ı, o) ∈ P`: on inputs `ı` the processes may output `o`. -/
  rel : (P → I) → (P → O) → Prop

variable [Fintype P]

/-- The runs considered for a task: at most `t` crashes and an allowed input vector. -/
def Task.IsRun (T : Task P I O) (t : ℕ) (r : Run P I) : Prop :=
  r.Admissible t ∧ r.input ∈ T.inputs

/-- `A` solves the decision task `T` when at most `t` processes crash (§2.2): completeness
(every nonfaulty process decides) and correctness (the decisions are part of an output vector
allowed for the input vector). -/
structure Solves (A : Protocol P I M O) (T : Task P I O) (t : ℕ) : Prop where
  complete : ∀ r, T.IsRun t r → ∀ p, ¬ r.Faulty p → ∃ m d, Decides A r p m d
  correct : ∀ r, T.IsRun t r → ∃ o, T.rel r.input o ∧ ∀ p m d, Decides A r p m d → o p = d

/-- `A` solves the simultaneous version `sim(T)`: in addition, all deciding processes decide in
the same round. -/
structure SolvesSim (A : Protocol P I M O) (T : Task P I O) (t : ℕ) : Prop extends
    Solves A T t where
  simultaneous : ∀ r, T.IsRun t r → ∀ p q m m' d d', Decides A r p m d → Decides A r q m' d' →
    m = m'

/-- `A` solves `T` and every nonfaulty process decides by time `k` (`k` is an upper bound on the
worst-case execution time). -/
structure SolvesWithin (A : Protocol P I M O) (T : Task P I O) (t k : ℕ) : Prop extends
    Solves A T t where
  within : ∀ r, T.IsRun t r → ∀ p, ¬ r.Faulty p → ∃ m ≤ k, ∃ d, Decides A r p m d

/-- All nonfaulty processes decide at time `k` in the run `r`. -/
def DecideAll (A : Protocol P I M O) (r : Run P I) (k : ℕ) : Prop :=
  ∀ p, ¬ r.Faulty p → ∃ d, Decides A r p k d

/-- All nonfaulty processes decide by time `k` in the run `r`. -/
def DecideBy (A : Protocol P I M O) (r : Run P I) (k : ℕ) : Prop :=
  ∀ p, ¬ r.Faulty p → ∃ m ≤ k, ∃ d, Decides A r p m d

/-! ### Histories -/

/-- Histories only depend on the sending functions. -/
lemma hist_eq_of_send {M O O' : Type} {A : Protocol P I M O} {B : Protocol P I M O'}
    (h : A.send = B.send) (r : Run P I) : ∀ m p, hist A r m p = hist B r m p := by
  intro m
  induction m with
  | zero => intro p; rfl
  | succ m ih =>
    intro p
    have : (fun q => msg A r q p m) = (fun q => msg B r q p m) := by
      funext q; rw [msg_eq_deliv, msg_eq_deliv, ih q, h]
    rw [Cslib.SyncCrash.hist_succ, Cslib.SyncCrash.hist_succ, ih p, this]

/-- The history at an earlier time is a prefix. -/
lemma hist_take (A : Protocol P I M O) (r : Run P I) {m k : ℕ} (h : m ≤ k) (p : P) :
    (hist A r k p).take m = hist A r m p := by
  induction k with
  | zero =>
    have : m = 0 := by omega
    subst this; simp
  | succ k ih =>
    rcases Nat.lt_or_ge m (k + 1) with hlt | hge
    · rw [Cslib.SyncCrash.hist_succ, List.take_append_of_le_length (by simp; omega), ih (by omega)]
    · have : m = k + 1 := by omega
      subst this
      exact List.take_of_length_le (by simp)

/-- Equal states at time `k` give equal states at earlier times. -/
lemma hist_eq_of_le {A : Protocol P I M O} {r r' : Run P I} {p : P} {m k : ℕ} (hmk : m ≤ k)
    (h : hist A r k p = hist A r' k p) : hist A r m p = hist A r' m p := by
  rw [← hist_take A r hmk, ← hist_take A r' hmk, h]

/-- A process with the same input and history at time `k` in two runs, alive in both, decides
at time `k` in one run iff it does in the other. -/
lemma decides_congr {A : Protocol P I M O} {r r' : Run P I} {p : P} {k : ℕ} {d : O}
    (hin : r.input p = r'.input p) (hh : hist A r k p = hist A r' k p) (ha' : r'.Alive p k)
    (h : Decides A r p k d) : Decides A r' p k d := by
  rw [decides_iff] at h ⊢
  simp only [raw] at h ⊢
  refine ⟨ha', ?_, fun m' hm' => ?_⟩
  · rw [← hin, ← hh]; exact h.2.1
  · rw [← hin, ← hist_eq_of_le hm'.le hh]; exact h.2.2 m' hm'

/-! ### Truncated failure patterns -/

-- CSLib candidate (`Run.trunc`, `SolvesSim.decides_of_alive`, `Decides`, `Task`, `Solves*`)

/-- The failure pattern of `r` truncated after round `k`: crashes in rounds `> k` are removed. -/
def _root_.Cslib.SyncCrash.Run.trunc (r : Run P I) (k : ℕ) : Run P I where
  input := r.input
  crash p := (r.crash p).bind fun c => if c ≤ k then some c else none
  reach := r.reach

lemma trunc_crash_eq_some {r : Run P I} {k c : ℕ} {p : P} :
    (r.trunc k).crash p = some c ↔ r.crash p = some c ∧ c ≤ k := by
  simp only [Run.trunc]
  cases h : r.crash p with
  | none => simp
  | some c' =>
    simp only [Option.bind_some, Option.some.injEq]
    split_ifs with h1
    · simp only [Option.some.injEq]; constructor
      · rintro rfl; exact ⟨rfl, h1⟩
      · rintro ⟨rfl, -⟩; rfl
    · simp only [reduceCtorEq, false_iff, not_and]; rintro rfl; exact h1

lemma trunc_alive_iff {r : Run P I} {k m : ℕ} (hm : m ≤ k) {p : P} :
    (r.trunc k).Alive p m ↔ r.Alive p m := by
  simp only [Run.Alive, trunc_crash_eq_some]
  constructor
  · intro h c hc
    by_contra hlt
    exact absurd (h c ⟨hc, by omega⟩) (by omega)
  · intro h c hc; exact h c hc.1

lemma trunc_deliv_iff {r : Run P I} {k t : ℕ} (ht : t < k) {p q : P} :
    (r.trunc k).Deliv p q t ↔ r.Deliv p q t := by
  simp only [Run.Deliv, trunc_alive_iff (le_of_lt ht), trunc_crash_eq_some]
  simp only [Run.trunc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨⟨h.1, by omega⟩, h.2⟩⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨h.1.1, h.2⟩⟩

lemma trunc_faulty {r : Run P I} {k : ℕ} {p : P} (h : (r.trunc k).Faulty p) : r.Faulty p := by
  intro hn
  apply h
  simp [Run.trunc, hn]

/-- A process alive at time `k` is correct in the truncation at `k`. -/
lemma trunc_not_faulty {r : Run P I} {k : ℕ} {p : P} (h : r.Alive p k) :
    ¬ (r.trunc k).Faulty p := by
  intro hf
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hf
  rw [trunc_crash_eq_some] at hc
  exact absurd (h c hc.1) (by omega)

lemma Task.IsRun.trunc {T : Task P I O} {t : ℕ} {r : Run P I} (h : T.IsRun t r) (k : ℕ) :
    T.IsRun t (r.trunc k) := by
  refine ⟨⟨?_, fun p c hc => h.1.2 p c (trunc_crash_eq_some.1 hc).1⟩, h.2⟩
  refine le_trans (Finset.card_le_card ?_) h.1.1
  intro p
  simp only [Run.mem_faulty]
  exact trunc_faulty

lemma hist_trunc (A : Protocol P I M O) (r : Run P I) {k m : ℕ} (hm : m ≤ k) (p : P) :
    hist A (r.trunc k) m p = hist A r m p :=
  hist_congr (alg := A) (r := r.trunc k) (r' := r) (fun _ => rfl)
    (fun _ ht _ _ => trunc_deliv_iff ht) m hm p

lemma decides_trunc_iff {A : Protocol P I M O} {r : Run P I} {k m : ℕ} (hm : m ≤ k) {p : P}
    {d : O} : Decides A (r.trunc k) p m d ↔ Decides A r p m d := by
  simp only [decides_iff, raw, trunc_alive_iff hm]
  have hin : (r.trunc k).input p = r.input p := rfl
  rw [hin, hist_trunc A r hm]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun m' hm' => by
      rw [← hist_trunc A r (k := k) (m := m') (by omega)]; exact h3 m' hm'⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun m' hm' => by
      rw [hist_trunc A r (k := k) (m := m') (by omega)]; exact h3 m' hm'⟩

/-- In a protocol solving `T` within `k` rounds, every process alive at time `k` (not only the
nonfaulty ones) has decided by time `k`. -/
lemma SolvesWithin.decides_of_alive {A : Protocol P I M O} {T : Task P I O} {t k : ℕ}
    (hA : SolvesWithin A T t k) {r : Run P I} (hr : T.IsRun t r) {p : P} (hp : r.Alive p k) :
    ∃ m ≤ k, ∃ d, Decides A r p m d := by
  obtain ⟨m, hm, d, hd⟩ := hA.within _ (hr.trunc k) p (trunc_not_faulty hp)
  exact ⟨m, hm, d, (decides_trunc_iff hm).1 hd⟩

/-- **Key fact about simultaneous protocols**: if some process decides at time `k`, then every
process alive at time `k` (even one that crashes later) decides at time `k`. -/
lemma SolvesSim.decides_of_alive {A : Protocol P I M O} {T : Task P I O} {t : ℕ}
    (hA : SolvesSim A T t) {r : Run P I} (hr : T.IsRun t r) {p q : P} {k : ℕ} {d : O}
    (hp : Decides A r p k d) (hq : r.Alive q k) : ∃ d', Decides A r q k d' := by
  have hr' := hr.trunc k
  obtain ⟨m, d', hd'⟩ := hA.complete _ hr' q (trunc_not_faulty hq)
  have hp' : Decides A (r.trunc k) p k d := (decides_trunc_iff le_rfl).2 hp
  have := hA.simultaneous _ hr' p q k m d d' hp' hd'
  subst this
  exact ⟨d', (decides_trunc_iff le_rfl).1 hd'⟩

lemma Task.IsRun.exists_correct {T : Task P I O} {t : ℕ} {r : Run P I} (hr : T.IsRun t r)
    (ht : t < Fintype.card P) : ∃ p, ¬ r.Faulty p :=
  hr.1.exists_correct ht

/-! ### Waste (§4) -/

-- CSLib candidate (`Run.exposed`, `Run.waste`, `waste_lt`)

/-- The failure of `p` is exposed in round `j ≥ 1`: the round-`j` message from `p` to some
process `q` that survives round `j` is missing in the failure pattern. -/
def _root_.Cslib.SyncCrash.Run.ExposedIn (r : Run P I) (p : P) (j : ℕ) : Prop :=
  1 ≤ j ∧ ∃ q, r.Alive q j ∧ ¬ r.Deliv p q (j - 1)

open Classical in
/-- `E(F, k)`: the number of processes whose failure is exposed in round `k` or earlier. -/
noncomputable def _root_.Cslib.SyncCrash.Run.exposed (r : Run P I) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun p => ∃ j ≤ k, r.ExposedIn p j).card

/-- The waste `W(F) = max_{k ≥ 0} (E(F, k) − k)`. Since `E(F, 0) = 0` and `E(F, k) ≤ n`, the
maximum over `k ≤ n` with truncated subtraction is the paper's maximum. -/
noncomputable def _root_.Cslib.SyncCrash.Run.waste (r : Run P I) : ℕ :=
  (Finset.range (Fintype.card P + 1)).sup fun k => r.exposed k - k

/-- Round `k` is premature in the run `r` (w.r.t. the bound `t`): `k < t + 1 − W(F)`. -/
def Premature (r : Run P I) (t k : ℕ) : Prop := k + r.waste < t + 1

lemma ExposedIn.faulty {r : Run P I} {p : P} {j : ℕ} (h : r.ExposedIn p j) : r.Faulty p := by
  obtain ⟨-, q, -, hq⟩ := h
  by_contra hn
  exact hq (Run.deliv_of_not_faulty hn q _)

lemma exposed_le_faulty (r : Run P I) (k : ℕ) : r.exposed k ≤ r.faulty.card := by
  classical
  unfold Run.exposed
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  obtain ⟨j, -, hj⟩ := hp
  simpa using ExposedIn.faulty hj

@[simp] lemma exposed_zero (r : Run P I) : r.exposed 0 = 0 := by
  classical
  unfold Run.exposed
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies]
  rintro p ⟨j, hj, h1, -⟩; omega

lemma card_le_exposed {r : Run P I} {k : ℕ} (s : Finset P)
    (h : ∀ p ∈ s, ∃ j ≤ k, r.ExposedIn p j) : s.card ≤ r.exposed k := by
  classical
  unfold Run.exposed
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h p hp

lemma exists_pair_of_two_le_exposed {r : Run P I} {k : ℕ} (h : 2 ≤ r.exposed k) :
    ∃ a b, a ≠ b ∧ (∃ j ≤ k, r.ExposedIn a j) ∧ (∃ j ≤ k, r.ExposedIn b j) := by
  classical
  unfold Run.exposed at h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (lt_of_lt_of_le one_lt_two h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact ⟨a, b, hab, ha, hb⟩

/-- `W(F) < t` when `t ≥ 1` (the paper: `0 ≤ W(F) ≤ t − 1`). -/
lemma waste_lt {r : Run P I} {t : ℕ} (hr : r.Admissible t) (ht : 1 ≤ t) : r.waste < t := by
  unfold Run.waste
  rw [Finset.sup_lt_iff (show (⊥ : ℕ) < t by simp; omega)]
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp; omega
  · have := (exposed_le_faulty r k).trans hr.1; omega

/-- With `t ≥ 1`, round `1` is premature in every run. -/
lemma premature_one {r : Run P I} {t : ℕ} (hr : r.Admissible t) (ht : 1 ≤ t) :
    Premature r t 1 := by
  have := waste_lt hr ht; unfold Premature; omega

lemma le_waste (r : Run P I) {k : ℕ} (hk : k ≤ Fintype.card P) :
    r.exposed k - k ≤ r.waste :=
  Finset.le_sup (f := fun k => r.exposed k - k) (Finset.mem_range.2 (by omega))

end Podc.SimultaneousAllCaseOptimal
