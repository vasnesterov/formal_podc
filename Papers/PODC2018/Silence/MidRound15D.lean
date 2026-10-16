import Papers.PODC2018.Silence.MidRound
import Podc.SyncCrash.Floodset

/-!
# The 1.5D protocol (Figure 5 of Goren–Moses, Appendix D)

An AC protocol for `γ̃_f` in which all processes commit in the middle of round 2 of the nice run,
with `n(n − 1) + n f = n² + n f − n` messages — matching Corollary 6.

* Round 1: every process with value `1` sends `'1'` to all.
* Round 2 (`ok` = value `1` and `'1'` received from all others): an `ok` process sends `all[1]` to
  its `f` designated successors `nb i` (in the paper `{i + 1, …, i + f} mod n`) and then commits
  (mid-round); other processes send `huh?` to all.
* A process that sent or received `huh?` takes part in a biased-to-1 consensus, starting with `1`
  iff it committed or received `all[1]`. The consensus is the max-floodset of
  `Podc.SyncCrash.Floodset` run for `f` rounds (rounds `3 … f + 2`); an uncommitted participant
  decides at time `f + 2` (commit iff it holds `1`).

Messages: `true` = `'1'` / `all[1]` / consensus `1`, `false` = `huh?` (the two kinds of round-2
messages must be distinguishable, see `differencies`: the paper's 1-bit encoding of `huh?` breaks
the protocol).
-/

namespace Papers.PODC2018.Silence.MidRound.OnePointFive

open Podc.SyncCrash Classical

variable {P : Type*} [Fintype P]

abbrev H (P : Type*) := Cslib.Byzantine.LockStep.History P Bool

/-- Value `1` and `'1'` from every other process in round 1. -/
def ok (p : P) (x : Bool) (h : H P) : Prop := x = true ∧ ∀ j, j ≠ p → rcv h 0 j ≠ none

/-- Received `huh?` in round 2. -/
def huhRcv (h : H P) : Prop := ∃ j, rcv h 1 j = some false

/-- Received `all[1]` in round 2. -/
def all1Rcv (h : H P) : Prop := ∃ j, rcv h 1 j = some true

/-- Takes part in the consensus. -/
def part (p : P) (x : Bool) (h : H P) : Prop := ¬ ok p x h ∨ huhRcv h

/-- Consensus value: `1` iff committed or received `all[1]`, or received a `1` in a consensus
round so far. -/
def val (p : P) (x : Bool) (h : H P) : Prop :=
  (ok p x h ∨ all1Rcv h) ∨ ∃ t', 2 ≤ t' ∧ t' < h.length ∧ ∃ j, rcv h t' j ≠ none

variable (f : ℕ) (nb : P → Finset P)

/-- The 1.5D protocol with successor sets `nb`. -/
noncomputable def alg : ACProtocol P Bool where
  send p x h q :=
    if h.length = 0 then (if x = true then some true else none)
    else if h.length = 1 then
      (if ok p x h then (if q ∈ nb p then some true else none) else some false)
    else if h.length < f + 2 then (if part p x h ∧ val p x h then some true else none)
    else none
  decide p x h :=
    if h.length = 1 ∧ ok p x h then some .commit
    else if h.length = f + 2 ∧ ¬ ok p x h then
      (if val p x h then some .commit else some .abort)
    else none

lemma send_def (p : P) (x : Bool) (h : H P) (q : P) : (alg f nb).send p x h q =
    if h.length = 0 then (if x = true then some true else none)
    else if h.length = 1 then
      (if ok p x h then (if q ∈ nb p then some true else none) else some false)
    else if h.length < f + 2 then (if part p x h ∧ val p x h then some true else none)
    else none := rfl

lemma decide_def (p : P) (x : Bool) (h : H P) : (alg f nb).decide p x h =
    if h.length = 1 ∧ ok p x h then some .commit
    else if h.length = f + 2 ∧ ¬ ok p x h then
      (if val p x h then some .commit else some .abort)
    else none := rfl

variable {f nb} {r : Run P Bool}

/-! ### Semantic versions of the local predicates -/

/-- `ok`, read off the run. -/
def okR (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  r.input p = true ∧ ∀ j, j ≠ p → Sent (alg f nb) r j p 0

def huhR (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  ∃ j, msg (alg f nb) r j p 1 = some false

def all1R (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  ∃ j, msg (alg f nb) r j p 1 = some true

/-- Consensus participants. -/
def part0 (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  ¬ okR f nb r p ∨ huhR f nb r p

/-- Initial consensus values. -/
def v0 (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  okR f nb r p ∨ all1R f nb r p

lemma ok_hist {p : P} {m : ℕ} (hm : 1 ≤ m) :
    ok p (r.input p) (hist (alg f nb) r m p) ↔ okR f nb r p := by
  simp only [ok, okR, rcv_hist r p _ (show 0 < m by omega), Sent]

lemma huh_hist {p : P} {m : ℕ} (hm : 2 ≤ m) :
    huhRcv (hist (alg f nb) r m p) ↔ huhR f nb r p := by
  simp only [huhRcv, huhR, rcv_hist r p _ (show 1 < m by omega)]

lemma all1_hist {p : P} {m : ℕ} (hm : 2 ≤ m) :
    all1Rcv (hist (alg f nb) r m p) ↔ all1R f nb r p := by
  simp only [all1Rcv, all1R, rcv_hist r p _ (show 1 < m by omega)]

lemma part_hist {p : P} {m : ℕ} (hm : 2 ≤ m) :
    part p (r.input p) (hist (alg f nb) r m p) ↔ part0 f nb r p := by
  rw [part, part0, ok_hist (by omega), huh_hist hm]

lemma val_hist {p : P} {m : ℕ} (hm : 2 ≤ m) :
    val p (r.input p) (hist (alg f nb) r m p) ↔ floodVal (alg f nb) r 2 (v0 f nb r) p m := by
  rw [val, floodVal, v0, ok_hist (by omega), all1_hist hm, length_hist]
  apply or_congr_right
  constructor
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rwa [rcv_hist r p _ h2] at hj⟩
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rwa [rcv_hist r p _ h2]⟩

/-! ### Messages -/

lemma sent0 {j p : P} : Sent (alg f nb) r j p 0 ↔ j ≠ p ∧ r.Deliv j p 0 ∧ r.input j = true := by
  rw [sent_iff_deliv, send_def]; simp only [length_hist]; simp

lemma msg1 (j p : P) : msg (alg f nb) r j p 1 =
    if j ≠ p ∧ r.Deliv j p 1 then
      (if okR f nb r j then (if p ∈ nb j then some true else none) else some false)
    else none := by
  rw [msg_eq_deliv, send_def]
  simp only [length_hist, one_ne_zero, if_false, if_true, ok_hist (le_refl 1)]

lemma sent_cons {y z : P} {t : ℕ} (h2 : 2 ≤ t) (hf : t < f + 2) :
    Sent (alg f nb) r y z t ↔
      y ≠ z ∧ r.Deliv y z t ∧ part0 f nb r y ∧ floodVal (alg f nb) r 2 (v0 f nb r) y t := by
  rw [sent_iff_deliv, send_def]
  simp only [length_hist]
  rw [if_neg (by omega), if_neg (by omega), if_pos hf, ← part_hist h2, ← val_hist h2]
  by_cases hc : part y (r.input y) (hist (alg f nb) r t y) ∧
      val y (r.input y) (hist (alg f nb) r t y)
  · rw [if_pos hc]; simp [hc.1, hc.2]
  · rw [if_neg hc]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]
    rintro ⟨-, -, h1, h2⟩; exact hc ⟨h1, h2⟩

lemma not_sent_late {y z : P} {t : ℕ} (ht : f + 2 ≤ t) : ¬ Sent (alg f nb) r y z t := by
  rw [sent_iff_deliv, send_def]
  simp only [length_hist]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp

lemma floodRounds : FloodRounds (alg f nb) r 2 f (part0 f nb r) (v0 f nb r) :=
  fun _ h1 h2 _ _ => sent_cons h1 (by omega)

/-- Mid-round decisions of 1.5D. -/
lemma decidesMid_iff (hf : 1 ≤ f) {p : P} {m : ℕ} {d : Decision} :
    DecidesMid (alg f nb) r p m d ↔
      r.Alive p m ∧
      (∀ q, q ≠ p → (alg f nb).send p (r.input p) (hist (alg f nb) r m p) q ≠ none →
        r.Deliv p q m) ∧
      ((m = 1 ∧ okR f nb r p ∧ d = .commit) ∨
       (m = f + 2 ∧ ¬ okR f nb r p ∧
        d = if floodVal (alg f nb) r 2 (v0 f nb r) p (f + 2) then .commit else .abort)) := by
  unfold DecidesMid
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  rw [decide_def]
  simp only [length_hist]
  by_cases h1 : m = 1
  · subst h1
    rw [ok_hist le_rfl]
    by_cases hok : okR f nb r p
    · simp [hok, eq_comm]
    · simp [hok]
  · by_cases h3 : m = f + 2
    · subst h3
      rw [ok_hist (by omega), val_hist (by omega)]
      by_cases hok : okR f nb r p
      · simp [hok, h1]
      · by_cases hv : floodVal (alg f nb) r 2 (v0 f nb r) p (f + 2)
        · simp [hok, hv, h1, eq_comm]
        · simp [hok, hv, h1, eq_comm]
    · simp [h1, h3]

/-- An `ok` process certifies that all inputs are `1`. -/
lemma all_one_of_okR {p : P} (h : okR f nb r p) (j : P) : r.input j = true := by
  by_cases hj : j = p
  · subst hj; exact h.1
  · exact (sent0.1 (h.2 j hj)).2.2

lemma exists_okR_of_v0 {p : P} (h : v0 f nb r p) : ∃ x, okR f nb r x := by
  rcases h with h | ⟨j, hj⟩
  · exact ⟨p, h⟩
  · refine ⟨j, ?_⟩
    rw [msg1] at hj
    by_contra hok
    split_ifs at hj <;> simp_all

/-- **1.5D solves AC in `γ̃_f`** (Claim 8 of Goren–Moses), for `1 ≤ f < n` and successor sets
`nb i` of `f` processes other than `i`. -/
theorem solvesACMid (hf : 1 ≤ f) (hnb : ∀ i, i ∉ nb i) (hcard : ∀ i, (nb i).card = f) :
    SolvesACMid (alg f nb) f := by
  intro r hr
  have hF := floodRounds (r := r) (f := f) (nb := nb)
  -- a consensus value `1` certifies `all[1]`
  have commit_valid : ∀ p, ¬ okR f nb r p →
      floodVal (alg f nb) r 2 (v0 f nb r) p (f + 2) → ∀ j, r.input j = true := by
    intro p hp hv
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    have h0 : ∀ y, part0 f nb r y → ¬ v0 f nb r y := fun y _ hy => by
      obtain ⟨x, hx⟩ := exists_okR_of_v0 hy
      exact hj (all_one_of_okR hx j)
    exact FloodRounds.not_val hF h0 (f + 2) (by omega) p (Or.inl hp) hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Decision
    intro i hi
    by_cases hok : okR f nb r i
    · exact ⟨1, .commit, (decidesMid_iff hf).2 ⟨Run.alive_of_not_faulty hi 1,
        fun q _ _ => Run.deliv_of_not_faulty hi q 1, Or.inl ⟨rfl, hok, rfl⟩⟩⟩
    · exact ⟨f + 2, _, (decidesMid_iff hf).2 ⟨Run.alive_of_not_faulty hi _,
        fun q _ _ => Run.deliv_of_not_faulty hi q _, Or.inr ⟨rfl, hok, rfl⟩⟩⟩
  · -- Agreement
    have no_abort : ∀ u m, DecidesMid (alg f nb) r u m .abort →
        ∀ i m', ¬ DecidesMid (alg f nb) r i m' .commit := by
      intro u m hab i m' hc
      rw [decidesMid_iff hf] at hab hc
      rcases hab with ⟨hau, -, ⟨-, -, h⟩ | ⟨rfl, hnu, hd⟩⟩
      · cases h
      by_cases hvu : floodVal (alg f nb) r 2 (v0 f nb r) u (f + 2)
      · rw [if_pos hvu] at hd; cases hd
      apply hvu
      rcases hc with ⟨hai, hdel, ⟨rfl, hoki, -⟩ | ⟨rfl, hni, hd'⟩⟩
      · -- `i` committed in mid-round 2: `{i} ∪ nb i` contains a correct process
        obtain ⟨c, hcG, hcc⟩ : ∃ c ∈ insert i (nb i), ¬ r.Faulty c := by
          by_contra hno
          push Not at hno
          have : insert i (nb i) ⊆ r.faulty := fun c hc => by rw [Run.mem_faulty]; exact hno c hc
          have := (Finset.card_le_card this).trans hr.1
          rw [Finset.card_insert_of_notMem (hnb i), hcard] at this
          omega
        have hv0c : v0 f nb r c := by
          rcases Finset.mem_insert.1 hcG with rfl | hcn
          · exact Or.inl hoki
          · refine Or.inr ⟨i, ?_⟩
            have hci : i ≠ c := fun h => hnb i (h ▸ hcn)
            have hsend : (alg f nb).send i (r.input i) (hist (alg f nb) r 1 i) c ≠ none := by
              rw [send_def]; simp only [length_hist]
              rw [ok_hist le_rfl]; simp [hoki, hcn]
            rw [msg1, if_pos ⟨hci, hdel c (Ne.symm hci) hsend⟩, if_pos hoki, if_pos hcn]
        by_cases hcu : c = u
        · subst hcu; exact Or.inl hv0c
        have hpc : part0 f nb r c := by
          refine Or.inr ⟨u, ?_⟩
          rw [msg1, if_pos ⟨Ne.symm hcu, ⟨hau.mono (by omega), fun h => by
            have := hau _ h.1; omega⟩⟩, if_neg hnu]
        exact FloodRounds.val_of_correct hF (by omega) hpc hv0c hcc u (by omega)
      · -- both decided by consensus: uniform agreement after a clean round
        by_cases hvi : floodVal (alg f nb) r 2 (v0 f nb r) i (f + 2)
        · have hall := commit_valid i hni hvi
          -- `u` missed a round-1 message: a crash in round 1
          have : ∃ j, j ≠ u ∧ ¬ Sent (alg f nb) r j u 0 := by
            by_contra hno; push Not at hno; exact hnu ⟨hall u, hno⟩
          obtain ⟨j, hju, hjs⟩ := this
          have hj1 : r.crash j = some 1 := by
            have hnd : ¬ r.Deliv j u 0 := fun hd => hjs (sent0.2 ⟨hju, hd, hall j⟩)
            cases hcj : r.crash j with
            | none => exact absurd (Run.deliv_of_not_faulty (by simp [Run.Faulty, hcj]) u 0) hnd
            | some c =>
              have := hr.2 j c hcj
              by_contra hne
              apply hnd
              refine ⟨fun c' hc' => ?_, fun h => ?_⟩
              · rw [hcj] at hc'; cases hc'; omega
              · rw [hcj] at h; apply hne; rw [h.1]
          obtain ⟨t₀, h1, h2, hcl⟩ := exists_clean_round r (T := 2) (R := f) (by
            have hsub : Finset.univ.filter (fun p => ∃ c, r.crash p = some c ∧ 2 < c ∧
                c ≤ 2 + f) ⊆ r.faulty.erase j := by
              intro p hp
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
              obtain ⟨c, hc, h2c, -⟩ := hp
              rw [Finset.mem_erase, Run.mem_faulty]
              refine ⟨fun h => ?_, by simp [Run.Faulty, hc]⟩
              subst h; rw [hj1] at hc; cases hc; omega
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem (by rw [Run.mem_faulty]; simp [Run.Faulty, hj1])] at this
            have := hr.1
            omega)
          have := FloodRounds.agree hF h1 (by omega) hcl (Or.inl hni) (Or.inl hnu)
            (by simpa [add_comm] using hai) (by simpa [add_comm] using hvi)
          simpa [add_comm] using this
        · rw [if_neg hvi] at hd'; cases hd'
    intro i m d i' m' d' h h'
    cases d <;> cases d'
    · rfl
    · exact absurd h (no_abort i' m' h' i m)
    · exact absurd h' (no_abort i m h i' m')
    · rfl
  · -- Commit Validity
    intro i m h j
    rw [decidesMid_iff hf] at h
    rcases h with ⟨-, -, ⟨-, hok, -⟩ | ⟨-, hn, hd⟩⟩
    · exact all_one_of_okR hok j
    · by_cases hv : floodVal (alg f nb) r 2 (v0 f nb r) i (f + 2)
      · exact commit_valid i hn hv j
      · rw [if_neg hv] at hd; cases hd
  · -- Abort Validity
    intro i m h
    by_contra hc
    push Not at hc
    obtain ⟨hin, hnf⟩ := hc
    rw [decidesMid_iff hf] at h
    rcases h with ⟨-, -, ⟨-, -, h⟩ | ⟨-, hn, -⟩⟩
    · cases h
    apply hn
    refine ⟨by simpa using hin i, fun j hji => sent0.2 ⟨hji, Run.deliv_of_not_faulty (by
      simpa [Run.Faulty] using hnf j) i 0, by simpa using hin j⟩⟩

/-! ### The nice run -/

lemma nice_okR (p : P) : okR f nb nice p :=
  ⟨rfl, fun j hj => sent0.2 ⟨hj, Run.deliv_of_not_faulty (nice_not_faulty j) p 0, rfl⟩⟩

/-- **Claim 7** of Goren–Moses: in the nice run every process commits in the middle of round 2… -/
theorem nice_commit (hf : 1 ≤ f) (p : P) : DecidesMid (alg f nb) nice p 1 .commit :=
  (decidesMid_iff hf).2 ⟨nice_alive p 1, fun q _ _ => Run.deliv_of_not_faulty (nice_not_faulty p) q 1,
    Or.inl ⟨rfl, nice_okR p, rfl⟩⟩

/-- … and exactly `n(n − 1) + Σ |nb i| = n² + n f − n` messages are sent. -/
theorem nice_msgs (hnb : ∀ i, i ∉ nb i) (hcard : ∀ i, (nb i).card = f) :
    (msgs (alg f nb) nice).encard =
      (Fintype.card P * (Fintype.card P - 1) + f * Fintype.card P : ℕ) := by
  let D1 : Finset (P × P × ℕ) := (Finset.univ : Finset P).offDiag.image (fun e => (e.1, e.2, 0))
  let D2 : Finset (P × P × ℕ) := Finset.univ.biUnion (fun i => (nb i).image (fun q => (i, q, 1)))
  have hset : msgs (alg f nb) nice = ((D1 ∪ D2 : Finset (P × P × ℕ)) : Set (P × P × ℕ)) := by
    ext ⟨a, b, t⟩
    simp only [msgs, Set.mem_setOf_eq, Finset.coe_union, Set.mem_union, Finset.mem_coe, D1, D2,
      Finset.mem_image, Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Prod.mk.injEq]
    constructor
    · intro h
      rcases (show t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t < f + 2) ∨ f + 2 ≤ t by omega)
        with rfl | rfl | ⟨h2, h3⟩ | ht
      · exact Or.inl ⟨(a, b), h.ne, rfl, rfl, rfl⟩
      · have : msg (alg f nb) nice a b 1 ≠ none := h
        rw [msg1] at this
        right
        refine ⟨a, b, ?_, rfl, rfl, rfl⟩
        by_contra hb
        split_ifs at this <;> simp_all [nice_okR]
      · obtain ⟨-, -, hp, -⟩ := (sent_cons h2 h3).1 h
        rcases hp with hp | ⟨j, hj⟩
        · exact absurd (nice_okR a) hp
        · rw [msg1] at hj; split_ifs at hj <;> simp_all [nice_okR]
      · exact absurd h (not_sent_late ht)
    · rintro (⟨⟨a', b'⟩, hab, rfl, rfl, rfl⟩ | ⟨i, q, hq, rfl, rfl, rfl⟩)
      · exact sent0.2 ⟨hab, Run.deliv_of_not_faulty (nice_not_faulty _) _ 0, rfl⟩
      · show msg (alg f nb) nice i q 1 ≠ none
        have hiq : i ≠ q := fun h => hnb i (h ▸ hq)
        rw [msg1, if_pos ⟨hiq, Run.deliv_of_not_faulty (nice_not_faulty _) _ 1⟩,
          if_pos (nice_okR i), if_pos hq]
        simp
  have hD1 : D1.card = Fintype.card P * (Fintype.card P - 1) := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by
      simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 hab.2.1), Finset.offDiag_card,
      Finset.card_univ, Nat.mul_sub_one]
  have hD2 : D2.card = f * Fintype.card P := by
    rw [Finset.card_biUnion]
    · have : ∀ i, ((nb i).image (fun q => (i, q, 1))).card = f := by
        intro i
        rw [Finset.card_image_of_injective _ (fun b c hbc => by
          simp only [Prod.mk.injEq] at hbc; exact hbc.2.1), hcard]
      simp [this, mul_comm]
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e hea heb
      simp only [Finset.mem_image] at hea heb
      obtain ⟨x, -, rfl⟩ := hea
      obtain ⟨y, -, hy⟩ := heb
      exact hab (congrArg Prod.fst hy).symm
  have hdisj : Disjoint D1 D2 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [D1, D2, Finset.mem_image, Finset.mem_biUnion] at h1 h2
    obtain ⟨_, -, rfl⟩ := h1
    obtain ⟨_, -, _, -, hy⟩ := h2
    simp at hy
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_union_of_disjoint hdisj, hD1, hD2]

/-- Successor sets as required exist whenever `f < n` (non-vacuity of the hypotheses). -/
lemma exists_nb (hfn : f < Fintype.card P) :
    ∃ nb : P → Finset P, (∀ i, i ∉ nb i) ∧ ∀ i, (nb i).card = f := by
  have : ∀ i : P, ∃ s : Finset P, s ⊆ Finset.univ.erase i ∧ s.card = f := by
    intro i
    have hle : f ≤ (Finset.univ.erase i).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
    exact Finset.exists_subset_card_eq hle
  choose nb' hnb' hcard' using this
  refine ⟨nb', fun i h => ?_, hcard'⟩
  simpa using hnb' i h

/-- **Corollary 6 is tight**: for every `2 ≤ f < n` there is an AC protocol for `γ̃_f` in which all
processes commit before time 2 of the nice run, using exactly `n² + n f − n` messages. -/
theorem corollary6_tight (hf : 2 ≤ f) (hfn : f < Fintype.card P) :
    ∃ nb : P → Finset P, SolvesACMid (alg f nb) f ∧
      (∀ p, DecidesMid (alg f nb) nice p 1 .commit) ∧
      (msgs (alg f nb) nice).encard =
        (Fintype.card P * (Fintype.card P - 1) + f * Fintype.card P : ℕ) := by
  obtain ⟨nb, hnb, hcard⟩ := exists_nb hfn
  exact ⟨nb, solvesACMid (by omega) hnb hcard, nice_commit (by omega), nice_msgs hnb hcard⟩

end Papers.PODC2018.Silence.MidRound.OnePointFive
