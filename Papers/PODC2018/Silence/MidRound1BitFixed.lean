import Papers.PODC2018.Silence.MidRound1Bit

/-!
# The 1-bit implementation of 1.5D with silence-as-`huh?` decoding is correct

The paper does not say how a receiver decodes the 1-bit `huh?` ("quiet to `{i+1, …, i+f}`, `1` to
the rest"). `MidRound1Bit.lean` shows that ignoring silence breaks the protocol. Here a process `p`
also reads `huh?` from `j` when `p ∈ nb j` and `p` got *no* round-2 message from `j` (an `ok` `j`
would have sent `all[1]` to `p`). With this decoding the 1-bit protocol solves AC in `γ̃_f`
(`solvesACMid`): the proof of `MidRound15D.lean` goes through, the only change being how a correct
process `c` that knows `all[1]` learns that an uncommitted `u` needs help (a `1` from `u` if
`c ∉ nb u`, silence from `u` if `c ∈ nb u`).
-/

namespace Papers.PODC2018.Silence.MidRound.OneBitFixed

open Cslib.SyncCrash Classical
open Papers.PODC2018.Silence.MidRound.OnePointFive (ok H)
open Papers.PODC2018.Silence.MidRound.OneBit (huh1 all11 val1)

variable {P : Type*} [Fintype P]

/-- Silence from a predecessor `j` (`p ∈ nb j`) in round 2, decoded as `huh?`. -/
def huhSil (nb : P → Finset P) (p : P) (h : H P) : Prop :=
  ∃ j, j ≠ p ∧ p ∈ nb j ∧ rcv h 1 j = none

/-- Participation with silence-as-`huh?` decoding. -/
def part2 (nb : P → Finset P) (p : P) (x : Bool) (h : H P) : Prop :=
  ¬ ok p x h ∨ huh1 nb p h ∨ huhSil nb p h

/-- The 1-bit 1.5D protocol with silence-as-`huh?` decoding. -/
noncomputable def alg1' (f : ℕ) (nb : P → Finset P) : ACProtocol P Bool where
  send p x h q :=
    if h.length = 0 then (if x = true then some true else none)
    else if h.length = 1 then
      (if ok p x h then (if q ∈ nb p then some true else none)
       else (if q ∉ nb p then some true else none))
    else if h.length < f + 2 then (if part2 nb p x h ∧ val1 nb p x h then some true else none)
    else none
  decide p x h :=
    if h.length = 1 ∧ ok p x h then some .commit
    else if h.length = f + 2 ∧ ¬ ok p x h then
      (if val1 nb p x h then some .commit else some .abort)
    else none

variable {f : ℕ} {nb : P → Finset P}

lemma send_def' (p : P) (x : Bool) (h : H P) (q : P) : (alg1' f nb).send p x h q =
    if h.length = 0 then (if x = true then some true else none)
    else if h.length = 1 then
      (if ok p x h then (if q ∈ nb p then some true else none)
       else (if q ∉ nb p then some true else none))
    else if h.length < f + 2 then (if part2 nb p x h ∧ val1 nb p x h then some true else none)
    else none := rfl

lemma decide_def (p : P) (x : Bool) (h : H P) : (alg1' f nb).decide p x h =
    if h.length = 1 ∧ ok p x h then some .commit
    else if h.length = f + 2 ∧ ¬ ok p x h then
      (if val1 nb p x h then some .commit else some .abort)
    else none := rfl

variable {r : Run P Bool}

def okR (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  r.input p = true ∧ ∀ j, j ≠ p → Sent (alg1' f nb) r j p 0

def huhR (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  ∃ j, msg (alg1' f nb) r j p 1 ≠ none ∧ p ∉ nb j

def silR (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  ∃ j, j ≠ p ∧ p ∈ nb j ∧ msg (alg1' f nb) r j p 1 = none

def all1R (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  ∃ j, msg (alg1' f nb) r j p 1 ≠ none ∧ p ∈ nb j

def part0 (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  ¬ okR f nb r p ∨ huhR f nb r p ∨ silR f nb r p

def v0 (f : ℕ) (nb : P → Finset P) (r : Run P Bool) (p : P) : Prop :=
  okR f nb r p ∨ all1R f nb r p

lemma ok_hist {p : P} {m : ℕ} (hm : 1 ≤ m) :
    ok p (r.input p) (hist (alg1' f nb) r m p) ↔ okR f nb r p := by
  simp only [ok, okR, rcv_hist r p _ (show 0 < m by omega), Sent]

lemma part_hist {p : P} {m : ℕ} (hm : 2 ≤ m) :
    part2 nb p (r.input p) (hist (alg1' f nb) r m p) ↔ part0 f nb r p := by
  simp only [part2, part0, ok_hist (show 1 ≤ m by omega), huh1, huhR, huhSil, silR,
    rcv_hist r p _ (show 1 < m by omega)]

lemma val_hist {p : P} {m : ℕ} (hm : 2 ≤ m) :
    val1 nb p (r.input p) (hist (alg1' f nb) r m p) ↔
      floodVal (alg1' f nb) r 2 (v0 f nb r) p m := by
  rw [val1, floodVal, v0, ok_hist (by omega), length_hist]
  simp only [all11, all1R, rcv_hist r p _ (show 1 < m by omega)]
  apply or_congr_right
  constructor
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rwa [rcv_hist r p _ h2] at hj⟩
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rwa [rcv_hist r p _ h2]⟩

lemma sent0 {j p : P} : Sent (alg1' f nb) r j p 0 ↔ j ≠ p ∧ r.Deliv j p 0 ∧ r.input j = true := by
  rw [sent_iff_deliv, send_def']; simp only [length_hist]; simp

lemma msg1 (j p : P) : msg (alg1' f nb) r j p 1 =
    if j ≠ p ∧ r.Deliv j p 1 then
      (if okR f nb r j then (if p ∈ nb j then some true else none)
       else (if p ∉ nb j then some true else none))
    else none := by
  rw [msg_eq_deliv, send_def']
  simp only [length_hist, one_ne_zero, ite_false, ite_true, ok_hist (le_refl 1)]

lemma sent_cons {y z : P} {t : ℕ} (h2 : 2 ≤ t) (hf : t < f + 2) :
    Sent (alg1' f nb) r y z t ↔
      y ≠ z ∧ r.Deliv y z t ∧ part0 f nb r y ∧ floodVal (alg1' f nb) r 2 (v0 f nb r) y t := by
  rw [sent_iff_deliv, send_def']
  simp only [length_hist]
  rw [if_neg (by omega), if_neg (by omega), if_pos hf, ← part_hist h2, ← val_hist h2]
  by_cases hc : part2 nb y (r.input y) (hist (alg1' f nb) r t y) ∧
      val1 nb y (r.input y) (hist (alg1' f nb) r t y)
  · rw [if_pos hc]; simp [hc.1, hc.2]
  · rw [if_neg hc]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]
    rintro ⟨-, -, h1, h2⟩; exact hc ⟨h1, h2⟩

lemma floodRounds : FloodRounds (alg1' f nb) r 2 f (part0 f nb r) (v0 f nb r) :=
  fun _ h1 h2 _ _ => sent_cons h1 (by omega)

lemma decidesMid_iff (hf : 1 ≤ f) {p : P} {m : ℕ} {d : Decision} :
    DecidesMid (alg1' f nb) r p m d ↔
      r.Alive p m ∧
      (∀ q, q ≠ p → (alg1' f nb).send p (r.input p) (hist (alg1' f nb) r m p) q ≠ none →
        r.Deliv p q m) ∧
      ((m = 1 ∧ okR f nb r p ∧ d = .commit) ∨
       (m = f + 2 ∧ ¬ okR f nb r p ∧
        d = if floodVal (alg1' f nb) r 2 (v0 f nb r) p (f + 2) then .commit else .abort)) := by
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
      · by_cases hv : floodVal (alg1' f nb) r 2 (v0 f nb r) p (f + 2)
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
    obtain ⟨hj, hpn⟩ := hj
    rw [msg1] at hj
    by_contra hok
    split_ifs at hj <;> simp_all

/-- **The 1-bit 1.5D protocol with silence-as-`huh?` decoding solves AC in `γ̃_f`**, for `1 ≤ f < n`
and successor sets `nb i` of `f` processes other than `i`. -/
theorem solvesACMid (hf : 1 ≤ f) (hnb : ∀ i, i ∉ nb i) (hcard : ∀ i, (nb i).card = f) :
    SolvesACMid (alg1' f nb) f := by
  intro r hr
  have hF := floodRounds (r := r) (f := f) (nb := nb)
  -- a consensus value `1` certifies `all[1]`
  have commit_valid : ∀ p, ¬ okR f nb r p →
      floodVal (alg1' f nb) r 2 (v0 f nb r) p (f + 2) → ∀ j, r.input j = true := by
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
    have no_abort : ∀ u m, DecidesMid (alg1' f nb) r u m .abort →
        ∀ i m', ¬ DecidesMid (alg1' f nb) r i m' .commit := by
      intro u m hab i m' hc
      rw [decidesMid_iff hf] at hab hc
      rcases hab with ⟨hau, -, ⟨-, -, h⟩ | ⟨rfl, hnu, hd⟩⟩
      · cases h
      by_cases hvu : floodVal (alg1' f nb) r 2 (v0 f nb r) u (f + 2)
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
            have hsend : (alg1' f nb).send i (r.input i) (hist (alg1' f nb) r 1 i) c ≠ none := by
              rw [send_def']; simp only [length_hist]
              rw [ok_hist le_rfl]; simp [hoki, hcn]
            refine ⟨?_, hcn⟩
            rw [msg1, if_pos ⟨hci, hdel c (Ne.symm hci) hsend⟩, if_pos hoki, if_pos hcn]
            simp
        by_cases hcu : c = u
        · subst hcu; exact Or.inl hv0c
        have hdu : r.Deliv u c 1 := ⟨hau.mono (by omega), fun h => by
            have := hau _ h.1; omega⟩
        have hpc : part0 f nb r c := by
          by_cases hcn : c ∈ nb u
          · refine Or.inr (Or.inr ⟨u, Ne.symm hcu, hcn, ?_⟩)
            rw [msg1, if_pos ⟨Ne.symm hcu, hdu⟩, if_neg hnu, if_neg (not_not.2 hcn)]
          · refine Or.inr (Or.inl ⟨u, ?_, hcn⟩)
            rw [msg1, if_pos ⟨Ne.symm hcu, hdu⟩, if_neg hnu, if_pos hcn]
            simp
        exact FloodRounds.val_of_correct hF (by omega) hpc hv0c hcc u (by omega)
      · -- both decided by consensus: uniform agreement after a clean round
        by_cases hvi : floodVal (alg1' f nb) r 2 (v0 f nb r) i (f + 2)
        · have hall := commit_valid i hni hvi
          -- `u` missed a round-1 message: a crash in round 1
          have : ∃ j, j ≠ u ∧ ¬ Sent (alg1' f nb) r j u 0 := by
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
          have := FloodRounds.agree (z' := u) hF h1 (by omega) hcl (Or.inl hni)
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
    · by_cases hv : floodVal (alg1' f nb) r 2 (v0 f nb r) i (f + 2)
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

end Papers.PODC2018.Silence.MidRound.OneBitFixed
