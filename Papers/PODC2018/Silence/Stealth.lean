import Papers.PODC2018.Silence.Defs
import Cslib.Computability.Distributed.SyncCrash.Floodset

/-!
# The STEALTH protocol (Appendix A, Figure 1 of Goren–Moses): `D = 3`, `M = n + f − 1`

Processes `Fin n`, choir `C = {0, 1, …, f}`; all messages are a single bit (`Unit`).

* Round 1: every process with value `1` sends `'1'` to process `0`.
* Round 2: process `0`, if its own value is `1` and it heard from all others, sends `all[1]` to
  `1, …, f`.
* Round 3: a choir member that does not know `all[1]` (process `0`: did not hear from all / has
  value `0`; others: did not get `all[1]`) sends `err` to all.
* Time 3: a process that neither received nor sent `err` commits; otherwise it sends `huh?` to all
  in round 4.
* Rounds 5 … f + 4: the processes that sent or received `huh?` run a biased-to-1 consensus, here a
  concrete *max-floodset*: every participant currently holding `1` sends `'1'` to all; initial bit
  `v̂ = 1` iff it committed or knows `all[1]`; a participant holds `1` once it received a consensus
  message. At time `f + 4` a participant that did not commit decides `commit` iff it holds `1`.

Since there are no self-messages in our model, "received `err`/`huh?`" is read as "sent or received".
-/

namespace Papers.PODC2018.Silence.Stealth

open Cslib.SyncCrash Classical

variable {n : ℕ} [NeZero n]

/-- The choir `{0, …, f}`. -/
def choir (f : ℕ) (p : Fin n) : Prop := p.val ≤ f

/-- `p` knows `all[1]` (at time `≥ 2`): process `0` has value `1` and heard from all others in
round 1; any other process got `all[1]` from `0` in round 2. -/
def hasAll1 (p : Fin n) (x : Bool) (h : Cslib.Byzantine.LockStep.History (Fin n) Unit) : Prop :=
  (p = 0 ∧ x = true ∧ ∀ j, j ≠ 0 → rcv h 0 j ≠ none) ∨ (p ≠ 0 ∧ rcv h 1 0 ≠ none)

/-- `p` sent or received `err` (at time `≥ 3`). -/
def errSeen (f : ℕ) (p : Fin n) (x : Bool) (h : Cslib.Byzantine.LockStep.History (Fin n) Unit) :
    Prop :=
  (∃ j, rcv h 2 j ≠ none) ∨ (choir f p ∧ ¬ hasAll1 p x h)

/-- `p` participates in the consensus (sent or received `huh?`). -/
def part (f : ℕ) (p : Fin n) (x : Bool) (h : Cslib.Byzantine.LockStep.History (Fin n) Unit) :
    Prop :=
  errSeen f p x h ∨ ∃ j, rcv h 3 j ≠ none

/-- The initial consensus bit `v̂`: committed, or knows `all[1]`. -/
def vhat (f : ℕ) (p : Fin n) (x : Bool) (h : Cslib.Byzantine.LockStep.History (Fin n) Unit) :
    Prop :=
  ¬ errSeen f p x h ∨ hasAll1 p x h

/-- The current consensus bit. -/
def bit (f : ℕ) (p : Fin n) (x : Bool) (h : Cslib.Byzantine.LockStep.History (Fin n) Unit) :
    Prop :=
  vhat f p x h ∨ ∃ t', 4 ≤ t' ∧ t' < h.length ∧ ∃ j, rcv h t' j ≠ none

variable (n) in
/-- The STEALTH protocol. -/
noncomputable def stealth (f : ℕ) : ACProtocol (Fin n) Unit where
  send p x h q :=
    if h.length = 0 then (if x = true ∧ q = 0 then some () else none)
    else if h.length = 1 then
      (if p = 0 ∧ hasAll1 p x h ∧ 1 ≤ q.val ∧ q.val ≤ f then some () else none)
    else if h.length = 2 then (if choir f p ∧ ¬ hasAll1 p x h then some () else none)
    else if h.length = 3 then (if errSeen f p x h then some () else none)
    else if h.length ≤ f + 3 then (if part f p x h ∧ bit f p x h then some () else none)
    else none
  decide p x h :=
    if h.length = 3 ∧ ¬ errSeen f p x h then some .commit
    else if h.length = f + 4 ∧ errSeen f p x h then
      (if bit f p x h then some .commit else some .abort)
    else none

variable {f : ℕ}

section Equations

variable {p q : Fin n} {x : Bool} {h : Cslib.Byzantine.LockStep.History (Fin n) Unit}

lemma send_def : (stealth n f).send p x h q =
    if h.length = 0 then (if x = true ∧ q = 0 then some () else none)
    else if h.length = 1 then
      (if p = 0 ∧ hasAll1 p x h ∧ 1 ≤ q.val ∧ q.val ≤ f then some () else none)
    else if h.length = 2 then (if choir f p ∧ ¬ hasAll1 p x h then some () else none)
    else if h.length = 3 then (if errSeen f p x h then some () else none)
    else if h.length ≤ f + 3 then (if part f p x h ∧ bit f p x h then some () else none)
    else none := rfl

lemma decide_def : (stealth n f).decide p x h =
    if h.length = 3 ∧ ¬ errSeen f p x h then some .commit
    else if h.length = f + 4 ∧ errSeen f p x h then
      (if bit f p x h then some .commit else some .abort)
    else none := rfl

lemma send_len0 (hh : h.length = 0) :
    (stealth n f).send p x h q = if x = true ∧ q = 0 then some () else none := by
  rw [send_def, if_pos hh]

lemma send_len1 (hh : h.length = 1) :
    (stealth n f).send p x h q =
      if p = 0 ∧ hasAll1 p x h ∧ 1 ≤ q.val ∧ q.val ≤ f then some () else none := by
  rw [send_def, if_neg (by omega), if_pos hh]

lemma send_len2 (hh : h.length = 2) :
    (stealth n f).send p x h q = if choir f p ∧ ¬ hasAll1 p x h then some () else none := by
  rw [send_def, if_neg (by omega), if_neg (by omega), if_pos hh]

lemma send_len3 (hh : h.length = 3) :
    (stealth n f).send p x h q = if errSeen f p x h then some () else none := by
  rw [send_def, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hh]

lemma send_flood (h4 : 4 ≤ h.length) (hf : h.length ≤ f + 3) :
    (stealth n f).send p x h q = if part f p x h ∧ bit f p x h then some () else none := by
  rw [send_def, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos hf]

lemma send_late (hl : f + 4 ≤ h.length) : (stealth n f).send p x h q = none := by
  rw [send_def, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

end Equations

/-! ### Semantic versions of the local predicates -/

variable (f) in
/-- `p` knows `all[1]`, in terms of the run. -/
def A1 (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  (p = 0 ∧ r.input p = true ∧ ∀ j, j ≠ 0 → Sent (stealth n f) r j p 0) ∨
    (p ≠ 0 ∧ Sent (stealth n f) r 0 p 1)

variable (f) in
/-- `p` sent or received `err`, in terms of the run. -/
def E (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  (∃ j, Sent (stealth n f) r j p 2) ∨ (choir f p ∧ ¬ A1 f r p)

variable (f) in
/-- `p` participates in the consensus, in terms of the run. -/
def Pt (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  E f r p ∨ ∃ j, Sent (stealth n f) r j p 3

variable (f) in
/-- `v̂`, in terms of the run. -/
def V (r : Run (Fin n) Bool) (p : Fin n) : Prop := ¬ E f r p ∨ A1 f r p

variable {r : Run (Fin n) Bool} {p : Fin n} {m : ℕ}

lemma hasAll1_hist (hm : 2 ≤ m) :
    hasAll1 p (r.input p) (hist (stealth n f) r m p) ↔ A1 f r p := by
  simp only [hasAll1, A1, rcv_hist r p _ (show 0 < m by omega),
    rcv_hist r p _ (show 1 < m by omega), Sent]

lemma errSeen_hist (hm : 3 ≤ m) :
    errSeen f p (r.input p) (hist (stealth n f) r m p) ↔ E f r p := by
  simp only [errSeen, E, rcv_hist r p _ (show 2 < m by omega), hasAll1_hist (show 2 ≤ m by omega),
    Sent]

lemma part_hist (hm : 4 ≤ m) :
    part f p (r.input p) (hist (stealth n f) r m p) ↔ Pt f r p := by
  simp only [part, Pt, errSeen_hist (show 3 ≤ m by omega), rcv_hist r p _ (show 3 < m by omega),
    Sent]

lemma vhat_hist (hm : 4 ≤ m) :
    vhat f p (r.input p) (hist (stealth n f) r m p) ↔ V f r p := by
  simp only [vhat, V, errSeen_hist (show 3 ≤ m by omega), hasAll1_hist (show 2 ≤ m by omega)]

lemma bit_hist (hm : 4 ≤ m) :
    bit f p (r.input p) (hist (stealth n f) r m p) ↔
      floodVal (stealth n f) r 4 (V f r) p m := by
  unfold bit floodVal
  rw [vhat_hist hm, length_hist]
  apply or_congr_right
  constructor
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rw [rcv_hist r p j h2] at hj; exact hj⟩
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rw [rcv_hist r p j h2]; exact hj⟩

/-! ### Which messages are sent -/

variable {j : Fin n}

lemma sent0 : Sent (stealth n f) r j p 0 ↔ j ≠ p ∧ r.Deliv j p 0 ∧ r.input j = true ∧ p = 0 := by
  rw [sent_iff_deliv, send_len0 (length_hist _ _ _)]
  by_cases h : r.input j = true ∧ p = 0
  · simp [h]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]; tauto

lemma sent1 : Sent (stealth n f) r j p 1 ↔
    j ≠ p ∧ r.Deliv j p 1 ∧ j = 0 ∧ A1 f r 0 ∧ 1 ≤ p.val ∧ p.val ≤ f := by
  rw [sent_iff_deliv, send_len1 (length_hist _ _ _)]
  by_cases h : j = 0 ∧ hasAll1 j (r.input j) (hist (stealth n f) r 1 j) ∧ 1 ≤ p.val ∧ p.val ≤ f
  · rw [if_pos h]
    obtain ⟨rfl, h2, h3, h4⟩ := h
    have : A1 f r 0 := by
      rcases h2 with ⟨-, h2a, h2b⟩ | ⟨h, -⟩
      · refine Or.inl ⟨rfl, h2a, fun k hk => ?_⟩
        have := h2b k hk
        rwa [rcv_hist r 0 k (show 0 < 1 by omega)] at this
      · exact absurd rfl h
    simp [this, h3, h4]
  · rw [if_neg h]
    simp only [ne_eq, not_true_eq_false, and_false, false_iff]
    rintro ⟨-, -, rfl, hA, h3, h4⟩
    apply h
    refine ⟨rfl, ?_, h3, h4⟩
    rcases hA with ⟨-, hA1, hA2⟩ | ⟨h, -⟩
    · refine Or.inl ⟨rfl, hA1, fun k hk => ?_⟩
      rw [rcv_hist r 0 k (show 0 < 1 by omega)]
      exact hA2 k hk
    · exact absurd rfl h

lemma sent2 : Sent (stealth n f) r j p 2 ↔ j ≠ p ∧ r.Deliv j p 2 ∧ choir f j ∧ ¬ A1 f r j := by
  rw [sent_iff_deliv, send_len2 (length_hist _ _ _), hasAll1_hist le_rfl]
  by_cases h : choir f j ∧ ¬ A1 f r j
  · simp [h]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]; tauto

lemma sent3 : Sent (stealth n f) r j p 3 ↔ j ≠ p ∧ r.Deliv j p 3 ∧ E f r j := by
  rw [sent_iff_deliv, send_len3 (length_hist _ _ _), errSeen_hist le_rfl]
  by_cases h : E f r j
  · simp [h]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]; tauto

lemma floodRounds : FloodRounds (stealth n f) r 4 f (Pt f r) (V f r) := by
  intro t h4 ht y z
  rw [sent_iff_deliv, send_flood (by simp; omega) (by simp; omega), part_hist h4, bit_hist h4]
  by_cases h : Pt f r y ∧ floodVal (stealth n f) r 4 (V f r) y t
  · simp [h]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]; tauto

lemma not_sent_late {t : ℕ} (ht : f + 4 ≤ t) : ¬ Sent (stealth n f) r j p t := by
  rw [sent_iff_deliv, send_late (by simp; omega)]; simp

lemma decidesAt_iff' {d : Decision} :
    DecidesAt (stealth n f) r p m d ↔ r.Alive p m ∧
      ((m = 3 ∧ ¬ E f r p ∧ d = .commit) ∨
       (m = f + 4 ∧ E f r p ∧
        d = if floodVal (stealth n f) r 4 (V f r) p (f + 4) then .commit else .abort)) := by
  rw [decidesAt_iff]
  apply and_congr_right
  intro _
  rw [decide_def, length_hist]
  by_cases h3 : m = 3
  · subst h3
    rw [errSeen_hist le_rfl]
    by_cases hE : E f r p
    · rw [if_neg (by tauto), if_neg (by omega)]; simp [hE]
    · rw [if_pos ⟨rfl, hE⟩]; simp [hE, eq_comm]
  · by_cases h4 : m = f + 4
    · subst h4
      rw [errSeen_hist (by omega), bit_hist (by omega), if_neg (by omega)]
      by_cases hE : E f r p
      · rw [if_pos ⟨rfl, hE⟩]
        split_ifs with hb <;> simp [hE, hb, eq_comm]
      · rw [if_neg (by tauto)]; simp [hE]
    · rw [if_neg (by omega), if_neg (by omega)]; simp [h3, h4]

/-! ### Key lemmas -/

lemma all_one_of_A1 {z : Fin n} (h : A1 f r z) : A1 f r 0 := by
  rcases h with ⟨rfl, h1⟩ | ⟨-, hs⟩
  · exact Or.inl ⟨rfl, h1⟩
  · exact (sent1.1 hs).2.2.2.1

lemma allOne_of_A1_zero (h : A1 f r 0) (k : Fin n) : r.input k = true := by
  rcases h with ⟨-, h1, h2⟩ | ⟨h, -⟩
  · by_cases hk : k = 0
    · subst hk; exact h1
    · exact (sent0.1 (h2 k hk)).2.2.1
  · exact absurd rfl h

lemma choir_iff (hfn : f < n) (p : Fin n) : choir f p ↔ p ∈ Finset.Iic (⟨f, hfn⟩ : Fin n) := by
  simp [choir, Fin.le_def]

lemma val_ne_zero {c : Fin n} (hc : c ≠ 0) : 1 ≤ c.val := by
  have : c.val ≠ 0 := fun h => hc (Fin.ext (by rw [h]; simp))
  omega

/-- If some process saw no `err`, a correct choir member knows `all[1]` (the silent choir). -/
lemma correct_choir_A1 (hr : r.Admissible f) (hfn : f < n) {i : Fin n} (hi : ¬ E f r i) :
    ∃ c, choir f c ∧ ¬ r.Faulty c ∧ A1 f r c := by
  obtain ⟨c, hc, hcf⟩ : ∃ c, choir f c ∧ ¬ r.Faulty c := by
    by_contra hno
    push Not at hno
    have hsub : Finset.Iic (⟨f, hfn⟩ : Fin n) ⊆ r.faulty := by
      intro z hz
      rw [Run.mem_faulty]; exact hno z ((choir_iff hfn z).2 hz)
    have := (Finset.card_le_card hsub).trans hr.1
    rw [Fin.card_Iic] at this
    simp at this
  refine ⟨c, hc, hcf, ?_⟩
  by_contra hA
  apply hi
  by_cases hci : c = i
  · subst hci; exact Or.inr ⟨hc, hA⟩
  · exact Or.inl ⟨c, sent2.2 ⟨hci, Run.deliv_of_not_faulty hcf i 2, hc, hA⟩⟩

/-- Some participant starts the consensus with `1` only if `all[1]` is known by process `0`. -/
lemma A1_zero_of_flood (hr : r.Admissible f) (hfn : f < n) {i : Fin n} (hi : Pt f r i)
    (hv : floodVal (stealth n f) r 4 (V f r) i (f + 4)) : A1 f r 0 := by
  by_contra hA0
  have hnot := FloodRounds.not_val (floodRounds (r := r)) (fun y _ hy => by
    rcases hy with hy | hy
    · obtain ⟨c, -, -, hc⟩ := correct_choir_A1 hr hfn hy
      exact hA0 (all_one_of_A1 hc)
    · exact hA0 (all_one_of_A1 hy)) (f + 4) (by omega) i hi
  exact hnot hv

lemma Pt_of_E {i : Fin n} (h : E f r i) : Pt f r i := Or.inl h

/-- **STEALTH solves AC in `γ_f`** (Claim 2 of Goren–Moses), for `1 ≤ f < n`. -/
theorem solvesAC (hf : 1 ≤ f) (hfn : f < n) : SolvesAC (stealth n f) f := by
  intro r hr
  -- a commit implies all values are 1
  have commit_one : ∀ i m, DecidesAt (stealth n f) r i m .commit → A1 f r 0 := by
    intro i m h
    rw [decidesAt_iff'] at h
    rcases h with ⟨-, ⟨-, hE, -⟩ | ⟨-, hE, hd⟩⟩
    · obtain ⟨c, -, -, hc⟩ := correct_choir_A1 hr hfn hE
      exact all_one_of_A1 hc
    · by_cases hv : floodVal (stealth n f) r 4 (V f r) i (f + 4)
      · exact A1_zero_of_flood hr hfn (Pt_of_E hE) hv
      · rw [if_neg hv] at hd; cases hd
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Decision
    intro i hi
    by_cases hE : E f r i
    · exact ⟨f + 4, _, decidesAt_iff'.2 ⟨Run.alive_of_not_faulty hi _, Or.inr ⟨rfl, hE, rfl⟩⟩⟩
    · exact ⟨3, .commit, decidesAt_iff'.2 ⟨Run.alive_of_not_faulty hi _, Or.inl ⟨rfl, hE, rfl⟩⟩⟩
  · -- Agreement
    have no_abort : ∀ i m, DecidesAt (stealth n f) r i m .abort →
        ∀ k m', ¬ DecidesAt (stealth n f) r k m' .commit := by
      intro i m hab k m' hck
      rw [decidesAt_iff'] at hab
      rcases hab with ⟨ha, ⟨-, -, h⟩ | ⟨rfl, hEi, hd⟩⟩
      · cases h
      have hvi : ¬ floodVal (stealth n f) r 4 (V f r) i (f + 4) := by
        intro hv; rw [if_pos hv] at hd; cases hd
      rw [decidesAt_iff'] at hck
      rcases hck with ⟨hak, ⟨rfl, hEk, -⟩ | ⟨rfl, hEk, hdk⟩⟩
      · -- `k` committed at time 3: a correct choir member with `all[1]` joins the consensus
        obtain ⟨c, -, hcf, hcA⟩ := correct_choir_A1 hr hfn hEk
        have hPc : Pt f r c := by
          by_cases hci : c = i
          · subst hci; exact Pt_of_E hEi
          · refine Or.inr ⟨i, sent3.2 ⟨Ne.symm hci, ⟨ha.mono (by omega), fun h => ?_⟩, hEi⟩⟩
            have := ha _ h.1; omega
        exact hvi (FloodRounds.val_of_correct floodRounds (by omega) hPc (Or.inr hcA) hcf i
          (by omega))
      · -- both decide by consensus: process 0 crashed early, so there is a clean round
        have hvk : floodVal (stealth n f) r 4 (V f r) k (f + 4) := by
          by_contra hv; rw [if_neg hv] at hdk; cases hdk
        have hA0 := A1_zero_of_flood hr hfn (Pt_of_E hEk) hvk
        -- the `err` seen by `i` comes from a choir member `c ≠ 0` without `all[1]`
        obtain ⟨c, hc, hca, hcA⟩ : ∃ c, choir f c ∧ r.Alive c 2 ∧ ¬ A1 f r c := by
          rcases hEi with ⟨c, hc⟩ | ⟨hc, hcA⟩
          · obtain ⟨-, hd, hch, hcA⟩ := sent2.1 hc
            exact ⟨c, hch, hd.1, hcA⟩
          · exact ⟨i, hc, ha.mono (by omega), hcA⟩
        have hc0 : c ≠ 0 := fun h => hcA (h ▸ hA0)
        have hcrash0 : ∃ c0, r.crash 0 = some c0 ∧ c0 ≤ 2 := by
          have hnd : ¬ r.Deliv 0 c 1 := by
            intro hd
            apply hcA
            refine Or.inr ⟨hc0, sent1.2 ⟨Ne.symm hc0, hd, rfl, hA0, ?_, hc⟩⟩
            exact val_ne_zero hc0
          by_contra hno
          push Not at hno
          apply hnd
          refine ⟨fun c0 h0 => ?_, fun h => ?_⟩
          · have := hno c0 h0; omega
          · have := hno 2 h.1; omega
        obtain ⟨c0, hc0r, hc0le⟩ := hcrash0
        obtain ⟨t₀, ht1, ht2, hclean⟩ := exists_clean_round (T := 4) (R := f) r (by
          have hsub : Finset.univ.filter (fun p => ∃ c, r.crash p = some c ∧ 4 < c ∧ c ≤ 4 + f)
              ⊆ r.faulty.erase 0 := by
            intro z hz
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
            obtain ⟨cz, hcz, h1, -⟩ := hz
            rw [Finset.mem_erase, Run.mem_faulty]
            refine ⟨fun h => ?_, by simp [Run.Faulty, hcz]⟩
            subst h; rw [hc0r] at hcz; cases hcz; omega
          have h0f : (0 : Fin n) ∈ r.faulty := by rw [Run.mem_faulty]; simp [Run.Faulty, hc0r]
          have := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem h0f] at this
          have := hr.1
          omega)
        exact hvi (FloodRounds.agree (z' := i) floodRounds ht1 ht2 hclean (Pt_of_E hEk)
          (by simpa [add_comm] using hak) (by simpa [add_comm] using hvk) |>
          fun h => by simpa [add_comm] using h)
    intro i m d i' m' d' h h'
    cases d <;> cases d'
    · rfl
    · exact absurd h (no_abort i' m' h' i m)
    · exact absurd h' (no_abort i m h i' m')
    · rfl
  · -- Commit Validity
    intro i m h k
    exact allOne_of_A1_zero (commit_one i m h) k
  · -- Abort Validity
    intro i m h
    by_contra hc
    push Not at hc
    obtain ⟨hin, hnf⟩ := hc
    have hin' : ∀ k, r.input k = true := fun k => by simpa using hin k
    have hnf' : ∀ k, ¬ r.Faulty k := fun k => by simpa [Run.Faulty] using hnf k
    rw [decidesAt_iff'] at h
    rcases h with ⟨-, ⟨-, -, h⟩ | ⟨-, hE, -⟩⟩
    · cases h
    have hA0 : A1 f r 0 := Or.inl ⟨rfl, hin' 0, fun k hk =>
      sent0.2 ⟨hk, Run.deliv_of_not_faulty (hnf' k) 0 0, hin' k, rfl⟩⟩
    have hAc : ∀ c, choir f c → A1 f r c := by
      intro c hc
      by_cases hc0 : c = 0
      · subst hc0; exact hA0
      · refine Or.inr ⟨hc0, sent1.2 ⟨Ne.symm hc0, Run.deliv_of_not_faulty (hnf' 0) c 1, rfl, hA0,
          ?_, hc⟩⟩
        exact val_ne_zero hc0
    rcases hE with ⟨c, hc⟩ | ⟨hc, hcA⟩
    · obtain ⟨-, -, hch, hcA⟩ := sent2.1 hc
      exact hcA (hAc c hch)
    · exact hcA (hAc i hc)

/-! ### The nice run -/

lemma nice_A1 (c : Fin n) (hc : choir f c) : A1 f (nice : Run (Fin n) Bool) c := by
  have hA0 : A1 f (nice : Run (Fin n) Bool) 0 := Or.inl ⟨rfl, rfl, fun k hk =>
    sent0.2 ⟨hk, Run.deliv_of_not_faulty (nice_not_faulty k) 0 0, rfl, rfl⟩⟩
  by_cases hc0 : c = 0
  · subst hc0; exact hA0
  · exact Or.inr ⟨hc0, sent1.2 ⟨Ne.symm hc0, Run.deliv_of_not_faulty (nice_not_faulty 0) c 1, rfl,
      hA0, val_ne_zero hc0, hc⟩⟩

lemma nice_not_E (p : Fin n) : ¬ E f (nice : Run (Fin n) Bool) p := by
  rintro (⟨c, hc⟩ | ⟨hc, hcA⟩)
  · obtain ⟨-, -, hch, hcA⟩ := sent2.1 hc
    exact hcA (nice_A1 c hch)
  · exact hcA (nice_A1 p hc)

/-- **Claim 1** of Goren–Moses: in the nice run of STEALTH every process commits at time `3`… -/
theorem nice_commit (p : Fin n) : DecidesAt (stealth n f) nice p 3 .commit :=
  decidesAt_iff'.2 ⟨nice_alive p 3, Or.inl ⟨rfl, nice_not_E p, rfl⟩⟩

lemma nice_sent_iff {a b : Fin n} {t : ℕ} :
    Sent (stealth n f) nice a b t ↔
      (t = 0 ∧ b = 0 ∧ a ≠ 0) ∨ (t = 1 ∧ a = 0 ∧ 1 ≤ b.val ∧ b.val ≤ f) := by
  constructor
  · intro h
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ (4 ≤ t ∧ t < 4 + f) ∨ f + 4 ≤ t by omega) with
      rfl | rfl | rfl | rfl | ⟨h4, h5⟩ | h6
    · obtain ⟨hab, -, -, rfl⟩ := sent0.1 h
      exact Or.inl ⟨rfl, rfl, hab⟩
    · obtain ⟨-, -, rfl, -, h1, h2⟩ := sent1.1 h
      exact Or.inr ⟨rfl, rfl, h1, h2⟩
    · obtain ⟨-, -, hch, hA⟩ := sent2.1 h
      exact absurd (nice_A1 a hch) hA
    · exact absurd (sent3.1 h).2.2 (nice_not_E a)
    · obtain ⟨-, -, hP, -⟩ := (floodRounds t h4 h5 a b).1 h
      rcases hP with hE | ⟨j, hj⟩
      · exact absurd hE (nice_not_E a)
      · exact absurd (sent3.1 hj).2.2 (nice_not_E j)
    · exact absurd h (not_sent_late h6)
  · rintro (⟨rfl, rfl, hab⟩ | ⟨rfl, rfl, h1, h2⟩)
    · exact sent0.2 ⟨hab, Run.deliv_of_not_faulty (nice_not_faulty a) 0 0, rfl, rfl⟩
    · have hb0 : b ≠ 0 := fun h => by subst h; simp at h1
      exact sent1.2 ⟨Ne.symm hb0, Run.deliv_of_not_faulty (nice_not_faulty 0) b 1, rfl,
        nice_A1 0 (by simp [choir]), h1, h2⟩

/-- … and exactly `n + f − 1` messages are sent (Claim 1). -/
theorem nice_msgs (hf : 1 ≤ f) (hfn : f < n) :
    (msgs (stealth n f) nice).encard = (n + f - 1 : ℕ) := by
  let A : Finset (Fin n × Fin n × ℕ) := (Finset.univ.erase 0).image (fun a => (a, 0, 0))
  let B : Finset (Fin n × Fin n × ℕ) :=
    (Finset.Icc (⟨1, by omega⟩ : Fin n) ⟨f, hfn⟩).image (fun b => (0, b, 1))
  have hset : msgs (stealth n f) nice = ((A ∪ B : Finset _) : Set (Fin n × Fin n × ℕ)) := by
    ext ⟨a, b, t⟩
    simp only [msgs, Set.mem_setOf_eq, nice_sent_iff, Finset.coe_union, Finset.coe_image,
      Set.mem_union, Set.mem_image, Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_Icc, Prod.mk.injEq, A, B, Fin.le_def]
    constructor
    · rintro (⟨rfl, rfl, hab⟩ | ⟨rfl, rfl, h1, h2⟩)
      · exact Or.inl ⟨a, hab, rfl, rfl, rfl⟩
      · exact Or.inr ⟨b, ⟨h1, h2⟩, rfl, rfl, rfl⟩
    · rintro (⟨a', hab, rfl, rfl, rfl⟩ | ⟨b', ⟨h1, h2⟩, rfl, rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl, hab⟩
      · exact Or.inr ⟨rfl, rfl, h1, h2⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro e heA heB
    simp only [A, B, Finset.mem_image] at heA heB
    obtain ⟨_, -, rfl⟩ := heA
    obtain ⟨_, -, he⟩ := heB
    simp at he
  have hA : A.card = n - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg Prod.fst hab),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hB : B.card = f := by
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using congrArg (·.2.1) hab),
      Fin.card_Icc]
    simp
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_union_of_disjoint hdisj, hA, hB]
  have : 1 ≤ n := by omega
  congr 1
  omega

end Papers.PODC2018.Silence.Stealth
