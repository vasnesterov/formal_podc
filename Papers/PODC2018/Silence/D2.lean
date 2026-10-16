import Papers.PODC2018.Silence.Defs
import Cslib.Computability.Distributed.SyncCrash.Floodset

/-!
# The protocol D2 (Appendix B / Figure 3 of Goren–Moses): `D = 2`, `M = f · n`

Processes are `Fin n`; `q` is one of the `f` *successors* of `p` iff `(q - p) mod n ∈ [1, f]`.

* Round 1: a process with value `1` sends `'1'` to its `f` successors.
* `ok1`: value `1` and `'1'` received from all `f` predecessors (the paper's "received `f + 1`
  messages of `'1'`", counting the process's own vote).
* Round 2: a process that is not `ok1` sends `err` to all.
* `errSeen`: not `ok1`, or received `err` in round 2 ("sent or received an error message").
  At time 2 a process with `¬ errSeen` commits.
* Round 3: a process with `errSeen` sends to all the set of ids from which it got `'1'` in round 1
  (including its own id if its value is `1`).
* Participants of the consensus (time 3): `errSeen`, or received an id set in round 3.
  Initial bit `v̂`: committed (`¬ errSeen`), or every id is covered by a received id set (or its own).
* Consensus (`B.1.Consensus`): max-floodset for `f` rounds (rounds 4 … f + 3): a participant
  holding `1` sends a message to all; it holds `1` if `v̂ = 1` or it received a consensus message.
  At time `f + 3` an uncommitted participant commits iff it holds `1`, and aborts otherwise.

Messages are `Finset (Fin n)`; one-bit messages are `∅`.
-/

namespace Papers.PODC2018.Silence.D2

open Cslib.SyncCrash Classical

variable {n : ℕ}

/-- Histories of D2. -/
abbrev H (n : ℕ) := Cslib.Byzantine.LockStep.History (Fin n) (Finset (Fin n))

/-- `q` is one of the `f` successors of `p` (cyclically). -/
def IsSucc (f : ℕ) (p q : Fin n) : Prop := 1 ≤ (q - p).val ∧ (q - p).val ≤ f

/-- Value `1` and `'1'` received from all `f` predecessors in round 1. -/
def ok1 (f : ℕ) (p : Fin n) (x : Bool) (h : H n) : Prop :=
  x = true ∧ ∀ j, IsSucc f j p → rcv h 0 j ≠ none

/-- Sent or received an `err` message in round 2. -/
def errSeen (f : ℕ) (p : Fin n) (x : Bool) (h : H n) : Prop :=
  ¬ ok1 f p x h ∨ ∃ j, rcv h 1 j ≠ none

/-- The ids from which `'1'` was received in round 1, plus the own id if the value is `1`. -/
noncomputable def ids (p : Fin n) (x : Bool) (h : H n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => rcv h 0 j ≠ none) ∪ (if x = true then {p} else ∅)

/-- Participates in the consensus. -/
def part (f : ℕ) (p : Fin n) (x : Bool) (h : H n) : Prop :=
  errSeen f p x h ∨ ∃ j, rcv h 2 j ≠ none

/-- Every id appears in an id set received in round 3 (or in the own one). -/
def covered (f : ℕ) (p : Fin n) (x : Bool) (h : H n) : Prop :=
  ∀ k, (errSeen f p x h ∧ k ∈ ids p x h) ∨ ∃ j S, rcv h 2 j = some S ∧ k ∈ S

/-- The initial consensus bit `v̂`. -/
def vhat (f : ℕ) (p : Fin n) (x : Bool) (h : H n) : Prop :=
  ¬ errSeen f p x h ∨ covered f p x h

/-- The consensus bit held at time `t`. -/
def bit (f : ℕ) (p : Fin n) (x : Bool) (h : H n) (t : ℕ) : Prop :=
  vhat f p x h ∨ ∃ t', 3 ≤ t' ∧ t' < t ∧ ∃ j, rcv h t' j ≠ none

/-- The protocol D2. -/
noncomputable def d2 (n f : ℕ) : ACProtocol (Fin n) (Finset (Fin n)) where
  send p x h q :=
    if h.length = 0 then (if x = true ∧ IsSucc f p q then some ∅ else none)
    else if h.length = 1 then (if ok1 f p x h then none else some ∅)
    else if h.length = 2 then (if errSeen f p x h then some (ids p x h) else none)
    else if h.length < f + 3 then
      (if part f p x h ∧ bit f p x h h.length then some ∅ else none)
    else none
  decide p x h :=
    if h.length = 2 ∧ ¬ errSeen f p x h then some .commit
    else if h.length = f + 3 ∧ errSeen f p x h then
      (if bit f p x h (f + 3) then some .commit else some .abort)
    else none

variable {f : ℕ}

lemma send_def (p : Fin n) (x : Bool) (h : H n) (q : Fin n) :
    (d2 n f).send p x h q =
      if h.length = 0 then (if x = true ∧ IsSucc f p q then some ∅ else none)
      else if h.length = 1 then (if ok1 f p x h then none else some ∅)
      else if h.length = 2 then (if errSeen f p x h then some (ids p x h) else none)
      else if h.length < f + 3 then
        (if part f p x h ∧ bit f p x h h.length then some ∅ else none)
      else none := rfl

lemma decide_def (p : Fin n) (x : Bool) (h : H n) :
    (d2 n f).decide p x h =
      if h.length = 2 ∧ ¬ errSeen f p x h then some .commit
      else if h.length = f + 3 ∧ errSeen f p x h then
        (if bit f p x h (f + 3) then some .commit else some .abort)
      else none := rfl

lemma send_len0 {p : Fin n} {x : Bool} {h : H n} {q : Fin n} (hh : h.length = 0) :
    (d2 n f).send p x h q = if x = true ∧ IsSucc f p q then some ∅ else none := by
  rw [send_def, if_pos hh]

lemma send_len1 {p : Fin n} {x : Bool} {h : H n} {q : Fin n} (hh : h.length = 1) :
    (d2 n f).send p x h q = if ok1 f p x h then none else some ∅ := by
  rw [send_def, if_neg (by omega), if_pos hh]

lemma send_len2 {p : Fin n} {x : Bool} {h : H n} {q : Fin n} (hh : h.length = 2) :
    (d2 n f).send p x h q = if errSeen f p x h then some (ids p x h) else none := by
  rw [send_def, if_neg (by omega), if_neg (by omega), if_pos hh]

lemma send_mid {p : Fin n} {x : Bool} {h : H n} {q : Fin n} (h3 : 3 ≤ h.length)
    (hf : h.length < f + 3) :
    (d2 n f).send p x h q = if part f p x h ∧ bit f p x h h.length then some ∅ else none := by
  rw [send_def, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hf]

lemma send_late {p : Fin n} {x : Bool} {h : H n} {q : Fin n} (hf : f + 3 ≤ h.length) :
    (d2 n f).send p x h q = none := by
  rw [send_def, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ### Run-level description -/

variable (f) in
/-- `ok1` in terms of the run. -/
def ok1R (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  r.input p = true ∧ ∀ j, IsSucc f j p → Sent (d2 n f) r j p 0

variable (f) in
def errR (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  ¬ ok1R f r p ∨ ∃ j, Sent (d2 n f) r j p 1

variable (f) in
noncomputable def idsR (r : Run (Fin n) Bool) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Sent (d2 n f) r j p 0) ∪ (if r.input p = true then {p} else ∅)

variable (f) in
def partR (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  errR f r p ∨ ∃ j, Sent (d2 n f) r j p 2

variable (f) in
def coveredR (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  ∀ k, (errR f r p ∧ k ∈ idsR f r p) ∨ ∃ j S, msg (d2 n f) r j p 2 = some S ∧ k ∈ S

variable (f) in
def vhatR (r : Run (Fin n) Bool) (p : Fin n) : Prop :=
  ¬ errR f r p ∨ coveredR f r p

variable {r : Run (Fin n) Bool}

lemma ok1_hist {p : Fin n} {m : ℕ} (hm : 1 ≤ m) :
    ok1 f p (r.input p) (hist (d2 n f) r m p) ↔ ok1R f r p := by
  simp only [ok1, ok1R, rcv_hist r p _ (show 0 < m by omega), Sent]

lemma errSeen_hist {p : Fin n} {m : ℕ} (hm : 2 ≤ m) :
    errSeen f p (r.input p) (hist (d2 n f) r m p) ↔ errR f r p := by
  simp only [errSeen, errR, ok1_hist (show 1 ≤ m by omega), rcv_hist r p _ (show 1 < m by omega),
    Sent]

lemma ids_hist {p : Fin n} {m : ℕ} (hm : 1 ≤ m) :
    ids p (r.input p) (hist (d2 n f) r m p) = idsR f r p := by
  unfold ids idsR
  ext k
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter,
    rcv_hist r p _ (show 0 < m by omega)]
  rfl

lemma part_hist {p : Fin n} {m : ℕ} (hm : 3 ≤ m) :
    part f p (r.input p) (hist (d2 n f) r m p) ↔ partR f r p := by
  simp only [part, partR, errSeen_hist (show 2 ≤ m by omega),
    rcv_hist r p _ (show 2 < m by omega), Sent]

lemma covered_hist {p : Fin n} {m : ℕ} (hm : 3 ≤ m) :
    covered f p (r.input p) (hist (d2 n f) r m p) ↔ coveredR f r p := by
  simp only [covered, coveredR, errSeen_hist (show 2 ≤ m by omega), ids_hist (show 1 ≤ m by omega),
    rcv_hist r p _ (show 2 < m by omega)]

lemma vhat_hist {p : Fin n} {m : ℕ} (hm : 3 ≤ m) :
    vhat f p (r.input p) (hist (d2 n f) r m p) ↔ vhatR f r p := by
  simp only [vhat, vhatR, errSeen_hist (show 2 ≤ m by omega), covered_hist hm]

lemma bit_hist {p : Fin n} {m t : ℕ} (hm : 3 ≤ m) (ht : t ≤ m) :
    bit f p (r.input p) (hist (d2 n f) r m p) t ↔
      floodVal (d2 n f) r 3 (vhatR f r) p t := by
  unfold bit floodVal
  rw [vhat_hist hm]
  apply or_congr_right
  constructor
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rw [rcv_hist r p _ (show t' < m by omega)] at hj; exact hj⟩
  · rintro ⟨t', h1, h2, j, hj⟩
    exact ⟨t', h1, h2, j, by rw [rcv_hist r p _ (show t' < m by omega)]; exact hj⟩

lemma sent0 {j p : Fin n} :
    Sent (d2 n f) r j p 0 ↔ j ≠ p ∧ r.Deliv j p 0 ∧ r.input j = true ∧ IsSucc f j p := by
  rw [sent_iff_deliv, send_len0 (length_hist _ _ _)]
  by_cases h : r.input j = true ∧ IsSucc f j p
  · rw [if_pos h]; simp [h.1, h.2]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]
    rintro ⟨_, _, h1, h2⟩; exact h ⟨h1, h2⟩

lemma sent1 {j p : Fin n} :
    Sent (d2 n f) r j p 1 ↔ j ≠ p ∧ r.Deliv j p 1 ∧ ¬ ok1R f r j := by
  rw [sent_iff_deliv, send_len1 (length_hist _ _ _), ok1_hist le_rfl]
  by_cases h : ok1R f r j
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

lemma msg2 {j p : Fin n} :
    msg (d2 n f) r j p 2 =
      if j ≠ p ∧ r.Deliv j p 2 ∧ errR f r j then some (idsR f r j) else none := by
  rw [msg_eq_deliv, send_len2 (length_hist _ _ _), errSeen_hist le_rfl, ids_hist (by omega)]
  by_cases h : j ≠ p ∧ r.Deliv j p 2
  · rw [if_pos h]
    by_cases he : errR f r j
    · rw [if_pos he, if_pos ⟨h.1, h.2, he⟩]
    · rw [if_neg he, if_neg (fun h' => he h'.2.2)]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]

lemma sent2 {j p : Fin n} :
    Sent (d2 n f) r j p 2 ↔ j ≠ p ∧ r.Deliv j p 2 ∧ errR f r j := by
  unfold Sent; rw [msg2]
  split_ifs with h
  · simp [h]
  · simp only [ne_eq, not_true_eq_false, false_iff]; exact h

lemma msg2_eq_some {j p : Fin n} {S : Finset (Fin n)} (h : msg (d2 n f) r j p 2 = some S) :
    S = idsR f r j := by
  rw [msg2] at h
  split_ifs at h
  · exact (Option.some.inj h).symm

lemma sentF {j p : Fin n} {t : ℕ} (h3 : 3 ≤ t) (hf : t < f + 3) :
    Sent (d2 n f) r j p t ↔
      j ≠ p ∧ r.Deliv j p t ∧ partR f r j ∧ floodVal (d2 n f) r 3 (vhatR f r) j t := by
  rw [sent_iff_deliv, send_mid (by simpa using h3) (by simpa using hf), length_hist,
    part_hist h3, bit_hist h3 le_rfl]
  by_cases h : partR f r j ∧ floodVal (d2 n f) r 3 (vhatR f r) j t
  · rw [if_pos h]; simp [h.1, h.2]
  · rw [if_neg h]; simp only [ne_eq, not_true_eq_false, and_false, false_iff]
    rintro ⟨_, _, h1, h2⟩; exact h ⟨h1, h2⟩

lemma not_sent_late {j p : Fin n} {t : ℕ} (ht : f + 3 ≤ t) : ¬ Sent (d2 n f) r j p t := by
  rw [sent_iff_deliv, send_late (by simpa using ht)]; simp

lemma floodRounds :
    FloodRounds (d2 n f) r 3 f (partR f r) (vhatR f r) := by
  intro t h3 hf y z
  exact sentF h3 (by omega)

lemma decidesAt_iff' {p : Fin n} {m : ℕ} {d : Decision} :
    DecidesAt (d2 n f) r p m d ↔ r.Alive p m ∧
      ((m = 2 ∧ ¬ errR f r p ∧ d = .commit) ∨
       (m = f + 3 ∧ errR f r p ∧
        d = if floodVal (d2 n f) r 3 (vhatR f r) p (f + 3) then .commit else .abort)) := by
  rw [decidesAt_iff]
  apply and_congr_right
  intro _
  rw [decide_def, length_hist]
  by_cases h2 : m = 2
  · subst h2
    rw [errSeen_hist le_rfl]
    by_cases he : errR f r p
    · rw [if_neg (fun h => h.2 he), if_neg (by omega)]; simp [he]
    · rw [if_pos ⟨rfl, he⟩]; simp [he, eq_comm]
  · by_cases hm : m = f + 3
    · subst hm
      rw [errSeen_hist (by omega), bit_hist (by omega) le_rfl, if_neg (fun h => h2 h.1)]
      by_cases he : errR f r p
      · rw [if_pos ⟨rfl, he⟩]
        split_ifs <;> simp [h2, he, eq_comm]
      · rw [if_neg (fun h => he h.2)]; simp [he]
    · rw [if_neg (fun h => h2 h.1), if_neg (fun h => hm h.1)]; simp [h2, hm]

/-! ### Successor blocks -/

lemma isSucc_ne {j p : Fin n} (h : IsSucc f j p) : j ≠ p := by
  rintro rfl
  have : (j - j).val = 0 := by simp [Fin.sub_def]
  unfold IsSucc at h
  omega

/-- Every process has exactly `f` successors (`f < n`). -/
lemma card_succ (hfn : f < n) (j : Fin n) : (Finset.univ.filter (IsSucc f j)).card = f := by
  have : NeZero n := ⟨by omega⟩
  have : (Finset.univ.filter (IsSucc f j)).card = (Finset.Icc 1 f).card := by
    apply Finset.card_bij (fun c _ => (c - j).val)
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsSucc] at hc
      simpa using hc
    · intro a _ b _ hab
      have : a - j = b - j := Fin.ext hab
      simpa using this
    · intro d hd
      rw [Finset.mem_Icc] at hd
      refine ⟨j + ⟨d, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsSucc, add_sub_cancel_left]
        exact hd
      · simp
  rw [this, Nat.card_Icc]; omega

/-- The block `{j, j + 1, …, j + f}` contains a correct process. -/
lemma exists_correct_block (hfn : f < n) {r : Run (Fin n) Bool} (hr : r.Admissible f) (j : Fin n) :
    ∃ c, ¬ r.Faulty c ∧ (c = j ∨ IsSucc f j c) := by
  by_contra hno
  push Not at hno
  have hsub : insert j (Finset.univ.filter (IsSucc f j)) ⊆ r.faulty := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_filter] at hc
    rw [Run.mem_faulty]
    by_contra hcf
    rcases hc with rfl | ⟨-, hc⟩
    · exact (hno c hcf).1 rfl
    · exact (hno c hcf).2 hc
  have := (Finset.card_le_card hsub).trans hr.1
  rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun h => isSucc_ne h rfl), card_succ hfn] at this
  omega

/-! ### Safety lemmas -/

variable {r : Run (Fin n) Bool}

/-- A correct process of the block of `j` is `ok1` unless it told `p` (which is not `errR`)
otherwise. -/
lemma ok1R_of_correct {p c : Fin n} (hp : ¬ errR f r p) (hc : ¬ r.Faulty c) : ok1R f r c := by
  by_contra hok
  have hp' : ok1R f r p ∧ ∀ k, ¬ Sent (d2 n f) r k p 1 := by
    unfold errR at hp; push Not at hp; exact hp
  by_cases hcp : c = p
  · subst hcp; exact hok hp'.1
  · exact hp'.2 c (sent1.2 ⟨hcp, Run.deliv_of_not_faulty hc p 1, hok⟩)

/-- If some process is not `errR` (e.g. it commits at time 2), all initial values are `1`, and
for every `j` a correct process of the block of `j` is `ok1` and has `j` among its ids. -/
lemma block_ids (hfn : f < n) (hr : r.Admissible f) {p : Fin n} (hp : ¬ errR f r p) (j : Fin n) :
    ∃ c, ¬ r.Faulty c ∧ ok1R f r c ∧ j ∈ idsR f r c ∧ r.input j = true := by
  obtain ⟨c, hc, hcj⟩ := exists_correct_block hfn hr j
  have hok := ok1R_of_correct hp hc
  have hin : r.input j = true := by
    rcases hcj with rfl | hs
    · exact hok.1
    · exact (sent0.1 (hok.2 j hs)).2.2.1
  refine ⟨c, hc, hok, ?_, hin⟩
  rcases hcj with rfl | hs
  · simp [idsR, hin]
  · simp only [idsR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inl (hok.2 j hs)

lemma allOne_of_not_errR (hfn : f < n) (hr : r.Admissible f) {p : Fin n} (hp : ¬ errR f r p)
    (j : Fin n) : r.input j = true := by
  obtain ⟨_, _, _, _, h⟩ := block_ids hfn hr hp j
  exact h

lemma input_of_mem_idsR {p k : Fin n} (h : k ∈ idsR f r p) : r.input k = true := by
  simp only [idsR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h
  rcases h with h | h
  · exact (sent0.1 h).2.2.1
  · split_ifs at h with hx
    · rw [Finset.mem_singleton] at h; subst h; exact hx
    · simp at h

lemma not_vhatR_of_input_false (hfn : f < n) (hr : r.Admissible f) {j : Fin n}
    (hj : r.input j = false) (p : Fin n) : ¬ vhatR f r p := by
  rintro (hp | hcov)
  · have := allOne_of_not_errR hfn hr hp j; simp_all
  · rcases hcov j with ⟨-, hmem⟩ | ⟨j', S, hS, hmem⟩
    · have := input_of_mem_idsR hmem; simp_all
    · rw [msg2_eq_some hS] at hmem
      have := input_of_mem_idsR hmem; simp_all

/-- In a run without crashes in the first three rounds and with all values `1`, nobody is `errR`. -/
lemma not_errR_of_clean (hall : ∀ j, r.input j = true) (hd : ∀ p q, r.Deliv p q 0)
    (p : Fin n) : ¬ errR f r p := by
  have hok : ∀ q, ok1R f r q := fun q =>
    ⟨hall q, fun j hs => sent0.2 ⟨isSucc_ne hs, hd j q, hall j, hs⟩⟩
  rintro (h | ⟨k, hk⟩)
  · exact h (hok p)
  · exact (sent1.1 hk).2.2 (hok k)

/-! ### Correctness -/

/-- A commit and an abort never coexist. -/
lemma no_commit_abort (hf : 1 ≤ f) (hfn : f < n) (hr : r.Admissible f) {i k : Fin n} {m m' : ℕ}
    (hab : DecidesAt (d2 n f) r i m .abort) (hc : DecidesAt (d2 n f) r k m' .commit) : False := by
  rw [decidesAt_iff'] at hab hc
  obtain ⟨hai, ⟨-, -, h⟩ | ⟨rfl, hei, hd⟩⟩ := hab
  · cases h
  have hvi : ¬ floodVal (d2 n f) r 3 (vhatR f r) i (f + 3) := by
    intro hv; rw [if_pos hv] at hd; cases hd
  obtain ⟨hak, ⟨rfl, hek, -⟩ | ⟨rfl, hek, hdk⟩⟩ := hc
  · -- commit at time 2
    by_cases hcom : ∃ c, ¬ r.Faulty c ∧ ¬ errR f r c
    · obtain ⟨c, hcc, hce⟩ := hcom
      have hci : c ≠ i := fun h => hce (h ▸ hei)
      have hdi : r.Deliv i c 2 := ⟨hai.mono (by omega), fun h => by
        have := hai _ h.1; omega⟩
      have hpc : partR f r c := Or.inr ⟨i, sent2.2 ⟨hci.symm, hdi, hei⟩⟩
      exact hvi (FloodRounds.val_of_correct floodRounds (by omega) hpc (Or.inl hce) hcc i
        (by omega))
    · push Not at hcom
      apply hvi
      refine Or.inl (Or.inr fun j => ?_)
      obtain ⟨c, hcc, -, hjc, -⟩ := block_ids hfn hr hek j
      have hce := hcom c hcc
      by_cases hci : c = i
      · subst hci; exact Or.inl ⟨hce, hjc⟩
      · refine Or.inr ⟨c, idsR f r c, ?_, hjc⟩
        rw [msg2, if_pos ⟨hci, Run.deliv_of_not_faulty hcc i 2, hce⟩]
  · -- commit at time f + 3
    have hvk : floodVal (d2 n f) r 3 (vhatR f r) k (f + 3) := by
      by_contra hv; rw [if_neg hv] at hdk; cases hdk
    have hpk : partR f r k := Or.inl hek
    by_cases hcl : (Finset.univ.filter (fun p => ∃ c, r.crash p = some c ∧ 3 < c ∧ c ≤ 3 + f)).card
        < f
    · obtain ⟨t₀, h1, h2, h3⟩ := exists_clean_round r hcl
      have hak' : r.Alive k (3 + f) := by rw [add_comm]; exact hak
      have hvk' : floodVal (d2 n f) r 3 (vhatR f r) k (3 + f) := by rw [add_comm]; exact hvk
      have := FloodRounds.agree (z' := i) floodRounds h1 h2 h3 hpk hak' hvk'
      rw [add_comm] at this
      exact hvi this
    · push Not at hcl
      have hsub : Finset.univ.filter (fun p => ∃ c, r.crash p = some c ∧ 3 < c ∧ c ≤ 3 + f) ⊆
          r.faulty := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨c, hc, -⟩ := hp
        rw [Run.mem_faulty]; simp [Run.Faulty, hc]
      have heq := Finset.eq_of_subset_of_card_le hsub (hr.1.trans hcl)
      have hd0 : ∀ p q, r.Deliv p q 0 := by
        intro p q
        by_cases hp : r.Faulty p
        · have : p ∈ Finset.univ.filter
              (fun p => ∃ c, r.crash p = some c ∧ 3 < c ∧ c ≤ 3 + f) := by
            rw [heq, Run.mem_faulty]; exact hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
          obtain ⟨c, hc, h3, -⟩ := this
          exact ⟨fun c' hc' => by rw [hc] at hc'; cases hc'; omega,
            fun h => by rw [hc] at h; cases h.1; omega⟩
        · exact Run.deliv_of_not_faulty hp q 0
      by_cases hall : ∀ j, r.input j = true
      · exact not_errR_of_clean hall hd0 i hei
      · push Not at hall
        obtain ⟨j, hj⟩ := hall
        simp only [ne_eq, Bool.not_eq_true] at hj
        exact FloodRounds.not_val floodRounds (fun y _ => not_vhatR_of_input_false hfn hr hj y) (f + 3)
          (by omega) k hpk hvk

/-- **D2 solves AC in `γ_f`** (Claim 4 of Goren–Moses), for `1 ≤ f < n`. -/
theorem solvesAC (hf : 1 ≤ f) (hfn : f < n) : SolvesAC (d2 n f) f := by
  intro r hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Decision
    intro i hi
    by_cases he : errR f r i
    · exact ⟨f + 3, _, decidesAt_iff'.2 ⟨Run.alive_of_not_faulty hi _, Or.inr ⟨rfl, he, rfl⟩⟩⟩
    · exact ⟨2, .commit, decidesAt_iff'.2 ⟨Run.alive_of_not_faulty hi _, Or.inl ⟨rfl, he, rfl⟩⟩⟩
  · -- Agreement
    intro i m d i' m' d' h h'
    cases d <;> cases d'
    · rfl
    · exact (no_commit_abort hf hfn hr h' h).elim
    · exact (no_commit_abort hf hfn hr h h').elim
    · rfl
  · -- Commit Validity
    intro i m h j
    rw [decidesAt_iff'] at h
    obtain ⟨-, ⟨rfl, he, -⟩ | ⟨rfl, he, hd⟩⟩ := h
    · exact allOne_of_not_errR hfn hr he j
    · by_contra hj
      simp only [Bool.not_eq_true] at hj
      have hv : floodVal (d2 n f) r 3 (vhatR f r) i (f + 3) := by
        by_contra hv; rw [if_neg hv] at hd; cases hd
      exact FloodRounds.not_val floodRounds (fun y _ => not_vhatR_of_input_false hfn hr hj y) (f + 3)
        (by omega) i (Or.inl he) hv
  · -- Abort Validity
    intro i m h
    by_contra hc
    push Not at hc
    obtain ⟨hin, hnf⟩ := hc
    rw [decidesAt_iff'] at h
    obtain ⟨-, ⟨-, -, h⟩ | ⟨rfl, he, -⟩⟩ := h
    · cases h
    exact not_errR_of_clean (fun j => by simpa using hin j)
      (fun p q => Run.deliv_of_not_faulty (by simpa [Run.Faulty] using hnf p) q 0) i he

/-! ### The nice run -/

lemma nice_not_errR (p : Fin n) : ¬ errR f (nice : Run (Fin n) Bool) p :=
  not_errR_of_clean (fun _ => rfl) (fun p q => Run.deliv_of_not_faulty (nice_not_faulty p) q 0) p

/-- **Claim 3** of Goren–Moses: in the nice run every process commits at time `2` … -/
theorem nice_commit (p : Fin n) : DecidesAt (d2 n f) nice p 2 .commit :=
  decidesAt_iff'.2 ⟨nice_alive p 2, Or.inl ⟨rfl, nice_not_errR p, rfl⟩⟩

/-- … and exactly `f · n` messages are sent. -/
theorem nice_msgs (hfn : f < n) : (msgs (d2 n f) nice).encard = (f * n : ℕ) := by
  have hset : msgs (d2 n f) nice = ((Finset.univ.biUnion fun p : Fin n =>
      (Finset.univ.filter (IsSucc f p)).image (fun q => (p, q, 0))) : Set (Fin n × Fin n × ℕ)) := by
    ext ⟨a, b, t⟩
    simp only [msgs, Set.mem_ofPred_eq, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ,
      Set.iUnion_true, Set.mem_iUnion, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · intro h
      rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ (3 ≤ t ∧ t < f + 3) ∨ f + 3 ≤ t by omega) with
        rfl | rfl | rfl | ⟨h3, hf3⟩ | ht
      · exact ⟨a, b, (sent0.1 h).2.2.2, rfl, rfl, rfl⟩
      · exact absurd (sent1.1 h).2.2 (fun hn => nice_not_errR a (Or.inl hn))
      · exact absurd (sent2.1 h).2.2 (nice_not_errR a)
      · obtain ⟨-, -, hp, -⟩ := (sentF h3 hf3).1 h
        rcases hp with hp | ⟨j, hj⟩
        · exact absurd hp (nice_not_errR a)
        · exact absurd (sent2.1 hj).2.2 (nice_not_errR j)
      · exact absurd h (not_sent_late ht)
    · rintro ⟨p, q, hs, rfl, rfl, rfl⟩
      exact sent0.2 ⟨isSucc_ne hs, Run.deliv_of_not_faulty (nice_not_faulty _) _ 0, rfl, hs⟩
  rw [hset, Set.encard_coe_eq_coe_finsetCard, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun p _ => by
      rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using hab), card_succ hfn p])]
    simp [mul_comm]
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e hea heb
    simp only [Finset.mem_image] at hea heb
    obtain ⟨x, -, rfl⟩ := hea
    obtain ⟨y, -, hy⟩ := heb
    exact hab (congrArg Prod.fst hy).symm

end Papers.PODC2018.Silence.D2
