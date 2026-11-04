import Papers.PODC2010.KBakery.RMRDSM
import Papers.PODC2010.KBakery.Liveness

/-!
# RMR complexity in the CC model (Lemma 7 of the paper, CC part; Lemmas 5.7, 5.8, 5.17–5.19 of
the thesis)

Write-through / write-invalidate caches (`Cfg.cached`): a read is an RMR iff the reader has no
valid copy, every write is an RMR and invalidates all other copies.

The waiting loop is bounded by an amortized argument. While `p` waits with ticket `tp`, the
budget `Bw s p q` counts the writes of `q` to `Want[q][p]` that can still happen before
`Want[q][p]` is good for `p` forever (at most 4: the thesis' "five RMRs" of Lemma 5.7), and
`Bc s p q` does the same for `Capture[q][p]` (at most 2: "three RMRs" of Lemma 5.18). Every
remote read of `p` either consumes an invalid cache line (re-validated only by a budgeted write
of `q`) or is the last read of that variable in the passage.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ} {s : Cfg P}

/-- At line 15 with maximum `acc` so far and `rem` still to read, `q`'s new ticket will exceed `v`
(it will be at least `v + 1`). -/
def WillExceed (s : Cfg P) (v acc : ℕ) (rem : Finset P) : Prop := v ≤ acc ∨ ∃ j ∈ rem, v ≤ s.ticket j

open Classical in
/-- Remaining writes of `q` to `Want[q][p]` before it is good for `p` forever. -/
noncomputable def Bw (s : Cfg P) (p q : P) : ℕ :=
  let tp := s.ticket p
  if lexLt tp p (s.ticket q) q then
    match s.pc q with
    | .d16 rem => if p ∈ rem ∧ ¬ wantGood tp p (s.want q p) q then 1 else 0
    | _ => 0
  else
    match s.pc q with
    | .ncs => 2
    | .d14 rem => if p ∈ rem then 2 else 1
    | .d15 acc rem => if WillExceed s tp acc rem then 1 else 4
    | .d16 rem => if p ∈ rem then 4 else 3
    | .ex rem => if p ∈ rem then 3 else 2
    | _ => 3

/-- `0` if the capture value `cv` exceeds `tp`, else `1`. -/
def goodC (tp cv : ℕ) : ℕ := if tp < cv then 0 else 1

lemma goodC_le (tp cv : ℕ) : goodC tp cv ≤ 1 := by unfold goodC; split_ifs <;> omega

lemma ite_goodC_le (c : Prop) [Decidable c] (tp cv : ℕ) : (if c then goodC tp cv else 2) ≤ 2 := by
  split
  · exact (goodC_le _ _).trans (by norm_num)
  · exact le_rfl

lemma goodC_of_lt {tp cv : ℕ} (h : tp < cv) : goodC tp cv = 0 := by simp [goodC, h]

open Classical in
/-- `Bc` as a function of the data it depends on. -/
noncomputable def BcF (tp : ℕ) (p : P) (tq : ℕ) (c : PC P) (cv : ℕ)
    (we : ℕ → Finset P → Prop) : ℕ :=
  match c with
  | .d15 acc rem => if we acc rem then goodC tp cv else 2
  | .d16 _ | .head _ _ | .scan _ _ | .chk _ _ _ => if tp < tq then goodC tp cv else 2
  | .cap23 rem => if p ∈ rem then (if tp < tq then goodC tp cv else 2) else goodC tp cv
  | _ => goodC tp cv

/-- Remaining writes of `q` to `Capture[q][p]` before it exceeds `Ticket[p]` forever. -/
noncomputable def Bc (s : Cfg P) (p q : P) : ℕ :=
  BcF (s.ticket p) p (s.ticket q) (s.pc q) (s.capture q p) (WillExceed s (s.ticket p))

/-- Cost of a missing cache line. -/
def miss (s : Cfg P) (p : P) (x : Var P) : ℕ := if s.cached p x then 0 else 1

/-- Potential for the reads of `Want[q][p]`. -/
noncomputable def phiW (s : Cfg P) (p q : P) : ℕ :=
  if Bw s p q = 0 then 1 else Bw s p q + miss s p (.want q p)

/-- Potential for the reads of `Capture[q][p]`. -/
noncomputable def phiC (s : Cfg P) (p q : P) : ℕ :=
  if q = p then miss s p (.capture p p)
  else if Bc s p q = 0 then 1 else Bc s p q + miss s p (.capture q p)

/-- `p` will read `Capture[q][p]` again in this passage. -/
def WillRead (q : P) : PC P → Prop
  | .head _ cap => cap = false
  | .scan _ _ => True
  | .chk _ rem cap => q ∈ rem ∨ cap = false
  | _ => False

instance (q : P) (c : PC P) : Decidable (WillRead q c) := by
  unfold WillRead; split <;> infer_instance

/-- Reserved RMRs for the loop and the rest of the passage. -/
def ccReserve (fife : Bool) (N : ℕ) : ℕ := 5 * (N - 1) + (if fife then 3 * N + N else 0) + N

/-- The total CC budget of a passage: `(N − 1) + (N + 1) + (N − 1) + ccReserve`, i.e.
`9N − 6` (unshaded) or `13N − 6` (full algorithm) for `N ≥ 1`. -/
def ccTotal (fife : Bool) (N : ℕ) : ℕ := (N - 1) + (N + 1) + (N - 1) + ccReserve fife N

/-- The CC potential of `p`'s passage. -/
noncomputable def ccPot (fife : Bool) (s : Cfg P) (p : P) : ℕ :=
  let N := Fintype.card P
  match s.pc p with
  | .ncs => 0
  | .d14 rem => rem.card + (N + 1) + (N - 1) + ccReserve fife N
  | .d15 _ rem => rem.card + 1 + (N - 1) + ccReserve fife N
  | .d16 rem => rem.card + ccReserve fife N
  | .head pred _ | .scan pred _ | .chk pred _ _ =>
    (∑ q ∈ pred, phiW s p q) +
      (if fife then ∑ q ∈ univ.filter (fun q => WillRead q (s.pc p)), phiC s p q else 0) +
      (if fife then N else 0) + N
  | .cap23 rem => rem.card + N
  | .cs => N
  | .ex rem => rem.card

lemma Bw_le (s : Cfg P) (p q : P) : Bw s p q ≤ 4 := by
  unfold Bw; dsimp only; split_ifs <;> split <;> (try split_ifs) <;> omega

lemma Bc_le (s : Cfg P) (p q : P) : Bc s p q ≤ 2 := by
  have := goodC_le (s.ticket p) (s.capture q p)
  unfold Bc BcF; split <;> (try split_ifs) <;> omega

lemma phiW_le (s : Cfg P) (p q : P) : phiW s p q ≤ 5 := by
  have := Bw_le s p q
  unfold phiW miss; split_ifs <;> omega

lemma phiC_le (s : Cfg P) (p q : P) : phiC s p q ≤ 3 := by
  have := Bc_le s p q
  unfold phiC miss; split_ifs <;> omega

lemma wantGood_of_Bw (hI : Inv k s) {p q : P} (hqp : q ≠ p) (h : Bw s p q = 0) :
    wantGood (s.ticket p) p (s.want q p) q := by
  have hw := hI.wantC q p hqp
  unfold WantSpec at hw
  unfold Bw at h
  dsimp only at h
  split_ifs at h with hg
  · rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc] at h hw <;>
      (try split_ifs at hw) <;> (try split_ifs at h) <;>
      first
      | (rw [hw]; exact Or.inl (WithTop.coe_lt_top _))
      | (rw [hw]; exact wantGood_coe.2 hg)
      | (by_contra hh; exact ‹¬(_ ∧ _)› ⟨‹p ∈ rem'›, hh⟩)
  · rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc] at h <;>
      (try split_ifs at h) <;> omega

lemma cached_step_of_ne {r p i : P} (h : r ≠ p) (x : Var P) :
    (stepAt fife k s r i).cached p x =
      (if access s r i = some (true, x) then false else s.cached p x) := by
  simp only [stepAt_cached]
  unfold updCache
  rcases hacc : access s r i with _ | ⟨_ | _, y⟩
  · simp
  · simp [Ne.symm h]
  · by_cases hy : x = y
    · subst hy; simp [Ne.symm h]
    · simp [hy, Ne.symm hy]

/-- A process writes only its own `Want[r][·]`, `Ticket[r]`, `Capture[r][·]`. -/
lemma access_write {r i : P} {x : Var P} (h : access s r i = some (true, x)) :
    (∃ j, x = .want r j) ∨ x = .ticket r ∨ ∃ j, x = .capture r j := by
  unfold access at h
  split at h <;> (try split_ifs at h) <;> simp at h <;> subst h <;> simp

lemma miss_step_of_ne {r p i : P} (h : r ≠ p) {x : Var P}
    (hx : access s r i ≠ some (true, x)) :
    miss (stepAt fife k s r i) p x = miss s p x := by
  unfold miss; rw [cached_step_of_ne h, if_neg hx]

lemma WillExceed.mono {s s' : Cfg P} {v acc : ℕ} {rem : Finset P}
    (ht : ∀ j, s.ticket j ≤ s'.ticket j) (h : WillExceed s v acc rem) : WillExceed s' v acc rem := by
  rcases h with h | ⟨j, hj, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, hj, h.trans (ht j)⟩

/-- Steps of a third process do not increase `Bw` and `Bc`. -/
lemma Bw_Bc_other (hI : Inv k s) {r p q i : P} (ha : Admissible s r i) (hrp : r ≠ p) (hrq : r ≠ q) :
    Bw (stepAt fife k s r i) p q ≤ Bw s p q ∧ Bc (stepAt fife k s r i) p q ≤ Bc s p q := by
  have htp : (stepAt fife k s r i).ticket p = s.ticket p := by
    rw [stepAt_ticket, core_ticket_ne (Ne.symm hrp)]
  have htq : (stepAt fife k s r i).ticket q = s.ticket q := by
    rw [stepAt_ticket, core_ticket_ne (Ne.symm hrq)]
  have hpcq : (stepAt fife k s r i).pc q = s.pc q := by
    rw [stepAt_pc, core_pc_ne (Ne.symm hrq)]
  have hwq : (stepAt fife k s r i).want q = s.want q := by
    rw [stepAt_want, core_want_ne (Ne.symm hrq)]
  have hcq : (stepAt fife k s r i).capture q = s.capture q := by
    rw [stepAt_capture, core_capture_ne (Ne.symm hrq)]
  have hmono : ∀ j, s.ticket j ≤ (stepAt fife k s r i).ticket j := ticket_mono hI ha
  generalize stepAt fife k s r i = s' at *
  have hWE : ∀ acc rem, WillExceed s (s.ticket p) acc rem → WillExceed s' (s.ticket p) acc rem :=
    fun _ _ h => WillExceed.mono hmono h
  constructor
  · unfold Bw
    rw [htp, htq, hpcq, hwq]
    dsimp only
    split_ifs <;> (try split) <;> (try split_ifs) <;> first | omega | exact absurd (hWE _ _ ‹_›) ‹_›
  · unfold Bc
    rw [htp, htq, hpcq, hcq]
    have := goodC_le (s.ticket p) (s.capture q p)
    unfold BcF
    split <;> (try split_ifs) <;> first | omega | exact absurd (hWE _ _ ‹_›) ‹_›

open Classical in
/-- `Bw` as a function of the data it depends on. -/
noncomputable def BwF (tp : ℕ) (p q : P) (tq : ℕ) (c : PC P) (w : WithTop ℕ)
    (we : ℕ → Finset P → Prop) : ℕ :=
  if lexLt tp p tq q then
    match c with
    | .d16 rem => if p ∈ rem ∧ ¬ wantGood tp p w q then 1 else 0
    | _ => 0
  else
    match c with
    | .ncs => 2
    | .d14 rem => if p ∈ rem then 2 else 1
    | .d15 acc rem => if we acc rem then 1 else 4
    | .d16 rem => if p ∈ rem then 4 else 3
    | .ex rem => if p ∈ rem then 3 else 2
    | _ => 3

lemma Bw_eq {p q : P} : Bw s p q = BwF (s.ticket p) p q (s.ticket q) (s.pc q) (s.want q p)
    (WillExceed s (s.ticket p)) := rfl

/-- Steps of `q` itself: `Bw` never increases, stays `0` once `0`, and every write of `q` to
`Want[q][p]` decreases a positive `Bw`. -/
lemma Bw_self (hI : Inv k s) {p q i : P} (ha : Admissible s q i) (hqp : q ≠ p) :
    Bw (stepAt fife k s q i) p q ≤ Bw s p q ∧ (Bw s p q = 0 → Bw (stepAt fife k s q i) p q = 0) ∧
      (access s q i = some (true, .want q p) → Bw s p q ≠ 0 →
        Bw (stepAt fife k s q i) p q < Bw s p q) := by
  have htp : (stepAt fife k s q i).ticket p = s.ticket p := by
    rw [stepAt_ticket, core_ticket_ne (Ne.symm hqp)]
  have hmono : ∀ j, s.ticket j ≤ (stepAt fife k s q i).ticket j := ticket_mono hI ha
  have hw := hI.wantC q p hqp
  unfold WantSpec at hw
  rw [Bw_eq (s := stepAt fife k s q i), Bw_eq (s := s), htp]
  have hWE : ∀ acc rem, WillExceed s (s.ticket p) acc rem →
      WillExceed (stepAt fife k s q i) (s.ticket p) acc rem :=
    fun _ _ h => WillExceed.mono hmono h
  have hWEp : ∀ acc rem, p ∈ rem → WillExceed (stepAt fife k s q i) (s.ticket p) acc rem :=
    fun _ _ h => Or.inr ⟨p, h, by rw [htp]⟩
  have hWEr : ∀ acc rem j, j ∈ rem → WillExceed s (s.ticket p) acc rem →
      WillExceed (stepAt fife k s q i) (s.ticket p) (max acc (s.ticket j)) (rem.erase j) := by
    intro acc rem j hj h
    rcases h with h | ⟨j', hj', h⟩
    · exact Or.inl (le_max_of_le_left h)
    · by_cases hjj : j' = j
      · subst hjj; exact Or.inl (le_max_of_le_right h)
      · exact Or.inr ⟨j', mem_erase.2 ⟨hjj, hj'⟩, h.trans (hmono j')⟩
  generalize WillExceed (stepAt fife k s q i) (s.ticket p) = we' at hWE hWEp hWEr ⊢
  simp only [stepAt_pc, stepAt_ticket, stepAt_want]
  rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc] at hw <;>
    simp only [core, hpc, access] <;>
    (try split_ifs) <;> (try cases fife) <;>
    simp [BwF, Function.update_apply, hqp.symm] <;> (try split_ifs) <;> (try omega) <;>
    (try simp_all) <;> (try omega) <;> (try first
      | exact fun h => ‹¬p = i› h.symm
      | exact fun h => ‹p ∉ _› (h ▸ ‹i ∈ _›)
      | (have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using ‹i ∉ _›)
         simp only [hpc, PC.rem] at h0; subst h0; simp_all; done)
      | (split_ifs <;> omega)
      | (have := hWEr acc' rem' i ‹_›; split_ifs <;> simp_all; done)
      | (have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using ‹i ∉ _›)
         simp only [hpc, PC.rem] at h0; subst h0
         have hg1 := hI.g1 q acc' ∅ hpc (by simp)
         first
         | exact ‹¬wantGood _ _ _ _› (wantGood_coe.2 ‹lexLt _ _ (s.ticket q) _›)
         | exact ‹¬lexLt _ _ (acc' + 1) _› (lexLt_mono ‹lexLt _ _ (s.ticket q) _› (by omega))
         | (rcases ‹WillExceed s _ _ _› with h | ⟨j, hj, _⟩
            · exact ‹¬lexLt _ _ (acc' + 1) _› (Or.inl (by omega))
            · simp at hj)))

lemma Bc_eq {p q : P} : Bc s p q = BcF (s.ticket p) p (s.ticket q) (s.pc q) (s.capture q p)
    (WillExceed s (s.ticket p)) := rfl

set_option maxHeartbeats 1000000 in
lemma Bc_self (hI : Inv k s) {p q i : P} (ha : Admissible s q i) (hqp : q ≠ p) :
    Bc (stepAt fife k s q i) p q ≤ Bc s p q ∧ (Bc s p q = 0 → Bc (stepAt fife k s q i) p q = 0) ∧
      (access s q i = some (true, .capture q p) → Bc s p q ≠ 0 →
        Bc (stepAt fife k s q i) p q < Bc s p q) := by
  have htp : (stepAt fife k s q i).ticket p = s.ticket p := by
    rw [stepAt_ticket, core_ticket_ne (Ne.symm hqp)]
  have hmono : ∀ j, s.ticket j ≤ (stepAt fife k s q i).ticket j := ticket_mono hI ha
  rw [Bc_eq (s := stepAt fife k s q i), Bc_eq (s := s), htp]
  have hWE : ∀ acc rem, WillExceed s (s.ticket p) acc rem →
      WillExceed (stepAt fife k s q i) (s.ticket p) acc rem :=
    fun _ _ h => WillExceed.mono hmono h
  have hWEp : ∀ acc rem, p ∈ rem → WillExceed (stepAt fife k s q i) (s.ticket p) acc rem :=
    fun _ _ h => Or.inr ⟨p, h, by rw [htp]⟩
  have hWEr : ∀ acc rem j, j ∈ rem → WillExceed s (s.ticket p) acc rem →
      WillExceed (stepAt fife k s q i) (s.ticket p) (max acc (s.ticket j)) (rem.erase j) := by
    intro acc rem j hj h
    rcases h with h | ⟨j', hj', h⟩
    · exact Or.inl (le_max_of_le_left h)
    · by_cases hjj : j' = j
      · subst hjj; exact Or.inl (le_max_of_le_right h)
      · exact Or.inr ⟨j', mem_erase.2 ⟨hjj, hj'⟩, h.trans (hmono j')⟩
  generalize WillExceed (stepAt fife k s q i) (s.ticket p) = we' at hWE hWEp hWEr ⊢
  have g1 := goodC_le (s.ticket p) (s.capture q p)
  have g2 := goodC_le (s.ticket p) (s.ticket q)
  have g3 : s.ticket p < s.ticket q → goodC (s.ticket p) (s.ticket q) = 0 := goodC_of_lt
  simp only [stepAt_pc, stepAt_ticket, stepAt_capture]
  rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;>
    simp only [core, hpc, access] <;>
    (try split_ifs) <;> (try cases fife) <;>
    simp [BcF, Function.update_apply, hqp.symm] <;> (try split_ifs) <;> (try omega) <;>
    (try simp_all) <;> (try omega) <;> (try first
      | exact fun h => ‹¬p = i› h.symm
      | exact fun h => ‹p ∉ _› (h ▸ ‹i ∈ _›)
      | (have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using ‹i ∉ _›)
         simp only [hpc, PC.rem] at h0; subst h0; simp_all; done)
      | (split_ifs <;> omega)
      | (have := hWEr acc' rem' i ‹_›; split_ifs <;> simp_all; done)
      | (intro h; exact absurd (h ▸ ‹i ∈ rem'›) ‹p ∉ rem'›)
      | (intro h; exact absurd h.symm ‹¬p = i›)
      | (split <;> omega)
      | exact ite_goodC_le _ _ _
      | (have h0 := admissible_of_not_mem ha (by simpa [hpc, PC.rem] using ‹i ∉ _›)
         simp only [hpc, PC.rem] at h0; subst h0
         rcases ‹WillExceed s _ _ _› with h | ⟨j, hj, _⟩
         · omega
         · simp at hj))

lemma lt_capture_of_Bc {s : Cfg P} {p q : P} (h : Bc s p q = 0) : s.ticket p < s.capture q p := by
  by_contra hc
  have hg : goodC (s.ticket p) (s.capture q p) = 1 := by simp [goodC, hc]
  unfold Bc BcF at h
  split at h <;> (try split_ifs at h) <;> omega

/-- Steps of other processes never increase `phiW s p q`. -/
lemma phiW_step (hI : Inv k s) {r p q i : P} (ha : Admissible s r i) (hrp : r ≠ p) (hqp : q ≠ p) :
    phiW (stepAt fife k s r i) p q ≤ phiW s p q := by
  have hB := Bw_le s p q
  by_cases hrq : r = q
  · subst hrq
    obtain ⟨h1, h2, h3⟩ := Bw_self (fife := fife) (k := k) hI ha hqp
    unfold phiW miss
    rw [cached_step_of_ne hrp]
    by_cases hw : access s r i = some (true, .want r p)
    · have := h3 hw
      simp only [hw, if_true]
      split_ifs <;> simp_all <;> omega
    · simp only [hw, if_false]
      split_ifs <;> simp_all <;> omega
  · have h1 := (Bw_Bc_other (fife := fife) hI ha hrp hrq).1
    have hm : miss (stepAt fife k s r i) p (.want q p) = miss s p (.want q p) := by
      apply miss_step_of_ne hrp
      intro h
      rcases access_write h with ⟨j, hj⟩ | hj | ⟨j, hj⟩ <;> simp at hj
      exact hrq hj.1.symm
    unfold phiW
    rw [hm]
    split_ifs <;> omega

/-- Steps of other processes never increase `phiC s p q`. -/
lemma phiC_step (hI : Inv k s) {r p q i : P} (ha : Admissible s r i) (hrp : r ≠ p) :
    phiC (stepAt fife k s r i) p q ≤ phiC s p q := by
  by_cases hqp : q = p
  · subst hqp
    have hm : miss (stepAt fife k s r i) q (.capture q q) = miss s q (.capture q q) := by
      apply miss_step_of_ne hrp
      intro h
      rcases access_write h with ⟨j, hj⟩ | hj | ⟨j, hj⟩ <;> simp at hj
      exact hrp hj.1.symm
    simp [phiC, hm]
  have hB := Bc_le s p q
  by_cases hrq : r = q
  · subst hrq
    obtain ⟨h1, h2, h3⟩ := Bc_self (fife := fife) (k := k) hI ha hqp
    unfold phiC miss
    simp only [hqp, if_false]
    rw [cached_step_of_ne hrp (.capture r p)]
    by_cases hw : access s r i = some (true, .capture r p)
    · have := h3 hw
      simp only [hw, if_true]
      split_ifs <;> simp_all <;> omega
    · simp only [hw, if_false]
      split_ifs <;> simp_all <;> omega
  · have h1 := (Bw_Bc_other (fife := fife) hI ha hrp hrq).2
    have hm : miss (stepAt fife k s r i) p (.capture q p) = miss s p (.capture q p) := by
      apply miss_step_of_ne hrp
      intro h
      rcases access_write h with ⟨j, hj⟩ | hj | ⟨j, hj⟩ <;> simp at hj
      exact hrq hj.1.symm
    unfold phiC
    rw [hm]
    simp only [hqp, if_false]
    split_ifs <;> omega

/-- Steps of other processes never increase the potential of `p`. -/
lemma ccPot_other (hI : Inv k s) {r p i : P} (ha : Admissible s r i) (hrp : r ≠ p) :
    ccPot fife (stepAt fife k s r i) p ≤ ccPot fife s p := by
  have hpc : (stepAt fife k s r i).pc p = s.pc p := by rw [stepAt_pc, core_pc_ne (Ne.symm hrp)]
  have hpred := hI.predNot p
  unfold ccPot
  rw [hpc]
  have hW : ∀ pred : Finset P, p ∉ pred →
      ∑ q ∈ pred, phiW (stepAt fife k s r i) p q ≤ ∑ q ∈ pred, phiW s p q := fun pred hp =>
    sum_le_sum fun q hq => phiW_step hI ha hrp (fun h => hp (h ▸ hq))
  have hC : ∀ t : Finset P, ∑ q ∈ t, phiC (stepAt fife k s r i) p q ≤ ∑ q ∈ t, phiC s p q :=
    fun t => sum_le_sum fun q _ => phiC_step hI ha hrp
  rcases hpc' : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc', PC.pred] at hpred <;>
    dsimp only <;> (try exact le_rfl) <;>
    (have := hW pred hpred; have := hC (univ.filter fun q => WillRead q (s.pc p));
     rw [hpc'] at this; split_ifs <;> omega)

-- CSLib candidate: `Cslib/Foundations/Data/Finset` (amortized cost of one charged element)
/-- Cost accounting for one read in the loop: `c` is the cost of the read of the variable of
`i`, `f`/`f'` the potentials before/after. -/
lemma sum_cost_le {t t' : Finset P} {f f' : P → ℕ} {i : P} {c : ℕ} (hsub : t' ⊆ t) (hi : i ∈ t)
    (hle : ∀ q ∈ t', f' q ≤ f q) (h1 : i ∈ t' → f' i + c ≤ f i) (h2 : c ≤ f i) :
    c + ∑ q ∈ t', f' q ≤ ∑ q ∈ t, f q := by
  by_cases hit : i ∈ t'
  · rw [← add_sum_erase t' f' hit, ← add_sum_erase t f hi]
    have h3 : ∑ q ∈ t'.erase i, f' q ≤ ∑ q ∈ t.erase i, f q :=
      (sum_le_sum fun q hq => hle q (mem_of_mem_erase hq)).trans
        (sum_le_sum_of_subset (erase_subset_erase i hsub))
    have := h1 hit
    omega
  · rw [← add_sum_erase t f hi]
    have h3 : ∑ q ∈ t', f' q ≤ ∑ q ∈ t.erase i, f q :=
      (sum_le_sum hle).trans (sum_le_sum_of_subset fun q hq =>
        mem_erase.2 ⟨fun h => hit (h ▸ hq), hsub hq⟩)
    omega

lemma WillExceed_congr {s s' : Cfg P} (h : s'.ticket = s.ticket) : WillExceed s' = WillExceed s := by
  funext v acc rem; simp [WillExceed, h]

lemma loop_ticket {p i : P} (h : (s.pc p).InLoop) : (stepAt fife k s p i).ticket = s.ticket := by
  rw [stepAt_ticket]
  rcases hpc : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp [hpc, PC.InLoop] at h <;>
    simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;> rfl

/-- In the loop, steps of `p` do not change the budgets. -/
lemma loop_B_eq {p i q : P} (h : (s.pc p).InLoop) (hqp : q ≠ p) :
    Bw (stepAt fife k s p i) p q = Bw s p q ∧ Bc (stepAt fife k s p i) p q = Bc s p q := by
  have ht := loop_ticket (fife := fife) (k := k) (i := i) h
  have hpc : (stepAt fife k s p i).pc q = s.pc q := by rw [stepAt_pc, core_pc_ne hqp]
  have hw : (stepAt fife k s p i).want q = s.want q := by rw [stepAt_want, core_want_ne hqp]
  have hc : (stepAt fife k s p i).capture q = s.capture q := by
    rw [stepAt_capture, core_capture_ne hqp]
  have hwe := WillExceed_congr ht
  constructor
  · rw [Bw_eq, Bw_eq (s := s), ht, hpc, hw, hwe]
  · rw [Bc_eq, Bc_eq (s := s), ht, hpc, hc, hwe]

lemma loop_access {p i : P} (h : (s.pc p).InLoop) :
    access s p i = none ∨ ∃ x, access s p i = some (false, x) := by
  unfold access
  rcases hpc : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp [hpc, PC.InLoop] at h <;> simp only <;>
    (try split_ifs) <;> simp

/-- In the loop, steps of `p` only add valid cache lines of `p`. -/
lemma loop_miss_le {p i : P} (h : (s.pc p).InLoop) (x : Var P) :
    miss (stepAt fife k s p i) p x ≤ miss s p x := by
  unfold miss
  rcases loop_access (i := i) h with ha | ⟨y, ha⟩ <;> simp only [stepAt_cached, ha, updCache]
  · exact le_rfl
  · split_ifs <;> simp_all

lemma loop_miss_read {p i : P} {x : Var P} (ha : access s p i = some (false, x)) :
    miss (stepAt fife k s p i) p x = 0 := by
  simp [miss, ha, updCache]

lemma phiW_loop_le {p i q : P} (h : (s.pc p).InLoop) (hqp : q ≠ p) :
    phiW (stepAt fife k s p i) p q ≤ phiW s p q := by
  have hB := (loop_B_eq (fife := fife) (k := k) (i := i) h hqp).1
  have hm := loop_miss_le (fife := fife) (k := k) (i := i) h (.want q p)
  unfold phiW; rw [hB]; split_ifs <;> omega

lemma phiC_loop_le {p i q : P} (h : (s.pc p).InLoop) :
    phiC (stepAt fife k s p i) p q ≤ phiC s p q := by
  by_cases hqp : q = p
  · subst hqp
    have hm := loop_miss_le (fife := fife) (k := k) (i := i) h (.capture q q)
    simp only [phiC, if_true]; exact hm
  have hB := (loop_B_eq (fife := fife) (k := k) (i := i) h hqp).2
  have hm := loop_miss_le (fife := fife) (k := k) (i := i) h (.capture q p)
  unfold phiC; rw [hB]; simp only [hqp, if_false]; split_ifs <;> omega

/-- Passage-local facts of `p`: a scan visits a subset of the predecessor set; line 22 is only
reached in the full algorithm. -/
def LoopOK (fife : Bool) (p : P) : PC P → Prop
  | .scan pred rem => rem ⊆ pred
  | .chk _ _ _ => fife = true
  | _ => True

lemma rmrCC_le_miss {p i : P} {x : Var P} (ha : access s p i = some (false, x)) :
    (if rmrCC s p i then 1 else 0) = miss s p x := by
  simp [rmrCC, ha, miss]; split_ifs <;> simp_all

lemma phiW_ge_miss {p q : P} : miss s p (.want q p) ≤ phiW s p q := by
  have : miss s p (.want q p) ≤ 1 := by unfold miss; split_ifs <;> omega
  unfold phiW; split_ifs <;> omega

lemma phiC_ge_miss {p q : P} : miss s p (.capture q p) ≤ phiC s p q := by
  have : miss s p (.capture q p) ≤ 1 := by unfold miss; split_ifs <;> omega
  unfold phiC; split_ifs with h1 <;> (try subst h1) <;> omega

lemma sum_phiW_le (s : Cfg P) (p : P) (t : Finset P) : ∑ q ∈ t, phiW s p q ≤ 5 * t.card := by
  calc ∑ q ∈ t, phiW s p q ≤ ∑ _q ∈ t, 5 := sum_le_sum fun q _ => phiW_le s p q
    _ = 5 * t.card := by rw [sum_const, smul_eq_mul, mul_comm]

lemma sum_phiC_le (s : Cfg P) (p : P) (t : Finset P) : ∑ q ∈ t, phiC s p q ≤ 3 * t.card := by
  calc ∑ q ∈ t, phiC s p q ≤ ∑ _q ∈ t, 3 := sum_le_sum fun q _ => phiC_le s p q
    _ = 3 * t.card := by rw [sum_const, smul_eq_mul, mul_comm]

lemma ccPot_self (hI : Inv k s) {p i : P} (ha : Admissible s p i) (hn : s.pc p ≠ .ncs)
    (hlo : LoopOK fife p (s.pc p)) :
    (if rmrCC s p i then 1 else 0) + ccPot fife (stepAt fife k s p i) p ≤ ccPot fife s p ∧
      LoopOK fife p ((stepAt fife k s p i).pc p) := by
  have he : (univ.erase p).card = Fintype.card P - 1 := by
    rw [card_erase_of_mem (mem_univ p), card_univ]
  have hrem : ∀ rem : Finset P, i ∉ rem → (s.pc p).rem = rem → rem = ∅ := by
    intro rem hi h
    have := admissible_of_not_mem ha (by rw [h]; exact hi)
    rwa [h] at this
  have hcard : ∀ t : Finset P, t.card ≤ Fintype.card P := fun t => card_le_univ t
  rcases hpc : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc, PC.rem] at hn hrem hlo
  · exact absurd rfl hn
  · -- line 14
    by_cases hi : i ∈ rem'
    · have := card_erase_add_one hi
      simp [ccPot, stepAt_pc, core, hpc, hi, rmrCC, access, LoopOK]; omega
    · have := hrem rem' hi rfl; subst this
      simp [ccPot, stepAt_pc, core, hpc, rmrCC, access, LoopOK]
  · -- line 15
    by_cases hi : i ∈ rem'
    · have := card_erase_add_one hi
      simp [ccPot, stepAt_pc, core, hpc, hi, rmrCC, access, LoopOK]
      split_ifs <;> omega
    · have := hrem rem' hi rfl; subst this
      simp [ccPot, stepAt_pc, core, hpc, rmrCC, access, LoopOK, he]; omega
  · -- line 16
    by_cases hi : i ∈ rem'
    · have := card_erase_add_one hi
      simp [ccPot, stepAt_pc, core, hpc, hi, rmrCC, access, LoopOK]; omega
    · have := hrem rem' hi rfl; subst this
      have h1 := sum_phiW_le (stepAt fife k s p i) p (univ.erase p)
      have h2 := sum_phiC_le (stepAt fife k s p i) p
        (univ.filter fun q => WillRead q (PC.head (univ.erase p) false : PC P))
      have h3 := hcard (univ.filter fun q => WillRead q (PC.head (univ.erase p) false : PC P))
      have hpc' : (stepAt fife k s p i).pc p = .head (univ.erase p) false := by
        simp [core, hpc]
      have hr : rmrCC s p i = false := by simp [rmrCC, access, hpc]
      refine ⟨?_, by rw [hpc']; trivial⟩
      rw [hr]
      simp only [ccPot, hpc', hpc]
      simp only [ccReserve, card_empty]
      rw [he] at h1
      cases fife <;> simp <;> omega
  · -- line 19
    have hloop : (s.pc p).InLoop := by simp [hpc, PC.InLoop]
    have hr : rmrCC s p i = false := by simp [rmrCC, access, hpc]
    rw [hr]
    simp only [Bool.false_eq_true, if_false, zero_add]
    have hW : ∑ q ∈ pred, phiW (stepAt fife k s p i) p q ≤ ∑ q ∈ pred, phiW s p q := by
      have hp := hI.predNot p; rw [hpc] at hp
      exact sum_le_sum fun q hq => phiW_loop_le hloop (fun h => hp (h ▸ hq))
    have hC : ∀ t : Finset P, ∑ q ∈ t, phiC (stepAt fife k s p i) p q ≤ ∑ q ∈ t, phiC s p q :=
      fun t => sum_le_sum fun q _ => phiC_loop_le hloop
    by_cases hk : k ≤ pred.card ∧ cap = false
    · have hpc' : (stepAt fife k s p i).pc p = .scan pred pred := by simp [core, hpc, hk]
      refine ⟨?_, by rw [hpc']; exact subset_refl _⟩
      simp only [ccPot, hpc', hpc, hk.2, WillRead]
      have := hC univ
      simp only [filter_true]
      split_ifs <;> omega
    · cases fife
      · have hpc' : (stepAt false k s p i).pc p = .cs := by simp [core, hpc, hk]
        refine ⟨?_, by rw [hpc']; trivial⟩
        simp only [ccPot, hpc', hpc]; simp
      · have hpc' : (stepAt true k s p i).pc p = .cap23 univ := by simp [core, hpc, hk]
        refine ⟨?_, by rw [hpc']; trivial⟩
        simp only [ccPot, hpc', hpc]; simp
  · -- lines 20–21
    have hloop : (s.pc p).InLoop := by simp [hpc, PC.InLoop]
    have hp := hI.predNot p; rw [hpc] at hp
    have hC : ∀ t : Finset P, ∑ q ∈ t, phiC (stepAt fife k s p i) p q ≤ ∑ q ∈ t, phiC s p q :=
      fun t => sum_le_sum fun q _ => phiC_loop_le hloop
    by_cases hi : i ∈ rem'
    · have hip : i ≠ p := fun h => hI.scanNot p pred rem' hpc (h ▸ hi)
      have hacc : access s p i = some (false, .want i p) := by simp [access, hpc, hi]
      rw [rmrCC_le_miss hacc]
      have hpc' : (stepAt fife k s p i).pc p = .scan
          (if wantGood (s.ticket p) p (s.want i p) i then pred.erase i else pred) (rem'.erase i) := by
        simp [core, hpc, hi]
      have hiP : i ∈ pred := hlo hi
      refine ⟨?_, ?_⟩
      · simp only [ccPot, hpc', hpc, WillRead]
        have hcost : miss s p (.want i p) + ∑ q ∈ (if wantGood (s.ticket p) p (s.want i p) i
            then pred.erase i else pred), phiW (stepAt fife k s p i) p q ≤
            ∑ q ∈ pred, phiW s p q := by
          apply sum_cost_le (i := i)
          · split_ifs
            · exact erase_subset i pred
            · exact subset_refl _
          · exact hiP
          · intro q hq
            have : q ∈ pred := by split_ifs at hq <;> [exact mem_of_mem_erase hq; exact hq]
            exact phiW_loop_le hloop (fun h => hp (h ▸ this))
          · intro hmem
            have hg : ¬ wantGood (s.ticket p) p (s.want i p) i := by
              intro hg; rw [if_pos hg] at hmem; simp at hmem
            have hB : Bw s p i ≠ 0 := fun h0 => hg (wantGood_of_Bw hI hip h0)
            have hB' := (loop_B_eq (fife := fife) (k := k) (i := i) hloop hip).1
            have hm := loop_miss_read (fife := fife) (k := k) hacc
            unfold phiW; rw [hB', hm]; simp only [hB, if_false]; omega
          · exact phiW_ge_miss
        have := hC univ
        split_ifs at hcost ⊢ <;> (try simp only [filter_true]) <;> omega
      · rw [hpc']; simp only [LoopOK]
        split_ifs
        · exact erase_subset_erase i hlo
        · exact (erase_subset i rem').trans hlo
    · have := hrem rem' hi rfl; subst this
      have hr : rmrCC s p i = false := by simp [rmrCC, access, hpc]
      rw [hr]
      simp only [Bool.false_eq_true, if_false, zero_add]
      have hW : ∑ q ∈ pred, phiW (stepAt fife k s p i) p q ≤ ∑ q ∈ pred, phiW s p q :=
        sum_le_sum fun q hq => phiW_loop_le hloop (fun h => hp (h ▸ hq))
      cases fife
      · have hpc' : (stepAt false k s p i).pc p = .head pred false := by simp [core, hpc]
        refine ⟨?_, by rw [hpc']; trivial⟩
        simp only [ccPot, hpc', hpc]; simp; omega
      · have hpc' : (stepAt true k s p i).pc p = .chk pred univ false := by simp [core, hpc]
        refine ⟨?_, by rw [hpc']; trivial⟩
        have := hC univ
        simp only [ccPot, hpc', hpc, WillRead]; simp; omega
  · -- line 22
    subst hlo
    have hloop : (s.pc p).InLoop := by simp [hpc, PC.InLoop]
    have hp := hI.predNot p; rw [hpc] at hp
    have hW : ∑ q ∈ pred, phiW (stepAt true k s p i) p q ≤ ∑ q ∈ pred, phiW s p q :=
      sum_le_sum fun q hq => phiW_loop_le hloop (fun h => hp (h ▸ hq))
    by_cases hi : i ∈ rem'
    · have hacc : access s p i = some (false, .capture i p) := by simp [access, hpc, hi]
      rw [rmrCC_le_miss hacc]
      set cap' := cap || decide (s.ticket p < s.capture i p) with hcap'
      have hpc' : (stepAt true k s p i).pc p = .chk pred (rem'.erase i) cap' := by
        simp [core, hpc, hi, hcap']
      refine ⟨?_, by rw [hpc']; trivial⟩
      simp only [ccPot, hpc', hpc, if_true]
      have hcost : miss s p (.capture i p) +
          ∑ q ∈ univ.filter (fun q => WillRead q (PC.chk pred (rem'.erase i) cap')),
            phiC (stepAt true k s p i) p q ≤
          ∑ q ∈ univ.filter (fun q => WillRead q (PC.chk pred rem' cap)), phiC s p q := by
        apply sum_cost_le (i := i)
        · intro q hq
          rw [mem_filter] at hq ⊢
          simp only [mem_univ, true_and, WillRead] at hq ⊢
          rcases hq with hq | hq
          · exact Or.inl (mem_of_mem_erase hq)
          · right; simp [hcap'] at hq; exact hq.1
        · rw [mem_filter]; simp [WillRead, hi]
        · exact fun q _ => phiC_loop_le hloop
        · intro hmem
          rw [mem_filter] at hmem
          simp only [mem_univ, true_and, WillRead] at hmem
          have hlt : ¬ s.ticket p < s.capture i p := by
            rcases hmem with h | h
            · simp at h
            · simp [hcap'] at h; exact not_lt.2 h.2
          have hm := loop_miss_read (fife := true) (k := k) hacc
          by_cases hip : i = p
          · subst hip
            simp only [phiC, if_true]; rw [hm]; omega
          · have hB : Bc s p i ≠ 0 := fun h0 => hlt (lt_capture_of_Bc h0)
            have hB' := (loop_B_eq (fife := true) (k := k) (i := i) hloop hip).2
            unfold phiC; rw [hB', hm]; simp only [hip, hB, if_false]; omega
        · exact phiC_ge_miss
      omega
    · have := hrem rem' hi rfl; subst this
      have hr : rmrCC s p i = false := by simp [rmrCC, access, hpc]
      rw [hr]
      simp only [Bool.false_eq_true, if_false, zero_add]
      have hpc' : (stepAt true k s p i).pc p = .head pred cap := by simp [core, hpc]
      refine ⟨?_, by rw [hpc']; trivial⟩
      have hC : ∑ q ∈ univ.filter (fun q => WillRead q (PC.head pred cap : PC P)),
          phiC (stepAt true k s p i) p q ≤
          ∑ q ∈ univ.filter (fun q => WillRead q (PC.head pred cap : PC P)), phiC s p q :=
        sum_le_sum fun q _ => phiC_loop_le hloop
      simp only [ccPot, hpc', hpc, if_true]
      have heq : (univ.filter fun q => WillRead q (PC.chk pred (∅ : Finset P) cap)) =
          univ.filter fun q => WillRead q (PC.head pred cap : PC P) := by
        ext q; rw [mem_filter, mem_filter]; simp [WillRead]
      rw [heq]; omega
  · -- line 23
    by_cases hi : i ∈ rem'
    · have := card_erase_add_one hi
      simp [ccPot, stepAt_pc, core, hpc, hi, rmrCC, access, LoopOK]; omega
    · have := hrem rem' hi rfl; subst this
      simp [ccPot, stepAt_pc, core, hpc, rmrCC, access, LoopOK]
  · -- CS
    simp [ccPot, stepAt_pc, core, hpc, rmrCC, access, LoopOK]
  · -- line 25
    by_cases hi : i ∈ rem'
    · have := card_erase_add_one hi
      simp [ccPot, stepAt_pc, core, hpc, hi, rmrCC, access, LoopOK]; omega
    · have := hrem rem' hi rfl; subst this
      simp [ccPot, stepAt_pc, core, hpc, rmrCC, access, LoopOK]

/-- **Lemma 7 (CC)** (thesis Lemmas 5.7, 5.8, 5.17–5.19): every (possibly incomplete) passage
of `p` — from its step leaving the NCS at time `t₀` up to time `t₁`, without returning to the
NCS in between — makes at most `ccTotal = 9N − 6` (unshaded) or `13N − 6` (full algorithm) RMRs
in the CC model, no matter how long `p` waits. -/
theorem rmr_cc_le (r : Run fife k P) (p : P) {t₀ t₁ : ℕ} (hp : (r.s t₀).pc p = .ncs)
    (hs : r.sched t₀ = p) (h₀₁ : t₀ < t₁) (hin : ∀ t, t₀ < t → t < t₁ → (r.s t).pc p ≠ .ncs) :
    r.rmrs rmrCC p t₀ t₁ ≤ ccTotal fife (Fintype.card P) := by
  have he : (univ.erase p).card = Fintype.card P - 1 := by
    rw [card_erase_of_mem (mem_univ p), card_univ]
  have key : ∀ t, t₀ + 1 ≤ t → t ≤ t₁ →
      r.rmrs rmrCC p t₀ t + ccPot fife (r.s t) p ≤ ccTotal fife (Fintype.card P) ∧
        LoopOK fife p ((r.s t).pc p) := by
    intro t h1 h2
    induction t, h1 using Nat.le_induction with
    | base =>
      have hpc : (r.s (t₀ + 1)).pc p = .d14 (univ.erase p) := by
        rw [r.step t₀, hs, stepAt_pc]; simp [core, hp]
      have hr : rmrCC (r.s t₀) p (r.choice t₀) = false := by simp [rmrCC, access, hp]
      rw [r.rmrs_succ _ _ le_rfl]
      simp only [Run.rmrs, Ico_self, filter_empty, card_empty, hs, hr, true_and]
      refine ⟨?_, by rw [hpc]; trivial⟩
      simp only [ccPot, hpc, he, ccTotal]; simp
    | succ t ht ih =>
      obtain ⟨h1, h3⟩ := ih (by omega)
      rw [r.rmrs_succ _ _ (by omega)]
      by_cases hst : r.sched t = p
      · have hadm := r.adm t
        rw [hst] at hadm
        obtain ⟨h4, h5⟩ := ccPot_self (fife := fife) (k := k) (r.inv t) hadm
          (hin t (by omega) (by omega)) h3
        have hst' := r.step t
        rw [hst] at hst'
        simp only [hst, true_and]
        rw [hst']
        refine ⟨?_, h5⟩
        split_ifs at h4 ⊢ <;> omega
      · have hadm := r.adm t
        have h4 := ccPot_other (fife := fife) (r.inv t) hadm hst
        have hpc := r.pc_succ_of_ne hst
        rw [← r.step t] at h4
        rw [if_neg (by simp [hst]), hpc]
        exact ⟨by omega, h3⟩
  have := (key t₁ h₀₁ le_rfl).1
  omega

/-- Remaining writes of `p`'s passage (all of them are RMRs in the CC model). -/
def wrRem (fife : Bool) (N : ℕ) : PC P → ℕ
  | .ncs => 0
  | .d14 rem => rem.card + 1 + (N - 1) + (if fife then N else 0) + N
  | .d15 _ _ => 1 + (N - 1) + (if fife then N else 0) + N
  | .d16 rem => rem.card + (if fife then N else 0) + N
  | .head _ _ | .scan _ _ | .chk _ _ _ => (if fife then N else 0) + N
  | .cap23 rem => rem.card + N
  | .cs => N
  | .ex rem => rem.card

lemma wrRem_self {p i : P} (ha : Admissible s p i) (hn : s.pc p ≠ .ncs) :
    wrRem fife (Fintype.card P) (s.pc p) ≤
      (if rmrCC s p i then 1 else 0) + wrRem fife (Fintype.card P) ((stepAt fife k s p i).pc p) := by
  have he : (univ.erase p).card = Fintype.card P - 1 := by
    rw [card_erase_of_mem (mem_univ p), card_univ]
  have hrem : ∀ rem : Finset P, i ∉ rem → (s.pc p).rem = rem → rem = ∅ := by
    intro rem hi h
    have := admissible_of_not_mem ha (by rw [h]; exact hi)
    rwa [h] at this
  rcases hpc : s.pc p with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc, PC.rem] at hn hrem
  · exact absurd rfl hn
  all_goals first
    | (by_cases hi : i ∈ rem'
       · have := card_erase_add_one hi
         simp [wrRem, stepAt_pc, core, hpc, hi, rmrCC, access]
         try (split_ifs <;> omega)
       · have := hrem rem' hi rfl; subst this
         simp [wrRem, stepAt_pc, core, hpc, rmrCC, access, he]
         try omega)
    | (simp [wrRem, stepAt_pc, core, hpc, rmrCC, access]
       try (split_ifs <;> simp_all <;> omega))
    | (cases fife <;> simp [wrRem, stepAt_pc, core, hpc, rmrCC, access] <;>
       split_ifs <;> simp_all)

/-- Lower bound (the `Ω(N)` half of `Θ(N)` in the CC model): a complete passage makes at least
`3N − 1` RMRs (its writes). -/
theorem rmr_cc_complete_ge (r : Run fife k P) (p : P) {t₀ t₁ : ℕ} (hp : (r.s t₀).pc p = .ncs)
    (hs : r.sched t₀ = p) (h₀₁ : t₀ < t₁) (hin : ∀ t, t₀ < t → t < t₁ → (r.s t).pc p ≠ .ncs)
    (hend : (r.s t₁).pc p = .ncs) :
    3 * Fintype.card P - 1 ≤ r.rmrs rmrCC p t₀ t₁ := by
  have he : (univ.erase p).card = Fintype.card P - 1 := by
    rw [card_erase_of_mem (mem_univ p), card_univ]
  have key : ∀ t, t₀ + 1 ≤ t → t ≤ t₁ →
      wrRem fife (Fintype.card P) (.d14 (univ.erase p)) ≤
        r.rmrs rmrCC p t₀ t + wrRem fife (Fintype.card P) ((r.s t).pc p) := by
    intro t h1 h2
    induction t, h1 using Nat.le_induction with
    | base =>
      have hpc : (r.s (t₀ + 1)).pc p = .d14 (univ.erase p) := by
        rw [r.step t₀, hs, stepAt_pc]; simp [core, hp]
      rw [hpc]; omega
    | succ t ht ih =>
      have h1 := ih (by omega)
      rw [r.rmrs_succ _ _ (by omega)]
      by_cases hst : r.sched t = p
      · have hadm := r.adm t
        rw [hst] at hadm
        have h4 := wrRem_self (fife := fife) (k := k) hadm (hin t (by omega) (by omega))
        have hst' := r.step t
        rw [hst] at hst'
        simp only [hst, true_and]
        rw [hst']
        split_ifs at h4 ⊢ <;> omega
      · rw [if_neg (by simp [hst]), r.pc_succ_of_ne hst]
        omega
  have := key t₁ h₀₁ le_rfl
  rw [hend] at this
  simp only [wrRem, he] at this
  split_ifs at this <;> omega

end Podc.KBakery
