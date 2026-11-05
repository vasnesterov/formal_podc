import Papers.PODC2013.ConstantBarriersMutex.RunBasic
import Papers.PODC2013.ConstantBarriersMutex.BoundedWaitingCore

/-!
# Progress: single-step facts and measures

Measures on program counters used for the progress lemmas (`Progress.lean`):

* `rkX` ranks the program counters of the critical and exit sections (and statement 50); it
  drops at every step of a lock holder. The measure `μ rkX s g = 2 · rkX (pc g) + |buf g|`
  therefore drops at every step of `g` (an issued write costs one, a rank step saves two) and
  never grows at other events. No bound on the local variables is needed: the levels are ranked
  by `h − 1 − l` and the candidate lists by their length.
* `rkE` ranks the program counters of the entry section; `μ rkE s p` drops at every step of
  `p` as long as `lock = p` (statement 25 then exits) and `signal[p]` is set (statement 27).
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

namespace Prog

/-- Rank of the program counters of the critical and exit sections (and statement 50). -/
def rkX : PC h → ℕ
  | .cs => 17 * h + 10
  | .x31 => 17 * h + 9
  | .x32 => 17 * h + 8
  | .x34 l j acc => 7 + 17 * (h - 1 - l) + 4 * acc.length + 5 * (3 - min j 2) + 1
  | .x35 l cands => 7 + 17 * (h - 1 - l) + 4 * cands.length + 1
  | .x36 l _ rest => 7 + 17 * (h - 1 - l) + 4 * rest.length + 4
  | .x37 l _ rest => 7 + 17 * (h - 1 - l) + 4 * rest.length + 3
  | .x38 l _ rest => 7 + 17 * (h - 1 - l) + 4 * rest.length + 2
  | .x42 => 6
  | .x43 => 5
  | .x45 => 5
  | .x46 _ => 4
  | .x47 _ => 3
  | .x48 _ => 2
  | .x50 _ => 1
  | _ => 0

/-- Rank of the program counters of the entry section. -/
def rkE : PC h → ℕ
  | .e18 => h + 9
  | .e19 l => l + 8
  | .e22 => 7
  | .e23 => 6
  | .e24 => 5
  | .e25a _ => 4
  | .e25b _ => 3
  | .e26 => 2
  | .e27 => 1
  | _ => 0

/-- The measure of process `q`: twice the rank of its program counter plus the length of its
store buffer. -/
def μ (rk : PC h → ℕ) (s : Cfg h) (q : Proc h) : ℕ := 2 * rk (s.pc q) + (s.buf q).length

lemma addCand_length (p : Proc h) (acc : List (Proc h)) (o : Option (Proc h)) :
    (addCand p acc o).length ≤ acc.length + 1 := by
  cases o with
  | none => simp [addCand]
  | some q => simp only [addCand]; split_ifs <;> simp

/-- Events of other processes do not increase the measure of `q`. -/
lemma μ_next_ne (rk : PC h → ℕ) (s : Cfg h) {e : Ev h} {q : Proc h} (he : e ≠ .step q) :
    μ rk (s.next e) q ≤ μ rk s q := by
  unfold μ
  rw [BW.next_pc_ne s e he]
  cases e with
  | step g =>
    have : q ≠ g := by rintro rfl; exact he rfl
    simp [Cfg.next, BW.stepProc_buf_ne s this]
  | flush g =>
    simp only [Cfg.next]
    unfold Cfg.flush
    split
    · exact le_rfl
    · rename_i w b hb
      by_cases hq : q = g
      · subst hq; simp [hb]
      · simp [Function.update_of_ne hq]

/-- A step of a process in its critical or exit section (or at statement 50) decreases its
measure, unless it returns to the remainder section. -/
lemma stepX {s : Cfg h} (hI : Inv s) {g : Proc h} (hpos : 0 < rkX (s.pc g))
    (hne : (s.stepProc g).pc g ≠ .rem) :
    0 < rkX ((s.stepProc g).pc g) ∧ μ rkX (s.stepProc g) g < μ rkX s g := by
  unfold μ
  cases hpc : s.pc g <;> simp only [rkX, hpc, lt_self_iff_false] at hpos <;>
    simp only [Cfg.stepProc, hpc] at hne ⊢
  case x35 l cands =>
    cases cands with
    | nil =>
      simp only [goto_pc, goto_buf, Function.update_self] at hne ⊢
      split_ifs <;> simp [rkX] <;> omega
    | cons c rest =>
      simp only [goto_pc, goto_buf, Function.update_self] at hne ⊢
      split_ifs <;> simp [rkX]
      omega
  case x45 =>
    have hc := hI.hc g
    simp only [HC, hpc] at hc
    have hh : Holds s g := by unfold Holds; rw [hpc]; trivial
    rw [hI.lv_of_holds hh] at hc
    obtain ⟨nx, rest, hq⟩ := List.exists_cons_of_ne_nil hc
    simp only [hq, issue_pc, issue_buf, Function.update_self] at hne ⊢
    simp [rkX]; omega
  case x50 o =>
    rcases BW.barrier_cases s g .rem with ⟨hb, he⟩ | ⟨w, b, hb, he⟩
    · rw [he] at hne; simp at hne
    · rw [he, flush_of_cons s g hb]
      simp [rkX, hpc, hb]
  case x34 l j acc =>
    have := addCand_length g acc ((s.view g).node (target (anc g l) j))
    simp only [goto_pc, goto_buf, Function.update_self] at hne ⊢
    split_ifs <;> simp [rkX] <;> omega
  all_goals
    simp only [goto_pc, goto_buf, issue_pc, issue_buf, Function.update_self] at hne ⊢
    (try split_ifs) <;> simp [rkX] <;> omega

/-- A step of a process in its entry section to which the lock was handed, with `signal[p]`
set, decreases its measure, unless it enters the critical section. -/
lemma stepE {s : Cfg h} (hI : Inv s) {p : Proc h} (hE : (s.pc p).Entry)
    (hl : s.mem.lock = some p) (hsig : s.mem.signal p = true)
    (hne : (s.stepProc p).pc p ≠ .cs) : μ rkE (s.stepProc p) p < μ rkE s p := by
  unfold μ
  have hL := hI.loc p
  cases hpc : s.pc p <;> simp only [PC.Entry, hpc] at hE <;> simp only [LI, hpc] at hL <;>
    simp only [Cfg.stepProc, hpc] at hne ⊢
  case e22 =>
    rcases BW.barrier_cases s p .e23 with ⟨hb, he⟩ | ⟨w, b, hb, he⟩
    · rw [he]; simp [rkE, hb]
    · rw [he, flush_of_cons s p hb]; simp [rkE, hpc, hb]
  case e23 | e26 =>
    rw [BW.cas_of_nil s _ hL.1] at hne ⊢
    simp [hl, rkE, hL.1]
  case e25b e =>
    rw [BW.view_of_nil hL.1]
    simp [hl, rkE]
  case e27 =>
    rw [BW.view_of_nil hL.1] at hne
    simp [hsig] at hne
  all_goals
    simp only [goto_pc, goto_buf, issue_pc, issue_buf, Function.update_self] at hne ⊢
    (try split_ifs) <;> simp [rkE] <;> omega

/-- While `lock = p` (in memory) and `p` is in its entry section, no event changes `lock`. -/
lemma lock_step {s : Cfg h} (hI : Inv s) {p : Proc h} (hl : s.mem.lock = some p)
    (hE : (s.pc p).Entry) (e : Ev h) : (s.next e).mem.lock = some p := by
  rcases BW.next_mem_cases hI e with ⟨g, w, b, hb, he⟩ | hm | ⟨g, hn, -⟩
  · rw [he, flush_of_cons s g hb]
    cases w with
    | lock o =>
      obtain ⟨hlg, hpg⟩ := BW.buf_lock hI (g := g) (o := o) (by rw [hb]; simp)
      rw [hl] at hlg; cases hlg
      exfalso
      rcases hpg with hpg | ⟨nx, -, hpg⟩ <;> rw [hpg] at hE <;> exact hE
    | _ => simpa using hl
  · rw [hm]; exact hl
  · rw [hl] at hn; cases hn

/-- While `p` is in its entry section with `apply[p]` performed and `lock = p`, a set
`signal[p]` stays set. -/
lemma signal_step {s : Cfg h} (hI : Inv s) {p : Proc h} (hl : s.mem.lock = some p)
    (hE : (s.pc p).Entry) (ha : s.mem.apply p = true) (hs : s.mem.signal p = true) (e : Ev h) :
    (s.next e).mem.signal p = true := by
  rcases BW.next_mem_cases hI e with ⟨g, w, b, hb, he⟩ | hm | ⟨g, hn, -⟩
  · rw [he, flush_of_cons s g hb]
    simp only [write_signal]
    cases w with
    | signal q bb =>
      simp only
      split_ifs with hq
      · subst hq
        cases bb
        · exfalso
          have hw : W.signal q false ∈ s.buf g := by rw [hb]; simp
          rcases BW.buf_cases hI hw with ⟨hd, -⟩ | ⟨hX, -⟩ | ⟨o, ho, -⟩ | ⟨nx, hn, -⟩
          · rcases BW.mem_doorList.1 hd with h1 | h1 | ⟨l, -, h1⟩ <;> cases h1
            have := hI.apply_false_of_head_sig hb
            rw [ha] at this; cases this
          · exact hX.ne_signal q false rfl
          · cases ho
          · cases hn
        · rfl
      · exact hs
    | _ => exact hs
  · rw [hm]; exact hs
  · rw [hl] at hn; cases hn

/-- A hand-off in progress (`Hands s g p`): the next event performs `signal[p] ← true` or
keeps the hand-off, and a step of `g` decreases its measure. -/
lemma hands_step {s : Cfg h} {g p : Proc h} (hH : Hands s g p) (e : Ev h) :
    (s.next e).mem.signal p = true ∨
      (Hands (s.next e) g p ∧ (e = .step g → μ rkX (s.next e) g < μ rkX s g)) := by
  by_cases he : e = .step g
  · subst he
    rcases hH with ⟨hpc, hb⟩ | ⟨hpc, hb⟩
    · right
      simp only [Cfg.next, Cfg.stepProc, hpc]
      refine ⟨Or.inr ⟨by simp, by simp [hb]⟩, fun _ => ?_⟩
      simp [μ, rkX, hpc, hb]
    · left
      simp only [Cfg.next, Cfg.stepProc, hpc]
      rw [BW.barrier_cases s g .rem |>.resolve_left (by simp [hb]) |>.choose_spec.choose_spec.2]
      rw [flush_of_cons s g hb]; simp [Mem.write]
  · by_cases hf : e = .flush g
    · subst hf
      rcases hH with ⟨hpc, hb⟩ | ⟨hpc, hb⟩
      · right
        simp only [Cfg.next, flush_of_nil s g hb]
        exact ⟨Or.inl ⟨hpc, hb⟩, fun h => absurd h (by simp)⟩
      · left
        simp only [Cfg.next, flush_of_cons s g hb]; simp [Mem.write]
    · right
      refine ⟨?_, fun h => absurd h he⟩
      have hp := BW.next_pc_ne s e he
      have hb : (s.next e).buf g = s.buf g := by
        cases e with
        | step q =>
          have : g ≠ q := by rintro rfl; exact he rfl
          simp [Cfg.next, BW.stepProc_buf_ne s this]
        | flush q =>
          have : g ≠ q := by rintro rfl; exact hf rfl
          simp [Cfg.next, BW.flush_buf_ne s this]
      unfold Hands; rw [hp, hb]; exact hH

end Prog

end Podc.ConstantBarriersMutex
