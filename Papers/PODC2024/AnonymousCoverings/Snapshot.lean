import Papers.PODC2024.AnonymousCoverings.Stable
import Papers.PODC2024.AnonymousCoverings.WriteScan

/-!
# The snapshot algorithm (Figure 3)

Registers hold a view and a level. A processor writes `(view, level)` to the next register of its
round-robin cycle, then reads all registers (storing the values read in `got`), and at the end of
the scan:

* if every value read has view equal to its own view, `level := min(levels read) + 1`, otherwise
  `level := 0`;
* `view := view ∪ (views read)`.

It loops until `level ≥ L` (the paper: `L = N`, the number of processors) and then outputs its view.
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R V : Type*} [DecidableEq P] [DecidableEq R] [Fintype R] [Nonempty R] [DecidableEq V]

/-- Local data of the snapshot algorithm. -/
structure SnapD (R V : Type*) where
  /-- The view: the set of inputs known. -/
  view : Finset V
  /-- The level. -/
  level : ℕ
  /-- The values read in the current scan (`read` in Figure 3). -/
  got : R → Finset V × ℕ

/-- Minimum level read. -/
def SnapD.minLevel (d : SnapD R V) : ℕ := univ.inf' univ_nonempty fun r => (d.got r).2

/-- Union of the views read. -/
def SnapD.unionRead (d : SnapD R V) : Finset V := univ.sup fun r => (d.got r).1

/-- End-of-scan computation (lines 21–25 of Figure 3). -/
def SnapD.finish (d : SnapD R V) : SnapD R V :=
  ⟨d.view ∪ d.unionRead,
   if ∀ r, (d.got r).1 = d.view then d.minLevel + 1 else 0, d.got⟩

/-- **Figure 3**: the snapshot algorithm with termination level `L`. -/
def snapshot (L : ℕ) : Algo R (SnapD R V) (Finset V × ℕ) where
  wr d := (d.view, d.level)
  rd d r x := { d with got := Function.update d.got r x }
  fin d := d.finish
  stop d := L ≤ d.level

/-- Initial local data. -/
def snapInit (v : V) : SnapD R V := ⟨{v}, 0, fun _ => (∅, 0)⟩

/-- Initial configuration of Figure 3 for inputs `input`. -/
def snapCfg (input : P → V) : Cfg P R (SnapD R V) (Finset V × ℕ) :=
  initCfg (fun p => snapInit (input p)) (∅, 0)

namespace Exec

variable {L : ℕ} (e : Exec (P := P) (snapshot (R := R) (V := V) L))

/-- Writes and reads do not change the view and the level; only scan ends do. -/
theorem snap_view_level_succ (t : ℕ) (p : P) :
    ((e.loc (t + 1) p).d.view = (e.loc t p).d.view ∧
      (e.loc (t + 1) p).d.level = (e.loc t p).d.level) ∨
    (e.Completes t p ∧ ∃ r, e.act t = .read p r ∧ ∃ S, (e.loc t p).scan = some S ∧ r ∉ S ∧
      insert r S = univ ∧
      (e.loc (t + 1) p).d = ((snapshot L).rd (e.loc t p).d r (e.reg t r).val).finish) := by
  by_cases hm : e.Moves t p
  · obtain ⟨r, hr | hr⟩ := hm
    · left; rw [(e.write_spec hr).2.2.2.2]; exact ⟨rfl, rfl⟩
    · obtain ⟨S, hS, hrS, hpost⟩ := e.read_spec hr
      by_cases hu : insert r S = univ
      · right
        refine ⟨⟨⟨r, hr⟩, by rw [hpost]; simp [hu]⟩, r, hr, S, hS, hrS, hu, ?_⟩
        rw [hpost]; simp [hu, snapshot]
      · left; rw [hpost]; simp [hu, snapshot]
  · left; rw [e.loc_succ_of_not_moves hm]; exact ⟨rfl, rfl⟩

theorem snap_view_mono (t : ℕ) (p : P) : (e.loc t p).d.view ⊆ (e.loc (t + 1) p).d.view := by
  rcases e.snap_view_level_succ t p with ⟨h, -⟩ | ⟨-, r, -, S, -, -, -, h⟩
  · rw [h]
  · rw [h]; exact subset_union_left

/-- The `got` field is changed only by reads, at the register read. -/
theorem snap_got_succ (t : ℕ) (p : P) (r : R) :
    (e.loc (t + 1) p).d.got r = (e.loc t p).d.got r ∨
      (e.act t = .read p r ∧ (e.loc (t + 1) p).d.got r = (e.reg t r).val) := by
  by_cases hm : e.Moves t p
  · obtain ⟨r', hr | hr⟩ := hm
    · left; rw [(e.write_spec hr).2.2.2.2]
    · obtain ⟨S, hS, hrS, hpost⟩ := e.read_spec hr
      by_cases hrr : r' = r
      · subst hrr; right
        refine ⟨hr, ?_⟩
        rw [hpost]; split_ifs <;> simp [snapshot, SnapD.finish]
      · left; rw [hpost]; split_ifs <;> simp [snapshot, SnapD.finish, Function.update_of_ne (Ne.symm hrr)]
  · left; rw [e.loc_succ_of_not_moves hm]

/-- After `a` reads `r` at time `t`, while it keeps scanning, `r` stays in its read set and the
value read stays in `got r`. -/
theorem snap_got_track {t c : ℕ} {a : P} {r : R} (hr : e.act t = .read a r)
    (hnc : ∀ t', t < t' → t' ≤ c → (e.loc t' a).scan ≠ none) :
    ∀ t', t < t' → t' ≤ c → ∃ S, (e.loc t' a).scan = some S ∧ r ∈ S ∧
      (e.loc t' a).d.got r = (e.reg t r).val := by
  intro t' h1 h2
  induction t', (show t + 1 ≤ t' by omega) using Nat.le_induction with
  | base =>
    obtain ⟨S, hS, hrS, hpost⟩ := e.read_spec hr
    have hne := hnc (t + 1) (by omega) h2
    rw [hpost] at hne ⊢
    split_ifs at hne ⊢ with hu
    · exact absurd rfl hne
    · exact ⟨insert r S, rfl, mem_insert_self r S, by simp [snapshot]⟩
  | succ t' ht ih =>
    obtain ⟨S, hS, hrS, hg⟩ := ih (by omega) (by omega)
    rcases e.snap_got_succ t' a r with hg' | ⟨hr', -⟩
    · by_cases hm : e.Moves t' a
      · obtain ⟨r', hr'' | hr''⟩ := hm
        · rw [(e.write_spec hr'').1] at hS; exact absurd hS (by simp)
        · obtain ⟨S', hS', hrS', hpost⟩ := e.read_spec hr''
          rw [hS] at hS'; cases hS'
          have hne := hnc (t' + 1) (by omega) h2
          refine ⟨insert r' S, ?_, mem_insert_of_mem hrS, by rw [hg', hg]⟩
          rw [hpost] at hne ⊢
          split_ifs at hne ⊢
          · exact absurd rfl hne
          · rfl
      · rw [e.loc_succ_of_not_moves hm]; exact ⟨S, hS, hrS, hg⟩
    · obtain ⟨S', hS', hrS', -⟩ := e.read_spec hr'
      rw [hS] at hS'; cases hS'
      exact absurd hrS hrS'

/-- Views and levels do not change during a scan. -/
theorem snap_view_level_const {s c : ℕ} {a : P} {r₀ : R} (_hw : e.act s = .write a r₀)
    (hnc : ∀ t, s < t → t ≤ c → (e.loc t a).scan ≠ none) :
    ∀ t, s ≤ t → t ≤ c → (e.loc t a).d.view = (e.loc s a).d.view ∧
      (e.loc t a).d.level = (e.loc s a).d.level := by
  intro t h1 h2
  induction t, h1 using Nat.le_induction with
  | base => exact ⟨rfl, rfl⟩
  | succ t ht ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rcases e.snap_view_level_succ t a with ⟨h3, h4⟩ | ⟨⟨-, hdone⟩, -⟩
    · exact ⟨h3.trans ih1, h4.trans ih2⟩
    · exact absurd hdone (hnc (t + 1) (by omega) h2)

/-- **Result of a scan.** A scan started by the write at `s` and completed at `c` sets the data to
`finish` of a record with the view and level of the scanner and, for every register `r`, the value
read in `r` at some time `g r ∈ (s, c]`. -/
theorem snap_scan_result {s c : ℕ} {a : P} {r₀ : R} (hw : e.act s = .write a r₀)
    (hc : e.Completes c a) (hsc : s < c)
    (hnc : ∀ t, s < t → t ≤ c → (e.loc t a).scan ≠ none) :
    ∃ g : R → ℕ, (∀ r, s < g r ∧ g r ≤ c ∧ e.act (g r) = .read a r) ∧
      ∃ d : SnapD R V, (e.loc (c + 1) a).d = d.finish ∧ d.view = (e.loc s a).d.view ∧
        d.level = (e.loc s a).d.level ∧ ∀ r, d.got r = (e.reg (g r) r).val := by
  classical
  have cover := e.read_all_of_scan hw hc hsc hnc
  choose g hg using cover
  refine ⟨g, fun r => hg r, ?_⟩
  obtain ⟨⟨rc, hrc⟩, hdone⟩ := hc
  obtain ⟨S, hS, hrS, hpost⟩ := e.read_spec hrc
  have hu : insert rc S = univ := by
    by_contra hu
    rw [hpost] at hdone; simp [hu] at hdone
  have hvl := e.snap_view_level_const hw hnc c hsc.le le_rfl
  refine ⟨(snapshot L).rd (e.loc c a).d rc (e.reg c rc).val, by rw [hpost]; simp [hu, snapshot],
    by simp [snapshot, hvl.1], by simp [snapshot, hvl.2], fun r => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hg r
  by_cases hrr : r = rc
  · subst hrr
    have : g r = c := by
      by_contra hne
      obtain ⟨S', hS', hrS', -⟩ := e.snap_got_track h3 (c := c)
        (fun t' ht1 ht2 => hnc t' (by omega) ht2) c (by omega) le_rfl
      rw [hS] at hS'; cases hS'
      exact hrS hrS'
    simp [snapshot, this]
  · have hlt : g r < c := by
      rcases Nat.lt_or_ge (g r) c with h | h
      · exact h
      · have : g r = c := by omega
        rw [this, hrc] at h3; cases h3; exact absurd rfl hrr
    obtain ⟨S', hS', -, hgot⟩ := e.snap_got_track h3 (c := c)
      (fun t' ht1 ht2 => hnc t' (by omega) ht2) c hlt le_rfl
    simp [snapshot, Function.update_of_ne hrr, hgot]

end Exec

end Podc.AnonymousCoverings
