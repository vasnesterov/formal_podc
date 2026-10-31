import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Podc.Computability.Distributed.SharedMemory.Persistent.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Persistent/Solo.lean

/-!
# Solo runs, renaming of operation identifiers, and wear accounting

Generic facts about the persistent-memory model `Cslib.SharedMemory.Persistent`:

* `exec_solo`: a running thread that takes `n` solo steps either is still running (no history
  events) or has returned exactly once;
* `exec_other_ts`: events of other threads do not change the state of a thread;
* `Rel d C D`, `rel_exec`: in the ideal wear model, configurations that differ only in the
  wear counters and by a shift `d` of operation identifiers behave the same (histories are
  shifted by `d`);
* `wearSum`, `exec_wearSum`: the total number of write-backs never decreases, and if it does not
  change then persistent memory does not change.
-/

namespace Cslib.SharedMemory.Persistent

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

variable {O : ObjSpec} {k : ℕ} {V : Type} {A : Alg O k V} {P : Type} [DecidableEq P]
  [DecidableEq V]

namespace Alg

lemma exec_cons (W : Wear k V) (C : Cfg A P) (e : Ev k P O.Op) (es : List (Ev k P O.Op)) :
    exec W C (e :: es) =
      ((exec W (step1 W C e).1 es).1, (step1 W C e).2 ++ (exec W (step1 W C e).1 es).2) := rfl

/-- A step of `p` does not change the state of another thread. -/
lemma step1_ts_ne (W : Wear k V) (C : Cfg A P) {p q : P} (hqp : q ≠ p) :
    (step1 W C (.step p)).1.ts q = C.ts q := by
  cases hp : C.ts p with
  | idle => simp [step1, hp]
  | run a o l =>
    cases hact : A.act l with
    | read i κ => simp [step1, hp, hact, Function.update_of_ne hqp]
    | cas i e n κ =>
      by_cases hc : C.cache i = e <;> simp [step1, hp, hact, hc, Function.update_of_ne hqp]
    | flush i l' => simp [step1, hp, hact, Function.update_of_ne hqp]
    | ret r => simp [step1, hp, hact, Function.update_of_ne hqp]

/-- An invocation by `p` does not change the state of another thread. -/
lemma step1_inv_ts_ne (W : Wear k V) (C : Cfg A P) {p q : P} (hqp : q ≠ p) (o : O.Op) :
    (step1 W C (.inv p o)).1.ts q = C.ts q := by
  cases hp : C.ts p <;> simp [step1, hp, Function.update_of_ne hqp]

/-- Events of thread `p` only do not change the state of another thread. -/
lemma exec_other_ts (W : Wear k V) {p q : P} (hqp : q ≠ p) :
    ∀ (es : List (Ev k P O.Op)) (C : Cfg A P),
      (∀ e ∈ es, e = .step p ∨ ∃ o, e = .inv p o) → (exec W C es).1.ts q = C.ts q
  | [], _, _ => rfl
  | e :: es, C, hes => by
    rw [exec_cons, exec_other_ts W hqp es _ (fun e' he' => hes e' (by simp [he']))]
    rcases hes e (by simp) with rfl | ⟨o, rfl⟩
    · exact step1_ts_ne W C hqp
    · exact step1_inv_ts_ne W C hqp o

/-- Solo steps of a running thread: it is still running (and nothing was emitted) or it
returned exactly once and is idle. -/
lemma exec_solo (W : Wear k V) (p : P) :
    ∀ (n : ℕ) (C : Cfg A P) (a : ℕ) (o : O.Op) (l : A.L), C.ts p = .run a o l →
      ((∃ l', (exec W C (List.replicate n (.step p))).1.ts p = .run a o l') ∧
          (exec W C (List.replicate n (.step p))).2 = []) ∨
      ((exec W C (List.replicate n (.step p))).1.ts p = .idle ∧
          ∃ r, (exec W C (List.replicate n (.step p))).2 = [.res a r])
  | 0, C, a, o, l, hp => Or.inl ⟨⟨l, hp⟩, rfl⟩
  | n + 1, C, a, o, l, hp => by
    rw [List.replicate_succ, exec_cons]
    cases hact : A.act l with
    | ret r =>
      have h1 : step1 W C (.step p) = ({ C with ts := Function.update C.ts p .idle }, [.res a r])
        := by simp [step1, hp, hact]
      rw [h1]
      -- the thread is idle: further steps do nothing
      have hidle : ∀ m (D : Cfg A P), D.ts p = .idle →
          exec W D (List.replicate m (.step p)) = (D, []) := by
        intro m
        induction m with
        | zero => intro D _; rfl
        | succ m ih =>
          intro D hD
          rw [List.replicate_succ, exec_cons]
          have : step1 W D (.step p) = (D, []) := by simp [step1, hD]
          rw [this, ih D hD]; rfl
      rw [hidle n _ (by simp)]
      exact Or.inr ⟨by simp, r, by simp⟩
    | read i κ =>
      have h1 : (step1 W C (.step p)).2 = [] := by simp [step1, hp, hact]
      have h2 : (step1 W C (.step p)).1.ts p = .run a o (κ (C.cache i)) := by
        simp [step1, hp, hact]
      rw [h1, List.nil_append]; exact exec_solo W p n _ a o _ h2
    | cas i e n' κ =>
      by_cases hc : C.cache i = e
      · have h1 : (step1 W C (.step p)).2 = [] := by simp [step1, hp, hact, hc]
        have h2 : (step1 W C (.step p)).1.ts p = .run a o (κ true) := by
          simp [step1, hp, hact, hc]
        rw [h1, List.nil_append]; exact exec_solo W p n _ a o _ h2
      · have h1 : (step1 W C (.step p)).2 = [] := by simp [step1, hp, hact, hc]
        have h2 : (step1 W C (.step p)).1.ts p = .run a o (κ false) := by
          simp [step1, hp, hact, hc]
        rw [h1, List.nil_append]; exact exec_solo W p n _ a o _ h2
    | flush i l' =>
      have h1 : (step1 W C (.step p)).2 = [] := by simp [step1, hp, hact]
      have h2 : (step1 W C (.step p)).1.ts p = .run a o l' := by simp [step1, hp, hact]
      rw [h1, List.nil_append]; exact exec_solo W p n _ a o _ h2

/-! ### Renaming operation identifiers -/

/-- Shift the identifier of a running operation. -/
def shiftTS (d : ℕ) : TS O.Op A.L → TS O.Op A.L
  | .idle => .idle
  | .run a o l => .run (a + d) o l

@[simp] lemma shiftTS_run (d a : ℕ) (o : O.Op) (l : A.L) :
    shiftTS d (.run a o l : TS O.Op A.L) = .run (a + d) o l := rfl

@[simp] lemma shiftTS_idle (d : ℕ) : shiftTS d (.idle : TS O.Op A.L) = .idle := rfl

/-- Shift the identifier of a history event. -/
def shiftEv (d : ℕ) : HEv P O.Op O.Resp → HEv P O.Op O.Resp
  | .inv a p o => .inv (a + d) p o
  | .res a r => .res (a + d) r
  | .crash => .crash

/-- `D` is `C` with operation identifiers shifted by `d` (wear counters are ignored). -/
structure Rel (d : ℕ) (C D : Cfg A P) : Prop where
  cache : D.cache = C.cache
  dirty : D.dirty = C.dirty
  pm : D.pm = C.pm
  ts : ∀ q, D.ts q = shiftTS d (C.ts q)
  cnt : D.cnt = C.cnt + d

lemma Rel.writeBack {d : ℕ} {C D : Cfg A P} (hR : Rel d C D) (i : Fin k) :
    Rel d (writeBack (Wear.ideal k V) C i) (writeBack (Wear.ideal k V) D i) := by
  have hc := hR.cache; have hd := hR.dirty; have hpm := hR.pm
  unfold Alg.writeBack
  by_cases h : C.dirty i = true
  · have h' : D.dirty i = true := by rw [hd]; exact h
    simp only [h, h', ite_true, Wear.ideal, ENat.natCast_lt_top]
    exact ⟨hc, by rw [hd], by rw [hpm, hc], hR.ts, hR.cnt⟩
  · have h' : ¬ D.dirty i = true := by rw [hd]; exact h
    simp only [h, h']
    exact hR

lemma Rel.update_ts {d : ℕ} {C D : Cfg A P} (hR : Rel d C D) (p : P) (s : TS O.Op A.L) :
    ∀ q, Function.update D.ts p (shiftTS d s) q = shiftTS d (Function.update C.ts p s q) := by
  intro q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq, hR.ts q]

/-- In the ideal model, related configurations take related steps. -/
lemma Rel.step1 {d : ℕ} {C D : Cfg A P} (hR : Rel d C D) (e : Ev k P O.Op) :
    Rel d (step1 (Wear.ideal k V) C e).1 (step1 (Wear.ideal k V) D e).1 ∧
      (step1 (Wear.ideal k V) D e).2 = (step1 (Wear.ideal k V) C e).2.map (shiftEv d) := by
  cases e with
  | inv p o =>
    cases hp : C.ts p with
    | run a o' l =>
      have hp' : D.ts p = .run (a + d) o' l := by rw [hR.ts p, hp]; rfl
      simp only [Alg.step1, hp, hp']; exact ⟨hR, rfl⟩
    | idle =>
      have hp' : D.ts p = .idle := by rw [hR.ts p, hp]; rfl
      simp only [Alg.step1, hp, hp']
      refine ⟨⟨hR.cache, hR.dirty, hR.pm, ?_, by simp [hR.cnt]; omega⟩, by
        simp [shiftEv, hR.cnt]⟩
      have := hR.update_ts p (.run C.cnt o (A.start o))
      intro q; rw [← this q]; simp [shiftTS, hR.cnt]
  | evict i =>
    exact ⟨hR.writeBack i, rfl⟩
  | crash =>
    refine ⟨⟨by simp [Alg.step1, hR.pm], rfl, by simp [Alg.step1, hR.pm], fun q => rfl,
      by simp [Alg.step1, hR.cnt]⟩, rfl⟩
  | step p =>
    cases hp : C.ts p with
    | idle =>
      have hp' : D.ts p = .idle := by rw [hR.ts p, hp]; rfl
      simp only [Alg.step1, hp, hp']; exact ⟨hR, rfl⟩
    | run a o l =>
      have hp' : D.ts p = .run (a + d) o l := by rw [hR.ts p, hp]; rfl
      cases hact : A.act l with
      | read i κ =>
        simp only [Alg.step1, hp, hp', hact]
        refine ⟨⟨hR.cache, hR.dirty, hR.pm, ?_, hR.cnt⟩, rfl⟩
        intro q
        have := hR.update_ts p (.run a o (κ (C.cache i))) q
        rw [shiftTS_run] at this
        show Function.update D.ts p (.run (a + d) o (κ (D.cache i))) q =
          shiftTS d (Function.update C.ts p (.run a o (κ (C.cache i))) q)
        rw [hR.cache]; exact this
      | cas i e n κ =>
        by_cases hc : C.cache i = e
        · have hc' : D.cache i = e := by rw [hR.cache]; exact hc
          simp only [Alg.step1, hp, hp', hact, hc, hc', ite_true]
          refine ⟨⟨by rw [hR.cache], by rw [hR.dirty], hR.pm, ?_, hR.cnt⟩, rfl⟩
          exact hR.update_ts p (.run a o (κ true))
        · have hc' : ¬ D.cache i = e := by rw [hR.cache]; exact hc
          simp only [Alg.step1, hp, hp', hact, hc, hc', ite_false]
          exact ⟨⟨hR.cache, hR.dirty, hR.pm, hR.update_ts p (.run a o (κ false)), hR.cnt⟩, rfl⟩
      | flush i l' =>
        simp only [Alg.step1, hp, hp', hact]
        have hw := hR.writeBack i
        refine ⟨⟨hw.cache, hw.dirty, hw.pm, ?_, hw.cnt⟩, rfl⟩
        have := hR.update_ts p (.run a o l')
        intro q
        have h' := this q
        rw [shiftTS_run] at h'
        exact h'
      | ret r =>
        simp only [Alg.step1, hp, hp', hact]
        exact ⟨⟨hR.cache, hR.dirty, hR.pm, hR.update_ts p .idle, hR.cnt⟩, by simp [shiftEv]⟩

lemma Rel.exec {d : ℕ} : ∀ (es : List (Ev k P O.Op)) {C D : Cfg A P}, Rel d C D →
    Rel d (exec (Wear.ideal k V) C es).1 (exec (Wear.ideal k V) D es).1 ∧
      (exec (Wear.ideal k V) D es).2 = (exec (Wear.ideal k V) C es).2.map (shiftEv d)
  | [], _, _, hR => ⟨hR, rfl⟩
  | e :: es, C, D, hR => by
    obtain ⟨h1, h2⟩ := hR.step1 e
    obtain ⟨h3, h4⟩ := Rel.exec es h1
    rw [exec_cons, exec_cons]
    exact ⟨h3, by rw [h2, h4, List.map_append]⟩

/-! ### Wear accounting -/

/-- Total number of write-backs. -/
def wearSum (C : Cfg A P) : ℕ := ∑ i, C.wear i

lemma writeBack_wearSum (W : Wear k V) (C : Cfg A P) (i : Fin k) :
    (wearSum (writeBack W C i) = wearSum C ∧ (writeBack W C i).pm = C.pm) ∨
      wearSum (writeBack W C i) = wearSum C + 1 := by
  unfold writeBack
  by_cases h : C.dirty i = true
  · right
    simp only [h, ite_true, wearSum]
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp [Finset.sdiff_singleton_eq_erase]
    omega
  · left; simp [h]

lemma step1_wearSum (W : Wear k V) (C : Cfg A P) (e : Ev k P O.Op) :
    (wearSum (step1 W C e).1 = wearSum C ∧ (step1 W C e).1.pm = C.pm) ∨
      wearSum (step1 W C e).1 = wearSum C + 1 := by
  cases e with
  | inv p o => left; cases hp : C.ts p <;> simp [step1, hp, wearSum]
  | evict i => exact writeBack_wearSum W C i
  | crash => left; simp [step1, wearSum]
  | step p =>
    cases hp : C.ts p with
    | idle => left; simp [step1, hp]
    | run a o l =>
      cases hact : A.act l with
      | flush i l' =>
        have := writeBack_wearSum W C i
        simp only [step1, hp, hact]
        exact this
      | cas i e n κ =>
        left; by_cases hc : C.cache i = e <;> simp [step1, hp, hact, hc, wearSum]
      | _ => left; simp [step1, hp, hact, wearSum]

/-- The total number of write-backs does not decrease, and if it does not change, persistent
memory does not change. -/
lemma exec_wearSum (W : Wear k V) :
    ∀ (es : List (Ev k P O.Op)) (C : Cfg A P),
      wearSum C ≤ wearSum (exec W C es).1 ∧
        (wearSum (exec W C es).1 = wearSum C → (exec W C es).1.pm = C.pm)
  | [], C => ⟨le_rfl, fun _ => rfl⟩
  | e :: es, C => by
    rw [exec_cons]
    dsimp only
    obtain ⟨h1, h2⟩ := exec_wearSum W es (step1 W C e).1
    rcases step1_wearSum W C e with ⟨h3, h4⟩ | h3
    · exact ⟨h3 ▸ h1, fun h => by rw [h2 (h.trans h3.symm), h4]⟩
    · exact ⟨by omega, fun h => by omega⟩

/-! ### Lock-freedom implies obstruction-freedom -/

lemma step1_res_idle (W : Wear k V) (C : Cfg A P) (p : P) {a : ℕ} {r : O.Resp}
    (h : (step1 W C (.step p)).2 = [.res a r]) : (step1 W C (.step p)).1.ts p = .idle := by
  cases hp : C.ts p with
  | idle => simp [step1, hp] at h
  | run b o l =>
    cases hact : A.act l with
    | read i κ => simp [step1, hp, hact] at h
    | cas i e n κ => by_cases hc : C.cache i = e <;> simp [step1, hp, hact, hc] at h
    | flush i l' => simp [step1, hp, hact] at h
    | ret r' => simp [step1, hp, hact]

/-- The schedule `es` followed by steps of `p` forever. -/
def thenSolo (es : List (Ev k P O.Op)) (p : P) (t : ℕ) : Ev k P O.Op :=
  if h : t < es.length then es[t] else .step p

lemma pfx_thenSolo (es : List (Ev k P O.Op)) (p : P) (t : ℕ) (ht : es.length ≤ t) :
    pfx P (thenSolo es p) t = es ++ List.replicate (t - es.length) (.step p) := by
  apply List.ext_getElem
  · simp [pfx]; omega
  · intro n h1 h2
    simp only [pfx, List.getElem_map, List.getElem_range, thenSolo]
    by_cases hn : n < es.length
    · rw [dite_eq_left hn, List.getElem_append_left hn]
    · rw [dite_eq_right hn, List.getElem_append_right (by omega)]; simp

/-- Lock-freedom implies obstruction-freedom. -/
lemma LockFree.obstructionFree {W : Wear k V} (hLF : LockFree A P W) : ObstructionFree A P W := by
  intro es p
  by_contra hcon
  push Not at hcon
  have hrun : ∀ t ≥ es.length, (cfgAt A P W (thenSolo es p) t).ts p ≠ .idle := by
    intro t ht
    rw [cfgAt, pfx_thenSolo es p t ht]
    exact hcon _
  have hev : ∀ t ≥ es.length, thenSolo es p t = .step p := by
    intro t ht; simp [thenSolo, show ¬ t < es.length by omega]
  obtain ⟨t', ht', a, r, hres⟩ := hLF (thenSolo es p) trivial
    ⟨es.length, fun t ht => by rw [hev t ht]; simp⟩
    (fun t => ⟨max t es.length, le_max_left _ _, p, hev _ (le_max_right _ _),
      hrun _ (le_max_right _ _)⟩) es.length
  rw [hev t' ht'] at hres
  have := step1_res_idle W _ p hres
  rw [← hev t' ht', ← cfgAt_succ] at this
  exact hrun (t' + 1) (by omega) this

end Alg

end Cslib.SharedMemory.Persistent
