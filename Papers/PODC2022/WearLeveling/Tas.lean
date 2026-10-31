import Mathlib
import Podc.Computability.Distributed.SharedMemory.Persistent.Model
import Cslib.Computability.Distributed.SharedMemory.Objects.TestAndSet

/-!
# Counterexample to Theorem 4.4 as stated: a test-and-set object

Theorem 4.4 claims that *any* implemented object using `k` base objects of endurance `T` can
guarantee endurance at most `k·T`. Its proof assumes that every update operation (every
operation other than a read) must update some base object. This fails for objects whose updates
stop changing the state, e.g. test-and-set (TAS is an update, but only the first TAS changes the
state).

`tasAlg`: a persistent TAS from one word (`k = 1`):
```
CAS(&A[0], false, true)   -- win iff it succeeds
Flush(&A[0])
return (not won)
```
The word is written back to persistent memory at most once in every execution, whatever the
number of invocations. So with one word of endurance `T = 1`, the implementation is strictly
linearizable and lock-free in **all** executions (`tas_guarantees`): its endurance is unbounded,
not `≤ k·T = 1`.
-/

namespace Podc.WearLeveling

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Persistent Alg

/-- Local states of the TAS algorithm. -/
inductive TL where
  /-- `CAS(&A[0], false, true)`. -/
  | start
  /-- `Flush(&A[0])`, then return `r`. -/
  | fl (r : Bool)
  /-- Return `r`. -/
  | done (r : Bool)

/-- Persistent test-and-set from one word. -/
@[reducible] def tasAlg : Alg tasObj 1 Bool where
  L := TL
  init := fun _ => false
  start := fun _ => .start
  act
    | .start => .cas 0 false true (fun b => if b then .fl false else .fl true)
    | .fl r => .flush 0 (.done r)
    | .done r => .ret r

variable {P : Type} [DecidableEq P]

/-- Local invariant of a thread running TAS instance `a`. -/
def TLoc (L : List (ℕ × Unit)) (pm : Bool) (a : ℕ) : TL → Prop
  | .start => a ∉ L.map Prod.fst
  | .fl false => ∃ rest, L = (a, ()) :: rest
  | .fl true => ∃ n, 1 ≤ n ∧ L[n]? = some (a, ())
  | .done false => (∃ rest, L = (a, ()) :: rest) ∧ pm = true
  | .done true => (∃ n, 1 ≤ n ∧ L[n]? = some (a, ())) ∧ pm = true

/-- Invariant of the TAS algorithm. -/
structure TInv (C : Cfg tasAlg P) (h : List (HEv P Unit Bool)) (L : List (ℕ × Unit)) : Prop where
  hinv : HInv C h
  lin : IsStrictLin tasObj h L
  cache_false : C.cache 0 = false → L = [] ∧ C.pm 0 = false ∧ C.dirty 0 = false
  cache_true : C.cache 0 = true → L ≠ [] ∧
    ((C.pm 0 = true ∧ C.dirty 0 = false) ∨
      (C.pm 0 = false ∧ C.dirty 0 = true ∧ ∀ x ∈ L, ∀ r, HEv.res x.1 r ∉ h))
  wear_eq : C.wear 0 = if C.pm 0 then 1 else 0
  loc : ∀ p a o l, C.ts p = .run a o l → TLoc L (C.pm 0) a l

lemma fin1 (i : Fin 1) : i = 0 := Subsingleton.elim _ _

/-- Responses of TAS in a sequential order: only the first one wins. -/
lemma tas_resp (L : List (ℕ × Unit)) (n : ℕ) :
    (tasObj.δ (tasObj.runOps tasObj.init ((L.take n).map Prod.snd)) ()).2 =
      decide (n ≠ 0 ∧ L ≠ []) := by
  have key : ∀ (q : Bool) (os : List Unit), tasObj.runOps q os = (q || decide (os ≠ [])) := by
    intro q os
    induction os generalizing q with
    | nil => rw [ObjSpec.runOps_nil]; simp
    | cons o os ih => rw [ObjSpec.runOps_cons, ih]; simp
  rw [key]
  cases L <;> cases n <;> simp

/-- With endurance at least `1`, a write-back of the (only) word always succeeds when it is
needed. -/
lemma TInv.writeBack {W : Wear 1 Bool} (hT : (1 : ℕ∞) ≤ W.T) {C : Cfg tasAlg P} {h L}
    (hI : TInv C h L) :
    TInv (Alg.writeBack W C 0) h L ∧ (C.cache 0 = true → (Alg.writeBack W C 0).pm 0 = true) := by
  by_cases hd : C.dirty 0 = true
  · -- the line is dirty: the word holds `false` persistently, the cache `true`
    have hc : C.cache 0 = true := by
      by_contra hc; simp at hc; have := (hI.cache_false hc).2.2; simp [this] at hd
    have hpm : C.pm 0 = false := by
      rcases (hI.cache_true hc).2 with h1 | h1
      · simp [h1.2] at hd
      · exact h1.1
    have hw : C.wear 0 = 0 := by rw [hI.wear_eq, hpm]; rfl
    have hlt : ((C.wear 0 : ℕ) : ℕ∞) < W.T := by
      rw [hw]; exact lt_of_lt_of_le (by norm_num) hT
    have hwb : Alg.writeBack W C 0 =
        { C with pm := Function.update C.pm 0 true,
                 wear := Function.update C.wear 0 1,
                 dirty := Function.update C.dirty 0 false } := by
      have h0 : (0 : ℕ∞) < W.T := lt_of_lt_of_le (by norm_num) hT
      simp [Alg.writeBack, hd, hlt, hc, hw, h0]
    rw [hwb]
    refine ⟨⟨⟨hI.hinv.inv_lt, hI.hinv.res_lt, hI.hinv.run_inv, hI.hinv.run_notEnded,
      hI.hinv.run_inj⟩, hI.lin, ?_, ?_, by simp, ?_⟩, by simp⟩
    · intro h'; simp [hc] at h'
    · intro _; exact ⟨(hI.cache_true hc).1, Or.inl ⟨by simp, by simp⟩⟩
    · intro p a o l hp
      have := hI.loc p a o l hp
      simp only [Function.update_self]
      cases l with
      | start => exact this
      | fl r => cases r <;> exact this
      | done r => cases r <;> exact this.1 |> fun h => ⟨h, rfl⟩
  · have hd' : C.dirty 0 = false := by simpa using hd
    have hwb : Alg.writeBack W C 0 = C := by simp [Alg.writeBack, hd']
    rw [hwb]
    refine ⟨hI, fun hc => ?_⟩
    rcases (hI.cache_true hc).2 with h1 | h1
    · exact h1.1
    · simp [h1.2.1] at hd'

lemma TLoc.mono_pm {L : List (ℕ × Unit)} {pm pm' : Bool} (hpm : pm = true → pm' = true) {a : ℕ} :
    ∀ {l : TL}, TLoc L pm a l → TLoc L pm' a l
  | .start, h => h
  | .fl false, h => h
  | .fl true, h => h
  | .done false, h => ⟨h.1, hpm h.2⟩
  | .done true, h => ⟨h.1, hpm h.2⟩

lemma TInv.cache_of_loc {C : Cfg tasAlg P} {h L} (hI : TInv C h L) {p a o} {r : Bool}
    (hp : C.ts p = .run a o (TL.fl r)) : C.cache 0 = true := by
  by_contra hc
  simp only [Bool.not_eq_true] at hc
  have hL := (hI.cache_false hc).1
  have := hI.loc p a o _ hp
  cases r
  · obtain ⟨rest, h⟩ := (this : ∃ rest, L = (a, ()) :: rest); simp [hL] at h
  · obtain ⟨n, _, h⟩ := (this : ∃ n, 1 ≤ n ∧ L[n]? = some (a, ())); simp [hL] at h

/-- One event preserves the TAS invariant (for every wear model with `T ≥ 1`). -/
lemma TInv.step1 {W : Wear 1 Bool} (hT : (1 : ℕ∞) ≤ W.T) {C : Cfg tasAlg P} {h L}
    (hI : TInv C h L) (e : Ev 1 P Unit) :
    ∃ L', TInv (Alg.step1 W C e).1 (h ++ (Alg.step1 W C e).2) L' := by
  have hH := hI.hinv.step1 W e
  cases e with
  | inv q o =>
    cases hq : C.ts q with
    | run b o' l =>
      have heq : Alg.step1 W C (.inv q o) = (C, []) := by simp [Alg.step1, hq]
      rw [heq]; simpa using ⟨L, hI⟩
    | idle =>
      have heq : Alg.step1 W C (.inv q o) =
          ({ C with ts := Function.update C.ts q (.run C.cnt o TL.start), cnt := C.cnt + 1 },
            [.inv C.cnt q o]) := by simp [Alg.step1, hq]
      rw [heq] at hH ⊢
      have hfresh : C.cnt ∉ L.map Prod.fst := by
        intro hc
        obtain ⟨x, hx, hx1⟩ := List.mem_map.1 hc
        obtain ⟨q', hq'⟩ := hI.lin.inv_of_mem x hx
        have := hI.hinv.inv_lt _ _ _ hq'; omega
      refine ⟨L, hH, hI.lin.append_inv hfresh, hI.cache_false, fun hc => ?_, hI.wear_eq, ?_⟩
      · obtain ⟨h1, h2⟩ := hI.cache_true hc
        refine ⟨h1, h2.imp id fun h3 => ⟨h3.1, h3.2.1, fun x hx r hr => ?_⟩⟩
        rcases List.mem_append.1 hr with hr | hr
        · exact h3.2.2 x hx r hr
        · simp at hr
      · intro p a o' l hp
        by_cases hpq : p = q
        · subst hpq; simp at hp; obtain ⟨rfl, -, rfl⟩ := hp; exact hfresh
        · simp only [Function.update_of_ne hpq] at hp; exact hI.loc p a o' l hp
  | evict i =>
    have hi := fin1 i; subst hi
    have heq : Alg.step1 W C (.evict 0) = (Alg.writeBack W C 0, []) := rfl
    rw [heq] at hH ⊢
    obtain ⟨hI', hpm⟩ := hI.writeBack hT
    refine ⟨L, by simpa using hI'⟩
  | crash =>
    have heq : Alg.step1 W C .crash =
        ({ C with cache := C.pm, dirty := fun _ => false, ts := fun _ => .idle }, [.crash]) := rfl
    rw [heq] at hH ⊢
    by_cases hpm : C.pm 0 = true
    · -- persistent: keep `L`
      have hc : C.cache 0 = true := by
        by_contra hc; simp at hc; have := (hI.cache_false hc).2.1; simp [this] at hpm
      refine ⟨L, hH, hI.lin.append_crash (List.prefix_refl L) (fun x hx hn => absurd
        (List.mem_map_of_mem hx) hn), fun h' => by simp [hpm] at h', fun _ => ?_, hI.wear_eq,
        by simp⟩
      exact ⟨(hI.cache_true hc).1, Or.inl ⟨hpm, rfl⟩⟩
    · -- not persistent: drop everything
      have hpm' : C.pm 0 = false := by simpa using hpm
      refine ⟨[], hH, hI.lin.append_crash (List.nil_prefix) ?_, fun _ => ⟨rfl, hpm', rfl⟩,
        fun h' => by simp [hpm'] at h', hI.wear_eq, by simp⟩
      intro x hx _ r hr
      by_cases hc : C.cache 0 = true
      · rcases (hI.cache_true hc).2 with h1 | h1
        · exact hpm h1.1
        · exact h1.2.2 x hx r hr
      · simp at hc; rw [(hI.cache_false hc).1] at hx; simp at hx
  | step q =>
    cases hq : C.ts q with
    | idle =>
      have heq : Alg.step1 W C (.step q) = (C, []) := by simp [Alg.step1, hq]
      rw [heq]; simpa using ⟨L, hI⟩
    | run a o l =>
      have hloc := hI.loc q a o l hq
      have hane := hI.hinv.run_notEnded _ _ _ _ hq
      have hainv := hI.hinv.run_inv _ _ _ _ hq
      have ho : o = () := rfl
      subst ho
      cases l with
      | start =>
        by_cases hc : C.cache 0 = true
        · -- failed CAS: linearize after the winner
          have heq : Alg.step1 W C (.step q) =
              ({ C with ts := Function.update C.ts q (.run a () (TL.fl true)) }, []) := by
            simp [Alg.step1, hq, hc]
          rw [heq] at hH ⊢
          simp only [List.append_nil] at hH ⊢
          obtain ⟨hne, h2⟩ := hI.cache_true hc
          refine ⟨L ++ [(a, ())], hH, hI.lin.push hainv hloc hane, fun h' => by simp [hc] at h',
            fun _ => ⟨by simp, h2.imp id fun h3 => ⟨h3.1, h3.2.1, fun x hx r hr => ?_⟩⟩,
            hI.wear_eq, fun p b o' l' hp => ?_⟩
          · rcases List.mem_append.1 hx with hx | hx
            · exact h3.2.2 x hx r hr
            · simp at hx; subst hx; exact not_mem_res_of_notEnded hane r hr
          · by_cases hpq : p = q
            · subst hpq; simp at hp; obtain ⟨rfl, -, rfl⟩ := hp
              refine ⟨L.length, ?_, by simp⟩
              exact Nat.one_le_iff_ne_zero.2 (by simpa using hne)
            · simp only [Function.update_of_ne hpq] at hp
              have hl := hI.loc p b o' l' hp
              have hb : b ≠ a := by
                rintro rfl; exact hpq (hI.hinv.run_inj _ _ _ _ _ _ _ hp hq)
              cases l' with
              | start =>
                show b ∉ (L ++ [(a, ())]).map Prod.fst
                have hl' : b ∉ L.map Prod.fst := hl
                simpa [hb] using hl'
              | fl r =>
                cases r
                · obtain ⟨rest, hr⟩ := (hl : ∃ rest, L = (b, ()) :: rest)
                  exact ⟨rest ++ [(a, ())], by simp [hr]⟩
                · obtain ⟨n, hn, hr⟩ := (hl : ∃ n, 1 ≤ n ∧ L[n]? = some (b, ()))
                  exact ⟨n, hn, by rw [List.getElem?_append_left
                    (List.getElem?_eq_some_iff.1 hr).1]; exact hr⟩
              | done r =>
                cases r
                · obtain ⟨⟨rest, hr⟩, hp'⟩ := (hl : (∃ rest, L = (b, ()) :: rest) ∧ _)
                  exact ⟨⟨rest ++ [(a, ())], by simp [hr]⟩, hp'⟩
                · obtain ⟨⟨n, hn, hr⟩, hp'⟩ := (hl : (∃ n, 1 ≤ n ∧ L[n]? = some (b, ())) ∧ _)
                  exact ⟨⟨n, hn, by rw [List.getElem?_append_left
                    (List.getElem?_eq_some_iff.1 hr).1]; exact hr⟩, hp'⟩
        · -- successful CAS: the winner
          have hc' : C.cache 0 = false := by simpa using hc
          obtain ⟨hL, hpm, hd⟩ := hI.cache_false hc'
          subst hL
          have heq : Alg.step1 W C (.step q) =
              ({ C with cache := Function.update C.cache 0 true,
                        dirty := Function.update C.dirty 0 true,
                        ts := Function.update C.ts q (.run a () (TL.fl false)) }, []) := by
            simp [Alg.step1, hq, hc']
          rw [heq] at hH ⊢
          simp only [List.append_nil] at hH ⊢
          refine ⟨[(a, ())], hH, by simpa using hI.lin.push hainv hloc hane,
            fun h' => by simp at h', fun _ => ⟨by simp, Or.inr ⟨hpm, by simp, ?_⟩⟩,
            hI.wear_eq, fun p b o' l' hp => ?_⟩
          · intro x hx r hr; simp at hx; subst hx; exact not_mem_res_of_notEnded hane r hr
          · by_cases hpq : p = q
            · subst hpq; simp at hp; obtain ⟨rfl, -, rfl⟩ := hp; exact ⟨[], rfl⟩
            · simp only [Function.update_of_ne hpq] at hp
              have hl := hI.loc p b o' l' hp
              have hb : b ≠ a := by
                rintro rfl; exact hpq (hI.hinv.run_inj _ _ _ _ _ _ _ hp hq)
              cases l' with
              | start =>
                show b ∉ [(a, ())].map Prod.fst
                simpa using hb
              | fl r =>
                cases r
                · obtain ⟨rest, hr⟩ := (hl : ∃ rest, ([] : List (ℕ × Unit)) = (b, ()) :: rest)
                  simp at hr
                · obtain ⟨n, _, hr⟩ := (hl : ∃ n, 1 ≤ n ∧ ([] : List (ℕ × Unit))[n]? = _)
                  simp at hr
              | done r =>
                cases r
                · obtain ⟨⟨rest, hr⟩, _⟩ :=
                    (hl : (∃ rest, ([] : List (ℕ × Unit)) = (b, ()) :: rest) ∧ _)
                  simp at hr
                · obtain ⟨⟨n, _, hr⟩, _⟩ :=
                    (hl : (∃ n, 1 ≤ n ∧ ([] : List (ℕ × Unit))[n]? = _) ∧ _)
                  simp at hr
      | fl r =>
        have hc := hI.cache_of_loc hq
        have heq : Alg.step1 W C (.step q) =
            ({ Alg.writeBack W C 0 with ts := Function.update C.ts q (.run a () (TL.done r)) },
              []) := by simp [Alg.step1, hq]
        rw [heq] at hH ⊢
        simp only [List.append_nil] at hH ⊢
        obtain ⟨hI', hpm⟩ := hI.writeBack hT
        have hmono : C.pm 0 = true → (Alg.writeBack W C 0).pm 0 = true := fun _ => hpm hc
        refine ⟨L, hH, hI'.lin, hI'.cache_false, hI'.cache_true, hI'.wear_eq,
          fun p b o' l' hp => ?_⟩
        by_cases hpq : p = q
        · subst hpq; simp at hp; obtain ⟨rfl, -, rfl⟩ := hp
          cases r
          · exact ⟨hloc, hpm hc⟩
          · exact ⟨hloc, hpm hc⟩
        · simp only [Function.update_of_ne hpq] at hp
          exact (hI.loc p b o' l' hp).mono_pm hmono
      | done r =>
        have heq : Alg.step1 W C (.step q) =
            ({ C with ts := Function.update C.ts q .idle }, [.res a r]) := by
          simp [Alg.step1, hq]
        rw [heq] at hH ⊢
        have hpmt : C.pm 0 = true := by cases r <;> exact hloc.2
        -- the position of `a` in `L` determines the response
        have hlin : IsStrictLin tasObj (h ++ [.res a r]) L := by
          cases r with
          | false =>
            obtain ⟨⟨rest, hL⟩, -⟩ := (hloc : (∃ rest, L = (a, ()) :: rest) ∧ _)
            exact hI.lin.append_res (L₁ := []) (by simpa using hL) (by simp; rfl)
          | true =>
            obtain ⟨⟨n, hn, hL⟩, -⟩ := (hloc : (∃ n, 1 ≤ n ∧ L[n]? = some (a, ())) ∧ _)
            have hlt := (List.getElem?_eq_some_iff.1 hL).1
            have hsplit : L = L.take n ++ (a, ()) :: L.drop (n + 1) := by
              conv_lhs => rw [← List.take_append_drop n L]
              congr 1
              rw [List.drop_eq_getElem_cons hlt]
              congr 1
              exact (List.getElem?_eq_some_iff.1 hL).2
            refine hI.lin.append_res hsplit ?_
            rw [tas_resp, eq_comm, decide_eq_true_eq]
            exact ⟨by omega, by rintro rfl; simp at hlt⟩
        refine ⟨L, hH, hlin, hI.cache_false, fun hc => ?_, hI.wear_eq, fun p b o' l' hp => ?_⟩
        · obtain ⟨hne, h2⟩ := hI.cache_true hc
          refine ⟨hne, Or.inl ⟨hpmt, ?_⟩⟩
          rcases h2 with h2 | h2
          · exact h2.2
          · simp [hpmt] at h2
        · by_cases hpq : p = q
          · subst hpq; simp at hp
          · simp only [Function.update_of_ne hpq] at hp
            exact hI.loc p b o' l' hp

lemma tInv_exec {W : Wear 1 Bool} (hT : (1 : ℕ∞) ≤ W.T) (es : List (Ev 1 P Unit)) :
    ∃ L, TInv (exec W (initCfg tasAlg P) es).1 (exec W (initCfg tasAlg P) es).2 L := by
  induction es using List.reverseRecOn with
  | nil =>
    refine ⟨[], hInv_init, IsStrictLin.nil, fun _ => ⟨rfl, rfl, rfl⟩, fun h => ?_, rfl, ?_⟩
    · exact absurd h Bool.false_ne_true
    · intro p a o l hp; cases hp
  | append_singleton es e ih =>
    obtain ⟨L, hI⟩ := ih
    rw [exec_concat]
    exact hI.step1 hT e

/-- The TAS implementation is strictly linearizable in every wear model with `T ≥ 1`, whatever
the number of invocations. -/
theorem tas_strictLin {W : Wear 1 Bool} (hT : (1 : ℕ∞) ≤ W.T) (es : List (Ev 1 P Unit)) :
    StrictLinearizable tasObj (hist tasAlg P W es) := by
  obtain ⟨L, hI⟩ := tInv_exec (P := P) hT es
  exact ⟨L, hI.lin⟩

/-! ### Lock-freedom (in fact wait-freedom: three steps per operation) -/

/-- Potential of a thread. -/
def φt : TS Unit TL → ℕ
  | .idle => 4
  | .run _ _ .start => 3
  | .run _ _ (.fl _) => 2
  | .run _ _ (.done _) => 1

lemma tas_phi_step (W : Wear 1 Bool) (C : Cfg tasAlg P) (ev : Ev 1 P Unit)
    (hcr : ev ≠ .crash) (hno : ∀ a r, (step1 W C ev).2 ≠ [.res a r]) :
    (∀ q, φt ((step1 W C ev).1.ts q) ≤ φt (C.ts q)) ∧
    (∀ p, ev = .step p → C.ts p ≠ .idle → φt ((step1 W C ev).1.ts p) < φt (C.ts p)) := by
  cases ev with
  | crash => exact absurd rfl hcr
  | evict i =>
    refine ⟨fun q => by simp [step1, writeBack_ts], ?_⟩
    intro p hp; cases hp
  | inv p o =>
    cases hp : C.ts p with
    | run => simp [step1, hp]
    | idle =>
      refine ⟨fun q => ?_, fun _ h => by cases h⟩
      by_cases hqp : q = p
      · subst hqp; simp [step1, hp, φt]
      · simp [step1, hp, Function.update_of_ne hqp]
  | step p =>
    cases hp : C.ts p with
    | idle =>
      refine ⟨fun q => by simp [step1, hp], ?_⟩
      intro p' hp' hne; cases hp'; exact absurd hp hne
    | run a o l =>
      have key : ∃ l' : TL, (step1 W C (.step p)).1.ts = Function.update C.ts p (.run a o l') ∧
          φt (.run a o l') < φt (.run a o l) := by
        cases l with
        | start =>
          by_cases hc : C.cache 0 = false
          · exact ⟨.fl false, by simp [step1, hp, hc], by simp [φt]⟩
          · exact ⟨.fl true, by simp [step1, hp, hc], by simp [φt]⟩
        | fl r => exact ⟨.done r, by simp [step1, hp, writeBack_ts], by simp [φt]⟩
        | done r => exact absurd (by simp [step1, hp]) (hno a r)
      obtain ⟨l', hts, hlt⟩ := key
      refine ⟨fun q => ?_, fun p' hp' _ => ?_⟩
      · rw [hts]
        by_cases hqp : q = p
        · subst hqp; simp [hp]; exact le_of_lt hlt
        · simp [Function.update_of_ne hqp]
      · cases hp'; rw [hts]; simp [hp]; exact hlt

/-- The TAS implementation is lock-free (for finitely many threads, in every wear model). -/
theorem tas_lockFree [Finite P] (W : Wear 1 Bool) : LockFree tasAlg P W := by
  classical
  have := Fintype.ofFinite P
  intro e _ ⟨t₀, hcr⟩ hsteps t
  by_contra hcon
  push Not at hcon
  set t₁ := max t t₀ with ht₁
  let Φ : ℕ → ℕ := fun s => ∑ p, φt ((cfgAt tasAlg P W e s).ts p)
  have hΦ : ∀ s ≥ t₁, Φ (s + 1) ≤ Φ s ∧
      (∀ p, e s = .step p → (cfgAt tasAlg P W e s).ts p ≠ .idle → Φ (s + 1) < Φ s) := by
    intro s hs
    have H := tas_phi_step W _ (e s) (hcr s (by omega)) (fun a r h => hcon s (by omega) a r h)
    refine ⟨?_, fun p hp hrun => ?_⟩
    · show ∑ q, _ ≤ ∑ q, _
      rw [cfgAt_succ]
      exact Finset.sum_le_sum fun q _ => H.1 q
    · show ∑ q, _ < ∑ q, _
      rw [cfgAt_succ]
      exact Finset.sum_lt_sum (fun q _ => H.1 q) ⟨p, Finset.mem_univ _, H.2 p hp hrun⟩
  have hmono : ∀ s ≥ t₁, ∀ u ≥ s, Φ u ≤ Φ s := by
    intro s hs u hu
    induction u, hu using Nat.le_induction with
    | base => exact le_rfl
    | succ u hu ih => exact le_trans (hΦ u (by omega)).1 ih
  have hdec : ∀ n, ∃ s ≥ t₁, Φ s + n ≤ Φ t₁ := by
    intro n
    induction n with
    | zero => exact ⟨t₁, le_rfl, by simp⟩
    | succ n ih =>
      obtain ⟨s, hs, hsn⟩ := ih
      obtain ⟨u, hu, p, hp, hrun⟩ := hsteps s
      have h1 := (hΦ u (by omega)).2 p hp hrun
      have h2 := hmono s hs u hu
      exact ⟨u + 1, by omega, by omega⟩
  obtain ⟨s, -, hs⟩ := hdec (Φ t₁ + 1)
  omega

/-- With one word of endurance `1`, the TAS implementation maintains safety and liveness in
**all** executions (any number of TAS invocations). -/
theorem tas_guarantees [Finite P] : GuaranteesUpTo tasAlg P 1 ⊤ :=
  fun _ => ⟨fun es _ => tas_strictLin (le_refl _) es, fun e _ => tas_lockFree _ e trivial⟩

/-- The statement of **Theorem 4.4** of [Liu–Golab, PODC'22], for implementations in our model:
any implementation using `k` words of endurance `T` cannot maintain safety and liveness in all
executions with `k·T + 1` updates. -/
def Theorem44Statement (P : Type) [DecidableEq P] : Prop :=
  ∀ (O : ObjSpec) (k : ℕ) (V : Type) [DecidableEq V] (A : Alg O k V) (T : ℕ),
    ¬ GuaranteesUpTo A P T (k * T + 1 : ℕ)

/-- **Theorem 4.4 is false as stated**: test-and-set from a single word of endurance `1`
maintains safety and liveness in all executions, in particular with `k·T + 1 = 2` updates. -/
theorem theorem_4_4_false [Finite P] : ¬ Theorem44Statement P := by
  intro h
  exact h tasObj 1 Bool tasAlg 1 fun junk => (tas_guarantees junk).imp
    (fun hS es _ => hS es le_top) (fun hL e _ => hL e fun _ => le_top)

end Podc.WearLeveling
