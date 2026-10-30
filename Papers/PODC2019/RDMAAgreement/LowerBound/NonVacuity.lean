import Papers.PODC2019.RDMAAgreement.LowerBound.Theorem61

/-!
# Non-vacuity of the hypotheses of Theorem 6.1

The hypotheses of `theorem_6_1` (agreement and validity in all asynchronous executions,
termination in synchronous runs with at most one crash) are satisfiable: we exhibit a 2-process
binary consensus algorithm with static permissions (all permissions granted) satisfying them.

Registers `a0`, `a1`, `d`, initially `none`. Every process has at most one operation in flight,
and a step receiving no response does nothing.
* `P0` (input `v0`): writes `a0 := some v0`; on the ack reads `a1`; if it is `none`, decides `v0`
  (fast path); otherwise reads `d` until it is `some w` and decides `w`.
* `P1` (input `v1`): writes `a1 := some v1`; on the ack reads `a0`; decides the value read if any,
  otherwise `v1`; then writes `d := its decision`.

Safety is proved by an inductive invariant: every reachable configuration is `embed v0 v1 φ0 φ1`
for *phases* `φ0 : Ph0`, `φ1 : Ph1` of the two processes satisfying the finite predicate `good`;
the commutation of events with `embed` and the preservation of `good` are checked by `decide`
over the finite set of phases.
-/

namespace Podc.RDMAAgreement.LowerBound.NonVacuity

open Podc.RDMAAgreement.LowerBound

/-- The registers. -/
inductive Reg | a0 | a1 | d
  deriving DecidableEq

instance : Fintype Reg where
  elems := {.a0, .a1, .d}
  complete x := by cases x <;> simp

/-- Local states: writing own register, reading the other's register, waiting on `d`, decided. -/
inductive St | wr (v : Bool) | rd (v : Bool) | wt (v : Bool) | dn (v : Bool)
  deriving DecidableEq

/-- Memory operations. -/
abbrev O := Op Reg (Option Bool)
/-- Responses. -/
abbrev Rs := Resp (Option Bool)

/-- The step function of `P0`. -/
def step0 : St → List (O × Rs) → St × List O
  | s, [] => (s, [])
  | .wr v, _ :: _ => (.rd v, [.read .a1])
  | .rd v, (_, .val none) :: _ => (.dn v, [])
  | .rd v, _ :: _ => (.wt v, [.read .d])
  | .wt _, (_, .val (some w)) :: _ => (.dn w, [])
  | .wt v, _ :: _ => (.wt v, [.read .d])
  | .dn v, _ :: _ => (.dn v, [])

/-- The step function of `P1`. -/
def step1 : St → List (O × Rs) → St × List O
  | s, [] => (s, [])
  | .wr v, _ :: _ => (.rd v, [.read .a0])
  | .rd _, (_, .val (some w)) :: _ => (.dn w, [.write .d (some w)])
  | .rd v, _ :: _ => (.dn v, [.write .d (some v)])
  | s, _ :: _ => (s, [])

/-- The decision recorded in a local state. -/
def St.dec : St → Option Bool
  | .dn v => some v
  | _ => none

/-- The algorithm. -/
def alg : Alg (Fin 2) Bool Reg (Option Bool) St where
  mem0 _ := none
  canRead _ _ := true
  canWrite _ _ := true
  init p v := (.wr v, [.write (if p = 0 then .a0 else .a1) (some v)])
  step p := if p = 0 then step0 else step1
  decision := St.dec

/-! ### Phases and the invariant -/

/-- Phases of `P0`. -/
inductive Ph0 | A | B | C | D (y : Option Bool) | E | F (y : Option Bool) | G (w : Bool)
  deriving DecidableEq, Fintype

/-- Phases of `P1`. -/
inductive Ph1 | A | B | C | D (y : Option Bool) | E (w : Bool) | F (w : Bool) | G (w : Bool)
  deriving DecidableEq, Fintype

/-- Local state, pending operations and undelivered responses of `P0` in a phase. -/
def loc0 (v : Bool) : Ph0 → St × List O × List (O × Rs)
  | .A => (.wr v, [.write .a0 (some v)], [])
  | .B => (.wr v, [], [(.write .a0 (some v), .ack)])
  | .C => (.rd v, [.read .a1], [])
  | .D y => (.rd v, [], [(.read .a1, .val y)])
  | .E => (.wt v, [.read .d], [])
  | .F y => (.wt v, [], [(.read .d, .val y)])
  | .G w => (.dn w, [], [])

/-- Local state, pending operations and undelivered responses of `P1` in a phase. -/
def loc1 (v : Bool) : Ph1 → St × List O × List (O × Rs)
  | .A => (.wr v, [.write .a1 (some v)], [])
  | .B => (.wr v, [], [(.write .a1 (some v), .ack)])
  | .C => (.rd v, [.read .a0], [])
  | .D y => (.rd v, [], [(.read .a0, .val y)])
  | .E w => (.dn w, [.write .d (some w)], [])
  | .F w => (.dn w, [], [(.write .d (some w), .ack)])
  | .G w => (.dn w, [], [])

/-- The content of `d` in a phase of `P1`. -/
def Ph1.dval : Ph1 → Option Bool
  | .F w => some w
  | .G w => some w
  | _ => none

/-- The decision of `P1` in a phase. -/
def Ph1.dec : Ph1 → Option Bool
  | .E w => some w
  | .F w => some w
  | .G w => some w
  | _ => none

/-- The memory determined by the phases. -/
def memOf (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) : Reg → Option Bool
  | .a0 => if φ0 = .A then none else some v0
  | .a1 => if φ1 = .A then none else some v1
  | .d => φ1.dval

/-- The configuration determined by the inputs and the phases. -/
def embed (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) : Cfg (Fin 2) Reg (Option Bool) St where
  st p := if p = 0 then (loc0 v0 φ0).1 else (loc1 v1 φ1).1
  mem := memOf v0 v1 φ0 φ1
  pend p := if p = 0 then (loc0 v0 φ0).2.1 else (loc1 v1 φ1).2.1
  ready p := if p = 0 then (loc0 v0 φ0).2.2 else (loc1 v1 φ1).2.2

/-- `P1` has not yet read `a0`, or read `some v0`. -/
def okD1 (v0 : Bool) : Ph1 → Bool
  | .A | .B | .C => true
  | .D y => y == some v0
  | _ => false

/-- The invariant on phases. -/
def good (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) : Bool :=
  (match φ0 with
    | .D none => okD1 v0 φ1 || φ1.dec == some v0
    | .D (some y) => y == v1
    | .F (some y) => φ1.dval == some y
    | .G w => φ1.dec == some w || (w == v0 && okD1 v0 φ1)
    | _ => true) &&
  (match φ1 with
    | .D (some y) => y == v0
    | .E w | .F w | .G w => w == v0 || w == v1
    | _ => true)

/-- Phase transition of `P0` when its pending operation takes effect. -/
def lin0 (v1 : Bool) (φ1 : Ph1) : Ph0 → Ph0
  | .A => .B
  | .C => .D (if φ1 = .A then none else some v1)
  | .E => .F φ1.dval
  | φ => φ

/-- Phase transition of `P0` when it takes a step receiving its response. -/
def stp0 (v0 : Bool) : Ph0 → Ph0
  | .B => .C
  | .D none => .G v0
  | .D (some _) => .E
  | .F (some w) => .G w
  | .F none => .E
  | φ => φ

/-- Phase transition of `P1` when its pending operation takes effect. -/
def lin1 (v0 : Bool) (φ0 : Ph0) : Ph1 → Ph1
  | .A => .B
  | .C => .D (if φ0 = .A then none else some v0)
  | .E w => .F w
  | φ => φ

/-- Phase transition of `P1` when it takes a step receiving its response. -/
def stp1 (v1 : Bool) : Ph1 → Ph1
  | .B => .C
  | .D (some w) => .E w
  | .D none => .E v1
  | .F w => .G w
  | φ => φ

/-- Abstract events: process, and whether its pending operation takes effect (`true`) or it takes
a step receiving its response (`false`). -/
def next (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) : Fin 2 × Bool → Ph0 × Ph1
  | (p, true) => if p = 0 then (lin0 v1 φ1 φ0, φ1) else (φ0, lin1 v0 φ0 φ1)
  | (p, false) => if p = 0 then (stp0 v0 φ0, φ1) else (φ0, stp1 v1 φ1)

/-- The concrete event of an abstract event. -/
def toEv (c : Cfg (Fin 2) Reg (Option Bool) St) : Fin 2 × Bool → Event (Fin 2) Reg (Option Bool)
  | (p, true) => .lin p ((c.pend p).headD (.read .d))
  | (p, false) => .step p 1

/-- Componentwise equality of configurations (decidable). -/
def CfgEqv (c c' : Cfg (Fin 2) Reg (Option Bool) St) : Prop :=
  (∀ p : Fin 2, c.st p = c'.st p ∧ c.pend p = c'.pend p ∧ c.ready p = c'.ready p) ∧
    ∀ r : Reg, c.mem r = c'.mem r

instance (c c' : Cfg (Fin 2) Reg (Option Bool) St) : Decidable (CfgEqv c c') := by
  unfold CfgEqv; infer_instance

lemma commute_all : ∀ (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) (ev : Fin 2 × Bool),
    CfgEqv (alg.exec (embed v0 v1 φ0 φ1) (toEv (embed v0 v1 φ0 φ1) ev))
      (embed v0 v1 (next v0 v1 φ0 φ1 ev).1 (next v0 v1 φ0 φ1 ev).2) := by
  decide

lemma good_next : ∀ (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) (ev : Fin 2 × Bool),
    good v0 v1 φ0 φ1 = true →
      good v0 v1 (next v0 v1 φ0 φ1 ev).1 (next v0 v1 φ0 φ1 ev).2 = true := by
  decide

lemma len_le_one : ∀ (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) (p : Fin 2),
    ((embed v0 v1 φ0 φ1).pend p).length ≤ 1 ∧ ((embed v0 v1 φ0 φ1).ready p).length ≤ 1 := by
  decide

lemma cfg_ext {c c' : Cfg (Fin 2) Reg (Option Bool) St} (h1 : c.st = c'.st) (h2 : c.mem = c'.mem)
    (h3 : c.pend = c'.pend) (h4 : c.ready = c'.ready) : c = c' := by
  cases c; cases c'; simp_all

lemma CfgEqv.eq {c c' : Cfg (Fin 2) Reg (Option Bool) St} (h : CfgEqv c c') : c = c' :=
  cfg_ext (funext fun p => (h.1 p).1) (funext h.2) (funext fun p => (h.1 p).2.1)
    (funext fun p => (h.1 p).2.2)

lemma alg_step_nil (p : Fin 2) (s : St) : alg.step p s [] = (s, []) := by
  simp only [alg]; split_ifs <;> cases s <;> rfl

lemma exec_step_zero (c : Cfg (Fin 2) Reg (Option Bool) St) (p : Fin 2) :
    alg.exec c (.step p 0) = c := by
  rw [Alg.exec_step]
  apply cfg_ext <;> simp [alg_step_nil]

lemma exec_step_succ (c : Cfg (Fin 2) Reg (Option Bool) St) (p : Fin 2) (k : ℕ)
    (h : (c.ready p).length ≤ 1) : alg.exec c (.step p (k + 1)) = alg.exec c (.step p 1) := by
  rw [Alg.exec_step, Alg.exec_step, List.take_of_length_le h,
    List.take_of_length_le (by omega), List.drop_of_length_le h,
    List.drop_of_length_le (by omega)]

/-- Every event from an embedded configuration acts as one of the abstract events, or not at
all. -/
lemma exec_embed (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) (e : Event (Fin 2) Reg (Option Bool)) :
    alg.exec (embed v0 v1 φ0 φ1) e = embed v0 v1 φ0 φ1 ∨
      ∃ ev, alg.exec (embed v0 v1 φ0 φ1) e =
        alg.exec (embed v0 v1 φ0 φ1) (toEv (embed v0 v1 φ0 φ1) ev) := by
  have hp := fun p => (len_le_one v0 v1 φ0 φ1 p).1
  have hr := fun p => (len_le_one v0 v1 φ0 φ1 p).2
  cases e with
  | lin p o =>
    by_cases ho : o ∈ (embed v0 v1 φ0 φ1).pend p
    · right
      refine ⟨(p, true), ?_⟩
      have hl := hp p
      rcases h : (embed v0 v1 φ0 φ1).pend p with _ | ⟨a, _ | ⟨b, l⟩⟩
      · simp [h] at ho
      · rw [h, List.mem_singleton] at ho; subst ho; simp [toEv, h]
      · rw [h] at hl; simp at hl
    · left
      simp only [Alg.exec_lin, ho, ↓reduceIte]
  | step p k =>
    rcases k with _ | k
    · exact Or.inl (exec_step_zero _ p)
    · exact Or.inr ⟨(p, false), exec_step_succ _ p k (hr p)⟩

/-- Reachable configurations from an embedded `good` configuration are embedded `good`
configurations. -/
lemma reach (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) (hg : good v0 v1 φ0 φ1 = true)
    (es : List (Event (Fin 2) Reg (Option Bool))) :
    ∃ ψ0 ψ1, good v0 v1 ψ0 ψ1 = true ∧ alg.run (embed v0 v1 φ0 φ1) es = embed v0 v1 ψ0 ψ1 := by
  induction es generalizing φ0 φ1 with
  | nil => exact ⟨φ0, φ1, hg, rfl⟩
  | cons e es ih =>
    rw [Alg.run_cons]
    rcases exec_embed v0 v1 φ0 φ1 e with h | ⟨ev, h⟩
    · rw [h]; exact ih φ0 φ1 hg
    · rw [h, (commute_all v0 v1 φ0 φ1 ev).eq]
      exact ih _ _ (good_next v0 v1 φ0 φ1 ev hg)

lemma init_eq (x : Fin 2 → Bool) : alg.initCfg x ∅ = embed (x 0) (x 1) .A .A := by
  apply cfg_ext
  · funext p; fin_cases p <;> rfl
  · funext r; cases r <;> rfl
  · funext p; fin_cases p <;> simp [Alg.initCfg, embed, alg, loc0, loc1]
  · funext p; fin_cases p <;> rfl

lemma reachable (x : Fin 2 → Bool) (es : List (Event (Fin 2) Reg (Option Bool))) :
    ∃ ψ0 ψ1, good (x 0) (x 1) ψ0 ψ1 = true ∧ alg.run (alg.initCfg x ∅) es = embed (x 0) (x 1) ψ0 ψ1 := by
  rw [init_eq]; exact reach _ _ _ _ (by decide +revert) es

/-! ### Decisions are irrevocable -/

lemma step_dn (p : Fin 2) (v : Bool) (l : List (O × Rs)) : (alg.step p (.dn v) l).1 = .dn v := by
  simp only [alg]; split_ifs <;> rcases l with _ | ⟨⟨o, r⟩, l⟩ <;> rfl

lemma dec_eq_some {s : St} {v : Bool} (h : s.dec = some v) : s = .dn v := by
  cases s <;> simp_all [St.dec]

lemma run_dn (c : Cfg (Fin 2) Reg (Option Bool) St) (es : List (Event (Fin 2) Reg (Option Bool)))
    (p : Fin 2) (v : Bool) (h : c.st p = .dn v) : (alg.run c es).st p = .dn v := by
  induction es generalizing c with
  | nil => exact h
  | cons e es ih =>
    rw [Alg.run_cons]
    apply ih
    cases e with
    | lin q o => rw [Alg.exec_lin_st]; exact h
    | step q k =>
      rw [Alg.exec_step]
      by_cases hq : p = q
      · subst hq; simp [h, step_dn]
      · simp [Function.update_of_ne hq, h]

lemma decides_at (x : Fin 2 → Bool) (es : List (Event (Fin 2) Reg (Option Bool))) (p : Fin 2)
    (v : Bool) {j J : ℕ} (hj : j ≤ J)
    (h : alg.decision ((alg.run (alg.initCfg x ∅) (es.take j)).st p) = some v) :
    alg.decision ((alg.run (alg.initCfg x ∅) (es.take J)).st p) = some v := by
  have hs := dec_eq_some h
  have he : es.take J = es.take j ++ (es.take J).drop j := by
    conv_lhs => rw [← List.take_append_drop j (es.take J)]
    rw [List.take_take, Nat.min_eq_left hj]
  rw [he, Alg.run_append, run_dn _ _ p v hs]; rfl

lemma agree_good : ∀ (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) (p q : Fin 2) (v w : Bool),
    good v0 v1 φ0 φ1 = true → ((embed v0 v1 φ0 φ1).st p).dec = some v →
      ((embed v0 v1 φ0 φ1).st q).dec = some w → v = w := by
  decide

lemma valid_good : ∀ (v0 v1 : Bool) (φ0 : Ph0) (φ1 : Ph1) (p : Fin 2) (v : Bool),
    good v0 v1 φ0 φ1 = true → ((embed v0 v1 φ0 φ1).st p).dec = some v → v = v0 ∨ v = v1 := by
  decide

/-- Agreement of the algorithm in all asynchronous executions. -/
theorem agreement : alg.Agreement := by
  rintro x es p q v w ⟨j, hj⟩ ⟨j', hj'⟩
  obtain ⟨ψ0, ψ1, hg, he⟩ := reachable x (es.take (max j j'))
  have h1 := decides_at x es p v (le_max_left j j') hj
  have h2 := decides_at x es q w (le_max_right j j') hj'
  rw [he] at h1 h2
  exact agree_good _ _ _ _ p q v w hg h1 h2

/-- Validity of the algorithm in all asynchronous executions. -/
theorem validity : alg.Validity := by
  rintro x es p v ⟨j, hj⟩
  obtain ⟨ψ0, ψ1, hg, he⟩ := reachable x (es.take j)
  rw [he] at hj
  rcases valid_good _ _ _ _ p v hg hj with h | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩

/-! ### Termination in synchronous runs -/

lemma univ_toList : (Finset.univ : Finset (Fin 2)).toList = [0, 1] ∨
    (Finset.univ : Finset (Fin 2)).toList = [1, 0] := by
  have hn := Finset.nodup_toList (Finset.univ : Finset (Fin 2))
  have hl : (Finset.univ : Finset (Fin 2)).toList.length = 2 := by simp
  revert hn hl
  generalize (Finset.univ : Finset (Fin 2)).toList = l
  intro hn hl
  match l, hn, hl with
  | [a, b], hn, _ => fin_cases a <;> fin_cases b <;> simp_all

/-- `roundEvs` with a given enumeration `L` of the processes (computable). -/
def roundEvsL (L : List (Fin 2)) (C : Finset (Fin 2)) (c : Cfg (Fin 2) Reg (Option Bool) St) :
    List (Event (Fin 2) Reg (Option Bool)) :=
  (L.flatMap fun q => ((c.pend q).filter Op.isRead).map (Event.lin q)) ++
    (L.flatMap fun q => ((c.pend q).filter fun o => !o.isRead).map (Event.lin q)) ++
    ((L.filter fun q => q ∉ C).map fun q => Event.step q (c.ready q).length)

/-- `syncRun` with a given enumeration `L` of the processes (computable). -/
def syncRunL (L : List (Fin 2)) (x : Fin 2 → Bool) (C : Finset (Fin 2)) :
    ℕ → Cfg (Fin 2) Reg (Option Bool) St
  | 0 => alg.initCfg x C
  | t + 1 => let c := syncRunL L x C t; alg.run c (roundEvsL L C c)

lemma syncRun_eq_L {L : List (Fin 2)} (hL : (Finset.univ : Finset (Fin 2)).toList = L)
    (x : Fin 2 → Bool) (C : Finset (Fin 2)) (t : ℕ) : alg.syncRun x C t = syncRunL L x C t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [Alg.syncRun, syncRunL, roundEvs, roundEvsL, hL, ih]

lemma crash_sets : ∀ C : Finset (Fin 2), C.card ≤ 1 → C = ∅ ∨ C = {0} ∨ C = {1} := by
  decide

lemma term_L : ∀ L ∈ [[(0 : Fin 2), 1], [1, 0]], ∀ a b : Bool, ∀ C ∈ [(∅ : Finset (Fin 2)), {0}, {1}],
    ∀ p : Fin 2, p ∉ C → (alg.decision ((syncRunL L ![a, b] C 8).st p)).isSome := by
  decide

/-- Termination of the algorithm in synchronous runs with at most one crash: every non-crashed
process has decided by time 8. -/
theorem syncTermination : alg.SyncTermination 1 := by
  intro x C hC p hp
  refine ⟨8, ?_⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] := ⟨x 0, x 1, by funext i; fin_cases i <;> rfl⟩
  have hCs : C ∈ [(∅ : Finset (Fin 2)), {0}, {1}] := by
    rcases crash_sets C hC with h | h | h <;> simp [h]
  rcases univ_toList with hL | hL
  · have h := term_L [0, 1] List.mem_cons_self a b C hCs p hp
    exact (syncRun_eq_L hL ![a, b] C 8) ▸ h
  · have h := term_L [1, 0] (List.mem_cons_of_mem _ List.mem_cons_self) a b C hCs p hp
    exact (syncRun_eq_L hL ![a, b] C 8) ▸ h

/-- The hypotheses of `theorem_6_1` are satisfiable: a 2-process binary consensus algorithm with
static permissions satisfying agreement, validity and synchronous termination with one crash. -/
theorem hypotheses_satisfiable :
    ∃ A : Alg (Fin 2) Bool Reg (Option Bool) St, A.Agreement ∧ A.Validity ∧ A.SyncTermination 1 :=
  ⟨alg, agreement, validity, syncTermination⟩

end Podc.RDMAAgreement.LowerBound.NonVacuity
