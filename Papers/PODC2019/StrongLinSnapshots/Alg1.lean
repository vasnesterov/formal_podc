import Papers.PODC2019.StrongLinSnapshots.ABADefs
import Podc.Computability.Distributed.SharedMemory.WriteStrongLin

/-!
# Observation 4: Algorithm 1 is not strongly linearizable

Sean Ovens, Philipp Woelfel. *Strongly Linearizable Implementations of Snapshots and Other
Types.* PODC 2019 (arXiv:1908.10826), Section 3.1.

Algorithm 1 is the linearizable ABA-detecting register of Aghazadeh–Woelfel. Its `DWrite` and
`GetSeq` are those of Algorithm 2 (`ABADefs.lean`); its `DRead_q()` uses a persistent local
Boolean `b` (initially `false`):

```
15 (x,p,s) ← X.Read()      16 (r,sr) ← A[q].Read()
17 A[q].Write(p,s)         18 (x',p',s') ← X.Read()
19–24 ret ← if (p,s) = (r,sr) then (x, b) else (x, true)
25–30 b ← ((x,p,s) ≠ (x',p',s'))
31 return ret
```

`alg1 v₀ pick` models it (for any `n`, `V`, `v₀` and choice function `pick`) as an
implementation of `abaObj (Fin n) V v₀`.

## The counterexample (Observation 4)

We instantiate the paper's proof with `n = 2`, `V = Bool`, `v₀ = false`, `pick = pickMin`
(choose the smallest admissible sequence number); reader `p = 0`, writer `q = 1`, written value
`true`. While `A[0] = A[1] = ⊥`, the consecutive `DWrite`s of `q` choose sequence numbers
`0, 1, 2, 3, 0`, so the paper's `dw_i` / `dw_{i+1}` / `dw_j` are `dw1` / `dw2` / `dw5`.

* `S  = dw1 ◦ (dr1 up to the end of line 16) ◦ dw2` (`dr1` reads `X = (x, q, 0)` on line 15);
* `T1 = S ◦ dw3 ◦ dw4 ◦ dw5 ◦ (rest of dr1) ◦ dr2`: `dr1` sees `(x,q,0)` again on line 18 and
  clears `b`; `dr2` finds `A[p] = (q,0) = X`'s tag and returns `(x, false)`;
* `T2 = S ◦ (rest of dr1) ◦ dr2`: `dr2` reads `X = (x,q,1) ≠ A[p] = (q,0)` and returns
  `(x, true)`.

If `dr1` is linearized before `dw2` in `f S`, then in `f T1` the operation `dw2` lies between
`dr1` and `dr2`, so `dr2` must return flag `true`. Otherwise `dw1, dw2` precede `dr1` in `f T2`,
which precede `dr2` with no `DWrite` in between, so `dr2` must return flag `false`.

Operation identifiers: `dw_k = (1, k-1)`, `dr1 = (0,0)`, `dr2 = (0,1)`.
-/

namespace Podc.StrongLinSnapshots.Alg1

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection Podc.StrongLinSnapshots

variable (n : ℕ) (V : Type)

/-- Program counters of Algorithm 1. -/
inductive PC where
  /-- No pending operation. -/
  | idle
  /-- `DWrite(x)`: about to read `A[c]` (line 3). -/
  | wA (x : V)
  /-- `DWrite(x)`: about to write `(x, p, s)` to `X` (line 2). -/
  | wX (x : V) (s : Seq n)
  /-- `DWrite(x)`: about to return. -/
  | wRet (x : V)
  /-- `DRead`: about to read `X` (line 15). -/
  | d15
  /-- `DRead`: about to read `A[q]` (line 16); `v` was read on line 15. -/
  | d16 (v : Val n V)
  /-- `DRead`: about to write `A[q]` (line 17); `a` was read on line 16. -/
  | d17 (v : Val n V) (a : Tag n)
  /-- `DRead`: about to read `X` (line 18). -/
  | d18 (v : Val n V) (a : Tag n)
  /-- `DRead`: about to return `(x, c)` (line 31). -/
  | dRet (x : V) (c : Bool)

/-- Local states of Algorithm 1. -/
structure Loc where
  /-- Program counter. -/
  pc : PC n V
  /-- The persistent flag `b` of `DRead`. -/
  b : Bool
  /-- `GetSeq` state. -/
  gs : GS n

variable {n V}

/-- The next action in each program counter. -/
def act [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) (p : Fin n) (l : Loc n V) :
    Action (abaObj (Fin n) V v₀) (B n V v₀) (Loc n V) :=
  match l.pc with
  | .idle => .ret (v₀, false) l
  | .wA x => .access (some l.gs.c) .read (fun r => ⟨.wX x (getSeq pick p l.gs r.2).1, l.b,
      (getSeq pick p l.gs r.2).2⟩)
  | .wX x s => .access none (.write (x, some (p, s))) (fun _ => ⟨.wRet x, l.b, l.gs⟩)
  | .wRet x => .ret (x, true) ⟨.idle, l.b, l.gs⟩
  | .d15 => .access none .read (fun v => ⟨.d16 v, l.b, l.gs⟩)
  | .d16 v => .access (some p) .read (fun a => ⟨.d17 v a.2, l.b, l.gs⟩)
  | .d17 v a => .access (some p) (.write (v₀, v.2)) (fun _ => ⟨.d18 v a, l.b, l.gs⟩)
  | .d18 v a => .access none .read (fun v' =>
      ⟨.dRet v.1 (if v.2 = a then l.b else true), (if v = v' then false else true), l.gs⟩)
  | .dRet x c => .ret (x, c) ⟨.idle, l.b, l.gs⟩

/-- **Algorithm 1** (Aghazadeh–Woelfel's linearizable ABA-detecting register), with `GetSeq`'s
arbitrary choice given by `pick`. -/
def alg1 [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) :
    Impl (abaObj (Fin n) V v₀) (B n V v₀) (Fin n) (Loc n V) where
  memInit _ := (v₀, none)
  locInit p := ⟨.idle, false, ⟨⟨0, p.pos⟩, fun _ => none, []⟩⟩
  invoke _ l o := match o with
    | .dwrite x => ⟨.wA x, l.b, l.gs⟩
    | .dread _ => ⟨.d15, l.b, l.gs⟩
  act := act v₀ pick
  allowed := allowedOp

instance [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) (p : Fin n)
    (o : ABAOp (Fin n) V) : Decidable ((alg1 v₀ pick).allowed p o) :=
  inferInstanceAs (Decidable (allowedOp p o))

/-! ## The flag of the sequential specification -/

section Flag

variable {P K : Type} [DecidableEq P] {v₀ : V}

lemma flag_true_of_no_dread (s : (abaObj P V v₀).State) (p : P) (os : List (ABAOp P V))
    (hs : s.2 p = true) (hos : ∀ o ∈ os, o ≠ .dread p) :
    ((abaObj P V v₀).runOps s os).2 p = true := by
  induction os generalizing s with
  | nil => exact hs
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    refine ih _ ?_ (fun o' h => hos o' (by simp [h]))
    cases o with
    | dread q =>
      have hq : q ≠ p := fun h => hos (.dread q) (by simp) (by rw [h])
      simp [Function.update_of_ne (Ne.symm hq), hs]
    | dwrite x => rfl

lemma flag_false_of_no_dwrite (s : (abaObj P V v₀).State) (p : P) (os : List (ABAOp P V))
    (hs : s.2 p = false) (hos : ∀ o ∈ os, ∀ x, o ≠ .dwrite x) :
    ((abaObj P V v₀).runOps s os).2 p = false := by
  induction os generalizing s with
  | nil => exact hs
  | cons o os ih =>
    rw [ObjSpec.runOps_cons]
    refine ih _ ?_ (fun o' h => hos o' (by simp [h]))
    cases o with
    | dread q =>
      by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne (Ne.symm hq), hs]
    | dwrite x => exact absurd rfl (hos _ (by simp) x)

/-- After a `DWrite` followed by no `DRead` of `p`, the flag of `p` is set. -/
lemma flag_after_dwrite (s : (abaObj P V v₀).State) (p : P) (L₁ L₂ : List (K × ABAOp P V))
    (y : K) (x : V) (h : ∀ e ∈ L₂, e.2 ≠ .dread p) :
    ((abaObj P V v₀).runOps s ((L₁ ++ (y, .dwrite x) :: L₂).map Prod.snd)).2 p = true := by
  rw [List.map_append, ObjSpec.runOps_append, List.map_cons, ObjSpec.runOps_cons]
  exact flag_true_of_no_dread _ p _ rfl (fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ho; exact h e he)

/-- After a `DRead` of `p` followed by no `DWrite`, the flag of `p` is clear. -/
lemma flag_after_dread (s : (abaObj P V v₀).State) (p : P) (L₁ L₂ : List (K × ABAOp P V))
    (y : K) (h : ∀ e ∈ L₂, ∀ x, e.2 ≠ .dwrite x) :
    ((abaObj P V v₀).runOps s ((L₁ ++ (y, .dread p) :: L₂).map Prod.snd)).2 p = false := by
  rw [List.map_append, ObjSpec.runOps_append, List.map_cons, ObjSpec.runOps_cons]
  exact flag_false_of_no_dwrite _ p _ (by simp) (fun o ho => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ho; exact h e he)

end Flag

/-! ## List lemmas -/

section Lists

variable {X : Type}

/-- If `a` is in the prefix `l` of the duplicate-free `m`, `c ∈ m`, and `c` does not come before
`a` in `l`, then `a` comes before `c` in `m`. -/
lemma sublist_pair_of_prefix {a c : X} {l m : List X} (hp : l <+: m) (ha : a ∈ l) (hc : c ∈ m)
    (hac : a ≠ c) (hn : ¬ [c, a].Sublist l) : [a, c].Sublist m := by
  obtain ⟨M, rfl⟩ := hp
  by_cases hcl : c ∈ l
  · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
    rcases List.mem_append.1 hcl with h | h
    · exact absurd (sublist_pair_iff.2 ⟨l₁, a :: l₂, rfl, h, by simp⟩) hn
    · rcases List.mem_cons.1 h with h | h
      · exact absurd h.symm hac
      · exact (sublist_pair_iff.2 ⟨l₁ ++ [a], l₂, by simp, by simp, h⟩).trans
          (List.sublist_append_left _ _)
  · exact sublist_pair_iff.2 ⟨l, M, rfl, ha, by simpa [hcl] using List.mem_append.1 hc⟩

lemma not_mem_both {u y : X} {l₁ l₂ l₃ : List X} (h : (l₁ ++ y :: (l₂ ++ l₃)).Nodup)
    (h₁ : u ∈ l₁) (h₂ : u ∈ l₂) : False :=
  (List.nodup_append.1 h).2.2 u h₁ u (by simp [h₂]) rfl

end Lists

/-! ## The executions -/

/-- Labels of the counterexample: `n = 2`, `V = Bool`, `v₀ = false`. -/
abbrev Lbl := Label (Fin 2) (abaObj (Fin 2) Bool false)

/-- The instance of Algorithm 1 used in the counterexample. -/
abbrev I₀ := alg1 (n := 2) false pickMin

/-- A complete `DWrite_q(true)` of the writer `q = 1`. -/
def dw : List Lbl := [.inv 1 (.dwrite true), .tau 1, .tau 1, .ret 1 (true, true)]

/-- `dr1` up to the end of line 16. -/
def dr1a : List Lbl := [.inv 0 (.dread 0), .tau 0, .tau 0]

/-- `dr1` from line 17 to completion; it returns `(true, true)` (it read `A[0] = ⊥`). -/
def dr1b : List Lbl := [.tau 0, .tau 0, .ret 0 (true, true)]

/-- A complete `dr2` returning `(true, c)`. -/
def dr2 (c : Bool) : List Lbl := [.inv 0 (.dread 0), .tau 0, .tau 0, .tau 0, .tau 0, .ret 0 (true, c)]

/-- `S = dw1 ◦ (dr1 to the end of line 16) ◦ dw2`. -/
def S : List Lbl := dw ++ dr1a ++ dw

/-- `T1 = S ◦ dw3 ◦ dw4 ◦ dw5 ◦ (dr1 from line 17) ◦ dr2`; `dr2` returns `(true, false)`. -/
def T1 : List Lbl := S ++ dw ++ dw ++ dw ++ dr1b ++ dr2 false

/-- `T2 = S ◦ (dr1 from line 17) ◦ dr2`; `dr2` returns `(true, true)`. -/
def T2 : List Lbl := S ++ dr1b ++ dr2 true

theorem valid_T1 : I₀.Valid T1 := by
  apply Impl.valid_of_crun; decide +kernel

theorem valid_T2 : I₀.Valid T2 := by
  apply Impl.valid_of_crun; decide +kernel

theorem S_prefix_T1 : S <+: T1 := by
  simp only [T1, List.append_assoc]; exact List.prefix_append _ _

theorem S_prefix_T2 : S <+: T2 := by
  simp only [T2, List.append_assoc]; exact List.prefix_append _ _

/-! ## Facts about the histories -/

lemma opsOf_T1 : opsOf T1 = fun p => if p = 0 then [.dread 0, .dread 0] else
    [.dwrite true, .dwrite true, .dwrite true, .dwrite true, .dwrite true] := by
  funext p; fin_cases p <;> decide

lemma opsOf_T2 : opsOf T2 = fun p => if p = 0 then [.dread 0, .dread 0] else
    [.dwrite true, .dwrite true] := by
  funext p; fin_cases p <;> decide

lemma dread_ids_T1 {y : OpId (Fin 2)} (h : opOf T1 y = some (.dread 0)) :
    y = (0, 0) ∨ y = (0, 1) := by
  obtain ⟨p, k⟩ := y
  simp only [opOf, opsOf_T1] at h
  fin_cases p
  · rcases k with _ | _ | k <;> simp_all
  · rcases k with _ | _ | _ | _ | _ | k <;> simp_all

lemma dwrite_ids_T2 {y : OpId (Fin 2)} {x : Bool} (h : opOf T2 y = some (.dwrite x)) :
    y = (1, 0) ∨ y = (1, 1) := by
  obtain ⟨p, k⟩ := y
  simp only [opOf, opsOf_T2] at h
  fin_cases p
  · rcases k with _ | _ | k <;> simp_all
  · rcases k with _ | _ | k <;> simp_all

lemma opOf_S_dr2 : opOf S ((0 : Fin 2), 1) = none := by decide

/-! ## Observation 4 -/

/-- **Observation 4 of [Ovens–Woelfel 2019]**: the ABA-detecting register of Algorithm 1
(Aghazadeh–Woelfel) is not strongly linearizable (instance `n = 2`, `V = Bool`, `v₀ = false`,
`GetSeq` choosing the smallest admissible sequence number). -/
theorem observation4 : ¬ I₀.StronglyLinearizable := by
  rintro ⟨f, hlin, hpre⟩
  have hS := hlin S (I₀.valid_of_prefix valid_T1 S_prefix_T1)
  have h1 := hlin T1 valid_T1
  have h2 := hlin T2 valid_T2
  have hp1 : (f S).map Prod.fst <+: (f T1).map Prod.fst :=
    (hpre S T1 valid_T1 S_prefix_T1).map _
  have hp2 : (f S).map Prod.fst <+: (f T2).map Prod.fst :=
    (hpre S T2 valid_T2 S_prefix_T2).map _
  have haS : ((1 : Fin 2), 1) ∈ (f S).map Prod.fst :=
    hS.complete _ (by unfold Completed; decide)
  have hbS : ((0 : Fin 2), 1) ∉ (f S).map Prod.fst := by
    intro hm
    obtain ⟨e, he, hee⟩ := List.mem_map.1 hm
    have := hS.op_eq e he
    rw [hee, opOf_S_dr2] at this
    exact absurd this (by simp)
  by_cases hA : [((0 : Fin 2), 0), ((1 : Fin 2), 1)].Sublist ((f S).map Prod.fst)
  · -- Case A: `dr1` is linearized before `dw2` in `f S`; look at `dr2` in `T1`.
    have hr := h1.respIn_eq (x := (0, 1)) (r := (true, false)) (by decide)
    obtain ⟨L₁, L₂, o, hsplit, hresp⟩ := ObjSpec.exists_split_of_respIn_eq_some hr
    have ho : o = .dread 0 := by
      have := h1.op_eq ((0, 1), o) (by rw [hsplit]; simp)
      rw [show opOf T1 (0, 1) = some (.dread 0) by decide] at this
      exact (Option.some.inj this).symm
    subst ho
    have hflag : ((abaObj (Fin 2) Bool false).runOps (abaObj (Fin 2) Bool false).init
        (L₁.map Prod.snd)).2 0 = false := by
      have := congrArg Prod.snd hresp; simpa using this
    have hnd := h1.nodup
    rw [hsplit] at hnd
    simp only [List.map_append, List.map_cons] at hnd
    -- `dw2` lies in `L₁`
    have hab : [((1 : Fin 2), 1), ((0 : Fin 2), 1)].Sublist ((f T1).map Prod.fst) := by
      obtain ⟨M, hM⟩ := hp1
      refine sublist_pair_iff.2 ⟨_, M, hM.symm, haS, ?_⟩
      have hb : ((0 : Fin 2), 1) ∈ (f T1).map Prod.fst := by rw [hsplit]; simp
      rw [← hM] at hb
      simpa [hbS] using List.mem_append.1 hb
    rw [hsplit] at hab
    simp only [List.map_append, List.map_cons] at hab
    have haL₁ := mem_left_of_sublist_pair hnd hab
    obtain ⟨e, he, hee⟩ := List.mem_map.1 haL₁
    obtain ⟨X, Y, rfl⟩ := List.append_of_mem he
    obtain ⟨y, o'⟩ := e
    simp only at hee
    subst hee
    have ho' : o' = .dwrite true := by
      have := h1.op_eq ((1, 1), o') (by rw [hsplit]; simp)
      rw [show opOf T1 (1, 1) = some (.dwrite true) by decide] at this
      exact (Option.some.inj this).symm
    subst ho'
    -- `dr1` lies in `X`
    have hca : [((0 : Fin 2), 0), ((1 : Fin 2), 1)].Sublist ((f T1).map Prod.fst) :=
      hA.trans hp1.sublist
    rw [hsplit] at hca
    simp only [List.append_assoc, List.cons_append, List.map_append, List.map_cons] at hca hnd
    have hcX := mem_left_of_sublist_pair hnd hca
    -- no `DRead` of `0` in `Y`
    have hY : ∀ e ∈ Y, e.2 ≠ .dread 0 := by
      intro e heY heq
      have hop := h1.op_eq e (by rw [hsplit]; simp [heY])
      rw [heq] at hop
      have heY' : e.1 ∈ Y.map Prod.fst := List.mem_map_of_mem heY
      rcases dread_ids_T1 hop with h | h
      · rw [h] at heY'
        exact not_mem_both hnd hcX heY'
      · rw [h] at heY'
        have hnd' := hnd.sublist (List.sublist_append_right _ _)
        simp only [List.nodup_cons, List.mem_append, List.mem_cons, not_or] at hnd'
        exact (List.nodup_append.1 hnd'.2).2.2 _ heY' _ (by simp) rfl
    have := flag_after_dwrite (v₀ := false) (abaObj (Fin 2) Bool false).init 0 X Y (1, 1) true hY
    rw [this] at hflag
    exact absurd hflag (by decide)
  · -- Case B: otherwise; look at `dr2` in `T2`.
    have hr := h2.respIn_eq (x := (0, 1)) (r := (true, true)) (by decide)
    obtain ⟨L₁, L₂, o, hsplit, hresp⟩ := ObjSpec.exists_split_of_respIn_eq_some hr
    have ho : o = .dread 0 := by
      have := h2.op_eq ((0, 1), o) (by rw [hsplit]; simp)
      rw [show opOf T2 (0, 1) = some (.dread 0) by decide] at this
      exact (Option.some.inj this).symm
    subst ho
    have hflag : ((abaObj (Fin 2) Bool false).runOps (abaObj (Fin 2) Bool false).init
        (L₁.map Prod.snd)).2 0 = true := by
      have := congrArg Prod.snd hresp; simpa using this
    have hnd := h2.nodup
    -- `dr1` precedes `dr2`
    have hcb : [((0 : Fin 2), 0), ((0 : Fin 2), 1)].Sublist ((f T2).map Prod.fst) :=
      h2.realtime _ _ (by decide) (by rw [hsplit]; simp)
    rw [hsplit] at hcb hnd
    simp only [List.map_append, List.map_cons] at hcb hnd
    have hcL₁ := mem_left_of_sublist_pair hnd hcb
    obtain ⟨e, he, hee⟩ := List.mem_map.1 hcL₁
    obtain ⟨X, Y, rfl⟩ := List.append_of_mem he
    obtain ⟨y, o'⟩ := e
    simp only at hee
    subst hee
    have ho' : o' = .dread 0 := by
      have := h2.op_eq ((0, 0), o') (by rw [hsplit]; simp)
      rw [show opOf T2 (0, 0) = some (.dread 0) by decide] at this
      exact (Option.some.inj this).symm
    subst ho'
    simp only [List.append_assoc, List.cons_append, List.map_append, List.map_cons] at hnd
    -- no `DWrite` in `Y`
    have hY : ∀ e ∈ Y, ∀ x, e.2 ≠ .dwrite x := by
      intro e heY x heq
      have hop := h2.op_eq e (by rw [hsplit]; simp [heY])
      rw [heq] at hop
      have heY' : e.1 ∈ Y.map Prod.fst := List.mem_map_of_mem heY
      have hpair : [e.1, ((0 : Fin 2), 0)].Sublist ((f T2).map Prod.fst) := by
        rcases dwrite_ids_T2 hop with h | h
        · rw [h]; exact h2.realtime _ _ (by decide) (by rw [hsplit]; simp)
        · rw [h]
          exact sublist_pair_of_prefix hp2 haS (by rw [hsplit]; simp) (by decide) hA
      rw [hsplit] at hpair
      simp only [List.append_assoc, List.cons_append, List.map_append, List.map_cons] at hpair
      exact not_mem_both hnd (mem_left_of_sublist_pair hnd hpair) heY'
    have := flag_after_dread (v₀ := false) (abaObj (Fin 2) Bool false).init 0 X Y (0, 0) hY
    rw [this] at hflag
    exact absurd hflag (by decide)

end Podc.StrongLinSnapshots.Alg1
