import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Infix
import Cslib.Computability.Distributed.SharedMemory.Spec

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Persistent/StrictLin.lean

/-!
# Strict linearizability of histories with system-wide crashes

Histories of a concurrent object whose executions may contain *system-wide crashes*: a list of
invocation events `inv a p o` (operation instance `a`, a fresh natural number, invoked by
thread `p` with operation `o`), response events `res a r` and crash events.

*Strict linearizability* (Aguilera–Frølund, HP Labs TR HPL-2003-241) requires a linearization in
which an operation that is pending at a crash either takes effect before the crash or never.
Equivalently: an operation *ends* at its response, or at the first crash after its invocation
(`EndsAt`); the strict real-time order `SPrec h a b` holds if `a` ends before `b` is invoked; a
strict linearization `IsStrictLin O h L` is a sequential order `L` of invoked operation instances
that contains every operation that responded, respects `SPrec`, and is legal for the sequential
specification `O` (completed operations return the response prescribed by `O`). Operations that
are pending at the end of the history may or may not be included.

The incremental lemmas `IsStrictLin.append_inv`, `append_res`, `append_crash`, `push` build a
strict linearization along an execution (linearization points, with the possibility to drop
a suffix of not-yet-persisted operations at a crash).

## Main definitions

* `HEv`, `InvAt`, `EndsAt`, `NotEnded`, `SPrec`, `Legal`, `IsStrictLin`, `invCount`
-/

namespace Cslib.SharedMemory.Persistent

open Cslib.SharedMemory

/-- Events of a history with system-wide crashes. -/
inductive HEv (P Op R : Type) where
  /-- Operation instance `a` is invoked by thread `p` with operation `o`. -/
  | inv (a : ℕ) (p : P) (o : Op)
  /-- Operation instance `a` returns `r`. -/
  | res (a : ℕ) (r : R)
  /-- A system-wide crash. -/
  | crash

variable {P Op R : Type}

/-- Position `j` of `h` is the invocation of `a`. -/
def InvAt (h : List (HEv P Op R)) (a j : ℕ) : Prop := ∃ p o, h[j]? = some (.inv a p o)

/-- Operation `a` has *ended* at position `i` of `h`: its response is at `i`, or `i` is a crash
after the invocation of `a`. -/
def EndsAt (h : List (HEv P Op R)) (a i : ℕ) : Prop :=
  (∃ r, h[i]? = some (.res a r)) ∨ (h[i]? = some .crash ∧ ∃ j < i, InvAt h a j)

/-- `a` has not ended in `h` (it has not responded and no crash occurred after its
invocation). -/
def NotEnded (h : List (HEv P Op R)) (a : ℕ) : Prop := ∀ i, ¬ EndsAt h a i

/-- Strict real-time order: `a` ended before `b` was invoked. -/
def SPrec (h : List (HEv P Op R)) (a b : ℕ) : Prop := ∃ i j, i < j ∧ EndsAt h a i ∧ InvAt h b j

/-- Number of invocations in a history. -/
def invCount (h : List (HEv P Op R)) : ℕ :=
  h.countP fun e => match e with | .inv .. => true | _ => false

@[simp] lemma invCount_nil : invCount ([] : List (HEv P Op R)) = 0 := rfl

@[simp] lemma invCount_append (h h' : List (HEv P Op R)) :
    invCount (h ++ h') = invCount h + invCount h' := by
  simp [invCount, List.countP_append]

@[simp] lemma invCount_inv (a : ℕ) (p : P) (o : Op) :
    invCount [(HEv.inv a p o : HEv P Op R)] = 1 := rfl

@[simp] lemma invCount_res (a : ℕ) (r : R) : invCount [(HEv.res a r : HEv P Op R)] = 0 := rfl

@[simp] lemma invCount_crash : invCount [(HEv.crash : HEv P Op R)] = 0 := rfl

@[simp] lemma invCount_cons_inv (a : ℕ) (p : P) (o : Op) (h : List (HEv P Op R)) :
    invCount (HEv.inv a p o :: h) = invCount h + 1 := by
  simp [invCount]

@[simp] lemma invCount_cons_res (a : ℕ) (r : R) (h : List (HEv P Op R)) :
    invCount (HEv.res a r :: h) = invCount h := by
  simp [invCount]

@[simp] lemma invCount_cons_crash (h : List (HEv P Op R)) :
    invCount (HEv.crash :: h) = invCount h := by
  simp [invCount]

variable (O : ObjSpec)

/-- Legality of a sequential order `L` of operation instances from state `σ`: every operation of
`L` that responded in `h` returned the response prescribed by the specification. -/
def Legal (h : List (HEv P O.Op O.Resp)) : O.State → List (ℕ × O.Op) → Prop
  | _, [] => True
  | σ, (a, o) :: L => (∀ r, HEv.res a r ∈ h → r = (O.δ σ o).2) ∧ Legal h (O.δ σ o).1 L

/-- `L` is a *strict linearization* of the history `h` (for the sequential specification `O`). -/
structure IsStrictLin (h : List (HEv P O.Op O.Resp)) (L : List (ℕ × O.Op)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  inv_of_mem : ∀ x ∈ L, ∃ p, HEv.inv x.1 p x.2 ∈ h
  mem_of_res : ∀ a r, HEv.res a r ∈ h → a ∈ L.map Prod.fst
  rt : L.Pairwise fun x y => ¬ SPrec h y.1 x.1
  legal : Legal O h O.init L

/-- A history is *strictly linearizable* if it has a strict linearization. -/
def StrictLinearizable (h : List (HEv P O.Op O.Resp)) : Prop := ∃ L, IsStrictLin O h L

/-! ### Legality -/

variable {O}

lemma Legal.mono {h h' : List (HEv P O.Op O.Resp)}
    (hh : ∀ a r, HEv.res a r ∈ h' → HEv.res a r ∈ h) :
    ∀ {σ L}, Legal O h σ L → Legal O h' σ L
  | _, [], _ => trivial
  | _, (_, _) :: _, ⟨h1, h2⟩ => ⟨fun r hr => h1 r (hh _ _ hr), Legal.mono hh h2⟩

lemma legal_append {h : List (HEv P O.Op O.Resp)} :
    ∀ {σ} (L₁ L₂ : List (ℕ × O.Op)),
      Legal O h σ (L₁ ++ L₂) ↔ Legal O h σ L₁ ∧ Legal O h (O.runOps σ (L₁.map Prod.snd)) L₂
  | _, [], _ => by simp [Legal]
  | _, (a, o) :: L₁, L₂ => by
    simp only [List.cons_append, Legal, List.map_cons, ObjSpec.runOps_cons]
    rw [legal_append L₁ L₂]; tauto

lemma legal_iff_getElem {h : List (HEv P O.Op O.Resp)} :
    ∀ {σ} (L : List (ℕ × O.Op)), Legal O h σ L ↔
      ∀ n x, L[n]? = some x → ∀ r, HEv.res x.1 r ∈ h →
        r = (O.δ (O.runOps σ ((L.take n).map Prod.snd)) x.2).2
  | _, [] => by simp [Legal]
  | σ, (a, o) :: L => by
    simp only [Legal]
    rw [legal_iff_getElem L]
    constructor
    · rintro ⟨h1, h2⟩ n x hx r hr
      cases n with
      | zero => simp at hx; subst hx; simpa using h1 r hr
      | succ n => simpa using h2 n x (by simpa using hx) r hr
    · intro H
      refine ⟨fun r hr => by simpa using H 0 (a, o) rfl r hr, fun n x hx r hr => ?_⟩
      simpa using H (n + 1) x (by simpa using hx) r hr

/-! ### Real-time order under appending events -/

lemma InvAt.append {h : List (HEv P Op R)} {a j : ℕ} (e : List (HEv P Op R))
    (hj : InvAt h a j) : InvAt (h ++ e) a j := by
  obtain ⟨p, o, hj⟩ := hj
  have : j < h.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  exact ⟨p, o, by rw [List.getElem?_append_left this]; exact hj⟩

lemma InvAt.of_append {h : List (HEv P Op R)} {e : HEv P Op R} {a j : ℕ}
    (hj : InvAt (h ++ [e]) a j) (hlt : j < h.length) : InvAt h a j := by
  obtain ⟨p, o, hj⟩ := hj
  exact ⟨p, o, by rwa [List.getElem?_append_left hlt] at hj⟩

lemma EndsAt.of_append {h : List (HEv P Op R)} {e : HEv P Op R} {a i : ℕ}
    (hi : EndsAt (h ++ [e]) a i) (hlt : i < h.length) : EndsAt h a i := by
  rcases hi with ⟨r, hr⟩ | ⟨hc, j, hj, hinv⟩
  · exact Or.inl ⟨r, by rwa [List.getElem?_append_left hlt] at hr⟩
  · exact Or.inr ⟨by rwa [List.getElem?_append_left hlt] at hc, j, hj,
      hinv.of_append (by omega)⟩

lemma EndsAt.append {h : List (HEv P Op R)} {a i : ℕ} (e : List (HEv P Op R))
    (hi : EndsAt h a i) : EndsAt (h ++ e) a i := by
  have hlt : i < h.length := by
    by_contra hc
    rcases hi with ⟨r, hr⟩ | ⟨hc', _⟩
    · rw [List.getElem?_eq_none (by omega)] at hr; cases hr
    · rw [List.getElem?_eq_none (by omega)] at hc'; cases hc'
  rcases hi with ⟨r, hr⟩ | ⟨hc, j, hj, hinv⟩
  · exact Or.inl ⟨r, by rw [List.getElem?_append_left hlt]; exact hr⟩
  · exact Or.inr ⟨by rw [List.getElem?_append_left hlt]; exact hc, j, hj, hinv.append e⟩

/-- Appending a non-invocation event creates no new strict real-time order. -/
lemma SPrec.of_append_noninv {h : List (HEv P Op R)} {e : HEv P Op R}
    (he : ∀ a p o, e ≠ .inv a p o) {x y : ℕ} (hs : SPrec (h ++ [e]) x y) : SPrec h x y := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  have hjlt : j < h.length := by
    obtain ⟨p, o, hj⟩ := hj
    by_contra hc
    rcases Nat.lt_or_ge j (h.length + 1) with h1 | h1
    · have : j = h.length := by omega
      subst this; simp at hj; exact he _ _ _ hj
    · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
  exact ⟨i, j, hij, hi.of_append (by omega), hj.of_append hjlt⟩

/-- Appending the invocation of `a` creates strict real-time order only towards `a`. -/
lemma SPrec.of_append_inv {h : List (HEv P Op R)} {a : ℕ} {p : P} {o : Op} {x y : ℕ}
    (hs : SPrec (h ++ [.inv a p o]) x y) (hy : y ≠ a) : SPrec h x y := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  have hjlt : j < h.length := by
    obtain ⟨p', o', hj⟩ := hj
    by_contra hc
    rcases Nat.lt_or_ge j (h.length + 1) with h1 | h1
    · have : j = h.length := by omega
      subst this; simp at hj; exact hy hj.1.symm
    · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
  exact ⟨i, j, hij, hi.of_append (by omega), hj.of_append hjlt⟩

/-- If `a` responded in `h₁` and `b` is invoked in `h₂`, then `a` strictly precedes `b` in
`h₁ ++ h₂`. -/
lemma SPrec.of_split {h₁ h₂ : List (HEv P Op R)} {a b : ℕ} {r : R} {p : P} {o : Op}
    (ha : HEv.res a r ∈ h₁) (hb : HEv.inv b p o ∈ h₂) : SPrec (h₁ ++ h₂) a b := by
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
  refine ⟨i, h₁.length + j, by omega, Or.inl ⟨r, ?_⟩, p, o, ?_⟩
  · rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hia]
  · rw [List.getElem?_append_right (by omega)]; simp [List.getElem?_eq_getElem hj, hjb]

lemma NotEnded.of_append {h : List (HEv P Op R)} {a : ℕ} (e : List (HEv P Op R))
    (ha : NotEnded (h ++ e) a) : NotEnded h a :=
  fun i hi => ha i (hi.append e)

lemma not_mem_res_of_notEnded {h : List (HEv P Op R)} {a : ℕ} (ha : NotEnded h a) (r : R) :
    HEv.res a r ∉ h := by
  intro hm
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  exact ha i (Or.inl ⟨r, by rw [List.getElem?_eq_getElem hi, he]⟩)

/-! ### Building strict linearizations incrementally -/

namespace IsStrictLin

variable {h : List (HEv P O.Op O.Resp)} {L : List (ℕ × O.Op)}

lemma nil : IsStrictLin O ([] : List (HEv P O.Op O.Resp)) [] :=
  ⟨by simp, by simp, by simp, by simp, trivial⟩

/-- A fresh invocation does not affect a strict linearization. -/
lemma append_inv (hL : IsStrictLin O h L) {a : ℕ} {p : P} {o : O.Op}
    (ha : a ∉ L.map Prod.fst) : IsStrictLin O (h ++ [.inv a p o]) L where
  nodup := hL.nodup
  inv_of_mem x hx := by
    obtain ⟨q, hq⟩ := hL.inv_of_mem x hx; exact ⟨q, List.mem_append_left _ hq⟩
  mem_of_res b r hr := by
    rcases List.mem_append.1 hr with hr | hr
    · exact hL.mem_of_res b r hr
    · simp at hr
  rt := hL.rt.imp_of_mem fun {x y} hx _ hxy hs => hxy (hs.of_append_inv fun he => ha (by
    rw [← he]; exact List.mem_map_of_mem hx))
  legal := Legal.mono (fun b r hr => by
    rcases List.mem_append.1 hr with hr | hr
    · exact hr
    · simp at hr) hL.legal

/-- A response that agrees with the position of the operation in the linearization. -/
lemma append_res (hL : IsStrictLin O h L) {L₁ L₂ : List (ℕ × O.Op)} {a : ℕ} {o : O.Op}
    (hsplit : L = L₁ ++ (a, o) :: L₂) {r : O.Resp}
    (hr : r = (O.δ (O.runOps O.init (L₁.map Prod.snd)) o).2) :
    IsStrictLin O (h ++ [.res a r]) L where
  nodup := hL.nodup
  inv_of_mem x hx := by
    obtain ⟨q, hq⟩ := hL.inv_of_mem x hx; exact ⟨q, List.mem_append_left _ hq⟩
  mem_of_res b r' hr' := by
    rcases List.mem_append.1 hr' with hr' | hr'
    · exact hL.mem_of_res b r' hr'
    · simp at hr'; rw [hr'.1, hsplit]; simp
  rt := hL.rt.imp fun hxy hs => hxy (hs.of_append_noninv (by intros; simp))
  legal := by
    have hl := hL.legal
    have hnd := hL.nodup
    subst hsplit
    rw [legal_iff_getElem] at hl ⊢
    intro n x hx r' hr'
    rcases List.mem_append.1 hr' with hr' | hr'
    · exact hl n x hx r' hr'
    · simp at hr'
      obtain ⟨rfl, rfl⟩ := hr'
      -- `x` is at position `n` and has id `a`, so `n = L₁.length` by `nodup`
      have hn : n = L₁.length := by
        have hlt : L₁.length < ((L₁ ++ (x.1, o) :: L₂).map Prod.fst).length := by simp
        have key : ((L₁ ++ (x.1, o) :: L₂).map Prod.fst)[L₁.length]? =
            ((L₁ ++ (x.1, o) :: L₂).map Prod.fst)[n]? := by
          rw [List.getElem?_map, List.getElem?_map, hx,
            List.getElem?_append_right (le_refl _)]
          simp
        exact ((List.Nodup.getElem?_inj hlt hnd).1 key).symm
      subst hn
      have : x = (x.1, o) := by
        rw [List.getElem?_append_right (le_refl _)] at hx; simp at hx; exact hx.symm
      rw [this]
      simpa [List.take_append_of_le_length (le_refl _)] using hr

/-- Linearizing an invoked, not yet ended operation at the end of the order. -/
lemma push (hL : IsStrictLin O h L) {a : ℕ} {p : P} {o : O.Op} (hinv : HEv.inv a p o ∈ h)
    (ha : a ∉ L.map Prod.fst) (hne : NotEnded h a) : IsStrictLin O h (L ++ [(a, o)]) where
  nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hL.nodup, by simp, ?_⟩
    intro b hb c hc hbc
    simp at hc; subst hc; subst hbc; exact ha hb
  inv_of_mem x hx := by
    rcases List.mem_append.1 hx with hx | hx
    · exact hL.inv_of_mem x hx
    · simp at hx; subst hx; exact ⟨p, hinv⟩
  mem_of_res b r hr := by
    have := hL.mem_of_res b r hr; simp only [List.map_append, List.mem_append]; exact Or.inl this
  rt := by
    rw [List.pairwise_append]
    refine ⟨hL.rt, by simp, ?_⟩
    intro x _ y hy hs
    simp at hy; subst hy
    obtain ⟨i, _, _, hi, _⟩ := hs
    exact hne i hi
  legal := by
    rw [legal_append]
    exact ⟨hL.legal, fun r hr => absurd hr (not_mem_res_of_notEnded hne r), trivial⟩

/-- At a crash, a suffix of operations that have not responded can be dropped. -/
lemma append_crash (hL : IsStrictLin O h L) {L' : List (ℕ × O.Op)} (hpre : L' <+: L)
    (hdrop : ∀ x ∈ L, x.1 ∉ L'.map Prod.fst → ∀ r, HEv.res x.1 r ∉ h) :
    IsStrictLin O (h ++ [.crash]) L' where
  nodup := (hpre.sublist.map Prod.fst).nodup hL.nodup
  inv_of_mem x hx := by
    obtain ⟨q, hq⟩ := hL.inv_of_mem x (hpre.subset hx); exact ⟨q, List.mem_append_left _ hq⟩
  mem_of_res b r hr := by
    rcases List.mem_append.1 hr with hr | hr
    · have hb := hL.mem_of_res b r hr
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
      by_contra hc
      exact hdrop x hx hc r hr
    · simp at hr
  rt := (hL.rt.sublist hpre.sublist).imp fun hxy hs =>
    hxy (hs.of_append_noninv (by intros; simp))
  legal := by
    obtain ⟨L₂, rfl⟩ := hpre
    exact Legal.mono (fun b r hr => by
      rcases List.mem_append.1 hr with hr | hr
      · exact hr
      · simp at hr) ((legal_append _ _).1 hL.legal).1

end IsStrictLin

end Cslib.SharedMemory.Persistent
