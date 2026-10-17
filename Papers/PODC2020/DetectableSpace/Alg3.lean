import Papers.PODC2020.DetectableSpace.Lin
import Papers.PODC2020.DetectableSpace.Perturbing
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Algorithm 3: a detectable max register without auxiliary state

Algorithm 3 of the paper: shared array `MR : Fin n → ℕ` (initially `0`); process `p` owns `MR[p]`.

* `WriteMax(v)`: if `MR[p] < v` then `MR[p] := v`; return `ack`.
* `Read()`: `a := 0`; `while a ≠ MR do a := MR`; persist and return `max a`. Comparing `a ≠ MR`
  reads `MR` entry by entry (a *comparison collect*), `a := MR` is an *assignment collect*.
* Recovery functions re-invoke the operation; no auxiliary state (`aux = id`).

We prove that it is durably linearizable and detectable (`alg3_durLinDet`) and
obstruction-free (`alg3_obstructionFree`), so the hypothesis "doubly-perturbing" of Theorem 2
cannot be dropped (a max register is not doubly-perturbing, Lemma 4).

Linearization: a write that changes `MR[p]` at its write; a write that does not, at its read of
`MR[p]` (unless it is already linearized, which happens when it is re-executed after a crash);
a read speculatively at the first read of a comparison collect if at that moment `MR = a`
(then `max a` is the current value), retracted if the collect fails or at a crash.
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg3

variable (n : ℕ)

/-- Local states (program counters with local variables). -/
inductive Loc where
  /-- `WriteMax(v)`, line 47: read `MR[p]`. -/
  | wmRead (v : ℕ)
  /-- line 48: `MR[p] := v`. -/
  | wmWrite (v : ℕ)
  /-- line 49: return `ack`. -/
  | wmRet
  /-- comparison collect: `a` the previous collect, `b` the entries read so far, next index `k`. -/
  | cmp (a b : Fin n → ℕ) (k : ℕ)
  /-- assignment collect `a := MR`, next index `k`. -/
  | asg (a : Fin n → ℕ) (k : ℕ)
  /-- line 54: persist the result. -/
  | persist (r : ℕ)
  /-- line 55: return. -/
  | rret (r : ℕ)

/-- Maximum of a collect. -/
def smax (a : Fin n → ℕ) : ℕ := Finset.univ.sup a

variable {n}

/-- The steps of Algorithm 3. -/
def act (p : Fin n) : Loc n → Act (Fin n → ℕ) (Option ℕ) (Loc n) ℕ
  | .wmRead v => .sh fun s => (if s p < v then .wmWrite v else .wmRet, s)
  | .wmWrite v => .sh fun s => (.wmRet, Function.update s p v)
  | .wmRet => .ret (some 0)
  | .cmp a b k =>
    if hk : k < n then .sh fun s => (.cmp a (Function.update b ⟨k, hk⟩ (s ⟨k, hk⟩)) (k + 1), s)
    else .sh fun s => (if b = a then .persist (smax n a) else .asg a 0, s)
  | .asg a k =>
    if hk : k < n then .sh fun s => (.asg (Function.update a ⟨k, hk⟩ (s ⟨k, hk⟩)) (k + 1), s)
    else .sh fun s => (.cmp a 0 0, s)
  | .persist r => .pv fun _ => (.rret r, some r)
  | .rret r => .ret (some r)

/-- Initial local state of an operation (also of its recovery: re-invocation). -/
def start : MaxOp → Loc n
  | .writeMax v => .wmRead v
  | .read => .cmp 0 0 0

end Alg3

open Alg3

/-- **Algorithm 3** as a recoverable implementation of a max register; no auxiliary state. -/
abbrev alg3 (n : ℕ) : RImpl maxReg (Fin n) where
  Sh := Fin n → ℕ
  Pv := Option ℕ
  L := Alg3.Loc n
  sh₀ := 0
  pv₀ := fun _ => none
  start _ o := Alg3.start o
  recov _ o := Alg3.start o
  aux _ _ v := v
  act := Alg3.act

lemma alg3_noAux (n : ℕ) : ∀ p o v, (alg3 n).aux p o v = v := fun _ _ _ => rfl

namespace Alg3

variable {n : ℕ}

/-! ### Auxiliary lemmas -/

lemma le_smax (a : Fin n → ℕ) (i : Fin n) : a i ≤ smax n a :=
  Finset.le_sup (f := a) (Finset.mem_univ i)

lemma smax_update (s : Fin n → ℕ) (p : Fin n) (v : ℕ) (h : s p ≤ v) :
    smax n (Function.update s p v) = max (smax n s) v := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    by_cases hi : i = p
    · subst hi; simp
    · simp only [Function.update_of_ne hi]; exact le_max_of_le_left (le_smax s i)
  · refine max_le (Finset.sup_le fun i _ => ?_) ?_
    · by_cases hi : i = p
      · subst hi; exact h.trans (by simpa using le_smax (Function.update s i v) i)
      · simpa [Function.update_of_ne hi] using le_smax (Function.update s p v) i
    · simpa using le_smax (Function.update s p v) p

lemma smax_zero : smax n (0 : Fin n → ℕ) = 0 :=
  Nat.eq_zero_of_le_zero (Finset.sup_le fun _ _ => le_rfl)

lemma maxReg_read_ro : maxReg.ReadOnly MaxOp.read := fun _ => rfl

/-- Two decompositions around the same identifier coincide (identifiers are distinct). -/
lemma decomp_unique {L L₁ L₂ M₁ M₂ : List (ℕ × MaxOp)} {a : ℕ} {o o' : MaxOp}
    (hnd : (L.map Prod.fst).Nodup) (h1 : L = L₁ ++ (a, o) :: L₂) (h2 : L = M₁ ++ (a, o') :: M₂) :
    L₁ = M₁ ∧ o = o' := by
  subst h1
  induction L₁ generalizing M₁ with
  | nil =>
    cases M₁ with
    | nil => simp at h2; exact ⟨rfl, h2.1⟩
    | cons y M₁ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp at hnd
  | cons x L₁ ih =>
    cases M₁ with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      simp at hnd
    | cons y M₁ =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, h2⟩ := h2
      obtain ⟨h3, h4⟩ := ih (by simpa using (List.nodup_cons.1 (by simpa using hnd)).2) h2
      exact ⟨by rw [h3], h4⟩

/-- The read entry of `a` sits at a position where the state is `r`. -/
def Pos (L : List (ℕ × MaxOp)) (a r : ℕ) : Prop :=
  ∃ L₁ L₂, L = L₁ ++ (a, .read) :: L₂ ∧ maxReg.runOps 0 (L₁.map Prod.snd) = r

lemma Pos.append {L : List (ℕ × MaxOp)} {a r : ℕ} (h : Pos L a r) (δ : List (ℕ × MaxOp)) :
    Pos (L ++ δ) a r := by
  obtain ⟨L₁, L₂, rfl, h2⟩ := h
  exact ⟨L₁, L₂ ++ δ, by simp, h2⟩

lemma Pos.filter {L : List (ℕ × MaxOp)} {a r : ℕ} (h : Pos L a r) (f : ℕ × MaxOp → Bool)
    (hf : ∀ y ∈ L, f y = false → y.1 ≠ a ∧ maxReg.ReadOnly y.2) : Pos (L.filter f) a r := by
  obtain ⟨L₁, L₂, rfl, h2⟩ := h
  have hfa : f (a, .read) = true := by
    by_contra hc; exact (hf (a, .read) (by simp) (by simpa using hc)).1 rfl
  refine ⟨L₁.filter f, L₂.filter f, by simp [List.filter_append, List.filter_cons_of_pos hfa], ?_⟩
  rw [← h2, maxReg.runOps_map_filter 0 L₁ Prod.snd f]
  intro x hx hfx
  exact (hf x (by simp [hx]) hfx).2

lemma Pos.mem {L : List (ℕ × MaxOp)} {a r : ℕ} (h : Pos L a r) : (a, .read) ∈ L := by
  obtain ⟨L₁, L₂, rfl, -⟩ := h; simp

/-! ### The per-process invariant -/

/-- What we know about process `p` executing operation instance `a` (operation `o`) in local
state `l`, given shared memory `sh` and linearization `L`. -/
def PInv (p : Fin n) (sh : Fin n → ℕ) (L : List (ℕ × MaxOp)) (a : ℕ) : MaxOp → Loc n → Prop
  | .writeMax v, .wmRead v' => v' = v ∧ (a ∈ L.map Prod.fst → v ≤ sh p)
  | .writeMax v, .wmWrite v' => v' = v ∧ sh p < v ∧ a ∉ L.map Prod.fst
  | .writeMax v, .wmRet => v ≤ sh p ∧ (a, .writeMax v) ∈ L
  | .read, .cmp x y k => (∀ i, x i ≤ sh i) ∧ (k = 0 → a ∉ L.map Prod.fst) ∧
      (a ∈ L.map Prod.fst → Pos L a (smax n x)) ∧
      (a ∉ L.map Prod.fst → 0 < k → ∃ i, x i < sh i ∧ (i.val < k → x i < y i))
  | .read, .asg x k => a ∉ L.map Prod.fst ∧ ∀ i : Fin n, i.val < k → x i ≤ sh i
  | .read, .persist r => Pos L a r
  | .read, .rret r => Pos L a r
  | _, _ => False

lemma PInv.push {p : Fin n} {sh : Fin n → ℕ} {L : List (ℕ × MaxOp)} {a : ℕ} {o : MaxOp}
    {l : Loc n} (h : PInv p sh L a o l) (x : ℕ × MaxOp) (hx : x.1 ≠ a) :
    PInv p sh (L ++ [x]) a o l := by
  have hmem : a ∈ (L ++ [x]).map Prod.fst ↔ a ∈ L.map Prod.fst := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]
    exact ⟨fun h' => h'.elim id (fun e => absurd e.symm hx), .inl⟩
  cases o <;> cases l <;> simp only [PInv] at h ⊢ <;> try rw [hmem]
  all_goals first
    | exact h
    | exact ⟨h.1, fun h' => (h.2 h')⟩
    | exact ⟨h.1, List.mem_append_left _ h.2⟩
    | exact Pos.append h _
    | exact ⟨h.1, h.2.1, fun h' => Pos.append (h.2.2.1 h') _, h.2.2.2⟩

lemma PInv.filter {p : Fin n} {sh : Fin n → ℕ} {L : List (ℕ × MaxOp)} {a : ℕ} {o : MaxOp}
    {l : Loc n} (h : PInv p sh L a o l) (f : ℕ × MaxOp → Bool)
    (hf : ∀ y ∈ L, f y = false → y.1 ≠ a ∧ maxReg.ReadOnly y.2) :
    PInv p sh (L.filter f) a o l := by
  have hkeep : ∀ y ∈ L, y.1 = a → y ∈ L.filter f := by
    intro y hy hya
    refine List.mem_filter.2 ⟨hy, ?_⟩
    by_contra hc; exact (hf y hy (by simpa using hc)).1 hya
  have hmem : a ∈ (L.filter f).map Prod.fst ↔ a ∈ L.map Prod.fst := by
    constructor
    · intro h'; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h'
      exact List.mem_map.2 ⟨y, List.mem_of_mem_filter hy, rfl⟩
    · intro h'; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h'
      exact List.mem_map.2 ⟨y, hkeep y hy rfl, rfl⟩
  cases o <;> cases l <;> simp only [PInv] at h ⊢ <;> try rw [hmem]
  all_goals first
    | exact h
    | exact ⟨h.1, fun h' => (h.2 h')⟩
    | exact ⟨h.1, hkeep _ h.2 rfl⟩
    | exact Pos.filter h f hf
    | exact ⟨h.1, h.2.1, fun h' => Pos.filter (h.2.2.1 h') f hf, h.2.2.2⟩

lemma PInv.mono {p : Fin n} {sh sh' : Fin n → ℕ} {L : List (ℕ × MaxOp)} {a : ℕ} {o : MaxOp}
    {l : Loc n} (h : PInv p sh L a o l) (hle : ∀ i, sh i ≤ sh' i) (hp : sh' p = sh p) :
    PInv p sh' L a o l := by
  cases o <;> cases l <;> simp only [PInv] at h ⊢
  all_goals first
    | exact h
    | exact ⟨h.1, fun h' => hp ▸ h.2 h'⟩
    | exact ⟨h.1, hp ▸ h.2.1, h.2.2⟩
    | exact ⟨hp ▸ h.1, h.2⟩
    | exact ⟨h.1, fun i hi => (h.2 i hi).trans (hle i)⟩
    | exact ⟨fun i => (h.1 i).trans (hle i), h.2.1, h.2.2.1, fun h1 h2 => by
        obtain ⟨i, hi1, hi2⟩ := h.2.2.2 h1 h2; exact ⟨i, lt_of_lt_of_le hi1 (hle i), hi2⟩⟩

/-! ### The global invariant -/

/-- The invariant maintained along executions of Algorithm 3. -/
structure Inv (C : (alg3 n).Cfg) (h : List (HEv (Fin n) MaxOp ℕ)) (L : List (ℕ × MaxOp)) :
    Prop where
  dlin : DLin maxReg h 0 L
  state : maxReg.runOps 0 (L.map Prod.snd) = smax n C.sh
  nofail : ∀ a c, HEv.res a none c ∉ h
  cnt : ∀ a q o, HEv.inv a q o ∈ h → a < C.cnt
  uniq : ∀ a q o q' o', HEv.inv a q o ∈ h → HEv.inv a q' o' ∈ h → q = q' ∧ o = o'
  resinv : ∀ a r c, HEv.res a r c ∈ h → ∃ q o, HEv.inv a q o ∈ h
  run : ∀ p a o b l, C.ps p = .run a o b l →
    HEv.inv a p o ∈ h ∧ (∀ r c, HEv.res a r c ∉ h) ∧ PInv p C.sh L a o l

lemma Inv.init : Inv (alg3 n).init [] [] where
  dlin := ⟨by simp, by simp, by simp, by simp, by simp, trivial⟩
  state := by simp [RImpl.init, smax_zero]; rfl
  nofail := by simp
  cnt := by simp
  uniq := by simp
  resinv := by simp
  run := by intro p a o b l h; cases h

lemma Inv.ids_ne {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) {p q : Fin n} {a a' : ℕ} {o o' : MaxOp}
    {b b' : Bool} {l l' : Loc n} (hp : C.ps p = .run a o b l) (hq : C.ps q = .run a' o' b' l')
    (hpq : q ≠ p) : a' ≠ a := by
  rintro rfl
  exact hpq ((hI.uniq _ _ _ _ _ (hI.run _ _ _ _ _ hp).1 (hI.run _ _ _ _ _ hq).1).1.symm)

/-- An entry of `L` carries the operation of its identifier. -/
lemma Inv.op_eq {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) {x : ℕ × MaxOp} (hx : x ∈ L) {q : Fin n}
    {o : MaxOp} (hinv : HEv.inv x.1 q o ∈ h) : x.2 = o := by
  obtain ⟨q', hq'⟩ := hI.dlin.inv_of_mem x hx
  exact (hI.uniq _ _ _ _ _ hq' hinv).2

lemma Inv.not_mem_cnt {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) : C.cnt ∉ L.map Prod.fst := by
  intro hm
  obtain ⟨x, hx, hxc⟩ := List.mem_map.1 hm
  obtain ⟨q, hq⟩ := hI.dlin.inv_of_mem x hx
  have := hI.cnt _ _ _ hq; omega

/-- Invocation events. -/
lemma Inv.ev_inv {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) (q : Fin n) (o : MaxOp) :
    ∃ L', Inv ((alg3 n).step1 C (.inv q o)).1 (h ++ ((alg3 n).step1 C (.inv q o)).2) L' := by
  cases hq : C.ps q with
  | run a o' b l => exact ⟨L, by simpa [RImpl.step1, hq] using hI⟩
  | idle =>
    rw [RImpl.step1_inv_idle _ C q o hq]
    have hnc := hI.not_mem_cnt
    refine ⟨L, ⟨?_, hI.state, ?_, ?_, ?_, ?_, ?_⟩⟩
    · exact hI.dlin.append_noRes _ (by simp) (by intro a q' o' ha; simp at ha; rw [ha.1]; exact hnc)
    · simpa using hI.nofail
    · intro a q' o' ha
      rcases List.mem_append.1 ha with ha | ha
      · have := hI.cnt _ _ _ ha; simp; omega
      · simp at ha; simp [ha.1]
    · intro a q₁ o₁ q₂ o₂ h1 h2
      rcases List.mem_append.1 h1 with h1 | h1 <;> rcases List.mem_append.1 h2 with h2 | h2
      · exact hI.uniq _ _ _ _ _ h1 h2
      · simp at h2; obtain ⟨rfl, -, -⟩ := h2; have := hI.cnt _ _ _ h1; omega
      · simp at h1; obtain ⟨rfl, -, -⟩ := h1; have := hI.cnt _ _ _ h2; omega
      · simp at h1 h2; exact ⟨h1.2.1.trans h2.2.1.symm, h1.2.2.trans h2.2.2.symm⟩
    · intro a r c ha
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨q', o', h'⟩ := hI.resinv a r c ha; exact ⟨q', o', List.mem_append_left _ h'⟩
      · simp at ha
    · intro p a o' b l hp
      by_cases hpq : p = q
      · subst hpq
        simp only [Function.update_self, PSt.run.injEq] at hp
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
        refine ⟨by simp, ?_, ?_⟩
        · intro r c hr
          rcases List.mem_append.1 hr with hr | hr
          · obtain ⟨q', o', h'⟩ := hI.resinv _ r c hr; have := hI.cnt _ _ _ h'; omega
          · simp at hr
        · cases o with
          | writeMax v => exact ⟨rfl, fun hm => absurd hm hnc⟩
          | read =>
            exact ⟨fun i => Nat.zero_le _, fun _ => hnc, fun hm => absurd hm hnc,
              fun _ h0 => absurd h0 (lt_irrefl 0)⟩
      · simp only [Function.update_of_ne hpq] at hp
        obtain ⟨h1, h2, h3⟩ := hI.run _ _ _ _ _ hp
        refine ⟨List.mem_append_left _ h1, ?_, h3⟩
        intro r c hr
        rcases List.mem_append.1 hr with hr | hr
        · exact h2 r c hr
        · simp at hr

open Classical in
/-- Entries kept at a crash: writes, and operations that already returned. -/
noncomputable def keep (h : List (HEv (Fin n) MaxOp ℕ)) (x : ℕ × MaxOp) : Bool :=
  decide (x.2 ≠ .read ∨ ∃ r c, HEv.res x.1 r c ∈ h)

/-- Crash events: pending reads are removed from the linearization. -/
lemma Inv.ev_crash {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) :
    ∃ L', Inv ((alg3 n).step1 C .crash).1 (h ++ ((alg3 n).step1 C .crash).2) L' := by
  have hs : (alg3 n).step1 C .crash =
      (⟨C.sh, C.pv, fun p => (alg3 n).crashPS p (C.ps p), C.cnt⟩, [.crash]) := rfl
  rw [hs]
  have hf : ∀ x ∈ L, keep h x = false → maxReg.ReadOnly x.2 ∧ ∀ r c, HEv.res x.1 r c ∉ h ++ [.crash] := by
    intro x _ hk
    simp only [keep, decide_eq_false_iff_not, not_or, not_not, not_exists] at hk
    refine ⟨hk.1 ▸ maxReg_read_ro, fun r c hr => ?_⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact hk.2 r c hr
    · simp at hr
  refine ⟨L.filter (keep h), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (hI.dlin.append_noRes [.crash] (by simp) (by simp)).filter_ro _ hf
  · show maxReg.runOps 0 ((L.filter (keep h)).map Prod.snd) = smax n C.sh
    rw [maxReg.runOps_map_filter 0 L Prod.snd (keep h) (fun x hx hk => (hf x hx hk).1)]
    exact hI.state
  · intro a c ha; rcases List.mem_append.1 ha with ha | ha
    · exact hI.nofail a c ha
    · simp at ha
  · intro a q o ha; rcases List.mem_append.1 ha with ha | ha
    · exact hI.cnt a q o ha
    · simp at ha
  · intro a q o q' o' h1 h2
    rcases List.mem_append.1 h1 with h1 | h1
    · rcases List.mem_append.1 h2 with h2 | h2
      · exact hI.uniq _ _ _ _ _ h1 h2
      · simp at h2
    · simp at h1
  · intro a r c ha; rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨q, o, h'⟩ := hI.resinv a r c ha; exact ⟨q, o, List.mem_append_left _ h'⟩
    · simp at ha
  · intro p a o b l hp
    change (alg3 n).crashPS p (C.ps p) = _ at hp
    show HEv.inv a p o ∈ h ++ [.crash] ∧ (∀ r c, HEv.res a r c ∉ h ++ [.crash]) ∧
      PInv p C.sh (L.filter (keep h)) a o l
    cases hc : C.ps p with
    | idle => rw [hc] at hp; cases hp
    | run a0 o0 b0 l0 =>
      rw [hc] at hp
      simp only [RImpl.crashPS, PSt.run.injEq] at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      obtain ⟨h1, h2, h3⟩ := hI.run _ _ _ _ _ hc
      refine ⟨List.mem_append_left _ h1, fun r c hr => ?_, ?_⟩
      · rcases List.mem_append.1 hr with hr | hr
        · exact h2 r c hr
        · simp at hr
      · have hmemL : a0 ∈ (L.filter (keep h)).map Prod.fst → a0 ∈ L.map Prod.fst := by
          intro hm; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
          exact List.mem_map.2 ⟨y, List.mem_of_mem_filter hy, rfl⟩
        cases o0 with
        | writeMax v =>
          refine ⟨rfl, fun hm => ?_⟩
          have hm' := hmemL hm
          cases l0 <;> simp only [PInv] at h3
          · exact h3.2 hm'
          · exact absurd hm' h3.2.2
          · exact h3.1
        | read =>
          refine ⟨fun i => Nat.zero_le _, fun _ => ?_, fun hm => ?_, fun _ h0 => absurd h0 (lt_irrefl 0)⟩
          all_goals
            first
            | (intro hm)
            | skip
          all_goals
            exfalso
            obtain ⟨y, hy, hya⟩ := List.mem_map.1 hm
            have hyL := List.mem_of_mem_filter hy
            have hop : y.2 = .read := hI.op_eq hyL (hya ▸ h1)
            have := (List.mem_filter.1 hy).2
            simp only [keep, decide_eq_true_eq, ne_eq] at this
            rcases this with h' | ⟨r, c, hr⟩
            · exact h' hop
            · exact h2 r c (hya ▸ hr)

/-! ### Steps of a process -/

lemma step_sh {C : (alg3 n).Cfg} {p : Fin n} {a : ℕ} {o : MaxOp} {b : Bool} {l : Loc n}
    (hc : C.ps p = .run a o b l) (f : (Fin n → ℕ) → Loc n × (Fin n → ℕ))
    (hact : Alg3.act p l = .sh f) :
    (alg3 n).step1 C (.step p) =
      (⟨(f C.sh).2, C.pv, Function.update C.ps p (.run a o b (f C.sh).1), C.cnt⟩, []) := by
  simp [RImpl.step1, hc, hact]

lemma step_pv {C : (alg3 n).Cfg} {p : Fin n} {a : ℕ} {o : MaxOp} {b : Bool} {l : Loc n}
    (hc : C.ps p = .run a o b l) (f : Option ℕ → Loc n × Option ℕ)
    (hact : Alg3.act p l = .pv f) :
    (alg3 n).step1 C (.step p) =
      (⟨C.sh, Function.update C.pv p (f (C.pv p)).2,
        Function.update C.ps p (.run a o b (f (C.pv p)).1), C.cnt⟩, []) := by
  simp [RImpl.step1, hc, hact]

lemma step_ret {C : (alg3 n).Cfg} {p : Fin n} {a : ℕ} {o : MaxOp} {b : Bool} {l : Loc n}
    (hc : C.ps p = .run a o b l) (r : Option ℕ) (hact : Alg3.act p l = .ret r) :
    (alg3 n).step1 C (.step p) =
      (⟨C.sh, C.pv, Function.update C.ps p .idle, C.cnt⟩, [.res a r b]) := by
  simp [RImpl.step1, hc, hact]

/-- A memory step of `p` preserves the invariant if the new linearization and states are fine. -/
lemma Inv.of_step {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) {p : Fin n} {a : ℕ} {o : MaxOp}
    {b : Bool} {l : Loc n} (hc : C.ps p = .run a o b l) (sh' : Fin n → ℕ) (pv' : Fin n → Option ℕ)
    (l' : Loc n) (L' : List (ℕ × MaxOp)) (hd : DLin maxReg h 0 L')
    (hst : maxReg.runOps 0 (L'.map Prod.snd) = smax n sh') (hp' : PInv p sh' L' a o l')
    (hoth : ∀ q a' o' b' l'', q ≠ p → C.ps q = .run a' o' b' l'' → a' ≠ a →
      PInv q C.sh L a' o' l'' → PInv q sh' L' a' o' l'') :
    Inv (⟨sh', pv', Function.update C.ps p (.run a o b l'), C.cnt⟩ : (alg3 n).Cfg) (h ++ []) L' := by
  rw [List.append_nil]
  refine ⟨hd, hst, hI.nofail, hI.cnt, hI.uniq, hI.resinv, ?_⟩
  intro q a' o' b' l'' hq
  by_cases hqp : q = p
  · subst hqp
    simp only [Function.update_self, PSt.run.injEq] at hq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
    obtain ⟨h1, h2, -⟩ := hI.run _ _ _ _ _ hc
    exact ⟨h1, h2, hp'⟩
  · simp only [Function.update_of_ne hqp] at hq
    obtain ⟨h1, h2, h3⟩ := hI.run _ _ _ _ _ hq
    exact ⟨h1, h2, hoth q a' o' b' l'' hqp hq (hI.ids_ne hc hq hqp) h3⟩

/-- A return step of `p` preserves the invariant if the linearization accepts the response. -/
lemma Inv.of_ret {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) {p : Fin n} {a : ℕ} {o : MaxOp}
    {b : Bool} {l : Loc n} (hc : C.ps p = .run a o b l) (r : ℕ)
    (hd : DLin maxReg (h ++ [.res a (some r) b]) 0 L) :
    Inv (⟨C.sh, C.pv, Function.update C.ps p .idle, C.cnt⟩ : (alg3 n).Cfg)
      (h ++ [.res a (some r) b]) L := by
  obtain ⟨h1, h2, -⟩ := hI.run _ _ _ _ _ hc
  refine ⟨hd, hI.state, ?_, ?_, ?_, ?_, ?_⟩
  · intro a' c ha; rcases List.mem_append.1 ha with ha | ha
    · exact hI.nofail a' c ha
    · simp at ha
  · intro a' q o' ha; rcases List.mem_append.1 ha with ha | ha
    · exact hI.cnt a' q o' ha
    · simp at ha
  · intro a' q o' q' o'' g1 g2
    rcases List.mem_append.1 g1 with g1 | g1
    · rcases List.mem_append.1 g2 with g2 | g2
      · exact hI.uniq _ _ _ _ _ g1 g2
      · simp at g2
    · simp at g1
  · intro a' r' c ha; rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨q, o', h'⟩ := hI.resinv a' r' c ha; exact ⟨q, o', List.mem_append_left _ h'⟩
    · simp at ha; obtain ⟨rfl, -⟩ := ha; exact ⟨p, o, List.mem_append_left _ h1⟩
  · intro q a' o' b' l'' hq
    by_cases hqp : q = p
    · subst hqp; simp at hq
    · simp only [Function.update_of_ne hqp] at hq
      obtain ⟨g1, g2, g3⟩ := hI.run _ _ _ _ _ hq
      refine ⟨List.mem_append_left _ g1, fun r' c hr => ?_, g3⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact g2 r' c hr
      · simp at hr; exact hI.ids_ne hc hq hqp hr.1

/-- Step events. -/
lemma Inv.ev_step {C : (alg3 n).Cfg} {h L} (hI : Inv C h L) (p : Fin n) :
    ∃ L', Inv ((alg3 n).step1 C (.step p)).1 (h ++ ((alg3 n).step1 C (.step p)).2) L' := by
  cases hc : C.ps p with
  | idle => exact ⟨L, by simpa [RImpl.step1, hc] using hI⟩
  | run a o b l =>
    obtain ⟨hinv, hnores, hpi⟩ := hI.run _ _ _ _ _ hc
    have hnL : ∀ (x : ℕ × MaxOp), x.1 = a → x ∈ L → x.2 = o := fun x hx hm =>
      hI.op_eq hm (hx ▸ hinv)
    cases o with
    | writeMax v =>
      cases l with
      | wmRead v' =>
        obtain ⟨rfl, hle⟩ := hpi
        rw [step_sh hc _ rfl]
        by_cases hlt : C.sh p < v'
        · refine ⟨L, hI.of_step hc _ _ _ L hI.dlin hI.state ?_ (fun _ _ _ _ _ _ _ _ h => h)⟩
          simp only [hlt, ↓reduceIte]
          exact ⟨rfl, hlt, fun hm => absurd (hle hm) (not_le.2 hlt)⟩
        · simp only [hlt, ↓reduceIte]
          by_cases hmem : a ∈ L.map Prod.fst
          · refine ⟨L, hI.of_step hc _ _ _ L hI.dlin hI.state ?_ (fun _ _ _ _ _ _ _ _ h => h)⟩
            obtain ⟨x, hx, hxa⟩ := List.mem_map.1 hmem
            have := hnL x hxa hx
            exact ⟨not_lt.1 hlt, by rw [show (a, MaxOp.writeMax v') = x from Prod.ext hxa.symm this.symm]; exact hx⟩
          · refine ⟨L ++ [(a, .writeMax v')], hI.of_step hc _ _ _ _
              (hI.dlin.push a p _ hinv hnores hmem) ?_ ?_ ?_⟩
            · rw [List.map_append, ObjSpec.runOps_append, hI.state]
              exact max_eq_left ((not_lt.1 hlt).trans (le_smax _ p))
            · exact ⟨not_lt.1 hlt, by simp⟩
            · intro q a' o' b' l'' _ _ hne h'
              exact h'.push _ (Ne.symm hne)
      | wmWrite v' =>
        obtain ⟨rfl, hlt, hmem⟩ := hpi
        rw [step_sh hc _ rfl]
        refine ⟨L ++ [(a, .writeMax v')], hI.of_step hc _ _ _ _
          (hI.dlin.push a p _ hinv hnores hmem) ?_ ?_ ?_⟩
        · rw [List.map_append, ObjSpec.runOps_append, hI.state]
          exact (smax_update _ _ _ hlt.le).symm
        · exact ⟨by simp, by simp⟩
        · intro q a' o' b' l'' hqp _ hne h'
          refine (h'.mono ?_ ?_).push _ (Ne.symm hne)
          · intro i
            by_cases hi : i = p
            · subst hi; simp [hlt.le]
            · simp [Function.update_of_ne hi]
          · simp [Function.update_of_ne hqp]
      | wmRet =>
        obtain ⟨-, hmem⟩ := hpi
        rw [step_ret hc _ rfl]
        refine ⟨L, hI.of_ret hc 0 (hI.dlin.append_res a (some 0) b ?_ ?_)⟩
        · exact ⟨fun _ => rfl, fun _ => List.mem_map.2 ⟨_, hmem, rfl⟩⟩
        · intro r' hr L₁ o' L₂ hL
          cases hr
          have : o' = .writeMax v := hnL (a, o') rfl (by rw [hL]; simp)
          subst this; rfl
      | cmp x y k => simp [PInv] at hpi
      | asg x k => simp [PInv] at hpi
      | persist r => simp [PInv] at hpi
      | rret r => simp [PInv] at hpi
    | read =>
      cases l with
      | wmRead v => simp [PInv] at hpi
      | wmWrite v => simp [PInv] at hpi
      | wmRet => simp [PInv] at hpi
      | cmp x y k =>
        obtain ⟨hxle, hk0, hpos, hwit⟩ := hpi
        by_cases hk : k < n
        · rw [step_sh hc _ (by simp [Alg3.act, hk]; rfl)]
          simp only
          set y' := Function.update y ⟨k, hk⟩ (C.sh ⟨k, hk⟩) with hy'
          by_cases hpush : k = 0 ∧ C.sh = x
          · obtain ⟨rfl, hsx⟩ := hpush
            have hmem := hk0 rfl
            refine ⟨L ++ [(a, .read)], hI.of_step hc _ _ _ _
              (hI.dlin.push a p _ hinv hnores hmem) ?_ ?_ ?_⟩
            · rw [List.map_append, ObjSpec.runOps_append, hI.state]; rfl
            · refine ⟨hxle, fun h0 => absurd h0 (Nat.succ_ne_zero 0), fun _ => ?_, fun hn => ?_⟩
              · exact ⟨L, [], by simp, by rw [hI.state, hsx]⟩
              · exact absurd (by simp) hn
            · intro q a' o' b' l'' _ _ hne h'
              exact h'.push _ (Ne.symm hne)
          · refine ⟨L, hI.of_step hc _ _ _ L hI.dlin hI.state ?_ (fun _ _ _ _ _ _ _ _ h => h)⟩
            refine ⟨hxle, fun h0 => absurd h0 (Nat.succ_ne_zero k), hpos, fun hn _ => ?_⟩
            have hyk : ∀ i : Fin n, i.val = k → y' i = C.sh i := by
              intro i hi
              rw [hy', show i = ⟨k, hk⟩ from Fin.ext hi]; simp
            have hyo : ∀ i : Fin n, i.val ≠ k → y' i = y i := by
              intro i hi
              rw [hy', Function.update_of_ne (fun e => hi (by rw [e]))]
            rcases Nat.eq_zero_or_pos k with rfl | hkpos
            · have hne : C.sh ≠ x := fun e => hpush ⟨rfl, e⟩
              obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
              have hlt : x i < C.sh i := lt_of_le_of_ne (hxle i) (Ne.symm hi)
              refine ⟨i, hlt, fun hi1 => ?_⟩
              rw [hyk i (by omega)]; exact hlt
            · obtain ⟨i, hlt, hiy⟩ := hwit hn hkpos
              refine ⟨i, hlt, fun hi1 => ?_⟩
              by_cases hik : i.val = k
              · rw [hyk i hik]; exact hlt
              · rw [hyo i hik]; exact hiy (by omega)
        · have hnpos : 0 < k := lt_of_lt_of_le (Fin.pos p) (not_lt.1 hk)
          rw [step_sh hc _ (by simp [Alg3.act, hk]; rfl)]
          simp only
          by_cases hyx : y = x
          · simp only [hyx, ite_true]
            have hmem : a ∈ L.map Prod.fst := by
              by_contra hn
              obtain ⟨i, hlt, hiy⟩ := hwit hn hnpos
              have := hiy (lt_of_lt_of_le i.isLt (not_lt.1 hk))
              rw [hyx] at this; exact lt_irrefl _ this
            exact ⟨L, hI.of_step hc _ _ _ L hI.dlin hI.state (hpos hmem)
              (fun _ _ _ _ _ _ _ _ h => h)⟩
          · simp only [hyx, ite_false]
            have hf : ∀ z ∈ L, decide (z.1 ≠ a) = false →
                maxReg.ReadOnly z.2 ∧ ∀ r c, HEv.res z.1 r c ∉ h := by
              intro z hz hza
              simp only [decide_eq_false_iff_not, not_not] at hza
              refine ⟨by rw [hnL z hza hz]; exact maxReg_read_ro, fun r c hr => ?_⟩
              exact hnores r c (hza ▸ hr)
            refine ⟨L.filter (fun z => decide (z.1 ≠ a)), hI.of_step hc _ _ _ _
              (hI.dlin.filter_ro _ hf) ?_ ?_ ?_⟩
            · rw [maxReg.runOps_map_filter 0 L Prod.snd _ (fun z hz hk' => (hf z hz hk').1)]
              exact hI.state
            · refine ⟨fun hm => ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
              obtain ⟨z, hz, hza⟩ := List.mem_map.1 hm
              have := (List.mem_filter.1 hz).2
              simp [hza] at this
            · intro q a' o' b' l'' _ _ hne h'
              refine h'.filter _ (fun z hz hza => ⟨?_, (hf z hz hza).1⟩)
              simp only [decide_eq_false_iff_not, not_not] at hza
              rw [hza]; exact Ne.symm hne
      | asg x k =>
        obtain ⟨hmem, hxle⟩ := hpi
        by_cases hk : k < n
        · rw [step_sh hc _ (by simp [Alg3.act, hk]; rfl)]
          refine ⟨L, hI.of_step hc _ _ _ L hI.dlin hI.state ⟨hmem, fun i hi => ?_⟩
            (fun _ _ _ _ _ _ _ _ h => h)⟩
          by_cases hik : i = ⟨k, hk⟩
          · subst hik; simp
          · rw [Function.update_of_ne hik]
            exact hxle i (by
              have : i.val ≠ k := fun e => hik (Fin.ext e)
              omega)
        · rw [step_sh hc _ (by simp [Alg3.act, hk]; rfl)]
          refine ⟨L, hI.of_step hc _ _ _ L hI.dlin hI.state ⟨fun i => hxle i
            (lt_of_lt_of_le i.isLt (not_lt.1 hk)), fun _ => hmem, fun hm => absurd hm hmem,
            fun _ h0 => absurd h0 (lt_irrefl 0)⟩ (fun _ _ _ _ _ _ _ _ h => h)⟩
      | persist r =>
        rw [step_pv hc _ rfl]
        exact ⟨L, hI.of_step hc _ _ _ L hI.dlin hI.state hpi (fun _ _ _ _ _ _ _ _ h => h)⟩
      | rret r =>
        rw [step_ret hc _ rfl]
        refine ⟨L, hI.of_ret hc r (hI.dlin.append_res a (some r) b ?_ ?_)⟩
        · exact ⟨fun _ => rfl, fun _ => List.mem_map.2 ⟨_, hpi.mem, rfl⟩⟩
        · intro r' hr L₁ o' L₂ hL
          cases hr
          obtain ⟨M₁, M₂, hM, hMr⟩ := hpi
          obtain ⟨rfl, rfl⟩ := decomp_unique hI.dlin.nodup hL hM
          exact hMr.symm

end Alg3

/-! ### Obstruction-freedom -/

section OF

variable {O : ObjSpec} {P : Type} [DecidableEq P]

/-- A measure on (local state, shared memory) that decreases at every step of a process, when
the shared memory is only modified by that process, gives obstruction-freedom. -/
theorem _root_.Papers.PODC2020.DetectableSpace.RImpl.obstructionFree_of_soloMeasure
    (A : RImpl O P) (μ : A.L → A.Sh → ℕ)
    (hμ : ∀ p l, match A.act p l with
      | .sh f => ∀ s, μ (f s).1 (f s).2 < μ l s
      | .pv f => ∀ v s, μ (f v).1 s < μ l s
      | .ret _ => True) : A.ObstructionFree := by
  have key : ∀ m (C : A.Cfg) (p : P) a o b l, C.ps p = .run a o b l → μ l C.sh < m →
      (A.exec C (RImpl.solo p m)).1.ps p = .idle := by
    intro m
    induction m with
    | zero => intro C p a o b l _ h; omega
    | succ m ih =>
      intro C p a o b l h1 h2
      rw [RImpl.solo_succ, RImpl.exec_cons]
      have hμp := hμ p l
      simp only [RImpl.step1, h1]
      cases hact : A.act p l with
      | sh f =>
        rw [hact] at hμp
        exact ih _ p a o b (f C.sh).1 (by simp)
          (by have h3 : μ (f C.sh).1 (f C.sh).2 < μ l C.sh := hμp C.sh; simp; omega)
      | pv f =>
        rw [hact] at hμp
        exact ih _ p a o b (f (C.pv p)).1 (by simp)
          (by have h3 : μ (f (C.pv p)).1 C.sh < μ l C.sh := hμp (C.pv p) C.sh; simp; omega)
      | ret r =>
        simp only
        rw [RImpl.exec_solo_idle _ _ _ (by simp)]
        simp
  intro C _ p
  cases hc : C.ps p with
  | idle => exact ⟨0, by simpa using hc⟩
  | run a o b l => exact ⟨μ l C.sh + 1, key _ C p a o b l hc (by omega)⟩

end OF

namespace Alg3

variable {n : ℕ}

/-- In a solo run, the current comparison collect will succeed. -/
def cond (x y : Fin n → ℕ) (k : ℕ) (s : Fin n → ℕ) : Prop :=
  (∀ i : Fin n, i.val < k → y i = x i) ∧ (∀ i : Fin n, k ≤ i.val → s i = x i)

open Classical in
/-- Solo-run measure. -/
noncomputable def μ : Loc n → (Fin n → ℕ) → ℕ
  | .wmRead _, _ => 3
  | .wmWrite _, _ => 2
  | .wmRet, _ => 1
  | .cmp x y k, s => (n - k) + (if cond x y k s then 3 else 2 * n + 8)
  | .asg x k, s => (n - k) + 1 + n + (if ∀ i : Fin n, i.val < k → s i = x i then 3 else 2 * n + 8)
  | .persist _, _ => 2
  | .rret _, _ => 1

lemma cond_step (x y s : Fin n → ℕ) (k : ℕ) (hk : k < n) :
    cond x (Function.update y ⟨k, hk⟩ (s ⟨k, hk⟩)) (k + 1) s ↔ cond x y k s := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have := h1 i (by omega)
      rwa [Function.update_of_ne (fun e => by rw [e] at hi; simp at hi)] at this
    · by_cases hik : i.val = k
      · have := h1 i (by omega)
        rw [show i = ⟨k, hk⟩ from Fin.ext hik] at this ⊢
        simpa using this
      · exact h2 i (by omega)
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => h2 i (by omega)⟩
    by_cases hik : i.val = k
    · rw [show i = ⟨k, hk⟩ from Fin.ext hik]; simp; exact h2 ⟨k, hk⟩ le_rfl
    · rw [Function.update_of_ne (fun e => hik (by rw [e]))]; exact h1 i (by omega)

lemma asg_step (x s : Fin n → ℕ) (k : ℕ) (hk : k < n) :
    (∀ i : Fin n, i.val < k + 1 → s i = Function.update x ⟨k, hk⟩ (s ⟨k, hk⟩) i) ↔
      (∀ i : Fin n, i.val < k → s i = x i) := by
  constructor
  · intro h i hi
    have := h i (by omega)
    rwa [Function.update_of_ne (fun e => by rw [e] at hi; simp at hi)] at this
  · intro h i hi
    by_cases hik : i.val = k
    · rw [show i = ⟨k, hk⟩ from Fin.ext hik]; simp
    · rw [Function.update_of_ne (fun e => hik (by rw [e]))]; exact h i (by omega)

end Alg3

open Alg3 in
/-- **Algorithm 3 is obstruction-free.** -/
theorem alg3_obstructionFree (n : ℕ) : (alg3 n).ObstructionFree := by
  refine (alg3 n).obstructionFree_of_soloMeasure Alg3.μ ?_
  intro p l
  cases l with
  | wmRead v => intro s; show Alg3.μ (if s p < v then _ else _) s < 3; split_ifs <;> simp [Alg3.μ]
  | wmWrite v => intro s; simp [Alg3.act, Alg3.μ]
  | wmRet => trivial
  | cmp x y k =>
    by_cases hk : k < n
    · rw [show (alg3 n).act p (.cmp x y k) = Act.sh (fun s =>
          (Alg3.Loc.cmp x (Function.update y ⟨k, hk⟩ (s ⟨k, hk⟩)) (k + 1), s)) by
        simp [Alg3.act, hk]]
      show ∀ s, Alg3.μ (Alg3.Loc.cmp x (Function.update y ⟨k, hk⟩ (s ⟨k, hk⟩)) (k + 1)) s <
        Alg3.μ (Alg3.Loc.cmp x y k) s
      intro s
      simp only [Alg3.μ, Alg3.cond_step x y s k hk]
      have : n - (k + 1) < n - k := by omega
      split_ifs with h1 h2 h2
      · omega
      · exact absurd ((Alg3.cond_step x y s k hk).1 h1) h2
      · exact absurd ((Alg3.cond_step x y s k hk).2 h2) h1
      · omega
    · rw [show (alg3 n).act p (.cmp x y k) = Act.sh (fun s =>
          (if y = x then Alg3.Loc.persist (Alg3.smax n x) else Alg3.Loc.asg x 0, s)) by
        simp [Alg3.act, hk]]
      show ∀ s, Alg3.μ (if y = x then Alg3.Loc.persist (Alg3.smax n x) else Alg3.Loc.asg x 0) s <
        Alg3.μ (Alg3.Loc.cmp x y k) s
      intro s
      have hc : Alg3.cond x y k s ↔ y = x := by
        constructor
        · rintro ⟨h1, -⟩; funext i; exact h1 i (by omega)
        · rintro rfl; exact ⟨fun _ _ => rfl, fun i hi => absurd hi (by omega)⟩
      have h0 : ∀ i : Fin n, i.val < 0 → s i = x i := fun i hi => absurd hi (Nat.not_lt_zero _)
      by_cases hyx : y = x
      · rw [if_pos hyx]
        simp only [Alg3.μ, if_pos (hc.2 hyx)]
        omega
      · rw [if_neg hyx]
        simp only [Alg3.μ, if_neg (fun h => hyx (hc.1 h)), if_pos h0]
        omega
  | asg x k =>
    by_cases hk : k < n
    · rw [show (alg3 n).act p (.asg x k) = Act.sh (fun s =>
          (Alg3.Loc.asg (Function.update x ⟨k, hk⟩ (s ⟨k, hk⟩)) (k + 1), s)) by
        simp [Alg3.act, hk]]
      show ∀ s, Alg3.μ (Alg3.Loc.asg (Function.update x ⟨k, hk⟩ (s ⟨k, hk⟩)) (k + 1)) s <
        Alg3.μ (Alg3.Loc.asg x k) s
      intro s
      simp only [Alg3.μ, Alg3.asg_step x s k hk]
      have : n - (k + 1) < n - k := by omega
      split_ifs <;> omega
    · rw [show (alg3 n).act p (.asg x k) = Act.sh (fun s => (Alg3.Loc.cmp x 0 0, s)) by
        simp [Alg3.act, hk]]
      show ∀ s, Alg3.μ (Alg3.Loc.cmp x 0 0) s < Alg3.μ (Alg3.Loc.asg x k) s
      intro s
      have hc : Alg3.cond x 0 0 s ↔ ∀ i : Fin n, i.val < k → s i = x i := by
        constructor
        · rintro ⟨-, h2⟩ i _; exact h2 i (Nat.zero_le _)
        · intro h; exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _),
            fun i _ => h i (lt_of_lt_of_le i.isLt (not_lt.1 hk))⟩
      simp only [Alg3.μ, hc]
      split_ifs <;> omega
  | persist r => intro v s; simp [Alg3.act, Alg3.μ]
  | rret r => trivial

open Alg3 in
/-- **Algorithm 3 is durably linearizable and detectable** (with no auxiliary state). -/
theorem alg3_durLinDet (n : ℕ) : (alg3 n).DurLinDet := by
  refine (alg3 n).durLinDet_of_inv Inv Inv.init ?_ (fun _ _ _ hI => hI.dlin)
    (fun _ _ _ hI a => hI.nofail a false)
  intro C h L e _ hI
  cases e with
  | inv q o => exact hI.ev_inv q o
  | step p => exact hI.ev_step p
  | crash => exact hI.ev_crash

end Papers.PODC2020.DetectableSpace
