import Papers.PODC2017.RegisterEmulationSpace.Algorithm2WaitFree

/-!
# Algorithm 2 is safe in sequential runs (Lemmas 6–8, Corollary 4, restricted to sequential runs)

Hypotheses on the write sets `R` (`Layout`): clients outside `Wr` have no registers; the registers of
every write set are on distinct servers; and the paper's capacity condition: if `R c` meets the
write sets of `m` other writers, then `m f + 2f + 1 ≤ |R c|` (for the paper's partition into sets
`R_j` shared by `w_j` writers this says `w_j ≤ ⌊(|R_j| - (f+1))/f⌋`).

The invariant `SInv` of sequential runs, with `T` = number of completed writes and `u` = the value
of the last one:
* every timestamped value in the system (registers, pending writes, `tsVal`s, maxima of collects)
  has timestamp `< T`, or is `(T, u)`, or is `(T + 1, v)` of the write `v` in its writing phase;
* (`quorum`, Lemma 7) if `T > 0`, there is a set `Q` of registers on `≥ f + 1` servers that are
  *protected* at level `T`: their value and every pending or queued write on them has timestamp
  `≥ T`; a collect that has heard from a register of `Q` has a maximum `≥ T`;
* (`count`, Observation 3 and Lemma 6) during the writing phase of `c` with `(T + 1, v)`:
  `|Sp| + Σ_{d ∈ Nb c} |U d| ≤ |Nb c| f`, where `U d` = registers covered or queued by `d` and `Sp` =
  registers of `wrSet` that were overwritten by an older write and are no longer covered.

When the write completes, `wrSet` has `≥ |R c| - f` registers, so at least
`|R c| - f - |Nb c| f ≥ f + 1` of them hold `(T + 1, v)` and are protected: the new `Q`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

variable {C B S V : Type*} [DecidableEq C] [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

/-! ### Sequential histories -/

/-- The pending invocation, as a history suffix. -/
def aPart : Option (C × HOp V) → List (HEv C V)
  | none => []
  | some (c, o) => [.inv c o]

/-- The pending high-level operations described by `a`. -/
def curOf (a : Option (C × HOp V)) (d : C) : Option (HOp V) :=
  match a with
  | some (c, o) => if d = c then some o else none
  | none => none

/-- The operation is a write. -/
def isW {V : Type*} : HOp V → Bool
  | .write _ => true
  | .read => false

/-- Number of writes in a sequential history. -/
def wcount (L : List (C × HOp V × V)) : ℕ := L.countP fun e => isW e.2.1

/-- Every read of a sequential history returns the value of the last preceding write. -/
def SeqCorrect (v₀ : V) (L : List (C × HOp V × V)) : Prop :=
  ∀ L₁ c x L₂, L = L₁ ++ (c, HOp.read, x) :: L₂ → x = lastVal v₀ L₁

/-- The history is (a prefix of) a sequential history. -/
def SeqShape (h : List (HEv C V)) : Prop := ∃ L a, h = seqHist L ++ aPart a

/-- All writes are invoked by `Wr`. -/
def WrOK (Wr : Finset C) (h : List (HEv C V)) : Prop := ∀ c v, HEv.inv c (.write v) ∈ h → c ∈ Wr

lemma seqHist_append (L L' : List (C × HOp V × V)) :
    seqHist (L ++ L') = seqHist L ++ seqHist L' := by
  simp [seqHist, List.flatMap_append]

lemma seqHist_snoc (L : List (C × HOp V × V)) (e : C × HOp V × V) :
    seqHist (L ++ [e]) = seqHist L ++ [.inv e.1 e.2.1, .ret e.1 e.2.2] := by
  simp [seqHist]

lemma length_seqHist (L : List (C × HOp V × V)) : (seqHist L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons e L ih => simp [seqHist] at ih ⊢; omega

lemma seqHist_inj : ∀ {L L' : List (C × HOp V × V)}, seqHist L = seqHist L' → L = L'
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp [seqHist] at h
  | _ :: _, [] => fun h => by simp [seqHist] at h
  | e :: L, e' :: L' => fun h => by
    simp only [seqHist, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
      HEv.inv.injEq, HEv.ret.injEq] at h
    obtain ⟨⟨h1, h2⟩, ⟨-, h3⟩, h4⟩ := h
    rw [seqHist_inj h4]
    obtain ⟨c, o, x⟩ := e; obtain ⟨c', o', x'⟩ := e'
    simp_all

lemma seqShape_eq {L L' : List (C × HOp V × V)} {a a' : Option (C × HOp V)}
    (h : seqHist L ++ aPart a = seqHist L' ++ aPart a') : L = L' ∧ a = a' := by
  have hl := congrArg List.length h
  simp only [List.length_append, length_seqHist] at hl
  rcases a with _ | ⟨c, o⟩ <;> rcases a' with _ | ⟨c', o'⟩ <;> simp [aPart] at h hl
  · exact ⟨seqHist_inj h, rfl⟩
  · omega
  · omega
  · obtain ⟨h1, h2, h3⟩ := h; exact ⟨seqHist_inj h1, by rw [h2, h3]⟩

lemma seqShape_of_snoc {h : List (HEv C V)} {e : HEv C V} (hs : SeqShape (h ++ [e])) :
    SeqShape h := by
  obtain ⟨L, a, hL⟩ := hs
  rcases a with _ | ⟨c, o⟩
  · rcases L.eq_nil_or_concat with rfl | ⟨L₀, e₀, rfl⟩
    · simp [seqHist, aPart] at hL
    · rw [List.concat_eq_append, seqHist_snoc, aPart, List.append_nil] at hL
      rw [show seqHist L₀ ++ [HEv.inv e₀.1 e₀.2.1, HEv.ret e₀.1 e₀.2.2] =
        (seqHist L₀ ++ [HEv.inv e₀.1 e₀.2.1]) ++ [HEv.ret e₀.1 e₀.2.2] by simp] at hL
      have := List.append_inj_left' hL rfl
      exact ⟨L₀, some (e₀.1, e₀.2.1), by rw [this]; rfl⟩
  · simp only [aPart] at hL
    exact ⟨L, none, by rw [List.append_inj_left' hL rfl]; simp [aPart]⟩

lemma wcount_snoc (L : List (C × HOp V × V)) (e : C × HOp V × V) :
    wcount (L ++ [e]) = wcount L + if isW e.2.1 then 1 else 0 := by
  simp [wcount, List.countP_append]

lemma lastVal_snoc (v₀ : V) (L : List (C × HOp V × V)) (e : C × HOp V × V) :
    lastVal v₀ (L ++ [e]) = match e.2.1 with | .write v => v | .read => lastVal v₀ L := by
  obtain ⟨c, o, x⟩ := e
  rcases o <;> simp [lastVal, List.foldl_append]

lemma lastVal_of_wcount_zero (v₀ : V) : ∀ L : List (C × HOp V × V), wcount L = 0 → lastVal v₀ L = v₀ := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro; rfl
  | append_singleton L e ih =>
    intro h
    rw [wcount_snoc] at h
    rw [lastVal_snoc]
    obtain ⟨c, o, x⟩ := e
    rcases o with _ | v
    · exact ih (by simp [isW] at h; exact h)
    · simp [isW] at h

lemma seqCorrect_snoc_write (v₀ : V) {L : List (C × HOp V × V)} (h : SeqCorrect v₀ L) (c : C) (v x : V) :
    SeqCorrect v₀ (L ++ [(c, .write v, x)]) := by
  intro L₁ d y L₂ hL
  rcases L₂.eq_nil_or_concat with rfl | ⟨L₃, e, rfl⟩
  · have := (List.append_inj' hL rfl).2
    simp at this
  · rw [List.concat_eq_append, show L₁ ++ (d, HOp.read, y) :: (L₃ ++ [e]) =
      (L₁ ++ (d, HOp.read, y) :: L₃) ++ [e] by simp] at hL
    exact h L₁ d y L₃ (List.append_inj_left' hL rfl)

lemma seqCorrect_snoc_read (v₀ : V) {L : List (C × HOp V × V)} (h : SeqCorrect v₀ L) (c : C) (x : V)
    (hx : x = lastVal v₀ L) : SeqCorrect v₀ (L ++ [(c, .read, x)]) := by
  intro L₁ d y L₂ hL
  rcases L₂.eq_nil_or_concat with rfl | ⟨L₃, e, rfl⟩
  · obtain ⟨h1, h2⟩ := List.append_inj' hL rfl
    simp only [List.cons.injEq, Prod.mk.injEq] at h2
    rw [← h1, ← h2.1.2.2, hx]
  · rw [List.concat_eq_append, show L₁ ++ (d, HOp.read, y) :: (L₃ ++ [e]) =
      (L₁ ++ (d, HOp.read, y) :: L₃) ++ [e] by simp] at hL
    exact h L₁ d y L₃ (List.append_inj_left' hL rfl)

/-! ### The layout hypotheses and the invariant -/

/-- Writers (other than `c`) whose write sets meet `R c`. -/
def Nb (Wr : Finset C) (R : C → Finset B) (c : C) : Finset C :=
  Wr.filter fun d => d ≠ c ∧ ¬ Disjoint (R d) (R c)

/-- Registers covered by a pending write of the client or queued for a rewrite. -/
def U (l : Loc B V) : Finset B := l.pw ∪ l.q

/-- Hypotheses on the write sets: only writers have one, the registers of a write set are on
distinct servers, and the capacity condition (`m f + 2f + 1 ≤ |R c|` if `R c` meets the write sets
of `m` other writers). -/
structure Layout (δ : B → S) (f : ℕ) (Wr : Finset C) (R : C → Finset B) : Prop where
  out : ∀ c ∉ Wr, R c = ∅
  inj : ∀ c, Set.InjOn δ ↑(R c)
  cap : ∀ c ∈ Wr, #(Nb Wr R c) * f + 2 * f + 1 ≤ #(R c)

section Inv

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V) (Wr : Finset C)

local notation "Cf" => Cfg C B V (ℕ × V) (Loc B V)

/-- Register `b` is protected at level `T`: its value and all pending or queued writes on it have
timestamps `≥ T`. -/
def Prot (X : Cf) (T : ℕ) (b : B) : Prop :=
  T ≤ (X.val b).1 ∧ ∀ d, (∀ p ∈ X.pend d, p.reg = b → ∀ w, p.op = .write w → T ≤ w.1) ∧
    (b ∈ (X.loc d).q → T ≤ (X.loc d).ts)

/-- `x` is the pair of the write in its writing phase. -/
def HI (X : Cf) (T : ℕ) (a : Option (C × HOp V)) (x : ℕ × V) : Prop :=
  ∃ c v, a = some (c, HOp.write v) ∧ (X.loc c).mode = .wp ∧ x = (T + 1, v)

/-- Admissible timestamped values. -/
def OK (X : Cf) (L : List (C × HOp V × V)) (a : Option (C × HOp V)) (x : ℕ × V) : Prop :=
  x.1 < wcount L ∨ x = (wcount L, lastVal v₀ L) ∨ HI X (wcount L) a x

open Classical in
/-- Registers of `wrSet` of `c` overwritten by a value other than `x` and no longer covered by
the writers sharing registers with `c`. -/
noncomputable def Sp (X : Cf) (c : C) (x : ℕ × V) : Finset B :=
  (X.loc c).wr.filter fun b => X.val b ≠ x ∧ ∀ d ∈ Nb Wr R c, b ∉ U (X.loc d)

/-- The invariant of sequential runs. -/
structure SInv (X : Cf) (L : List (C × HOp V × V)) (a : Option (C × HOp V)) : Prop where
  hist : X.hist = seqHist L ++ aPart a
  corr : SeqCorrect v₀ L
  cur : ∀ d, X.cur d = curOf a d
  wpTs : ∀ c v, a = some (c, .write v) → (X.loc c).mode = .wp →
    (X.loc c).ts = wcount L + 1 ∧ (X.loc c).val = v
  fresh : ∀ c v, a = some (c, .write v) → (X.loc c).mode = .wp → ∀ p ∈ X.pend c, ∀ w,
    p.op = .write w → p.reg ∉ (X.loc c).cov → w = (wcount L + 1, v)
  vals : ∀ b, OK v₀ X L a (X.val b)
  pends : ∀ d, ∀ p ∈ X.pend d, ∀ w, p.op = .write w → OK v₀ X L a w ∧ w.1 ≤ (X.loc d).ts
  tsv : ∀ d, OK v₀ X L a ((X.loc d).ts, (X.loc d).val)
  best : ∀ d, (X.loc d).mode.isColl → OK v₀ X L a (X.loc d).best
  quorum : wcount L = 0 ∨ ∃ Q : Finset B, f + 1 ≤ #(Q.image δ) ∧ (∀ b ∈ Q, Prot X (wcount L) b) ∧
    ∀ d, (X.loc d).mode.isColl → (∃ b ∈ Q, b ∈ (X.loc d).got) → wcount L ≤ (X.loc d).best.1
  count : ∀ c v, a = some (c, .write v) → (X.loc c).mode = .wp →
    #(Sp R Wr X c (wcount L + 1, v)) + ∑ d ∈ Nb Wr R c, #(U (X.loc d)) ≤ #(Nb Wr R c) * f

lemma OK.le {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)} {x : ℕ × V} (h : OK v₀ X L a x) :
    x.1 ≤ wcount L + 1 := by
  rcases h with h | h | ⟨c, v, -, -, h⟩
  · omega
  · rw [h]; simp
  · rw [h]

lemma OK.le_of_not_wp {X : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)} {x : ℕ × V} (h : OK v₀ X L a x)
    (hn : ∀ c v, a = some (c, .write v) → (X.loc c).mode ≠ .wp) : x.1 ≤ wcount L := by
  rcases h with h | rfl | ⟨c, v, h1, h2, rfl⟩
  · omega
  · simp
  · exact absurd h2 (hn c v h1)

/-- `OK` only depends on the modes. -/
lemma OK.congr {X X' : Cf} {L : List (C × HOp V × V)} {a : Option (C × HOp V)} {x : ℕ × V}
    (hm : ∀ c, (X'.loc c).mode = (X.loc c).mode) (h : OK v₀ X L a x) : OK v₀ X' L a x := by
  rcases h with h | h | ⟨c, v, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨c, v, h1, (hm c).trans h2, h3⟩)

end Inv

end Podc.RegisterEmulationSpace.Alg2
