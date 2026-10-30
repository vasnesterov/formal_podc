import Papers.PODC2023.MBroadcast.FromRegisters

/-!
# A causal variant of Algorithm 2 (causal-MBroadcast on top of atomic SWMR registers)

Section 3 of the brief announcement states that the enriched variants of MBroadcast (fifo-,
causal-, reliable-MBroadcast) do not change its computing power. Algorithm 2 (full version)
implements fifo-MBroadcast but not causal-MBroadcast (`not_causalOrdering`). This file gives a
variant (ours, not in the paper) that implements causal-MBroadcast on top of atomic SWMR
registers, with any number of crashes:

```
shared: SENT[1..n]; SENT[i] = list of entries (m, h): m mbroadcast by pᵢ, h = the history of pᵢ
        (the list of its mdeliveries (sender, message), in order) when it mbroadcast m
local:  histᵢ (initially empty)
operation mbroadcast(m): (1) SENT[i] ← SENT[i] ⊕ (m, histᵢ); (2) catch_up(); (3) mdeliver m from pᵢ
periodically do catch_up().
catch_up(): for j from 1 to n, j ≠ i: L ← flattening of SENT[j] (each entry (x, h) gives h, then
  (j, x)); for (q, y) ∈ L in order: if (q, y) ∈ histᵢ: skip; else if q = i: stop processing L
  (it is the message of the current mbroadcast of pᵢ, which pᵢ mdelivers only at line 3);
  else mdeliver y from q.
```

The model is the one of `FromRegisters.lean` (the same phases and actions): one atomic step per
register access, the local processing of the read list `L` (function `go`) in the same step.
Safety: unique broadcasts, Validity, No-duplication, Mutual ordering, FIFO and causal ordering.
-/

namespace Podc.MBroadcast.FromRegisters.Causal

open Function

/-! ## Histories, dependencies and the processing function -/

section Generic

variable {P M : Type} [DecidableEq P] [DecidableEq M]

set_option linter.unusedSectionVars false

/-- The mdeliveries of `r`, in trace order, as pairs (sender, message). -/
def hdl (tr : List (Ev P M)) (r : P) : List (P × M) :=
  tr.filterMap fun
    | .bc .. => none
    | .dl r' q m => if r' = r then some (q, m) else none

/-- The trace events of the mdeliveries `L` by `r`. -/
def dlEvs (r : P) (L : List (P × M)) : List (Ev P M) := L.map fun z => .dl r z.1 z.2

variable {tr tr' : List (Ev P M)} {r q : P} {m : M}

@[simp] lemma hdl_nil : hdl ([] : List (Ev P M)) r = [] := rfl
@[simp] lemma hdl_append : hdl (tr ++ tr') r = hdl tr r ++ hdl tr' r := List.filterMap_append
@[simp] lemma hdl_cons_bc (p : P) (m : M) (tr : List (Ev P M)) :
    hdl (.bc p m :: tr) r = hdl tr r := by simp [hdl]
@[simp] lemma hdl_cons_dl (r' q : P) (m : M) (tr : List (Ev P M)) :
    hdl (.dl r' q m :: tr) r = (if r' = r then [(q, m)] else []) ++ hdl tr r := by
  by_cases h : r' = r <;> simp [hdl, h]

lemma hdl_dlEvs (r' : P) (L : List (P × M)) :
    hdl (dlEvs r' L) r = if r' = r then L else [] := by
  induction L with
  | nil => simp [dlEvs]
  | cons a L ih =>
    by_cases h : r' = r
    · simp_all [dlEvs]
    · simp only [dlEvs, List.map_cons, hdl_cons_dl, h, ite_false, List.nil_append] at ih ⊢
      exact ih

@[simp] lemma bcs_dlEvs (r' p : P) (L : List (P × M)) : bcs (dlEvs r' L) p = [] := by
  induction L <;> simp_all [dlEvs]

lemma mem_hdl {z : P × M} : z ∈ hdl tr r ↔ .dl r z.1 z.2 ∈ tr := by
  induction tr with
  | nil => simp
  | cons e tr ih =>
    cases e with
    | bc p' m' => simp [ih]
    | dl r' q' m' =>
      by_cases h : r' = r
      · subst h; obtain ⟨z1, z2⟩ := z; simp [ih, eq_comm]
      · simp [h, ih, Ne.symm h]

lemma count_hdl : (hdl tr r).count (q, m) = tr.count (.dl r q m) := by
  induction tr with
  | nil => simp
  | cons e tr ih =>
    cases e with
    | bc p' m' => simp [ih]
    | dl r' q' m' =>
      by_cases h : r' = r
      · subst h
        by_cases h' : (q', m') = (q, m)
        · simp only [Prod.mk.injEq] at h'; obtain ⟨rfl, rfl⟩ := h'; simp [ih]
        · have h'' : ¬ (q' = q ∧ m' = m) := fun ⟨a, b⟩ => h' (by rw [a, b])
          simp [ih, h'']
      · simp [h, ih]

lemma noDuplication_iff : NoDuplication tr ↔ ∀ r, (hdl tr r).Nodup := by
  simp only [NoDuplication, List.nodup_iff_count_le_one]
  constructor
  · intro h r z; obtain ⟨q, m⟩ := z; rw [count_hdl]; exact h r q m
  · intro h r q m; rw [← count_hdl]; exact h r (q, m)

lemma hdl_take_prefix (b : ℕ) : hdl (tr.take b) r <+: hdl tr r := by
  conv_rhs => rw [← List.take_append_drop b tr]
  rw [hdl_append]; exact List.prefix_append _ _

lemma hdl_decomp {k : ℕ} (h : tr[k]? = some (.dl r q m)) :
    hdl tr r = hdl (tr.take k) r ++ (q, m) :: hdl (tr.drop (k + 1)) r := by
  have hk : k < tr.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  conv_lhs => rw [← List.take_append_drop k tr, List.drop_eq_getElem_cons hk]
  rw [List.getElem?_eq_getElem hk] at h
  simp [Option.some.inj h]

/-- `L` is closed for the dependency relation `D`: the dependencies of each element precede
it. -/
def Closed (D : P × M → P × M → Prop) (L : List (P × M)) : Prop :=
  ∀ i z, L[i]? = some z → ∀ w, D z w → w ∈ L.take i

/-- `L` is closed relative to `acc`: the dependencies of each element precede it in `L` or are
in `acc`. -/
def SC (D : P × M → P × M → Prop) (acc L : List (P × M)) : Prop :=
  ∀ i z, L[i]? = some z → ∀ w, D z w → w ∈ L.take i ∨ w ∈ acc

variable {D : P × M → P × M → Prop}

lemma Closed.nil : Closed D [] := by intro i z h; simp at h

lemma Closed.snoc {acc : List (P × M)} {z : P × M} (h : Closed D acc)
    (hz : ∀ w, D z w → w ∈ acc) : Closed D (acc ++ [z]) := by
  intro i z' hi w hw
  by_cases hil : i < acc.length
  · rw [List.getElem?_append_left hil] at hi
    rw [List.take_append_of_le_length hil.le]; exact h i z' hi w hw
  · rw [List.getElem?_append_right (by omega)] at hi
    have : i - acc.length = 0 := by
      by_contra hc
      rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
    rw [this] at hi; simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
    rw [List.take_append, List.take_of_length_le (by omega)]
    exact List.mem_append_left _ (hz w hw)

lemma Closed.mono {D' : P × M → P × M → Prop} {L : List (P × M)} (h : Closed D L)
    (hD : ∀ z ∈ L, ∀ w, D' z w → D z w) : Closed D' L :=
  fun i z hi w hw => h i z hi w (hD z (List.mem_of_getElem? hi) w hw)

lemma Closed.sc {acc L : List (P × M)} (h : Closed D L) : SC D acc L :=
  fun i z hi w hw => Or.inl (h i z hi w hw)

lemma SC.append {acc L1 L2 : List (P × M)} (h1 : SC D acc L1) (h2 : SC D (acc ++ L1) L2) :
    SC D acc (L1 ++ L2) := by
  intro i z hi w hw
  by_cases hil : i < L1.length
  · rw [List.getElem?_append_left hil] at hi
    rw [List.take_append_of_le_length hil.le]; exact h1 i z hi w hw
  · rw [List.getElem?_append_right (by omega)] at hi
    rw [List.take_append, List.take_of_length_le (by omega)]
    rcases h2 _ z hi w hw with h | h
    · exact Or.inl (List.mem_append_right _ h)
    · rcases List.mem_append.1 h with h | h
      · exact Or.inr h
      · exact Or.inl (List.mem_append_left _ h)

lemma SC.singleton {acc : List (P × M)} {z : P × M} (h : ∀ w, D z w → w ∈ acc) :
    SC D acc [z] := by
  intro i z' hi w hw
  match i, hi with
  | 0, hi => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
             exact Or.inr (h w hw)

/-- Processing of a read list by `p`: skip what is already mdelivered, stop at a message of `p`
itself, mdeliver the rest (`acc` is the history). -/
def go (p : P) : List (P × M) → List (P × M) → List (P × M)
  | acc, [] => acc
  | acc, z :: L => if z ∈ acc then go p acc L else if z.1 = p then acc else go p (acc ++ [z]) L

variable {p : P}

lemma go_prefix : ∀ (acc L : List (P × M)), acc <+: go p acc L
  | acc, [] => List.prefix_rfl
  | acc, z :: L => by
    simp only [go]
    split_ifs
    · exact go_prefix acc L
    · exact List.prefix_rfl
    · exact (List.prefix_append acc [z]).trans (go_prefix _ L)

lemma go_mem : ∀ (acc L : List (P × M)) (z : P × M), z ∈ go p acc L → z ∈ acc ∨ z ∈ L
  | acc, [], z, h => Or.inl h
  | acc, a :: L, z, h => by
    simp only [go] at h
    split_ifs at h
    · rcases go_mem acc L z h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · exact Or.inl h
    · rcases go_mem _ L z h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · simp at h; subst h; exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

lemma go_nodup : ∀ (acc L : List (P × M)), acc.Nodup → (go p acc L).Nodup
  | acc, [], h => h
  | acc, z :: L, h => by
    simp only [go]
    split_ifs with h1
    · exact go_nodup acc L h
    · exact h
    · exact go_nodup _ L (List.nodup_append.2 ⟨h, List.nodup_singleton z,
        fun a ha b hb hab => h1 (by simp at hb; rw [← hb, ← hab]; exact ha)⟩)

lemma go_new : ∀ (acc L : List (P × M)) (z : P × M), z ∈ go p acc L → z ∉ acc → z.1 ≠ p
  | acc, [], z, h, h' => absurd h h'
  | acc, a :: L, z, h, h' => by
    simp only [go] at h
    split_ifs at h with h1 h2
    · exact go_new acc L z h h'
    · exact absurd h h'
    · by_cases hz : z = a
      · subst hz; exact h2
      · exact go_new _ L z h (by simp [h', hz])

lemma go_nonblock : ∀ (acc L1 L2 : List (P × M)), (∀ z ∈ L1, z.1 = p → z ∈ acc) →
    ∀ z ∈ L1, z ∈ go p acc (L1 ++ L2)
  | acc, [], L2, _, z, hz => by simp at hz
  | acc, a :: L1, L2, h, z, hz => by
    simp only [List.cons_append, go]
    have hrec : ∀ acc', acc ⊆ acc' → ∀ z ∈ L1, z ∈ go p acc' (L1 ++ L2) := fun acc' hsub =>
      go_nonblock acc' L1 L2 (fun z hz hzp => hsub (h z (List.mem_cons_of_mem _ hz) hzp))
    split_ifs with h1 h2
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact (go_prefix acc _).subset h1
      · exact hrec acc (fun _ h => h) z hz
    · exact absurd (h a (List.mem_cons_self ..) h2) h1
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact (go_prefix _ _).subset (by simp)
      · exact hrec _ (fun _ h => List.mem_append_left _ h) z hz

lemma go_closed : ∀ (acc L : List (P × M)), Closed D acc → SC D acc L → Closed D (go p acc L)
  | acc, [], h, _ => h
  | acc, z :: L, h, hL => by
    simp only [go]
    have htail : ∀ acc', z ∈ acc' → acc ⊆ acc' → SC D acc' L := by
      intro acc' hz hsub i z' hi w hw
      rcases hL (i + 1) z' (by simpa using hi) w hw with h' | h'
      · simp only [List.take_succ_cons, List.mem_cons] at h'
        rcases h' with rfl | h'
        · exact Or.inr hz
        · exact Or.inl h'
      · exact Or.inr (hsub h')
    split_ifs with h1 h2
    · exact go_closed acc L h (htail acc h1 (fun _ h => h))
    · exact h
    · refine go_closed _ L ?_ (htail _ (by simp) (fun _ h => List.mem_append_left _ h))
      refine h.snoc fun w hw => ?_
      rcases hL 0 z rfl w hw with h' | h'
      · simp at h'
      · exact h'

end Generic

/-! ## Trace lemmas -/

section TraceLemmas

variable {P M : Type} [DecidableEq P] [DecidableEq M]

set_option linter.unusedSectionVars false

lemma validity_append {tr L : List (Ev P M)} (h : Validity tr)
    (hL : ∀ r q m, Ev.dl r q m ∈ L → Ev.bc q m ∈ tr) : Validity (tr ++ L) := by
  intro i r q m hi
  by_cases hil : i < tr.length
  · rw [List.getElem?_append_left hil] at hi
    rw [List.take_append_of_le_length hil.le]; exact h i r q m hi
  · rw [List.getElem?_append_right (by omega)] at hi
    rw [List.take_append, List.take_of_length_le (by omega)]
    exact List.mem_append_left _ (hL r q m (List.mem_of_getElem? hi))

/-- A process has mdelivered all its previous messages when it mbroadcasts a new one. -/
def OwnBefore (tr : List (Ev P M)) : Prop :=
  ∀ j p m', tr[j]? = some (.bc p m') → ∀ m, .bc p m ∈ tr.take j → .dl p p m ∈ tr.take j

lemma OwnBefore.nil : OwnBefore ([] : List (Ev P M)) := by intro j p m h; simp at h

lemma OwnBefore.append_nobc {tr L : List (Ev P M)} (h : OwnBefore tr)
    (hL : ∀ p m, Ev.bc p m ∉ L) : OwnBefore (tr ++ L) := by
  intro j p m' hj m hm
  by_cases hjl : j < tr.length
  · rw [List.getElem?_append_left hjl] at hj
    rw [List.take_append_of_le_length hjl.le] at hm ⊢; exact h j p m' hj m hm
  · rw [List.getElem?_append_right (by omega)] at hj
    exact absurd (List.mem_of_getElem? hj) (hL p m')

lemma OwnBefore.snoc_bc {tr : List (Ev P M)} {p : P} {m' : M} (h : OwnBefore tr)
    (hp : ∀ m, Ev.bc p m ∈ tr → Ev.dl p p m ∈ tr) : OwnBefore (tr ++ [.bc p m']) := by
  intro j p' m'' hj m hm
  by_cases hjl : j < tr.length
  · rw [List.getElem?_append_left hjl] at hj
    rw [List.take_append_of_le_length hjl.le] at hm ⊢; exact h j p' m'' hj m hm
  · rw [List.getElem?_append_right (by omega)] at hj
    have hj' : j - tr.length = 0 := by
      by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
    rw [hj'] at hj; simp only [List.getElem?_cons_zero, Option.some.injEq, Ev.bc.injEq] at hj
    obtain ⟨rfl, rfl⟩ := hj
    have hjt : (tr ++ [Ev.bc p m']).take j = tr := by
      rw [List.take_append, List.take_of_length_le (by omega), hj']; simp
    rw [hjt] at hm ⊢; exact hp m hm

lemma fifo_of_causal {tr : List (Ev P M)} (hc : CausalOrdering tr) (ho : OwnBefore tr) :
    FifoOrdering tr := by
  intro p m m' i j hi hj hij q k hk
  obtain ⟨i', hi'j, hi'⟩ := exists_lt_of_mem_take (ho j p m' hj m (mem_take_of_getElem? hi hij))
  exact hc p p m m' i' j hi' hj hi'j q k hk

end TraceLemmas

/-! ## The model -/

/-- An entry of a register: a message and the history of its sender when it mbroadcast it. -/
abbrev Entry (n : ℕ) (M : Type) := M × List (Fin n × M)

/-- Configurations of the causal variant. -/
structure Cfg (n : ℕ) (M : Type) where
  /-- The shared registers `SENT[1..n]`. -/
  sent : Fin n → List (Entry n M)
  /-- The local histories (mdeliveries, in order). -/
  hist : Fin n → List (Fin n × M)
  /-- The control position of each process. -/
  phase : Fin n → Phase M
  /-- The crashed processes. -/
  crashed : Fin n → Bool
  /-- The MBroadcast trace. -/
  log : List (Ev (Fin n) M)

variable {n : ℕ} {M : Type} [DecidableEq M]

set_option linter.unusedSectionVars false

/-- The read list of a register `SENT[q]`: each entry `(x, h)` gives `h`, then `(q, x)`. -/
def flat (q : Fin n) (E : List (Entry n M)) : List (Fin n × M) :=
  E.flatMap fun e => e.2 ++ [(q, e.1)]

/-- `w` is a dependency of `z = (q, y)`: it is in the history attached to `y` in `SENT[q]`. -/
def Dep (S : Fin n → List (Entry n M)) (z w : Fin n × M) : Prop :=
  ∃ e ∈ S z.1, e.1 = z.2 ∧ w ∈ e.2

/-- The initial configuration. -/
def init : Cfg n M := ⟨fun _ => [], fun _ => [], fun _ => .idle, fun _ => false, []⟩

/-- `p` starts a periodic `catch_up`. -/
def startCU (c : Cfg n M) (p : Fin n) : Cfg n M :=
  { c with phase := update c.phase p (.catchUp none 0) }

/-- `p` skips its own register. -/
def skipSelf (c : Cfg n M) (p : Fin n) (own : Option M) (j : ℕ) : Cfg n M :=
  { c with phase := update c.phase p (.catchUp own (j + 1)) }

/-- One atomic read of `SENT[q]` by `p`, and the local processing of the read list. -/
def readReg (c : Cfg n M) (p q : Fin n) (own : Option M) (j : ℕ) : Cfg n M :=
  { c with
    phase := update c.phase p (.catchUp own (j + 1))
    hist := update c.hist p (go p (c.hist p) (flat q (c.sent q)))
    log := c.log ++ dlEvs p ((go p (c.hist p) (flat q (c.sent q))).drop (c.hist p).length) }

/-- End of `catch_up`; line 3 if this is the `catch_up` of `mbroadcast(m)`. -/
def finish (c : Cfg n M) (p : Fin n) (own : Option M) : Cfg n M :=
  { c with
    phase := update c.phase p .idle
    hist := update c.hist p (c.hist p ++ own.toList.map (Prod.mk p))
    log := c.log ++ dlEvs p (own.toList.map (Prod.mk p)) }

/-- The next local step of `p`. -/
def tick (c : Cfg n M) (p : Fin n) : Cfg n M :=
  match c.phase p with
  | .idle => startCU c p
  | .catchUp own j =>
    if hj : j < n then
      if (⟨j, hj⟩ : Fin n) = p then skipSelf c p own j else readReg c p ⟨j, hj⟩ own j
    else finish c p own

/-- One atomic step (`none`: the action is not enabled). -/
def step (c : Cfg n M) : Act n M → Option (Cfg n M)
  | .invoke p m =>
    if c.crashed p = false ∧ c.phase p = .idle ∧ Ev.bc p m ∉ c.log then
      some { c with
        sent := update c.sent p (c.sent p ++ [(m, c.hist p)])
        phase := update c.phase p (.catchUp (some m) 0)
        log := c.log ++ [.bc p m] }
    else none
  | .tick p => if c.crashed p = false then some (tick c p) else none
  | .crash p => some { c with crashed := update c.crashed p true }

/-- Reachable configurations. -/
inductive Reachable : Cfg n M → Prop
  | init : Reachable init
  | step {c c' : Cfg n M} {a : Act n M} : Reachable c → step c a = some c' → Reachable c'

/-! ## The invariant -/

/-- The inductive invariant of the causal variant. -/
structure Inv (c : Cfg n M) : Prop where
  uniq : UniqueBc c.log
  valid : Validity c.log
  mo : MOInv c.log
  ownb : OwnBefore c.log
  /-- Every mbroadcast message has an entry in the register of its sender. -/
  entryEx : ∀ p m, .bc p m ∈ c.log → ∃ e ∈ c.sent p, e.1 = m
  /-- The history in an entry is the history of the sender when it mbroadcast the message. -/
  entry : ∀ p e, e ∈ c.sent p → ∃ b, c.log[b]? = some (.bc p e.1) ∧ e.2 = hdl (c.log.take b) p
  /-- The histories of the entries of a register grow. -/
  chain : ∀ p, (c.sent p).Pairwise fun e e' => e.2 <+: e'.2
  hist : ∀ r, c.hist r = hdl c.log r
  nodup : ∀ r, (c.hist r).Nodup
  closedH : ∀ r, Closed (Dep c.sent) (c.hist r)
  closedE : ∀ p e, e ∈ c.sent p → Closed (Dep c.sent) e.2
  /-- A process has mdelivered all its messages, except the one of its current `mbroadcast`. -/
  own : ∀ p m, .bc p m ∈ c.log → (p, m) ∈ c.hist p ∨ ∃ j, c.phase p = .catchUp (some m) j
  pend : ∀ p m j, c.phase p = .catchUp (some m) j → (p, m) ∉ c.hist p
  jle : ∀ p o j, c.phase p = .catchUp o j → j ≤ n
  cu : ∀ p m j, c.phase p = .catchUp (some m) j → ∃ b, c.log[b]? = some (.bc p m) ∧
    ∀ q : Fin n, q.val < j → q ≠ p → ∀ m', .bc q m' ∈ c.log.take b → .dl p q m' ∈ c.log

lemma inv_init : Inv (init : Cfg n M) where
  uniq := by intro p m; simp [init]
  valid := by intro i p q m h; simp [init] at h
  mo := MOInv.nil
  ownb := OwnBefore.nil
  entryEx := by intro p m h; simp [init] at h
  entry := by intro p e h; simp [init] at h
  chain := by intro p; simp [init]
  hist := by intro r; simp [init]
  nodup := by intro r; simp [init]
  closedH := by intro r; simpa [init] using Closed.nil
  closedE := by intro p e h; simp [init] at h
  own := by intro p m h; simp [init] at h
  pend := by intro p m j h; simp [init] at h
  jle := by intro p o j h; simp [init] at h
  cu := by intro p m j h; simp [init] at h

/-! ## Preservation of the invariant -/

section Preservation

variable {c : Cfg n M}

lemma validity_bc_mem {tr : List (Ev (Fin n) M)} (hv : Validity tr) {r q : Fin n} {m : M}
    (h : Ev.dl r q m ∈ tr) : Ev.bc q m ∈ tr := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 h
  exact List.mem_of_mem_take (hv k r q m hk)

lemma Inv.bc_of_hist (h : Inv c) {r : Fin n} {z : Fin n × M} (hz : z ∈ c.hist r) :
    Ev.bc z.1 z.2 ∈ c.log := by
  rw [h.hist r, mem_hdl] at hz; exact validity_bc_mem h.valid hz

lemma Inv.bc_of_entry (h : Inv c) {q : Fin n} {e : Entry n M} (he : e ∈ c.sent q) :
    Ev.bc q e.1 ∈ c.log := by
  obtain ⟨b, hb, -⟩ := h.entry q e he; exact List.mem_of_getElem? hb

lemma Inv.bc_of_entryHist (h : Inv c) {q : Fin n} {e : Entry n M} (he : e ∈ c.sent q)
    {w : Fin n × M} (hw : w ∈ e.2) : Ev.bc w.1 w.2 ∈ c.log := by
  obtain ⟨b, -, hb⟩ := h.entry q e he
  rw [hb] at hw
  have := (hdl_take_prefix (tr := c.log) (r := q) b).subset hw
  rw [mem_hdl] at this; exact validity_bc_mem h.valid this

lemma Inv.bc_of_flat (h : Inv c) {q : Fin n} {z : Fin n × M} (hz : z ∈ flat q (c.sent q)) :
    Ev.bc z.1 z.2 ∈ c.log := by
  simp only [flat, List.mem_flatMap, List.mem_append, List.mem_singleton] at hz
  obtain ⟨e, he, hz | rfl⟩ := hz
  · exact h.bc_of_entryHist he hz
  · exact h.bc_of_entry he

lemma Inv.entry_hist_eq (h : Inv c) {p : Fin n} {e e' : Entry n M} (he : e ∈ c.sent p)
    (he' : e' ∈ c.sent p) (heq : e.1 = e'.1) : e.2 = e'.2 := by
  obtain ⟨b, hb, hb'⟩ := h.entry p e he
  obtain ⟨b', hb2, hb2'⟩ := h.entry p e' he'
  rw [heq] at hb
  have := eq_of_count_le_one (h.uniq p e'.1) hb hb2
  subst this; rw [hb', hb2']

lemma sc_flat {D : Fin n × M → Fin n × M → Prop} {q : Fin n} :
    ∀ {E : List (Entry n M)}, (∀ e ∈ E, Closed D e.2 ∧ ∀ w, D (q, e.1) w → w ∈ e.2) →
    ∀ acc, SC D acc (flat q E)
  | [], _, acc => by intro i z hi; simp [flat] at hi
  | e :: E, hE, acc => by
    have : flat q (e :: E) = (e.2 ++ [(q, e.1)]) ++ flat q E := by simp [flat]
    rw [this]
    refine SC.append (SC.append (hE e (by simp)).1.sc (SC.singleton fun w hw => ?_)) ?_
    · exact List.mem_append_right _ ((hE e (by simp)).2 w hw)
    · exact sc_flat (fun e' he' => hE e' (List.mem_cons_of_mem _ he')) _

lemma Inv.sc_read (h : Inv c) (q : Fin n) (acc : List (Fin n × M)) :
    SC (Dep c.sent) acc (flat q (c.sent q)) := by
  refine sc_flat (fun e he => ⟨h.closedE q e he, fun w hw => ?_⟩) acc
  obtain ⟨e', he', h1, h2⟩ := hw
  rwa [h.entry_hist_eq he he' h1.symm]

lemma dep_update {S : Fin n → List (Entry n M)} {p : Fin n} {m : M} {hh : List (Fin n × M)}
    {z w : Fin n × M} (hd : Dep (update S p (S p ++ [(m, hh)])) z w) :
    Dep S z w ∨ (z = (p, m) ∧ w ∈ hh) := by
  obtain ⟨e, he, h1, h2⟩ := hd
  by_cases hz : z.1 = p
  · rw [hz, update_self] at he
    rcases List.mem_append.1 he with he | he
    · exact Or.inl ⟨e, by rw [hz]; exact he, h1, h2⟩
    · simp only [List.mem_singleton] at he; subst he
      exact Or.inr ⟨Prod.ext hz h1.symm, h2⟩
  · rw [update_of_ne hz] at he; exact Or.inl ⟨e, he, h1, h2⟩

lemma Inv.after_invoke (h : Inv c) {p : Fin n} {m : M} (hidle : c.phase p = .idle)
    (hnot : Ev.bc p m ∉ c.log) :
    Inv { c with
        sent := update c.sent p (c.sent p ++ [(m, c.hist p)])
        phase := update c.phase p (.catchUp (some m) 0)
        log := c.log ++ [.bc p m] } := by
  have hfresh : ∀ {z : Fin n × M}, Ev.bc z.1 z.2 ∈ c.log → z ≠ (p, m) := by
    rintro z hz rfl; exact hnot hz
  have hmono : ∀ {L : List (Fin n × M)}, (∀ z ∈ L, Ev.bc z.1 z.2 ∈ c.log) →
      Closed (Dep c.sent) L →
      Closed (Dep (update c.sent p (c.sent p ++ [(m, c.hist p)]))) L := by
    intro L hL hc
    refine hc.mono fun z hz w hw => ?_
    rcases dep_update hw with hw | ⟨hzp, -⟩
    · exact hw
    · exact absurd hzp (hfresh (hL z hz))
  have htake : ∀ {b : ℕ} {e : Ev (Fin n) M}, c.log[b]? = some e →
      (c.log ++ [Ev.bc p m])[b]? = some e ∧ (c.log ++ [Ev.bc p m]).take b = c.log.take b := by
    intro b e hb
    have hbl : b < c.log.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
    exact ⟨by rw [List.getElem?_append_left hbl]; exact hb,
      List.take_append_of_le_length hbl.le⟩
  exact {
  uniq := by
    intro p' m'
    rw [List.count_append]
    by_cases hh : Ev.bc p' m' = Ev.bc p m
    · rw [hh, List.count_eq_zero.2 hnot]; simp
    · have hh' : ¬ (p = p' ∧ m = m') := fun ⟨h1, h2⟩ => hh (by rw [h1, h2])
      rw [List.count_singleton]; simpa [hh'] using h.uniq p' m'
  valid := validity_append h.valid (by simp)
  mo := h.mo.append (by intro p m hm; simp at hm)
  ownb := h.ownb.snoc_bc fun m' hm' => by
    rcases h.own p m' hm' with h1 | ⟨j, h1⟩
    · rw [h.hist p, mem_hdl] at h1; exact h1
    · rw [hidle] at h1; cases h1
  entryEx := by
    intro p' m' hm'
    rcases List.mem_append.1 hm' with hm' | hm'
    · obtain ⟨e, he, he'⟩ := h.entryEx p' m' hm'
      refine ⟨e, ?_, he'⟩
      by_cases hp : p' = p
      · subst hp; simp [he]
      · simpa [update_of_ne hp] using he
    · simp only [List.mem_singleton, Ev.bc.injEq] at hm'; obtain ⟨rfl, rfl⟩ := hm'
      exact ⟨(m', c.hist p'), by simp, rfl⟩
  entry := by
    intro p' e he
    by_cases hp : p' = p
    · subst hp
      simp only [update_self, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · obtain ⟨b, hb, hb'⟩ := h.entry p' e he
        exact ⟨b, (htake hb).1, by rw [(htake hb).2]; exact hb'⟩
      · refine ⟨c.log.length, by simp, ?_⟩
        simp [h.hist p']
    · simp only [update_of_ne hp] at he
      obtain ⟨b, hb, hb'⟩ := h.entry p' e he
      exact ⟨b, (htake hb).1, by rw [(htake hb).2]; exact hb'⟩
  chain := by
    intro p'
    by_cases hp : p' = p
    · subst hp
      simp only [update_self]
      refine List.pairwise_append.2 ⟨h.chain p', List.pairwise_singleton _ _, ?_⟩
      intro e he e' he'
      simp only [List.mem_singleton] at he'; subst he'
      obtain ⟨b, -, hb⟩ := h.entry p' e he
      rw [hb, h.hist p']; exact hdl_take_prefix b
    · simp only [update_of_ne hp]; exact h.chain p'
  hist := by intro r; simp [h.hist r]
  nodup := h.nodup
  closedH := fun r => hmono (fun z hz => h.bc_of_hist hz) (h.closedH r)
  closedE := by
    intro p' e he
    by_cases hp : p' = p
    · subst hp
      simp only [update_self, List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hmono (fun z hz => h.bc_of_entryHist he hz) (h.closedE p' e he)
      · exact hmono (fun z hz => h.bc_of_hist hz) (h.closedH p')
    · simp only [update_of_ne hp] at he
      exact hmono (fun z hz => h.bc_of_entryHist he hz) (h.closedE p' e he)
  own := by
    intro p' m' hm'
    rcases List.mem_append.1 hm' with hm' | hm'
    · rcases h.own p' m' hm' with h1 | ⟨j, h1⟩
      · exact Or.inl h1
      · by_cases hp : p' = p
        · subst hp; rw [hidle] at h1; cases h1
        · exact Or.inr ⟨j, by simp only [update_of_ne hp]; exact h1⟩
    · simp only [List.mem_singleton, Ev.bc.injEq] at hm'; obtain ⟨rfl, rfl⟩ := hm'
      exact Or.inr ⟨0, by simp⟩
  pend := by
    intro p' m' j hph
    by_cases hp : p' = p
    · subst hp
      simp only [update_self, Phase.catchUp.injEq, Option.some.injEq] at hph
      obtain ⟨rfl, rfl⟩ := hph
      intro hin; exact hnot (h.bc_of_hist hin)
    · simp only [update_of_ne hp] at hph; exact h.pend p' m' j hph
  jle := by
    intro p' o j hph
    by_cases hp : p' = p
    · subst hp; simp only [update_self, Phase.catchUp.injEq] at hph; omega
    · simp only [update_of_ne hp] at hph; exact h.jle p' o j hph
  cu := by
    intro p' m' j hph
    by_cases hp : p' = p
    · subst hp; simp only [update_self, Phase.catchUp.injEq, Option.some.injEq] at hph
      obtain ⟨rfl, rfl⟩ := hph
      exact ⟨c.log.length, by simp, fun q hq => absurd hq (by omega)⟩
    · simp only [update_of_ne hp] at hph; exact cu_append _ (h.cu p' m' j hph) }

lemma Inv.after_startCU (h : Inv c) {p : Fin n} (hidle : c.phase p = .idle) :
    Inv (startCU c p) where
  uniq := h.uniq
  valid := h.valid
  mo := h.mo
  ownb := h.ownb
  entryEx := h.entryEx
  entry := h.entry
  chain := h.chain
  hist := h.hist
  nodup := h.nodup
  closedH := h.closedH
  closedE := h.closedE
  own := by
    intro p' m' hm'
    rcases h.own p' m' hm' with h1 | ⟨j, h1⟩
    · exact Or.inl h1
    · by_cases hp : p' = p
      · subst hp; rw [hidle] at h1; cases h1
      · exact Or.inr ⟨j, by simp only [startCU, update_of_ne hp]; exact h1⟩
  pend := by
    intro p' m' j hph
    by_cases hp : p' = p
    · subst hp; simp [startCU] at hph
    · simp only [startCU, update_of_ne hp] at hph; exact h.pend p' m' j hph
  jle := by
    intro p' o j hph
    by_cases hp : p' = p
    · subst hp; simp only [startCU, update_self, Phase.catchUp.injEq] at hph; omega
    · simp only [startCU, update_of_ne hp] at hph; exact h.jle p' o j hph
  cu := by
    intro p' m' j hph
    by_cases hp : p' = p
    · subst hp; simp [startCU] at hph
    · simp only [startCU, update_of_ne hp] at hph; exact h.cu p' m' j hph

lemma Inv.after_skipSelf (h : Inv c) {p : Fin n} {own : Option M} {j : ℕ}
    (hph : c.phase p = .catchUp own j) (hj : j < n) (hjp : (⟨j, hj⟩ : Fin n) = p) :
    Inv (skipSelf c p own j) where
  uniq := h.uniq
  valid := h.valid
  mo := h.mo
  ownb := h.ownb
  entryEx := h.entryEx
  entry := h.entry
  chain := h.chain
  hist := h.hist
  nodup := h.nodup
  closedH := h.closedH
  closedE := h.closedE
  own := by
    intro p' m' hm'
    rcases h.own p' m' hm' with h1 | ⟨j', h1⟩
    · exact Or.inl h1
    · by_cases hp : p' = p
      · subst hp; rw [hph] at h1
        simp only [Phase.catchUp.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
        exact Or.inr ⟨j + 1, by simp [skipSelf]⟩
      · exact Or.inr ⟨j', by simp only [skipSelf, update_of_ne hp]; exact h1⟩
  pend := by
    intro p' m' j' hph'
    by_cases hp : p' = p
    · subst hp
      simp only [skipSelf, update_self, Phase.catchUp.injEq] at hph'
      obtain ⟨rfl, rfl⟩ := hph'
      exact h.pend p' m' j hph
    · simp only [skipSelf, update_of_ne hp] at hph'; exact h.pend p' m' j' hph'
  jle := by
    intro p' o j' hph'
    by_cases hp : p' = p
    · subst hp; simp only [skipSelf, update_self, Phase.catchUp.injEq] at hph'; omega
    · simp only [skipSelf, update_of_ne hp] at hph'; exact h.jle p' o j' hph'
  cu := by
    intro p' m' j' hph'
    by_cases hp : p' = p
    · subst hp
      simp only [skipSelf, update_self, Phase.catchUp.injEq] at hph'
      obtain ⟨rfl, rfl⟩ := hph'
      obtain ⟨b, hb, hb'⟩ := h.cu p' m' j hph
      refine ⟨b, hb, fun q hq hqp => hb' q ?_ hqp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · exact hq
      · exact absurd (hjp ▸ Fin.ext hq) hqp
    · simp only [skipSelf, update_of_ne hp] at hph'; exact h.cu p' m' j' hph'

lemma Inv.after_readReg (h : Inv c) {p q : Fin n} {own : Option M} {j : ℕ}
    (hph : c.phase p = .catchUp own j) (hqj : q.val = j) (hqp : q ≠ p) :
    Inv (readReg c p q own j) := by
  set L := flat q (c.sent q) with hL
  set acc := go p (c.hist p) L with hacc
  obtain ⟨new, hnew⟩ := go_prefix (p := p) (c.hist p) L
  rw [← hacc] at hnew
  have hdrop : acc.drop (c.hist p).length = new := by rw [← hnew]; simp
  have hc : readReg c p q own j = { c with
      phase := update c.phase p (.catchUp own (j + 1))
      hist := update c.hist p acc
      log := c.log ++ dlEvs p new } := by
    simp only [readReg, ← hL, ← hacc, hdrop]
  rw [hc]
  have hnd : acc.Nodup := go_nodup _ _ (h.nodup p)
  have hnewdisj : ∀ z ∈ new, z ∉ c.hist p := by
    rw [← hnew] at hnd
    intro z hz hz'; exact (List.nodup_append.1 hnd).2.2 z hz' z hz rfl
  have hnewp : ∀ z ∈ new, z.1 ≠ p := fun z hz =>
    go_new _ _ z (by rw [← hacc, ← hnew]; exact List.mem_append_right _ hz) (hnewdisj z hz)
  have hnobc : ∀ p' m', Ev.bc p' m' ∉ dlEvs p new := by intro p' m'; simp [dlEvs]
  have hmem_log : ∀ {e : Ev (Fin n) M}, e ∈ c.log ++ dlEvs p new → (∀ p' m', e ≠ .bc p' m') ∨
      e ∈ c.log := by
    intro e he
    rcases List.mem_append.1 he with he | he
    · exact Or.inr he
    · left; intro p' m' hpm; subst hpm; exact hnobc p' m' he
  have hbc : ∀ {p' : Fin n} {m' : M}, Ev.bc p' m' ∈ c.log ++ dlEvs p new → Ev.bc p' m' ∈ c.log := by
    intro p' m' hm
    rcases hmem_log hm with h1 | h1
    · exact absurd rfl (h1 p' m')
    · exact h1
  have hacc_sub : ∀ z ∈ c.hist p, z ∈ acc := fun z hz => by
    rw [← hnew]; exact List.mem_append_left _ hz
  exact {
  uniq := by
    intro p' m'
    rw [List.count_append, List.count_eq_zero.2 (hnobc p' m')]; simpa using h.uniq p' m'
  valid := validity_append h.valid (by
    intro r q' m' hm
    simp only [dlEvs, List.mem_map, Ev.dl.injEq] at hm
    obtain ⟨z, hz, rfl, rfl, rfl⟩ := hm
    have hz' : z ∈ acc := by rw [← hnew]; exact List.mem_append_right _ hz
    rcases go_mem _ _ z hz' with hz' | hz'
    · exact h.bc_of_hist hz'
    · exact h.bc_of_flat hz')
  mo := h.mo.append (by
    intro p' m' hm
    simp only [dlEvs, List.mem_map, Ev.dl.injEq] at hm
    obtain ⟨z, hz, rfl, h1, h2⟩ := hm
    exact absurd h1 (hnewp z hz))
  ownb := h.ownb.append_nobc hnobc
  entryEx := fun p' m' hm => h.entryEx p' m' (hbc hm)
  entry := by
    intro p' e he
    obtain ⟨b, hb, hb'⟩ := h.entry p' e he
    have hbl : b < c.log.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
    exact ⟨b, by rw [List.getElem?_append_left hbl]; exact hb,
      by rw [List.take_append_of_le_length hbl.le]; exact hb'⟩
  chain := h.chain
  hist := by
    intro r
    simp only [hdl_append, hdl_dlEvs]
    by_cases hr : r = p
    · subst hr; simp [← hnew, h.hist r]
    · simp [update_of_ne hr, Ne.symm hr, h.hist r]
  nodup := by
    intro r
    by_cases hr : r = p
    · subst hr; simpa using hnd
    · simpa [update_of_ne hr] using h.nodup r
  closedH := by
    intro r
    by_cases hr : r = p
    · subst hr; simpa using go_closed _ _ (h.closedH r) (h.sc_read q _)
    · simpa [update_of_ne hr] using h.closedH r
  closedE := h.closedE
  own := by
    intro p' m' hm'
    rcases h.own p' m' (hbc hm') with h1 | ⟨j', h1⟩
    · left
      by_cases hp : p' = p
      · subst hp; simpa using hacc_sub _ h1
      · simpa [update_of_ne hp] using h1
    · by_cases hp : p' = p
      · subst hp; rw [hph] at h1
        simp only [Phase.catchUp.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
        exact Or.inr ⟨j + 1, by simp⟩
      · exact Or.inr ⟨j', by simp only [update_of_ne hp]; exact h1⟩
  pend := by
    intro p' m' j' hph'
    by_cases hp : p' = p
    · subst hp
      simp only [update_self, Phase.catchUp.injEq] at hph'
      obtain ⟨rfl, rfl⟩ := hph'
      have h0 := h.pend p' m' j hph
      simp only [update_self]
      rw [← hnew]; intro hin
      rcases List.mem_append.1 hin with hin | hin
      · exact h0 hin
      · exact hnewp _ hin rfl
    · simp only [update_of_ne hp] at hph' ⊢; exact h.pend p' m' j' hph'
  jle := by
    intro p' o j' hph'
    by_cases hp : p' = p
    · subst hp; simp only [update_self, Phase.catchUp.injEq] at hph'
      have := q.isLt; omega
    · simp only [update_of_ne hp] at hph'; exact h.jle p' o j' hph'
  cu := by
    intro p' m' j' hph'
    by_cases hp : p' = p
    · subst hp
      simp only [update_self, Phase.catchUp.injEq] at hph'
      obtain ⟨rfl, rfl⟩ := hph'
      obtain ⟨b, hb, hb'⟩ := h.cu p' m' j hph
      have hbl : b < c.log.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
      refine ⟨b, by rw [List.getElem?_append_left hbl]; exact hb, fun q' hq hq'p m'' hm => ?_⟩
      rw [List.take_append_of_le_length hbl.le] at hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | hq
      · exact List.mem_append_left _ (hb' q' hq hq'p m'' hm)
      · have hq'q : q' = q := Fin.ext (hq.trans hqj.symm)
        subst hq'q
        -- the entry of `m''` in `SENT[q']`
        obtain ⟨e, he, he1⟩ := h.entryEx q' m'' (List.mem_of_mem_take hm)
        obtain ⟨A, B, hAB⟩ := List.append_of_mem he
        obtain ⟨be, hbe, hbe'⟩ := h.entry q' e he
        rw [he1] at hbe
        have hbeb : be < b := by
          obtain ⟨b'', hb'', hb''e⟩ := exists_lt_of_mem_take hm
          have := eq_of_count_le_one (h.uniq q' m'') hb''e hbe
          omega
        -- every element of `e.2` of sender `p'` is mdelivered by `p'`
        have hkey : ∀ z ∈ e.2, z.1 = p' → z ∈ c.hist p' := by
          rintro ⟨z1, z2⟩ hz hzp
          simp only at hzp; subst z1
          rw [hbe', mem_hdl] at hz
          obtain ⟨i, hi, hi'⟩ := exists_lt_of_mem_take hz
          have hvi := h.valid i q' p' z2 hi'
          rcases h.own p' z2 (List.mem_of_mem_take hvi) with h1 | ⟨j'', h1⟩
          · exact h1
          · exfalso
            rw [hph] at h1; simp only [Phase.catchUp.injEq, Option.some.injEq] at h1
            obtain ⟨rfl, -⟩ := h1
            obtain ⟨i', hi'i, hi'e⟩ := exists_lt_of_mem_take hvi
            have := eq_of_count_le_one (h.uniq _ _) hi'e hb
            have hil : i < be := by
              by_contra hc
              have hlen := List.length_take_le' be c.log
              have : i < (c.log.take be).length := by
                obtain ⟨_, _⟩ := List.getElem?_eq_some_iff.1 hi'
                simp_all
              omega
            omega
        have hflat : L = (flat q' A ++ (e.2 ++ [(q', e.1)])) ++ flat q' B := by
          rw [hL, hAB]; simp [flat]
        have hnb : ∀ z ∈ flat q' A ++ (e.2 ++ [(q', e.1)]), z.1 = p' → z ∈ c.hist p' := by
          intro z hz hzp
          simp only [List.mem_append, List.mem_singleton] at hz
          rcases hz with hz | hz | rfl
          · simp only [flat, List.mem_flatMap, List.mem_append, List.mem_singleton] at hz
            obtain ⟨e', he', hz | rfl⟩ := hz
            · have hpw := h.chain q'
              rw [hAB] at hpw
              have hpre : e'.2 <+: e.2 := by
                rw [List.pairwise_append] at hpw
                exact hpw.2.2 e' he' e (by simp)
              exact hkey z (hpre.subset hz) hzp
            · exact absurd hzp hqp
          · exact hkey z hz hzp
          · exact absurd hzp hqp
        have hin : (q', m'') ∈ acc := by
          rw [hacc, hflat]
          exact go_nonblock _ _ _ hnb _ (by simp [he1])
        rw [← hnew] at hin
        rcases List.mem_append.1 hin with hin | hin
        · rw [h.hist p', mem_hdl] at hin; exact List.mem_append_left _ hin
        · exact List.mem_append_right _ (by simp only [dlEvs, List.mem_map]; exact ⟨_, hin, rfl⟩)
    · simp only [update_of_ne hp] at hph'
      exact cu_append _ (h.cu p' m' j' hph') }

lemma Inv.after_finish (h : Inv c) {p : Fin n} {own : Option M} {j : ℕ}
    (hph : c.phase p = .catchUp own j) (hj : n ≤ j) :
    Inv (finish c p own) := by
  cases own with
  | none =>
    have hc : finish c p none = { c with phase := update c.phase p .idle } := by
      simp [finish, dlEvs]
    rw [hc]
    exact {
    uniq := h.uniq, valid := h.valid, mo := h.mo, ownb := h.ownb, entryEx := h.entryEx,
    entry := h.entry, chain := h.chain, hist := h.hist, nodup := h.nodup, closedH := h.closedH,
    closedE := h.closedE
    own := by
      intro p' m' hm'
      rcases h.own p' m' hm' with h1 | ⟨j', h1⟩
      · exact Or.inl h1
      · by_cases hp : p' = p
        · subst hp; rw [hph] at h1; cases h1
        · exact Or.inr ⟨j', by simp only [update_of_ne hp]; exact h1⟩
    pend := by
      intro p' m' j' hph'
      by_cases hp : p' = p
      · subst hp; simp at hph'
      · simp only [update_of_ne hp] at hph'; exact h.pend p' m' j' hph'
    jle := by
      intro p' o j' hph'
      by_cases hp : p' = p
      · subst hp; simp at hph'
      · simp only [update_of_ne hp] at hph'; exact h.jle p' o j' hph'
    cu := by
      intro p' m' j' hph'
      by_cases hp : p' = p
      · subst hp; simp at hph'
      · simp only [update_of_ne hp] at hph'; exact h.cu p' m' j' hph' }
  | some m =>
    have hc : finish c p (some m) = { c with
        phase := update c.phase p .idle
        hist := update c.hist p (c.hist p ++ [(p, m)])
        log := c.log ++ [.dl p p m] } := by
      simp [finish, dlEvs]
    rw [hc]
    obtain ⟨b, hb, hb'⟩ := h.cu p m j hph
    have hbm : Ev.bc p m ∈ c.log := List.mem_of_getElem? hb
    exact {
    uniq := by
      intro p' m'
      have h0 : [Ev.dl p p m].count (Ev.bc p' m') = 0 := List.count_eq_zero.2 (by simp)
      rw [List.count_append, h0]; exact h.uniq p' m'
    valid := validity_append h.valid (by
      intro r q m' hm; simp only [List.mem_singleton, Ev.dl.injEq] at hm
      obtain ⟨rfl, rfl, rfl⟩ := hm; exact hbm)
    mo := h.mo.append (by
      intro p' m' hm
      simp only [List.mem_singleton, Ev.dl.injEq] at hm
      obtain ⟨rfl, -, rfl⟩ := hm
      exact ⟨b, hb, fun q hq => hb' q (by have := q.isLt; omega) hq⟩)
    ownb := h.ownb.append_nobc (by simp)
    entryEx := by
      intro p' m' hm'
      exact h.entryEx p' m' (by simpa using hm')
    entry := by
      intro p' e he
      obtain ⟨b, hb, hb'⟩ := h.entry p' e he
      have hbl : b < c.log.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
      exact ⟨b, by rw [List.getElem?_append_left hbl]; exact hb,
        by rw [List.take_append_of_le_length hbl.le]; exact hb'⟩
    chain := h.chain
    hist := by
      intro r
      by_cases hr : r = p
      · subst hr; simp [h.hist r]
      · simp [update_of_ne hr, Ne.symm hr, h.hist r]
    nodup := by
      intro r
      by_cases hr : r = p
      · subst hr; simp only [update_self]
        exact List.nodup_append.2 ⟨h.nodup r, List.nodup_singleton _,
          fun a ha b hb hab => h.pend r m j hph (by simp at hb; rw [← hb, ← hab]; exact ha)⟩
      · simpa [update_of_ne hr] using h.nodup r
    closedH := by
      intro r
      by_cases hr : r = p
      · subst hr; simp only [update_self]
        refine (h.closedH r).snoc fun w hw => ?_
        obtain ⟨e, he, he1, hw⟩ := hw
        obtain ⟨b, -, hb⟩ := h.entry r e he
        rw [hb] at hw
        rw [h.hist r]; exact (hdl_take_prefix b).subset hw
      · simpa [update_of_ne hr] using h.closedH r
    closedE := h.closedE
    own := by
      intro p' m' hm'
      have hm'' : Ev.bc p' m' ∈ c.log := by simpa using hm'
      by_cases hp : p' = p
      · subst hp
        rcases h.own p' m' hm'' with h1 | ⟨j', h1⟩
        · left; simp [h1]
        · rw [hph] at h1; simp only [Phase.catchUp.injEq, Option.some.injEq] at h1
          obtain ⟨rfl, -⟩ := h1
          left; simp
      · rcases h.own p' m' hm'' with h1 | ⟨j', h1⟩
        · left; simpa [update_of_ne hp] using h1
        · exact Or.inr ⟨j', by simp only [update_of_ne hp]; exact h1⟩
    pend := by
      intro p' m' j' hph'
      by_cases hp : p' = p
      · subst hp; simp at hph'
      · simp only [update_of_ne hp] at hph' ⊢; exact h.pend p' m' j' hph'
    jle := by
      intro p' o j' hph'
      by_cases hp : p' = p
      · subst hp; simp at hph'
      · simp only [update_of_ne hp] at hph'; exact h.jle p' o j' hph'
    cu := by
      intro p' m' j' hph'
      by_cases hp : p' = p
      · subst hp; simp at hph'
      · simp only [update_of_ne hp] at hph'; exact cu_append _ (h.cu p' m' j' hph') }

lemma Inv.after_tick (h : Inv c) (p : Fin n) : Inv (tick c p) := by
  unfold Causal.tick
  split
  · next hidle => exact h.after_startCU hidle
  · next own j hph =>
    split
    · next hj =>
      split
      · next hjp => exact h.after_skipSelf hph hj hjp
      · next hjp => exact h.after_readReg hph rfl hjp
    · next hj => exact h.after_finish hph (by omega)

lemma Inv.after_step (h : Inv c) {a : Act n M} {c' : Cfg n M} (hs : step c a = some c') :
    Inv c' := by
  cases a with
  | invoke p m =>
    simp only [Causal.step] at hs
    split_ifs at hs with hc
    cases hs; exact h.after_invoke hc.2.1 hc.2.2
  | tick p =>
    simp only [Causal.step] at hs
    split_ifs at hs; cases hs; exact h.after_tick p
  | crash p =>
    simp only [Causal.step, Option.some.injEq] at hs; subst hs
    exact ⟨h.uniq, h.valid, h.mo, h.ownb, h.entryEx, h.entry, h.chain, h.hist, h.nodup,
      h.closedH, h.closedE, h.own, h.pend, h.jle, h.cu⟩

lemma Reachable.inv {c : Cfg n M} (h : Reachable c) : Inv c := by
  induction h with
  | init => exact inv_init
  | step _ hs ih => exact ih.after_step hs

end Preservation

/-! ## Safety of the causal variant -/

/-- **Causal ordering** of the causal variant (any number of crashes). -/
theorem causalOrdering {c : Cfg n M} (hr : Reachable c) : CausalOrdering c.log := by
  have h := hr.inv
  intro p q m m' i j hi hj hij r k hk
  obtain ⟨e, he, he1⟩ := h.entryEx p m' (List.mem_of_getElem? hj)
  obtain ⟨be, hbe, hbe'⟩ := h.entry p e he
  rw [he1] at hbe
  have := eq_of_count_le_one (h.uniq p m') hbe hj
  subst this
  have hdep : Dep c.sent (p, m') (q, m) :=
    ⟨e, he, he1, by rw [hbe', mem_hdl]; exact mem_take_of_getElem? hi hij⟩
  have hdec := hdl_decomp hk
  have hcl := h.closedH r
  rw [h.hist r, hdec] at hcl
  have := hcl (hdl (c.log.take k) r).length (p, m') (by simp) (q, m) hdep
  rw [List.take_left'] at this
  · exact mem_hdl.1 this
  · rfl

/-- **Safety of the causal variant** (any number of crashes): unique broadcasts, Validity,
No-duplication and Mutual ordering. -/
theorem safe {c : Cfg n M} (hr : Reachable c) : UniqueBc c.log ∧ Safe c.log := by
  have h := hr.inv
  refine ⟨h.uniq, h.valid, noDuplication_iff.2 fun r => ?_, h.mo.mutualOrdering⟩
  rw [← h.hist r]; exact h.nodup r

/-- **FIFO ordering** of the causal variant. -/
theorem fifoOrdering {c : Cfg n M} (hr : Reachable c) : FifoOrdering c.log :=
  fifo_of_causal (causalOrdering hr) hr.inv.ownb

end Podc.MBroadcast.FromRegisters.Causal
