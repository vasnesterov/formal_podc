import Papers.PODC2019.RDMAAgreement.PMP.Model

/-!
# The inductive invariant for the repaired Protected Memory Paxos

Definitions of the invariant `Inv` (global part) and `LInv` (per process), and the frame lemma
`LInv.frame` used for processes that do not take the step.

The heart of the invariant is the Paxos-style `SafeAt` (Lamport): when the attempt with ballot
`c` enters phase 2 with value `w`, for every smaller ballot `b` a majority of memories either
accepted `(b, w)` or will never accept anything with ballot `b`, witnessed by a slot with
`minProp > b`. "Never" is justified by the permission mechanism (Lemma D.3), captured by the
`d3*` fields: while a process holds the permission of `m` after reading `m`, no slot of `m` has a
`minProp` larger than the one it read.
-/

namespace Podc.RDMAAgreement.PMP

set_option linter.unusedSectionVars false

open Function

variable {P M V : Type*} [DecidableEq P] [DecidableEq M] [Fintype M]

/-- `x ≤ y` on `(accProp, value)` pairs, comparing ballots, `⊥` least. -/
def AccLe (x y : Option (ℕ × V)) : Prop :=
  ∀ a v, x = some (a, v) → ∃ a' v', y = some (a', v') ∧ a ≤ a'

theorem AccLe.refl (x : Option (ℕ × V)) : AccLe x x := fun a v h => ⟨a, v, h, le_rfl⟩

theorem AccLe.trans {x y z : Option (ℕ × V)} (h1 : AccLe x y) (h2 : AccLe y z) : AccLe x z := by
  intro a v hx
  obtain ⟨a', v', hy, ha⟩ := h1 a v hx
  obtain ⟨a'', v'', hz, ha'⟩ := h2 a' v' hy
  exact ⟨a'', v'', hz, ha.trans ha'⟩

theorem AccLe.none_left (y : Option (ℕ × V)) : AccLe none y := by
  intro a v h; cases h

theorem AccLe.some_some {a a' : ℕ} (v v' : V) (h : a ≤ a') : AccLe (some (a, v)) (some (a', v')) := by
  intro b w hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  exact ⟨a', v', rfl, h⟩

/-- Lamport's `SafeAt(w, c)`: no ballot `0 < b < c` can ever be chosen with a value other than
`w`. -/
def SafeAt (s : State P M V) (w : V) (c : ℕ) : Prop :=
  ∀ b, 0 < b → b < c → ∃ Q : Finset M, Maj Q ∧ ∀ m ∈ Q,
    (∃ r, (m, r, b, w) ∈ s.votes) ∨
      ((∀ r x, (m, r, b, x) ∉ s.votes) ∧ ∃ r, b < (s.slot m r).mp)

/-- Per-thread part of the invariant: thread `m` of process `p` (local state `x`) has program
counter `c` and link `l`. -/
structure TInv (slot : M → P → Slot V) (perm : M → P) (votes : Set (M × P × ℕ × V))
    (p2val : ℕ → Option V) (p : P) (x : Proc P M V) (m : M) (c : PC) (l : Link P V) : Prop where
  unst : x.started = false → c = .off ∧ l = .idle
  pcAct : c ≠ .off → x.active = true
  np : x.noPh1 = true → c = .off ∨ c = .ph2 ∨ c = .wW2 ∨ c = .fin
  ph2 : c = .ph2 → x.noPh1 = true
  w2p2 : (c = .wW2 ∨ c = .fin) → x.p2s = true ∨ x.noPh1 = true
  idle : (c = .barrier ∨ c = .ph2 ∨ c = .fin) → l = .idle
  ready : x.active = true → m ∈ x.ready → c = .barrier ∨ c = .wW2 ∨ c = .fin
  doneFin : x.active = true → m ∈ x.done → c = .fin
  tperm : c = .wPerm → l = .sent .perm ∨ l = .resp .ack
  tw1 : c = .wW1 → (∃ sl, l = .sent (.w1 sl) ∧ sl.mp = x.bal) ∨
    (l = .resp .ack ∧ x.bal ≤ (slot m p).mp) ∨ l = .resp .nak
  trd : c = .wRd → l = .sent .rd ∨ ∃ f, l = .resp (.snap f)
  tw2 : c = .wW2 → l = .sent (.w2 x.bal x.curVal) ∨
    (l = .resp .ack ∧ (m, p, x.bal, x.curVal) ∈ votes) ∨ l = .resp .nak
  tmp : x.noPh1 = false → (c = .wRd ∨ c = .barrier ∨ c = .wW2 ∨ c = .fin) →
    x.bal ≤ (slot m p).mp
  linkW1 : ∀ sl, l = .sent (.w1 sl) → (slot m p).mp ≤ sl.mp ∧ sl.mp ≤ x.bal ∧
    AccLe (slot m p).acc sl.acc ∧ AccLe sl.acc x.lastIss ∧
    ∀ a y, sl.acc = some (a, y) → p2val a = some y
  linkW2 : ∀ b v, l = .sent (.w2 b v) → (slot m p).mp ≤ b ∧ b ≤ x.bal ∧
    AccLe (slot m p).acc (some (b, v)) ∧ AccLe (some (b, v)) x.lastIss ∧ p2val b = some v
  snapP2 : ∀ f, l = .resp (.snap f) → ∀ r a y, (f r).acc = some (a, y) → p2val a = some y
  d3a : ∀ b v, l = .sent (.w2 b v) → perm m = p → ∀ r, (slot m r).mp ≤ b
  d3b : c = .barrier → perm m = p → ∀ r, (slot m r).mp ≤ x.bal
  d3c : c = .ph2 → perm m = p → ∀ r, (slot m r).mp ≤ x.bal
  d3d : ∀ f, c = .wRd → l = .resp (.snap f) → perm m = p → ∀ r, (slot m r).mp ≤ (f r).mp
  r1 : ∀ f, c = .wRd → l = .resp (.snap f) → ∀ b, b < x.bal → ∀ r y,
    (m, r, b, y) ∈ votes → ∃ r' a z, (f r').acc = some (a, z) ∧ b ≤ a

/-- Per-process part of the invariant (`x` is the local state of process `p`). -/
structure LInv (inp : P → V) (slot : M → P → Slot V) (perm : M → P)
    (votes : Set (M × P × ℕ × V)) (p2val : ℕ → Option V) (used : Finset ℕ) (p : P)
    (x : Proc P M V) : Prop where
  unst : x.started = false → x.active = false
  balUsed : x.started = true → x.bal ∈ used
  balPos : x.started = true → 1 ≤ x.bal
  p2cur : x.active = true → (x.p2s = true ∨ x.noPh1 = true) → p2val x.bal = some x.curVal
  p2none : x.active = true → x.p2s = false → x.noPh1 = false → p2val x.bal = none
  curInp : ∃ q, inp q = x.curVal
  curMax : x.active = true → x.noPh1 = false → x.curMax = 0 ∨ p2val x.curMax = some x.curVal
  lastIss : ∀ a y, x.lastIss = some (a, y) → p2val a = some y ∧ a ≤ x.bal
  done : x.active = true → ∀ m ∈ x.done, (m, p, x.bal, x.curVal) ∈ votes
  slotMp : ∀ m, (slot m p).mp ≤ x.bal
  accLI : ∀ m, AccLe (slot m p).acc x.lastIss
  r2 : x.active = true → x.noPh1 = false → ∀ m ∈ x.ready, ∀ b, x.curMax < b → b < x.bal →
    ∀ r y, (m, r, b, y) ∉ votes
  thr : ∀ m, TInv slot perm votes p2val p x m (x.pc m) (x.link m)

/-- The inductive invariant of the repaired algorithm. -/
structure Inv (p1 : P) (inp : P → V) (s : State P M V) : Prop where
  p2zero : s.p2val 0 = none
  p2used : ∀ b w, s.p2val b = some w → b ∈ s.used
  p2inp : ∀ b w, s.p2val b = some w → ∃ q, inp q = w
  safe : ∀ c w, s.p2val c = some w → SafeAt s w c
  voteP2 : ∀ m r b x, (m, r, b, x) ∈ s.votes → s.p2val b = some x
  accMono : ∀ m r b x, (m, r, b, x) ∈ s.votes → AccLe (some (b, x)) (s.slot m r).acc
  slotP2 : ∀ m r a y, (s.slot m r).acc = some (a, y) → s.p2val a = some y
  dec : ∀ v ∈ s.decs, ∃ p b, ∃ W : Finset M, Maj W ∧ ∀ m ∈ W, (m, p, b, v) ∈ s.votes
  fresh : (s.pr p1).started = false → ∀ m, s.perm m = p1 → ∀ r, (s.slot m r).mp = 0
  inj : ∀ p q, p ≠ q → (s.pr p).started = true → (s.pr q).started = true →
    (s.pr p).bal ≠ (s.pr q).bal
  loc : ∀ p, LInv inp s.slot s.perm s.votes s.p2val s.used p (s.pr p)

/-- Frame lemma for one thread: changes of the global state that do not concern memory `m`'s
own slot of `p`, nor memory `m` while `p` holds its permission. -/
theorem TInv.frame {slot slot' : M → P → Slot V} {perm perm' : M → P}
    {votes votes' : Set (M × P × ℕ × V)} {p2val p2val' : ℕ → Option V}
    {p : P} {x : Proc P M V} {m : M} {c : PC} {l : Link P V}
    (h : TInv slot perm votes p2val p x m c l)
    (hslot : slot' m p = slot m p)
    (hperm : perm' m = p → perm m = p ∧ ∀ r, slot' m r = slot m r)
    (hp2 : ∀ a y, p2val a = some y → p2val' a = some y)
    (hvotes : votes ⊆ votes')
    (hnew : ∀ r b y, (m, r, b, y) ∈ votes' → (m, r, b, y) ∉ votes → (slot m p).mp ≤ b) :
    TInv slot' perm' votes' p2val' p x m c l where
  unst := h.unst
  pcAct := h.pcAct
  np := h.np
  ph2 := h.ph2
  w2p2 := h.w2p2
  idle := h.idle
  ready := h.ready
  doneFin := h.doneFin
  tperm := h.tperm
  tw1 hm := by rw [hslot]; exact h.tw1 hm
  trd := h.trd
  tw2 hm := (h.tw2 hm).imp id (Or.imp (And.imp id (fun h => hvotes h)) id)
  tmp := by rw [hslot]; exact h.tmp
  linkW1 sl hl := by
    rw [hslot]
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.linkW1 sl hl
    exact ⟨h1, h2, h3, h4, fun a y hy => hp2 _ _ (h5 a y hy)⟩
  linkW2 b v hl := by
    rw [hslot]
    obtain ⟨h1, h2, h3, h4, h5⟩ := h.linkW2 b v hl
    exact ⟨h1, h2, h3, h4, hp2 _ _ h5⟩
  snapP2 f hl r a y hy := hp2 _ _ (h.snapP2 f hl r a y hy)
  d3a b v hl hp r := by
    obtain ⟨hp, hs⟩ := hperm hp; rw [hs]; exact h.d3a b v hl hp r
  d3b hpc hp r := by
    obtain ⟨hp, hs⟩ := hperm hp; rw [hs]; exact h.d3b hpc hp r
  d3c hpc hp r := by
    obtain ⟨hp, hs⟩ := hperm hp; rw [hs]; exact h.d3c hpc hp r
  d3d f hpc hl hp r := by
    obtain ⟨hp, hs⟩ := hperm hp; rw [hs]; exact h.d3d f hpc hl hp r
  r1 f hpc hl b hb r y hv := by
    by_cases hold : (m, r, b, y) ∈ votes
    · exact h.r1 f hpc hl b hb r y hold
    · have h1 := hnew r b y hv hold
      by_cases hnp : x.noPh1 = false
      · have := h.tmp hnp (Or.inl hpc); omega
      · have := h.np (by simpa using hnp)
        rw [hpc] at this; simp at this

/-- Frame lemma: the local invariant of a process that does not take the step survives the
changes that other processes make to the global state. -/
theorem LInv.frame {inp : P → V} {slot slot' : M → P → Slot V} {perm perm' : M → P}
    {votes votes' : Set (M × P × ℕ × V)} {p2val p2val' : ℕ → Option V} {used used' : Finset ℕ}
    {p : P} {x : Proc P M V} (h : LInv inp slot perm votes p2val used p x)
    (hslot : ∀ m, slot' m p = slot m p)
    (hperm : ∀ m, perm' m = p → perm m = p ∧ ∀ r, slot' m r = slot m r)
    (hused : used ⊆ used')
    (hp2 : ∀ a y, p2val a = some y → p2val' a = some y)
    (hp2b : x.active = true → p2val' x.bal = p2val x.bal)
    (hvotes : votes ⊆ votes')
    (hnew : ∀ m r b y, (m, r, b, y) ∈ votes' → (m, r, b, y) ∉ votes → (slot m p).mp ≤ b) :
    LInv inp slot' perm' votes' p2val' used' p x where
  unst := h.unst
  balUsed hs := hused (h.balUsed hs)
  balPos := h.balPos
  p2cur ha h2 := hp2 _ _ (h.p2cur ha h2)
  p2none ha h1 h2 := by rw [hp2b ha]; exact h.p2none ha h1 h2
  curInp := h.curInp
  curMax ha h1 := (h.curMax ha h1).imp id (hp2 _ _)
  lastIss a y hl := ⟨hp2 _ _ (h.lastIss a y hl).1, (h.lastIss a y hl).2⟩
  done ha m hm := hvotes (h.done ha m hm)
  slotMp m := by rw [hslot]; exact h.slotMp m
  accLI m := by rw [hslot]; exact h.accLI m
  r2 ha hnp m hm b hb1 hb2 r y hv := by
    by_cases hold : (m, r, b, y) ∈ votes
    · exact h.r2 ha hnp m hm b hb1 hb2 r y hold
    · have h1 := hnew m r b y hv hold
      have h2 := (h.thr m).tmp hnp (Or.inr ((h.thr m).ready ha hm))
      omega
  thr m := (h.thr m).frame (hslot m) (hperm m) hp2 hvotes (hnew m)

end Podc.RDMAAgreement.PMP
