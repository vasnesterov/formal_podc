import Papers.PODC2020.DetectableSpace.Alg1Lin

/-!
# The invariant for the corrected Algorithm 1 (`R` initially `⟨v_init, 0, 1⟩`)

Ghost state: the sequence `rv 0, rv 1, …, rv wc` of values written to `R` (`rv 0` is the
initial value), for each process `p` the index `s p` of the value it read in line 1 of its
current `Write`, and whether its current `Write` has already written `R` (`wr p`).

Linearization: a `Read` is linearized at its read of `R`; a `Write` that writes `R` at that
write; a `Write` `W` of `p` that has executed line 1 and has not yet written `R` is linearized
*speculatively* immediately before the first write to `R` after its line 1 (`s p < wc`). Such a
speculative entry is always immediately followed by another write in the linearization (`Good`),
so it can be removed again if `W` later writes `R` itself (then it is re-linearized at that write)
or if `W.Recover` returns `fail`.

Views of a process (for a `Write` in progress): `Ph 1` (past line 1), `Ph 2`, `Ph 3`, `Dec`
(decided to complete: lines 8–13 or `CP = 2`), `vw = (⟨qval, q, qtoggle⟩, mtoggle)` and the bit
`A[p][q][1 - qtoggle]` (`bitOf`). The heart of the proof are the fields `f1` (all writes of `p` to
`R` after its line 1 are by its current `Write`), `f2b`/`f3` (a process never reuses the toggle
index of its own last visible write — this is where `R = ⟨v_init, 0, 1⟩` and `T_0 = 0` matter),
`cl1` (claim 1 of the paper) and `c2`/`kk` (claim 2 of the paper).
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n]

abbrev St (V : Type) (n : ℕ) := PSt (RWOp V) (Loc V n)

/-- Non-recovery states past line 1 with possibly `CP = 0`: 1 = after line 1, 2 = after
line 2, 3 = after line 3. -/
def Loc.stage : Loc V n → ℕ
  | .w2 .. => 1
  | .w3 .. => 2
  | .w4 .. | .w5 .. | .w6 .. | .w8 .. => 3
  | _ => 0

/-- Lines 8–12. -/
def Loc.isDec : Loc V n → Prop
  | .w8 .. | .w9 .. | .w11 .. | .w12 .. => True
  | _ => False

/-- Progress of the loop of lines 9–10. -/
def Loc.prog (n : ℕ) : Loc V n → ℕ
  | .w9 _ _ _ i => i.val
  | .w11 .. | .w12 .. | .ret _ => n
  | _ => 0

/-- Lines 6, 7. -/
def Loc.kd : Loc V n → Prop
  | .w6 .. | .w7 .. => True
  | _ => False

/-- Second conjunct of line 20. -/
def Loc.is20b : Loc V n → Prop
  | .r20b .. => True
  | _ => False

/-- Line 12. -/
def Loc.is12 : Loc V n → Prop
  | .w12 .. => True
  | _ => False

/-- `(⟨qval, q, qtoggle⟩, mtoggle)` of a write in progress (from the local state, or from
`RD_p` in recovery); before line 3 `mtoggle` is `T_p`. -/
def Loc.info (d : Trip V n × Bool) (m : Pv V n) : Loc V n → Trip V n × Bool
  | .w2 _ tr | .w3 _ tr => (tr, m.T)
  | .w4 _ tr mt | .w5 _ tr mt | .w6 _ tr mt | .w7 _ tr mt | .w8 _ tr mt | .w9 _ tr mt _
  | .w11 _ tr mt | .w12 _ tr mt => (tr, mt)
  | .r15 _ tr mt | .r17 _ tr mt | .r19 _ tr mt | .r20 _ tr mt | .r20b _ tr mt => (tr, mt)
  | _ => match m.rd with
    | some (mt, tr) => (tr, mt)
    | none => d

variable (v₀ : V)

/-- Default for `info`. -/
def dflt : Trip V n × Bool := ((v₀, 0, false), false)

/-- Past line `k` (`k = 1, 2, 3`) of a `Write`. -/
def Ph (k : ℕ) : St V n → Pv V n → Prop
  | .run _ (.write _) _ l, m => k ≤ l.stage ∨ 1 ≤ m.cp
  | _, _ => False

/-- Decided: will complete with `ack` unless a crash occurs while `CP ≤ 1`. -/
def Dec : St V n → Pv V n → Prop
  | .run _ (.write _) _ l, m => l.isDec ∨ m.cp = 2
  | _, _ => False

/-- Kdom: lines 6–7, or wrote `R` and `CP = 1`. -/
def Kd : St V n → Pv V n → Bool → Prop
  | .run _ (.write _) _ l, m, wr => l.kd ∨ (wr = true ∧ m.cp = 1)
  | _, _, _ => False

def vw : St V n → Pv V n → Trip V n × Bool
  | .run _ (.write _) _ l, m => l.info (dflt v₀) m
  | _, _ => dflt v₀

def valOf : St V n → V
  | .run _ (.write v) _ _ => v
  | _ => v₀

def progOf : St V n → ℕ
  | .run _ (.write _) _ l => l.prog n
  | _ => 0

def at20b : St V n → Prop
  | .run _ _ _ l => l.is20b
  | _ => False

/-- The bit `A[p][q][1 - qtoggle]`. -/
def bitOf (sh : Sh V n) (p : Fin n) (st : St V n) (m : Pv V n) : Bool :=
  sh.A (p, (vw v₀ st m).1.2.1, !(vw v₀ st m).1.2.2)

/-- Local consistency of a `Write(v)`. -/
def LCW (v : V) (wr : Bool) (b : Bool) (m : Pv V n) : Loc V n → Prop
  | .w1 v' | .w2 v' _ | .w3 v' _ => v' = v ∧ b = false ∧ m.cp = 0 ∧ m.res = none ∧ wr = false
  | .w4 v' _ mt => v' = v ∧ b = false ∧ m.cp = 0 ∧ m.res = none ∧ wr = false ∧ m.T = mt
  | .w5 v' tr mt | .w6 v' tr mt => v' = v ∧ b = false ∧ m.cp = 0 ∧ m.res = none ∧ wr = false ∧
      m.rd = some (mt, tr)
  | .w7 v' _ _ => v' = v ∧ b = false ∧ m.cp = 1 ∧ m.res = none ∧ wr = false
  | .w8 v' tr mt => v' = v ∧ m.res = none ∧ m.rd = some (mt, tr) ∧
      (b = false → m.cp ≤ 1 ∧ (m.cp = 1 ↔ wr = true)) ∧ (b = true → 1 ≤ m.cp)
  | .w9 v' _ _ _ | .w11 v' _ _ | .w12 v' _ _ => v' = v ∧ m.cp = 2 ∧ m.res = none
  | .r14 v' | .r15 v' _ _ => v' = v ∧ b = true
  | .r17 v' _ _ => v' = v ∧ b = true ∧ m.res = none
  | .r19 v' _ _ => v' = v ∧ b = true ∧ m.res = none ∧ m.cp ≠ 0
  | .r20 v' _ _ | .r20b v' _ _ => v' = v ∧ b = true ∧ m.res = none ∧ m.cp = 1
  | .ret r => (r = some v ∧ m.res = some v) ∨
      (r = none ∧ b = true ∧ m.res = none ∧ wr = false ∧ m.cp ≤ 1)
  | .d1 | .d2 _ | .dr => False

/-- Local consistency of a `Read`. -/
def LCR (b : Bool) (m : Pv V n) : Loc V n → Prop
  | .d1 | .d2 _ => m.res = none
  | .dr => b = true
  | .ret r => ∃ x, r = some x ∧ m.res = some x
  | _ => False

/-- Local consistency. -/
def LC (st : St V n) (m : Pv V n) (wr : Bool) : Prop :=
  match st with
  | .idle => wr = false
  | .run _ .read b l => LCR b m l ∧ wr = false
  | .run _ (.write v) b l => LCW v wr b m l ∧ m.cp ≤ 2 ∧ (wr = true → 1 ≤ m.cp) ∧
      (∀ x, m.res = some x → x = v ∧ m.cp = 2) ∧
      (1 ≤ m.cp → m.rd = some ((l.info (dflt v₀) m).2, (l.info (dflt v₀) m).1)) ∧
      (Ph 3 st m → m.cp ≤ 1 → m.T = (l.info (dflt v₀) m).2) ∧
      ((l.is12 ∨ m.res.isSome) → m.T = !(l.info (dflt v₀) m).2)

/-- Per-process invariant of `p` (state `st`, private memory `m`, ghost `s`, `wr`). -/
structure PI (p : Fin n) (st : St V n) (m : Pv V n) (s : ℕ) (wr : Bool) (wc : ℕ)
    (rv : ℕ → Trip V n) (sh : Sh V n) (inL : ℕ → Prop) : Prop where
  lc : LC v₀ st m wr
  m0 : ∀ a v, st = .run a (.write v) false (.w1 v) → ¬ inL a
  m1 : ∀ a v b l, st = .run a (.write v) b l → Ph 1 st m → wr = false → m.cp ≤ 1 →
    (inL a ↔ s < wc)
  m2 : ∀ a v b l, st = .run a (.write v) b l → (wr = true ∨ Dec st m) → inL a
  mr : ∀ a b l, st = .run a .read b l → ((∃ x, l = .d2 x) ∨ m.res.isSome) → inL a
  f1 : Ph 1 st m → ∀ k, s < k → k ≤ wc → (rv k).2.1 = p →
    wr = true ∧ rv k = (valOf v₀ st, p, (vw v₀ st m).2)
  f1w : wr = true → s < wc
  f2a : Ph 1 st m → s ≤ wc ∧ rv s = (vw v₀ st m).1
  f2b : Ph 1 st m → (vw v₀ st m).1.2.1 = p → (vw v₀ st m).1.2.2 ≠ (vw v₀ st m).2
  d : Dec st m → s < wc
  cl1 : Ph 2 st m → bitOf v₀ sh p st m = true → s < wc
  c2 : wr = true → m.cp = 1 → (sh.R ≠ (vw v₀ st m).1 ∨ bitOf v₀ sh p st m = true) ∧
    (at20b st → bitOf v₀ sh p st m = true)

/-- The conditions on `q = (vw p).1.2.1` needed for claim 2 (`t = qtoggle` of `p`). -/
def KQ (st : St V n) (m : Pv V n) (wr : Bool) (t : Bool) (p : Fin n) : Prop :=
  (m.T = t → wr = true) ∧ (Ph 3 st m → (vw v₀ st m).2 = t → wr = true) ∧
  (Dec st m → (vw v₀ st m).2 = !t → m.T = (vw v₀ st m).2 ∧ progOf st ≤ p.val)

/-- Ghost state. -/
structure Ghost (V : Type) (n : ℕ) where
  wc : ℕ
  rv : ℕ → Trip V n
  s : Fin n → ℕ
  wr : Fin n → Bool

abbrev Cfg1 (V : Type) [DecidableEq V] (v₀ : V) (n : ℕ) [NeZero n] := (alg1 V v₀ n true).Cfg
abbrev Hist (V : Type) (n : ℕ) := List (HEv (Fin n) (RWOp V) V)
abbrev LinL (V : Type) := List (ℕ × RWOp V)

/-- Committed responses: returned, persisted in `Ann_p.result`, or read by a `Read` in
line `d2`. -/
def rho (C : Cfg1 V v₀ n) (h : Hist V n) (a : ℕ) (r : V) : Prop :=
  (∃ c, HEv.res a (some r) c ∈ h) ∨
    ∃ p o b l, C.ps p = .run a o b l ∧ ((C.pv p).res = some r ∨ l = .d2 r)

/-- Removable (speculative) writes. -/
def SS (C : Cfg1 V v₀ n) (g : Ghost V n) (a : ℕ) : Prop :=
  ∃ p v b l, C.ps p = .run a (.write v) b l ∧ g.wr p = false ∧ (C.pv p).cp ≤ 1

/-- The invariant. -/
structure Inv (C : Cfg1 V v₀ n) (g : Ghost V n) (h : Hist V n) (L : LinL V) : Prop where
  R : C.sh.R = g.rv g.wc
  abs : fin v₀ L = (g.rv g.wc).1
  dl : DL h (rho v₀ C h) v₀ L
  good : Good (SS v₀ C g) L
  ids : ∀ a p o, HEv.inv a p o ∈ h → a < C.cnt
  uniq : ∀ a p o p' o', HEv.inv a p o ∈ h → HEv.inv a p' o' ∈ h → p = p' ∧ o = o'
  run : ∀ p a o b l, C.ps p = .run a o b l → HEv.inv a p o ∈ h ∧ ∀ r c, HEv.res a r c ∉ h
  nf : ∀ a, HEv.res a none false ∉ h
  resid : ∀ a r c, HEv.res a r c ∈ h → a < C.cnt
  pi : ∀ p, PI v₀ p (C.ps p) (C.pv p) (g.s p) (g.wr p) g.wc g.rv C.sh (· ∈ L.map Prod.fst)
  f3 : ∀ q, (g.rv g.wc).2.1 = q → (C.pv q).T = (g.rv g.wc).2.2 → g.wr q = true
  kk : ∀ p, Kd (C.ps p) (C.pv p) (g.wr p) → bitOf v₀ C.sh p (C.ps p) (C.pv p) = false →
    KQ v₀ (C.ps (vw v₀ (C.ps p) (C.pv p)).1.2.1) (C.pv (vw v₀ (C.ps p) (C.pv p)).1.2.1)
      (g.wr (vw v₀ (C.ps p) (C.pv p)).1.2.1) (vw v₀ (C.ps p) (C.pv p)).1.2.2 p

/-- The initial ghost state. -/
def g₀ : Ghost V n := ⟨0, fun _ => (v₀, 0, true), fun _ => 0, fun _ => false⟩

theorem inv_init : Inv v₀ (alg1 V v₀ n true).init (g₀ v₀) [] [] where
  R := rfl
  abs := rfl
  dl := ⟨by simp, by simp, by simp, by simp, by simp, trivial⟩
  good := trivial
  ids := by simp
  uniq := by simp
  run := by simp [RImpl.init]
  nf := by simp
  resid := by simp
  pi p := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [RImpl.init, Ph, Dec, g₀, alg1]
  f3 q _ hT := by simp [RImpl.init, alg1, g₀] at hT
  kk p hk := by simp [RImpl.init, Kd] at hk

/-- The invariant yields a durable detectable linearization. -/
theorem Inv.dlin {C : Cfg1 V v₀ n} {g : Ghost V n} {h : Hist V n} {L : LinL V}
    (hI : Inv v₀ C g h L) : DLin (register V v₀) h v₀ L :=
  hI.dl.toDLin v₀ (fun _ _ c hr => .inl ⟨c, hr⟩)

end Alg1

end Papers.PODC2020.DetectableSpace
