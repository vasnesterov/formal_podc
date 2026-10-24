import Papers.PODC2017.RegisterEmulationSpace.Algorithm2SeqSafe

/-!
# Write-sequential regularity (WS-Regularity, Section 2 and Appendix A.3)

A history is *write-sequential* if no two high-level writes overlap. Since writes are then totally
ordered by real time, the `t`-th write (`t ≥ 1`, in invocation order) has a well-defined value
`valOf v₀ wv t` (`valOf v₀ wv 0 = v₀`). A complete read is *regular* if it returns `valOf t` for
some `t` with `D ≤ t ≤ I`, where `D` is the number of writes that completed before the read was
invoked and `I` the number of writes invoked before the read returned. This is exactly the paper's
condition "there is a linearization of the read and all the writes": the writes must be linearized
in their real-time order, the read after the `D` writes that precede it and before the writes
invoked after its return, and it must return the value of the last write linearized before it.

`hscan` computes, by one pass over the history, the write values, the number of completed writes,
the pending operations with the number of completed writes at their invocation, and the two
properties `ws` (writes are sequential) and `reg` (every completed read is regular).
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace.Alg2

open Finset Function

/-- State of the history scan. -/
structure HSt (C V : Type*) where
  /-- values of the invoked writes, in order -/
  wv : List V
  /-- number of completed writes -/
  done : ℕ
  /-- pending operation of each client, with the number of writes completed at its invocation -/
  op : C → Option (HOp V × ℕ)
  /-- a write is pending -/
  wpend : Bool
  /-- the writes so far are sequential -/
  ws : Prop
  /-- the reads completed so far are regular -/
  reg : Prop

/-- The value of the `t`-th write (`v₀` for `t = 0`). -/
def valOf {V : Type*} (v₀ : V) (wv : List V) : ℕ → V
  | 0 => v₀
  | t + 1 => wv.getD t v₀

variable {C B S V : Type*} [DecidableEq C]

/-- One event of the history scan. -/
def hstep (v₀ : V) (s : HSt C V) : HEv C V → HSt C V
  | .inv c o =>
    { s with op := update s.op c (some (o, s.done)),
             wv := match o with | .write v => s.wv ++ [v] | .read => s.wv,
             wpend := match o with | .write _ => true | .read => s.wpend,
             ws := s.ws ∧ (isW o = true → s.wpend = false) }
  | .ret c x =>
    match s.op c with
    | some (.read, lv) =>
      { s with op := update s.op c none,
               reg := s.reg ∧ ∃ t, lv ≤ t ∧ t ≤ s.wv.length ∧ x = valOf v₀ s.wv t }
    | some (.write _, _) => { s with op := update s.op c none, done := s.done + 1, wpend := false }
    | none => s

/-- The initial scan state. -/
def hinit : HSt C V := ⟨[], 0, fun _ => none, false, True, True⟩

/-- The scan of a history. -/
def hscan (v₀ : V) (h : List (HEv C V)) : HSt C V := h.foldl (hstep v₀) hinit

lemma hscan_snoc (v₀ : V) (h : List (HEv C V)) (e : HEv C V) :
    hscan v₀ (h ++ [e]) = hstep v₀ (hscan v₀ h) e := by
  simp [hscan, List.foldl_append]

lemma hstep_ws (v₀ : V) (s : HSt C V) (e : HEv C V) (h : (hstep v₀ s e).ws) : s.ws := by
  cases e with
  | inv c o => exact h.1
  | ret c x =>
    simp only [hstep] at h
    split at h
    · exact h
    · exact h
    · exact h

/-- **WS-Regularity** (Section 2): in every run whose history is write-sequential (and whose
writes are invoked by `Wr`), every complete read is regular. -/
def WSRegular {L W : Type*} [DecidableEq B] (A : Alg C B V W L) (v₀ : V) (Wr : Set C) : Prop :=
  ∀ E : List (Ev C V), (∀ c v, HEv.inv c (.write v) ∈ (A.run E).hist → c ∈ Wr) →
    (hscan v₀ (A.run E).hist).ws → (hscan v₀ (A.run E).hist).reg

/-! ### The invariant of write-sequential runs -/

variable [LinearOrder B] [Fintype B] [Fintype S] [DecidableEq S]

section Inv

variable (δ : B → S) (f : ℕ) (R : C → Finset B) (v₀ : V) (Wr : Finset C)

local notation "Cf" => Cfg C B V (ℕ × V) (Loc B V)

/-- Some write is in its writing phase. -/
def WP (X : Cf) : Prop := ∃ d v, X.cur d = some (.write v) ∧ (X.loc d).mode = .wp

/-- Admissible timestamped values: `(t, valOf t)` with `t ≤ T`, or `t = T + 1` if the pending
write is in its writing phase. -/
def OKr (X : Cf) (σ : HSt C V) (x : ℕ × V) : Prop :=
  x.2 = valOf v₀ σ.wv x.1 ∧ (x.1 ≤ σ.done ∨ (x.1 = σ.done + 1 ∧ WP X))

/-- The invariant of write-sequential runs. -/
structure RInv (X : Cf) (σ : HSt C V) : Prop where
  reg : σ.reg
  cur : ∀ d, X.cur d = (σ.op d).map Prod.fst
  inHist : ∀ d o, X.cur d = some o → HEv.inv d o ∈ X.hist
  lvl : ∀ d o lv, σ.op d = some (o, lv) → lv ≤ σ.done ∧ (isW o = true → lv = σ.done)
  wlen : ∀ d v, X.cur d = some (.write v) → σ.wv.length = σ.done + 1 ∧ valOf v₀ σ.wv (σ.done + 1) = v
  wnone : (∀ d v, X.cur d ≠ some (.write v)) → σ.wv.length = σ.done
  wpend : σ.wpend = true ↔ ∃ d v, X.cur d = some (.write v)
  wuniq : ∀ d d' v v', X.cur d = some (.write v) → X.cur d' = some (.write v') → d = d'
  wpTs : ∀ c v, X.cur c = some (.write v) → (X.loc c).mode = .wp →
    (X.loc c).ts = σ.done + 1 ∧ (X.loc c).val = v
  fresh : ∀ c v, X.cur c = some (.write v) → (X.loc c).mode = .wp → ∀ p ∈ X.pend c, ∀ w,
    p.op = .write w → p.reg ∉ (X.loc c).cov → w = (σ.done + 1, v)
  vals : ∀ b, OKr v₀ X σ (X.val b)
  pends : ∀ d, ∀ p ∈ X.pend d, ∀ w, p.op = .write w → OKr v₀ X σ w ∧ w.1 ≤ (X.loc d).ts
  tsv : ∀ d, OKr v₀ X σ ((X.loc d).ts, (X.loc d).val)
  best : ∀ d, (X.loc d).mode.isColl → OKr v₀ X σ (X.loc d).best
  quorum : σ.done = 0 ∨ ∃ Q : Finset B, f + 1 ≤ #(Q.image δ) ∧ ∀ b ∈ Q, Prot X σ.done b
  coll : ∀ d o lv, σ.op d = some (o, lv) → (X.loc d).mode.isColl → lv = 0 ∨
    ∃ Q : Finset B, f + 1 ≤ #(Q.image δ) ∧ (∀ b ∈ Q, Prot X lv b) ∧
      ((∃ b ∈ Q, b ∈ (X.loc d).got) → lv ≤ (X.loc d).best.1)
  count : ∀ c v, X.cur c = some (.write v) → (X.loc c).mode = .wp →
    #(Sp R Wr X c (σ.done + 1, v)) + ∑ d ∈ Nb Wr R c, #(U (X.loc d)) ≤ #(Nb Wr R c) * f

/-- `OKr` only depends on the values written, the modes and the pending operations. -/
lemma OKr.congr {X X' : Cf} {σ : HSt C V} {x : ℕ × V} (hwp : WP X → WP X')
    (h : OKr v₀ X σ x) : OKr v₀ X' σ x :=
  ⟨h.1, h.2.imp_right fun h' => ⟨h'.1, hwp h'.2⟩⟩

lemma OKr.le {X : Cf} {σ : HSt C V} {x : ℕ × V} (h : OKr v₀ X σ x) : x.1 ≤ σ.done + 1 := by
  rcases h.2 with h | h <;> omega

lemma Prot.mono {X : Cf} {T T' : ℕ} {b : B} (h : Prot X T b) (hT : T' ≤ T) : Prot X T' b :=
  ⟨hT.trans h.1, fun d => ⟨fun p hp hpb w hw => hT.trans ((h.2 d).1 p hp hpb w hw),
    fun hq => hT.trans ((h.2 d).2 hq)⟩⟩

end Inv

end Podc.RegisterEmulationSpace.Alg2
