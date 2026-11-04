import Mathlib

/-!
# The arbiter object (Section 6.1, Figure 4, Appendix A, Theorem 5)

Imbs, Raynal, Taubenfeld. *On Asymmetric Progress Conditions.* PODC 2010 (full version:
IRISA research report PI-1952).

**Model.** Asynchronous shared memory, crash-stop processes indexed by an arbitrary type `ι`.
Each process `p` has a fixed role `role p ∈ {owner, guest}` and invokes `arbitrate(role p)` at
most once: a process *invokes* (participates) iff it takes at least one step, its first step being
line 01. Executions are given by an arbitrary schedule `σ : ℕ → ι` (the process taking step `t`);
a process is *correct* in `σ` iff it takes infinitely many steps (`Correct`), crash-stop = finitely
many steps. Each step performs exactly one access to a shared object; local computation is folded
into the step. Shared objects (`ArbSh`): atomic registers `PART[owner]`, `PART[guest]`
(initially `false`) and `WINNER` (initially `⊥`), and the consensus object `XCONS`. `XCONS` is
accessed by the (at most `x`) owners only and is wait-free for them, hence it is modelled as an
atomic consensus object: the first proposal is decided and every `propose` returns the decided
value in one step. (The bound "at most `x` owners" of Theorem 5 is only needed to implement `XCONS`
from `(x, x)`-live consensus; in this model it plays no role.)

**Program counters** (`APc`), one per access of Figure 4:
`idle` (line 01), `oRead` (read `PART[guest]`, line 02), `oProp b` (`XCONS.propose(b)`, line 02),
`oWrite w` (write `WINNER`, line 03), `gRead` (read `PART[owner]`, line 04), `gWait` (one read of
the busy-wait `wait(WINNER ≠ ⊥)`, line 04), `gWrite` (`WINNER ← guest`, line 04), `ret` (read
`WINNER` and return it, line 06), `done a` (returned `a`).

**Results** (Theorem 5 = Lemmas 12–16): `arbiter_agreement`, `arbiter_validity_owner`,
`arbiter_validity_guest` (the returned role was *invoked before the return* — the real-time version
needed in the proof of Lemma 10 of the paper), `arbiter_termination`.

The invariant `ArbInv` is also used by `GroupConsensus.lean`, where the arbiter is inlined into the
consensus algorithm of Figure 5.
-/

namespace Podc.AsymmetricProgress.Group

open Function

/-- The two possible arguments / results of `arbitrate()`. -/
inductive Role
  | owner
  | guest
  deriving DecidableEq, Repr

/-- The shared objects of one arbiter. -/
structure ArbSh where
  /-- `PART[owner]` -/
  pO : Bool := false
  /-- `PART[guest]` -/
  pG : Bool := false
  /-- `WINNER` (`none` = `⊥`) -/
  W : Option Role := none
  /-- the value decided by `XCONS` (`none` = no proposal yet) -/
  X : Option Bool := none
  deriving DecidableEq

/-- Program counters of `arbitrate()` (Figure 4), one per shared-memory access. -/
inductive APc
  /-- line 01, `PART[b] ← true` -/
  | idle
  /-- line 02, owner reads `PART[guest]` -/
  | oRead
  /-- line 02, owner proposes `b` to `XCONS` -/
  | oProp (b : Bool)
  /-- line 03, owner writes `WINNER` (`w` = `guest_win`) -/
  | oWrite (w : Bool)
  /-- line 04, guest reads `PART[owner]` -/
  | gRead
  /-- line 04, guest busy-waits for `WINNER ≠ ⊥` -/
  | gWait
  /-- line 04, guest writes `WINNER ← guest` -/
  | gWrite
  /-- line 06, read `WINNER` and return it -/
  | ret
  /-- returned `a` -/
  | done (a : Role)
  deriving DecidableEq

/-- One step of `arbitrate(r)` (Figure 4) from program counter `s` on the shared state `sh`:
the new program counter and the new shared state. -/
def astep (r : Role) : APc → ArbSh → APc × ArbSh
  | .idle, sh => match r with
    | .owner => (.oRead, { sh with pO := true })
    | .guest => (.gRead, { sh with pG := true })
  | .oRead, sh => (.oProp sh.pG, sh)
  | .oProp b, sh => (.oWrite (sh.X.getD b), { sh with X := some (sh.X.getD b) })
  | .oWrite w, sh => (.ret, { sh with W := some (if w then .guest else .owner) })
  | .gRead, sh => (if sh.pO then .gWait else .gWrite, sh)
  | .gWait, sh => (if sh.W.isSome then .ret else .gWait, sh)
  | .gWrite, sh => (.ret, { sh with W := some .guest })
  | .ret, sh => (sh.W.elim .ret .done, sh)
  | .done a, sh => (.done a, sh)

/-- Which program counters a process of role `r` can have. -/
def Shape : Role → APc → Prop
  | .owner, .gRead => False
  | .owner, .gWait => False
  | .owner, .gWrite => False
  | .guest, .oRead => False
  | .guest, .oProp _ => False
  | .guest, .oWrite _ => False
  | _, _ => True

/-- The part of the arbiter invariant that only concerns the shared state. -/
structure Glob (sh : ArbSh) : Prop where
  XT : sh.X = some true → sh.pG = true
  W_owner : sh.W = some .owner → sh.X = some false
  W_guest : sh.W = some .guest → sh.pG = true
  XF_W : sh.X = some false → sh.W ≠ some .guest
  X_pO : sh.X ≠ none → sh.pO = true

/-- The part of the arbiter invariant that concerns one process (of role `r`, at `s`). -/
structure Loc (sh : ArbSh) (r : Role) (s : APc) : Prop where
  pO_of : s ≠ .idle → r = .owner → sh.pO = true
  pG_of : s ≠ .idle → r = .guest → sh.pG = true
  shape : Shape r s
  oPropT : s = .oProp true → sh.pG = true
  oWrite_X : ∀ w, s = .oWrite w → sh.X = some w
  XF_gWrite : sh.X = some false → s ≠ .gWrite
  Xnone_W : sh.X = none → sh.W = some .guest → s ≠ .oProp false
  gWait_pO : s = .gWait → sh.pO = true
  ret_W : s = .ret → sh.W ≠ none
  done_W : ∀ a, s = .done a → sh.W = some a

/-- The inductive invariant of the arbiter (the proofs of Lemmas 12–16, made inductive). -/
structure ArbInv {ι : Type} (role : ι → Role) (sh : ArbSh) (pc : ι → APc) : Prop where
  glob : Glob sh
  loc : ∀ q, Loc sh (role q) (pc q)
  /-- an owner that read `PART[guest] = false` excludes guests about to write `WINNER ← guest` -/
  pair : ∀ q q', pc q = .oProp false → pc q' ≠ .gWrite
  exO : sh.pO = true → ∃ q, role q = .owner ∧ pc q ≠ .idle
  exG : sh.pG = true → ∃ q, role q = .guest ∧ pc q ≠ .idle

section Inv

variable {ι : Type} [DecidableEq ι] {role : ι → Role} {sh : ArbSh} {pc : ι → APc}

omit [DecidableEq ι] in
lemma ArbInv.init : ArbInv role ({} : ArbSh) (fun _ : ι => .idle) where
  glob := ⟨by decide, by decide, by decide, by decide, by decide⟩
  loc q := ⟨by simp, by simp, by cases role q <;> trivial, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp⟩
  pair := by simp
  exO h := absurd h (by decide)
  exG h := absurd h (by decide)

lemma astep_ne_idle (r : Role) (s : APc) (sh : ArbSh) : (astep r s sh).1 ≠ .idle := by
  cases s <;> cases r <;> simp only [astep] <;> (try split_ifs) <;> simp
  all_goals cases sh.W <;> simp

lemma upd_ne {f : ι → APc} {p q : ι} {s : APc} (h : q ≠ p) : update f p s q = f q :=
  update_of_ne h _ _

lemma ArbInv.upd (h : ArbInv role sh pc) {p : ι} {s' : APc} {sh' : ArbSh} (hg : Glob sh')
    (hp : Loc sh' (role p) s') (ho : ∀ q, q ≠ p → Loc sh' (role q) (pc q))
    (h1 : s' = .oProp false → ∀ q, q ≠ p → pc q ≠ .gWrite)
    (h2 : s' = .gWrite → ∀ q, q ≠ p → pc q ≠ .oProp false) (hne : s' ≠ .idle)
    (hO : sh'.pO = true → sh.pO = true ∨ role p = .owner)
    (hG : sh'.pG = true → sh.pG = true ∨ role p = .guest) :
    ArbInv role sh' (update pc p s') where
  glob := hg
  loc q := by
    rcases eq_or_ne q p with rfl | hq
    · simpa using hp
    · rw [upd_ne hq]; exact ho q hq
  pair q q' hq hq' := by
    rcases eq_or_ne q p with hqp | hqp <;> rcases eq_or_ne q' p with hqp' | hqp'
    · subst q q'; simp at hq hq'; rw [hq] at hq'; cases hq'
    · subst q; simp at hq; rw [upd_ne hqp'] at hq'; exact h1 hq q' hqp' hq'
    · subst q'; simp at hq'; rw [upd_ne hqp] at hq; exact h2 hq' q hqp hq
    · rw [upd_ne hqp] at hq; rw [upd_ne hqp'] at hq'; exact h.pair q q' hq hq'
  exO hp' := by
    rcases hO hp' with h' | h'
    · obtain ⟨q, hq, hq'⟩ := h.exO h'
      refine ⟨q, hq, ?_⟩
      rcases eq_or_ne q p with rfl | hqp
      · simpa using hne
      · rwa [upd_ne hqp]
    · exact ⟨p, h', by simpa using hne⟩
  exG hp' := by
    rcases hG hp' with h' | h'
    · obtain ⟨q, hq, hq'⟩ := h.exG h'
      refine ⟨q, hq, ?_⟩
      rcases eq_or_ne q p with rfl | hqp
      · simpa using hne
      · rwa [upd_ne hqp]
    · exact ⟨p, h', by simpa using hne⟩

lemma Loc.setPO {r : Role} {s : APc} (h : Loc sh r s) : Loc { sh with pO := true } r s :=
  ⟨fun _ _ => rfl, h.pG_of, h.shape, h.oPropT, h.oWrite_X, h.XF_gWrite, h.Xnone_W,
    fun _ => rfl, h.ret_W, h.done_W⟩

lemma Loc.setPG {r : Role} {s : APc} (h : Loc sh r s) : Loc { sh with pG := true } r s :=
  ⟨h.pO_of, fun _ _ => rfl, h.shape, fun _ => rfl, h.oWrite_X, h.XF_gWrite, h.Xnone_W,
    h.gWait_pO, h.ret_W, h.done_W⟩

lemma Loc.setX {r : Role} {s : APc} {b : Bool} (h : Loc sh r s)
    (hX : sh.X = none → b = false → s ≠ .gWrite) :
    Loc { sh with X := some (sh.X.getD b) } r s := by
  refine ⟨h.pO_of, h.pG_of, h.shape, h.oPropT, fun w hw => ?_, fun hx => ?_, fun hx => ?_,
    h.gWait_pO, h.ret_W, h.done_W⟩
  · rw [h.oWrite_X w hw]; rfl
  · cases hX' : sh.X with
    | none => simp [hX'] at hx; exact hX hX' hx
    | some c => simp [hX'] at hx; exact h.XF_gWrite (hX'.trans (by rw [hx]))
  · simp at hx

lemma Loc.setW {r : Role} {s : APc} {W' : Option Role} (h : Loc sh r s)
    (hW : ∀ a, sh.W = some a → W' = some a) (hW' : W' ≠ none)
    (h7 : sh.X = none → W' = some .guest → s ≠ .oProp false) :
    Loc { sh with W := W' } r s :=
  ⟨h.pO_of, h.pG_of, h.shape, h.oPropT, h.oWrite_X, h.XF_gWrite, h7, h.gWait_pO,
    fun _ => hW', fun a ha => hW a (h.done_W a ha)⟩

lemma shape_gWrite {r : Role} (h : Shape r .gWrite) : r = .guest := by cases r <;> trivial

lemma shape_oProp {r : Role} {b : Bool} (h : Shape r (.oProp b)) : r = .owner := by
  cases r <;> trivial

lemma ArbInv.same (h : ArbInv role sh pc) {p : ι} {s : APc} (hs : pc p = s) :
    ArbInv role sh (update pc p s) := by
  rw [← hs, update_eq_self]; exact h

theorem ArbInv.step (h : ArbInv role sh pc) (p : ι) :
    ArbInv role (astep (role p) (pc p) sh).2 (update pc p (astep (role p) (pc p) sh).1) := by
  have hl := h.loc p
  have hg := h.glob
  rcases hr : role p with _ | _ <;> rcases hs : pc p with _ | _ | b | w | _ | _ | _ | _ | a <;>
    rw [hr, hs] at hl <;> (try exact hl.shape.elim) <;> simp only [astep]
  case owner.idle =>
    refine h.upd ⟨hg.XT, hg.W_owner, hg.W_guest, hg.XF_W, fun _ => rfl⟩ ?_
      (fun q _ => (h.loc q).setPO) (by simp) (by simp) (by simp) (fun _ => Or.inr hr)
      (fun h' => Or.inl h')
    rw [hr]; exact ⟨fun _ _ => rfl, by simp, trivial, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp⟩
  case guest.idle =>
    refine h.upd ⟨fun _ => rfl, hg.W_owner, fun _ => rfl, hg.XF_W, hg.X_pO⟩ ?_
      (fun q _ => (h.loc q).setPG) (by simp) (by simp) (by simp) (fun h' => Or.inl h')
      (fun _ => Or.inr hr)
    rw [hr]; exact ⟨by simp, fun _ _ => rfl, trivial, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp⟩
  case owner.oRead =>
    refine h.upd hg ?_ (fun q _ => h.loc q) ?_ (by simp) (by simp) (fun h' => Or.inl h')
      (fun h' => Or.inl h')
    · rw [hr]
      refine ⟨fun _ _ => hl.pO_of (by simp) rfl, by simp, trivial, fun h' => by simpa using h',
        by simp, by simp, fun _ hW h' => ?_, by simp, by simp, by simp⟩
      simp only [APc.oProp.injEq] at h'
      simp [hg.W_guest hW] at h'
    · intro he q _ hq
      simp only [APc.oProp.injEq] at he
      have := (h.loc q).pG_of (by simp [hq]) (shape_gWrite (hq ▸ (h.loc q).shape))
      simp [he] at this
  case owner.oProp =>
    have hpO := hl.pO_of (by simp) rfl
    refine h.upd ⟨fun hx => ?_, fun hW => ?_, hg.W_guest, fun hx => ?_, fun _ => hpO⟩ ?_
      (fun q _ => (h.loc q).setX (fun _ hb hq => h.pair p q (by rw [hs, hb]) hq)) (by simp)
      (by simp) (by simp) (fun h' => Or.inl h') (fun h' => Or.inl h')
    · cases hX : sh.X with
      | none => simp only [hX, Option.getD_none, Option.some.injEq] at hx; exact hl.oPropT (by rw [hx])
      | some c => simp only [hX, Option.getD_some] at hx; exact hg.XT (by rw [hX, hx])
    · simp [hg.W_owner hW]
    · cases hX : sh.X with
      | none =>
        simp only [hX, Option.getD_none, Option.some.injEq] at hx
        exact fun hW => hl.Xnone_W hX hW (by rw [hx])
      | some c => simp only [hX, Option.getD_some] at hx; exact hg.XF_W (by rw [hX, hx])
    · rw [hr]
      exact ⟨fun _ _ => hpO, by simp, trivial, by simp, fun w hw => by simp at hw; rw [hw],
        by simp, by simp, by simp, by simp, by simp⟩
  case owner.oWrite =>
    have hX := hl.oWrite_X w rfl
    have hW : ∀ a, sh.W = some a → some (if w = true then Role.guest else .owner) = some a := by
      intro a ha
      cases a
      · have := hg.W_owner ha; rw [hX] at this; simp at this; simp [this]
      · have : w = true := by
          by_contra hw
          simp only [Bool.not_eq_true] at hw
          exact hg.XF_W (by rw [hX, hw]) ha
        simp [this]
    refine h.upd ⟨hg.XT, fun hW' => ?_, fun hW' => ?_, fun hx => ?_, hg.X_pO⟩ ?_
      (fun q _ => (h.loc q).setW hW (by simp) (fun hx => by rw [hX] at hx; cases hx))
      (by simp) (by simp) (by simp) (fun h' => Or.inl h') (fun h' => Or.inl h')
    · cases w <;> simp_all
    · cases w <;> simp_all [hg.XT]
    · rw [hX] at hx; simp at hx; simp [hx]
    · rw [hr]
      exact ⟨fun _ _ => hl.pO_of (by simp) rfl, by simp, trivial, by simp, by simp, by simp,
        by simp, by simp, fun _ => by simp, by simp⟩
  case guest.gWrite =>
    have hW : ∀ a, sh.W = some a → some Role.guest = some a := by
      intro a ha
      cases a
      · exact absurd rfl (hl.XF_gWrite (hg.W_owner ha))
      · rfl
    have hpG := hl.pG_of (by simp) rfl
    refine h.upd ⟨hg.XT, fun hW' => by simp at hW', fun _ => hpG,
      fun hx => absurd rfl (hl.XF_gWrite hx), hg.X_pO⟩ ?_
      (fun q _ => (h.loc q).setW hW (by simp) (fun _ _ hq => h.pair q p hq hs))
      (by simp) (by simp) (by simp) (fun h' => Or.inl h') (fun h' => Or.inl h')
    rw [hr]
    exact ⟨by simp, fun _ _ => hpG, trivial, by simp, by simp, by simp, by simp, by simp,
      fun _ => by simp, by simp⟩
  case guest.gRead =>
    have hpG := hl.pG_of (by simp) rfl
    split_ifs with hpO
    · refine h.upd hg ?_ (fun q _ => h.loc q) (by simp) (by simp) (by simp)
        (fun h' => Or.inl h') (fun h' => Or.inl h')
      rw [hr]
      exact ⟨by simp, fun _ _ => hpG, trivial, by simp, by simp, by simp, by simp,
        fun _ => hpO, by simp, by simp⟩
    · refine h.upd hg ?_ (fun q _ => h.loc q) (by simp) ?_ (by simp)
        (fun h' => Or.inl h') (fun h' => Or.inl h')
      · rw [hr]
        exact ⟨by simp, fun _ _ => hpG, trivial, by simp, by simp,
          fun hx => absurd (hg.X_pO (by simp [hx])) hpO, by simp, by simp, by simp, by simp⟩
      · intro _ q _ hq
        exact hpO ((h.loc q).pO_of (by simp [hq]) (shape_oProp (hq ▸ (h.loc q).shape)))
  case guest.gWait =>
    split_ifs with hW
    · refine h.upd hg ?_ (fun q _ => h.loc q) (by simp) (by simp) (by simp)
        (fun h' => Or.inl h') (fun h' => Or.inl h')
      rw [hr]
      exact ⟨by simp, fun _ _ => hl.pG_of (by simp) rfl, trivial, by simp, by simp, by simp,
        by simp, by simp, fun _ => by simpa [Option.isSome_iff_ne_none] using hW, by simp⟩
    · exact h.same hs
  case owner.ret =>
    rcases hW : sh.W with _ | a
    · exact absurd hW (hl.ret_W rfl)
    · refine h.upd hg ?_ (fun q _ => h.loc q) (by simp) (by simp) (by simp)
        (fun h' => Or.inl h') (fun h' => Or.inl h')
      rw [hr]
      exact ⟨fun _ _ => hl.pO_of (by simp) rfl, by simp, trivial, by simp, by simp, by simp,
        by simp, by simp, by simp, fun b hb => by simp at hb; rw [hW, hb]⟩
  case guest.ret =>
    rcases hW : sh.W with _ | a
    · exact absurd hW (hl.ret_W rfl)
    · refine h.upd hg ?_ (fun q _ => h.loc q) (by simp) (by simp) (by simp)
        (fun h' => Or.inl h') (fun h' => Or.inl h')
      rw [hr]
      exact ⟨by simp, fun _ _ => hl.pG_of (by simp) rfl, trivial, by simp, by simp, by simp,
        by simp, by simp, by simp, fun b hb => by simp at hb; rw [hW, hb]⟩
  case owner.done => exact h.same hs
  case guest.done => exact h.same hs

omit [DecidableEq ι] in
/-- Once `WINNER ≠ ⊥`, it never changes (agreement of the arbiter, Lemma 15). -/
theorem ArbInv.W_stable (h : ArbInv role sh pc) (p : ι) {a : Role} (ha : sh.W = some a) :
    (astep (role p) (pc p) sh).2.W = some a := by
  have hl := h.loc p
  have hg := h.glob
  rcases hr : role p with _ | _ <;> rcases hs : pc p with _ | _ | b | w | _ | _ | _ | _ | c <;>
    rw [hr, hs] at hl <;> (try exact hl.shape.elim) <;> simp only [astep] <;> (try exact ha)
  · have hX := hl.oWrite_X w rfl
    cases a
    · have := hg.W_owner ha; rw [hX] at this; simp at this; simp [this]
    · have : w = true := by
        by_contra hw
        simp only [Bool.not_eq_true] at hw
        exact hg.XF_W (by rw [hX, hw]) ha
      simp [this]
  · cases a
    · exact absurd rfl (hl.XF_gWrite (hg.W_owner ha))
    · rfl

/-- The rank of a program counter: the number of steps to the return, if nobody blocks. -/
def APc.rank : APc → ℕ
  | .idle => 5
  | .oRead => 4
  | .oProp _ => 3
  | .gRead => 3
  | .oWrite _ => 2
  | .gWait => 2
  | .gWrite => 2
  | .ret => 1
  | .done _ => 0

omit [DecidableEq ι] in
/-- Lemmas 12–14 (local form): every step of a process that has not returned and is not
blocked in `wait(WINNER ≠ ⊥)` with `WINNER = ⊥` brings it closer to the return. -/
lemma ArbInv.rank_lt (h : ArbInv role sh pc) (p : ι) (hd : ∀ a, pc p ≠ .done a)
    (hb : ¬ (pc p = .gWait ∧ sh.W = none)) :
    (astep (role p) (pc p) sh).1.rank < (pc p).rank := by
  have hl := h.loc p
  rcases hr : role p with _ | _ <;> rcases hs : pc p with _ | _ | b | w | _ | _ | _ | _ | c <;>
    rw [hr, hs] at hl <;> (try exact hl.shape.elim) <;> rw [hs] at hd hb <;>
    simp only [astep, APc.rank]
  all_goals (try split_ifs) <;> (try simp)
  · rcases hW : sh.W with _ | a
    · exact absurd hW (hl.ret_W rfl)
    · rfl
  · exact absurd rfl (hd c)
  · simp only [true_and] at hb
    rename_i h'
    exact h' (Option.isSome_iff_ne_none.2 hb)
  · rcases hW : sh.W with _ | a
    · exact absurd hW (hl.ret_W rfl)
    · rfl
  · exact absurd rfl (hd c)

end Inv

/-! ### Executions -/

/-- A configuration of the arbiter system. -/
structure ACfg (ι : Type) where
  /-- the shared objects -/
  sh : ArbSh
  /-- the program counters -/
  pc : ι → APc

variable {ι : Type} [DecidableEq ι]

/-- One step of process `p`. -/
def ACfg.step (role : ι → Role) (c : ACfg ι) (p : ι) : ACfg ι :=
  ⟨(astep (role p) (c.pc p) c.sh).2, update c.pc p (astep (role p) (c.pc p) c.sh).1⟩

/-- The configuration after the first `t` steps of the schedule `σ`. -/
def aexec (role : ι → Role) (σ : ℕ → ι) : ℕ → ACfg ι
  | 0 => ⟨{}, fun _ => .idle⟩
  | t + 1 => (aexec role σ t).step role (σ t)

/-- A process is correct in an infinite schedule iff it takes infinitely many steps. -/
def Correct (σ : ℕ → ι) (p : ι) : Prop := ∀ N, ∃ t, N ≤ t ∧ σ t = p

omit [DecidableEq ι] in
/-- A generic progress lemma: if from time `N` on, as long as `P` fails, a measure `f` never
increases and strictly decreases at every step of a correct process `p`, then `P` eventually
holds. -/
lemma exists_of_measure {σ : ℕ → ι} {p : ι} (hc : Correct σ p) (f : ℕ → ℕ) (N : ℕ)
    (P : ℕ → Prop) (hstep : ∀ t, N ≤ t → ¬ P t → f (t + 1) ≤ f t ∧ (σ t = p → f (t + 1) < f t)) :
    ∃ t, P t := by
  by_contra hne
  push Not at hne
  have mono : ∀ t, N ≤ t → ∀ d, f (t + d) ≤ f t := by
    intro t ht d
    induction d with
    | zero => rfl
    | succ d ih => exact ((hstep (t + d) (by omega) (hne _)).1).trans ih
  have key : ∀ k, ∃ t, N ≤ t ∧ f t + k ≤ f N := by
    intro k
    induction k with
    | zero => exact ⟨N, le_rfl, by simp⟩
    | succ k ih =>
      obtain ⟨t, ht, hk⟩ := ih
      obtain ⟨t', ht', hp⟩ := hc t
      have h1 := mono t ht (t' - t)
      rw [Nat.add_sub_cancel' ht'] at h1
      have h2 := (hstep t' (by omega) (hne _)).2 hp
      exact ⟨t' + 1, by omega, by omega⟩
  obtain ⟨t, -, ht⟩ := key (f N + 1)
  omega

section Exec

variable {role : ι → Role} {σ : ℕ → ι}

lemma aexec_inv (t : ℕ) : ArbInv role (aexec role σ t).sh (aexec role σ t).pc := by
  induction t with
  | zero => exact ArbInv.init
  | succ t ih => exact ih.step (σ t)

lemma aexec_pc_other {t : ℕ} {q : ι} (hq : σ t ≠ q) :
    (aexec role σ (t + 1)).pc q = (aexec role σ t).pc q := by
  simp only [aexec, ACfg.step]; exact update_of_ne (Ne.symm hq) _ _

lemma aexec_pc_self (t : ℕ) :
    (aexec role σ (t + 1)).pc (σ t) =
      (astep (role (σ t)) ((aexec role σ t).pc (σ t)) (aexec role σ t).sh).1 := by
  simp [aexec, ACfg.step]

lemma aexec_W_mono {t t' : ℕ} (htt : t ≤ t') {a : Role} (ha : (aexec role σ t).sh.W = some a) :
    (aexec role σ t').sh.W = some a := by
  induction htt with
  | refl => exact ha
  | step _ ih => exact (aexec_inv _).W_stable _ ih

/-- A process that is not at line 01 has taken a step before. -/
lemma stepped_of_ne_idle {t : ℕ} {q : ι} (h : (aexec role σ t).pc q ≠ .idle) :
    ∃ s, s < t ∧ σ s = q := by
  induction t with
  | zero => simp [aexec] at h
  | succ t ih =>
    by_cases hq : σ t = q
    · exact ⟨t, by omega, hq⟩
    · rw [aexec_pc_other hq] at h
      obtain ⟨s, hs, hs'⟩ := ih h
      exact ⟨s, by omega, hs'⟩

lemma done_W {t : ℕ} {q : ι} {a : Role} (h : (aexec role σ t).pc q = .done a) :
    (aexec role σ t).sh.W = some a :=
  ((aexec_inv t).loc q).done_W a h

end Exec

/-! ### Theorem 5 -/

variable {role : ι → Role} {σ : ℕ → ι}

/-- Theorem 5 (Agreement, Lemma 15): no two processes return different values (at any times). -/
theorem arbiter_agreement {t t' : ℕ} {p q : ι} {a b : Role}
    (hp : (aexec role σ t).pc p = .done a) (hq : (aexec role σ t').pc q = .done b) : a = b := by
  have ha := done_W hp
  have hb := done_W hq
  rcases le_total t t' with h | h
  · rw [aexec_W_mono h ha] at hb; exact Option.some.inj hb
  · rw [aexec_W_mono h hb] at ha; exact (Option.some.inj ha).symm

/-- Theorem 5 (Validity, Lemma 16, owner part): if a process has returned `owner` by time `t`,
then an owner invoked `arbitrate()` (took a step) before time `t`. -/
theorem arbiter_validity_owner {t : ℕ} {p : ι} (hp : (aexec role σ t).pc p = .done .owner) :
    ∃ s, s < t ∧ role (σ s) = .owner := by
  have hI := aexec_inv (role := role) (σ := σ) t
  have hX := hI.glob.W_owner (done_W hp)
  obtain ⟨q, hq, hq'⟩ := hI.exO (hI.glob.X_pO (by simp [hX]))
  obtain ⟨s, hs, rfl⟩ := stepped_of_ne_idle hq'
  exact ⟨s, hs, hq⟩

/-- Theorem 5 (Validity, Lemma 16, guest part): if a process has returned `guest` by time `t`,
then a guest invoked `arbitrate()` (took a step) before time `t`. -/
theorem arbiter_validity_guest {t : ℕ} {p : ι} (hp : (aexec role σ t).pc p = .done .guest) :
    ∃ s, s < t ∧ role (σ s) = .guest := by
  have hI := aexec_inv (role := role) (σ := σ) t
  obtain ⟨q, hq, hq'⟩ := hI.exG (hI.glob.W_guest (done_W hp))
  obtain ⟨s, hs, rfl⟩ := stepped_of_ne_idle hq'
  exact ⟨s, hs, hq⟩

/-- A correct process that, from some time on, is never blocked in `wait(WINNER ≠ ⊥)` with
`WINNER = ⊥`, returns. -/
lemma returns_of_not_blocked {p : ι} (hc : Correct σ p) (N : ℕ)
    (hb : ∀ t, N ≤ t → ¬ ((aexec role σ t).pc p = .gWait ∧ (aexec role σ t).sh.W = none)) :
    ∃ t a, (aexec role σ t).pc p = .done a := by
  obtain ⟨t, a, ht⟩ := exists_of_measure hc (fun t => ((aexec role σ t).pc p).rank) N
    (fun t => ∃ a, (aexec role σ t).pc p = .done a) (by
      intro t ht hnd
      push Not at hnd
      by_cases hp : σ t = p
      · subst hp
        rw [aexec_pc_self]
        have := (aexec_inv t).rank_lt (σ t) hnd (hb t ht)
        exact ⟨this.le, fun _ => this⟩
      · rw [aexec_pc_other hp]; exact ⟨le_rfl, fun h => absurd h hp⟩)
  exact ⟨t, a, ht⟩

/-- Theorem 5 (Termination, Lemmas 12–14): in every infinite schedule, if a correct owner
invokes `arbitrate()`, or only guests invoke `arbitrate()`, or some process returns, then every
correct process returns. -/
theorem arbiter_termination
    (H : (∃ o, role o = .owner ∧ Correct σ o) ∨ (∀ t, role (σ t) = .guest) ∨
      (∃ t q a, (aexec role σ t).pc q = .done a)) :
    ∀ p, Correct σ p → ∃ t a, (aexec role σ t).pc p = .done a := by
  -- once some process has returned, nobody is blocked any more
  have of_done : (∃ t q a, (aexec role σ t).pc q = .done a) →
      ∀ p, Correct σ p → ∃ t a, (aexec role σ t).pc p = .done a := by
    rintro ⟨t, q, a, hq⟩ p hp
    refine returns_of_not_blocked hp t fun t' ht' hb => ?_
    rw [aexec_W_mono ht' (done_W hq)] at hb
    simp at hb
  rcases H with ⟨o, ho, hc⟩ | hg | hd
  · refine of_done ?_
    obtain ⟨t, a, ht⟩ := returns_of_not_blocked (role := role) hc 0 fun t _ hb => by
      have := ((aexec_inv (role := role) (σ := σ) t).loc o).shape
      rw [ho, hb.1] at this
      exact this
    exact ⟨t, o, a, ht⟩
  · intro p hp
    refine returns_of_not_blocked hp 0 fun t _ hb => ?_
    have hI := aexec_inv (role := role) (σ := σ) t
    obtain ⟨q, hq, hq'⟩ := hI.exO ((hI.loc p).gWait_pO hb.1)
    obtain ⟨s, -, rfl⟩ := stepped_of_ne_idle hq'
    rw [hg s] at hq
    cases hq
  · exact of_done hd

end Podc.AsymmetricProgress.Group
