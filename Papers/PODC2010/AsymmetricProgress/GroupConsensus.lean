import Papers.PODC2010.AsymmetricProgress.Arbiter

/-!
# Consensus with group-based asymmetric progress (Section 6.2–6.4, Figure 5, Theorem 6)

Imbs, Raynal, Taubenfeld. *On Asymmetric Progress Conditions.* PODC 2010 (full version:
IRISA research report PI-1952).

**Model.** `n` asynchronous crash-stop processes `Fin n` communicating through shared memory.
The processes are partitioned into `m` ordered groups by `grp : Fin n → ℕ` (`grp q < m`; group `0`
here is group `1` of the paper, the group with the strongest progress guarantee). Process `q`
proposes `inp q` (an arbitrary value type `V`). Executions are given by an arbitrary schedule
`σ : ℕ → Fin n`; a process *participates* (invokes `propose()`) iff it takes at least one step,
is *correct* iff it takes infinitely many steps (`Correct`), and crash-stop = finitely many steps.
Each step performs one access to one shared object, local computation being folded into it.

Shared objects (`GSh`): atomic registers `VAL[g]`, `ARB_VAL[g] : Option V` (`none` = `⊥`), the
`(x, x)`-live consensus objects `GXCONS[g]` (accessed only by the at most `x` processes of group
`g`, hence wait-free: modelled as atomic consensus objects — the first proposal is decided, every
`propose` returns the decided value in one step), and the arbiters `ARBITER[g]`, `g + 1 < m`,
inlined: their registers and their `XCONS` object (accessed by the owners of `ARBITER[g]` = the
processes of group `g` only) are those of `Arbiter.lean`.

**The two tasks.** Each process runs task T1 (lines 01–18 of Figure 5) and task T2
(`wait(ARB_VAL[1] ≠ ⊥); return(ARB_VAL[1])`). The two tasks of a process are interleaved
*alternately*: the steps of a process are T1, T2, T1, T2, … (a fair interleaving; since a T2 step
is a read, this loses no reachable shared state). A T2 step reads `ARB_VAL[1]` and, if it is not
`⊥`, decides that value (the busy-wait read and the read in `return(ARB_VAL[1])` are folded into
one read). Deciding does *not* stop task T1 (this only adds executions, so the safety results
are stronger; the paper does not say whether `return` kills T1).

Program counters of T1 (`Pc`): `start` (line 02, `GXCONS[y].propose(v)`), `wVal d` (line 02,
`VAL[y] ← d`), `arb g s` (inside `ARBITER[g].arbitrate()`, at arbiter program counter `s`; lines
04 and 12), `rdV ℓ` (read `VAL[ℓ]`, lines 03, 06, 15), `rdA ℓ` (read `ARB_VAL[ℓ+1]`, lines 07,
14), `wAV ℓ x` (write `ARB_VAL[ℓ] ← x`, lines 03, 06, 07, 14, 15), `fin` (end of T1).

**Results** (Theorem 6): `group_validity`, `group_agreement` (Lemma 11), `group_termination`
(Lemma 10).
-/

namespace Podc.AsymmetricProgress.Group

open Function

variable {n : ℕ} {V : Type}

/-- An instance of the problem: `m` groups, the group of each process, the proposals. -/
structure Inst (n : ℕ) (V : Type) where
  /-- number of groups -/
  m : ℕ
  /-- the group of each process (`0` = the paper's group `1`) -/
  grp : Fin n → ℕ
  /-- the proposal of each process -/
  inp : Fin n → V
  grp_lt : ∀ q, grp q < m

/-- The shared objects of Figure 5. -/
structure GSh (V : Type) where
  /-- the value decided by `GXCONS[g]` (`none`: no proposal yet) -/
  gx : ℕ → Option V
  /-- `VAL[g]` -/
  val : ℕ → Option V
  /-- `ARB_VAL[g]` -/
  av : ℕ → Option V
  /-- the shared objects of `ARBITER[g]` -/
  arb : ℕ → ArbSh

/-- Program counters of task T1 (Figure 5, with Figure 4 inlined). -/
inductive Pc (V : Type)
  /-- line 02: `GXCONS[y].propose(v)` -/
  | start
  /-- line 02: `VAL[y] ← d` -/
  | wVal (d : V)
  /-- inside `ARBITER[g].arbitrate()` (line 04 or 12) -/
  | arb (g : ℕ) (s : APc)
  /-- read `VAL[ℓ]` (lines 03, 06, 15) -/
  | rdV (ℓ : ℕ)
  /-- read `ARB_VAL[ℓ + 1]` (lines 07, 14) -/
  | rdA (ℓ : ℕ)
  /-- `ARB_VAL[ℓ] ← x` (lines 03, 06, 07, 14, 15) -/
  | wAV (ℓ : ℕ) (x : Option V)
  /-- task T1 has terminated -/
  | fin

/-- Where T1 continues inside or after `ARBITER[g]` (lines 05–07 and 13–15: the winner
`owner` leads to `VAL[g]`, the winner `guest` to `ARB_VAL[g + 1]`). -/
def afterArb (g : ℕ) : APc → Pc V
  | .done .owner => .rdV g
  | .done .guest => .rdA g
  | .idle => .arb g .idle
  | .oRead => .arb g .oRead
  | .oProp b => .arb g (.oProp b)
  | .oWrite w => .arb g (.oWrite w)
  | .gRead => .arb g .gRead
  | .gWait => .arb g .gWait
  | .gWrite => .arb g .gWrite
  | .ret => .arb g .ret

/-- Where T1 continues after writing `ARB_VAL[ℓ]`: the next iteration of the loop of lines
10–17 (`ARBITER[ℓ - 1].arbitrate(guest)`), or the end of T1. -/
def nextAfter : ℕ → Pc V
  | 0 => .fin
  | k + 1 => .arb k .idle

/-- One step of task T1 of a process of group `y` with proposal `v`. -/
def t1 (m y : ℕ) (v : V) : Pc V → GSh V → Pc V × GSh V
  | .start, sh =>
    (.wVal ((sh.gx y).getD v), { sh with gx := update sh.gx y (some ((sh.gx y).getD v)) })
  | .wVal d, sh =>
    (if y + 1 < m then .arb y .idle else .rdV y, { sh with val := update sh.val y (some d) })
  | .arb g s, sh =>
    (afterArb g (astep (if g = y then .owner else .guest) s (sh.arb g)).1,
      { sh with arb := update sh.arb g (astep (if g = y then .owner else .guest) s (sh.arb g)).2 })
  | .rdV ℓ, sh => (.wAV ℓ (sh.val ℓ), sh)
  | .rdA ℓ, sh => (.wAV ℓ (sh.av (ℓ + 1)), sh)
  | .wAV ℓ x, sh => (nextAfter ℓ, { sh with av := update sh.av ℓ x })
  | .fin, sh => (.fin, sh)

/-- A configuration: shared objects, T1 program counters, whose turn it is (`t2 q = true`: the
next step of `q` is a T2 step), decisions. -/
structure GCfg (n : ℕ) (V : Type) where
  /-- shared objects -/
  sh : GSh V
  /-- program counters of task T1 -/
  pc : Fin n → Pc V
  /-- whether the next step of the process belongs to task T2 -/
  t2 : Fin n → Bool
  /-- the decided value (`return` of task T2) -/
  dec : Fin n → Option V

/-- The initial configuration. -/
def GCfg.init : GCfg n V :=
  ⟨⟨fun _ => none, fun _ => none, fun _ => none, fun _ => {}⟩, fun _ => .start, fun _ => false,
    fun _ => none⟩

/-- One step of process `p`: a T2 step (read `ARB_VAL[1]`, decide it if it is not `⊥`) or a T1
step, alternately. -/
def GCfg.step (A : Inst n V) (c : GCfg n V) (p : Fin n) : GCfg n V :=
  if c.t2 p then
    { c with t2 := update c.t2 p false, dec := update c.dec p ((c.dec p).or (c.sh.av 0)) }
  else
    { c with sh := (t1 A.m (A.grp p) (A.inp p) (c.pc p) c.sh).2,
             pc := update c.pc p (t1 A.m (A.grp p) (A.inp p) (c.pc p) c.sh).1,
             t2 := update c.t2 p true }

/-- The configuration after the first `t` steps of the schedule `σ`. -/
def gexec (A : Inst n V) (σ : ℕ → Fin n) : ℕ → GCfg n V
  | 0 => GCfg.init
  | t + 1 => (gexec A σ t).step A (σ t)

/-! ### The value of `ARB_VAL[ℓ]` -/

/-- The only value `ARB_VAL[ℓ]` can take (Lemma 11): `VAL[ℓ]` if the owners won
`ARBITER[ℓ]` (or `ℓ` is the last group), the value of `ARB_VAL[ℓ + 1]` if the guests won. -/
def Val (m : ℕ) (sh : GSh V) (ℓ : ℕ) : Option V :=
  if _h : ℓ + 1 < m then
    match (sh.arb ℓ).W with
    | some .owner => sh.gx ℓ
    | some .guest => Val m sh (ℓ + 1)
    | none => none
  else sh.gx ℓ
termination_by m - ℓ

section Val

variable {m : ℕ} {sh sh' : GSh V} {ℓ : ℕ}

lemma Val_owner (h : ℓ + 1 < m) (hW : (sh.arb ℓ).W = some .owner) : Val m sh ℓ = sh.gx ℓ := by
  rw [Val]; simp only [h, ↓reduceDIte, hW]

lemma Val_guest (h : ℓ + 1 < m) (hW : (sh.arb ℓ).W = some .guest) :
    Val m sh ℓ = Val m sh (ℓ + 1) := by
  rw [Val]; simp only [h, ↓reduceDIte, hW]

lemma Val_none (h : ℓ + 1 < m) (hW : (sh.arb ℓ).W = none) : Val m sh ℓ = none := by
  rw [Val]; simp only [h, ↓reduceDIte, hW]

lemma Val_last (h : ¬ ℓ + 1 < m) : Val m sh ℓ = sh.gx ℓ := by
  rw [Val]; simp only [h, ↓reduceDIte]

/-- `sh'` extends `sh`: no defined value of `GXCONS`, `VAL`, `ARB_VAL`, `WINNER` changes. -/
structure Ext (m : ℕ) (sh sh' : GSh V) : Prop where
  gx : ∀ g x, sh.gx g = some x → sh'.gx g = some x
  val : ∀ g x, sh.val g = some x → sh'.val g = some x
  av : ∀ g x, sh.av g = some x → sh'.av g = some x
  W : ∀ g a, g + 1 < m → (sh.arb g).W = some a → (sh'.arb g).W = some a

lemma Ext.refl : Ext m sh sh := ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ _ h => h⟩

lemma Ext.trans {sh'' : GSh V} (h : Ext m sh sh') (h' : Ext m sh' sh'') : Ext m sh sh'' :=
  ⟨fun g x hx => h'.gx g x (h.gx g x hx), fun g x hx => h'.val g x (h.val g x hx),
    fun g x hx => h'.av g x (h.av g x hx), fun g a hg hx => h'.W g a hg (h.W g a hg hx)⟩

lemma Val_ext (hE : Ext m sh sh') : ∀ ℓ x, Val m sh ℓ = some x → Val m sh' ℓ = some x := by
  suffices H : ∀ d ℓ, m - ℓ ≤ d → ∀ x, Val m sh ℓ = some x → Val m sh' ℓ = some x from
    fun ℓ => H _ ℓ le_rfl
  intro d
  induction d with
  | zero =>
    intro ℓ hd x hx
    rw [Val_last (by omega)] at hx ⊢
    exact hE.gx _ _ hx
  | succ d ih =>
    intro ℓ hd x hx
    by_cases h : ℓ + 1 < m
    · rcases hW : (sh.arb ℓ).W with _ | _ | _
      · rw [Val_none h hW] at hx; cases hx
      · rw [Val_owner h hW] at hx; rw [Val_owner h (hE.W _ _ h hW)]; exact hE.gx _ _ hx
      · rw [Val_guest h hW] at hx; rw [Val_guest h (hE.W _ _ h hW)]
        exact ih (ℓ + 1) (by omega) x hx
    · rw [Val_last h] at hx ⊢
      exact hE.gx _ _ hx

/-- Validity core: a value of `Val` was decided by some `GXCONS[g]`. -/
lemma Val_gx : ∀ ℓ x, Val m sh ℓ = some x → ∃ g, sh.gx g = some x := by
  suffices H : ∀ d ℓ, m - ℓ ≤ d → ∀ x, Val m sh ℓ = some x → ∃ g, sh.gx g = some x from
    fun ℓ => H _ ℓ le_rfl
  intro d
  induction d with
  | zero =>
    intro ℓ hd x hx
    rw [Val_last (by omega)] at hx
    exact ⟨ℓ, hx⟩
  | succ d ih =>
    intro ℓ hd x hx
    by_cases h : ℓ + 1 < m
    · rcases hW : (sh.arb ℓ).W with _ | _ | _
      · rw [Val_none h hW] at hx; cases hx
      · rw [Val_owner h hW] at hx; exact ⟨ℓ, hx⟩
      · rw [Val_guest h hW] at hx; exact ih (ℓ + 1) (by omega) x hx
    · rw [Val_last h] at hx
      exact ⟨ℓ, hx⟩

end Val


/-! ### Projection onto one arbiter -/

/-- The program counter *in `ARBITER[g]`* of a process of group `y` at T1 program counter `s`:
`idle` before it invokes `ARBITER[g]` (forever if `y < g`: it never invokes it), the inner
program counter while inside, and `done WINNER` after the return. -/
def proj (g : ℕ) (W : Option Role) (y : ℕ) : Pc V → APc
  | .start => .idle
  | .wVal _ => .idle
  | .arb g' s =>
    if y < g then .idle else if g' = g then s else if g' < g then .done (W.getD .owner) else .idle
  | .rdV ℓ => if y < g then .idle else if ℓ ≤ g then .done (W.getD .owner) else .idle
  | .rdA ℓ => if y < g then .idle else if ℓ ≤ g then .done (W.getD .owner) else .idle
  | .wAV ℓ _ => if y < g then .idle else if ℓ ≤ g then .done (W.getD .owner) else .idle
  | .fin => if y < g then .idle else .done (W.getD .owner)

/-- The role of process `q` in `ARBITER[g]`: owner iff it belongs to group `g`. -/
def roleAt (A : Inst n V) (g : ℕ) (q : Fin n) : Role := if g = A.grp q then .owner else .guest

/-- The arbiter program counters of all processes for `ARBITER[g]`. -/
def projCfg (A : Inst n V) (g : ℕ) (sh : GSh V) (pc : Fin n → Pc V) (q : Fin n) : APc :=
  proj g (sh.arb g).W (A.grp q) (pc q)

/-- `Wrote y s k`: a process of group `y` at T1 program counter `s` has already written
`ARB_VAL[k]`. -/
def Wrote (y : ℕ) : Pc V → ℕ → Prop
  | .start, _ => False
  | .wVal _, _ => False
  | .arb g _, k => g < k ∧ k ≤ y
  | .rdV ℓ, k => ℓ < k ∧ k ≤ y
  | .rdA ℓ, k => ℓ < k ∧ k ≤ y
  | .wAV ℓ _, k => ℓ < k ∧ k ≤ y
  | .fin, k => k ≤ y

/-- Well-formedness of a T1 program counter of a process of group `y`. -/
def PcOK (m y : ℕ) : Pc V → Prop
  | .start => True
  | .wVal _ => True
  | .arb g s => g ≤ y ∧ g + 1 < m ∧ ∀ a, s ≠ .done a
  | .rdV ℓ => ℓ ≤ y
  | .rdA ℓ => ℓ ≤ y
  | .wAV ℓ _ => ℓ ≤ y
  | .fin => True

/-- The per-process part of the invariant (process of group `y` at T1 program counter `s`). -/
structure GLoc (m : ℕ) (sh : GSh V) (y : ℕ) (s : Pc V) : Prop where
  wVal_gx : ∀ d, s = .wVal d → sh.gx y = some d
  val_ne : s ≠ .start → (∀ d, s ≠ .wVal d) → sh.val y ≠ none
  wAV : ∀ ℓ x, s = .wAV ℓ x → ∃ z, x = some z ∧ Val m sh ℓ = some z
  rdV : ∀ ℓ, s = .rdV ℓ → sh.val ℓ ≠ none ∧ (ℓ + 1 < m → (sh.arb ℓ).W = some .owner)
  rdA : ∀ ℓ, s = .rdA ℓ → ℓ + 1 < m ∧ (sh.arb ℓ).W = some .guest ∧ sh.av (ℓ + 1) ≠ none
  wrote : ∀ k, Wrote y s k → sh.av k ≠ none
  ok : PcOK m y s

/-- The inductive invariant of the algorithm of Figure 5 (task T1). -/
structure GInv (A : Inst n V) (sh : GSh V) (pc : Fin n → Pc V) : Prop where
  /-- every inlined arbiter satisfies the arbiter invariant -/
  arb : ∀ g, g + 1 < A.m → ArbInv (roleAt A g) (sh.arb g) (projCfg A g sh pc)
  gx_wit : ∀ g x, sh.gx g = some x → ∃ q, A.grp q = g ∧ A.inp q = x ∧ pc q ≠ .start
  val_gx : ∀ g x, sh.val g = some x → sh.gx g = some x
  /-- Lemma 11: `ARB_VAL[ℓ]` only takes the value `Val ℓ` -/
  av_Val : ∀ ℓ x, sh.av ℓ = some x → Val A.m sh ℓ = some x
  loc : ∀ q, GLoc A.m sh (A.grp q) (pc q)

section Lemmas

variable {m : ℕ} {sh sh' : GSh V} {y g : ℕ} {W W' : Option Role}

lemma proj_ne_idle {s : Pc V} (h : proj g W y s ≠ .idle) : s ≠ .start ∧ ∀ d, s ≠ .wVal d := by
  cases s <;> simp_all [proj]

lemma le_of_proj_ne_idle {s : Pc V} (h : proj g W y s ≠ .idle) : g ≤ y := by
  by_contra hy
  cases s <;> simp_all [proj]

lemma wrote_of_proj {s : Pc V} (hok : PcOK m y s) (h : proj g W y s ≠ .idle) (hg : g < y) :
    Wrote y s (g + 1) := by
  cases s <;> simp only [proj, PcOK, Wrote] at h hok ⊢ <;> (try simp at h) <;>
    (try split_ifs at h) <;> (try simp at h) <;> omega

lemma proj_W (s : Pc V) :
    proj g W' y s = proj g W y s ∨
      (proj g W y s = .done (W.getD .owner) ∧ proj g W' y s = .done (W'.getD .owner)) := by
  cases s <;> simp only [proj] <;> (try split_ifs) <;> simp

lemma GLoc.ext {s : Pc V} (h : GLoc m sh y s) (hE : Ext m sh sh') : GLoc m sh' y s := by
  refine ⟨fun d hd => hE.gx _ _ (h.wVal_gx d hd), fun h1 h2 => ?_, fun ℓ x hx => ?_,
    fun ℓ hℓ => ?_, fun ℓ hℓ => ?_, fun k hk => ?_, h.ok⟩
  · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (h.val_ne h1 h2)
    simp [hE.val _ _ hz]
  · obtain ⟨z, hz, hz'⟩ := h.wAV ℓ x hx
    exact ⟨z, hz, Val_ext hE _ _ hz'⟩
  · obtain ⟨h1, h2⟩ := h.rdV ℓ hℓ
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 h1
    exact ⟨by simp [hE.val _ _ hz], fun hm => hE.W _ _ hm (h2 hm)⟩
  · obtain ⟨h1, h2, h3⟩ := h.rdA ℓ hℓ
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 h3
    exact ⟨h1, hE.W _ _ h1 h2, by simp [hE.av _ _ hz]⟩
  · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (h.wrote k hk)
    simp [hE.av _ _ hz]

variable {A : Inst n V} {pc : Fin n → Pc V}

lemma GInv.upd (h : GInv A sh pc) {p : Fin n} {s' : Pc V} (hE : Ext A.m sh sh')
    (hp : GLoc A.m sh' (A.grp p) s') (hst : s' ≠ .start)
    (harb : ∀ g, g + 1 < A.m → ArbInv (roleAt A g) (sh'.arb g) (projCfg A g sh' (update pc p s')))
    (hgx : ∀ g x, sh'.gx g = some x → sh.gx g = some x ∨ (A.grp p = g ∧ A.inp p = x))
    (hval : ∀ g x, sh'.val g = some x → sh'.gx g = some x)
    (hav : ∀ ℓ x, sh'.av ℓ = some x → Val A.m sh' ℓ = some x) :
    GInv A sh' (update pc p s') := by
  refine ⟨harb, fun g x hx => ?_, hval, hav, fun q => ?_⟩
  · rcases hgx g x hx with h' | ⟨h1, h2⟩
    · obtain ⟨q, hq1, hq2, hq3⟩ := h.gx_wit g x h'
      refine ⟨q, hq1, hq2, ?_⟩
      rcases eq_or_ne q p with rfl | hqp
      · simpa using hst
      · rwa [update_of_ne hqp]
    · exact ⟨p, h1, h2, by simpa using hst⟩
  · rcases eq_or_ne q p with rfl | hqp
    · simpa using hp
    · rw [update_of_ne hqp]; exact (h.loc q).ext hE

/-- Frame lemma for the arbiters not accessed by a step. -/
lemma arb_frame {p : Fin n} {s' : Pc V}
    (h : ArbInv (roleAt A g) (sh.arb g) (projCfg A g sh pc)) (hsh : sh'.arb g = sh.arb g)
    (hp : proj g (sh.arb g).W (A.grp p) s' = proj g (sh.arb g).W (A.grp p) (pc p)) :
    ArbInv (roleAt A g) (sh'.arb g) (projCfg A g sh' (update pc p s')) := by
  have : projCfg A g sh' (update pc p s') = projCfg A g sh pc := by
    funext q
    rcases eq_or_ne q p with rfl | hqp
    · simp [projCfg, hsh, hp]
    · simp [projCfg, hsh, update_of_ne hqp]
  rw [this, hsh]; exact h

lemma proj_afterArb_other {g' : ℕ} (hne : g' ≠ g) (r r0 : APc) :
    proj g W y (afterArb g' r : Pc V) = proj g W y (.arb g' r0 : Pc V) := by
  cases r <;> try (rename_i a; cases a)
  all_goals simp only [afterArb, proj, hne, ite_false]
  all_goals split_ifs <;> first | rfl | omega

lemma proj_afterArb_self (hy : g ≤ y) (r : APc) :
    proj g W y (afterArb g r : Pc V) = match r with
      | .done _ => .done (W.getD .owner)
      | r => r := by
  have : ¬ y < g := by omega
  cases r <;> try (rename_i a; cases a)
  all_goals simp [afterArb, proj, this]

end Lemmas


section Step

variable {A : Inst n V} {sh : GSh V} {pc : Fin n → Pc V}

lemma GInv.init : GInv A (GCfg.init : GCfg n V).sh (GCfg.init : GCfg n V).pc := by
  refine ⟨fun g _ => ?_, fun g x hx => by simp [GCfg.init] at hx,
    fun g x hx => by simp [GCfg.init] at hx, fun g x hx => by simp [GCfg.init] at hx,
    fun q => ⟨by simp [GCfg.init], by simp [GCfg.init], by simp [GCfg.init], by simp [GCfg.init],
      by simp [GCfg.init], by simp [GCfg.init, Wrote], by simp [GCfg.init, PcOK]⟩⟩
  have : projCfg A g (GCfg.init : GCfg n V).sh (GCfg.init : GCfg n V).pc = fun _ => .idle := by
    funext q; simp [projCfg, GCfg.init, proj]
  rw [this]
  exact ArbInv.init

/-- The invariant is preserved by every T1 step, and T1 steps only extend the shared state. -/
theorem GInv.t1_step (h : GInv A sh pc) (p : Fin n) :
    GInv A (t1 A.m (A.grp p) (A.inp p) (pc p) sh).2
      (update pc p (t1 A.m (A.grp p) (A.inp p) (pc p) sh).1) ∧
    Ext A.m sh (t1 A.m (A.grp p) (A.inp p) (pc p) sh).2 := by
  have hl := h.loc p
  cases hs : pc p with
  | start =>
    simp only [t1]
    have hE : Ext A.m sh
        { sh with gx := update sh.gx (A.grp p) (some ((sh.gx (A.grp p)).getD (A.inp p))) } := by
      refine ⟨fun g x hx => ?_, fun _ _ h => h, fun _ _ h => h, fun _ _ _ h => h⟩
      by_cases hg : g = A.grp p
      · subst hg; simp [hx]
      · simp [update_of_ne hg, hx]
    refine ⟨h.upd hE ⟨fun d hd => ?_, by simp, by simp, by simp, by simp, by simp [Wrote],
      by simp [PcOK]⟩ (by simp) (fun g hg => arb_frame (h.arb g hg) rfl (by rw [hs]; simp [proj]))
      (fun g x hx => ?_) (fun g x hx => hE.gx _ _ (h.val_gx g x hx))
      (fun ℓ x hx => Val_ext hE _ _ (h.av_Val ℓ x hx)), hE⟩
    · simp only [Pc.wVal.injEq] at hd; subst hd; simp
    · by_cases hg : g = A.grp p
      · subst hg
        rcases hz : sh.gx (A.grp p) with _ | z
        · simp [hz] at hx; exact Or.inr ⟨rfl, hx⟩
        · simp [hz] at hx; exact Or.inl (by rw [hx])
      · simp [update_of_ne hg] at hx; exact Or.inl hx
  | wVal d =>
    simp only [t1]
    rw [hs] at hl
    have hgd := hl.wVal_gx d rfl
    have hE : Ext A.m sh { sh with val := update sh.val (A.grp p) (some d) } := by
      refine ⟨fun _ _ h => h, fun g x hx => ?_, fun _ _ h => h, fun _ _ _ h => h⟩
      by_cases hg : g = A.grp p
      · subst hg
        have := h.val_gx _ _ hx
        rw [hgd] at this
        simp [Option.some.inj this]
      · simp [update_of_ne hg, hx]
    have hval : ∀ g x, (update sh.val (A.grp p) (some d)) g = some x → sh.gx g = some x := by
      intro g x hx
      by_cases hg : g = A.grp p
      · subst hg; simp at hx; rw [← hx]; exact hgd
      · rw [update_of_ne hg] at hx; exact h.val_gx g x hx
    have hy := A.grp_lt p
    split_ifs with hm
    · refine ⟨h.upd hE ⟨by simp, fun _ _ => by simp, by simp, by simp, by simp,
        fun k hk => by simp [Wrote] at hk; omega, by simp [PcOK, hm]⟩ (by simp)
        (fun g hg => arb_frame (h.arb g hg) rfl ?_) (fun g x hx => Or.inl hx) hval
        (fun ℓ x hx => Val_ext hE _ _ (h.av_Val ℓ x hx)), hE⟩
      rw [hs]; simp only [proj]; split_ifs <;> rfl
    · refine ⟨h.upd hE ⟨by simp, fun _ _ => by simp, by simp,
        fun ℓ hℓ => by simp at hℓ; subst hℓ; exact ⟨by simp, fun h' => absurd h' hm⟩, by simp,
        fun k hk => by simp [Wrote] at hk; omega, by simp [PcOK]⟩ (by simp)
        (fun g hg => arb_frame (h.arb g hg) rfl ?_) (fun g x hx => Or.inl hx) hval
        (fun ℓ x hx => Val_ext hE _ _ (h.av_Val ℓ x hx)), hE⟩
      rw [hs]; simp only [proj]; split_ifs <;> first | rfl | omega
  | arb g s =>
    simp only [t1]
    rw [hs] at hl
    obtain ⟨hgy, hgm, hsd⟩ := hl.ok
    have Ig := h.arb g hgm
    have hPp : projCfg A g sh pc p = s := by
      simp [projCfg, hs, proj, show ¬ A.grp p < g by omega]
    have hrole : roleAt A g p = if g = A.grp p then Role.owner else .guest := rfl
    have Ig' := Ig.step p
    have hWs : ∀ a, (sh.arb g).W = some a →
        (astep (roleAt A g p) (projCfg A g sh pc p) (sh.arb g)).2.W = some a :=
      fun a ha => Ig.W_stable p ha
    rw [hPp, hrole] at Ig' hWs
    generalize astep (if g = A.grp p then Role.owner else .guest) s (sh.arb g) = st at Ig' hWs ⊢
    obtain ⟨s1, A1⟩ := st
    simp only at Ig' hWs ⊢
    have hE : Ext A.m sh { sh with arb := update sh.arb g A1 } := by
      refine ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun g' a _ ha => ?_⟩
      by_cases hg' : g' = g
      · subst hg'; simp only [update_self]; exact hWs a ha
      · simp only [update_of_ne hg']; exact ha
    have hproj : projCfg A g { sh with arb := update sh.arb g A1 } (update pc p (afterArb g s1)) =
        update (projCfg A g sh pc) p s1 := by
      funext q
      rcases eq_or_ne q p with rfl | hqp
      · simp only [projCfg, update_self]
        rw [proj_afterArb_self hgy]
        cases s1 with
        | done a =>
          have := (Ig'.loc q).done_W a (by simp)
          simp [this]
        | _ => rfl
      · simp only [projCfg, update_self, update_of_ne hqp]
        rcases proj_W (W := (sh.arb g).W) (W' := A1.W) (y := A.grp q) (g := g) (pc q)
          with h' | ⟨h1, h2⟩
        · exact h'
        · have := (Ig.loc q).done_W _ h1
          rw [h2, h1, hWs _ this, Option.getD_some]
    have harb : ∀ g', g' + 1 < A.m → ArbInv (roleAt A g') ({ sh with arb := update sh.arb g A1 }.arb g')
        (projCfg A g' { sh with arb := update sh.arb g A1 } (update pc p (afterArb g s1))) := by
      intro g' hg'
      by_cases hgg : g' = g
      · subst hgg
        rw [hproj]; simp only [update_self]; exact Ig'
      · exact arb_frame (h.arb g' hg') (update_of_ne hgg _ _)
          (by rw [hs]; exact proj_afterArb_other (Ne.symm hgg) s1 s)
    have hst : (afterArb g s1 : Pc V) ≠ .start := by
      cases s1 <;> try (rename_i a; cases a)
      all_goals simp [afterArb]
    refine ⟨h.upd hE ?_ hst harb (fun g x hx => Or.inl hx)
      (fun g x hx => hE.gx _ _ (h.val_gx g x hx)) (fun ℓ x hx => Val_ext hE _ _ (h.av_Val ℓ x hx)),
      hE⟩
    have hvne : sh.val (A.grp p) ≠ none := hl.val_ne (by simp) (by simp)
    cases s1 with
    | done a =>
      have hW := (Ig'.loc p).done_W a (by simp)
      cases a with
      | owner =>
        refine ⟨by simp [afterArb], fun _ _ => hvne, by simp [afterArb], fun ℓ hℓ => ?_,
          by simp [afterArb], fun k hk => hl.wrote k hk, hgy⟩
        simp only [afterArb, Pc.rdV.injEq] at hℓ; subst hℓ
        refine ⟨?_, fun _ => by simpa using hW⟩
        by_cases hgp : g = A.grp p
        · rw [hgp]; exact hvne
        · obtain ⟨q, hq1, hq2⟩ := Ig'.exO (Ig'.glob.X_pO (by rw [Ig'.glob.W_owner hW]; simp))
          have hq : g = A.grp q := by
            unfold roleAt at hq1; split_ifs at hq1 with h'; exact h'
          have hqp : q ≠ p := by rintro rfl; exact hgp hq
          rw [update_of_ne hqp] at hq2
          obtain ⟨h1, h2⟩ := proj_ne_idle hq2
          rw [hq]; exact (h.loc q).val_ne h1 h2
      | guest =>
        refine ⟨by simp [afterArb], fun _ _ => hvne, by simp [afterArb], by simp [afterArb],
          fun ℓ hℓ => ?_, fun k hk => hl.wrote k hk, hgy⟩
        simp only [afterArb, Pc.rdA.injEq] at hℓ; subst hℓ
        refine ⟨hgm, by simpa using hW, ?_⟩
        obtain ⟨q, hq1, hq2⟩ := Ig'.exG (Ig'.glob.W_guest hW)
        have hq : g ≠ A.grp q := by
          unfold roleAt at hq1; split_ifs at hq1 with h'; exact h'
        rcases eq_or_ne q p with rfl | hqp
        · exact hl.wrote (g + 1) ⟨by omega, by omega⟩
        · rw [update_of_ne hqp] at hq2
          have hle := le_of_proj_ne_idle hq2
          exact (h.loc q).wrote _ (wrote_of_proj (h.loc q).ok hq2 (by omega))
    | _ =>
      exact ⟨by simp [afterArb], fun _ _ => hvne, by simp [afterArb], by simp [afterArb],
        by simp [afterArb], fun k hk => hl.wrote k hk, ⟨hgy, hgm, by simp⟩⟩
  | rdV ℓ =>
    simp only [t1]
    rw [hs] at hl
    obtain ⟨hv, hW⟩ := hl.rdV ℓ rfl
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hv
    have hgz := h.val_gx _ _ hz
    have hVal : Val A.m sh ℓ = some z := by
      by_cases hm : ℓ + 1 < A.m
      · rw [Val_owner hm (hW hm)]; exact hgz
      · rw [Val_last hm]; exact hgz
    refine ⟨h.upd Ext.refl ⟨by simp, fun _ _ => hl.val_ne (by simp) (by simp),
      fun ℓ' x hx => ?_, by simp, by simp, fun k hk => hl.wrote k hk, hl.ok⟩ (by simp)
      (fun g hg => arb_frame (h.arb g hg) rfl (by rw [hs]; simp [proj]))
      (fun g x hx => Or.inl hx) h.val_gx h.av_Val, Ext.refl⟩
    simp only [Pc.wAV.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
    exact ⟨z, hz, hVal⟩
  | rdA ℓ =>
    simp only [t1]
    rw [hs] at hl
    obtain ⟨hm, hW, hv⟩ := hl.rdA ℓ rfl
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hv
    have hVal : Val A.m sh ℓ = some z := by
      rw [Val_guest hm hW]; exact h.av_Val _ _ hz
    refine ⟨h.upd Ext.refl ⟨by simp, fun _ _ => hl.val_ne (by simp) (by simp),
      fun ℓ' x hx => ?_, by simp, by simp, fun k hk => hl.wrote k hk, hl.ok⟩ (by simp)
      (fun g hg => arb_frame (h.arb g hg) rfl (by rw [hs]; simp [proj]))
      (fun g x hx => Or.inl hx) h.val_gx h.av_Val, Ext.refl⟩
    simp only [Pc.wAV.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx
    exact ⟨z, hz, hVal⟩
  | wAV ℓ x =>
    simp only [t1]
    rw [hs] at hl
    obtain ⟨z, rfl, hVal⟩ := hl.wAV ℓ x rfl
    have hE : Ext A.m sh { sh with av := update sh.av ℓ (some z) } := by
      refine ⟨fun _ _ h => h, fun _ _ h => h, fun g x hx => ?_, fun _ _ _ h => h⟩
      by_cases hg : g = ℓ
      · subst hg
        have := h.av_Val _ _ hx
        rw [hVal] at this
        simp [Option.some.inj this]
      · simp [update_of_ne hg, hx]
    have hav : ∀ ℓ' x', (update sh.av ℓ (some z)) ℓ' = some x' →
        Val A.m { sh with av := update sh.av ℓ (some z) } ℓ' = some x' := by
      intro ℓ' x' hx
      by_cases hg : ℓ' = ℓ
      · subst hg; simp at hx; subst hx; exact Val_ext hE _ _ hVal
      · rw [update_of_ne hg] at hx; exact Val_ext hE _ _ (h.av_Val _ _ hx)
    have hok : ℓ ≤ A.grp p := hl.ok
    have hy := A.grp_lt p
    have hwr : ∀ k, ℓ ≤ k → k ≤ A.grp p → (update sh.av ℓ (some z)) k ≠ none := by
      intro k hk1 hk2
      by_cases hk : k = ℓ
      · subst hk; simp
      · rw [update_of_ne hk]; exact hl.wrote k ⟨by omega, hk2⟩
    have hvne : sh.val (A.grp p) ≠ none := hl.val_ne (by simp) (by simp)
    cases ℓ with
    | zero =>
      refine ⟨h.upd hE ⟨by simp [nextAfter], fun _ _ => hvne, by simp [nextAfter],
        by simp [nextAfter], by simp [nextAfter],
        fun k hk => hwr k (by omega) (by simpa [nextAfter, Wrote] using hk),
        by simp [nextAfter, PcOK]⟩ (by simp [nextAfter])
        (fun g hg => arb_frame (h.arb g hg) rfl ?_) (fun g x hx => Or.inl hx)
        (fun g x hx => hE.gx _ _ (h.val_gx g x hx)) hav, hE⟩
      rw [hs]; simp only [nextAfter, proj]; split_ifs <;> first | rfl | omega
    | succ k =>
      refine ⟨h.upd hE ⟨by simp [nextAfter], fun _ _ => hvne, by simp [nextAfter],
        by simp [nextAfter], by simp [nextAfter],
        fun k' hk => ?_, ⟨by omega, by omega, by simp⟩⟩ (by simp [nextAfter])
        (fun g hg => arb_frame (h.arb g hg) rfl ?_) (fun g x hx => Or.inl hx)
        (fun g x hx => hE.gx _ _ (h.val_gx g x hx)) hav, hE⟩
      · simp only [nextAfter, Wrote] at hk
        exact hwr k' (by omega) hk.2
      · rw [hs]; simp only [nextAfter, proj]; split_ifs <;> first | rfl | omega
  | fin =>
    simp only [t1]
    rw [← hs, update_eq_self]
    exact ⟨h, Ext.refl⟩

end Step


/-! ### Executions -/

section Exec

variable {A : Inst n V} {σ : ℕ → Fin n}

/-- The full invariant: `GInv` and "a decided value is the value of `ARB_VAL[1]`". -/
def FInv (A : Inst n V) (c : GCfg n V) : Prop :=
  GInv A c.sh c.pc ∧ ∀ q v, c.dec q = some v → c.sh.av 0 = some v

lemma FInv.step {c : GCfg n V} (h : FInv A c) (p : Fin n) :
    FInv A (c.step A p) ∧ Ext A.m c.sh (c.step A p).sh := by
  obtain ⟨hG, hd⟩ := h
  unfold GCfg.step
  split_ifs with ht
  · refine ⟨⟨hG, fun q v hv => ?_⟩, Ext.refl⟩
    rcases eq_or_ne q p with rfl | hqp
    · simp only [update_self] at hv
      rcases hdq : c.dec q with _ | w
      · simpa [hdq] using hv
      · simp [hdq] at hv; subst hv; exact hd _ _ hdq
    · simp only [update_of_ne hqp] at hv; exact hd q v hv
  · obtain ⟨hG', hE⟩ := hG.t1_step p
    exact ⟨⟨hG', fun q v hv => hE.av _ _ (hd q v hv)⟩, hE⟩

lemma GCfg.step_of_t2 {c : GCfg n V} {p : Fin n} (h : c.t2 p = true) :
    c.step A p =
      { c with t2 := update c.t2 p false
               dec := update c.dec p ((c.dec p).or (c.sh.av 0)) } := by
  simp [GCfg.step, h]

lemma GCfg.step_of_t1 {c : GCfg n V} {p : Fin n} (h : c.t2 p = false) :
    c.step A p =
      { c with sh := (t1 A.m (A.grp p) (A.inp p) (c.pc p) c.sh).2
               pc := update c.pc p (t1 A.m (A.grp p) (A.inp p) (c.pc p) c.sh).1
               t2 := update c.t2 p true } := by
  simp [GCfg.step, h]

lemma gexec_inv (t : ℕ) : FInv A (gexec A σ t) := by
  induction t with
  | zero =>
    refine ⟨GInv.init, fun q v hv => ?_⟩
    simp [gexec, GCfg.init] at hv
  | succ t ih => exact (ih.step (σ t)).1

lemma gexec_ext {t t' : ℕ} (h : t ≤ t') : Ext A.m (gexec A σ t).sh (gexec A σ t').sh := by
  induction h with
  | refl => exact Ext.refl
  | step _ ih => exact ih.trans ((gexec_inv _).step _).2

lemma gexec_other {t : ℕ} {q : Fin n} (hq : σ t ≠ q) :
    (gexec A σ (t + 1)).pc q = (gexec A σ t).pc q ∧
    (gexec A σ (t + 1)).t2 q = (gexec A σ t).t2 q ∧
    (gexec A σ (t + 1)).dec q = (gexec A σ t).dec q := by
  simp only [gexec, GCfg.step]
  split_ifs <;> simp [update_of_ne (Ne.symm hq)]

/-- A process whose T1 is past line 01 has taken a step before. -/
lemma stepped_of_ne_start {t : ℕ} {q : Fin n} (h : (gexec A σ t).pc q ≠ .start) :
    ∃ s, s < t ∧ σ s = q := by
  induction t with
  | zero => simp [gexec, GCfg.init] at h
  | succ t ih =>
    by_cases hq : σ t = q
    · exact ⟨t, by omega, hq⟩
    · rw [(gexec_other hq).1] at h
      obtain ⟨s, hs, hs'⟩ := ih h
      exact ⟨s, by omega, hs'⟩

end Exec

/-! ### Theorem 6: validity and agreement -/

section Safety

variable {A : Inst n V} {σ : ℕ → Fin n}

/-- Theorem 6 (Validity, "left to the reader" in the paper): a decided value is the proposal of a
process that invoked `propose()` (took a step) before the decision. -/
theorem group_validity {t : ℕ} {p : Fin n} {v : V} (hv : (gexec A σ t).dec p = some v) :
    ∃ q s, s < t ∧ σ s = q ∧ A.inp q = v := by
  obtain ⟨hG, hd⟩ := gexec_inv (A := A) (σ := σ) t
  obtain ⟨g, hg⟩ := Val_gx _ _ (hG.av_Val _ _ (hd p v hv))
  obtain ⟨q, -, hq, hq'⟩ := hG.gx_wit _ _ hg
  obtain ⟨s, hs, hs'⟩ := stepped_of_ne_start hq'
  exact ⟨q, s, hs, hs', hq⟩

/-- Theorem 6 (Agreement, Lemma 11): no two processes decide different values (at any times). -/
theorem group_agreement {t t' : ℕ} {p q : Fin n} {v w : V}
    (hv : (gexec A σ t).dec p = some v) (hw : (gexec A σ t').dec q = some w) : v = w := by
  have h1 := (gexec_inv (A := A) (σ := σ) t).2 p v hv
  have h2 := (gexec_inv (A := A) (σ := σ) t').2 q w hw
  rcases le_total t t' with h | h
  · rw [(gexec_ext h).av _ _ h1] at h2; exact Option.some.inj h2
  · rw [(gexec_ext h).av _ _ h2] at h1; exact (Option.some.inj h1).symm


end Safety

/-! ### Theorem 6: termination (Lemma 10) -/

/-- Rank of a T1 program counter of a process of group `y`: the number of steps to the end of
T1 is at most this, if the process is never blocked. -/
def gRank (y : ℕ) : Pc V → ℕ
  | .start => 10 * y + 20
  | .wVal _ => 10 * y + 19
  | .arb g s => 10 * g + 3 + s.rank
  | .rdV ℓ => 10 * ℓ + 2
  | .rdA ℓ => 10 * ℓ + 2
  | .wAV ℓ _ => 10 * ℓ + 1
  | .fin => 0

section Rank

variable {A : Inst n V} {sh : GSh V} {pc : Fin n → Pc V}

/-- Every T1 step of a process that has not finished T1 and is not blocked in a
`wait(WINNER ≠ ⊥)` with `WINNER = ⊥` decreases its rank. -/
lemma GInv.rank_lt (h : GInv A sh pc) (p : Fin n) (hf : pc p ≠ .fin)
    (hb : ∀ g, pc p = .arb g .gWait → (sh.arb g).W ≠ none) :
    gRank (A.grp p) (t1 A.m (A.grp p) (A.inp p) (pc p) sh).1 < gRank (A.grp p) (pc p) := by
  have hl := h.loc p
  cases hs : pc p with
  | start => simp [t1, gRank]
  | wVal d => simp only [t1, gRank]; split_ifs <;> simp [APc.rank]
  | arb g s =>
    rw [hs] at hl hb
    obtain ⟨hgy, hgm, hsd⟩ := hl.ok
    simp only [t1, gRank]
    have Ig := h.arb g hgm
    have hPp : projCfg A g sh pc p = s := by
      simp [projCfg, hs, proj, show ¬ A.grp p < g by omega]
    have hrole : roleAt A g p = if g = A.grp p then Role.owner else .guest := rfl
    have := Ig.rank_lt p (by rw [hPp]; exact hsd)
      (by rw [hPp]; rintro ⟨rfl, hW⟩; exact hb g rfl hW)
    rw [hPp, hrole] at this
    generalize astep (if g = A.grp p then Role.owner else .guest) s (sh.arb g) = st at this ⊢
    obtain ⟨s1, A1⟩ := st
    simp only at this ⊢
    cases s1 <;> try (rename_i a; cases a)
    all_goals simp only [afterArb, APc.rank] at this ⊢; omega
  | rdV ℓ => simp [t1, gRank]
  | rdA ℓ => simp [t1, gRank]
  | wAV ℓ x => (cases ℓ <;> simp [t1, gRank, nextAfter, APc.rank]); omega
  | fin => exact absurd hs hf

end Rank

variable {A : Inst n V} {σ : ℕ → Fin n}

/-- Theorem 6 (Termination, Lemma 10 — the paper writes `y ∈ [1..n]`, meaning `[1..m]`): in
every infinite schedule, if there is a group `y` such that no process of a group `z < y`
participates and some process of group `y` participates and is correct, then every correct
process decides. (A correct process takes infinitely many steps, hence participates.) -/
theorem group_termination {y : ℕ} (hno : ∀ q, A.grp q < y → ∀ t, σ t ≠ q) {p : Fin n}
    (hpy : A.grp p = y) (hp : Correct σ p) :
    ∀ q, Correct σ q → ∃ t v, (gexec A σ t).dec q = some v := by
  -- `p` is never blocked in an arbiter: it is the owner of `ARBITER[y]`, and the owners of the
  -- arbiters `ARBITER[z]`, `z < y`, it visits as a guest never participate.
  have hnb : ∀ t g, (gexec A σ t).pc p = .arb g .gWait → False := by
    intro t g hg
    obtain ⟨hG, -⟩ := gexec_inv (A := A) (σ := σ) t
    have hl := hG.loc p
    rw [hg] at hl
    obtain ⟨hgy, hgm, -⟩ := hl.ok
    have Ig := hG.arb g hgm
    have hPp : projCfg A g (gexec A σ t).sh (gexec A σ t).pc p = .gWait := by
      simp [projCfg, hg, proj, show ¬ A.grp p < g by omega]
    have hsh := (Ig.loc p).shape
    rw [hPp] at hsh
    have hguest : g ≠ A.grp p := by
      intro he; simp [roleAt, he, Shape] at hsh
    obtain ⟨q, hq1, hq2⟩ := Ig.exO ((Ig.loc p).gWait_pO hPp)
    have hq : g = A.grp q := by
      unfold roleAt at hq1; split_ifs at hq1 with h'; exact h'
    obtain ⟨h1, -⟩ := proj_ne_idle hq2
    obtain ⟨s, -, hs⟩ := stepped_of_ne_start h1
    exact hno q (by omega) s hs
  -- hence `p` finishes task T1
  obtain ⟨T, hT⟩ := exists_of_measure hp
    (fun t => 2 * gRank (A.grp p) ((gexec A σ t).pc p) + if (gexec A σ t).t2 p then 1 else 0) 0
    (fun t => (gexec A σ t).pc p = .fin) (by
      intro t _ hf
      by_cases hσ : σ t = p
      · have hstep : gexec A σ (t + 1) = (gexec A σ t).step A p := by simp [gexec, hσ]
        rw [hstep]
        cases ht : (gexec A σ t).t2 p
        · have := (gexec_inv (A := A) (σ := σ) t).1.rank_lt p hf
            (fun g hg => absurd hg (fun hg => hnb t g hg))
          rw [GCfg.step_of_t1 ht]
          simp only [update_self]
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega
        · rw [GCfg.step_of_t2 ht]
          simp
      · obtain ⟨h1, h2, -⟩ := gexec_other (A := A) hσ
        rw [h1, h2]
        exact ⟨le_rfl, fun h => absurd h hσ⟩)
  -- then `ARB_VAL[1] ≠ ⊥` forever
  have hav : ∀ t, T ≤ t → (gexec A σ t).sh.av 0 ≠ none := by
    intro t ht
    have := ((gexec_inv (A := A) (σ := σ) T).1.loc p).wrote 0 (by rw [hT]; simp [Wrote])
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 this
    simp [(gexec_ext ht).av _ _ hz]
  -- and every correct process decides at its next T2 step
  intro q hq
  obtain ⟨t, ht⟩ := exists_of_measure hq
    (fun t => if (gexec A σ t).dec q = none then (if (gexec A σ t).t2 q then 1 else 2) else 0) T
    (fun t => (gexec A σ t).dec q ≠ none) (by
      intro t ht hd
      simp only [ne_eq, not_not] at hd
      by_cases hσ : σ t = q
      · have hstep : gexec A σ (t + 1) = (gexec A σ t).step A q := by simp [gexec, hσ]
        rw [hstep]
        cases h2 : (gexec A σ t).t2 q
        · rw [GCfg.step_of_t1 h2]
          simp [hd]
        · rw [GCfg.step_of_t2 h2]
          simp [hd, hav t ht]
      · obtain ⟨-, h2, h3⟩ := gexec_other (A := A) hσ
        rw [h2, h3]
        exact ⟨le_rfl, fun h => absurd h hσ⟩)
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 ht
  exact ⟨t, v, hv⟩

end Podc.AsymmetricProgress.Group
