import Papers.PODC2023.DuraCAS.AModel

/-!
# The DurEC invariant (Lemmas A.1–A.10 of the full version), stated on concrete/A-level pairs

The refinement proof (`Refinement.lean`) is a forward simulation: the A-level state `a` is carried
along as a ghost of the concrete state `s`, related by `Inv s a`. The ghost part proper is
`a.ls` (the abstract `DETECT` value of each DurEC handle = the sequence number of its last *moved*
install) and `a.ps p` (the A-level program counter, `.aft pc true` once the `ECSC` of `p` has been
linearized by a move, and the *orphan* = an install of a crashed `ECSC` that is not moved yet).

Vocabulary of the paper (Appendix A.1): an *install* is a successful `CAS` on `X` (line 10), a
*move* a successful `CAS` on `Y` (line 18). An install on `o` is *pending* (`Pend`) iff
`Y.seq < X.seq` (Lemma A.2: installs and moves alternate; an install makes `X.seq > Y.seq`, a move
brings `Y.seq` up to `X.seq`).
-/

set_option linter.unusedSectionVars false

namespace Podc.DuraCAS

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- An install on `o` is pending: `Y.seq < X.seq` (Lemma A.2). -/
def Pend (m : Mem P K V) (o : Obj K) : Prop := (m.Y o).1 < (m.X o).2

/-- The pending install on `o` is the one of handle `g` with sequence number `e`. -/
def PendAt (m : Mem P K V) (o : Obj K) (g : Hd P) (e : ℕ) : Prop :=
  m.X o = (some g, e) ∧ Pend m o

/-- A value `(g, e)` read from `X o` earlier is still the pending install, or it has been moved
(Lemma A.5: a stale `x` cannot be moved). -/
def Fresh (m : Mem P K V) (ls : Hd P → ℕ) (o : Obj K) (g : Hd P) (e : ℕ) : Prop :=
  PendAt m o g e ∨ (e ≤ (m.Y o).1 ∧ e ≤ ls g)

/-- An installing `ECSC` frame whose install has been moved (it is linearized). -/
def Moved (m : Mem P K V) (f : Frame P K V) : Prop :=
  f.kind = .sc ∧ f.r = true ∧ f.sh ≤ (m.Y f.o).1

instance (m : Mem P K V) (f : Frame P K V) : Decidable (Moved m f) := by
  unfold Moved; infer_instance

/-- The frame is in its `FORWARD` part (lines 13–18). -/
def FPc.IsFwd : FPc P V → Prop
  | .l7 => False
  | .l8 => False
  | .l9 _ => False
  | .l10 _ => False
  | _ => True

/-- The A-level program counter of a concrete process. -/
def apcOf (m : Mem P K V) (st : PState P K V) : APc V :=
  match st.fr with
  | some f => if Moved m f then .aft st.pc true else .at st.pc
  | none => .at st.pc

/-- The `FORWARD` of frame `f` must move the current pending install of `f.o` (Lemmas A.3, A.4,
A.6, A.7): `f` is a hitchhiker whose context `s` is still current, an installer whose install
is not moved yet, or the `RECOVER` of an object with an orphan of its process. -/
def Need (m : Mem P K V) (orph : Option (Orph P K V)) (f : Frame P K V) : Prop :=
  Pend m f.o ∧ ((f.kind = .sc ∧ f.r = false ∧ (m.Y f.o).1 = f.s) ∨
    (f.kind = .sc ∧ f.r = true ∧ (m.Y f.o).1 < f.sh) ∨
    (f.kind = .recov ∧ ∃ x, orph = some x ∧ x.o = f.o))

/-- Invariant of the local variables of a frame, by line (`N` = `Need`). -/
def StageOK (m : Mem P K V) (ls : Hd P → ℕ) (f : Frame P K V) (N : Prop) : Prop :=
  match f.pc with
  | .l7 => f.r = false
  | .l8 => f.r = false ∧ m.hval f.h = f.v
  | .l9 hh => f.r = false ∧ m.hval f.h = f.v ∧ ((m.X f.o).2 = f.s → (m.X f.o).1 = hh)
  | .l10 hh => f.r = false ∧ m.hval f.h = f.v ∧ ((m.X f.o).2 = f.s → (m.X f.o).1 = hh) ∧
      f.sh = max (ls f.h) f.s + 1
  | .f13 => True
  | .f14 x => (N → x = m.X f.o) ∧ ∀ g, x.1 = some g → Fresh m ls f.o g x.2
  | .f15 g e d => (N → m.X f.o = (some g, e)) ∧ Fresh m ls f.o g e ∧
      (PendAt m f.o g e → m.det g = e ∨ (m.det g = d ∧ d < e))
  | .f16 g e => (N → m.X f.o = (some g, e)) ∧ Fresh m ls f.o g e ∧
      (PendAt m f.o g e → m.det g = e)
  | .f17 g e vh => (N → m.X f.o = (some g, e)) ∧ Fresh m ls f.o g e ∧
      (PendAt m f.o g e → m.det g = e ∧ vh = m.hval g)
  | .f18 g e vh y => (N → m.X f.o = (some g, e) ∧ y = m.Y f.o) ∧ Fresh m ls f.o g e ∧
      (PendAt m f.o g e → m.det g = e ∧ vh = m.hval g)

/-- Invariant of an `ECSC` frame (Lemmas A.1, A.2, A.5, A.6). -/
def ScOK (m : Mem P K V) (f : Frame P K V) : Prop :=
  f.s ≤ (m.Y f.o).1 ∧
  (f.pc.IsFwd → (f.r = true → f.s < f.sh ∧ (f.sh ≤ (m.Y f.o).1 ∨
      (m.X f.o = (some f.h, f.sh) ∧ (m.Y f.o).1 = f.s ∧ m.hval f.h = f.v))) ∧
    (f.r = false → f.s < (m.X f.o).2))

/-- Invariant of the active frame `f` of process `p`. -/
def FrameOK (m : Mem P K V) (ls : Hd P → ℕ) (p : P) (st : PState P K V)
    (orph : Option (Orph P K V)) (f : Frame P K V) : Prop :=
  f.h.1 = p ∧
  (∃ r, st.op = some r ∧
    (f.kind = .sc → scArgs p r.k r.op st.pc = some ⟨f.o, f.h, f.s, f.v⟩) ∧
    (f.kind = .recov → ∃ j, st.pc = .recv j ∧ f.o = recObj r.k j)) ∧
  (f.kind = .sc → ScOK m f) ∧ (f.kind = .recov → f.pc.IsFwd) ∧
  StageOK m ls f (Need m orph f)

/-- Invariant of an orphan `x` of process `p`: its install is pending, and `p` is recovering, at
line 22 (`j = 0`) if the orphan is on `W`, at line 22 or 23 if it is on `Z`. -/
def COrphOK (m : Mem P K V) (p : P) (st : PState P K V) (x : Orph P K V) : Prop :=
  x.h.1 = p ∧ (m.X x.o).1 = some x.h ∧ Pend m x.o ∧ x.s = (m.Y x.o).1 ∧ x.v = m.hval x.h ∧
  ∃ r j, st.op = some r ∧ st.pc = .recv j ∧
    ((x.o = (r.k, .W) ∧ j.val = 0) ∨ (x.o = (r.k, .Z) ∧ j.val ≤ 1))

/-- Per-process part of the invariant. -/
structure PInv (m : Mem P K V) (ls : Hd P → ℕ) (p : P) (st : PState P K V) (ap : APS P K V) :
    Prop where
  op : ap.op = st.op
  idle : st.op = none ↔ st.pc = .idle
  idleFr : st.pc = .idle → st.fr = none
  pc : ap.pc = apcOf m st
  orph : ∀ x, ap.orph = some x → COrphOK m p st x
  fr : ∀ f, st.fr = some f → FrameOK m ls p st ap.orph f

/-- Memory part of the invariant (Lemmas A.1, A.2, A.10, with the ghost `ls`). -/
structure CGInv (m : Mem P K V) (ls : Hd P → ℕ) : Prop where
  yx : ∀ o, (m.Y o).1 ≤ (m.X o).2
  xnone : ∀ o, (m.X o).1 = none → (m.X o).2 = 0
  done : ∀ o g, (m.X o).1 = some g → ¬ Pend m o → (m.X o).2 ≤ ls g
  pendSeq : ∀ o g, (m.X o).1 = some g → Pend m o → (m.X o).2 = max (ls g) (m.Y o).1 + 1
  pendDet : ∀ o g, (m.X o).1 = some g → Pend m o → m.det g = ls g ∨ m.det g = (m.X o).2
  lsDet : ∀ g, ls g ≤ m.det g
  detEq : ∀ g, (∀ o, (m.X o).1 = some g → ¬ Pend m o) → m.det g = ls g
  uniq : ∀ o o' g g', (m.X o).1 = some g → (m.X o').1 = some g' → Pend m o → Pend m o' →
    g.1 = g'.1 → o = o'

/-- The pending install on `o` (of handle `g`) belongs to the active frame of `g.1` or to an
orphan of `g.1`. -/
def Owner (m : Mem P K V) (ps : P → PState P K V) (aps : P → APS P K V) (o : Obj K) (g : Hd P) :
    Prop :=
  (∃ f, (ps g.1).fr = some f ∧ f.kind = .sc ∧ f.r = true ∧ f.o = o ∧ f.h = g ∧
    f.sh = (m.X o).2) ∨
  ∃ x, (aps g.1).orph = some x ∧ x.o = o

/-- The simulation invariant between a concrete state and an A-level state. -/
structure Inv (s : St P K V) (a : AS P K V) : Prop where
  Y : a.Y = s.m.Y
  hist : a.hist = s.hist
  nid : a.nid = s.nid
  g : CGInv s.m a.ls
  p : ∀ p, PInv s.m a.ls p (s.ps p) (a.ps p)
  own : ∀ o g, (s.m.X o).1 = some g → Pend s.m o → Owner s.m s.ps a.ps o g

/-! ## Basic facts -/

theorem inv_init (init : K → V) (hv0 : Hd P → V × Bool) :
    Inv (initSt init hv0) (ainit (P := P) init) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initSt, ainit, Pend]
  · intro p
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initSt, ainit, apcOf]
  · intro o g h; simp [initSt] at h

theorem scArgs_recv (p : P) (k : K) (op : Op V) (j : Fin 4) :
    scArgs p k op (.recv j) = (none : Option (Orph P K V)) := rfl

theorem FrameOK.sc_not_recv {m : Mem P K V} {ls p st orph f} (h : FrameOK m ls p st orph f)
    (hk : f.kind = .sc) (j : Fin 4) : st.pc ≠ .recv j := by
  obtain ⟨_, ⟨r, _, hsc, _⟩, _⟩ := h
  intro hpc; have := hsc hk; rw [hpc, scArgs_recv] at this; cases this

/-- Structure of an owner. -/
theorem owner_cases {m : Mem P K V} {ls ps aps o g} (ho : Owner m ps aps o g)
    (hXo : (m.X o).1 = some g) (hp : PInv m ls g.1 (ps g.1) (aps g.1)) :
    (∃ f, (ps g.1).fr = some f ∧ f.kind = .sc ∧ f.r = true ∧ f.o = o ∧ f.h = g ∧
      f.sh = (m.X o).2 ∧ f.pc.IsFwd ∧ (aps g.1).orph = none) ∨
    (∃ x, (aps g.1).orph = some x ∧ x.o = o ∧ x.h = g ∧
      (∀ f, (ps g.1).fr = some f → f.kind = .recov)) := by
  rcases ho with ⟨f, hf, hk, hr, hoo, hh, hsh⟩ | ⟨x, hx, hxo⟩
  · left
    refine ⟨f, hf, hk, hr, hoo, hh, hsh, ?_, ?_⟩
    · have hst := (hp.fr f hf).2.2.2.2
      revert hst; unfold StageOK; cases f.pc <;> simp [FPc.IsFwd, hr]
    · cases hx : (aps g.1).orph with
      | none => rfl
      | some x =>
        obtain ⟨-, -, -, -, -, r, j, -, hpc, -⟩ := hp.orph x hx
        exact absurd hpc ((hp.fr f hf).sc_not_recv hk j)
  · right
    obtain ⟨hxh, hX, -, -, -, r, j, -, hpc, -⟩ := hp.orph x hx
    refine ⟨x, hx, hxo, ?_, ?_⟩
    · subst hxo; rw [hXo] at hX; exact (Option.some.inj hX).symm
    · intro f hf
      cases hk : f.kind
      · exact absurd hpc ((hp.fr f hf).sc_not_recv hk j)
      · rfl

/-! ## Transfer of the frame invariant along memory changes of other processes -/

theorem StageOK.transfer {m m' : Mem P K V} {ls ls' : Hd P → ℕ} {f : Frame P K V} {N N' : Prop}
    (h : StageOK m ls f N)
    (hN : f.pc.IsFwd → N' → N ∧ m'.X f.o = m.X f.o ∧ m'.Y f.o = m.Y f.o)
    (hF : ∀ g e, Fresh m ls f.o g e → Fresh m' ls' f.o g e)
    (hP : ∀ g e, Fresh m ls f.o g e → PendAt m' f.o g e → PendAt m f.o g e ∧
        (m'.det g = m.det g ∨ m'.det g = e) ∧ m'.hval g = m.hval g)
    (hpre : ¬ f.pc.IsFwd → m'.hval f.h = m.hval f.h ∧ ls' f.h = ls f.h ∧
        ((m'.X f.o).2 = f.s → m'.X f.o = m.X f.o)) :
    StageOK m' ls' f N' := by
  rcases f with ⟨kind, o, hd, s, v, sh, r, pc⟩
  cases pc with
  | l7 => exact h
  | l8 =>
    obtain ⟨h1, h2⟩ := h; obtain ⟨e1, -, -⟩ := hpre (by simp [FPc.IsFwd])
    exact ⟨h1, by simp only at e1 h2 ⊢; rw [e1, h2]⟩
  | l9 hh =>
    obtain ⟨h1, h2, h3⟩ := h; obtain ⟨e1, -, e3⟩ := hpre (by simp [FPc.IsFwd])
    simp only at e1 e3 h2 h3 ⊢
    exact ⟨h1, by rw [e1, h2], fun hs => by rw [e3 hs]; exact h3 (by rw [← e3 hs]; exact hs)⟩
  | l10 hh =>
    obtain ⟨h1, h2, h3, h4⟩ := h; obtain ⟨e1, e2, e3⟩ := hpre (by simp [FPc.IsFwd])
    simp only at e1 e2 e3 h2 h3 h4 ⊢
    exact ⟨h1, by rw [e1, h2], fun hs => by rw [e3 hs]; exact h3 (by rw [← e3 hs]; exact hs),
      by rw [e2, h4]⟩
  | f13 => trivial
  | f14 x =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hn => ?_, fun g hg => hF g x.2 (h2 g hg)⟩
    obtain ⟨hn, hx, -⟩ := hN (by simp [FPc.IsFwd]) hn; simp only at hx ⊢; rw [hx]; exact h1 hn
  | f15 g e d =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hn => ?_, hF g e h2, fun hp => ?_⟩
    · obtain ⟨hn, hx, -⟩ := hN (by simp [FPc.IsFwd]) hn; simp only at hx ⊢; rw [hx]; exact h1 hn
    · obtain ⟨hp', hd, -⟩ := hP g e h2 hp
      rcases hd with hd | hd
      · rw [hd]; exact h3 hp'
      · exact Or.inl hd
  | f16 g e =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hn => ?_, hF g e h2, fun hp => ?_⟩
    · obtain ⟨hn, hx, -⟩ := hN (by simp [FPc.IsFwd]) hn; simp only at hx ⊢; rw [hx]; exact h1 hn
    · obtain ⟨hp', hd, -⟩ := hP g e h2 hp
      rcases hd with hd | hd
      · rw [hd]; exact h3 hp'
      · exact hd
  | f17 g e vh =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hn => ?_, hF g e h2, fun hp => ?_⟩
    · obtain ⟨hn, hx, -⟩ := hN (by simp [FPc.IsFwd]) hn; simp only at hx ⊢; rw [hx]; exact h1 hn
    · obtain ⟨hp', hd, hv⟩ := hP g e h2 hp
      obtain ⟨h3, h4⟩ := h3 hp'
      refine ⟨?_, by rw [hv]; exact h4⟩
      rcases hd with hd | hd
      · rw [hd]; exact h3
      · exact hd
  | f18 g e vh y =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hn => ?_, hF g e h2, fun hp => ?_⟩
    · obtain ⟨hn, hx, hy⟩ := hN (by simp [FPc.IsFwd]) hn; simp only at hx hy ⊢; rw [hx, hy]; exact h1 hn
    · obtain ⟨hp', hd, hv⟩ := hP g e h2 hp
      obtain ⟨h3, h4⟩ := h3 hp'
      refine ⟨?_, by rw [hv]; exact h4⟩
      rcases hd with hd | hd
      · rw [hd]; exact h3
      · exact hd

end Podc.DuraCAS
