import Papers.PODC2023.DuraCAS.AFrame

/-!
# The local invariant after a step of the process itself

One lemma per kind of step of the acting process (a step that only moves the program counter,
a failing `ECSC`, an install/move/imprint by the process, orphan effects, crash, invocation).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

theorem Loc.orph_none {p : P} {v : KV V} {x : PV P K V} (hl : Loc p v x)
    (h : ∀ j, x.pc ≠ .at (.recv j)) : x.orph = none := by
  cases ho : x.orph with
  | none => rfl
  | some o =>
    rcases (hl.orph o ho).1 with h' | ⟨h', -⟩
    · exact absurd h' (h 0)
    · exact absurd h' (h 1)

theorem orphOK_none {p : P} {v : KV V} {x : PV P K V} (h : x.orph = none) : OrphOK p v x := by
  intro o ho; rw [h] at ho; cases ho

/-- Changing only the program counter of a process without orphan. -/
theorem loc_setPc {p : P} {v : KV V} {x : PV P K V} (pc' : APc V) (hl : Loc p v x)
    (ho : x.orph = none) (h : PcOK v { x with pc := pc' } pc') : Loc p v { x with pc := pc' } :=
  ⟨hl.d1_le, hl.inL_lt, hl.lt_inL, hl.not_both, hl.pw_op, hl.wit_sig, orphOK_none ho, h⟩

theorem snap_refl (c : Cell V) : Snap c c := ⟨le_rfl, fun _ => rfl⟩

theorem Snap.lt_of_ne {c cur : Cell V} (h : Snap c cur) (hne : c.1 ≠ cur.1) : c.1 < cur.1 :=
  lt_of_le_of_ne h.1 hne

/-- If the bit of the snapshot differs from the current bit, the object has changed. -/
theorem Snap.lt_of_bit {c cur : Cell V} (h : Snap c cur) (hne : c.2.2 ≠ cur.2.2) : c.1 < cur.1 :=
  h.lt_of_ne (fun e => hne (by rw [h.2 e]))

/-! ### Steps that only move the program counter -/

theorem go_aft_cas10 {p : P} {v : KV V} {x : PV P K V} {z : Cell V} (hl : Loc p v x)
    (hpc : x.pc = .aft (.cas10 false z) false) :
    Loc p v { x with pc := .at (.cas7 true) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨hop, -, h3⟩ := h
  obtain ⟨h1, -, -, h4⟩ := h3 rfl
  exact loc_setPc _ hl (hl.orph_none (by simp [hpc])) ⟨hop, h1, fun _ => h4 rfl⟩

theorem go_aft_wr15 {p : P} {v : KV V} {x : PV P K V} {w : Cell V} {b : Bool} (hl : Loc p v x)
    (hpc : x.pc = .aft (.wr15 w) b) :
    Loc p v { x with pc := .at (.tw19 .wr1) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨hw, -, h3⟩ := h
  exact loc_setPc _ hl (hl.orph_none (by simp [hpc])) ⟨trivial, hw, h3, fun h => h.elim⟩

theorem go_aft_tw21_casT {p : P} {v : KV V} {x : PV P K V} {i : Bool} {z zh wh : Cell V} {b : Bool}
    (hl : Loc p v x) (hpc : x.pc = .aft (.tw21 (.casT i z) zh wh) b) :
    Loc p v { x with pc := .at (.cas10 i z) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨-, old, new, hop, hm, hc⟩ := h
  simp only [CasTw] at hc
  exact loc_setPc _ hl (hl.orph_none (by simp [hpc]))
    ⟨⟨old, new, hop, hm⟩, fun e => by omega⟩

theorem go_aft_tw21_1 {p : P} {v : KV V} {x : PV P K V} {r : Ret V} {zh wh : Cell V} {b : Bool}
    (hl : Loc p v x) (hpc : x.pc = .aft (.tw21 r zh wh) b) (hr : r = .wr1 ∨ r = .rec1) :
    Loc p v { x with pc := .at (.tw19 (if r = .wr1 then .wr2 else .rec2)) } := by
  have h := hl.pc; rw [hpc] at h
  rcases hr with rfl | rfl <;> simp only [PcOK, TwOK, Stage, if_true, reduceCtorEq, if_false] at h ⊢
  · exact loc_setPc _ hl (hl.orph_none (by simp [hpc]))
      ⟨trivial, h.2.1, fun hn => (h.2.2.2 hn).1, fun _ hn => (h.2.2.2 hn).2⟩
  · exact loc_setPc _ hl (hl.orph_none (by simp [hpc]))
      ⟨trivial, fun hn => (h.2.2 hn).1, fun _ hn => (h.2.2 hn).2⟩

theorem go_cas7 {p : P} {v : KV V} {x : PV P K V} {i : Bool} {old new : V} (hl : Loc p v x)
    (hpc : x.pc = .at (.cas7 i)) (hop : x.r.op = .cas old new) (hZ : v.Z.2.1 = old)
    (hne : old ≠ new) :
    Loc p v { x with pc := .at (.tw19 (.casT i v.Z)) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨-, h2, h3⟩ := h
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc]))
    ⟨trivial, old, new, hop, ⟨h2, hZ, hne, snap_refl _, fun hw => ?_⟩, trivial⟩
  cases i
  · simp
  · simp [h3 rfl hw]

theorem go_wr12 {p : P} {v : KV V} {x : PV P K V} (hl : Loc p v x) (hpc : x.pc = .at .wr12) :
    Loc p v { x with pc := .at (.wr13 v.W) } := by
  have h := hl.pc; rw [hpc] at h
  exact loc_setPc _ hl (hl.orph_none (by simp [hpc]))
    ⟨h.1, h.2, snap_refl _, fun _ e => absurd rfl e⟩

theorem go_wr13_15 {p : P} {v : KV V} {x : PV P K V} {w : Cell V} {u : V} (hl : Loc p v x)
    (hpc : x.pc = .at (.wr13 w)) (hop : x.r.op = .write u) (hZ : v.Z.2.1 ≠ u)
    (hb : v.Z.2.2 = w.2.2) :
    Loc p v { x with pc := .at (.wr15 w) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc])) ⟨⟨u, hop, fun e => ⟨?_, fun _ => hZ⟩⟩, h2, h3, h4⟩
  have := h3.2 e.symm
  unfold KV.pend; rw [← this, hb]; simp

theorem go_wr13_19 {p : P} {v : KV V} {x : PV P K V} {w : Cell V} (hl : Loc p v x) (hv : v.Inv)
    (hpc : x.pc = .at (.wr13 w)) (hb : v.Z.2.2 ≠ w.2.2) :
    Loc p v { x with pc := .at (.tw19 .wr1) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc])) ⟨trivial, h1, fun hn => ?_, fun h => h.elim⟩
  rcases hn with hn | ⟨-, hw⟩
  · have := (hl.pw_op hn).1; omega
  · by_cases e : v.W.1 = w.1
    · have := h3.2 e.symm
      unfold KV.pend; rw [← this]; exact fun h' => hb h'.symm
    · exact h4 hw e

theorem go_tw19 {p : P} {v : KV V} {x : PV P K V} {r : Ret V} (hl : Loc p v x) (hv : v.Inv)
    (hpc : x.pc = .at (.tw19 r)) :
    Loc p v { x with pc := .at (.tw20 r v.Z) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨-, hm⟩ := h
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc])) ⟨snap_refl _, ?_⟩
  rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only [Stage] at hm ⊢
  · obtain ⟨old, new, hop, hm, -⟩ := hm
    exact ⟨old, new, hop, hm, hm.2.2.2.1.1⟩
  · exact ⟨hm.1, hm.2.1, fun _ => ⟨fun h => h.elim, hv.zAt_le⟩⟩
  · exact ⟨hm.1, hm.2.1, fun hn => ⟨fun _ => ⟨hm.2.2 trivial hn, trivial⟩, hv.zAt_le⟩⟩
  · exact ⟨hm.1, fun _ => ⟨fun h => h.elim, hv.zAt_le⟩⟩
  · exact ⟨hm.1, fun hn => ⟨fun _ => ⟨hm.2 trivial hn, trivial⟩, hv.zAt_le⟩⟩

theorem go_tw20_21 {p : P} {v : KV V} {x : PV P K V} {r : Ret V} {zh : Cell V} (hl : Loc p v x)
    (hpc : x.pc = .at (.tw20 r zh)) (hb : zh.2.2 ≠ v.W.2.2) :
    Loc p v { x with pc := .at (.tw21 r zh v.W) } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨hg, hm⟩ := h
  simp only [TwGen] at hg
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc]))
    ⟨⟨hg, fun e => hb e.symm, fun e => ⟨rfl, ?_⟩⟩, ?_⟩
  · have := hg.2 e.symm
    unfold KV.pend; rw [← this]; exact fun h' => hb h'.symm
  · rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> exact hm

theorem go_tw20_ret {p : P} {v : KV V} {x : PV P K V} {r : Ret V} {zh : Cell V} {pc' : Pc V}
    (hl : Loc p v x) (hpc : x.pc = .at (.tw20 r zh)) (hb : zh.2.2 = v.W.2.2)
    (hn : afterTW r = .go pc') :
    Loc p v { x with pc := .at pc' } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨hg, hm⟩ := h
  simp only [TwGen] at hg
  have hpz : v.pend → zh.1 < v.Z.1 := fun hp => hg.lt_of_bit (fun e => hp (by rw [← e, hb]))
  rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only [afterTW, Next.go.injEq, reduceCtorEq] at hn <;>
    subst hn <;> simp only [Stage] at hm
  · obtain ⟨old, new, hop, hm, hc⟩ := hm
    simp only [CasTw] at hc
    refine loc_setPc _ hl (hl.orph_none (by simp [hpc])) ⟨⟨old, new, hop, hm⟩, fun e hp => ?_⟩
    have := hpz hp; have := hg.1; omega
  · exact loc_setPc _ hl (hl.orph_none (by simp [hpc]))
      ⟨trivial, hm.1, hm.2.1, fun _ hn' => by have := hpz (hm.2.1 hn'); have := (hm.2.2 hn').2; omega⟩
  · exact loc_setPc _ hl (hl.orph_none (by simp [hpc]))
      ⟨trivial, hm.1, fun _ hn' => by have := hpz (hm.1 hn'); have := (hm.2 hn').2; omega⟩

theorem go_recv {p : P} {v : KV V} {x : PV P K V} {j : Fin 4} {pc' : Pc V} (hl : Loc p v x)
    (hv : v.Inv) (hpc : x.pc = .at (.recv j))
    (hen : ∀ o, x.orph = some o → o.o ≠ recObj x.r.k j)
    (hn : afterCall (.recv j) false = .go pc') :
    Loc p v { x with pc := .at pc' } := by
  have hneed : needR v x → v.pend := fun h => hv.pend_iff.2 (by rw [h]; simp)
  simp only [afterCall] at hn
  split_ifs at hn with hj <;> simp only [Next.go.injEq] at hn <;> subst hn
  · refine ⟨hl.d1_le, hl.inL_lt, hl.lt_inL, hl.not_both, hl.pw_op, hl.wit_sig, ?_, hneed⟩
    intro o ho
    obtain ⟨hp, hk⟩ := hl.orph o ho
    refine ⟨?_, hk⟩
    have he := hen o ho
    rw [hpc] at hp
    rcases hp with hp | ⟨hp, ho'⟩
    · simp only [APc.at.injEq, Pc.recv.injEq] at hp; subst hp
      right; refine ⟨rfl, ?_⟩
      rcases hk with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 (by simpa [recObj] using he)
      · exact h1
      · exact h1
    · simp only [APc.at.injEq, Pc.recv.injEq] at hp; subst hp
      exact absurd ho' (by simpa [recObj] using he)
  · have ho : x.orph = none := by
      cases ho : x.orph with
      | none => rfl
      | some o =>
        rcases (hl.orph o ho).1 with h' | ⟨h', -⟩ <;> rw [hpc] at h' <;>
          simp only [APc.at.injEq, Pc.recv.injEq] at h' <;> subst h' <;> simp at hj
    exact loc_setPc _ hl ho ⟨trivial, hneed, fun h => h.elim⟩

/-! ### Failing `ECSC`s -/

theorem fail_cas10 {p : P} {v : KV V} {x : PV P K V} {i : Bool} {z : Cell V} (hl : Loc p v x)
    (hpc : x.pc = .at (.cas10 i z)) (hZ : v.Z.1 ≠ z.1) :
    Loc p v { x with pc := .aft (.cas10 i z) false } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨⟨old, new, hop, h1, -, -, hs, h5⟩, -⟩ := h
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc]))
    ⟨⟨old, new, hop⟩, fun h => by simp at h, fun _ => ⟨h1, hs.lt_of_ne (Ne.symm hZ), fun hi hw => ?_,
      fun hi hw => ?_⟩⟩
  · subst hi; simp only [↓reduceIte] at h5; exact hZ (h5 hw).2
  · subst hi; simp only [Bool.false_eq_true, ↓reduceIte] at h5; exact h5 hw hZ

theorem fail_wr15 {p : P} {v : KV V} {x : PV P K V} {w : Cell V} (hl : Loc p v x)
    (hpc : x.pc = .at (.wr15 w)) (hW : v.W.1 ≠ w.1) :
    Loc p v { x with pc := .aft (.wr15 w) false } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨⟨u, hop, -⟩, h2, -, h4⟩ := h
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc]))
    ⟨⟨u, hop⟩, by simp; omega, fun hn => ?_⟩
  rcases hn with hn | ⟨-, hw⟩
  · have := (hl.pw_op hn).1; omega
  · exact h4 hw hW

theorem fail_tw21 {p : P} {v : KV V} {x : PV P K V} {r : Ret V} {zh wh : Cell V} (hl : Loc p v x)
    (hpc : x.pc = .at (.tw21 r zh wh)) (hZ : v.Z.1 ≠ zh.1) :
    Loc p v { x with pc := .aft (.tw21 r zh wh) false } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨hg, hm⟩ := h
  simp only [TwGen] at hg
  have hlt : zh.1 < v.Z.1 := hg.1.lt_of_ne (Ne.symm hZ)
  refine loc_setPc _ hl (hl.orph_none (by simp [hpc])) ⟨trivial, ?_⟩
  rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only [Stage, CasTw] at hm ⊢
  · obtain ⟨old, new, hop, hm, hc⟩ := hm
    exact ⟨old, new, hop, hm, by omega⟩
  · exact ⟨hm.1, fun h => h.elim, fun hn => ⟨hm.2.1 hn, by have := (hm.2.2 hn).2; omega⟩⟩
  · have hc := fun hn => hZ (by rw [((hm.2.2 hn).1 trivial).2])
    exact ⟨hm.1, fun _ hn => hc hn, fun hn => absurd hn hc⟩
  · exact ⟨fun h => h.elim, fun hn => ⟨hm.1 hn, by have := (hm.2 hn).2; omega⟩⟩
  · have hc := fun hn => hZ (by rw [((hm.2 hn).1 trivial).2])
    exact ⟨fun _ hn => hc hn, fun hn => absurd hn hc⟩

/-! ### Successful `ECSC`s of the process at its call sites -/

/-- Imprint by the process (line 10). -/
theorem impr_actor {p : P} {v : KV V} {x : PV P K V} {i : Bool} {z : Cell V} {old new : V}
    (t s' : ℕ) (hl : Loc p v x) (hv : v.Inv) (hpc : x.pc = .at (.cas10 i z))
    (hop : x.r.op = .cas old new) (hZ : v.Z.1 = z.1) (hs : x.ls < s') (hs2 : v.Z.1 < s') :
    Impr v ⟨v.W, (s', (new, z.2.2)), v.pw, v.zAt, false, new⟩ new ∧
      Loc p ⟨v.W, (s', (new, z.2.2)), v.pw, v.zAt, false, new⟩
        { x with pc := .aft (.cas10 i z) true, ls := s', wit := massWit x new false t,
                 inL := True } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨⟨old', new', hop', h1, h2, h3, hsn, -⟩, hi4⟩ := h
  rw [hop] at hop'; simp only [Op.cas.injEq] at hop'; obtain ⟨rfl, rfl⟩ := hop'
  have hzZ : z = v.Z := hsn.2 hZ.symm
  have hnpw : v.pw ≠ some x.r.id := fun e => by simp [(hl.pw_op e).2] at hop
  refine ⟨⟨fun hp => (hi4 hZ hp).trans hZ.symm, rfl, hs2, by rw [hzZ], by rw [← hzZ, h2]; exact h3.symm,
    rfl, rfl, rfl, rfl⟩, ?_⟩
  refine ⟨by simp; omega, fun _ => by simp; omega, fun _ => Or.inl trivial,
    fun h => hnpw h.2, fun h => absurd h hnpw, fun o n hop2 hw => ?_,
    orphOK_none (hl.orph_none (by simp [hpc])), ⟨⟨old, new, hop⟩, fun _ => trivial, fun h => by simp at h⟩⟩
  obtain ⟨hw0, hn⟩ := massWit_cas (x := x) hop2 hw
  rw [hop] at hop2; simp only [Op.cas.injEq] at hop2; obtain ⟨rfl, rfl⟩ := hop2
  exact absurd hn h3.symm

/-- Install by the process (line 15). -/
theorem inst_actor {p : P} {v : KV V} {x : PV P K V} {w : Cell V} {u : V}
    (s' : ℕ) (hl : Loc p v x) (hpc : x.pc = .at (.wr15 w))
    (hop : x.r.op = .write u) (hW : v.W.1 = w.1) (hs : x.ls < s') (hs2 : w.1 < s') :
    Inst v ⟨(s', (u, !w.2.2)), v.Z, some x.r.id, v.Z.1, v.lm, v.sig⟩ x.r.id ∧
      Loc p ⟨(s', (u, !w.2.2)), v.Z, some x.r.id, v.Z.1, v.lm, v.sig⟩
        { x with pc := .aft (.wr15 w) true, ls := s' } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨⟨u', hop', h1⟩, h2, hsn, -⟩ := h
  rw [hop] at hop'; simp only [Op.write.injEq] at hop'; subst hop'
  obtain ⟨hnp, ha⟩ := h1 hW
  have hwW : w = v.W := hsn.2 hW.symm
  have hb : v.W.2.2 = v.Z.2.2 := not_not.1 hnp
  refine ⟨⟨hnp, by simp; omega, by simp [← hwW], rfl, rfl, rfl, rfl, rfl, fun h => (ha h).symm⟩, ?_⟩
  have hninL : ¬x.inL := fun h => by have := hl.inL_lt h; omega
  refine ⟨by simp; omega, fun h => absurd h hninL, fun _ => Or.inr rfl,
    fun h => hninL h.1, fun _ => ⟨by simp; omega, by simp [hop]⟩, fun o n hop2 => by simp [hop] at hop2,
    orphOK_none (hl.orph_none (by simp [hpc])), ⟨⟨u, hop⟩, by simp; omega, fun _ => ?_⟩⟩
  simp only [KV.pend]; rw [← hb, ← hwW]; simp

/-- Move by the process (line 21). -/
theorem move_actor {p : P} {v : KV V} {x : PV P K V} {r : Ret V} {zh wh : Cell V}
    (t s' : ℕ) (hl : Loc p v x) (hv : v.Inv) (hpc : x.pc = .at (.tw21 r zh wh))
    (hZ : v.Z.1 = zh.1) (hs2 : zh.1 < s') :
    Move v ⟨v.W, (s', wh.2), none, v.zAt, true, v.W.2.1⟩ ∧
      Loc p ⟨v.W, (s', wh.2), none, v.zAt, true, v.W.2.1⟩
        { x with pc := .aft (.tw21 r zh wh) true, wit := massWit x v.W.2.1 true t,
                 inL := x.inL ∨ v.pw = some x.r.id } := by
  have h := hl.pc; rw [hpc] at h
  obtain ⟨hg, hm⟩ := h
  simp only [TwGen] at hg
  obtain ⟨hWw, hp⟩ := hg.2.2 hZ
  have hM : Move v ⟨v.W, (s', wh.2), none, v.zAt, true, v.W.2.1⟩ :=
    ⟨hp, rfl, by simp; omega, by simp [hWw], rfl, rfl, rfl, rfl⟩
  refine ⟨hM, ?_⟩
  have H := loc_move t hl hv hM
  refine ⟨H.1, H.2, H.3, H.4, H.5, H.6, orphOK_none (hl.orph_none (by simp [hpc])), trivial, ?_⟩
  rcases r with ⟨i, z⟩ | _ | _ | _ | _ <;> simp only at hm ⊢
  · obtain ⟨old, new, hop, hm, hc⟩ := hm
    simp only [CasTw] at hc ⊢
    exact ⟨old, new, hop, casMid_move hv hM hm rfl rfl (fun hw => massWit_cas (x := x) hop hw),
      by omega⟩
  · exact ⟨hm.1, stage_of_not _ (fun hn => by
      rcases hn with hn | hn
      · simp at hn
      · exact massWit_wr_true hm.1 hn.2)⟩
  · exact ⟨hm.1, stage_of_not _ (fun hn => by
      rcases hn with hn | hn
      · simp at hn
      · exact massWit_wr_true hm.1 hn.2)⟩
  · exact stage_of_not _ (by simp [needR])
  · exact stage_of_not _ (by simp [needR])

/-! ### Orphans -/

theorem pcOK_recv {v : KV V} {x : PV P K V} (hv : v.Inv) (j : Fin 4) : PcOK v x (.at (.recv j)) :=
  fun h => hv.pend_iff.2 (by unfold needR at h; rw [h]; simp)

theorem Loc.orph_pc {p : P} {v : KV V} {x : PV P K V} {o : Orph P K V} (hl : Loc p v x)
    (ho : x.orph = some o) : ∃ j, x.pc = .at (.recv j) := by
  rcases (hl.orph o ho).1 with h | ⟨h, -⟩
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- An orphan install takes effect. -/
theorem orph_inst {p : P} {v : KV V} {x : PV P K V} {o : Orph P K V} (s' : ℕ) (hl : Loc p v x)
    (hv : v.Inv) (ho : x.orph = some o) (hoo : o.o = (x.r.k, .W)) (hW : v.W.1 = o.s)
    (hs : x.ls < s') (hs2 : o.s < s') :
    Inst v ⟨(s', o.v), v.Z, some x.r.id, v.Z.1, v.lm, v.sig⟩ x.r.id ∧
      Loc p ⟨(s', o.v), v.Z, some x.r.id, v.Z.1, v.lm, v.sig⟩
        { x with orph := none, ls := s' } := by
  obtain ⟨j, hpc⟩ := hl.orph_pc ho
  obtain ⟨-, hk⟩ := hl.orph o ho
  rcases hk with ⟨-, -, h2, -, u, hop, hu, h7⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · obtain ⟨hnp, ha, hb⟩ := h7 hW
    have hI : Inst v ⟨(s', o.v), v.Z, some x.r.id, v.Z.1, v.lm, v.sig⟩ x.r.id :=
      ⟨hnp, by simp; omega, hb, rfl, rfl, rfl, rfl, rfl, fun h => by simp only; rw [hu]; exact (ha h).symm⟩
    refine ⟨hI, ?_⟩
    have hninL : ¬x.inL := fun h => by have := hl.inL_lt h; omega
    refine ⟨by simp; omega, fun h => absurd h hninL, fun _ => Or.inr rfl,
      fun h => hninL h.1, fun _ => ⟨by simp; omega, by simp [hop, hu]⟩, fun o n hop2 => by simp [hop] at hop2,
      orphOK_none rfl, ?_⟩
    show PcOK _ _ x.pc
    rw [hpc]; exact pcOK_recv (KV.Inv.inst hv hI) j
  · rw [hoo] at h1; simp at h1
  · rw [hoo] at h1; simp at h1

/-- An orphan imprint takes effect. -/
theorem orph_impr {p : P} {v : KV V} {x : PV P K V} {o : Orph P K V} (t s' : ℕ) (hl : Loc p v x)
    (hv : v.Inv) (ho : x.orph = some o) (hoo : o.o = (x.r.k, .Z)) (hoh : o.h = (p, .crit))
    (hZ : v.Z.1 = o.s) (hs : x.ls < s') (hs2 : o.s < s') :
    Impr v ⟨v.W, (s', o.v), v.pw, v.zAt, false, o.v.1⟩ o.v.1 ∧
      Loc p ⟨v.W, (s', o.v), v.pw, v.zAt, false, o.v.1⟩
        { x with orph := none, ls := s', wit := massWit x o.v.1 false t, inL := True } ∧
      ∃ old, x.r.op = .cas old o.v.1 ∧ v.Z.2.1 = old := by
  obtain ⟨j, hpc⟩ := hl.orph_pc ho
  obtain ⟨-, hk⟩ := hl.orph o ho
  rcases hk with ⟨h1, -⟩ | ⟨-, -, h2, -, old, new, hop, hne, hn, h8⟩ | ⟨-, h1, -⟩
  · rw [hoo] at h1; simp at h1
  · obtain ⟨hZ2, hi4⟩ := h8 hZ
    have hI : Impr v ⟨v.W, (s', o.v), v.pw, v.zAt, false, o.v.1⟩ o.v.1 :=
      ⟨fun hp => (hi4 hp).trans hZ.symm, rfl, by simp; omega,
        by simp only; rw [hZ2], by rw [hZ2, hn]; exact hne.symm, rfl, rfl, rfl, rfl⟩
    have hnpw : v.pw ≠ some x.r.id := fun e => by simp [(hl.pw_op e).2] at hop
    refine ⟨hI, ⟨by simp; omega, fun _ => by simp; omega, fun _ => Or.inl trivial,
      fun h => hnpw h.2, fun h => absurd h hnpw, fun o' n hop2 hw => ?_, orphOK_none rfl, ?_⟩,
      old, by rw [hop, hn], by rw [hZ2]⟩
    · obtain ⟨-, hn'⟩ := massWit_cas (x := x) hop2 hw
      rw [hop] at hop2; simp only [Op.cas.injEq] at hop2; obtain ⟨rfl, rfl⟩ := hop2
      exact absurd (hn'.symm.trans hn) hne
    · show PcOK _ _ x.pc
      rw [hpc]; exact pcOK_recv (KV.Inv.impr hv hI) j
  · rw [hoh] at h1; simp at h1

/-- An orphan move takes effect. -/
theorem orph_move {p : P} {v : KV V} {x : PV P K V} {o : Orph P K V} (t s' : ℕ) (hl : Loc p v x)
    (hv : v.Inv) (ho : x.orph = some o) (hoo : o.o = (x.r.k, .Z)) (hoh : o.h = (p, .cas))
    (hZ : v.Z.1 = o.s) (hs2 : o.s < s') :
    Move v ⟨v.W, (s', o.v), none, v.zAt, true, v.W.2.1⟩ ∧
      Loc p ⟨v.W, (s', o.v), none, v.zAt, true, v.W.2.1⟩
        { x with orph := none, wit := massWit x v.W.2.1 true t,
                 inL := x.inL ∨ v.pw = some x.r.id } := by
  obtain ⟨j, hpc⟩ := hl.orph_pc ho
  obtain ⟨-, hk⟩ := hl.orph o ho
  rcases hk with ⟨h1, -⟩ | ⟨-, h1, -⟩ | ⟨-, -, -, h8⟩
  · rw [hoo] at h1; simp at h1
  · rw [hoh] at h1; simp at h1
  · obtain ⟨hWo, hp⟩ := h8 hZ
    have hM : Move v ⟨v.W, (s', o.v), none, v.zAt, true, v.W.2.1⟩ :=
      ⟨hp, rfl, by simp; omega, by simp [hWo], rfl, rfl, rfl, rfl⟩
    have H := loc_move t hl hv hM
    refine ⟨hM, H.1, H.2, H.3, H.4, H.5, H.6, orphOK_none rfl, ?_⟩
    show PcOK _ _ x.pc
    rw [hpc]; exact pcOK_recv (KV.Inv.move hv hM) j

/-- An orphan is dropped. -/
theorem drop_actor {p : P} {v : KV V} {x : PV P K V} (hl : Loc p v x) :
    Loc p v { x with orph := none } :=
  ⟨hl.d1_le, hl.inL_lt, hl.lt_inL, hl.not_both, hl.pw_op, hl.wit_sig, orphOK_none rfl, hl.pc⟩

/-! ### Crash and invocation -/

/-- A crash; `o'` is the new orphan (`scArgs` of the call the process is poised at, if any). -/
theorem crash_actor {p : P} {v : KV V} {x : PV P K V} (o' : Option (Orph P K V)) (hl : Loc p v x)
    (hv : v.Inv) (ho' : o' = none ∨ ∃ c, x.pc = .at c ∧ scArgs p x.r.k x.r.op c = o') :
    Loc p v { x with pc := .at (.recv 0), orph := o'.orElse fun _ => x.orph } := by
  refine ⟨hl.d1_le, hl.inL_lt, hl.lt_inL, hl.not_both, hl.pw_op, hl.wit_sig, ?_, pcOK_recv hv 0⟩
  rcases ho' with rfl | ⟨c, hpc, hc⟩
  · intro o ho
    exact ⟨Or.inl rfl, (hl.orph o ho).2⟩
  · cases o' with
    | none => intro o ho; exact ⟨Or.inl rfl, (hl.orph o ho).2⟩
    | some o' =>
      intro o ho
      simp only [Option.orElse_some, Option.some.injEq] at ho
      subst ho
      refine ⟨Or.inl rfl, ?_⟩
      have h := hl.pc; rw [hpc] at h
      cases c <;> simp only [scArgs, reduceCtorEq] at hc
      · -- cas10
        rename_i i z
        obtain ⟨⟨old, new, hop, h1, h2, h3, hsn, -⟩, hi4⟩ := h
        rw [hop] at hc; simp only [Option.some.injEq] at hc; subst hc
        refine Or.inr (Or.inl ⟨rfl, rfl, h1, hsn.1, old, new, hop, h3, rfl, fun e => ?_⟩)
        have hz := hsn.2 e.symm
        exact ⟨by rw [← hz]; exact Prod.ext h2 rfl, fun hp => hi4 e hp⟩
      · -- wr15
        rename_i w
        obtain ⟨⟨u, hop, h1⟩, h2, hsn, -⟩ := h
        rw [hop] at hc; simp only [Option.some.injEq] at hc; subst hc
        refine Or.inl ⟨rfl, rfl, h2, hsn.1, u, hop, rfl, fun e => ?_⟩
        obtain ⟨hnp, ha⟩ := h1 e
        have hw := hsn.2 e.symm
        exact ⟨hnp, ha, by rw [← hw]; simp⟩
      · -- tw21
        rename_i r zh wh
        obtain ⟨hg, -⟩ := h
        simp only [TwGen] at hg
        simp only [Option.some.injEq] at hc; subst hc
        refine Or.inr (Or.inr ⟨rfl, rfl, hg.1.1, fun e => ?_⟩)
        obtain ⟨hw, hp⟩ := hg.2.2 e
        exact ⟨by rw [hw], hp⟩

/-- A freshly invoked operation. -/
theorem invoke_loc {p : P} {v : KV V} {x : PV P K V} (hv : v.Inv) (hd : x.r.d1 = x.ls)
    (hinL : ¬x.inL) (hpw : v.pw ≠ some x.r.id) (ho : x.orph = none)
    (hpc : x.pc = .at (firstPc x.r.op))
    (hw : ∀ old new, x.r.op = .cas old new → x.wit = none → v.sig = old) : Loc p v x := by
  refine ⟨by omega, fun h => absurd h hinL, fun h => by omega, fun h => hinL h.1,
    fun h => absurd h hpw, hw, orphOK_none ho, ?_⟩
  rw [hpc]
  rcases hop : x.r.op with _ | ⟨old, new⟩ | u <;> simp only [firstPc, PcOK]
  · exact ⟨hop, hd.symm⟩
  · exact ⟨⟨old, new, hop⟩, hd.symm, fun h => by simp at h⟩
  · exact ⟨⟨u, hop⟩, hd.symm⟩

end Podc.DuraCAS
