import Papers.PODC2019.RDMAAgreement.PMP.Invariant

/-!
# Preservation of the invariant by every step (repaired algorithm)
-/

namespace Podc.RDMAAgreement.PMP

set_option linter.unusedSectionVars false

open Function

variable {P M V : Type*} [DecidableEq P] [DecidableEq M] [Fintype M]

section Helpers

variable {inp : P → V} {slot : M → P → Slot V} {perm : M → P} {votes : Set (M × P × ℕ × V)}
  {p2val : ℕ → Option V} {used : Finset ℕ} {p : P} {x : Proc P M V}

theorem TInv.congr {x' : Proc P M V} {m : M} {c : PC} {l : Link P V}
    (h : TInv slot perm votes p2val p x m c l) (h1 : x'.started = x.started)
    (h2 : x'.active = x.active) (h3 : x'.noPh1 = x.noPh1) (h4 : x'.p2s = x.p2s)
    (h5 : x'.ready = x.ready) (h6 : x'.done = x.done) (h7 : x'.bal = x.bal)
    (h8 : x'.curVal = x.curVal) (h9 : x'.lastIss = x.lastIss) :
    TInv slot perm votes p2val p x' m c l := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ := h
  constructor <;> (try simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9]) <;> assumption

theorem TInv.congr' {x' : Proc P M V} {m : M} {c : PC} {l : Link P V}
    (h : TInv slot perm votes p2val p x m c l) (h1 : x'.started = x.started)
    (h2 : x'.active = x.active) (h3 : x'.noPh1 = x.noPh1) (h4 : x.p2s = true → x'.p2s = true)
    (h5 : m ∈ x'.ready → m ∈ x.ready) (h6 : m ∈ x'.done → m ∈ x.done) (h7 : x'.bal = x.bal)
    (h8 : c = .wW2 → x'.curVal = x.curVal) (h9 : AccLe x.lastIss x'.lastIss) :
    TInv slot perm votes p2val p x' m c l where
  unst hs := h.unst (h1 ▸ hs)
  pcAct hc := h2 ▸ h.pcAct hc
  np hn := h.np (h3 ▸ hn)
  ph2 hc := h3 ▸ h.ph2 hc
  w2p2 hc := (h.w2p2 hc).imp h4 (fun h => h3 ▸ h)
  idle := h.idle
  ready ha hm := h.ready (h2 ▸ ha) (h5 hm)
  doneFin ha hm := h.doneFin (h2 ▸ ha) (h6 hm)
  tperm := h.tperm
  tw1 hc := by rw [h7]; exact h.tw1 hc
  trd := h.trd
  tw2 hc := by rw [h7, h8 hc]; exact h.tw2 hc
  tmp hn hc := by rw [h7]; exact h.tmp (h3 ▸ hn) hc
  linkW1 sl hl := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := h.linkW1 sl hl
    exact ⟨a1, h7 ▸ a2, a3, a4.trans h9, a5⟩
  linkW2 b v hl := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := h.linkW2 b v hl
    exact ⟨a1, h7 ▸ a2, a3, a4.trans h9, a5⟩
  snapP2 := h.snapP2
  d3a := h.d3a
  d3b hc hp r := h7 ▸ h.d3b hc hp r
  d3c hc hp r := h7 ▸ h.d3c hc hp r
  d3d := h.d3d
  r1 f hc hl b hb := h.r1 f hc hl b (h7 ▸ hb)

theorem TInv.offIdle {m : M} (hact : x.active = false) :
    TInv slot perm votes p2val p x m .off .idle where
  unst _ := ⟨rfl, rfl⟩
  pcAct h := absurd rfl h
  np _ := Or.inl rfl
  ph2 h := by cases h
  w2p2 h := by rcases h with h | h <;> cases h
  idle _ := rfl
  ready h := by simp [hact] at h
  doneFin h := by simp [hact] at h
  tperm h := by cases h
  tw1 h := by cases h
  trd h := by cases h
  tw2 h := by cases h
  tmp _ h := by rcases h with h | h | h | h <;> cases h
  linkW1 _ h := by cases h
  linkW2 _ _ h := by cases h
  snapP2 _ h := by cases h
  d3a _ _ h := by cases h
  d3b h := by cases h
  d3c h := by cases h
  d3d _ h := by cases h
  r1 _ h := by cases h

theorem TInv.toOff {x' : Proc P M V} {m : M} {c : PC} {l : Link P V}
    (h : TInv slot perm votes p2val p x m c l) (hb : x'.bal = x.bal)
    (hli : x'.lastIss = x.lastIss) (hst : x'.started = x.started) (hact : x'.active = false) :
    TInv slot perm votes p2val p x' m .off l where
  unst hs := ⟨rfl, ((h.unst (hst ▸ hs)).2)⟩
  pcAct h := absurd rfl h
  np _ := Or.inl rfl
  ph2 h := by cases h
  w2p2 h := by rcases h with h | h <;> cases h
  idle h := by rcases h with h | h | h <;> cases h
  ready h := by simp [hact] at h
  doneFin h := by simp [hact] at h
  tperm h := by cases h
  tw1 h := by cases h
  trd h := by cases h
  tw2 h := by cases h
  tmp _ h := by rcases h with h | h | h | h <;> cases h
  linkW1 sl hl := by rw [hb, hli]; exact h.linkW1 sl hl
  linkW2 b v hl := by rw [hb, hli]; exact h.linkW2 b v hl
  snapP2 := h.snapP2
  d3a := h.d3a
  d3b h := by cases h
  d3c h := by cases h
  d3d _ h := by cases h
  r1 _ h := by cases h

/-- Killing all threads (after clearing the link of thread `m0`). -/
theorem LInv.killSetL (h : LInv inp slot perm votes p2val used p x) (m0 : M) :
    LInv inp slot perm votes p2val used p ((x.setL m0 .idle).kill) where
  unst _ := rfl
  balUsed := h.balUsed
  balPos := h.balPos
  p2cur h := by simp [Proc.kill] at h
  p2none h := by simp [Proc.kill] at h
  curInp := h.curInp
  curMax h := by simp [Proc.kill] at h
  lastIss := h.lastIss
  done h := by simp [Proc.kill] at h
  slotMp := h.slotMp
  accLI := h.accLI
  r2 h := by simp [Proc.kill] at h
  thr m := by
    by_cases hm : m = m0
    · subst hm
      simpa [Proc.kill, Proc.setL] using TInv.offIdle (slot := slot) (perm := perm)
        (votes := votes) (p2val := p2val) (p := p) (x := (x.setL m .idle).kill) (m := m) rfl
    · simpa [Proc.kill, Proc.setL, update_of_ne hm] using
        (h.thr m).toOff (x' := (x.setL m0 .idle).kill) rfl rfl rfl rfl

/-- Changing only thread `m0`. -/
theorem LInv.setT (h : LInv inp slot perm votes p2val used p x) (m0 : M) (c : PC) (l : Link P V)
    (ht : TInv slot perm votes p2val p x m0 c l) :
    LInv inp slot perm votes p2val used p (x.setT m0 c l) where
  unst := h.unst
  balUsed := h.balUsed
  balPos := h.balPos
  p2cur := h.p2cur
  p2none := h.p2none
  curInp := h.curInp
  curMax := h.curMax
  lastIss := h.lastIss
  done := h.done
  slotMp := h.slotMp
  accLI := h.accLI
  r2 := h.r2
  thr m := by
    refine TInv.congr (x := x) ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    by_cases hm : m = m0
    · subst hm; simpa [Proc.setT] using ht
    · simpa [Proc.setT, update_of_ne hm] using h.thr m

/-- Changing only the link of thread `m0`. -/
theorem LInv.setL (h : LInv inp slot perm votes p2val used p x) (m0 : M) (l : Link P V)
    (ht : TInv slot perm votes p2val p x m0 (x.pc m0) l) :
    LInv inp slot perm votes p2val used p (x.setL m0 l) where
  unst := h.unst
  balUsed := h.balUsed
  balPos := h.balPos
  p2cur := h.p2cur
  p2none := h.p2none
  curInp := h.curInp
  curMax := h.curMax
  lastIss := h.lastIss
  done := h.done
  slotMp := h.slotMp
  accLI := h.accLI
  r2 := h.r2
  thr m := by
    refine TInv.congr (x := x) ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    by_cases hm : m = m0
    · subst hm; simpa [Proc.setL] using ht
    · simpa [Proc.setL, update_of_ne hm] using h.thr m

/-- If thread `m0` of a process that is not `p1`'s first attempt is at `pc`, then `noPh1` is
false. -/
theorem LInv.noPh1_false (h : LInv inp slot perm votes p2val used p x) (m0 : M)
    (hpc : x.pc m0 = .init ∨ x.pc m0 = .wPerm ∨ x.pc m0 = .wW1 ∨ x.pc m0 = .wRd ∨
      x.pc m0 = .barrier) : x.noPh1 = false := by
  cases hn : x.noPh1
  · rfl
  · have := (h.thr m0).np hn
    rcases hpc with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at this <;> simp at this

/-- Lines 24–33 followed by line 6: thread `m0` joins `ListOfReady`, with the new
`CurrentVal = cv`, `CurrentMaxProp = cm`. -/
theorem LInv.toBarrier (h : LInv inp slot perm votes p2val used p x) (m0 : M) (f : P → Slot V)
    (hpc : x.pc m0 = .wRd) (hl : x.link m0 = .resp (.snap f)) (hmp : ∀ r, (f r).mp ≤ x.bal)
    (cv : V) (cm : ℕ)
    (hcases : (cv = x.curVal ∧ cm = x.curMax) ∨
      (x.p2s = false ∧ x.curMax < cm ∧ p2val cm = some cv ∧ ∃ q', inp q' = cv))
    (hno : ∀ r a z, (f r).acc = some (a, z) → a ≤ cm) :
    LInv inp slot perm votes p2val used p
      { x.setT m0 .barrier .idle with ready := insert m0 x.ready, curVal := cv, curMax := cm } := by
  have hnp : x.noPh1 = false := h.noPh1_false m0 (by simp [hpc])
  have ho := h.thr m0
  rw [hpc, hl] at ho
  have hact : x.active = true := ho.pcAct (by simp)
  have hst : x.started = true := by
    cases hs : x.started
    · simp [h.unst hs] at hact
    · rfl
  have hcm : x.curMax ≤ cm := by
    rcases hcases with ⟨-, rfl⟩ | ⟨-, h2, -⟩
    · exact le_rfl
    · exact h2.le
  -- in the adopting case no thread has reached line 35
  have hnow2 : x.p2s = false → ∀ m, x.pc m ≠ .wW2 ∧ x.pc m ≠ .fin := by
    intro hp2 m
    constructor
    · intro hm; have := (h.thr m).w2p2 (Or.inl hm); simp [hp2, hnp] at this
    · intro hm; have := (h.thr m).w2p2 (Or.inr hm); simp [hp2, hnp] at this
  refine
    { unst := h.unst
      balUsed := h.balUsed
      balPos := h.balPos
      p2cur := ?_
      p2none := h.p2none
      curInp := ?_
      curMax := ?_
      lastIss := h.lastIss
      done := ?_
      slotMp := h.slotMp
      accLI := h.accLI
      r2 := ?_
      thr := ?_ }
  · intro ha h2
    rcases hcases with ⟨rfl, rfl⟩ | ⟨hp2, -⟩
    · exact h.p2cur ha h2
    · simp [Proc.setT, hp2, hnp] at h2
  · rcases hcases with ⟨rfl, rfl⟩ | ⟨-, -, -, hi⟩
    · exact h.curInp
    · exact hi
  · intro ha hn
    rcases hcases with ⟨rfl, rfl⟩ | ⟨-, -, h3, -⟩
    · exact h.curMax ha hn
    · exact Or.inr h3
  · intro ha m hm
    rcases hcases with ⟨rfl, rfl⟩ | ⟨hp2, -⟩
    · exact h.done ha m hm
    · exact absurd ((h.thr m).doneFin ha hm) (hnow2 hp2 m).2
  · intro ha hn m hm b hb1 hb2 r y hv
    rcases Finset.mem_insert.mp hm with rfl | hm
    · obtain ⟨r', a, z, h1, h2⟩ := ho.r1 f rfl rfl b hb2 r y hv
      have := hno r' a z h1
      simp only at hb1
      omega
    · exact h.r2 ha hn m hm b (lt_of_le_of_lt hcm hb1) hb2 r y hv
  · intro m
    by_cases hm : m = m0
    · subst hm
      have hfin : m ∉ x.done := fun hd => by simpa using ho.doneFin hact hd
      have htmp := ho.tmp hnp (Or.inl rfl)
      have hd3 := ho.d3d f rfl rfl
      simp only [Proc.setT, update_self]
      exact
        { unst := by simp [hst]
          pcAct := fun _ => hact
          np := by simp [hnp]
          ph2 := by simp
          w2p2 := by simp
          idle := fun _ => rfl
          ready := fun _ _ => Or.inl rfl
          doneFin := fun _ hd => absurd hd hfin
          tperm := by simp
          tw1 := by simp
          trd := by simp
          tw2 := by simp
          tmp := fun _ _ => htmp
          linkW1 := by simp
          linkW2 := by simp
          snapP2 := by simp
          d3a := by simp
          d3b := fun _ hp r => (hd3 hp r).trans (hmp r)
          d3c := by simp
          d3d := by simp
          r1 := by simp }
    · have := (h.thr m).congr' (x' := { x.setT m0 .barrier .idle with
          ready := insert m0 x.ready, curVal := cv, curMax := cm })
        rfl rfl rfl id (fun hr => by simpa [hm] using hr) id rfl ?_ (AccLe.refl _)
      · simpa [Proc.setT, update_of_ne hm] using this
      · intro hc
        rcases hcases with ⟨rfl, rfl⟩ | ⟨hp2, -⟩
        · rfl
        · exact absurd hc (hnow2 hp2 m).1

/-- Line 35 is invoked by thread `m0` (after the barrier, or in `p1`'s first attempt). -/
theorem LInv.toW2 {p2val' : ℕ → Option V} (h : LInv inp slot perm votes p2val used p x) (m0 : M)
    (hpc : x.pc m0 = .barrier ∨ x.pc m0 = .ph2) (hl : x.link m0 = .idle) (ps : Bool)
    (hps : ps = true ∨ x.noPh1 = true) (hps' : x.p2s = true → ps = true)
    (hext : ∀ a y, p2val a = some y → p2val' a = some y) (hb : p2val' x.bal = some x.curVal) :
    LInv inp slot perm votes p2val' used p
      { x.setT m0 .wW2 (.sent (.w2 x.bal x.curVal)) with
        p2s := ps, lastIss := some (x.bal, x.curVal) } := by
  have ho := h.thr m0
  rw [hl] at ho
  have hact : x.active = true := ho.pcAct (by rcases hpc with h | h <;> simp [h])
  have hst : x.started = true := by
    cases hs : x.started
    · simp [h.unst hs] at hact
    · rfl
  have hli : AccLe x.lastIss (some (x.bal, x.curVal)) := by
    intro a y hy
    exact ⟨x.bal, x.curVal, rfl, (h.lastIss a y hy).2⟩
  refine
    { unst := h.unst
      balUsed := h.balUsed
      balPos := h.balPos
      p2cur := fun _ _ => hb
      p2none := ?_
      curInp := h.curInp
      curMax := fun ha hn => (h.curMax ha hn).imp id (hext _ _)
      lastIss := ?_
      done := h.done
      slotMp := h.slotMp
      accLI := fun m => (h.accLI m).trans hli
      r2 := h.r2
      thr := ?_ }
  · intro _ h1 h2
    rcases hps with hps | hps
    · simp [hps] at h1
    · simp [Proc.setT, hps] at h2
  · intro a y hy
    simp only [Option.some.injEq, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨hb, le_rfl⟩
  · intro m
    by_cases hm : m = m0
    · subst hm
      have hfin : m ∉ x.done := fun hd => by
        have := ho.doneFin hact hd
        rcases hpc with h | h <;> rw [h] at this <;> simp at this
      have hd3 : perm m = p → ∀ r, (slot m r).mp ≤ x.bal := by
        rcases hpc with h | h
        · exact ho.d3b h
        · exact ho.d3c h
      have htmp : x.noPh1 = false → x.bal ≤ (slot m p).mp := by
        intro hn
        rcases hpc with h | h
        · exact ho.tmp hn (Or.inr (Or.inl h))
        · simp [ho.ph2 h] at hn
      simp only [Proc.setT, update_self]
      exact
        { unst := by simp [hst]
          pcAct := fun _ => hact
          np := by simp
          ph2 := by simp
          w2p2 := fun _ => hps
          idle := by simp
          ready := fun _ _ => Or.inr (Or.inl rfl)
          doneFin := fun _ hd => absurd hd hfin
          tperm := by simp
          tw1 := by simp
          trd := by simp
          tw2 := fun _ => Or.inl rfl
          tmp := fun hn _ => htmp hn
          linkW1 := by simp
          linkW2 := by
            intro b v hbv
            simp only [Link.sent.injEq, Op.w2.injEq] at hbv
            obtain ⟨rfl, rfl⟩ := hbv
            exact ⟨h.slotMp m, le_rfl, (h.accLI m).trans hli, AccLe.refl _, hb⟩
          snapP2 := by simp
          d3a := by
            intro b v hbv
            simp only [Link.sent.injEq, Op.w2.injEq] at hbv
            obtain ⟨rfl, rfl⟩ := hbv
            exact hd3
          d3b := by simp
          d3c := by simp
          d3d := by simp
          r1 := by simp }
    · have := ((h.thr m).frame rfl (fun hp => ⟨hp, fun _ => rfl⟩) hext subset_rfl
        (fun _ _ _ hv hn => absurd hv hn)).congr'
        (x' := { x.setT m0 .wW2 (.sent (.w2 x.bal x.curVal)) with
          p2s := ps, lastIss := some (x.bal, x.curVal) })
        rfl rfl rfl hps' id id rfl (fun _ => rfl) hli
      simpa [Proc.setT, update_of_ne hm] using this

/-- Killing all threads. -/
theorem LInv.kill (h : LInv inp slot perm votes p2val used p x) :
    LInv inp slot perm votes p2val used p x.kill where
  unst _ := rfl
  balUsed := h.balUsed
  balPos := h.balPos
  p2cur h := by simp [Proc.kill] at h
  p2none h := by simp [Proc.kill] at h
  curInp := h.curInp
  curMax h := by simp [Proc.kill] at h
  lastIss := h.lastIss
  done h := by simp [Proc.kill] at h
  slotMp := h.slotMp
  accLI := h.accLI
  r2 h := by simp [Proc.kill] at h
  thr m := (h.thr m).toOff (x' := x.kill) rfl rfl rfl rfl

/-- A line-35 write was acknowledged: thread `m0` is done. -/
theorem LInv.toFin (h : LInv inp slot perm votes p2val used p x) (m0 : M)
    (hpc : x.pc m0 = .wW2) (hl : x.link m0 = .resp .ack) :
    LInv inp slot perm votes p2val used p
      { x.setT m0 .fin .idle with done := insert m0 x.done } := by
  have ho := h.thr m0
  rw [hpc, hl] at ho
  have hact : x.active = true := ho.pcAct (by simp)
  have hst : x.started = true := by
    cases hs : x.started
    · simp [h.unst hs] at hact
    · rfl
  have hv : (m0, p, x.bal, x.curVal) ∈ votes := by
    rcases ho.tw2 rfl with h1 | h1 | h1
    · cases h1
    · exact h1.2
    · cases h1
  refine
    { unst := h.unst
      balUsed := h.balUsed
      balPos := h.balPos
      p2cur := h.p2cur
      p2none := h.p2none
      curInp := h.curInp
      curMax := h.curMax
      lastIss := h.lastIss
      done := ?_
      slotMp := h.slotMp
      accLI := h.accLI
      r2 := h.r2
      thr := ?_ }
  · intro ha m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hv
    · exact h.done ha m hm
  · intro m
    by_cases hm : m = m0
    · subst hm
      have htmp := ho.tmp
      have hw := ho.w2p2 (Or.inl rfl)
      simp only [Proc.setT, update_self]
      exact
        { unst := by simp [hst]
          pcAct := fun _ => hact
          np := by simp
          ph2 := by simp
          w2p2 := fun _ => hw
          idle := fun _ => rfl
          ready := fun _ _ => Or.inr (Or.inr rfl)
          doneFin := fun _ _ => rfl
          tperm := by simp
          tw1 := by simp
          trd := by simp
          tw2 := by simp
          tmp := fun hn _ => htmp hn (by simp)
          linkW1 := by simp
          linkW2 := by simp
          snapP2 := by simp
          d3a := by simp
          d3b := by simp
          d3c := by simp
          d3d := by simp
          r1 := by simp }
    · have := (h.thr m).congr' (x' := { x.setT m0 .fin .idle with done := insert m0 x.done })
        rfl rfl rfl id id (fun hr => by simpa [hm] using hr) rfl (fun _ => rfl) (AccLe.refl _)
      simpa [Proc.setT, update_of_ne hm] using this

/-- A memory operation of thread `m0` takes effect: the link of `m0` changes and the global state
changes only at memory `m0`. -/
theorem LInv.effThread {slot' : M → P → Slot V} {perm' : M → P} {votes' : Set (M × P × ℕ × V)}
    (h : LInv inp slot perm votes p2val used p x) (m0 : M) (l : Link P V)
    (hslot : ∀ m, m ≠ m0 → slot' m = slot m) (hperm : ∀ m, m ≠ m0 → perm' m = perm m)
    (hvotes : votes ⊆ votes') (hnew : ∀ m r b y, (m, r, b, y) ∈ votes' → (m, r, b, y) ∉ votes →
      m = m0)
    (hmp : (slot' m0 p).mp ≤ x.bal) (hacc : AccLe (slot' m0 p).acc x.lastIss)
    (hr2 : x.active = true → x.noPh1 = false → m0 ∈ x.ready → ∀ b, x.curMax < b → b < x.bal →
      ∀ r y, (m0, r, b, y) ∉ votes')
    (ht : TInv slot' perm' votes' p2val p x m0 (x.pc m0) l) :
    LInv inp slot' perm' votes' p2val used p (x.setL m0 l) := by
  refine
    { unst := h.unst
      balUsed := h.balUsed
      balPos := h.balPos
      p2cur := h.p2cur
      p2none := h.p2none
      curInp := h.curInp
      curMax := h.curMax
      lastIss := h.lastIss
      done := fun ha m hm => hvotes (h.done ha m hm)
      slotMp := ?_
      accLI := ?_
      r2 := ?_
      thr := ?_ }
  · intro m
    by_cases hm : m = m0
    · subst hm; exact hmp
    · rw [hslot m hm]; exact h.slotMp m
  · intro m
    by_cases hm : m = m0
    · subst hm; exact hacc
    · rw [hslot m hm]; exact h.accLI m
  · intro ha hn m hm b hb1 hb2 r y hv
    by_cases hm0 : m = m0
    · subst hm0; exact hr2 ha hn hm b hb1 hb2 r y hv
    · by_cases hold : (m, r, b, y) ∈ votes
      · exact h.r2 ha hn m hm b hb1 hb2 r y hold
      · exact hm0 (hnew m r b y hv hold)
  · intro m
    refine TInv.congr (x := x) ?_ rfl rfl rfl rfl rfl rfl rfl rfl rfl
    by_cases hm : m = m0
    · subst hm; simpa [Proc.setL] using ht
    · simp only [Proc.setL, update_of_ne hm]
      exact (h.thr m).frame (by rw [hslot m hm])
        (fun hp => ⟨(hperm m hm) ▸ hp, fun r => by rw [hslot m hm]⟩) (fun _ _ h => h) hvotes
        (fun r b y hv hn => absurd (hnew m r b y hv hn) hm)

theorem SafeAt.mono {s s' : State P M V} {w : V} {c : ℕ} (h : SafeAt s w c)
    (hslot : ∀ m r, (s.slot m r).mp ≤ (s'.slot m r).mp) (hv : s'.votes = s.votes) :
    SafeAt s' w c := by
  intro b hb0 hb
  obtain ⟨Q, hQ, hQm⟩ := h b hb0 hb
  refine ⟨Q, hQ, fun m hm => ?_⟩
  rw [hv]
  rcases hQm m hm with h1 | ⟨h1, r, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, r, lt_of_lt_of_le h2 (hslot m r)⟩

end Helpers

variable {p1 : P} {inp : P → V} {s : State P M V}

/-- For steps that change only the local state of `q`. -/
theorem Inv.of_pr (h : Inv p1 inp s) (q : P) (X : Proc P M V)
    (hst : X.started = (s.pr q).started) (hbal : X.bal = (s.pr q).bal)
    (hX : LInv inp s.slot s.perm s.votes s.p2val s.used q X) :
    Inv p1 inp { s with pr := update s.pr q X } where
  p2zero := h.p2zero
  p2used := h.p2used
  p2inp := h.p2inp
  safe := h.safe
  voteP2 := h.voteP2
  accMono := h.accMono
  slotP2 := h.slotP2
  dec := h.dec
  fresh hs := by
    apply h.fresh
    by_cases hq : p1 = q
    · subst hq; simpa [hst] using hs
    · simpa [update_of_ne hq] using hs
  inj p r hpr hp hr := by
    by_cases hpq : p = q
    · subst hpq
      simp only [update_self, update_of_ne (Ne.symm hpr)] at hp hr ⊢
      rw [hbal]; exact h.inj p r hpr (hst ▸ hp) hr
    · by_cases hrq : r = q
      · subst hrq
        simp only [update_self, update_of_ne hpq] at hp hr ⊢
        rw [hbal]; exact h.inj p r hpr hp (hst ▸ hr)
      · simp only [update_of_ne hpq, update_of_ne hrq] at hp hr ⊢
        exact h.inj p r hpr hp hr
  loc p := by
    by_cases hpq : p = q
    · subst hpq; simpa using hX
    · simpa [update_of_ne hpq] using h.loc p

/-- Close a `TInv` goal from the old thread invariant `ho` and the context. -/
macro "tinv_tac " ho:term : tactic => `(tactic| (
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := $ho
  constructor <;> intros <;> subst_vars <;> simp_all <;> aesop))

theorem inv_invPerm (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .init)
    (hl : (s.pr q).link m0 = .idle) :
    Inv p1 inp { s with pr := update s.pr q ((s.pr q).setT m0 .wPerm (.sent .perm)) } := by
  refine h.of_pr q _ rfl rfl ((h.loc q).setT m0 _ _ ?_)
  have ho := (h.loc q).thr m0
  rw [hpc, hl] at ho
  tinv_tac ho

theorem inv_dlvW1 (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .wW1)
    (hl : (s.pr q).link m0 = .resp .ack) :
    Inv p1 inp { s with pr := update s.pr q ((s.pr q).setT m0 .wRd (.sent .rd)) } := by
  refine h.of_pr q _ rfl rfl ((h.loc q).setT m0 _ _ ?_)
  have ho := (h.loc q).thr m0
  rw [hpc, hl] at ho
  tinv_tac ho

theorem inv_dlvPerm (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .wPerm)
    (hl : (s.pr q).link m0 = .resp .ack) :
    Inv p1 inp { s with pr := update s.pr q ((s.pr q).setT m0 .wW1
      (.sent (.w1 ⟨(s.pr q).bal, line21 .repaired (s.pr q).lastIss⟩))) } := by
  refine h.of_pr q _ rfl rfl ((h.loc q).setT m0 _ _ ?_)
  have ho := (h.loc q).thr m0
  rw [hpc, hl] at ho
  have e1 := (h.loc q).slotMp m0
  have e2 := (h.loc q).accLI m0
  have e3 := (h.loc q).lastIss
  have e4 := AccLe.refl (s.pr q).lastIss
  simp only [line21]
  tinv_tac ho

theorem inv_kill (h : Inv p1 inp s) (q : P) (m0 : M) :
    Inv p1 inp { s with pr := update s.pr q (((s.pr q).setL m0 .idle).kill) } :=
  h.of_pr q _ rfl rfl ((h.loc q).killSetL m0)

theorem inv_discard (h : Inv p1 inp s) (q : P) (m0 : M) (r : Resp P V)
    (hpc : (s.pr q).pc m0 ≠ .wPerm ∧ (s.pr q).pc m0 ≠ .wW1 ∧ (s.pr q).pc m0 ≠ .wRd ∧
        (s.pr q).pc m0 ≠ .wW2)
    (hl : (s.pr q).link m0 = .resp r) :
    Inv p1 inp { s with pr := update s.pr q ((s.pr q).setL m0 .idle) } := by
  refine h.of_pr q _ rfl rfl ((h.loc q).setL m0 _ ?_)
  have ho := (h.loc q).thr m0
  rw [hl] at ho
  obtain ⟨hc1, hc2, hc3, hc4⟩ := hpc
  tinv_tac ho

theorem inv_dlvRdNone (h : Inv p1 inp s) (q : P) (m0 : M) (f : P → Slot V)
    (hpc : (s.pr q).pc m0 = .wRd) (hl : (s.pr q).link m0 = .resp (.snap f))
    (hmp : ∀ r, (f r).mp ≤ (s.pr q).bal) (hn : ∀ r, (f r).acc = none) :
    Inv p1 inp { s with
      pr := update s.pr q
        { (s.pr q).setT m0 .barrier .idle with ready := insert m0 (s.pr q).ready } } :=
  h.of_pr q _ rfl rfl ((h.loc q).toBarrier m0 f hpc hl hmp _ _ (Or.inl ⟨rfl, rfl⟩)
    (fun r a z hr => by simp [hn r] at hr))

theorem inv_dlvRdKeep (h : Inv p1 inp s) (q : P) (m0 : M) (f : P → Slot V) (_r : P) (a : ℕ)
    (_y : V) (hpc : (s.pr q).pc m0 = .wRd) (hl : (s.pr q).link m0 = .resp (.snap f))
    (hmp : ∀ r, (f r).mp ≤ (s.pr q).bal)
    (hmax : ∀ r' a' y', (f r').acc = some (a', y') → a' ≤ a) (hle : a ≤ (s.pr q).curMax) :
    Inv p1 inp { s with
      pr := update s.pr q
        { (s.pr q).setT m0 .barrier .idle with ready := insert m0 (s.pr q).ready } } :=
  h.of_pr q _ rfl rfl ((h.loc q).toBarrier m0 f hpc hl hmp _ _ (Or.inl ⟨rfl, rfl⟩)
    (fun r' a' z hr => (hmax r' a' z hr).trans hle))

theorem inv_dlvRdAdopt (h : Inv p1 inp s) (q : P) (m0 : M) (f : P → Slot V) (r : P) (a : ℕ)
    (y : V) (hpc : (s.pr q).pc m0 = .wRd) (hl : (s.pr q).link m0 = .resp (.snap f))
    (hmp : ∀ r, (f r).mp ≤ (s.pr q).bal) (hr : (f r).acc = some (a, y))
    (hmax : ∀ r' a' y', (f r').acc = some (a', y') → a' ≤ a) (hgt : (s.pr q).curMax < a)
    (hp2 : (s.pr q).p2s = false) :
    Inv p1 inp { s with
      pr := update s.pr q
        { (s.pr q).setT m0 .barrier .idle with
        ready := insert m0 (s.pr q).ready, curVal := y, curMax := a } } := by
  have hy : s.p2val a = some y := ((h.loc q).thr m0).snapP2 f hl r a y hr
  exact h.of_pr q _ rfl rfl ((h.loc q).toBarrier m0 f hpc hl hmp _ _
    (Or.inr ⟨hp2, hgt, hy, h.p2inp a y hy⟩) hmax)

theorem inv_passLate (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .barrier)
    (hl : (s.pr q).link m0 = .idle) (hp2 : (s.pr q).p2s = true) :
    Inv p1 inp { s with
      pr := update s.pr q
        { (s.pr q).setT m0 .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
          lastIss := some ((s.pr q).bal, (s.pr q).curVal) } } := by
  have hact : (s.pr q).active = true := ((h.loc q).thr m0).pcAct (by simp [hpc])
  have := (h.loc q).toW2 m0 (Or.inl hpc) hl true (Or.inl rfl) (fun _ => rfl) (fun _ _ h => h)
    ((h.loc q).p2cur hact (Or.inl hp2))
  rw [← hp2] at this
  exact h.of_pr q _ rfl rfl this

theorem inv_issueFirst (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .ph2)
    (hl : (s.pr q).link m0 = .idle) :
    Inv p1 inp { s with
      pr := update s.pr q
        { (s.pr q).setT m0 .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
          lastIss := some ((s.pr q).bal, (s.pr q).curVal) } } := by
  have hact : (s.pr q).active = true := ((h.loc q).thr m0).pcAct (by simp [hpc])
  have hn := ((h.loc q).thr m0).ph2 hpc
  have := (h.loc q).toW2 m0 (Or.inr hpc) hl (s.pr q).p2s (Or.inr hn) id (fun _ _ h => h)
    ((h.loc q).p2cur hact (Or.inr hn))
  exact h.of_pr q _ rfl rfl this

theorem inv_passFirst (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .barrier)
    (hl : (s.pr q).link m0 = .idle) (hmaj : Maj (s.pr q).ready) (hp2 : (s.pr q).p2s = false) :
    Inv p1 inp { s with
      pr := update s.pr q
        { (s.pr q).setT m0 .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
          p2s := true, lastIss := some ((s.pr q).bal, (s.pr q).curVal) }
      p2val := update s.p2val (s.pr q).bal (some (s.pr q).curVal) } := by
  have hx := h.loc q
  have hact : (s.pr q).active = true := (hx.thr m0).pcAct (by simp [hpc])
  have hst : (s.pr q).started = true := by
    cases hs : (s.pr q).started
    · simp [hx.unst hs] at hact
    · rfl
  have hnp : (s.pr q).noPh1 = false := hx.noPh1_false m0 (by simp [hpc])
  have hnone : s.p2val (s.pr q).bal = none := hx.p2none hact hp2 hnp
  have hext : ∀ a y, s.p2val a = some y →
      update s.p2val (s.pr q).bal (some (s.pr q).curVal) a = some y := by
    intro a y hy
    have : a ≠ (s.pr q).bal := by rintro rfl; simp [hnone] at hy
    simpa [update_of_ne this] using hy
  have hpos := hx.balPos hst
  -- SafeAt for the new phase-2 value
  have hsafe : SafeAt s (s.pr q).curVal (s.pr q).bal := by
    intro b hb0 hb
    by_cases hbm : b < (s.pr q).curMax
    · rcases hx.curMax hact hnp with h0 | h0
      · omega
      · exact h.safe _ _ h0 b hb0 hbm
    · refine ⟨(s.pr q).ready, hmaj, fun m hm => ?_⟩
      by_cases hv : ∃ r y, (m, r, b, y) ∈ s.votes
      · obtain ⟨r, y, hv⟩ := hv
        left
        refine ⟨r, ?_⟩
        have hbeq : b = (s.pr q).curMax := by
          by_contra hne
          exact hx.r2 hact hnp m hm b (by omega) hb r y hv
        have h1 := h.voteP2 m r b y hv
        rcases hx.curMax hact hnp with h0 | h0
        · omega
        · rw [← hbeq, h1] at h0
          simp only [Option.some.injEq] at h0
          rwa [← h0]
      · push Not at hv
        right
        refine ⟨hv, q, ?_⟩
        have := (hx.thr m).tmp hnp (Or.inr ((hx.thr m).ready hact hm))
        omega
  refine
    { p2zero := by
        dsimp only; rw [update_of_ne (by omega)]; exact h.p2zero
      p2used := by
        intro b w hbw
        dsimp only at hbw ⊢
        by_cases hb : b = (s.pr q).bal
        · subst hb; exact hx.balUsed hst
        · rw [update_of_ne hb] at hbw; exact h.p2used b w hbw
      p2inp := by
        intro b w hbw
        dsimp only at hbw ⊢
        by_cases hb : b = (s.pr q).bal
        · subst hb; simp only [update_self, Option.some.injEq] at hbw; subst hbw; exact hx.curInp
        · rw [update_of_ne hb] at hbw; exact h.p2inp b w hbw
      safe := by
        intro c w hcw
        dsimp only at hcw ⊢
        by_cases hc : c = (s.pr q).bal
        · subst hc; simp only [update_self, Option.some.injEq] at hcw; subst hcw; exact hsafe
        · rw [update_of_ne hc] at hcw; exact h.safe c w hcw
      voteP2 := fun m r b y hv => hext _ _ (h.voteP2 m r b y hv)
      accMono := h.accMono
      slotP2 := fun m r a y hy => hext _ _ (h.slotP2 m r a y hy)
      dec := h.dec
      fresh := ?_
      inj := ?_
      loc := ?_ }
  · intro hs
    apply h.fresh
    by_cases hq : p1 = q
    · subst hq; simpa [Proc.setT] using hs
    · simpa [update_of_ne hq] using hs
  · intro p r hpr hp hr
    by_cases hpq : p = q
    · subst hpq
      simp only [update_self, update_of_ne (Ne.symm hpr)] at hp hr ⊢
      exact h.inj p r hpr hp hr
    · by_cases hrq : r = q
      · subst hrq
        simp only [update_self, update_of_ne hpq] at hp hr ⊢
        exact h.inj p r hpr hp hr
      · simp only [update_of_ne hpq, update_of_ne hrq] at hp hr ⊢
        exact h.inj p r hpr hp hr
  · intro p
    by_cases hpq : p = q
    · subst hpq
      simpa using hx.toW2 m0 (Or.inl hpc) hl true (Or.inl rfl) (fun _ => rfl) hext (by simp)
    · simp only [update_of_ne hpq]
      refine (h.loc p).frame (fun _ => rfl) (fun _ hp => ⟨hp, fun _ => rfl⟩) subset_rfl hext ?_
        subset_rfl (fun _ _ _ _ hv hn => absurd hv hn)
      intro hap
      have hsp : (s.pr p).started = true := by
        cases hs : (s.pr p).started
        · simp [(h.loc p).unst hs] at hap
        · rfl
      rw [update_of_ne (h.inj p q hpq hsp hst)]

theorem inv_effW1nak (h : Inv p1 inp s) (q : P) (m0 : M) (sl : Slot V)
    (hl : (s.pr q).link m0 = .sent (.w1 sl)) :
    Inv p1 inp { s with pr := update s.pr q ((s.pr q).setL m0 (.resp .nak)) } := by
  refine h.of_pr q _ rfl rfl ((h.loc q).setL m0 _ ?_)
  have ho := (h.loc q).thr m0
  rw [hl] at ho
  tinv_tac ho

theorem inv_effW2nak (h : Inv p1 inp s) (q : P) (m0 : M) (b : ℕ) (v : V)
    (hl : (s.pr q).link m0 = .sent (.w2 b v)) :
    Inv p1 inp { s with pr := update s.pr q ((s.pr q).setL m0 (.resp .nak)) } := by
  refine h.of_pr q _ rfl rfl ((h.loc q).setL m0 _ ?_)
  have ho := (h.loc q).thr m0
  rw [hl] at ho
  tinv_tac ho

theorem inv_dlvW2 (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .wW2)
    (hl : (s.pr q).link m0 = .resp .ack) :
    Inv p1 inp { s with
      pr := update s.pr q { (s.pr q).setT m0 .fin .idle with done := insert m0 (s.pr q).done } } :=
  h.of_pr q _ rfl rfl ((h.loc q).toFin m0 hpc hl)

theorem inv_dlvW2Decide (h : Inv p1 inp s) (q : P) (m0 : M) (hpc : (s.pr q).pc m0 = .wW2)
    (hl : (s.pr q).link m0 = .resp .ack) (hmaj : Maj (insert m0 (s.pr q).done)) :
    Inv p1 inp { s with
      pr := update s.pr q
        ({ (s.pr q).setT m0 .fin .idle with done := insert m0 (s.pr q).done }).kill
      decs := (s.pr q).curVal :: s.decs } := by
  have h1 := h.of_pr q _ (by rfl) (by rfl) ((h.loc q).toFin m0 hpc hl).kill
  have hx := h.loc q
  have ho := hx.thr m0
  rw [hpc, hl] at ho
  have hact : (s.pr q).active = true := ho.pcAct (by simp)
  have hv : (m0, q, (s.pr q).bal, (s.pr q).curVal) ∈ s.votes := by
    rcases ho.tw2 rfl with h1 | h1 | h1
    · cases h1
    · exact h1.2
    · cases h1
  refine { h1 with dec := ?_ }
  intro v hv'
  rcases List.mem_cons.mp hv' with rfl | hv'
  · refine ⟨q, (s.pr q).bal, insert m0 (s.pr q).done, hmaj, fun m hm => ?_⟩
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hv
    · exact hx.done hact m hm
  · exact h.dec v hv'

/-- `p1`, if it has not started, has no operation in flight. -/
theorem Inv.unstarted_idle (h : Inv p1 inp s) (q : P) (hs : (s.pr q).started = false) (m : M) :
    (s.pr q).link m = .idle :=
  (((h.loc q).thr m).unst hs).2

theorem inv_effPerm (h : Inv p1 inp s) (q : P) (m0 : M) (hl : (s.pr q).link m0 = .sent .perm) :
    Inv p1 inp { s with
      perm := update s.perm m0 q
      pr := update s.pr q ((s.pr q).setL m0 (.resp .ack)) } := by
  have hx := h.loc q
  have ho := hx.thr m0
  rw [hl] at ho
  have hst : (s.pr q).started = true := by
    cases hs : (s.pr q).started
    · have := h.unstarted_idle q hs m0; rw [hl] at this; cases this
    · rfl
  have hX : LInv inp s.slot (update s.perm m0 q) s.votes s.p2val s.used q
      ((s.pr q).setL m0 (.resp .ack)) := by
    refine hx.effThread m0 _ (fun _ _ => rfl) (fun m hm => update_of_ne hm _ _) subset_rfl
      (fun _ _ _ _ hv hn => absurd hv hn) (hx.slotMp m0) (hx.accLI m0)
      (fun ha hn hm => hx.r2 ha hn m0 hm) ?_
    tinv_tac ho
  refine
    { p2zero := h.p2zero
      p2used := h.p2used
      p2inp := h.p2inp
      safe := h.safe
      voteP2 := h.voteP2
      accMono := h.accMono
      slotP2 := h.slotP2
      dec := h.dec
      fresh := ?_
      inj := ?_
      loc := ?_ }
  · intro hs m hm r
    dsimp only at hs hm ⊢
    by_cases hq : p1 = q
    · subst hq; simp [Proc.setL, hst] at hs
    · rw [update_of_ne hq] at hs
      by_cases hmm : m = m0
      · subst hmm; simp at hm; exact absurd hm.symm hq
      · rw [update_of_ne hmm] at hm; exact h.fresh hs m hm r
  · intro p r hpr hp hr
    by_cases hpq : p = q
    · subst hpq
      simp only [update_self, update_of_ne (Ne.symm hpr)] at hp hr ⊢
      exact h.inj p r hpr hp hr
    · by_cases hrq : r = q
      · subst hrq
        simp only [update_self, update_of_ne hpq] at hp hr ⊢
        exact h.inj p r hpr hp hr
      · simp only [update_of_ne hpq, update_of_ne hrq] at hp hr ⊢
        exact h.inj p r hpr hp hr
  · intro p
    by_cases hpq : p = q
    · subst hpq; simpa using hX
    · simp only [update_of_ne hpq]
      refine (h.loc p).frame (fun _ => rfl) ?_ subset_rfl (fun _ _ h => h) (fun _ => rfl)
        subset_rfl (fun _ _ _ _ hv hn => absurd hv hn)
      intro m hm
      by_cases hmm : m = m0
      · subst hmm; simp at hm; exact absurd hm.symm hpq
      · exact ⟨by simpa [update_of_ne hmm] using hm, fun _ => rfl⟩

theorem inv_effW1 (h : Inv p1 inp s) (q : P) (m0 : M) (sl : Slot V)
    (hl : (s.pr q).link m0 = .sent (.w1 sl)) (hp : s.perm m0 = q) :
    Inv p1 inp { s with
      slot := update s.slot m0 (update (s.slot m0) q sl)
      pr := update s.pr q ((s.pr q).setL m0 (.resp .ack)) } := by
  have hx := h.loc q
  have ho := hx.thr m0
  rw [hl] at ho
  obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := ho.linkW1 sl rfl
  have hst : (s.pr q).started = true := by
    cases hs : (s.pr q).started
    · have := h.unstarted_idle q hs m0; rw [hl] at this; cases this
    · rfl
  have hslot : ∀ m r, update s.slot m0 (update (s.slot m0) q sl) m r =
      if m = m0 ∧ r = q then sl else s.slot m r := by
    intro m r
    by_cases hm : m = m0
    · subst hm; by_cases hr : r = q
      · subst hr; simp
      · simp [hr]
    · simp [hm]
  have hX : LInv inp (update s.slot m0 (update (s.slot m0) q sl)) s.perm s.votes s.p2val s.used q
      ((s.pr q).setL m0 (.resp .ack)) := by
    refine hx.effThread m0 _ (fun m hm => update_of_ne hm _ _) (fun _ _ => rfl) subset_rfl
      (fun _ _ _ _ hv hn => absurd hv hn) (by simpa using hl2) (by simpa using hl4)
      (fun ha hn hm => hx.r2 ha hn m0 hm) ?_
    have e1 : (update s.slot m0 (update (s.slot m0) q sl) m0 q) = sl := by simp
    have e2 : ∀ r, r ≠ q → update s.slot m0 (update (s.slot m0) q sl) m0 r = s.slot m0 r :=
      fun r hr => by simp [hr]
    tinv_tac ho
  refine
    { p2zero := h.p2zero
      p2used := h.p2used
      p2inp := h.p2inp
      safe := fun c w hcw => (h.safe c w hcw).mono (fun m r => by
        dsimp only; rw [hslot]; split_ifs with hc
        · obtain ⟨rfl, rfl⟩ := hc; exact hl1
        · exact le_rfl) rfl
      voteP2 := h.voteP2
      accMono := ?_
      slotP2 := ?_
      dec := h.dec
      fresh := ?_
      inj := ?_
      loc := ?_ }
  · intro m r b y hv
    dsimp only; rw [hslot]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact (h.accMono _ _ _ _ hv).trans hl3
    · exact h.accMono _ _ _ _ hv
  · intro m r a y hy
    dsimp only at hy; rw [hslot] at hy; split_ifs at hy with hc
    · exact hl5 a y hy
    · exact h.slotP2 m r a y hy
  · intro hs m hm r
    dsimp only at hs hm ⊢
    have hq : p1 ≠ q := by
      rintro rfl; simp [Proc.setL, hst] at hs
    rw [update_of_ne hq] at hs
    rw [hslot]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact absurd (hm.symm.trans hp) hq
    · exact h.fresh hs m hm r
  · intro p r hpr hp hr
    by_cases hpq : p = q
    · subst hpq
      simp only [update_self, update_of_ne (Ne.symm hpr)] at hp hr ⊢
      exact h.inj p r hpr hp hr
    · by_cases hrq : r = q
      · subst hrq
        simp only [update_self, update_of_ne hpq] at hp hr ⊢
        exact h.inj p r hpr hp hr
      · simp only [update_of_ne hpq, update_of_ne hrq] at hp hr ⊢
        exact h.inj p r hpr hp hr
  · intro p
    by_cases hpq : p = q
    · subst hpq; simpa using hX
    · simp only [update_of_ne hpq]
      refine (h.loc p).frame (fun m => by rw [hslot]; simp [hpq]) ?_ subset_rfl (fun _ _ h => h)
        (fun _ => rfl) subset_rfl (fun _ _ _ _ hv hn => absurd hv hn)
      intro m hm
      refine ⟨hm, fun r => ?_⟩
      rw [hslot]; split_ifs with hc
      · obtain ⟨hm0, -⟩ := hc; subst hm0; exact absurd (hm.symm.trans hp) hpq
      · rfl

theorem inv_effW2 (h : Inv p1 inp s) (q : P) (m0 : M) (b : ℕ) (v : V)
    (hl : (s.pr q).link m0 = .sent (.w2 b v)) (hp : s.perm m0 = q) :
    Inv p1 inp { s with
      slot := update s.slot m0 (update (s.slot m0) q ⟨b, some (b, v)⟩)
      pr := update s.pr q ((s.pr q).setL m0 (.resp .ack))
      votes := insert (m0, q, b, v) s.votes } := by
  have hx := h.loc q
  have ho := hx.thr m0
  rw [hl] at ho
  obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := ho.linkW2 b v rfl
  have hd3 := ho.d3a b v rfl hp
  have hst : (s.pr q).started = true := by
    cases hs : (s.pr q).started
    · have := h.unstarted_idle q hs m0; rw [hl] at this; cases this
    · rfl
  set sl : Slot V := ⟨b, some (b, v)⟩ with hsl
  have hslot : ∀ m r, update s.slot m0 (update (s.slot m0) q sl) m r =
      if m = m0 ∧ r = q then sl else s.slot m r := by
    intro m r
    by_cases hm : m = m0
    · subst hm; by_cases hr : r = q
      · subst hr; simp
      · simp [hr]
    · simp [hm]
  have hmono : ∀ m r, (s.slot m r).mp ≤ (update s.slot m0 (update (s.slot m0) q sl) m r).mp := by
    intro m r; rw [hslot]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hl1
    · exact le_rfl
  have hvmem : ∀ m r b' y, (m, r, b', y) ∈ insert (m0, q, b, v) s.votes ↔
      (m = m0 ∧ r = q ∧ b' = b ∧ y = v) ∨ (m, r, b', y) ∈ s.votes := by
    intro m r b' y; simp
  -- the new vote has ballot `bal` when thread `m0` is a member of `ListOfReady`
  have hbal : (s.pr q).active = true → m0 ∈ (s.pr q).ready → b = (s.pr q).bal := by
    intro ha hm
    rcases ho.ready ha hm with h1 | h1 | h1
    · have := ho.idle (Or.inl h1); cases this
    · rcases ho.tw2 h1 with h2 | h2 | h2
      · simp only [Link.sent.injEq, Op.w2.injEq] at h2; exact h2.1
      · cases h2.1
      · cases h2
    · have := ho.idle (Or.inr (Or.inr h1)); cases this
  have hX : LInv inp (update s.slot m0 (update (s.slot m0) q sl)) s.perm
      (insert (m0, q, b, v) s.votes) s.p2val s.used q ((s.pr q).setL m0 (.resp .ack)) := by
    refine hx.effThread m0 _ (fun m hm => update_of_ne hm _ _) (fun _ _ => rfl)
      (Set.subset_insert _ _) ?_ (by simpa using hl2) (by simpa using hl4) ?_ ?_
    · intro m r b' y hv hn
      rcases (hvmem m r b' y).mp hv with h1 | h1
      · exact h1.1
      · exact absurd h1 hn
    · intro ha hn hm b' hb1 hb2 r y hv
      rcases (hvmem m0 r b' y).mp hv with h1 | h1
      · obtain ⟨-, -, rfl, -⟩ := h1
        rw [hbal ha hm] at hb2; exact lt_irrefl _ hb2
      · exact hx.r2 ha hn m0 hm b' hb1 hb2 r y h1
    · have e1 : (update s.slot m0 (update (s.slot m0) q sl) m0 q) = sl := by simp
      have e2 : ∀ r, r ≠ q → update s.slot m0 (update (s.slot m0) q sl) m0 r = s.slot m0 r :=
        fun r hr => by simp [hr]
      tinv_tac ho
  refine
    { p2zero := h.p2zero
      p2used := h.p2used
      p2inp := h.p2inp
      safe := ?_
      voteP2 := ?_
      accMono := ?_
      slotP2 := ?_
      dec := fun w hw => by
        obtain ⟨p, b', W, hW, hWm⟩ := h.dec w hw
        exact ⟨p, b', W, hW, fun m hm => Set.mem_insert_of_mem _ (hWm m hm)⟩
      fresh := ?_
      inj := ?_
      loc := ?_ }
  · intro c w hcw b' hb0 hb'
    obtain ⟨Q, hQ, hQm⟩ := h.safe c w hcw b' hb0 hb'
    refine ⟨Q, hQ, fun m hm => ?_⟩
    rcases hQm m hm with ⟨r, h1⟩ | ⟨h1, r, h2⟩
    · exact Or.inl ⟨r, Set.mem_insert_of_mem _ h1⟩
    · right
      refine ⟨fun r' y hv => ?_, r, lt_of_lt_of_le h2 (hmono m r)⟩
      rcases (hvmem m r' b' y).mp hv with h3 | h3
      · obtain ⟨rfl, -, rfl, -⟩ := h3
        have := hd3 r; omega
      · exact h1 r' y h3
  · intro m r b' y hv
    rcases (hvmem m r b' y).mp hv with h1 | h1
    · obtain ⟨-, -, rfl, rfl⟩ := h1; exact hl5
    · exact h.voteP2 m r b' y h1
  · intro m r b' y hv
    dsimp only; rw [hslot]
    rcases (hvmem m r b' y).mp hv with h1 | h1
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h1; simp [sl, AccLe.refl]
    · split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; exact (h.accMono _ _ _ _ h1).trans hl3
      · exact h.accMono _ _ _ _ h1
  · intro m r a y hy
    dsimp only at hy; rw [hslot] at hy; split_ifs at hy with hc
    · simp only [sl, Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy; exact hl5
    · exact h.slotP2 m r a y hy
  · intro hs m hm r
    dsimp only at hs hm ⊢
    have hq : p1 ≠ q := by
      rintro rfl; simp [Proc.setL, hst] at hs
    rw [update_of_ne hq] at hs
    rw [hslot]; split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact absurd (hm.symm.trans hp) hq
    · exact h.fresh hs m hm r
  · intro p r hpr hp hr
    by_cases hpq : p = q
    · subst hpq
      simp only [update_self, update_of_ne (Ne.symm hpr)] at hp hr ⊢
      exact h.inj p r hpr hp hr
    · by_cases hrq : r = q
      · subst hrq
        simp only [update_self, update_of_ne hpq] at hp hr ⊢
        exact h.inj p r hpr hp hr
      · simp only [update_of_ne hpq, update_of_ne hrq] at hp hr ⊢
        exact h.inj p r hpr hp hr
  · intro p
    by_cases hpq : p = q
    · subst hpq; simpa using hX
    · simp only [update_of_ne hpq]
      refine (h.loc p).frame (fun m => by rw [hslot]; simp [hpq]) ?_ subset_rfl (fun _ _ h => h)
        (fun _ => rfl) (Set.subset_insert _ _) ?_
      · intro m hm
        refine ⟨hm, fun r => ?_⟩
        rw [hslot]; split_ifs with hc
        · obtain ⟨hm0, -⟩ := hc; subst hm0; exact absurd (hm.symm.trans hp) hpq
        · rfl
      · intro m r b' y hv hn
        rcases (hvmem m r b' y).mp hv with h1 | h1
        · obtain ⟨rfl, -, rfl, -⟩ := h1; exact hd3 p
        · exact absurd h1 hn

theorem inv_startNext (h : Inv p1 inp s) (q : P) (b : ℕ)
    (hact : (s.pr q).active = false) (hb : b ∉ s.used) (hlt : (s.pr q).bal < b) (h2 : 2 ≤ b) :
    Inv p1 inp { s with
      pr := update s.pr q
        { s.pr q with
          active := true, started := true, noPh1 := false, bal := b,
          curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
          pc := fun _ => .init }
      used := insert b s.used } := by
  have hx := h.loc q
  have hnone : s.p2val b = none := by
    cases hpb : s.p2val b with
    | none => rfl
    | some w => exact absurd (h.p2used b w hpb) hb
  set X : Proc P M V := { s.pr q with
    active := true, started := true, noPh1 := false, bal := b,
    curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
    pc := fun _ => .init } with hXdef
  have hX : LInv inp s.slot s.perm s.votes s.p2val (insert b s.used) q X := by
    refine
      { unst := by simp [X]
        balUsed := fun _ => Finset.mem_insert_self _ _
        balPos := fun _ => by simp only [X]; omega
        p2cur := by simp [X]
        p2none := fun _ _ _ => hnone
        curInp := ⟨q, rfl⟩
        curMax := fun _ _ => Or.inl rfl
        lastIss := fun a y hy => by
          obtain ⟨h1, h3⟩ := hx.lastIss a y hy
          exact ⟨h1, by simp only [X]; omega⟩
        done := by simp [X]
        slotMp := fun m => by have := hx.slotMp m; simp only [X]; omega
        accLI := hx.accLI
        r2 := by simp [X]
        thr := fun m => ?_ }
    have ho := hx.thr m
    exact
      { unst := by simp [X]
        pcAct := fun _ => rfl
        np := by simp [X]
        ph2 := by simp
        w2p2 := by simp
        idle := by simp
        ready := by simp [X]
        doneFin := by simp [X]
        tperm := by simp
        tw1 := by simp
        trd := by simp
        tw2 := by simp
        tmp := by simp
        linkW1 := fun sl hl => by
          obtain ⟨a1, a2, a3, a4, a5⟩ := ho.linkW1 sl hl
          exact ⟨a1, by simp only [X]; omega, a3, a4, a5⟩
        linkW2 := fun b' v hl => by
          obtain ⟨a1, a2, a3, a4, a5⟩ := ho.linkW2 b' v hl
          exact ⟨a1, by simp only [X]; omega, a3, a4, a5⟩
        snapP2 := ho.snapP2
        d3a := ho.d3a
        d3b := by simp
        d3c := by simp
        d3d := by simp
        r1 := by simp }
  refine
    { p2zero := h.p2zero
      p2used := fun b' w hbw => Finset.mem_insert_of_mem (h.p2used b' w hbw)
      p2inp := h.p2inp
      safe := h.safe
      voteP2 := h.voteP2
      accMono := h.accMono
      slotP2 := h.slotP2
      dec := h.dec
      fresh := ?_
      inj := ?_
      loc := ?_ }
  · intro hs m hm r
    dsimp only at hs hm ⊢
    by_cases hq : p1 = q
    · subst hq; simp [X] at hs
    · rw [update_of_ne hq] at hs; exact h.fresh hs m hm r
  · intro p r hpr hp hr
    dsimp only at hp hr ⊢
    by_cases hpq : p = q
    · subst hpq
      simp only [update_self, update_of_ne (Ne.symm hpr)] at hp hr ⊢
      intro he; apply hb; have := (h.loc r).balUsed hr; rw [← he] at this; simpa [X] using this
    · by_cases hrq : r = q
      · subst hrq
        simp only [update_self, update_of_ne hpq] at hp hr ⊢
        intro he; apply hb; have := (h.loc p).balUsed hp; rw [he] at this; simpa [X] using this
      · simp only [update_of_ne hpq, update_of_ne hrq] at hp hr ⊢
        exact h.inj p r hpr hp hr
  · intro p
    by_cases hpq : p = q
    · subst hpq; simpa using hX
    · simp only [update_of_ne hpq]
      exact (h.loc p).frame (fun _ => rfl) (fun _ hp => ⟨hp, fun _ => rfl⟩)
        (Finset.subset_insert _ _) (fun _ _ h => h) (fun _ => rfl) subset_rfl
        (fun _ _ _ _ hv hn => absurd hv hn)

theorem inv_startFirst (h : Inv p1 inp s) (q : P) (hq : q = p1) (hs : (s.pr q).started = false)
    (hb : 1 ∉ s.used) (hlt : (s.pr q).bal < 1) :
    Inv p1 inp { s with
      pr := update s.pr q
        { s.pr q with
          active := true, started := true, noPh1 := true, bal := 1,
          curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
          pc := fun _ => .ph2 }
      used := insert 1 s.used
      p2val := update s.p2val 1 (some (inp q)) } := by
  subst hq
  have hx := h.loc q
  have hnone : s.p2val 1 = none := by
    cases hpb : s.p2val 1 with
    | none => rfl
    | some w => exact absurd (h.p2used 1 w hpb) hb
  have hext : ∀ a y, s.p2val a = some y → update s.p2val 1 (some (inp q)) a = some y := by
    intro a y hy
    have : a ≠ 1 := by rintro rfl; simp [hnone] at hy
    simpa [update_of_ne this] using hy
  set X : Proc P M V := { s.pr q with
    active := true, started := true, noPh1 := true, bal := 1,
    curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
    pc := fun _ => .ph2 } with hXdef
  have hX : LInv inp s.slot s.perm s.votes (update s.p2val 1 (some (inp q))) (insert 1 s.used)
      q X := by
    refine
      { unst := by simp [X]
        balUsed := fun _ => Finset.mem_insert_self _ _
        balPos := fun _ => le_rfl
        p2cur := fun _ _ => by simp [X]
        p2none := by simp [X]
        curInp := ⟨q, rfl⟩
        curMax := by simp [X]
        lastIss := fun a y hy => by
          obtain ⟨h1, h3⟩ := hx.lastIss a y hy
          have : a = 0 := by omega
          subst this; simp [h.p2zero] at h1
        done := by simp [X]
        slotMp := fun m => by have := hx.slotMp m; simp only [X]; omega
        accLI := hx.accLI
        r2 := by simp [X]
        thr := fun m => ?_ }
    have hidle := h.unstarted_idle q hs m
    exact
      { unst := by simp [X]
        pcAct := fun _ => rfl
        np := fun _ => Or.inr (Or.inl rfl)
        ph2 := fun _ => rfl
        w2p2 := by simp
        idle := fun _ => hidle
        ready := by simp [X]
        doneFin := by simp [X]
        tperm := by simp
        tw1 := by simp
        trd := by simp
        tw2 := by simp
        tmp := by simp [X]
        linkW1 := by simp [X, hidle]
        linkW2 := by simp [X, hidle]
        snapP2 := by simp [X, hidle]
        d3a := by simp [X, hidle]
        d3b := by simp
        d3c := fun _ hp r => by simp [X, h.fresh hs m hp r]
        d3d := by simp
        r1 := by simp }
  refine
    { p2zero := by dsimp only; rw [update_of_ne (by omega)]; exact h.p2zero
      p2used := by
        intro b w hbw
        dsimp only at hbw ⊢
        by_cases hb1 : b = 1
        · subst hb1; exact Finset.mem_insert_self _ _
        · rw [update_of_ne hb1] at hbw; exact Finset.mem_insert_of_mem (h.p2used b w hbw)
      p2inp := by
        intro b w hbw
        dsimp only at hbw ⊢
        by_cases hb1 : b = 1
        · subst hb1; simp only [update_self, Option.some.injEq] at hbw; exact ⟨q, hbw⟩
        · rw [update_of_ne hb1] at hbw; exact h.p2inp b w hbw
      safe := by
        intro c w hcw
        dsimp only at hcw ⊢
        by_cases hc1 : c = 1
        · subst hc1; intro b hb0 hb1; omega
        · rw [update_of_ne hc1] at hcw; exact h.safe c w hcw
      voteP2 := fun m r b y hv => hext _ _ (h.voteP2 m r b y hv)
      accMono := h.accMono
      slotP2 := fun m r a y hy => hext _ _ (h.slotP2 m r a y hy)
      dec := h.dec
      fresh := ?_
      inj := ?_
      loc := ?_ }
  · intro hs' _ _ _
    simp [X] at hs'
  · intro p r hpr hp hr
    dsimp only at hp hr ⊢
    by_cases hpq : p = q
    · subst hpq
      simp only [update_self, update_of_ne (Ne.symm hpr)] at hp hr ⊢
      intro he; apply hb; have := (h.loc r).balUsed hr; rw [← he] at this; simpa [X] using this
    · by_cases hrq : r = q
      · subst hrq
        simp only [update_self, update_of_ne hpq] at hp hr ⊢
        intro he; apply hb; have := (h.loc p).balUsed hp; rw [he] at this; simpa [X] using this
      · simp only [update_of_ne hpq, update_of_ne hrq] at hp hr ⊢
        exact h.inj p r hpr hp hr
  · intro p
    by_cases hpq : p = q
    · subst hpq; simpa using hX
    · simp only [update_of_ne hpq]
      refine (h.loc p).frame (fun _ => rfl) (fun _ hp => ⟨hp, fun _ => rfl⟩)
        (Finset.subset_insert _ _) hext ?_ subset_rfl (fun _ _ _ _ hv hn => absurd hv hn)
      intro hap
      have hsp : (s.pr p).started = true := by
        cases hs' : (s.pr p).started
        · simp [(h.loc p).unst hs'] at hap
        · rfl
      have : (s.pr p).bal ≠ 1 := fun he => hb (he ▸ (h.loc p).balUsed hsp)
      rw [update_of_ne this]

theorem inv_effRd (h : Inv p1 inp s) (q : P) (m0 : M) (hl : (s.pr q).link m0 = .sent .rd) :
    Inv p1 inp { s with pr := update s.pr q ((s.pr q).setL m0 (.resp (.snap (s.slot m0))))} := by
  refine h.of_pr q _ rfl rfl ((h.loc q).setL m0 _ ?_)
  have ho := (h.loc q).thr m0
  rw [hl] at ho
  have e1 := h.slotP2 m0
  have e2 : ∀ b r y, (m0, r, b, y) ∈ s.votes → ∃ r' a z, (s.slot m0 r').acc = some (a, z) ∧ b ≤ a :=
    fun b r y hv => by
      obtain ⟨a, z, h1, h2⟩ := h.accMono m0 r b y hv b y rfl
      exact ⟨r, a, z, h1, h2⟩
  tinv_tac ho

end Podc.RDMAAgreement.PMP
