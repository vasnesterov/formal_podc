import Papers.PODC2014.DistributedUniversality.WaitFree

/-!
# Theorem 3: the helping window

Fix an object `x`, a process `j` whose current operation `X = (j, s₀)` on `x` is pending forever,
and the first moment the global sequence `G x` reaches a length `L ≡ j (mod n)`, by the commit of
`e` in round `ρ`. Until `G x` grows again, every proposal of a round `> ρ` for `x` is `e` or `X`,
and from round `ρ + 2` on it is `X` (all processes help `p_j`): `Wst`.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

/-- Lines L1–L5 propose `X` when the history has length `L ≡ j (mod n)`. -/
theorem nextProp_help (hhelp : M.help = true) {lastOp : Fin n → Fin k → Option ℕ} {p j : Fin n}
    {x : Fin k} {h : List (Op n)} {c L s0 : ℕ} (hL : h.length = L) (hLj : L % n = j.val)
    (hlast : lastOp j x = some s0) (hX : (j, s0) ∉ h) :
    nextProp M lastOp p x h c = (j, s0) := by
  have hj : (⟨h.length % n, Nat.mod_lt _ p.pos⟩ : Fin n) = j := Fin.ext (by simp only; rw [hL, hLj])
  unfold nextProp
  simp only [hhelp, ↓reduceIte, hj, hlast, hX]

/-- A prefix of `G` that contains its last element `e` is `G`. -/
theorem eq_of_prefix_mem_last {G h : List (Op n)} {L : ℕ} {e : Op n} (hG : G.Nodup)
    (hlen : G.length = L) (hlast : G[L - 1]? = some e) (hp : h <+: G) (he : e ∈ h) : h = G := by
  by_contra hne
  have hlt : h.length < L := by
    rcases Nat.lt_or_ge h.length G.length with h1 | h1
    · omega
    · exact absurd (hp.eq_of_length (le_antisymm hp.length_le h1)) hne
  have hL : 0 < L := by omega
  have hx : L - 1 < G.length := by omega
  rw [List.getElem?_eq_getElem hx] at hlast
  simp only [Option.some.injEq] at hlast
  have : e ∉ G.take h.length := by
    subst hlast
    intro hm
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hm
    rw [List.getElem_take] at hix
    have := (List.Nodup.getElem_inj_iff hG).1 hix
    simp at hi; omega
  rw [← List.prefix_iff_eq_take.1 hp] at this
  exact this he

/-- The frozen facts of the window. -/
structure Frozen (s : St n k) (x : Fin k) (j : Fin n) (s0 L : ℕ) (e : Op n) (ρ : ℕ) : Prop where
  len : (s.G x).length = L
  last : (s.G x)[L - 1]? = some e
  born : (s.born x)[L - 1]? = some ρ
  cnt : (s.loc j).cnt x = s0
  init : (s.loc j).pc ≠ .init
  nX : (j, s0) ∉ s.G x

/-- The helping invariant of the window. -/
structure Wst (s : St n k) (x : Fin k) (j : Fin n) (s0 : ℕ) (e : Op n) (ρ : ℕ) : Prop where
  w1 : ∀ p ρ'' W, ρ + 1 ≤ ρ'' → s.opRec ρ'' x p = some W → W = e ∨ W = (j, s0)
  w2 : ∀ p ρ'' W, ρ + 2 ≤ ρ'' → s.opRec ρ'' x p = some W → W = (j, s0)
  w3 : ∀ p, (s.loc p).r = ρ → pastUpd (s.loc p).pc x →
    (s.loc p).oper x = e ∨ (s.loc p).oper x = (j, s0)
  w4 : ∀ p, ρ + 1 ≤ (s.loc p).r → pastUpd (s.loc p).pc x → (s.loc p).oper x = (j, s0)

section Window
variable {x : Fin k} {j : Fin n} {s0 L : ℕ} {e : Op n} {ρ : ℕ}

/-- Round `ρ` is uniform with value `e` in the window. -/
theorem Frozen.unif (hM : M.Good) (hI : Inv M s) (F : Frozen s x j s0 L e ρ) : Unif s ρ x e := by
  obtain ⟨q, hq⟩ := hI.B.GS1 x (L - 1) ρ e F.born F.last
  exact hI.A.unif_of_commit hM hq

/-- In the window, a process that completed lines 16–28 of round `ρ + 1` for `x` has the whole
`G x` as local history. -/
theorem Frozen.hist_eq (hM : M.Good) (hI : Inv M s) (F : Frozen s x j s0 L e ρ) {p : Fin n}
    (hp : passedUpd (s.loc p) (ρ + 1) x) : (s.loc p).hist x = s.G x :=
  eq_of_prefix_mem_last (hI.B.G_nodup x) F.len F.last (hI.B.hist_G p x)
    (hI.B.know p ρ x e (F.unif hM hI) hp)

/-- Values of final pairs of rounds `> ρ` are `e` or `X`. -/
theorem Wst.fin_val (hI : Inv M s) (W : Wst s x j s0 e ρ) {r : ℕ} (hr : ρ + 1 ≤ r) {p : Fin n}
    {b : Bool} {w : Op n} (hf : s.finR r x p = some (b, w)) : w = e ∨ w = (j, s0) := by
  have hsrc : ∃ bb, s.acR r bb x p = some (b, w) := by
    rcases hI.A.finR_src _ _ _ _ hf with h1 | ⟨-, h1⟩
    · exact ⟨true, h1⟩
    · exact ⟨false, h1⟩
  obtain ⟨bb, hbb⟩ := hsrc
  obtain ⟨-, -, ⟨j', hj'⟩, -⟩ := hI.A.acR_inv _ _ _ _ _ _ hbb
  have hop : ∃ j'', s.opRec r x j'' = some w := by
    cases bb
    · exact ⟨j', hI.A.acI0 _ _ _ _ hj'⟩
    · exact hI.A.acI1 _ _ _ _ hj'
  obtain ⟨j'', hj''⟩ := hop
  exact W.w1 _ _ _ hr hj''

end Window

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}
variable {x : Fin k} {j : Fin n} {s0 L : ℕ} {e : Op n} {ρ : ℕ}

theorem Inv.step' (hM : M.Good) (hI : Inv M s) (h : stepFn M s a = some s') : Inv M s' :=
  ⟨hI.A.step h, hI.B.step hI.A hM h, hI.C.step hI.A hI.B hM h, hI.D.step hI.A hI.B hI.C hM h⟩

theorem Frozen.rho_pos (hI : Inv M s) (F : Frozen s x j s0 L e ρ) : 1 ≤ ρ := by
  obtain ⟨q, hq⟩ := hI.B.GS1 x (L - 1) ρ e F.born F.last
  exact hI.A.finR_pos _ _ _ _ hq

theorem Frozen.lastOp (hI : Inv M s) (F : Frozen s x j s0 L e ρ) : s.lastOp j x = some s0 := by
  rw [hI.D.last_cnt j x F.init, F.cnt]

/-- The opRec part of the window invariant is preserved. -/
theorem Wst.rec_step (hI : Inv M s) (h : stepFn M s a = some s') (F : Frozen s x j s0 L e ρ)
    (W : Wst s x j s0 e ρ) :
    (∀ p ρ'' Wv, ρ + 1 ≤ ρ'' → s'.opRec ρ'' x p = some Wv → Wv = e ∨ Wv = (j, s0)) ∧
    (∀ p ρ'' Wv, ρ + 2 ≤ ρ'' → s'.opRec ρ'' x p = some Wv → Wv = (j, s0)) := by
  have hρ := F.rho_pos hI
  constructor
  · intro p ρ'' Wv hle hW
    by_cases hold : s.opRec ρ'' x p = some Wv
    · exact W.w1 _ _ _ hle hold
    · obtain ⟨rfl, hc⟩ := hI.A.opRec_new h hW hold
      rcases hc with ⟨-, rfl, -⟩ | ⟨hpc, rfl, rfl⟩
      · omega
      · rcases Nat.lt_or_ge (s.loc a.proc).r (ρ + 1) with h1 | h1
        · exact W.w3 _ (by omega) (by simp [hpc])
        · exact Or.inr (W.w4 _ h1 (by simp [hpc]))
  · intro p ρ'' Wv hle hW
    by_cases hold : s.opRec ρ'' x p = some Wv
    · exact W.w2 _ _ _ hle hold
    · obtain ⟨rfl, hc⟩ := hI.A.opRec_new h hW hold
      rcases hc with ⟨-, rfl, -⟩ | ⟨hpc, rfl, rfl⟩
      · omega
      · exact W.w4 _ (by omega) (by simp [hpc])

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}
variable {x : Fin k} {j : Fin n} {s0 L : ℕ} {e : Op n} {ρ : ℕ}

/-- The core of Theorem 3: lines 16–28 for `x` in the window produce `e` (round `ρ`, adopt) or
the helped operation `X`. -/
theorem Wst.oper_step (hM : M.Good) (hhelp : M.help = true) (hLj : L % n = j.val)
    (hI : Inv M s) (h : stepFn M s a = some s') (F : Frozen s x j s0 L e ρ)
    (F' : Frozen s' x j s0 L e ρ) (W : Wst s x j s0 e ρ) (p : Fin n)
    (hpu : pastUpd (s'.loc p).pc x) :
    ((s'.loc p).r = ρ → (s'.loc p).oper x = e ∨ (s'.loc p).oper x = (j, s0)) ∧
    (ρ + 1 ≤ (s'.loc p).r → (s'.loc p).oper x = (j, s0)) := by
  by_cases hp : p = a.proc
  · subst hp
    have hI' := Inv.step' hM hI h
    have hlast := F.lastOp hI
    have hgen : (s'.loc a.proc).r = (s.loc a.proc).r → (s'.loc a.proc).oper x = (s.loc a.proc).oper x →
        pastUpd (s.loc a.proc).pc x →
        ((s'.loc a.proc).r = ρ → (s'.loc a.proc).oper x = e ∨ (s'.loc a.proc).oper x = (j, s0)) ∧
        (ρ + 1 ≤ (s'.loc a.proc).r → (s'.loc a.proc).oper x = (j, s0)) := by
      intro h1 h2 h3
      rw [h1, h2]
      exact ⟨fun h4 => W.w3 _ h4 h3, fun h4 => W.w4 _ h4 h3⟩
    have hpass : ρ + 1 ≤ (s'.loc a.proc).r → passedUpd (s'.loc a.proc) (ρ + 1) x := by
      intro h1
      rcases Nat.lt_or_ge (ρ + 1) (s'.loc a.proc).r with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨by omega, hpu⟩
    have hGe : e ∈ s'.G x := by
      have := F'.last
      have hx : L - 1 < (s'.G x).length := by
        have := List.getElem?_eq_some_iff.1 this; exact this.1
      rw [List.getElem?_eq_getElem hx] at this
      simp only [Option.some.injEq] at this
      rw [← this]; exact List.getElem_mem hx
    have hne_off : ∀ mm (hmm : mm < k), x ≠ ⟨mm, hmm⟩ → pastUpd (updPC (k := k) mm) x →
        pastUpd (PC.upd mm) x := by
      intro mm hmm hy h1
      rw [pastUpd_updPC hmm] at h1
      have : x.val ≠ mm := fun e => hy (Fin.ext e)
      simp only [pastUpd_upd]; omega
    du_step_cases h
    · exfalso; revert hpu; simp [startPC]; split_ifs <;> simp
    · exfalso; revert hpu; simp
    · exfalso; revert hpu; simp; split_ifs <;> simp [afterN1] <;> (try split_ifs) <;> simp
    · exfalso; revert hpu; simp
    · exfalso; revert hpu; simp
    · exfalso; revert hpu; simp
    · exfalso; revert hpu; simp; split_ifs <;> simp
    · exfalso; revert hpu; simp; split_ifs <;> simp
    · exfalso; revert hpu; simp; split_ifs with hk <;> simp; exact absurd x.isLt (by omega)
    · -- line 27 / L1–L5: the operation is already in the history
      by_cases hy : x = ⟨m, hm⟩
      · subst hy
        have hfin := hI.A.finR_loc a.proc (by simp [hpc]) ⟨m, hm⟩
        have hhist' := fun h1 => F'.hist_eq hM hI' (hpass h1)
        simp only [tUpdIn_loc, Function.update_self] at hhist' ⊢
        refine ⟨fun hr => Or.inr ?_, fun hr => ?_⟩
        · have hacop : (s.loc a.proc).acop ⟨m, hm⟩ = e := (F.unif hM hI).2 _ _ _ (hr ▸ hfin)
          have hh := eq_of_prefix_mem_last (hI.B.G_nodup _) F.len F.last (hI.B.hist_G _ _)
            (hacop ▸ hin)
          exact nextProp_help hhelp (by rw [hh, F.len]) hLj hlast (by rw [hh]; exact F.nX)
        · have hh := hhist' hr
          exact nextProp_help hhelp (by rw [hh, F'.len]) hLj hlast (by rw [hh]; exact F'.nX)
      · exact hgen (by simp) (by simp [Function.update_of_ne hy])
          (by simp only [hpc]; exact hne_off m hm hy (by simpa using hpu))
    · -- lines 18–24, own operation
      by_cases hy : x = ⟨m, hm⟩
      · subst hy
        have hfin := hI.A.finR_loc a.proc (by simp [hpc]) ⟨m, hm⟩
        have hjp : j ≠ a.proc := by
          rintro rfl
          have h1 := F'.cnt; have h2 := F.cnt
          simp only [tUpdMine_loc, Function.update_self] at h1
          omega
        have hlast' : (fun j' y => if j' = a.proc ∧ y = (⟨m, hm⟩ : Fin k) then
            some ((s.loc a.proc).cnt ⟨m, hm⟩ + 1) else s.lastOp j' y) j ⟨m, hm⟩ = some s0 := by
          simp [hjp, hlast]
        have hpost := hI'.B.hist_G a.proc ⟨m, hm⟩
        have hhist' := fun h1 => F'.hist_eq hM hI' (hpass h1)
        simp only [tUpdMine_loc, Function.update_self] at hhist' hpost ⊢
        refine ⟨fun hr => Or.inr ?_, fun hr => ?_⟩
        · have hacop : (s.loc a.proc).acop ⟨m, hm⟩ = e := (F.unif hM hI).2 _ _ _ (hr ▸ hfin)
          have hh := eq_of_prefix_mem_last (hI'.B.G_nodup _) F'.len F'.last hpost
            (by rw [hacop]; simp)
          exact nextProp_help hhelp (by rw [hh, F'.len]) hLj hlast' (by rw [hh]; exact F'.nX)
        · have hh := hhist' hr
          exact nextProp_help hhelp (by rw [hh, F'.len]) hLj hlast' (by rw [hh]; exact F'.nX)
      · exact hgen (by simp) (by simp [Function.update_of_ne hy])
          (by simp only [hpc]; exact hne_off m hm hy (by simpa using hpu))
    · -- lines 18–24, operation of another process
      by_cases hy : x = ⟨m, hm⟩
      · subst hy
        have hfin := hI.A.finR_loc a.proc (by simp [hpc]) ⟨m, hm⟩
        have hpost := hI'.B.hist_G a.proc ⟨m, hm⟩
        have hhist' := fun h1 => F'.hist_eq hM hI' (hpass h1)
        simp only [tUpdOther_loc, Function.update_self] at hhist' hpost ⊢
        refine ⟨fun hr => Or.inr ?_, fun hr => ?_⟩
        · have hacop : (s.loc a.proc).acop ⟨m, hm⟩ = e := (F.unif hM hI).2 _ _ _ (hr ▸ hfin)
          have hh := eq_of_prefix_mem_last (hI'.B.G_nodup _) F'.len F'.last hpost
            (by rw [hacop]; simp)
          exact nextProp_help hhelp (by rw [hh, F'.len]) hLj hlast (by rw [hh]; exact F'.nX)
        · have hh := hhist' hr
          exact nextProp_help hhelp (by rw [hh, F'.len]) hLj hlast (by rw [hh]; exact F'.nX)
      · exact hgen (by simp) (by simp [Function.update_of_ne hy])
          (by simp only [hpc]; exact hne_off m hm hy (by simpa using hpu))
    · -- line 25: adopt
      by_cases hy : x = ⟨m, hm⟩
      · subst hy
        have hfin := hI.A.finR_loc a.proc (by simp [hpc]) ⟨m, hm⟩
        have hhist' := fun h1 => F'.hist_eq hM hI' (hpass h1)
        simp only [tUpdAdopt_loc, Function.update_self] at hhist' ⊢
        refine ⟨fun hr => Or.inl ((F.unif hM hI).2 _ _ _ (hr ▸ hfin)), fun hr => ?_⟩
        rcases W.fin_val hI hr hfin with h1 | h1
        · exfalso; apply hnin; rw [hhist' hr, h1]; exact hGe
        · exact h1
      · exact hgen (by simp) (by simp [Function.update_of_ne hy])
          (by simp only [hpc]; exact hne_off m hm hy (by simpa using hpu))
    · exfalso; revert hpu; simp [startPC]; split_ifs <;> simp
  · rw [loc_ne h hp] at hpu ⊢
    exact ⟨fun h1 => W.w3 p h1 hpu, fun h1 => W.w4 p h1 hpu⟩

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}
variable {x : Fin k} {j : Fin n} {s0 L : ℕ} {e : Op n} {ρ : ℕ}

theorem Wst.step (hM : M.Good) (hhelp : M.help = true) (hLj : L % n = j.val)
    (hI : Inv M s) (h : stepFn M s a = some s') (F : Frozen s x j s0 L e ρ)
    (F' : Frozen s' x j s0 L e ρ) (W : Wst s x j s0 e ρ) : Wst s' x j s0 e ρ := by
  obtain ⟨h1, h2⟩ := W.rec_step hI h F
  exact ⟨h1, h2, fun p hr hpu => (W.oper_step hM hhelp hLj hI h F F' p hpu).1 hr,
    fun p hr hpu => (W.oper_step hM hhelp hLj hI h F F' p hpu).2 hr⟩

/-- The window opens: the step that makes `G x` reach length `L` (appending `e` committed in
round `ρ`) establishes the helping invariant. -/
theorem Wst.start (hM : M.Good) (hhelp : M.help = true) (hLj : L % n = j.val)
    (hI : Inv M s) (h : stepFn M s a = some s') (hlen : (s.G x).length + 1 = L)
    (F' : Frozen s' x j s0 L e ρ) (hcnt : (s.loc j).cnt x = s0) (hini : (s.loc j).pc ≠ .init) :
    Wst s' x j s0 e ρ := by
  have hI' := Inv.step' hM hI h
  rcases GB_cases h x with ⟨hG, -⟩ | ⟨mm, hpcG, hxm, htag, hnin, heq, hG, hB⟩
  · have := F'.len; rw [hG] at this; omega
  -- the appended operation is `e`, born in the round `ρ` of the appender
  have he : (s.loc a.proc).acop x = e := by
    have := F'.last; rw [hG, ← hlen, Nat.add_sub_cancel, List.getElem?_append_right le_rfl] at this
    simpa using this
  have hρ : (s.loc a.proc).r = ρ := by
    have := F'.born; rw [hB, ← hlen, Nat.add_sub_cancel, ← hI.B.born_len,
      List.getElem?_append_right le_rfl] at this
    simpa using this
  have hfin : s.finR ρ x a.proc = some (true, e) := by
    rw [← hρ, hI.A.finR_loc a.proc (by simp [hpcG]) x, htag, he]
  have hU : Unif s ρ x e := hI.A.unif_of_commit hM hfin
  have heG : e ∉ s.G x := by rw [← heq, ← he]; exact hnin
  have hnotpassed : ∀ p, ¬ passedUpd (s.loc p) (ρ + 1) x := fun p hp =>
    heG ((hI.B.hist_G p x).subset (hI.B.know p ρ x e hU hp))
  have hlast := hI.D.last_cnt j x hini
  rw [hcnt] at hlast
  have hrec : ∀ ρ'' p Wv, s'.opRec ρ'' x p = some Wv → s.opRec ρ'' x p = some Wv := by
    intro ρ'' p Wv hW
    by_contra hold
    obtain ⟨-, hc⟩ := hI.A.opRec_new h hW hold
    rcases hc with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [hpcG] at h1
  refine ⟨fun p ρ'' Wv hle hW => ?_, fun p ρ'' Wv hle hW => ?_, fun p hr hpu => ?_,
    fun p hr hpu => ?_⟩
  · have hW0 := hrec _ _ _ hW
    by_contra hne
    push Not at hne
    rcases Nat.lt_or_ge (ρ + 1) ρ'' with h1 | h1
    · have := (hI.A.opRec_le _ _ _ _ hW0).2
      exact hnotpassed p (Or.inl (by omega))
    · have h2 : ρ'' = ρ + 1 := by omega
      subst h2
      obtain ⟨q, hq⟩ := hI.B.PIa ρ x e p Wv hU hW0 hne.1
      exact heG (((hI.B.gst_hist q x).trans (hI.B.hist_G q x)).subset hq)
  · have hW0 := hrec _ _ _ hW
    have := (hI.A.opRec_le _ _ _ _ hW0).2
    exact absurd (Or.inl (by omega)) (hnotpassed p)
  · by_cases hp : p = a.proc
    · subst hp
      right
      have hXG' : (j, s0) ∉ s.G x ++ [(s.loc a.proc).acop x] := by rw [← hG]; exact F'.nX
      have hlenG' : (s.G x ++ [(s.loc a.proc).acop x]).length = L := by simp; omega
      du_step_cases h <;> rw [hpcG] at hpc <;> simp only [reduceCtorEq, PC.upd.injEq] at hpc
      · subst hpc; obtain rfl : x = ⟨_, hm⟩ := Fin.ext (by simp; omega); exact absurd hin hnin
      · subst hpc; obtain rfl : x = ⟨_, hm⟩ := Fin.ext (by simp; omega)
        have hjp : j ≠ a.proc := by
          rintro rfl
          have h1 := F'.cnt
          simp only [tUpdMine_loc, Function.update_self] at h1
          omega
        simp only [tUpdMine_loc, Function.update_self]
        rw [← heq] at hlenG' hXG'
        exact nextProp_help hhelp hlenG' hLj (by simp [hjp, hlast]) hXG'
      · subst hpc; obtain rfl : x = ⟨_, hm⟩ := Fin.ext (by simp; omega)
        simp only [tUpdOther_loc, Function.update_self]
        rw [← heq] at hlenG' hXG'
        exact nextProp_help hhelp hlenG' hLj hlast hXG'
      · subst hpc; obtain rfl : x = ⟨_, hm⟩ := Fin.ext (by simp; omega); simp [htag] at *
    · rw [loc_ne h hp] at hr hpu ⊢
      left
      obtain ⟨b, v, hf, hv⟩ := hI.B.opPost p x hpu
      rw [hr] at hf
      have hve : v = e := hU.2 _ _ _ hf
      subst hve
      rcases hv with hv | hv
      · exact hv
      · exact absurd ((hI.B.hist_G p x).subset hv) heG
  · by_cases hp : p = a.proc
    · subst hp
      have := r_post h; simp [hpcG] at this; omega
    · rw [loc_ne h hp] at hr hpu ⊢
      exact absurd (if h1 : ρ + 1 < (s.loc p).r then Or.inl h1 else Or.inr ⟨by omega, hpu⟩)
        (hnotpassed p)

end Podc.DistributedUniversality
