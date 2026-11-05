import Papers.PODC2014.DistributedUniversality.InvDStep

/-!
# Safety: Lemmas 1–4 of the paper

For every reachable state of the construction (any variant: Figure 1, Figure 2, helping,
`(k, ℓ)`-SC objects; the only restriction is `Mode.Good`, i.e. line 4M of Figure 2 proposes
`ac_opᵢ[m]`), for every object `m` there is one duplicate-free sequence of operations `H`
(the ghost `G m`) such that

* every local history `ℓ_histᵢ[m]`, every register `GSTATE[i][m]` is a prefix of `H` (Lemma 3);
* every operation in `H` has been invoked by its process (Lemma 1) and committed in some round;
* no operation occurs twice (Lemma 2);
* every returned operation is in `H`; its linearization point — the first write of a `GSTATE`
  register containing it (Lemma 4) — lies between its invocation and its return; linearization
  points respect the order of `H`; and the output was computed on a prefix of `H` containing the
  operation, i.e. from the state of the object after the operations preceding it in `H`.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s : St n k}

/-- **Lemma 1.** Every operation present in a local history, a `GSTATE` register or the global
sequence was invoked (it is the `c`-th operation of `my_listⱼ[m]` for its process `j`, and
`next()` returned it at time `t`). -/
theorem lemma_1 (hM : M.Good) (hs : Reachable M s) (m : Fin k) (o : Op n) :
    (o ∈ s.G m ∨ (∃ i, o ∈ (s.loc i).hist m) ∨ ∃ i, o ∈ s.gst i m) →
    ∃ t, s.invAt o.1 m o.2 = some t := by
  have hI := Reachable.invAll hM hs
  rintro (h | ⟨i, h⟩ | ⟨i, h⟩)
  · exact hI.C.v_G m o h
  · exact hI.C.v_hist i m o h
  · exact hI.C.v_hist i m o ((hI.B.gst_hist i m).subset h)

/-- **Lemma 2.** No operation appears twice in a local history or a `GSTATE` register. -/
theorem lemma_2 (hM : M.Good) (hs : Reachable M s) (i : Fin n) (m : Fin k) :
    ((s.loc i).hist m).Nodup ∧ (s.gst i m).Nodup := by
  have hI := Reachable.invAll hM hs
  have hG := hI.B.G_nodup m
  exact ⟨(hI.B.hist_G i m).sublist.nodup hG,
    ((hI.B.gst_hist i m).trans (hI.B.hist_G i m)).sublist.nodup hG⟩

/-- **Lemma 3.** All local histories and `GSTATE` registers of an object are prefixes of one
duplicate-free sequence, each of whose operations was committed (returned with tag `commit` by
the adopt-commit objects) in some round. -/
theorem lemma_3 (hM : M.Good) (hs : Reachable M s) (m : Fin k) :
    ∃ H : List (Op n), H.Nodup ∧ (∀ i, (s.loc i).hist m <+: H ∧ s.gst i m <+: H) ∧
      ∀ o ∈ H, ∃ r j, s.finR r m j = some (true, o) := by
  have hI := Reachable.invAll hM hs
  refine ⟨s.G m, hI.B.G_nodup m, fun i => ⟨hI.B.hist_G i m,
    (hI.B.gst_hist i m).trans (hI.B.hist_G i m)⟩, fun o ho => ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem ho
  have hb : x < (s.born m).length := by rw [hI.B.born_len]; exact hx
  obtain ⟨j, hj⟩ := hI.B.GS1 m x _ _ (List.getElem?_eq_getElem hb) (List.getElem?_eq_getElem hx)
  exact ⟨_, j, hj⟩

theorem order_of_lin_pre (hI : Inv M s) {m : Fin k} {x y : ℕ} {o1 o2 : Op n} {t2 : ℕ}
    (h1 : (s.G m)[x]? = some o1) (h2 : (s.G m)[y]? = some o2) (hlt : x < y)
    (hl : s.lin m o2 = some t2) : ∃ t1, s.lin m o1 = some t1 ∧ t1 ≤ t2 := by
  obtain ⟨hh, hpre, hmem, hall⟩ := hI.C.lin_pre m _ _ hl
  have hG := hI.B.G_nodup m
  obtain ⟨z, hz, rfl⟩ := List.getElem_of_mem hmem
  have hzG : z < (s.G m).length := lt_of_lt_of_le hz hpre.length_le
  have hy : y < (s.G m).length := (List.getElem?_eq_some_iff.1 h2).1
  have e2 : (s.G m)[y] = hh[z] := (List.getElem?_eq_some_iff.1 h2).2
  rw [hpre.getElem hz] at e2
  have hzy : y = z := (List.Nodup.getElem_inj_iff hG).1 e2
  subst hzy
  have hx : x < hh.length := lt_trans hlt hz
  have e1 : (s.G m)[x]'(lt_of_lt_of_le hx hpre.length_le) = o1 :=
    (List.getElem?_eq_some_iff.1 h1).2
  rw [← hpre.getElem hx] at e1
  exact hall o1 (e1 ▸ List.getElem_mem hx)

/-- **Lemma 4** (linearizability). For each object `m` there is a duplicate-free sequence `H`
such that every returned operation `(i, c)` is in `H`, with a linearization point (the ghost
`lin m (i, c)`: the first time a `GSTATE` register contained the operation) between its invocation
and its return; linearization points are ordered as `H`; and the history from which the output was
computed (`retH`) is a prefix of `H` containing the operation. -/
theorem lemma_4 (hM : M.Good) (hs : Reachable M s) (m : Fin k) :
    ∃ H : List (Op n), H.Nodup ∧
      (∀ i c t, s.retAt i m c = some t → (i, c) ∈ H ∧ ∃ tl ti, s.lin m (i, c) = some tl ∧
        s.invAt i m c = some ti ∧ ti ≤ tl ∧ tl ≤ t) ∧
      (∀ (x y : ℕ) (o1 o2 : Op n) (t2 : ℕ), H[x]? = some o1 → H[y]? = some o2 → x < y →
        s.lin m o2 = some t2 →
        ∃ t1, s.lin m o1 = some t1 ∧ t1 ≤ t2) ∧
      (∀ i c h, s.retH i m c = some h → h <+: H ∧ (i, c) ∈ h) := by
  have hI := Reachable.invAll hM hs
  refine ⟨s.G m, hI.B.G_nodup m, fun i c t ht => ?_,
    fun x y o1 o2 t2 h1 h2 hlt hl => order_of_lin_pre hI h1 h2 hlt hl,
    fun i c h hh => hI.C.ret_H i m c h hh⟩
  obtain ⟨tl, htl, hle⟩ := hI.C.ret_lin i m c t ht
  obtain ⟨-, ti, hti, hle'⟩ := hI.C.lin_inv m _ _ htl
  obtain ⟨hh, hpre, hmem, -⟩ := hI.C.lin_pre m _ _ htl
  exact ⟨hpre.subset hmem, tl, ti, htl, hti, hle', hle⟩

/-- **Linearizability, real-time order.** If a returned operation `o₁` returned before the
invocation of another returned operation `o₂`, then `o₁` precedes `o₂` in the sequence `H = G m`
of Lemma 4. -/
theorem lemma_4_realtime (hM : M.Good) (hs : Reachable M s) (m : Fin k) {i1 i2 : Fin n}
    {c1 c2 t1 t2 ti : ℕ} (hr1 : s.retAt i1 m c1 = some t1) (hr2 : s.retAt i2 m c2 = some t2)
    (hi2 : s.invAt i2 m c2 = some ti) (hlt : t1 < ti) :
    ∃ x y : ℕ, (s.G m)[x]? = some (i1, c1) ∧ (s.G m)[y]? = some (i2, c2) ∧ x < y := by
  have hI := Reachable.invAll hM hs
  have hret : ∀ i c t, s.retAt i m c = some t → (i, c) ∈ s.G m ∧ ∃ tl ti, s.lin m (i, c) = some tl ∧
      s.invAt i m c = some ti ∧ ti ≤ tl ∧ tl ≤ t := by
    intro i c t ht
    obtain ⟨tl, htl, hle⟩ := hI.C.ret_lin i m c t ht
    obtain ⟨-, ti, hti, hle'⟩ := hI.C.lin_inv m _ _ htl
    obtain ⟨hh, hpre, hmem, -⟩ := hI.C.lin_pre m _ _ htl
    exact ⟨hpre.subset hmem, tl, ti, htl, hti, hle', hle⟩
  obtain ⟨hm1, tl1, -, hl1, -, -, hle1⟩ := hret _ _ _ hr1
  obtain ⟨hm2, tl2, ti', hl2, hi2', hle2, -⟩ := hret _ _ _ hr2
  rw [hi2] at hi2'; simp only [Option.some.injEq] at hi2'; subst hi2'
  obtain ⟨x, hx, e1⟩ := List.getElem_of_mem hm1
  obtain ⟨y, hy, e2⟩ := List.getElem_of_mem hm2
  have h1 : (s.G m)[x]? = some (i1, c1) := by rw [List.getElem?_eq_getElem hx, e1]
  have h2 : (s.G m)[y]? = some (i2, c2) := by rw [List.getElem?_eq_getElem hy, e2]
  refine ⟨x, y, h1, h2, ?_⟩
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact hxy
  · rw [h1] at h2
    simp only [Option.some.injEq] at h2
    rw [h2] at hl1
    rw [hl1] at hl2; simp only [Option.some.injEq] at hl2
    omega
  · obtain ⟨t', ht', hle⟩ := order_of_lin_pre hI h2 h1 hxy hl1
    rw [hl2] at ht'; simp only [Option.some.injEq] at ht'
    omega

end Podc.DistributedUniversality
