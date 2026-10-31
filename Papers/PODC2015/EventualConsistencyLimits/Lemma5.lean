import Papers.PODC2015.EventualConsistencyLimits.Late

/-!
# Lemma 5: writes must be propagated

**Lemma 5 of [AEM15]** (proved only in the full version): in an eventually consistent data
store with invisible reads and op-driven messages, if the last event of `α` is a write `w` at
`R`, and `R` has directly received everything that happened before `w`, then `R` has a message
pending after `w`.

We prove it (`lemma5`) under the following explicit form of the hypothesis "`e →hb w ⇒ e →rcv w`":
no replica has a message pending at the end of `α` and `R` has received every message sent in
`α` by another replica. We also need a second replica `R' ≠ R` (with a single replica the lemma
is false: nothing ever needs to be sent) and that `w` writes a fresh value and the writes of `α`
write pairwise distinct values (the paper assumes all written values distinct).

Proof (ours). Let `δ` deliver every message of `α` to every replica other than `R` and the
sender. If `R` had no message pending after `w`, then both `α δ` and `α r w δ` (with an invisible
read `r` of `o` at `R` inserted before `w`) are quiescent. Appending reads forever (Lemma 3,
`exists_late_ae`): in `α δ` the late reads at `R` and `R'` return the response `S` of `r`, which
does not contain `w`'s value. In `α r w δ` the state of `R'` is the same, so late reads at `R'`
again return `S`, and late reads at `R` return `S` too. But `w` is visible to them, so it is
overwritten by a returned write `w₂ ∈ S`, i.e. `w →vis⁺ w₂`. Since `w₂ ∈ S = rval(r)`,
`w₂ →vis r`, hence `w₂ →vis w` (Definition 4(2)) — a cycle.
-/

namespace Podc.EventualConsistencyLimits

variable {ι Obj V M St : Type*} [DecidableEq ι]

namespace Store

variable {D : Store ι Obj V M St}

/-- Deliver every message sent in `α` to every replica other than `R` and its sender. -/
noncomputable def deliverAll [Fintype ι] (R : ι) (α : List (ι × Ev Obj V M)) :
    List (ι × Ev Obj V M) :=
  α.flatMap fun x => match x.2 with
    | .send m => ((Finset.univ : Finset ι).toList.filter fun i => i ≠ x.1 ∧ i ≠ R).map
        fun i => (i, .recv m)
    | _ => []

lemma mem_deliverAll [Fintype ι] {R : ι} {α : List (ι × Ev Obj V M)} {x : ι × Ev Obj V M}
    (hx : x ∈ deliverAll R α) :
    x.1 ≠ R ∧ ∃ m, x.2 = .recv m ∧ ∃ j, j ≠ x.1 ∧ (j, .send m) ∈ α := by
  simp only [deliverAll, List.mem_flatMap] at hx
  obtain ⟨⟨j, e⟩, hjα, hx⟩ := hx
  cases e with
  | do_ d => simp at hx
  | recv m => simp at hx
  | send m =>
    simp only [List.mem_map, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
      decide_eq_true_eq] at hx
    obtain ⟨i, ⟨hij, hiR⟩, rfl⟩ := hx
    exact ⟨hiR, m, rfl, j, fun h => hij h.symm, hjα⟩

lemma recv_mem_deliverAll [Fintype ι] {R : ι} {α : List (ι × Ev Obj V M)} {j i : ι} {m : M}
    (hj : (j, .send m) ∈ α) (hij : i ≠ j) (hiR : i ≠ R) :
    (i, .recv m) ∈ deliverAll R α := by
  simp only [deliverAll, List.mem_flatMap]
  refine ⟨(j, .send m), hj, ?_⟩
  simp [hij, hiR]

lemma deliverAll_ne [Fintype ι] {R : ι} {α : List (ι × Ev Obj V M)} :
    ∀ x ∈ deliverAll R α, x.1 ≠ R := fun _ hx => (mem_deliverAll hx).1

/-- Appending receipts of messages already sent keeps an execution well formed. -/
lemma IsExec.append_recvs (hR : D.RecvEnabled) {β γ : List (ι × Ev Obj V M)} (hβ : D.IsExec β)
    (hγ : ∀ x ∈ γ, ∃ m, x.2 = .recv m ∧ ∃ j, j ≠ x.1 ∧ (j, .send m) ∈ β) :
    D.IsExec (β ++ γ) := by
  induction γ using List.reverseRecOn with
  | nil => simpa using hβ
  | append_singleton γ x ih =>
    rw [← List.append_assoc]
    have ih := ih fun y hy => hγ y (by simp [hy])
    obtain ⟨m, hm, j, hj, hjβ⟩ := hγ x (by simp)
    obtain ⟨i, e⟩ := x
    simp only at hm hj
    subst hm
    refine ih.snoc' (fun σ _ => hR i σ m) fun m' hm' => ?_
    cases hm'
    exact ⟨j, hj, by simp [hjβ]⟩

/-- Receipts keep a replica without pending messages (op-driven messages). -/
lemma not_pending_append_recvs (hOD : D.OpDriven) {β γ : List (ι × Ev Obj V M)} {i : ι}
    (hγ : ∀ x ∈ γ, ∃ m, x.2 = .recv m)
    (hβ : ∀ σ, D.state i β = some σ → ¬ D.Pending i σ) :
    ∀ σ, D.state i (β ++ γ) = some σ → ¬ D.Pending i σ := by
  induction γ using List.reverseRecOn with
  | nil => simpa using hβ
  | append_singleton γ x ih =>
    have ih := ih fun y hy => hγ y (by simp [hy])
    obtain ⟨m, hm⟩ := hγ x (by simp)
    obtain ⟨j, e⟩ := x
    simp only at hm
    subst hm
    intro σ hσ
    rw [← List.append_assoc, state_snoc] at hσ
    split_ifs at hσ with hji
    · subst hji
      obtain ⟨σ₀, h₀⟩ : ∃ σ₀, D.state j (β ++ γ) = some σ₀ := by
        cases h : D.state j (β ++ γ) with
        | none => simp [h] at hσ
        | some σ₀ => exact ⟨σ₀, rfl⟩
      rw [h₀] at hσ
      exact hOD.2 j σ₀ m σ hσ (ih σ₀ h₀)
    · exact ih σ hσ

end Store

open Store

variable {D : Store ι Obj V M St}

/-- **Lemma 5 of [AEM15]** (repaired; see the module docstring). If `α` followed by a write `w`
of a fresh value `v` at `R` is an execution, nobody has a message pending at the end of `α`,
`R` has received every message sent in `α` by others, and there is a second replica `R'`, then
`R` has a message pending after `w`. -/
theorem lemma5 [Fintype ι] {P : AE ι Obj V → Prop} (hEC : D.EventuallyConsistent P)
    (hIR : D.InvisibleReads) (hOD : D.OpDriven) (hAv : D.Available) (hRecv : D.RecvEnabled)
    {α : List (ι × Ev Obj V M)} {R R' : ι} (hRR' : R ≠ R') {o : Obj} {v : V} {r : Resp V}
    {σ σw : St} (hα : D.IsExec α) (hσ : D.state R α = some σ)
    (hσw : D.step R σ (.do_ ⟨o, .write v, r⟩) = some σw)
    (hfresh : ∀ x ∈ α, ∀ o' r', x.2 ≠ .do_ ⟨o', .write v, r'⟩)
    (hdist : ∀ p q (hp : p < α.length) (hq : q < α.length) i j o₁ o₂ u r₁ r₂,
      α[p] = (i, .do_ ⟨o₁, .write u, r₁⟩) → α[q] = (j, .do_ ⟨o₂, .write u, r₂⟩) → p = q)
    (hnp : ∀ i σi, D.state i α = some σi → ¬ D.Pending i σi)
    (hrcv : ∀ j m, (j, .send m) ∈ α → j ≠ R → (R, .recv m) ∈ α) :
    D.Pending R σw := by
  by_contra hpend
  set δ := deliverAll R α with hδ
  have hδmem : ∀ x ∈ δ, ∃ m, x.2 = .recv m ∧ ∃ j, j ≠ x.1 ∧ (j, .send m) ∈ α :=
    fun x hx => (mem_deliverAll hx).2
  have hδrecv : ∀ x ∈ δ, ∃ m, x.2 = .recv m := fun x hx =>
    let ⟨m, hm, _⟩ := hδmem x hx; ⟨m, hm⟩
  have hδR : ∀ x ∈ δ, x.1 ≠ R := deliverAll_ne
  -- sends of `α ++ γ ++ δ` are those of `α`, when `γ` has no sends
  have hq2 : ∀ γ : List (ι × Ev Obj V M), (∀ x ∈ γ, ∀ m, x.2 ≠ .send m) →
      ∀ j m, (j, .send m) ∈ α ++ γ ++ δ → ∀ i, i ≠ j → (i, .recv m) ∈ α ++ γ ++ δ := by
    intro γ hγ j m hj i hij
    have hjα : (j, Ev.send m) ∈ α := by
      simp only [List.mem_append] at hj
      rcases hj with (hj | hj) | hj
      · exact hj
      · exact absurd rfl (hγ _ hj m)
      · obtain ⟨m', hm', -⟩ := hδmem _ hj; cases hm'
    by_cases hiR : i = R
    · subst hiR; simp [hrcv j m hjα (Ne.symm hij)]
    · simp only [List.mem_append]
      exact Or.inr (recv_mem_deliverAll (R := R) hjα hij hiR)
  -- the invisible read before `w`
  obtain ⟨rS, σS, hS⟩ := hAv R σ o .read
  have hS' : D.step R σ (rd o rS) = some σ := (hIR _ _ _ _ _ hS) ▸ hS
  /- First execution: `α δ`. -/
  have hE0 : D.IsExec (α ++ δ) := hα.append_recvs hRecv hδmem
  have hσ0 : D.state R (α ++ δ) = some σ := by rw [state_append_of_not_mem _ _ _ hδR, hσ]
  have hq0 : D.Quiescent (α ++ δ) := by
    refine ⟨fun i σi h => not_pending_append_recvs hOD hδrecv (hnp i) σi h, ?_⟩
    have := hq2 [] (by simp)
    simpa using this
  obtain ⟨σ', hσ'⟩ := hE0.state_isSome R'
  obtain ⟨rW, σW, hW⟩ := hAv R' σ' o .read
  have hW' : D.step R' σ' (rd o rW) = some σ' := (hIR _ _ _ _ _ hW) ▸ hW
  obtain ⟨A₀, hOn₀, hWF₀, hC₀, -, hwr₀, p₁, p₂, -, -, d₁, d₂, -, -, v₁, v₂, c₁, c₂⟩ :=
    exists_late_ae hEC hE0 hq0 hσ0 hS' hσ' hW'
  set Sset := {u | ∃ a ∈ A₀.ctxW p₂, (A₀.ev a).op = .write u ∧ ∀ b ∈ A₀.ctxW p₂, ¬ A₀.vis a b}
  have hrW : rW = .vals Sset := AE.Correct.read' (hA := hC₀) d₂ v₂
  have hrS : rS = .vals Sset := by
    rw [AE.Correct.read' (hA := hC₀) d₁ v₁, c₁, ← c₂]
  -- locating do events
  have hloc : ∀ (γ : List (ι × Ev Obj V M)) (a : ℕ) (ha : a < (α ++ γ ++ δ).length) (i : ι)
      (d : DoEv Obj V), (α ++ γ ++ δ)[a] = (i, .do_ d) →
        (∃ h : a < α.length, α[a] = (i, .do_ d)) ∨
        (∃ h : a - α.length < γ.length, α.length ≤ a ∧ γ[a - α.length] = (i, .do_ d)) := by
    intro γ a ha i d h
    rw [List.getElem_append] at h
    split_ifs at h with h1
    · rw [List.getElem_append] at h
      split_ifs at h with h2
      · exact Or.inl ⟨h2, h⟩
      · simp only [List.length_append] at h1
        exact Or.inr ⟨by omega, by omega, h⟩
    · exfalso
      have hmem : (i, Ev.do_ d) ∈ δ := h ▸ List.getElem_mem _
      obtain ⟨m, hm⟩ := hδrecv _ hmem
      cases hm
  have hvS : v ∉ Sset := by
    rintro ⟨a, ha, hav, -⟩
    have hda := (hWF₀.vis_dom ha.1).1
    have hlt := hwr₀ a hda ⟨v, hav⟩
    obtain ⟨i, d, hsd, -, hev⟩ := hOn₀.of_dom hda
    rw [ext2_lt hlt] at hsd
    rcases hloc [] a (by simpa using hlt) i d (by simpa using hsd) with ⟨h1, h2⟩ | ⟨h1, -⟩
    · rw [hev] at hav
      obtain ⟨o', op', r'⟩ := d
      simp only at hav
      subst hav
      exact hfresh _ (h2 ▸ List.getElem_mem h1) o' r' rfl
    · simp at h1
  /- Second execution: `α r w δ`. -/
  set γ : List (ι × Ev Obj V M) := [(R, rd o rS), (R, .do_ ⟨o, .write v, r⟩)] with hγ
  have hγsplit : α ++ γ = α ++ [(R, rd o rS)] ++ [(R, .do_ ⟨o, .write v, r⟩)] := by simp [hγ]
  have h1s : D.state R (α ++ [(R, rd o rS)]) = some σ := by rw [state_snoc_self D hσ, hS']
  have hE2 : D.IsExec (α ++ γ) := by
    have h1 : D.IsExec (α ++ [(R, rd o rS)]) := .snoc hα hσ hS' (fun m h => by cases h)
    rw [hγsplit]
    exact .snoc h1 h1s hσw (fun m h => by cases h)
  have hσw2 : D.state R (α ++ γ) = some σw := by rw [hγsplit, state_snoc_self D h1s, hσw]
  have hE3 : D.IsExec (α ++ γ ++ δ) := hE2.append_recvs hRecv fun x hx =>
    let ⟨m, hm, j, hj, hjα⟩ := hδmem x hx; ⟨m, hm, j, hj, by simp [hjα]⟩
  have hσw3 : D.state R (α ++ γ ++ δ) = some σw := by
    rw [state_append_of_not_mem _ _ _ hδR, hσw2]
  have hσ'3 : D.state R' (α ++ γ ++ δ) = some σ' := by
    rw [← hσ']
    apply state_congr
    simp [hγ, hRR']
  have hγR : ∀ x ∈ γ, x.1 ≠ R' := by simp [hγ, hRR']
  have hq3 : D.Quiescent (α ++ γ ++ δ) := by
    refine ⟨fun i σi h => ?_, hq2 γ (by simp [hγ])⟩
    refine not_pending_append_recvs hOD hδrecv (β := α ++ γ) ?_ σi h
    intro σ₀ h₀
    by_cases hi : i = R
    · subst hi
      rw [hσw2] at h₀
      cases h₀
      exact hpend
    · rw [state_append_of_not_mem _ _ _ (by simp [hγ, Ne.symm hi])] at h₀
      exact hnp i σ₀ h₀
  obtain ⟨rT, σT, hT⟩ := hAv R σw o .read
  have hT' : D.step R σw (rd o rT) = some σw := (hIR _ _ _ _ _ hT) ▸ hT
  obtain ⟨A, hOn, hWF, hC, -, hwr, q₁, q₂, -, -, e₁, e₂, -, -, w₁, w₂, k₁, k₂⟩ :=
    exists_late_ae hEC hE3 hq3 hσw3 hT' hσ'3 hW'
  set Tset := {u | ∃ a ∈ A.ctxW q₁, (A.ev a).op = .write u ∧ ∀ b ∈ A.ctxW q₁, ¬ A.vis a b}
  have hTS : Tset = Sset := by
    have : rW = .vals Tset := by rw [AE.Correct.read' (hA := hC) e₂ w₂, k₂, ← k₁]
    rw [hrW] at this
    exact (Resp.vals.inj this).symm
  -- positions of `r` and `w`
  have hlen : α.length + 1 < (α ++ γ ++ δ).length := by simp [hγ]
  have hsr : ext2 (α ++ γ ++ δ) R (rd o rT) R' (rd o rW) α.length = (R, rd o rS) := by
    rw [ext2_lt (by omega)]
    simp [hγ, List.getElem_append_right]
  have hsw : ext2 (α ++ γ ++ δ) R (rd o rT) R' (rd o rW) (α.length + 1) =
      (R, .do_ ⟨o, .write v, r⟩) := by
    rw [ext2_lt hlen]
    simp [hγ, List.getElem_append_right]
  obtain ⟨dr, rr, er⟩ := hOn.at hsr
  obtain ⟨dw, rw', ew⟩ := hOn.at hsw
  have hwq : α.length + 1 ∈ A.ctxW q₁ := by
    rw [k₁]; exact ⟨dw, by rw [ew], ⟨v, by rw [ew]⟩⟩
  obtain ⟨c, hc, hrtg, hmax⟩ := hWF.exists_max_above hwq
  obtain ⟨u, hu⟩ := hc.2.2
  have huS : u ∈ Sset := hTS ▸ (⟨c, hc, hu, hmax⟩ : u ∈ Tset)
  have huv : u ≠ v := fun h => hvS (h ▸ huS)
  have hcw : c ≠ α.length + 1 := by
    rintro rfl
    rw [ew] at hu
    cases hu
    exact huv rfl
  have htg : Relation.TransGen A.vis (α.length + 1) c :=
    (Relation.reflTransGen_iff_eq_or_transGen.1 hrtg).resolve_left hcw
  -- `u` is returned by the read `r`, hence a write of `u` is visible to `r`
  have hrS' := AE.Correct.read' (hA := hC) dr er
  rw [hrS] at hrS'
  have hu' := (Resp.vals.inj hrS') ▸ huS
  obtain ⟨a, ha, hau, -⟩ := hu'
  -- the writes of `u` are in `α`
  have loc : ∀ b, A.dom b → (A.ev b).op = .write u →
      ∃ h : b < α.length, ∃ i o' r', α[b] = (i, .do_ ⟨o', .write u, r'⟩) := by
    intro b hdb hbu
    have hlt := hwr b hdb ⟨u, hbu⟩
    obtain ⟨i, d, hsd, -, hev⟩ := hOn.of_dom hdb
    rw [ext2_lt hlt] at hsd
    rw [hev] at hbu
    obtain ⟨o', op', r'⟩ := d
    simp only at hbu
    subst hbu
    rcases hloc γ b hlt i _ hsd with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨h1, i, o', r', h2⟩
    · exfalso
      have : b - α.length = 0 ∨ b - α.length = 1 := by simp [hγ] at h1; omega
      rcases this with h | h <;> simp [hγ, h] at h3
      exact huv h3.2.2.1.symm
  obtain ⟨ha1, ia, oa, ra, ha2⟩ := loc a (hWF.vis_dom ha.1).1 hau
  obtain ⟨hc1, ic, oc, rc, hc2⟩ := loc c (hWF.vis_dom hc.1).1 hu
  have hac : a = c := hdist a c ha1 hc1 ia ic oa oc u ra rc ha2 hc2
  subst hac
  have hord : A.ord α.length (α.length + 1) :=
    hOn.2.2 _ _ dr dw (by rw [rr, rw']) (by omega)
  have hvis : A.vis a (α.length + 1) := hWF.vis_mono ha.1 hord (by rw [rr, rw'])
  exact hWF.ord_irrefl _ (hWF.transGen_ord (htg.tail hvis))

end Podc.EventualConsistencyLimits
