import Papers.PODC2010.MultiVersionSTM.Basic

/-!
# Forced responses

Tools for the impossibility proofs: in the scenarios of the paper, MV-permissiveness forces every
operation to succeed, and then all structural facts about a history (who began, committed, wrote,
real-time order) are facts about its schedule.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type}

/-- All operations of `h` succeeded (no abort). -/
def AllSucc (h : Hist Tx O) : Prop := ∀ e ∈ h, e.resp ≠ none

section Succ

variable {h h₁ h₂ : Hist Tx O} {T : Tx} {o : O}

lemma AllSucc.append (h₁s : AllSucc h₁) (h₂s : AllSucc h₂) : AllSucc (h₁ ++ h₂) := by
  intro e he; rcases List.mem_append.1 he with he | he
  exacts [h₁s e he, h₂s e he]

lemma AllSucc.of_append (hs : AllSucc (h₁ ++ h₂)) : AllSucc h₁ :=
  fun e he => hs e (List.mem_append_left _ he)

lemma allSucc_snoc {e : Event Tx O} : AllSucc (h ++ [e]) ↔ AllSucc h ∧ e.resp ≠ none := by
  simp [AllSucc, or_imp, forall_and]

lemma committed_iff_of_succ (hs : AllSucc h) : Committed h T ↔ Inv.commit T ∈ h.map Event.inv := by
  constructor
  · rintro ⟨r, hr⟩; exact List.mem_map.2 ⟨_, hr, rfl⟩
  · intro hm
    obtain ⟨e, he, hei⟩ := List.mem_map.1 hm
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 (hs e he)
    refine ⟨r, ?_⟩
    cases e; simp_all

lemma not_aborted_of_succ (hs : AllSucc h) : ¬ Aborted h T := by
  rintro ⟨e, he, -, hr⟩; exact hs e he hr

lemma terminated_iff_of_succ (hs : AllSucc h) : Terminated h T ↔ Inv.commit T ∈ h.map Event.inv := by
  simp [Terminated, not_aborted_of_succ hs, committed_iff_of_succ hs]

lemma began_iff_map : Began h T ↔ ∃ i ∈ h.map Event.inv, i.tx = T := by
  simp [Began]

lemma writes_iff_map : Writes h T o ↔ Inv.write T o ∈ h.map Event.inv := by
  constructor
  · rintro ⟨r, hr⟩; exact List.mem_map.2 ⟨_, hr, rfl⟩
  · intro hm
    obtain ⟨e, he, hei⟩ := List.mem_map.1 hm
    exact ⟨e.resp, by cases e; simp_all⟩

lemma accesses_iff_map : Accesses h T o ↔ ∃ i ∈ h.map Event.inv, i.tx = T ∧ i.obj? = some o := by
  simp [Accesses]

end Succ

/-! ### Real-time order and concurrency -/

section RT

variable {h h' : Hist Tx O} {A B T : Tx}

lemma RT.of_split (h₁ h₂ : Hist Tx O) (hh : h = h₁ ++ h₂) (hA : Committed h₁ A) (hB : ¬ Began h₁ B)
    (hB' : Began h B) : RT h A B :=
  ⟨hB', h₁, h₂, hh, hA, hB⟩

lemma RT.mono (hr : RT h A B) (h' : Hist Tx O) : RT (h ++ h') A B := by
  obtain ⟨hb, h₁, h₂, rfl, hA, hB⟩ := hr
  exact ⟨hb.mono h', h₁, h₂ ++ h', by simp, hA, hB⟩

lemma not_concurrent_of_not_began (hb : ¬ Began h B) : ¬ Concurrent h A B :=
  fun hc => hb hc.2.1

lemma not_concurrent_of_rt (hr : RT h B A) : ¬ Concurrent h A B :=
  fun hc => hc.2.2.2 hr

end RT

/-! ### Decomposing histories of executions -/

namespace STM

variable (X : STM Tx O P) [TxSys Tx P]

lemma hist_decomp (σ₁ : List (Inv Tx O)) (i : Inv Tx O) (σ₂ : List (Inv Tx O)) :
    ∃ h₂, X.hist (σ₁ ++ i :: σ₂) = X.hist σ₁ ++ ⟨i, X.resp σ₁ i⟩ :: h₂ := by
  rw [hist_append, run_cons]
  exact ⟨_, rfl⟩

lemma hist_prefix (σ₁ σ₂ : List (Inv Tx O)) : ∃ h₂, X.hist (σ₁ ++ σ₂) = X.hist σ₁ ++ h₂ := by
  rw [hist_append]; exact ⟨_, rfl⟩

/-- MV-permissiveness forces a successful response when the transaction is read-only, or no
concurrent update transaction conflicts with it. -/
lemma resp_ne_none (hm : X.MVPermissive) (σ : List (Inv Tx O)) (i : Inv Tx O)
    (hwf : WF (X.hist σ)) (hok : OKNext (X.hist σ) i)
    (hni : ro i.tx = true ∨ ∀ T', T' ≠ i.tx → ro T' = false →
      ¬ (Concurrent (X.hist σ ++ [⟨i, none⟩]) i.tx T' ∧ Conflict (X.hist σ ++ [⟨i, none⟩]) i.tx T')) :
    X.resp σ i ≠ none := by
  intro hr
  have hwf' : WF (X.hist (σ ++ [i])) := by
    rw [hist_snoc]; exact hwf.snoc _ hok
  have := hm (σ ++ [i]) hwf' (X.hist σ) i [] (by rw [hist_snoc, hr])
  obtain ⟨hro, T', hne, hroT, hc, hcf⟩ := this
  rcases hni with h | h
  · simp_all
  · exact h T' hne hroT ⟨hc, hcf⟩

/-- A successful read returns `none` if no write of the object has been invoked. -/
lemma resp_read_eq_none (hr : X.ReadsWrittenOnly) (σ : List (Inv Tx O)) (T : Tx) (o : O)
    (hwf : WF (X.hist (σ ++ [.read T o]))) (hs : X.resp σ (.read T o) ≠ none)
    (hnw : ∀ W, ¬ Writes (X.hist σ) W o) : X.resp σ (.read T o) = some none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hs
  rw [hv]
  cases v with
  | none => rfl
  | some W =>
    exact absurd (hr _ hwf (X.hist σ) T o W [] (by rw [hist_snoc, hv])) (hnw W)

end STM

/-! ### Good executions: well-formed, all operations successful -/

section Good

variable [TxSys Tx P]

/-- `OKNext` on the schedule level (for histories without aborts). -/
def OKNextS (σ : List (Inv Tx O)) (i : Inv Tx O) : Prop :=
  Inv.commit i.tx ∉ σ ∧ (∀ T o, i = .write T o → ro T = false) ∧
  ((¬ ∃ j ∈ σ, Inv.tx j = i.tx) → ∀ T', T' ≠ i.tx → thr T' = thr i.tx → (∃ j ∈ σ, Inv.tx j = T') →
    Inv.commit T' ∈ σ)

/-- The thread condition of `OKNextS` holds when all transactions involved run on distinct
threads. -/
lemma okNextS_thr {ι : Type} (t : ι → Tx) (ht : Function.Injective (fun k => thr (t k)))
    (σ : List (Inv Tx O)) (i : Inv Tx O) (hσ : ∀ j ∈ σ, ∃ k, Inv.tx j = t k) (hi : ∃ k, i.tx = t k) :
    (¬ ∃ j ∈ σ, Inv.tx j = i.tx) → ∀ T', T' ≠ i.tx → thr T' = thr i.tx → (∃ j ∈ σ, Inv.tx j = T') →
      Inv.commit T' ∈ σ := by
  intro _ T' hne hth ⟨j, hj, hjt⟩
  obtain ⟨a, ha⟩ := hσ j hj
  obtain ⟨b, hb⟩ := hi
  subst hjt; rw [ha, hb] at hth; rw [ha, hb] at hne
  exact absurd (congrArg t (ht hth)) hne

namespace STM

variable (X : STM Tx O P)

/-- The execution of `σ` is well-formed and has no abort. -/
def Good (σ : List (Inv Tx O)) : Prop := WF (X.hist σ) ∧ AllSucc (X.hist σ)

lemma good_nil : X.Good [] := ⟨WF.nil, fun _ h => by simp at h⟩

lemma okNext_of_S {σ : List (Inv Tx O)} {i : Inv Tx O} (hs : AllSucc (X.hist σ)) (hok : OKNextS σ i) :
    OKNext (X.hist σ) i := by
  obtain ⟨h1, h2, h3⟩ := hok
  refine ⟨?_, h2, ?_⟩
  · rw [terminated_iff_of_succ hs, map_inv_hist]; exact h1
  · intro hnb T' hne hthr hb
    rw [began_iff_map, map_inv_hist] at hnb hb
    rw [terminated_iff_of_succ hs, map_inv_hist]
    exact h3 hnb T' hne hthr hb

lemma rt_snoc_of_split {σ σ₁ σ₂ : List (Inv Tx O)} (hσ : σ = σ₁ ++ σ₂) {i : Inv Tx O} {r : Resp Tx}
    {A : Tx} (hs : AllSucc (X.hist σ)) (hA : Inv.commit A ∈ σ₁) (hB : ∀ j ∈ σ₁, Inv.tx j ≠ i.tx) :
    RT (X.hist σ ++ [⟨i, r⟩]) A i.tx := by
  subst hσ
  obtain ⟨h₂, hh⟩ := X.hist_prefix σ₁ σ₂
  have hs₁ : AllSucc (X.hist σ₁) := by rw [hh] at hs; exact hs.of_append
  refine RT.of_split (X.hist σ₁) (h₂ ++ [⟨i, r⟩]) (by rw [hh]; simp) ?_ ?_ ?_
  · rw [committed_iff_of_succ hs₁, map_inv_hist]; exact hA
  · rw [began_iff_map, map_inv_hist]; rintro ⟨j, hj, hjt⟩; exact hB j hj hjt
  · exact ⟨⟨i, r⟩, by simp, rfl⟩

/-- One more operation of a good execution succeeds, if it is well-formed and the transaction is
read-only or every update transaction that has begun committed before it began. -/
lemma good_snoc (hm : X.MVPermissive) {σ : List (Inv Tx O)} {i : Inv Tx O} (hg : X.Good σ)
    (hok : OKNextS σ i)
    (hni : ro i.tx = true ∨ ∀ T', T' ≠ i.tx → ro T' = false → (∃ j ∈ σ, Inv.tx j = T') →
      ∃ σ₁ σ₂, σ = σ₁ ++ σ₂ ∧ Inv.commit T' ∈ σ₁ ∧ ∀ j ∈ σ₁, Inv.tx j ≠ i.tx) :
    X.Good (σ ++ [i]) := by
  have hok' := X.okNext_of_S hg.2 hok
  have hne : X.resp σ i ≠ none := by
    refine X.resp_ne_none hm σ i hg.1 hok' ?_
    rcases hni with h | h
    · exact Or.inl h
    · refine Or.inr fun T' hT' hro ⟨hc, _⟩ => ?_
      have hb : ∃ j ∈ σ, Inv.tx j = T' := by
        have := hc.2.1
        rw [began_append, began_iff_map, map_inv_hist] at this
        rcases this with h' | ⟨e, he, het⟩
        · exact h'
        · simp at he; subst he; exact absurd het.symm hT'
      obtain ⟨σ₁, σ₂, hσ, hA, hB⟩ := h T' hT' hro hb
      exact not_concurrent_of_rt (X.rt_snoc_of_split hσ hg.2 hA hB) hc
  refine ⟨?_, ?_⟩
  · rw [hist_snoc]; exact hg.1.snoc _ hok'
  · rw [hist_snoc]; exact allSucc_snoc.2 ⟨hg.2, hne⟩

lemma good_take_succ (hm : X.MVPermissive) (σ : List (Inv Tx O)) (k : ℕ) (hk : k < σ.length)
    (hg : X.Good (σ.take k)) (hok : OKNextS (σ.take k) σ[k])
    (hni : ro (σ[k]).tx = true ∨ ∀ T', T' ≠ (σ[k]).tx → ro T' = false →
      (∃ j ∈ σ.take k, Inv.tx j = T') →
      ∃ σ₁ σ₂, σ.take k = σ₁ ++ σ₂ ∧ Inv.commit T' ∈ σ₁ ∧ ∀ j ∈ σ₁, Inv.tx j ≠ (σ[k]).tx) :
    X.Good (σ.take (k + 1)) := by
  rw [List.take_succ_eq_append_getElem hk]
  exact X.good_snoc hm hg hok hni

lemma good_snoc_ro (hm : X.MVPermissive) {σ : List (Inv Tx O)} {i : Inv Tx O} (hg : X.Good σ)
    (hok : OKNextS σ i) (hro : ro i.tx = true) : X.Good (σ ++ [i]) :=
  X.good_snoc hm hg hok (Or.inl hro)

lemma committed_hist_iff {σ : List (Inv Tx O)} {T : Tx} (hs : AllSucc (X.hist σ)) :
    Committed (X.hist σ) T ↔ Inv.commit T ∈ σ := by
  rw [committed_iff_of_succ hs, map_inv_hist]

lemma writes_hist_iff {σ : List (Inv Tx O)} {T : Tx} {o : O} :
    Writes (X.hist σ) T o ↔ Inv.write T o ∈ σ := by
  rw [writes_iff_map, map_inv_hist]

lemma began_hist_iff {σ : List (Inv Tx O)} {T : Tx} :
    Began (X.hist σ) T ↔ ∃ j ∈ σ, Inv.tx j = T := by
  rw [began_iff_map, map_inv_hist]

lemma cwriter_hist_iff {σ : List (Inv Tx O)} {o : O} {W : Tx} (hs : AllSucc (X.hist σ)) :
    CWriter (X.hist σ) o W ↔ Inv.commit W ∈ σ ∧ Inv.write W o ∈ σ := by
  rw [CWriter, committed_hist_iff X hs, writes_hist_iff]

lemma rt_hist (σ₁ σ₂ : List (Inv Tx O)) {A B : Tx} (hs : AllSucc (X.hist (σ₁ ++ σ₂)))
    (hA : Inv.commit A ∈ σ₁) (hB : ∀ j ∈ σ₁, Inv.tx j ≠ B) (hB' : ∃ j ∈ σ₂, Inv.tx j = B) :
    RT (X.hist (σ₁ ++ σ₂)) A B := by
  obtain ⟨h₂, hh⟩ := X.hist_prefix σ₁ σ₂
  have hs₁ : AllSucc (X.hist σ₁) := by rw [hh] at hs; exact hs.of_append
  refine RT.of_split (X.hist σ₁) h₂ hh ?_ ?_ ?_
  · rw [committed_hist_iff X hs₁]; exact hA
  · rw [began_hist_iff]; rintro ⟨j, hj, hjt⟩; exact hB j hj hjt
  · rw [began_hist_iff]; obtain ⟨j, hj, hjt⟩ := hB'; exact ⟨j, by simp [hj], hjt⟩

lemma commitBefore_hist (σ₁ σ₂ : List (Inv Tx O)) {A B : Tx} (hs : AllSucc (X.hist (σ₁ ++ σ₂)))
    (hA : Inv.commit A ∈ σ₁) (hB : Inv.commit B ∉ σ₁) : CommitBefore (X.hist (σ₁ ++ σ₂)) A B := by
  obtain ⟨h₂, hh⟩ := X.hist_prefix σ₁ σ₂
  have hs₁ : AllSucc (X.hist σ₁) := by rw [hh] at hs; exact hs.of_append
  exact ⟨X.hist σ₁, h₂, hh, (committed_hist_iff X hs₁).2 hA, by rwa [committed_hist_iff X hs₁]⟩

/-- In a good execution, a read of an object no write of which has been invoked returns the
initial version. -/
lemma read_none (hr : X.ReadsWrittenOnly) {σ : List (Inv Tx O)} {T : Tx} {o : O}
    (hg : X.Good (σ ++ [.read T o])) (hnw : ∀ W, Inv.write W o ∉ σ) :
    X.resp σ (.read T o) = some none := by
  refine X.resp_read_eq_none hr σ T o hg.1 ?_ ?_
  · have := hg.2; rw [hist_snoc] at this; exact (allSucc_snoc.1 this).2
  · intro W; rw [writes_hist_iff]; exact hnw W

lemma hist_decomp' {σ σ₁ σ₂ : List (Inv Tx O)} {i : Inv Tx O} (hσ : σ = σ₁ ++ i :: σ₂) :
    ∃ h₂, X.hist σ = X.hist σ₁ ++ ⟨i, X.resp σ₁ i⟩ :: h₂ := by
  subst hσ; exact X.hist_decomp σ₁ i σ₂

lemma resp_some_of_good {σ : List (Inv Tx O)} {i : Inv Tx O} (hg : X.Good (σ ++ [i])) :
    ∃ r, X.resp σ i = some r := by
  have := hg.2; rw [hist_snoc] at this
  exact Option.ne_none_iff_exists'.1 (allSucc_snoc.1 this).2

lemma good_of_append {σ τ : List (Inv Tx O)} (hg : X.Good (σ ++ τ)) : X.Good σ := by
  obtain ⟨h₂, hh⟩ := X.hist_prefix σ τ
  rw [Good, hh] at hg
  exact ⟨hg.1.of_append, hg.2.of_append⟩

/-- Variant of `good_snoc`: every update transaction that has begun either committed before
`i.tx` began, or accesses no object that `i.tx` accesses. -/
lemma good_snoc2 (hm : X.MVPermissive) {σ : List (Inv Tx O)} {i : Inv Tx O} (hg : X.Good σ)
    (hok : OKNextS σ i)
    (hni : ro i.tx = true ∨ ∀ T', T' ≠ i.tx → ro T' = false → (∃ j ∈ σ, Inv.tx j = T') →
      (∃ σ₁ σ₂, σ = σ₁ ++ σ₂ ∧ Inv.commit T' ∈ σ₁ ∧ ∀ j ∈ σ₁, Inv.tx j ≠ i.tx) ∨
      (∀ o, (∃ j ∈ σ ++ [i], Inv.tx j = i.tx ∧ j.obj? = some o) →
        ¬ ∃ j ∈ σ, Inv.tx j = T' ∧ j.obj? = some o)) :
    X.Good (σ ++ [i]) := by
  have hok' := X.okNext_of_S hg.2 hok
  have hne : X.resp σ i ≠ none := by
    refine X.resp_ne_none hm σ i hg.1 hok' ?_
    rcases hni with h | h
    · exact Or.inl h
    · refine Or.inr fun T' hT' hro ⟨hc, hcf⟩ => ?_
      have hmap : (X.hist σ ++ ([⟨i, none⟩] : Hist Tx O)).map Event.inv = σ ++ [i] := by
        simp [map_inv_hist]
      have hb : ∃ j ∈ σ, Inv.tx j = T' := by
        have := hc.2.1
        rw [began_iff_map, hmap] at this
        obtain ⟨j, hj, hjt⟩ := this
        rcases List.mem_append.1 hj with hj | hj
        · exact ⟨j, hj, hjt⟩
        · simp at hj; subst hj; exact absurd hjt.symm hT'
      rcases h T' hT' hro hb with ⟨σ₁, σ₂, hσ, hA, hB⟩ | hno
      · exact not_concurrent_of_rt (X.rt_snoc_of_split hσ hg.2 hA hB) hc
      · obtain ⟨o, h1, h2, -⟩ := hcf
        rw [accesses_iff_map, hmap] at h1 h2
        refine hno o h1 ?_
        obtain ⟨j, hj, hjt, hjo⟩ := h2
        rcases List.mem_append.1 hj with hj | hj
        · exact ⟨j, hj, hjt, hjo⟩
        · simp at hj; subst hj; exact absurd hjt.symm hT'
  refine ⟨?_, ?_⟩
  · rw [hist_snoc]; exact hg.1.snoc _ hok'
  · rw [hist_snoc]; exact allSucc_snoc.2 ⟨hg.2, hne⟩

lemma good_take_succ2 (hm : X.MVPermissive) (σ : List (Inv Tx O)) (k : ℕ) (hk : k < σ.length)
    (hg : X.Good (σ.take k)) (hok : OKNextS (σ.take k) σ[k])
    (hni : ro (σ[k]).tx = true ∨ ∀ T', T' ≠ (σ[k]).tx → ro T' = false →
      (∃ j ∈ σ.take k, Inv.tx j = T') →
      (∃ σ₁ σ₂, σ.take k = σ₁ ++ σ₂ ∧ Inv.commit T' ∈ σ₁ ∧ ∀ j ∈ σ₁, Inv.tx j ≠ (σ[k]).tx) ∨
      (∀ o, (∃ j ∈ σ.take k ++ [σ[k]], Inv.tx j = (σ[k]).tx ∧ j.obj? = some o) →
        ¬ ∃ j ∈ σ.take k, Inv.tx j = T' ∧ j.obj? = some o)) :
    X.Good (σ.take (k + 1)) := by
  rw [List.take_succ_eq_append_getElem hk]
  exact X.good_snoc2 hm hg hok hni

end STM

lemma SerWitness.lt_of_rt {h : Hist Tx O} {pos : Tx → ℕ} (hw : SerWitness h pos) {A B : Tx}
    (hA : Committed h A) (hB : Committed h B) (hr : RT h A B) : pos A < pos B :=
  hw.2.1 A B hA (Or.inl hB) hr

lemma SerWitness.ext {h : Hist Tx O} {pos : Tx → ℕ} (hw : SerWitness h pos) {T : Tx} {o : O}
    {v : Option Tx} {h₁ h₂ : Hist Tx O} (hT : Committed h T)
    (hh : h = h₁ ++ ⟨.read T o, some v⟩ :: h₂) (hnw : ¬ Writes h₁ T o) : ExtLegal h pos T o v :=
  (hw.2.2 T (Or.inl hT) h₁ o v h₂ hh).2 hnw

lemma SerWitness.inj {h : Hist Tx O} {pos : Tx → ℕ} (hw : SerWitness h pos) {A B : Tx}
    (hA : Committed h A) (hB : Committed h B) (hne : A ≠ B) : pos A ≠ pos B :=
  fun he => hne (hw.1 A B (Or.inl hA) (Or.inl hB) he)

lemma SerWitness.lt_split (X : STM Tx O P) {σ : List (Inv Tx O)} {pos : Tx → ℕ}
    (hw : SerWitness (X.hist σ) pos) (hs : AllSucc (X.hist σ)) (σ₁ σ₂ : List (Inv Tx O))
    (hσ : σ = σ₁ ++ σ₂) {A B : Tx} (hA : Inv.commit A ∈ σ₁) (hB : ∀ j ∈ σ₁, Inv.tx j ≠ B)
    (hB' : ∃ j ∈ σ₂, Inv.tx j = B) (hBc : Inv.commit B ∈ σ₂) : pos A < pos B := by
  subst hσ
  exact hw.lt_of_rt ((X.committed_hist_iff hs).2 (List.mem_append_left _ hA))
    ((X.committed_hist_iff hs).2 (List.mem_append_right _ hBc)) (X.rt_hist σ₁ σ₂ hs hA hB hB')

end Good

end Podc.MultiVersionSTM
