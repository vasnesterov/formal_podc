import Papers.PODC2010.MultiVersionSTM.SnapshotProofs

/-!
# The eager snapshot STM with self-erasing read-only transactions

A variant `snapSmall` of the eager snapshot STM (`snapSTM false`, `Snapshot.lean`): its shared
memory holds the history *without the events of committed read-only transactions*
(`erase h`). A read-only transaction erases its own events when it commits. Under
well-formedness the responses are the same as those of `snapSTM false` (`snapResp_erase`), so
the two STMs have the same histories (`snapSmall_hist`), and `snapSmall` is valid with the kept
versions `keptSmall C = snapKept false (C.mem ())` (`snapSmall_valid`).

The point of the construction (used in `Theorem3False.lean`): a solo read-only transaction of
`snapSmall` leaves the shared memory unchanged (`erase_append_ro`).

Main lemmas:

* `latest_filter`: removing events of read-only transactions does not change the latest versions;
* `take_findIdx_filter`: the snapshot prefix of a filtered history is the filtered snapshot
  prefix;
* `validates_filter`: the read-set validation of an update transaction only depends on its own
  events and on the latest versions;
* `snapResp_erase`, `snapKept_erase`, `erase_snoc`: the snapshot strategy and the kept versions
  are the same on `erase h` and on `h`, and `erase` is maintained step by step.
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type}

/-! ### List helper -/

/-- The prefix of a filtered list up to the first element satisfying `q` is the filtered prefix,
if `q` implies `p`. -/
lemma take_findIdx_filter {α : Type} (l : List α) (p q : α → Bool)
    (hqp : ∀ a, q a = true → p a = true) :
    (l.filter p).take ((l.filter p).findIdx q) = (l.take (l.findIdx q)).filter p := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases hq : q x = true
    · simp [hqp x hq, List.findIdx_cons, hq]
    · by_cases hp : p x = true
      · simp [hp, List.findIdx_cons, hq, ih]
      · simp [hp, List.findIdx_cons, hq, ih]

/-! ### Filtering histories -/

section Filter

variable [TxSys Tx P]

lemma writes_filter_iff {l : Hist Tx O} {p : Event Tx O → Bool} {W : Tx} {o : O}
    (hp : ∀ e ∈ l, e.inv.tx = W → p e = true) : Writes (l.filter p) W o ↔ Writes l W o := by
  constructor
  · rintro ⟨r, hr⟩; exact ⟨r, (List.mem_filter.1 hr).1⟩
  · rintro ⟨r, hr⟩; exact ⟨r, List.mem_filter.2 ⟨hr, hp _ hr rfl⟩⟩

/-- Removing events of read-only transactions (which write nothing) does not change the latest
versions. -/
lemma latest_filter (l : Hist Tx O) (p : Event Tx O → Bool) (o : O)
    (hp : ∀ e ∈ l, ro e.inv.tx = false → p e = true)
    (hro : ∀ W o', Writes l W o' → ro W = false) :
    latest (l.filter p) o = latest l o := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l x ih =>
    have hp' : ∀ e ∈ l, ro e.inv.tx = false → p e = true :=
      fun e he => hp e (List.mem_append_left _ he)
    have hro' : ∀ W o', Writes l W o' → ro W = false := fun W o' hw => hro W o' (hw.mono _)
    have hcw : CommitWrites (l.filter p) x o ↔ CommitWrites l x o := by
      unfold CommitWrites
      refine and_congr Iff.rfl (exists_congr fun W => and_congr_right fun _ => ?_)
      constructor
      · rintro ⟨r, hr⟩; exact ⟨r, (List.mem_filter.1 hr).1⟩
      · intro hw
        have hWro := hro' W o hw
        exact (writes_filter_iff (fun e he heW => hp' e he (heW ▸ hWro))).2 hw
    rw [List.filter_append, latest_snoc]
    by_cases hpx : p x = true
    · simp only [List.filter_cons, hpx, ↓reduceIte, List.filter_nil]
      rw [latest_snoc, ih hp' hro']
      simp only [hcw]
    · have hxro : ro x.inv.tx = true := by
        by_contra hc
        exact hpx (hp x (by simp) (by simpa using hc))
      have hncw : ¬ CommitWrites l x o := by
        rintro ⟨_, W, hW, hw⟩
        have := hro' W o hw
        rw [hW] at hxro
        simp [this] at hxro
      simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte, List.filter_nil,
        List.append_nil, hncw]
      exact ih hp' hro'

/-- The read-set validation of `T` is the same after removing events of other transactions that
do not change the latest versions. -/
lemma validates_filter (l : Hist Tx O) (p : Event Tx O → Bool) (T : Tx)
    (hp : ∀ e : Event Tx O, e.inv.tx = T → p e = true)
    (hlat : ∀ o, latest (l.filter p) o = latest l o) :
    Validates (l.filter p) T ↔ Validates l T := by
  have hwr : ∀ (h₁ : Hist Tx O) o, Writes (h₁.filter p) T o ↔ Writes h₁ T o :=
    fun h₁ o => writes_filter_iff (fun e _ he => hp e he)
  constructor
  · intro hv h₁ o v h₂ hdec hnw
    have : l.filter p = h₁.filter p ++ ⟨.read T o, some v⟩ :: h₂.filter p := by
      rw [hdec, List.filter_append, List.filter_cons, hp _ rfl]; rfl
    rw [← hlat]
    exact hv _ o v _ this (by rwa [hwr])
  · intro hv h₁ o v h₂ hdec hnw
    obtain ⟨a, b, rfl, ha, hb⟩ := List.filter_eq_append_iff.1 hdec
    obtain ⟨c, d, rfl, hc, -, -⟩ := List.filter_eq_cons_iff.1 hb
    have hcn : c.filter p = [] := List.filter_eq_nil_iff.2 hc
    rw [hlat]
    refine hv (a ++ c) o v d (by simp) ?_
    rw [← hwr, List.filter_append, ha, hcn, List.append_nil]; exact hnw

end Filter

/-! ### Erasing committed read-only transactions -/

section Erase

variable [TxSys Tx P]

/-- The events kept by `erase h`: those that are not of a committed read-only transaction. -/
noncomputable def keepEv (h : Hist Tx O) (e : Event Tx O) : Bool :=
  decide (¬ (ro e.inv.tx = true ∧ Committed h e.inv.tx))

/-- The history `h` without the events of its committed read-only transactions. -/
noncomputable def erase (h : Hist Tx O) : Hist Tx O := h.filter (keepEv h)

variable {h : Hist Tx O} {T : Tx} {o : O}

lemma keepEv_eq_true_iff {e : Event Tx O} :
    keepEv h e = true ↔ ¬ (ro e.inv.tx = true ∧ Committed h e.inv.tx) := by
  simp only [keepEv, decide_eq_true_eq]

lemma keepEv_of_ro_false {e : Event Tx O} (hro : ro e.inv.tx = false) : keepEv h e = true :=
  keepEv_eq_true_iff.2 (fun ⟨h1, _⟩ => by simp [hro] at h1)

lemma keepEv_of_not_committed {e : Event Tx O} (hc : ¬ Committed h e.inv.tx) :
    keepEv h e = true :=
  keepEv_eq_true_iff.2 (fun ⟨_, h2⟩ => hc h2)

@[simp] lemma erase_nil : erase ([] : Hist Tx O) = [] := rfl

lemma mem_of_mem_erase {e : Event Tx O} (he : e ∈ erase h) : e ∈ h := (List.mem_filter.1 he).1

lemma snap_false (h : Hist Tx O) (T : Tx) : snap false h T = firstIdx h T := rfl

lemma latest_erase (hw : WF h) (o : O) : latest (erase h) o = latest h o :=
  latest_filter h _ o (fun _ _ he => keepEv_of_ro_false he) (fun _ _ hw' => hw.ro_of_writes hw')

/-- The snapshot of a transaction that has not committed is the same in `erase h` and `h`. -/
lemma latest_erase_snap (hw : WF h) (hc : ¬ Committed h T) (o : O) :
    latest ((erase h).take (firstIdx (erase h) T)) o = latest (h.take (firstIdx h T)) o := by
  unfold erase firstIdx
  rw [take_findIdx_filter]
  · exact latest_filter _ _ o (fun _ _ he => keepEv_of_ro_false he)
      (fun _ _ hw' => hw.ro_of_writes hw'.of_take)
  · intro e he
    simp only [decide_eq_true_eq] at he
    exact keepEv_of_not_committed (he ▸ hc)

lemma writes_erase (hro : ro T = false) : Writes (erase h) T o ↔ Writes h T o :=
  writes_filter_iff (fun _ _ he => keepEv_of_ro_false (he ▸ hro))

lemma validates_erase (hw : WF h) (hro : ro T = false) : Validates (erase h) T ↔ Validates h T :=
  validates_filter h _ T (fun _ he => keepEv_of_ro_false (he ▸ hro)) (latest_erase hw)

/-- **The eager snapshot strategy gives the same responses on `erase h` as on `h`.** -/
lemma snapResp_erase (hw : WF h) {i : Inv Tx O} (hok : OKNext h i) :
    snapResp false (erase h) i = snapResp false h i := by
  cases i with
  | read T o =>
    simp only [snapResp, snap_false]
    by_cases hro : ro T = true
    · simp only [hro, ↓reduceIte]
      have hnc : ¬ Committed h T := fun hc => hok.1 (Or.inl hc)
      rw [latest_erase_snap hw hnc]
    · simp only [Bool.not_eq_true] at hro
      simp only [hro, Bool.false_eq_true, ↓reduceIte, writes_erase hro, latest_erase hw,
        validates_erase hw hro]
  | write T o => rfl
  | commit T =>
    simp only [snapResp]
    by_cases hro : ro T = true
    · simp [hro]
    · simp only [Bool.not_eq_true] at hro
      simp only [hro, Bool.false_eq_true, ↓reduceIte, validates_erase hw hro]

lemma terminated_of_terminated_erase (ht : Terminated (erase h) T) : Terminated h T := by
  rcases ht with ⟨r, hr⟩ | ⟨e, he, h1, h2⟩
  · exact Or.inl ⟨r, mem_of_mem_erase hr⟩
  · exact Or.inr ⟨e, mem_of_mem_erase he, h1, h2⟩

lemma terminated_erase_of_not_committed (hc : ¬ Committed h T) (ht : Terminated h T) :
    Terminated (erase h) T := by
  rcases ht with hc' | ⟨e, he, h1, h2⟩
  · exact absurd hc' hc
  · exact Or.inr ⟨e, List.mem_filter.2 ⟨he, keepEv_of_not_committed (h1 ▸ hc)⟩, h1, h2⟩

lemma not_began_erase (hro : ro T = true) (hc : Committed h T) : ¬ Began (erase h) T := by
  rintro ⟨e, he, rfl⟩
  have := (List.mem_filter.1 he).2
  rw [keepEv_eq_true_iff] at this
  exact this ⟨hro, hc⟩

/-- **The kept versions of the eager snapshot STM are the same on `erase h` as on `h`.** A
committed read-only transaction has no event in `erase h`; its snapshot there is the latest
version, which is kept anyway. -/
lemma snapKept_erase (hw : WF h) : snapKept false (erase h) = snapKept false h := by
  ext ⟨o, x⟩
  simp only [mem_snapKept, snap_false, latest_erase hw]
  constructor
  · rintro (h1 | ⟨T, hro, hnt, hx⟩)
    · exact Or.inl h1
    · by_cases hc : Committed h T
      · left
        rw [hx, firstIdx_eq_length (not_began_erase hro hc), List.take_length, latest_erase hw]
      · exact Or.inr ⟨T, hro, fun ht => hnt (terminated_erase_of_not_committed hc ht),
          by rw [hx, latest_erase_snap hw hc]⟩
  · rintro (h1 | ⟨T, hro, hnt, hx⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨T, hro, fun ht => hnt (terminated_of_terminated_erase ht),
        by rw [latest_erase_snap hw (fun hc => hnt (Or.inl hc)), hx]⟩

lemma committed_snoc {e : Event Tx O} :
    Committed (h ++ [e]) T ↔ Committed h T ∨ ∃ r, e = ⟨.commit T, some r⟩ := by
  rw [committed_append, committed_cons]; simp

/-- `i` is the commit of a read-only transaction. -/
def roCommit : Inv Tx O → Bool
  | .commit T => ro T
  | _ => false

lemma erase_snoc_of_not_roCommit {e : Event Tx O} (hok : OKNext h e.inv)
    (hrc : roCommit e.inv = false) : erase (h ++ [e]) = erase h ++ [e] := by
  have hcomm : ∀ T, ro T = true → (Committed (h ++ [e]) T ↔ Committed h T) := by
    intro T hro
    rw [committed_snoc]
    refine or_iff_left ?_
    rintro ⟨r, hr⟩
    rw [hr] at hrc
    simp [roCommit, hro] at hrc
  unfold erase
  rw [List.filter_append]
  congr 1
  · refine List.filter_congr (fun x _ => ?_)
    simp only [keepEv]
    by_cases hro : ro x.inv.tx = true
    · rw [hcomm _ hro]
    · simp [hro]
  · have : keepEv (h ++ [e]) e = true := by
      rw [keepEv_eq_true_iff]
      rintro ⟨hro, hc⟩
      exact hok.1 (Or.inl ((hcomm _ hro).1 hc))
    simp [this]

lemma erase_snoc_roCommit (hro : ro T = true) (r : Option Tx) :
    erase (h ++ [(⟨.commit T, some r⟩ : Event Tx O)]) =
      (erase h ++ [(⟨.commit T, some r⟩ : Event Tx O)]).filter (fun e => decide (e.inv.tx ≠ T)) := by
  unfold erase
  rw [List.filter_append, List.filter_append, List.filter_filter]
  have h1 : keepEv (h ++ [(⟨.commit T, some r⟩ : Event Tx O)]) ⟨.commit T, some r⟩ = false := by
    simp only [keepEv, Inv.tx_commit]
    simpa using ⟨hro, committed_snoc.2 (Or.inr ⟨r, rfl⟩)⟩
  simp only [List.filter_cons, h1, List.filter_nil, Inv.tx_commit, ne_eq, not_true_eq_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  refine List.filter_congr (fun x _ => ?_)
  by_cases hxT : x.inv.tx = T
  · simp [keepEv, hxT, hro, committed_snoc]
  · have : Committed (h ++ [(⟨.commit T, some r⟩ : Event Tx O)]) x.inv.tx ↔
        Committed h x.inv.tx := by
      rw [committed_snoc]
      refine or_iff_left ?_
      rintro ⟨r', hr'⟩
      simp only [Event.mk.injEq, Inv.commit.injEq] at hr'
      exact hxT hr'.1.symm
    simp [keepEv, hxT, this]

/-- A solo read-only transaction that commits leaves the erased history unchanged. -/
lemma erase_append_ro {t : Hist Tx O} (hro : ro T = true) (ht : ∀ e ∈ t, e.inv.tx = T)
    (hnb : ¬ Began h T) (hc : Committed (h ++ t) T) : erase (h ++ t) = erase h := by
  unfold erase
  rw [List.filter_append]
  have h2 : t.filter (keepEv (h ++ t)) = [] := by
    refine List.filter_eq_nil_iff.2 (fun e he => ?_)
    rw [keepEv_eq_true_iff, ht e he]
    exact fun hn => hn ⟨hro, hc⟩
  rw [h2, List.append_nil]
  refine List.filter_congr (fun x hx => ?_)
  have hxT : x.inv.tx ≠ T := fun hxT => hnb ⟨x, hx, hxT⟩
  have : Committed (h ++ t) x.inv.tx ↔ Committed h x.inv.tx := by
    rw [committed_append]
    refine or_iff_left ?_
    rintro ⟨r', hr'⟩
    exact hxT (ht ⟨.commit x.inv.tx, some r'⟩ hr')
  simp [keepEv, this]

end Erase

/-! ### The STM `snapSmall` -/

section STMDef

variable [TxSys Tx P]

/-- The step of `snapSmall` on its shared memory `s` (an erased history): append the event of `i`,
with the response of the eager snapshot strategy computed from `s`; if `i` is the commit of a
read-only transaction (which always succeeds), erase that transaction. -/
noncomputable def smallNext (s : Hist Tx O) (i : Inv Tx O) : Hist Tx O :=
  if roCommit i then
    (s ++ [(⟨i, snapResp false s i⟩ : Event Tx O)]).filter (fun e => decide (e.inv.tx ≠ i.tx))
  else s ++ [⟨i, snapResp false s i⟩]

/-- **The eager snapshot STM with self-erasing read-only transactions.** One base object holds the
history without the events of committed read-only transactions; each step runs the eager snapshot
strategy on it and appends its event, and a read-only transaction erases its events when it
commits. -/
noncomputable def snapSmall : STM Tx O P where
  B := Unit
  M := Hist Tx O
  L := Unit
  mem₀ := fun _ => []
  loc₀ := fun _ => ()
  prog := fun _ _ i => .access () (fun s => smallNext s i) (fun s => .ret ((), snapResp false s i))

/-- The versions kept by `snapSmall`: those kept by the eager snapshot STM after the history
stored in its memory. -/
def keptSmall (C : Config (snapSmall (Tx := Tx) (O := O) (P := P))) : Set (Version Tx O) :=
  snapKept false (C.mem ())

variable {h : Hist Tx O}

/-- `erase` is maintained by the steps of `snapSmall`. -/
lemma erase_snoc (hw : WF h) {i : Inv Tx O} (hok : OKNext h i) :
    erase (h ++ [⟨i, snapResp false h i⟩]) = smallNext (erase h) i := by
  unfold smallNext
  rw [snapResp_erase hw hok]
  split_ifs with hrc
  · cases i with
    | read T o => simp [roCommit] at hrc
    | write T o => simp [roCommit] at hrc
    | commit T =>
      simp only [roCommit] at hrc
      have : snapResp false h (.commit T) = some none := by simp [snapResp, hrc]
      rw [this]
      exact erase_snoc_roCommit hrc none
  · exact erase_snoc_of_not_roCommit hok (by simpa using hrc)

end STMDef

/-! ### `snapSmall` simulates the eager snapshot STM -/

section STMLevel

variable [TxSys Tx P]

lemma snapSmall_resp (σ : List (Inv Tx O)) (i : Inv Tx O) :
    (snapSmall (P := P)).resp σ i = snapResp false (((snapSmall (P := P)).conf σ).mem ()) i := by
  simp [STM.resp, STM.step, snapSmall, Prog.run]

lemma snapSmall_conf_mem_snoc (σ : List (Inv Tx O)) (i : Inv Tx O) :
    ((snapSmall (P := P)).conf (σ ++ [i])).mem () =
      smallNext (((snapSmall (P := P)).conf σ).mem ()) i := by
  rw [STM.conf_snoc]; simp [STM.step, snapSmall, Prog.run]

/-- **Simulation.** On well-formed schedules, `snapSmall` has the same history as the eager
snapshot STM, and its memory holds the erased history. -/
theorem snapSmall_sim (σ : List (Inv Tx O))
    (hw : WF ((snapSmall (Tx := Tx) (O := O) (P := P)).hist σ)) :
    (snapSmall (P := P)).hist σ = (snapSTM (P := P) false).hist σ ∧
      ((snapSmall (P := P)).conf σ).mem () = erase ((snapSmall (P := P)).hist σ) := by
  induction σ using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton σ i ih =>
    rw [STM.hist_snoc] at hw
    obtain ⟨hw₁, hok⟩ := (WF.snoc_iff _).1 hw
    obtain ⟨hh, hm⟩ := ih hw₁
    have hr : (snapSmall (P := P)).resp σ i = snapResp false ((snapSmall (P := P)).hist σ) i := by
      rw [snapSmall_resp, hm, snapResp_erase hw₁ hok]
    refine ⟨?_, ?_⟩
    · rw [STM.hist_snoc, STM.hist_snoc, hr, snapSTM_resp, hh]
    · rw [snapSmall_conf_mem_snoc, hm, STM.hist_snoc, hr, erase_snoc hw₁ hok]

/-- **`snapSmall` is valid**: strictly serializable, MV-permissive, its reads return written and
kept versions, and garbage collection is final. -/
theorem snapSmall_valid : (snapSmall (Tx := Tx) (O := O) (P := P)).Valid keptSmall := by
  refine ⟨fun σ hw => ?_, fun σ hw => ?_, fun σ hw => ?_, ?_, ?_⟩
  · have hh := (snapSmall_sim σ hw).1
    rw [hh]; exact snapSTM_correct false σ (hh ▸ hw)
  · have hh := (snapSmall_sim σ hw).1
    rw [hh]; exact snapSTM_mvPermissive false σ (hh ▸ hw)
  · have hh := (snapSmall_sim σ hw).1
    rw [hh]; exact snapSTM_readsWritten false σ (hh ▸ hw)
  · intro σ T o v hw hr hnw
    rw [STM.hist_snoc] at hw
    obtain ⟨hw₁, hok⟩ := (WF.snoc_iff _).1 hw
    have hm := (snapSmall_sim σ hw₁).2
    show (o, v) ∈ snapKept false (((snapSmall (P := P)).conf σ).mem ())
    rw [hm, snapKept_erase hw₁]
    rw [snapSmall_resp, hm, snapResp_erase hw₁ hok] at hr
    exact snapKept_of_read hok hr hnw
  · intro σ τ v hw hv hnk
    have hw₁ : WF ((snapSmall (P := P)).hist σ) := by
      rw [STM.hist_append] at hw; exact hw.of_append
    show v ∉ snapKept false (((snapSmall (P := P)).conf (σ ++ τ)).mem ())
    change v ∉ snapKept false (((snapSmall (P := P)).conf σ).mem ()) at hnk
    rw [(snapSmall_sim (σ ++ τ) hw).2, snapKept_erase hw]
    rw [(snapSmall_sim σ hw₁).2, snapKept_erase hw₁] at hnk
    rw [STM.hist_append] at hw ⊢
    exact not_mem_snapKept_append hw hv hnk

/-- **Read-only transactions of `snapSmall` leave no trace**: a solo read-only transaction that
commits leaves the shared memory unchanged (and the private states are trivial). -/
theorem snapSmall_noTrace : (snapSmall (Tx := Tx) (O := O) (P := P)).NoTrace := by
  intro σ τ T hw hro hτ hnb hc
  have hw₁ : WF ((snapSmall (P := P)).hist σ) := by
    rw [STM.hist_append] at hw; exact hw.of_append
  refine ⟨funext fun b => ?_, fun q _ => rfl⟩
  cases b
  rw [(snapSmall_sim σ hw₁).2, (snapSmall_sim (σ ++ τ) hw).2, STM.hist_append]
  rw [STM.hist_append] at hc
  refine (erase_append_ro hro (fun e he => ?_) hnb hc).symm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 he
  apply hτ
  rw [← STM.map_inv_run _ ((snapSmall (P := P)).conf σ) τ]
  exact List.mem_map_of_mem (f := fun s => s.1.inv) hs

end STMLevel

/-! ### Reading a kept version (for UP GC) -/

section UPGCHist

variable [TxSys Tx P] {h : Hist Tx O} {T : Tx} {o : O}

/-- `ExtLegal` determines the version read, when `pos` is injective on committed transactions. -/
lemma extLegal_unique {pos : Tx → ℕ} {a b : Option Tx}
    (hinj : ∀ A B, Committed h A → Committed h B → pos A = pos B → A = B)
    (ha : ExtLegal h pos T o a) (hb : ExtLegal h pos T o b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some W =>
      obtain ⟨hne, hcw, hlt, -⟩ := hb
      exact absurd (ha W hcw hne) (not_lt.2 hlt.le)
  | some W =>
    cases b with
    | none =>
      obtain ⟨hne, hcw, hlt, -⟩ := ha
      exact absurd (hb W hcw hne) (not_lt.2 hlt.le)
    | some W' =>
      obtain ⟨hne, hcw, hlt, hmax⟩ := ha
      obtain ⟨hne', hcw', hlt', hmax'⟩ := hb
      rw [hinj W W' hcw.1 hcw'.1 (le_antisymm (hmax' W hcw hne hlt) (hmax W' hcw' hne' hlt'))]

lemma commitBefore_irrefl {A : Tx} : ¬ CommitBefore h A A := by
  rintro ⟨_, _, _, h1, h2⟩; exact h2 h1

lemma firstIdx_snoc_self {e : Event Tx O} (he : e.inv.tx = T) :
    firstIdx (h ++ [e]) T = firstIdx h T := by
  unfold firstIdx
  rw [List.findIdx_append]
  split_ifs with hlt
  · rfl
  · have : h.findIdx (fun e => decide (e.inv.tx = T)) = h.length :=
      le_antisymm List.findIdx_le_length (not_lt.1 hlt)
    simp [List.findIdx_cons, he, this]

lemma not_terminated_snoc_read {v : Option Tx} (hnt : ¬ Terminated h T) :
    ¬ Terminated (h ++ [⟨.read T o, some v⟩]) T := by
  rw [terminated_append, terminated_cons]; simp [hnt]

lemma snapResp_read_ro (hro : ro T = true) :
    snapResp false h (.read T o) = some (latest (h.take (firstIdx h T)) o) := by
  simp [snapResp, hro, snap_false]

/-- **A read-only transaction reading its snapshot version.** If a read-only transaction `T` may
read `o` after a generated, well-formed history `h`, the eager snapshot strategy returns the
version `x` of its snapshot; afterwards `T` is live, can read `(o, x)` (reading it again and
committing gives a generated, hence strictly serializable, history), and cannot read any version
of `o` written after `(o, x)` (two reads of `o` by `T` must return the same version in any
serialization). -/
lemma upgc_read (hw : WF h) (hg : Gen false h) (hro : ro T = true) (hok : OKNext h (.read T o))
    {x : Option Tx} (hx : x = latest (h.take (firstIdx h T)) o) :
    WF (h ++ [⟨.read T o, some x⟩]) ∧ Live (h ++ [⟨.read T o, some x⟩]) T ∧
      STM.CanRead (h ++ [⟨.read T o, some x⟩]) T (o, x) ∧
      ∀ w, WrittenAfter (h ++ [⟨.read T o, some x⟩]) (o, x) w →
        ¬ STM.CanRead (h ++ [⟨.read T o, some x⟩]) T w := by
  have hresp : snapResp false h (.read T o) = some x := by rw [snapResp_read_ro hro, hx]
  have hw' : WF (h ++ [⟨.read T o, some x⟩]) := hw.snoc _ hok
  have hg' : Gen false (h ++ [⟨.read T o, some x⟩]) := by
    have := hg.snoc (.read T o); rwa [hresp] at this
  have hnt' : ¬ Terminated (h ++ [⟨.read T o, some x⟩]) T := not_terminated_snoc_read hok.1
  have hb' : Began (h ++ [⟨.read T o, some x⟩]) T :=
    ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
  have hnw : ∀ h₁ : Hist Tx O, WF h₁ → ¬ Writes h₁ T o := fun h₁ hw₁ hwr => by
    simp [hw₁.ro_of_writes hwr] at hro
  refine ⟨hw', ⟨hb', hnt'⟩, ?_, ?_⟩
  · -- the second read and the commit are generated by the strategy
    have hresp' : snapResp false (h ++ [⟨.read T o, some x⟩]) (.read T o) = some x := by
      rw [snapResp_read_ro hro, firstIdx_snoc_self (T := T) (e := ⟨.read T o, some x⟩) rfl,
        List.take_append_of_le_length firstIdx_le_length, hx]
    have hok' : OKNext (h ++ [⟨.read T o, some x⟩]) (.read T o) := by
      refine ⟨hnt', ?_, fun hnb => absurd hb' hnb⟩
      intro _ _ hi; cases hi
    have hw'' := hw'.snoc ⟨.read T o, some x⟩ hok'
    have hg'' : Gen false (h ++ [⟨.read T o, some x⟩] ++ [⟨.read T o, some x⟩]) := by
      have := hg'.snoc (.read T o); rwa [hresp'] at this
    have hnt'' := not_terminated_snoc_read (o := o) (v := x) hnt'
    have hok'' : OKNext (h ++ [⟨.read T o, some x⟩] ++ [⟨.read T o, some x⟩]) (.commit T) := by
      refine ⟨hnt'', ?_, fun hnb => absurd (hb'.mono _) hnb⟩
      intro _ _ hi; cases hi
    have hresp'' : snapResp false (h ++ [⟨.read T o, some x⟩] ++ [⟨.read T o, some x⟩])
        (.commit T) = some none := by simp [snapResp, hro]
    have hw''' := hw''.snoc ⟨.commit T, some none⟩ hok''
    have hg''' : Gen false (h ++ [⟨.read T o, some x⟩] ++ [⟨.read T o, some x⟩] ++
        [⟨.commit T, some none⟩]) := by
      have := hg''.snoc (.commit T); rwa [hresp''] at this
    have := strictSer_of_gen hw''' hg'''
    simpa [STM.CanRead] using this
  · rintro ⟨o', w⟩ ⟨ho, W', hw2, -, hbefore⟩ ⟨pos, hinj, -, hleg⟩
    simp only at ho hw2 hbefore
    subst ho hw2
    have hcT : Committed (h ++ [⟨.read T o', some x⟩] ++
        [⟨.read T o', some (some W')⟩, ⟨.commit T, some none⟩]) T := ⟨none, by simp⟩
    have h1 := (hleg T (Or.inl hcT) h o' x [⟨.read T o', some (some W')⟩, ⟨.commit T, some none⟩]
      (by simp)).2 (hnw h hw)
    have h2 := (hleg T (Or.inl hcT) _ o' (some W') [⟨.commit T, some none⟩] (by simp)).2
      (hnw _ hw')
    exact commitBefore_irrefl (hbefore W'
      (extLegal_unique (fun A B hA hB => hinj A B (Or.inl hA) (Or.inl hB)) h1 h2))

end UPGCHist

end Podc.MultiVersionSTM
