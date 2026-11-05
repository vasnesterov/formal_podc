import Podc.Computability.Distributed.NIS.Model

-- CSLib candidate: Cslib/Computability/Distributed/NIS/Views.lean
-- (staged by Papers/PODC2020/WhyExtensionBased)
/-!
# Views, causal past and restricted executions in the NIS model

Structural facts about configurations of the full-information NIS model (`Model.lean`) that are
reachable from an initial configuration by an arbitrary schedule (`Rch`, no protocol involved):

* `InPast z s`: `z` lies in the causal past of `s` (ancestors, the states read by scans, and
  recursively their pasts); `Seen a s`: some process with input `a` is in the causal past of `s`.
* shape of reachable states, views refer to performed updates (`Rch.view_write`), views of the same
  snapshot object are nested (`Rch.view_nested`), the causal past of a state of process `i` consists
  of ancestors of the current states (`Rch.past_anc`), and is active (`Reach.past_active`).
* **Restriction**: keeping, for each process, only a prefix of its steps that is closed under
  "reads-from" gives an execution in which every process ends in the corresponding ancestor of its
  final state (`exec_restrict`). Special cases: truncation to level `r` (`trunc`), and keeping the
  causal past of a set of processes (`exists_sched_restrict`).

The proofs rest on a structural invariant `RchInv` of reachable configurations (shape of the states
`Good`, views are contained in the current memory contents, views of one object are nested).
-/

namespace Cslib.NIS

open St

namespace St
variable {P X : Type}

/-- Settled states: initial or post-scan states (not between an update and the following scan). -/
def Settled : St P X → Prop
  | init _ _ => True
  | upd _ => False
  | scan _ _ => True

/-- The result of the last scan (empty for non-scan states). -/
def view : St P X → P → Option (St P X)
  | scan _ v => v
  | _ => fun _ => none

/-- `cut s d`: the ancestor of `s` of depth `d` (`s` itself if `depth s ≤ d`). -/
def cut : St P X → ℕ → St P X
  | init i x, _ => init i x
  | upd s, d => if (upd s).depth ≤ d then upd s else cut s d
  | scan s v, d => if (scan s v).depth ≤ d then scan s v else cut s d

@[simp] lemma settled_init (i : P) (x : X) : (init i x).Settled := trivial
@[simp] lemma not_settled_upd (s : St P X) : ¬ (upd s).Settled := id
@[simp] lemma settled_scan (s : St P X) v : (scan s v).Settled := trivial
@[simp] lemma view_scan (s : St P X) v : (scan s v).view = v := rfl

lemma cut_of_depth_le {s : St P X} {d : ℕ} (h : s.depth ≤ d) : s.cut d = s := by
  cases s with
  | init i x => rfl
  | upd s => simp only [cut, ite_eq_left h]
  | scan s v => simp only [cut, ite_eq_left h]

lemma cut_mem_anc : ∀ (s : St P X) (d : ℕ), s.cut d ∈ s.anc
  | init i x, d => by simp [cut, anc]
  | upd s, d => by
    simp only [cut, anc]; split_ifs
    · simp
    · exact List.mem_cons_of_mem _ (cut_mem_anc s d)
  | scan s v, d => by
    simp only [cut, anc]; split_ifs
    · simp
    · exact List.mem_cons_of_mem _ (cut_mem_anc s d)

lemma depth_cut : ∀ (s : St P X) (d : ℕ), (s.cut d).depth = min s.depth d
  | init i x, d => by simp [cut, depth]
  | upd s, d => by
    have ih := depth_cut s d
    simp only [cut]; split_ifs with h
    · simp only [depth] at h ⊢; omega
    · simp only [depth] at h ⊢; omega
  | scan s v, d => by
    have ih := depth_cut s d
    simp only [cut]; split_ifs with h
    · simp only [depth] at h ⊢; omega
    · simp only [depth] at h ⊢; omega

lemma cut_eq_of_mem_anc {s z : St P X} (hz : z ∈ s.anc) {d : ℕ} (hd : z.depth = d) : s.cut d = z := by
  have h1 := depth_le_of_mem_anc hz
  refine eq_of_mem_anc_of_depth_eq (cut_mem_anc s d) hz ?_
  rw [depth_cut]; omega

/-- Ancestors share the process identifier. -/
lemma pid_of_mem_anc : ∀ {z t : St P X}, z ∈ t.anc → z.pid = t.pid
  | _, init i x, h => by simp [anc] at h; subst h; rfl
  | _, upd t, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; rfl
    · rw [pid_of_mem_anc h]; rfl
  | _, scan t v, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; rfl
    · rw [pid_of_mem_anc h]; rfl

/-- Ancestors share the input. -/
lemma input_of_mem_anc : ∀ {z t : St P X}, z ∈ t.anc → z.input = t.input
  | _, init i x, h => by simp [anc] at h; subst h; rfl
  | _, upd t, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; rfl
    · rw [input_of_mem_anc h]; rfl
  | _, scan t v, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with h | h
    · subst h; rfl
    · rw [input_of_mem_anc h]; rfl

/-- The ancestors of a state form a chain ordered by depth. -/
lemma mem_anc_of_mem_anc_of_depth_le : ∀ {a b t : St P X}, a ∈ t.anc → b ∈ t.anc →
    a.depth ≤ b.depth → a ∈ b.anc
  | _, _, init i x, ha, hb, _ => by
    simp [anc] at ha hb; subst ha; subst hb; exact mem_anc_self _
  | _, _, upd t, ha, hb, hd => by
    simp only [anc, List.mem_cons] at ha hb
    rcases hb with rfl | hb
    · simp only [anc, List.mem_cons]; exact ha
    · rcases ha with rfl | ha
      · have := depth_le_of_mem_anc hb; simp only [depth] at hd; omega
      · exact mem_anc_of_mem_anc_of_depth_le ha hb hd
  | _, _, scan t v, ha, hb, hd => by
    simp only [anc, List.mem_cons] at ha hb
    rcases hb with rfl | hb
    · simp only [anc, List.mem_cons]; exact ha
    · rcases ha with rfl | ha
      · have := depth_le_of_mem_anc hb; simp only [depth] at hd; omega
      · exact mem_anc_of_mem_anc_of_depth_le ha hb hd

/-- An ancestor of depth `≤ d` is an ancestor of the cut at `d`. -/
lemma mem_anc_cut {a t : St P X} (ha : a ∈ t.anc) {d : ℕ} (hd : a.depth ≤ d) : a ∈ (t.cut d).anc :=
  mem_anc_of_mem_anc_of_depth_le ha (cut_mem_anc t d)
    (by rw [depth_cut]; have := depth_le_of_mem_anc ha; omega)

/-- The history of an ancestor is a prefix of the history. -/
lemma hist_prefix_of_mem_anc : ∀ {a t : St P X}, a ∈ t.anc → a.hist <+: t.hist
  | _, init i x, h => by simp [anc] at h; subst h; exact List.prefix_refl _
  | _, upd t, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.prefix_refl _
    · exact (hist_prefix_of_mem_anc h).trans (List.prefix_append _ _)
  | _, scan t v, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.prefix_refl _
    · have := hist_prefix_of_mem_anc h; exact this

/-- Entries of a prefix are entries of the longer list. -/
lemma getElem?_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {m : ℕ} {w : α}
    (hw : l₁[m]? = some w) : l₂[m]? = some w := by
  obtain ⟨t, rfl⟩ := h
  have : m < l₁.length := by
    by_contra hc; push Not at hc; rw [List.getElem?_eq_none hc] at hw; cases hw
  rw [List.getElem?_append_left this, hw]

/-- Shape of the states reachable by some schedule: updates are performed from settled states, a
scan follows an update and reads the value the process just wrote. -/
def Good : St P X → Prop
  | init _ _ => True
  | upd s => Good s ∧ s.Settled
  | scan s v => Good s ∧ ∃ s', s = upd s' ∧ v s'.pid = some s'

lemma Good.of_mem_anc : ∀ {z t : St P X}, t.Good → z ∈ t.anc → z.Good
  | _, init i x, h, hz => by simp [anc] at hz; subst hz; exact h
  | _, upd t, h, hz => by
    simp only [anc, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h
    · exact Good.of_mem_anc h.1 hz
  | _, scan t v, h, hz => by
    simp only [anc, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact h
    · exact Good.of_mem_anc h.1 hz

/-- Length of the history and depth of a good state. -/
lemma Good.counts : ∀ {t : St P X}, t.Good →
    (t.Settled → t.hist.length = t.rounds ∧ t.depth = 2 * t.rounds) ∧
    (¬ t.Settled → t.hist.length = t.rounds + 1 ∧ t.depth = 2 * t.rounds + 1)
  | init i x, _ => by simp [hist, rounds, depth]
  | upd s, h => by
    have ih := (Good.counts h.1).1 h.2
    refine ⟨fun h' => absurd h' (not_settled_upd s), fun _ => ?_⟩
    simp only [hist, rounds, depth, List.length_append, List.length_singleton]; omega
  | scan s v, h => by
    have ih := Good.counts h.1
    obtain ⟨-, s', rfl, -⟩ := h
    have ih := ih.2 (not_settled_upd s')
    refine ⟨fun _ => ?_, fun h' => absurd (settled_scan _ _) h'⟩
    simp only [hist, rounds, depth] at ih ⊢; omega

/-- The history of a good state lists the values of its updates, indexed by their rounds. -/
lemma Good.hist_getElem : ∀ {t : St P X}, t.Good → ∀ {m : ℕ} {w : St P X},
    (t.hist[m]? = some w ↔ upd w ∈ t.anc ∧ w.rounds = m)
  | init i x, _, m, w => by simp [hist, anc]
  | upd s, h, m, w => by
    have ih := Good.hist_getElem h.1 (m := m) (w := w)
    have hl := ((Good.counts h.1).1 h.2).1
    simp only [hist, anc, List.mem_cons, upd.injEq]
    constructor
    · intro hw
      by_cases hm : m < s.hist.length
      · rw [List.getElem?_append_left hm] at hw
        obtain ⟨h1, h2⟩ := ih.1 hw
        exact ⟨Or.inr h1, h2⟩
      · push Not at hm
        rw [List.getElem?_append_right hm] at hw
        have h0 : m - s.hist.length = 0 := by
          by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at hw; cases hw
        rw [h0] at hw; simp at hw; subst hw; exact ⟨Or.inl rfl, by omega⟩
    · rintro ⟨h1 | h1, rfl⟩
      · subst h1; rw [List.getElem?_append_right (by omega)]; simp [hl]
      · exact getElem?_of_prefix (List.prefix_append _ _) (ih.2 ⟨h1, rfl⟩)
  | scan s v, h, m, w => by
    have ih := Good.hist_getElem h.1 (m := m) (w := w)
    simp only [hist, anc, List.mem_cons, reduceCtorEq, false_or]
    exact ih

/-- Rounds of a good state in terms of its depth. -/
lemma Good.two_mul_rounds_le {t : St P X} (h : t.Good) :
    2 * t.rounds ≤ t.depth ∧ t.depth ≤ 2 * t.rounds + 1 := by
  by_cases hs : t.Settled
  · have := (h.counts.1 hs).2; omega
  · have := (h.counts.2 hs).2; omega

end St

variable {P X Y : Type} [DecidableEq P]

/-- `InPast z s`: `z` belongs to the causal past of `s`. -/
inductive InPast : St P X → St P X → Prop
  | refl (s : St P X) : InPast s s
  | upd {z s : St P X} : InPast z s → InPast z (upd s)
  | scanSelf {z s : St P X} {v : P → Option (St P X)} : InPast z s → InPast z (scan s v)
  | scanView {z s : St P X} {v : P → Option (St P X)} {k : P} {w : St P X} :
      v k = some w → InPast z (upd w) → InPast z (scan s v)

omit [DecidableEq P] in
lemma InPast.trans {a b c : St P X} (h1 : InPast a b) (h2 : InPast b c) : InPast a c := by
  induction h2 with
  | refl => exact h1
  | upd _ ih => exact InPast.upd ih
  | scanSelf _ ih => exact InPast.scanSelf ih
  | scanView hv _ ih => exact InPast.scanView hv ih

omit [DecidableEq P] in
lemma InPast.of_mem_anc : ∀ {z s : St P X}, z ∈ s.anc → InPast z s
  | _, St.init i x, h => by simp [anc] at h; subst h; exact InPast.refl _
  | _, St.upd s, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with rfl | h
    · exact InPast.refl _
    · exact InPast.upd (InPast.of_mem_anc h)
  | _, St.scan s v, h => by
    simp only [anc, List.mem_cons] at h
    rcases h with rfl | h
    · exact InPast.refl _
    · exact InPast.scanSelf (InPast.of_mem_anc h)

/-- `s` has seen the input value `a`: an initial state with input `a` is in its causal past. -/
def Seen (a : X) (s : St P X) : Prop := ∃ i, InPast (init i a) s

omit [DecidableEq P] in
lemma Seen.mono {a : X} {z s : St P X} (h : Seen a z) (hz : InPast z s) : Seen a s := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi.trans hz⟩

/-- Configurations reachable from an initial configuration by an arbitrary schedule. -/
def Rch (C : Config P X) : Prop := ∃ x α, C = exec (initC x) α

lemma Reach.rch {δ : Protocol P X Y} {C : Config P X} (h : Reach δ C) : Rch C := by
  obtain ⟨x, α, -, rfl⟩ := h
  exact ⟨x, α, rfl⟩

lemma Rch.step {C : Config P X} (h : Rch C) (q : P) : Rch (step C q) := by
  obtain ⟨x, α, rfl⟩ := h
  exact ⟨x, α ++ [q], by rw [exec_append]; rfl⟩

lemma Rch.exec {C : Config P X} (h : Rch C) (α : List P) : Rch (exec C α) := by
  obtain ⟨x, β, rfl⟩ := h
  exact ⟨x, β ++ α, (exec_append _ _ _).symm⟩

lemma rch_initC (x : P → X) : Rch (initC x : Config P X) := ⟨x, [], rfl⟩

/-! ### The structural invariant -/

/-- Structural invariant of configurations reachable by an arbitrary schedule. -/
structure RchInv (E : Config P X) : Prop where
  pid : ∀ j, (E j).pid = j
  good : ∀ j, (E j).Good
  view : ∀ j s v, scan (upd s) v ∈ (E j).anc → ∀ k w, v k = some w → (E k).hist[s.rounds]? = some w
  nested : ∀ j k s s' v v', scan (upd s) v ∈ (E j).anc → scan (upd s') v' ∈ (E k).anc →
    s.rounds = s'.rounds →
    (∀ i w, v i = some w → v' i = some w) ∨ (∀ i w, v' i = some w → v i = some w)

omit [DecidableEq P] in
lemma rchInv_initC (x : P → X) : RchInv (initC x : Config P X) where
  pid _ := rfl
  good _ := trivial
  view j s v h := by simp [initC, anc] at h
  nested j k s s' v v' h := by simp [initC, anc] at h

/-- Ancestors of a state after a step: old ancestors, or the new state. -/
lemma mem_anc_step {C : Config P X} {q j : P} {z : St P X} (h : z ∈ (step C q j).anc) :
    z ∈ (C j).anc ∨ (j = q ∧ z = stepState C q) := by
  by_cases hj : j = q
  · subst hj; rw [step_self, anc_stepState] at h
    rcases List.mem_cons.1 h with h | h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl h
  · rw [step_ne _ hj] at h; exact Or.inl h

/-- The invariant is preserved by steps. -/
lemma rchInv_step {C : Config P X} (hC : RchInv C) (q : P) : RchInv (step C q) := by
  have hpre : ∀ k, (C k).hist <+: (step C q k).hist := fun k =>
    St.hist_prefix_of_mem_anc (mem_anc_exec C [q] k)
  have hnew : ∀ s v, stepState C q = scan (upd s) v →
      v = fun k => (C k).hist[s.rounds]? := by
    intro s v h
    rcases stepState_cases C q with ⟨s', _, h2⟩ | ⟨_, h2⟩
    · rw [h2] at h; simp only [scan.injEq, upd.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
    · rw [h2] at h; cases h
  refine ⟨fun j => ?_, fun j => ?_, ?_, ?_⟩
  · by_cases hj : j = q
    · subst hj; simp [hC.pid]
    · rw [step_ne _ hj, hC.pid]
  · by_cases hj : j = q
    · subst hj; rw [step_self]
      rcases stepState_cases C j with ⟨s, h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        have hg := hC.good j; rw [h1] at hg
        refine ⟨hg, s, rfl, ?_⟩
        have hp : s.pid = j := by have := hC.pid j; rw [h1] at this; exact this
        show (C s.pid).hist[s.rounds]? = some s
        rw [hp, h1]
        have hl := ((St.Good.counts hg.1).1 hg.2).1
        simp only [St.hist]
        rw [List.getElem?_append_right (by omega)]; simp [hl]
      · rw [h2]
        refine ⟨hC.good j, ?_⟩
        cases hcq : C j with
        | init => trivial
        | upd s => exact absurd hcq (h1 s)
        | scan => trivial
    · rw [step_ne _ hj]; exact hC.good j
  · intro j s v hz k w hv
    rcases mem_anc_step hz with hz | ⟨rfl, hz⟩
    · exact St.getElem?_of_prefix (hpre k) (hC.view j s v hz k w hv)
    · obtain rfl := hnew s v hz.symm
      exact St.getElem?_of_prefix (hpre k) hv
  · intro j k s s' v v' hz hz' hr
    rcases mem_anc_step hz with hz | ⟨_, hz⟩ <;> rcases mem_anc_step hz' with hz' | ⟨_, hz'⟩
    · exact hC.nested j k s s' v v' hz hz' hr
    · obtain rfl := hnew s' v' hz'.symm
      left; intro i w hw; rw [← hr]; exact hC.view j s v hz i w hw
    · obtain rfl := hnew s v hz.symm
      right; intro i w hw; rw [hr]; exact hC.view k s' v' hz' i w hw
    · have := hz.trans hz'.symm
      simp only [scan.injEq] at this
      obtain ⟨_, rfl⟩ := this
      left; exact fun i w h => h

/-- The invariant is preserved by executions. -/
lemma rchInv_exec {C : Config P X} (hC : RchInv C) (α : List P) : RchInv (exec C α) := by
  induction α generalizing C with
  | nil => exact hC
  | cons q α ih => exact ih (rchInv_step hC q)

lemma Rch.inv {E : Config P X} (hE : Rch E) : RchInv E := by
  obtain ⟨x, α, rfl⟩ := hE
  exact rchInv_exec (rchInv_initC x) α

section Rch
variable {E : Config P X} (hE : Rch E)
include hE

lemma Rch.pid_anc {j : P} {z : St P X} (hz : z ∈ (E j).anc) : z.pid = j :=
  (St.pid_of_mem_anc hz).trans (hE.inv.pid j)

/-- Ancestors of reachable states are good. -/
lemma Rch.good {j : P} {z : St P X} (hz : z ∈ (E j).anc) : z.Good :=
  (hE.inv.good j).of_mem_anc hz

/-- A reachable post-scan state is `scan (upd s') v` with `s'` settled, and the process read its
own update. -/
lemma Rch.scan_shape {j : P} {s : St P X} {v : P → Option (St P X)} (hz : scan s v ∈ (E j).anc) :
    ∃ s', s = upd s' ∧ s'.Settled ∧ v j = some s' := by
  obtain ⟨hs, s', rfl, hv⟩ := hE.good hz
  have hp : (scan (upd s') v).pid = j := hE.pid_anc hz
  have hp' : s'.pid = j := hp
  exact ⟨s', rfl, hs.2, hp' ▸ hv⟩

lemma Rch.upd_settled {j : P} {s : St P X} (hz : upd s ∈ (E j).anc) : s.Settled :=
  (hE.good hz).2

/-- Depth of a reachable settled state: two steps per round. -/
lemma Rch.depth_settled {j : P} {z : St P X} (hz : z ∈ (E j).anc) (hs : z.Settled) :
    z.depth = 2 * z.rounds :=
  ((hE.good hz).counts.1 hs).2

lemma Rch.depth_upd {j : P} {s : St P X} (hz : upd s ∈ (E j).anc) :
    (upd s).depth = 2 * s.rounds + 1 :=
  ((hE.good hz).counts.2 (not_settled_upd s)).2

/-- Views refer to updates that were performed: if a scan of `S_{m+1}` (with `m = s.rounds`) read the
value `w` in the component of `k`, then `k` performed `update(w)` on `S_{m+1}`. -/
lemma Rch.view_write {j k : P} {s w : St P X} {v : P → Option (St P X)}
    (hz : scan (upd s) v ∈ (E j).anc) (hv : v k = some w) :
    upd w ∈ (E k).anc ∧ w.rounds = s.rounds ∧ w.Settled := by
  have h := hE.inv.view j s v hz k w hv
  obtain ⟨h1, h2⟩ := ((hE.inv.good k).hist_getElem).1 h
  exact ⟨h1, h2, hE.upd_settled h1⟩

/-- Two scans of the same snapshot object return nested views. -/
lemma Rch.view_nested {j k : P} {s s' : St P X} {v v' : P → Option (St P X)}
    (hz : scan (upd s) v ∈ (E j).anc) (hz' : scan (upd s') v' ∈ (E k).anc)
    (hr : s.rounds = s'.rounds) :
    (∀ i w, v i = some w → v' i = some w) ∨ (∀ i w, v' i = some w → v i = some w) :=
  hE.inv.nested j k s s' v v' hz hz' hr

/-- Generalized form of `Rch.past_anc`. -/
lemma Rch.past_anc_aux {z t : St P X} (h : InPast z t) :
    ∀ {j}, t ∈ (E j).anc → z ∈ (E z.pid).anc := by
  induction h with
  | refl => intro j ht; rw [hE.pid_anc ht]; exact ht
  | upd _ ih => intro j ht; exact ih (St.anc_subset_of_mem ht (by simp [St.anc, St.mem_anc_self]))
  | scanSelf _ ih =>
    intro j ht; exact ih (St.anc_subset_of_mem ht (by simp [St.anc, St.mem_anc_self]))
  | scanView hv _ ih =>
    intro j ht
    obtain ⟨s', rfl, -, -⟩ := hE.scan_shape ht
    exact ih (hE.view_write ht hv).1

/-- The causal past of a state of the configuration consists of ancestors of current states. -/
lemma Rch.past_anc {i : P} {z : St P X} (hz : InPast z (E i)) : z ∈ (E z.pid).anc :=
  hE.past_anc_aux hz (St.mem_anc_self _)

lemma Rch.seen_input {i : P} {a : X} (h : Seen a (E i)) : ∃ j, (E j).input = a := by
  obtain ⟨i', h⟩ := h
  exact ⟨_, (St.input_of_mem_anc (hE.past_anc h)).symm⟩

/-- Causality: the causal past of a reachable state consists of the state itself and of states of
smaller depth. -/
lemma Rch.past_depth_aux {z t : St P X} (h : InPast z t) :
    ∀ {j}, t ∈ (E j).anc → z = t ∨ z.depth < t.depth := by
  induction h with
  | refl => intro _ _; exact Or.inl rfl
  | @upd s _ ih =>
    intro j ht
    have := ih (St.anc_subset_of_mem ht (by simp [St.anc, St.mem_anc_self]))
    right; simp only [St.depth]; rcases this with rfl | h <;> omega
  | @scanSelf s v _ ih =>
    intro j ht
    have := ih (St.anc_subset_of_mem ht (by simp [St.anc, St.mem_anc_self]))
    right; simp only [St.depth]; rcases this with rfl | h <;> omega
  | @scanView s v k w hv _ ih =>
    intro j ht
    obtain ⟨s', rfl, -, -⟩ := hE.scan_shape ht
    obtain ⟨hw, hr, -⟩ := hE.view_write ht hv
    have h1 := ih hw
    have h2 := hE.depth_upd hw
    have h3 := hE.depth_settled ht trivial
    right
    simp only [St.depth, St.rounds] at h2 h3 ⊢
    rcases h1 with rfl | h1
    · simp only [St.depth] at h2 ⊢; omega
    · simp only [St.depth] at h1; omega

/-- The causal past of a state of the configuration has depth at most its depth. -/
lemma Rch.past_depth {i : P} {z : St P X} (hz : InPast z (E i)) : z.depth ≤ (E i).depth := by
  rcases hE.past_depth_aux hz (St.mem_anc_self _) with rfl | h
  · exact le_rfl
  · exact h.le

/-- Rounds along the causal past: they do not increase, and strictly decrease between distinct
settled states. -/
lemma Rch.past_rounds {j : P} {s z : St P X} (hs : s ∈ (E j).anc) (hz : InPast z s) :
    z.rounds ≤ s.rounds ∧ (z ≠ s → z.Settled → s.Settled → z.rounds < s.rounds) := by
  have hzg : z.Good := hE.good (hE.past_anc_aux hz hs)
  have hsg : s.Good := hE.good hs
  have h1 := hzg.two_mul_rounds_le
  have h2 := hsg.two_mul_rounds_le
  rcases hE.past_depth_aux hz hs with rfl | h
  · exact ⟨le_rfl, fun h => absurd rfl h⟩
  · refine ⟨by omega, fun _ hzs hss => ?_⟩
    have := (hzg.counts.1 hzs).2
    have := (hsg.counts.1 hss).2
    omega

/-- Strict causal past: strict ancestors of current states, or update states. -/
lemma Rch.past_strict {z t : St P X} (h : InPast z t) : ∀ {j}, t ∈ (E j).anc → z ≠ t →
    z.depth < (E z.pid).depth ∨ ∃ w, z = upd w := by
  induction h with
  | refl => intro _ _ h; exact absurd rfl h
  | @upd s h ih =>
    intro j ht hne
    have hs : s ∈ (E j).anc := St.anc_subset_of_mem ht (by simp [St.anc, St.mem_anc_self])
    by_cases hzs : z = s
    · subst hzs; left; rw [hE.pid_anc hs]
      have := St.depth_le_of_mem_anc ht; simp only [St.depth] at this; omega
    · exact ih hs hzs
  | @scanSelf s v h ih =>
    intro j ht hne
    have hs : s ∈ (E j).anc := St.anc_subset_of_mem ht (by simp [St.anc, St.mem_anc_self])
    by_cases hzs : z = s
    · subst hzs; left; rw [hE.pid_anc hs]
      have := St.depth_le_of_mem_anc ht; simp only [St.depth] at this; omega
    · exact ih hs hzs
  | @scanView s v k w hv h ih =>
    intro j ht hne
    obtain ⟨s', rfl, -, -⟩ := hE.scan_shape ht
    have hw := (hE.view_write ht hv).1
    by_cases hz : z = upd w
    · exact Or.inr ⟨w, hz⟩
    · exact ih hw hz

end Rch

/-- In a reachable configuration, the strict causal past of every current state is active (some
process took a step from each of those states). -/
lemma Reach.past_active {δ : Protocol P X Y} {E : Config P X} (hE : Reach δ E) {i : P}
    {z : St P X} (hz : InPast z (E i)) (hne : z ≠ E i) : decided δ z = none := by
  have hR := hE.rch
  obtain ⟨x, α, hα, rfl⟩ := hE
  rcases hR.past_strict hz (St.mem_anc_self _) hne with h | ⟨w, rfl⟩
  · exact (isSched_iff _ _).1 hα z.pid z (hR.past_anc hz) (by simp [initC, St.depth]) h
  · rfl

/-! ## Restriction -/

/-- Keep, for each process `j`, only its first `K j` steps of the schedule. -/
def restrict : (P → ℕ) → List P → List P
  | _, [] => []
  | K, q :: α => if 0 < K q then q :: restrict (Function.update K q (K q - 1)) α else restrict K α

lemma restrict_sublist (K : P → ℕ) (α : List P) : (restrict K α).Sublist α := by
  induction α generalizing K with
  | nil => exact List.Sublist.slnil
  | cons q α ih =>
    simp only [restrict]; split_ifs
    · exact (ih _).cons_cons q
    · exact (ih K).cons q

lemma restrict_append {K : P → ℕ} {β : List P} (h : ∀ j, β.count j ≤ K j) (γ : List P) :
    restrict K (β ++ γ) = β ++ restrict (fun j => K j - β.count j) γ := by
  induction β generalizing K with
  | nil => simp
  | cons q β ih =>
    have hq : 0 < K q := by have := h q; simp at this; omega
    simp only [List.cons_append, restrict, ite_eq_left hq, List.cons.injEq, true_and]
    rw [ih (fun j => ?_)]
    · congr 2; funext j
      by_cases hj : j = q
      · subst hj; simp [Function.update_self]; omega
      · simp [Function.update_of_ne hj, Ne.symm hj]
    · by_cases hj : j = q
      · subst hj; have := h j; simp [Function.update_self] at this ⊢; omega
      · have := h j; simp [Function.update_of_ne hj, Ne.symm hj] at this ⊢
        exact this

/-- Restriction of a schedule extended by one step. -/
lemma restrict_concat (K : P → ℕ) (α : List P) (q : P) :
    restrict K (α ++ [q]) = restrict K α ++ (if α.count q < K q then [q] else []) := by
  induction α generalizing K with
  | nil =>
    simp only [List.nil_append, restrict]
    split_ifs <;> simp_all
  | cons p α ih =>
    simp only [List.cons_append, restrict]
    by_cases h1 : 0 < K p
    · rw [ite_eq_left h1, ite_eq_left h1, ih, List.cons_append]
      have hc : List.count q (p :: α) < K q ↔
          List.count q α < Function.update K p (K p - 1) q := by
        by_cases hpq : q = p
        · subst hpq; simp [Function.update_self]; omega
        · simp [Function.update_of_ne hpq, Ne.symm hpq]
      by_cases h : List.count q (p :: α) < K q
      · rw [ite_eq_left h, ite_eq_left (hc.1 h)]
      · rw [ite_eq_right h, ite_eq_right (mt hc.2 h)]
    · rw [ite_eq_right h1, ite_eq_right h1, ih]
      have hc : List.count q (p :: α) < K q ↔ List.count q α < K q := by
        by_cases hpq : q = p
        · subst hpq; simp; omega
        · simp [Ne.symm hpq]
      by_cases h : List.count q (p :: α) < K q
      · rw [ite_eq_left h, ite_eq_left (hc.1 h)]
      · rw [ite_eq_right h, ite_eq_right (mt hc.2 h)]

/-- `K` is closed for `F`: every kept scan read only kept updates. -/
def Closed (F : Config P X) (K : P → ℕ) : Prop :=
  ∀ j, ∀ z ∈ ((F j).cut (K j)).anc, ∀ k w, z.view k = some w → (upd w).depth ≤ K k

omit [DecidableEq P] in
/-- Closedness passes to configurations of ancestors. -/
lemma Closed.of_anc {F F' : Config P X} {K : P → ℕ} (h : ∀ j, F' j ∈ (F j).anc)
    (hK : Closed F K) : Closed F' K := by
  intro j z hz k w hv
  refine hK j z ?_ k w hv
  refine St.anc_subset_of_mem ?_ hz
  apply St.mem_anc_of_mem_anc_of_depth_le (t := F j)
  · exact St.anc_subset_of_mem (h j) (St.cut_mem_anc _ _)
  · exact St.cut_mem_anc _ _
  · rw [St.depth_cut, St.depth_cut]; have := St.depth_le_of_mem_anc (h j); omega

/-- Cutting a state after a step below the depth of the old state. -/
lemma cut_stepState (C : Config P X) (q : P) {d : ℕ} (hd : d ≤ (C q).depth) :
    (stepState C q).cut d = (C q).cut d := by
  rcases stepState_cases C q with ⟨s, h1, h2⟩ | ⟨_, h2⟩
  · rw [h2, h1]; simp only [St.cut]; rw [ite_eq_right]
    rw [h1] at hd; simp only [St.depth] at hd ⊢; omega
  · rw [h2]; simp only [St.cut]; rw [ite_eq_right]; simp only [St.depth]; omega

/-- **Restriction lemma.** -/
theorem exec_restrict {x : P → X} {α : List P} {K : P → ℕ} (hK : Closed (exec (initC x) α) K) :
    exec (initC x) (restrict K α) = fun j => (exec (initC x) α j).cut (K j) := by
  induction α using List.reverseRecOn with
  | nil => funext j; simp [restrict, initC, St.cut]
  | append_singleton α q ih =>
    have hR : Rch (exec (initC x) α) := ⟨x, α, rfl⟩
    have hF : exec (initC x) (α ++ [q]) = step (exec (initC x) α) q := exec_append _ _ _
    rw [hF] at hK ⊢
    have hK' : Closed (exec (initC x) α) K := hK.of_anc (fun j => mem_anc_exec _ [q] j)
    rw [restrict_concat, exec_append, ih hK']
    have hdq : (exec (initC x) α q).depth = α.count q := by
      rw [depth_exec]; simp [initC, St.depth]
    generalize exec (initC x) α = F at hR hK hK' hdq ⊢
    have hgood := hR.inv.good
    split_ifs with hc
    · show step (fun j => (F j).cut (K j)) q = _
      funext j
      by_cases hj : j = q
      · subst hj
        rw [step_self, step_self, St.cut_of_depth_le (by rw [depth_stepState]; omega)]
        have hRq : (F j).cut (K j) = F j := St.cut_of_depth_le (by omega)
        rcases stepState_cases F j with ⟨s, h1, h2⟩ | ⟨h1, h2⟩
        · have hRs : (fun j => (F j).cut (K j)) j = upd s := by simp only; rw [hRq, h1]
          rcases stepState_cases (fun j => (F j).cut (K j)) j with ⟨s', h1', h2'⟩ | ⟨h1', _⟩
          · have hss : s' = s := (St.upd.inj (hRs.symm.trans h1')).symm
            rw [h2', h2, hss]
            congr 1; funext k
            have hcl : ∀ w, (F k).hist[s.rounds]? = some w → (upd w).depth ≤ K k := by
              intro w hw
              refine hK j (stepState F j) ?_ k w ?_
              · rw [step_self, St.cut_of_depth_le (by rw [depth_stepState]; omega)]
                exact St.mem_anc_self _
              · rw [h2]; exact hw
            have hpre := St.hist_prefix_of_mem_anc (St.cut_mem_anc (F k) (K k))
            show ((F k).cut (K k)).hist[s.rounds]? = (F k).hist[s.rounds]?
            cases hFk : (F k).hist[s.rounds]? with
            | none =>
              cases hRk : ((F k).cut (K k)).hist[s.rounds]? with
              | none => rfl
              | some w' => have := St.getElem?_of_prefix hpre hRk; rw [hFk] at this; cases this
            | some w =>
              obtain ⟨hw1, hw2⟩ := (hgood k).hist_getElem.1 hFk
              have hgc : ((F k).cut (K k)).Good := (hgood k).of_mem_anc (St.cut_mem_anc _ _)
              exact hgc.hist_getElem.2 ⟨St.mem_anc_cut hw1 (hcl w hFk), hw2⟩
          · exact absurd hRs (h1' s)
        · rcases stepState_cases (fun j => (F j).cut (K j)) j with ⟨s', h1', _⟩ | ⟨_, h2'⟩
          · rw [hRq] at h1'; exact absurd h1' (h1 s')
          · rw [h2', h2, hRq]
      · rw [step_ne _ hj, step_ne _ hj]
    · funext j
      by_cases hj : j = q
      · subst hj; simp only [exec_nil]; rw [step_self, cut_stepState F j (by omega)]
      · simp only [exec_nil]; rw [step_ne _ hj]

/-- Truncation of a configuration to level `r`: every process is put back to its state after `r`
rounds (processes that did fewer steps keep their state). -/
def trunc (r : ℕ) (F : Config P X) : Config P X := fun j => (F j).cut (2 * r)

/-- Truncation at level `r` is closed: a scan of round `≤ r` reads updates of round `< r`. -/
lemma Rch.closed_trunc {F : Config P X} (h : Rch F) (r : ℕ) : Closed F (fun _ => 2 * r) := by
  intro j z hz k w hv
  have hz' : z ∈ (F j).anc := St.anc_subset_of_mem (St.cut_mem_anc _ _) hz
  have hd : z.depth ≤ 2 * r := by
    have := St.depth_le_of_mem_anc hz; rw [St.depth_cut] at this; simp only at this; omega
  cases z with
  | init => simp [St.view] at hv
  | upd => simp [St.view] at hv
  | scan s v =>
    simp only [St.view_scan] at hv
    obtain ⟨s', rfl, -, -⟩ := h.scan_shape hz'
    obtain ⟨hw, hr, -⟩ := h.view_write hz' hv
    have h1 := h.depth_settled hz' trivial
    have h2 := h.depth_upd hw
    simp only [St.depth, St.rounds] at h1 h2 hd ⊢
    omega

lemma Rch.trunc {F : Config P X} (h : Rch F) (r : ℕ) : Rch (Cslib.NIS.trunc r F) := by
  have hc := h.closed_trunc r
  obtain ⟨x, α, rfl⟩ := h
  exact ⟨x, restrict _ α, (exec_restrict hc).symm⟩

/-- The truncation is reachable already under any protocol that agrees on the states of rounds
`< r`. -/
lemma Reach.trunc_congr {δ δ' : Protocol P X Y} {F : Config P X} (h : Reach δ F) (r : ℕ)
    (hδ : ∀ s : St P X, s.rounds < r → decided δ s = decided δ' s) : Reach δ' (Cslib.NIS.trunc r F) := by
  obtain ⟨x, α, hα, rfl⟩ := h
  have hR : Rch (exec (initC x) α) := ⟨x, α, rfl⟩
  have hres := exec_restrict (hR.closed_trunc r)
  refine ⟨x, restrict (fun _ => 2 * r) α, ?_, hres.symm⟩
  rw [isSched_iff, hres]
  intro q s hs _ h2
  simp only at hs h2
  have hs' : s ∈ (exec (initC x) α q).anc := St.anc_subset_of_mem (St.cut_mem_anc _ _) hs
  have hdc := St.depth_cut (exec (initC x) α q) (2 * r)
  have hd : decided δ s = none :=
    (isSched_iff _ _).1 hα q s hs' (by simp [initC, St.depth]) (by omega)
  have hg := (hR.good hs').two_mul_rounds_le
  rw [← hδ s (by omega)]; exact hd

lemma Reach.trunc {δ : Protocol P X Y} {F : Config P X} (h : Reach δ F) (r : ℕ) :
    Reach δ (Cslib.NIS.trunc r F) :=
  h.trunc_congr r (fun _ _ => rfl)

/-- **Keeping a causal past.** Let `C = C₀ β` and `F = C μ`. Some subschedule `μ'` of `μ` (not
depending on any protocol) leads from `C` to a configuration in which the processes of `A` are in
the same states as in `F`, and every other process is either in its state in `C` or in a state of
the causal past of the state in `F` of some process of `A`. It is a `δ'`-schedule for every
protocol `δ'` for which the strict causal pasts of the states in `F` of the processes in `A` are
active. -/
theorem exists_sched_restrict {x : P → X} {β μ : List P} (A : Set P) :
    ∃ μ', μ'.Sublist μ ∧
      (∀ i ∈ A, exec (exec (initC x) β) μ' i = exec (initC x) (β ++ μ) i) ∧
      (∀ j, exec (exec (initC x) β) μ' j = exec (initC x) β j ∨
        ∃ i ∈ A, InPast (exec (exec (initC x) β) μ' j) (exec (initC x) (β ++ μ) i)) ∧
      ∀ {Y : Type} (δ' : Protocol P X Y), (∀ i ∈ A, ∀ z, InPast z (exec (initC x) (β ++ μ) i) →
        z ≠ exec (initC x) (β ++ μ) i → decided δ' z = none) → IsSched δ' (exec (initC x) β) μ' := by
  classical
  obtain ⟨C, hC⟩ : ∃ C, exec (initC x) β = C := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, exec (initC x) (β ++ μ) = F := ⟨_, rfl⟩
  have hCF : F = Cslib.NIS.exec C μ := by rw [← hF, ← hC, exec_append]
  have hRC : Rch C := ⟨x, β, hC.symm⟩
  have hRF : Rch F := ⟨x, β ++ μ, hF.symm⟩
  have hCa : ∀ j, C j ∈ (F j).anc := fun j => by rw [hCF]; exact mem_anc_exec _ _ _
  have hCd : ∀ j, (C j).depth = β.count j := fun j => by
    rw [← hC, depth_exec]; simp [initC, St.depth]
  have hCle : ∀ j, (C j).depth ≤ (F j).depth := fun j => St.depth_le_of_mem_anc (hCa j)
  let K : P → ℕ := fun j => Nat.findGreatest
    (fun d => d ≤ (C j).depth ∨ ∃ i ∈ A, InPast ((F j).cut d) (F i)) (F j).depth
  have hKQ : ∀ j, K j ≤ (C j).depth ∨ ∃ i ∈ A, InPast ((F j).cut (K j)) (F i) := fun j =>
    Nat.findGreatest_spec (P := fun d => d ≤ (C j).depth ∨ ∃ i ∈ A, InPast ((F j).cut d) (F i))
      (hCle j) (Or.inl le_rfl)
  have hKle : ∀ j, K j ≤ (F j).depth := fun j => Nat.findGreatest_le _
  have hKge : ∀ j, (C j).depth ≤ K j := fun j => Nat.le_findGreatest (hCle j) (Or.inl le_rfl)
  have hKA : ∀ i ∈ A, K i = (F i).depth := fun i hi => le_antisymm (hKle i)
    (Nat.le_findGreatest le_rfl
      (Or.inr ⟨i, hi, by rw [St.cut_of_depth_le le_rfl]; exact InPast.refl _⟩))
  have hcutC : ∀ j, K j ≤ (C j).depth → (F j).cut (K j) = C j := fun j hK =>
    St.cut_eq_of_mem_anc (hCa j) (le_antisymm (hKge j) hK)
  have hclosed : Closed F K := by
    intro j z hz k w hv
    have hz' : z ∈ (F j).anc := St.anc_subset_of_mem (St.cut_mem_anc _ _) hz
    cases z with
    | init => simp [St.view] at hv
    | upd => simp [St.view] at hv
    | scan s v =>
      simp only [St.view_scan] at hv
      obtain ⟨s', rfl, -, -⟩ := hRF.scan_shape hz'
      obtain ⟨hw, -, -⟩ := hRF.view_write hz' hv
      rcases hKQ j with hK | ⟨i, hi, hpast⟩
      · rw [hcutC j hK] at hz
        obtain ⟨hw', -, -⟩ := hRC.view_write hz hv
        exact (St.depth_le_of_mem_anc hw').trans (hKge k)
      · apply Nat.le_findGreatest (St.depth_le_of_mem_anc hw)
        refine Or.inr ⟨i, hi, ?_⟩
        rw [St.cut_eq_of_mem_anc hw rfl]
        exact (InPast.scanView hv (InPast.refl _)).trans ((InPast.of_mem_anc hz).trans hpast)
  have hcount : ∀ j, β.count j ≤ K j := fun j => (hCd j) ▸ hKge j
  have hres := exec_restrict (x := x) (α := β ++ μ) (K := K) (by rw [hF]; exact hclosed)
  rw [restrict_append hcount, exec_append, hC, hF] at hres
  rw [hF, hC]
  refine ⟨restrict (fun j => K j - β.count j) μ, restrict_sublist _ _, ?_, ?_, ?_⟩
  · intro i hi; rw [hres]; simp only; rw [hKA i hi, St.cut_of_depth_le le_rfl]
  · intro j; rw [hres]; simp only
    rcases hKQ j with hK | h
    · exact Or.inl (hcutC j hK)
    · exact Or.inr h
  · intro Y δ' hA
    rw [isSched_iff, hres]
    intro q s hs h1 h2
    simp only at hs h2
    have hdc := St.depth_cut (F q) (K q)
    rcases hKQ q with hK | ⟨i, hi, hpast⟩
    · have := hKge q; omega
    · apply hA i hi s ((InPast.of_mem_anc hs).trans hpast)
      rintro rfl
      have := hRF.past_depth hpast
      omega

/-- Occurrence version of `exists_sched_restrict`. -/
theorem Rch.exists_reach {δ' : Protocol P X Y} {E : Config P X} (hE : Rch E) (A : Set P)
    (hA : ∀ i ∈ A, ∀ z, InPast z (E i) → z ≠ E i → decided δ' z = none) :
    ∃ E', Reach δ' E' ∧ ∀ i ∈ A, E' i = E i := by
  obtain ⟨x, α, rfl⟩ := hE
  obtain ⟨μ', -, hA', -, hμ'⟩ := exists_sched_restrict (x := x) (β := []) (μ := α) A
  refine ⟨Cslib.NIS.exec (initC x) μ', ⟨x, μ', ?_, rfl⟩, by simpa using hA'⟩
  simpa using hμ' δ' (by simpa using hA)

lemma IsSched.mono {δ δ' : Protocol P X Y} (h : ∀ s, decided δ' s = none → decided δ s = none)
    {C : Config P X} {α : List P} (hα : IsSched δ' C α) : IsSched δ C α := by
  induction α generalizing C with
  | nil => trivial
  | cons q α ih => exact ⟨h _ hα.1, ih hα.2⟩

lemma Reach.mono {δ δ' : Protocol P X Y} (h : ∀ s, decided δ' s = none → decided δ s = none)
    {C : Config P X} (hC : Reach δ' C) : Reach δ C := by
  obtain ⟨x, α, hα, rfl⟩ := hC
  exact ⟨x, α, IsSched.mono h hα, rfl⟩

end Cslib.NIS
