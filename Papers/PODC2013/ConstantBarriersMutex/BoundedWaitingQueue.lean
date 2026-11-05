import Papers.PODC2013.ConstantBarriersMutex.BoundedWaitingBasic

/-!
# Bounded waiting, part 2: the promotion order is FIFO

The *promotion order* `Q s` of a configuration lists the processes that will enter the critical
section through a hand-off, in the order in which they will enter: first the process the lock is
being handed to (if any: `hd s`), then the logical contents of `promQ` (`(lv s).promQ`).

`Q_enter` and `Q_noenter` show that a step either leaves `Q` unchanged, appends a fresh process
to it (statement 37), or removes its head, which is the process that enters the critical section
at that step (or `Q` is empty and the entering process wins a CAS). Consequently (`fifo`), once a
process `r` is in `Q`, any other process enters the critical section at most once before `r` does
("every process appears at most once in the promotion queue", proof of Lemma 8 of the paper).
-/

namespace Podc.ConstantBarriersMutex.BW

open Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- `g` at program counter `c` is handing the lock to `x` (statements 46–48, or 50 with the
hand-off writes not yet performed). -/
def HTpc (c : PC h) (x : Proc h) (ne : Prop) : Prop :=
  c = .x46 x ∨ c = .x47 x ∨ c = .x48 x ∨ (c = .x50 (some x) ∧ ne)

/-- `x` is the target of a lock hand-off that `x` has not yet used to enter. -/
def IsHT (s : Cfg h) (x : Proc h) : Prop :=
  (∃ g, HTpc (s.pc g) x (s.buf g ≠ [])) ∨ (s.mem.lock = some x ∧ (s.pc x).Entry)

lemma htpc_facts {s : Cfg h} (hI : Inv s) {g x : Proc h} (hg : HTpc (s.pc g) x (s.buf g ≠ [])) :
    (s.mem.lock = some g ∨ s.mem.lock = some x) ∧ s.InCSX g ∧ (s.pc x).Entry ∧
      x ∉ (lv s).promQ ∧ x ≠ g := by
  have hL := hI.loc g
  have hH := hI.hc g
  rcases hg with hpc | hpc | hpc | ⟨hpc, hne⟩ <;> simp only [LI, HC, hpc] at hL hH
  · exact ⟨Or.inl hL.1, Or.inr (Or.inl (by simp [hpc, PC.Exit])), hH.1, hH.2.2, hL.2.2⟩
  · exact ⟨Or.inl hL.1, Or.inr (Or.inl (by simp [hpc, PC.Exit])), hH.1, hH.2.2.1, hL.2.2⟩
  · refine ⟨?_, Or.inr (Or.inl (by simp [hpc, PC.Exit])), hH.1, hH.2.2.1, hL.1⟩
    rcases hL.2 with ⟨B, -, -, hl⟩ | ⟨-, hl, -⟩
    · exact Or.inl hl
    · exact Or.inr hl
  · obtain ⟨hE, -, hq, -⟩ := hH hne
    refine ⟨?_, Or.inr (Or.inr ⟨⟨_, hpc⟩, hne⟩), hE, hq, hL.1⟩
    rcases hL.2 with ⟨B, -, -, hl⟩ | ⟨-, hl, -⟩ | ⟨hb, -⟩
    · exact Or.inl hl
    · exact Or.inr hl
    · exact absurd hb hne

lemma IsHT.entry {s : Cfg h} (hI : Inv s) {x : Proc h} (hx : IsHT s x) : (s.pc x).Entry := by
  rcases hx with ⟨g, hg⟩ | ⟨-, hE⟩
  · exact (htpc_facts hI hg).2.2.1
  · exact hE

lemma IsHT.not_mem {s : Cfg h} (hI : Inv s) {x : Proc h} (hx : IsHT s x) : x ∉ (lv s).promQ := by
  rcases hx with ⟨g, hg⟩ | ⟨hl, -⟩
  · exact (htpc_facts hI hg).2.2.2.1
  · intro hm; exact (hI.pq x hm).2.2 hl

lemma entry_not_incsx {s : Cfg h} {x : Proc h} (hE : (s.pc x).Entry) : ¬ s.InCSX x := by
  unfold Cfg.InCSX
  cases hpc : s.pc x <;> simp_all [PC.Entry, PC.Exit]

lemma IsHT.unique {s : Cfg h} (hI : Inv s) {x y : Proc h} (hx : IsHT s x) (hy : IsHT s y) :
    x = y := by
  have key : ∀ {x y g}, HTpc (s.pc g) x (s.buf g ≠ []) → s.mem.lock = some y →
      (s.pc y).Entry → x = y := by
    intro x y g hg hl hE
    obtain ⟨hl' | hl', hcs, -⟩ := htpc_facts hI hg
    · rw [hl] at hl'; cases hl'; exact absurd hcs (entry_not_incsx hE)
    · rw [hl] at hl'; cases hl'; rfl
  rcases hx with ⟨g, hg⟩ | ⟨hl, hE⟩ <;> rcases hy with ⟨g', hg'⟩ | ⟨hl', hE'⟩
  · have := hI.uniq g g' (htpc_facts hI hg).2.1 (htpc_facts hI hg').2.1
    subst this
    rcases hg with h1 | h1 | h1 | ⟨h1, -⟩ <;> rcases hg' with h2 | h2 | h2 | ⟨h2, -⟩ <;>
      rw [h1] at h2 <;> simp at h2 <;> exact h2
  · exact key hg hl' hE'
  · exact (key hg' hl hE).symm
  · rw [hl] at hl'; cases hl'; rfl

open Classical in
/-- The process the lock is being handed to, as a list with at most one element. -/
noncomputable def hd (s : Cfg h) : List (Proc h) :=
  if hx : ∃ x, IsHT s x then [hx.choose] else []

/-- The promotion order. -/
noncomputable def Q (s : Cfg h) : List (Proc h) := hd s ++ (lv s).promQ

lemma hd_of {s : Cfg h} (hI : Inv s) {x : Proc h} (hx : IsHT s x) : hd s = [x] := by
  have hex : ∃ x, IsHT s x := ⟨x, hx⟩
  simp only [hd, hex, dite_true, List.cons.injEq, and_true]
  exact IsHT.unique hI hex.choose_spec hx

lemma hd_of_not {s : Cfg h} (hx : ∀ x, ¬ IsHT s x) : hd s = [] := by
  simp [hd, hx]

lemma mem_hd {s : Cfg h} (hI : Inv s) {x : Proc h} : x ∈ hd s ↔ IsHT s x := by
  by_cases hex : ∃ x, IsHT s x
  · obtain ⟨y, hy⟩ := hex
    rw [hd_of hI hy, List.mem_singleton]
    exact ⟨fun h => h ▸ hy, fun h => IsHT.unique hI h hy⟩
  · push Not at hex; rw [hd_of_not hex]; simpa using hex _

lemma hd_congr {s s' : Cfg h} (hI : Inv s) (hI' : Inv s') (hx : ∀ x, IsHT s' x ↔ IsHT s x) :
    hd s' = hd s := by
  by_cases hex : ∃ x, IsHT s x
  · obtain ⟨y, hy⟩ := hex
    rw [hd_of hI hy, hd_of hI' ((hx y).2 hy)]
  · push Not at hex
    rw [hd_of_not hex, hd_of_not (fun x h => hex x ((hx x).1 h))]

lemma mem_Q {s : Cfg h} (hI : Inv s) {x : Proc h} : x ∈ Q s ↔ IsHT s x ∨ x ∈ (lv s).promQ := by
  simp [Q, List.mem_append, mem_hd hI]

lemma Q_entry {s : Cfg h} (hI : Inv s) {x : Proc h} (hx : x ∈ Q s) : (s.pc x).Entry := by
  rcases (mem_Q hI).1 hx with hx | hx
  · exact hx.entry hI
  · exact (hI.pq x hx).1

lemma Q_nodup {s : Cfg h} (hI : Inv s) : (Q s).Nodup := by
  unfold Q
  rw [List.nodup_append]
  refine ⟨?_, hI.nodup, ?_⟩
  · by_cases hex : ∃ x, IsHT s x
    · obtain ⟨y, hy⟩ := hex; rw [hd_of hI hy]; simp
    · push Not at hex; rw [hd_of_not hex]; simp
  · intro a ha b hb hab
    subst hab
    exact ((mem_hd hI).1 ha).not_mem hI hb


/-! ### The logical promotion queue under single operations -/

lemma lv_goto (s : Cfg h) (g : Proc h) (c : PC h) : lv (s.goto g c) = lv s := rfl

lemma lv_owner {s : Cfg h} {g : Proc h} (hl : s.mem.lock = some g) : lv s = s.view g := by
  simp [lv, hl, Cfg.view]

lemma lv_issue_promQ (s : Cfg h) (g : Proc h) {w : W h} (c : PC h) (hw : w.isPromQ = false) :
    (lv (s.issue g w c)).promQ = (lv s).promQ := by
  unfold lv
  simp only [issue_mem]
  split
  · rename_i o _
    by_cases ho : o = g
    · subst ho
      simp only [issue_buf, Function.update_self, Mem.view_append, Mem.view_cons, Mem.view_nil,
        write_promQ]
      cases w <;> simp_all [W.isPromQ]
    · simp [Function.update_of_ne ho]
  · rfl

lemma lv_issue_owner {s : Cfg h} {g : Proc h} (w : W h) (c : PC h) (hl : s.mem.lock = some g) :
    lv (s.issue g w c) = (lv s).write w := by
  simp [lv, hl, Mem.view_append]

lemma view_promQ_congr' {m₁ m₂ : Mem h} {b : List (W h)} (he : m₁.promQ = m₂.promQ) :
    (m₁.view b).promQ = (m₂.view b).promQ := by
  induction b generalizing m₁ m₂ with
  | nil => exact he
  | cons w b ih =>
    simp only [Mem.view_cons]
    apply ih
    simp only [write_promQ]; split <;> simp [he]

lemma IsHT_frame {s s' : Cfg h} {g : Proc h} (hlock : s'.mem.lock = s.mem.lock)
    (hpc : ∀ y, y ≠ g → s'.pc y = s.pc y) (hbuf : ∀ y, y ≠ g → s'.buf y = s.buf y)
    (hHT : ∀ x, HTpc (s'.pc g) x (s'.buf g ≠ []) ↔ HTpc (s.pc g) x (s.buf g ≠ []))
    (hent : s.mem.lock = some g → ((s'.pc g).Entry ↔ (s.pc g).Entry)) (x : Proc h) :
    IsHT s' x ↔ IsHT s x := by
  unfold IsHT
  rw [hlock]
  constructor
  · rintro (⟨g', hg'⟩ | ⟨hl, hE⟩)
    · by_cases hgg : g' = g
      · subst hgg; exact Or.inl ⟨g', (hHT x).1 hg'⟩
      · rw [hpc g' hgg, hbuf g' hgg] at hg'; exact Or.inl ⟨g', hg'⟩
    · by_cases hxg : x = g
      · subst hxg; exact Or.inr ⟨hl, (hent hl).1 hE⟩
      · rw [hpc x hxg] at hE; exact Or.inr ⟨hl, hE⟩
  · rintro (⟨g', hg'⟩ | ⟨hl, hE⟩)
    · by_cases hgg : g' = g
      · subst hgg; exact Or.inl ⟨g', (hHT x).2 hg'⟩
      · rw [← hpc g' hgg, ← hbuf g' hgg] at hg'; exact Or.inl ⟨g', hg'⟩
    · by_cases hxg : x = g
      · subst hxg; exact Or.inr ⟨hl, (hent hl).2 hE⟩
      · rw [← hpc x hxg] at hE; exact Or.inr ⟨hl, hE⟩

lemma Q_eq_of {s s' : Cfg h} (hI : Inv s) (hI' : Inv s') {g : Proc h}
    (hlock : s'.mem.lock = s.mem.lock)
    (hpc : ∀ y, y ≠ g → s'.pc y = s.pc y) (hbuf : ∀ y, y ≠ g → s'.buf y = s.buf y)
    (hHT : ∀ x, HTpc (s'.pc g) x (s'.buf g ≠ []) ↔ HTpc (s.pc g) x (s.buf g ≠ []))
    (hent : s.mem.lock = some g → ((s'.pc g).Entry ↔ (s.pc g).Entry))
    (hq : (lv s').promQ = (lv s).promQ) : Q s' = Q s := by
  unfold Q
  rw [hd_congr hI hI' (IsHT_frame hlock hpc hbuf hHT hent), hq]

lemma IsHT_iff_of {s s' : Cfg h} (hI : Inv s) (hI' : Inv s') {x₀ : Proc h} (h1 : IsHT s x₀)
    (h2 : IsHT s' x₀) (x : Proc h) : IsHT s' x ↔ IsHT s x :=
  ⟨fun h => (IsHT.unique hI' h2 h) ▸ h1, fun h => (IsHT.unique hI h1 h) ▸ h2⟩


/-! ### Flushes do not change the promotion order -/

lemma exitType_not_lock {g : Proc h} {o : Option (Proc h)} : ¬ ExitType g (W.lock o) := by
  rintro (h1 | h1 | h1 | ⟨r, b, h1⟩) <;> simp_all [W.isExits, W.isPromQ]

/-- Behind a buffered write to `lock` there is at most `signal[nx] ← true`. -/
lemma tail_of_head_lock {s : Cfg h} (hI : Inv s) {g : Proc h} {o : Option (Proc h)}
    {b : List (W h)} (hb : s.buf g = W.lock o :: b) :
    b = [] ∨ ∃ nx, o = some nx ∧ b = [.signal nx true] ∧ s.pc g = .x50 (some nx) := by
  have hL := hI.loc g
  have hB : ∀ {B L : List (W h)}, (∀ w ∈ B, ExitType g w) → B ++ L = W.lock o :: b →
      L = W.lock o :: b := by
    intro B L hB he
    cases B with
    | nil => simpa using he
    | cons w B =>
      simp only [List.cons_append, List.cons.injEq] at he
      exact absurd (he.1 ▸ hB w (by simp)) exitType_not_lock
  obtain ⟨-, hp⟩ := buf_lock hI (hb ▸ List.mem_cons_self ..)
  rcases hp with hp | ⟨nx, rfl, hp⟩
  · cases o with
    | none =>
      simp only [LI, hp] at hL
      rcases hL with ⟨B, hb', hX, -⟩ | ⟨hb', -⟩
      · rw [hb'] at hb; have := hB hX.1 hb; simp at this; exact Or.inl this
      · rw [hb'] at hb; cases hb
    | some nx =>
      simp only [LI, hp] at hL
      rcases hL.2 with ⟨B, hb', hX, -⟩ | ⟨hb', -⟩ | ⟨hb', -⟩
      · rw [hb'] at hb; have := hB hX.1 hb; simp at this
        exact Or.inr ⟨nx, rfl, this.symm, hp⟩
      · rw [hb'] at hb; simp at hb
      · rw [hb'] at hb; cases hb
  · simp only [LI, hp] at hL
    rcases hL.2 with ⟨B, hb', hX, -⟩ | ⟨hb', -⟩
    · rw [hb'] at hb; have := hB hX.1 hb; simp at this; exact Or.inl this
    · rw [hb'] at hb; cases hb

lemma lock_target {s : Cfg h} (hI : Inv s) {g nx : Proc h} (hw : W.lock (some nx) ∈ s.buf g) :
    nx ≠ g ∧ (s.pc nx).Entry := by
  obtain ⟨-, hp⟩ := buf_lock hI hw
  have : HTpc (s.pc g) nx (s.buf g ≠ []) := by
    rcases hp with hp | ⟨nx', h1, hp⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hp, List.ne_nil_of_mem hw⟩))
    · cases h1; exact Or.inr (Or.inr (Or.inl hp))
  have := htpc_facts hI this
  exact ⟨this.2.2.2.2, this.2.2.1⟩

lemma entry_no_promQ {s : Cfg h} (hI : Inv s) {g : Proc h} (hE : (s.pc g).Entry) :
    ∀ w ∈ s.buf g, w.isPromQ = false := by
  intro w hw
  rcases mem_doorList.1 (buf_entry hI hE hw) with rfl | rfl | ⟨l, -, rfl⟩ <;> rfl

lemma lv_flush_promQ {s : Cfg h} (hI : Inv s) {g : Proc h} {w : W h} {b : List (W h)}
    (hb : s.buf g = w :: b) : (lv (s.flush g)).promQ = (lv s).promQ := by
  have hw : w ∈ s.buf g := hb ▸ List.mem_cons_self ..
  rw [flush_of_cons s g hb]
  unfold lv
  simp only
  by_cases hwl : ∃ o, w = .lock o
  · obtain ⟨o, rfl⟩ := hwl
    obtain ⟨hl, -⟩ := buf_lock hI hw
    have hq : (s.mem.view (s.buf g)).promQ = s.mem.promQ := by
      rw [hb]
      rcases tail_of_head_lock hI hb with rfl | ⟨nx, -, rfl, -⟩ <;> simp
    rw [hl]; simp only [write_lock, hq]
    cases o with
    | none => simp
    | some nx =>
      obtain ⟨hng, hE⟩ := lock_target hI hw
      simp only
      rw [Function.update_of_ne hng, view_promQ_of (entry_no_promQ hI hE)]
      simp
  · have hwl' : (s.mem.write w).lock = s.mem.lock := by
      cases w <;> simp_all
    rw [hwl']
    rcases hlk : s.mem.lock with _ | o
    · simp only
      have : w.isPromQ = false := by
        cases hq : w.isPromQ
        · rfl
        · have := buf_promQ hI hw hq; rw [hlk] at this; cases this
      simp only [write_promQ]; cases w <;> simp_all [W.isPromQ]
    · simp only
      by_cases ho : o = g
      · subst ho; simp [hb]
      · rw [Function.update_of_ne ho]
        apply view_promQ_congr'
        have : w.isPromQ = false := by
          cases hq : w.isPromQ
          · rfl
          · have := buf_promQ hI hw hq; rw [hlk] at this; cases this; exact absurd rfl ho
        simp only [write_promQ]; cases w <;> simp_all [W.isPromQ]


lemma hd_flush {s : Cfg h} (hI : Inv s) (hI' : Inv (s.flush g)) {w : W h} {b : List (W h)}
    (hb : s.buf g = w :: b) : hd (s.flush g) = hd s := by
  have hw : w ∈ s.buf g := hb ▸ List.mem_cons_self ..
  have hs' := flush_of_cons s g hb
  have hpc' : (s.flush g).pc = s.pc := flush_pc s g
  apply hd_congr hI hI'
  by_cases hwl : ∃ o, w = .lock o
  · obtain ⟨o, rfl⟩ := hwl
    obtain ⟨hl, hp⟩ := buf_lock hI hw
    rcases hp with hp | ⟨nx, rfl, hp⟩
    · cases o with
      | none =>
        -- nobody is a hand-off target before or after
        have hn : ∀ {t : Cfg h}, Inv t → t.pc g = .x50 none → (t.mem.lock = some g ∨
            t.mem.lock = none) → (t.mem.lock = some g → t.InCSX g) → ∀ x, ¬ IsHT t x := by
          intro t hIt htp htl hcs x hx
          rcases hx with ⟨g', hg'⟩ | ⟨hl', hE⟩
          · obtain ⟨hl'' | hl'', hcs', hE', -, hne⟩ := htpc_facts hIt hg'
            · rcases htl with htl | htl <;> rw [htl] at hl'' <;> cases hl''
              rw [htp] at hg'; rcases hg' with h1 | h1 | h1 | ⟨h1, -⟩ <;> cases h1
            · rcases htl with htl | htl <;> rw [htl] at hl'' <;> cases hl''
              rw [htp] at hE'; simp [PC.Entry] at hE'
          · rcases htl with htl | htl <;> rw [htl] at hl' <;> cases hl'
            rw [htp] at hE; simp [PC.Entry] at hE
        intro x
        constructor
        · intro hx; exfalso
          refine hn hI' (by rw [hpc']; exact hp) (Or.inr (by rw [hs']; simp)) ?_ x hx
          intro h1; rw [hs'] at h1; simp at h1
        · intro hx; exfalso
          refine hn hI hp (Or.inl hl) (fun _ => ?_) x hx
          exact Or.inr (Or.inr ⟨⟨_, hp⟩, List.ne_nil_of_mem hw⟩)
      | some nx =>
        have h1 : IsHT s nx := Or.inl ⟨g, Or.inr (Or.inr (Or.inr ⟨hp, List.ne_nil_of_mem hw⟩))⟩
        have hE : (s.pc nx).Entry := h1.entry hI
        apply IsHT_iff_of hI hI' h1
        by_cases hbn : b = []
        · refine Or.inr ⟨by rw [hs']; simp, by rw [hpc']; exact hE⟩
        · refine Or.inl ⟨g, Or.inr (Or.inr (Or.inr ⟨by rw [hpc']; exact hp, ?_⟩))⟩
          rw [hs']; simpa using hbn
    · have h1 : IsHT s nx := Or.inl ⟨g, Or.inr (Or.inr (Or.inl hp))⟩
      apply IsHT_iff_of hI hI' h1
      exact Or.inl ⟨g, Or.inr (Or.inr (Or.inl (by rw [hpc']; exact hp)))⟩
  · have hwl' : (s.flush g).mem.lock = s.mem.lock := by
      rw [hs']; cases w <;> simp_all
    by_cases hsp : ∃ x, s.pc g = .x50 (some x) ∧ b = []
    · obtain ⟨x, hp, rfl⟩ := hsp
      have h1 : IsHT s x := Or.inl ⟨g, Or.inr (Or.inr (Or.inr ⟨hp, by simp [hb]⟩))⟩
      apply IsHT_iff_of hI hI' h1
      have hL := hI.loc g
      simp only [LI, hp] at hL
      rcases hL.2 with ⟨B, hb', -, -⟩ | ⟨hb', hl, -⟩ | ⟨hb', -⟩
      · rw [hb] at hb'
        have := congrArg List.length hb'; simp at this
      · exact Or.inr ⟨by rw [hwl', hl], by rw [hpc']; exact h1.entry hI⟩
      · rw [hb] at hb'; cases hb'
    · push Not at hsp
      apply IsHT_frame hwl' (fun y _ => by rw [hpc']) (fun y hy => flush_buf_ne s hy)
      · intro x
        rw [hpc', hs']
        simp only [Function.update_self, hb, ne_eq, reduceCtorEq, not_false_eq_true]
        unfold HTpc
        constructor
        · rintro (h1 | h1 | h1 | ⟨h1, -⟩)
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inr (Or.inr ⟨h1, trivial⟩))
        · rintro (h1 | h1 | h1 | ⟨h1, -⟩)
          · exact Or.inl h1
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inr (Or.inr ⟨h1, hsp x h1⟩))
      · intro _; rw [hpc']

lemma Q_flush {s : Cfg h} (hI : Inv s) (g : Proc h) (hI' : Inv (s.flush g)) :
    Q (s.flush g) = Q s := by
  cases hb : s.buf g with
  | nil => rw [flush_of_nil s g hb]
  | cons w b =>
    unfold Q
    rw [hd_flush hI hI' hb, lv_flush_promQ hI hb]


/-! ### Steps of processes -/

lemma Q_goto {s : Cfg h} (hI : Inv s) {g : Proc h} {c : PC h} (hI' : Inv (s.goto g c))
    (hHT : ∀ x, HTpc c x (s.buf g ≠ []) ↔ HTpc (s.pc g) x (s.buf g ≠ []))
    (hent : s.mem.lock = some g → (c.Entry ↔ (s.pc g).Entry)) : Q (s.goto g c) = Q s :=
  Q_eq_of hI hI' (g := g) rfl (fun y hy => by simp [Function.update_of_ne hy]) (fun _ _ => rfl)
    (by simpa using hHT) (by simpa using hent) rfl

lemma Q_issue {s : Cfg h} (hI : Inv s) {g : Proc h} {c : PC h} {w : W h}
    (hI' : Inv (s.issue g w c)) (hw : w.isPromQ = false)
    (hHT : ∀ x, HTpc c x True ↔ HTpc (s.pc g) x (s.buf g ≠ []))
    (hent : s.mem.lock = some g → (c.Entry ↔ (s.pc g).Entry)) : Q (s.issue g w c) = Q s :=
  Q_eq_of hI hI' (g := g) rfl (fun y hy => by simp [Function.update_of_ne hy])
    (fun y hy => by simp [Function.update_of_ne hy]) (by simpa using hHT) (by simpa using hent)
    (lv_issue_promQ s g c hw)

lemma lock_ne_rem {s : Cfg h} (hI : Inv s) {g : Proc h} (hpc : s.pc g = .rem) :
    s.mem.lock ≠ some g := by
  intro hl
  rcases hI.lockRole g hl with hH | ⟨hE, -⟩
  · simp [Holds, hpc] at hH
  · simp [hpc, PC.Entry] at hE

lemma Q_stepProc {s : Cfg h} (hI : Inv s) (g : Proc h) (hI' : Inv (s.stepProc g))
    (hn : ¬ (s.pc g ≠ .cs ∧ (s.stepProc g).pc g = .cs)) :
    Q (s.stepProc g) = Q s ∨ ∃ x ∉ Q s, Q (s.stepProc g) = Q s ++ [x] := by
  have hL := hI.loc g
  have hH := hI.hc g
  cases hpc : s.pc g <;> simp only [LI, HC, hpc] at hL hH <;>
    simp only [Cfg.stepProc, hpc] at hI' hn ⊢
  case rem =>
    exact Or.inl (Q_issue hI hI' rfl (by simp [HTpc, hpc])
      (fun hl => absurd hl (lock_ne_rem hI hpc)))
  case e22 =>
    rcases barrier_cases s g .e23 with ⟨hb, he⟩ | ⟨w, b, hb, he⟩ <;> rw [he] at hI' ⊢
    · exact Or.inl (Q_goto hI hI' (by simp [HTpc, hpc]) (by simp [hpc, PC.Entry]))
    · exact Or.inl (Q_flush hI g hI')
  case x50 o =>
    rcases barrier_cases s g .rem with ⟨hb, he⟩ | ⟨w, b, hb, he⟩ <;> rw [he] at hI' ⊢
    · exact Or.inl (Q_goto hI hI' (by simp [HTpc, hpc, hb]) (by simp [hpc, PC.Entry]))
    · exact Or.inl (Q_flush hI g hI')
  case e23 | e26 =>
    rw [cas_of_nil s _ hL.1] at hI' hn ⊢
    split_ifs at hI' hn ⊢ with hl
    · exfalso; exact hn ⟨by simp, by simp⟩
    · exact Or.inl (Q_goto hI hI' (by simp [HTpc, hpc]) (by simp [hpc, PC.Entry]))
  case e27 =>
    split_ifs at hI' hn ⊢ with hs
    · exfalso; exact hn ⟨by simp, by simp⟩
    · exact Or.inl rfl
  case x35 l cands =>
    cases cands <;> simp only at hI' hn ⊢ <;>
    exact Or.inl (Q_goto hI hI' (by intro x; (try split_ifs) <;> simp [HTpc, hpc])
      (by intro _; (try split_ifs) <;> simp [hpc, PC.Entry]))
  all_goals first
    | exact Or.inl (Q_goto hI hI' (by intro x; (try split_ifs) <;> simp [HTpc, hpc])
        (by intro _; (try split_ifs) <;> simp [hpc, PC.Entry]))
    | exact Or.inl (Q_issue hI hI' rfl (by intro x; (try split_ifs) <;> simp [HTpc, hpc])
        (by intro _; (try split_ifs) <;> simp [hpc, PC.Entry]))
    | skip
  case x37 l c rest =>
    right
    refine ⟨c, ?_, ?_⟩
    · rw [mem_Q hI]
      rintro (hx | hm)
      rcases hx with ⟨g', hg'⟩ | ⟨hl, -⟩
      · have hcs : s.InCSX g := Or.inr (Or.inl (by simp [hpc, PC.Exit]))
        have := hI.uniq g' g (htpc_facts hI hg').2.1 hcs
        subst this; rw [hpc] at hg'; rcases hg' with h1 | h1 | h1 | ⟨h1, -⟩ <;> cases h1
      · rw [hL.1] at hl; cases hl; exact hL.2.2.2 rfl
      · exact hH.2.2.1 hm
    · unfold Q
      rw [lv_issue_owner _ _ hL.1, ← lv_owner hL.1]
      have : hd (s.issue g (W.promQ ((lv s).promQ ++ [c])) (PC.x38 l c rest)) = hd s := by
        rw [lv_owner hL.1]
        exact hd_congr hI hI' (IsHT_frame (g := g) rfl (fun y hy => by simp [Function.update_of_ne hy])
          (fun y hy => by simp [Function.update_of_ne hy]) (by simp [HTpc, hpc])
          (by simp [hpc, PC.Entry]))
      rw [this]; simp
  case x45 =>
    rcases hv : (s.view g).promQ with _ | ⟨nx, rest⟩ <;> simp only [hv] at hI' hn ⊢
    · exact Or.inl (Q_goto hI hI' (by simp [HTpc, hpc]) (by simp [hpc, PC.Entry]))
    · left
      have h0 : hd s = [] := by
        apply hd_of_not
        rintro x (⟨g', hg'⟩ | ⟨hl, hE⟩)
        · have hcs : s.InCSX g := Or.inr (Or.inl (by simp [hpc, PC.Exit]))
          have := hI.uniq g' g (htpc_facts hI hg').2.1 hcs
          subst this; rw [hpc] at hg'; rcases hg' with h1 | h1 | h1 | ⟨h1, -⟩ <;> cases h1
        · rw [hL.1] at hl; cases hl; rw [hpc] at hE; simp [PC.Entry] at hE
      have h1 : hd (s.issue g (W.promQ rest) (PC.x46 nx)) = [nx] :=
        hd_of hI' (Or.inl ⟨g, Or.inl (by simp)⟩)
      unfold Q
      rw [h0, h1, lv_issue_owner _ _ hL.1, lv_owner hL.1, hv]
      simp


/-- A process entering the critical section is the head of the promotion order (or the order is
empty and it won a CAS). -/
lemma Q_enter {s : Cfg h} (hI : Inv s) (e : Ev h) {x : Proc h}
    (h1 : s.pc x ≠ .cs) (h2 : (s.next e).pc x = .cs) :
    Q s = x :: Q (s.next e) ∨ (Q s = [] ∧ Q (s.next e) = []) := by
  obtain ⟨-, hE, ⟨hpc, hl, hs'⟩ | ⟨hpc, hsig, hs'⟩⟩ := enters_cases hI e h1 h2
  · right
    have hL := hI.loc x
    have hbx : s.buf x = [] := by
      rcases hpc with hpc | hpc <;> simp only [LI, hpc] at hL <;> exact hL.1
    have hd0 : hd s = [] := by
      apply hd_of_not
      rintro y (⟨g', hg'⟩ | ⟨hl', -⟩)
      · rcases (htpc_facts hI hg').1 with h | h <;> rw [hl] at h <;> cases h
      · rw [hl] at hl'; cases hl'
    have hq0 : (lv s).promQ = [] := by simp [lv, hl, hI.q4 hl]
    refine ⟨by simp [Q, hd0, hq0], ?_⟩
    have hd1 : hd (s.next e) = [] := by
      apply hd_of_not
      rintro y (⟨g', hg'⟩ | ⟨hl', hE'⟩)
      · by_cases hgx : g' = x
        · subst hgx; rw [h2] at hg'; rcases hg' with h | h | h | ⟨h, -⟩ <;> cases h
        · rw [hs'] at hg'; simp only [Function.update_of_ne hgx] at hg'
          rcases (htpc_facts hI hg').1 with h | h <;> rw [hl] at h <;> cases h
      · rw [hs'] at hl'; simp at hl'; subst hl'; rw [h2] at hE'; simp [PC.Entry] at hE'
    have hq1 : (lv (s.next e)).promQ = [] := by
      rw [hs']; simp [lv, hbx, hI.q4 hl]
    simp [Q, hd1, hq1]
  · left
    have hL := hI.loc x
    simp only [LI, hpc] at hL
    obtain ⟨hlx, hnh⟩ := hI.sig x hsig hE hL.2
    have hx : IsHT s x := Or.inr ⟨hlx, hE⟩
    have hd1 : hd (s.next e) = [] := by
      apply hd_of_not
      rintro y (⟨g', hg'⟩ | ⟨hl', hE'⟩)
      · by_cases hgx : g' = x
        · subst hgx; rw [h2] at hg'; rcases hg' with h | h | h | ⟨h, -⟩ <;> cases h
        · rw [hs'] at hg'
          simp only [goto_pc, goto_buf, Function.update_of_ne hgx] at hg'
          have hLg := hI.loc g'
          rcases (htpc_facts hI hg').1 with h | h <;> rw [hlx] at h <;> cases h
          · exact hgx rfl
          · rcases hg' with hp | hp | hp | ⟨hp, hne⟩ <;> simp only [LI, hp] at hLg
            · rw [hlx] at hLg; cases hLg.1; exact hgx rfl
            · rw [hlx] at hLg; cases hLg.1; exact hgx rfl
            · rcases hLg.2 with ⟨B, -, -, hl'⟩ | ⟨hb, -⟩
              · rw [hlx] at hl'; cases hl'; exact hgx rfl
              · exact hnh g' (Or.inl ⟨hp, hb⟩)
            · rcases hLg.2 with ⟨B, -, -, hl'⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
              · rw [hlx] at hl'; cases hl'; exact hgx rfl
              · exact hnh g' (Or.inr ⟨hp, hb⟩)
              · exact hne hb
      · rw [hs'] at hl'; simp only [goto_mem] at hl'; rw [hlx] at hl'; cases hl'
        rw [h2] at hE'; simp [PC.Entry] at hE'
    have hq : lv (s.next e) = lv s := by rw [hs']; rfl
    simp [Q, hd_of hI hx, hd1, hq]


/-- If nobody enters the critical section, the promotion order is unchanged or a fresh process
is appended to it. -/
lemma Q_noenter {s : Cfg h} (hI : Inv s) (e : Ev h) (hI' : Inv (s.next e))
    (hn : ∀ x, ¬ (s.pc x ≠ .cs ∧ (s.next e).pc x = .cs)) :
    Q (s.next e) = Q s ∨ ∃ x ∉ Q s, Q (s.next e) = Q s ++ [x] := by
  cases e with
  | flush g => exact Or.inl (Q_flush hI g hI')
  | step g => exact Q_stepProc hI g hI' (hn g)

/-! ### Runs -/

/-- `x` enters the critical section at step `t` of the run. -/
def Enters (r : Run h) (x : Proc h) (t : ℕ) : Prop :=
  (r.s t).pc x ≠ .cs ∧ (r.s (t + 1)).pc x = .cs

lemma Q_run_step (r : Run h) (hI : ∀ t, Inv (r.s t)) (t : ℕ) :
    (∃ y, Enters r y t ∧ (Q (r.s t) = y :: Q (r.s (t + 1)) ∨
      (Q (r.s t) = [] ∧ Q (r.s (t + 1)) = []))) ∨
    (∀ y, ¬ Enters r y t) ∧
      (Q (r.s (t + 1)) = Q (r.s t) ∨ ∃ x ∉ Q (r.s t), Q (r.s (t + 1)) = Q (r.s t) ++ [x]) := by
  have hI' := hI (t + 1)
  rw [r.step t] at hI' ⊢
  by_cases hy : ∃ y, Enters r y t
  · obtain ⟨y, hy⟩ := hy
    have hy' := hy
    unfold Enters at hy'; rw [r.step t] at hy'
    exact Or.inl ⟨y, hy, Q_enter (hI t) _ hy'.1 hy'.2⟩
  · push Not at hy
    refine Or.inr ⟨hy, Q_noenter (hI t) _ hI' (fun x hx => hy x ?_)⟩
    unfold Enters; rw [r.step t]; exact hx

lemma sublist_pair_of_append {α : Type*} {a b z : α} {L : List α} (hs : List.Sublist [a, b] (L ++ [z]))
    (hb : b ≠ z) : List.Sublist [a, b] L := by
  rw [List.sublist_append_iff] at hs
  obtain ⟨l₁, l₂, he, h1, h2⟩ := hs
  rcases List.sublist_singleton.1 h2 with rfl | rfl
  · simp only [List.append_nil] at he; exact he ▸ h1
  · rcases l₁ with _ | ⟨c, _ | ⟨d, l₁⟩⟩
    · simp at he
    · simp at he; exact absurd he.2 hb
    · simp at he

/-- Membership in the promotion order persists until the process enters the critical section. -/
lemma Q_persist (r : Run h) (hI : ∀ t, Inv (r.s t)) {x : Proc h} {a b : ℕ} (hab : a ≤ b)
    (hx : x ∈ Q (r.s a)) (hn : ∀ t, a ≤ t → t < b → ¬ Enters r x t) : x ∈ Q (r.s b) := by
  induction b, hab using Nat.le_induction with
  | base => exact hx
  | succ b hab ih =>
    have hxb := ih (fun t h1 h2 => hn t h1 (by omega))
    rcases Q_run_step r hI b with ⟨y, hy, he | ⟨he, -⟩⟩ | ⟨-, he | ⟨z, -, he⟩⟩
    · rw [he] at hxb
      rcases List.mem_cons.1 hxb with rfl | h
      · exact absurd hy (hn b hab (by omega))
      · exact h
    · rw [he] at hxb; simp at hxb
    · rw [he]; exact hxb
    · rw [he]; exact List.mem_append_left _ hxb

/-- **FIFO.** If `x` is in the promotion order at time `π` and another process `q` enters the
critical section twice at or after `π` (at `e₁ < e₂`), then `x` enters before `e₂`. -/
theorem fifo (r : Run h) (hI : ∀ t, Inv (r.s t)) {x q : Proc h} {π e₁ e₂ : ℕ}
    (hx : x ∈ Q (r.s π)) (h1 : π ≤ e₁) (h12 : e₁ < e₂) (hq1 : Enters r q e₁)
    (hq2 : Enters r q e₂) : ∃ g, π ≤ g ∧ g < e₂ ∧ Enters r x g := by
  by_contra hno
  push Not at hno
  have hxq : x ≠ q := by rintro rfl; exact hno e₁ h1 h12 hq1
  have hin : ∀ t, π ≤ t → t ≤ e₂ → x ∈ Q (r.s t) := fun t ht1 ht2 =>
    Q_persist r hI ht1 hx (fun g hg1 hg2 => hno g hg1 (by omega))
  -- after the first entry of `q`, `q` is never ahead of `x`
  have key : ∀ t, e₁ + 1 ≤ t → t ≤ e₂ → ¬ List.Sublist [q, x] (Q (r.s t)) := by
    intro t ht1 ht2
    induction t, ht1 using Nat.le_induction with
    | base =>
      intro hs
      have := Q_entry (hI _) (hs.subset (List.mem_cons_self (a := q) (l := [x])))
      rw [hq1.2] at this; simp [PC.Entry] at this
    | succ t ht ih =>
      intro hs
      have hxt := hin t (by omega) (by omega)
      rcases Q_run_step r hI t with ⟨y, hy, he | ⟨he, -⟩⟩ | ⟨-, he | ⟨z, hz, he⟩⟩
      · exact ih (by omega) (he ▸ hs.cons y)
      · rw [he] at hxt; simp at hxt
      · exact ih (by omega) (he ▸ hs)
      · rw [he] at hs
        exact ih (by omega) (sublist_pair_of_append hs (fun h => hz (h ▸ hxt)))
  have hx2 := hin e₂ (by omega) le_rfl
  rcases Q_run_step r hI e₂ with ⟨y, hy, he | ⟨he, -⟩⟩ | ⟨hn, -⟩
  · have hyq : y = q := by
      by_contra hyq
      -- only one process changes its program counter in a step
      have : r.ev e₂ = .step y ∧ r.ev e₂ = .step q := by
        constructor
        · exact eq_step_of_pc_ne (r.s e₂) (r.ev e₂) (by rw [← r.step]; exact fun h => hy.1 (h ▸ hy.2))
        · exact eq_step_of_pc_ne (r.s e₂) (r.ev e₂) (by rw [← r.step]; exact fun h => hq2.1 (h ▸ hq2.2))
      rw [this.1] at this; exact hyq (Ev.step.inj this.2)
    subst hyq
    rw [he] at hx2
    rcases List.mem_cons.1 hx2 with h | h
    · exact hxq h
    · apply key e₂ (by omega) le_rfl
      rw [he]
      exact List.Sublist.cons_cons _ (List.singleton_sublist.2 h)
  · rw [he] at hx2; simp at hx2
  · exact hn q hq2


/-! ### Promotion by an exit section -/

/-- A process in the entry section stays there until it enters the critical section. -/
lemma entry_step {s : Cfg h} (hI : Inv s) (e : Ev h) {x : Proc h} (hE : (s.pc x).Entry)
    (hn : (s.next e).pc x ≠ .cs) : ((s.next e).pc x).Entry := by
  by_cases he : e = .step x
  · subst he
    have hL := hI.loc x
    cases hpc : s.pc x <;> simp only [hpc, PC.Entry] at hE <;> simp only [LI, hpc] at hL <;>
      simp only [Cfg.next, Cfg.stepProc, hpc] at hn ⊢
    case e22 =>
      rcases barrier_cases s x .e23 with ⟨-, hb⟩ | ⟨w, b, -, hb⟩ <;> rw [hb] <;>
        simp [hpc, PC.Entry]
    case e23 | e26 =>
      rw [cas_of_nil s _ hL.1] at hn ⊢
      split_ifs at hn ⊢ <;> simp_all [PC.Entry]
    case e27 =>
      split_ifs at hn ⊢ <;> simp_all [PC.Entry]
    all_goals (try split_ifs) <;> simp [PC.Entry]
  · rw [next_pc_ne s e he]; exact hE

/-- `r` is still to be examined (statements 35–38) by the exit section at program counter `c`. -/
def Pending (c : PC h) (r : Proc h) : Prop :=
  match c with
  | .x34 _ _ acc => r ∈ acc
  | .x35 _ cands => r ∈ cands
  | .x36 _ c rest | .x37 _ c rest => r = c ∨ r ∈ rest
  | .x38 _ _ rest => r ∈ rest
  | _ => False

lemma Pending.incsx {s : Cfg h} {g r : Proc h} (hp : Pending (s.pc g) r) : s.InCSX g := by
  unfold Cfg.InCSX
  cases hpc : s.pc g <;> simp_all [Pending, PC.Exit]

lemma mem_addCand {g r : Proc h} {acc : List (Proc h)} (o : Option (Proc h)) (hr : r ∈ acc) :
    r ∈ addCand g acc o := by
  cases o with
  | none => exact hr
  | some q => simp only [addCand]; split_ifs <;> simp [hr]

lemma mem_addCand_self {g r : Proc h} {acc : List (Proc h)} (hr : r ≠ g) :
    r ∈ addCand g acc (some r) := by
  simp only [addCand]; split_ifs with hc
  · simp
  · push Not at hc; exact hc hr

lemma Pending.step {s : Cfg h} (hI : Inv s) (e : Ev h) {g r : Proc h}
    (hp : Pending (s.pc g) r) (hE : (s.pc r).Entry) (ha : s.mem.apply r = true) :
    Pending ((s.next e).pc g) r ∨ r ∈ Q s ∨ r ∈ (lv (s.next e)).promQ := by
  have hrg : r ≠ g := by
    rintro rfl; exact entry_not_incsx hE hp.incsx
  by_cases he : e = .step g
  · subst he
    have hL := hI.loc g
    cases hpc : s.pc g <;> simp only [hpc, Pending] at hp <;> simp only [LI, hpc] at hL <;>
      simp only [Cfg.next, Cfg.stepProc, hpc]
    case x34 l j acc =>
      left; split_ifs <;> simp only [goto_pc, Function.update_self, Pending] <;>
        exact mem_addCand _ hp
    case x35 l cands =>
      cases cands with
      | nil => simp at hp
      | cons c rest =>
        left
        simp only [goto_pc, Function.update_self]
        have hva : (s.view g).apply r = true := by
          unfold Cfg.view; rw [view_apply_of]; · exact ha
          intro w hw
          cases w with
          | apply x b => obtain ⟨rfl, -⟩ := buf_apply hI hw; simp [W.isApply, Ne.symm hrg]
          | _ => rfl
        rcases List.mem_cons.1 hp with rfl | hp
        · simp [hva, Pending]
        · split_ifs <;> simp [Pending, hp]
    case x36 l c rest =>
      rcases hp with rfl | hp
      · split_ifs with hin
        · right; left
          rw [← lv_owner hL.1] at hin
          rcases (hI.inpq r).1 hin with ⟨hm, -⟩ | ⟨g', hg'⟩
          · exact (mem_Q hI).2 (Or.inr hm)
          · exfalso
            have hcs : s.InCSX g := Or.inr (Or.inl (by simp [hpc, PC.Exit]))
            have := hI.uniq g' g (Or.inr (Or.inl (by simp [hg', PC.Exit]))) hcs
            subst this; rw [hpc] at hg'; cases hg'
        · left; simp [Pending]
      · left; split_ifs <;> simp [Pending, hp]
    case x37 l c rest =>
      rcases hp with rfl | hp
      · right; right
        rw [lv_issue_owner _ _ hL.1]; simp
      · left; simp [Pending, hp]
    case x38 l c rest =>
      left; simp [Pending, hp]
  · left; rw [next_pc_ne s e he]; exact hp

/-- **Promotion.** If an exit section of `g` still has to examine `x` (or `x` is already in the
promotion order) and `x` is in its entry section with `apply[x] = true`, then by any time `U`
at which `g` has left its exit section, `x` has entered the critical section or is in the
promotion order. -/
theorem promote (r : Run h) (hI : ∀ t, Inv (r.s t)) {g x : Proc h} {T U : ℕ} (hTU : T ≤ U)
    (hP : Pending ((r.s T).pc g) x ∨ x ∈ Q (r.s T)) (hE : ((r.s T).pc x).Entry)
    (ha : (r.s T).mem.apply x = true) (hU : ¬ (r.s U).InCSX g) :
    (∃ t, T ≤ t ∧ t < U ∧ Enters r x t) ∨ x ∈ Q (r.s U) := by
  have main : ∀ U, T ≤ U → (∃ t, T ≤ t ∧ t < U ∧ Enters r x t) ∨
      ((Pending ((r.s U).pc g) x ∨ x ∈ Q (r.s U)) ∧ ((r.s U).pc x).Entry ∧
        (r.s U).mem.apply x = true) := by
    intro U hTU
    induction U, hTU using Nat.le_induction with
    | base => exact Or.inr ⟨hP, hE, ha⟩
    | succ U hTU ih =>
      rcases ih with ⟨t, h1, h2, h3⟩ | ⟨hP', hE', ha'⟩
      · exact Or.inl ⟨t, h1, by omega, h3⟩
      · by_cases hen : Enters r x U
        · exact Or.inl ⟨U, hTU, by omega, hen⟩
        · right
          have hcs : (r.s (U + 1)).pc x ≠ .cs := fun h => hen ⟨fun h' => by
            rw [h'] at hE'; simp [PC.Entry] at hE', h⟩
          have hnoent : ∀ t, U ≤ t → t < U + 1 → ¬ Enters r x t := by
            intro t h1 h2; rwa [show t = U by omega]
          refine ⟨?_, ?_, ?_⟩
          · rcases hP' with hP' | hQ
            · have := Pending.step (hI U) (r.ev U) hP' hE' ha'
              rw [← r.step U] at this
              rcases this with h | h | h
              · exact Or.inl h
              · exact Or.inr (Q_persist r hI (by omega) h hnoent)
              · exact Or.inr ((mem_Q (hI _)).2 (Or.inr h))
            · exact Or.inr (Q_persist r hI (by omega) hQ hnoent)
          · have := entry_step (hI U) (r.ev U) hE' (by rw [← r.step U]; exact hcs)
            rwa [← r.step U] at this
          · have := apply_step (hI U) (r.ev U) hE' ha'
            rwa [← r.step U] at this
  rcases main U hTU with h | ⟨hP', -, -⟩
  · exact Or.inl h
  · rcases hP' with hP' | hQ
    · exact absurd hP'.incsx hU
    · exact Or.inr hQ

end Podc.ConstantBarriersMutex.BW
