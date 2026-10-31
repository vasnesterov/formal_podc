import Papers.PODC2015.HelpFreeWaitFree.ExactOrder

/-!
# The shape of a linearization in the proof of Theorem 4.3

Combinatorial core of Claims 4.5.2 and 4.5.3 of [CPT15]: in the setting of the proof of
Theorem 4.3 (process `p₁` runs `op`, `p₂` runs `W`, `p₃` runs `R`), suppose that after `p₂`
completed `W(n)` and `p₃` completed `R(m)`, a sequential history `S` (a linearization) puts

* the first `n` operations of `p₂` before everything else that is relevant,
* the operations of `p₃` in program order,
* everything not invoked yet when `R(m)` completed after `R(m)`,
* `op₁ = (p₁, 0)` or `op₂ = (p₂, n)` before the first operation of `p₃`.

Then the prefix of `S` up to the `m`-th operation of `p₃` is a sequence of
`W(n) ∘ op ∘ (R(m) + W_{n+1}?)` if `op₁` comes before `op₂` (or `op₂` is missing), and of
`W(n+1) ∘ (R(m) + op?)` otherwise (`shape`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

/-! ### List lemmas -/

section ListLemmas

variable {α : Type}

lemma insertIdx_length_append (s t : List α) (x : α) :
    (s ++ t).insertIdx s.length x = s ++ x :: t := by
  induction s with
  | nil => simp
  | cons a s ih => simp [List.insertIdx_succ_cons, ih]

lemma mem_optIns_of_split {xs s t : List α} {x : α} (h : xs = s ++ t) :
    s ++ x :: t ∈ OptIns xs x :=
  Or.inr ⟨s.length, by simp [h], by rw [h, insertIdx_length_append]⟩

lemma self_mem_optIns (xs : List α) (x : α) : xs ∈ OptIns xs x := Or.inl rfl

/-- A list where every `p`-element comes before every non-`p` element splits into its
`p`-part followed by the rest. -/
lemma eq_filter_append_filter (p : α → Bool) :
    ∀ {l : List α}, l.Pairwise (fun a b => p b = true → p a = true) →
      l = l.filter p ++ l.filter (fun a => !p a)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : p a = true
    · simp only [List.filter_cons, ha, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
        List.cons_append]
      exact congrArg _ (eq_filter_append_filter p h.2)
    · have hl : ∀ b ∈ l, p b = false := fun b hb => by
        by_contra hb'; exact ha (h.1 b hb (by simpa using hb'))
      have h1 : l.filter p = [] := List.filter_eq_nil_iff.2 (fun b hb => by simp [hl b hb])
      have h2 : l.filter (fun a => !p a) = l := List.filter_eq_self.2 (fun b hb => by simp [hl b hb])
      simp [ha, h1, h2]

lemma eq_range_of_pairwise {l : List ℕ} {n : ℕ} (hnd : l.Nodup) (hs : l.Pairwise (· < ·))
    (hm : ∀ x, x ∈ l ↔ x < n) : l = List.range n := by
  apply List.Perm.eq_of_pairwise (le := (· < ·)) (fun a b _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl _))
    hs List.pairwise_lt_range
  rw [List.perm_ext_iff_of_nodup hnd List.nodup_range]
  intro x; rw [hm x, List.mem_range]

variable [DecidableEq α]

lemma pairwise_idxOf_lt : ∀ {l : List α}, l.Nodup → l.Pairwise (fun a b => l.idxOf a < l.idxOf b)
  | [], _ => List.Pairwise.nil
  | x :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, ?_⟩
    · have : b ≠ x := fun e => h.1 (e ▸ hb)
      rw [List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm this)]; exact Nat.succ_pos _
    · refine (pairwise_idxOf_lt h.2).imp_of_mem (fun {a b} ha hb hab => ?_)
      have ha' : a ≠ x := fun e => h.1 (e ▸ ha)
      have hb' : b ≠ x := fun e => h.1 (e ▸ hb)
      rw [List.idxOf_cons_ne _ (Ne.symm ha'), List.idxOf_cons_ne _ (Ne.symm hb')]
      exact Nat.succ_lt_succ hab

end ListLemmas

/-! ### Positions in a sequential history with distinct instances -/

section Pos

variable {P : Type} [DecidableEq P] {A : ObjSpec}

lemma pos_getElem {S : List (OpId P × A.Op)} (hnd : (S.map Prod.fst).Nodup) (i : ℕ)
    (hi : i < S.length) : pos S S[i].1 = i := by
  have : (S.map Prod.fst)[i]'(by simpa using hi) = S[i].1 := by simp
  rw [pos, ← this, List.Nodup.idxOf_getElem hnd]

lemma eq_of_mem_of_fst_eq {S : List (OpId P × A.Op)} (hnd : (S.map Prod.fst).Nodup)
    {e e' : OpId P × A.Op} (he : e ∈ S) (he' : e' ∈ S) (h : e.1 = e'.1) : e = e' :=
  List.inj_on_of_nodup_map hnd he he' h

lemma mem_take_iff {S : List (OpId P × A.Op)} (hnd : (S.map Prod.fst).Nodup) {j : ℕ}
    {e : OpId P × A.Op} : e ∈ S.take j ↔ e ∈ S ∧ pos S e.1 < j := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
    simp only [List.length_take] at hi
    rw [List.getElem_take]
    refine ⟨List.getElem_mem _, ?_⟩
    rw [pos_getElem hnd]; omega
  · rintro ⟨h, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
    rw [pos_getElem hnd] at hp
    exact List.mem_iff_getElem.2 ⟨i, by simp; omega, by rw [List.getElem_take]⟩

lemma mem_drop_iff {S : List (OpId P × A.Op)} (hnd : (S.map Prod.fst).Nodup) {j : ℕ}
    {e : OpId P × A.Op} : e ∈ S.drop j ↔ e ∈ S ∧ j ≤ pos S e.1 := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
    simp only [List.length_drop] at hi
    rw [List.getElem_drop]
    refine ⟨List.getElem_mem _, ?_⟩
    rw [pos_getElem hnd]; omega
  · rintro ⟨h, hp⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 h
    rw [pos_getElem hnd] at hp
    exact List.mem_iff_getElem.2 ⟨i - j, by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩

/-- An instance occurring in `S` has an entry. -/
lemma exists_entry {S : List (OpId P × A.Op)} {x : OpId P} (hx : x ∈ S.map Prod.fst) :
    ∃ e ∈ S, e.1 = x := by
  simpa using hx

lemma pairwise_pos (S : List (OpId P × A.Op)) (hnd : (S.map Prod.fst).Nodup) :
    S.Pairwise (fun a b => pos S a.1 < pos S b.1) := by
  have := pairwise_idxOf_lt hnd
  rw [List.pairwise_map] at this
  exact this

end Pos

lemma pre_succ' {α : Type} (S : ℕ → α) (n : ℕ) : pre S (n + 1) = pre S n ++ [S n] := by
  simp [pre, List.range_succ]

lemma tagged_append' {A : ObjSpec} (t : Bool) (xs ys : List A.Op) :
    tagged t (xs ++ ys) = tagged t xs ++ tagged t ys := by
  simp [tagged]

/-! ### The shape lemma -/

section Shape

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- Tag of an entry: it is one of the first `m` operations of `p₃`. -/
def tagR (p₃ : P) (m : ℕ) (e : OpId P × A.Op) : Bool := decide (e.1.1 = p₃ ∧ e.1.2 < m)

/-- A sequential history as a tagged sequence of operations (tag = one of the first `m`
operations of `p₃`). -/
def toTagged (p₃ : P) (m : ℕ) (S : List (OpId P × A.Op)) : List (Bool × A.Op) :=
  S.map (fun e => (tagR p₃ m e, e.2))

variable (p₁ p₂ p₃ : P) (op : A.Op) (W R : ℕ → A.Op) (n m : ℕ)

/-- The instances that matter in Claims 4.5.2–4.5.3: `op₁ = (p₁,0)`, `(p₂, i)` for `i ≤ n`, and
`(p₃, j)` for `j < m`. -/
def Known (x : OpId P) : Prop :=
  x = (p₁, 0) ∨ (x.1 = p₂ ∧ x.2 ≤ n) ∨ (x.1 = p₃ ∧ x.2 < m)


/-- A sublist of `S` consisting of instances of `q` with indices exactly `0, …, N-1`, ordered in
`S` by index, is the list of these instances in order. -/
lemma eq_range_of_sublist {S l : List (OpId P × A.Op)} (hnd : (S.map Prod.fst).Nodup)
    (hl : l.Sublist S) (q : P) (N : ℕ) (F : ℕ → A.Op)
    (hproc : ∀ e ∈ l, e.1.1 = q) (hlt : ∀ e ∈ l, e.1.2 < N)
    (hall : ∀ j < N, ∃ e ∈ l, e.1 = (q, j))
    (hmono : ∀ j j', j < j' → j' < N → pos S (q, j) < pos S (q, j'))
    (hops : ∀ e ∈ l, e.2 = F e.1.2) :
    l = (List.range N).map (fun j => (((q, j) : OpId P), F j)) := by
  have hndl : (l.map Prod.fst).Nodup := (hl.map Prod.fst).nodup hnd
  have hpw : l.Pairwise (fun a b => pos S a.1 < pos S b.1) := (pairwise_pos S hnd).sublist hl
  have hix : l.map (fun e => e.1.2) = List.range N := by
    apply eq_range_of_pairwise
    · have : l.map (fun e => e.1.2) = (l.map Prod.fst).map Prod.snd := by simp
      rw [this]
      refine hndl.map_on (fun x hx y hy hxy => ?_)
      obtain ⟨ex, hex, rfl⟩ := List.mem_map.1 hx
      obtain ⟨ey, hey, rfl⟩ := List.mem_map.1 hy
      exact Prod.ext ((hproc ex hex).trans (hproc ey hey).symm) hxy
    · rw [List.pairwise_map]
      refine hpw.imp_of_mem (fun {a b} ha hb hab => ?_)
      by_contra hc
      push Not at hc
      rcases hc.lt_or_eq with hc | hc
      · have := hmono _ _ hc (hlt a ha)
        have ha' : a.1 = (q, a.1.2) := by rw [← hproc a ha]
        have hb' : b.1 = (q, b.1.2) := by rw [← hproc b hb]
        rw [← ha', ← hb'] at this
        omega
      · have : a.1 = b.1 := Prod.ext ((hproc a ha).trans (hproc b hb).symm) hc.symm
        rw [this] at hab; omega
    · intro x
      constructor
      · intro hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        exact hlt e he
      · intro hx
        obtain ⟨e, he, he1⟩ := hall x hx
        exact List.mem_map.2 ⟨e, he, by simp [he1]⟩
  rw [← hix, List.map_map]
  conv_lhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro e he
  simp only [id, Function.comp]
  rw [← hops e he, ← hproc e he]

/-- **Shape of a linearization** (core of Claims 4.5.2 and 4.5.3). -/
theorem shape (S : List (OpId P × A.Op))
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) (hm : 0 < m)
    (hnd : (S.map Prod.fst).Nodup)
    (hop1 : ∀ e ∈ S, pos S e.1 ≤ pos S (p₃, m - 1) → e.1 = (p₁, 0) → e.2 = op)
    (hopW : ∀ e ∈ S, pos S e.1 ≤ pos S (p₃, m - 1) → e.1.1 = p₂ → e.2 = W e.1.2)
    (hopR : ∀ e ∈ S, pos S e.1 ≤ pos S (p₃, m - 1) → e.1.1 = p₃ → e.2 = R e.1.2)
    (hmemW : ∀ i < n, ((p₂, i) : OpId P) ∈ S.map Prod.fst)
    (hmemR : ∀ j < m, ((p₃, j) : OpId P) ∈ S.map Prod.fst)
    (hlate : ∀ x ∈ S.map Prod.fst, ¬ Known p₁ p₂ p₃ n m x → pos S (p₃, m - 1) < pos S x)
    (hW1 : ∀ i < n, ((p₁, 0) : OpId P) ∈ S.map Prod.fst → pos S (p₂, i) < pos S (p₁, 0))
    (hW2 : ∀ i < n, ((p₂, n) : OpId P) ∈ S.map Prod.fst → pos S (p₂, i) < pos S (p₂, n))
    (hWR : ∀ i < n, pos S (p₂, i) < pos S (p₃, 0))
    (hWW : ∀ i i', i < i' → i' < n → pos S (p₂, i) < pos S (p₂, i'))
    (hRR : ∀ j j', j < j' → j' < m → pos S (p₃, j) < pos S (p₃, j'))
    (hfirst : pos S (p₁, 0) < pos S (p₃, 0) ∨ pos S (p₂, n) < pos S (p₃, 0)) :
    (S.filter (tagR p₃ m)).map Prod.fst = (List.range m).map (fun j => ((p₃, j) : OpId P)) ∧
    ∃ T₁ T₂, toTagged p₃ m S = T₁ ++ T₂ ∧ (∀ e ∈ T₂, e.1 = false) ∧
      (Prec S (p₂, n) (p₁, 0) → T₁ ∈ seqWFirst op W R n m) ∧
      (¬ Prec S (p₂, n) (p₁, 0) → T₁ ∈ seqOpFirst op W R n m) := by
  classical
  set ids := S.map Prod.fst with hids
  set k := pos S (p₃, m - 1) with hk
  have hRk : ∀ j < m, pos S (p₃, j) ≤ k := by
    intro j hj
    rcases Nat.lt_or_ge j (m - 1) with h | h
    · exact (hRR j (m - 1) h (by omega)).le
    · have : j = m - 1 := by omega
      rw [this]
  have hklen : k < S.length := pos_lt_length_iff.2 (hmemR (m - 1) (by omega))
  have hR0k : pos S (p₃, 0) ≤ k := hRk 0 hm
  -- entries with position `≤ k` form `S'`
  set S' := S.take (k + 1) with hS'
  set S'' := S.drop (k + 1) with hS''
  have hmemS' : ∀ {e}, e ∈ S' ↔ e ∈ S ∧ pos S e.1 ≤ k := by
    intro e; rw [hS', mem_take_iff hnd, Nat.lt_succ_iff]
  have hentry : ∀ x ∈ ids, pos S x ≤ k → ∃ e ∈ S', e.1 = x := by
    intro x hx hxk
    obtain ⟨e, he, rfl⟩ := exists_entry hx
    exact ⟨e, hmemS'.2 ⟨he, hxk⟩, rfl⟩
  have hknown : ∀ e ∈ S', Known p₁ p₂ p₃ n m e.1 := by
    intro e he
    obtain ⟨he, hek⟩ := hmemS'.1 he
    by_contra hc
    have := hlate e.1 (List.mem_map.2 ⟨e, he, rfl⟩) hc
    omega
  have hpwS' : S'.Pairwise (fun a b => pos S a.1 < pos S b.1) :=
    (pairwise_pos S hnd).sublist (List.take_sublist _ _)
  have hsubS' : S'.Sublist S := List.take_sublist _ _
  -- tags after position `k` are `false`
  have hT2 : ∀ e ∈ S'', tagR p₃ m e = false := by
    intro e he
    obtain ⟨he, hek⟩ := (mem_drop_iff hnd).1 he
    by_contra hc
    simp only [tagR, Bool.not_eq_false, decide_eq_true_eq] at hc
    have := hRk e.1.2 hc.2
    have he' : e.1 = (p₃, e.1.2) := by rw [← hc.1]
    rw [← he'] at this
    omega
  have hfilt : S.filter (tagR p₃ m) = S'.filter (tagR p₃ m) := by
    have h0 : S''.filter (tagR p₃ m) = [] :=
      List.filter_eq_nil_iff.2 (fun e he => by simp [hT2 e he])
    conv_lhs => rw [← List.take_append_drop (k + 1) S]
    rw [List.filter_append, ← hS'', h0, List.append_nil]
  -- the `W`-part
  set isW : OpId P × A.Op → Bool := fun e => decide (e.1.1 = p₂ ∧ e.1.2 < n) with hisW
  set Wl := S'.filter isW with hWl
  set rest := S'.filter (fun e => !isW e) with hrest
  have hsplit : S' = Wl ++ rest := by
    apply eq_filter_append_filter isW
    refine hpwS'.imp_of_mem (fun {a b} ha hb hab hbW => ?_)
    by_contra haW
    simp only [hisW, decide_eq_true_eq] at hbW haW
    have hb' : b.1 = (p₂, b.1.2) := by rw [← hbW.1]
    rcases hknown a ha with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hW1 _ hbW.2 (by rw [← h]; exact List.mem_map.2 ⟨a, (hmemS'.1 ha).1, rfl⟩)
      rw [← hb', ← h] at this; omega
    · have hn : a.1.2 = n := by
        by_contra hne; exact haW ⟨h1, by omega⟩
      have ha' : a.1 = (p₂, n) := by rw [← h1, ← hn]
      have := hW2 _ hbW.2 (by rw [← ha']; exact List.mem_map.2 ⟨a, (hmemS'.1 ha).1, rfl⟩)
      rw [← hb', ← ha'] at this; omega
    · have h1' := hWR _ hbW.2
      have h2' : pos S (p₃, 0) ≤ pos S a.1 := by
        have ha' : a.1 = (p₃, a.1.2) := by rw [← h1]
        rcases Nat.eq_zero_or_pos a.1.2 with h0 | h0
        · rw [ha', h0]
        · rw [ha']; exact (hRR 0 _ h0 h2).le
      rw [← hb'] at h1'; omega
  have hWl : Wl = (List.range n).map (fun i => (((p₂, i) : OpId P), W i)) := by
    apply eq_range_of_sublist hnd ((List.filter_sublist).trans hsubS') p₂ n W
    · intro e he; exact (by simpa [hisW] using (List.mem_filter.1 he).2 : e.1.1 = p₂ ∧ e.1.2 < n).1
    · intro e he; exact (by simpa [hisW] using (List.mem_filter.1 he).2 : e.1.1 = p₂ ∧ e.1.2 < n).2
    · intro i hi
      obtain ⟨e, he, he1⟩ := hentry _ (hmemW i hi) ((hWR i hi).le.trans hR0k)
      exact ⟨e, List.mem_filter.2 ⟨he, by simp [hisW, he1, hi]⟩, he1⟩
    · exact hWW
    · intro e he
      exact hopW e (hmemS'.1 (List.mem_filter.1 he).1).1 (hmemS'.1 (List.mem_filter.1 he).1).2
        (by simpa [hisW] using (List.mem_filter.1 he).2 : e.1.1 = p₂ ∧ e.1.2 < n).1
  have hRl : S'.filter (tagR p₃ m) = (List.range m).map (fun j => (((p₃, j) : OpId P), R j)) := by
    apply eq_range_of_sublist hnd ((List.filter_sublist).trans hsubS') p₃ m R
    · intro e he; exact (by simpa [tagR] using (List.mem_filter.1 he).2 : e.1.1 = p₃ ∧ e.1.2 < m).1
    · intro e he; exact (by simpa [tagR] using (List.mem_filter.1 he).2 : e.1.1 = p₃ ∧ e.1.2 < m).2
    · intro j hj
      obtain ⟨e, he, he1⟩ := hentry _ (hmemR j hj) (hRk j hj)
      exact ⟨e, List.mem_filter.2 ⟨he, by simp [tagR, he1, hj]⟩, he1⟩
    · exact hRR
    · intro e he
      exact hopR e (hmemS'.1 (List.mem_filter.1 he).1).1 (hmemS'.1 (List.mem_filter.1 he).1).2
        (by simpa [tagR] using (List.mem_filter.1 he).2 : e.1.1 = p₃ ∧ e.1.2 < m).1
  refine ⟨by rw [hfilt, hRl, List.map_map]; rfl, ?_⟩
  -- the rest: `op₁`, `op₂` and the operations of `p₃`
  have hrestS' : ∀ {e}, e ∈ rest → e ∈ S' ∧ isW e = false := by
    intro e he; have := List.mem_filter.1 he; simpa using this
  have hrestKind : ∀ e ∈ rest, e.1 = (p₁, 0) ∨ e.1 = (p₂, n) ∨ tagR p₃ m e = true := by
    intro e he
    obtain ⟨he1, he2⟩ := hrestS' he
    rcases hknown e he1 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h
    · right; left
      have hn : e.1.2 = n := by
        by_contra hne; simp [hisW, h1] at he2; omega
      rw [← h1, ← hn]
    · right; right; simp [tagR, h1, h2]
  have hpwrest : rest.Pairwise (fun a b => pos S a.1 < pos S b.1) :=
    hpwS'.sublist List.filter_sublist
  have hndrest : (rest.map Prod.fst).Nodup :=
    ((List.filter_sublist.trans hsubS').map Prod.fst).nodup hnd
  have hRrest : rest.filter (tagR p₃ m) = S'.filter (tagR p₃ m) := by
    have h0 : Wl.filter (tagR p₃ m) = [] := List.filter_eq_nil_iff.2 (fun e he => by
      rw [hWl] at he; obtain ⟨i, -, rfl⟩ := List.mem_map.1 he; simp [tagR, h23])
    conv_rhs => rw [hsplit]
    rw [List.filter_append, h0, List.nil_append]
  have hinrest : ∀ e ∈ S, pos S e.1 ≤ k → isW e = false → e ∈ rest := fun e he hk hw =>
    List.mem_filter.2 ⟨hmemS'.2 ⟨he, hk⟩, by simp [hw]⟩
  obtain ⟨e, rest', hre⟩ : ∃ e rest', rest = e :: rest' := by
    obtain ⟨e, he, he1⟩ := hentry _ (hmemR 0 hm) hR0k
    have : e ∈ rest := List.mem_filter.2 ⟨he, by simp [hisW, he1, h23.symm]⟩
    cases h : rest with
    | nil => rw [h] at this; simp at this
    | cons e r => exact ⟨e, r, rfl⟩
  have hhead : ∀ x ∈ rest', pos S e.1 < pos S x.1 := by
    have := hpwrest; rw [hre, List.pairwise_cons] at this; exact this.1
  have he_rest : e ∈ rest := by rw [hre]; simp
  have hnd' : (e.1 :: rest'.map Prod.fst).Nodup := by
    have := hndrest; rw [hre] at this; simpa using this
  have hnotin : e.1 ∉ rest'.map Prod.fst := (List.nodup_cons.1 hnd').1
  have hndr' : (rest'.map Prod.fst).Nodup := (List.nodup_cons.1 hnd').2
  have he12 : e.1 = (p₁, 0) ∨ e.1 = (p₂, n) := by
    rcases hrestKind e he_rest with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      simp only [tagR, decide_eq_true_eq] at h
      have hpe : pos S (p₃, 0) ≤ pos S e.1 := by
        have he' : e.1 = (p₃, e.1.2) := by rw [← h.1]
        rcases Nat.eq_zero_or_pos e.1.2 with h0 | h0
        · rw [he', h0]
        · rw [he']; exact (hRR 0 _ h0 h.2).le
      obtain ⟨x, hx, hxne, hxW⟩ : ∃ x : OpId P, pos S x < pos S (p₃, 0) ∧ x.1 ≠ p₃ ∧
          (∀ ex ∈ S, ex.1 = x → isW ex = false) := by
        rcases hfirst with h1 | h1
        · exact ⟨(p₁, 0), h1, h13, fun ex _ hex => by simp [hisW, hex, h12]⟩
        · exact ⟨(p₂, n), h1, h23, fun ex _ hex => by simp [hisW, hex]⟩
      have hxmem : x ∈ ids :=
        pos_lt_length_iff.1 (lt_of_lt_of_le hx (pos_le_length _ _))
      obtain ⟨ex, hex, hex1⟩ := exists_entry hxmem
      have hexr : ex ∈ rest := hinrest ex hex (by rw [hex1]; omega) (hxW ex hex hex1)
      rw [hre] at hexr
      rcases List.mem_cons.1 hexr with h' | h'
      · subst h'; exact hxne (by rw [← hex1, h.1])
      · have := hhead ex h'; rw [hex1] at this; omega
  have heS : e ∈ S := (hmemS'.1 (hrestS' he_rest).1).1
  have hek : pos S e.1 ≤ k := (hmemS'.1 (hrestS' he_rest).1).2
  have hetag : tagR p₃ m e = false := by
    rcases he12 with h | h <;> simp [tagR, h, h13, h23]
  have hR' : rest'.filter (tagR p₃ m) = S'.filter (tagR p₃ m) := by
    rw [← hRrest, hre, List.filter_cons, hetag]; simp
  have htagR : toTagged p₃ m (S'.filter (tagR p₃ m)) = tagged true (pre R m) := by
    rw [hRl]
    simp only [toTagged, tagged, pre, List.map_map]
    apply List.map_congr_left
    intro j hj
    simp [tagR, List.mem_range.1 hj]
  have htagW : toTagged p₃ m Wl = tagged false (pre W n) := by
    rw [hWl]; simp [toTagged, tagged, pre, tagR, h23]
  have hT1 : toTagged p₃ m S' = tagged false (pre W n) ++ (false, e.2) :: toTagged p₃ m rest' := by
    have : toTagged p₃ m S' = toTagged p₃ m Wl ++ toTagged p₃ m (e :: rest') := by
      conv_lhs => rw [hsplit, hre]
      simp [toTagged]
    rw [this, htagW]; simp [toTagged, hetag]
  -- `rest'` is `R(m)`, possibly with the other one of `op₁`, `op₂` inserted
  have hu : toTagged p₃ m rest' = tagged true (pre R m) ∨ ∃ y ∈ rest',
      (y.1 = (p₁, 0) ∨ y.1 = (p₂, n)) ∧ y.1 ≠ e.1 ∧
        toTagged p₃ m rest' ∈ OptIns (tagged true (pre R m)) (false, y.2) := by
    by_cases hex : ∃ y ∈ rest', tagR p₃ m y = false
    · obtain ⟨y, hy, hyt⟩ := hex
      have hyrest : y ∈ rest := by rw [hre]; exact List.mem_cons_of_mem _ hy
      have hy12 : y.1 = (p₁, 0) ∨ y.1 = (p₂, n) := by
        rcases hrestKind y hyrest with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · rw [hyt] at h; exact absurd h (by simp)
      have hyne : y.1 ≠ e.1 := fun h => hnotin (h ▸ List.mem_map.2 ⟨y, hy, rfl⟩)
      obtain ⟨s, t, hst⟩ := List.append_of_mem hy
      have hndst : (s.map Prod.fst ++ y.1 :: t.map Prod.fst).Nodup := by
        have := hndr'; rw [hst] at this; simpa using this
      have hall : ∀ z ∈ s ++ t, tagR p₃ m z = true := by
        intro z hz
        have hzr : z ∈ rest' := by
          rw [hst]; rcases List.mem_append.1 hz with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        rcases hrestKind z (by rw [hre]; exact List.mem_cons_of_mem _ hzr) with h | h | h
        · exfalso
          have hz' : z.1 = e.1 ∨ z.1 = y.1 := by
            rcases he12 with h' | h' <;> rcases hy12 with h'' | h''
            · exact absurd (h''.trans h'.symm) hyne
            · exact Or.inl (h.trans h'.symm)
            · exact Or.inr (h.trans h''.symm)
            · exact absurd (h''.trans h'.symm) hyne
          rcases hz' with hz' | hz'
          · exact hnotin (hz' ▸ List.mem_map.2 ⟨z, hzr, rfl⟩)
          · rcases List.mem_append.1 hz with hz | hz
            · exact (List.nodup_append.1 hndst).2.2 _ (List.mem_map.2 ⟨z, hz, rfl⟩) _
                (List.mem_cons_self) hz'
            · have := (List.nodup_append.1 hndst).2.1
              rw [List.nodup_cons] at this
              exact this.1 (hz' ▸ List.mem_map.2 ⟨z, hz, rfl⟩)
        · exfalso
          have hz' : z.1 = e.1 ∨ z.1 = y.1 := by
            rcases he12 with h' | h' <;> rcases hy12 with h'' | h''
            · exact absurd (h''.trans h'.symm) hyne
            · exact Or.inr (h.trans h''.symm)
            · exact Or.inl (h.trans h'.symm)
            · exact absurd (h''.trans h'.symm) hyne
          rcases hz' with hz' | hz'
          · exact hnotin (hz' ▸ List.mem_map.2 ⟨z, hzr, rfl⟩)
          · rcases List.mem_append.1 hz with hz | hz
            · exact (List.nodup_append.1 hndst).2.2 _ (List.mem_map.2 ⟨z, hz, rfl⟩) _
                (List.mem_cons_self) hz'
            · have := (List.nodup_append.1 hndst).2.1
              rw [List.nodup_cons] at this
              exact this.1 (hz' ▸ List.mem_map.2 ⟨z, hz, rfl⟩)
        · exact h
      have hfst : s ++ t = S'.filter (tagR p₃ m) := by
        rw [← hR', hst, List.filter_append, List.filter_cons, hyt,
          List.filter_eq_self.2 (fun z hz => hall z (List.mem_append_left _ hz)),
          List.filter_eq_self.2 (fun z hz => hall z (List.mem_append_right _ hz))]
        simp
      refine Or.inr ⟨y, hy, hy12, hyne, ?_⟩
      have : toTagged p₃ m rest' = toTagged p₃ m s ++ (false, y.2) :: toTagged p₃ m t := by
        rw [hst]; simp [toTagged, hyt]
      rw [this]
      apply mem_optIns_of_split
      rw [← htagR, ← hfst]; simp [toTagged]
    · push Not at hex
      left
      rw [← htagR, ← hR', List.filter_eq_self.2 (fun z hz => by simpa using hex z hz)]
  -- whichever of `op₁`, `op₂` heads `rest` comes first in `S`
  have hbefore : ∀ x : OpId P, (x = (p₁, 0) ∨ x = (p₂, n)) → x ≠ e.1 → pos S e.1 < pos S x := by
    intro x hx hxe
    by_cases hxin : x ∈ ids ∧ pos S x ≤ k
    · obtain ⟨ex, hex, hex1⟩ := exists_entry hxin.1
      have hW : isW ex = false := by
        rcases hx with h | h <;> simp [hisW, hex1, h, h12]
      have hexr := hinrest ex hex (by rw [hex1]; exact hxin.2) hW
      rw [hre] at hexr
      rcases List.mem_cons.1 hexr with h' | h'
      · exact absurd (by rw [← hex1, h']) hxe
      · have := hhead ex h'; rwa [hex1] at this
    · have : k < pos S x := by
        by_cases hxi : x ∈ ids
        · have := hxin; push Not at this; exact this hxi
        · rw [pos_eq_length_iff.2 hxi]; exact hklen
      omega
  have hdecomp : toTagged p₃ m S = toTagged p₃ m S' ++ toTagged p₃ m S'' := by
    simp only [toTagged, ← List.map_append, hS', hS'', List.take_append_drop]
  have hT2' : ∀ x ∈ toTagged p₃ m S'', x.1 = false := by
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hx
    exact hT2 e' he'
  refine ⟨toTagged p₃ m S', toTagged p₃ m S'', hdecomp, hT2', ?_, ?_⟩
  · -- `op₂ ≺ op₁`: `op₂` heads `rest`
    intro hP
    rw [prec_iff_pos_lt] at hP
    have he2 : e.1 = (p₂, n) := by
      rcases he12 with h | h
      · exfalso
        have := hbefore (p₂, n) (Or.inr rfl) (by rw [h]; exact fun h' => h12 (Prod.ext_iff.1 h').1.symm)
        rw [h] at this; omega
      · exact h
    have hev : e.2 = W n := by rw [hopW e heS hek (by rw [he2]), he2]
    rcases hu with hu | ⟨y, hy, hy12, hyne, hu⟩
    · refine ⟨toTagged p₃ m rest', by rw [hu]; exact self_mem_optIns _ _, ?_⟩
      rw [hT1, hev, pre_succ', tagged_append']
      simp [tagged]
    · have hy1 : y.1 = (p₁, 0) := by
        rcases hy12 with h | h
        · exact h
        · exact absurd (h.trans he2.symm) hyne
      have hyS := hmemS'.1 (hrestS' (by rw [hre]; exact List.mem_cons_of_mem _ hy)).1
      have hyv : y.2 = op := hop1 y hyS.1 hyS.2 hy1
      rw [hyv] at hu
      refine ⟨toTagged p₃ m rest', hu, ?_⟩
      rw [hT1, hev, pre_succ', tagged_append']
      simp [tagged]
  · -- not `op₂ ≺ op₁`: `op₁` heads `rest`
    intro hP
    rw [prec_iff_pos_lt] at hP
    have he1 : e.1 = (p₁, 0) := by
      rcases he12 with h | h
      · exact h
      · exfalso
        have := hbefore (p₁, 0) (Or.inl rfl) (by rw [h]; exact fun h' => h12 (Prod.ext_iff.1 h').1)
        rw [h] at this; exact hP this
    have hev : e.2 = op := hop1 e heS hek he1
    rcases hu with hu | ⟨y, hy, hy12, hyne, hu⟩
    · exact ⟨toTagged p₃ m rest', by rw [hu]; exact self_mem_optIns _ _, by rw [hT1, hev]⟩
    · have hy2 : y.1 = (p₂, n) := by
        rcases hy12 with h | h
        · exact absurd (h.trans he1.symm) hyne
        · exact h
      have hyv : y.2 = W n := by
        have hyS := hmemS'.1 (hrestS' (by rw [hre]; exact List.mem_cons_of_mem _ hy)).1
        rw [hopW y hyS.1 hyS.2
          (by rw [hy2]), hy2]
      rw [hyv] at hu
      exact ⟨toTagged p₃ m rest', hu, by rw [hT1, hev]⟩

end Shape

end Podc.HelpFreeWaitFree
