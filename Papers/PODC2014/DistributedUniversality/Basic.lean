import Papers.PODC2014.DistributedUniversality.Model

/-!
# Step lemmas

The transitions of `stepFn` as named post-states, and a case analysis lemma `stepFn_cases`.
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ}

section Trans
variable (M : Mode) (s : St n k) (i : Fin n)

/-- Initialization line. -/
@[simps] def tInit : St n k :=
  { s with
    loc := Function.update s.loc i
      { s.loc i with pc := startPC M, r := 1, cnt := fun _ => 0, oper := fun _ => (i, 0) }
    lastOp := fun j m => if j = i then some 0 else s.lastOp j m
    invAt := fun j m t => if j = i ∧ t = 0 then some s.time else s.invAt j m t
    opRec := fun r m j => if r = 1 ∧ j = i then some (i, 0) else s.opRec r m j
    time := s.time + 1 }

/-- Line N1, invocation. -/
@[simps] def tN1Inv (m : ℕ) (x : Fin k) : St n k :=
  { s with
    loc := Function.update s.loc i { s.loc i with pc := .n1Resp m }
    acI := fun r b y j => if r = (s.loc i).r ∧ b = false ∧ y = x ∧ j = i then
      some ((s.loc i).oper x) else s.acI r b y j
    time := s.time + 1 }

/-- Line N1, response. -/
@[simps] def tN1Resp (m : ℕ) (x : Fin k) (t : Bool) (v : Op n) : St n k :=
  let l := s.loc i
  let l' : Loc n k := { l with tag := Function.update l.tag x t,
                               acop := Function.update l.acop x v }
  { s with
    loc := Function.update s.loc i
      { l' with pc := if m + 1 < k then .n1Inv (m + 1) else afterN1 l' }
    acR := fun r b y j => if r = l.r ∧ b = false ∧ y = x ∧ j = i then some (t, v)
      else s.acR r b y j
    acFree := fun r b y => if r = l.r ∧ b = false ∧ y = x then
        freeUpd (s.acI l.r false x) (s.acFree l.r false x) i (l.oper x)
      else s.acFree r b y
    finR := fun r y j => if r = l.r ∧ j = i ∧ ¬ m + 1 < k ∧ (∀ z, l'.tag z = true) then
        some (l'.tag y, l'.acop y)
      else s.finR r y j
    time := s.time + 1 }

/-- Line 2 / 2M, invocation. -/
@[simps] def tScInv : St n k :=
  { s with
    loc := Function.update s.loc i { s.loc i with pc := .scResp }
    scI := fun r j => if r = (s.loc i).r ∧ j = i then
      some (if M.ca then (s.loc i).acop else (s.loc i).oper) else s.scI r j
    time := s.time + 1 }

/-- Line 2 / 2M, response. -/
@[simps] def tScResp (d : Fin k → Option (Op n)) : St n k :=
  { s with
    loc := Function.update s.loc i { s.loc i with pc := .acInv 0, scd := d, ord := ordOf d }
    scR := fun r j => if r = (s.loc i).r ∧ j = i then some d else s.scR r j
    time := s.time + 1 }

/-- Lines 3–4, invocation. -/
@[simps] def tAcInv (j : ℕ) (x : Fin k) : St n k :=
  { s with
    loc := Function.update s.loc i { s.loc i with pc := .acResp j }
    acI := fun r b y q => if r = (s.loc i).r ∧ b = true ∧ y = x ∧ q = i then
      some (acVal M (s.loc i) x) else s.acI r b y q
    time := s.time + 1 }

/-- Lines 3–4, response. -/
@[simps] def tAcResp (j : ℕ) (x : Fin k) (t : Bool) (v : Op n) : St n k :=
  let l := s.loc i
  { s with
    loc := Function.update s.loc i
      { l with tag := Function.update l.tag x t,
               acop := Function.update l.acop x v,
               pc := if j + 1 < l.ord.length then .acInv (j + 1) else .collect 0 }
    acR := fun r b y q => if r = l.r ∧ b = true ∧ y = x ∧ q = i then some (t, v)
      else s.acR r b y q
    acFree := fun r b y => if r = l.r ∧ b = true ∧ y = x then
        freeUpd (s.acI l.r true x) (s.acFree l.r true x) i (acVal M l x)
      else s.acFree r b y
    firstL := fun r => if r = l.r ∧ j + 1 = M.ℓ ∧ s.firstL r = none then some i
      else s.firstL r
    finR := fun r y q => if r = l.r ∧ q = i ∧ ¬ j + 1 < l.ord.length then
        some (Function.update l.tag x t y, Function.update l.acop x v y)
      else s.finR r y q
    time := s.time + 1 }

/-- Line 5, one read. -/
@[simps] def tCollect (q : ℕ) (y : Fin n) : St n k :=
  { s with
    loc := Function.update s.loc i
      { s.loc i with pc := if q + 1 < n then .collect (q + 1) else .loc,
                     gs := Function.update (s.loc i).gs y (s.gst y) }
    time := s.time + 1 }

/-- The merged histories of line 7. -/
def mergedHist : Fin k → List (Op n) :=
  fun m => merge (fun q => (s.loc i).gs q m) ((s.loc i).hist m)

/-- Lines 6–13. -/
@[simps] def tLoc : St n k :=
  let l := s.loc i
  let hist' := mergedHist s i
  let done : Fin k → Prop := fun m => (i, l.cnt m) ∈ hist' m
  { s with
    loc := Function.update s.loc i
      { l with pc := if 0 < k then .upd 0 else .write, hist := hist',
               cnt := fun m => if done m then l.cnt m + 1 else l.cnt m }
    lastOp := fun j m => if j = i ∧ done m then some (l.cnt m + 1) else s.lastOp j m
    invAt := fun j m t => if j = i ∧ done m ∧ t = l.cnt m + 1 then some s.time
      else s.invAt j m t
    retH := fun j m t => if j = i ∧ done m ∧ t = l.cnt m then some (hist' m)
      else s.retH j m t
    retAt := fun j m t => if j = i ∧ done m ∧ t = l.cnt m then some s.time
      else s.retAt j m t
    time := s.time + 1 }

/-- The program counter after `upd m`. -/
def updPC (m : ℕ) : PC := if m + 1 < k then .upd (m + 1) else .write

/-- Lines 16, 27 (or L1–L5): the operation is already in the history. -/
@[simps] def tUpdIn (m : ℕ) (x : Fin k) : St n k :=
  let l := s.loc i
  { s with
    loc := Function.update s.loc i
      { l with pc := updPC (k := k) m,
               oper := Function.update l.oper x (nextProp M s.lastOp i x (l.hist x) (l.cnt x)) }
    time := s.time + 1 }

/-- Lines 17–24 when the committed operation is the process' own. -/
@[simps] def tUpdMine (m : ℕ) (x : Fin k) : St n k :=
  let l := s.loc i
  let hx' := l.hist x ++ [l.acop x]
  let c' := l.cnt x + 1
  let lastOp' : Fin n → Fin k → Option ℕ :=
    fun j y => if j = i ∧ y = x then some c' else s.lastOp j y
  { s with
    loc := Function.update s.loc i
      { l with pc := updPC (k := k) m, hist := Function.update l.hist x hx',
               cnt := Function.update l.cnt x c',
               res := (x, l.cnt x) :: l.res,
               oper := Function.update l.oper x (nextProp M lastOp' i x hx' c') }
    G := if l.hist x = s.G x then Function.update s.G x hx' else s.G
    born := if l.hist x = s.G x then Function.update s.born x (s.born x ++ [l.r]) else s.born
    lastOp := lastOp'
    invAt := fun j y t => if j = i ∧ y = x ∧ t = c' then some s.time else s.invAt j y t
    retH := fun j y t => if j = i ∧ y = x ∧ t = l.cnt x then some hx' else s.retH j y t
    time := s.time + 1 }

/-- Lines 17–18, 24 when the committed operation is not the process' own. -/
@[simps] def tUpdOther (m : ℕ) (x : Fin k) : St n k :=
  let l := s.loc i
  let hx' := l.hist x ++ [l.acop x]
  { s with
    loc := Function.update s.loc i
      { l with pc := updPC (k := k) m, hist := Function.update l.hist x hx',
               oper := Function.update l.oper x (nextProp M s.lastOp i x hx' (l.cnt x)) }
    G := if l.hist x = s.G x then Function.update s.G x hx' else s.G
    born := if l.hist x = s.G x then Function.update s.born x (s.born x ++ [l.r]) else s.born
    time := s.time + 1 }

/-- Line 25: adopt. -/
@[simps] def tUpdAdopt (m : ℕ) (x : Fin k) : St n k :=
  let l := s.loc i
  { s with
    loc := Function.update s.loc i
      { l with pc := updPC (k := k) m, oper := Function.update l.oper x (l.acop x) }
    time := s.time + 1 }

/-- Lines 30–31. -/
@[simps] def tWrite : St n k :=
  let l := s.loc i
  { s with
    loc := Function.update s.loc i { l with pc := startPC M, r := l.r + 1, res := [] }
    gst := Function.update s.gst i l.hist
    lin := fun m o => if (s.lin m o).isNone ∧ o ∈ l.hist m then some s.time else s.lin m o
    retAt := fun j m t => if j = i ∧ (m, t) ∈ l.res then some s.time else s.retAt j m t
    opRec := fun r m j => if r = l.r + 1 ∧ j = i then some (l.oper m) else s.opRec r m j
    time := s.time + 1 }

end Trans

/-- Case analysis of a step. -/
theorem stepFn_cases {M : Mode} {s s' : St n k} {a : Act n k} (h : stepFn M s a = some s') :
    let i := a.proc
    let l := s.loc i
    (l.pc = .init ∧ s' = tInit M s i) ∨
    (∃ m, ∃ hm : m < k, l.pc = .n1Inv m ∧ s' = tN1Inv s i m ⟨m, hm⟩) ∨
    (∃ m, ∃ hm : m < k, ∃ t v, l.pc = .n1Resp m ∧ a = .ac i t v ∧
      acOK M.strongAC (s.acI l.r false ⟨m, hm⟩) (s.acR l.r false ⟨m, hm⟩)
        (s.acFree l.r false ⟨m, hm⟩) i (l.oper ⟨m, hm⟩) t v ∧
      s' = tN1Resp s i m ⟨m, hm⟩ t v) ∨
    (l.pc = .scInv ∧ s' = tScInv M s i) ∨
    (∃ d, l.pc = .scResp ∧ a = .sc i d ∧ scOK M.ℓ (s.scI l.r) (s.scR l.r) d ∧
      s' = tScResp s i d) ∨
    (∃ j x, l.pc = .acInv j ∧ l.ord[j]? = some x ∧ s' = tAcInv M s i j x) ∨
    (∃ j x t v, l.pc = .acResp j ∧ l.ord[j]? = some x ∧ a = .ac i t v ∧
      acOK M.strongAC (s.acI l.r true x) (s.acR l.r true x) (s.acFree l.r true x) i
        (acVal M l x) t v ∧
      s' = tAcResp M s i j x t v) ∨
    (∃ q, ∃ hq : q < n, l.pc = .collect q ∧ s' = tCollect s i q ⟨q, hq⟩) ∨
    (l.pc = .loc ∧ s' = tLoc s i) ∨
    (∃ m, ∃ hm : m < k, l.pc = .upd m ∧ l.acop ⟨m, hm⟩ ∈ l.hist ⟨m, hm⟩ ∧
      s' = tUpdIn M s i m ⟨m, hm⟩) ∨
    (∃ m, ∃ hm : m < k, l.pc = .upd m ∧ l.acop ⟨m, hm⟩ ∉ l.hist ⟨m, hm⟩ ∧
      l.tag ⟨m, hm⟩ = true ∧ l.acop ⟨m, hm⟩ = (i, l.cnt ⟨m, hm⟩) ∧
      s' = tUpdMine M s i m ⟨m, hm⟩) ∨
    (∃ m, ∃ hm : m < k, l.pc = .upd m ∧ l.acop ⟨m, hm⟩ ∉ l.hist ⟨m, hm⟩ ∧
      l.tag ⟨m, hm⟩ = true ∧ l.acop ⟨m, hm⟩ ≠ (i, l.cnt ⟨m, hm⟩) ∧
      s' = tUpdOther M s i m ⟨m, hm⟩) ∨
    (∃ m, ∃ hm : m < k, l.pc = .upd m ∧ l.acop ⟨m, hm⟩ ∉ l.hist ⟨m, hm⟩ ∧
      l.tag ⟨m, hm⟩ = false ∧ s' = tUpdAdopt s i m ⟨m, hm⟩) ∨
    (l.pc = .write ∧ s' = tWrite M s i) := by
  intro i l
  rcases a with i' | ⟨i', t, v⟩ | ⟨i', d⟩
  · simp only [stepFn] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact Or.inl ⟨by assumption, rfl⟩
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        exact Or.inr (Or.inl ⟨_, by assumption, by assumption, rfl⟩)
      · simp at h
    · simp only [Option.some.injEq] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by assumption, rfl⟩)))
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, by assumption,
          by assumption, rfl⟩)))))
      · simp at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨_, by assumption, by assumption, rfl⟩)))))))
      · simp at h
    · simp only [Option.some.injEq] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by assumption, rfl⟩))))))))
    · rename_i m hpc
      split at h
      · rename_i hm
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨m, hm, hpc, by assumption, rfl⟩)))))))))
        · split at h
          · split at h
            · simp only [Option.some.injEq] at h; subst h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inl ⟨m, hm, hpc, by assumption, by assumption, by assumption,
                  rfl⟩))))))))))
            · simp only [Option.some.injEq] at h; subst h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr (Or.inl ⟨m, hm, hpc, by assumption, by assumption,
                  by assumption, rfl⟩)))))))))))
          · simp only [Option.some.injEq] at h; subst h
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm, hpc, by assumption,
                Bool.eq_false_iff.mpr ‹_›, rfl⟩))))))))))))
      · simp at h
    · simp only [Option.some.injEq] at h; subst h
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨by assumption, rfl⟩))))))))))))
    · simp at h
  · simp only [stepFn] at h
    split at h
    · rename_i m hpc
      split at h
      · rename_i hm
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact Or.inr (Or.inr (Or.inl ⟨m, hm, t, v, hpc, rfl, by assumption, rfl⟩))
        · simp at h
      · simp at h
    · rename_i j hpc
      split at h
      · rename_i x hx
        split at h
        · simp only [Option.some.injEq] at h; subst h
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨j, x, t, v, hpc, hx, rfl, by assumption, rfl⟩))))))
        · simp at h
      · simp at h
    · simp at h
  · simp only [stepFn] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, by assumption, rfl,
          by assumption, rfl⟩))))
      · simp at h
    · simp at h

/-! ### Merging histories (line 7) -/

theorem foldl_merge_spec {α : Type*} [DecidableEq α] {ι : Type*} (cands : ι → List α)
    (G : List α) (hc : ∀ q, cands q <+: G) :
    ∀ (qs : List ι) (acc : List α), acc <+: G →
      let R := qs.foldl (fun acc q => if acc.isPrefixOf (cands q) then cands q else acc) acc
      R <+: G ∧ acc <+: R ∧ ∀ q ∈ qs, cands q <+: R := by
  intro qs
  induction qs with
  | nil => intro acc hacc; simp [hacc]
  | cons q qs ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    by_cases hp : acc.isPrefixOf (cands q) = true
    · simp only [hp, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih (cands q) (hc q)
      have hp' : acc <+: cands q := (List.isPrefixOf_iff_prefix).1 hp
      refine ⟨h1, hp'.trans h2, ?_⟩
      intro q' hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact h2
      · exact h3 q' hq'
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, h3⟩ := ih acc hacc
      refine ⟨h1, h2, ?_⟩
      intro q' hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      · have hnp : ¬ acc <+: cands q' := fun h' => hp ((List.isPrefixOf_iff_prefix).2 h')
        have : cands q' <+: acc := by
          rcases le_total (cands q').length acc.length with hl | hl
          · exact List.prefix_of_prefix_length_le (hc q') hacc hl
          · exact absurd (List.prefix_of_prefix_length_le hacc (hc q') hl) hnp
        exact this.trans h2
      · exact h3 q' hq'

/-- Line 7 returns a history between `h` and `G` that contains all candidates, when all of them
are prefixes of a common `G`. -/
theorem merge_spec (cands : Fin n → List (Op n)) (h G : List (Op n)) (hh : h <+: G)
    (hc : ∀ q, cands q <+: G) :
    merge cands h <+: G ∧ h <+: merge cands h ∧ ∀ q, cands q <+: merge cands h := by
  obtain ⟨h1, h2, h3⟩ := foldl_merge_spec cands G hc (List.finRange n) h hh
  exact ⟨h1, h2, fun q => h3 q (List.mem_finRange q)⟩

set_option hygiene false in
/-- Case analysis on a step `h : stepFn M s a = some s'`, substituting the post-state. Names:
`hpc` (program counter), `m hm` / `j x hx` / `q hq` (indices), `t v ha hok` (responses),
`d` (SC decision), `hin`, `hnin htag hmine` (lines 16–19). -/
macro "du_step_cases" h:ident : tactic => `(tactic| (rcases stepFn_cases $h with
  ⟨hpc, rfl⟩ | ⟨m, hm, hpc, rfl⟩ | ⟨m, hm, t, v, hpc, ha, hok, rfl⟩ | ⟨hpc, rfl⟩ |
  ⟨d, hpc, ha, hok, rfl⟩ | ⟨j, x, hpc, hx, rfl⟩ | ⟨j, x, t, v, hpc, hx, ha, hok, rfl⟩ |
  ⟨q, hq, hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨m, hm, hpc, hin, rfl⟩ |
  ⟨m, hm, hpc, hnin, htag, hmine, rfl⟩ | ⟨m, hm, hpc, hnin, htag, hmine, rfl⟩ |
  ⟨m, hm, hpc, hnin, htag, rfl⟩ | ⟨hpc, rfl⟩))

/-! ### The order of lines 3–4 -/

theorem ordOf_nodup (d : Fin k → Option (Op n)) : (ordOf d).Nodup := by
  unfold ordOf
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange k).filter _, (List.nodup_finRange k).filter _, ?_⟩
  intro a ha b hb hab
  subst hab
  simp only [List.mem_filter] at ha hb
  cases h : d a <;> simp_all

theorem mem_ordOf (d : Fin k → Option (Op n)) (y : Fin k) : y ∈ ordOf d := by
  unfold ordOf
  cases h : d y <;> simp [h]

theorem length_ordOf (d : Fin k → Option (Op n)) : (ordOf d).length = k := by
  have h1 := (ordOf_nodup d).length_le_card
  have h2 : (List.finRange k).toFinset ⊆ (ordOf d).toFinset := by
    intro y _; simp [mem_ordOf]
  have h3 := Finset.card_le_card h2
  rw [List.toFinset_card_of_nodup (List.nodup_finRange k),
    List.toFinset_card_of_nodup (ordOf_nodup d)] at h3
  simp at h1 h3
  omega

theorem not_mem_take_of_getElem? {α : Type*} {l : List α} (hl : l.Nodup) {j : ℕ} {x : α}
    (hx : l[j]? = some x) : x ∉ l.take j := by
  intro hmem
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hmem
  rw [List.getElem_take] at hix
  have hi' : i < j := by simp at hi; omega
  have := (List.Nodup.getElem_inj_iff hl).1 hix
  omega

theorem take_succ_of_getElem? {α : Type*} {l : List α} {j : ℕ} {x : α} (hx : l[j]? = some x) :
    l.take (j + 1) = l.take j ++ [x] := by
  rw [List.take_succ, hx]; rfl

/-! ### Frame lemmas -/

section Frame
variable {M : Mode} {s s' : St n k} {a : Act n k}

theorem loc_ne (h : stepFn M s a = some s') {j : Fin n} (hj : j ≠ a.proc) :
    s'.loc j = s.loc j := by
  du_step_cases h <;> simp [Function.update_of_ne hj]

theorem r_mono (h : stepFn M s a = some s') (h0 : ∀ i, (s.loc i).pc = .init → (s.loc i).r = 0)
    (j : Fin n) : (s.loc j).r ≤ (s'.loc j).r := by
  by_cases hj : j = a.proc
  · subst hj
    du_step_cases h <;> first | simp [h0 _ hpc] | simp
  · rw [loc_ne h hj]

theorem r_post (h : stepFn M s a = some s') :
    (s'.loc a.proc).r = if (s.loc a.proc).pc = .init then 1
      else if (s.loc a.proc).pc = .write then (s.loc a.proc).r + 1 else (s.loc a.proc).r := by
  du_step_cases h <;> simp [hpc]

theorem acR_ne (h : stepFn M s a = some s') {j : Fin n} (hj : j ≠ a.proc) (r b y) :
    s'.acR r b y j = s.acR r b y j := by
  du_step_cases h <;> simp [hj]

theorem acI_ne (h : stepFn M s a = some s') {j : Fin n} (hj : j ≠ a.proc) (r b y) :
    s'.acI r b y j = s.acI r b y j := by
  du_step_cases h <;> simp [hj]

theorem scI_ne (h : stepFn M s a = some s') {j : Fin n} (hj : j ≠ a.proc) (r) :
    s'.scI r j = s.scI r j := by
  du_step_cases h <;> simp [hj]

theorem scR_ne (h : stepFn M s a = some s') {j : Fin n} (hj : j ≠ a.proc) (r) :
    s'.scR r j = s.scR r j := by
  du_step_cases h <;> simp [hj]

theorem finR_ne (h : stepFn M s a = some s') {j : Fin n} (hj : j ≠ a.proc) (r y) :
    s'.finR r y j = s.finR r y j := by
  du_step_cases h <;> simp [hj]

theorem opRec_ne (h : stepFn M s a = some s') {j : Fin n} (hj : j ≠ a.proc) (r y) :
    s'.opRec r y j = s.opRec r y j := by
  du_step_cases h <;> simp [hj]

end Frame

end Podc.DistributedUniversality
