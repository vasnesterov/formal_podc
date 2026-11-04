import Papers.PODC2013.TMObservationalRefinement.Sufficiency

/-!
# Necessity of the opacity relation, for refinement with respect to traces (Section 7, repaired)

Theorem 24 of the paper (observational refinement with respect to *states* implies the opacity
relation) is false. Its repair, as in the journal version (JACM 2017, Section 7.1), is necessity
from observational refinement with respect to *traces* (Definition 15).

* `TraceNec.opac_of_rt`: two histories with the same per-thread projections, the second
  preserving the real-time order of the first (`RT`), are related by `⊑` (Definition 4).
* `trace_necessity`: `H_C ⊑_trace H_A ⟹ H_C ⊑ H_A` (all histories, pending ones included);
  `trace_necessity_complete`: the version for complete histories.
* `theorem_16_repaired`: for transactional systems, `H_C ⊑ H_A ⟺ H_C ⊑_trace H_A`.

The proof follows Lemma 7.1 / Figure 15 of the journal version, simplified for trace observation:
for `H ∈ H_C` we build a program `P_H` whose thread `t` executes, for each of its transactions in
`H|t`, an atomic block with exactly the calls of that transaction (parameters taken from `H`),
preceded and followed by non-transactional *marker* assignments `x := v` with values unique in the
trace. A trace `τ` of `P_H` with `history τ = H` exists; refinement gives `τ' ∼ τ` with
`history τ' ∈ H_A`. Per-thread equality gives the per-thread projections of `history τ'`, and the
markers, being non-transactional, are ordered in `τ'` as in `τ`; this transfers the real-time order.
-/

namespace Podc.TMObservationalRefinement

open IKind Act Lang CmdClass TState

namespace TraceNec

variable {T LV GV O M BE IE C : Type} [Lang T LV GV BE IE C]

/-! ### List helpers -/

lemma prefix_append_cases {α : Type} {L A X : List α} (h : L <+: A ++ X) :
    L <+: A ∨ ∃ X', X' <+: X ∧ L = A ++ X' := by
  obtain ⟨r, hr⟩ := h
  rcases List.append_eq_append_iff.mp hr with ⟨a', h1, -⟩ | ⟨c', h1, h2⟩
  · exact Or.inl ⟨a', h1.symm⟩
  · exact Or.inr ⟨c', ⟨r, h2.symm⟩, h1⟩

/-! ### Primitive commands used by `P_H` -/

section cmds

lemma sem_eq_of_isAssume {c : C}
    (hc : IsAssume (T := T) (LV := LV) (GV := GV) (BE := BE) (IE := IE) c)
    (s s' : State T LV GV) (h : s' ∈ sem c s) : s' = s := by
  obtain ⟨t, ⟨b, p, rfl⟩ | ⟨e, n, rfl⟩⟩ := hc
  · rw [sem_assume] at h; exact h.1
  · rw [sem_assumeEq] at h; exact h.1

lemma assign_not_isAssume (u : T) (x : LV) (v : ℤ) :
    ¬ IsAssume (T := T) (LV := LV) (GV := GV) (BE := BE) (IE := IE) (assign u x v : C) := by
  intro hc
  have := sem_eq_of_isAssume hc (fun _ => v + 1) _ (by rw [sem_assign]; rfl)
  have := congrFun this (.inr (u, x))
  simp at this

lemma assign_inj {u : T} {x : LV} {v w : ℤ} (h : (assign u x v : C) = assign u x w) : v = w := by
  have h1 := sem_assign (C := C) u x v (fun _ => 0)
  rw [h, sem_assign] at h1
  have := congrFun (Set.singleton_eq_singleton_iff.mp h1) (.inr (u, x))
  simpa using this.symm

lemma assumeEq_ne_assign (u u' : T) (e : IE) (n : ℤ) (x : LV) (v : ℤ) :
    (assumeEq u e n : C) ≠ assign u' x v := by
  intro h
  exact assign_not_isAssume (T := T) (BE := BE) (IE := IE) (GV := GV) u' x v
    ⟨u, Or.inr ⟨e, n, h.symm⟩⟩

end cmds

section markers

variable [Inhabited LV]

/-- The action `x := v` of thread `u`, on the default local variable `x`. -/
def mk (u : T) (v : ℤ) : Act T O M C := .cmd u (assign u (default : LV) v)

lemma mk_inj {u : T} {v w : ℤ} : (mk u v : Act T O M C) = mk u w ↔ v = w := by
  constructor
  · intro h; simp only [mk, Act.cmd.injEq, true_and] at h; exact assign_inj h
  · rintro rfl; rfl

variable (B : ℤ)

/-- The part of the trace of `P_H` contributed by an interface action `(u, k)` that is the `i`-th
action of thread `u` in `H`. Markers are `x := B + 2i` (before `txbegin`) and `x := B + 2i + 1`
(after `committed`/`aborted`); `B` exceeds all other values assigned in the trace. -/
def chunk (u : T) (k : IKind O M) (i : ℕ) : List (Act T O M C) :=
  match k with
  | txbegin => [mk u (B + 2 * i), iface u txbegin]
  | ok => [iface u ok, mk u 0]
  | call o f n => [cmd u (assumeEq u (cst C n) n), iface u (call o f n)]
  | ret n o f => [iface u (ret n o f), mk u n]
  | txcommit => [iface u txcommit]
  | committed => [iface u committed, mk u (vCom C), mk u (B + 2 * i + 1)]
  | aborted => [iface u aborted, mk u (vAb C), mk u (B + 2 * i + 1)]

/-- The trace of thread `u` for its actions `l` (the first being its `i`-th action). -/
def expandT (u : T) : ℕ → List (IKind O M) → List (Act T O M C)
  | _, [] => []
  | i, k :: l => chunk B u k i ++ expandT u (i + 1) l

lemma chunk_thread (u : T) (k : IKind O M) (i : ℕ) :
    ∀ a ∈ (chunk B u k i : List (Act T O M C)), a.thread = u := by
  cases k <;> simp [chunk, mk]

lemma history_chunk (u : T) (k : IKind O M) (i : ℕ) :
    history (chunk B u k i : List (Act T O M C)) = [(u, k)] := by
  cases k <;> simp [chunk, mk]

lemma expandT_thread (u : T) (i : ℕ) (l : List (IKind O M)) :
    ∀ a ∈ (expandT B u i l : List (Act T O M C)), a.thread = u := by
  induction l generalizing i with
  | nil => simp [expandT]
  | cons k l ih =>
    intro a ha
    simp only [expandT, List.mem_append] at ha
    rcases ha with ha | ha
    · exact chunk_thread B u k i a ha
    · exact ih _ a ha

lemma history_expandT (u : T) (i : ℕ) (l : List (IKind O M)) :
    history (expandT B u i l : List (Act T O M C)) = l.map (fun k => (u, k)) := by
  induction l generalizing i with
  | nil => rfl
  | cons k l ih => simp [expandT, history_chunk, ih]

lemma expandT_append (u : T) (i : ℕ) (l₁ l₂ : List (IKind O M)) :
    (expandT B u i (l₁ ++ l₂) : List (Act T O M C)) =
      expandT B u i l₁ ++ expandT B u (i + l₁.length) l₂ := by
  induction l₁ generalizing i with
  | nil => simp [expandT]
  | cons k l ih =>
    simp only [List.cons_append, expandT, ih, List.append_assoc, List.length_cons]
    congr 3; omega

@[simp] lemma mk_ne_iface (u w : T) (v : ℤ) (k : IKind O M) :
    (mk u v : Act T O M C) ≠ iface w k := by simp [mk]

@[simp] lemma mk_ne_assumeEq (u w : T) (v : ℤ) (e : IE) (n : ℤ) :
    (mk u v : Act T O M C) ≠ cmd w (assumeEq w e n) := by
  simp only [mk, ne_eq, Act.cmd.injEq, not_and]
  intro _ h; exact assumeEq_ne_assign w u e n default v h.symm

@[simp] lemma mk_inj' {u : T} {v w : ℤ} : (mk u v : Act T O M C) = mk u w ↔ v = w := mk_inj

/-- All values returned by `ret` actions in `l` are below `B`. -/
def RetLt (B : ℤ) (l : List (IKind O M)) : Prop := ∀ n o f, ret n o f ∈ l → n < B

/-- `B` exceeds the other values assigned in the traces of `P_H`. -/
def BigB (C : Type) [Lang T LV GV BE IE C] (B : ℤ) : Prop := vCom C < B ∧ vAb C < B ∧ 0 < B

lemma chunk_mk {u : T} {k : IKind O M} {i : ℕ} {v : ℤ} (hB : BigB C B)
    (hk : ∀ n o f, k = ret n o f → n < B) (h : (mk u v : Act T O M C) ∈ chunk B u k i) :
    v < B ∨ v = B + 2 * i ∨ v = B + 2 * i + 1 := by
  obtain ⟨h1, h2, h3⟩ := hB
  cases k with
  | ret n o f => simp [chunk] at h; exact Or.inl (h ▸ hk n o f rfl)
  | _ => simp [chunk] at h <;> omega

lemma retLt_cons {k : IKind O M} {l : List (IKind O M)} (h : RetLt B (k :: l)) :
    (∀ n o f, k = ret n o f → n < B) ∧ RetLt B l :=
  ⟨fun n o f hk => h n o f (by simp [hk]), fun n o f hm => h n o f (by simp [hm])⟩

/-- A begin marker `x := B + 2j` occurs in `expandT B u i l` only for `j < i + |l|`. -/
lemma lt_of_beginMarker {u : T} {j : ℕ} (hB : BigB C B) :
    ∀ (i : ℕ) (l : List (IKind O M)), RetLt B l →
      (mk u (B + 2 * j) : Act T O M C) ∈ expandT B u i l → j < i + l.length
  | i, [], _, h => by simp [expandT] at h
  | i, k :: l, hr, h => by
    obtain ⟨hk, hl⟩ := retLt_cons B hr
    simp only [expandT, List.mem_append] at h
    rcases h with h | h
    · have := chunk_mk B hB hk h; simp; omega
    · have := lt_of_beginMarker hB (i + 1) l hl h; simp; omega

lemma history_ne_nil_of_prefix_chunk {u : T} {k : IKind O M} {i j : ℕ} {L : List (Act T O M C)}
    (hB : BigB C B) (hk : ∀ n o f, k = ret n o f → n < B) (hL : L <+: chunk B u k i)
    (hm : (mk u (B + 2 * j + 1) : Act T O M C) ∈ L) : j = i ∧ history L ≠ [] := by
  have hj := chunk_mk B hB hk (hL.subset hm)
  have hji : j = i := by omega
  refine ⟨hji, ?_⟩
  have hmem := hL.subset hm
  cases k with
  | txbegin => simp [chunk] at hmem; omega
  | call o f n => simp [chunk] at hmem
  | _ =>
    obtain ⟨r, hr⟩ := hL
    rcases L with _ | ⟨a, L⟩
    · simp at hm
    · simp [chunk] at hr; obtain ⟨rfl, -⟩ := hr; simp

/-- If an end marker `x := B + 2j + 1` occurs in a prefix `L` of `expandT B u i l`, then `L`
contains more than `j - i` interface actions. -/
lemma lt_of_endMarker_prefix {u : T} {j : ℕ} (hB : BigB C B) :
    ∀ (i : ℕ) (l : List (IKind O M)) (L : List (Act T O M C)), RetLt B l →
      L <+: expandT B u i l → mk u (B + 2 * j + 1) ∈ L → j < i + (history L).length
  | i, [], L, _, hL, hm => by
    have : L = [] := List.prefix_nil.mp hL
    subst this; simp at hm
  | i, k :: l, L, hr, hL, hm => by
    obtain ⟨hk, hl⟩ := retLt_cons B hr
    rcases prefix_append_cases hL with hL | ⟨X', hX', rfl⟩
    · obtain ⟨rfl, hne⟩ := history_ne_nil_of_prefix_chunk B hB hk hL hm
      have := List.length_pos_of_ne_nil hne
      omega
    · rw [history_append, history_chunk, List.length_append]
      simp only [List.mem_append] at hm
      rcases hm with hm | hm
      · have := chunk_mk B hB hk hm; simp; omega
      · have := lt_of_endMarker_prefix hB (i + 1) l X' hl hX' hm; simp; omega

variable [DecidableEq T]

/-- The trace of `P_H` for the history `H`; `c u` counts the actions of `u` already expanded. -/
def expand : (T → ℕ) → List (IAct T O M) → List (Act T O M C)
  | _, [] => []
  | c, (u, k) :: H => chunk B u k (c u) ++ expand (Function.update c u (c u + 1)) H

lemma history_expand (c : T → ℕ) (H : List (IAct T O M)) :
    history (expand B c H : List (Act T O M C)) = H := by
  induction H generalizing c with
  | nil => rfl
  | cons a H ih => obtain ⟨u, k⟩ := a; simp [expand, history_chunk, ih]

lemma tproj_chunk (w u : T) (k : IKind O M) (i : ℕ) :
    tproj w (chunk B u k i : List (Act T O M C)) = if u = w then chunk B u k i else [] := by
  split_ifs with h
  · exact List.filter_eq_self.mpr (fun a ha => by simp [chunk_thread B u k i a ha, h])
  · exact List.filter_eq_nil_iff.mpr (fun a ha => by simp [chunk_thread B u k i a ha, h])

lemma tproj_expand (c : T → ℕ) (H : List (IAct T O M)) (w : T) :
    tproj w (expand B c H : List (Act T O M C)) = expandT B w (c w) (proj w H) := by
  induction H generalizing c with
  | nil => rfl
  | cons a H ih =>
    obtain ⟨u, k⟩ := a
    simp only [expand, tproj_append, tproj_chunk, ih]
    by_cases h : u = w
    · subst h; simp [proj, expandT]
    · simp [proj, h, Function.update_of_ne (Ne.symm h)]

lemma expand_append (c : T → ℕ) (H₁ H₂ : List (IAct T O M)) :
    ∃ c', (expand B c (H₁ ++ H₂) : List (Act T O M C)) = expand B c H₁ ++ expand B c' H₂ := by
  induction H₁ generalizing c with
  | nil => exact ⟨c, rfl⟩
  | cons a H ih =>
    obtain ⟨u, k⟩ := a
    obtain ⟨c', hc'⟩ := ih (Function.update c u (c u + 1))
    exact ⟨c', by simp [expand, hc']⟩

/-- The end marker of the `a`-th action of `l` (a `committed`/`aborted` action) is
non-transactional in `expandT B u i l`, whatever the initial status. -/
lemma endMarker_mem_ann (u : T) :
    ∀ (l : List (IKind O M)) (a i : ℕ) (k : IKind O M) (st : T → Bool), l[a]? = some k →
      k.isEnd = true → ((mk u (B + 2 * ((i + a : ℕ) : ℤ) + 1) : Act T O M C), false) ∈
        ann st (expandT B u i l)
  | [], a, i, k, st, h, _ => by simp at h
  | k₀ :: l, 0, i, k, st, h, hk => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [expandT, ann_append, List.mem_append]
    left
    cases k₀ <;> simp [isEnd] at hk <;> simp [chunk, mk, flag, upd, Act.isBoundA]
  | k₀ :: l, a + 1, i, k, st, h, hk => by
    simp only [List.getElem?_cons_succ] at h
    rw [expandT, ann_append, List.mem_append]
    right
    have e : i + (a + 1) = (i + 1) + a := by omega
    rw [e]
    exact endMarker_mem_ann u l a (i + 1) k _ h hk

lemma stAfter_expandT (u : T) (i : ℕ) (l : List (IKind O M)) (st : T → Bool) (q₀ q : TState O M)
    (hs : st u = q₀.inside) (hr : run q₀ l = some q) :
    stAfter st (expandT B u i l : List (Act T O M C)) u = q.inside := by
  refine stAfter_eq_inside u _ st q₀ q (expandT_thread B u i l) hs ?_
  rw [history_expandT, List.map_map]
  simpa using hr

/-! ### The program `P_H` -/

/-- Every complete per-thread history `l` from the idle state is produced (as `expandT B u j l`,
up to an extension) by an allowed command. -/
def IdleOK (C : Type) [Lang T LV GV BE IE C] (u : T) (l : List (IKind O M)) : Prop :=
  ∀ j, run idle l = some idle → ∃ (Cm : Cmd LV O M C BE IE) (ext : List (Act T O M C)),
    Cm.Allowed u false ∧ Tr u Cm (expandT B u j l ++ ext)

omit [DecidableEq T] in
lemma allowed_prim_mk (u : T) (ins : Bool) (v : ℤ) :
    (Cmd.prim (assign u (default : LV) v : C) : Cmd LV O M C BE IE).Allowed u ins := by
  simp [Cmd.Allowed, assign_not_isAssume]

omit [DecidableEq T] in
lemma not_ends_aborted {u : T} {τb : List (Act T O M C)} (h : ∃ τ₀ c, τb = τ₀ ++ [cmd u c]) :
    ∀ τ', τb ≠ τ' ++ [iface u aborted] := by
  obtain ⟨τ₀, c, rfl⟩ := h
  intro τ' he
  have := (List.append_inj' he rfl).2
  simp at this

omit [DecidableEq T] in
/-- The atomic-block phase: the block has body `Cb` so far (trace `τb`), and the rest of the
thread's history is `l`, starting inside the transaction. -/
theorem tx_phase (u : T) : ∀ (l : List (IKind O M)) (i : ℕ) (Cb : Cmd LV O M C BE IE)
    (τb : List (Act T O M C)),
    (∀ l' : List (IKind O M), l'.length < l.length → IdleOK B C u l') →
    run inTx l = some idle → Tr u Cb τb → Cb.Allowed u true → (∃ τ₀ c, τb = τ₀ ++ [cmd u c]) →
    ∃ (Cm : Cmd LV O M C BE IE) (ext : List (Act T O M C)), Cm.Allowed u false ∧
      Tr u Cm (iface u txbegin :: iface u ok :: (τb ++ expandT B u i l ++ ext))
  | [], _, _, _, _, hr, _, _, _ => by simp at hr
  | [k], _, _, _, _, hr, _, _, _ => by cases k <;> simp [step] at hr
  | k₁ :: k₂ :: l, i, Cb, τb, hI, hr, hT, hA, hend => by
    have hI' : ∀ l' : List (IKind O M), l'.length ≤ l.length → IdleOK B C u l' :=
      fun l' hl' => hI l' (by simp; omega)
    cases k₁ with
    | call o f n =>
      cases k₂ with
      | ret n' o' f' =>
        simp only [run_cons, step, Option.bind_some] at hr
        split_ifs at hr with ho
        · obtain ⟨rfl, rfl⟩ := ho
          simp only [Option.bind_some] at hr
          obtain ⟨Cm, ext, hCA, hCT⟩ := tx_phase u l (i + 1 + 1)
            (.seq Cb (.call default o' f' (cst C n)))
            (τb ++ [cmd u (assumeEq u (cst C n) n), iface u (call o' f' n), iface u (ret n' o' f'),
              cmd u (assign u default n')])
            (fun l' hl' => hI' l' hl'.le) hr (Tr.seq hT (Tr.callRet n n'))
            ⟨hA, rfl⟩ ⟨τb ++ [cmd u (assumeEq u (cst C n) n), iface u (call o' f' n),
              iface u (ret n' o' f')], assign u default n', by simp⟩
          refine ⟨Cm, ext, hCA, ?_⟩
          simpa [expandT, chunk, mk] using hCT
        · simp at hr
      | aborted =>
        simp only [run_cons, step, Option.bind_some] at hr
        obtain ⟨Cm₂, ext, hA₂, hT₂⟩ := hI' l le_rfl (i + 1 + 1) hr
        refine ⟨.seq (.atomic default (.seq Cb (.call default o f (cst C n))))
          (.seq (.prim (assign u default (B + 2 * ((i + 1 : ℕ) : ℤ) + 1))) Cm₂), ext, ?_, ?_⟩
        · simp [Cmd.Allowed, hA, hA₂, assign_not_isAssume]
        · have h1 := Tr.atomicAbort (x := (default : LV))
            (τ := τb ++ [cmd u (assumeEq u (cst C n) n), iface u (call o f n)])
            (by simpa using Tr.seq hT (Tr.callAbort (x := (default : LV)) (o := o) (f := f) n))
          have h2 := Tr.seq h1 (Tr.seq (Tr.prim (t := u)
            (assign u (default : LV) (B + 2 * ((i + 1 : ℕ) : ℤ) + 1))) hT₂)
          simpa [expandT, chunk, mk] using h2
      | _ => simp [step] at hr
    | txcommit =>
      cases k₂ with
      | committed =>
        simp only [run_cons, step, Option.bind_some] at hr
        obtain ⟨Cm₂, ext, hA₂, hT₂⟩ := hI' l le_rfl (i + 1 + 1) hr
        refine ⟨.seq (.atomic default Cb)
          (.seq (.prim (assign u default (B + 2 * ((i + 1 : ℕ) : ℤ) + 1))) Cm₂), ext, ?_, ?_⟩
        · simp [Cmd.Allowed, hA, hA₂, assign_not_isAssume]
        · have h1 := Tr.atomicCommit (x := (default : LV)) hT (not_ends_aborted hend)
          have h2 := Tr.seq h1 (Tr.seq (Tr.prim (t := u)
            (assign u (default : LV) (B + 2 * ((i + 1 : ℕ) : ℤ) + 1))) hT₂)
          simpa [expandT, chunk, mk] using h2
      | aborted =>
        simp only [run_cons, step, Option.bind_some] at hr
        obtain ⟨Cm₂, ext, hA₂, hT₂⟩ := hI' l le_rfl (i + 1 + 1) hr
        refine ⟨.seq (.atomic default Cb)
          (.seq (.prim (assign u default (B + 2 * ((i + 1 : ℕ) : ℤ) + 1))) Cm₂), ext, ?_, ?_⟩
        · simp [Cmd.Allowed, hA, hA₂, assign_not_isAssume]
        · have h1 := Tr.atomicCommitAbort (x := (default : LV)) hT (not_ends_aborted hend)
          have h2 := Tr.seq h1 (Tr.seq (Tr.prim (t := u)
            (assign u (default : LV) (B + 2 * ((i + 1 : ℕ) : ℤ) + 1))) hT₂)
          simpa [expandT, chunk, mk] using h2
      | _ => simp [step] at hr
    | _ => simp [step] at hr

omit [DecidableEq T] in
/-- The idle phase: complete per-thread histories are produced by allowed commands. -/
theorem idle_ok (u : T) : ∀ l : List (IKind O M), IdleOK B C (LV := LV) (BE := BE) (IE := IE) u l
  | [] => fun j _ => ⟨.prim (assign u default 0), [mk u 0], allowed_prim_mk u false 0,
      by simpa [expandT, mk] using Tr.prim (t := u) (assign u (default : LV) 0 : C)⟩
  | [k] => fun j hr => by cases k <;> simp [step] at hr
  | k₁ :: k₂ :: l => fun j hr => by
    cases k₁ with
    | txbegin =>
      cases k₂ with
      | ok =>
        simp only [run_cons, step, Option.bind_some] at hr
        obtain ⟨Cm, ext, hA, hT⟩ := tx_phase B u l (j + 1 + 1) (.prim (assign u default 0))
          [mk u 0] (fun l' _ => idle_ok u l') hr (Tr.prim _) (allowed_prim_mk u true 0)
          ⟨[], _, rfl⟩
        refine ⟨.seq (.prim (assign u default (B + 2 * (j : ℤ)))) Cm, ext, ?_, ?_⟩
        · simp [Cmd.Allowed, hA, assign_not_isAssume]
        · have h2 := Tr.seq (Tr.prim (t := u) (assign u (default : LV) (B + 2 * (j : ℤ)))) hT
          simpa [expandT, chunk, mk] using h2
      | _ => simp [step] at hr
    | _ => simp [step] at hr
termination_by l => l.length

omit [DecidableEq T] in
/-- Every per-thread history accepted by the automaton is produced by an allowed command. -/
theorem prog_exists (u : T) (l : List (IKind O M)) (hw : (run idle l).isSome) :
    ∃ (Cm : Cmd LV O M C BE IE) (ext : List (Act T O M C)),
      Cm.Allowed u false ∧ Tr u Cm (expandT B u 0 l ++ ext) := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hw
  have hc : ∃ c : List (IKind O M), run q c = some idle := by
    cases q with
    | idle => exact ⟨[], rfl⟩
    | beginP => exact ⟨[ok, txcommit, committed], by simp [step]⟩
    | inTx => exact ⟨[txcommit, committed], by simp [step]⟩
    | callP o f => exact ⟨[ret 0 o f, txcommit, committed], by simp [step]⟩
    | commitP => exact ⟨[committed], by simp [step]⟩
  obtain ⟨c, hc⟩ := hc
  obtain ⟨Cm, ext, hA, hT⟩ := idle_ok (C := C) (LV := LV) (BE := BE) (IE := IE) B u (l ++ c) 0
    (by rw [run_append, hq]; simpa using hc)
  exact ⟨Cm, _, hA, by rw [expandT_append, List.append_assoc] at hT; exact hT⟩

end markers

/-! ### Opacity from per-thread equality and preserved real-time order -/

section rt

variable [DecidableEq T]

/-- The number of actions of thread `t` in `L`. -/
def cnt (t : T) (L : List (IAct T O M)) : ℕ := (proj t L).length

lemma proj_append' (t : T) (A B : List (IAct T O M)) : proj t (A ++ B) = proj t A ++ proj t B := by
  simp [proj]

lemma proj_cons' (t : T) (x : IAct T O M) (L : List (IAct T O M)) :
    proj t (x :: L) = if x.1 = t then x.2 :: proj t L else proj t L := by
  by_cases h : x.1 = t <;> simp [proj, h]

lemma proj_eq_nil_of {t : T} {A : List (IAct T O M)} (h : ∀ x ∈ A, x.1 ≠ t) : proj t A = [] := by
  simp only [proj, List.map_eq_nil_iff]
  exact List.filter_eq_nil_iff.mpr (fun x hx => by simpa using h x hx)

/-- `RT H S`: the real-time order of `H` (a `committed`/`aborted` action before a `txbegin`
action) is preserved in `S`. Actions are identified by thread and per-thread index: `a` is the
`a`-th action of `t'`; "`x` precedes `y`" is "some prefix contains `x` but not `y`". -/
def RT (H S : List (IAct T O M)) : Prop :=
  ∀ (t' t : T) (a b : ℕ), (∃ k, (proj t' H)[a]? = some k ∧ k.isEnd = true) →
    (proj t H)[b]? = some txbegin →
    (∃ H₁, H₁ <+: H ∧ a < cnt t' H₁ ∧ cnt t H₁ ≤ b) →
    ∃ S₁, S₁ <+: S ∧ a < cnt t' S₁ ∧ cnt t S₁ ≤ b

lemma split_first {t : T} {k : IKind O M} {rest : List (IKind O M)} :
    ∀ {H : List (IAct T O M)}, proj t H = k :: rest →
      ∃ A B, H = A ++ (t, k) :: B ∧ (∀ x ∈ A, x.1 ≠ t) ∧ proj t B = rest
  | [], h => by simp [proj] at h
  | x :: H, h => by
    rw [proj_cons'] at h
    split_ifs at h with hx
    · obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact ⟨[], H, by simp [← hx], by simp, rfl⟩
    · obtain ⟨A, B, rfl, hA, hB⟩ := split_first h
      exact ⟨x :: A, B, rfl, by simpa [hx] using hA, hB⟩

lemma proj_insert (u t₀ : T) (k : IKind O M) (A B : List (IAct T O M)) (hA : ∀ x ∈ A, x.1 ≠ t₀) :
    proj u (A ++ (t₀, k) :: B) = (if t₀ = u then [k] else []) ++ proj u (A ++ B) := by
  by_cases h : t₀ = u
  · subst h
    simp [proj_append', proj_cons', proj_eq_nil_of hA]
  · simp [proj_append', proj_cons', h]

lemma cnt_insert (u t₀ : T) (k : IKind O M) (A B : List (IAct T O M)) (hA : ∀ x ∈ A, x.1 ≠ t₀) :
    cnt u (A ++ (t₀, k) :: B) = (if t₀ = u then 1 else 0) + cnt u (A ++ B) := by
  simp only [cnt, proj_insert u t₀ k A B hA, List.length_append]
  split_ifs <;> simp

lemma cnt_cons (u : T) (x : IAct T O M) (L : List (IAct T O M)) :
    cnt u (x :: L) = (if x.1 = u then 1 else 0) + cnt u L := by
  simp only [cnt, proj_cons']
  split_ifs <;> simp; omega

lemma getElem?_insert (u t₀ : T) (k : IKind O M) (A B : List (IAct T O M))
    (hA : ∀ x ∈ A, x.1 ≠ t₀) (n : ℕ) :
    (proj u (A ++ (t₀, k) :: B))[n + if t₀ = u then 1 else 0]? = (proj u (A ++ B))[n]? := by
  rw [proj_insert u t₀ k A B hA]
  split_ifs <;> simp

/-- Two histories with the same per-thread projections, the second preserving the real-time
order of the first, are related by the opacity relation (Definition 4). -/
theorem opac_of_rt : ∀ (S H : List (IAct T O M)), (∀ t, proj t H = proj t S) → RT H S → Opac H S
  | [], H, hp, _ => by
    have : H = [] := by
      rcases H with _ | ⟨x, H⟩
      · rfl
      · have := hp x.1; simp [proj] at this
    subst this; exact (opac_nil_left []).mpr rfl
  | (t₀, k) :: S, H, hp, hrt => by
    have h0 : proj t₀ H = k :: proj t₀ S := by rw [hp]; simp [proj_cons']
    obtain ⟨A, B, rfl, hA, hB⟩ := split_first h0
    refine Opac.cons_intro ?_ (opac_of_rt S (A ++ B) ?_ ?_)
    · -- no action of `A` must precede `(t₀, k)`
      rintro x hx (h1 | ⟨he, hb⟩)
      · exact hA x hx h1
      obtain ⟨A₁, A₂, rfl⟩ := List.append_of_mem hx
      have hA₁ : ∀ y ∈ A₁, y.1 ≠ t₀ := fun y hy => hA y (by simp [hy])
      obtain ⟨S₁, hS₁, h1, h2⟩ := hrt x.1 t₀ (cnt x.1 A₁) 0
        ⟨x.2, by simp [proj_append', proj_cons', cnt], he⟩
        (by simp only at hb; subst hb; simp [proj_append', proj_cons', hA x hx,
          proj_eq_nil_of hA₁,
          proj_eq_nil_of (fun y hy => hA y (by simp [hy]) : ∀ y ∈ A₂, y.1 ≠ t₀)])
        ⟨A₁ ++ [x], ⟨A₂ ++ (t₀, k) :: B, by simp⟩, by simp [cnt, proj_append', proj_cons'],
          by
            rw [cnt, proj_append', proj_cons', proj_eq_nil_of hA₁]; simp [hA x hx, proj]⟩
      rcases List.prefix_cons_iff.mp hS₁ with rfl | ⟨S₁', rfl, -⟩
      · simp [cnt, proj] at h1
      · simp [cnt_cons] at h2
    · intro u
      have := hp u
      rw [proj_insert u t₀ k A B hA] at this
      by_cases h : t₀ = u
      · subst h; simpa [proj_cons'] using this
      · simpa [h, proj_cons'] using this
    · rintro t' t a b ⟨k', hk', hke⟩ hbeg ⟨H₁, hH₁, ha, hb⟩
      have key := hrt t' t (a + if t₀ = t' then 1 else 0) (b + if t₀ = t then 1 else 0)
        ⟨k', by rw [getElem?_insert t' t₀ k A B hA]; exact hk', hke⟩
        (by rw [getElem?_insert t t₀ k A B hA]; exact hbeg) ?_
      · obtain ⟨S₁, hS₁, h1, h2⟩ := key
        rcases List.prefix_cons_iff.mp hS₁ with rfl | ⟨S₁', rfl, hS₁'⟩
        · simp [cnt, proj] at h1
        · rw [cnt_cons] at h1 h2
          exact ⟨S₁', hS₁', by simp only at h1; omega, by simp only at h2; omega⟩
      · rcases prefix_append_cases hH₁ with hH₁ | ⟨X', hX', rfl⟩
        · have hn : ∀ x ∈ H₁, x.1 ≠ t₀ := fun x hx => hA x (hH₁.subset hx)
          have ht' : t₀ ≠ t' := by
            rintro rfl; simp [cnt, proj_eq_nil_of hn] at ha
          refine ⟨H₁, hH₁.trans (List.prefix_append _ _), by simp [ht', ha], ?_⟩
          split_ifs <;> omega
        · refine ⟨A ++ (t₀, k) :: X', ?_, ?_, ?_⟩
          · exact (List.prefix_append_right_inj A).mpr
              (List.prefix_cons_iff.mpr (Or.inr ⟨X', rfl, hX'⟩))
          · rw [cnt_insert t' t₀ k A X' hA]; split_ifs <;> omega
          · rw [cnt_insert t t₀ k A X' hA]; split_ifs <;> omega

end rt

/-! ### Non-transactional actions and evaluation -/

section nontr

variable [DecidableEq T]

lemma mem_nontrans_iff (τ : List (Act T O M C)) (x : Act T O M C) :
    x ∈ nontrans τ ↔ (x, false) ∈ ann (fun _ => false) τ := by
  simp [nontrans, nontransFrom]

lemma mem_of_mem_nontrans {τ : List (Act T O M C)} {x : Act T O M C} (h : x ∈ nontrans τ) :
    x ∈ τ := by
  rw [mem_nontrans_iff] at h
  have := List.mem_map_of_mem (f := Prod.fst) h
  rwa [map_fst_ann] at this

lemma mem_ann_of_tproj {st : T → Bool} {τ : List (Act T O M C)} {t : T} {p : Act T O M C × Bool}
    (h : p ∈ ann st (tproj t τ)) : p ∈ ann st τ := by
  rw [← ann_tproj] at h; exact (List.mem_filter.mp h).1

/-- Every prefix of `nontrans τ` is `nontrans` of a prefix of `τ`. -/
lemma exists_prefix_nontrans (τ : List (Act T O M C)) :
    ∀ N, N <+: nontrans τ → ∃ ρ, ρ <+: τ ∧ nontrans ρ = N := by
  induction τ using List.reverseRecOn with
  | nil => intro N hN; exact ⟨[], List.prefix_rfl, (List.prefix_nil.mp hN).symm⟩
  | append_singleton τ a ih =>
    intro N hN
    rw [nontrans_append] at hN
    rcases prefix_append_cases hN with hN | ⟨X', hX', rfl⟩
    · obtain ⟨ρ, hρ, e⟩ := ih N hN
      exact ⟨ρ, hρ.trans (List.prefix_append _ _), e⟩
    · have hY : (nontransFrom (stAfter (fun _ => false) τ) [a]).length ≤ 1 := by
        simp only [nontransFrom, ann_cons, ann_nil, List.length_map]
        exact (List.length_filter_le _ _).trans (by simp)
      have hl := hX'.length_le
      rcases Nat.eq_zero_or_pos X'.length with h0 | h0
      · rw [List.length_eq_zero_iff.mp h0, List.append_nil]
        exact ⟨τ, List.prefix_append _ _, rfl⟩
      · rw [hX'.eq_of_length (by omega), ← nontrans_append]
        exact ⟨τ ++ [a], List.prefix_rfl, rfl⟩

end nontr

lemma evalSet_nonempty' {S : Set (State T LV GV)} (hS : S.Nonempty) :
    ∀ τ : List (Act T O M C), (∀ t c, cmd t c ∈ τ → ∀ s, (sem c s).Nonempty) →
      (evalSet S τ).Nonempty
  | [], _ => hS
  | a :: τ, h => by
    refine evalSet_nonempty' (S := evalStep S a) ?_ τ (fun t c hc => h t c (by simp [hc]))
    obtain ⟨s, hs⟩ := hS
    cases a with
    | iface t k => exact ⟨s, s, hs, rfl⟩
    | cmd t c =>
      obtain ⟨s', hs'⟩ := h t c (by simp) s
      exact ⟨s', s, hs, hs'⟩

section total

variable [Inhabited LV] (B : ℤ)

lemma chunk_total (u : T) (k : IKind O M) (i : ℕ) :
    ∀ t c, cmd t c ∈ (chunk B u k i : List (Act T O M C)) → ∀ s, (sem c s).Nonempty := by
  intro t c hc s
  cases k with
  | committed | aborted =>
    simp only [chunk, mk, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
      Act.cmd.injEq] at hc
    rcases hc with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · rw [sem_assign]; exact Set.singleton_nonempty _
    · rw [sem_assign]; exact Set.singleton_nonempty _
  | call o f n =>
    simp [chunk] at hc; obtain ⟨-, rfl⟩ := hc; rw [sem_assumeEq]; exact ⟨s, rfl, by simp⟩
  | _ =>
    simp [chunk, mk] at hc <;> obtain ⟨-, rfl⟩ := hc <;> rw [sem_assign] <;>
      exact Set.singleton_nonempty _

variable [DecidableEq T]

lemma expand_total (c₀ : T → ℕ) (H : List (IAct T O M)) :
    ∀ t c, cmd t c ∈ (expand B c₀ H : List (Act T O M C)) → ∀ s, (sem c s).Nonempty := by
  induction H generalizing c₀ with
  | nil => simp [expand]
  | cons a H ih =>
    obtain ⟨u, k⟩ := a
    intro t c hc
    simp only [expand, List.mem_append] at hc
    rcases hc with hc | hc
    · exact chunk_total B u k _ t c hc
    · exact ih _ t c hc

end total

/-! ### The marker argument: real-time order is preserved -/

section marker_arg

variable [Inhabited LV] (B : ℤ) [DecidableEq T]

lemma retLt_of_subset {B : ℤ} {l l' : List (IKind O M)} (h : RetLt B l) (hs : l' ⊆ l) :
    RetLt B l' := fun n o f hm => h n o f (hs hm)

lemma tproj_expand0 (H : List (IAct T O M)) (u : T) :
    tproj u (expand B (fun _ => 0) H : List (Act T O M C)) = expandT B u 0 (proj u H) :=
  tproj_expand B _ H u

lemma mem_tproj_mk {u : T} {v : ℤ} {ρ : List (Act T O M C)} (h : mk u v ∈ ρ) :
    (mk u v : Act T O M C) ∈ tproj u ρ := by
  simp only [tproj, List.mem_filter]; exact ⟨h, by simp [mk]⟩

/-- **The marker argument.** If `τ' ∼ τ` for the trace `τ` of `P_H` with `history τ = H`, then
`history τ'` preserves the real-time order of `H`. -/
theorem rt_of_obsEq (hB : BigB C B) {H : List (IAct T O M)} (hw : WellFormed H)
    (hret : ∀ u, RetLt B (proj u H)) {τ' : List (Act T O M C)}
    (hobs : ObsEq (expand B (fun _ => 0) H) τ') : RT H (history τ') := by
  rintro t' t a b ⟨k, hk, hke⟩ hbeg ⟨H₁, ⟨H₂, rfl⟩, ha, hb⟩
  obtain ⟨c', hsplit⟩ := expand_append (C := C) B (fun _ => 0) H₁ H₂
  have hτ : ∀ u, tproj u τ' = expandT B u 0 (proj u (H₁ ++ H₂)) := fun u => by
    rw [← hobs.1 u, tproj_expand0]
  have hpre : nontrans (expand B (fun _ => 0) H₁ : List (Act T O M C)) <+: nontrans τ' := by
    rw [← hobs.2, hsplit, nontrans_append]; exact List.prefix_append _ _
  obtain ⟨ρ, hρ, hρN⟩ := exists_prefix_nontrans τ' _ hpre
  have hρt : ∀ u, tproj u ρ <+: expandT B u 0 (proj u (H₁ ++ H₂)) := fun u => by
    rw [← hτ u]; exact hρ.filter _
  have hcnt : ∀ u, cnt u (history ρ) = (history (tproj u ρ)).length := fun u => by
    simp [cnt, proj_history']
  have hret₁ : ∀ u, RetLt B (proj u H₁) := fun u =>
    retLt_of_subset (hret u) (by rw [proj_append']; exact List.subset_append_left _ _)
  refine ⟨history ρ, hρ.filterMap _, ?_, ?_⟩
  · -- the end marker of the `a`-th action of `t'` is in `nontrans τ₁`, hence in `ρ`
    have hk₁ : (proj t' H₁)[a]? = some k := by
      rw [proj_append', List.getElem?_append_left (by simpa [cnt] using ha)] at hk; exact hk
    have m1 := endMarker_mem_ann (C := C) B t' (proj t' H₁) a 0 k (fun _ => false) hk₁ hke
    rw [← tproj_expand0] at m1
    have m2 : (mk t' (B + 2 * ((0 + a : ℕ) : ℤ) + 1) : Act T O M C) ∈ nontrans ρ := by
      rw [hρN, mem_nontrans_iff]; exact mem_ann_of_tproj m1
    have := lt_of_endMarker_prefix B hB 0 _ _ (hret t') (hρt t')
      (mem_tproj_mk (mem_of_mem_nontrans m2))
    rw [hcnt]; omega
  · -- otherwise the begin marker of the `b`-th action of `t` would be in `ρ`, hence in `τ₁`
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨hbl, hlb⟩ := List.getElem?_eq_some_iff.mp hbeg
    have hdec : proj t (H₁ ++ H₂) = (proj t (H₁ ++ H₂)).take b ++
        txbegin :: (proj t (H₁ ++ H₂)).drop (b + 1) := by
      rw [← hlb, ← List.drop_eq_getElem_cons hbl, List.take_append_drop]
    have htk : ((proj t (H₁ ++ H₂)).take b).length = b := by simp; omega
    have hE : (expandT B t 0 (proj t (H₁ ++ H₂)) : List (Act T O M C)) =
        expandT B t 0 ((proj t (H₁ ++ H₂)).take b) ++ (mk t (B + 2 * (b : ℤ)) ::
          iface t txbegin :: expandT B t (b + 1) ((proj t (H₁ ++ H₂)).drop (b + 1))) := by
      conv_lhs => rw [hdec]
      rw [expandT_append, htk]; simp [expandT, chunk]
    have hP := hρt t
    rw [hE] at hP
    have hhist : (history (expandT B t 0 ((proj t (H₁ ++ H₂)).take b) :
        List (Act T O M C))).length = b := by rw [history_expandT, List.length_map, htk]
    have hlt' : b < (history (tproj t ρ)).length := by rw [← hcnt]; exact hlt
    rcases prefix_append_cases hP with hP' | ⟨X', hX', he⟩
    · have : (history (tproj t ρ)).length ≤ (history (expandT B t 0
          ((proj t (H₁ ++ H₂)).take b) : List (Act T O M C))).length :=
        (hP'.filterMap Act.toI).length_le
      omega
    rcases List.prefix_cons_iff.mp hX' with rfl | ⟨X'', rfl, -⟩
    · rw [he, List.append_nil] at hlt'; omega
    have hst : stAfter (fun _ => false)
        (expandT B t 0 ((proj t (H₁ ++ H₂)).take b) : List (Act T O M C)) t = false := by
      have hrun := (wellFormed_iff_run _).mp hw t
      rw [hdec, run_append] at hrun
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hrun
      obtain ⟨q₁, hq₁, hq⟩ := Option.bind_eq_some_iff.mp hq
      rw [stAfter_expandT B t 0 _ _ idle q₁ rfl hq₁]
      cases q₁ <;> simp [step] at hq
      rfl
    have m1 : ((mk t (B + 2 * (b : ℤ)) : Act T O M C), false) ∈
        ann (fun _ => false) (tproj t ρ) := by
      rw [he, ann_append]
      simp [flag, hst, mk, Act.isBoundA]
    have m2 : (mk t (B + 2 * (b : ℤ)) : Act T O M C) ∈ nontrans (expand B (fun _ => 0) H₁) := by
      rw [← hρN, mem_nontrans_iff]; exact mem_ann_of_tproj m1
    have m3 := mem_tproj_mk (mem_of_mem_nontrans m2)
    rw [tproj_expand0] at m3
    have := lt_of_beginMarker B hB 0 (proj t H₁) (hret₁ t) m3
    simp [cnt] at hb; omega

end marker_arg

/-! ### The bound `B` and the core of the necessity proof -/

section core

/-- `|n|` for a `ret n` action, `0` otherwise. -/
def retAbs (a : IAct T O M) : ℤ :=
  match a.2 with
  | ret n _ _ => |n|
  | _ => 0

lemma retAbs_nonneg (a : IAct T O M) : 0 ≤ retAbs a := by
  obtain ⟨u, k⟩ := a; cases k <;> simp [retAbs]

/-- The marker base for a history `H`: larger than every value assigned in the trace of `P_H`
other than markers. -/
def bound (C : Type) [Lang T LV GV BE IE C] (H : List (IAct T O M)) : ℤ :=
  1 + |vCom C| + |vAb C| + (H.map retAbs).sum

lemma bigB_bound (H : List (IAct T O M)) : BigB C (bound C H) := by
  have h0 : 0 ≤ (H.map retAbs).sum :=
    List.sum_nonneg (fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact retAbs_nonneg a)
  have := le_abs_self (vCom C)
  have := le_abs_self (vAb C)
  have := abs_nonneg (vCom C)
  have := abs_nonneg (vAb C)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [bound] <;> linarith

variable [DecidableEq T]

lemma mem_proj_iff {t : T} {k : IKind O M} {L : List (IAct T O M)} :
    k ∈ proj t L ↔ (t, k) ∈ L := by
  simp only [proj, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨u, k'⟩, ⟨h, rfl⟩, rfl⟩; exact h
  · intro h; exact ⟨(t, k), ⟨h, rfl⟩, rfl⟩

lemma retLt_bound (H : List (IAct T O M)) (u : T) : RetLt (bound C H) (proj u H) := by
  intro n o f hm
  have hm' := List.mem_map_of_mem (f := retAbs) (mem_proj_iff.mp hm)
  have h1 := List.single_le_sum (fun x hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact retAbs_nonneg a) _ hm'
  simp only [retAbs] at h1
  have := le_abs_self n
  have := abs_nonneg (vCom C)
  have := abs_nonneg (vAb C)
  simp only [bound]; linarith

variable [Fintype T] [Inhabited LV]

/-- **Core of the necessity proof** (journal version, Lemma 7.1, with trace observation): every
history `H ∈ H_C` is related by `⊑` to a history `S ∈ H_A` with the same per-thread projections. -/
theorem necessity_core {HC HA : Set (List (IAct T O M))} (hC : ∀ h ∈ HC, WellFormed h)
    (h : TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA) :
    ∀ H ∈ HC, ∃ S ∈ HA, Opac H S ∧ ∀ t, proj t H = proj t S := by
  intro H hH
  have hw := hC H hH
  have hex : ∀ u, ∃ (Cm : Cmd LV O M C BE IE) (ext : List (Act T O M C)), Cm.Allowed u false ∧
      Tr u Cm (expandT (bound C H) u 0 (proj u H) ++ ext) :=
    fun u => prog_exists (bound C H) u _ ((wellFormed_iff_run H).mp hw u)
  choose P ext hPA hPT using hex
  have hInA : InA P (expand (bound C H) (fun _ => 0) H) :=
    inA_of_ext P _ (fun u => ⟨ext u, by rw [tproj_expand0]; exact hPT u⟩)
  let s : State T LV GV := fun _ => 0
  have hτ : expand (bound C H) (fun _ => 0) H ∈ denH P s HC :=
    ⟨⟨hInA, Set.nonempty_iff_ne_empty.mp
      (evalSet_nonempty' (Set.singleton_nonempty s) _ (expand_total _ _ H))⟩,
      by rw [history_expand]; exact hH⟩
  obtain ⟨τ', ⟨-, hS⟩, hobs⟩ := h P hPA s _ hτ
  have hproj : ∀ t, proj t H = proj t (history τ') := fun t => by
    conv_lhs => rw [← history_expand (C := C) (bound C H) (fun _ => 0) H]
    rw [proj_history', hobs.1 t, ← proj_history']
  exact ⟨history τ', hS, opac_of_rt _ _ hproj
    (rt_of_obsEq _ (bigB_bound H) hw (retLt_bound H) hobs), hproj⟩

end core

/-! ### Complete histories -/

section complete

variable [DecidableEq T]

lemma split_mid {t : T} {k : IKind O M} {l₂ : List (IKind O M)} :
    ∀ (l₁ : List (IKind O M)) {H : List (IAct T O M)}, proj t H = l₁ ++ k :: l₂ →
      ∃ H₁ H₂, H = H₁ ++ (t, k) :: H₂ ∧ proj t H₂ = l₂
  | [], H, h => by
    obtain ⟨A, B, rfl, -, hB⟩ := split_first h
    exact ⟨A, B, rfl, hB⟩
  | x :: l₁, H, h => by
    obtain ⟨A, B, rfl, -, hB⟩ := split_first h
    obtain ⟨B₁, B₂, rfl, hB₂⟩ := split_mid l₁ hB
    exact ⟨A ++ (t, x) :: B₁, B₂, by simp, hB₂⟩

/-- Completeness (Definition 3) only depends on the per-thread projections. -/
lemma complete_of_proj {H S : List (IAct T O M)} (hp : ∀ t, proj t H = proj t S)
    (hc : Complete H) : Complete S := by
  intro S₁ t S₂ hS
  have e : proj t H = proj t S₁ ++ txbegin :: proj t S₂ := by
    rw [hp, hS, proj_append', proj_cons']; simp
  obtain ⟨H₁, H₂, rfl, hH₂⟩ := split_mid _ e
  rcases hc H₁ t H₂ rfl with h | h
  · left; rw [← mem_proj_iff, ← hH₂, mem_proj_iff]; exact h
  · right; rw [← mem_proj_iff, ← hH₂, mem_proj_iff]; exact h

end complete

end TraceNec

open TraceNec

variable {T LV GV O M BE IE C : Type} [Lang T LV GV BE IE C] [DecidableEq T] [Fintype T]
  [Inhabited LV]

/-- **Repair of Theorem 24** (journal version, Theorem 7.2 with Lemma 7.1): observational
refinement with respect to traces (Definition 15) implies the opacity relation, `H_C ⊑_trace H_A ⟹
H_C ⊑ H_A`, for all histories of `H_C` (pending ones included). Only the well-formedness of `H_C` is
used. Theorem 24 as stated (refinement with respect to states) is false. -/
theorem trace_necessity {HC HA : Set (List (IAct T O M))} (hC : IsTS HC)
    (h : TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA) :
    OpacRel HC HA := fun H hH =>
  let ⟨S, hS, hop, _⟩ := necessity_core hC.1 h H hH
  ⟨S, hS, hop⟩

/-- **Repair of Theorem 24**, for complete histories (the form of the paper's statement):
`H_C ⊑_trace H_A ⟹ H_C|complete ⊑ H_A|complete`. -/
theorem trace_necessity_complete {HC HA : Set (List (IAct T O M))} (hC : IsTS HC)
    (h : TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA) :
    OpacRel (completeSub HC) (completeSub HA) := by
  rintro H ⟨hH, hc⟩
  obtain ⟨S, hS, hop, hp⟩ := necessity_core hC.1 h H hH
  exact ⟨S, ⟨hS, complete_of_proj hp hc⟩, hop⟩

/-- **Theorem 16, repaired**: for transactional systems, the opacity relation is equivalent to
observational refinement with respect to traces, `H_C ⊑ H_A ⟺ H_C ⊑_trace H_A` (Theorem 21 and
the repaired Theorem 24). -/
theorem theorem_16_repaired {HC HA : Set (List (IAct T O M))} (hC : IsTS HC) :
    OpacRel HC HA ↔ TraceRef (LV := LV) (GV := GV) (C := C) (BE := BE) (IE := IE) O M HC HA :=
  ⟨theorem_21 hC.1, trace_necessity hC⟩

end Podc.TMObservationalRefinement
