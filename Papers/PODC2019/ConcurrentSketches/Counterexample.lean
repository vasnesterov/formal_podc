import Papers.PODC2019.ConcurrentSketches.ParSketchMain

/-!
# The initial hint `1` must be the hint of the empty sketch

Algorithm 2 initialises `hint_i` and `prop_i` to the constant `1`, while the paper only requires
of a composable sketch that `calcHint()` returns a non-zero value and that `shouldAdd(h, a)` is
safe *for hints `h` returned by `calcHint`*. For the paper's Θ sketch `1` is indeed the hint of
the empty sketch (`Θ = 1`), but for a general composable sketch the first `b` updates of every
thread are filtered with a hint that was never computed by `calcHint`, and Lemma 1 / Theorem 1
fail.

`cntSketch` is an exact counter whose hints are always `2`, and `shouldAdd h a = (h ≠ 1)`: it
satisfies all requirements of a composable sketch (`shouldAdd(calcHint(), a)` is always true).
With the paper's initial hint `1`, every update is filtered out forever, and queries after two
completed updates return `0`. This history has no linearization in `SeqSketch_{Nb}` for
`N = b = 1` (`parSketch_hint_one_not_relaxed`), so `ParSketch` is not even linearisable with
respect to `SeqSketch_{Nb}` (`parSketch_hint_one_not_stronglyLinearizable`).

With the initial hint of the empty sketch (`S.calcHint S.init`, here `2`) the algorithm is
correct (`lemma1` with `safe_init_hint`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentSketches

open Cslib.SharedMemory

/-- An exact counter of updates; its hints are always `2`, and `shouldAdd h a = (h ≠ 1)`. -/
abbrev cntSketch : Composable where
  State := ℕ
  Elem := Unit
  Arg := Unit
  Val := ℕ
  init := 0
  update s _ := s + 1
  query s _ := s
  merge := (· + ·)
  Snap := ℕ
  snapshot := id
  snapQuery x _ := x
  Hint := ℕ
  calcHint _ := 2
  shouldAdd h _ := h != 1
  merge_run A B := by
    have key : ∀ (A : List Unit) (n : ℕ), A.foldl (fun s _ => s + 1) n = n + A.length := by
      intro A; induction A with
      | nil => simp
      | cons a A ih => intro n; simp [ih]; omega
    simp [key]
  snapQuery_snapshot _ _ := rfl
  shouldAdd_spec A a h := by simp at h

/-- The execution: two updates by thread `0` (each returns at once), then two queries
returning `0`. -/
def cexExec : List (Lbl cntSketch 1 Unit) :=
  [.inv (.upd 0) (.update ()), .ret (.upd 0) .ack,
   .inv (.upd 0) (.update ()), .ret (.upd 0) .ack,
   .inv (.qry ()) (.query ()), .tau (.qry ()), .ret (.qry ()) (.val (0 : ℕ)),
   .inv (.qry ()) (.query ()), .tau (.qry ()), .ret (.qry ()) (.val (0 : ℕ))]

/-- `cexExec` is an execution of `ParSketch` with the paper's initial hint `1`, one update
thread and `b = 1`. -/
lemma cexExec_valid : (parSketch cntSketch 1 Unit 1 (1 : ℕ)).Valid cexExec := by
  unfold Impl.Valid
  simp [cexExec, Impl.run, Impl.runFrom, Impl.step, parSketch, PLoc.invoke, PLoc.act,
    Impl.initCfg, PLoc.init, Proc.allowed, cntSketch]

/-- The last occurrence of an element. -/
lemma exists_last_split {X : Type} {x : X} {H : List X} (hx : x ∈ H) :
    ∃ A B, H = A ++ x :: B ∧ x ∉ B := by
  induction H using List.reverseRecOn with
  | nil => simp at hx
  | append_singleton H z ih =>
    by_cases hz : z = x
    · subst hz; exact ⟨H, [], by simp, by simp⟩
    · have : x ∈ H := by
        rcases List.mem_append.1 hx with h | h
        · exact h
        · simp at h; exact absurd h.symm hz
      obtain ⟨A, B, rfl, hB⟩ := ih this
      exact ⟨A, B ++ [z], by simp, by simp [hB, Ne.symm hz]⟩

/-- In a history of the counter's `SeqSketch`, a query preceded by an update does not return
`0`. -/
lemma cnt_query_ne_zero {H : List (Entry (Proc 1 Unit) cntSketch.toSketch)}
    (hH : SeqSketch cntSketch.toSketch H) {x y : Entry (Proc 1 Unit) cntSketch.toSketch}
    (hxq : x.2.1 = .query ()) (hyu : y.2.1 = .update ()) (hy : Prec H y x) :
    x.2.2 ≠ .val (0 : ℕ) := by
  have hx : x ∈ H := hy.subset (by simp)
  obtain ⟨A, B, rfl, hB⟩ := exists_last_split hx
  have hyA : y ∈ A := by
    obtain ⟨l₁, l₂, h12, h1, h2⟩ := List.sublist_append_iff.1 hy
    match l₁, h12 with
    | [], h12 =>
      simp only [List.nil_append] at h12; subst h12
      rcases List.sublist_cons_iff.1 h2 with h | ⟨r, h1', h2'⟩
      · exact absurd (h.subset (by simp)) hB
      · simp only [List.cons.injEq] at h1'
        obtain ⟨rfl, rfl⟩ := h1'
        exact absurd (h2'.subset (by simp)) hB
    | [z], h12 =>
      simp only [List.singleton_append, List.cons.injEq] at h12
      obtain ⟨rfl, -⟩ := h12; exact h1.subset (by simp)
    | [z, w], h12 =>
      simp only [List.cons.injEq] at h12
      obtain ⟨rfl, -⟩ := h12; exact h1.subset (by simp)
    | _ :: _ :: _ :: _, h12 => simp at h12
  have hresp := hH A x B rfl
  rw [hxq] at hresp
  rw [hresp]
  simp only [seqResp, ne_eq, SkResp.val.injEq]
  have hne : upds A ≠ [] := by
    intro h
    simp only [upds, List.filterMap_eq_nil_iff] at h
    have := h y hyA
    rw [hyu] at this; simp at this
  have key : ∀ (A : List Unit) (n : ℕ), A.foldl (fun s _ => s + 1) n = n + A.length := by
    intro A; induction A with
    | nil => simp
    | cons a A ih => intro n; simp [ih]; omega
  simp only [Sketch.run, key]
  simpa using hne

/-- **The paper's initial hint `1` breaks Lemma 1 for general composable sketches.** The history
of `cexExec` (two completed updates, then two queries returning `0`) has no linearization in
`SeqSketch_{Nb}` for `N = b = 1`. -/
theorem parSketch_hint_one_not_relaxed (L : List (Entry (Proc 1 Unit) cntSketch.toSketch)) :
    ¬ IsHLinearization (SeqSketchR (1 * 1) cntSketch.toSketch) cexExec L := by
  intro hL
  obtain ⟨H, hH, hsub, ⟨D, hD, hcov⟩, hpre⟩ := hL.mem
  have hD1 : ∀ {D : List (Entry (Proc 1 Unit) cntSketch.toSketch)}, D.length ≤ 1 * 1 →
      ∀ a ∈ D, ∀ c ∈ D, a = c := by
    intro D hD a ha c hc
    match D, hD with
    | [], _ => simp at ha
    | [_], _ => simp only [List.mem_singleton] at ha hc; rw [ha, hc]
    | _ :: _ :: _, h => simp at h
  -- the completed operation instances
  have entry : ∀ x, Completed cexExec x → ∃ e ∈ L, e.1 = x := fun x hx => by
    obtain ⟨e, he, h⟩ := List.mem_map.1 (hL.complete x hx); exact ⟨e, he, h⟩
  have hou : opsOf cexExec (.upd 0) = [.update (), .update ()] := rfl
  have hoq : opsOf cexExec (.qry ()) = [.query (), .query ()] := rfl
  have hru : respsOf cexExec (.upd 0) = [.ack, .ack] := rfl
  have hrq : respsOf cexExec (.qry ()) = [.val (0 : ℕ), .val (0 : ℕ)] := rfl
  have hru4 : respsOf (cexExec.take 4) (.upd 0) = [.ack, .ack] := rfl
  have hoq4 : opsOf (cexExec.take 4) (.qry ()) = [] := rfl
  obtain ⟨u0, hu0, hu0i⟩ := entry (.upd 0, 0) (by
    simp [Completed, hru, hrq])
  obtain ⟨u1, hu1, hu1i⟩ := entry (.upd 0, 1) (by
    simp [Completed, hru, hrq])
  obtain ⟨q0, hq0, hq0i⟩ := entry (.qry (), 0) (by
    simp [Completed, hru, hrq])
  obtain ⟨q1, hq1, hq1i⟩ := entry (.qry (), 1) (by
    simp [Completed, hru, hrq])
  have hop : ∀ e ∈ L, ∀ x o, e.1 = x → opOf cexExec x = some o → e.2.1 = o := by
    intro e he x o h1 h2
    have := hL.op_eq e he; rw [h1, h2] at this; exact (Option.some.inj this).symm
  have hu0o : u0.2.1 = .update () := hop u0 hu0 _ _ hu0i (by simp [opOf, hou, hoq])
  have hu1o : u1.2.1 = .update () := hop u1 hu1 _ _ hu1i (by simp [opOf, hou, hoq])
  have hq0o : q0.2.1 = .query () := hop q0 hq0 _ _ hq0i (by simp [opOf, hou, hoq])
  have hq1o : q1.2.1 = .query () := hop q1 hq1 _ _ hq1i (by simp [opOf, hou, hoq])
  have hq0r : q0.2.2 = .val (0 : ℕ) := hL.resp_eq q0 hq0 _ (by
    rw [hq0i]; simp [respOf, hrq])
  have hq1r : q1.2.2 = .val (0 : ℕ) := hL.resp_eq q1 hq1 _ (by
    rw [hq1i]; simp [respOf, hrq])
  -- real-time order: both updates precede both queries
  have hprec : ∀ u ∈ L, ∀ q ∈ L, u.1.1 = .upd 0 → u.1.2 < 2 → q.1.1 = .qry () → Prec L u q := by
    intro u hu q hq hu1 hu2 hq1
    have hP : Precedes cexExec u.1 q.1 := by
      refine ⟨cexExec.take 4, cexExec.drop 4, by simp, ?_, ?_⟩
      · obtain ⟨⟨p, k⟩, rest⟩ := u; simp only at hu1 hu2; subst hu1
        simp [Completed, hru4]; omega
      · obtain ⟨⟨p, k⟩, rest⟩ := q; simp only at hq1; subst hq1
        simp [Invoked, hoq4]
    obtain ⟨l', hl', hmap⟩ := List.sublist_map_iff.1
      (hL.realtime _ _ hP (List.mem_map_of_mem (f := Prod.fst) hq))
    match l', hl', hmap with
    | [a, c], hl', hmap =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
      have ha : a = u := List.inj_on_of_nodup_map hL.nodup (hl'.subset (by simp)) hu hmap.1.symm
      have hc' : c = q :=
        List.inj_on_of_nodup_map hL.nodup (hl'.subset (by simp)) hq hmap.2.symm
      subst ha hc'; exact hl'
    | [], _, h => simp at h
    | [_], _, h => simp at h
    | _ :: _ :: _ :: _, _, h => simp at h
  -- at most one entry is dropped, so one of the queries is in `H`
  have hq01 : q0 ≠ q1 := fun h => by rw [h, hq1i] at hq0i; simp at hq0i
  obtain ⟨q, hqH, hqo, hqr, hqq⟩ : ∃ q ∈ H, q.2.1 = .query () ∧ q.2.2 = .val (0 : ℕ) ∧
      q.1.1 = .qry () := by
    rcases hcov q0 hq0 with h | h
    · exact ⟨q0, h, hq0o, hq0r, by rw [hq0i]⟩
    rcases hcov q1 hq1 with h' | h'
    · exact ⟨q1, h', hq1o, hq1r, by rw [hq1i]⟩
    exact absurd (hD1 hD _ h _ h') hq01
  -- the query is preceded in `H` by one of the two updates
  obtain ⟨D', hD', hcov'⟩ := hpre q hqH
  have hqL : q ∈ L := hsub q hqH
  have hu01 : u0 ≠ u1 := fun h => by rw [h, hu1i] at hu0i; simp at hu0i
  have hp0 := hcov' u0 (hprec u0 hu0 q hqL (by rw [hu0i]) (by rw [hu0i]; decide) hqq)
  have hp1 := hcov' u1 (hprec u1 hu1 q hqL (by rw [hu1i]) (by rw [hu1i]; decide) hqq)
  rcases hp0 with h0 | h0
  · exact cnt_query_ne_zero hH hqo hu0o h0 hqr
  rcases hp1 with h1 | h1
  · exact cnt_query_ne_zero hH hqo hu1o h1 hqr
  exact hu01 (hD1 hD' _ h0 _ h1)

/-- Consequently `ParSketch` with the literal initial hint `1` is not (strongly) linearisable
with respect to `SeqSketch_{Nb}` for this composable sketch. -/
theorem parSketch_hint_one_not_stronglyLinearizable :
    ¬ (parSketch cntSketch 1 Unit 1 (1 : ℕ)).HStronglyLinearizable
      (SeqSketchR (1 * 1) cntSketch.toSketch) := by
  rintro ⟨h, hh, -⟩
  exact parSketch_hint_one_not_relaxed _ (hh _ cexExec_valid)

/-- With the hint of the empty sketch (here `2`) Lemma 1 applies. -/
example : (parSketch cntSketch 1 Unit 1 (cntSketch.calcHint cntSketch.init)).HStronglyLinearizable
    (SeqSketchR (1 * 1) cntSketch.toSketch) :=
  lemma1 one_pos (safe_init_hint _)

end Podc.ConcurrentSketches
