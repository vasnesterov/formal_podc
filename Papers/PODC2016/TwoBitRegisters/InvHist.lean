import Papers.PODC2016.TwoBitRegisters.InvRead

/-!
# The history invariant (Lemma 10 of the paper)

We run a *ghost state* alongside the executions:

* `snap i j`: the value of `w_sync_j[j]` when the current read of `i` was invoked;
* `rf x`: for a completed read `x`, the sequence number of the value it returned.

`InvH` relates the configuration, the history and the ghost state. Its main consequences are the
three claims of the proof of Lemma 10 (no read from the future, no overwritten value, no new/old
inversion), from which linearizability follows by the SWMR reads-from criterion.

Key ingredients:
* `q_write` / `q_read`: after a write (resp. a read returning the `x`-th value) completes, at least
  `n - t` processes know the value (`w_sync_j[j] ≥ x`; lines 3 and 9 with Lemma 2);
* `r7_req`: the values a pending read must not miss are known by a quorum at its invocation;
* `pipe_snap`: a process `j` sends `PROCEED()` for the current read of `i` only once
  `w_sync_j[i] ≥ snap i j` (line 20);
* at line 8 the two quorums intersect (`2t < n`).
-/

set_option linter.unusedSectionVars false

namespace Podc.TwoBit

open Cslib.SharedMemory Cslib.AsyncMP

variable {P V : Type} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- Ghost state. -/
structure Ghost (P : Type) where
  /-- `snap i j`: `w_sync_j[j]` at the invocation of the current read of `i`. -/
  snap : P → P → ℕ
  /-- Reads-from: the index of the value returned by a completed read. -/
  rf : OpId P → ℕ

/-- The current (or next) operation of `i`. -/
def cur {A : ObjSpec} (h : List (Label P A)) (i : P) : OpId P := (i, (respsOf h i).length)

/-- `m` is a lower bound that the current read of `i` must respect: write number `m` (1-based)
or a read returning value number `m` completed before the current operation of `i` started. -/
def Req {A : ObjSpec} (w : P) (h : List (Label P A)) (rf : OpId P → ℕ) (i : P) (m : ℕ) : Prop :=
  ∃ y : OpId P, Precedes h y (cur h i) ∧ ((y.1 = w ∧ m = y.2 + 1) ∨ (y.1 ≠ w ∧ m = rf y))

/-- `pipe_snap` (see the module docstring). -/
def PipeSnap (C : Cfg P V) (g : Ghost P) : Prop :=
  ∀ i rsn, i ∉ C.crashed → (C.loc i).phase = .r7 rsn → ∀ j, j ≠ i →
    g.snap i j ≤ W C j i ∨ (i, j, Msg.read) ∈ C.net ∨
      ∃ sn, g.snap i j ≤ sn ∧ (i, sn) ∈ (C.loc j).tasks

/-- The history invariant. `Q = n - t` is the quorum size. -/
structure InvH (w : P) (Q : ℕ) (v₀ : V) (C : Cfg P V) (h : List (Label P (register V v₀)))
    (g : Ghost P) : Prop where
  wf : WellFormed h
  ops : ∀ p, ∀ o ∈ opsOf h p, (p = w ∧ ∃ v, o = .write v) ∨ (p ≠ w ∧ o = .read)
  cnt : ∀ p, (opsOf h p).length =
    (respsOf h p).length + if (C.loc p).phase = .idle then 0 else 1
  own_w : W C w w = (opsOf h w).length
  ph_w3 : ∀ p wsn, (C.loc p).phase = .w3 wsn → p = w ∧ wsn = W C w w
  ph_r7 : ∀ p n, (C.loc p).phase = .r7 n → p ≠ w
  ph_r9 : ∀ p n, (C.loc p).phase = .r9 n → p ≠ w ∧ n ≤ W C p p
  hist_w : ∀ k, k ≤ W C w w → Hw w C k = writeVal v₀ (opsOf h w) k
  write_resp : ∀ j v x, opOf h (w, j) = some (.write v) → respOf h (w, j) = some x → x = v
  pipe_snap : PipeSnap C g
  snap_le : ∀ i j, g.snap i j ≤ W C j j
  q_write : ∀ k, Completed h (w, k) → Q ≤ count (fun j => k + 1 ≤ W C j j)
  q_read : ∀ y : OpId P, y.1 ≠ w → Completed h y → Q ≤ count (fun j => g.rf y ≤ W C j j)
  r7_req : ∀ i rsn m, (C.loc i).phase = .r7 rsn → Req w h g.rf i m →
    Q ≤ count (fun j => m ≤ g.snap i j)
  r9_req : ∀ i sn m, (C.loc i).phase = .r9 sn → Req w h g.rf i m → m ≤ sn
  read_val : ∀ x : OpId P, x.1 ≠ w → Completed h x →
    respOf h x = some (writeVal v₀ (opsOf h w) (g.rf x))
  rf_le : ∀ x : OpId P, x.1 ≠ w → Completed h x → g.rf x ≤ (opsOf h w).length
  not_future : ∀ x : OpId P, x.1 ≠ w → Completed h x → 0 < g.rf x →
    ¬ Precedes h x (w, g.rf x - 1)
  not_overwritten : ∀ x : OpId P, x.1 ≠ w → Completed h x → ¬ Precedes h (w, g.rf x) x
  mono : ∀ x y : OpId P, x.1 ≠ w → y.1 ≠ w → Completed h y → Precedes h x y → g.rf x ≤ g.rf y

/-! ## Counting -/

lemma count_mono {c₁ c₂ : P → Prop} [DecidablePred c₁] [DecidablePred c₂]
    (h : ∀ j, c₁ j → c₂ j) : count c₁ ≤ count c₂ :=
  Finset.card_le_card (fun j hj => by simp only [Finset.mem_filter] at hj ⊢; exact ⟨hj.1, h j hj.2⟩)

/-- Two quorums of size `n - t` intersect when `2t < n`. -/
lemma quorum_inter {t : ℕ} (ht : 2 * t < Fintype.card P) {c₁ c₂ : P → Prop} [DecidablePred c₁]
    [DecidablePred c₂] (h₁ : Fintype.card P - t ≤ count c₁) (h₂ : Fintype.card P - t ≤ count c₂) :
    ∃ j, c₁ j ∧ c₂ j := by
  by_contra hcon
  push Not at hcon
  have hdisj : Disjoint (Finset.univ.filter c₁) (Finset.univ.filter c₂) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_filter] at hj1 hj2
    exact hcon j hj1.2 hj2.2
  have := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ (Finset.univ.filter c₁ ∪ Finset.univ.filter c₂)
  simp only [count] at h₁ h₂
  omega

/-! ## Frame lemmas -/

lemma PipeSnap.mono {C C' : Cfg P V} {g : Ghost P} (hps : PipeSnap C g)
    (hcr : C.crashed ⊆ C'.crashed)
    (hph : ∀ i rsn, (C'.loc i).phase = .r7 rsn → (C.loc i).phase = .r7 rsn)
    (hW : ∀ i j, W C i j ≤ W C' i j)
    (hread : ∀ i j, i ∉ C'.crashed → (i, j, Msg.read) ∈ C.net → (i, j, Msg.read) ∈ C'.net)
    (htasks : ∀ j x, x ∈ (C.loc j).tasks → x ∈ (C'.loc j).tasks) : PipeSnap C' g := by
  intro i rsn hi hph' j hji
  rcases hps i rsn (fun h => hi (hcr h)) (hph i rsn hph') j hji with h1 | h1 | ⟨sn, h1, h2⟩
  · exact Or.inl (h1.trans (hW j i))
  · exact Or.inr (Or.inl (hread i j hi h1))
  · exact Or.inr (Or.inr ⟨sn, h1, htasks j _ h2⟩)

/-- Steps that change neither the history, nor the ghost state, nor the phases, nor the writer's
`w_sync_w[w]`/history, and only increase `w_sync`. -/
lemma InvH.frame {w : P} {Q : ℕ} {v₀ : V} {C C' : Cfg P V} {h : List (Label P (register V v₀))}
    {g : Ghost P} (hH : InvH w Q v₀ C h g)
    (hph : ∀ p, (C'.loc p).phase = (C.loc p).phase) (hW : ∀ i j, W C i j ≤ W C' i j)
    (hWw : W C' w w = W C w w) (hHw : ∀ k, k ≤ W C w w → Hw w C' k = Hw w C k)
    (hps : PipeSnap C' g) : InvH w Q v₀ C' h g where
  wf := hH.wf
  ops := hH.ops
  cnt p := by rw [hph]; exact hH.cnt p
  own_w := by rw [hWw]; exact hH.own_w
  ph_w3 p wsn h1 := by rw [hph] at h1; rw [hWw]; exact hH.ph_w3 p wsn h1
  ph_r7 p n h1 := by rw [hph] at h1; exact hH.ph_r7 p n h1
  ph_r9 p n h1 := by
    rw [hph] at h1; obtain ⟨h2, h3⟩ := hH.ph_r9 p n h1; exact ⟨h2, h3.trans (hW p p)⟩
  hist_w k hk := by rw [hWw] at hk; rw [hHw k hk]; exact hH.hist_w k hk
  write_resp := hH.write_resp
  pipe_snap := hps
  snap_le i j := (hH.snap_le i j).trans (hW j j)
  q_write k hk := (hH.q_write k hk).trans (count_mono (fun j hj => hj.trans (hW j j)))
  q_read y hy hc := (hH.q_read y hy hc).trans (count_mono (fun j hj => hj.trans (hW j j)))
  r7_req i rsn m h1 h2 := by rw [hph] at h1; exact hH.r7_req i rsn m h1 h2
  r9_req i sn m h1 h2 := by rw [hph] at h1; exact hH.r9_req i sn m h1 h2
  read_val := hH.read_val
  rf_le := hH.rf_le
  not_future := hH.not_future
  not_overwritten := hH.not_overwritten
  mono := hH.mono

/-! ## Initial configuration -/

lemma invH_init (w : P) (t : ℕ) (v₀ : V) :
    InvH w (Fintype.card P - t) v₀ ((alg w t v₀).initCfg) [] ⟨fun _ _ => 0, fun _ => 0⟩ where
  wf := by intro β ℓ γ h; simp at h
  ops := by simp
  cnt := by simp [Protocol.initCfg, alg, Loc.init]
  own_w := by simp [Protocol.initCfg, alg, Loc.init, W]
  ph_w3 := by simp [Protocol.initCfg, alg, Loc.init]
  ph_r7 := by simp [Protocol.initCfg, alg, Loc.init]
  ph_r9 := by simp [Protocol.initCfg, alg, Loc.init]
  hist_w := by simp [Protocol.initCfg, alg, Loc.init, Hw, W]
  write_resp := by simp [opOf]
  pipe_snap := by simp [PipeSnap, Protocol.initCfg, alg, Loc.init]
  snap_le := by simp
  q_write := by simp [Completed]
  q_read := by simp [Completed]
  r7_req := by simp [Protocol.initCfg, alg, Loc.init]
  r9_req := by simp [Protocol.initCfg, alg, Loc.init]
  read_val := by simp [Completed]
  rf_le := by simp [Completed]
  not_future := by simp [Completed]
  not_overwritten := by simp [Completed]
  mono := by simp [Completed]

/-! ## History lemmas -/

section HistoryLemmas

variable {A : ObjSpec}

lemma completed_append_of_not_ret {h : List (Label P A)} {ℓ : Label P A}
    (hℓ : ∀ p r, ℓ ≠ .ret p r) (x : OpId P) : Completed (h ++ [ℓ]) x ↔ Completed h x := by
  cases ℓ with
  | ret p r => exact absurd rfl (hℓ p r)
  | inv p o => simp [Completed]
  | tau p => simp [Completed]

lemma respOf_append_of_not_ret {h : List (Label P A)} {ℓ : Label P A}
    (hℓ : ∀ p r, ℓ ≠ .ret p r) (x : OpId P) : respOf (h ++ [ℓ]) x = respOf h x := by
  cases ℓ with
  | ret p r => exact absurd rfl (hℓ p r)
  | inv p o => simp [respOf]
  | tau p => simp [respOf]

/-- A pending operation is the current one and has been invoked. -/
lemma invoked_cur_of_pending {h : List (Label P A)} {i : P}
    (hc : (opsOf h i).length = (respsOf h i).length + 1) : Invoked h (cur h i) := by
  simp only [Invoked, cur]; omega

lemma req_append_iff {w : P} {h β : List (Label P A)} {rf : OpId P → ℕ} {i : P} {m : ℕ}
    (hinv : Invoked h (cur h i)) (hcur : cur (h ++ β) i = cur h i) :
    Req w (h ++ β) rf i m ↔ Req w h rf i m := by
  simp only [Req, hcur, precedes_append_iff_of_invoked hinv]

lemma completed_append_ret {h : List (Label P A)} {p : P} {r : A.Resp} (x : OpId P) :
    Completed (h ++ [.ret p r]) x ↔ Completed h x ∨ x = (p, (respsOf h p).length) := by
  obtain ⟨q, k⟩ := x
  simp only [Completed, respsOf_append, respsOf_cons, Label.retOf_ret, respsOf_nil,
    List.append_nil, List.length_append, Prod.mk.injEq]
  by_cases hq : p = q
  · subst hq; simp; omega
  · simp [hq, Ne.symm hq]

lemma completed_append_ret_of_ne {h : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (hx : x.1 ≠ p) : Completed (h ++ [.ret p r]) x ↔ Completed h x := by
  rw [completed_append_ret]
  constructor
  · rintro (h1 | rfl)
    · exact h1
    · exact absurd rfl hx
  · exact Or.inl

lemma respOf_append_ret_of_ne {h : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (hx : x.1 ≠ p) : respOf (h ++ [.ret p r]) x = respOf h x := by
  rw [respOf_append_ret, if_neg (fun he => hx (by rw [he]))]

end HistoryLemmas

namespace InvH

variable {w : P} {t : ℕ} {v₀ : V} {C : Cfg P V} {h : List (Label P (register V v₀))}
  {g : Ghost P}

local notation "Q" => Fintype.card P - t

lemma pending (hH : InvH w Q v₀ C h g) {i : P} (hi : (C.loc i).phase ≠ .idle) :
    (opsOf h i).length = (respsOf h i).length + 1 := by
  have := hH.cnt i; rw [if_neg hi] at this; exact this

lemma idle (hH : InvH w Q v₀ C h g) {i : P} (hi : (C.loc i).phase = .idle) :
    (opsOf h i).length = (respsOf h i).length := by
  have := hH.cnt i; rw [if_pos hi] at this; exact this

/-- Lines 1–2. -/
lemma of_invoke_write (hH : InvH w Q v₀ C h g) {p : P} {v : V} {l : Loc P V}
    {out : Multiset (P × Msg V)} (hinv : invoke w p (.write v) (C.loc p) = some (l, out)) :
    InvH w Q v₀ (C.apply p l out C.net) (h ++ [.inv p (.write v)]) g := by
  obtain ⟨hpw, hidle, rfl, rfl⟩ := invoke_write hinv
  subst p
  set C' := C.apply w _ _ C.net with hC'
  obtain ⟨o, ho⟩ : ∃ o, o = W C w w := ⟨_, rfl⟩
  have hlen : (opsOf h w).length = o := by rw [ho, hH.own_w]
  have hidle' := hH.idle hidle
  have hphw : (C'.loc w).phase = .w3 (o + 1) := by simp [hC', ho, W]
  have hpho : ∀ q, q ≠ w → (C'.loc q).phase = (C.loc q).phase := by intro q hq; simp [hC', hq]
  have hWw : ∀ j, W C' w j = if j = w then o + 1 else W C w j := by
    intro j; by_cases hj : j = w <;> simp [hC', W, hj, ho]
  have hWo : ∀ i, i ≠ w → ∀ j, W C' i j = W C i j := by intro i hi j; simp [hC', W, hi]
  have hWmono : ∀ i j, W C i j ≤ W C' i j := by
    intro i j
    by_cases hi : i = w
    · subst hi; rw [hWw]; split_ifs with hj
      · subst hj; omega
      · exact le_refl _
    · rw [hWo i hi]
  have hHw : ∀ k, Hw w C' k = if k = o + 1 then v else Hw w C k := by
    intro k; by_cases hk : k = o + 1 <;> simp [hC', Hw, hk, Function.update_apply, ho, W]
  have hops : ∀ q, opsOf (h ++ [.inv w (.write v)]) q =
      opsOf h q ++ if q = w then [.write v] else [] := by
    intro q; by_cases hq : q = w
    · subst hq; simp
    · simp [hq, Ne.symm hq]
  have hresps : ∀ q, respsOf (h ++ [.inv w (.write v)]) q = respsOf h q := by intro q; simp
  have hcompl := completed_append_of_not_ret (h := h) (ℓ := .inv w (.write v))
    (fun _ _ => by simp)
  have hresp := respOf_append_of_not_ret (h := h) (ℓ := .inv w (.write v)) (fun _ _ => by simp)
  have hreq : ∀ i, (C.loc i).phase ≠ .idle → ∀ m,
      Req w (h ++ [.inv w (.write v)]) g.rf i m ↔ Req w h g.rf i m := by
    intro i hi m
    exact req_append_iff (invoked_cur_of_pending (hH.pending hi)) (by simp [cur, hresps])
  have hwv : writeVal v₀ (opsOf h w ++ [.write v]) (o + 1) = v :=
    writeVal_succ (by simp [hlen])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.wf.append_inv hidle'
  · intro q o' ho'
    rw [hops] at ho'
    rcases List.mem_append.1 ho' with ho' | ho'
    · exact hH.ops q o' ho'
    · split_ifs at ho' with hq
      · simp only [List.mem_singleton] at ho'; exact Or.inl ⟨hq, v, ho'⟩
      · simp at ho'
  · intro q
    rw [hops, hresps]
    by_cases hq : q = w
    · subst hq; rw [hphw]; simp [hidle']
    · rw [hpho q hq]; simp [hq, hH.cnt q]
  · rw [hWw, if_pos rfl, hops, if_pos rfl]; simp [hlen]
  · intro q wsn hq
    by_cases hqw : q = w
    · subst hqw; rw [hphw] at hq; simp only [Phase.w3.injEq] at hq
      rw [hWw, if_pos rfl]; exact ⟨rfl, hq.symm⟩
    · rw [hpho q hqw] at hq; exact absurd (hH.ph_w3 q wsn hq).1 hqw
  · intro q n hq
    by_cases hqw : q = w
    · subst hqw; rw [hphw] at hq; simp at hq
    · rw [hpho q hqw] at hq; exact hH.ph_r7 q n hq
  · intro q n hq
    by_cases hqw : q = w
    · subst hqw; rw [hphw] at hq; simp at hq
    · rw [hpho q hqw] at hq; obtain ⟨h1, h2⟩ := hH.ph_r9 q n hq
      exact ⟨h1, h2.trans (hWmono q q)⟩
  · intro k hk
    rw [hWw, if_pos rfl] at hk
    rw [hops, if_pos rfl, hHw]
    split_ifs with hk'
    · subst hk'; exact hwv.symm
    · rw [writeVal_append_of_le (by omega)]; exact hH.hist_w k (by omega)
  · intro j v' x hop hrx
    rw [hresp] at hrx
    have hj : j < (respsOf h w).length := (List.getElem?_eq_some_iff.1 hrx).1
    have hj' : Invoked h (w, j) := by simp only [Invoked]; omega
    rw [opOf_append_of_invoked hj'] at hop
    exact hH.write_resp j v' x hop hrx
  · refine hH.pipe_snap.mono (by simp [hC']) ?_ hWmono ?_ ?_
    · intro i rsn hi
      by_cases hiw : i = w
      · subst hiw; rw [hphw] at hi; simp at hi
      · rwa [hpho i hiw] at hi
    · intro i j _ hm; simp [hC', hm]
    · intro j x hx
      by_cases hj : j = w
      · subst hj; simpa [hC'] using hx
      · simpa [hC', hj] using hx
  · intro i j; exact (hH.snap_le i j).trans (hWmono j j)
  · intro k hk; rw [hcompl] at hk
    exact (hH.q_write k hk).trans (count_mono (fun j hj => hj.trans (hWmono j j)))
  · intro y hy hc; rw [hcompl] at hc
    exact (hH.q_read y hy hc).trans (count_mono (fun j hj => hj.trans (hWmono j j)))
  · intro i rsn m hi hr
    have hiw : i ≠ w := by intro he; subst he; rw [hphw] at hi; simp at hi
    rw [hpho i hiw] at hi
    rw [hreq i (by rw [hi]; simp) m] at hr
    exact hH.r7_req i rsn m hi hr
  · intro i sn m hi hr
    have hiw : i ≠ w := by intro he; subst he; rw [hphw] at hi; simp at hi
    rw [hpho i hiw] at hi
    rw [hreq i (by rw [hi]; simp) m] at hr
    exact hH.r9_req i sn m hi hr
  · intro x hx hc
    rw [hcompl] at hc
    rw [hresp, hH.read_val x hx hc, hops, if_pos rfl, writeVal_append_of_le (hH.rf_le x hx hc)]
  · intro x hx hc
    rw [hcompl] at hc
    rw [hops, if_pos rfl]; simp only [List.length_append]
    have := hH.rf_le x hx hc; simp; omega
  · intro x hx hc hpos hpre
    rw [hcompl] at hc
    have hinv : Invoked h (w, g.rf x - 1) := by
      have := hH.rf_le x hx hc; simp only [Invoked]; omega
    exact hH.not_future x hx hc hpos ((precedes_append_iff_of_invoked hinv).1 hpre)
  · intro x hx hc hpre
    rw [hcompl] at hc
    exact hH.not_overwritten x hx hc
      ((precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre)
  · intro x y hx hy hc hpre
    rw [hcompl] at hc
    exact hH.mono x y hx hy hc
      ((precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre)

/-- Lines 5–6 (the ghost `snap` of the reader is set). -/
lemma of_invoke_read (hH : InvH w Q v₀ C h g) {p : P} {l : Loc P V}
    {out : Multiset (P × Msg V)} (hinv : invoke w p .read (C.loc p) = some (l, out)) :
    InvH w Q v₀ (C.apply p l out C.net) (h ++ [.inv p .read])
      ⟨Function.update g.snap p (fun j => W C j j), g.rf⟩ := by
  obtain ⟨hpw, hidle, rfl, rfl⟩ := invoke_read hinv
  set C' := C.apply p _ _ C.net with hC'
  set g' : Ghost P := ⟨Function.update g.snap p (fun j => W C j j), g.rf⟩ with hg'
  have hidle' := hH.idle hidle
  have hphp : (C'.loc p).phase = .r7 ((C.loc p).rs p + 1) := by simp [hC']
  have hpho : ∀ q, q ≠ p → (C'.loc q).phase = (C.loc q).phase := by intro q hq; simp [hC', hq]
  have hW : ∀ i j, W C' i j = W C i j := by
    intro i j; by_cases hi : i = p
    · subst hi; simp [hC', W]
    · simp [hC', W, hi]
  have hHw : ∀ k, Hw w C' k = Hw w C k := by intro k; simp [hC', Hw, Ne.symm hpw]
  have hopsw : opsOf (h ++ [.inv p .read]) w = opsOf h w := by simp [hpw]
  have hresps : ∀ q, respsOf (h ++ [.inv p .read]) q = respsOf h q := by intro q; simp
  have hcompl := completed_append_of_not_ret (h := h) (ℓ := .inv p .read) (fun _ _ => by simp)
  have hresp := respOf_append_of_not_ret (h := h) (ℓ := .inv p .read) (fun _ _ => by simp)
  have hreq : ∀ i, (C.loc i).phase ≠ .idle → ∀ m,
      Req w (h ++ [.inv p .read]) g.rf i m ↔ Req w h g.rf i m := by
    intro i hi m
    exact req_append_iff (invoked_cur_of_pending (hH.pending hi)) (by simp [cur, hresps])
  have hsnap : ∀ i, i ≠ p → g'.snap i = g.snap i := by
    intro i hi; simp [hg', hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.wf.append_inv hidle'
  · intro q o' ho'
    by_cases hq : q = p
    · subst hq
      simp only [opsOf_append, opsOf_cons, Label.invOf_inv, ite_true, Option.toList_some,
        opsOf_nil, List.append_nil, List.mem_append, List.mem_singleton] at ho'
      rcases ho' with ho' | rfl
      · exact hH.ops q o' ho'
      · exact Or.inr ⟨hpw, rfl⟩
    · simp only [opsOf_append, opsOf_cons, Label.invOf_inv, Ne.symm hq, ite_false,
        Option.toList_none, opsOf_nil, List.append_nil] at ho'
      exact hH.ops q o' ho'
  · intro q
    rw [hresps]
    by_cases hq : q = p
    · subst hq; rw [hphp]; simp [hidle']
    · rw [hpho q hq]; simp [Ne.symm hq, hH.cnt q]
  · rw [hW, hopsw]; exact hH.own_w
  · intro q wsn hq
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq; simp at hq
    · rw [hpho q hqp] at hq; rw [hW]; exact hH.ph_w3 q wsn hq
  · intro q n hq
    by_cases hqp : q = p
    · subst hqp; exact hpw
    · rw [hpho q hqp] at hq; exact hH.ph_r7 q n hq
  · intro q n hq
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq; simp at hq
    · rw [hpho q hqp] at hq; rw [hW]; exact hH.ph_r9 q n hq
  · intro k hk; rw [hW] at hk; rw [hHw, hopsw]; exact hH.hist_w k hk
  · intro j v' x hop hrx
    rw [hresp] at hrx
    have : opOf (h ++ [.inv p .read]) (w, j) = opOf h (w, j) := by simp [opOf, hopsw]
    rw [this] at hop
    exact hH.write_resp j v' x hop hrx
  · intro i rsn hi hph j hji
    by_cases hip : i = p
    · subst hip
      refine Or.inr (Or.inl ?_)
      simp [hC', mem_outMsgs_sendTo, hji]
    · rw [hpho i hip] at hph
      rw [hsnap i hip, hW]
      rcases hH.pipe_snap i rsn hi hph j hji with h1 | h1 | ⟨sn, h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl (by simp [hC', h1]))
      · refine Or.inr (Or.inr ⟨sn, h1, ?_⟩)
        by_cases hj : j = p
        · subst hj; simpa [hC'] using h2
        · simpa [hC', hj] using h2
  · intro i j
    rw [hW]
    by_cases hip : i = p
    · subst hip; simp [hg']
    · rw [hsnap i hip]; exact hH.snap_le i j
  · intro k hk; rw [hcompl] at hk
    simp only [hW]; exact hH.q_write k hk
  · intro y hy hc; rw [hcompl] at hc
    simp only [hW]; exact hH.q_read y hy hc
  · intro i rsn m hi hr
    by_cases hip : i = p
    · subst hip
      have hcur : cur (h ++ [.inv i .read]) i = (i, (opsOf h i).length) := by
        simp [cur, hresps, hidle']
      obtain ⟨y, hy, hm⟩ := hr
      rw [hcur, precedes_append_inv_iff] at hy
      have hs : ∀ j, g'.snap i j = W C j j := by intro j; simp [hg']
      simp only [hs]
      rcases hm with ⟨hyw, rfl⟩ | ⟨hyw, rfl⟩
      · obtain ⟨y1, y2⟩ := y; simp only at hyw; subst hyw
        exact hH.q_write y2 hy
      · exact hH.q_read y hyw hy
    · rw [hpho i hip] at hi
      rw [hreq i (by rw [hi]; simp) m] at hr
      rw [hsnap i hip]
      exact hH.r7_req i rsn m hi hr
  · intro i sn m hi hr
    have hip : i ≠ p := by intro he; subst he; rw [hphp] at hi; simp at hi
    rw [hpho i hip] at hi
    rw [hreq i (by rw [hi]; simp) m] at hr
    exact hH.r9_req i sn m hi hr
  · intro x hx hc
    rw [hcompl] at hc
    rw [hresp, hopsw]; exact hH.read_val x hx hc
  · intro x hx hc; rw [hcompl] at hc; rw [hopsw]; exact hH.rf_le x hx hc
  · intro x hx hc hpos hpre
    rw [hcompl] at hc
    have hinv : Invoked h (w, g.rf x - 1) := by
      have := hH.rf_le x hx hc; have hrf : g'.rf x = g.rf x := rfl; simp only [Invoked]; omega
    exact hH.not_future x hx hc hpos ((precedes_append_iff_of_invoked hinv).1 hpre)
  · intro x hx hc hpre
    rw [hcompl] at hc
    exact hH.not_overwritten x hx hc
      ((precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre)
  · intro x y hx hy hc hpre
    rw [hcompl] at hc
    exact hH.mono x y hx hy hc
      ((precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre)

/-- Lines 3–4. -/
lemma of_wret (hH : InvH w Q v₀ C h g) (hW : InvW w C) {p : P} {l : Loc P V}
    {out : Multiset (P × Msg V)} {r : Option V} (hint : internal Q p .wret (C.loc p) = some (l, out, r)) :
    InvH w Q v₀ (C.apply p l out C.net) (h ++ (r.map (Label.ret p)).toList) g := by
  obtain ⟨wsn, hph, hq, rfl, rfl, rfl⟩ := internal_wret hint
  obtain ⟨hpw, hwsn⟩ := hH.ph_w3 p wsn hph
  subst p
  set C' := C.apply w _ _ C.net with hC'
  simp only [Option.map_some, Option.toList_some]
  have hpend := hH.pending (i := w) (by rw [hph]; simp)
  have hlen : (opsOf h w).length = wsn := by rw [hwsn, hH.own_w]
  have hphp : (C'.loc w).phase = .idle := by simp [hC']
  have hpho : ∀ q, q ≠ w → (C'.loc q).phase = (C.loc q).phase := by intro q hq; simp [hC', hq]
  have hW' : ∀ i j, W C' i j = W C i j := by
    intro i j; by_cases hi : i = w
    · subst hi; simp [hC', W]
    · simp [hC', W, hi]
  have hHw : ∀ k, Hw w C' k = Hw w C k := by intro k; simp [hC', Hw]
  set x0 : OpId P := (w, (respsOf h w).length) with hx0
  have hops : ∀ q, opsOf (h ++ [.ret w (Hw w C wsn)]) q = opsOf h q := by intro q; simp
  have hresps : ∀ q, q ≠ w → respsOf (h ++ [.ret w (Hw w C wsn)]) q = respsOf h q := by
    intro q hq; simp [Ne.symm hq]
  have hreq : ∀ i, i ≠ w → (C.loc i).phase ≠ .idle → ∀ m,
      Req w (h ++ [.ret w (Hw w C wsn)]) g.rf i m ↔ Req w h g.rf i m := by
    intro i hip hi m
    exact req_append_iff (invoked_cur_of_pending (hH.pending hi)) (by simp [cur, hresps i hip])
  -- the written value
  have hval : ∃ v, opOf h (w, wsn - 1) = some (.write v) ∧ Hw w C wsn = v := by
    have hmem : (opsOf h w)[wsn - 1]? = some ((opsOf h w)[wsn - 1]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    rcases hH.ops w _ (List.getElem_mem (by omega : wsn - 1 < (opsOf h w).length)) with
      ⟨-, v, hv⟩ | ⟨hne, -⟩
    · refine ⟨v, by simp only [opOf]; rw [hmem, hv], ?_⟩
      rw [hH.hist_w wsn (by omega)]
      have : wsn = wsn - 1 + 1 := by omega
      rw [this]; exact writeVal_succ (by rw [hmem, hv])
    · exact absurd rfl hne
  obtain ⟨v, hopv, hHv⟩ := hval
  have hx0' : x0 = (w, wsn - 1) := by rw [hx0]; congr 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.wf.append_ret hpend
  · intro q o ho; rw [hops] at ho; exact hH.ops q o ho
  · intro q
    rw [hops]
    by_cases hqp : q = w
    · subst hqp; rw [hphp]; simp [hpend]
    · rw [hpho q hqp, hresps q hqp]; exact hH.cnt q
  · rw [hW', hops]; exact hH.own_w
  · intro q n hq
    by_cases hqp : q = w
    · subst hqp; rw [hphp] at hq; simp at hq
    · rw [hpho q hqp] at hq; rw [hW']; exact hH.ph_w3 q n hq
  · intro q n hq
    by_cases hqp : q = w
    · subst hqp; rw [hphp] at hq; simp at hq
    · rw [hpho q hqp] at hq; exact hH.ph_r7 q n hq
  · intro q n hq
    by_cases hqp : q = w
    · subst hqp; rw [hphp] at hq; simp at hq
    · rw [hpho q hqp] at hq; rw [hW']; exact hH.ph_r9 q n hq
  · intro k hk; rw [hW'] at hk; rw [hHw, hops]; exact hH.hist_w k hk
  · intro j v' x hop hrx
    rw [respOf_append_ret] at hrx
    have hop' : opOf (h ++ [.ret w (Hw w C wsn)]) (w, j) = opOf h (w, j) := by simp [opOf]
    rw [hop'] at hop
    split_ifs at hrx with hj
    · simp only [Option.some.injEq] at hrx
      subst hrx
      simp only [Prod.mk.injEq, true_and] at hj
      have : j = wsn - 1 := by omega
      subst this
      rw [hop] at hopv; simp only [Option.some.injEq, RWOp.write.injEq] at hopv
      rw [hopv, ← hHv]
    · exact hH.write_resp j v' x hop hrx
  · refine hH.pipe_snap.mono (by simp [hC']) ?_ (fun i j => (hW' i j).symm ▸ le_refl _) ?_ ?_
    · intro i rsn hi
      by_cases hip : i = w
      · subst hip; rw [hphp] at hi; simp at hi
      · rwa [hpho i hip] at hi
    · intro i j _ hm; simpa [hC'] using hm
    · intro j x hx
      by_cases hj : j = w
      · subst hj; simpa [hC'] using hx
      · simpa [hC', hj] using hx
  · intro i j; rw [hW']; exact hH.snap_le i j
  · intro k hk
    simp only [hW']
    rw [completed_append_ret] at hk
    rcases hk with hk | hk
    · exact hH.q_write k hk
    · simp only [Prod.mk.injEq, true_and] at hk
      refine hq.trans (count_mono ?_)
      intro j hj
      have : k + 1 = wsn := by omega
      rw [this]
      by_cases hjp : j = w
      · subst hjp; simp only [W] at hj hwsn ⊢; omega
      · have h1 := hW.recv_le j w hjp
        have h2 := InvW.sent_le_own C j w
        simp only [W] at hj h1 h2 ⊢; omega
  · intro y hy hc
    rw [completed_append_ret_of_ne hy] at hc
    simp only [hW']; exact hH.q_read y hy hc
  · intro i rsn m hi hr
    have hip : i ≠ w := by intro he; subst he; rw [hphp] at hi; simp at hi
    rw [hpho i hip] at hi
    rw [hreq i hip (by rw [hi]; simp) m] at hr
    exact hH.r7_req i rsn m hi hr
  · intro i sn m hi hr
    have hip : i ≠ w := by intro he; subst he; rw [hphp] at hi; simp at hi
    rw [hpho i hip] at hi
    rw [hreq i hip (by rw [hi]; simp) m] at hr
    exact hH.r9_req i sn m hi hr
  · intro x hx hc
    rw [completed_append_ret_of_ne hx] at hc
    rw [respOf_append_ret_of_ne hx, hops]; exact hH.read_val x hx hc
  · intro x hx hc; rw [completed_append_ret_of_ne hx] at hc; rw [hops]; exact hH.rf_le x hx hc
  · intro x hx hc hpos hpre
    rw [completed_append_ret_of_ne hx] at hc
    have hinv : Invoked h (w, g.rf x - 1) := by
      have := hH.rf_le x hx hc; simp only [Invoked]; omega
    exact hH.not_future x hx hc hpos ((precedes_append_iff_of_invoked hinv).1 hpre)
  · intro x hx hc hpre
    rw [completed_append_ret_of_ne hx] at hc
    exact hH.not_overwritten x hx hc
      ((precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre)
  · intro x y hx hy hc hpre
    rw [completed_append_ret_of_ne hy] at hc
    exact hH.mono x y hx hy hc
      ((precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre)

/-- Lines 7–8: the quorum intersection argument of Claims 2 and 3 of Lemma 10. -/
lemma of_r8 (hH : InvH w Q v₀ C h g) (hW : InvW w C) (hP : InvP C) (ht : 2 * t < Fintype.card P)
    {p : P} (hpc : p ∉ C.crashed) {l : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (hint : internal Q p .r8 (C.loc p) = some (l, out, r)) :
    InvH w Q v₀ (C.apply p l out C.net) (h ++ (r.map (Label.ret p)).toList) g := by
  obtain ⟨rsn, hph, hq, rfl, rfl, rfl⟩ := internal_r8 hint
  simp only [Option.map_none, Option.toList_none, List.append_nil]
  set C' := C.apply p _ _ C.net with hC'
  have hphp : (C'.loc p).phase = .r9 (W C p p) := by simp [hC', W]
  have hpho : ∀ q, q ≠ p → (C'.loc q).phase = (C.loc q).phase := by intro q hq; simp [hC', hq]
  have hW' : ∀ i j, W C' i j = W C i j := by
    intro i j; by_cases hi : i = p
    · subst hi; simp [hC', W]
    · simp [hC', W, hi]
  have hpw : p ≠ w := hH.ph_r7 p rsn hph
  have hHw : ∀ k, Hw w C' k = Hw w C k := by intro k; simp [hC', Hw, Ne.symm hpw]
  -- the key step
  have hkey : ∀ m, Req w h g.rf p m → m ≤ W C p p := by
    intro m hm
    obtain ⟨j, hj1, hj2⟩ := quorum_inter ht (hH.r7_req p rsn m hph hm) hq
    by_cases hjp : j = p
    · subst hjp; exact hj1.trans (hH.snap_le j j)
    · have hpipe := hP.pipe p j (Ne.symm hjp)
      have hrsn := hP.r7_rsn p rsn hph
      simp only [R] at hpipe hrsn hj2
      rcases hH.pipe_snap p rsn hpc hph j hjp with h1 | h1 | ⟨sn, h1, h2⟩
      · have h3 := hW.recv_le p j (Ne.symm hjp)
        have h4 := InvW.sent_le_own C p j
        omega
      · have := Multiset.count_pos.2 h1
        simp only [cR] at hpipe; omega
      · have : 0 < tk C j p := Multiset.countP_pos.2 ⟨_, h2, rfl⟩
        omega
  refine ⟨hH.wf, hH.ops, ?_, ?_, ?_, ?_, ?_, ?_, hH.write_resp, ?_, ?_, ?_, ?_, ?_, ?_,
    hH.read_val, hH.rf_le, hH.not_future, hH.not_overwritten, hH.mono⟩
  · intro q
    by_cases hqp : q = p
    · subst hqp; rw [hphp, hH.cnt q, hph]; simp
    · rw [hpho q hqp]; exact hH.cnt q
  · rw [hW']; exact hH.own_w
  · intro q n hq'
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq'; simp at hq'
    · rw [hpho q hqp] at hq'; rw [hW']; exact hH.ph_w3 q n hq'
  · intro q n hq'
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq'; simp at hq'
    · rw [hpho q hqp] at hq'; exact hH.ph_r7 q n hq'
  · intro q n hq'
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq'; simp only [Phase.r9.injEq] at hq'
      rw [hW', ← hq']; exact ⟨hpw, le_refl _⟩
    · rw [hpho q hqp] at hq'; rw [hW']; exact hH.ph_r9 q n hq'
  · intro k hk; rw [hW'] at hk; rw [hHw]; exact hH.hist_w k hk
  · refine hH.pipe_snap.mono (by simp [hC']) ?_ (fun i j => (hW' i j).symm ▸ le_refl _) ?_ ?_
    · intro i rsn' hi
      by_cases hip : i = p
      · subst hip; rw [hphp] at hi; simp at hi
      · rwa [hpho i hip] at hi
    · intro i j _ hm; simpa [hC'] using hm
    · intro j x hx
      by_cases hj : j = p
      · subst hj; simpa [hC'] using hx
      · simpa [hC', hj] using hx
  · intro i j; rw [hW']; exact hH.snap_le i j
  · intro k hk; simp only [hW']; exact hH.q_write k hk
  · intro y hy hc; simp only [hW']; exact hH.q_read y hy hc
  · intro i rsn' m hi hr
    have hip : i ≠ p := by intro he; subst he; rw [hphp] at hi; simp at hi
    rw [hpho i hip] at hi
    exact hH.r7_req i rsn' m hi hr
  · intro i sn m hi hr
    by_cases hip : i = p
    · subst hip; rw [hphp] at hi; simp only [Phase.r9.injEq] at hi
      rw [← hi]; exact hkey m hr
    · rw [hpho i hip] at hi; exact hH.r9_req i sn m hi hr

/-- Lines 9–10: the read returns `history_i[sn]`; the ghost `rf` records `sn`. -/
lemma of_rret (hH : InvH w Q v₀ C h g) (hW : InvW w C) {p : P} {l : Loc P V}
    {out : Multiset (P × Msg V)} {r : Option V}
    (hint : internal Q p .rret (C.loc p) = some (l, out, r)) :
    ∃ sn, InvH w Q v₀ (C.apply p l out C.net) (h ++ (r.map (Label.ret p)).toList)
      ⟨g.snap, Function.update g.rf (cur h p) sn⟩ := by
  obtain ⟨sn, hph, hq, rfl, rfl, rfl⟩ := internal_rret hint
  refine ⟨sn, ?_⟩
  simp only [Option.map_some, Option.toList_some]
  set C' := C.apply p _ _ C.net with hC'
  set x0 := cur h p with hx0
  set g' : Ghost P := ⟨g.snap, Function.update g.rf x0 sn⟩ with hg'
  obtain ⟨hpw, hsn⟩ := hH.ph_r9 p sn hph
  have hpend := hH.pending (i := p) (by rw [hph]; simp)
  have hphp : (C'.loc p).phase = .idle := by simp [hC']
  have hpho : ∀ q, q ≠ p → (C'.loc q).phase = (C.loc q).phase := by intro q hq; simp [hC', hq]
  have hW' : ∀ i j, W C' i j = W C i j := by
    intro i j; by_cases hi : i = p
    · subst hi; simp [hC', W]
    · simp [hC', W, hi]
  have hHw : ∀ k, Hw w C' k = Hw w C k := by intro k; simp [hC', Hw, Ne.symm hpw]
  set v := (C.loc p).hist sn with hv
  have hopsw : opsOf (h ++ [.ret p v]) w = opsOf h w := by simp
  have hops : ∀ q, opsOf (h ++ [.ret p v]) q = opsOf h q := by intro q; simp
  have hresps : ∀ q, q ≠ p → respsOf (h ++ [.ret p v]) q = respsOf h q := by
    intro q hq; simp [Ne.symm hq]
  have hx0' : x0 = (p, (respsOf h p).length) := rfl
  have hx0nc : ¬ Completed h x0 := by simp [hx0, cur, Completed]
  have hx0inv : Invoked h x0 := invoked_cur_of_pending hpend
  have hrf : ∀ y, y ≠ x0 → g'.rf y = g.rf y := by
    intro y hy; simp [hg', Function.update_of_ne hy]
  have hrf0 : g'.rf x0 = sn := by simp [hg']
  have hcompl : ∀ y, Completed (h ++ [.ret p v]) y ↔ Completed h y ∨ y = x0 :=
    fun y => completed_append_ret y
  have hne_of_compl : ∀ y, Completed h y → y ≠ x0 := by
    rintro y hy rfl; exact hx0nc hy
  -- requirements of other readers are unchanged
  have hreq : ∀ i, i ≠ p → (C.loc i).phase ≠ .idle → ∀ m,
      Req w (h ++ [.ret p v]) g'.rf i m → Req w h g.rf i m := by
    intro i hip hi m hr
    obtain ⟨y, hy, hm⟩ := hr
    have hcur : cur (h ++ [.ret p v]) i = cur h i := by simp [cur, hresps i hip]
    rw [hcur, precedes_append_iff_of_invoked (invoked_cur_of_pending (hH.pending hi))] at hy
    refine ⟨y, hy, ?_⟩
    rwa [hrf y (hne_of_compl y hy.completed)] at hm
  -- the value returned
  have hval : v = writeVal v₀ (opsOf h w) sn := by
    rw [hv, hW.hist p sn hsn]
    exact hH.hist_w sn (hsn.trans (hW.own_le p))
  have hsnw : sn ≤ (opsOf h w).length := by
    rw [← hH.own_w]; exact hsn.trans (hW.own_le p)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.wf.append_ret hpend
  · intro q o ho; rw [hops] at ho; exact hH.ops q o ho
  · intro q
    rw [hops]
    by_cases hqp : q = p
    · subst hqp; rw [hphp]; simp [hpend]
    · rw [hpho q hqp, hresps q hqp]; exact hH.cnt q
  · rw [hW', hopsw]; exact hH.own_w
  · intro q n hq'
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq'; simp at hq'
    · rw [hpho q hqp] at hq'; rw [hW']; exact hH.ph_w3 q n hq'
  · intro q n hq'
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq'; simp at hq'
    · rw [hpho q hqp] at hq'; exact hH.ph_r7 q n hq'
  · intro q n hq'
    by_cases hqp : q = p
    · subst hqp; rw [hphp] at hq'; simp at hq'
    · rw [hpho q hqp] at hq'; rw [hW']; exact hH.ph_r9 q n hq'
  · intro k hk; rw [hW'] at hk; rw [hHw, hopsw]; exact hH.hist_w k hk
  · intro j v' x hop hrx
    rw [respOf_append_ret_of_ne (by simpa using hpw.symm)] at hrx
    have : opOf (h ++ [.ret p v]) (w, j) = opOf h (w, j) := by simp [opOf]
    rw [this] at hop
    exact hH.write_resp j v' x hop hrx
  · refine hH.pipe_snap.mono (by simp [hC']) ?_ (fun i j => (hW' i j).symm ▸ le_refl _) ?_ ?_
    · intro i rsn' hi
      by_cases hip : i = p
      · subst hip; rw [hphp] at hi; simp at hi
      · rwa [hpho i hip] at hi
    · intro i j _ hm; simpa [hC'] using hm
    · intro j x hx
      by_cases hj : j = p
      · subst hj; simpa [hC'] using hx
      · simpa [hC', hj] using hx
  · intro i j; rw [hW']; exact hH.snap_le i j
  · intro k hk
    rw [completed_append_ret_of_ne (by simpa using hpw.symm)] at hk
    simp only [hW']; exact hH.q_write k hk
  · intro y hy hc
    simp only [hW']
    rw [hcompl] at hc
    rcases hc with hc | rfl
    · rw [hrf y (hne_of_compl y hc)]; exact hH.q_read y hy hc
    · rw [hrf0]
      refine hq.trans (count_mono ?_)
      intro j hj
      by_cases hjp : j = p
      · subst hjp; exact hj
      · have h1 := hW.recv_le j p hjp
        have h2 := InvW.sent_le_own C j p
        simp only [W] at h1 h2 ⊢; omega
  · intro i rsn m hi hr
    have hip : i ≠ p := by intro he; subst he; rw [hphp] at hi; simp at hi
    rw [hpho i hip] at hi
    exact hH.r7_req i rsn m hi (hreq i hip (by rw [hi]; simp) m hr)
  · intro i sn' m hi hr
    have hip : i ≠ p := by intro he; subst he; rw [hphp] at hi; simp at hi
    rw [hpho i hip] at hi
    exact hH.r9_req i sn' m hi (hreq i hip (by rw [hi]; simp) m hr)
  · intro x hx hc
    rw [hopsw]
    rw [hcompl] at hc
    rcases hc with hc | rfl
    · have hne := hne_of_compl x hc
      rw [hrf x hne, respOf_append_ret, if_neg (fun he => hne (he.trans hx0'.symm))]
      exact hH.read_val x hx hc
    · rw [hrf0, respOf_append_ret, if_pos hx0', hval]
  · intro x hx hc
    rw [hopsw]
    rw [hcompl] at hc
    rcases hc with hc | rfl
    · rw [hrf x (hne_of_compl x hc)]; exact hH.rf_le x hx hc
    · rw [hrf0]; exact hsnw
  · intro x hx hc hpos hpre
    rw [hcompl] at hc
    rcases hc with hc | rfl
    · have hne := hne_of_compl x hc
      rw [hrf x hne] at hpos hpre
      have hinv : Invoked h (w, g.rf x - 1) := by
        have := hH.rf_le x hx hc; simp only [Invoked]; omega
      exact hH.not_future x hx hc hpos ((precedes_append_iff_of_invoked hinv).1 hpre)
    · rw [hrf0] at hpos hpre
      have hinv : Invoked h (w, sn - 1) := by simp only [Invoked]; omega
      exact Precedes.not_of_invoked hinv hx0nc hpre
  · intro x hx hc hpre
    rw [hcompl] at hc
    rcases hc with hc | rfl
    · have hne := hne_of_compl x hc
      rw [hrf x hne] at hpre
      exact hH.not_overwritten x hx hc
        ((precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre)
    · rw [hrf0] at hpre
      have hpre' := (precedes_append_iff_of_invoked hx0inv).1 hpre
      have := hH.r9_req p sn (sn + 1) hph ⟨(w, sn), hpre', Or.inl ⟨rfl, rfl⟩⟩
      omega
  · intro x y hx hy hc hpre
    rw [hcompl] at hc
    rcases hc with hc | rfl
    · -- `y` completed before
      have hney := hne_of_compl y hc
      have hpre' := (precedes_append_iff_of_invoked (hH.wf.invoked_of_completed hc)).1 hpre
      have hnex := hne_of_compl x hpre'.completed
      rw [hrf x hnex, hrf y hney]
      exact hH.mono x y hx hy hc hpre'
    · -- `y` is the returning read
      have hpre' := (precedes_append_iff_of_invoked hx0inv).1 hpre
      have hnex := hne_of_compl x hpre'.completed
      rw [hrf x hnex, hrf0]
      exact hH.r9_req p sn (g.rf x) hph ⟨x, hpre', Or.inr ⟨hx, rfl⟩⟩

/-- Lines 11–18. -/
lemma of_recv_write (hH : InvH w Q v₀ C h g) (hI : InvW w C) {src dst : P} {b : Bool} {v : V}
    (hm : (src, dst, Msg.write b v) ∈ C.net) {l : Loc P V} {out : Multiset (P × Msg V)}
    {r : Option V} (hrc : receive dst src (.write b v) (C.loc dst) = some (l, out, r)) :
    InvH w Q v₀ (C.apply dst l out (C.net.erase (src, dst, .write b v))) h g := by
  obtain ⟨hb, -, hcase0⟩ := receive_write hrc
  obtain ⟨hqp, hsq, -, -, -⟩ := hI.recv_facts hm hb
  have hle0 := hI.ws_le dst src
  have himpf : ¬ ((C.loc dst).ws dst + 1 < (C.loc dst).ws src + 1) := by
    simp only [W] at hle0; omega
  set C' := C.apply dst l out (C.net.erase (src, dst, .write b v)) with hC'
  -- common facts
  have hph : ∀ q, (C'.loc q).phase = (C.loc q).phase := by
    intro q; by_cases hq : q = dst
    · subst hq; rcases hcase0 with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | himp
      all_goals first | exact absurd ‹_› himpf | simp [hC']
    · simp [hC', hq]
  have htasks : ∀ q, (C'.loc q).tasks = (C.loc q).tasks := by
    intro q; by_cases hq : q = dst
    · subst hq; rcases hcase0 with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | himp
      all_goals first | exact absurd ‹_› himpf | simp [hC']
    · simp [hC', hq]
  have hWo : ∀ i, i ≠ dst → ∀ j, W C' i j = W C i j := by intro i hi j; simp [hC', W, hi]
  have hHo : ∀ k, dst ≠ w → Hw w C' k = Hw w C k := by intro k hd; simp [hC', Hw, Ne.symm hd]
  have hown := hI.own_le src
  have hsent := InvW.sent_le_own C src dst
  have hle := hI.ws_le dst src
  rcases hcase0 with ⟨ha, rfl, rfl⟩ | ⟨hlt, rfl, rfl⟩ | ⟨heq, rfl, rfl⟩ | himp
  rotate_left 3
  · exact absurd himp himpf
  · have hdw : dst ≠ w := by
      rintro rfl; simp only [W] at ha hsq hown hsent; omega
    have hWd : ∀ j, W C dst j ≤ W C' dst j := by
      intro j
      by_cases hj : j = src
      · subst hj; simp [hC', W]
      · by_cases hj' : j = dst
        · subst hj'; simp [hC', W, hj, ha]
        · simp [hC', W, hj, hj', Function.update_apply]
    have hW : ∀ i j, W C i j ≤ W C' i j := by
      intro i j; by_cases hi : i = dst
      · subst hi; exact hWd j
      · rw [hWo i hi]
    refine hH.frame hph hW (hWo w (Ne.symm hdw) w) (fun k _ => hHo k hdw) ?_
    refine hH.pipe_snap.mono (by simp [hC']) (fun i rsn h => by rwa [hph] at h) hW ?_ ?_
    · intro i j _ hr
      simp only [hC', Config.apply_net, Multiset.mem_add]
      exact Or.inl ((Multiset.mem_erase_of_ne (by simp)).2 hr)
    · intro j x hx; rw [htasks]; exact hx
  all_goals
    have hW : ∀ i j, W C i j ≤ W C' i j := by
      intro i j; by_cases hi : i = dst
      · subst hi
        by_cases hj : j = src
        · subst hj; simp [hC', W]
        · simp [hC', W, hj, Function.update_apply]
      · rw [hWo i hi]
    have hWw : W C' w w = W C w w := by
      by_cases hdw : dst = w
      · subst hdw; simp [hC', W, Ne.symm hqp]
      · exact hWo w (Ne.symm hdw) w
    have hHw : ∀ k, Hw w C' k = Hw w C k := by
      intro k; by_cases hdw : dst = w
      · subst hdw; simp [hC', Hw]
      · exact hHo k hdw
    refine hH.frame hph hW hWw (fun k _ => hHw k) ?_
    refine hH.pipe_snap.mono (by simp [hC']) (fun i rsn h => by rwa [hph] at h) hW ?_ ?_
    · intro i j _ hr
      simp only [hC', Config.apply_net, Multiset.mem_add]
      exact Or.inl ((Multiset.mem_erase_of_ne (by simp)).2 hr)
    · intro j x hx; rw [htasks]; exact hx

/-- Line 19. -/
lemma of_recv_read (hH : InvH w Q v₀ C h g) {src dst : P} (hm : (src, dst, Msg.read) ∈ C.net)
    {l : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (hrc : receive dst src .read (C.loc dst) = some (l, out, r)) :
    InvH w Q v₀ (C.apply dst l out (C.net.erase (src, dst, .read))) h g := by
  obtain ⟨rfl, rfl, -⟩ := receive_read hrc
  set C' := C.apply dst _ _ (C.net.erase (src, dst, .read)) with hC'
  have hph : ∀ q, (C'.loc q).phase = (C.loc q).phase := by
    intro q; by_cases hq : q = dst
    · subst hq; simp [hC']
    · simp [hC', hq]
  have hW : ∀ i j, W C' i j = W C i j := by
    intro i j; by_cases hi : i = dst
    · subst hi; simp [hC', W]
    · simp [hC', W, hi]
  have hHw : ∀ k, Hw w C' k = Hw w C k := by
    intro k; by_cases hdw : w = dst
    · subst hdw; simp [hC', Hw]
    · simp [hC', Hw, hdw]
  refine hH.frame hph (fun i j => (hW i j).symm ▸ le_refl _) (hW w w) (fun k _ => hHw k) ?_
  intro i rsn hi hph' j hji
  rw [hph] at hph'
  rw [hW]
  by_cases hij : i = src ∧ j = dst
  · obtain ⟨rfl, rfl⟩ := hij
    refine Or.inr (Or.inr ⟨W C j j, hH.snap_le i j, ?_⟩)
    simp [hC', W]
  · rcases hH.pipe_snap i rsn hi hph' j hji with h1 | h1 | ⟨sn, h1, h2⟩
    · exact Or.inl h1
    · refine Or.inr (Or.inl ?_)
      simp only [hC', Config.apply_net, Multiset.mem_add]
      refine Or.inl ((Multiset.mem_erase_of_ne ?_).2 h1)
      simp only [ne_eq, Prod.mk.injEq, and_true]; exact hij
    · refine Or.inr (Or.inr ⟨sn, h1, ?_⟩)
      by_cases hj : j = dst
      · subst hj; simp [hC', h2]
      · simpa [hC', hj] using h2

/-- Line 22. -/
lemma of_recv_proceed (hH : InvH w Q v₀ C h g) {src dst : P}
    {l : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (hrc : receive dst src .proceed (C.loc dst) = some (l, out, r)) :
    InvH w Q v₀ (C.apply dst l out (C.net.erase (src, dst, .proceed))) h g := by
  obtain ⟨rfl, rfl, -⟩ := receive_proceed hrc
  set C' := C.apply dst _ _ (C.net.erase (src, dst, .proceed)) with hC'
  have hph : ∀ q, (C'.loc q).phase = (C.loc q).phase := by
    intro q; by_cases hq : q = dst
    · subst hq; simp [hC']
    · simp [hC', hq]
  have hW : ∀ i j, W C' i j = W C i j := by
    intro i j; by_cases hi : i = dst
    · subst hi; simp [hC', W]
    · simp [hC', W, hi]
  have hHw : ∀ k, Hw w C' k = Hw w C k := by
    intro k; by_cases hdw : w = dst
    · subst hdw; simp [hC', Hw]
    · simp [hC', Hw, hdw]
  refine hH.frame hph (fun i j => (hW i j).symm ▸ le_refl _) (hW w w) (fun k _ => hHw k) ?_
  refine hH.pipe_snap.mono (by simp [hC']) (fun i rsn h => by rwa [hph] at h)
    (fun i j => (hW i j).symm ▸ le_refl _) ?_ ?_
  · intro i j _ hr
    simp only [hC', Config.apply_net, Multiset.mem_add]
    exact Or.inl ((Multiset.mem_erase_of_ne (by simp)).2 hr)
  · intro j x hx
    by_cases hj : j = dst
    · subst hj; simpa [hC'] using hx
    · simpa [hC', hj] using hx

/-- Lines 20–21. -/
lemma of_proceed (hH : InvH w Q v₀ C h g) {p j : P} {sn : ℕ}
    {l : Loc P V} {out : Multiset (P × Msg V)} {r : Option V}
    (hint : internal Q p (.proceed j sn) (C.loc p) = some (l, out, r)) :
    InvH w Q v₀ (C.apply p l out C.net) (h ++ (r.map (Label.ret p)).toList) g := by
  obtain ⟨hmem, hle, rfl, rfl, rfl⟩ := internal_proceed hint
  simp only [Option.map_none, Option.toList_none, List.append_nil]
  set C' := C.apply p _ _ C.net with hC'
  have hph : ∀ q, (C'.loc q).phase = (C.loc q).phase := by
    intro q; by_cases hq : q = p
    · subst hq; simp [hC']
    · simp [hC', hq]
  have hW : ∀ i k, W C' i k = W C i k := by
    intro i k; by_cases hi : i = p
    · subst hi; simp [hC', W]
    · simp [hC', W, hi]
  have hHw : ∀ k, Hw w C' k = Hw w C k := by
    intro k; by_cases hdw : w = p
    · subst hdw; simp [hC', Hw]
    · simp [hC', Hw, hdw]
  refine hH.frame hph (fun i j => (hW i j).symm ▸ le_refl _) (hW w w) (fun k _ => hHw k) ?_
  intro i rsn hi hph' q hqi
  rw [hph] at hph'
  rw [hW]
  rcases hH.pipe_snap i rsn hi hph' q hqi with h1 | h1 | ⟨sn', h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl (by simp [hC', h1]))
  · by_cases hq : q = p
    · subst hq
      by_cases he : (i, sn') = (j, sn)
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact Or.inl (h1.trans hle)
      · refine Or.inr (Or.inr ⟨sn', h1, ?_⟩)
        simp only [hC', Config.apply_loc', ite_true]
        exact (Multiset.mem_erase_of_ne he).2 h2
    · exact Or.inr (Or.inr ⟨sn', h1, by simpa [hC', hq] using h2⟩)

end InvH

/-- **The history invariant** holds in every reachable configuration (for some ghost state). -/
theorem invH_of_reach {w : P} {t : ℕ} {v₀ : V} (ht : 2 * t < Fintype.card P) {C : Cfg P V}
    {h : List (Label P (register V v₀))} (hr : (alg w t v₀).Reach C h) :
    ∃ g, InvH w (Fintype.card P - t) v₀ C h g := by
  induction hr with
  | init => exact ⟨_, invH_init w t v₀⟩
  | @step C h s C' ℓ hr hs ih =>
    obtain ⟨g, hH⟩ := ih
    have hI := invW_of_reach hr
    have hP := invP_of_reach hr
    cases s with
    | inv p o =>
      obtain ⟨-, rfl, l, out, hinv, rfl⟩ := step_inv hs
      cases o with
      | write v => exact ⟨g, hH.of_invoke_write hinv⟩
      | read => exact ⟨_, hH.of_invoke_read hinv⟩
    | internal p a =>
      obtain ⟨hpc, l, out, r, hint, rfl, rfl⟩ := step_internal hs
      cases a with
      | wret => exact ⟨g, hH.of_wret hI hint⟩
      | r8 => exact ⟨g, hH.of_r8 hI hP ht hpc hint⟩
      | rret =>
        obtain ⟨sn, h'⟩ := hH.of_rret hI hint
        exact ⟨_, h'⟩
      | proceed j sn => exact ⟨g, hH.of_proceed hint⟩
    | recv src dst m =>
      obtain ⟨-, hm, l, out, r, hrc, rfl, rfl⟩ := step_recv hs
      have hr' : ∀ x : Option V, x = none → h ++ (x.map (Label.ret dst)).toList = h := by
        rintro x rfl; simp
      cases m with
      | write b v =>
        rw [hr' r (receive_write hrc).2.1]; exact ⟨g, hH.of_recv_write hI hm hrc⟩
      | read =>
        rw [hr' r (receive_read hrc).2.2]; exact ⟨g, hH.of_recv_read hm hrc⟩
      | proceed =>
        rw [hr' r (receive_proceed hrc).2.2]; exact ⟨g, hH.of_recv_proceed hrc⟩
    | drop src dst m =>
      obtain ⟨hsrc, -, rfl, rfl⟩ := step_drop hs
      refine ⟨g, ?_⟩
      simp only [Option.toList_none, List.append_nil]
      refine hH.frame (fun _ => rfl) (fun _ _ => le_refl _) rfl (fun _ _ => rfl) ?_
      refine hH.pipe_snap.mono (fun _ h => h) (fun _ _ h => h) (fun _ _ => le_refl _) ?_
        (fun _ _ h => h)
      intro i j hi hr
      refine (Multiset.mem_erase_of_ne ?_).2 hr
      intro he; simp only [Prod.mk.injEq] at he; exact hi (he.1 ▸ hsrc)
    | crash p =>
      obtain ⟨-, rfl, rfl⟩ := step_crash hs
      refine ⟨g, ?_⟩
      simp only [Option.toList_none, List.append_nil]
      refine hH.frame (fun _ => rfl) (fun _ _ => le_refl _) rfl (fun _ _ => rfl) ?_
      exact hH.pipe_snap.mono (Finset.subset_insert _ _) (fun _ _ h => h)
        (fun _ _ => le_refl _) (fun _ _ _ h => h) (fun _ _ h => h)
    | skip =>
      obtain ⟨rfl, rfl⟩ := step_skip hs
      exact ⟨g, by simpa using hH⟩

end Podc.TwoBit
