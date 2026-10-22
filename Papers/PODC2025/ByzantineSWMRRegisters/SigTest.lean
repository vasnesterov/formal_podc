import Podc.Computability.Distributed.SharedMemory.Byzantine.Restrict

/-!
# Signature-like objects and Lemma 28 of Hu–Toueg (PODC 2025)

The impossibility proof of Theorem 29 only uses three properties of a correct implementation of
test-or-set (Lemma 28): *validity*, *unforgeability* and *relay* of a positive test. The same
properties hold for a verifiable register (`Write(v); Sign(v)` / `Verify(v)`), an authenticated
register (`Write(v)` / `Verify(v)`, `v ≠ v₀`) and a sticky register (`Write(v)` / `Read ≠ ⊥`)
(Observations 11–13, 16–18, 22–24). We capture the common structure as `SigTest`:

* a distinguished process `s` (the setter/writer) and a sequence `setOps` of operations it
  invokes to "sign";
* a test operation `testOp` (allowed for every other process) with a positivity predicate `pos`;
* a chain of *stable* state predicates `R 0 = ⊤, R 1, …, R m` (`m = setOps.length`): the `k`-th
  set operation moves from `R k` to `R (k+1)`, the test is positive iff `R m` holds, `R m` fails
  initially, and only operations allowed for `s` can establish `R m`.

`SigTest.validity`, `SigTest.unforgeability`, `SigTest.relay` derive Lemma 28 (generalized to
every `SigTest`) from Byzantine linearizability (Definition 7).

The first part of the file contains positional lemmas on linearizations: `stAt A L j` is the
state of the object before position `j` of the sequential history `L`, and `idx L y` the position
of the operation instance `y`.
-/

namespace Podc.ByzantineSWMRRegisters

open Cslib.SharedMemory Cslib.SharedMemory.Byzantine

variable {A : ObjSpec} {P : Type} [DecidableEq P]

/-! ## Positions in linearizations -/

/-- The state before position `j` of the sequential history `L`. -/
def stAt (A : ObjSpec) (L : List (OpId P × A.Op)) (j : ℕ) : A.State :=
  A.runOps A.init ((L.take j).map Prod.snd)

omit [DecidableEq P] in
lemma stAt_zero (L : List (OpId P × A.Op)) : stAt A L 0 = A.init := by simp [stAt]

omit [DecidableEq P] in
lemma stAt_succ (L : List (OpId P × A.Op)) {j : ℕ} (hj : j < L.length) :
    stAt A L (j + 1) = (A.δ (stAt A L j) L[j].2).1 := by
  rw [stAt, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    ObjSpec.runOps_append, List.map_singleton, ObjSpec.runOps_cons, ObjSpec.runOps_nil, stAt]

/-- A predicate preserved by every operation. -/
def Stable (A : ObjSpec) (Q : A.State → Prop) : Prop := ∀ q o, Q q → Q (A.δ q o).1

lemma Stable.runOps {Q : A.State → Prop} (hQ : Stable A Q) {q : A.State} (hq : Q q)
    (os : List A.Op) : Q (A.runOps q os) := by
  induction os generalizing q with
  | nil => exact hq
  | cons o os ih => exact ih (hQ q o hq)

omit [DecidableEq P] in
lemma Stable.stAt_mono {Q : A.State → Prop} (hQ : Stable A Q) (L : List (OpId P × A.Op))
    {j j' : ℕ} (hjj : j ≤ j') (h : Q (stAt A L j)) : Q (stAt A L j') := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjj
  simp only [stAt, List.take_add, List.map_append, ObjSpec.runOps_append] at h ⊢
  exact hQ.runOps h _

lemma seqOK_getElem {α : List (Label P A)} {q : A.State} {L : List (OpId P × A.Op)}
    (h : SeqOK α q L) {j : ℕ} (hj : j < L.length) {r : A.Resp}
    (hr : respOf α L[j].1 = some r) :
    (A.δ (A.runOps q ((L.take j).map Prod.snd)) L[j].2).2 = r := by
  induction L generalizing q j with
  | nil => simp at hj
  | cons y L ih =>
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero => simpa using h1 r hr
    | succ j => simpa using ih h2 (by simpa using hj) hr

/-- The position of `y` in `L`. -/
def idx (L : List (OpId P × A.Op)) (y : OpId P) : ℕ := (L.map Prod.fst).idxOf y

lemma idx_lt {L : List (OpId P × A.Op)} {y : OpId P} (hy : y ∈ L.map Prod.fst) :
    idx L y < L.length := by
  simpa [idx] using List.idxOf_lt_length_iff.2 hy

lemma getElem_idx {L : List (OpId P × A.Op)} {y : OpId P} (hy : y ∈ L.map Prod.fst) :
    (L[idx L y]'(idx_lt hy)).1 = y := by
  have := List.getElem_idxOf (List.idxOf_lt_length_iff.2 hy)
  rw [List.getElem_map] at this
  exact this

lemma idx_getElem {L : List (OpId P × A.Op)} (hnd : (L.map Prod.fst).Nodup) {j : ℕ}
    (hj : j < L.length) : idx L L[j].1 = j := by
  have := hnd.idxOf_getElem j (by simpa using hj)
  simpa [idx] using this

lemma idx_lt_idx {L : List (OpId P × A.Op)} (hnd : (L.map Prod.fst).Nodup) {a b : OpId P}
    (hs : [a, b].Sublist (L.map Prod.fst)) : idx L a < idx L b := by
  obtain ⟨r₁, r₂, he, ha, hb⟩ := List.cons_sublist_iff.1 hs
  have hb : b ∈ r₂ := by simpa using hb
  have hbr : b ∉ r₁ := by
    rw [he, List.nodup_append] at hnd
    exact fun hb1 => hnd.2.2 b hb1 b hb rfl
  simp only [idx, he]
  rw [List.idxOf_append_of_mem ha, List.idxOf_append_of_notMem hbr]
  have := List.idxOf_lt_length_iff.2 ha
  omega

lemma completed_of_respOf {α : List (Label P A)} {x : OpId P} {r : A.Resp}
    (h : respOf α x = some r) : Completed α x := by
  simp only [respOf] at h
  exact (List.getElem?_eq_some_iff.1 h).1

section Lin

variable {α : List (Label P A)} {L : List (OpId P × A.Op)}

lemma lin_mem (hL : IsLinearization α L) {x : OpId P} {r : A.Resp}
    (h : respOf α x = some r) : x ∈ L.map Prod.fst :=
  hL.complete x (completed_of_respOf h)

lemma lin_idx_lt (hL : IsLinearization α L) {a b : OpId P} (h : Precedes α a b)
    (hb : b ∈ L.map Prod.fst) : idx L a < idx L b :=
  idx_lt_idx hL.nodup (hL.realtime a b h hb)

lemma lin_opOf_idx (hL : IsLinearization α L) {y : OpId P} (hy : y ∈ L.map Prod.fst) :
    opOf α y = some (L[idx L y]'(idx_lt hy)).2 := by
  have := hL.op_eq _ (List.getElem_mem (idx_lt hy))
  rwa [getElem_idx hy] at this

lemma lin_resp_idx (hL : IsLinearization α L) {y : OpId P} {r : A.Resp}
    (hr : respOf α y = some r) :
    (A.δ (stAt A L (idx L y)) (L[idx L y]'(idx_lt (lin_mem hL hr))).2).2 = r := by
  have hy := lin_mem hL hr
  exact seqOK_getElem hL.seq (idx_lt hy) (by rw [getElem_idx hy]; exact hr)

end Lin

/-! ## Signature-like objects -/

/-- An object with a "sign" procedure for the process `s` and a "test" for the others, whose
sequential specification has the validity, unforgeability and relay properties of signatures. -/
structure SigTest (A : ObjSpec) (allowed : P → A.Op → Prop) (s : P) where
  /-- The operations the setter invokes, in order, to sign. -/
  setOps : List A.Op
  /-- The test operation. -/
  testOp : A.Op
  /-- Positive responses of the test. -/
  pos : A.Resp → Prop
  /-- `R k`: the first `k` set operations have taken effect. -/
  R : ℕ → A.State → Prop
  setOps_ne_nil : setOps ≠ []
  R_zero : ∀ q, R 0 q
  R_stable : ∀ k, Stable A (R k)
  R_succ : ∀ k (hk : k < setOps.length) q, R k q → R (k + 1) (A.δ q setOps[k]).1
  pos_iff : ∀ q, pos (A.δ q testOp).2 ↔ R setOps.length q
  not_R_init : ¬ R setOps.length A.init
  only_setter : ∀ q o p, ¬ R setOps.length q → R setOps.length (A.δ q o).1 → allowed p o → p = s
  allowed_set : ∀ o ∈ setOps, allowed s o
  allowed_test : ∀ p, p ≠ s → allowed p testOp

namespace SigTest

variable {allowed : P → A.Op → Prop} {s : P} (T : SigTest A allowed s)
  {Bz : Finset P} {h : List (Label P A)}

/-- Lemma 28(1), generalized: if the (correct) setter has completed its set operations before a
correct process invokes a test, the test is positive. -/
theorem validity (hBL : ByzLinearizable allowed Bz h) (hs : s ∉ Bz) {x : OpId P}
    (hx : x.1 ∉ Bz) (hset : ∀ k (hk : k < T.setOps.length), opOf h (s, k) = some T.setOps[k])
    (hprog : ∀ k, k + 1 < T.setOps.length → Precedes h (s, k) (s, k + 1))
    (hlast : Precedes h (s, T.setOps.length - 1) x) (htest : opOf h x = some T.testOp)
    {r : A.Resp} (hr : respOf h x = some r) : T.pos r := by
  obtain ⟨h', -, -, hfilt, L, hL⟩ := hBL
  have hm : 0 < T.setOps.length := List.length_pos_iff.2 T.setOps_ne_nil
  have hr' : respOf h' x = some r := by rw [respOf_eq_of_filter_eq hfilt hx]; exact hr
  have hxL := lin_mem hL hr'
  have hpre : ∀ k, k < T.setOps.length → Precedes h' (s, k) (if k + 1 < T.setOps.length then
      (s, k + 1) else x) := fun k hk => by
    split_ifs with hk1
    · exact (precedes_iff_of_filter_eq hfilt hs hs).2 (hprog k hk1)
    · have : k = T.setOps.length - 1 := by omega
      subst this; exact (precedes_iff_of_filter_eq hfilt hs hx).2 hlast
  have hmem : ∀ k, k < T.setOps.length → (s, k) ∈ L.map Prod.fst := fun k hk =>
    hL.complete _ ((hpre k hk).completed)
  have hop : ∀ k (hk : k < T.setOps.length),
      (L[idx L (s, k)]'(idx_lt (hmem k hk))).2 = T.setOps[k] := fun k hk => by
    have h1 := lin_opOf_idx hL (hmem k hk)
    rw [opOf_eq_of_filter_eq hfilt hs, hset k hk] at h1
    exact (Option.some.inj h1).symm
  -- after the `k`-th set operation, `R (k+1)` holds
  have key : ∀ k (hk : k < T.setOps.length), T.R (k + 1) (stAt A L (idx L (s, k) + 1)) := by
    intro k hk
    induction k with
    | zero =>
      rw [stAt_succ L (idx_lt (hmem 0 hk)), hop 0 hk]
      exact T.R_succ 0 hk _ (T.R_zero _)
    | succ k ih =>
      have ih := ih (by omega)
      have hlt : idx L (s, k) < idx L (s, k + 1) := by
        have := lin_idx_lt hL (hpre k (by omega)) (by
          rw [ite_eq_left hk]; exact hmem (k + 1) hk)
        rwa [ite_eq_left hk] at this
      have h2 := (T.R_stable (k + 1)).stAt_mono L (show idx L (s, k) + 1 ≤ idx L (s, k + 1)
        by omega) ih
      rw [stAt_succ L (idx_lt (hmem (k + 1) hk)), hop (k + 1) hk]
      exact T.R_succ (k + 1) hk _ h2
  have hk : T.setOps.length - 1 < T.setOps.length := by omega
  have hlt : idx L (s, T.setOps.length - 1) < idx L x := by
    have := lin_idx_lt hL (hpre _ hk) (by rw [ite_eq_right (by omega)]; exact hxL)
    rwa [ite_eq_right (by omega)] at this
  have hR := (T.R_stable _).stAt_mono L (show idx L (s, T.setOps.length - 1) + 1 ≤ idx L x
    by omega) (key _ hk)
  rw [show T.setOps.length - 1 + 1 = T.setOps.length by omega] at hR
  have hresp := lin_resp_idx hL hr'
  have hopx := lin_opOf_idx hL hxL
  rw [opOf_eq_of_filter_eq hfilt hx, htest] at hopx
  rw [← Option.some.inj hopx] at hresp
  rw [← hresp]
  exact (T.pos_iff _).2 hR

/-- Lemma 28(2), generalized (unforgeability): if a test by a correct process is positive and the
setter is correct, then the setter invoked an operation before the test returned. -/
theorem unforgeability (hBL : ByzLinearizable allowed Bz h) (hs : s ∉ Bz) {x : OpId P}
    (hx : x.1 ∉ Bz) (htest : opOf h x = some T.testOp) {r : A.Resp} (hr : respOf h x = some r)
    (hpos : T.pos r) : ¬ Precedes h x (s, 0) := by
  intro hprec
  obtain ⟨h', -, hall, hfilt, L, hL⟩ := hBL
  have hr' : respOf h' x = some r := by rw [respOf_eq_of_filter_eq hfilt hx]; exact hr
  have hxL := lin_mem hL hr'
  have hresp := lin_resp_idx hL hr'
  have hopx := lin_opOf_idx hL hxL
  rw [opOf_eq_of_filter_eq hfilt hx, htest] at hopx
  rw [← Option.some.inj hopx] at hresp
  have hRx : T.R T.setOps.length (stAt A L (idx L x)) := (T.pos_iff _).1 (hresp ▸ hpos)
  -- the first position where `R m` holds
  obtain ⟨i, hi, hni, hRi⟩ : ∃ i, i < idx L x ∧ ¬ T.R T.setOps.length (stAt A L i) ∧
      T.R T.setOps.length (stAt A L (i + 1)) := by
    by_contra hcon
    push Not at hcon
    have : ∀ i ≤ idx L x, ¬ T.R T.setOps.length (stAt A L i) := by
      intro i hi
      induction i with
      | zero => rw [stAt_zero]; exact T.not_R_init
      | succ i ih => exact fun h => hcon i (by omega) (ih (by omega)) h
    exact this _ le_rfl hRx
  have hiL : i < L.length := lt_trans hi (idx_lt hxL)
  rw [stAt_succ L hiL] at hRi
  -- the operation at position `i` is by the setter
  have hinv := hL.op_eq _ (List.getElem_mem hiL)
  have hproc : L[i].1.1 = s := by
    have hinvoked : Label.inv L[i].1.1 L[i].2 ∈ h' := by
      simp only [opOf, opsOf] at hinv
      obtain ⟨ℓ, hℓ, hℓe⟩ := List.mem_filterMap.1 (List.mem_of_getElem? hinv)
      cases ℓ with
      | inv q o =>
        simp only [Label.invOf] at hℓe
        split_ifs at hℓe with hq; cases hℓe; subst hq; exact hℓ
      | ret _ _ => simp [Label.invOf] at hℓe
      | tau _ => simp [Label.invOf] at hℓe
    exact T.only_setter _ _ _ hni hRi (hall _ _ hinvoked)
  -- but the test precedes every operation of the setter
  set y := L[i].1 with hy
  have hprec' : Precedes h x y := by
    obtain ⟨β, γ, he, hc, hni'⟩ := hprec
    refine ⟨β, γ, he, hc, ?_⟩
    simp only [Invoked, not_lt, Nat.le_zero] at hni' ⊢
    rw [hproc, hni']; exact Nat.zero_le _
  have hy' : y.1 ∉ Bz := by rw [hproc]; exact hs
  have h1 := lin_idx_lt hL ((precedes_iff_of_filter_eq hfilt hx hy').2 hprec')
    (by rw [hy]; exact List.mem_map_of_mem (List.getElem_mem hiL))
  rw [hy, idx_getElem hL.nodup hiL] at h1
  omega

/-- Lemma 28(3), generalized (relay): a positive test by a correct process that precedes a test
by a correct process makes the latter positive. -/
theorem relay (hBL : ByzLinearizable allowed Bz h) {x y : OpId P} (hx : x.1 ∉ Bz)
    (hy : y.1 ∉ Bz) (htx : opOf h x = some T.testOp) (hty : opOf h y = some T.testOp)
    {r r' : A.Resp} (hr : respOf h x = some r) (hpos : T.pos r) (hprec : Precedes h x y)
    (hr' : respOf h y = some r') : T.pos r' := by
  obtain ⟨h', -, -, hfilt, L, hL⟩ := hBL
  have hrx : respOf h' x = some r := by rw [respOf_eq_of_filter_eq hfilt hx]; exact hr
  have hry : respOf h' y = some r' := by rw [respOf_eq_of_filter_eq hfilt hy]; exact hr'
  have hxL := lin_mem hL hrx
  have hyL := lin_mem hL hry
  have hresp := lin_resp_idx hL hrx
  have hopx := lin_opOf_idx hL hxL
  rw [opOf_eq_of_filter_eq hfilt hx, htx] at hopx
  rw [← Option.some.inj hopx] at hresp
  have hRx : T.R T.setOps.length (stAt A L (idx L x)) := (T.pos_iff _).1 (hresp ▸ hpos)
  have hlt := lin_idx_lt hL ((precedes_iff_of_filter_eq hfilt hx hy).2 hprec) hyL
  have hRy := (T.R_stable _).stAt_mono L hlt.le hRx
  have hresp' := lin_resp_idx hL hry
  have hopy := lin_opOf_idx hL hyL
  rw [opOf_eq_of_filter_eq hfilt hy, hty] at hopy
  rw [← Option.some.inj hopy] at hresp'
  rw [← hresp']
  exact (T.pos_iff _).2 hRy

end SigTest

section Admits

variable {ι : Type} {B : ι → ObjSpec}

namespace SigTest

variable {allowed : P → A.Op → Prop} {s : P} (T : SigTest A allowed s)

/-- The invocation patterns of the proof: the setter invokes a prefix of `setOps`, every other
process invokes nothing or one test. -/
def Admits (adm : P → List A.Op → Prop) : Prop :=
  (∀ k, adm s (T.setOps.take k)) ∧ ∀ p, p ≠ s → adm p [] ∧ adm p [T.testOp]

/-- A history whose invocation patterns are among those of `Admits`. -/
def AdmOK (h : List (Label P A)) : Prop :=
  opsOf h s <+: T.setOps ∧ ∀ q, q ≠ s → opsOf h q <+: [T.testOp]

variable {T}

lemma AdmOK.adm {adm : P → List A.Op → Prop} (hadm : T.Admits adm) {h : List (Label P A)}
    (hh : T.AdmOK h) (p : P) : adm p (opsOf h p) := by
  by_cases hp : p = s
  · subst hp; rw [List.prefix_iff_eq_take.1 hh.1]; exact hadm.1 _
  · rcases List.prefix_cons_iff.1 (hh.2 p hp) with h0 | ⟨l, hl, hl'⟩
    · rw [h0]; exact (hadm.2 p hp).1
    · rw [hl]
      rcases (List.prefix_nil.1 hl') with rfl
      exact (hadm.2 p hp).2

lemma AdmOK.take {α : List (Event P A B)} (hh : T.AdmOK (hist α)) (j : ℕ) :
    T.AdmOK (hist (α.take j)) := by
  have hpre : ∀ q, opsOf (hist (α.take j)) q <+: opsOf (hist α) q := fun q => by
    conv_rhs => rw [← List.take_append_drop j α]
    rw [hist_append, opsOf_append]; exact List.prefix_append _ _
  exact ⟨(hpre s).trans hh.1, fun q hq => (hpre q).trans (hh.2 q hq)⟩

lemma AdmOK.adm_take {adm : P → List A.Op → Prop} (hadm : T.Admits adm)
    {α : List (Event P A B)} (hh : T.AdmOK (hist α)) (Bz : Finset P) :
    ∀ k, ∀ p ∉ Bz, adm p (opsOf (hist (α.take k)) p) :=
  fun k p _ => (hh.take k).adm hadm p

end SigTest

end Admits

end Podc.ByzantineSWMRRegisters
