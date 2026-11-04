import Podc.Computability.Distributed.SharedMemory.AwarenessRound
import Cslib.Computability.Distributed.SharedMemory.Linearization
import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# The read/update tradeoff for counter-like objects (Section 3 of Hendler–Khait, PODC'14)

A generic version of Theorem 1: an obstruction-free linearizable implementation, from
read/write/CAS base objects, of an object in which `N − 1` processes each apply one *update*
`u p` and a reader `r` applies a *read* `rd` whose response *reveals* all participants
(`Reveals`). If `rd` completes within `R` solo steps, then some update takes more than `k`
steps whenever `R · 3^k + 1 < N`.

Counters (`inc`/`read`) and single-writer snapshots (`update i 1`/`scan`) both satisfy
`Reveals` (`CounterSnapshot.lean`).
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

variable {A : ObjSpec} {ι P L V : Type} [Fintype P] [DecidableEq P] [DecidableEq ι]
  [DecidableEq V] {v₀ : V}

/-- The response of `rd` after the updates of the processes in `l` (in this order). -/
def respAfter (A : ObjSpec) (u : P → A.Op) (rd : A.Op) (l : List P) : A.Resp :=
  (A.δ (A.runOps A.init (l.map u)) rd).2

/-- The read operation `rd` *reveals* the participants of the updates: its response after the
updates of all processes but `r` (in any order) differs from its response after the updates of
any set of processes missing some `q ≠ r`. -/
def Reveals (A : ObjSpec) (r : P) (u : P → A.Op) (rd : A.Op) : Prop :=
  ∀ q, q ≠ r → ∀ l₁ l₂ : List P, l₁.Nodup → (∀ p, p ∈ l₁ ↔ p ≠ r) → l₂.Nodup →
    (∀ p ∈ l₂, p ≠ r ∧ p ≠ q) → respAfter A u rd l₁ ≠ respAfter A u rd l₂

/-- The operation `rd` of process `r` completes within `R` of its own steps when run solo from
any reachable configuration in which `r` is idle. (Implied by obstruction-freedom together with
a bound `R` on the step complexity of `rd`.) -/
def SoloBound (I : Impl A (RWC ι V v₀) P L) (r : P) (rd : A.Op) (R : ℕ) : Prop :=
  ∀ α C, I.run α = some C → C.pend r = none →
    ∃ j ≤ R, ∃ v, I.Valid (α ++ .inv r rd :: (List.replicate j (.tau r) ++ [.ret r v]))

/-- Number of internal steps of `p` in `α`. -/
def tauCount (α : List (Label P A)) (p : P) : ℕ := (α.filter (fun ℓ => ℓ.isTauOf p)).length

/-! ### Linearizations of executions with one operation per process -/

omit [Fintype P] in
lemma lin_split {α : List (Label P A)} {L : List (OpId P × A.Op)} (hL : IsLinearization α L)
    {x : OpId P} {v : A.Resp} (hv : respOf α x = some v) :
    ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧ opOf α x = some o ∧
      (A.δ (A.runOps A.init (L₁.map Prod.snd)) o).2 = v := by
  have hx : x ∈ L.map Prod.fst := hL.complete x (Completed.of_respOf_eq_some hv)
  obtain ⟨⟨x', o⟩, hmem, hx'⟩ := List.mem_map.1 hx
  simp only at hx'; subst hx'
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hmem
  refine ⟨L₁, L₂, o, rfl, hL.op_eq _ hmem, ?_⟩
  have hs := (seqOK_append (α := α) A.init L₁ ((x', o) :: L₂)).1 hL.seq
  exact hs.2.1 v hv

variable (u : P → A.Op) (rd : A.Op) (r : P)

omit [Fintype P] in
/-- Shape of the prefix of a linearization before the read, when every process invokes at most
one operation (`u p`, or `rd` for `r`). -/
lemma prefix_shape {α : List (Label P A)} {L₁ L₂ : List (OpId P × A.Op)} {o : A.Op}
    (hL : IsLinearization α (L₁ ++ ((r, 0), o) :: L₂))
    (hops : ∀ p, (opsOf α p).Sublist [if p = r then rd else u p]) :
    ∃ l : List P, l.Nodup ∧ L₁.map Prod.snd = l.map u ∧ (∀ p ∈ l, p ≠ r ∧ opsOf α p ≠ []) ∧
      ∀ p, p ≠ r → (p, 0) ∈ L₁.map Prod.fst → p ∈ l := by
  have hnd := hL.nodup
  have hmem : ∀ y ∈ L₁, y.1 = (y.1.1, 0) ∧ y.1.1 ≠ r ∧ y.2 = u y.1.1 ∧ opsOf α y.1.1 ≠ [] := by
    intro y hy
    have hop := hL.op_eq y (List.mem_append_left _ hy)
    have hinv : Invoked α y.1 := Invoked.of_opOf_eq_some hop
    have hlen := (hops y.1.1).length_le
    simp only [List.length_singleton] at hlen
    have h0 : y.1.2 = 0 := by unfold Invoked at hinv; omega
    have hy1 : y.1 = (y.1.1, 0) := Prod.ext rfl h0
    have hne : y.1.1 ≠ r := by
      intro h
      have : y.1 = (r, 0) := by rw [hy1, h]
      simp only [List.map_append, List.map_cons] at hnd
      exact List.disjoint_of_nodup_append hnd (List.mem_map_of_mem hy) (this ▸ List.mem_cons_self)
    refine ⟨hy1, hne, ?_, ?_⟩
    · have hsub := hops y.1.1
      rw [if_neg hne] at hsub
      unfold opOf at hop
      rw [hy1] at hop
      simp only at hop
      have hne' : opsOf α y.1.1 ≠ [] := by intro h; rw [h] at hop; simp at hop
      rcases List.sublist_singleton.1 hsub with h | h
      · exact absurd h hne'
      · rw [h] at hop; simpa using hop.symm
    · intro h; rw [hy1] at hinv; unfold Invoked at hinv; rw [h] at hinv; simp at hinv
  refine ⟨L₁.map (fun y => y.1.1), ?_, ?_, ?_, ?_⟩
  · have hnd1 : (L₁.map Prod.fst).Nodup := by
      simp only [List.map_append] at hnd; exact hnd.sublist (List.sublist_append_left _ _)
    have heq : L₁.map Prod.fst = (L₁.map (fun y => y.1.1)).map (fun p => ((p, 0) : OpId P)) := by
      rw [List.map_map]; exact List.map_congr_left (fun y hy => (hmem y hy).1)
    rw [heq] at hnd1
    exact hnd1.of_map _
  · rw [List.map_map]
    exact List.map_congr_left (fun y hy => (hmem y hy).2.2.1)
  · intro p hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hmem y hy).2.1, (hmem y hy).2.2.2⟩
  · intro p _ hp
    obtain ⟨y, hy, hyp⟩ := List.mem_map.1 hp
    exact List.mem_map.2 ⟨y, hy, by rw [hyp]⟩

omit [Fintype P] in
lemma mem_prefix_of_sublist {M₁ M₂ : List (OpId P)} {a b : OpId P} (hnd : (M₁ ++ b :: M₂).Nodup)
    (hs : [a, b].Sublist (M₁ ++ b :: M₂)) : a ∈ M₁ := by
  obtain ⟨r₁, r₂, he, ha, hb⟩ := List.cons_sublist_iff.1 hs
  have hb' : b ∈ r₂ := (List.singleton_sublist).1 hb
  rw [he] at hnd
  rcases List.append_eq_append_iff.1 he.symm with ⟨a', rfl, -⟩ | ⟨c', rfl, hc⟩
  · exact List.mem_append_left _ ha
  · cases c' with
    | nil => simpa using ha
    | cons c c'' =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact absurd hb' (List.disjoint_of_nodup_append hnd (by simp))

variable {u rd r}
variable {I : Impl A (RWC ι V v₀) P L}

/-- While only `r` takes steps, each step adds at most `B` processes to `r`'s awareness set. -/
lemma solo_aw_bound {X Y : Config A (RWC ι V v₀) P L × Ghost P ι V} {γ : List (Label P A)}
    (h : arunFrom I X γ = some Y) (hγ : ∀ ℓ ∈ γ, ℓ.proc = r) {B : ℕ}
    (hF : ∀ i, (X.2.F i).card ≤ B ∨ X.2.F i ⊆ X.2.aw r) :
    (Y.2.aw r).card ≤ (X.2.aw r).card + tauCount γ r * B := by
  induction γ generalizing X with
  | nil => simp only [arunFrom_nil, Option.some.injEq] at h; subst h; simp [tauCount]
  | cons ℓ γ ih =>
    simp only [arunFrom_cons] at h
    cases hs : astep I X ℓ with
    | none => simp [hs] at h
    | some Z =>
      simp only [hs, Option.bind_some] at h
      obtain ⟨h1, h2⟩ := (astep_eq_some I).1 hs
      obtain ⟨Z1, Z2⟩ := Z; simp only at h1 h2; subst h2
      have hr : ℓ.proc = r := hγ ℓ List.mem_cons_self
      have key : (∀ i, ((gstep I X.1 X.2 ℓ).F i).card ≤ B ∨
            (gstep I X.1 X.2 ℓ).F i ⊆ (gstep I X.1 X.2 ℓ).aw r) ∧
          ((gstep I X.1 X.2 ℓ).aw r).card ≤ (X.2.aw r).card +
            (if ℓ.isTauOf r then B else 0) := by
        cases ℓ with
        | inv p o =>
          simp only [gstep_inv', Label.isTauOf_inv]; exact ⟨hF, by simp⟩
        | ret p o =>
          simp only [gstep_ret', Label.isTauOf_ret]; exact ⟨hF, by simp⟩
        | tau p =>
          simp only [Label.proc] at hr
          have hr' : r = p := hr.symm
          subst hr'
          obtain ⟨-, -, i, o, k, hact, -⟩ := Impl.step_tau h1
          have hFi : (X.2.aw r ∪ X.2.F i).card ≤ (X.2.aw r).card + B := by
            rcases hF i with h | h
            · exact (Finset.card_union_le _ _).trans (by omega)
            · rw [Finset.union_eq_left.2 h]; omega
          simp only [Label.isTauOf_tau, decide_true, if_true]
          cases o with
          | read =>
            rw [gstep_tau_read hact]
            refine ⟨fun j => ?_, by simpa using hFi⟩
            rcases hF j with h | h
            · exact Or.inl h
            · right; simp only [Function.update_self]
              exact h.trans Finset.subset_union_left
          | write v =>
            rw [gstep_tau_write hact]
            refine ⟨fun j => ?_, by simp⟩
            by_cases hj : j = i
            · subst hj; right; simp [Ghost.F]
            · simp only [Ghost.F, Function.update_of_ne hj]; exact hF j
          | cas a b =>
            rw [gstep_tau_cas hact]
            refine ⟨fun j => ?_, by simpa using hFi⟩
            simp only [Ghost.F, Function.update_self]
            split_ifs
            · by_cases hj : j = i
              · subst hj; right; simp
              · simp only [Function.update_of_ne hj]
                rcases hF j with h | h
                · exact Or.inl h
                · exact Or.inr (h.trans Finset.subset_union_left)
            · rcases hF j with h | h
              · exact Or.inl h
              · exact Or.inr (h.trans Finset.subset_union_left)
      have := ih h (fun ℓ' h' => hγ ℓ' (List.mem_cons_of_mem _ h')) key.1
      have htc : tauCount (ℓ :: γ) r = (if ℓ.isTauOf r then 1 else 0) + tauCount γ r := by
        simp only [tauCount, List.filter_cons]; split_ifs <;> simp [add_comm]
      rw [htc]
      simp only at this
      split_ifs at key ⊢ with ht
      · rw [Nat.add_mul, one_mul]; have := key.2; omega
      · rw [zero_add]; have := key.2; omega

variable (u rd r)

/-- **Lemma 3 of Hendler–Khait (generic form).** In an execution in which every process other
than `r` completes its single update before `r` invokes its single read, and the read completes,
the reader is aware of every process. -/
theorem reader_aware_all (hlin : I.Linearizable) (hrev : Reveals A r u rd)
    {γ : List (Label P A)} {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V}
    (h : arun I γ = some (C, G))
    (hops : ∀ p, (opsOf γ p).Sublist [if p = r then rd else u p])
    (hprec : ∀ p, p ≠ r → Precedes γ (p, 0) (r, 0))
    {v : A.Resp} (hv : respOf γ (r, 0) = some v) : ∀ q, q ∈ G.aw r := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨q, hq⟩ := hcon
  have hI := arun_inv h
  have hqr : q ≠ r := fun e => hq (e ▸ hI.self_mem r)
  obtain ⟨hlf, hlinf⟩ := hlin
  -- the full execution
  have hγv : I.Valid γ := ⟨C, arun_fst I h⟩
  obtain ⟨L₁, L₂, o, hLeq, hop, hres⟩ := lin_split (hlinf γ hγv) hv
  have hL := hlinf γ hγv
  rw [hLeq] at hL
  have hor : o = rd := by
    have hsub := hops r; rw [if_pos rfl] at hsub
    unfold opOf at hop; simp only at hop
    rcases List.sublist_singleton.1 hsub with h' | h'
    · rw [h'] at hop; simp at hop
    · rw [h'] at hop; simpa using hop.symm
  subst hor
  obtain ⟨l₁, hnd₁, hmap₁, hl₁, hall₁⟩ := prefix_shape u o r hL hops
  have hl₁iff : ∀ p, p ∈ l₁ ↔ p ≠ r := by
    intro p
    refine ⟨fun hp => (hl₁ p hp).1, fun hp => hall₁ p hp ?_⟩
    have hrt := hL.realtime (p, 0) (r, 0) (hprec p hp) (by simp)
    simp only [List.map_append, List.map_cons] at hrt
    exact mem_prefix_of_sublist (by simpa using hL.nodup) hrt
  rw [hmap₁] at hres
  -- the erased execution
  obtain ⟨C', G', h', hR⟩ := arun_erase (I := I) {q} h
  have hdr : Disjoint (G.aw r) {q} := Finset.disjoint_singleton_right.2 hq
  have hfr := eraseFrom_filter_proc (I := I) (S := {q}) (X := (I.initCfg, Ghost.init))
    (Y := (C, G)) h r hdr
  have hopsr : opsOf (erase I {q} γ) r = opsOf γ r := by
    rw [← opsOf_filter_proc, erase, hfr, opsOf_filter_proc]
  have hrespr : respsOf (erase I {q} γ) r = respsOf γ r := by
    rw [← respsOf_filter_proc, erase, hfr, respsOf_filter_proc]
  have hv' : respOf (erase I {q} γ) (r, 0) = some v := by
    unfold respOf at hv ⊢; rw [hrespr]; exact hv
  have hγ'v : I.Valid (erase I {q} γ) := ⟨C', arun_fst I h'⟩
  obtain ⟨M₁, M₂, o', hMeq, hop', hres'⟩ := lin_split (hlinf _ hγ'v) hv'
  have hM := hlinf _ hγ'v
  rw [hMeq] at hM
  have hor' : o' = o := by
    unfold opOf at hop hop'; simp only at hop hop'; rw [hopsr] at hop'
    rw [hop] at hop'; exact (Option.some.inj hop').symm
  subst hor'
  have hsubl : ∀ p, (opsOf (erase I {q} γ) p).Sublist (opsOf γ p) := fun p =>
    (erase_sublist {q} γ).filterMap _
  obtain ⟨l₂, hnd₂, hmap₂, hl₂, -⟩ := prefix_shape u o' r hM
    (fun p => (hsubl p).trans (hops p))
  rw [hmap₂] at hres'
  have hnoq : opsOf (erase I {q} γ) q = [] := by
    apply opsOf_eq_nil_of_proc_ne
    intro ℓ hℓ
    have := eraseFrom_proc_not_mem (I := I) (S := {q}) (X := (I.initCfg, Ghost.init)) h inv_init
      ℓ hℓ
    simpa using this
  refine hrev q hqr l₁ l₂ hnd₁ hl₁iff hnd₂ (fun p hp => ⟨(hl₂ p hp).1, ?_⟩) ?_
  · rintro rfl; exact (hl₂ p hp).2 hnoq
  · unfold respAfter; rw [hres, hres']

/-! ### The round construction (proof of Theorem 1) -/

section Construction

variable {u rd r}

omit [Fintype P] in
lemma tauCount_map_tau (l : List P) (p : P) :
    tauCount ((l.map .tau : List (Label P A))) p = l.count p := by
  induction l with
  | nil => simp [tauCount]
  | cons q l ih =>
    simp only [tauCount, List.map_cons, List.filter_cons, Label.isTauOf_tau,
      decide_eq_true_eq, List.count_cons, beq_iff_eq] at ih ⊢
    split_ifs <;> simp [ih]

omit [Fintype P] in
lemma tauCount_append (α β : List (Label P A)) (p : P) :
    tauCount (α ++ β) p = tauCount α p + tauCount β p := by
  simp [tauCount, List.filter_append]

omit [Fintype P] in
lemma opsOf_map_tau (l : List P) (p : P) : opsOf ((l.map .tau : List (Label P A))) p = [] := by
  induction l with
  | nil => rfl
  | cons q l ih => simpa using ih

omit [Fintype P] in
lemma respsOf_map_tau (l : List P) (p : P) :
    respsOf ((l.map .tau : List (Label P A))) p = [] := by
  induction l with
  | nil => rfl
  | cons q l ih => simpa using ih

omit [Fintype P] in
lemma opsOf_map_inv (f : P → A.Op) (ps : List P) (hnd : ps.Nodup) (p : P) :
    opsOf ((ps.map (fun q => .inv q (f q)) : List (Label P A))) p =
      if p ∈ ps then [f p] else [] := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    have hnd' := List.nodup_cons.1 hnd
    simp only [List.map_cons, opsOf_cons, Label.invOf_inv, ih hnd'.2, List.mem_cons]
    by_cases hqp : q = p
    · subst hqp; simp [hnd'.1]
    · simp [hqp, Ne.symm hqp]

omit [Fintype P] in
lemma respsOf_map_inv (f : P → A.Op) (ps : List P) (p : P) :
    respsOf ((ps.map (fun q => .inv q (f q)) : List (Label P A))) p = [] := by
  induction ps with
  | nil => rfl
  | cons q l ih => simpa using ih

omit [Fintype P] in
lemma respsOf_map_ret (f : P → A.Resp) (ps : List P) (hnd : ps.Nodup) (p : P) :
    respsOf ((ps.map (fun q => .ret q (f q)) : List (Label P A))) p =
      if p ∈ ps then [f p] else [] := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    have hnd' := List.nodup_cons.1 hnd
    simp only [List.map_cons, respsOf_cons, Label.retOf_ret, ih hnd'.2, List.mem_cons]
    by_cases hqp : q = p
    · subst hqp; simp [hnd'.1]
    · simp [hqp, Ne.symm hqp]

omit [Fintype P] in
lemma opsOf_map_ret (f : P → A.Resp) (ps : List P) (p : P) :
    opsOf ((ps.map (fun q => .ret q (f q)) : List (Label P A))) p = [] := by
  induction ps with
  | nil => rfl
  | cons q l ih => simpa using ih

omit [Fintype P] in
lemma tauCount_map_inv (f : P → A.Op) (ps : List P) (p : P) :
    tauCount ((ps.map (fun q => .inv q (f q)) : List (Label P A))) p = 0 := by
  induction ps with
  | nil => rfl
  | cons q l ih => simpa [tauCount] using ih

omit [Fintype P] in
lemma arunFrom_invs (f : P → A.Op) (ps : List P) :
    ∀ (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V), ps.Nodup →
      (∀ p ∈ ps, C.pend p = none ∧ I.allowed p (f p)) →
      ∃ C', arunFrom I (C, G) (ps.map (fun p => .inv p (f p))) = some (C', G) ∧
        (∀ p ∈ ps, C'.pend p ≠ none) ∧
        (∀ p, p ∉ ps → C'.pend p = C.pend p ∧ C'.loc p = C.loc p) := by
  induction ps with
  | nil => intro C G _ _; exact ⟨C, rfl, by simp, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons q ps ih =>
    intro C G hnd hps
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨hq0, hqa⟩ := hps q List.mem_cons_self
    obtain ⟨C₁, hs⟩ : ∃ C₁, I.step C (.inv q (f q)) = some C₁ :=
      ⟨_, Impl.step_inv_eq_some (I := I) hq0 hqa⟩
    have hC₁ := Impl.step_inv hs
    have hoth : ∀ p, p ≠ q → C₁.pend p = C.pend p ∧ C₁.loc p = C.loc p := fun p hpq =>
      ⟨(Impl.step_other hs (q := p) (by simpa [Label.proc] using Ne.symm hpq)).2,
        (Impl.step_other hs (q := p) (by simpa [Label.proc] using Ne.symm hpq)).1⟩
    obtain ⟨C', h1, h2, h3⟩ := ih C₁ G hnd'.2 (fun p hp => by
      have hpq : p ≠ q := fun e => hnd'.1 (e ▸ hp)
      refine ⟨?_, (hps p (List.mem_cons_of_mem _ hp)).2⟩
      rw [(hoth p hpq).1]
      exact (hps p (List.mem_cons_of_mem _ hp)).1)
    refine ⟨C', ?_, ?_, ?_⟩
    · simp only [List.map_cons, arunFrom_cons]
      rw [show astep I (C, G) (.inv q (f q)) = some (C₁, G) from
        (astep_eq_some I).2 ⟨hs, rfl⟩]
      exact h1
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [(h3 p hnd'.1).1, hC₁.2.2.1]; simp
      · exact h2 p hp
    · intro p hp
      have hpq : p ≠ q := fun e => hp (e ▸ List.mem_cons_self)
      have hp' : p ∉ ps := fun h => hp (List.mem_cons_of_mem _ h)
      rw [(h3 p hp').1, (h3 p hp').2]
      exact hoth p hpq

omit [Fintype P] in
lemma arunFrom_rets (f : P → A.Resp) (ps : List P) :
    ∀ (C : Config A (RWC ι V v₀) P L) (G : Ghost P ι V), ps.Nodup →
      (∀ p ∈ ps, C.pend p ≠ none ∧ ∃ l, I.act p (C.loc p) = .ret (f p) l) →
      ∃ C', arunFrom I (C, G) (ps.map (fun p => .ret p (f p))) = some (C', G) ∧
        (∀ p ∈ ps, C'.pend p = none) ∧
        (∀ p, p ∉ ps → C'.pend p = C.pend p ∧ C'.loc p = C.loc p) := by
  induction ps with
  | nil => intro C G _ _; exact ⟨C, rfl, by simp, fun _ _ => ⟨rfl, rfl⟩⟩
  | cons q ps ih =>
    intro C G hnd hps
    have hnd' := List.nodup_cons.1 hnd
    obtain ⟨hq0, l, hql⟩ := hps q List.mem_cons_self
    obtain ⟨C₁, hs⟩ : ∃ C₁, I.step C (.ret q (f q)) = some C₁ :=
      ⟨_, Impl.step_ret_eq_some (I := I) hq0 hql⟩
    have hC₁ := Impl.step_ret hs
    have hoth : ∀ p, p ≠ q → C₁.pend p = C.pend p ∧ C₁.loc p = C.loc p := fun p hpq =>
      ⟨(Impl.step_other hs (q := p) (by simpa [Label.proc] using Ne.symm hpq)).2,
        (Impl.step_other hs (q := p) (by simpa [Label.proc] using Ne.symm hpq)).1⟩
    obtain ⟨C', h1, h2, h3⟩ := ih C₁ G hnd'.2 (fun p hp => by
      have hpq : p ≠ q := fun e => hnd'.1 (e ▸ hp)
      rw [(hoth p hpq).1, (hoth p hpq).2]
      exact hps p (List.mem_cons_of_mem _ hp))
    refine ⟨C', ?_, ?_, ?_⟩
    · simp only [List.map_cons, arunFrom_cons]
      rw [show astep I (C, G) (.ret q (f q)) = some (C₁, G) from
        (astep_eq_some I).2 ⟨hs, rfl⟩]
      exact h1
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [(h3 p hnd'.1).1, hC₁.2.1]; simp
      · exact h2 p hp
    · intro p hp
      have hpq : p ≠ q := fun e => hp (e ▸ List.mem_cons_self)
      have hp' : p ∉ ps := fun h => hp (List.mem_cons_of_mem _ h)
      rw [(h3 p hp').1, (h3 p hp').2]
      exact hoth p hpq

omit [Fintype P] in
lemma runFrom_taus_pend {C C' : Config A (RWC ι V v₀) P L} (l : List P)
    (h : I.runFrom C (l.map .tau) = some C') : C'.pend = C.pend := by
  induction l generalizing C with
  | nil => simp only [List.map_nil, Impl.runFrom_nil, Option.some.injEq] at h; rw [h]
  | cons q l ih =>
    simp only [List.map_cons, Impl.runFrom_cons] at h
    cases hs : I.step C (.tau q) with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      rw [ih h, (Impl.step_tau hs).2.1]

variable (I u rd r)

/-- The state of the round construction after `j` rounds: every updater has invoked its update,
has not returned, and has taken exactly `j` steps unless its next action is a return; the
reader has not taken any step; awareness and familiarity sets have at most `3^j` elements. -/
structure Good (j : ℕ) (β : List (Label P A)) (C : Config A (RWC ι V v₀) P L)
    (G : Ghost P ι V) : Prop where
  run : arun I β = some (C, G)
  bdd : Bounded G (3 ^ j)
  noR : ∀ ℓ ∈ β, ℓ.proc ≠ r
  ops : ∀ p, p ≠ r → opsOf β p = [u p]
  resps : ∀ p, p ≠ r → respsOf β p = []
  pend : ∀ p, p ≠ r → C.pend p ≠ none
  pendR : C.pend r = none
  taus : ∀ p, p ≠ r → (∃ i o k, I.act p (C.loc p) = .access i o k) → tauCount β p = j

variable {I u rd r}

lemma good_zero (hall : ∀ p, p ≠ r → I.allowed p (u p)) :
    ∃ β C G, Good (I := I) (u := u) (r := r) 0 β C G := by
  classical
  set ps := (Finset.univ.erase r).toList with hps
  have hnd : ps.Nodup := Finset.nodup_toList _
  have hmem : ∀ p, p ∈ ps ↔ p ≠ r := by intro p; simp [hps]
  obtain ⟨C, h1, h2, h3⟩ := arunFrom_invs (I := I) u ps I.initCfg Ghost.init hnd
    (fun p hp => ⟨rfl, hall p ((hmem p).1 hp)⟩)
  refine ⟨ps.map (fun p => (.inv p (u p) : Label P A)), C, Ghost.init, ⟨h1, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro q; simp [Ghost.init]
  · intro i; simp [Ghost.F, Ghost.init]
  · intro ℓ hℓ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hℓ
    exact (hmem p).1 hp
  · intro p hp; rw [opsOf_map_inv u ps hnd, if_pos ((hmem p).2 hp)]
  · intro p _; exact respsOf_map_inv u ps p
  · intro p hp; exact h2 p ((hmem p).2 hp)
  · rw [(h3 r (fun h => (hmem r).1 h rfl)).1]; rfl
  · intro p _ _; simp [tauCount_map_inv]

/-- One round of the construction. -/
lemma good_succ {j : ℕ} {β : List (Label P A)} {C : Config A (RWC ι V v₀) P L} {G : Ghost P ι V}
    (hG : Good (I := I) (u := u) (r := r) j β C G) :
    ∃ β' C' G', Good (I := I) (u := u) (r := r) (j + 1) β' C' G' ∧ β <+: β' := by
  classical
  set T := Finset.univ.filter (fun p => p ≠ r ∧ ∃ i o k, I.act p (C.loc p) = .access i o k)
    with hT
  obtain ⟨l, hperm, C', G', h1, h2⟩ := exists_round (I := I) (T := T) hG.run (fun p hp => by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact ⟨hG.pend p hp.1, hp.2⟩) hG.bdd
  have hlT : ∀ p, p ∈ l ↔ p ∈ T := fun p => by rw [hperm.mem_iff, Finset.mem_toList]
  have hlnd : l.Nodup := hperm.nodup_iff.2 (Finset.nodup_toList _)
  have hrun' : I.runFrom C (l.map .tau) = some C' := arunFrom_fst I h1
  have hpend' := runFrom_taus_pend l hrun'
  refine ⟨β ++ l.map .tau, C', G', ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, List.prefix_append _ _⟩
  · rw [arun_append_of_eq I hG.run]; exact h1
  · rw [pow_succ, mul_comm]; exact h2
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact hG.noR ℓ hℓ
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hℓ
      have := (hlT p).1 hp
      simp only [hT, Finset.mem_filter] at this
      exact this.2.1
  · intro p hp; simp [opsOf_map_tau, hG.ops p hp]
  · intro p hp; simp [respsOf_map_tau, hG.resps p hp]
  · intro p hp; rw [hpend']; exact hG.pend p hp
  · rw [hpend']; exact hG.pendR
  · intro p hp hacc
    rw [tauCount_append, tauCount_map_tau]
    by_cases hpT : p ∈ T
    · have hpT' := hpT
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hpT'
      rw [hG.taus p hp hpT'.2, List.count_eq_one_of_mem hlnd ((hlT p).2 hpT)]
    · exfalso
      have hpl : p ∉ l := fun h => hpT ((hlT p).1 h)
      have hloc := (Impl.runFrom_other I hrun' (q := p) (fun ℓ hℓ => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hℓ
        exact fun e => hpl (by simp only [Label.proc] at e; exact e ▸ hq))).1
      rw [hloc] at hacc
      exact hpT (by simp [hT, hp, hacc])

omit [Fintype P] in
lemma tauCount_replicate (j : ℕ) (p : P) :
    tauCount ((List.replicate j (.tau p) : List (Label P A))) p = j := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [tauCount, List.replicate_succ, List.filter_cons] using ih

omit [Fintype P] in
lemma opsOf_replicate (j : ℕ) (p q : P) :
    opsOf ((List.replicate j (.tau p) : List (Label P A))) q = [] := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [List.replicate_succ] using ih

omit [Fintype P] in
lemma respsOf_replicate (j : ℕ) (p q : P) :
    respsOf ((List.replicate j (.tau p) : List (Label P A))) q = [] := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [List.replicate_succ] using ih

/-- If the construction stops because every updater is about to return, the reader's solo
read would be aware of at most `1 + R · 3^j` processes, contradicting Lemma 3. -/
lemma final_contra (hlin : I.Linearizable) (hrev : Reveals A r u rd) {R : ℕ}
    (hR : SoloBound I r rd R) {j : ℕ} {β : List (Label P A)} {C : Config A (RWC ι V v₀) P L}
    {G : Ghost P ι V} (hG : Good (I := I) (u := u) (r := r) j β C G)
    (hret : ∀ p, p ≠ r → ¬ ∃ i o k, I.act p (C.loc p) = .access i o k)
    (hk : R * 3 ^ j + 1 < Fintype.card P) : False := by
  classical
  -- some updater exists
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, p₀ ≠ r := by
    by_contra hcon; push_neg at hcon
    have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 (fun a b => (hcon a).trans (hcon b).symm)
    omega
  have hretx : ∀ p, p ≠ r → ∃ x l, I.act p (C.loc p) = .ret x l := by
    intro p hp
    cases h : I.act p (C.loc p) with
    | access i o k => exact absurd ⟨i, o, k, h⟩ (hret p hp)
    | ret x l => exact ⟨x, l, rfl⟩
  obtain ⟨x₀, -⟩ := hretx p₀ hp₀
  let f : P → A.Resp := fun p => if h : ∃ x l, I.act p (C.loc p) = .ret x l then h.choose else x₀
  have hf : ∀ p, p ≠ r → ∃ l, I.act p (C.loc p) = .ret (f p) l := by
    intro p hp
    have h := hretx p hp
    simp only [f, dif_pos h]
    exact h.choose_spec
  set ps := (Finset.univ.erase r).toList with hps
  have hnd : ps.Nodup := Finset.nodup_toList _
  have hmem : ∀ p, p ∈ ps ↔ p ≠ r := by intro p; simp [hps]
  obtain ⟨C₁, h1, h2, h3⟩ := arunFrom_rets (I := I) f ps C G hnd
    (fun p hp => ⟨hG.pend p ((hmem p).1 hp), hf p ((hmem p).1 hp)⟩)
  set β₁ := β ++ ps.map (fun p => (.ret p (f p) : Label P A)) with hβ₁
  have hrun₁ : arun I β₁ = some (C₁, G) := by rw [arun_append_of_eq I hG.run]; exact h1
  have hrnot : r ∉ ps := fun h => (hmem r).1 h rfl
  have hpendr : C₁.pend r = none := by rw [(h3 r hrnot).1]; exact hG.pendR
  obtain ⟨t, ht, v, γC, hγC⟩ := hR β₁ C₁ (arun_fst I hrun₁) hpendr
  set γ := β₁ ++ (.inv r rd :: (List.replicate t (.tau r) ++ [.ret r v]) : List (Label P A))
    with hγ
  obtain ⟨Gf, hGf⟩ := exists_arun I hγC
  have hsuf := hGf
  rw [hγ, arun_append_of_eq I hrun₁] at hsuf
  -- the reader's awareness set
  have hβ₁r : ∀ ℓ ∈ β₁, ℓ.proc ≠ r := by
    intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact hG.noR ℓ hℓ
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hℓ; exact (hmem p).1 hp
  have hawr : G.aw r = {r} := by
    have := arunFrom_aw_of_not_mem (I := I) (X := (I.initCfg, Ghost.init)) hrun₁ r hβ₁r
    simpa [Ghost.init] using this
  have hbound := solo_aw_bound (r := r) (I := I) hsuf
    (fun ℓ hℓ => by
      simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.mem_singleton] at hℓ
      rcases hℓ with rfl | ⟨-, rfl⟩ | rfl | h <;> simp_all [Label.proc])
    (B := 3 ^ j) (fun i => Or.inl (hG.bdd.2 i))
  have htc : tauCount ((.inv r rd :: (List.replicate t (.tau r) ++ [.ret r v])) : List (Label P A))
      r = t := by
    simp [tauCount, List.filter_append, List.filter_cons]
  rw [htc, hawr] at hbound
  simp only [Finset.card_singleton] at hbound
  -- Lemma 3
  have hops : ∀ p, (opsOf γ p).Sublist [if p = r then rd else u p] := by
    intro p
    have hβr : opsOf β r = [] := opsOf_eq_nil_of_proc_ne hG.noR
    by_cases hpr : p = r
    · subst hpr
      simp [hγ, hβ₁, hβr, opsOf_map_ret, opsOf_replicate]
    · simp [hγ, hβ₁, hG.ops p hpr, opsOf_map_ret, opsOf_replicate, hpr, Ne.symm hpr]
  have hprec : ∀ p, p ≠ r → Precedes γ (p, 0) (r, 0) := by
    intro p hp
    refine ⟨β₁, _, rfl, ?_, ?_⟩
    · unfold Completed
      simp [hβ₁, hG.resps p hp, respsOf_map_ret f ps hnd, (hmem p).2 hp]
    · unfold Invoked
      simp [hβ₁, opsOf_eq_nil_of_proc_ne hG.noR, opsOf_map_ret]
  have hv : respOf γ (r, 0) = some v := by
    unfold respOf
    have hβr : respsOf β r = [] := respsOf_eq_nil_of_proc_ne hG.noR
    simp [hγ, hβ₁, hβr, respsOf_map_ret f ps hnd, hrnot, respsOf_replicate]
  have hall := reader_aware_all u rd r hlin hrev hGf hops hprec hv
  have hcard : Fintype.card P ≤ (Gf.aw r).card := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (fun q _ => hall q)
  have : t * 3 ^ j ≤ R * 3 ^ j := Nat.mul_le_mul_right _ ht
  omega

/-- **Theorem 1 of Hendler–Khait, PODC'14 (generic, non-asymptotic form).** Let `I` be a
linearizable implementation, from read/write/CAS base objects, of an object in which every
process `p ≠ r` may apply the update `u p` and the reader's operation `rd` reveals the
participants (`Reveals`). If `rd` completes within `R` solo steps (`SoloBound`, e.g. an
obstruction-free implementation in which `rd` has step complexity `R`), then for every `k` with
`R · 3^k + 1 < N` there is an execution in which some process `p ≠ r` takes at least `k + 1`
steps while performing a single (still pending) update `u p`. -/
theorem update_lower_bound (hlin : I.Linearizable) (hrev : Reveals A r u rd)
    (hall : ∀ p, p ≠ r → I.allowed p (u p)) {R : ℕ} (hR : SoloBound I r rd R) (k : ℕ)
    (hk : R * 3 ^ k + 1 < Fintype.card P) :
    ∃ α, I.Valid α ∧ ∃ p, p ≠ r ∧ opsOf α p = [u p] ∧ respsOf α p = [] ∧
      k + 1 ≤ tauCount α p := by
  classical
  have key : ∀ j, j ≤ k → ∃ j' β C G, j' ≤ j ∧ Good (I := I) (u := u) (r := r) j' β C G ∧
      (j' = j ∨ ∀ p, p ≠ r → ¬ ∃ i o k, I.act p (C.loc p) = .access i o k) := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨β, C, G, hG⟩ := good_zero (I := I) (u := u) (r := r) hall
      exact ⟨0, β, C, G, le_rfl, hG, Or.inl rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨j', β, C, G, hj', hG, hor⟩ := ih (by omega)
      rcases hor with rfl | hor
      · by_cases hex : ∃ p, p ≠ r ∧ ∃ i o k, I.act p (C.loc p) = .access i o k
        · obtain ⟨β', C', G', hG', -⟩ := good_succ hG
          exact ⟨j' + 1, β', C', G', le_rfl, hG', Or.inl rfl⟩
        · push_neg at hex
          exact ⟨j', β, C, G, by omega, hG, Or.inr fun p hp h => by
            obtain ⟨i, o, k, h⟩ := h; exact hex p hp i o k h⟩
      · exact ⟨j', β, C, G, by omega, hG, Or.inr hor⟩
  obtain ⟨j', β, C, G, hj', hG, hor⟩ := key k le_rfl
  have hk' : R * 3 ^ j' + 1 < Fintype.card P :=
    lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) hj')) _) hk
  by_cases hex : ∃ p, p ≠ r ∧ ∃ i o k, I.act p (C.loc p) = .access i o k
  · rcases hor with rfl | hor
    · obtain ⟨p, hp, i, o, kk, hact⟩ := hex
      have hs := Impl.step_tau_eq_some (I := I) (hG.pend p hp) hact
      refine ⟨β ++ [.tau p], ⟨_, by rw [Impl.run_concat, arun_fst I hG.run]; exact hs⟩,
        p, hp, ?_, ?_, ?_⟩
      · simp [hG.ops p hp]
      · simp [hG.resps p hp]
      · rw [tauCount_append, hG.taus p hp ⟨i, o, kk, hact⟩]
        simp [tauCount]
    · obtain ⟨p, hp, h⟩ := hex
      exact absurd h (hor p hp)
  · push_neg at hex
    exact (final_contra (rd := rd) hlin hrev hR hG (fun p hp h => by
      obtain ⟨i, o, k, h⟩ := h; exact hex p hp i o k h) hk').elim

end Construction

end Podc.ReadUpdateTradeoffs
