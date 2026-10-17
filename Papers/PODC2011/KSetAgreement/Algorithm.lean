import Papers.PODC2011.KSetAgreement.Basic
import Papers.PODC2011.KSetAgreement.SourceComponents

/-!
# The k-set agreement algorithm for initially dead processes (Section VI of [BRS11])

The two-stage protocol of Fischer, Lynch and Paterson for initially dead processes, as generalized
in Section VI of the paper, with `L = n - f` and `δ = L - 1 = n - f - 1` (the parameter `d` below):

* **Stage 1.** Upon waking up, a process sends a stage-1 message (its id) to all others and waits
  for stage-1 messages from `d` other processes; the set of these senders is its *in-list*.
* **Stage 2.** Having chosen its in-list `I`, it sends `(x_p, I)` to all others, and records all
  stage-2 messages it receives (`know`). The in-lists define the digraph `G` with edges `u → r`
  iff `u ∈ I_r`.
* **Decision.** As soon as `know` is *closed* (it contains `p` and, for every recorded `r`, all
  members of `I_r`), `p` knows all its ancestors in `G` together with their in-lists. It decides
  the input of `m`, the minimum *root* ancestor of `p` (a root is a vertex of a source component).

This file contains the definitions and the local (per-process) lemmas.
-/

namespace KSetAgreement.InitDeadAlg

open Cslib Cslib.FLP Relation SourceComp

variable {n : ℕ} {V : Type}

/-- Message contents: sender and payload; `none` = stage-1 message, `some (v, I)` = stage-2
message with the sender's input `v` and in-list `I`. -/
abbrev Msg (n : ℕ) (V : Type) := Fin n × Option (V × Finset (Fin n))

/-- Local state of a process (the decision is kept separately by `KAlgorithm`). -/
@[ext] structure St (n : ℕ) (V : Type) where
  /-- Own input. -/
  input : V
  /-- Senders of the stage-1 messages received so far (frozen once the in-list is chosen). -/
  heard : Finset (Fin n)
  /-- The chosen in-list (`none` = still in stage 1). -/
  inl : Option (Finset (Fin n))
  /-- Stage-2 information: input and in-list of other processes (and of itself). -/
  know : Fin n → Option (V × Finset (Fin n))

/-! ### The known graph and the decision rule -/

/-- A partial map of in-lists (`IL r = some I`: `r` chose in-list `I`). -/
abbrev InLists (n : ℕ) := Fin n → Option (Finset (Fin n))

/-- The digraph of in-lists: `u → r` iff `r` has chosen an in-list containing `u`. -/
def Edge (IL : InLists n) (u r : Fin n) : Prop := ∃ I, IL r = some I ∧ u ∈ I

/-- The in-lists recorded in `know`. -/
def ilOf (know : Fin n → Option (V × Finset (Fin n))) : InLists n := fun r => (know r).map Prod.snd

/-- `know` is closed at `p`: it contains `p`, and the in-lists of all recorded processes. -/
def Closed (know : Fin n → Option (V × Finset (Fin n))) (p : Fin n) : Prop :=
  (know p).isSome ∧ ∀ r vI, know r = some vI → ∀ u ∈ vI.2, (know u).isSome

open Classical in
/-- The root ancestors of `p` in the known graph. -/
noncomputable def roots (know : Fin n → Option (V × Finset (Fin n))) (p : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun r => ReflTransGen (Edge (ilOf know)) r p ∧ IsRoot (Edge (ilOf know)) r

open Classical in
/-- The decision rule: if `know` is closed, the input of the minimal root ancestor of `p`. -/
noncomputable def tryDec (p : Fin n) (st : St n V) : Option V :=
  if Closed st.know p then
    if h : (roots st.know p).Nonempty then (st.know ((roots st.know p).min' h)).map Prod.fst
    else none
  else none

/-! ### The algorithm -/

/-- Processing an event (before the in-list check). -/
def pre (p : Fin n) : Option (Msg n V) → St n V → St n V
  | none, st => st
  | some (q, none), st =>
      if q ≠ p ∧ st.inl = none then { st with heard := insert q st.heard } else st
  | some (q, some vI), st =>
      if q ≠ p then { st with know := Function.update st.know q (some vI) } else st

/-- `p` is ready to choose its in-list. -/
def Ready (d : ℕ) (st : St n V) : Prop := st.inl = none ∧ d ≤ st.heard.card

instance (d : ℕ) (st : St n V) : Decidable (Ready d st) := by unfold Ready; infer_instance

/-- Choosing the in-list (once `d` stage-1 messages have been received). -/
def post (d : ℕ) (p : Fin n) (st : St n V) : St n V :=
  if Ready d st then
    { st with inl := some st.heard, know := Function.update st.know p (some (st.input, st.heard)) }
  else st

/-- Broadcast content `c` from `p` to all other processes. -/
def bcast (p : Fin n) (c : Msg n V) : Multiset (Fin n × Msg n V) :=
  (Finset.univ.erase p).val.map fun q => (q, c)

/-- Stage-2 messages sent when the in-list is chosen. -/
def stage2 (d : ℕ) (p : Fin n) (st : St n V) : Multiset (Fin n × Msg n V) :=
  if Ready d st then bcast p (p, some (st.input, st.heard)) else 0

/-- Stage-1 messages, sent upon wake-up. -/
def stage1 (p : Fin n) : Option (Msg n V) → Multiset (Fin n × Msg n V)
  | none => bcast p (p, none)
  | some _ => 0

/-- **The algorithm of Section VI** (with `d = L - 1 = n - f - 1`). -/
noncomputable def alg (d : ℕ) : KAlgorithm (Fin n) (Msg n V) (St n V) V where
  init _ v := ⟨v, ∅, none, fun _ => none⟩
  step p e st := post d p (pre p e st.1)
  send p e st := stage1 p e + stage2 d p (pre p e st.1)
  out p e st := tryDec p (post d p (pre p e st.1))

/-! ### Local lemmas -/

@[simp] theorem pre_input (p : Fin n) (e : Option (Msg n V)) (st : St n V) :
    (pre p e st).input = st.input := by
  rcases e with _ | ⟨q, _ | vI⟩ <;> simp only [pre] <;> split_ifs <;> rfl

@[simp] theorem pre_inl (p : Fin n) (e : Option (Msg n V)) (st : St n V) :
    (pre p e st).inl = st.inl := by
  rcases e with _ | ⟨q, _ | vI⟩ <;> simp only [pre] <;> split_ifs <;> rfl

@[simp] theorem post_input (d : ℕ) (p : Fin n) (st : St n V) :
    (post d p st).input = st.input := by
  unfold post; split_ifs <;> rfl

theorem post_inl_of_some (d : ℕ) (p : Fin n) {st : St n V} {I : Finset (Fin n)}
    (h : st.inl = some I) : (post d p st).inl = some I := by
  unfold post Ready; split_ifs with h' <;> simp_all

theorem step_inl_of_some (d : ℕ) (p : Fin n) (e : Option (Msg n V)) {st : St n V}
    {I : Finset (Fin n)} (h : st.inl = some I) : (post d p (pre p e st)).inl = some I :=
  post_inl_of_some d p (by rw [pre_inl]; exact h)

/-- The in-list never changes once chosen (along a run of events). -/
theorem run_inl_of_some (d : ℕ) (p : Fin n) (es : List (Option (Msg n V))) (st : St n V × Option V)
    {I : Finset (Fin n)} (h : st.1.inl = some I) :
    (((alg (V := V) d).run p es st).1.1).inl = some I := by
  induction es generalizing st with
  | nil => exact h
  | cons e es ih =>
    exact ih _ (step_inl_of_some d p e h)

/-! ### Graph lemmas -/

/-- `IL'` extends `IL` (in-lists, once chosen, are never changed). -/
def Ext (IL IL' : InLists n) : Prop := ∀ r I, IL r = some I → IL' r = some I

theorem Ext.refl (IL : InLists n) : Ext IL IL := fun _ _ h => h

theorem Ext.trans {IL₁ IL₂ IL₃ : InLists n} (h₁ : Ext IL₁ IL₂) (h₂ : Ext IL₂ IL₃) :
    Ext IL₁ IL₃ := fun r I h => h₂ r I (h₁ r I h)

theorem Ext.edge {IL IL' : InLists n} (h : Ext IL IL') {u r : Fin n} (he : Edge IL u r) :
    Edge IL' u r := by
  obtain ⟨I, hI, hu⟩ := he
  exact ⟨I, h r I hI, hu⟩

theorem Ext.rtg {IL IL' : InLists n} (h : Ext IL IL') {u r : Fin n}
    (he : ReflTransGen (Edge IL) u r) : ReflTransGen (Edge IL') u r :=
  ReflTransGen.mono (fun _ _ => h.edge) _ _ he

/-- If `IL'` extends `IL`, and `S` is a set of processes with chosen in-lists closed under
in-neighbours, then `IL` and `IL'` have the same ancestors of members of `S`. -/
theorem Ext.rtg_iff {IL IL' : InLists n} (h : Ext IL IL') {S : Set (Fin n)}
    (hS1 : ∀ r ∈ S, (IL r).isSome) (hS2 : ∀ r ∈ S, ∀ u, Edge IL u r → u ∈ S) {u r : Fin n}
    (hr : r ∈ S) : ReflTransGen (Edge IL') u r ↔ ReflTransGen (Edge IL) u r := by
  refine Digraph.reachable_iff_of_closed (G := ⟨Edge IL⟩) (H := ⟨Edge IL'⟩) (fun r hr u => ?_)
    hS2 hr
  obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 (hS1 r hr)
  simp [Edge, hI, h r I hI]

/-- `m` is a *frozen root* of the in-list graph: all its ancestors have chosen their in-lists
(so its ancestor set will never change), it is a root, and it is the minimum of its source
component. -/
structure FrozenRoot (IL : InLists n) (m : Fin n) : Prop where
  frozen : ∀ u, ReflTransGen (Edge IL) u m → (IL u).isSome
  root : IsRoot (Edge IL) m
  min : ∀ u, ReflTransGen (Edge IL) u m → m ≤ u

theorem FrozenRoot.mono {IL IL' : InLists n} (h : Ext IL IL') {m : Fin n}
    (hm : FrozenRoot IL m) : FrozenRoot IL' m := by
  have key : ∀ u, ReflTransGen (Edge IL') u m ↔ ReflTransGen (Edge IL) u m := fun u =>
    h.rtg_iff (S := {u | ReflTransGen (Edge IL) u m}) (fun r hr => hm.frozen r hr)
      (fun r hr u hu => ReflTransGen.head hu hr) ReflTransGen.refl
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => hm.min u ((key u).1 hu)⟩
  · obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 (hm.frozen u ((key u).1 hu))
    simp [h u I hI]
  · exact h.rtg (hm.root u ((key u).1 hu))

theorem mem_roots {know : Fin n → Option (V × Finset (Fin n))} {p r : Fin n} :
    r ∈ roots know p ↔ ReflTransGen (Edge (ilOf know)) r p ∧ IsRoot (Edge (ilOf know)) r := by
  classical
  simp [roots]

/-- Consistency of recorded stage-2 information with the actual in-lists and inputs. -/
def KnowOK (x : Fin n → V) (IL : InLists n) (know : Fin n → Option (V × Finset (Fin n))) :
    Prop :=
  ∀ r v I, know r = some (v, I) → v = x r ∧ IL r = some I

theorem Closed.inClosed {know : Fin n → Option (V × Finset (Fin n))} {p : Fin n}
    (hc : Closed know p) : ∀ r ∈ {r | (know r).isSome}, ∀ u, Edge (ilOf know) u r →
      u ∈ {r | (know r).isSome} := by
  rintro r - u ⟨I, hI, hu⟩
  simp only [ilOf, Option.map_eq_some_iff] at hI
  obtain ⟨⟨v, I'⟩, hr, rfl⟩ := hI
  exact hc.2 r _ hr u hu

theorem Closed.isSome_of_rtg {know : Fin n → Option (V × Finset (Fin n))} {p : Fin n}
    (hc : Closed know p) {u : Fin n} (hu : ReflTransGen (Edge (ilOf know)) u p) :
    (know u).isSome :=
  Digraph.mem_of_reachable_of_closed (G := ⟨Edge (ilOf know)⟩) hc.inClosed hu hc.1

/-- The decision rule of a closed `know` that is consistent with the actual in-lists picks a
frozen root. -/
theorem frozenRoot_of_closed {x : Fin n → V} {IL : InLists n}
    {know : Fin n → Option (V × Finset (Fin n))} (hk : KnowOK x IL know) {p m : Fin n}
    (hc : Closed know p) (hm : m ∈ roots know p) (hmin : ∀ r ∈ roots know p, m ≤ r) :
    FrozenRoot IL m := by
  set K := ilOf know
  have hext : Ext K IL := by
    intro r I hI
    simp only [K, ilOf, Option.map_eq_some_iff] at hI
    obtain ⟨⟨v, I'⟩, hr, rfl⟩ := hI
    exact (hk r v I' hr).2
  have hS1 : ∀ r ∈ {r | (know r).isSome}, (K r).isSome := by
    intro r hr; simpa [K, ilOf] using hr
  rw [mem_roots] at hm
  have hmS : (know m).isSome := hc.isSome_of_rtg hm.1
  have key : ∀ u, ReflTransGen (Edge IL) u m ↔ ReflTransGen (Edge K) u m := fun u =>
    hext.rtg_iff hS1 hc.inClosed hmS
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · have hu' := (key u).1 hu
    obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 (hS1 u (hc.isSome_of_rtg (hu'.trans hm.1)))
    simp [hext u I hI]
  · exact hext.rtg (hm.2 u ((key u).1 hu))
  · have hu' := (key u).1 hu
    exact hmin u (mem_roots.2 ⟨hu'.trans hm.1, hm.2.of_reachable hu'⟩)

theorem roots_nonempty (know : Fin n → Option (V × Finset (Fin n))) (p : Fin n) :
    (roots know p).Nonempty := by
  obtain ⟨r, hr, hroot⟩ := (Digraph.mk (Edge (ilOf know))).exists_inSourceComponent p
  exact ⟨r, mem_roots.2 ⟨hr, hroot⟩⟩

theorem tryDec_isSome {p : Fin n} {st : St n V} (hc : Closed st.know p) :
    (tryDec p st).isSome := by
  have hne := roots_nonempty st.know p
  have hm := mem_roots.1 ((roots st.know p).min'_mem hne)
  have := hc.isSome_of_rtg hm.1
  simp only [tryDec, hc, ↓reduceIte, hne, ↓reduceDIte, Option.isSome_map]
  exact this

theorem tryDec_spec {x : Fin n → V} {IL : InLists n} {p : Fin n} {st : St n V}
    (hk : KnowOK x IL st.know) {v : V} (h : tryDec p st = some v) :
    ∃ m, v = x m ∧ FrozenRoot IL m := by
  unfold tryDec at h
  split_ifs at h with hc hne
  obtain ⟨⟨v', I⟩, hm, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨_, (hk _ _ _ hm).1, frozenRoot_of_closed hk hc ((roots st.know p).min'_mem hne)
    (fun r hr => Finset.min'_le _ _ hr)⟩

/-! ### Local invariants -/

/-- A message content is consistent with the in-lists `IL`, the woken processes `W` and the
inputs `x`: stage-1 senders are woken; stage-2 messages carry the sender's input and in-list. -/
def GoodMsg (x : Fin n → V) (IL : InLists n) (W : Fin n → Prop) (c : Msg n V) : Prop :=
  (c.2 = none → W c.1) ∧ ∀ v I, c.2 = some (v, I) → v = x c.1 ∧ IL c.1 = some I

theorem GoodMsg.mono {x : Fin n → V} {IL IL' : InLists n} {W W' : Fin n → Prop} {c : Msg n V}
    (h : Ext IL IL') (hW : ∀ r, W r → W' r) (hc : GoodMsg x IL W c) : GoodMsg x IL' W' c :=
  ⟨fun h0 => hW _ (hc.1 h0), fun v I h1 => ⟨(hc.2 v I h1).1, h _ _ (hc.2 v I h1).2⟩⟩

/-- The invariant of the local state of a woken process `p` (relative to the global in-lists
`IL` and woken processes `W`). -/
structure LocalGood (x : Fin n → V) (d : ℕ) (IL : InLists n) (W : Fin n → Prop) (p : Fin n)
    (st : St n V) (dec : Option V) : Prop where
  input : st.input = x p
  notMem_heard : p ∉ st.heard
  heard : ∀ u ∈ st.heard, W u
  inl : ∀ I, st.inl = some I →
    IL p = some I ∧ I = st.heard ∧ d ≤ I.card ∧ st.know p = some (st.input, I)
  know : KnowOK x IL st.know
  dec : ∀ v, dec = some v → ∃ m, v = x m ∧ FrozenRoot IL m

theorem LocalGood.mono {x : Fin n → V} {d : ℕ} {IL IL' : InLists n} {W W' : Fin n → Prop}
    {p : Fin n} {st : St n V} {dec : Option V} (h : Ext IL IL') (hW : ∀ r, W r → W' r)
    (hg : LocalGood x d IL W p st dec) : LocalGood x d IL' W' p st dec where
  input := hg.input
  notMem_heard := hg.notMem_heard
  heard u hu := hW u (hg.heard u hu)
  inl I hI := ⟨h _ _ (hg.inl I hI).1, (hg.inl I hI).2⟩
  know r v I hr := ⟨(hg.know r v I hr).1, h _ _ (hg.know r v I hr).2⟩
  dec v hv := by
    obtain ⟨m, hm, hfr⟩ := hg.dec v hv
    exact ⟨m, hm, hfr.mono h⟩

/-- Properties guaranteed after every event. -/
structure PostGood (d : ℕ) (p : Fin n) (st : St n V) (dec : Option V) : Prop where
  heard : st.inl = none → st.heard.card < d
  closed : Closed st.know p → dec.isSome

theorem apply_postGood (d : ℕ) (p : Fin n) (e : Option (Msg n V)) (st : St n V × Option V) :
    PostGood d p ((alg d).apply p e st).1 ((alg d).apply p e st).2 := by
  refine ⟨fun h => ?_, fun hc => ?_⟩
  · simp only [KAlgorithm.apply, alg, post] at h ⊢
    by_cases hr : Ready d (pre p e st.1)
    · simp [hr] at h
    · simp only [hr, ite_false] at h ⊢
      simp only [Ready, not_and, not_le] at hr
      exact hr h
  · simp only [KAlgorithm.apply, alg] at hc ⊢
    simp [Option.isSome_or, tryDec_isSome hc]

theorem run_postGood (d : ℕ) (p : Fin n) (e : Option (Msg n V)) (es : List (Option (Msg n V)))
    (st : St n V × Option V) :
    PostGood d p ((alg d).run p (e :: es) st).1.1 ((alg d).run p (e :: es) st).1.2 := by
  induction es generalizing e st with
  | nil => exact apply_postGood d p e st
  | cons e' es ih => exact ih e' _

theorem pre_good {x : Fin n → V} {d : ℕ} {IL : InLists n} {W : Fin n → Prop} {p : Fin n}
    {st : St n V} {dec : Option V} {e : Option (Msg n V)} (hg : LocalGood x d IL W p st dec)
    (he : ∀ c, e = some c → GoodMsg x IL W c) : LocalGood x d IL W p (pre p e st) dec := by
  rcases e with _ | ⟨q, _ | ⟨v, I⟩⟩
  · exact hg
  · have hq := (he _ rfl).1 rfl
    simp only [pre]
    split_ifs with h
    · obtain ⟨hqp, hinl⟩ := h
      refine ⟨hg.input, ?_, ?_, ?_, hg.know, hg.dec⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => hqp h.symm, hg.notMem_heard⟩
      · intro u hu
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact hq
        · exact hg.heard u hu
      · intro I hI
        simp [hinl] at hI
    · exact hg
  · have hq := (he _ rfl).2 v I rfl
    simp only [pre]
    split_ifs with hqp
    · refine ⟨hg.input, hg.notMem_heard, hg.heard, ?_, ?_, hg.dec⟩
      · intro J hJ
        have := hg.inl J hJ
        simp only [Function.update_of_ne (Ne.symm hqp)]
        exact this
      · intro r v' J hr
        by_cases hrq : r = q
        · subst hrq
          simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact hq
        · simp only [Function.update_of_ne hrq] at hr
          exact hg.know r v' J hr
    · exact hg

theorem post_good {x : Fin n → V} {d : ℕ} {IL : InLists n} {W : Fin n → Prop} {p : Fin n}
    {st : St n V} {dec : Option V} (hg : LocalGood x d IL W p st dec)
    (hIL : ∀ I, (post d p st).inl = some I → IL p = some I) :
    LocalGood x d IL W p (post d p st) dec := by
  unfold post at hIL ⊢
  split_ifs with hr
  · simp only [ite_true, hr] at hIL
    have hp := hIL _ rfl
    refine ⟨hg.input, hg.notMem_heard, hg.heard, ?_, ?_, hg.dec⟩
    · intro I hI
      simp only [Option.some.injEq] at hI
      subst hI
      simp [hp, hr.2]
    · intro r v J hrJ
      by_cases hrp : r = p
      · subst hrp
        simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hrJ
        obtain ⟨rfl, rfl⟩ := hrJ
        exact ⟨hg.input, hp⟩
      · simp only [Function.update_of_ne hrp] at hrJ
        exact hg.know r v J hrJ
  · exact hg

theorem mem_bcast {p : Fin n} {c : Msg n V} {qc : Fin n × Msg n V} (h : qc ∈ bcast p c) :
    qc.2 = c ∧ qc.1 ≠ p := by
  simp only [bcast, Multiset.mem_map, Finset.mem_val, Finset.mem_erase, Finset.mem_univ,
    and_true] at h
  obtain ⟨q, hq, rfl⟩ := h
  exact ⟨rfl, hq⟩

theorem mem_bcast_of_ne {p : Fin n} {c : Msg n V} {q : Fin n} (hq : q ≠ p) :
    (q, c) ∈ bcast p c := by
  exact Multiset.mem_map.2 ⟨q, (Finset.mem_erase.2 ⟨hq, Finset.mem_univ _⟩ : q ∈ Finset.univ.erase p), rfl⟩

/-- One event preserves the local invariant, and all messages sent are good. -/
theorem apply_good {x : Fin n → V} {d : ℕ} {IL : InLists n} {W : Fin n → Prop} {p : Fin n}
    {st : St n V} {dec : Option V} {e : Option (Msg n V)} (hg : LocalGood x d IL W p st dec)
    (hW : W p) (he : ∀ c, e = some c → GoodMsg x IL W c)
    (hIL : ∀ I, (post d p (pre p e st)).inl = some I → IL p = some I) :
    LocalGood x d IL W p ((alg d).apply p e (st, dec)).1 ((alg d).apply p e (st, dec)).2 ∧
      ∀ qc ∈ (alg d).send p e (st, dec), GoodMsg x IL W qc.2 := by
  have h1 := post_good (pre_good hg he) hIL
  refine ⟨⟨h1.input, h1.notMem_heard, h1.heard, h1.inl, h1.know, ?_⟩, ?_⟩
  · intro v hv
    simp only [KAlgorithm.apply, alg] at hv
    cases hdec : dec with
    | some w =>
      rw [hdec] at hv
      simp only [Option.some_or, Option.some.injEq] at hv
      subst hv
      exact hg.dec w hdec
    | none =>
      rw [hdec] at hv
      simp only [Option.none_or] at hv
      exact tryDec_spec h1.know hv
  · intro qc hqc
    simp only [alg, Multiset.mem_add] at hqc
    rcases hqc with hqc | hqc
    · rcases e with _ | c
      · rw [(mem_bcast hqc).1]
        exact ⟨fun _ => hW, fun v I h => by simp at h⟩
      · simp [stage1] at hqc
    · simp only [stage2] at hqc
      split_ifs at hqc with hr
      · rw [(mem_bcast hqc).1]
        refine ⟨fun h => by simp at h, fun v I h => ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simpa using hg.input, hIL _ ?_⟩
        simp [post, hr]
      · simp at hqc

/-- A run of events preserves the local invariant, and all messages sent are good. -/
theorem run_good {x : Fin n → V} {d : ℕ} {IL : InLists n} {W : Fin n → Prop} {p : Fin n}
    (hW : W p) (es : List (Option (Msg n V))) (st : St n V) (dec : Option V)
    (hg : LocalGood x d IL W p st dec) (hes : ∀ c, some c ∈ es → GoodMsg x IL W c)
    (hIL : ∀ I, ((alg d).run p es (st, dec)).1.1.inl = some I → IL p = some I) :
    LocalGood x d IL W p ((alg d).run p es (st, dec)).1.1 ((alg d).run p es (st, dec)).1.2 ∧
      ∀ qc ∈ ((alg d).run p es (st, dec)).2, GoodMsg x IL W qc.2 := by
  induction es generalizing st dec with
  | nil => exact ⟨hg, fun qc hqc => by simp [KAlgorithm.run] at hqc⟩
  | cons e es ih =>
    have hIL1 : ∀ I, (post d p (pre p e st)).inl = some I → IL p = some I := fun I hI =>
      hIL I (run_inl_of_some d p es ((alg d).apply p e (st, dec)) hI)
    obtain ⟨hg1, hs1⟩ := apply_good hg hW (fun c hc => hes c (hc ▸ List.mem_cons_self ..)) hIL1
    obtain ⟨hg2, hs2⟩ := ih _ _ hg1 (fun c hc => hes c (List.mem_cons_of_mem _ hc)) hIL
    refine ⟨hg2, fun qc hqc => ?_⟩
    simp only [KAlgorithm.run, Multiset.mem_add] at hqc
    rcases hqc with hqc | hqc
    · exact hs1 qc hqc
    · exact hs2 qc hqc

end KSetAgreement.InitDeadAlg
