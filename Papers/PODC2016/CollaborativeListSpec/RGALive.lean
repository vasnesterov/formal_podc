import Papers.PODC2016.CollaborativeListSpec.RGA
import Papers.PODC2016.CollaborativeListSpec.SpecFacts

/-!
# Theorem 1 for infinite executions: eventual visibility (Definitions 1, 9, 10)

Attiya, Burckhardt, Gotsman, Morrison, Yang, Zawirski. *Specification and space complexity of
collaborative text editing.* TCS 855 (2021); PODC 2016.

An infinite execution is a sequence `f : ℕ → Act Rep Op`; its finite prefixes are `pre f m`
(`Encoding.lean`). It is well formed (`InfWF`) iff all its prefixes are. The history of `do`
events and the visibility relation (happens-before) of the infinite execution are read off long
enough prefixes (`histInf`, `visInf`); both are prefix-stable.

* `SufficientlyConnected` is Definition 1 (eventual transmission, eventual delivery).
* `RGA.theorem1_strong_inf`: the abstract execution `(histInf, visInf)` of every infinite
  execution of RGA with causal broadcast (and the user assumptions) is in `A_strong`, with one
  global list order: `lo a b` iff `[a, b]` is a subsequence of `s(Nall)` of some prefix
  (consistent by Lemma 6).
* `RGA.theorem1_eventualVisibility`: if moreover the network is sufficiently connected, this
  abstract execution satisfies eventual visibility (Definition 9). This is Theorem 1, liveness
  part.
* `RGA.def10_needs_connectivity`: Definition 10 as literally stated quantifies over *all*
  executions with causal broadcast, without the connectivity assumption of Definition 1; then no
  protocol that ever buffers messages guarantees eventual visibility. For RGA: replica 0 inserts
  and never sends, replica 1 reads forever; no abstract execution in `A_weak` with eventual
  visibility complies with it. The paper's remark after Definition 10 ("a protocol would rely on
  the network being sufficiently connected") and the proof of Theorem 1 show that the intended
  definition only quantifies over sufficiently connected infinite executions.
-/

namespace Podc.CollaborativeListSpec

section Defs

variable {Rep Op Val Q M : Type} [DecidableEq Rep]

/-- An infinite execution is well formed iff all its finite prefixes are. -/
def InfWF (P : Protocol Rep Op Val Q M) (f : ℕ → Act Rep Op) : Prop := ∀ m, P.WF (pre f m)

/-- **Definition 1** (sufficiently connected network) for an infinite execution `f`.
(1) Eventual transmission: if replica `r` has a message pending (after the event at position `m`)
for infinitely many `m`, then `r` sends infinitely often. (2) Eventual delivery: the message of
every send event (at position `s`, by `r`) is received by every replica `r' ≠ r`. -/
def SufficientlyConnected (P : Protocol Rep Op Val Q M) (f : ℕ → Act Rep Op) : Prop :=
  (∀ r : Rep, (∀ N, ∃ m ≥ N, ((P.exec (pre f (m + 1))).st r).2.isSome) →
      ∀ N, ∃ m ≥ N, f m = .send r) ∧
  (∀ s (r : Rep), f s = .send r → ∀ r', r' ≠ r → ∃ q, f q = .recv r' s)

/-- The history of the `do` events of an infinite execution (indexed by position). -/
def histInf (P : Protocol Rep Op Val Q M) (f : ℕ → Act Rep Op) (p : ℕ) : Option (Rep × Op × Val) :=
  P.hist (pre f (p + 1)) p

end Defs

/-- Visibility of an infinite execution: happens-before between `do` events. -/
def visInf {Rep U : Type} (f : ℕ → Act Rep (LOp U)) (i j : ℕ) : Prop :=
  visHB (pre f (j + 1)) i j

section Prefix

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U] {P : Protocol Rep (LOp U) (List U) Q M}
  {f : ℕ → Act Rep (LOp U)}

theorem histInf_eq {p m : ℕ} (hp : p < m) : histInf P f p = P.hist (pre f m) p := by
  rcases le_total (p + 1) m with h | h
  · exact hist_prefix (pre_prefix f h) (by simp)
  · exact (hist_prefix (pre_prefix f h) (by simp; omega)).symm

omit [DecidableEq Rep] [DecidableEq U] in
theorem isDo_pre_iff {m p : ℕ} (hp : p < m) : IsDo (pre f m) p ↔ ∃ r op, f p = .doOp r op := by
  simp [IsDo, pre_getElem?_of_lt f hp]

omit [DecidableEq Rep] [DecidableEq U] in
theorem visInf_iff {i j m : ℕ} (hj : j < m) : visInf f i j ↔ visHB (pre f m) i j := by
  have key : ∀ m₁ m₂, j < m₁ → m₁ ≤ m₂ → (visHB (pre f m₁) i j ↔ visHB (pre f m₂) i j) := by
    intro m₁ m₂ h₁ h₂
    unfold visHB
    rw [HB.prefix_iff (pre_prefix f h₂) (i := i) (by simpa using h₁)]
    constructor
    · rintro ⟨h, hi, hj'⟩
      have hij := h.lt
      rw [isDo_pre_iff (by omega)] at hi hj' ⊢
      rw [isDo_pre_iff (by omega)]
      exact ⟨h, hi, hj'⟩
    · rintro ⟨h, hi, hj'⟩
      have hij := h.lt
      rw [isDo_pre_iff (by omega)] at hi hj' ⊢
      rw [isDo_pre_iff (by omega)]
      exact ⟨h, hi, hj'⟩
  unfold visInf
  rcases le_total (j + 1) m with h | h
  · exact key _ _ (by omega) h
  · exact (key _ _ hj h).symm

omit [DecidableEq Rep] [DecidableEq U] in
theorem visInf_lt {i j : ℕ} (h : visInf f i j) : i < j := h.1.lt

/-- The infinite abstract execution is causal (Definition 4). -/
theorem absWF_inf : AbsWF (histInf P f) (visInf f) where
  dom i j h := by
    have hij := visInf_lt h
    rw [histInf_eq (show i < j + 1 by omega), histInf_eq (show j < j + 1 by omega)]
    exact (visHB_absWF (P := P) _).dom i j h
  ro i j a b hij ha hb hab := by
    rw [histInf_eq (show i < j + 1 by omega)] at ha
    rw [histInf_eq (show j < j + 1 by omega)] at hb
    exact (visHB_absWF (P := P) _).ro i j a b hij ha hb hab
  trans i j k h₁ h₂ := by
    have hjk := visInf_lt h₂
    rw [visInf_iff (show j < k + 1 by omega)] at h₁
    exact (visHB_absWF (P := P) _).trans i j k h₁ h₂
  irrefl i h := lt_irrefl _ (visInf_lt h)

theorem elems_pre_subset {m : ℕ} {a : U} (ha : a ∈ elems (P.hist (pre f m))) :
    a ∈ elems (histInf P f) := by
  obtain ⟨p, r, k, w, hp⟩ := ha
  have hpm : p < m := by
    have := (hist_eq_some hp).1
    rw [pre_getElem?] at this; split_ifs at this with h; exact h
  exact ⟨p, r, k, w, by rw [histInf_eq hpm]; exact hp⟩

omit [DecidableEq U] in
theorem elems_histInf {a : U} (ha : a ∈ elems (histInf P f)) :
    ∃ p, a ∈ elems (P.hist (pre f (p + 1))) := by
  obtain ⟨p, r, k, w, hp⟩ := ha
  exact ⟨p, p, r, k, w, hp⟩

omit [DecidableEq U] in
/-- A receive names an earlier position (well-formedness). -/
theorem recv_src_lt (hwf : InfWF P f) {q s : ℕ} {r : Rep} (hq : f q = .recv r s) : s < q := by
  have := hwf (q + 1) q (by simp)
  simp only [pre, List.getElem_map, List.getElem_range, hq] at this
  exact this.1

end Prefix

section VisCongr

variable {Rep U : Type} {h h' : ℕ → Option (Rep × LOp U × List U)} {vis vis' : ℕ → ℕ → Prop}
  {p : ℕ}

theorem insVis_congr (hv : ∀ q, VisLe vis q p ↔ VisLe vis' q p)
    (hh : ∀ q, VisLe vis q p → h q = h' q) (a : U) : InsVis h vis p a ↔ InsVis h' vis' p a := by
  constructor
  · rintro ⟨q, r, k, w, hq, hhq⟩
    exact ⟨q, r, k, w, (hv q).1 hq, (hh q hq) ▸ hhq⟩
  · rintro ⟨q, r, k, w, hq, hhq⟩
    exact ⟨q, r, k, w, (hv q).2 hq, (hh q ((hv q).2 hq)) ▸ hhq⟩

theorem delVis_congr (hv : ∀ q, VisLe vis q p ↔ VisLe vis' q p)
    (hh : ∀ q, VisLe vis q p → h q = h' q) (a : U) : DelVis h vis p a ↔ DelVis h' vis' p a := by
  constructor
  · rintro ⟨q, r, w, hq, hhq⟩
    exact ⟨q, r, w, (hv q).1 hq, (hh q hq) ▸ hhq⟩
  · rintro ⟨q, r, w, hq, hhq⟩
    exact ⟨q, r, w, (hv q).2 hq, (hh q ((hv q).2 hq)) ▸ hhq⟩

end VisCongr

namespace RGA

variable {U : Type} [DecidableEq U] {n : ℕ}

/-! ### Theorem 1 (safety) for infinite executions -/

section Safety

theorem nodeAt_prefix {α β : List (Act (Fin n) (LOp U))} (h : α <+: β) {q : ℕ}
    (hq : q < α.length) : nodeAt α q = nodeAt β q := by
  have h1 : α[q]? = β[q]? := List.IsPrefix.getElem?_of_lt h hq
  have h2 : α.take q = β.take q := by
    obtain ⟨t, rfl⟩ := h; rw [List.take_append_of_le_length hq.le]
  simp only [nodeAt, Protocol.stBefore, h1, h2]

theorem Nall_mono {α β : List (Act (Fin n) (LOp U))} (h : α <+: β) {x : Node U}
    (hx : x ∈ Nall α) : x ∈ Nall β := by
  obtain ⟨q, hq⟩ := mem_Nall.1 hx
  exact mem_Nall.2 ⟨q, (nodeAt_prefix h (lt_length_of_nodeAt hq)) ▸ hq⟩

variable {f : ℕ → Act (Fin n) (LOp U)} (hwf : InfWF (protocol U n) f)
  (hadm : ∀ m, Adm U n (pre f m))
include hwf hadm

theorem isTITree_Nall_pre (m : ℕ) : IsTITree (Nall (pre f m)) :=
  isTITree_Nall (hwf m) (hadm m).1 (hadm m).2.1

theorem s_Nall_sublist {m m' : ℕ} (h : m ≤ m') :
    (s (Nall (pre f m))).Sublist (s (Nall (pre f m'))) :=
  s_sublist (isTITree_Nall_pre hwf hadm m) (isTITree_Nall_pre hwf hadm m')
    (fun _ hx => Nall_mono (pre_prefix f h) hx)

/-- A response is a subsequence of `s(Nall)` of the prefix ending with it (Lemma 6). -/
theorem resp_sublist {p : ℕ} {r : Fin n} {op : LOp U} {w : List U}
    (hp : histInf (protocol U n) f p = some (r, op, w)) :
    w.Sublist (s (Nall (pre f (p + 1)))) := by
  set α := pre f (p + 1)
  obtain ⟨hα, rfl⟩ := hist_eq_some (P := protocol U n) hp
  have hlen := lt_length_of_getElem? hα
  obtain ⟨hC, hU, -⟩ := hadm (p + 1)
  have hTI := isTITree_st (hwf (p + 1)) hC hU (m := p + 1) hlen r
  rw [resp_eq hα]
  exact List.filter_sublist.trans (s_sublist hTI (isTITree_Nall (hwf (p + 1)) hC hU)
    fun x hx => mem_Nall_of_mem (hwf (p + 1)) hC hlen hx)

theorem mem_s_of_elems {a : U} (ha : a ∈ elems (histInf (protocol U n) f)) :
    ∃ m, a ∈ s (Nall (pre f m)) := by
  obtain ⟨p, hp⟩ := elems_histInf ha
  exact ⟨p + 1, mem_s_Nall_of_elems (hwf (p + 1)) (hadm (p + 1)).1 (hadm (p + 1)).2.1 hp⟩

/-- The infinite abstract execution of RGA is in `A_strong`, with the list order "`a` precedes `b`
in `s(Nall)` of some prefix". -/
theorem strong_inf : Strong (histInf (protocol U n) f) (visInf f) := by
  refine ⟨fun a b => ∃ m, List.Sublist [a, b] (s (Nall (pre f m))), ?_, ?_, ?_, ?_, ?_⟩
  · rintro a b ⟨m, h⟩
    exact ⟨elems_pre_subset (mem_elems_of_mem_s (h.subset (by simp))),
      elems_pre_subset (mem_elems_of_mem_s (h.subset (by simp)))⟩
  · intro p r op w hp
    obtain ⟨lo', -, hc, -⟩ := strong (hwf (p + 1)) (hadm (p + 1))
    obtain ⟨ha, -, hcc⟩ := hc p r op w hp
    have hv : ∀ q, VisLe (visInf f) q p ↔ VisLe (visHB (pre f (p + 1))) q p := fun q => by
      unfold VisLe; rw [visInf_iff (show p < p + 1 by omega)]
    have hh : ∀ q, VisLe (visInf f) q p →
        histInf (protocol U n) f q = (protocol U n).hist (pre f (p + 1)) q := by
      intro q hq
      have : q ≤ p := by
        rcases hq with rfl | hq
        · exact le_rfl
        · exact (visInf_lt hq).le
      exact histInf_eq (by omega)
    refine ⟨fun a => ?_, ?_, hcc⟩
    · rw [insVis_congr hv hh, delVis_congr hv hh]; exact ha a
    · exact List.pairwise_iff_forall_sublist.2 fun h => ⟨p + 1, h.trans (resp_sublist hwf hadm hp)⟩
  · rintro a b c ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    exact ⟨max m₁ m₂, pair_sublist_trans (s_nodup (isTITree_Nall_pre hwf hadm _))
      (h₁.trans (s_Nall_sublist hwf hadm (le_max_left _ _)))
      (h₂.trans (s_Nall_sublist hwf hadm (le_max_right _ _)))⟩
  · rintro a ⟨m, h⟩
    exact List.nodup_iff_sublist.1 (s_nodup (isTITree_Nall_pre hwf hadm m)) a h
  · intro a ha b hb hab
    obtain ⟨m₁, h₁⟩ := mem_s_of_elems hwf hadm ha
    obtain ⟨m₂, h₂⟩ := mem_s_of_elems hwf hadm hb
    rcases pair_sublist_total ((s_Nall_sublist hwf hadm (le_max_left m₁ m₂)).subset h₁)
      ((s_Nall_sublist hwf hadm (le_max_right m₁ m₂)).subset h₂) hab with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr ⟨_, h⟩

end Safety

/-! ### Theorem 1 (liveness): eventual visibility -/

section Liveness

/-- Only a send empties the send buffer. -/
theorem step_buf_isSome {c : Cfg (Fin n) (St U) (Msg U)} {a : Act (Fin n) (LOp U)} {r : Fin n}
    (h : (c.st r).2.isSome) (ha : a ≠ .send r) : (((protocol U n).step c a).st r).2.isSome := by
  cases a with
  | doOp r' op =>
    simp only [Protocol.step]
    rcases eq_or_ne r r' with rfl | hr
    · simp only [Function.update_self]
      cases op <;> simp [protocol, h]
    · simp [Function.update_of_ne hr, h]
  | send r' =>
    have hr : r ≠ r' := fun e => ha (e ▸ rfl)
    simp [Protocol.step, Function.update_of_ne hr, h]
  | recv r' src =>
    simp only [Protocol.step]
    rcases c.sent[src]?.join with _ | m
    · exact h
    · rcases eq_or_ne r r' with rfl | hr
      · simp [protocol, h]
      · simp [Function.update_of_ne hr, h]

variable {f : ℕ → Act (Fin n) (LOp U)}

/-- The send buffer of `r` stays non-empty until `r` sends. -/
theorem buf_persist {p m : ℕ} {r : Fin n} (hpm : p ≤ m)
    (h0 : (((protocol U n).exec (pre f (p + 1))).st r).2.isSome)
    (hno : ∀ j, p < j → j ≤ m → f j ≠ .send r) :
    (((protocol U n).exec (pre f (m + 1))).st r).2.isSome := by
  induction m, hpm using Nat.le_induction with
  | base => exact h0
  | succ m hpm ih =>
    rw [pre_succ, Protocol.exec_concat]
    exact step_buf_isSome (ih fun j h1 h2 => hno j h1 (by omega)) (hno _ (by omega) le_rfl)

/-- **Theorem 1** (liveness part): in a sufficiently connected infinite well-formed execution of
`R_rga^n`, the abstract execution with visibility = happens-before satisfies eventual visibility
(Definition 9). After an update by `r`, the send buffer of `r` is non-empty until `r` sends; by
eventual transmission `r` sends later, by eventual delivery every other replica receives that
message, and every event after all these receives is happens-after the update. -/
theorem theorem1_eventualVisibility (f : ℕ → Act (Fin n) (LOp U))
    (hwf : InfWF (protocol U n) f) (hsc : SufficientlyConnected (protocol U n) f) :
    EventualVisibility (histInf (protocol U n) f) (visInf f) := by
  intro e r op w he hop
  have hα := (hist_eq_some (P := protocol U n) he).1
  have hfe : f e = .doOp r op := by
    rw [pre_getElem?_of_lt f (by omega)] at hα; exact Option.some.inj hα
  have h0 : (((protocol U n).exec (pre f (e + 1))).st r).2.isSome := by
    have := (pending_of_update hα hop).2
    rwa [pre_take, min_self] at this
  -- `r` sends after `e`
  obtain ⟨s, hes, hs⟩ : ∃ s, e < s ∧ f s = .send r := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hsend⟩ := hsc.1 r (fun N => ⟨max N e, le_max_left _ _,
      buf_persist (le_max_right _ _) h0 fun j hj _ => hcon j hj⟩) (e + 1)
    exact hcon m (by omega) hsend
  -- every other replica receives that message
  have hdel : ∀ r', ∃ q, r' ≠ r → f q = .recv r' s := fun r' => by
    by_cases h : r' = r
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨q, hq⟩ := hsc.2 s r hs r' h; exact ⟨q, fun _ => hq⟩
  choose g hg using hdel
  refine (Set.finite_Iio (Finset.univ.sup g + s + 1)).subset ?_
  rintro j ⟨hj, hnv⟩
  by_contra hjN
  simp only [Set.mem_Iio, not_lt] at hjN
  apply hnv
  have hjd : IsDo (pre f (j + 1)) j := (hist_isSome_iff (P := protocol U n)).1 hj
  obtain ⟨r'', op'', hj'⟩ := hjd
  have get : ∀ {i a}, i ≤ j → f i = a → (pre f (j + 1))[i]? = some a := fun hi h => by
    rw [pre_getElem?_of_lt f (by omega), h]
  refine ⟨?_, ⟨r, op, get (by omega) hfe⟩, ⟨r'', op'', hj'⟩⟩
  have hes' : HB (pre f (j + 1)) e s := HB.of_rep hes (get (by omega) hfe) (get (by omega) hs) rfl
  by_cases hr : r'' = r
  · subst hr
    exact HB.of_rep (by omega) (get (by omega) hfe) hj' rfl
  · have hq := hg r'' hr
    have hqs := recv_src_lt hwf hq
    have hqN : g r'' ≤ Finset.univ.sup g := Finset.le_sup (Finset.mem_univ r'')
    exact (hes'.trans (HB.of_recv hqs (get (by omega) hs) (get (by omega) hq))).trans
      (HB.of_rep (by omega) (get (by omega) hq) hj' rfl)

/-- **Theorem 1** for infinite executions: `R_rga^n` satisfies the strong list specification and,
when the network is sufficiently connected (Definition 1), guarantees eventual visibility. -/
theorem theorem1_inf (f : ℕ → Act (Fin n) (LOp U)) (hwf : InfWF (protocol U n) f)
    (hadm : ∀ m, Adm U n (pre f m)) (hsc : SufficientlyConnected (protocol U n) f) :
    AbsWF (histInf (protocol U n) f) (visInf f) ∧ Strong (histInf (protocol U n) f) (visInf f) ∧
      EventualVisibility (histInf (protocol U n) f) (visInf f) :=
  ⟨absWF_inf, strong_inf hwf hadm, theorem1_eventualVisibility f hwf hsc⟩

/-! Non-vacuity: a sufficiently connected execution with an update. -/

/-- Replica `0` inserts `0` and sends, replica `1` receives the message and reads forever. -/
def connectedExec : ℕ → Act (Fin 2) (LOp ℕ)
  | 0 => .doOp 0 (.ins 0 0)
  | 1 => .send 0
  | 2 => .recv 1 1
  | _ + 3 => .doOp 1 .read

theorem step_buf_eq {c : Cfg (Fin n) (St U) (Msg U)} {a : Act (Fin n) (LOp U)} (r : Fin n)
    (ha : (∃ r' src, a = .recv r' src) ∨ ∃ r', a = .doOp r' .read) :
    (((protocol U n).step c a).st r).2 = (c.st r).2 := by
  rcases ha with ⟨r', src, rfl⟩ | ⟨r', rfl⟩
  · simp only [Protocol.step]
    rcases c.sent[src]?.join with _ | m
    · rfl
    · rcases eq_or_ne r r' with rfl | hr
      · simp [protocol]
      · simp [Function.update_of_ne hr]
  · simp only [Protocol.step]
    rcases eq_or_ne r r' with rfl | hr
    · simp [protocol]
    · simp [Function.update_of_ne hr]

theorem connectedExec_buf {m : ℕ} (hm : 2 ≤ m) (r : Fin 2) :
    (((protocol ℕ 2).exec (pre connectedExec m)).st r).2 = none := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [pre_succ, Protocol.exec_concat]
    fin_cases r <;> simp [connectedExec, Protocol.step, pre, Protocol.exec, Protocol.init₀, protocol]
  | succ m hm ih =>
    rw [pre_succ, Protocol.exec_concat, step_buf_eq r, ih]
    rcases m with _ | _ | _ | m
    · omega
    · omega
    · exact Or.inl ⟨1, 1, rfl⟩
    · exact Or.inr ⟨1, rfl⟩

theorem connectedExec_wf : InfWF (protocol ℕ 2) connectedExec := by
  intro m p hp
  have hp' : p < m := by simpa using hp
  have e : (pre connectedExec m)[p] = connectedExec p := by simp [pre]
  rw [e, pre_take, min_eq_left hp'.le]
  rcases p with _ | _ | _ | p
  · trivial
  · simp [connectedExec, Enabled, pre, Protocol.exec, Protocol.step, Protocol.init₀, protocol]
  · exact ⟨by omega, 0, by rw [pre_getElem?_of_lt _ (by omega)]; rfl⟩
  · trivial

theorem connectedExec_adm (m : ℕ) : Adm ℕ 2 (pre connectedExec m) := by
  have get : ∀ {p a}, (pre connectedExec m)[p]? = some a → connectedExec p = a := fun h => by
    rw [pre_getElem?] at h; split_ifs at h; exact Option.some.inj h
  refine ⟨?_, ?_, ?_⟩
  · rintro s s' r q ⟨r₁, h₁⟩ ⟨r₂, h₂⟩ hss
    have e1 := get h₁
    have e2 := get h₂
    have : s = s' := by
      rcases s with _ | _ | _ | s <;> rcases s' with _ | _ | _ | s' <;> simp [connectedExec] at e1 e2 ⊢
    exact absurd (this ▸ hss) (HB.irrefl _)
  · intro p q r r' a k k' hp hq
    have h1 := get hp
    have h2 := get hq
    rcases p with _ | _ | _ | p <;> rcases q with _ | _ | _ | q <;> simp_all [connectedExec]
  · intro p r a hp
    have := get hp
    rcases p with _ | _ | _ | p <;> simp [connectedExec] at this

theorem connectedExec_sufficientlyConnected :
    SufficientlyConnected (protocol ℕ 2) connectedExec := by
  refine ⟨fun r h => ?_, fun s r hs r' hr' => ?_⟩
  · obtain ⟨m, hm, hp⟩ := h 1
    rw [connectedExec_buf (by omega)] at hp
    cases hp
  · rcases s with _ | _ | _ | s <;> simp [connectedExec] at hs
    subst hs
    refine ⟨2, ?_⟩
    have : r' = 1 := by fin_cases r' <;> simp_all
    subst this; rfl

/-- The hypotheses of `theorem1_inf` are satisfiable by an execution with an update. -/
example : InfWF (protocol ℕ 2) connectedExec ∧ (∀ m, Adm ℕ 2 (pre connectedExec m)) ∧
    SufficientlyConnected (protocol ℕ 2) connectedExec :=
  ⟨connectedExec_wf, connectedExec_adm, connectedExec_sufficientlyConnected⟩

end Liveness

/-! ### Definition 10 needs the connectivity assumption -/

section Counterexample

/-- Replica `0` inserts `0` at position `0` and never sends; replica `1` reads forever. -/
def readerExec : ℕ → Act (Fin 2) (LOp ℕ)
  | 0 => .doOp 0 (.ins 0 0)
  | _ + 1 => .doOp 1 .read

theorem readerExec_wf : InfWF (protocol ℕ 2) readerExec := by
  intro m p hp
  simp only [pre, List.getElem_map, List.getElem_range]
  cases p <;> trivial

theorem readerExec_adm (m : ℕ) : Adm ℕ 2 (pre readerExec m) := by
  have get : ∀ {p a}, (pre readerExec m)[p]? = some a → readerExec p = a := fun h => by
    rw [pre_getElem?] at h; split_ifs at h; exact Option.some.inj h
  refine ⟨?_, ?_, ?_⟩
  · rintro s s' r q ⟨r₁, h₁⟩
    have := get h₁
    cases s <;> simp [readerExec] at this
  · intro p q r r' a k k' hp hq
    have h1 := get hp
    have h2 := get hq
    cases p <;> cases q <;> simp_all [readerExec]
  · intro p r a hp
    have := get hp
    cases p <;> simp [readerExec] at this

/-- Replica `1` never leaves its initial state. -/
theorem readerExec_st_one (m : ℕ) :
    ((protocol ℕ 2).exec (pre readerExec m)).st 1 = (([], []), none) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pre_succ, Protocol.exec_concat]
    cases m with
    | zero => simp [readerExec, Protocol.step, ih]
    | succ m =>
      simp only [readerExec, Protocol.step, Function.update_self]
      rw [ih]; rfl

theorem readerExec_hist_read (j : ℕ) :
    histInf (protocol ℕ 2) readerExec (j + 1) = some (1, .read, []) := by
  unfold histInf
  rw [hist_of_getElem? (pre_getElem?_of_lt readerExec (show j + 1 < j + 1 + 1 by omega))]
  simp only [Protocol.stBefore, pre_take, min_eq_left (show j + 1 ≤ j + 1 + 1 by omega),
    readerExec_st_one]
  simp [protocol, visible]

/-- **Definition 10 needs Definition 1.** Definition 10, as literally stated, requires *every*
execution with causal broadcast to comply with an abstract execution in `A_weak` (a fortiori
`A_strong`) satisfying eventual visibility. This fails for RGA (and for every protocol that
buffers updates): in `readerExec` replica `0` inserts `0` and never sends, replica `1` reads
forever. The execution is well formed, satisfies causal broadcast and the user assumptions, but
the network is not sufficiently connected, and no visibility relation whatsoever makes its history
satisfy `A_weak` and eventual visibility: all reads of replica `1` return `[]`, so by (1a) the
insert is visible to none of them. -/
theorem def10_needs_connectivity :
    ∃ f : ℕ → Act (Fin 2) (LOp ℕ), InfWF (protocol ℕ 2) f ∧ (∀ m, Adm ℕ 2 (pre f m)) ∧
      ¬ SufficientlyConnected (protocol ℕ 2) f ∧
      ¬ ∃ vis, Weak (histInf (protocol ℕ 2) f) vis ∧
        EventualVisibility (histInf (protocol ℕ 2) f) vis := by
  refine ⟨readerExec, readerExec_wf, readerExec_adm, ?_, ?_⟩
  · rintro ⟨htr, -⟩
    have h0 : (((protocol ℕ 2).exec (pre readerExec (0 + 1))).st 0).2.isSome := by
      have := (pending_of_update (α := pre readerExec 1) (p := 0) (r := 0) (op := .ins 0 0)
        (pre_getElem?_of_lt readerExec (by omega)) (by simp)).2
      simpa [pre_take] using this
    obtain ⟨m, -, hm⟩ := htr 0 (fun N => ⟨N, le_rfl,
      buf_persist (Nat.zero_le N) h0 fun j hj _ => by
        obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp [readerExec]⟩) 0
    cases m <;> simp [readerExec] at hm
  · rintro ⟨vis, ⟨lo, -, hc, -⟩, hev⟩
    have h0 := hist_of_getElem? (P := protocol ℕ 2)
      (pre_getElem?_of_lt readerExec (show 0 < 0 + 1 by omega))
    obtain ⟨B, hB⟩ := (hev 0 0 (.ins 0 0) _ h0 (by simp)).bddAbove
    have hv : vis 0 (B + 1) := by
      by_contra hv
      have := hB ⟨by simp [readerExec_hist_read B], hv⟩
      omega
    have := ((hc (B + 1) 1 .read [] (readerExec_hist_read B)).1 0).2
    refine absurd (this ⟨⟨0, 0, 0, _, Or.inr hv, h0⟩, ?_⟩) (by simp)
    rintro ⟨q, r, w, -, hq⟩
    have := (hist_eq_some (P := protocol ℕ 2) hq).1
    rw [pre_getElem?_of_lt readerExec (by omega)] at this
    cases q <;> simp [readerExec] at this

end Counterexample

/-- **Theorem 1** (safety part) for infinite executions: for every infinite well-formed execution
of `R_rga^n` all of whose prefixes satisfy causal broadcast and the user assumptions, the abstract
execution with visibility = happens-before is causal and belongs to `A_strong`. -/
theorem theorem1_strong_inf (f : ℕ → Act (Fin n) (LOp U)) (hwf : InfWF (protocol U n) f)
    (hadm : ∀ m, Adm U n (pre f m)) :
    AbsWF (histInf (protocol U n) f) (visInf f) ∧ Strong (histInf (protocol U n) f) (visInf f) :=
  ⟨absWF_inf, strong_inf hwf hadm⟩

end RGA

end Podc.CollaborativeListSpec
