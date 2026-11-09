/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Send
import Papers.PODC2019.ReconfigurableCommit.Hist
import Papers.PODC2019.ReconfigurableCommit.Erase
import Papers.PODC2019.ReconfigurableCommit.Buf
import Papers.PODC2019.ReconfigurableCommit.Consequences

/-!
# Preservation of the invariant: simple steps

`certify`, `retry`, `decide`, and the delivery of `PREPARE_ACK`, `ACCEPT_ACK`, `PROBE_ACK` and of a
`PREPARE` for an already prepared transaction.
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

variable {Pa : Params T Pl S P} {st st' : State T Pl S P}

theorem certified_eq_false {h : History T Pl} {t : T} (hc : certified h t = false) (l : Pl) :
    Event.certify t l ∉ h := by
  intro hm
  unfold certified at hc
  rw [List.any_eq_false] at hc
  exact absurd (by simp) (hc _ hm)

theorem decided_eq_false {h : History T Pl} {t : T} (hc : decided h t = false) (d : Dec) :
    Event.decide t d ∉ h := by
  intro hm
  unfold decided at hc
  rw [List.any_eq_false] at hc
  exact absurd (by simp) (hc _ hm)

theorem decided_eq_true {h : History T Pl} {t : T} (hc : decided h t = true) :
    ∃ d, Event.decide t d ∈ h := by
  unfold decided at hc
  rw [List.any_eq_true] at hc
  obtain ⟨x, hx, h⟩ := hc
  rcases x with ⟨t', l⟩ | ⟨t', d⟩
  · simp at h
  · simp at h; subst h; exact ⟨d, hx⟩

theorem Inv.step_certify (hI : Inv Pa st) {p : P} {t : T} {l : Pl}
    (h : step Pa st (.certify p t l) = some st') : Inv Pa st' := by
  simp only [step] at h
  split_ifs at h with hc
  cases h
  have hI' := hI.addEvent (.certify t l) (fun t' l' he => by
      cases he; exact ⟨hc.2, certified_eq_false hc.1⟩)
    (fun t' d he => by cases he)
  refine hI'.send_benign p _ fun b m hm => ?_
  split_ifs at hm with hb
  cases hm
  exact ⟨hb.1, l, by simp, Or.inr rfl⟩

theorem Inv.step_retry (hI : Inv Pa st) {p : P} {k : ℕ}
    (h : step Pa st (.retry p k) = some st') : Inv Pa st' := by
  simp only [step] at h
  split at h
  · rename_i t l d hent
    split_ifs at h with hph
    cases h
    refine hI.send_benign p _ fun b m hm => ?_
    split_ifs at hm with hb
    cases hm
    obtain ⟨o, ho⟩ := hI.loc_elog p k _ hent
    obtain ⟨-, l₀, hl₀, -⟩ := hI.elog_txn _ _ _ _ _ _ _ ho
    exact ⟨hb.1, l₀, hl₀, Or.inl rfl⟩
  · cases h

/-- Delivering message `m` (the `i`-th of channel `src → dst`) is running its handler on the state
with the message removed. -/
theorem step_deliver {src dst : P} {i : ℕ} (h : step Pa st (.deliver src dst i) = some st') :
    ∃ m, (st.net src dst)[i]? = some m ∧ handle Pa (st.erase src dst i) src dst m = some st' := by
  simp only [step] at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

theorem Inv.deliver_prepareAck (hI : Inv Pa st) {src dst : P} {e : ℕ} {s : S} {k : ℕ} {t : T}
    {l : Pl} {d : Dec} (hm : Msg.prepareAck e s k t l d ∈ st.sent src dst)
    (h : handle Pa st src dst (.prepareAck e s k t l d) = some st') : Inv Pa st' := by
  simp only [handle] at h
  split_ifs at h with he
  cases h
  refine hI.send_benign dst _ fun b m hm => ?_
  split_ifs at hm with hb
  cases hm
  obtain ⟨o, ho⟩ := hI.m_prepareAck _ _ _ _ _ _ _ _ hm
  have hview := hI.loc_view dst s
  rw [he] at hview
  have hhome := (hI.cfg_wf _ _ _ hview).2.1 b (Finset.mem_sdiff.1 hb).1
  exact ⟨o, by rw [hhome]; exact ho⟩

theorem Inv.deliver_acceptAck (hI : Inv Pa st) {src dst : P} {s : S} {e k : ℕ} {t : T} {d : Dec}
    (hm : Msg.acceptAck s e k t d ∈ st.sent src dst)
    (h : handle Pa st src dst (.acceptAck s e k t d) = some st') : Inv Pa st' := by
  simp only [handle] at h
  cases h
  have := State.setLoc_eq_setBuf st dst ((src, s, e, k, t, d) :: (st.loc dst).acceptAcks)
    (st.loc dst).probeAcks
  simp only at this
  rw [this]
  refine hI.setBuf dst _ _ (fun q s' e' k' t' d' hq => ?_) (hI.loc_probeAcks dst)
  rcases List.mem_cons.1 hq with hq | hq
  · simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hq
    exact hm
  · exact hI.loc_acceptAcks dst q s' e' k' t' d' hq

theorem Inv.deliver_probeAck (hI : Inv Pa st) {src dst : P} {b : Bool} {E : ℕ} {s : S}
    (hm : Msg.probeAck b E s ∈ st.sent src dst)
    (h : handle Pa st src dst (.probeAck b E s) = some st') : Inv Pa st' := by
  simp only [handle] at h
  cases h
  have := State.setLoc_eq_setBuf st dst (st.loc dst).acceptAcks
    ((src, b, E, s) :: (st.loc dst).probeAcks)
  simp only at this
  rw [this]
  refine hI.setBuf dst _ _ (hI.loc_acceptAcks dst) (fun q b' E' s' hq => ?_)
  rcases List.mem_cons.1 hq with hq | hq
  · simp only [Prod.mk.injEq] at hq
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
    exact hm
  · exact hI.loc_probeAcks dst q b' E' s' hq

omit [DecidableEq Pl] [DecidableEq S] [DecidableEq P] [Fintype S] in
theorem findSlot_spec {a : Arrays T Pl} {t : T} {k : ℕ} (h : a.findSlot t = some k) :
    (a.ent k).map (·.1) = some t := by
  unfold Arrays.findSlot at h
  have := List.find?_some h
  simpa using this

omit [DecidableEq Pl] [DecidableEq S] [DecidableEq P] [Fintype S] in
theorem findSlot_none {a : Arrays T Pl} {t : T} (h : a.findSlot t = none) (k : ℕ)
    (hk : k ≤ a.len) : (a.ent k).map (·.1) ≠ some t := by
  unfold Arrays.findSlot at h
  rw [List.find?_eq_none] at h
  have := h k (List.mem_range.2 (by omega))
  simpa using this

theorem Inv.deliver_prepare_old (hI : Inv Pa st) {src dst : P} {t : T} {lo : Option Pl} {k : ℕ}
    (hk : (st.loc dst).arr.findSlot t = some k)
    (h : handle Pa st src dst (.prepare t lo) = some st') : Inv Pa st' := by
  simp only [handle, hk] at h
  split_ifs at h with hl
  split at h
  · rename_i t' l' d' hent
    cases h
    refine hI.send_benign dst _ fun b m hm => ?_
    split_ifs at hm with hb
    cases hm
    have := findSlot_spec hk
    rw [hent] at this
    simp only [Option.map_some, Option.some.injEq] at this
    subst this
    exact hI.loc_elog dst k _ hent
  · cases h

/-- Accepted entries from the buffered acknowledgements of a coordinator (line 26). -/
theorem Inv.accL_of_acks (hI : Inv Pa st) {p : P} {s : S} {k : ℕ} {t : T} {d : Dec}
    (h : ∀ r ∈ (st.loc p).members s \ {(st.loc p).leader s},
      (r, s, (st.loc p).epoch s, k, t, d) ∈ (st.loc p).acceptAcks) :
    ∃ v, AccL st s ((st.loc p).epoch s) k v ∧ v.1.1 = t ∧ v.1.2.2 = d := by
  have hview := hI.loc_view p s
  obtain ⟨hlm, -, hcard⟩ := hI.cfg_wf _ _ _ hview
  simp only at hlm hcard
  obtain ⟨r, hr, hrl⟩ := Finset.exists_mem_ne hcard ((st.loc p).leader s)
  have hrF : r ∈ (st.loc p).members s \ {(st.loc p).leader s} := by simp [hr, hrl]
  obtain ⟨-, ⟨l, o, ho⟩, -⟩ := hI.m_acceptAck _ _ _ _ _ _ _ (hI.loc_acceptAcks _ _ _ _ _ _ _ (h r hrF))
  refine ⟨((t, l, d), o), ⟨ho, _, hview, fun q hq => ⟨p, hI.loc_acceptAcks _ _ _ _ _ _ _ (h q hq)⟩⟩,
    rfl, rfl⟩

theorem Inv.step_decide (hI : Inv Pa st) (hsh : ∀ t, (Pa.σ.shards t).Nonempty) {p : P} {t : T}
    {ks : S → ℕ} {ds : S → Dec} (h : step Pa st (.decide p t ks ds) = some st') : Inv Pa st' := by
  simp only [step] at h
  split at h
  swap
  · cases h
  rename_i hacks
  cases h
  have hacc : ∀ s ∈ Pa.σ.shards t, ∃ v, AccL st s ((st.loc p).epoch s) (ks s) v ∧ v.1.1 = t ∧
      v.1.2.2 = ds s := fun s hs => hI.accL_of_acks (hacks s hs)
  classical
  let vs : S → Entry T Pl × ℕ := fun s =>
    if hs : s ∈ Pa.σ.shards t then (hacc s hs).choose else ((t, Pa.σ.eps, .commit), 0)
  have hvs : ∀ s ∈ Pa.σ.shards t, AccL st s ((st.loc p).epoch s) (ks s) (vs s) ∧ (vs s).1.1 = t ∧
      (vs s).1.2.2 = ds s := fun s hs => by
    simp only [vs, dif_pos hs]; exact (hacc s hs).choose_spec
  have hdec : Decided Pa st t (meetOver (Pa.σ.shards t) ds) := by
    refine ⟨fun s => (st.loc p).epoch s, ks, vs, fun s hs => ⟨(hvs s hs).1, (hvs s hs).2.1⟩, ?_⟩
    unfold meetOver
    congr 1
    apply propext
    constructor
    · intro h s hs
      show (vs s).1.2.2 = _
      rw [(hvs s hs).2.2]; exact h s hs
    · intro h s hs
      have := h s hs
      simp only at this
      rw [(hvs s hs).2.2] at this; exact this
  obtain ⟨s₀, hs₀⟩ := hsh t
  obtain ⟨-, l₀, hl₀, -⟩ := hI.elog_txn _ _ _ _ _ _ _ (((hvs s₀ hs₀).2.1 ▸ (hvs s₀ hs₀).1.1 :
    st.elog s₀ ((st.loc p).epoch s₀) (ks s₀) = some (((t, (vs s₀).1.2.1, (vs s₀).1.2.2)), (vs s₀).2)))
  -- the history after the step contains `decide t (meetOver ..)`
  have key : ∀ st₁ : State T Pl S P, Inv Pa st₁ → st₁.sent = st.sent → st₁.elog = st.elog →
      st₁.cs = st.cs → st₁.loc = st.loc →
      Event.decide t (meetOver (Pa.σ.shards t) ds) ∈ st₁.hist →
      Inv Pa (st₁.send p fun b => if Pa.home b ∈ Pa.σ.shards t ∧ b ∈ (st.loc p).members (Pa.home b)
        then some (.decision ((st.loc p).epoch (Pa.home b)) (ks (Pa.home b))
          (meetOver (Pa.σ.shards t) ds)) else none) := by
    intro st₁ hI₁ h1 h2 h3 h4 hmem
    refine hI₁.send_benign p _ fun b m hm => ?_
    split_ifs at hm with hb
    cases hm
    refine ⟨vs (Pa.home b), ?_, by rw [(hvs _ hb.1).2.1]; exact hmem⟩
    have := (hvs _ hb.1).1
    unfold AccL Acked cfg at this ⊢
    rw [h1, h2, h3]
    exact this
  split_ifs with hd
  · obtain ⟨d', hd'⟩ := decided_eq_true hd
    have := hI.decided_unique (hI.hist_decide t d' hd') hdec
    subst this
    exact key st hI rfl rfl rfl rfl hd'
  · refine key _ (hI.addEvent _ (fun _ _ he => by cases he) fun t' d he => ?_) rfl rfl rfl rfl
      (by simp)
    cases he
    refine ⟨hdec, decided_eq_false (by simpa using hd), ⟨l₀, hl₀⟩, fun s hs => ⟨_, _, vs s, (hvs s hs).1,
      (hvs s hs).2.1, fun J₁ J₂ hl hv => hI.vinfo_len _ _ _ _ _ _ hv⟩⟩

end Podc.ReconfigurableCommit
