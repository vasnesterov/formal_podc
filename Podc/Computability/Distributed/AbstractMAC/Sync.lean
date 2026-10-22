import Podc.Computability.Distributed.AbstractMAC.Basic

-- CSLib candidate: Cslib/Computability/Distributed/AbstractMAC/Sync.lean

/-!
# Synchronous rounds in the abstract MAC layer model

A *round with held set `H`* (`roundEvents G H c`): every node `u` that is broadcasting at the start
of the round and is not held (`H u = false`) has its message delivered to all its neighbours, and
then receives its acknowledgment. Each receiver gets its messages in the order of a fixed (but
arbitrary) linear order on messages, so the result depends only on the *multiset* of received
messages (`inbox`). Held nodes still receive messages, but their own broadcast neither progresses
nor is acknowledged. With `H = ∅` this is the *synchronous scheduler* of Newport (PODC 2014); with
some nodes held for `t` rounds it is his *semi-synchronous scheduler*.

* `round_eq`: the event-level round computes `roundLoc` (crash-free configurations with no pending
  deliveries).
* `syncSched H c₀`, `syncLoc H x₀`: the execution of rounds with hold sets `H j`, and its local
  recursion (`run_syncSched`).
* `syncSched_fair`, `syncSched_timely`: fairness when the holds stop, timeliness with bound `F`
  when there are no holds (round `j` at time `j F`).
* `syncLoc_comp`: simulation along a map `p : V' → V` that is a bijection from the neighbours of
  `v'` onto the non-held neighbours of `p v'` (covering / embedding arguments).
* `syncLoc_congr_of_walk`: after `r` rounds a node only depends on the initial data of the nodes
  within distance `r`.
-/

namespace Cslib.AbstractMAC

open Filter

variable {I M S V : Type*}

/-- A fixed (arbitrary) linear order on messages, used to order the messages of a round. -/
@[instance_reducible] noncomputable def msgOrder : LinearOrder M := by
  classical exact linearOrderOfSTO WellOrderingRel

attribute [local instance] msgOrder

section Round

variable [Fintype V] [DecidableEq V] (A : Algorithm I M S) (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- The messages that `v` receives in a round with held set `H` from local data `x`. -/
noncomputable def inbox (H : V → Bool) (x : V → Node M S) (v : V) : Multiset M :=
  (Finset.univ.filter fun u => G.Adj u v ∧ H u = false).val.filterMap fun u => (x u).cur

/-- The local data of `v` after a round with held set `H`. -/
noncomputable def roundLoc (H : V → Bool) (x : V → Node M S) (v : V) : Node M S :=
  if (x v).cur.isSome ∧ H v = false then
    A.ackNode (((inbox G H x v).sort (· ≤ ·)).foldl A.recvNode (x v))
  else ((inbox G H x v).sort (· ≤ ·)).foldl A.recvNode (x v)

/-- The message of `u` in `c`, in `WithBot M` (used to sort senders). -/
def msgKey (c : Config V M S) (u : V) : WithBot M := (c.loc u).cur

/-- The broadcasting non-held neighbours of `v`, sorted by their messages. -/
noncomputable def senders (c : Config V M S) (H : V → Bool) (v : V) : List V :=
  (Finset.univ.filter fun u => G.Adj u v ∧ H u = false ∧ (c.loc u).cur.isSome).toList.mergeSort
    fun a b => decide (msgKey c a ≤ msgKey c b)

/-- The events of a round with held set `H` starting in configuration `c`. -/
noncomputable def roundEvents (H : V → Bool) (c : Config V M S) : List (Event V) :=
  (Finset.univ.toList.flatMap fun v => (senders G c H v).map fun u => Event.recv u v) ++
    (Finset.univ.filter fun u => (c.loc u).cur.isSome ∧ H u = false).toList.map Event.ack

variable {G}

omit [DecidableEq V] in
lemma mem_senders {c : Config V M S} {H : V → Bool} {v u : V} :
    u ∈ senders G c H v ↔ G.Adj u v ∧ H u = false ∧ (c.loc u).cur.isSome := by
  simp [senders, List.mem_mergeSort]

omit [DecidableEq V] in
lemma senders_nodup (c : Config V M S) (H : V → Bool) (v : V) : (senders G c H v).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)

omit [DecidableEq V] in
lemma filterMap_senders (c : Config V M S) (H : V → Bool) (v : V) :
    (senders G c H v).filterMap (fun u => (c.loc u).cur) =
      (inbox G H (fun u => c.loc u) v).sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·))
  · intro a b _ _ h1 h2; exact le_antisymm h1 h2
  · refine List.Pairwise.filterMap _ ?_ (List.pairwise_mergeSort ?_ ?_ _)
    · intro a a' h b hb b' hb'
      have h' : msgKey c a ≤ msgKey c a' := of_decide_eq_true h
      rw [msgKey, msgKey, hb, hb'] at h'
      exact WithBot.coe_le_coe.1 h'
    · intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact h1.trans h2
    · intro a b; simpa using le_total _ _
  · exact Multiset.pairwise_sort _ _
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, inbox, ← Multiset.filterMap_coe, senders]
    have hf : (Finset.univ.filter fun u => G.Adj u v ∧ H u = false ∧ (c.loc u).cur.isSome) =
        (Finset.univ.filter fun u => G.Adj u v ∧ H u = false).filter
          fun u => (c.loc u).cur.isSome := by
      ext u; simp [and_assoc]
    rw [(Multiset.coe_eq_coe.2 (List.mergeSort_perm _ _)), Finset.coe_toList, hf,
      Finset.filter_val, Multiset.filterMap_filter]
    congr 1; funext u; split_ifs with h
    · rfl
    · exact (Option.not_isSome_iff_eq_none.1 h).symm

omit [Fintype V] [DecidableRel G.Adj] in
lemma step_recv {c : Config V M S} {u v : V} {m : M} (hcur : (c.loc u).cur = some m)
    (hu : u ∉ c.down) (hv : v ∉ c.down) (hadj : G.Adj u v) (hg : v ∉ c.got u) :
    step A G c (.recv u v) =
      { c with loc := Function.update c.loc v (A.recvNode (c.loc v) m)
               got := Function.update c.got u (insert v (c.got u)) } := by
  simp [step, hcur, hu, hadj, hg, hv]

omit [Fintype V] [DecidableRel G.Adj] in
lemma step_ack {c : Config V M S} {u : V} (hl : (c.loc u).cur.isSome) (hu : u ∉ c.down)
    (hg : ∀ v, G.Adj u v → v ∈ c.got u) :
    step A G c (.ack u) =
      { c with loc := Function.update c.loc u (A.ackNode (c.loc u))
               got := Function.update c.got u ∅
               acks := Function.update c.acks u (c.acks u + 1) } := by
  simp only [step]; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hl, hu, hg⟩)]

lemma Algorithm.foldl_recvNode_cur {x : Node M S} (h : x.cur.isSome) (l : List M) :
    (l.foldl A.recvNode x).cur = x.cur := by
  induction l generalizing x with
  | nil => rfl
  | cons m l ih =>
    simp only [List.foldl_cons]
    rw [ih (by rw [A.recvNode_cur_of_isSome h]; exact h), A.recvNode_cur_of_isSome h]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Delivering to `v` the messages of the senders `l`, in this order. -/
lemma foldl_recv (v : V) (l : List V) (hnd : l.Nodup) (d : Config V M S) (hdown : d.down = ∅)
    (hl : ∀ u ∈ l, G.Adj u v ∧ (d.loc u).cur.isSome ∧ v ∉ d.got u) :
    (l.map fun u => Event.recv u v).foldl (step A G) d =
      { d with
        loc := Function.update d.loc v
          ((l.filterMap fun u => (d.loc u).cur).foldl A.recvNode (d.loc v))
        got := fun u => if u ∈ l then insert v (d.got u) else d.got u } := by
  induction l generalizing d with
  | nil => simp
  | cons u l ih =>
    obtain ⟨hadj, hcur, hg⟩ := hl u (by simp)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hcur
    have huv : u ≠ v := hadj.ne
    simp only [List.map_cons, List.foldl_cons]
    rw [step_recv A hm (by simp [hdown]) (by simp [hdown]) hadj hg]
    have hnd' := (List.nodup_cons.1 hnd)
    rw [ih hnd'.2 _ (by exact hdown)]
    · have hlv : ∀ w ∈ l, w ≠ v := fun w hw => (hl w (by simp [hw])).1.ne
      ext1
      · simp only
        funext w
        by_cases hw : w = v
        · subst hw
          simp only [Function.update_self, List.filterMap_cons, hm, List.foldl_cons]
          congr 1
          refine List.filterMap_congr fun w hw' => ?_
          rw [Function.update_of_ne (hlv w hw')]
        · simp [Function.update_of_ne hw]
      · simp only
        funext w
        by_cases hwu : w = u
        · subst hwu; simp [hnd'.1]
        · simp only [Function.update_of_ne hwu, List.mem_cons, hwu, false_or]
      · rfl
      · rfl
    · intro w hw
      obtain ⟨h1, h2, h3⟩ := hl w (by simp [hw])
      have hwu : w ≠ u := fun h => hnd'.1 (h ▸ hw)
      refine ⟨h1, ?_, ?_⟩
      · simpa [Function.update_of_ne h1.ne] using h2
      · simpa [Function.update_of_ne hwu] using h3

/-- The delivery phase of a round, for the receivers in `R`. -/
lemma foldl_deliver (H : V → Bool) (c : Config V M S) (hdown : c.down = ∅)
    (hgot : ∀ u, c.got u = ∅) (R : List V) (hR : R.Nodup) :
    (R.flatMap fun v => (senders G c H v).map fun u => Event.recv u v).foldl (step A G) c =
      { c with
        loc := fun v => if v ∈ R then
          ((inbox G H (fun u => c.loc u) v).sort (· ≤ ·)).foldl A.recvNode (c.loc v) else c.loc v
        got := fun u => {w | w ∈ R ∧ G.Adj u w ∧ H u = false ∧ (c.loc u).cur.isSome} } := by
  induction R using List.reverseRecOn with
  | nil =>
    refine Config.ext rfl ?_ rfl rfl
    funext u; simp [hgot]
  | append_singleton R v ih =>
    have hnd := List.nodup_append.1 hR
    have hvR : v ∉ R := fun h => by simpa using hnd.2.2 v h v (by simp)
    rw [List.flatMap_append, List.foldl_append, ih hnd.1]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [foldl_recv A v _ (senders_nodup c H v) _ (by exact hdown)]
    · ext1
      · simp only
        funext w
        by_cases hw : w = v
        · subst hw
          simp only [Function.update_self, hvR, ite_false, List.mem_append, List.mem_singleton,
            or_true, ite_true]
          congr 1
          rw [← filterMap_senders]
          refine List.filterMap_congr fun u hu => ?_
          split_ifs
          · exact A.foldl_recvNode_cur ((mem_senders.1 hu).2.2) _
          · rfl
        · simp [hw]
      · simp only
        funext u
        ext w
        by_cases hu : u ∈ senders G c H v
        · have := mem_senders.1 hu
          simp only [hu, ite_true, Set.mem_insert_iff, Set.mem_ofPred_eq, List.mem_append,
            List.mem_singleton]
          constructor
          · rintro (rfl | ⟨h1, h2⟩)
            · exact ⟨Or.inr rfl, this.1, this.2.1, this.2.2⟩
            · exact ⟨Or.inl h1, h2⟩
          · rintro ⟨h1 | rfl, h2⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact Or.inl rfl
        · simp only [hu, ite_false, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
          · rintro ⟨h1 | rfl, h2⟩
            · exact ⟨h1, h2⟩
            · exact absurd (mem_senders.2 ⟨h2.1, h2.2.1, h2.2.2⟩) hu
      · rfl
      · rfl
    · intro u hu
      obtain ⟨h1, h2, h3⟩ := mem_senders.1 hu
      refine ⟨h1, ?_, ?_⟩
      · simp only
        split_ifs
        · rw [A.foldl_recvNode_cur h3]; exact h3
        · exact h3
      · simp [hvR]

omit [Fintype V] [DecidableRel G.Adj] in
/-- The acknowledgment phase. -/
lemma foldl_ack (K : List V) (hK : K.Nodup) (d : Config V M S)
    (hk : ∀ u ∈ K, (d.loc u).cur.isSome ∧ u ∉ d.down ∧ ∀ w, G.Adj u w → w ∈ d.got u) :
    (K.map Event.ack).foldl (step A G) d =
      { d with
        loc := fun u => if u ∈ K then A.ackNode (d.loc u) else d.loc u
        got := fun u => if u ∈ K then ∅ else d.got u
        acks := fun u => if u ∈ K then d.acks u + 1 else d.acks u } := by
  induction K generalizing d with
  | nil => simp
  | cons u K ih =>
    obtain ⟨h1, h2, h3⟩ := hk u (by simp)
    have hnd := List.nodup_cons.1 hK
    simp only [List.map_cons, List.foldl_cons]
    rw [step_ack A h1 h2 h3, ih hnd.2]
    · ext1 <;> simp only <;> funext w <;> by_cases hw : w = u
      all_goals first
        | (subst hw; simp [hnd.1])
        | simp [hw]
    · intro w hw
      have hwu : w ≠ u := fun h => hnd.1 (h ▸ hw)
      obtain ⟨g1, g2, g3⟩ := hk w (by simp [hw])
      exact ⟨by simpa [Function.update_of_ne hwu] using g1, g2,
        by simpa [Function.update_of_ne hwu] using g3⟩

/-- **A round, computed.** In a crash-free configuration without pending deliveries, the events of
a round with held set `H` produce `roundLoc`; afterwards there are again no pending deliveries,
and exactly the broadcasting non-held nodes are acknowledged. -/
theorem round_eq (H : V → Bool) (c : Config V M S) (hdown : c.down = ∅)
    (hgot : ∀ u, c.got u = ∅) :
    (roundEvents G H c).foldl (step A G) c =
      ⟨roundLoc A G H c.loc, fun _ => ∅, ∅,
        fun u => c.acks u + if (c.loc u).cur.isSome ∧ H u = false then 1 else 0⟩ := by
  rw [roundEvents, List.foldl_append, foldl_deliver A H c hdown hgot _ (Finset.nodup_toList _),
    foldl_ack A _ (Finset.nodup_toList _)]
  · ext1
    · funext v
      simp only [Finset.mem_toList, Finset.mem_univ, ite_true, Finset.mem_filter, true_and,
        roundLoc]
    · funext u
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h
      · rfl
      · ext w; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hw; exact h ⟨hw.2.2, hw.2.1⟩
    · simp [hdown]
    · funext u; simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs <;> simp
  · intro u hu
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    refine ⟨?_, by simp [hdown], fun w hw => ?_⟩
    · simp only [Finset.mem_toList, Finset.mem_univ, ite_true]
      rw [A.foldl_recvNode_cur hu.1]; exact hu.1
    · simp [hu.1, hu.2, hw]

end Round

/-! ### Executions made of rounds -/

section Sync

variable [Fintype V] [DecidableEq V] (A : Algorithm I M S) (G : SimpleGraph V)
  [DecidableRel G.Adj]

/-- The execution made of rounds with held sets `H j` (round `j` = block `j`). -/
noncomputable def syncSched (H : ℕ → V → Bool) (c₀ : Config V M S) : ℕ → List (Event V) :=
  stratSched A G (fun j c => roundEvents G (H j) c) c₀

/-- Local data after `j` rounds. -/
noncomputable def syncLoc (H : ℕ → V → Bool) (x₀ : V → Node M S) : ℕ → V → Node M S
  | 0 => x₀
  | j + 1 => roundLoc A G (H j) (syncLoc H x₀ j)

/-- Ack counters after `j` rounds. -/
noncomputable def syncAcks (H : ℕ → V → Bool) (x₀ : V → Node M S) (a₀ : V → ℕ) : ℕ → V → ℕ
  | 0 => a₀
  | j + 1 => fun u => syncAcks H x₀ a₀ j u +
      if (syncLoc A G H x₀ j u).cur.isSome ∧ H j u = false then 1 else 0

lemma run_syncSched (H : ℕ → V → Bool) (c₀ : Config V M S) (hdown : c₀.down = ∅)
    (hgot : ∀ u, c₀.got u = ∅) (j : ℕ) :
    run A G c₀ (syncSched A G H c₀) j =
      ⟨syncLoc A G H c₀.loc j, fun _ => ∅, ∅, syncAcks A G H c₀.loc c₀.acks j⟩ := by
  rw [syncSched, run_stratSched]
  induction j with
  | zero => refine Config.ext rfl (funext hgot) hdown rfl
  | succ j ih =>
    simp only [stratCfg]; rw [ih]
    exact (round_eq A (H j) _ rfl (fun _ => rfl)).trans rfl

variable {A G}

omit [DecidableEq V] in
lemma roundLoc_dec {H : V → Bool} {x : V → Node M S} {v : V} {b : Bool}
    (h : (x v).dec = some b) : (roundLoc A G H x v).dec = some b := by
  have hf : ∀ (l : List M) (y : Node M S), y.dec = some b → (l.foldl A.recvNode y).dec = some b := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons m l ih => exact fun y h => ih _ (A.recvNode_dec h m)
  unfold roundLoc
  split_ifs
  · exact A.ackNode_dec (hf _ _ h)
  · exact hf _ _ h

omit [DecidableEq V] in
/-- Decisions are kept along rounds. -/
lemma syncLoc_dec_mono {H : ℕ → V → Bool} {x₀ : V → Node M S} {v : V} {b : Bool} {i j : ℕ}
    (h : (syncLoc A G H x₀ i v).dec = some b) (hij : i ≤ j) :
    (syncLoc A G H x₀ j v).dec = some b := by
  induction hij with
  | refl => exact h
  | step _ ih => exact roundLoc_dec ih

/-- Rounds starting from an initial configuration are crash-free. -/
lemma syncSched_down (H : ℕ → V → Bool) (id : V → I) (inp : V → Bool) (j : ℕ) :
    (run A G (Config.init A id inp) (syncSched A G H (Config.init A id inp)) j).down = ∅ := by
  rw [run_syncSched A G H (Config.init A id inp) rfl (fun _ => rfl)]

lemma syncSched_loc (H : ℕ → V → Bool) (id : V → I) (inp : V → Bool) (j : ℕ) :
    (run A G (Config.init A id inp) (syncSched A G H (Config.init A id inp)) j).loc =
      syncLoc A G H (fun v => A.initNode (id v) (inp v)) j := by
  rw [run_syncSched A G H (Config.init A id inp) rfl (fun _ => rfl)]; rfl

/-- Rounds are fair once the holds stop. -/
theorem syncSched_fair (H : ℕ → V → Bool) (c₀ : Config V M S) (hdown : c₀.down = ∅)
    (hgot : ∀ u, c₀.got u = ∅) (t : ℕ) (ht : ∀ j ≥ t, ∀ u, H j u = false) :
    Fair A G c₀ (syncSched A G H c₀) := by
  intro u i hl
  by_cases hp : Prog A G c₀ (syncSched A G H c₀) u i (max i t)
  · exact ⟨_, le_max_left _ _, hp⟩
  · obtain ⟨hl', he⟩ := live_of_not_prog (le_max_left _ _) hl hp
    refine ⟨max i t + 1, by omega, Or.inl ?_⟩
    rw [← he]
    have hr := run_syncSched A G H c₀ hdown hgot
    rw [hr, hr] at *
    simp only [Config.Live] at hl'
    simp only [syncAcks, hl', ht _ (le_max_right _ _), and_self, ite_true]
    omega

/-- Rounds without holds are timely for any bound `F ≥ 0`, round `j` taking place at time
`(j + 1) F`. -/
theorem syncSched_timely (H : ℕ → V → Bool) (c₀ : Config V M S) (hdown : c₀.down = ∅)
    (hgot : ∀ u, c₀.got u = ∅) (hH : ∀ j u, H j u = false) {F : ℝ} (hF : 0 ≤ F) :
    Timely A G c₀ (syncSched A G H c₀) (fun i => i * F) F := by
  refine ⟨fun i j hij => by simp only; gcongr, by simp, fun u i hfr => ?_⟩
  refine ⟨i + 1, by omega, by push_cast; linarith, Or.inl ?_⟩
  have hl := hfr.live
  have hr := run_syncSched A G H c₀ hdown hgot
  rw [hr] at hl
  rw [hr, hr]
  simp only [Config.Live] at hl
  simp [syncAcks, hl, hH]

/-- Timely executions made of rounds without holds, with diverging time. -/
lemma tendsto_mul_const {F : ℝ} (hF : 0 < F) :
    Tendsto (fun i : ℕ => (i : ℝ) * F) atTop atTop :=
  Tendsto.atTop_mul_const hF tendsto_natCast_atTop_atTop

end Sync

/-! ### Simulation and locality -/

section Sim

variable [DecidableEq V] [Fintype V] {V' : Type*} [DecidableEq V'] [Fintype V']
  (A : Algorithm I M S) {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph V'}
  [DecidableRel G'.Adj]

omit [DecidableEq V] [DecidableEq V'] in
/-- **Simulation.** If `p` maps the neighbours of every `v'` bijectively (as a multiset) onto the
non-held neighbours of `p v'`, held sets correspond, and the initial data agree along `p`, then
the rounds agree along `p` for `t` rounds. -/
theorem syncLoc_comp (p : V' → V) (H : ℕ → V → Bool) (H' : ℕ → V' → Bool)
    (x₀ : V → Node M S) (x₀' : V' → Node M S) (t : ℕ)
    (hnb : ∀ j < t, ∀ v', (Finset.univ.filter fun u => G.Adj u (p v') ∧ H j u = false).val =
      (Finset.univ.filter fun u' => G'.Adj u' v' ∧ H' j u' = false).val.map p)
    (hH : ∀ j < t, ∀ v', H j (p v') = H' j v') (h₀ : ∀ v', x₀ (p v') = x₀' v') :
    ∀ r ≤ t, ∀ v', syncLoc A G H x₀ r (p v') = syncLoc A G' H' x₀' r v' := by
  intro r hr
  induction r with
  | zero => exact h₀
  | succ r ih =>
    intro v'
    have ih' := ih (by omega)
    have hin : inbox G (H r) (syncLoc A G H x₀ r) (p v') =
        inbox G' (H' r) (syncLoc A G' H' x₀' r) v' := by
      rw [inbox, hnb r (by omega), Multiset.filterMap_map, inbox]
      congr 1; funext u'; simp [ih']
    simp only [syncLoc, roundLoc, hin, ih', hH r (by omega)]

omit [DecidableEq V] in
/-- **Locality.** After `r` rounds (with the same holds), a node only depends on the initial data
of the nodes it reaches by walks of length at most `r`. -/
theorem syncLoc_congr_of_walk (H : ℕ → V → Bool) (x₀ x₀' : V → Node M S) :
    ∀ r v, (∀ w, ∀ q : G.Walk v w, q.length ≤ r → x₀ w = x₀' w) →
      syncLoc A G H x₀ r v = syncLoc A G H x₀' r v := by
  intro r
  induction r with
  | zero => intro v h; exact h v .nil le_rfl
  | succ r ih =>
    intro v h
    have hv := ih v fun w q hq => h w q (by omega)
    have hin : inbox G (H r) (syncLoc A G H x₀ r) v = inbox G (H r) (syncLoc A G H x₀' r) v := by
      rw [inbox, inbox, ← Finset.coe_toList, Multiset.filterMap_coe, Multiset.filterMap_coe]
      congr 1
      refine List.filterMap_congr fun u hu => ?_
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [ih u fun w q hq => h w (.cons hu.1.symm q) (by simp; omega)]
    simp only [syncLoc, roundLoc, hin, hv]

end Sim

end Cslib.AbstractMAC
