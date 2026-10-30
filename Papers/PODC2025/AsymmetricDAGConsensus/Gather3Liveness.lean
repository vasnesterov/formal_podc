import Papers.PODC2025.AsymmetricDAGConsensus.Gather3

/-!
# Algorithm 3: liveness (Lemmas 3.3, 3.6, termination) and the main theorem (Lemma 3.8)

In a weakly fair execution (`Exec.Fair`: messages between correct processes are delivered, a
correct process whose guard for a message holds forever eventually sends it) with the
reliable-broadcast guarantees `RBC` for a nonempty guild `G`:

* `lemma_3_3`: some guild member sends `DISTRIBUTET`;
* `lemma_3_6`: every guild member sends `DISTRIBUTET`;
* `termination`: every guild member ag-delivers;
* `lemma_3_8`: Algorithm 3 is an asymmetric gather (termination, common core, validity,
  agreement), for every nonempty guild, in particular the maximal guild (`lemma_3_8_maxGuild`).

Contents of messages depend on the state (`DISTRIBUTES Sᵢ`, `DISTRIBUTET Tᵢ`); weak fairness is
per message, so we use that the arb-delivered and acknowledged sets of a guild member
stabilize: by consistency of the reliable broadcast they contain at most one pair per sender.
-/

namespace Podc.AsymmetricDAGConsensus

open Cslib.Byzantine.AsyncBroadcast Cslib.AsymmetricQuorum

variable {P V : Type*}

/-- A monotone family of sets with finite union is eventually constant. -/
theorem eventually_const_of_mono {α : Type*} (f : ℕ → Set α)
    (hmono : ∀ i j, i ≤ j → f i ⊆ f j) (hfin : (⋃ j, f j).Finite) :
    ∃ i₀, ∀ j, i₀ ≤ j → f j = f i₀ := by
  have := hfin.to_subtype
  obtain ⟨i₀, hi₀⟩ := exists_forall_of_mono (fun (a : ↥(⋃ j, f j)) i => (a : α) ∈ f i)
    (fun a i j hij h => hmono i j hij h) (fun a => Set.mem_iUnion.1 a.2)
  refine ⟨i₀, fun j hj => (Set.Subset.antisymm ?_ (hmono _ _ hj))⟩
  intro a ha
  exact hi₀ ⟨a, Set.mem_iUnion.2 ⟨j, ha⟩⟩

namespace Gather3

variable [DecidableEq P] [Fintype P] {Fs Qs : P → Set (Finset P)} {x : P → V} {fk : FaultKind}
  {t : ℕ} (E : Exec (protocol Qs) x fk t) {G : Set P}

/-- The arb-delivered pairs of `g` at time `i`. -/
def dl (g : P) (i : ℕ) : Set (P × V) := delivered ((E.σ i).inbox g)

omit [Fintype P] in
theorem dl_mono (g : P) {i j : ℕ} (h : i ≤ j) : dl E g i ⊆ dl E g j :=
  delivered_mono fun s => E.inbox_mono h g s

theorem dl_finite (hrbc : RBC E G) {g : P} (hg : g ∈ G) : (⋃ i, dl E g i).Finite := by
  refine Set.Finite.of_finite_image (f := Prod.fst) (Set.toFinite _) ?_
  rintro ⟨s, v⟩ hv ⟨s', v'⟩ hv' (h : s = s')
  subst h
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hv
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hv'
  rw [hrbc.agree g hg g hg s v v' i j hi hj]

/-- The delivered set of a guild member stabilizes. -/
theorem dl_stable (hrbc : RBC E G) {g : P} (hg : g ∈ G) :
    ∃ i₀, ∀ j, i₀ ≤ j → dl E g j = dl E g i₀ :=
  eventually_const_of_mono _ (fun _ _ h => dl_mono E g h) (dl_finite E hrbc hg)

/-- The acknowledged set `Tᵢ` of a guild member stabilizes. -/
theorem acked_stable (hrbc : RBC E G) {g : P} (hg : g ∈ G) :
    ∃ i₀, ∀ j, i₀ ≤ j → acked ((E.σ j).out g) = acked ((E.σ i₀).out g) := by
  refine eventually_const_of_mono (fun i => acked ((E.σ i).out g))
    (fun _ _ h => acked_mono fun m hm => E.sent_mono h hm) ((dl_finite E hrbc hg).subset ?_)
  intro sv hsv
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hsv
  exact Set.mem_iUnion.2 ⟨i, acked_sub_delivered (E.reachable i) g hi⟩

/-- A set of pairs delivered by a guild member is eventually delivered by every guild member. -/
theorem eventually_dl_sub (hrbc : RBC E G) {g g' : P} (hg : g ∈ G) (hg' : g' ∈ G) {i : ℕ}
    {S : Set (P × V)} (hS : S ⊆ dl E g i) : ∃ j, S ⊆ dl E g' j := by
  have hfin : S.Finite := (dl_finite E hrbc hg).subset fun a ha => Set.mem_iUnion.2 ⟨i, hS ha⟩
  have := hfin.to_subtype
  obtain ⟨j, hj⟩ := exists_forall_of_mono (fun (a : ↥S) j => (a : P × V) ∈ dl E g' j)
    (fun a i j hij h => dl_mono E g' hij h)
    (fun a => hrbc.total g hg g' hg' _ _ i (hS a.2))
  exact ⟨j, fun a ha => hj ⟨a, ha⟩⟩

variable (hF : E.Fair) (hrbc : RBC E G) (hG : IsGuild Fs Qs (Faulty E) G)
include hF hrbc hG

omit hrbc in
/-- Every guild member eventually receives the inputs of all members of a quorum inside `G`. -/
theorem eventually_quorum_delivered {g : P} (hg : g ∈ G) {Q : Finset P}
    (hQG : (Q : Set P) ⊆ G) :
    ∃ i, ∀ q ∈ Q, (q, x q) ∈ dl E g i := by
  have hsent : ∀ q ∈ (Q : Set P), ∃ i, (q, GMsg.val (x q)) ∈ (E.σ i).sent := fun q hq =>
    hF.send q _ 0 (correct_of_guild E hG (hQG hq)) fun _ _ => Or.inl rfl
  exact (E.eventually_rcv_all hF (fun q hq => correct_of_guild E hG (hQG hq)) hsent
    (correct_of_guild E hG hg)).imp fun i hi q hq => hi q hq

/-- Every guild member eventually sends `DISTRIBUTES`. -/
theorem eventually_distS {g : P} (hg : g ∈ G) : ∃ i S, (g, GMsg.distS S) ∈ (E.σ i).sent := by
  obtain ⟨Qg, hQg, hQgG⟩ := hG.2 g hg
  obtain ⟨i₁, hi₁⟩ := eventually_quorum_delivered E hF hG hg hQgG
  obtain ⟨i₀, hi₀⟩ := dl_stable E hrbc hg
  obtain ⟨j, m, ⟨S, rfl⟩, hj⟩ := E.eventually_sent hF (correct_of_guild E hG hg)
    (φ := fun m => ∃ S, m = GMsg.distS S) (m := GMsg.distS (dl E g (max i₀ i₁)))
    (i := max i₀ i₁) ⟨_, rfl⟩ fun j hj hno => Or.inr <| Or.inl ⟨by
      show GMsg.distS (dl E g (max i₀ i₁)) = GMsg.distS (dl E g j)
      rw [hi₀ j (le_trans (le_max_left _ _) hj), hi₀ _ (le_max_left _ _)], ⟨Qg, hQg, fun q hq =>
      ⟨x q, dl_mono E g (le_trans (le_max_right _ _) hj) (hi₁ q hq)⟩⟩, fun S hS => hno _ ⟨S, rfl⟩ hS⟩
  exact ⟨j, S, hj⟩

/-- Every guild member eventually receives `CONFIRM` from all members of a quorum inside `G`
once they have all sent it, and then sends `DISTRIBUTET` (or has already sent it). -/
theorem eventually_distT_of_confirm {g : P} (hg : g ∈ G) {Q : Finset P} (hQ : Q ∈ Qs g)
    (hQG : (Q : Set P) ⊆ G) (hconf : ∀ q ∈ Q, ∃ i, (q, GMsg.confirm) ∈ (E.σ i).sent) :
    ∃ i T, (g, GMsg.distT T) ∈ (E.σ i).sent := by
  obtain ⟨i₁, hi₁⟩ := E.eventually_rcv_all hF (S := (Q : Set P)) (m := fun _ => GMsg.confirm)
    (fun q hq => correct_of_guild E hG (hQG hq)) (fun q hq => hconf q hq)
    (correct_of_guild E hG hg)
  obtain ⟨i₀, hi₀⟩ := acked_stable E hrbc hg
  obtain ⟨j, m, ⟨T, rfl⟩, hj⟩ := E.eventually_sent hF (correct_of_guild E hG hg)
    (φ := fun m => ∃ T, m = GMsg.distT T) (m := GMsg.distT (acked ((E.σ (max i₀ i₁)).out g)))
    (i := max i₀ i₁) ⟨_, rfl⟩ fun j hj hno => Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨by
        show GMsg.distT (acked ((E.σ (max i₀ i₁)).out g)) = GMsg.distT (acked ((E.σ j).out g))
        rw [hi₀ j (le_trans (le_max_left _ _) hj), hi₀ _ (le_max_left _ _)],
        ⟨Q, hQ, fun q hq => E.inbox_mono (le_trans (le_max_right _ _) hj) g q (hi₁ q hq)⟩,
        fun T hT => hno _ ⟨T, rfl⟩ hT⟩
  exact ⟨j, T, hj⟩

/-- **Lemma 3.3.** In a fair execution with a nonempty guild, some guild member sends
`DISTRIBUTET`. -/
theorem lemma_3_3 (hne : G.Nonempty) :
    ∃ g ∈ G, ∃ i T, (g, GMsg.distT T) ∈ (E.σ i).sent := by
  by_contra hno
  push Not at hno
  -- every guild member sends DISTRIBUTES
  have hS := fun g (hg : g ∈ G) => eventually_distS E hF hrbc hG hg
  choose! iS S hSs using hS
  -- every guild member acknowledges the DISTRIBUTES of every guild member
  have hack : ∀ g ∈ G, ∀ q ∈ G, ∃ i, (q, GMsg.ack g (S g)) ∈ (E.σ i).sent := by
    intro g hg q hq
    have hgc := correct_of_guild E hG hg
    have hqc := correct_of_guild E hG hq
    obtain ⟨i₃, hi₃⟩ := hF.deliver q g _ _ hqc hgc (hSs g hg)
    obtain ⟨i₄, hi₄⟩ := eventually_dl_sub E hrbc hg hq
      (sent_distS (E.reachable (iS g)) (hSs g hg)).1
    refine hF.send q _ (max i₃ i₄) hqc fun j hj => Or.inr <| Or.inr <| Or.inl
      ⟨g, S g, rfl, E.rcv_mono (le_trans (le_max_left _ _) hj) hi₃,
        (hi₄.trans (dl_mono E q (le_trans (le_max_right _ _) hj))), fun T hT => hno q hq j T hT⟩
  -- every guild member sends READY
  have hready : ∀ g ∈ G, ∃ i, (g, GMsg.ready) ∈ (E.σ i).sent := by
    intro g hg
    obtain ⟨Qg, hQg, hQgG⟩ := hG.2 g hg
    obtain ⟨i₁, hi₁⟩ := E.eventually_rcv_all hF (S := (Qg : Set P))
      (m := fun _ => GMsg.ack g (S g)) (fun q hq => correct_of_guild E hG (hQgG hq))
      (fun q hq => hack g hg q (hQgG hq)) (correct_of_guild E hG hg)
    exact hF.send g _ i₁ (correct_of_guild E hG hg) fun j hj => Or.inr <| Or.inr <| Or.inr <|
      Or.inl ⟨rfl, Qg, hQg, fun q hq => ⟨S g, E.inbox_mono hj g q (hi₁ q hq)⟩⟩
  -- every guild member sends CONFIRM
  have hconf : ∀ g ∈ G, ∃ i, (g, GMsg.confirm) ∈ (E.σ i).sent := by
    intro g hg
    obtain ⟨Qg, hQg, hQgG⟩ := hG.2 g hg
    obtain ⟨i₁, hi₁⟩ := E.eventually_rcv_all hF (S := (Qg : Set P))
      (m := fun _ => GMsg.ready) (fun q hq => correct_of_guild E hG (hQgG hq))
      (fun q hq => hready q (hQgG hq)) (correct_of_guild E hG hg)
    exact hF.send g _ i₁ (correct_of_guild E hG hg) fun j hj => Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl ⟨rfl, Or.inl ⟨Qg, hQg, fun q hq => E.inbox_mono hj g q (hi₁ q hq)⟩⟩
  -- hence a guild member sends DISTRIBUTET: contradiction
  obtain ⟨g, hg⟩ := hne
  obtain ⟨Qg, hQg, hQgG⟩ := hG.2 g hg
  obtain ⟨i, T, hT⟩ := eventually_distT_of_confirm E hF hrbc hG hg hQg hQgG
    fun q hq => hconf q (hQgG hq)
  exact hno g hg i T hT

/-- **Lemma 3.6.** In a fair execution with a nonempty guild, every guild member sends
`DISTRIBUTET`. -/
theorem lemma_3_6 (hQ : IsQuorumSystem Fs Qs) (hne : G.Nonempty) :
    ∀ g ∈ G, ∃ i T, (g, GMsg.distT T) ∈ (E.σ i).sent := by
  obtain ⟨g₀, hg₀, i₀, T₀, hT₀⟩ := lemma_3_3 E hF hrbc hG hne
  obtain ⟨Q₀, hQ₀, hc₀⟩ := (sent_distT (E.reachable i₀) hT₀).1
  -- every guild member sends CONFIRM, triggered by the kernel `Q₀ \ F`
  have hconf : ∀ g ∈ G, ∃ i, (g, GMsg.confirm) ∈ (E.σ i).sent := by
    intro g hg
    have hK := hQ.isKernel_correct (hG.1 g₀ hg₀) (hG.1 g hg) hQ₀
    have hKc : ∀ y ∈ {y | y ∈ Q₀ ∧ y ∉ Faulty E}, E.Correct y := fun y hy => by
      simpa [Faulty] using hy.2
    obtain ⟨i₁, hi₁⟩ := E.eventually_rcv_all hF (S := {y | y ∈ Q₀ ∧ y ∉ Faulty E})
      (m := fun _ => GMsg.confirm) hKc
      (fun y hy => ⟨i₀, genuine_of_correct E (hKc y hy) (hc₀ y hy.1)⟩)
      (correct_of_guild E hG hg)
    exact hF.send g _ i₁ (correct_of_guild E hG hg) fun j hj => Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl ⟨rfl, Or.inr ⟨_, hK, fun y hy => E.inbox_mono hj g y (hi₁ y hy)⟩⟩
  intro g hg
  obtain ⟨Qg, hQg, hQgG⟩ := hG.2 g hg
  exact eventually_distT_of_confirm E hF hrbc hG hg hQg hQgG fun q hq => hconf q (hQgG hq)

/-- **Termination.** In a fair execution with a nonempty guild, every guild member
ag-delivers. -/
theorem termination (hQ : IsQuorumSystem Fs Qs) (hne : G.Nonempty) :
    ∀ k ∈ G, ∃ n U, (E.σ n).dec k = some U := by
  have h36 := lemma_3_6 E hF hrbc hG hQ hne
  choose! iT Tq hTq using h36
  intro k hk
  obtain ⟨Qk, hQk, hQkG⟩ := hG.2 k hk
  have hkc := correct_of_guild E hG hk
  -- eventually every `T_q` (`q ∈ Qk`) is received and all its pairs are delivered
  have hq : ∀ q : ↥Qk, ∃ j, QualT ((E.σ j).inbox k) q (Tq q) := by
    rintro ⟨q, hq⟩
    have hqG := hQkG hq
    obtain ⟨j₁, hj₁⟩ := hF.deliver k q _ _ hkc (correct_of_guild E hG hqG) (hTq q hqG)
    obtain ⟨j₂, hj₂⟩ := eventually_dl_sub E hrbc hqG hk
      (distT_sub_delivered (E.reachable (iT q)) (hTq q hqG))
    exact ⟨max j₁ j₂, E.rcv_mono (le_max_left _ _) hj₁,
      hj₂.trans (dl_mono E k (le_max_right _ _))⟩
  obtain ⟨j, hj⟩ := exists_forall_of_mono (fun (q : ↥Qk) j => QualT ((E.σ j).inbox k) q (Tq q))
    (fun q i j hij h => h.mono fun s => E.inbox_mono hij k s) hq
  let U : Set (P × V) := {sv | ∃ q ∈ Qk, sv ∈ Tq q}
  obtain ⟨n, hn⟩ := hF.decide k U j hkc fun j' hj' =>
    ⟨Qk, hQk, Tq, fun q hq => ⟨(hj ⟨q, hq⟩).mono fun s => E.inbox_mono hj' k s,
      fun sv hsv => ⟨q, hq, hsv⟩⟩, fun sv ⟨q, hq, hsv⟩ =>
        ⟨q, Tq q, (hj ⟨q, hq⟩).mono fun s => E.inbox_mono hj' k s, hsv⟩⟩
  obtain ⟨U', hU'⟩ := Option.ne_none_iff_exists'.1 hn
  exact ⟨n, U', hU'⟩

omit hF hrbc in
/-- **Lemma 3.8.** Algorithm 3 implements an asymmetric gather: in every fair execution in
which the reliable broadcast of the inputs has its guarantees for a nonempty guild `G`,
every member of `G` ag-delivers (termination), there is a common core (Lemma 3.7),
validity and agreement hold. -/
theorem lemma_3_8 (hF : E.Fair) (hrbc : RBC E G) (hQ : IsQuorumSystem Fs Qs)
    (hne : G.Nonempty) :
    (∀ k ∈ G, ∃ n U, (E.σ n).dec k = some U) ∧
    ExecCommonCore G E ∧
    (∀ k ∈ G, ∀ s, Wise Fs (Faulty E) s → ∀ n U, (E.σ n).dec k = some U →
      ∀ v, (s, v) ∈ U → v = x s) ∧
    (∀ k ∈ G, ∀ k' ∈ G, ∀ s n n' U U' v v', (E.σ n).dec k = some U →
      (E.σ n').dec k' = some U' → (s, v) ∈ U → (s, v') ∈ U' → v = v') :=
  ⟨termination E hF hrbc hG hQ hne, lemma_3_7 E hG hQ (lemma_3_3 E hF hrbc hG hne),
    fun _ _ _ hs _ _ hU _ hv => validity E hs hU hv,
    fun _ hk _ hk' _ _ _ _ _ _ _ hU hU' hv hv' => agreement E hrbc hk hk' hU hU' hv hv'⟩

end Gather3

end Podc.AsymmetricDAGConsensus
