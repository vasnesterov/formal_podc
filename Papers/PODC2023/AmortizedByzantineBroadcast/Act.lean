import Papers.PODC2023.AmortizedByzantineBroadcast.Exec

/-!
# What honest nodes send in Algorithm 4

Characterizations of the outputs of `act`.
-/

namespace Podc.AmortizedByzantineBroadcast

variable {n : ℕ} {V : Type} [DecidableEq V] [NeZero n] (P : Params n V) (pol : Skip)

lemma mem_star {r : ℕ} {u : Fin n} {st : St n V} {w : Fin n} {x : Item n V}
    (h : (w, x) ∈ star P r u st) :
    (∃ a b, x = .accuse a b ∧ x ∈ held st r ∧ ∃ s, (r - 1, s, x) ∈ st.rcv) ∨
    (∃ v, x = .cpf v ∧ n - P.f ≤ (accusers (held st r) v).length) ∨
    (∃ k j m, x = .cproof k j m ∧ x ∈ held st r) := by
  simp only [star, mcast, List.mem_append, List.mem_filterMap, List.mem_map, List.mem_filter,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_dedup] at h
  rcases h with (h | h) | h
  · obtain ⟨y, ⟨⟨t, s, z⟩, ⟨hz, ht⟩, rfl⟩, hy⟩ := h
    cases z <;> simp at hy
    obtain ⟨-, rfl, rfl⟩ := hy
    simp only [beq_iff_eq] at ht
    refine Or.inl ⟨_, _, rfl, ?_, s, ?_⟩
    · rw [mem_held]; exact ⟨t, s, by omega, hz⟩
    · rw [show r - 1 = t by omega]; exact hz
  · obtain ⟨v, hv, w', hw⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [Prod.mk.injEq] at hw
    exact Or.inr (Or.inl ⟨v, hw.2.symm, hv.1⟩)
  · obtain ⟨y, hy, w', hw⟩ := h
    simp only [Prod.mk.injEq] at hw
    obtain ⟨-, rfl⟩ := hw
    obtain ⟨hy, hc⟩ := hy
    cases y <;> simp at hc
    refine Or.inr (Or.inr ⟨_, _, _, rfl, ?_⟩)
    simp only [List.mem_map, List.mem_filter, beq_iff_eq] at hy
    obtain ⟨⟨t, s, z⟩, ⟨hz, ht⟩, rfl⟩ := hy
    rw [mem_held]; exact ⟨t, s, by omega, hz⟩

lemma star_vote {r : ℕ} {u₀ : Fin n} {st : St n V} {w u : Fin n} {k i : ℕ} {m : V} :
    (w, .vote u k i m) ∉ star P r u₀ st := by
  intro h; rcases mem_star P h with ⟨_, _, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, _, h, -⟩ <;> cases h

lemma star_cshare {r : ℕ} {u₀ : Fin n} {st : St n V} {w u : Fin n} {k i : ℕ} {m : V} :
    (w, .cshare u k i m) ∉ star P r u₀ st := by
  intro h; rcases mem_star P h with ⟨_, _, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, _, h, -⟩ <;> cases h

lemma star_prop {r : ℕ} {u₀ : Fin n} {st : St n V} {w L : Fin n} {k i : ℕ} {m : V} {c : Option ℕ} :
    (w, .prop L k i m c) ∉ star P r u₀ st := by
  intro h; rcases mem_star P h with ⟨_, _, h, -⟩ | ⟨_, h, -⟩ | ⟨_, _, _, h, -⟩ <;> cases h

/-- Kill the cases of `steps` that cannot produce a given item. -/
macro "kill_steps" h:ident : tactic =>
  `(tactic| first
    | (simp [mcast, nbcast] at $h:ident; done)
    | (simp [mcast, nbcast] at $h:ident
       repeat' (first | split at $h:ident | split_ifs at $h:ident)
       all_goals simp_all))

/-- Honest votes: only in step (4) (Vote) of the epoch, signed by the node itself, after having
forwarded the leader's proposal on `m` in Propagate-1 and without detected equivocation. -/
lemma act_vote {r : ℕ} {u w u' : Fin n} {inp : ℕ → V} {st : St n V} {k i : ℕ} {m : V}
    (h : (w, .vote u' k i m) ∈ act P pol r u inp st) :
    u' = u ∧ stepOf r = 3 ∧ slotOf P r = k ∧ epochOf P r = i ∧
      (propVals (held st r) (leader P k i) k i).length < 2 ∧
      ∃ w' c, (epochStart r + 2, w', .prop (leader P k i) k i m c) ∈ st.sent := by
  unfold act at h
  rw [List.mem_append] at h
  rcases h with h | h
  · split_ifs at h with ha
    · have h3 : stepOf r = 3 := by
        by_contra hne
        unfold steps at h
        generalize hs : stepOf r = s at h hne
        have : s < 11 := hs ▸ stepOf_lt r
        interval_cases s <;> first | exact hne rfl | kill_steps h
      simp only [steps, h3] at h
      split_ifs at h with hv
      all_goals try (simp [mcast] at h; done)
      simp only [List.mem_map, List.mem_dedup, List.mem_filterMap, Prod.mk.injEq] at h
      obtain ⟨m', ⟨⟨t, w', z⟩, hz, hz'⟩, -, hm⟩ := h
      split_ifs at hz' with ht
      cases z <;> simp at hz'
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hz'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      simp only at ht
      exact ⟨rfl, h3, rfl, rfl, by omega, w', _, ht ▸ hz⟩
    · simp at h
  · exact absurd h (star_vote P)

/-- Honest commit-proof shares: only in step (6) (Propagate-2), signed by the node itself, for a
certificate it holds, which it simultaneously sends to all its `G_ε`-neighbours. -/
lemma act_cshare {r : ℕ} {u w u' : Fin n} {inp : ℕ → V} {st : St n V} {k i : ℕ} {m : V}
    (h : (w, .cshare u' k i m) ∈ act P pol r u inp st) :
    u' = u ∧ stepOf r = 5 ∧ slotOf P r = k ∧ epochOf P r = i ∧ (i, m) ∈ certsOf (held st r) k ∧
      ∀ w', P.G u w' = true → (w', .cert k i m) ∈ act P pol r u inp st := by
  unfold act at h ⊢
  rw [List.mem_append] at h
  rcases h with h | h
  · split_ifs at h with ha
    · have h5 : stepOf r = 5 := by
        by_contra hne
        unfold steps at h
        generalize hs : stepOf r = s at h hne
        have : s < 11 := hs ▸ stepOf_lt r
        interval_cases s <;> first | exact hne rfl | kill_steps h
      simp only [steps, h5, List.mem_flatMap, List.mem_dedup, List.mem_filterMap,
        List.mem_append, nbcast, List.mem_map, List.mem_filter, List.mem_singleton,
        Prod.mk.injEq] at h
      obtain ⟨m', ⟨⟨j, m''⟩, hc, hc'⟩, h⟩ := h
      split_ifs at hc' with hj
      cases hc'
      rcases h with ⟨_, _, _, h⟩ | ⟨-, h⟩
      · cases h
      · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        simp only at hj
        subst hj
        refine ⟨rfl, h5, rfl, rfl, hc, fun w' hw' => ?_⟩
        simp only [ha, ↓reduceIte, List.mem_append]
        left
        simp only [steps, h5, List.mem_flatMap, List.mem_dedup, List.mem_filterMap,
          List.mem_append, nbcast, List.mem_map, List.mem_filter, List.mem_singleton,
          Prod.mk.injEq, List.mem_finRange, true_and]
        exact ⟨_, ⟨_, hc, by simp⟩, Or.inl ⟨w', hw', rfl, rfl⟩⟩
    · simp at h
  · exact absurd h (star_cshare P)

/-- The freshness of the certificate `u` sent in Collect in the epoch of round `r`. -/
def collectVal (r : ℕ) (st : St n V) : Option ℕ :=
  (freshest (certsOf (held st (epochStart r)) (slotOf P r))).map (·.1)

/-- Proposals sent in step (3) (Propagate-1): received in this epoch, of this epoch's leader, at
least as fresh as the Collect certificate, and sent to all `G_ε`-neighbours. -/
lemma act_prop_step2 {r : ℕ} {u w L : Fin n} {inp : ℕ → V} {st : St n V} {k i : ℕ} {m : V}
    {c : Option ℕ} (h2 : stepOf r = 2) (h : (w, .prop L k i m c) ∈ act P pol r u inp st) :
    Item.prop L k i m c ∈ heldIn st (epochStart r) r ∧ L = leader P k i ∧ slotOf P r = k ∧
      epochOf P r = i ∧ fle (collectVal P r st) c = true ∧
      ∀ w', P.G u w' = true → (w', .prop L k i m c) ∈ act P pol r u inp st := by
  unfold act at h ⊢
  rw [List.mem_append] at h
  rcases h with h | h
  · split_ifs at h with ha
    · simp only [steps, h2, List.mem_flatMap, List.mem_dedup, List.mem_filter, nbcast,
        List.mem_map, Prod.mk.injEq] at h
      obtain ⟨y, ⟨hy, hf⟩, w', -, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
      obtain ⟨⟨rfl, rfl, rfl⟩, hf⟩ := hf
      refine ⟨hy, rfl, rfl, rfl, hf, fun w'' hw'' => ?_⟩
      simp only [ha, ↓reduceIte, List.mem_append]
      left
      simp only [steps, h2, List.mem_flatMap, List.mem_dedup, List.mem_filter, nbcast,
        List.mem_map, Prod.mk.injEq, List.mem_finRange, true_and]
      exact ⟨_, ⟨hy, by simp [hf]⟩, w'', hw'', rfl, rfl⟩
    · simp at h
  · exact absurd h (star_prop P)

lemma freshest_mem {cs : List (ℕ × V)} {c : ℕ × V} (h : freshest cs = some c) : c ∈ cs := by
  unfold freshest at h
  suffices ∀ (acc : Option (ℕ × V)), (∀ a, acc = some a → a ∈ cs) → ∀ l : List (ℕ × V),
      (∀ x ∈ l, x ∈ cs) → ∀ c, l.foldl (fun acc c => match acc with
        | none => some c
        | some a => if a.1 < c.1 then some c else some a) acc = some c → c ∈ cs from
    this none (by simp) cs (fun _ h => h) c h
  intro acc hacc l hl
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons x l ih =>
    intro c hc
    simp only [List.foldl_cons] at hc
    refine ih _ ?_ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) c hc
    intro a ha
    rcases acc with _ | b
    · simp only [Option.some.injEq] at ha; subst ha; exact hl _ List.mem_cons_self
    · simp only at ha
      split_ifs at ha
      · cases ha; exact hl _ List.mem_cons_self
      · cases ha; exact hacc _ rfl

lemma mem_of_mem_cproofVals {xs : List (Item n V)} {k i : ℕ} {m : V} (h : m ∈ cproofVals xs k i) :
    Item.cproof k i m ∈ xs := by
  simp only [cproofVals, List.mem_dedup, List.mem_filterMap] at h
  obtain ⟨y, hy, h⟩ := h
  cases y <;> simp at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  exact hy

/-- Why an honest node may send an item: it is its own signed atom (for a proposal with a
certificate, a certificate it holds), an item it holds, or an aggregate of `n - f` shares it
holds. -/
def Justified (r : ℕ) (st : St n V) (u : Fin n) (x : Item n V) : Prop :=
  (x.signer = some u ∧ ∀ L k i m j, x = .prop L k i m (some j) → (j, m) ∈ certsOf (held st r) k) ∨
  x ∈ held st r ∨
  (∃ k j m, x = .cert k j m ∧
    ((j, m) ∈ certsOf (held st r) k ∨ n - P.f ≤ (voters (held st r) k j m).length)) ∨
  (∃ k j m, x = .cproof k j m ∧ n - P.f ≤ (sharers (held st r) k j m).length) ∨
  (∃ v, x = .cpf v ∧ n - P.f ≤ (accusers (held st r) v).length)

lemma act_justified {r : ℕ} {u w : Fin n} {inp : ℕ → V} {st : St n V} {x : Item n V}
    (h : (w, x) ∈ act P pol r u inp st) : Justified P r st u x := by
  unfold act at h
  rw [List.mem_append] at h
  rcases h with h | h
  · split_ifs at h with ha
    · have : stepOf r < 11 := stepOf_lt r
      generalize hs : stepOf r = s at this
      interval_cases s <;> simp only [steps, hs] at h
      · -- Collect
        split at h
        · rename_i hf
          simp only [List.mem_singleton, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, Or.inl (freshest_mem hf)⟩))
        · simp at h
      · -- Propose
        split at h
        · split at h
          · rename_i hf
            simp only [mcast, List.mem_map, Prod.mk.injEq] at h
            obtain ⟨_, _, -, rfl⟩ := h
            refine Or.inl ⟨rfl, ?_⟩
            rintro L k i m j ⟨⟩
            exact freshest_mem hf
          · simp only [mcast, List.mem_map, Prod.mk.injEq] at h
            obtain ⟨_, _, -, rfl⟩ := h
            exact Or.inl ⟨rfl, by rintro L k i m j ⟨⟩⟩
        · simp at h
      · -- Propagate-1
        simp only [List.mem_flatMap, List.mem_dedup, List.mem_filter, nbcast, List.mem_map,
          Prod.mk.injEq] at h
        obtain ⟨y, ⟨hy, -⟩, _, -, -, rfl⟩ := h
        exact Or.inr (Or.inl (heldIn_sub_held st _ _ _ hy))
      · -- Vote
        split_ifs at h
        · simp at h
        · simp only [mcast, List.mem_map, Prod.mk.injEq] at h
          obtain ⟨_, _, -, rfl⟩ := h
          exact Or.inl ⟨rfl, by rintro L k i m j ⟨⟩⟩
        · simp only [List.mem_map, Prod.mk.injEq] at h
          obtain ⟨_, _, -, rfl⟩ := h
          exact Or.inl ⟨rfl, by rintro L k i m j ⟨⟩⟩
      · -- Certificate
        split_ifs at h
        · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, mcast, List.mem_map,
            Prod.mk.injEq] at h
          obtain ⟨m, ⟨-, hm⟩, _, -, -, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, Or.inr hm⟩))
        · simp at h
      · -- Propagate-2
        simp only [List.mem_flatMap, List.mem_dedup, List.mem_filterMap, List.mem_append, nbcast,
          List.mem_map, List.mem_filter, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨m, ⟨⟨j, m'⟩, hc, hc'⟩, h⟩ := h
        split_ifs at hc' with hj
        cases hc'
        simp only at hj
        subst hj
        rcases h with ⟨_, _, -, rfl⟩ | ⟨-, rfl⟩
        · exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, Or.inl hc⟩))
        · exact Or.inl ⟨rfl, by rintro L k i m j ⟨⟩⟩
      · -- Commit
        split_ifs at h
        · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, mcast, List.mem_map,
            Prod.mk.injEq] at h
          obtain ⟨m, ⟨-, hm⟩, _, -, -, rfl⟩ := h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, hm⟩)))
        · simp at h
      · -- Query-1
        split at h
        · simp only [List.mem_append] at h
          rcases h with h | h
          · split at h
            · simp at h
            · simp only [mcast, List.mem_map, Prod.mk.injEq] at h
              obtain ⟨_, _, -, rfl⟩ := h
              exact Or.inl ⟨rfl, by rintro L k i m j ⟨⟩⟩
          · split at h
            · simp only [List.mem_singleton, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h
              exact Or.inl ⟨rfl, by rintro L k i m j ⟨⟩⟩
            · simp at h
        · simp at h
      · -- Respond-1
        split at h
        · rename_i m hm
          simp only [List.mem_filterMap] at h
          obtain ⟨v, -, h⟩ := h
          split_ifs at h
          cases h
          exact Or.inr (Or.inl (mem_of_mem_cproofVals (List.mem_of_mem_head? hm)))
        · simp at h
      · -- Query-2
        split at h
        · split_ifs at h
          · simp at h
          · simp only [mcast, List.mem_append, List.mem_map, Prod.mk.injEq] at h
            rcases h with ⟨_, _, -, rfl⟩ | ⟨_, _, -, rfl⟩ <;>
              exact Or.inl ⟨rfl, by rintro L k i m j ⟨⟩⟩
        · simp at h
      · -- Respond-2
        split at h
        · rename_i m hm
          simp only [List.mem_map, Prod.mk.injEq] at h
          obtain ⟨_, _, -, rfl⟩ := h
          exact Or.inr (Or.inl (mem_of_mem_cproofVals (List.mem_of_mem_head? hm)))
        · simp at h
    · simp at h
  · rcases mem_star P h with ⟨a, b, rfl, hx, -⟩ | ⟨v, rfl, hv⟩ | ⟨k, j, m, rfl, hx⟩
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, rfl, hv⟩)))
    · exact Or.inr (Or.inl hx)

end Podc.AmortizedByzantineBroadcast
