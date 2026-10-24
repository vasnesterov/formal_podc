import Papers.PODC2016.StorageCostLowerBounds.RelayInv

/-!
# Liveness of the relay algorithm

With quorum size `qs = n - f` and `2 f < n`, every operation of a non-crashed client returns in
every fair execution with at most `f` server failures (`isLive`). A pending write keeps its
index and collects the acknowledgement of every correct server (each correct server receives
`W k v` and its `A k` reaches the writer, `Fair.delivered`); since there are at least `qs` correct
servers, it returns. Reads are symmetric (`Q j` / `D j`).
-/

namespace Podc.StorageCost.Relay

open Cslib.ChannelFailures Cslib.SharedMemory

variable {n : ℕ} {V : Type} {v₀ : V} (qs : ℕ)

/-! ### One-step facts -/

/-- A server receiving `W t v` appends `A t` to its channel to the writer. -/
lemma chan_srv_wr_W {C : Cfg n V v₀} {i : Fin n} {t : ℕ} {v : V} {rest : List (Msg V)}
    (hc : C.chan .wr (.srv i) = .W t v :: rest) :
    ((relay v₀ qs).step C (.deliver .wr (.srv i))).1.chan (.srv i) .wr =
      C.chan (.srv i) .wr ++ [.A t] := by
  rw [step_deliver_eq qs C hc]; simp [Config.apply, Config.pop, handle, msgsTo]

/-- A server receiving `Q j` appends `D j` to its channel to the reader. -/
lemma chan_srv_rd_Q {C : Cfg n V v₀} {i : Fin n} {j : ℕ} {rest : List (Msg V)}
    (hc : C.chan .rd (.srv i) = .Q j :: rest) :
    ((relay v₀ qs).step C (.deliver .rd (.srv i))).1.chan (.srv i) .rd =
      C.chan (.srv i) .rd ++ [.D j] := by
  rw [step_deliver_eq qs C hc]; simp [Config.apply, Config.pop, handle, msgsTo]

/-- While a write is pending and does not return, its index stays, it stays pending, and the
set of acknowledgements grows; an acknowledgement of the current write is recorded. -/
lemma wr_stable {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hb : (C.loc .wr).1.busy = true) (e : Event (Node n) (register V v₀))
    (hnr : ∀ x, Label.ret .wr x ∉ ((relay v₀ qs).step C e).2) :
    (((relay v₀ qs).step C e).1.loc .wr).1.k = (C.loc .wr).1.k ∧
      (((relay v₀ qs).step C e).1.loc .wr).1.busy = true ∧
      (C.loc .wr).1.acked ⊆ (((relay v₀ qs).step C e).1.loc .wr).1.acked ∧
      ∀ i rest, e = .deliver (.srv i) .wr → C.chan (.srv i) .wr = .A (C.loc .wr).1.k :: rest →
        i ∈ (((relay v₀ qs).step C e).1.loc .wr).1.acked := by
  by_cases ho : e.owner = .wr
  · cases e with
    | invoke p o =>
      simp only [Event.owner] at ho; subst ho
      obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 (hI.wbusy.1 hb)
      have : (relay v₀ qs).step C (.invoke .wr o) = (C, []) := by simp [Algorithm.step, ho']
      rw [this]; exact ⟨rfl, hb, subset_rfl, fun _ _ h => by simp at h⟩
    | tick p c =>
      simp only [Event.owner] at ho; subst ho
      have : (relay v₀ qs).step C (.tick .wr c) = (C, []) := by
        simp only [Algorithm.step, relay]; rw [handle_tick, apply_noop]
      rw [this]; exact ⟨rfl, hb, subset_rfl, fun _ _ h => by simp at h⟩
    | deliver a p =>
      simp only [Event.owner] at ho; subst ho
      rcases hc : C.chan a .wr with _ | ⟨m, rest⟩
      · have : (relay v₀ qs).step C (.deliver a .wr) = (C, []) := by simp [Algorithm.step, hc]
        rw [this]
        refine ⟨rfl, hb, subset_rfl, fun i rest h h' => ?_⟩
        simp only [Event.deliver.injEq, and_true] at h; subst h; rw [hc] at h'; simp at h'
      have hne : C.chan a .wr ≠ [] := by simp [hc]
      have hok : OkPair a .wr := by by_contra h; exact hne (hI.other a .wr h)
      rcases a with i | _ | _ <;> simp only [OkPair] at hok
      obtain ⟨t, rfl, -⟩ := hI.chA i m (by rw [hc]; simp)
      rw [step_deliver_eq qs C hc] at hnr ⊢
      set w := (C.loc .wr).1
      have hcl : C.loc .wr = (w, (C.loc .wr).2) := rfl
      have hloc : ∀ r, ((C.pop (.srv i) .wr rest).apply .wr r).1.loc .wr = r.1 := by
        intro r; simp [Config.apply]
      rw [hloc]
      by_cases hcond : w.busy = true ∧ t = w.k
      · by_cases hq : qs ≤ (insert i w.acked).card
        · exfalso
          apply hnr w.cur
          obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hI.wbusy.1 hb)
          rw [hcl]; simp [Config.apply, Config.pop, handle, hcond, hq, respOut, ho]
        · rw [hcl]; simp only [handle, hcond, hq, and_self, ite_true, ite_false]
          refine ⟨trivial, trivial, Finset.subset_insert _ _, fun i' rest' h _ => ?_⟩
          simp only [Event.deliver.injEq, Node.srv.injEq, and_true] at h; subst h
          exact Finset.mem_insert_self _ _
      · rw [hcl]; simp only [handle]; rw [ite_eq_right hcond]
        refine ⟨rfl, hb, subset_rfl, fun i' rest' h h' => ?_⟩
        simp only [Event.deliver.injEq, Node.srv.injEq, and_true] at h; subst h
        rw [hc] at h'; simp only [List.cons.injEq, Msg.A.injEq] at h'
        exact absurd ⟨hb, h'.1⟩ hcond
  · rw [loc_step_ne _ _ _ (Ne.symm ho)]
    refine ⟨rfl, hb, subset_rfl, fun i rest h _ => ?_⟩
    subst h; exact absurd rfl ho

/-- While a read is pending and does not return, the same holds for the reader. -/
lemma rd_stable {C : Cfg n V v₀} {α : Hist n V v₀} (hI : Inv qs C α)
    (hb : (C.loc .rd).2.busy = true) (e : Event (Node n) (register V v₀))
    (hnr : ∀ x, Label.ret .rd x ∉ ((relay v₀ qs).step C e).2) :
    (((relay v₀ qs).step C e).1.loc .rd).2.q = (C.loc .rd).2.q ∧
      (((relay v₀ qs).step C e).1.loc .rd).2.busy = true ∧
      (C.loc .rd).2.resp ⊆ (((relay v₀ qs).step C e).1.loc .rd).2.resp ∧
      ∀ i rest, e = .deliver (.srv i) .rd → C.chan (.srv i) .rd = .D (C.loc .rd).2.q :: rest →
        i ∈ (((relay v₀ qs).step C e).1.loc .rd).2.resp := by
  by_cases ho : e.owner = .rd
  · cases e with
    | invoke p o =>
      simp only [Event.owner] at ho; subst ho
      obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 (hI.rbusy.1 hb)
      have : (relay v₀ qs).step C (.invoke .rd o) = (C, []) := by simp [Algorithm.step, ho']
      rw [this]; exact ⟨rfl, hb, subset_rfl, fun _ _ h => by simp at h⟩
    | tick p c =>
      simp only [Event.owner] at ho; subst ho
      have : (relay v₀ qs).step C (.tick .rd c) = (C, []) := by
        simp only [Algorithm.step, relay]; rw [handle_tick, apply_noop]
      rw [this]; exact ⟨rfl, hb, subset_rfl, fun _ _ h => by simp at h⟩
    | deliver a p =>
      simp only [Event.owner] at ho; subst ho
      rcases hc : C.chan a .rd with _ | ⟨m, rest⟩
      · have : (relay v₀ qs).step C (.deliver a .rd) = (C, []) := by simp [Algorithm.step, hc]
        rw [this]
        refine ⟨rfl, hb, subset_rfl, fun i rest h h' => ?_⟩
        simp only [Event.deliver.injEq, and_true] at h; subst h; rw [hc] at h'; simp at h'
      have hne : C.chan a .rd ≠ [] := by simp [hc]
      have hok : OkPair a .rd := by by_contra h; exact hne (hI.other a .rd h)
      rcases a with i | _ | _ <;> simp only [OkPair] at hok
      rw [step_deliver_eq qs C hc] at hnr ⊢
      set r := (C.loc .rd).2
      have hcl : C.loc .rd = ((C.loc .rd).1, r) := rfl
      have hloc : ∀ x, ((C.pop (.srv i) .rd rest).apply .rd x).1.loc .rd = x.1 := by
        intro x; simp [Config.apply]
      rw [hloc]
      rcases hI.chR i m (by rw [hc]; simp) with ⟨t, v, rfl, -⟩ | ⟨j, rfl, -⟩
      · rw [hcl]; simp only [handle]
        split_ifs
        · refine ⟨rfl, hb, subset_rfl, fun i' rest' h h' => ?_⟩
          simp only [Event.deliver.injEq, Node.srv.injEq, and_true] at h; subst h
          rw [hc] at h'; simp at h'
        · refine ⟨rfl, hb, subset_rfl, fun i' rest' h h' => ?_⟩
          simp only [Event.deliver.injEq, Node.srv.injEq, and_true] at h; subst h
          rw [hc] at h'; simp at h'
      · by_cases hcond : r.busy = true ∧ j = r.q
        · by_cases hq : qs ≤ (insert i r.resp).card
          · exfalso
            apply hnr r.val
            obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 (hI.rbusy.1 hb)
            rw [hcl]; simp [Config.apply, Config.pop, handle, hcond, hq, respOut, ho]
          · rw [hcl]; simp only [handle, hcond, hq, and_self, ite_true, ite_false]
            refine ⟨trivial, trivial, Finset.subset_insert _ _, fun i' rest' h _ => ?_⟩
            simp only [Event.deliver.injEq, Node.srv.injEq, and_true] at h; subst h
            exact Finset.mem_insert_self _ _
        · rw [hcl]; simp only [handle]; rw [ite_eq_right hcond]
          refine ⟨rfl, hb, subset_rfl, fun i' rest' h h' => ?_⟩
          simp only [Event.deliver.injEq, Node.srv.injEq, and_true] at h; subst h
          rw [hc] at h'; simp only [List.cons.injEq, Msg.D.injEq] at h'
          exact absurd ⟨hb, h'.1⟩ hcond
  · rw [loc_step_ne _ _ _ (Ne.symm ho)]
    refine ⟨rfl, hb, subset_rfl, fun i rest h _ => ?_⟩
    subst h; exact absurd rfl ho

lemma invoke_wr_loc (C : Cfg n V v₀) (hp : C.pend .wr = none) (v : V) :
    ((relay v₀ qs).step C (.invoke .wr (.write v))).1.loc .wr =
      (⟨(C.loc .wr).1.k + 1, true, v, ∅⟩, (C.loc .wr).2) := by
  simp [Algorithm.step, hp, relay, handle, Config.apply]

lemma invoke_wr_chan (C : Cfg n V v₀) (hp : C.pend .wr = none) (v : V) (i : Fin n) :
    ((relay v₀ qs).step C (.invoke .wr (.write v))).1.chan .wr (.srv i) =
      C.chan .wr (.srv i) ++ [.W ((C.loc .wr).1.k + 1) v] := by
  simp [Algorithm.step, hp, relay, handle, Config.apply, msgsTo_toAll_srv]

lemma invoke_rd_loc (C : Cfg n V v₀) (hp : C.pend .rd = none) :
    (((relay v₀ qs).step C (.invoke .rd .read)).1.loc .rd).2 =
      ⟨(C.loc .rd).2.q + 1, true, (C.loc .rd).2.best, (C.loc .rd).2.val, ∅⟩ := by
  simp [Algorithm.step, hp, relay, handle, Config.apply]

lemma invoke_rd_chan (C : Cfg n V v₀) (hp : C.pend .rd = none) (i : Fin n) :
    ((relay v₀ qs).step C (.invoke .rd .read)).1.chan .rd (.srv i) =
      C.chan .rd (.srv i) ++ [.Q ((C.loc .rd).2.q + 1)] := by
  simp [Algorithm.step, hp, relay, handle, Config.apply, msgsTo_toAll_srv]

/-! ### Liveness -/

lemma inv_at (hq2 : n < 2 * qs) (hqn : qs ≤ n) (ev : ℕ → Event (Node n) (register V v₀))
    (hev : ∀ t, EvOk (ev t)) (t : ℕ) :
    Inv qs ((relay v₀ qs).cfgAt ev t)
      ((relay v₀ qs).hist (relay v₀ qs).initCfg (Algorithm.pre ev t)) := by
  rw [Algorithm.cfgAt_eq_run]
  exact inv_reach qs hq2 hqn _ (fun e he => by
    simp only [Algorithm.pre, List.mem_map] at he; obtain ⟨u, -, rfl⟩ := he; exact hev u)

open Classical in
lemma card_correct {f : ℕ} {fp : FailurePattern (Node n)} (hfail : (srvFail fp).card ≤ f)
    (ev : ℕ → Event (Node n) (register V v₀)) :
    n - f ≤ (Finset.univ.filter fun i => ¬ Algorithm.Crashed fp ev (.srv i)).card := by
  classical
  have h1 : Finset.univ.filter (fun i => Algorithm.Crashed fp ev (Node.srv i)) ⊆ srvFail fp := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [srvFail, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi.1
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun i => Algorithm.Crashed fp ev (Node.srv i))
  have h3 := Finset.card_le_card h1
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- Monotonicity along a time interval. -/
lemma subset_of_le {S : ℕ → Finset (Fin n)} {a : ℕ} (h : ∀ t ≥ a, S t ⊆ S (t + 1)) :
    ∀ t t', a ≤ t → t ≤ t' → S t ⊆ S t' := by
  intro t t' hat htt'
  induction t', htt' using Nat.le_induction with
  | base => exact subset_rfl
  | succ t' ht' ih => exact ih.trans (h t' (by omega))

/-- **The relay algorithm is live** with `qs = n - f` and `2 f < n`. -/
theorem isLive {f : ℕ} (hf : 2 * f < n) :
    Live (relay v₀ (n - f) : Algorithm (Node n) (register V v₀) _ _) f := by
  classical
  set qs := n - f with hqs
  have hq2 : n < 2 * qs := by omega
  have hqn : qs ≤ n := by omega
  intro fp hch hfail ev hfair hev p hp t₀ o hinv hpend
  have hI := inv_at qs hq2 hqn ev hev
  have hcfg : ∀ t, (relay v₀ qs).cfgAt ev (t + 1) =
      ((relay v₀ qs).step ((relay v₀ qs).cfgAt ev t) (ev t)).1 := fun t => rfl
  set Cor := Finset.univ.filter fun i => ¬ Algorithm.Crashed fp ev (Node.srv i)
  have hCor : qs ≤ Cor.card := card_correct hfail ev
  have hcq : ∀ i ∈ Cor, ¬ Algorithm.Crashed fp ev (Node.srv i) := by
    intro i hi; simpa [Cor] using hi
  have hnoch : ∀ a b, (a, b) ∉ fp.chans := by intro a b; rw [hch]; simp
  by_contra hnr
  have hnr' : ∀ t ≥ t₀, ∀ x, Label.ret p x ∉ (relay v₀ qs).labAt ev t := by
    intro t ht x hx; exact hnr ⟨t, ht, x, hx⟩
  rcases hev t₀ p o hinv with ⟨rfl, v, rfl⟩ | ⟨rfl, rfl⟩
  · -- a write
    set C₀ := (relay v₀ qs).cfgAt ev t₀
    set k₀ := (C₀.loc .wr).1.k + 1
    have h1 : ((relay v₀ qs).cfgAt ev (t₀ + 1)).loc .wr =
        (⟨k₀, true, v, ∅⟩, (C₀.loc .wr).2) := by
      rw [hcfg, hinv]; exact invoke_wr_loc qs _ hpend v
    have h2 : ∀ i, ((relay v₀ qs).cfgAt ev (t₀ + 1)).chan .wr (.srv i) =
        C₀.chan .wr (.srv i) ++ [.W k₀ v] := by
      intro i
      rw [hcfg, hinv]; exact invoke_wr_chan qs _ hpend v i
    -- stability
    have hst : ∀ t ≥ t₀ + 1, (((relay v₀ qs).cfgAt ev t).loc .wr).1.k = k₀ ∧
        (((relay v₀ qs).cfgAt ev t).loc .wr).1.busy = true := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => rw [h1]; exact ⟨rfl, rfl⟩
      | succ t ht ih =>
        have := wr_stable qs (hI t) ih.2 (ev t) (hnr' t (by omega))
        rw [hcfg]; exact ⟨this.1.trans ih.1, this.2.1⟩
    have hmono : ∀ t ≥ t₀ + 1, (((relay v₀ qs).cfgAt ev t).loc .wr).1.acked ⊆
        (((relay v₀ qs).cfgAt ev (t + 1)).loc .wr).1.acked := by
      intro t ht
      rw [hcfg]; exact (wr_stable qs (hI t) (hst t ht).2 (ev t) (hnr' t (by omega))).2.2.1
    -- every correct server eventually acknowledges
    have hack : ∀ i ∈ Cor, ∃ T ≥ t₀ + 1,
        i ∈ (((relay v₀ qs).cfgAt ev T).loc .wr).1.acked := by
      intro i hi
      have hpos : (((relay v₀ qs).cfgAt ev (t₀ + 1)).chan .wr (.srv i))[(C₀.chan .wr (.srv i)).length]? =
          some (.W k₀ v) := by rw [h2]; simp
      obtain ⟨t₁, ht₁, he₁, hh₁⟩ := Algorithm.Fair.delivered hfair hp (hcq i hi) (hnoch _ _) _ _ _ hpos
      obtain ⟨rest, hr⟩ : ∃ rest, ((relay v₀ qs).cfgAt ev t₁).chan .wr (.srv i) = .W k₀ v :: rest := by
        cases hc : ((relay v₀ qs).cfgAt ev t₁).chan .wr (.srv i) with
        | nil => simp [hc] at hh₁
        | cons a rest => simp [hc] at hh₁; exact ⟨rest, by rw [hh₁]⟩
      have h3 : ((relay v₀ qs).cfgAt ev (t₁ + 1)).chan (.srv i) .wr =
          ((relay v₀ qs).cfgAt ev t₁).chan (.srv i) .wr ++ [.A k₀] := by
        rw [hcfg, he₁]; exact chan_srv_wr_W qs hr
      have hpos' : (((relay v₀ qs).cfgAt ev (t₁ + 1)).chan (.srv i) .wr)[
          (((relay v₀ qs).cfgAt ev t₁).chan (.srv i) .wr).length]? = some (.A k₀) := by
        rw [h3]; simp
      obtain ⟨t₂, ht₂, he₂, hh₂⟩ :=
        Algorithm.Fair.delivered hfair (hcq i hi) hp (hnoch _ _) _ _ _ hpos'
      obtain ⟨rest', hr'⟩ : ∃ rest, ((relay v₀ qs).cfgAt ev t₂).chan (.srv i) .wr = .A k₀ :: rest := by
        cases hc : ((relay v₀ qs).cfgAt ev t₂).chan (.srv i) .wr with
        | nil => simp [hc] at hh₂
        | cons a rest => simp [hc] at hh₂; exact ⟨rest, by rw [hh₂]⟩
      have hk := hst t₂ (by omega)
      refine ⟨t₂ + 1, by omega, ?_⟩
      rw [hcfg]
      exact (wr_stable qs (hI t₂) hk.2 (ev t₂) (hnr' t₂ (by omega))).2.2.2 i rest' he₂
        (by rw [hk.1]; exact hr')
    choose! T hT1 hT2 using hack
    set T₀ := Cor.sup T + (t₀ + 1)
    have hall : Cor ⊆ (((relay v₀ qs).cfgAt ev T₀).loc .wr).1.acked := by
      intro i hi
      exact subset_of_le hmono (T i) T₀ (hT1 i hi)
        (by have := Finset.le_sup (f := T) hi; omega) (hT2 i hi)
    have := ((hI T₀).wacked (hst T₀ (by omega)).2).2
    have := Finset.card_le_card hall
    omega
  · -- a read
    set C₀ := (relay v₀ qs).cfgAt ev t₀
    set q₀ := (C₀.loc .rd).2.q + 1
    have h1 : (((relay v₀ qs).cfgAt ev (t₀ + 1)).loc .rd).2 =
        ⟨q₀, true, (C₀.loc .rd).2.best, (C₀.loc .rd).2.val, ∅⟩ := by
      rw [hcfg, hinv]; exact invoke_rd_loc qs _ hpend
    have h2 : ∀ i, ((relay v₀ qs).cfgAt ev (t₀ + 1)).chan .rd (.srv i) =
        C₀.chan .rd (.srv i) ++ [.Q q₀] := by
      intro i
      rw [hcfg, hinv]; exact invoke_rd_chan qs _ hpend i
    have hst : ∀ t ≥ t₀ + 1, (((relay v₀ qs).cfgAt ev t).loc .rd).2.q = q₀ ∧
        (((relay v₀ qs).cfgAt ev t).loc .rd).2.busy = true := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => rw [h1]; exact ⟨rfl, rfl⟩
      | succ t ht ih =>
        have := rd_stable qs (hI t) ih.2 (ev t) (hnr' t (by omega))
        rw [hcfg]; exact ⟨this.1.trans ih.1, this.2.1⟩
    have hmono : ∀ t ≥ t₀ + 1, (((relay v₀ qs).cfgAt ev t).loc .rd).2.resp ⊆
        (((relay v₀ qs).cfgAt ev (t + 1)).loc .rd).2.resp := by
      intro t ht
      rw [hcfg]; exact (rd_stable qs (hI t) (hst t ht).2 (ev t) (hnr' t (by omega))).2.2.1
    have hack : ∀ i ∈ Cor, ∃ T ≥ t₀ + 1,
        i ∈ (((relay v₀ qs).cfgAt ev T).loc .rd).2.resp := by
      intro i hi
      have hpos : (((relay v₀ qs).cfgAt ev (t₀ + 1)).chan .rd (.srv i))[(C₀.chan .rd (.srv i)).length]? =
          some (.Q q₀) := by rw [h2]; simp
      obtain ⟨t₁, ht₁, he₁, hh₁⟩ := Algorithm.Fair.delivered hfair hp (hcq i hi) (hnoch _ _) _ _ _ hpos
      obtain ⟨rest, hr⟩ : ∃ rest, ((relay v₀ qs).cfgAt ev t₁).chan .rd (.srv i) = .Q q₀ :: rest := by
        cases hc : ((relay v₀ qs).cfgAt ev t₁).chan .rd (.srv i) with
        | nil => simp [hc] at hh₁
        | cons a rest => simp [hc] at hh₁; exact ⟨rest, by rw [hh₁]⟩
      have h3 : ((relay v₀ qs).cfgAt ev (t₁ + 1)).chan (.srv i) .rd =
          ((relay v₀ qs).cfgAt ev t₁).chan (.srv i) .rd ++ [.D q₀] := by
        rw [hcfg, he₁]; exact chan_srv_rd_Q qs hr
      have hpos' : (((relay v₀ qs).cfgAt ev (t₁ + 1)).chan (.srv i) .rd)[
          (((relay v₀ qs).cfgAt ev t₁).chan (.srv i) .rd).length]? = some (.D q₀) := by
        rw [h3]; simp
      obtain ⟨t₂, ht₂, he₂, hh₂⟩ :=
        Algorithm.Fair.delivered hfair (hcq i hi) hp (hnoch _ _) _ _ _ hpos'
      obtain ⟨rest', hr'⟩ : ∃ rest, ((relay v₀ qs).cfgAt ev t₂).chan (.srv i) .rd = .D q₀ :: rest := by
        cases hc : ((relay v₀ qs).cfgAt ev t₂).chan (.srv i) .rd with
        | nil => simp [hc] at hh₂
        | cons a rest => simp [hc] at hh₂; exact ⟨rest, by rw [hh₂]⟩
      have hk := hst t₂ (by omega)
      refine ⟨t₂ + 1, by omega, ?_⟩
      rw [hcfg]
      exact (rd_stable qs (hI t₂) hk.2 (ev t₂) (hnr' t₂ (by omega))).2.2.2 i rest' he₂
        (by rw [hk.1]; exact hr')
    choose! T hT1 hT2 using hack
    set T₀ := Cor.sup T + (t₀ + 1)
    have hall : Cor ⊆ (((relay v₀ qs).cfgAt ev T₀).loc .rd).2.resp := by
      intro i hi
      exact subset_of_le hmono (T i) T₀ (hT1 i hi)
        (by have := Finset.le_sup (f := T) hi; omega) (hT2 i hi)
    have := ((hI T₀).rcur (hst T₀ (by omega)).2).1
    have := Finset.card_le_card hall
    omega

end Podc.StorageCost.Relay
