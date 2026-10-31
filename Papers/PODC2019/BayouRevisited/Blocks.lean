import Papers.PODC2019.BayouRevisited.Basic

/-!
# Building blocks of executions

* `intBlk`: run a replica's internal events until it is passive (exists by input-driven
  processing);
* `no_casts_of_quiet`: after a replica has become passive (or if it never invoked an operation
  other than weak reads), it casts no further messages unless a new such invocation arrives
  (op-driven messages);
* delivery blocks: delivering a list of fresh `RB` messages, and `TOB`-delivering a segment of a
  global total order.
-/

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {Op Val : Type} (I : Impl n Op Val)

/-! ### Internal steps until passive -/

/-- The internal events `ιs` are successively enabled after `ℓ`. -/
def IntOK (i : Fin n) (ℓ : List I.Input) (ιs : List I.IntEv) : Prop :=
  ∀ t (h : t < ιs.length), I.enabled i (I.lstate i (ℓ ++ (ιs.take t).map LIn.int)) ιs[t]

/-- A canonical sequence of internal events leading to a passive state (if one exists). -/
noncomputable def toPassive (i : Fin n) (ℓ : List I.Input) : List I.IntEv :=
  open Classical in
  if h : ∃ ιs, I.IntOK i ℓ ιs ∧ I.Passive i (I.lstate i (ℓ ++ ιs.map LIn.int)) then h.choose
  else []

/-- The internal steps of `toPassive`, as local inputs. -/
noncomputable def intBlk (i : Fin n) (ℓ : List I.Input) : List I.Input :=
  (I.toPassive i ℓ).map LIn.int

variable {I} {S : ACTSpec Op Val}

lemma exists_toPassive (hI : I.IsACT S) {P : List I.Act} (hP : I.Valid S P) (i : Fin n) :
    ∃ ιs, I.IntOK i (I.loc i P) ιs ∧ I.Passive i (I.lstate i (I.loc i P ++ ιs.map LIn.int)) := by
  classical
  by_contra hne
  push_neg at hne
  set ℓ := I.loc i P
  have h0 := hne [] (fun t h => absurd h (by simp))
  simp only [Passive, List.map_nil, List.append_nil, not_forall, not_not] at h0
  obtain ⟨ι0, -⟩ := h0
  let c : List I.IntEv → I.IntEv := fun L =>
    if h : ∃ ι, I.enabled i (I.lstate i (ℓ ++ L.map LIn.int)) ι then h.choose else ι0
  let g : ℕ → List I.IntEv := fun k => Nat.rec [] (fun _ L => L ++ [c L]) k
  have gs : ∀ k, g (k + 1) = g k ++ [c (g k)] := fun k => rfl
  have glen : ∀ k, (g k).length = k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [gs]; simp [ih]
  have gok : ∀ k, I.IntOK i ℓ (g k) := by
    intro k; induction k with
    | zero => intro t h; simp [g] at h
    | succ k ih =>
      have hnp := hne (g k) ih
      simp only [Passive, not_forall, not_not] at hnp
      rw [gs]
      intro t ht
      simp only [List.length_append, List.length_singleton, glen] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · have := ih t (by rw [glen]; exact ht)
        rwa [List.take_append_of_le_length (by rw [glen]; omega),
          List.getElem_append_left (by rw [glen]; exact ht)]
      · rw [List.take_append_of_le_length (by rw [glen]), List.take_of_length_le (by rw [glen]),
          List.getElem_append_right (by rw [glen])]
        simp only [glen, Nat.sub_self, List.getElem_singleton]
        simp only [c, dif_pos hnp]
        exact hnp.choose_spec
  have grange : ∀ k, g k = (List.range k).map fun j => c (g j) := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [gs, List.range_succ, List.map_append, ← ih]; rfl
  obtain ⟨k, hk⟩ := hI.input_driven P hP i fun j => c (g j)
  apply hk
  have hok := gok (k + 1)
  rw [gs] at hok
  have := hok k (by simp [glen])
  rw [List.take_append_of_le_length (by rw [glen]), List.take_of_length_le (by rw [glen]),
    List.getElem_append_right (by rw [glen])] at this
  simp only [glen, Nat.sub_self, List.getElem_singleton] at this
  convert this using 3
  rw [grange k, List.map_map]; rfl

lemma toPassive_spec (hI : I.IsACT S) {P : List I.Act} (hP : I.Valid S P) (i : Fin n) :
    I.IntOK i (I.loc i P) (I.toPassive i (I.loc i P)) ∧
      I.Passive i (I.lstate i (I.loc i P ++ I.intBlk i (I.loc i P))) := by
  classical
  have h := exists_toPassive hI hP i
  rw [intBlk, toPassive, dif_pos h]
  exact h.choose_spec

lemma valid_intBlk (hI : I.IsACT S) {P : List I.Act} (hP : I.Valid S P) (i : Fin n) :
    I.Valid S (P ++ I.atR i (I.intBlk i (I.loc i P))) := by
  apply valid_atR hP
  intro t ht
  simp only [intBlk, List.length_map] at ht
  simp only [intBlk, List.getElem_map, Enabled, loc_append, loc_atR_self]
  have := (toPassive_spec hI hP i).1 t ht
  rwa [← List.map_take]

lemma passive_intBlk (hI : I.IsACT S) {P : List I.Act} (hP : I.Valid S P) (i : Fin n) :
    I.Passive i (I.lstate i (I.loc i (P ++ I.atR i (I.intBlk i (I.loc i P))))) := by
  simpa using (toPassive_spec hI hP i).2

/-! ### Quiet replicas cast nothing -/

/-- A local input that is not a weak read-only invocation could license casts. -/
def Licensing (S : ACTSpec Op Val) (x : I.Input) : Prop :=
  ∃ op l, x = .inv op l ∧ ¬ (l = .weak ∧ RDT.IsReadOnly S.F op)

/-- A replica is quiet after `ℓ` if it is passive (after at least one step), or if it never
received a licensing invocation. -/
def Quiet (S : ACTSpec Op Val) (i : Fin n) (ℓ : List I.Input) : Prop :=
  (ℓ ≠ [] ∧ I.Passive i (I.lstate i ℓ)) ∨ ∀ x ∈ ℓ, ¬ Licensing S x

lemma no_casts_of_quiet (hI : I.IsACT S) {P : List I.Act} (hP : I.Valid S P) {i : Fin n}
    {ℓ δ : List I.Input} (hl : I.loc i P = ℓ ++ δ) (hq : Quiet S i ℓ)
    (hδ : ∀ x ∈ δ, ¬ Licensing S x) :
    I.rbCasts i (ℓ ++ δ) = I.rbCasts i ℓ ∧ I.tobCasts i (ℓ ++ δ) = I.tobCasts i ℓ := by
  obtain ⟨X, hX, hXl⟩ := I.leffs_append i ℓ δ
  have hX0 : ∀ e ∈ X, e.rbCast = [] ∧ e.tobCast = [] := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := List.getElem_of_mem he
    by_contra hc
    have hc' : X[u].rbCast ≠ [] ∨ X[u].tobCast ≠ [] := by tauto
    have hidx : (I.leffs i (I.loc i P))[ℓ.length + u]? = some X[u] := by
      rw [hl, hX, List.getElem?_append_right (by simp)]; simp
    obtain ⟨s, hs, ⟨op, l, hsx, hlic⟩, hnp⟩ := hI.op_driven P hP i _ _ hidx hc'
    rw [hl] at hsx hnp
    by_cases hsl : s < ℓ.length
    · rw [List.getElem?_append_left hsl] at hsx
      rcases hq with ⟨hne, hpas⟩ | hno
      · apply hnp (ℓ.length - 1) (by omega) (by omega)
        have : ℓ.length - 1 + 1 = ℓ.length := by
          have := List.length_pos_of_ne_nil hne; omega
        rw [this, List.take_append_of_le_length le_rfl, List.take_length]
        exact hpas
      · exact hno _ (List.mem_of_getElem? hsx) ⟨op, l, rfl, hlic⟩
    · rw [List.getElem?_append_right (by omega)] at hsx
      exact hδ _ (List.mem_of_getElem? hsx) ⟨op, l, rfl, hlic⟩
  have h1 : X.flatMap Eff.rbCast = [] :=
    List.flatMap_eq_nil_iff.2 fun e he => (hX0 e he).1
  have h2 : X.flatMap Eff.tobCast = [] :=
    List.flatMap_eq_nil_iff.2 fun e he => (hX0 e he).2
  exact ⟨by simp [rbCasts, hX, h1], by simp [tobCasts, hX, h2]⟩

/-! ### Delivery blocks -/

/-- The identity of an `RB`-delivered message. -/
def rbIdOf : I.Input → Option (Fin n × ℕ)
  | .rb j k _ => some (j, k)
  | _ => none

lemma valid_rbDels {P : List I.Act} (hP : I.Valid S P) (i : Fin n) (ds : List I.Input)
    (hds : ∀ x ∈ ds, ∃ j k m, x = .rb j k m ∧ (I.rbCasts j (I.loc j P))[k]? = some m ∧
      ∀ m', LIn.rb j k m' ∉ I.loc i P)
    (hnd : (ds.filterMap rbIdOf).Nodup) :
    I.Valid S (P ++ I.atR i ds) := by
  induction ds using List.reverseRecOn with
  | nil => simpa [atR] using hP
  | append_singleton ds x ih =>
    have hds' : ∀ y ∈ ds, _ := fun y hy => hds y (List.mem_append_left _ hy)
    have hnd' : (ds.filterMap rbIdOf).Nodup := by
      rw [List.filterMap_append] at hnd; exact hnd.of_append_left
    have hV := ih hds' hnd'
    rw [atR_append, ← List.append_assoc]
    refine valid_concat hV ?_
    obtain ⟨j, k, m, rfl, hm, hnot⟩ := hds x (by simp)
    refine ⟨?_, ?_⟩
    · rw [loc_append, loc_atR]
      split_ifs
      · exact I.rbCasts_getElem?_append hm _
      · simpa using hm
    · intro m' hm'
      rw [loc_append, loc_atR_self, List.mem_append] at hm'
      rcases hm' with h | h
      · exact hnot m' h
      · rw [List.filterMap_append] at hnd
        have := List.disjoint_of_nodup_append hnd
        apply this (a := (j, k))
        · exact List.mem_filterMap.2 ⟨_, h, rfl⟩
        · simp [rbIdOf]

lemma valid_tobDels {P : List I.Act} (hP : I.Valid S P) (i : Fin n) (G : List (Fin n × ℕ))
    (hG : G.Nodup) (hpre : ∀ i', I.tobSeq i' P <+: G)
    (ds : List I.Input)
    (hds : ds.filterMap LIn.tobId = (G.drop (I.tobSeq i P).length).take ds.length)
    (hdl : ds.length ≤ G.length - (I.tobSeq i P).length)
    (hpay : ∀ x ∈ ds, ∃ j k m, x = .tob j k m ∧ (I.tobCasts j (I.loc j P))[k]? = some m) :
    I.Valid S (P ++ I.atR i ds) := by
  induction ds using List.reverseRecOn with
  | nil => simpa [atR] using hP
  | append_singleton ds x ih =>
    obtain ⟨j, k, m, rfl, hm⟩ := hpay x (by simp)
    have hlen : ∀ L : List I.Input, (∀ y ∈ L, ∃ j k m, y = LIn.tob j k m) →
        (L.filterMap LIn.tobId).length = L.length := by
      intro L hL
      induction L with
      | nil => rfl
      | cons y L ihL =>
        obtain ⟨j', k', m', rfl⟩ := hL y (by simp)
        simp [LIn.tobId, ihL (fun z hz => hL z (by simp [hz]))]
    have hdsT : ∀ y ∈ ds, ∃ j k m, y = LIn.tob j k m := fun y hy => by
      obtain ⟨j, k, m, h, -⟩ := hpay y (List.mem_append_left _ hy); exact ⟨j, k, m, h⟩
    set s := I.tobSeq i P
    set D := G.drop s.length with hDdef
    have hD : ds.length < D.length := by simp [D]; simp at hdl; omega
    rw [List.filterMap_append] at hds
    simp only [LIn.tobId, List.filterMap_cons_some, List.filterMap_nil, List.length_append,
      List.length_singleton, List.take_succ, List.getElem?_eq_getElem hD,
      Option.toList_some] at hds
    obtain ⟨hds', hx1⟩ := List.append_inj hds (by
      rw [hlen ds hdsT, List.length_take]; omega)
    have hV := ih hds' (by simp at hdl; omega)
      (fun y hy => hpay y (List.mem_append_left _ hy))
    rw [atR_append, ← List.append_assoc]
    refine valid_concat hV ?_
    obtain ⟨R, hR⟩ := hpre i
    have hR' : s ++ R = G := hR
    have hRD : D = R := by rw [hDdef, ← hR', List.drop_left]
    have hlt : s.length + ds.length < G.length := by
      have := congrArg List.length hR'; simp only [List.length_append] at this
      rw [hRD] at hD; omega
    have hx' : G[s.length + ds.length] = (j, k) := by
      have : D[ds.length] = (j, k) := by
        simp [List.filterMap, LIn.tobId] at hx1; exact hx1.symm
      rw [← this]; simp [D, List.getElem_drop]
    have hseq : I.tobSeq i (P ++ I.atR i ds) = G.take (s.length + ds.length) := by
      rw [tobSeq_append, loc_atR_self, hds', ← hR', List.take_append, ← hRD]
      simp [s]
    have hnew : I.tobSeq i (P ++ I.atR i ds) ++ [(j, k)] =
        G.take (s.length + ds.length + 1) := by
      rw [hseq, List.take_succ, List.getElem?_eq_getElem hlt, hx']; rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [loc_append, loc_atR]
      split_ifs
      · exact I.tobCasts_getElem?_append hm _
      · simpa using hm
    · intro m' hm'
      have hmem : (j, k) ∈ I.tobSeq i (P ++ I.atR i ds) :=
        List.mem_filterMap.2 ⟨_, hm', rfl⟩
      rw [hseq] at hmem
      obtain ⟨u, hu, hue⟩ := List.getElem_of_mem hmem
      simp only [List.length_take] at hu
      rw [List.getElem_take] at hue
      have := (List.Nodup.getElem_inj_iff hG (i := u) (j := s.length + ds.length)
        (hi := by omega) (hj := hlt)).1 (by rw [hue, hx'])
      omega
    · intro i'
      rw [hnew]
      by_cases hii : i' = i
      · subst hii; right; rw [hseq]; exact (List.take_prefix_take_left (by omega))
      · have hi' : I.tobSeq i' (P ++ I.atR i ds) = I.tobSeq i' P := by
          rw [tobSeq_append, I.loc_atR_ne (Ne.symm hii)]; simp
        rw [hi']
        exact List.prefix_or_prefix_of_prefix (List.take_prefix _ _) (hpre i')

end Podc.BayouRevisited.Impl

namespace Podc.BayouRevisited.Impl

variable {n : ℕ} {Op Val : Type} (I : Impl n Op Val)

/-! ### Catch-up blocks -/

/-- Deliver (in index order) all messages `RB-cast` by `j` (payloads `cs`) not yet delivered. -/
noncomputable def catchRB (ℓi : List I.Input) (j : Fin n) (cs : List I.Msg) : List I.Input :=
  open Classical in
  (List.range cs.length).filterMap fun k =>
    if ∃ m, LIn.rb j k m ∈ ℓi then none else cs[k]?.map (LIn.rb j k)

/-- Catch up on `RB` messages from all senders in `Ss`. -/
noncomputable def catchRBs (ℓi : List I.Input) (Ss : List (Fin n)) (rc : Fin n → List I.Msg) :
    List I.Input :=
  Ss.flatMap fun j => I.catchRB ℓi j (rc j)

/-- `TOB`-deliver the rest of the total order `G`. -/
def catchTOB (ℓi : List I.Input) (G : List (Fin n × ℕ)) (tc : Fin n → List I.Msg) :
    List I.Input :=
  (G.drop (ℓi.filterMap LIn.tobId).length).filterMap fun p => (tc p.1)[p.2]?.map (LIn.tob p.1 p.2)

/-- Local catch-up: `RB` from `Ss`, then `TOB` along `G`. -/
noncomputable def cuL (ℓi : List I.Input) (Ss : List (Fin n)) (G : List (Fin n × ℕ))
    (rc tc : Fin n → List I.Msg) : List I.Input :=
  I.catchRBs ℓi Ss rc ++ I.catchTOB ℓi G tc

/-- Catch-up of replica `i` after the execution `P`. -/
noncomputable def cu (i : Fin n) (Ss : List (Fin n)) (G : List (Fin n × ℕ)) (P : List I.Act) :
    List I.Input :=
  I.cuL (I.loc i P) Ss G (fun j => I.rbCasts j (I.loc j P)) (fun j => I.tobCasts j (I.loc j P))

/-- Catch-up followed by internal steps until passive. -/
noncomputable def blk (i : Fin n) (Ss : List (Fin n)) (G : List (Fin n × ℕ)) (P : List I.Act) :
    List I.Input :=
  I.cu i Ss G P ++ I.intBlk i (I.loc i P ++ I.cu i Ss G P)

variable {I} {S : ACTSpec Op Val}

lemma mem_catchRB {ℓi : List I.Input} {j : Fin n} {cs : List I.Msg} {x : I.Input} :
    x ∈ I.catchRB ℓi j cs ↔
      ∃ k m, x = .rb j k m ∧ cs[k]? = some m ∧ ¬ ∃ m', LIn.rb j k m' ∈ ℓi := by
  classical
  simp only [catchRB, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨k, -, hk⟩
    split_ifs at hk with hd
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hk
    exact ⟨k, m, rfl, hm, hd⟩
  · rintro ⟨k, m, rfl, hm, hd⟩
    refine ⟨k, (List.getElem?_eq_some_iff.1 hm).1, ?_⟩
    simp [hd, hm]

lemma mem_catchRBs {ℓi : List I.Input} {Ss : List (Fin n)} {rc : Fin n → List I.Msg}
    {x : I.Input} :
    x ∈ I.catchRBs ℓi Ss rc ↔
      ∃ j ∈ Ss, ∃ k m, x = .rb j k m ∧ (rc j)[k]? = some m ∧ ¬ ∃ m', LIn.rb j k m' ∈ ℓi := by
  simp only [catchRBs, List.mem_flatMap, mem_catchRB]

lemma catchRBs_ids_nodup (ℓi : List I.Input) {Ss : List (Fin n)} (hSs : Ss.Nodup)
    (rc : Fin n → List I.Msg) : ((I.catchRBs ℓi Ss rc).filterMap rbIdOf).Nodup := by
  classical
  have key : ∀ j, ∀ p ∈ (I.catchRB ℓi j (rc j)).filterMap rbIdOf, p.1 = j := by
    intro j p hp
    obtain ⟨x, hx, hpx⟩ := List.mem_filterMap.1 hp
    obtain ⟨k, m, rfl, -, -⟩ := mem_catchRB.1 hx
    simp [rbIdOf] at hpx; rw [← hpx]
  rw [catchRBs, List.filterMap_flatMap, List.nodup_flatMap]
  refine ⟨fun j _ => ?_, hSs.pairwise_of_forall_ne fun a _ b _ hab => ?_⟩
  · rw [catchRB, List.filterMap_filterMap]
    refine List.Nodup.filterMap ?_ List.nodup_range
    have hf : ∀ a b, b ∈ (if ∃ m, LIn.rb j a m ∈ ℓi then none
        else ((rc j)[a]?).map (LIn.rb j a)).bind rbIdOf → b = (j, a) := by
      intro a b h
      split_ifs at h
      · simp at h
      · cases hc : (rc j)[a]? <;> simp [hc, rbIdOf] at h; exact h.symm
    intro a a' b ha ha'
    have h1 := hf a b ha
    have h2 := hf a' b ha'
    rw [h1] at h2; exact (Prod.mk.inj h2).2
  · intro p hpa hpb
    exact hab ((key a p hpa).symm.trans (key b p hpb))

lemma mem_catchTOB {ℓi : List I.Input} {G : List (Fin n × ℕ)} {tc : Fin n → List I.Msg}
    {x : I.Input} (hx : x ∈ I.catchTOB ℓi G tc) :
    ∃ j k m, x = .tob j k m ∧ (tc j)[k]? = some m := by
  obtain ⟨p, -, hp⟩ := List.mem_filterMap.1 hx
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hp
  exact ⟨p.1, p.2, m, rfl, hm⟩

lemma filterMap_eq_self_of {β : Type} (g : β → Option β) :
    ∀ L : List β, (∀ p ∈ L, g p = some p) → L.filterMap g = L
  | [], _ => rfl
  | a :: L, h => by
    rw [List.filterMap_cons_some (h a (by simp)),
      filterMap_eq_self_of g L (fun p hp => h p (by simp [hp]))]

lemma catchTOB_ids {ℓi : List I.Input} {G : List (Fin n × ℕ)} {tc : Fin n → List I.Msg}
    (hcast : ∀ p ∈ G, p.2 < (tc p.1).length) :
    (I.catchTOB ℓi G tc).filterMap LIn.tobId = G.drop (ℓi.filterMap LIn.tobId).length := by
  rw [catchTOB, List.filterMap_filterMap]
  apply filterMap_eq_self_of
  intro p hp
  have := hcast p (List.mem_of_mem_drop hp)
  rw [List.getElem?_eq_getElem this]; rfl

lemma catchTOB_length {ℓi : List I.Input} {G : List (Fin n × ℕ)} {tc : Fin n → List I.Msg}
    (hcast : ∀ p ∈ G, p.2 < (tc p.1).length) :
    (I.catchTOB ℓi G tc).length = (G.drop (ℓi.filterMap LIn.tobId).length).length := by
  rw [← catchTOB_ids hcast]
  have hall : ∀ y ∈ I.catchTOB ℓi G tc, ∃ j k m, y = LIn.tob j k m := fun y hy => by
    obtain ⟨j, k, m, h, -⟩ := mem_catchTOB hy; exact ⟨j, k, m, h⟩
  generalize I.catchTOB ℓi G tc = L at hall
  induction L with
  | nil => rfl
  | cons y L ih =>
    obtain ⟨j, k, m, rfl⟩ := hall y (by simp)
    simp [LIn.tobId, ih (fun z hz => hall z (by simp [hz]))]

lemma catchRBs_tobIds (ℓi : List I.Input) (Ss : List (Fin n)) (rc : Fin n → List I.Msg) :
    (I.catchRBs ℓi Ss rc).filterMap LIn.tobId = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro x hx
  obtain ⟨j, -, k, m, rfl, -⟩ := mem_catchRBs.1 hx
  rfl

lemma valid_cu {P : List I.Act} (hP : I.Valid S P) (i : Fin n) {Ss : List (Fin n)}
    (hSs : Ss.Nodup) {G : List (Fin n × ℕ)} (hG : G.Nodup) (hpre : ∀ i', I.tobSeq i' P <+: G)
    (hcast : ∀ p ∈ G, p.2 < (I.tobCasts p.1 (I.loc p.1 P)).length) :
    I.Valid S (P ++ I.atR i (I.cu i Ss G P)) := by
  rw [cu, cuL, atR_append, ← List.append_assoc]
  set rbs := I.catchRBs (I.loc i P) Ss fun j => I.rbCasts j (I.loc j P)
  have h1 : I.Valid S (P ++ I.atR i rbs) := by
    refine valid_rbDels hP i rbs (fun x hx => ?_) (catchRBs_ids_nodup _ hSs _)
    obtain ⟨j, -, k, m, rfl, hm, hd⟩ := mem_catchRBs.1 hx
    exact ⟨j, k, m, rfl, hm, fun m' hm' => hd ⟨m', hm'⟩⟩
  have hseq : ∀ i', I.tobSeq i' (P ++ I.atR i rbs) = I.tobSeq i' P := by
    intro i'
    rw [tobSeq_append, loc_atR]
    split_ifs
    · rw [catchRBs_tobIds]; simp
    · simp
  have hcast' : ∀ p ∈ G, p.2 < ((fun j => I.tobCasts j (I.loc j P)) p.1).length := hcast
  apply valid_tobDels h1 i G hG (fun i' => by rw [hseq]; exact hpre i')
  · rw [hseq, catchTOB_ids hcast', catchTOB_length hcast']; simp [tobSeq]
  · rw [catchTOB_length hcast', hseq]; simp [tobSeq]
  · intro x hx
    obtain ⟨j, k, m, rfl, hm⟩ := mem_catchTOB hx
    refine ⟨j, k, m, rfl, ?_⟩
    rw [loc_append, loc_atR]
    split_ifs
    · exact I.tobCasts_getElem?_append hm _
    · simpa using hm

lemma valid_blk (hI : I.IsACT S) {P : List I.Act} (hP : I.Valid S P) (i : Fin n)
    {Ss : List (Fin n)} (hSs : Ss.Nodup) {G : List (Fin n × ℕ)} (hG : G.Nodup)
    (hpre : ∀ i', I.tobSeq i' P <+: G)
    (hcast : ∀ p ∈ G, p.2 < (I.tobCasts p.1 (I.loc p.1 P)).length) :
    I.Valid S (P ++ I.atR i (I.blk i Ss G P)) ∧
      I.Passive i (I.lstate i (I.loc i (P ++ I.atR i (I.blk i Ss G P)))) := by
  have h := valid_cu hP i hSs hG hpre hcast
  have h2 := valid_intBlk hI h i
  have h3 := passive_intBlk hI h i
  simp only [loc_append, loc_atR_self] at h2 h3
  rw [blk, atR_append, ← List.append_assoc]
  exact ⟨h2, by simpa using h3⟩

lemma tobSeq_blk {P : List I.Act} (i : Fin n) (Ss : List (Fin n)) {G : List (Fin n × ℕ)}
    (hpre : I.tobSeq i P <+: G)
    (hcast : ∀ p ∈ G, p.2 < (I.tobCasts p.1 (I.loc p.1 P)).length) :
    I.tobSeq i (P ++ I.atR i (I.blk i Ss G P)) = G := by
  have hcast' : ∀ p ∈ G, p.2 < ((fun j => I.tobCasts j (I.loc j P)) p.1).length := hcast
  have hint : (I.intBlk i (I.loc i P ++ I.cu i Ss G P)).filterMap LIn.tobId = [] := by
    simp [intBlk, List.filterMap_map, LIn.tobId, Function.comp_def]
  rw [tobSeq_append, loc_atR_self, blk, List.filterMap_append, hint, cu, cuL,
    List.filterMap_append, catchRBs_tobIds, catchTOB_ids hcast']
  obtain ⟨R, hR⟩ := hpre
  simp only [List.nil_append, List.append_nil]
  rw [show (I.loc i P).filterMap LIn.tobId = I.tobSeq i P from rfl, ← hR, List.drop_left]

lemma rb_delivered_blk {P : List I.Act} (i : Fin n) {Ss : List (Fin n)}
    (G : List (Fin n × ℕ)) {j : Fin n} (hj : j ∈ Ss) {k : ℕ}
    (hk : k < (I.rbCasts j (I.loc j P)).length) :
    ∃ m, LIn.rb j k m ∈ I.loc i (P ++ I.atR i (I.blk i Ss G P)) := by
  classical
  rw [loc_append, loc_atR_self, blk, cu, cuL]
  by_cases hd : ∃ m, LIn.rb j k m ∈ I.loc i P
  · obtain ⟨m, hm⟩ := hd; exact ⟨m, by simp [hm]⟩
  · refine ⟨(I.rbCasts j (I.loc j P))[k], ?_⟩
    apply List.mem_append_right; apply List.mem_append_left; apply List.mem_append_left
    exact mem_catchRBs.2 ⟨j, hj, k, _, rfl, List.getElem?_eq_getElem hk, hd⟩

lemma not_licensing_blk (i : Fin n) (Ss : List (Fin n)) (G : List (Fin n × ℕ))
    (P : List I.Act) : ∀ x ∈ I.blk i Ss G P, ¬ Licensing S x := by
  rintro x hx ⟨op, l, hxe, -⟩
  subst hxe
  simp only [blk, cu, cuL, List.mem_append] at hx
  rcases hx with (h | h) | h
  · obtain ⟨_, -, _, _, h, -⟩ := mem_catchRBs.1 h; cases h
  · obtain ⟨_, _, _, h, -⟩ := mem_catchTOB h; cases h
  · simp [intBlk] at h

end Podc.BayouRevisited.Impl
