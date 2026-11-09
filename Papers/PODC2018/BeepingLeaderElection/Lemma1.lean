import Papers.PODC2018.BeepingLeaderElection.Rules

set_option linter.unusedSectionVars false

/-!
# Lemma 1 for the repaired rule priority

For Algorithm 1 with the deletion rule of [Casteigts et al.] (`Priority.maxDelete`: among rules 1 and
2 the largest deletion), we prove by induction on the phase the two invariants

* `EdgeInv`: the prefixes of any two neighbours are in one of the five forms of Lemma 6 of
  [Casteigts et al.] (`Form`);
* `SuspInv`: a suspicious node has rule 1, 2 or 3 enabled (Lemma 2 of [Casteigts et al.]: a deletion
  is followed by a deletion or a change);

and derive **Lemma 1** (`lemma_1`). No assumption on the identifiers or on the graph is needed.
-/

namespace Podc.BeepingLeaderElection

section Network

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem mem_received {C : V → NState} {v : V} {m : Word × Bool} :
    m ∈ received G C v ↔ ∃ u, G.Adj v u ∧ ((C u).pre, (C u).susp) = m := by
  simp [received]

theorem pair_mem_received {C : V → NState} {u v : V} (h : G.Adj v u) :
    ((C u).pre, (C u).susp) ∈ received G C v := (mem_received G).2 ⟨u, h, rfl⟩

/-- Every pair of neighbours is in one of the five forms. -/
def EdgeInv (C : V → NState) : Prop :=
  ∀ u v, G.Adj u v → Form (C u).pre (C v).pre (C u).susp (C v).susp

/-- A suspicious node has a deletion (rules 1–2) or a change (rule 3) enabled. -/
def SuspInv (pr : Priority) (C : V → NState) : Prop :=
  ∀ v, (C v).susp = true → 0 < delAmount pr (C v).pre (received G C v) ∨
    ∃ m ∈ received G C v, chgBy (C v).pre m.1 = true

end Network

/-! ### Facts about `actOf` -/

section actOf

variable {pr : Priority} {Y : Word} {s : NState} {R : Finset (Word × Bool)}

theorem actOf_of_pos (h : 0 < delAmount pr s.pre R) :
    actOf pr Y s R = .del (delAmount pr s.pre R) := by
  simp [actOf, h]

theorem actOf_of_chg (h0 : ¬ 0 < delAmount pr s.pre R) (h : ∃ m ∈ R, chgBy s.pre m.1 = true) :
    actOf pr Y s R = .chg := by
  simp only [actOf, h0, h, ite_false, ite_true]

theorem actOf_del_iff {k : ℕ} : actOf pr Y s R = .del k ↔ 0 < delAmount pr s.pre R ∧
    k = delAmount pr s.pre R := by
  unfold actOf; dsimp only
  split_ifs with h1 <;> simp [h1, eq_comm]

theorem actOf_chg_last (h : actOf pr Y s R = .chg) : ∃ z, s.pre = z ++ [false] := by
  unfold actOf at h; dsimp only at h
  split_ifs at h with h1 h2
  obtain ⟨m, -, hm⟩ := h2
  obtain ⟨z, y', hz, -⟩ := chgBy_eq_true_iff.1 hm
  exact ⟨z, hz⟩

theorem actOf_delOrChg (h : 0 < delAmount pr s.pre R ∨ ∃ m ∈ R, chgBy s.pre m.1 = true) :
    (actOf pr Y s R).isDel = true ∨ actOf pr Y s R = .chg := by
  by_cases h0 : 0 < delAmount pr s.pre R
  · simp [actOf_of_pos h0]
  · exact Or.inr (actOf_of_chg h0 (h.resolve_left h0))

theorem actOf_r4 (h : ∃ m ∈ R, s.pre ++ [true] <+: m.1) :
    (actOf pr Y s R).isDel = true ∨ actOf pr Y s R = .chg ∨ actOf pr Y s R = .app true := by
  unfold actOf; dsimp only
  split_ifs <;> simp_all

theorem actOf_r5 (h : ∃ m ∈ R, s.pre ++ [false] <+: m.1) : actOf pr Y s R ≠ .null := by
  unfold actOf; dsimp only
  split_ifs <;> simp_all

end actOf

theorem delAmount_maxDelete (x : Word) (R : Finset (Word × Bool)) :
    delAmount .maxDelete x R = max (R.sup (amt1 x)) (R.sup fun m => amt2 x m.1) := rfl

theorem amt1_le_delAmount {x : Word} {R : Finset (Word × Bool)} {m : Word × Bool} (hm : m ∈ R) :
    amt1 x m ≤ delAmount .maxDelete x R :=
  (Finset.le_sup (f := amt1 x) hm).trans (le_max_left _ _)

theorem amt2_le_delAmount {x : Word} {R : Finset (Word × Bool)} {m : Word × Bool} (hm : m ∈ R) :
    amt2 x m.1 ≤ delAmount .maxDelete x R :=
  (Finset.le_sup (f := fun m : Word × Bool => amt2 x m.1) hm).trans (le_max_right _ _)

/-! ### Corollary 7 of [Casteigts et al.]: rule 2 deletes at most 3 letters -/

theorem amt2_of_prefix {x y : Word} (h : x <+: y) : amt2 x y = 0 := by
  obtain ⟨w, rfl⟩ := h
  simp [amt2, branchLow]

theorem amt2_of_prefix' {x y : Word} (h : y <+: x) : amt2 x y = 0 := by
  obtain ⟨w, rfl⟩ := h
  simp [amt2, branchLow]

theorem amt2_le_three_of_F {x y : Word} {sx : Bool} (h : F x y sx) : amt2 x y ≤ 3 := by
  rcases h with rfl | ⟨w, rfl, -⟩ | ⟨p, c, rfl, rfl⟩ | ⟨p, w, rfl, rfl, hw⟩ | ⟨w, rfl, -⟩
  · simp [amt2_of_prefix (List.prefix_refl x)]
  · simp [amt2_of_prefix (prefix_append_self x w)]
  · rw [show p ++ [false] = p ++ false :: [] from rfl, show p ++ [true, c] = p ++ true :: [c] from rfl,
      amt2_eq]; simp
  · simp [amt2, branchLow]
  · simp [amt2_of_prefix (prefix_append_self x w)]

theorem amt2_le_three_of_F' {x y : Word} {sy : Bool} (h : F y x sy) : amt2 x y ≤ 3 := by
  rcases h with rfl | ⟨w, rfl, -⟩ | ⟨p, c, rfl, rfl⟩ | ⟨p, w, rfl, rfl, hw⟩ | ⟨w, rfl, -⟩
  · simp [amt2_of_prefix (List.prefix_refl y)]
  · simp [amt2_of_prefix' (prefix_append_self y w)]
  · simp [amt2, branchLow]
  · rw [show p ++ [true] = p ++ true :: [] from rfl, amt2_eq]; exact hw
  · simp [amt2_of_prefix' (prefix_append_self y w)]

theorem amt2_le_three_of_form {x y : Word} {sx sy : Bool} (h : Form x y sx sy) : amt2 x y ≤ 3 :=
  h.elim amt2_le_three_of_F amt2_le_three_of_F'

/-! ### The constraints hold in the network -/

section Network

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem delAmount_le_three {C : V → NState} (hE : EdgeInv G C) (v : V) :
    delAmount .maxDelete (C v).pre (received G C v) ≤ 3 := by
  rw [delAmount_maxDelete]
  refine max_le (Finset.sup_le fun m _ => amt1_le_three _ _) (Finset.sup_le fun m hm => ?_)
  obtain ⟨u, hu, rfl⟩ := (mem_received G).1 hm
  exact amt2_le_three_of_form (hE v u hu)

theorem delAmount_le_length (C : V → NState) (v : V) :
    delAmount .maxDelete (C v).pre (received G C v) ≤ (C v).pre.length := by
  rw [delAmount_maxDelete]
  exact max_le (Finset.sup_le fun m _ => amt1_le_length _ _)
    (Finset.sup_le fun m _ => amt2_le_length _ _)

/-- The actions of the rules satisfy the per-edge constraints `Allowed`. -/
theorem allowed_of_inv {C : V → NState} (hE : EdgeInv G C) (hS : SuspInv G .maxDelete C)
    (Y : Word) {u v : V} (huv : G.Adj v u) :
    Allowed (actOf .maxDelete Y (C v) (received G C v)) (C v).pre (C v).susp
      (C u).pre (C u).susp := by
  set R := received G C v
  have hm : ((C u).pre, (C u).susp) ∈ R := pair_mem_received G huv
  refine ⟨fun h => actOf_delOrChg (hS v h), ?_, fun h => actOf_chg_last h, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨h0, rfl⟩ := actOf_del_iff.1 hk
    exact ⟨h0, delAmount_le_three G hE v, delAmount_le_length G C v⟩
  · intro hs hp hl
    have h1 : 0 < amt1 (C v).pre ((C u).pre, (C u).susp) := amt1_pos_iff.2 ⟨hs, hp, hl⟩
    have h2 := amt1_le_delAmount (x := (C v).pre) hm
    refine ⟨_, actOf_of_pos (by omega), ?_⟩
    have : amt1 (C v).pre ((C u).pre, (C u).susp) = min ((C v).pre.length - (C u).pre.length) 3 := by
      simp [amt1, hs, hp, hl]
    omega
  · intro z w y' hx hy hw
    have h1 : amt2 (C v).pre (C u).pre = w.length := by rw [hx, hy, amt2_eq]
    have h2 := amt2_le_delAmount (x := (C v).pre) hm
    have hw' := List.length_pos_of_ne_nil hw
    refine ⟨_, actOf_of_pos (by simp at h2; omega), ?_⟩
    simp at h2; omega
  · intro z y' hx hy
    exact actOf_delOrChg (Or.inr ⟨_, hm, chgBy_eq_true_iff.2 ⟨z, y', hx, hy⟩⟩)
  · intro w hy
    exact actOf_r4 ⟨_, hm, by rw [hy]; simp⟩
  · intro w hy
    exact actOf_r5 ⟨_, hm, by rw [hy]; simp⟩

variable (ident : V → ℕ)

theorem phase_pre (C : V → NState) (v : V) :
    (phase G .maxDelete ident C v).pre =
      (actOf .maxDelete (alpha (ident v)) (C v) (received G C v)).apply (C v).pre :=
  ruleStep_pre _ _ _ _

theorem phase_susp (C : V → NState) (v : V) :
    (phase G .maxDelete ident C v).susp =
      (actOf .maxDelete (alpha (ident v)) (C v) (received G C v)).isDel :=
  ruleStep_susp _ _ _ _

theorem edgeInv_phase {C : V → NState} (hE : EdgeInv G C) (hS : SuspInv G .maxDelete C) :
    EdgeInv G (phase G .maxDelete ident C) := by
  intro u v huv
  rw [phase_pre, phase_pre, phase_susp, phase_susp]
  exact form_step (hE u v huv) (allowed_of_inv G hE hS _ huv) (allowed_of_inv G hE hS _ huv.symm)


/-- A word with prefix `z ++ [true]` keeps it under any action other than a deletion. -/
theorem prefix_keep_of_not_del {z t : Word} {a : Act} (ha : a.isDel = false)
    (hchg : a = .chg → ∃ q, z ++ true :: t = q ++ [false]) :
    z ++ [true] <+: a.apply (z ++ true :: t) := by
  cases a with
  | del k => simp at ha
  | chg =>
    obtain ⟨q, hq⟩ := hchg rfl
    rcases eq_or_ne t [] with rfl | ht
    · have := congrArg List.getLast? hq; simp at this
    · rw [show z ++ true :: t = (z ++ [true]) ++ t by simp, Act.chg_apply_append ht]
      exact prefix_append_self _ _
  | app b =>
    exact (show z ++ [true] <+: z ++ true :: t by simp).trans (prefix_append_self _ [b])
  | null => simp

/-- **Lemma 2 of [Casteigts et al.]** (as an invariant): a node that deleted letters in the last phase
has a deletion or a change enabled. -/
theorem suspInv_phase {C : V → NState} (hS : SuspInv G .maxDelete C) :
    SuspInv G .maxDelete (phase G .maxDelete ident C) := by
  intro v hv
  set C' := phase G .maxDelete ident C with hC'
  set x := (C v).pre with hx
  set R := received G C v with hR
  set d := delAmount .maxDelete x R with hd
  have hact : actOf .maxDelete (alpha (ident v)) (C v) R = .del d ∧ 0 < d := by
    rw [phase_susp] at hv
    generalize ha : actOf .maxDelete (alpha (ident v)) (C v) R = a at hv
    cases a with
    | del k => obtain ⟨h0, rfl⟩ := actOf_del_iff.1 ha; exact ⟨rfl, h0⟩
    | _ => simp at hv
  obtain ⟨hact, hd0⟩ := hact
  have hx' : (C' v).pre = x.take (x.length - d) := by
    rw [hC', phase_pre, hact]; rfl
  have hdx : d ≤ x.length := delAmount_le_length G C v
  -- the action of a neighbour `u`
  have hmem' : ∀ u, G.Adj v u → ((C' u).pre, (C' u).susp) ∈ received G C' v :=
    fun u hu => pair_mem_received G hu
  have hpos1 : ∀ m ∈ received G C' v, 0 < amt1 (C' v).pre m →
      0 < delAmount .maxDelete (C' v).pre (received G C' v) := fun m hm h =>
    lt_of_lt_of_le h (amt1_le_delAmount hm)
  have hpos2 : ∀ m ∈ received G C' v, 0 < amt2 (C' v).pre m.1 →
      0 < delAmount .maxDelete (C' v).pre (received G C' v) := fun m hm h =>
    lt_of_lt_of_le h (amt2_le_delAmount hm)
  rw [hd, delAmount_maxDelete] at hd0
  rcases le_total (R.sup fun m => amt2 x m.1) (R.sup (amt1 x)) with hle | hle
  · -- rule 1 witness
    have hd1 : d = R.sup (amt1 x) := by rw [hd, delAmount_maxDelete, max_eq_left hle]
    have hne : R.Nonempty := by
      by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; simp [h] at hd0
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup R hne (amt1 x)
    obtain ⟨u, hu, rfl⟩ := (mem_received G).1 hm
    have h1 : 0 < amt1 x ((C u).pre, (C u).susp) := by omega
    obtain ⟨hsu, hpy, hly⟩ := amt1_pos_iff.1 h1
    simp only at hsu hpy hly
    have hdy : d ≤ x.length - (C u).pre.length := by
      have : amt1 x ((C u).pre, (C u).susp) = min (x.length - (C u).pre.length) 3 := by
        simp [amt1, hsu, hpy, hly]
      omega
    have hyx' : (C u).pre <+: (C' v).pre := by
      rw [hx']
      exact List.prefix_of_prefix_length_le hpy (List.take_prefix _ _) (by simp; omega)
    rcases actOf_delOrChg (Y := alpha (ident u)) (hS u hsu) with ha | ha
    · generalize hau : actOf .maxDelete (alpha (ident u)) (C u) (received G C u) = a at ha
      cases a with
      | del k =>
        obtain ⟨hk0, rfl⟩ := actOf_del_iff.1 hau
        have hky := delAmount_le_length G C u
        have hu' : (C' u).pre = (Act.del (delAmount .maxDelete (C u).pre (received G C u))).apply
            (C u).pre := by rw [hC', phase_pre, hau]
        have hsu' : (C' u).susp = true := by rw [hC', phase_susp, hau]; rfl
        left
        refine hpos1 _ (hmem' u hu) (amt1_pos_iff.2 ⟨hsu', ?_, ?_⟩)
        · rw [hu']; exact (Act.del_prefix _ _).trans hyx'
        · rw [hu', Act.del_length]; have := hyx'.length_le; omega
      | _ => simp at ha
    · obtain ⟨z, hz⟩ := actOf_chg_last ha
      have hu' : (C' u).pre = z ++ [true] := by rw [hC', phase_pre, ha, hz, Act.chg_apply]
      obtain ⟨r, hr⟩ := hz ▸ hyx'
      rcases eq_or_ne r [] with rfl | hrne
      · right
        refine ⟨_, hmem' u hu, chgBy_eq_true_iff.2 ⟨z, [], ?_, ?_⟩⟩
        · simpa using hr.symm
        · simp [hu']
      · left
        refine hpos2 _ (hmem' u hu) (amt2_pos_iff.2 ⟨z, r, [], ?_, ?_, hrne⟩)
        · simpa using hr.symm
        · simp [hu']
  · -- rule 2 witness
    have hd2 : d = R.sup fun m => amt2 x m.1 := by
      rw [hd, delAmount_maxDelete, max_eq_right hle]
    have hne : R.Nonempty := by
      by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h; simp [h] at hd0
    obtain ⟨m, hm, hmeq⟩ := Finset.exists_mem_eq_sup R hne (fun m => amt2 x m.1)
    obtain ⟨u, hu, rfl⟩ := (mem_received G).1 hm
    have h2 : 0 < amt2 x (C u).pre := by simp only at hmeq; omega
    obtain ⟨z, w, y'', hxz, hyz, hw⟩ := amt2_pos_iff.1 h2
    have hdw : d = w.length := by simp only at hmeq; rw [hd2, hmeq, hxz, hyz, amt2_eq]
    have hx'z : (C' v).pre = z ++ [false] := by
      rw [hx', hdw, hxz, show z ++ false :: w = (z ++ [false]) ++ w by simp]
      exact Act.del_apply_append_eq rfl
    generalize hau : actOf .maxDelete (alpha (ident u)) (C u) (received G C u) = a
    have hu' : (C' u).pre = a.apply (C u).pre := by rw [hC', phase_pre, hau]
    have hsu' : (C' u).susp = a.isDel := by rw [hC', phase_susp, hau]
    by_cases hp : z ++ [true] <+: (C' u).pre
    · right
      obtain ⟨t, ht⟩ := hp
      refine ⟨_, hmem' u hu, chgBy_eq_true_iff.2 ⟨z, t, hx'z, ?_⟩⟩
      simp [← ht]
    · left
      cases a with
      | del k =>
        have hyp : (C' u).pre <+: z := by
          have h1 : (C' u).pre <+: z ++ true :: y'' := by rw [hu', ← hyz]; exact Act.del_prefix _ _
          by_contra hcon
          apply hp
          rcases List.prefix_or_prefix_of_prefix h1 (prefix_append_self z (true :: y'')) with h | h
          · exact absurd h hcon
          · obtain ⟨t, ht⟩ := h
            rw [← ht] at h1
            obtain ⟨t', ht'⟩ := h1
            rcases t with _ | ⟨c, t⟩
            · simp at ht; exact absurd (by rw [ht]) hcon
            · have : c = true := by
                have := congrArg (fun l => l[z.length]?) ht'; simp at this; exact this
              subst this
              exact ⟨t, by simpa using ht⟩
        refine hpos1 _ (hmem' u hu) (amt1_pos_iff.2 ⟨by rw [hsu']; rfl, ?_, ?_⟩)
        · rw [hx'z]; exact hyp.trans (prefix_append_self _ _)
        · rw [hx'z]; have := hyp.length_le; simp; omega
      | _ =>
        exfalso; apply hp
        rw [hu', hyz]
        refine prefix_keep_of_not_del rfl fun hc => ?_
        obtain ⟨q, hq⟩ := actOf_chg_last (hau.trans hc)
        exact ⟨q, hyz ▸ hq⟩

/-- Both invariants hold in every phase of Algorithm 1 with the repaired rule priority. -/
theorem invariants (t : ℕ) :
    EdgeInv G (run G .maxDelete ident t) ∧ SuspInv G .maxDelete (run G .maxDelete ident t) := by
  induction t with
  | zero =>
    refine ⟨fun u v _ => form_refl _ _ _, fun v h => ?_⟩
    simp [run, NState.init] at h
  | succ t ih =>
    exact ⟨edgeInv_phase G ident ih.1 ih.2, suspInv_phase G ident ih.2⟩


end Network

/-! ### From the five forms to Lemma 1 -/

theorem lemma1Rel_of_prefix {x y : Word} (h : x <+: y) (hl : y.length ≤ x.length + 6) :
    Lemma1Rel x y :=
  ⟨(List.dropLast_prefix x).trans h, hl, fun h' => absurd h h'⟩

theorem lemma1Holds_of_prefix {x y : Word} (h : x <+: y) (hl : y.length ≤ x.length + 6) :
    Lemma1Holds x y := by
  refine ⟨fun _ => lemma1Rel_of_prefix h hl, fun h2 => ?_⟩
  have := h.eq_of_length (le_antisymm h.length_le h2)
  subst this
  exact lemma1Rel_of_prefix (List.prefix_refl _) (by omega)

theorem Lemma1Holds.symm {x y : Word} (h : Lemma1Holds x y) : Lemma1Holds y x := ⟨h.2, h.1⟩

theorem lemma1Holds_of_F {x y : Word} {sx : Bool} (h : F x y sx) : Lemma1Holds x y := by
  rcases h with rfl | ⟨w, rfl, -, h2⟩ | ⟨p, c, rfl, rfl⟩ | ⟨p, w, rfl, rfl, hw⟩ | ⟨w, rfl, -, h6, -⟩
  · exact lemma1Holds_of_prefix (List.prefix_refl x) (by omega)
  · exact lemma1Holds_of_prefix (prefix_append_self x w) (by simp; omega)
  · refine ⟨fun _ => ⟨by simp, by simp, fun _ => by simp⟩, fun h => by simp at h⟩
  · refine ⟨fun _ => ⟨by simp, by simp; omega, fun _ => by simp; omega⟩, fun h => ?_⟩
    have hw0 : w = [] := List.eq_nil_of_length_eq_zero (by
      simp only [List.length_append, List.length_cons, List.length_nil] at h; omega)
    subst hw0
    exact ⟨by simp, by simp, fun _ => by simp⟩
  · exact lemma1Holds_of_prefix (prefix_append_self x w) (by simp; omega)

/-- The five forms of [Casteigts et al.] imply the conclusion of Lemma 1. -/
theorem lemma1Holds_of_form {x y : Word} {sx sy : Bool} (h : Form x y sx sy) : Lemma1Holds x y :=
  h.elim lemma1Holds_of_F fun h => (lemma1Holds_of_F h).symm

/-- **Lemma 1** (beeping version of Lemma 8 of [5]), for Algorithm 1 with the deletion rule of
[Casteigts et al.] (largest deletion among rules 1 and 2): in every phase, the prefixes of two
neighbours `u` and `v` are identical except in at most 6 least significant bits, from the
`|prefix_u|`-th (possibly included) to the `|prefix_v|`-th bit (when `|prefix_u| ≤ |prefix_v|`), and
if the `|prefix_u|`-th bit differs then `|prefix_v| - |prefix_u| < 6`. Holds for every graph and every
identifier assignment. -/
theorem lemma_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (ident : V → ℕ) (t : ℕ) {u v : V} (huv : G.Adj u v) :
    Lemma1Holds (run G .maxDelete ident t u).pre (run G .maxDelete ident t v).pre :=
  lemma1Holds_of_form ((invariants G ident t).1 u v huv)

end Podc.BeepingLeaderElection
