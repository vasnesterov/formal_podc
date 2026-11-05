import Papers.PODC2023.DuraCAS.AActor

/-!
# The global invariant of the A-level proof

Ghost state `Gh`: a step counter `clk`, the step `evT i` of the `i`-th history event, the keyed
linearization `L` (see `ALin.lean`), the invocation step `it p` and witness step `wit p` of the
current operation of each process, and the per-object ghost variables `pw`, `zAt`, `lm`.

`GInv init a g` collects the per-object and per-process invariants of `AInv.lean` with the
bookkeeping that relates `L` to the history; `GInv.durLinDet` derives durable linearizability
and detectability of the history from it (Lemmas A.44 and A.45).
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

variable (P K V) in
/-- Ghost state. -/
structure Gh where
  clk : ℕ
  evT : ℕ → ℕ
  L : List (GE K V)
  it : P → ℕ
  wit : P → Option ℕ
  pw : K → Option ℕ
  zAt : K → ℕ
  lm : K → Bool

/-- The view of object `k`. -/
def view (init : K → V) (a : AS P K V) (g : Gh P K V) (k : K) : KV V :=
  ⟨a.Y (k, .W), a.Y (k, .Z), g.pw k, g.zAt k, g.lm k, curSt init g.L k⟩

/-- The view of process `p` executing `r`. -/
def pview (a : AS P K V) (g : Gh P K V) (p : P) (r : OpRec K V) : PV P K V :=
  ⟨(a.ps p).pc, r, (a.ps p).orph, a.ls (p, .crit), g.wit p, r.id ∈ g.L.map GE.id⟩

/-- The `DETECT` value carried by an event ending an operation. -/
def Ev.dEnd : Ev P K V → ℕ
  | .ret _ _ d => d
  | .rdone _ d => d
  | _ => 0

/-- Invariants of the keyed linearization list alone. -/
structure LGood (init : K → V) (L : List (GE K V)) (clk : ℕ) : Prop where
  sorted : KSorted L
  nodup : (L.map GE.id).Nodup
  key_lt : ∀ e ∈ L, e.key < 4 * clk
  resp : RespOK init L
  rank0 : ∀ e ∈ L, e.key % 4 = 0 →
    e.op.IsWrite ∧ ∃ y ∈ L, y.key = e.key + 1 ∧ y.k = e.k ∧ y.op.IsWrite
  rank1 : ∀ e ∈ L, ∀ e' ∈ L, e.key = e'.key → e.key % 4 = 1 → e = e'

/-- The witness facts of a busy process. -/
def WitOK (init : K → V) (g : Gh P K V) (p : P) (r : OpRec K V) : Prop :=
  ∀ t, g.wit p = some t → g.it p ≤ t ∧ t < g.clk ∧
    (∀ old new, r.op = .cas old new → stAt init g.L t r.k ≠ old) ∧
    (∀ u, r.op = .write u → g.it p < t ∧ ∃ y ∈ g.L, y.key = 4 * t + 1 ∧ y.k = r.k ∧ y.op.IsWrite)

/-- The global invariant. -/
structure GInv (init : K → V) (a : AS P K V) (g : Gh P K V) : Prop where
  kinv : ∀ k, (view init a g k).Inv
  loc : ∀ p r, (a.ps p).op = some r → Loc p (view init a g r.k) (pview a g p r)
  idle : ∀ p, (a.ps p).op = none → (a.ps p).orph = none
  pw_ex : ∀ k id, g.pw k = some id → ∃ p r, (a.ps p).op = some r ∧ r.id = id ∧ r.k = k
  uniq : ∀ p q r s, (a.ps p).op = some r → (a.ps q).op = some s → r.id = s.id → p = q
  busy_nid : ∀ p r, (a.ps p).op = some r → r.id < a.nid
  busy_inv : ∀ p r, (a.ps p).op = some r →
    ∃ i, a.hist[i]? = some (Ev.inv r.id p r.k r.op r.d1) ∧ g.evT i = g.it p
  busy_end : ∀ p r, (a.ps p).op = some r → ∀ e ∈ a.hist, ¬ e.Ends r.id
  busy_it : ∀ p r, (a.ps p).op = some r → g.it p < g.clk
  wit : ∀ p r, (a.ps p).op = some r → WitOK init g p r
  act_rsp : ∀ p r, (a.ps p).op = some r → ∀ e ∈ g.L, e.id = r.id →
    e.k = r.k ∧ e.op = r.op ∧ e.rsp = .ok true
  lgood : LGood init g.L g.clk
  evT_mono : ∀ i j, i < j → j < a.hist.length → g.evT i < g.evT j
  evT_lt : ∀ i, i < a.hist.length → g.evT i < g.clk
  inv_lt : ∀ id p k op d, Ev.inv id p k op d ∈ a.hist → id < a.nid
  end_lt : ∀ e ∈ a.hist, ∀ id, e.Ends id → id < a.nid
  inv_idx : ∀ (i j : ℕ) id p k op d p' k' op' d', a.hist[i]? = some (Ev.inv id p k op d) →
    a.hist[j]? = some (Ev.inv id p' k' op' d') → i = j
  ent_inv : ∀ e ∈ g.L, ∃ i : ℕ, ∃ p d, a.hist[i]? = some (Ev.inv e.id p e.k e.op d)
  ent_invT : ∀ e ∈ g.L, ∀ i p k op d, a.hist[i]? = some (Ev.inv e.id p k op d) →
    4 * g.evT i + 2 < e.key
  ent_endT : ∀ e ∈ g.L, ∀ i ev, a.hist[i]? = some ev → ev.Ends e.id → e.key ≤ 4 * g.evT i + 2
  complete : ∀ id r d, Ev.ret id r d ∈ a.hist → ∃ e ∈ g.L, e.id = id ∧ e.rsp = r
  mono : ∀ id p k op d, Ev.inv id p k op d ∈ a.hist → ∀ ev ∈ a.hist, ev.Ends id → d ≤ ev.dEnd
  took : ∀ id p k op d, Ev.inv id p k op d ∈ a.hist → ∀ ev ∈ a.hist, ev.Ends id →
    d < ev.dEnd → ∃ e ∈ g.L, e.id = id ∧ e.rsp = .ok true
  noeff : ∀ id p k op d, Ev.inv id p k op d ∈ a.hist → Ev.rdone id d ∈ a.hist →
    id ∉ g.L.map GE.id

/-- The initial ghost state. -/
def gInit : Gh P K V := ⟨0, fun _ => 0, [], fun _ => 0, fun _ => none, fun _ => none, fun _ => 0,
  fun _ => false⟩

theorem gInv_init (init : K → V) : GInv init (ainit init : AS P K V) gInit := by
  refine ⟨fun k => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [view, ainit, gInit, KV.pend, curSt]
  all_goals first
    | exact ⟨List.Pairwise.nil, List.nodup_nil, by simp, trivial, by simp, by simp⟩
    | intro id p k op d h; simp [ainit] at h

/-! ### From the invariant to durable linearizability and detectability -/

theorem getElem?_of_mem {α : Type*} {L : List α} {x : α} (h : x ∈ L) : ∃ i : ℕ, L[i]? = some x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, by simp [hi]⟩

theorem ent_eq_of_id {L : List (GE K V)} (hn : (L.map GE.id).Nodup) {e e' : GE K V} (he : e ∈ L)
    (he' : e' ∈ L) (h : e.id = e'.id) : e = e' :=
  List.inj_on_of_nodup_map hn he he' h

theorem GInv.durLinDet {init : K → V} {a : AS P K V} {g : Gh P K V} (h : GInv init a g) :
    DurLinDet init a.hist := by
  have hL := h.lgood
  -- the op of an entry is the op of its invocation
  have hinv_op : ∀ e ∈ g.L, ∀ p k op d, Ev.inv e.id p k op d ∈ a.hist → k = e.k ∧ op = e.op := by
    intro e he p k op d hm
    obtain ⟨i, p', d', hi⟩ := h.ent_inv e he
    obtain ⟨j, hj⟩ := getElem?_of_mem hm
    have := h.inv_idx _ _ _ _ _ _ _ _ _ _ _ hi hj
    subst this
    rw [hi] at hj; simp only [Option.some.injEq, Ev.inv.injEq] at hj
    exact ⟨hj.2.2.1.symm, hj.2.2.2.1.symm⟩
  refine ⟨g.L.map GE.ent, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · have : (g.L.map GE.ent).map Prod.fst = g.L.map GE.id := by simp [Function.comp_def, GE.ent]
    rw [this]; exact hL.nodup
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    obtain ⟨i, p, d, hi⟩ := h.ent_inv e' he'
    exact ⟨p, d, List.mem_of_getElem? hi⟩
  · intro id r d hr
    obtain ⟨e, he, rfl, -⟩ := h.complete id r d hr
    simp only [List.map_map]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  · intro L₁ e L₂ hs r d hr
    obtain ⟨g', hg', hent, hresp⟩ := respOK_split hL.resp L₁ e L₂ hs
    obtain ⟨e', he', hid, hr'⟩ := h.complete _ _ _ hr
    have : g' = e' := ent_eq_of_id hL.nodup hg' he' (by rw [hid, ← hent]; rfl)
    subst this
    rw [hresp, hr']
  · intro x y hxy hx hy hne
    obtain ⟨ex, hex, rfl⟩ := List.mem_map.1 hx
    obtain ⟨ey, hey, rfl⟩ := List.mem_map.1 hy
    obtain ⟨i, j, hi, hj, hij, hend, p, k, op, d, hinv⟩ := hxy
    have h1 := h.ent_endT ex hex i _ (List.getElem?_eq_getElem hi) hend
    have h2 := h.ent_invT ey hey j p k op d (by rw [List.getElem?_eq_getElem hj, hinv]; rfl)
    have h3 := h.evT_mono i j hij hj
    exact (kSorted_sublist hL.sorted hex hey (by omega)).map _
  · intro id p k op d₁ r d₂ hi hr
    exact h.mono id p k op d₁ hi _ hr rfl
  · intro id p k op d₁ d₂ hi hr
    exact h.mono id p k op d₁ hi _ hr rfl
  · intro id p k op d₁ d₂ hi hend hlt
    have : ∃ ev ∈ a.hist, ev.Ends id ∧ ev.dEnd = d₂ := by
      rcases hend with hr | ⟨r, hr⟩
      · exact ⟨_, hr, rfl, rfl⟩
      · exact ⟨_, hr, rfl, rfl⟩
    obtain ⟨ev, hev, hends, hd⟩ := this
    obtain ⟨e, he, rfl, hok⟩ := h.took _ p k op d₁ hi ev hev hends (by rw [hd]; exact hlt)
    obtain ⟨hk, hop⟩ := hinv_op e he p k op d₁ hi
    subst hk hop
    obtain ⟨L₁, L₂, hs⟩ := List.append_of_mem (List.mem_map.2 ⟨e, he, rfl⟩ : e.ent ∈ g.L.map GE.ent)
    refine ⟨L₁, L₂, hs, ?_⟩
    obtain ⟨g', hg', hent, hresp⟩ := respOK_split hL.resp L₁ _ L₂ hs
    have : g' = e := ent_eq_of_id hL.nodup hg' he (congrArg Prod.fst hent)
    subst this
    rw [← hok]; exact hresp
  · intro id p k op d hi hr
    have := h.noeff id p k op d hi hr
    simpa [List.map_map, Function.comp_def, GE.ent] using this

end Podc.DuraCAS
