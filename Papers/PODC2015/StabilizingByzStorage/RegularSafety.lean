import Papers.PODC2015.StabilizingByzStorage.Regular

/-!
# Eventual regularity of Fig. 2 (Lemma 3)

Every read of the register of Fig. 2 that is invoked after some write has completed returns a
*regular* value: the value of the last write completed before the read was invoked, or of a write
invoked before the read returns and not completed when the read was invoked.

The proof is by an inductive invariant `Inv` over reachable states:
* bookkeeping of the ghost tags (`SInv`, per server);
* `Inv.sync`: after the `WRITE` of the current/last write `k - 1` ended (`k = kSync σ`), at least
  `n - 2t` correct servers have `last_val` set by a write `≥ k - 1` and only messages of writes
  `≥ k - 1` pending (`Ghost.Fresh`);
* `Inv.read`: during a read, at least `n - 2t` correct servers are fresh w.r.t. `base - 1` and all
  their recorded replies (and their `helping_val` once they delivered the `READ(true)`) are regular.
At the return step, `2t + 1` copies among `n - t` replies include one from such a server.

Main results: `lemma3_regular` (on the ghost history) and `lemma3_regular_exec` (on the labels of a
finite execution, with the regularity condition `RegularRead` of Section 2.2). No bound on `n`, `t`
or `|B|` is needed: the counting only uses `|Q| = n - t` and the `n - 2t` synchronized correct
servers of the guards.
-/

namespace Podc.StabilizingByzStorage.Regular

open Podc.StabilizingByzStorage

variable {n : ℕ} {V : Type}

/-! ### Predicates -/

/-- `x` is the value of a write of index `≥ base - 1` (a regular value for a read with `base ≥ 1`). -/
def Reg (vals : List V) (base : ℕ) (x : V) : Prop := ∃ j, base - 1 ≤ j ∧ vals[j]? = some x

lemma Reg.append {vals : List V} {base : ℕ} {x : V} (l : List V) (h : Reg vals base x) :
    Reg (vals ++ l) base x := by
  obtain ⟨j, hj, hx⟩ := h
  refine ⟨j, hj, ?_⟩
  have : j < vals.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hx; exact absurd hx (by simp)
  rw [List.getElem?_append_left this, hx]

/-- The writer is between lines 01 and 02 (`WRITE(v)` broadcast, not yet followed by anything). -/
def WPhase.writing : WPhase V → Bool
  | .bcastWrite _ => true
  | .waitAck _ => true
  | _ => false

/-- The `WRITE` broadcast of the current write has ended. -/
def WPhase.afterWrite : WPhase V → Bool
  | .waitAck _ => true
  | .bcastHelp => true
  | _ => false

/-- Number of writes whose `WRITE` broadcast has ended. -/
def kSync (σ : State n V) : ℕ := if σ.w.afterWrite then σ.vals.length else σ.nDone

/-- A pending writer message tagged with write `k` is `WRITE(vals[k])` or `NEW_HELP_VAL(vals[k])`. -/
def WOk (vals : List V) (tg : Option ℕ) (m : WMsg V) : Prop :=
  ∀ k, tg = some k → ∃ d, vals[k]? = some d ∧ (m = .write d ∨ m = .newHelp d)

/-- Tag of a pending reader message is consistent with its content. -/
def ROk (tg : Option Bool) (b : Bool) : Prop := tg = none ∨ tg = some b

/-- Shape of the reader tags during a read: older messages, then (if not delivered) the
`READ(true)`, then the `READ(false)`s. -/
def RShape (g : Ghost) : Prop :=
  (g.rtd = false ∧ ∃ a b, g.rtags = List.replicate a none ++ some true :: List.replicate b (some false)) ∨
  (g.rtd = true ∧ ∃ b, g.rtags = List.replicate b (some false))

/-- `last_val` was set by a write `≥ j` and all pending writer messages come from writes `≥ j`. -/
def Ghost.Fresh (g : Ghost) (j : ℕ) : Prop :=
  (∃ j', j ≤ j' ∧ g.lastTag = some j') ∧ ∀ tg ∈ g.wtags, ∃ k, tg = some k ∧ j ≤ k

/-- Per-server bookkeeping invariant. -/
structure SInv (vals : List V) (w : WPhase V) (r : RPhase) (sv : Server V) (g : Ghost) : Prop where
  wtags : List.Forall₂ (WOk vals) g.wtags sv.wq
  lastTag : ∀ k, g.lastTag = some k → vals[k]? = some sv.last
  rtags : List.Forall₂ ROk g.rtags sv.rq
  shape : r ≠ .idle → RShape g
  writing : w.writing → (sv.wq = [] ∧ g.lastTag = some (vals.length - 1)) ∨
    (g.wtags.getLast? = some (some (vals.length - 1)) ∧ ∃ d, sv.wq.getLast? = some (.write d))

/-- A server whose state guarantees regular replies for the current read. -/
structure RGood (vals : List V) (base : ℕ) (sv : Server V) (g : Ghost) : Prop where
  fresh : g.Fresh (base - 1)
  help : g.rtd = true → ∀ x, sv.help = some x → Reg vals base x
  rack : ∀ l h, sv.rack = some (l, h) → Reg vals base l ∧ ∀ x, h = some x → Reg vals base x


/-! ### Server-level lemmas -/

namespace Ghost

lemma Fresh.mono {g : Ghost} {i j : ℕ} (h : g.Fresh j) (hij : i ≤ j) : g.Fresh i := by
  obtain ⟨⟨j', hj', hl⟩, hw⟩ := h
  refine ⟨⟨j', by omega, hl⟩, fun tg htg => ?_⟩
  obtain ⟨k, rfl, hk⟩ := hw tg htg
  exact ⟨k, rfl, by omega⟩

lemma Fresh.deliverW {g : Ghost} {j : ℕ} (h : g.Fresh j) (b : Bool) : (g.deliverW b).Fresh j := by
  obtain ⟨⟨j', hj', hl⟩, hw⟩ := h
  unfold Ghost.deliverW
  rcases hg : g.wtags with _ | ⟨tg, rest⟩
  · exact ⟨⟨j', hj', hl⟩, by simp [hg] at hw ⊢⟩
  · rw [hg] at hw
    have hrest : ∀ tg ∈ rest, ∃ k, tg = some k ∧ j ≤ k := fun tg h => hw tg (by simp [h])
    cases b
    · exact ⟨⟨j', hj', hl⟩, hrest⟩
    · obtain ⟨k, rfl, hk⟩ := hw tg (by simp)
      exact ⟨⟨k, hk, rfl⟩, hrest⟩

lemma Fresh.append {g : Ghost} {j k : ℕ} (h : g.Fresh j) (hk : j ≤ k) :
    ({ g with wtags := g.wtags ++ [some k] } : Ghost).Fresh j := by
  obtain ⟨hl, hw⟩ := h
  refine ⟨hl, fun tg htg => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at htg
  rcases htg with htg | rfl
  · exact hw tg htg
  · exact ⟨k, rfl, hk⟩

end Ghost

lemma Server.deliverW_write {sv : Server V} {d : V} {rest : List (WMsg V)}
    (h : sv.wq = .write d :: rest) :
    sv.deliverW =
      { sv with last := d, wq := rest, wack := if rest = [] then some sv.help else sv.wack } := by
  unfold Server.deliverW; rw [h]

lemma Server.deliverW_newHelp {sv : Server V} {d : V} {rest : List (WMsg V)}
    (h : sv.wq = .newHelp d :: rest) :
    sv.deliverW = { sv with help := some d, wq := rest } := by
  unfold Server.deliverW; rw [h]

lemma Server.deliverR_cons {sv : Server V} {b : Bool} {rest : List Bool} (h : sv.rq = b :: rest) :
    sv.deliverR =
      { sv with help := if b then none else sv.help, rq := rest,
                rack := if rest = [] then some (sv.last, if b then none else sv.help) else sv.rack } := by
  unfold Server.deliverR; rw [h]

lemma Ghost.deliverW_cons {g : Ghost} {tg : Option ℕ} {rest : List (Option ℕ)}
    (h : g.wtags = tg :: rest) (b : Bool) :
    g.deliverW b = if b then { g with wtags := rest, lastTag := tg }
      else { g with wtags := rest, helpTag := tg } := by
  unfold Ghost.deliverW; rw [h]

lemma Ghost.deliverR_cons {g : Ghost} {tg : Option Bool} {rest : List (Option Bool)}
    (h : g.rtags = tg :: rest) (b : Bool) :
    g.deliverR b =
      { g with rtags := rest, helpTag := if b then none else g.helpTag,
               rtd := if tg = some true then true else g.rtd } := by
  unfold Ghost.deliverR; rw [h]

lemma WOk.mono {vals : List V} {tg : Option ℕ} {m : WMsg V} (h : WOk vals tg m) (l : List V) :
    WOk (vals ++ l) tg m := by
  intro k hk
  obtain ⟨d, hd, hm⟩ := h k hk
  have : k < vals.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hd; exact absurd hd (by simp)
  exact ⟨d, by rw [List.getElem?_append_left this, hd], hm⟩

lemma getElem?_append_of_eq {vals : List V} {k : ℕ} {x : V} (h : vals[k]? = some x) (l : List V) :
    (vals ++ l)[k]? = some x := by
  have : k < vals.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; exact absurd h (by simp)
  rw [List.getElem?_append_left this, h]

lemma RShape.deliverR {g : Ghost} {tg : Option Bool} {rest : List (Option Bool)}
    (hs : RShape g) (h : g.rtags = tg :: rest) (b : Bool) : RShape (g.deliverR b) := by
  rw [Ghost.deliverR_cons h]
  rcases hs with ⟨hr, a, c, hrt⟩ | ⟨hr, c, hrt⟩
  · rw [h] at hrt
    cases a with
    | zero =>
      simp only [List.replicate_zero, List.nil_append, List.cons.injEq] at hrt
      obtain ⟨rfl, rfl⟩ := hrt
      exact Or.inr ⟨by simp, c, rfl⟩
    | succ a =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at hrt
      obtain ⟨rfl, rfl⟩ := hrt
      exact Or.inl ⟨by simp [hr], a, c, rfl⟩
  · rw [h] at hrt
    cases c with
    | zero => simp at hrt
    | succ c =>
      simp only [List.replicate_succ, List.cons.injEq] at hrt
      obtain ⟨rfl, rfl⟩ := hrt
      exact Or.inr ⟨by simp [hr], c, rfl⟩

lemma SInv.deliverW {vals : List V} {w : WPhase V} {r : RPhase} {sv : Server V} {g : Ghost}
    (h : SInv vals w r sv g) (hq : sv.wq ≠ []) :
    SInv vals w r sv.deliverW (g.deliverW (headIsWrite sv)) := by
  obtain ⟨m, rest, hm⟩ := List.exists_cons_of_ne_nil hq
  obtain ⟨tg, rtg, hok, hrest, hg⟩ := List.forall₂_cons_right_iff.1 (hm ▸ h.wtags)
  rw [Ghost.deliverW_cons hg]
  obtain ⟨hw, hl, hr, hsh, hwr⟩ := h
  cases m with
  | write d =>
    rw [Server.deliverW_write hm]
    have hhd : headIsWrite sv = true := by simp [headIsWrite, hm]
    simp only [hhd, ↓reduceIte]
    refine ⟨hrest, ?_, hr, hsh, ?_⟩
    · intro k hk
      obtain ⟨d', hd', hm'⟩ := hok k hk
      simp only [WMsg.write.injEq, reduceCtorEq, or_false] at hm'
      subst hm'; exact hd'
    · intro hwt
      rcases hwr hwt with ⟨hnil, _⟩ | ⟨hlt, d', hld⟩
      · simp [hm] at hnil
      · rcases rest with _ | ⟨m', rest'⟩
        · obtain rfl : rtg = [] := List.forall₂_nil_right_iff.1 hrest
          refine Or.inl ⟨rfl, ?_⟩
          simpa [hg] using hlt
        · obtain ⟨tg', rtg', -, -, rfl⟩ := List.forall₂_cons_right_iff.1 hrest
          refine Or.inr ⟨?_, d', ?_⟩
          · rwa [hg, List.getLast?_cons_cons] at hlt
          · rwa [hm, List.getLast?_cons_cons] at hld
  | newHelp d =>
    rw [Server.deliverW_newHelp hm]
    have hhd : headIsWrite sv = false := by simp [headIsWrite, hm]
    simp only [hhd, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hrest, hl, hr, hsh, ?_⟩
    intro hwt
    rcases hwr hwt with ⟨hnil, _⟩ | ⟨hlt, d', hld⟩
    · simp [hm] at hnil
    · rcases rest with _ | ⟨m', rest'⟩
      · simp [hm] at hld
      · obtain ⟨tg', rtg', -, -, rfl⟩ := List.forall₂_cons_right_iff.1 hrest
        refine Or.inr ⟨?_, d', ?_⟩
        · rwa [hg, List.getLast?_cons_cons] at hlt
        · rwa [hm, List.getLast?_cons_cons] at hld

lemma SInv.deliverR {vals : List V} {w : WPhase V} {r : RPhase} {sv : Server V} {g : Ghost}
    (h : SInv vals w r sv g) (hq : sv.rq ≠ []) :
    SInv vals w r sv.deliverR (g.deliverR (headR sv)) := by
  obtain ⟨b, rest, hm⟩ := List.exists_cons_of_ne_nil hq
  obtain ⟨tg, rtg, hok, hrest, hg⟩ := List.forall₂_cons_right_iff.1 (hm ▸ h.rtags)
  have hsh' : r ≠ .idle → RShape (g.deliverR (headR sv)) := fun hr => (h.shape hr).deliverR hg _
  rw [Ghost.deliverR_cons hg, Server.deliverR_cons hm] at *
  obtain ⟨hw, hl, hr, hsh, hwr⟩ := h
  exact ⟨hw, hl, hrest, hsh', hwr⟩

lemma RShape.singleton {g : Ghost} {tg : Option Bool} (hs : RShape g) (h : g.rtags = [tg]) :
    tg = some true ∨ (tg = some false ∧ g.rtd = true) := by
  rcases hs with ⟨-, a, c, hrt⟩ | ⟨hr, c, hrt⟩
  · rw [h] at hrt
    have hl := congrArg List.length hrt
    simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate] at hl
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by omega
    simp only [List.replicate_zero, List.nil_append, List.cons.injEq, and_true] at hrt
    exact Or.inl hrt
  · rw [h] at hrt
    have hl := congrArg List.length hrt
    simp only [List.length_cons, List.length_nil, List.length_replicate] at hl
    subst hl
    simp only [zero_add, List.replicate_one, List.cons.injEq, and_true] at hrt
    exact Or.inr ⟨hrt, hr⟩

lemma RGood.deliverW {vals : List V} {base : ℕ} {w : WPhase V} {r : RPhase} {sv : Server V}
    {g : Ghost} (h : RGood vals base sv g) (hs : SInv vals w r sv g) (hq : sv.wq ≠ []) :
    RGood vals base sv.deliverW (g.deliverW (headIsWrite sv)) := by
  have hf := h.fresh.deliverW (headIsWrite sv)
  obtain ⟨m, rest, hm⟩ := List.exists_cons_of_ne_nil hq
  obtain ⟨tg, rtg, hok, -, hg⟩ := List.forall₂_cons_right_iff.1 (hm ▸ hs.wtags)
  rw [Ghost.deliverW_cons hg] at hf ⊢
  obtain ⟨hfr, hh, hra⟩ := h
  cases m with
  | write d =>
    rw [Server.deliverW_write hm]
    have hhd : headIsWrite sv = true := by simp [headIsWrite, hm]
    simp only [hhd, ↓reduceIte] at hf ⊢
    exact ⟨hf, hh, hra⟩
  | newHelp d =>
    rw [Server.deliverW_newHelp hm]
    have hhd : headIsWrite sv = false := by simp [headIsWrite, hm]
    simp only [hhd, Bool.false_eq_true, ↓reduceIte] at hf ⊢
    refine ⟨hf, ?_, hra⟩
    intro _ x hx
    simp only [Option.some.injEq] at hx
    subst hx
    obtain ⟨k, rfl, hk⟩ := hfr.2 tg (by simp [hg])
    obtain ⟨d', hd', hm'⟩ := hok k rfl
    simp only [reduceCtorEq, WMsg.newHelp.injEq, false_or] at hm'
    subst hm'
    exact ⟨k, hk, hd'⟩

lemma RGood.deliverR {vals : List V} {base : ℕ} {w : WPhase V} {r : RPhase} {sv : Server V}
    {g : Ghost} (h : RGood vals base sv g) (hs : SInv vals w r sv g) (hsh : RShape g)
    (hq : sv.rq ≠ []) :
    RGood vals base sv.deliverR (g.deliverR (headR sv)) := by
  obtain ⟨b, rest, hm⟩ := List.exists_cons_of_ne_nil hq
  obtain ⟨tg, rtg, hok, hrest, hg⟩ := List.forall₂_cons_right_iff.1 (hm ▸ hs.rtags)
  have hb : headR sv = b := by simp [headR, hm]
  rw [Ghost.deliverR_cons hg, Server.deliverR_cons hm, hb]
  obtain ⟨⟨⟨j', hj', hlt⟩, hwt⟩, hh, hra⟩ := h
  have hlast : Reg vals base sv.last := ⟨j', hj', hs.lastTag j' hlt⟩
  refine ⟨⟨⟨j', hj', hlt⟩, hwt⟩, ?_, ?_⟩
  · intro hr x hx
    cases b
    · have : tg ≠ some true := by rcases hok with rfl | rfl <;> simp
      simp only [this, ↓reduceIte] at hr
      exact hh hr x (by simpa using hx)
    · simp at hx
  · intro l h' hra'
    by_cases hnil : rest = []
    · simp only [hnil, ↓reduceIte] at hra'
      subst hnil
      obtain rfl : rtg = [] := List.forall₂_nil_right_iff.1 hrest
      simp only [Option.some.injEq, Prod.mk.injEq] at hra'
      obtain ⟨rfl, rfl⟩ := hra'
      refine ⟨hlast, fun x hx => ?_⟩
      rcases hsh.singleton hg with rfl | ⟨rfl, hr⟩
      · rcases hok with h1 | h1 <;> simp at h1; subst h1; simp at hx
      · rcases hok with h1 | h1 <;> simp at h1; subst h1
        exact hh hr x (by simpa using hx)
    · simp only [hnil, ↓reduceIte] at hra'
      exact hra l h' hra'

lemma Ghost.Fresh.deliverR {g : Ghost} {j : ℕ} (h : g.Fresh j) (b : Bool) :
    (g.deliverR b).Fresh j := by
  unfold Ghost.deliverR
  rcases g.rtags with _ | ⟨tg, rest⟩
  · exact h
  · exact h

lemma RShape.append {g : Ghost} (h : RShape g) :
    RShape { g with rtags := g.rtags ++ [some false] } := by
  rcases h with ⟨hr, a, c, hrt⟩ | ⟨hr, c, hrt⟩
  · refine Or.inl ⟨hr, a, c + 1, ?_⟩
    simp [hrt, List.replicate_succ']
  · refine Or.inr ⟨hr, c + 1, ?_⟩
    simp [hrt, List.replicate_succ']

lemma RGood.mono_vals {vals : List V} {base : ℕ} {sv : Server V} {g : Ghost}
    (h : RGood vals base sv g) (l : List V) : RGood (vals ++ l) base sv g :=
  ⟨h.fresh, fun hr x hx => (h.help hr x hx).append l,
    fun a b hab => ⟨(h.rack a b hab).1.append l, fun x hx => ((h.rack a b hab).2 x hx).append l⟩⟩

lemma RGood.bcastW {vals : List V} {base : ℕ} {sv : Server V} {g : Ghost}
    (h : RGood vals base sv g) (m : WMsg V) {k : ℕ} (hk : base - 1 ≤ k) :
    RGood vals base (sv.bcastW m) { g with wtags := g.wtags ++ [some k] } :=
  ⟨h.fresh.append hk, h.help, h.rack⟩

lemma RGood.bcastR {vals : List V} {base : ℕ} {sv : Server V} {g : Ghost}
    (h : RGood vals base sv g) (b : Bool) :
    RGood vals base (sv.bcastR b) { g with rtags := g.rtags ++ [some false] } :=
  ⟨h.fresh, h.help, fun l h' hr => by simp [Server.bcastR] at hr⟩

/-- Among the `n - t` members of `Q`, a value with `2t + 1` copies has one from `S`
(`|S| ≥ n - 2t`). -/
lemma exists_mem_of_cnt {α : Type} [DecidableEq α] {t : ℕ} {S Q : Finset (Fin n)}
    {f : Fin n → α} {a : α} (hS : n - 2 * t ≤ S.card) (hQ : Q.card = n - t)
    (hc : 2 * t + 1 ≤ cnt Q f a) : ∃ s ∈ Q, s ∈ S ∧ f s = a := by
  set F := Q.filter fun s => f s = a
  have hF : F.card ≤ Q.card := Finset.card_filter_le _ _
  have hu := Finset.card_union_add_card_inter F S
  have hle : (F ∪ S).card ≤ n := by
    simpa using Finset.card_le_univ (F ∪ S)
  have hc' : 2 * t + 1 ≤ F.card := hc
  obtain ⟨s, hs⟩ : (F ∩ S).Nonempty := by
    rw [← Finset.card_pos]; omega
  simp only [Finset.mem_inter, F, Finset.mem_filter] at hs
  exact ⟨s, hs.1.1, hs.2, hs.1.2⟩

variable (t : ℕ) (B : Finset (Fin n))

/-- The inductive invariant. -/
structure Inv (σ : State n V) : Prop where
  done : σ.w = .idle → σ.nDone = σ.vals.length
  done' : σ.w ≠ .idle → σ.nDone + 1 = σ.vals.length
  wval : ∀ v, (σ.w = .bcastWrite v ∨ σ.w = .waitAck v) → σ.vals[σ.vals.length - 1]? = some v
  base : σ.r ≠ .idle → σ.base ≤ σ.nDone
  srv : ∀ s, SInv σ.vals σ.w σ.r (σ.srv s) (σ.g s)
  sync : 1 ≤ kSync σ → ∃ S : Finset (Fin n), n - 2 * t ≤ S.card ∧
    ∀ s ∈ S, s ∉ B ∧ (σ.g s).Fresh (kSync σ - 1)
  read : σ.r ≠ .idle → 1 ≤ σ.base → ∃ S : Finset (Fin n), n - 2 * t ≤ S.card ∧
    ∀ s ∈ S, s ∉ B ∧ RGood σ.vals σ.base (σ.srv s) (σ.g s)


lemma inv_init {σ : State n V} (h : Init σ) : Inv t B σ := by
  obtain ⟨hw, hr, hv, hd, hg⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hv, hd]
  · simp [hw]
  · intro v hv'; rw [hw] at hv'; simp at hv'
  · simp [hr]
  · intro s
    obtain ⟨h1, h2, h3, -⟩ := hg s
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, List.forall₂_map_left_iff]
      exact List.forall₂_same.2 fun _ _ k hk => by simp at hk
    · simp [h3]
    · rw [h2, List.forall₂_map_left_iff]
      exact List.forall₂_same.2 fun _ _ => Or.inl rfl
    · simp [hr]
    · simp [hw, WPhase.writing]
  · simp [kSync, hw, WPhase.afterWrite, hd]
  · simp [hr]

variable [DecidableEq V]

lemma inv_step {σ σ' : State n V} {ℓ : Label V} (h : Inv t B σ) (hs : Step t B σ ℓ σ') :
    Inv t B σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  cases hs with
  | delivW s hq =>
    refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
    · intro s'
      rcases eq_or_ne s' s with rfl | hne
      · simpa using (h5 s').deliverW hq
      · simpa [hne] using h5 s'
    · intro hk
      obtain ⟨S, hS, hS'⟩ := h6 hk
      refine ⟨S, hS, fun s' hs' => ⟨(hS' s' hs').1, ?_⟩⟩
      rcases eq_or_ne s' s with rfl | hne
      · simp only [Function.update_self]; exact (hS' s' hs').2.deliverW _
      · simp only [Function.update_of_ne hne]; exact (hS' s' hs').2
    · intro hr hb
      obtain ⟨S, hS, hS'⟩ := h7 hr hb
      refine ⟨S, hS, fun s' hs' => ⟨(hS' s' hs').1, ?_⟩⟩
      rcases eq_or_ne s' s with rfl | hne
      · simpa using (hS' s' hs').2.deliverW (h5 s') hq
      · simpa [hne] using (hS' s' hs').2
  | delivR s hq =>
    refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
    · intro s'
      rcases eq_or_ne s' s with rfl | hne
      · simpa using (h5 s').deliverR hq
      · simpa [hne] using h5 s'
    · intro hk
      obtain ⟨S, hS, hS'⟩ := h6 hk
      refine ⟨S, hS, fun s' hs' => ⟨(hS' s' hs').1, ?_⟩⟩
      rcases eq_or_ne s' s with rfl | hne
      · simp only [Function.update_self]; exact (hS' s' hs').2.deliverR _
      · simp only [Function.update_of_ne hne]; exact (hS' s' hs').2
    · intro hr hb
      obtain ⟨S, hS, hS'⟩ := h7 hr hb
      refine ⟨S, hS, fun s' hs' => ⟨(hS' s' hs').1, ?_⟩⟩
      rcases eq_or_ne s' s with rfl | hne
      · simpa using (hS' s' hs').2.deliverR (h5 s') ((h5 s').shape hr) hq
      · simpa [hne] using (hS' s' hs').2
  | invWrite v hw =>
    have hd := h1 hw
    refine ⟨by simp, by simp [hd], by simp, h4, ?_, ?_, ?_⟩
    · intro s
      obtain ⟨hw', hl, hr', hsh, -⟩ := h5 s
      refine ⟨?_, fun k hk => getElem?_append_of_eq (hl k hk) _, hr', hsh, ?_⟩
      · simp only [Server.bcastW]
        exact List.rel_append (hw'.imp fun _ _ h => h.mono _)
          (List.Forall₂.cons (fun k hk => ⟨v, by simp_all, Or.inl rfl⟩) .nil)
      · intro _; right; simp [Server.bcastW]
    · simp only [kSync, hw, WPhase.afterWrite, Bool.false_eq_true, ↓reduceIte] at h6 ⊢
      intro hk
      obtain ⟨S, hS, hS'⟩ := h6 hk
      exact ⟨S, hS, fun s hs => ⟨(hS' s hs).1, (hS' s hs).2.append (by omega)⟩⟩
    · intro hr hb
      obtain ⟨S, hS, hS'⟩ := h7 hr hb
      have := h4 hr
      exact ⟨S, hS, fun s hs => ⟨(hS' s hs).1, ((hS' s hs).2.mono_vals _).bcastW _ (by omega)⟩⟩
  | endWrite v hw hsync =>
    refine ⟨by simp, fun _ => h2 (by simp [hw]), ?_, h4, ?_, ?_, h7⟩
    · intro v' hv'
      simp only [reduceCtorEq, WPhase.waitAck.injEq, false_or] at hv'
      subst hv'; exact h3 v (Or.inl hw)
    · intro s
      obtain ⟨a, b, c, d, e⟩ := h5 s
      exact ⟨a, b, c, d, fun _ => e (by simp [hw, WPhase.writing])⟩
    · intro _
      refine ⟨Finset.univ.filter fun s => s ∉ B ∧ (σ.srv s).wq = [], hsync, fun s hs => ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      refine ⟨hs.1, ?_⟩
      have hnil : (σ.g s).wtags = [] := List.forall₂_nil_right_iff.1 (hs.2 ▸ (h5 s).wtags)
      rcases (h5 s).writing (by simp [hw, WPhase.writing]) with ⟨-, hl⟩ | ⟨hl, -⟩
      · simp only [kSync, WPhase.afterWrite, ↓reduceIte]
        exact ⟨⟨_, le_rfl, hl⟩, by simp [hnil]⟩
      · simp [hnil] at hl
  | ackDone v hw Q acks hQ hacks hc =>
    have hk : σ.nDone + 1 = σ.vals.length := h2 (by simp [hw])
    refine ⟨fun _ => hk, fun h => absurd rfl h, by simp, fun hr => (h4 hr).trans (Nat.le_succ _),
      fun s => ?_, ?_, h7⟩
    · obtain ⟨a, b, c, d, -⟩ := h5 s
      exact ⟨a, b, c, d, fun h => by simp [WPhase.writing] at h⟩
    · simp only [kSync, hw, WPhase.afterWrite, ↓reduceIte, Bool.false_eq_true] at h6 ⊢
      rw [hk]; exact h6
  | ackHelp v hw Q acks hQ hacks hc =>
    have hk : σ.nDone + 1 = σ.vals.length := h2 (by simp [hw])
    refine ⟨by simp, fun _ => hk, by simp, h4, ?_, ?_, ?_⟩
    · intro s
      obtain ⟨hw', hl, hr', hsh, -⟩ := h5 s
      refine ⟨?_, hl, hr', hsh, by simp [WPhase.writing]⟩
      simp only [Server.bcastW]
      refine List.rel_append hw' (List.Forall₂.cons (fun k hk' => ⟨v, ?_, Or.inr rfl⟩) .nil)
      simp only [Option.some.injEq] at hk'
      subst hk'; exact h3 v (Or.inr hw)
    · simp only [kSync, hw, WPhase.afterWrite, ↓reduceIte] at h6 ⊢
      intro hk1
      obtain ⟨S, hS, hS'⟩ := h6 hk1
      exact ⟨S, hS, fun s hs => ⟨(hS' s hs).1, (hS' s hs).2.append le_rfl⟩⟩
    · intro hr hb
      obtain ⟨S, hS, hS'⟩ := h7 hr hb
      have := h4 hr
      exact ⟨S, hS, fun s hs => ⟨(hS' s hs).1, (hS' s hs).2.bcastW _ (by omega)⟩⟩
  | endHelp hw hsync =>
    have hk : σ.nDone + 1 = σ.vals.length := h2 (by simp [hw])
    refine ⟨fun _ => hk, fun h => absurd rfl h, by simp, fun hr => (h4 hr).trans (Nat.le_succ _),
      fun s => ?_, ?_, h7⟩
    · obtain ⟨a, b, c, d, -⟩ := h5 s
      exact ⟨a, b, c, d, fun h => by simp [WPhase.writing] at h⟩
    · simp only [kSync, hw, WPhase.afterWrite, ↓reduceIte, Bool.false_eq_true] at h6 ⊢
      rw [hk]; exact h6
  | invRead hr =>
    refine ⟨h1, h2, h3, fun _ => le_rfl, ?_, h6, ?_⟩
    · intro s
      obtain ⟨hw', hl, hr', -, hwr⟩ := h5 s
      refine ⟨hw', hl, ?_, fun _ => Or.inl ⟨rfl, (σ.g s).rtags.length, 0, by simp⟩, hwr⟩
      simp only [Server.bcastR]
      refine List.rel_append ?_ (List.Forall₂.cons (Or.inr rfl) .nil)
      rw [List.forall₂_map_left_iff]
      exact hr'.imp fun _ _ _ => Or.inl rfl
    · intro _ hb
      have hb' : 1 ≤ σ.nDone := hb
      have hk : σ.nDone ≤ kSync σ := by
        unfold kSync
        split_ifs with ha
        · have : σ.w ≠ .idle := by intro h; simp [h, WPhase.afterWrite] at ha
          have := h2 this; omega
        · exact le_rfl
      obtain ⟨S, hS, hS'⟩ := h6 (by omega)
      exact ⟨S, hS, fun s hs => ⟨(hS' s hs).1, ⟨(hS' s hs).2.mono (show σ.nDone - 1 ≤ kSync σ - 1 by omega),
        fun h => by simp at h, fun l h' hr => by simp [Server.bcastR] at hr⟩⟩⟩
  | endLoop hr hsync =>
    refine ⟨h1, h2, h3, fun _ => h4 (by simp [hr]), fun s => ?_, h6,
      fun _ hb => h7 (by simp [hr]) hb⟩
    obtain ⟨a, b, c, d, e⟩ := h5 s
    exact ⟨a, b, c, fun _ => d (by simp [hr]), e⟩
  | retLast hr Q reps hQ hreps v hd =>
    refine ⟨h1, h2, h3, fun h => absurd rfl h, fun s => ?_, h6, fun h => absurd rfl h⟩
    obtain ⟨a, b, c, d, e⟩ := h5 s
    exact ⟨a, b, c, fun h => absurd rfl h, e⟩
  | retHelp hr Q reps hQ hreps hl v hd =>
    refine ⟨h1, h2, h3, fun h => absurd rfl h, fun s => ?_, h6, fun h => absurd rfl h⟩
    obtain ⟨a, b, c, d, e⟩ := h5 s
    exact ⟨a, b, c, fun h => absurd rfl h, e⟩
  | retry hr Q reps hQ hreps hl hh =>
    refine ⟨h1, h2, h3, fun _ => h4 (by simp [hr]), fun s => ?_, h6, ?_⟩
    · obtain ⟨a, b, c, d, e⟩ := h5 s
      refine ⟨a, b, ?_, fun _ => (d (by simp [hr])).append, e⟩
      exact List.rel_append c (List.Forall₂.cons (Or.inr rfl) .nil)
    · intro _ hb
      obtain ⟨S, hS, hS'⟩ := h7 (by simp [hr]) hb
      exact ⟨S, hS, fun s hs => ⟨(hS' s hs).1, (hS' s hs).2.bcastR _⟩⟩

/-- The invariant holds in every state reachable from an initial state. -/
lemma inv_of_reach {σ₀ σ : State n V} (h0 : Init σ₀) (hr : Reach t B σ₀ σ) : Inv t B σ := by
  induction hr with
  | refl => exact inv_init t B h0
  | step _ hs ih => exact inv_step t B ih hs

/-- **Lemma 3** of [Bonomi, Dolev, Potop-Butucaru, Raynal, PODC 2015] (eventual regularity of the
register of Fig. 2). Every read invoked after some write completed (`1 ≤ base`) returns the value of
a write `j` that is either the last write completed before the read was invoked (`j = base - 1`)
or a write invoked before the read returns that had not completed when the read was invoked
(`j ≥ base`). This holds for every `n` and `t` (no bound on `|B|` is needed), whatever the replies of the
Byzantine servers `B`, starting from arbitrary server states and links (`Init`). -/
theorem lemma3_regular {σ₀ σ σ' : State n V} {v : V} (h0 : Init σ₀)
    (hr : Reach t B σ₀ σ) (hs : Step t B σ (.retRead v) σ') (hb : 1 ≤ σ.base) :
    ∃ j, σ.base - 1 ≤ j ∧ ∃ hj : j < σ.vals.length, σ.vals[j] = v := by
  have hI := inv_of_reach t B h0 hr
  suffices h : Reg σ.vals σ.base v by
    obtain ⟨j, hj, hv⟩ := h
    obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.1 hv
    exact ⟨j, hj, hlt, hv⟩
  cases hs with
  | retLast hr Q reps hQ hreps v hd =>
    obtain ⟨S, hS, hS'⟩ := hI.read (by simp [hr]) hb
    obtain ⟨s, hsQ, hsS, rfl⟩ := exists_mem_of_cnt hS hQ hd
    obtain ⟨hsB, hg⟩ := hS' s hsS
    exact (hg.rack _ _ (hreps s hsQ hsB)).1
  | retHelp hr Q reps hQ hreps hl v hd =>
    obtain ⟨S, hS, hS'⟩ := hI.read (by simp [hr]) hb
    obtain ⟨s, hsQ, hsS, hv⟩ := exists_mem_of_cnt hS hQ hd
    obtain ⟨hsB, hg⟩ := hS' s hsS
    exact (hg.rack _ _ (hreps s hsQ hsB)).2 v hv

/-! ### Lemma 3 in terms of the operations of an execution -/

section Labels

variable {V' : Type}

/-- The read invoked at event `i` returns `v` at event `j`. -/
def ReadOp (lab : ℕ → Label V') (i j : ℕ) (v : V') : Prop :=
  i < j ∧ lab i = .invRead ∧ lab j = .retRead v ∧ ∀ k, i < k → k < j → ∀ v', lab k ≠ .retRead v'

/-- The write of `v` is invoked at event `i` and returns at event `j`. -/
def WriteOp (lab : ℕ → Label V') (i j : ℕ) (v : V') : Prop :=
  i < j ∧ lab i = .invWrite v ∧ lab j = .retWrite ∧ ∀ k, i < k → k < j → lab k ≠ .retWrite

/-- Section 2.2: the read `[i, j]` returns a *regular* value `v`: written by the last write that
completed before the read, or by a write invoked before the read returns and not completed when
the read is invoked. -/
def RegularRead (lab : ℕ → Label V') (i j : ℕ) (v : V') : Prop :=
  (∃ a b, WriteOp lab a b v ∧ b < i ∧ ∀ k, b < k → k < i → lab k ≠ .retWrite) ∨
  (∃ a, a < j ∧ lab a = .invWrite v ∧ ∀ k, a < k → k ≤ i → lab k ≠ .retWrite)

/-- Is the label a write invocation? -/
def Label.isInvW : Label V' → Bool
  | .invWrite _ => true
  | _ => false

/-- Is the label a write return? -/
def Label.isRetW : Label V' → Bool
  | .retWrite => true
  | _ => false

/-- Number of events `< k` satisfying `p`. -/
def cntL (p : Label V' → Bool) (lab : ℕ → Label V') : ℕ → ℕ
  | 0 => 0
  | k + 1 => cntL p lab k + if p (lab k) then 1 else 0

variable {p : Label V' → Bool} {lab : ℕ → Label V'}

lemma cntL_mono {k k' : ℕ} (h : k ≤ k') : cntL p lab k ≤ cntL p lab k' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => simp only [cntL]; omega

lemma cntL_lt {k k' : ℕ} (h : k < k') (hp : p (lab k) = true) :
    cntL p lab k + 1 ≤ cntL p lab k' := by
  have := cntL_mono (p := p) (lab := lab) (Nat.succ_le_of_lt h)
  simp only [cntL, hp, ↓reduceIte] at this
  exact this

lemma cntL_succ_of_false {k : ℕ} (hp : p (lab k) = false) :
    cntL p lab (k + 1) = cntL p lab k := by
  simp [cntL, hp]

lemma exists_of_lt_cntL {m : ℕ} : ∀ {i : ℕ}, m < cntL p lab i →
    ∃ b < i, p (lab b) = true ∧ cntL p lab b = m
  | 0, h => by simp [cntL] at h
  | i + 1, h => by
    by_cases hm : m < cntL p lab i
    · obtain ⟨b, hb, hpb, hcb⟩ := exists_of_lt_cntL hm
      exact ⟨b, by omega, hpb, hcb⟩
    · simp only [cntL] at h
      split_ifs at h with hp
      · exact ⟨i, by omega, hp, by omega⟩
      · omega

end Labels

section Exec

variable {t B} {σ σ' : State n V} {ℓ : Label V}

/-- The value appended to `vals` by a step with label `ℓ`. -/
def Label.wval : Label V → List V
  | .invWrite v => [v]
  | _ => []

lemma Step.vals_eq (h : Step t B σ ℓ σ') :
    σ'.vals = σ.vals ++ ℓ.wval := by
  cases h <;> simp [Label.wval]

lemma Step.nDone_eq (h : Step t B σ ℓ σ') :
    σ'.nDone = σ.nDone + if ℓ.isRetW then 1 else 0 := by
  cases h <;> simp [Label.isRetW]

lemma Step.idle_of_invWrite {v : V} (h : Step t B σ (.invWrite v) σ') : σ.w = .idle := by
  cases h; assumption

lemma Step.busy_of_retWrite (h : Step t B σ .retWrite σ') : σ.w ≠ .idle := by
  cases h <;> simp_all

lemma Step.of_invRead (h : Step t B σ .invRead σ') :
    σ.r = .idle ∧ σ'.base = σ.nDone ∧ σ'.r ≠ .idle := by
  cases h; simp_all

lemma Step.base_eq (h : Step t B σ ℓ σ') (hℓ : ℓ ≠ .invRead) : σ'.base = σ.base := by
  cases h <;> simp_all

lemma Step.r_busy (h : Step t B σ ℓ σ') (hr : σ.r ≠ .idle) (hℓ : ∀ v, ℓ ≠ .retRead v) :
    σ'.r ≠ .idle := by
  cases h <;> simp_all

lemma Next.vals_eq (h : Next t B σ ℓ σ') : σ'.vals = σ.vals ++ ℓ.wval := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h.vals_eq
  · simp [Label.wval]

lemma Next.nDone_eq (h : Next t B σ ℓ σ') :
    σ'.nDone = σ.nDone + if ℓ.isRetW then 1 else 0 := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h.nDone_eq
  · simp [Label.isRetW]

lemma Next.base_eq (h : Next t B σ ℓ σ') (hℓ : ℓ ≠ .invRead) : σ'.base = σ.base := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h.base_eq hℓ
  · rfl

lemma Next.r_busy (h : Next t B σ ℓ σ') (hr : σ.r ≠ .idle) (hℓ : ∀ v, ℓ ≠ .retRead v) :
    σ'.r ≠ .idle := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact h.r_busy hr hℓ
  · exact hr

lemma Next.step (h : Next t B σ ℓ σ') (hℓ : ℓ ≠ .tau) : Step t B σ ℓ σ' := by
  rcases h with h | ⟨-, rfl⟩
  · exact h
  · exact absurd rfl hℓ

variable {σ : ℕ → State n V} {lab : ℕ → Label V} {N : ℕ}

lemma reach_of_exec (h0 : Init (σ 0)) (hexec : ∀ k < N, Next t B (σ k) (lab k) (σ (k + 1))) :
    ∀ k ≤ N, Reach t B (σ 0) (σ k)
  | 0, _ => .refl
  | k + 1, hk => by
    rcases hexec k (by omega) with hs | ⟨heq, -⟩
    · exact .step (reach_of_exec h0 hexec k (by omega)) hs
    · rw [heq]; exact reach_of_exec h0 hexec k (by omega)

/-- The ghost history agrees with the labels of the execution. -/
lemma ghost_of_exec (hexec : ∀ k < N, Next t B (σ k) (lab k) (σ (k + 1))) (h0 : Init (σ 0)) :
    ∀ k ≤ N, (σ k).vals.length = cntL Label.isInvW lab k ∧
      (σ k).nDone = cntL Label.isRetW lab k ∧
      ∀ m v, (σ k).vals[m]? = some v →
        ∃ a < k, lab a = .invWrite v ∧ cntL Label.isInvW lab a = m
  | 0, _ => by
    obtain ⟨-, -, hv, hd, -⟩ := h0
    simp [hv, hd, cntL]
  | k + 1, hk => by
    obtain ⟨h1, h2, h3⟩ := ghost_of_exec hexec h0 k (by omega)
    have hs := hexec k (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hs.vals_eq, cntL]
      cases lab k <;> simp [Label.isInvW, Label.wval, h1]
    · rw [hs.nDone_eq, cntL, h2]
    · intro m v hm
      rw [hs.vals_eq] at hm
      cases hl : lab k with
      | invWrite w =>
        rw [hl, Label.wval] at hm
        rw [List.getElem?_append] at hm
        split_ifs at hm with hlt
        · obtain ⟨a, ha, h⟩ := h3 m v hm
          exact ⟨a, by omega, h⟩
        · have hm' : m = (σ k).vals.length := by
            have := (List.getElem?_eq_some_iff.1 hm).1
            simp at this; omega
          subst hm'
          simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨k, by omega, hl, h1.symm⟩
      | _ =>
        simp only [hl, Label.wval, List.append_nil] at hm
        obtain ⟨a, ha, h⟩ := h3 m v hm
        exact ⟨a, by omega, h⟩

/-- **Lemma 3** of [Bonomi, Dolev, Potop-Butucaru, Raynal, PODC 2015], stated on the operations of
an execution: in an execution of Fig. 2 from an initial state (arbitrary servers and links), every
read invoked after the return of some write returns a regular value (Section 2.2). Hence the
register is eventually regular with `τ_stab` = the return of the first write. -/
theorem lemma3_regular_exec (h0 : Init (σ 0))
    (hexec : ∀ k < N, Next t B (σ k) (lab k) (σ (k + 1))) {i j : ℕ} {v : V} (hjN : j < N)
    (hread : ReadOp lab i j v) (hw : ∃ k < i, lab k = .retWrite) : RegularRead lab i j v := by
  obtain ⟨hij, hli, hlj, hnr⟩ := hread
  have hreach := reach_of_exec h0 hexec
  have hinv : ∀ k ≤ N, Inv t B (σ k) := fun k hk => inv_of_reach t B h0 (hreach k hk)
  have hgh := ghost_of_exec hexec h0
  -- the base of the read
  have hbase : ∀ k, i < k → k ≤ j → (σ k).r ≠ .idle ∧ (σ k).base = (σ i).nDone := by
    intro k hik hkj
    induction k with
    | zero => omega
    | succ k ih =>
      have hs := hexec k (by omega)
      rcases Nat.lt_or_ge i k with hik' | hik'
      · obtain ⟨hr, hb⟩ := ih hik' (by omega)
        have hne : lab k ≠ .invRead := by
          intro hl; rw [hl] at hs; exact hr (hs.step (by simp)).of_invRead.1
        refine ⟨hs.r_busy hr (hnr k hik' (by omega)), ?_⟩
        rw [hs.base_eq hne, hb]
      · obtain rfl : k = i := by omega
        rw [hli] at hs
        have hs := hs.step (by simp)
        exact ⟨hs.of_invRead.2.2, hs.of_invRead.2.1⟩
  obtain ⟨-, hb⟩ := hbase j hij le_rfl
  obtain ⟨hvi, hdi, -⟩ := hgh i (by omega)
  obtain ⟨hvj, hdj, hmj⟩ := hgh j (by omega)
  obtain ⟨k0, hk0, hk0l⟩ := hw
  have hcnt1 : 1 ≤ cntL Label.isRetW lab i :=
    le_trans (Nat.le_add_left _ _) (cntL_lt hk0 (by simp [hk0l, Label.isRetW]))
  have hs := hexec j hjN
  rw [hlj] at hs
  have hs := hs.step (by simp)
  obtain ⟨j', hj', hj'l, hv⟩ := lemma3_regular t B h0 (hreach j hjN.le) hs (by omega)
  obtain ⟨a, haj, hla, hca⟩ := hmj j' v (List.getElem?_eq_some_iff.2 ⟨hj'l, hv⟩)
  -- at the invocation `a` the writer is idle, so `a` follows exactly `j'` returns
  have hsa := hexec a (by omega)
  rw [hla] at hsa
  have hsa := hsa.step (by simp)
  have hra : cntL Label.isRetW lab a = j' := by
    obtain ⟨hva, hda, -⟩ := hgh a (by omega)
    have := (hinv a (by omega)).done hsa.idle_of_invWrite
    omega
  have hra1 : cntL Label.isRetW lab (a + 1) = j' := by
    rw [cntL_succ_of_false (by simp [hla, Label.isRetW]), hra]
  rcases Nat.lt_or_ge j' (σ i).nDone with hlt' | hge
  · -- `j' = base - 1`: the last write completed before the read
    obtain ⟨b, hbi, hbl, hcb⟩ := exists_of_lt_cntL (p := Label.isRetW) (lab := lab)
      (show j' < cntL Label.isRetW lab i by omega)
    have hlb : lab b = .retWrite := by
      revert hbl; cases lab b <;> simp [Label.isRetW]
    have hsb := hexec b (by omega)
    rw [hlb] at hsb
    have hsb := hsb.step (by simp)
    have hib : cntL Label.isInvW lab b = j' + 1 := by
      obtain ⟨hvb, hdb, -⟩ := hgh b (by omega)
      have := (hinv b (by omega)).done' hsb.busy_of_retWrite
      omega
    have hab : a < b := by
      by_contra hc
      have := cntL_mono (p := Label.isInvW) (lab := lab) (show b ≤ a by omega)
      omega
    left
    refine ⟨a, b, ⟨hab, hla, hlb, fun k hak hkb hk => ?_⟩, hbi, fun k hbk hki hk => ?_⟩
    · have := cntL_lt (p := Label.isRetW) (lab := lab) hkb (by simp [hk, Label.isRetW])
      have := cntL_mono (p := Label.isRetW) (lab := lab) (show a + 1 ≤ k by omega)
      omega
    · have := cntL_lt (p := Label.isRetW) (lab := lab) hki (by simp [hk, Label.isRetW])
      have := cntL_mono (p := Label.isRetW) (lab := lab) (show b + 1 ≤ k by omega)
      have : cntL Label.isRetW lab (b + 1) = j' + 1 := by
        simp [cntL, hlb, Label.isRetW, hcb]
      omega
  · -- `j' ≥ base`: a write not completed when the read is invoked
    right
    refine ⟨a, haj, hla, fun k hak hki hk => ?_⟩
    have hki' : k < i := by
      rcases Nat.lt_or_ge k i with h | h
      · exact h
      · obtain rfl : k = i := by omega
        rw [hli] at hk; cases hk
    have := cntL_lt (p := Label.isRetW) (lab := lab) hki' (by simp [hk, Label.isRetW])
    have := cntL_mono (p := Label.isRetW) (lab := lab) (show a + 1 ≤ k by omega)
    omega

end Exec

end Podc.StabilizingByzStorage.Regular
