import Papers.PODC2020.DetectableSpace.Model
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.SWSRRegister
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Seq
import Podc.SharedMemory.History

/-!
# `DLin` on crash-free histories is CSLib's linearizability

The paper's correctness condition `DLin` (durable linearizability + detectability) is stated for
histories of the recoverable model: operation instances carry identifiers `ℕ`, and histories may
contain crashes and `fail` responses. On histories **without crashes and `fail` responses** it is
exactly the (Herlihy–Wing) linearizability of CSLib, `Cslib.SharedMemory.IsLinearization`, whose
histories are lists of labels `Label P O` with instances `OpId P = P × ℕ` (`(p, k)` = the `k`-th
operation of `p`).

* `HistCorr ι α h` — the crash-free, `fail`-free history `h` records the CSLib history `α`, the
  instance `(p, k)` having identifier `ι (p, k)` (internal steps are not recorded). Every `α` has
  such an `h` (`HistCorr.exists_of`); `ι` must be injective on the invoked instances, which is
  possible whenever `P` is countable.
* `dLin_iff_isLinearization` — for a well-formed `α`, a list `M` of invoked instances is a
  linearization of `α` iff `M` with identifiers renamed by `ι` is a durable detectable
  linearization of `h` (from the initial state);
* `exists_dLin_iff_exists_isLinearization` — hence `h` has a `DLin` iff `α` is linearizable.
-/

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

variable {O : ObjSpec} {P : Type} [DecidableEq P]

/-- `HistCorr ι α h`: the history `h` of the recoverable model (no crash, no `fail`) records the
CSLib history `α`; the instance `(p, k)` has the identifier `ι (p, k)`, and internal steps are not
recorded. -/
inductive HistCorr (ι : OpId P → ℕ) : List (Label P O) → List (HEv P O.Op O.Resp) → Prop
  | nil : HistCorr ι [] []
  | inv {α h} (p : P) (o : O.Op) : HistCorr ι α h →
      HistCorr ι (α ++ [.inv p o]) (h ++ [.inv (ι (p, (opsOf α p).length)) p o])
  | ret {α h} (p : P) (r : O.Resp) : HistCorr ι α h →
      HistCorr ι (α ++ [.ret p r]) (h ++ [.res (ι (p, (respsOf α p).length)) (some r) false])
  | tau {α h} (p : P) : HistCorr ι α h → HistCorr ι (α ++ [.tau p]) h

namespace HistCorr

variable {ι : OpId P → ℕ} {α : List (Label P O)} {h : List (HEv P O.Op O.Resp)}

/-- Every CSLib history is recorded by some history of the recoverable model. -/
lemma exists_of (ι : OpId P → ℕ) (α : List (Label P O)) : ∃ h, HistCorr ι α h := by
  induction α using List.reverseRecOn with
  | nil => exact ⟨[], .nil⟩
  | append_singleton α ℓ ih =>
    obtain ⟨h, hh⟩ := ih
    cases ℓ with
    | inv p o => exact ⟨_, hh.inv p o⟩
    | ret p r => exact ⟨_, hh.ret p r⟩
    | tau p => exact ⟨_, hh.tau p⟩

/-- Invocation events of `h` are the invocations of `α`. -/
lemma mem_inv (hc : HistCorr ι α h) {n : ℕ} {p : P} {o : O.Op} :
    HEv.inv n p o ∈ h ↔ ∃ k, n = ι (p, k) ∧ opOf α (p, k) = some o := by
  induction hc with
  | nil => simp [opOf]
  | @inv α h q o' hc ih =>
    simp only [List.mem_append, List.mem_singleton, HEv.inv.injEq, ih, opOf_concat_inv]
    constructor
    · rintro (⟨k, rfl, hk⟩ | ⟨rfl, rfl, rfl⟩)
      · refine ⟨k, rfl, ?_⟩
        rw [ite_eq_right]; · exact hk
        rintro hpk
        simp only [Prod.mk.injEq] at hpk
        obtain ⟨rfl, rfl⟩ := hpk
        simp [opOf] at hk
      · exact ⟨_, rfl, by simp⟩
    · rintro ⟨k, rfl, hk⟩
      split_ifs at hk with hpk
      · simp only [Prod.mk.injEq] at hpk
        obtain ⟨rfl, rfl⟩ := hpk
        cases hk
        exact Or.inr ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨k, rfl, hk⟩
  | @ret α h q r hc ih =>
    have e : ∀ x, opOf (α ++ [.ret q r]) x = opOf α x :=
      fun x => opOf_concat_of_ne (x := x) (fun _ h => by cases h)
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false, ih, e]
  | @tau α h q hc ih =>
    have e : ∀ x, opOf (α ++ [.tau q]) x = opOf α x :=
      fun x => opOf_concat_of_ne (x := x) (fun _ h => by cases h)
    simp only [ih, e]

/-- Response events of `h` are the responses of `α`; none of them is `fail`. -/
lemma mem_res (hc : HistCorr ι α h) {n : ℕ} {r : Option O.Resp} {c : Bool} :
    HEv.res n r c ∈ h ↔ ∃ x r', n = ι x ∧ r = some r' ∧ c = false ∧ respOf α x = some r' := by
  induction hc with
  | nil => simp [respOf]
  | @inv α h q o hc ih =>
    have e : ∀ x, respOf (α ++ [.inv q o]) x = respOf α x :=
      respOf_append_of_not_ret (fun _ _ h => by cases h)
    simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false, ih, e]
  | @ret α h q r' hc ih =>
    simp only [List.mem_append, List.mem_singleton, HEv.res.injEq, ih, respOf_append_ret]
    constructor
    · rintro (⟨x, r'', rfl, rfl, rfl, hx⟩ | ⟨rfl, rfl, rfl⟩)
      · refine ⟨x, r'', rfl, rfl, rfl, ?_⟩
        rw [ite_eq_right]; · exact hx
        rintro rfl
        simp [respOf] at hx
      · exact ⟨_, r', rfl, rfl, rfl, by simp⟩
    · rintro ⟨x, r'', rfl, rfl, rfl, hx⟩
      split_ifs at hx with hpk
      · subst hpk
        cases hx
        exact Or.inr ⟨rfl, rfl, rfl⟩
      · exact Or.inl ⟨x, r'', rfl, rfl, rfl, hx⟩
  | @tau α h q hc ih =>
    have e : ∀ x, respOf (α ++ [.tau q]) x = respOf α x :=
      respOf_append_of_not_ret (fun _ _ h => by cases h)
    simp only [ih, e]

/-- A prefix of `α` is recorded by a prefix of `h`. -/
lemma exists_split_of_split (hc : HistCorr ι α h) :
    ∀ β γ, α = β ++ γ → ∃ h₁ h₂, h = h₁ ++ h₂ ∧ HistCorr ι β h₁ := by
  induction hc with
  | nil =>
    intro β γ hβ
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hβ.symm
    exact ⟨[], [], rfl, .nil⟩
  | inv _ _ hc ih | ret _ _ hc ih | tau _ hc ih =>
    intro β γ hβ
    rcases List.eq_nil_or_concat γ with rfl | ⟨γ', ℓ, rfl⟩
    · rw [List.append_nil] at hβ; subst hβ
      exact ⟨_, [], (List.append_nil _).symm,
        by first | exact hc.inv _ _ | exact hc.ret _ _ | exact hc.tau _⟩
    · rw [List.concat_eq_append, ← List.append_assoc] at hβ
      obtain ⟨rfl, -⟩ := List.append_inj' hβ rfl
      obtain ⟨h₁, h₂, rfl, h1⟩ := ih β γ' rfl
      exact ⟨h₁, _, by first | exact List.append_assoc _ _ _ | rfl, h1⟩

/-- A prefix of `h` records a prefix `β` of `α`; the invocations in the rest of `h` are those of
instances not invoked in `β`. -/
lemma exists_split (hc : HistCorr ι α h) :
    ∀ h₁ h₂, h = h₁ ++ h₂ → ∃ β γ, α = β ++ γ ∧ HistCorr ι β h₁ ∧
      ∀ n p o, HEv.inv n p o ∈ h₂ → ∃ k, n = ι (p, k) ∧ (opsOf β p).length ≤ k ∧
        Invoked α (p, k) := by
  induction hc with
  | nil =>
    intro h₁ h₂ hh
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hh.symm
    exact ⟨[], [], rfl, .nil, by simp⟩
  | inv _ _ hc ih | ret _ _ hc ih =>
    intro h₁ h₂ hh
    rcases List.eq_nil_or_concat h₂ with rfl | ⟨h₂', e, rfl⟩
    · rw [List.append_nil] at hh; subst hh
      exact ⟨_, [], (List.append_nil _).symm,
        by first | exact hc.inv _ _ | exact hc.ret _ _, by simp⟩
    · rw [List.concat_eq_append, ← List.append_assoc] at hh
      obtain ⟨rfl, he⟩ := List.append_inj' hh rfl
      simp only [List.cons.injEq, and_true] at he
      subst he
      obtain ⟨β, γ, rfl, h1, h2⟩ := ih h₁ h₂' rfl
      refine ⟨β, γ ++ [_], List.append_assoc _ _ _, h1, ?_⟩
      intro n p o' hn
      rw [List.concat_eq_append] at hn
      rcases List.mem_append.1 hn with hn | hn
      · obtain ⟨k, rfl, hk, hi⟩ := h2 n p o' hn
        exact ⟨k, rfl, hk, hi.mono⟩
      · simp only [List.mem_singleton, HEv.inv.injEq, reduceCtorEq] at hn <;>
          (obtain ⟨rfl, rfl, rfl⟩ := hn; exact ⟨_, rfl, by simp, by simp [Invoked]⟩)
  | @tau α h q hc ih =>
    intro h₁ h₂ hh
    obtain ⟨β, γ, rfl, h1, h2⟩ := ih h₁ h₂ hh
    refine ⟨β, γ ++ [.tau q], by simp, h1, ?_⟩
    intro n p o' hn
    obtain ⟨k, rfl, hk, hi⟩ := h2 n p o' hn
    exact ⟨k, rfl, hk, hi.mono⟩

/-- Real-time order of `α` implies the paper's real-time order `Prec` of `h`. -/
lemma prec_of_precedes (hc : HistCorr ι α h) (hι : Set.InjOn ι {x | Invoked α x})
    {a b : OpId P} (hab : Precedes α a b) (hb : Invoked α b) : Prec h (ι a) (ι b) := by
  obtain ⟨β, γ, rfl, ha, hnb⟩ := hab
  obtain ⟨h₁, h₂, rfl, h1⟩ := hc.exists_split_of_split β γ rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 ha)
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1
    (by simpa [opOf, Invoked] using hb : (opOf (β ++ γ) b).isSome)
  refine ⟨h₁, h₂, rfl, ⟨some r, false, h1.mem_res.2 ⟨a, r, rfl, rfl, rfl, hr⟩⟩, b.1, o, ?_⟩
  have hinv : HEv.inv (ι b) b.1 o ∈ h₁ ++ h₂ := hc.mem_inv.2 ⟨b.2, rfl, ho⟩
  rcases List.mem_append.1 hinv with hin | hin
  · exfalso
    obtain ⟨k, hk, hok⟩ := h1.mem_inv.1 hin
    have hki : Invoked β (b.1, k) := Invoked.of_opOf_eq_some hok
    have := hι hb hki.mono hk
    exact hnb (this ▸ hki)
  · exact hin

/-- The paper's real-time order `Prec` of `h` between invoked instances is the real-time order
of `α`. -/
lemma precedes_of_prec (hc : HistCorr ι α h) (hα : WellFormed α)
    (hι : Set.InjOn ι {x | Invoked α x}) {a b : OpId P} (ha : Invoked α a) (hb : Invoked α b)
    (hab : Prec h (ι a) (ι b)) : Precedes α a b := by
  obtain ⟨h₁, h₂, rfl, ⟨r, c, hr⟩, p, o, hinv⟩ := hab
  obtain ⟨β, γ, rfl, h1, h2⟩ := hc.exists_split h₁ h₂ rfl
  refine ⟨β, γ, rfl, ?_, ?_⟩
  · obtain ⟨x, r', hx, -, -, hxr⟩ := h1.mem_res.1 hr
    have hxc : Completed β x := Completed.of_respOf_eq_some hxr
    have hxi : Invoked β x := hα.of_append.invoked_of_completed hxc
    rw [hι ha hxi.mono hx]; exact hxc
  · obtain ⟨k, hk, hle, hki⟩ := h2 _ _ _ hinv
    rw [hι hb hki hk]
    simp only [Invoked, not_lt]; exact hle

end HistCorr

variable {ι : OpId P → ℕ} {α : List (Label P O)} {h : List (HEv P O.Op O.Resp)}

/-- Legality of the renamed sequential history is `SeqOK`. -/
lemma legal_map_iff (hc : HistCorr ι α h) (hα : WellFormed α)
    (hι : Set.InjOn ι {x | Invoked α x}) :
    ∀ (σ : O.State) (M : List (OpId P × O.Op)), (∀ y ∈ M, Invoked α y.1) →
      (Legal O h σ (M.map (Prod.map ι id)) ↔ SeqOK α σ M) := by
  intro σ M hM
  induction M generalizing σ with
  | nil => simp [Legal, SeqOK]
  | cons y M ih =>
    obtain ⟨x, o⟩ := y
    have hx : Invoked α x := hM (x, o) (by simp)
    simp only [List.map_cons, Prod.map_apply, id_eq, Legal, SeqOK]
    rw [ih _ (fun y hy => hM y (by simp [hy]))]
    refine and_congr_left fun _ => ⟨fun H r hr => (H r false
      (hc.mem_res.2 ⟨x, r, rfl, rfl, rfl, hr⟩)).symm, fun H r c hr => ?_⟩
    obtain ⟨x', r', hx', hr', -, hxr⟩ := hc.mem_res.1 hr
    cases hr'
    have hx'i : Invoked α x' := hα.invoked_of_completed (Completed.of_respOf_eq_some hxr)
    rw [hι hx hx'i hx'] at H
    exact (H r hxr).symm

/-- **Bridge.** On a crash-free, `fail`-free history `h` recording the well-formed CSLib
history `α`, a list `M` of invoked instances is a linearization of `α` (CSLib's
`IsLinearization`) iff its renaming by `ι` is a durable detectable linearization of `h`. -/
theorem dLin_iff_isLinearization (hc : HistCorr ι α h) (hα : WellFormed α)
    (hι : Set.InjOn ι {x | Invoked α x}) (M : List (OpId P × O.Op))
    (hM : ∀ y ∈ M, Invoked α y.1) :
    DLin O h O.init (M.map (Prod.map ι id)) ↔ IsLinearization α M := by
  have hfst : (M.map (Prod.map ι id)).map Prod.fst = (M.map Prod.fst).map ι := by simp
  have hMi : ∀ a ∈ M.map Prod.fst, Invoked α a := by
    intro a ha; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha; exact hM y hy
  have hmem : ∀ a, Invoked α a → (ι a ∈ (M.map Prod.fst).map ι ↔ a ∈ M.map Prod.fst) := by
    intro a ha
    refine ⟨fun h' => ?_, List.mem_map_of_mem⟩
    obtain ⟨b, hb, hba⟩ := List.mem_map.1 h'
    rwa [← hι (hMi b hb) ha hba]
  have hrt : (M.map (Prod.map ι id)).Pairwise (fun x y => ¬ Prec h y.1 x.1) ↔
      (M.map Prod.fst).Pairwise (fun a b => ¬ Prec h (ι b) (ι a)) := by
    simp only [List.pairwise_map, Prod.map_fst]
  constructor
  · intro hd
    have hnd : (M.map Prod.fst).Nodup := List.Nodup.of_map ι (hfst ▸ hd.nodup)
    have hcomp : ∀ a, Completed α a → a ∈ M.map Prod.fst := by
      intro a ha
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 ha)
      have := hd.mem_of_res (ι a) r false (hc.mem_res.2 ⟨a, r, rfl, rfl, rfl, hr⟩)
      rw [hfst] at this
      exact (hmem a (hα.invoked_of_completed ha)).1 this
    refine ⟨hnd, ?_, hcomp, ?_, ?_⟩
    · intro y hy
      obtain ⟨p, hp⟩ := hd.inv_of_mem (Prod.map ι id y) (List.mem_map_of_mem hy)
      obtain ⟨k, hk, hok⟩ := hc.mem_inv.1 hp
      rw [hι (hM y hy) (Invoked.of_opOf_eq_some hok) hk]; exact hok
    · intro a b hab hb
      have ha : a ∈ M.map Prod.fst := hcomp a hab.completed
      have hne : a ≠ b := by
        rintro rfl
        obtain ⟨β, γ, rfl, h1, h2⟩ := hab
        exact h2 (hα.of_append.invoked_of_completed h1)
      rcases HerlihyWing.pair_sublist_total hnd ha hb hne with h' | h'
      · exact h'
      · exact absurd (hc.prec_of_precedes hι hab (hMi b hb))
          (List.pairwise_iff_forall_sublist.1 (hrt.1 hd.rt) h')
    · exact (legal_map_iff hc hα hι O.init M hM).1 hd.legal
  · intro hL
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hfst]
      exact hL.nodup.map_on fun a ha b hb hab => hι (hMi a ha) (hMi b hb) hab
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact ⟨y.1.1, hc.mem_inv.2 ⟨y.1.2, rfl, hL.op_eq y hy⟩⟩
    · intro a r c ha
      obtain ⟨x, r', rfl, -, -, hxr⟩ := hc.mem_res.1 ha
      rw [hfst]
      exact List.mem_map_of_mem (hL.complete x (Completed.of_respOf_eq_some hxr))
    · intro a c ha
      obtain ⟨x, r', -, h', -⟩ := hc.mem_res.1 ha
      cases h'
    · refine hrt.2 (List.pairwise_iff_forall_sublist.2 fun {a b} hab hprec => ?_)
      have hai := hMi a (hab.subset (by simp))
      have hbi := hMi b (hab.subset (by simp))
      have hba := hL.realtime b a (hc.precedes_of_prec hα hι hbi hai hprec)
        (hab.subset (by simp))
      exact HerlihyWing.pair_sublist_asymm hL.nodup hab hba
    · exact (legal_map_iff hc hα hι O.init M hM).2 hL.seq

/-- **Bridge.** On a crash-free, `fail`-free history `h` recording the well-formed CSLib
history `α`, `h` has a durable detectable linearization iff `α` is linearizable. -/
theorem exists_dLin_iff_exists_isLinearization (hc : HistCorr ι α h) (hα : WellFormed α)
    (hι : Set.InjOn ι {x | Invoked α x}) :
    (∃ L, DLin O h O.init L) ↔ ∃ M, IsLinearization α M := by
  constructor
  · rintro ⟨L, hd⟩
    have key : ∀ L : List (ℕ × O.Op), (∀ x ∈ L, ∃ p, HEv.inv x.1 p x.2 ∈ h) →
        ∃ M : List (OpId P × O.Op), L = M.map (Prod.map ι id) ∧ ∀ y ∈ M, Invoked α y.1 := by
      intro L hL
      induction L with
      | nil => exact ⟨[], rfl, by simp⟩
      | cons x L ih =>
        obtain ⟨M, rfl, hM⟩ := ih fun y hy => hL y (by simp [hy])
        obtain ⟨p, hp⟩ := hL x (by simp)
        obtain ⟨k, hk, hok⟩ := hc.mem_inv.1 hp
        refine ⟨((p, k), x.2) :: M, by simp [← hk], ?_⟩
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact Invoked.of_opOf_eq_some hok
        · exact hM y hy
    obtain ⟨M, rfl, hM⟩ := key L hd.inv_of_mem
    exact ⟨M, (dLin_iff_isLinearization hc hα hι M hM).1 hd⟩
  · rintro ⟨M, hL⟩
    have hM : ∀ y ∈ M, Invoked α y.1 := fun y hy =>
      Invoked.of_opOf_eq_some (hL.op_eq y hy)
    exact ⟨_, (dLin_iff_isLinearization hc hα hι M hM).2 hL⟩

end Papers.PODC2020.DetectableSpace
