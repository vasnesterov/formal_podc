import Papers.PODC2024.TetraBFT.Refinement

/-!
# Validity of single-shot TetraBFT (Theorem 1, validity)

"If all nodes are well-behaved and they all have the same input value `val`, then every
well-behaved node that decides a value decides `val`." (Definition 1.)

The leader proposes its input whenever Rule 1 shows the input safe (as the paper's step 2
prescribes when "arbitrary values are safe"); the key fact is that, when all reports carry only
the value `x₀`, Rule 1 (and Rule 3) showing *some* value safe implies that it shows `x₀` safe
(`ShowsSafe.of_vals`). This holds in every run (no timing assumption).
-/

set_option linter.unusedSectionVars false

namespace TetraBFT

open Finset Cslib.Byzantine.PartialSync

variable {V : Type} [DecidableEq V]

/-- All entries of a report carry the value `x₀`. -/
def ReportVals (rep : Report V) (x₀ : V) : Prop :=
  (∀ u y, rep.hi = some (u, y) → y = x₀) ∧ (∀ u y, rep.prev = some (u, y) → y = x₀) ∧
  (∀ u y, rep.top = some (u, y) → y = x₀)

theorem Blocking.of_vals {P : Type*} {f : ℕ} {S : Finset P} {rep : P → Report V} {x x₀ : V}
    {w : ℕ} (hv : ∀ q ∈ S, ReportVals (rep q) x₀) (h : Blocking f S rep x w) :
    Blocking f S rep x₀ w := by
  obtain ⟨B, hBS, hB, hc⟩ := h
  refine ⟨B, hBS, hB, fun q hq => ?_⟩
  rcases hc q hq with h0 | ⟨u, hu, hwu⟩ | hprev
  · exact Or.inl h0
  · have := (hv q (hBS hq)).1 u x hu
    subst this
    exact Or.inr (Or.inl ⟨u, hu, hwu⟩)
  · exact Or.inr (Or.inr hprev)

/-- If all reports carry only `x₀`, any value shown safe can be replaced by `x₀`. -/
theorem ShowsSafe.of_vals {P : Type*} {m f : ℕ} {bB : Bool} {S : Finset P}
    {rep : P → Report V} {x x₀ : V} {v : ℕ} (hv : ∀ q ∈ S, ReportVals (rep q) x₀)
    (h : ShowsSafe m f bB S rep x v) : ShowsSafe m f bB S rep x₀ v := by
  rcases h with h0 | ⟨Q, hQS, hQ, hcase⟩
  · exact Or.inl h0
  refine Or.inr ⟨Q, hQS, hQ, ?_⟩
  rcases hcase with hnone | ⟨w, hwv, hok, hiii⟩
  · exact Or.inl hnone
  refine Or.inr ⟨w, hwv, fun q hq u y htop => ?_, ?_⟩
  · have hy := (hv q (hQS hq)).2.2 u y htop
    rcases hok q hq u y htop with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hy⟩
  · rcases hiii with hA | hB
    · exact Or.inl (hA.of_vals hv)
    · exact Or.inr hB

theorem mkReport_vals {votes : List (Vote V)} {x₀ : V} (h : ∀ w ∈ votes, w.val = x₀)
    (r a b : ℕ) : ReportVals (mkReport votes r a b) x₀ := by
  have key : ∀ c u y, (u, y) ∈ phaseVotes votes c r → y = x₀ := fun c u y hm =>
    h _ (mem_phaseVotes.1 hm).2
  refine ⟨fun u y hu => key a u y (best_mem hu), fun u y hu => ?_,
    fun u y hu => key b u y (best_mem hu)⟩
  simp only [mkReport] at hu
  split at hu
  · simp at hu
  · exact key a u y (List.mem_filter.1 (best_mem hu)).1

theorem mem_of_repSenders_suggest {n : ℕ} {rcv : List (Fin n × Msg V)} {v : ℕ} {q : Fin n}
    (hq : q ∈ repSenders rcv (getSuggest v)) :
    (q, Msg.suggest v (repOf rcv (getSuggest v) q)) ∈ rcv := by
  simp only [repSenders, mem_filter, mem_univ, true_and, Option.isSome_iff_exists] at hq
  obtain ⟨a, ha⟩ := hq
  have hrep : repOf rcv (getSuggest v) q = a := by simp [repOf, ha]
  rw [hrep]
  obtain ⟨⟨q', m⟩, hm, he⟩ := List.exists_of_findSome?_eq_some ha
  simp only at he
  split_ifs at he with hq'
  subst hq'
  cases m with
  | suggest v' rep =>
    simp only [getSuggest] at he
    split_ifs at he with hv
    · subst hv; simp only [Option.some.injEq] at he; subst he; exact hm
  | _ => simp [getSuggest] at he

/-- The value carried by a message is `x₀`. -/
def MsgVal (x₀ : V) : Msg V → Prop
  | .proposal _ x => x = x₀
  | .vote _ _ x => x = x₀
  | .proof _ rep => ReportVals rep x₀
  | .suggest _ rep => ReportVals rep x₀
  | .viewChange _ => True

section Run

variable {n : ℕ} {prm : Params n} (R : Run (Fin n) (Msg V) V)

local notation "A" => tetra (V := V) prm

theorem st_inp (τ : ℕ) (p : Fin n) : (R.st A τ p).inp = R.inp p := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [st_succ', step_inp, ih]

/-- **Theorem 1 (validity).** If no node is faulty and all inputs equal `x₀`, every decision
is `x₀`. -/
theorem tetra_validity (hf : prm.f < n) (hR : R.faulty = ∅) {x₀ : V} (hinp : ∀ p, R.inp p = x₀)
    {p : Fin n} {x : V} (hx : R.Decides A p x) : x = x₀ := by
  have hcorr : ∀ q, q ∉ R.faulty := by simp [hR]
  -- by strong induction on time: all votes, messages and decisions carry `x₀`
  have claim : ∀ τ q, (∀ w ∈ (R.st A τ q).votes, w.val = x₀) ∧
      (∀ m ∈ (R.st A τ q).out, MsgVal x₀ m) ∧
      (∀ y v, (R.st A τ q).dec = some (y, v) → y = x₀) := by
    intro τ
    induction τ using Nat.strong_induction_on with
    | _ τ ih =>
    intro q
    have hrcv : ∀ q' m, (q', m) ∈ (R.st A τ q).rcv → MsgVal x₀ m := fun q' m hm => by
      obtain ⟨τ', hτ', hm'⟩ := rcv_authentic R (hcorr q') hm
      exact (ih τ' hτ' q').2.1 m hm'
    have hquorum : ∀ k v y, n - prm.f ≤ (senders (R.st A τ q).rcv (.vote k v y)).card →
        y = x₀ := by
      intro k v y hc
      obtain ⟨q', hq'⟩ : (senders (R.st A τ q).rcv (.vote k v y)).Nonempty :=
        card_pos.1 (by omega)
      simp only [senders, mem_filter, mem_univ, true_and] at hq'
      exact hrcv q' _ hq'
    have hinv := st_inv (prm := prm) R τ q
    have hvotes : ∀ w ∈ (R.st A τ q).votes, w.val = x₀ := by
      intro w hw
      obtain ⟨h1, h4, -, hq, hpr⟩ := hinv.just w hw
      rcases Nat.lt_or_ge w.phase 2 with h | h
      · exact hrcv _ _ (hpr (by omega))
      · exact hquorum _ _ _ (hq h)
    refine ⟨hvotes, fun m hm => ?_, fun y v hd => hquorum _ _ _ (hinv.dec y v hd)⟩
    have hok := hinv.out m hm
    cases m with
    | proposal v y =>
      obtain ⟨hs, h | hns⟩ := hok
      · rw [h, st_inp, hinp]; rfl
      · exfalso
        apply hns
        rcases hs with rfl | hs
        · exact Or.inl rfl
        · rw [st_inp, hinp]
          refine hs.of_vals fun q' hq' => ?_
          exact hrcv _ _ (mem_of_repSenders_suggest hq')
    | vote k v y => exact hvotes _ hok
    | proof v rep => rw [hok.2]; exact mkReport_vals hvotes _ _ _
    | suggest v rep => rw [hok.2]; exact mkReport_vals hvotes _ _ _
    | viewChange => trivial
  obtain ⟨τ, h⟩ := hx
  simp only [tetra, Option.map_eq_some_iff] at h
  obtain ⟨⟨y, v⟩, h, rfl⟩ := h
  exact (claim τ p).2.2 y v h

end Run

end TetraBFT
