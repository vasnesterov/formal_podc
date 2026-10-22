import Papers.PODC2015.SetAgreementSpace.Defs
import Podc.Computability.Distributed.SharedMemory.Splice

/-!
# Lemma 1 of [DFKR15] from the wait-free set-agreement impossibility

Lemma 1 of the paper derives from the impossibility of wait-free `(q-1)`-set agreement among `q`
processes from registers (Borowsky–Gafni, Herlihy–Shavit, Saks–Zaharoglou) that an
`m`-obstruction-free set-agreement algorithm has, for any `m` processes with `m` distinct inputs,
an execution of these processes only in which all `m` inputs are output.

We do not formalize the topological impossibility proof; it is the explicit hypothesis
`BGImpossibility` (a true, standard theorem; see its docstring).

* `Lemma1Prop I m` — the form of Lemma 1 used in the proof of Theorem 2: it is stated *from an
  arbitrary reachable configuration* `C` (not only from the initial one), for the first instance
  of repeated set agreement that nobody has invoked yet.
* `lemma1` — `BGImpossibility` + validity + `m`-obstruction-freedom imply `Lemma1Prop I m`.
  The reduction restarts `I` from `C`, allowing only the processes of `Q` to propose, each its own
  input (`Cslib.SharedMemory.Impl.restrict`): the restarted algorithm is wait-free because at
  most `m` processes ever take steps, and satisfies validity because the instance is fresh.
-/

namespace Podc.SetAgreementSpace

open Cslib.SharedMemory

variable {P V ι W L : Type} [DecidableEq P] [DecidableEq ι] [Inhabited V] {w₀ : W}

/-- **Impossibility of wait-free set agreement** (Borowsky–Gafni, Herlihy–Shavit,
Saks–Zaharoglou, references [2, 10, 11] of [DFKR15]), in the special case used by Lemma 1: no
wait-free read/write algorithm in which exactly the processes of a nonempty set `Q` may propose,
each its own fixed input `inp p` (pairwise distinct), solves `(|Q| - 1)`-set agreement (validity
and `(|Q|-1)`-agreement on all one-shot executions). The initial memory and local states are
arbitrary (they are part of the algorithm `J`). This is a true theorem; it is assumed here, not
proved. -/
def BGImpossibility (P V ι W L : Type) [DecidableEq P] [DecidableEq ι] [Inhabited V] (w₀ : W) :
    Prop :=
  ∀ (J : Impl (saObj V) (RegFamily ι W w₀) P L) (Q : Finset P) (inp : P → V),
    Q.Nonempty → Set.InjOn inp Q → (∀ p o, J.allowed p o ↔ p ∈ Q ∧ o = inp p) →
    J.WaitFreeOn OneShot → ¬ J.Solves (kSetAgreement P V (Q.card - 1))

/-- **Lemma 1 of [DFKR15]**, in the form used in the proof of Theorem 2. Let `C` be reached by an
execution `α` in which every process invoked `Propose` at most `s` times, and let `Q` be a set of
at most `m` processes that are idle in `C` and invoked exactly `s` times, with pairwise distinct
inputs `inp q`. Then there is an execution fragment `β` from `C` in which only processes of `Q`
take steps and in which all values `inp q`, `q ∈ Q`, are output: each by a process of `Q` that
returns exactly once in `β` (i.e. in the `(s+1)`-th instance).

The paper states Lemma 1 for executions from the initial configuration; Theorem 2 applies it
from the configurations `D_j`, to the `(s+1)`-th instance. -/
def Lemma1Prop {B : ι → ObjSpec} (I : Impl (saObj V) B P L) (m : ℕ) : Prop :=
  ∀ (α : List (Label P (saObj V))) (C : Config (saObj V) B P L) (s : ℕ) (Q : Finset P)
    (inp : P → V), I.run α = some C → (∀ p, (opsOf α p).length ≤ s) → Q.card ≤ m →
    (∀ q ∈ Q, C.pend q = none ∧ (opsOf α q).length = s) → Set.InjOn inp Q →
    ∃ β C', I.runFrom C β = some C' ∧ (∀ ℓ ∈ β, ℓ.proc ∈ Q) ∧
      ∀ q ∈ Q, ∃ q' ∈ Q, respsOf β q' = [inp q]

/-- **Lemma 1 of [DFKR15]** (in the generalized form `Lemma1Prop`) from the impossibility of
wait-free set agreement: every `m`-obstruction-free read/write algorithm satisfying the validity
of repeated set agreement has, from any reachable configuration, executions of any `m` idle
processes in which all their (distinct) inputs are output in a fresh instance. -/
theorem lemma1 (I : Impl (saObj V) (RegFamily ι W w₀) P L) {k m : ℕ}
    (hBG : BGImpossibility P V ι W L w₀) (hall : ∀ p o, I.allowed p o)
    (hsolve : I.SolvesRepeated k) (hof : I.MObstructionFreeOn m (fun _ => True)) :
    Lemma1Prop I m := by
  intro α C s Q inp hα hs hQm hQ hinj
  rcases Q.eq_empty_or_nonempty with rfl | hne
  · exact ⟨[], C, rfl, by simp, by simp⟩
  let al : P → V → Prop := fun p o => p ∈ Q ∧ o = inp p
  have hal : ∀ p o, al p o → p ∈ (Q : Set P) ∧ I.allowed p o := fun p o h => ⟨h.1, hall p o⟩
  have hidle : ∀ q ∈ (Q : Set P), C.pend q = none := fun q hq => (hQ q hq).1
  have hwf : (I.restrict C al).WaitFree :=
    Impl.waitFree_of_restrict hof hα (by simpa using hQm) hal hidle
  have hresp : ∀ q ∈ Q, (respsOf α q).length = s := fun q hq => by
    rw [← I.run_idle_counts hα (hQ q hq).1]; exact (hQ q hq).2
  have hproc : ∀ β, (I.restrict C al).Valid β → ∀ ℓ ∈ β, ℓ.proc ∈ (Q : Set P) :=
    fun β hβ => Impl.restrict_proc_mem (fun p o h => h.1) hβ
  -- a process that returns in an execution of the restarted algorithm belongs to `Q`
  have hmemQ : ∀ β, (I.restrict C al).Valid β → ∀ p, respsOf β p ≠ [] → p ∈ Q := by
    intro β hβ p hp
    by_contra hpQ
    exact hp (respsOf_eq_nil_of_proc_ne fun ℓ hℓ h => hpQ (h ▸ hproc β hβ ℓ hℓ))
  -- validity of the restarted algorithm
  have hvalid : ∀ β, (I.restrict C al).Valid β → OneShot β →
      ∀ p w, outputs β p = some w → ∃ q, inputs β q = some w := by
    intro β hβ h1 p w hw
    obtain ⟨X, hX⟩ := hβ
    obtain ⟨Y, hY, -⟩ := Impl.restrict_run hal hidle hX
    have hv : I.Valid (α ++ β) := ⟨Y, by rw [Impl.run_append_of_eq I hα, hY]⟩
    have hpβ : respsOf β p ≠ [] := by intro h; simp [outputs, h] at hw
    have hpQ := hmemQ β ⟨X, hX⟩ p hpβ
    have hw' : w ∈ outputsAt (α ++ β) s := by
      refine ⟨p, ?_⟩
      rw [respsOf_append, List.getElem?_append_right (by rw [hresp p hpQ]), hresp p hpQ,
        Nat.sub_self, ← List.head?_eq_getElem?]
      exact hw
    obtain ⟨q, hq⟩ := (hsolve _ hv s).1 hw'
    rw [opsOf_append, List.getElem?_append_right (hs q)] at hq
    have h0 : s - (opsOf α q).length = 0 := by
      by_contra hne
      have := h1 q
      rw [List.getElem?_eq_none (by omega)] at hq
      simp at hq
    rw [h0, ← List.head?_eq_getElem?] at hq
    exact ⟨q, hq⟩
  have hnot := hBG (I.restrict C al) Q inp hne hinj (fun _ _ => Iff.rfl) (hwf.waitFreeOn _)
  simp only [Impl.Solves, not_forall] at hnot
  obtain ⟨β, hβ, h1, hΔ⟩ := hnot
  have hagr : ¬ {w | ∃ p, outputs β p = some w}.encard ≤ ((Q.card - 1 : ℕ) : ℕ∞) :=
    fun h => hΔ ⟨hvalid β hβ h1, h⟩
  set O := {w | ∃ p, outputs β p = some w} with hOdef
  have hO : O ⊆ inp '' Q := by
    rintro w ⟨p, hp⟩
    obtain ⟨q, hq⟩ := hvalid β hβ h1 p w hp
    have hmem : w ∈ opsOf β q := List.mem_of_mem_head? hq
    obtain ⟨hqQ, rfl⟩ := (I.restrict C al).allowed_of_mem_opsOf hβ hmem
    exact ⟨q, hqQ, rfl⟩
  have hcard : (inp '' Q).encard = Q.card := by
    rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard]
  have hle : (inp '' Q).encard ≤ O.encard := by
    rw [hcard]
    have hlt : ((Q.card - 1 : ℕ) : ℕ∞) < O.encard := not_le.1 hagr
    have := Order.add_one_le_of_lt hlt
    have hc : ((Q.card - 1 : ℕ) : ℕ∞) + 1 = (Q.card : ℕ∞) := by
      have := hne.card_pos
      norm_cast; omega
    rwa [hc] at this
  have hfin : O.Finite := (Set.toFinite _ |>.image inp).subset hO
  have hOeq : O = inp '' Q := hfin.eq_of_subset_of_encard_le hO hle
  obtain ⟨X, hX⟩ := hβ
  obtain ⟨Y, hY, -⟩ := Impl.restrict_run hal hidle hX
  refine ⟨β, Y, hY, hproc β ⟨X, hX⟩, fun q hq => ?_⟩
  have : inp q ∈ O := hOeq ▸ ⟨q, hq, rfl⟩
  obtain ⟨p, hp⟩ := this
  have hpβ : respsOf β p ≠ [] := by intro h; simp [outputs, h] at hp
  refine ⟨p, hmemQ β ⟨X, hX⟩ p hpβ, ?_⟩
  have hlen : (respsOf β p).length ≤ 1 :=
    ((Impl.Valid.wellFormed (I := I.restrict C al) ⟨X, hX⟩).resps_le_ops p).trans (h1 p)
  simp only [outputs] at hp
  match h : respsOf β p, hlen with
  | [], _ => simp [h] at hp
  | [r], _ => simp only [h, List.head?_cons] at hp; exact congrArg (· :: []) (Option.some.inj hp)
  | _ :: _ :: _, hl => simp at hl

/-! ### Non-vacuity of `Lemma1Prop` -/

/-- The trivial algorithm in which every process decides its own proposal (no registers). It
solves repeated `n`-set agreement; we use it to show that `Lemma1Prop` is satisfiable. -/
def trivialImpl (P V : Type) [Inhabited V] : Impl (saObj V) (RegFamily Empty Unit ()) P (Option V)
    where
  memInit := fun i => i.elim
  locInit := fun _ => none
  invoke := fun _ _ o => some o
  act := fun _ l => .ret (l.getD default) none

/-- Labels of the processes of `l` proposing `inp q` and deciding, one after the other. -/
def trivialLabels (inp : P → V) (l : List P) : List (Label P (saObj V)) :=
  l.flatMap fun q => [.inv q (inp q), .ret q (inp q)]

lemma trivialLabels_run (inp : P → V) :
    ∀ (l : List P) (X : Config (saObj V) (RegFamily Empty Unit ()) P (Option V)),
      (∀ q ∈ l, X.pend q = none) →
      ∃ X', (trivialImpl P V).runFrom X (trivialLabels inp l) = some X' := by
  classical
  intro l
  induction l with
  | nil => intro X _; exact ⟨X, rfl⟩
  | cons q l ih =>
    intro X hX
    set X₁ : Config (saObj V) (RegFamily Empty Unit ()) P (Option V) :=
      ⟨Function.update X.loc q (some (inp q)), Function.update X.pend q (some (inp q)), X.mem⟩
    set X₂ : Config (saObj V) (RegFamily Empty Unit ()) P (Option V) :=
      ⟨Function.update X₁.loc q none, Function.update X₁.pend q none, X₁.mem⟩
    have h1 : (trivialImpl P V).step X (.inv q (inp q)) = some X₁ := by
      simp [Impl.step, hX q (by simp), trivialImpl, X₁]
    have h2 : (trivialImpl P V).step X₁ (.ret q (inp q)) = some X₂ := by
      simp [Impl.step, trivialImpl, X₁, X₂]
    obtain ⟨X', hX'⟩ := ih X₂ (fun q' hq' => by
      by_cases h : q' = q
      · simp [X₂, h]
      · simp [X₂, X₁, h, hX q' (by simp [hq'])])
    refine ⟨X', ?_⟩
    simp only [trivialLabels, List.flatMap_cons, List.cons_append, List.nil_append,
      Impl.runFrom_cons, h1, Option.bind_some, h2]
    exact hX'

lemma respsOf_trivialLabels (inp : P → V) :
    ∀ (l : List P), l.Nodup → ∀ q ∈ l, respsOf (trivialLabels inp l) q = [inp q] := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hnd q hq
    have hnil' : respsOf (trivialLabels inp l) a = [] := by
      apply respsOf_eq_nil_of_proc_ne
      intro ℓ hℓ h
      simp only [trivialLabels, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
        or_false] at hℓ
      obtain ⟨b, hb, rfl | rfl⟩ := hℓ <;>
        exact (List.nodup_cons.1 hnd).1 (by simp only [Label.proc] at h; exact h ▸ hb)
    rcases List.mem_cons.1 hq with rfl | hq
    · simp [trivialLabels, respsOf_cons, hnil'] at *
    · have hqa : a ≠ q := fun h => (List.nodup_cons.1 hnd).1 (h ▸ hq)
      have := ih (List.nodup_cons.1 hnd).2 q hq
      simp only [trivialLabels, List.flatMap_cons] at this ⊢
      simpa [respsOf_cons, hqa] using this

/-- `Lemma1Prop` is satisfiable: the trivial algorithm satisfies it for every `m`. -/
theorem lemma1Prop_trivialImpl (m : ℕ) : Lemma1Prop (trivialImpl P V) m := by
  intro α C s Q inp _ _ _ hQ _
  obtain ⟨C', hC'⟩ := trivialLabels_run inp Q.toList C
    (fun q hq => (hQ q (Finset.mem_toList.1 hq)).1)
  refine ⟨trivialLabels inp Q.toList, C', hC', fun ℓ hℓ => ?_, fun q hq =>
    ⟨q, hq, respsOf_trivialLabels inp _ Q.nodup_toList q (Finset.mem_toList.2 hq)⟩⟩
  simp only [trivialLabels, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  obtain ⟨b, hb, rfl | rfl⟩ := hℓ <;> exact Finset.mem_toList.1 hb

end Podc.SetAgreementSpace
