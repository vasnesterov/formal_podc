import Podc.Computability.Distributed.CongestedClique.Oblivious

-- CSLib candidate: Cslib/Computability/Distributed/CongestedClique/Bandwidth.lean

/-!
# The congested clique with bandwidth `B`

In the model `Prog V W σ ρ` of `Phases.lean` one word crosses an ordered pair of nodes per round.
In the congested clique with bandwidth `B` (`CLIQUE-UCAST_{n,B}` in the notation of Drucker, Kuhn,
Oshman, PODC 2014), `B` words (typically `B` bits, `W = Bool`) cross every ordered pair per round,
so a direct step whose longest list has `width` words takes `⌈width / B⌉` rounds. A routed step is
still charged `lenzenRounds` rounds (Lenzen's algorithm needs bandwidth one word).

## Main definitions and statements

* `Cslib.CongestedClique.Prog.roundsAt`: the number of rounds at bandwidth `B`.
* `Cslib.CongestedClique.Prog.exists_oblivious_bw`: the oblivious routing lemma at bandwidth `B`:
  a direct step with a fixed pattern of row and column sums at most `|V| * D` takes
  `2 * ⌈D / B⌉` rounds.
* `Cslib.CongestedClique.Prog.exists_slots`: a convenient interface to the oblivious routing lemma.
  For every ordered pair `(u, v)` a fixed finite set of *slots* `L u v` is given; `u` sends to `v`
  one word `enc u (s u) t` for every slot `t ∈ L u v`, and `v` receives these words indexed by
  slots.
-/

namespace Cslib.CongestedClique

namespace Prog

variable {V W : Type}

section Fintype

variable [Fintype V]

/-- The number of rounds of the run of `P` from `s` when `B` words cross every ordered pair per
round: a direct step of width `w` takes `⌈w / B⌉` rounds, a routed step `lenzenRounds` rounds. -/
def roundsAt (B : ℕ) : {σ ρ : Type} → Prog V W σ ρ → (V → σ) → ℕ
  | _, _, done _, _ => 0
  | _, _, step .direct send recv rest, s =>
      (width send s + B - 1) / B + rest.roundsAt B (next send recv s)
  | _, _, step .routed send recv rest, s => lenzenRounds + rest.roundsAt B (next send recv s)

@[simp] lemma roundsAt_done (B : ℕ) {σ : Type} (s : V → σ) :
    (done σ : Prog V W σ σ).roundsAt B s = 0 := rfl

lemma roundsAt_step_direct (B : ℕ) {σ τ ρ : Type} (send : V → σ → V → List W)
    (recv : V → σ → (V → List W) → τ) (rest : Prog V W τ ρ) (s : V → σ) :
    (step .direct send recv rest).roundsAt B s =
      (width send s + B - 1) / B + rest.roundsAt B (next send recv s) := rfl

lemma roundsAt_step_routed (B : ℕ) {σ τ ρ : Type} (send : V → σ → V → List W)
    (recv : V → σ → (V → List W) → τ) (rest : Prog V W τ ρ) (s : V → σ) :
    (step .routed send recv rest).roundsAt B s = lenzenRounds + rest.roundsAt B (next send recv s) :=
  rfl

@[simp] lemma roundsAt_append (B : ℕ) {σ τ ρ : Type} (P : Prog V W σ τ) (Q : Prog V W τ ρ)
    (s : V → σ) : (P.append Q).roundsAt B s = P.roundsAt B s + Q.roundsAt B (P.run s) := by
  induction P with
  | done => simp [append]
  | step m send recv rest ih =>
    cases m <;> simp only [append, roundsAt, run_step, ih] <;> omega

@[simp] lemma roundsAt_compute (B : ℕ) {σ τ : Type} (f : V → σ → τ) (s : V → σ) :
    (compute f : Prog V W σ τ).roundsAt B s = 0 := by
  have h : width (fun _ _ _ => ([] : List W)) s = 0 :=
    Nat.le_zero.mp ((width_le_iff _ _ 0).mpr fun _ _ => by simp)
  simp only [compute, roundsAt_step_direct, h, roundsAt_done]
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  · rw [Nat.div_eq_of_lt (by omega)]

/-- At bandwidth one word, `roundsAt` is `rounds`. -/
lemma roundsAt_one {σ ρ : Type} (P : Prog V W σ ρ) (s : V → σ) : P.roundsAt 1 s = P.rounds s := by
  induction P with
  | done => rfl
  | step m send recv rest ih =>
    cases m <;> simp [roundsAt, rounds, ih]

/-- `⌈w / B⌉ ≤ ⌈D / B⌉` for `w ≤ D`. -/
lemma ceilDiv_mono {w D : ℕ} (B : ℕ) (h : w ≤ D) : (w + B - 1) / B ≤ (D + B - 1) / B :=
  Nat.div_le_div_right (by omega)

/-- `⌈K / K⌉ = 1` for `0 < K`. -/
lemma ceilDiv_self {K : ℕ} (hK : 0 < K) : (K + K - 1) / K = 1 := by
  rw [Nat.div_eq_iff hK]
  omega

open Oblivious

/-- **Oblivious routing at bandwidth `B`** (Dolev, Lenzen, Peled, DISC 2012, Lemma 1): a direct
step whose pattern `A` is fixed in advance and has row and column sums at most `|V| * D` can be
executed in `2 * ⌈D / B⌉` rounds of bandwidth `B`; the words sent are among the words of the
original step. -/
theorem exists_oblivious_bw {σ τ : Type} (A : V → V → ℕ) (D B : ℕ)
    (hr : ∀ u, ∑ v, A u v ≤ Fintype.card V * D) (hc : ∀ v, ∑ u, A u v ≤ Fintype.card V * D)
    (send : V → σ → V → List W) (hlen : ∀ u x v, (send u x v).length = A u v)
    (recv : V → σ → (V → List W) → τ) :
    ∃ Q : Prog V W σ τ, ∀ s, Q.run s = next send recv s ∧
      Q.roundsAt B s ≤ 2 * ((D + B - 1) / B) ∧
      ∀ ok : W → Prop, (∀ u v, ∀ w ∈ send u (s u) v, ok w) → Q.Valid ok s := by
  obtain ⟨P, hPA, hPr, hPc⟩ := Matrix.exists_split_parts (ι := V) A D hr hc
  refine ⟨twoHop P send recv, fun s => ?_⟩
  have hseg : ∀ u x v m, (segI (fun m' => P m' u v) (send u x v) m).length = P m u v :=
    fun u x v m => length_segI _ _ (by rw [hlen, hPA]) m
  have hfwd : ∀ m v, (catI fun u => segI (fun v' => P m u v')
      (catI fun v' => segI (fun m' => P m' u v') (send u (s u) v') m) v) =
      catI fun u => segI (fun m' => P m' u v) (send u (s u) v) m := by
    intro m v
    congr 1; funext u
    rw [segI_catI _ _ (fun v' => hseg u (s u) v' m)]
  refine ⟨?_, ?_, ?_⟩
  · funext v
    simp only [twoHop, run_step, run_done, next, hfwd]
    congr 1; funext u
    have h1 : ∀ m, segI (fun u' => P m u' v)
        (catI fun u => segI (fun m' => P m' u v) (send u (s u) v) m) u =
        segI (fun m' => P m' u v) (send u (s u) v) m := fun m => by
      rw [segI_catI _ _ (fun u' => hseg u' (s u') v m)]
    simp only [h1]
    exact catI_segI _ _ (by rw [hlen, hPA])
  · simp only [twoHop, roundsAt_step_direct, roundsAt_done]
    have h1 : width (fun u x m => catI fun v => segI (fun m' => P m' u v) (send u x v) m) s ≤ D := by
      rw [width_le_iff]
      intro u m
      simp only [length_catI, hseg]
      exact hPr m u
    have h2 : width (fun m (y : σ × (V → List W)) v =>
        catI fun u => segI (fun v' => P m u v') (y.2 u) v)
        (next (fun u x m => catI fun v => segI (fun m' => P m' u v) (send u x v) m)
          (fun _ x r => (x, r)) s) ≤ D := by
      rw [width_le_iff]
      intro m v
      simp only [next, hfwd, length_catI, hseg]
      exact hPc m v
    have := ceilDiv_mono B h1
    have := ceilDiv_mono B h2
    omega
  · intro ok hok
    simp only [twoHop, Valid, next, hfwd]
    refine ⟨?_, by simp, ?_, by simp, trivial⟩
    · intro u m w hw
      obtain ⟨v, hv⟩ := mem_catI.mp hw
      exact hok u v w (mem_of_mem_segI hv)
    · intro m v w hw
      obtain ⟨u, hu⟩ := mem_catI.mp hw
      exact hok u v w (mem_of_mem_segI hu)

/-- Decoding a word indexed by a slot from a list of words sent in the order of a slot list. -/
lemma getD_map_idxOf {S : Type} [DecidableEq S] (l : List S) (f : S → W) (d : W) {t : S}
    (ht : t ∈ l) : (l.map f).getD (l.idxOf t) d = f t := by
  have hlt : l.idxOf t < l.length := List.idxOf_lt_length_of_mem ht
  rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map, List.getElem_idxOf]

/-- **Slot communication.** For every ordered pair `(u, v)` a fixed finite set `L u v` of slots is
given, with row and column sums of the cardinalities at most `|V| * D`. Node `u` in state `x`
sends to `v` the word `enc u x t` for every slot `t ∈ L u v`; node `v` then knows, for every `u`
and every slot `t ∈ L u v`, the word `enc u (s u) t` (and the default word for the other slots).
This takes `2 * ⌈D / B⌉` rounds of bandwidth `B`. -/
theorem exists_slots [Inhabited W] {σ τ S : Type} [DecidableEq S] (L : V → V → Finset S)
    (D B : ℕ) (hr : ∀ u, ∑ v, (L u v).card ≤ Fintype.card V * D)
    (hc : ∀ v, ∑ u, (L u v).card ≤ Fintype.card V * D)
    (enc : V → σ → S → W) (recv : V → σ → (V → S → W) → τ) :
    ∃ Q : Prog V W σ τ, ∀ s, Q.run s =
        (fun v => recv v (s v) fun u t => if t ∈ L u v then enc u (s u) t else default) ∧
      Q.roundsAt B s ≤ 2 * ((D + B - 1) / B) ∧
      ∀ ok : W → Prop, (∀ u v, ∀ t ∈ L u v, ok (enc u (s u) t)) → Q.Valid ok s := by
  obtain ⟨Q, hQ⟩ := exists_oblivious_bw (fun u v => (L u v).card) D B hr hc
    (fun u x v => (L u v).toList.map (enc u x)) (fun u x v => by simp)
    (fun v x m => recv v x fun u t =>
      if t ∈ L u v then (m u).getD ((L u v).toList.idxOf t) default else default)
  refine ⟨Q, fun s => ⟨?_, (hQ s).2.1, fun ok hok => (hQ s).2.2 ok ?_⟩⟩
  · rw [(hQ s).1]
    funext v
    simp only [next]
    congr 1
    funext u t
    split_ifs with ht
    · exact getD_map_idxOf _ _ _ (Finset.mem_toList.mpr ht)
    · rfl
  · intro u v w hw
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
    exact hok u v t (Finset.mem_toList.mp ht)

end Fintype

end Prog

end Cslib.CongestedClique
