import Podc.Computability.Distributed.CongestedClique.Oblivious

/-!
# Theorem 1 (semiring part): the 3D algorithm (Censor-Hillel et al., PODC 2015)

Section 2.1 of [Censor-Hillel, Kaski, Korhonen, Lenzen, Paz, Suomela, *Algebraic Methods in the
Congested Clique*, PODC 2015]: on the congested clique with `n = q³` nodes, the product of two
`n × n` matrices over a semiring, where node `v` holds row `v` of both factors and must output row
`v` of the product, can be computed in `O(n^{1/3})` rounds. Here: at most `6 q` rounds, with one
semiring element per word.

Nodes are triples `v = (v₁, v₂, v₃) ∈ [q]³` (`Node q`). Node `v` computes the block
`P^(v₂)[v₁∗∗, v₃∗∗] = S[v₁∗∗, v₂∗∗] T[v₂∗∗, v₃∗∗]`:

* Step 1a: `v` sends `S[v, u₂∗∗]` to every `u ∈ v₁∗∗`;
* Step 1b: `v` sends `T[v, u₃∗∗]` to every `u ∈ ∗v₁∗` (the paper says `u ∈ ∗v₂∗`, a typo, see
  `step1_as_written_wrong`), so that `u` receives `T[w, u₃∗∗]` from every `w ∈ u₂∗∗`;
* Step 2 (local, done on receipt in Step 1b): `v` multiplies its blocks;
* Step 3: `v` sends `P^(v₂)[u, v₃∗∗]` to every `u ∈ v₁∗∗`;
* Step 4 (local, done on receipt in Step 3): `u` sums `P[u, ∗] = ∑_w P^(w)[u, ∗]`.

Each communication step has a fixed pattern in which every node sends and receives `q⁴ = n · q`
words, so by oblivious routing (`Cslib.CongestedClique.Prog.exists_oblivious`) it takes `2 q`
rounds. (The paper merges Steps 1a and 1b, with `2 q⁴` words per node, which also gives `4 q`
rounds.) Blocks `X[u, a∗∗]` are sent as lists of `q²` words in the order of `finProdFinEquiv`.
-/

namespace Podc.AlgebraicCongestedClique

open Finset Cslib.CongestedClique

/-- Nodes of the clique with `n = q³` nodes, as triples `(v₁, v₂, v₃)`. -/
abbrev Node (q : ℕ) := Fin q × Fin q × Fin q

section Blocks

variable {R : Type} {q : ℕ}

/-- A block `g : [q] × [q] → R` as a list of `q²` words. -/
def blk (g : Fin q × Fin q → R) : List R := List.ofFn fun k => g (finProdFinEquiv.symm k)

/-- Entry `ab` of a block received as a list (`0` if the list is too short). -/
def getB [Zero R] (l : List R) (ab : Fin q × Fin q) : R := l.getD (finProdFinEquiv ab) 0

@[simp] lemma length_blk (g : Fin q × Fin q → R) : (blk g).length = q * q := by simp [blk]

@[simp] lemma getB_blk [Zero R] (g : Fin q × Fin q → R) (ab : Fin q × Fin q) :
    getB (blk g) ab = g ab := by
  have h : (finProdFinEquiv ab : ℕ) < (blk g).length := by
    simpa using (finProdFinEquiv ab).isLt
  rw [getB, List.getD_eq_getElem _ _ h]
  simp only [blk, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]

end Blocks

section Counting

variable {q : ℕ}

lemma sum_ite_fst (a : Fin q) :
    ∑ v : Node q, (if v.1 = a then q * q else 0) = q * q * (q * q) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma sum_ite_fst' (a : Fin q) :
    ∑ v : Node q, (if a = v.1 then q * q else 0) = q * q * (q * q) := by
  simp_rw [eq_comm (a := a)]
  exact sum_ite_fst a

lemma sum_ite_snd (a : Fin q) :
    ∑ v : Node q, (if v.2.1 = a then q * q else 0) = q * q * (q * q) := by
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl fun x _ => ?_).trans
    (by simp; ring : ∑ _x : Fin q, q * q * q = _)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp; ring

lemma card_node : Fintype.card (Node q) = q * (q * q) := by simp

lemma qqqq_le : q * q * (q * q) ≤ Fintype.card (Node q) * q := by
  rw [card_node]; exact le_of_eq (by ring)

end Counting

variable (R : Type) [NonUnitalNonAssocSemiring R] (q : ℕ)

/-- States: input (rows of `S` and `T`). -/
abbrev St0 := (Node q → R) × (Node q → R)
/-- States after Step 1a: the row of `T`, and the block `S[v₁∗∗, v₂∗∗]` (`Sb u ab = S[u, v₂ ab]`). -/
abbrev St1 := (Node q → R) × (Node q → Fin q × Fin q → R)
/-- States after Step 1b + Step 2: the block `P^(v₂)[v₁∗∗, v₃∗∗]`
(`Pb u ab = P^(v₂)[u, v₃ ab]`). -/
abbrev St2 := Node q → Fin q × Fin q → R

/-! The steps of the 3D algorithm live in the namespace `ThreeD` (the 4-cycle algorithm uses the
same step names). -/

namespace ThreeD

/-- Step 1a: `v` sends `S[v, u₂∗∗]` to `u` if `u₁ = v₁`. -/
def send1 (v : Node q) (x : St0 R q) (u : Node q) : List R :=
  if u.1 = v.1 then blk fun ab => x.1 (u.2.1, ab) else []

/-- Step 1a, receipt: keep the row of `T`, store `S[u, v₂∗∗]` received from `u`. -/
def recv1 (_v : Node q) (x : St0 R q) (m : Node q → List R) : St1 R q :=
  (x.2, fun u ab => getB (m u) ab)

/-- Step 1b (corrected): `w` sends `T[w, v₃∗∗]` to `v` if `v₂ = w₁`, i.e. `v ∈ ∗w₁∗`. -/
def send2 (w : Node q) (y : St1 R q) (v : Node q) : List R :=
  if v.2.1 = w.1 then blk fun ab => y.1 (v.2.2, ab) else []

/-- Step 1b receipt and Step 2: `v` computes `P^(v₂)[u, v₃ ab] = ∑_c S[u, v₂ c] T[v₂ c, v₃ ab]`. -/
def recv2 (v : Node q) (y : St1 R q) (m : Node q → List R) : St2 R q :=
  fun u ab => ∑ c : Fin q × Fin q, y.2 u c * getB (m (v.2.1, c)) ab

/-- Step 3: `v` sends `P^(v₂)[u, v₃∗∗]` to `u` if `u₁ = v₁`. -/
def send3 (v : Node q) (z : St2 R q) (u : Node q) : List R :=
  if u.1 = v.1 then blk (z u) else []

/-- Step 3 receipt and Step 4: `u` computes `P[u, x] = ∑_c P^(c)[u, x]`, receiving
`P^(c)[u, x₁∗∗]` from `(u₁, c, x₁)`. -/
def recv3 (u : Node q) (_z : St2 R q) (m : Node q → List R) : Node q → R :=
  fun x => ∑ c : Fin q, getB (m (u.1, c, x.1)) x.2

end ThreeD

open ThreeD in
/-- Theorem 1 (semiring part) of [Censor-Hillel et al., PODC 2015]: on the congested clique with
`n = q³` nodes, where node `v` holds rows `S[v, ∗]` and `T[v, ∗]` of two matrices over a semiring,
every node `v` can compute row `(ST)[v, ∗]` in `O(n^{1/3})` rounds — here `6 n^{1/3} = 6 q` rounds
of direct communication, one semiring element per word (the 3D algorithm with oblivious routing). -/
theorem theorem_1_semiring :
    ∃ P : Prog (Node q) R ((Node q → R) × (Node q → R)) (Node q → R),
      ∀ S T : Matrix (Node q) (Node q) R,
        P.run (fun v => (S v, T v)) = (fun v => (S * T) v) ∧
        P.rounds (fun v => (S v, T v)) ≤ 6 * q ∧
        P.Valid (fun _ => True) (fun v => (S v, T v)) := by
  have hb := @qqqq_le q
  obtain ⟨Q1, hQ1⟩ := Prog.exists_oblivious (fun v u : Node q => if u.1 = v.1 then q * q else 0) q
    (fun v => (sum_ite_fst v.1).trans_le hb) (fun u => (sum_ite_fst' u.1).trans_le hb)
    (send1 R q) (fun v x u => by unfold send1; split_ifs <;> simp) (recv1 R q)
  obtain ⟨Q2, hQ2⟩ := Prog.exists_oblivious
    (fun w v : Node q => if v.2.1 = w.1 then q * q else 0) q
    (fun w => (sum_ite_snd w.1).trans_le hb) (fun v => (sum_ite_fst' v.2.1).trans_le hb)
    (send2 R q) (fun w y v => by unfold send2; split_ifs <;> simp) (recv2 R q)
  obtain ⟨Q3, hQ3⟩ := Prog.exists_oblivious (fun v u : Node q => if u.1 = v.1 then q * q else 0) q
    (fun v => (sum_ite_fst v.1).trans_le hb) (fun u => (sum_ite_fst' u.1).trans_le hb)
    (send3 R q) (fun v z u => by unfold send3; split_ifs <;> simp) (recv3 R q)
  refine ⟨Q1.append (Q2.append Q3), fun S T => ?_⟩
  set s : Node q → St0 R q := fun v => (S v, T v)
  obtain ⟨r1, c1, v1⟩ := hQ1 s
  obtain ⟨r2, c2, v2⟩ := hQ2 (Q1.run s)
  obtain ⟨r3, c3, v3⟩ := hQ3 (Q2.run (Q1.run s))
  refine ⟨?_, ?_, ?_⟩
  · rw [Prog.run_append, Prog.run_append, r3, r2, r1]
    funext u x
    simp only [Prog.next, recv3, send3, recv2, send2, recv1, send1, s, ite_true, getB_blk,
      Matrix.mul_apply]
    rw [Fintype.sum_prod_type]
  · rw [Prog.rounds_append, Prog.rounds_append]
    omega
  · rw [Prog.valid_append, Prog.valid_append]
    exact ⟨v1 _ (by simp), v2 _ (by simp), v3 _ (by simp)⟩

/-! ### The typo in Step 1 -/

/-- Step 1 as written in the paper: node `w` sends `T[w, v₃∗∗]` to every `v ∈ ∗w₂∗`. -/
def step1TRecipientAsWritten {q : ℕ} (w v : Node q) : Prop := v.2.1 = w.2.1

/-- Step 1 corrected: node `w` sends `T[w, v₃∗∗]` to every `v ∈ ∗w₁∗` (as in `send2`). -/
def step1TRecipient {q : ℕ} (w v : Node q) : Prop := v.2.1 = w.1

/-- The typo in Step 1 of the paper: node `v` needs the rows `T[w, ∗]` for all `w ∈ v₂∗∗`
(to compute `S[v₁∗∗, v₂∗∗] T[v₂∗∗, v₃∗∗]`), but with the pattern as written (`T[w, v₃∗∗]` sent
to `v ∈ ∗w₂∗`) some needed row is never sent to `v`, as soon as `q ≥ 2`. -/
theorem step1_as_written_wrong {q : ℕ} (hq : 2 ≤ q) (v : Node q) :
    ∃ w : Node q, w.1 = v.2.1 ∧ ¬ step1TRecipientAsWritten w v := by
  have : Nontrivial (Fin q) := Fin.nontrivial_iff_two_le.mpr hq
  obtain ⟨b, hb⟩ := exists_ne v.2.1
  exact ⟨(v.2.1, b, v.2.2), rfl, fun h => hb h.symm⟩

/-- With the corrected pattern, every needed row `T[w, v₃∗∗]`, `w ∈ v₂∗∗`, is sent to `v`. -/
theorem step1_corrected (q : ℕ) (v w : Node q) (hw : w.1 = v.2.1) : step1TRecipient w v :=
  hw.symm

end Podc.AlgebraicCongestedClique
