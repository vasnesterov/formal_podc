import Papers.PODC2026.LocalComputable.Concrete
import Papers.PODC2026.LocalComputable.Collapse
import Papers.PODC2026.LocalComputable.Decide
import Cslib.Computability.Primrec.List

/-!
# Computability of the concrete LOCAL model

The abstract Section 5 results (`classII_iff`, `classIII_iff`, `critical_decidable`) assume that
networks are `Primcodable`, that sizes and views are computable, and that the networks with at
most `N` nodes form a computable list. Here we discharge all of these assumptions for the concrete
LOCAL model of Section 3 (`concreteModel Δ c k` in `Concrete.lean`), so that only the genuinely
problem-specific hypotheses remain (computable locality `T`, computable `f`, computable validity
check).

* `PNet` is `Primcodable` (as a tuple), well-formedness is a primitive recursive predicate
  (`PNet.wfb`, `PNet.primrecPred_WF`), hence `Net Δ c k` is `Primcodable` (subtype).
* Views are coded injectively by natural numbers (`VTree.code`, `VTree.code_injective`);
  `concreteModelN Δ c k` is the concrete model with coded views, distinguishing exactly the same
  views (`concreteModelN_view_eq_iff`, `critical_code_iff`), and with the same solvable problems
  for arbitrary algorithms (`exists_solves_iff`, `exists_solvesWith_iff`).
* Views are computed by dynamic programming over the radius (`PNet.viewCode`, primitive
  recursive), giving `computable_size` and `computable_view`.
* `netsN Δ c k N` enumerates all well-formed networks with at most `N` nodes (`mem_netsN`,
  `primrec_netsN`), by brute force over raw networks followed by a well-formedness filter.
* End-to-end corollaries: `concrete_classII`, `concrete_uncomputable_iff_computable`,
  `concrete_classIII`, `concrete_critical_decidable`, `concrete_critical_decidable'`.

Computable-LOCAL algorithms in the corollaries read coded views (natural numbers); this is the
standard way to feed a finite labelled graph to a Turing machine.
-/

namespace LocalComputable

/-! ### Generic helpers -/

section Helpers

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- Boolean test for `List.Nodup`. -/
def nodupb [DecidableEq β] (l : List β) : Bool :=
  List.recOn l true fun b l' IH => !(l'.any (· == b)) && IH

omit [Primcodable β] in
/-- `nodupb` decides `List.Nodup`. -/
theorem nodupb_iff [DecidableEq β] (l : List β) : nodupb l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupb]
  | cons b l ih =>
    simp only [nodupb] at ih ⊢
    simp only [List.nodup_cons, ← ih]
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
      beq_iff_eq]
    exact and_congr_left fun _ => ⟨fun h hb => h b hb rfl, fun h x hx hxb => h (hxb ▸ hx)⟩

/-- `List.Nodup` is a primitive recursive predicate. -- CSLib candidate -/
theorem primrec_nodupb [DecidableEq β] : Primrec (nodupb (β := β)) :=
  (Primrec.list_rec Primrec.id (Primrec.const true)
    (Primrec.and.comp (Primrec.not.comp (Primrec.list_any (Primrec.fst.comp (Primrec.snd.comp
      Primrec.snd)) (Primrec.beq.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp
        Primrec.fst))).to₂))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun _ => rfl

end Helpers

/-! ### Encoding raw networks -/

namespace PNet

/-- A raw network as a tuple `(n, nbr, id, inp)`. -/
def equivTuple : PNet ≃ ℕ × List (List ℕ) × List ℕ × List ℕ where
  toFun G := (G.n, G.nbr, G.id, G.inp)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Raw networks are `Primcodable`, via `equivTuple`. -/
instance : Primcodable PNet := Primcodable.ofEquiv _ equivTuple

/-- The tuple encoding is primitive recursive. -/
theorem primrec_equivTuple : Primrec equivTuple := Primrec.of_equiv

/-- Building a raw network from its fields is primitive recursive. -/
theorem primrec_mk' :
    Primrec fun x : ℕ × List (List ℕ) × List ℕ × List ℕ => PNet.mk x.1 x.2.1 x.2.2.1 x.2.2.2 :=
  Primrec.of_equiv_symm (e := equivTuple)

/-- The number of nodes is primitive recursive. -/
theorem primrec_n : Primrec PNet.n := Primrec.fst.comp primrec_equivTuple

/-- The neighbour lists are primitive recursive. -/
theorem primrec_nbr : Primrec PNet.nbr := Primrec.fst.comp (Primrec.snd.comp primrec_equivTuple)

/-- The identifier list is primitive recursive. -/
theorem primrec_id : Primrec PNet.id :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp primrec_equivTuple))

/-- The input list is primitive recursive. -/
theorem primrec_inp : Primrec PNet.inp :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp primrec_equivTuple))

/-- `nbrOf` is primitive recursive. -/
theorem primrec_nbrOf : Primrec₂ PNet.nbrOf :=
  (Primrec.list_getD []).comp (primrec_nbr.comp Primrec.fst) Primrec.snd

/-- `idOf` is primitive recursive. -/
theorem primrec_idOf : Primrec₂ PNet.idOf :=
  (Primrec.list_getD 0).comp (primrec_id.comp Primrec.fst) Primrec.snd

/-- `inpOf` is primitive recursive. -/
theorem primrec_inpOf : Primrec₂ PNet.inpOf :=
  (Primrec.list_getD 0).comp (primrec_inp.comp Primrec.fst) Primrec.snd

end PNet

/-! ### Coding views by natural numbers -/

namespace VTree

open Encodable in
/-- An injective code of views by natural numbers. -/
def code : VTree → ℕ
  | node i p d ks => Nat.pair i (Nat.pair p (Nat.pair d (encode (ks.map code))))

/-- The defining equation of `code`. -/
theorem code_node (i p d : ℕ) (ks : List VTree) :
    code (node i p d ks) =
      Nat.pair i (Nat.pair p (Nat.pair d (Encodable.encode (ks.map code)))) := by
  rw [code]

/-- If `map f` identifies two lists and `f` is injective on the first one, they are equal. -/
theorem map_eq_map_of_injOn {γ δ : Type*} {f : γ → δ} :
    ∀ {l l' : List γ}, (∀ a ∈ l, ∀ b, f a = f b → a = b) → l.map f = l'.map f → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l, b :: l', hf, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf a (by simp) b h.1, map_eq_map_of_injOn (fun x hx => hf x (by simp [hx])) h.2]

/-- Injectivity of `code`, by well-founded recursion on views. -/
theorem code_inj : ∀ x y : VTree, code x = code y → x = y
  | node i p d ks, node i' p' d' ks', h => by
    simp only [code_node, Nat.pair_eq_pair, Encodable.encode_inj] at h
    obtain ⟨rfl, rfl, rfl, h⟩ := h
    have : ks = ks' := map_eq_map_of_injOn (fun a ha b hab => code_inj a b hab) h
    rw [this]
termination_by x => sizeOf x
decreasing_by
  have := List.sizeOf_lt_of_mem ha
  simp_wf
  omega

/-- Views are coded injectively. -/
theorem code_injective : Function.Injective code := fun x y h => code_inj x y h

end VTree

/-! ### The concrete model with coded views -/

/-- **The LOCAL model of Section 3 with views coded by natural numbers**: the same networks and
sizes as `concreteModel`, the view of `v` at radius `t` being the code of `fview G v t`. -/
def concreteModelN (Δ c k : ℕ) : Model (Net Δ c k) ℕ where
  size G := G.1.n
  view G v t := (fview G.1 v t).code
  restrict h he := by rw [fview_restrict h (VTree.code_injective he)]

/-- The coded model distinguishes exactly the same views as `concreteModel`. -/
theorem concreteModelN_view_eq_iff {Δ c k : ℕ} (G G' : Net Δ c k) (v v' t : ℕ) :
    (concreteModelN Δ c k).view G v t = (concreteModelN Δ c k).view G' v' t ↔
      (concreteModel Δ c k).view G v t = (concreteModel Δ c k).view G' v' t :=
  VTree.code_injective.eq_iff

/-! ### Deciding well-formedness -/

namespace PNet

/-- Boolean check of the per-node conditions of `PNet.WF`. -/
def nodeOk (Δ c k : ℕ) (G : PNet) (v : ℕ) : Bool :=
  nodupb (G.nbrOf v) && decide ((G.nbrOf v).length ≤ Δ) &&
    (G.nbrOf v).all (fun u => decide (u < G.n) && (G.nbrOf u).any (· == v)) &&
    !((G.nbrOf v).any (· == v)) &&
    (List.range G.n).all (fun u => !(G.idOf u == G.idOf v) || (u == v)) &&
    decide (1 ≤ G.idOf v) && decide (G.idOf v ≤ G.n ^ c) && decide (G.inpOf v < k)

/-- Boolean check of `PNet.WF`. -/
def wfb (Δ c k : ℕ) (G : PNet) : Bool :=
  (G.nbr.length == G.n) && (G.id.length == G.n) && (G.inp.length == G.n) &&
    (List.range G.n).all (nodeOk Δ c k G)

/-- `wfb` decides well-formedness. -/
theorem wfb_iff {Δ c k : ℕ} {G : PNet} : wfb Δ c k G = true ↔ G.WF Δ c k := by
  simp only [wfb, nodeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, List.any_eq_true, nodupb_iff, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.any_eq_false, Bool.or_eq_true, beq_eq_false_iff_ne, exists_eq_right]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun v hv => (h4 v hv).1.1.1.1.1.1.1, fun v hv => (h4 v hv).1.1.1.1.1.1.2,
      fun v hv u hu => ((h4 v hv).1.1.1.1.1.2 u hu).1,
      fun v hv hmem => (h4 v hv).1.1.1.1.2 v hmem rfl,
      fun v hv u hu => ((h4 v hv).1.1.1.1.1.2 u hu).2,
      fun u hu v hv he => ((h4 v hv).1.1.1.2 u hu).resolve_left (not_not_intro he),
      fun v hv => (h4 v hv).1.1.2, fun v hv => (h4 v hv).1.2, fun v hv => (h4 v hv).2⟩
  · intro h
    exact ⟨⟨⟨h.len_nbr, h.len_id⟩, h.len_inp⟩, fun v hv => ⟨⟨⟨⟨⟨⟨⟨h.nodup v hv, h.deg_le v hv⟩,
      fun u hu => ⟨h.nbr_lt v hv u hu, h.symm v hv u hu⟩⟩,
      fun u hu hue => h.irrefl v hv (hue ▸ hu)⟩,
      fun u hu => (em (G.idOf u = G.idOf v)).elim (fun he => Or.inr (h.id_inj u hu v hv he))
        Or.inl⟩, h.id_pos v hv⟩, h.id_le v hv⟩, h.inp_lt v hv⟩⟩

open Primrec in
/-- The per-node check is primitive recursive. -/
theorem primrec_nodeOk (Δ c k : ℕ) : Primrec fun q : PNet × ℕ => nodeOk Δ c k q.1 q.2 := by
  have hNB : Primrec fun q : PNet × ℕ => q.1.nbrOf q.2 := primrec_nbrOf.comp fst snd
  have hn : Primrec fun q : PNet × ℕ => q.1.n := primrec_n.comp fst
  have hid : Primrec fun q : PNet × ℕ => q.1.idOf q.2 := primrec_idOf.comp fst snd
  have hinp : Primrec fun q : PNet × ℕ => q.1.inpOf q.2 := primrec_inpOf.comp fst snd
  have h1 : Primrec fun q : PNet × ℕ => nodupb (q.1.nbrOf q.2) := primrec_nodupb.comp hNB
  have h2 : Primrec fun q : PNet × ℕ => decide ((q.1.nbrOf q.2).length ≤ Δ) :=
    nat_le.decide.comp (list_length.comp hNB) (const Δ)
  have h3 : Primrec fun q : PNet × ℕ =>
      (q.1.nbrOf q.2).all (fun u => decide (u < q.1.n) && (q.1.nbrOf u).any (· == q.2)) := by
    refine Primrec.list_all hNB ?_
    refine Primrec.and.comp (nat_lt.decide.comp snd (hn.comp fst)) ?_
    exact Primrec.list_any (primrec_nbrOf.comp (fst.comp fst) snd)
      (Primrec.beq.comp snd (snd.comp (fst.comp fst))).to₂
  have h4 : Primrec fun q : PNet × ℕ => !((q.1.nbrOf q.2).any (· == q.2)) :=
    Primrec.not.comp (Primrec.list_any hNB (Primrec.beq.comp snd (snd.comp fst)).to₂)
  have h5 : Primrec fun q : PNet × ℕ =>
      (List.range q.1.n).all (fun u => !(q.1.idOf u == q.1.idOf q.2) || (u == q.2)) :=
    Primrec.list_all (list_range.comp hn) (Primrec.or.comp (Primrec.not.comp
      (Primrec.beq.comp (primrec_idOf.comp (fst.comp fst) snd) (hid.comp fst)))
      (Primrec.beq.comp snd (snd.comp fst))).to₂
  have h6 : Primrec fun q : PNet × ℕ => decide (1 ≤ q.1.idOf q.2) :=
    nat_le.decide.comp (const 1) hid
  have h7 : Primrec fun q : PNet × ℕ => decide (q.1.idOf q.2 ≤ q.1.n ^ c) :=
    nat_le.decide.comp hid (Primrec.nat_pow.comp hn (const c))
  have h8 : Primrec fun q : PNet × ℕ => decide (q.1.inpOf q.2 < k) :=
    nat_lt.decide.comp hinp (const k)
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp h1 h2) h3) h4) h5) h6) h7) h8

open Primrec in
/-- The well-formedness check is primitive recursive. -/
theorem primrec_wfb (Δ c k : ℕ) : Primrec (wfb Δ c k) :=
  Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.beq.comp (list_length.comp primrec_nbr) primrec_n)
    (Primrec.beq.comp (list_length.comp primrec_id) primrec_n))
    (Primrec.beq.comp (list_length.comp primrec_inp) primrec_n))
    (Primrec.list_all (list_range.comp primrec_n) (primrec_nodeOk Δ c k).to₂)

/-- Well-formedness is decidable (via `wfb`). -/
instance (Δ c k : ℕ) : DecidablePred (PNet.WF Δ c k) := fun _ => decidable_of_iff _ wfb_iff

/-- Well-formedness of networks is a primitive recursive predicate. -/
theorem primrecPred_WF (Δ c k : ℕ) : PrimrecPred (PNet.WF Δ c k) :=
  Primrec.primrecPred ((primrec_wfb Δ c k).of_eq fun G => by
    rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact wfb_iff)

end PNet

/-- Well-formed networks are `Primcodable` (a primitive recursive subtype of `PNet`). -/
instance (Δ c k : ℕ) : Primcodable (Net Δ c k) := Primcodable.subtype (PNet.primrecPred_WF Δ c k)

/-- The underlying raw network of a well-formed network is primitive recursive. -/
theorem primrec_net_val (Δ c k : ℕ) : Primrec fun G : Net Δ c k => G.1 :=
  Primrec.subtype_val

/-! ### Computing views -/

namespace PNet

open Encodable

/-- The code of the radius-`0` view of `w`. -/
def leafCode (G : PNet) (w : ℕ) : ℕ :=
  Nat.pair (G.idOf w) (Nat.pair (G.inpOf w) (Nat.pair (G.nbrOf w).length (encode ([] : List ℕ))))

/-- The code of the radius-`(t+1)` view of `w`, given the list `L` of the radius-`t` view codes. -/
def stepCode (G : PNet) (L : List ℕ) (w : ℕ) : ℕ :=
  Nat.pair (G.idOf w) (Nat.pair (G.inpOf w) (Nat.pair (G.nbrOf w).length
    (encode ((G.nbrOf w).map fun u => L.getD u 0))))

/-- The codes of the radius-`t` views of the nodes `0, …, m-1`. -/
def codes (G : PNet) (m : ℕ) : ℕ → List ℕ
  | 0 => (List.range m).map (leafCode G)
  | t + 1 => (List.range m).map (stepCode G (codes G m t))

/-- The code of the radius-`t` view of `v`, computed by dynamic programming over the radius. -/
def viewCode (G : PNet) (v t : ℕ) : ℕ := (codes G (max G.n (v + 1)) t).getD v 0

/-- Correctness of the dynamic programme, for a set of nodes `0, …, m-1` closed under
neighbours. -/
theorem codes_getD {G : PNet} {m : ℕ} (hm : ∀ w < m, ∀ u ∈ G.nbrOf w, u < m) (t : ℕ) :
    ∀ w < m, (codes G m t).getD w 0 = (fview G w t).code := by
  induction t with
  | zero =>
    intro w hw
    simp [codes, fview, VTree.code_node, leafCode, hw]
  | succ t ih =>
    intro w hw
    simp only [codes, fview, VTree.code_node, stepCode, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range hw, Option.map_some, Option.getD_some, List.map_map]
    congr 4
    refine List.map_congr_left fun u hu => ?_
    rw [← List.getD_eq_getElem?_getD]
    exact ih u (hm w hw u hu)

/-- In a well-formed network, `viewCode` computes the code of the view of every `v` (also for
`v ≥ n`, where `v` is an isolated node with identifier and input `0`). -/
theorem viewCode_eq {Δ c k : ℕ} {G : PNet} (hG : G.WF Δ c k) (v t : ℕ) :
    G.viewCode v t = (fview G v t).code := by
  refine codes_getD (fun w hw u hu => ?_) t v (by omega)
  by_cases hwn : w < G.n
  · exact lt_max_of_lt_left (hG.nbr_lt w hwn u hu)
  · simp [nbrOf, List.getElem?_eq_none (show G.nbr.length ≤ w by rw [hG.len_nbr]; omega)] at hu

open Primrec in
/-- The dynamic programme is primitive recursive. -/
theorem primrec_codes : Primrec fun q : PNet × ℕ × ℕ => codes q.1 q.2.1 q.2.2 := by
  have hleaf : Primrec₂ leafCode :=
    Primrec₂.natPair.comp primrec_idOf (Primrec₂.natPair.comp primrec_inpOf
      (Primrec₂.natPair.comp (list_length.comp primrec_nbrOf) (const _)))
  have hstep : Primrec fun r : PNet × List ℕ × ℕ => stepCode r.1 r.2.1 r.2.2 := by
    have hNB : Primrec fun r : PNet × List ℕ × ℕ => r.1.nbrOf r.2.2 :=
      primrec_nbrOf.comp fst (snd.comp snd)
    exact Primrec₂.natPair.comp (primrec_idOf.comp fst (snd.comp snd))
      (Primrec₂.natPair.comp (primrec_inpOf.comp fst (snd.comp snd))
      (Primrec₂.natPair.comp (list_length.comp hNB) (Primrec.encode.comp
        (list_map hNB ((list_getD 0).comp (fst.comp (snd.comp fst)) snd).to₂))))
  refine (nat_rec' (f := fun q : PNet × ℕ × ℕ => q.2.2)
    (g := fun q => (List.range q.2.1).map (leafCode q.1))
    (h := fun q p => (List.range q.2.1).map (stepCode q.1 p.2)) (snd.comp snd)
    (list_map (list_range.comp (fst.comp snd)) (hleaf.comp (fst.comp fst) snd).to₂)
    (list_map (list_range.comp (fst.comp (snd.comp fst)))
      (hstep.comp (pair (fst.comp (fst.comp fst)) (pair (snd.comp (snd.comp fst)) snd))).to₂)).of_eq
    ?_
  rintro ⟨G, m, t⟩
  induction t with
  | zero => rfl
  | succ t ih => simp only [codes] at ih ⊢; rw [ih]

open Primrec in
/-- `viewCode` is primitive recursive. -/
theorem primrec_viewCode : Primrec fun q : PNet × ℕ × ℕ => viewCode q.1 q.2.1 q.2.2 :=
  (list_getD 0).comp (primrec_codes.comp (pair fst (pair (nat_max.comp (primrec_n.comp fst)
    (succ.comp (fst.comp snd))) (snd.comp snd)))) (fst.comp snd)

end PNet

/-- Sizes are computable in the coded concrete model. -/
theorem computable_size (Δ c k : ℕ) : Computable (concreteModelN Δ c k).size :=
  (PNet.primrec_n.comp (primrec_net_val Δ c k)).to_comp

/-- Views are computable in the coded concrete model. -/
theorem computable_view (Δ c k : ℕ) :
    Computable fun p : Net Δ c k × ℕ × ℕ => (concreteModelN Δ c k).view p.1 p.2.1 p.2.2 :=
  (PNet.primrec_viewCode.comp (Primrec.pair ((primrec_net_val Δ c k).comp Primrec.fst)
    Primrec.snd)).to_comp.of_eq fun p => PNet.viewCode_eq p.1.2 _ _

/-! ### Enumerating the networks with at most `N` nodes -/

/-- All lists of length `m` with entries from `xs`. -- CSLib candidate -/
def listsOfLen {β : Type*} (xs : List β) : ℕ → List (List β)
  | 0 => [[]]
  | m + 1 => (listsOfLen xs m).flatMap fun l => xs.map fun x => x :: l

/-- Membership in `listsOfLen`. -/
theorem mem_listsOfLen {β : Type*} {xs : List β} {m : ℕ} {l : List β} :
    l ∈ listsOfLen xs m ↔ l.length = m ∧ ∀ x ∈ l, x ∈ xs := by
  induction m generalizing l with
  | zero =>
    simp only [listsOfLen, List.mem_singleton, List.length_eq_zero_iff]
    exact ⟨fun h => ⟨h, by simp [h]⟩, fun h => h.1⟩
  | succ m ih =>
    cases l with
    | nil => simp [listsOfLen]
    | cons a l =>
      simp only [listsOfLen, List.mem_flatMap, List.mem_map, List.cons.injEq, ih,
        List.length_cons, List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨l', ⟨hl', hx'⟩, x, hx, rfl, rfl⟩
        exact ⟨hl', hx, hx'⟩
      · rintro ⟨hl, ha, hx⟩
        exact ⟨l, ⟨hl, hx⟩, a, ha, rfl, rfl⟩

open Primrec in
/-- `listsOfLen` is primitive recursive. -- CSLib candidate -/
theorem primrec_listsOfLen {β : Type*} [Primcodable β] : Primrec₂ (listsOfLen (β := β)) :=
  (nat_rec (f := fun _ => [[]]) (g := fun xs p => p.2.flatMap fun l => xs.map fun x => x :: l)
    (const _) (list_flatMap (snd.comp snd)
      (list_map (fst.comp fst) (list_cons.comp snd (snd.comp fst)).to₂).to₂)).of_eq
    fun xs m => by induction m <;> simp [listsOfLen, *]

/-- All raw networks with at most `N` nodes, neighbour lists of length `≤ Δ` with entries `< n`,
identifiers in `[0, n^c]` and inputs `< k` (a finite superset of the well-formed ones). -/
def rawNets (Δ c k N : ℕ) : List PNet :=
  (List.range (N + 1)).flatMap fun n =>
    (listsOfLen ((List.range (Δ + 1)).flatMap (listsOfLen (List.range n))) n).flatMap fun nbr =>
      (listsOfLen (List.range (n ^ c + 1)) n).flatMap fun id =>
        (listsOfLen (List.range k) n).map fun inp => PNet.mk n nbr id inp

/-- The raw networks of `rawNets Δ c k N` have at most `N` nodes. -/
theorem n_le_of_mem_rawNets {Δ c k N : ℕ} {G : PNet} (h : G ∈ rawNets Δ c k N) : G.n ≤ N := by
  simp only [rawNets, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨n, hn, -, -, -, -, -, -, rfl⟩ := h
  exact Nat.lt_succ_iff.mp hn

/-- Every well-formed network with at most `N` nodes is in `rawNets Δ c k N`. -/
theorem mem_rawNets_of_WF {Δ c k N : ℕ} {G : PNet} (hG : G.WF Δ c k) (hN : G.n ≤ N) :
    G ∈ rawNets Δ c k N := by
  have key : ∀ {l : List ℕ} {x : ℕ}, l.length = G.n → x ∈ l →
      ∃ v < G.n, l.getD v 0 = x := by
    intro l x hl hx
    obtain ⟨v, hv, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨v, hl ▸ hv, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]⟩
  simp only [rawNets, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨G.n, by omega, G.nbr, ?_, G.id, ?_, G.inp, ?_, rfl⟩
  · rw [mem_listsOfLen]
    refine ⟨hG.len_nbr, fun l hl => ?_⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_iff_getElem.mp hl
    have hv' : v < G.n := hG.len_nbr ▸ hv
    have hl' : G.nbr[v] = G.nbrOf v := by
      simp [PNet.nbrOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
    simp only [List.mem_flatMap, List.mem_range, mem_listsOfLen]
    refine ⟨(G.nbr[v]).length, ?_, rfl, fun u hu => ?_⟩
    · have := hG.deg_le v hv'; rw [hl']; omega
    · exact hG.nbr_lt v hv' u (hl' ▸ hu)
  · rw [mem_listsOfLen]
    refine ⟨hG.len_id, fun i hi => ?_⟩
    obtain ⟨v, hv, rfl⟩ := key hG.len_id hi
    exact List.mem_range.mpr (Nat.lt_succ_of_le (hG.id_le v hv))
  · rw [mem_listsOfLen]
    refine ⟨hG.len_inp, fun i hi => ?_⟩
    obtain ⟨v, hv, rfl⟩ := key hG.len_inp hi
    exact List.mem_range.mpr (hG.inp_lt v hv)

open Primrec in
/-- `rawNets` is primitive recursive. -/
theorem primrec_rawNets (Δ c k : ℕ) : Primrec (rawNets Δ c k) := by
  have hL3 : Primrec fun r : (ℕ × List (List ℕ)) × List ℕ =>
      (listsOfLen (List.range k) r.1.1).map fun inp => PNet.mk r.1.1 r.1.2 r.2 inp :=
    list_map (primrec_listsOfLen.comp (const _) (fst.comp fst))
      (PNet.primrec_mk'.comp (pair (fst.comp (fst.comp fst))
        (pair (snd.comp (fst.comp fst)) (pair (snd.comp fst) snd)))).to₂
  have hL2 : Primrec fun r : ℕ × List (List ℕ) =>
      (listsOfLen (List.range (r.1 ^ c + 1)) r.1).flatMap fun id =>
        (listsOfLen (List.range k) r.1).map fun inp => PNet.mk r.1 r.2 id inp :=
    list_flatMap (primrec_listsOfLen.comp
      (list_range.comp (succ.comp (Primrec.nat_pow.comp fst (const c)))) fst) hL3.to₂
  have hL1 : Primrec fun n : ℕ =>
      (listsOfLen ((List.range (Δ + 1)).flatMap (listsOfLen (List.range n))) n).flatMap
        fun nbr => (listsOfLen (List.range (n ^ c + 1)) n).flatMap fun id =>
          (listsOfLen (List.range k) n).map fun inp => PNet.mk n nbr id inp :=
    list_flatMap (primrec_listsOfLen.comp
      (list_flatMap (const _) (primrec_listsOfLen.comp (list_range.comp fst) snd).to₂) .id)
      hL2.to₂
  exact (list_flatMap (list_range.comp succ) (hL1.comp snd).to₂).of_eq fun _ => rfl

/-- The well-formed networks with at most `N` nodes, as a computable list. -/
def netsN (Δ c k N : ℕ) : List (Net Δ c k) :=
  (rawNets Δ c k N).filterMap fun G => Encodable.decode₂ (Net Δ c k) (Encodable.encode G)

/-- A well-formed network is encoded as its underlying raw network. -/
theorem encode_net {Δ c k : ℕ} (G : Net Δ c k) : Encodable.encode G = Encodable.encode G.1 := rfl

/-- `netsN Δ c k N` lists exactly the networks with at most `N` nodes. -/
theorem mem_netsN {Δ c k N : ℕ} {G : Net Δ c k} : G ∈ netsN Δ c k N ↔ G.1.n ≤ N := by
  simp only [netsN, List.mem_filterMap, Encodable.decode₂_eq_some, encode_net]
  constructor
  · rintro ⟨G', hG', he⟩
    rw [Encodable.encode_injective he]
    exact n_le_of_mem_rawNets hG'
  · intro h
    exact ⟨G.1, mem_rawNets_of_WF G.2 h, rfl⟩

/-- The enumeration of the networks with at most `N` nodes is primitive recursive. -/
theorem primrec_netsN (Δ c k : ℕ) : Primrec (netsN Δ c k) :=
  Primrec.listFilterMap (primrec_rawNets Δ c k)
    (Primrec.decode₂.comp (Primrec.encode.comp Primrec.snd)).to₂

/-! ### Transfer between tree views and coded views -/

section Transfer

variable {Δ c k : ℕ} {Out : Type*}

open Classical in
/-- An algorithm on tree views, run on coded views (`⊥` on numbers that code no view). -/
noncomputable def decodeAlg (A : Alg VTree Out) : Alg ℕ Out := fun x t =>
  if h : ∃ y : VTree, y.code = x then A h.choose t else none

/-- `decodeAlg A` behaves as `A` on codes of views. -/
theorem decodeAlg_code (A : Alg VTree Out) (y : VTree) (t : ℕ) :
    decodeAlg A y.code t = A y t := by
  unfold decodeAlg
  split
  next h => rw [VTree.code_injective h.choose_spec]
  next h => exact absurd ⟨y, rfl⟩ h

/-- `decodeAlg A` produces the same outputs in the coded model as `A` in the tree model. -/
theorem out_decodeAlg (A : Alg VTree Out) (G : Net Δ c k) (v r : ℕ) :
    (concreteModelN Δ c k).out (decodeAlg A) G v r = (concreteModel Δ c k).out A G v r := by
  unfold Model.out
  congr 1
  funext t
  exact decodeAlg_code A (fview G.1 v t) t

/-- `decodeAlg A` solves a problem in the coded model iff `A` does in the tree model. -/
theorem solvesOn_decodeAlg (P : (concreteModelN Δ c k).Problem Out) (A : Alg VTree Out)
    (T : ℕ → ℕ) (G : Net Δ c k) :
    (concreteModelN Δ c k).SolvesOn P (decodeAlg A) T G ↔
      (concreteModel Δ c k).SolvesOn P A T G := by
  unfold Model.SolvesOn
  simp only [out_decodeAlg]
  rfl

/-- An algorithm on coded views, precomposed with `code`, solves the same problems in the tree
model. -/
theorem solvesOn_comp_code (P : (concreteModelN Δ c k).Problem Out) (A : Alg ℕ Out)
    (T : ℕ → ℕ) (G : Net Δ c k) :
    (concreteModel Δ c k).SolvesOn P (fun x t => A x.code t) T G ↔
      (concreteModelN Δ c k).SolvesOn P A T G :=
  Iff.rfl

/-- Solvability (by arbitrary, possibly uncomputable algorithms, with any promise `Adm`) is the
same for tree views and for coded views. -/
theorem exists_solvesWith_iff (Adm : ℕ → Net Δ c k → Prop)
    (P : (concreteModelN Δ c k).Problem Out) (T : ℕ → ℕ) :
    (∃ A : ℕ → Alg VTree Out, (concreteModel Δ c k).SolvesWith Adm P A T) ↔
      ∃ A : ℕ → Alg ℕ Out, (concreteModelN Δ c k).SolvesWith Adm P A T := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨fun N => decodeAlg (A N), fun N G h => (solvesOn_decodeAlg P _ T G).mpr (hA N G h)⟩
  · rintro ⟨A, hA⟩
    exact ⟨fun N x t => A N x.code t, fun N G h => (solvesOn_comp_code P _ T G).mpr (hA N G h)⟩

/-- Solvability without information on `n` is the same for tree views and for coded views. -/
theorem exists_solves_iff (P : (concreteModelN Δ c k).Problem Out) (T : ℕ → ℕ) :
    (∃ A : Alg VTree Out, (concreteModel Δ c k).Solves P A T) ↔
      ∃ A : Alg ℕ Out, (concreteModelN Δ c k).Solves P A T := by
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨decodeAlg A, fun G => (solvesOn_decodeAlg P _ T G).mpr (hA G)⟩
  · rintro ⟨A, hA⟩
    exact ⟨fun x t => A x.code t, fun G => (solvesOn_comp_code P _ T G).mpr (hA G)⟩

/-- Critical views are the same for tree views and for coded views. -/
theorem critical_code_iff (T : ℕ → ℕ) (x : VTree) (t : ℕ) :
    (concreteModelN Δ c k).Critical T x.code t ↔ (concreteModel Δ c k).Critical T x t := by
  unfold Model.Critical
  refine exists_congr fun G => exists_congr fun v => and_congr_right fun _ => and_congr_left
    fun _ => VTree.code_injective.eq_iff

end Transfer

/-! ### End-to-end corollaries for the concrete model -/

section Corollaries

variable {Δ c k : ℕ} {Out : Type*} [Primcodable Out]

/-- **Table 1, class II, for the concrete LOCAL model of Section 3** (networks of maximum degree
`Δ`, identifiers in `[1, n^c]`, inputs `< k`; views coded by natural numbers). For a computable
locality `T`, a finite output alphabet and a computable validity check, the following are
equivalent: (1) uncomputable-LOCAL without information on `n` solves `P` with locality `T`;
(2) uncomputable-LOCAL with an upper bound `N ≥ n` does; (3) computable-LOCAL with an upper bound
`N ≥ n` does. -/
theorem concrete_classII [Finite Out] {T : ℕ → ℕ} (hT : Computable T)
    {P : (concreteModelN Δ c k).Problem Out} (check : Net Δ c k → List Out → Bool)
    (hcheck : Computable₂ check) (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab) :
    [(∃ A : Alg ℕ Out, (concreteModelN Δ c k).Solves P A T),
      (∃ A : ℕ → Alg ℕ Out,
        (concreteModelN Δ c k).SolvesWith (concreteModelN Δ c k).UpperBound P A T),
      (∃ A : ℕ → Alg ℕ Out, Model.IsComputableFam A ∧
        (concreteModelN Δ c k).SolvesWith (concreteModelN Δ c k).UpperBound P A T)].TFAE :=
  (concreteModelN Δ c k).classII_iff (computable_size Δ c k) (computable_view Δ c k) hT
    (netsN Δ c k) (primrec_netsN Δ c k).to_comp (fun _ _ => mem_netsN) check hcheck hP

/-- **Corollary of Theorems 5.3 and 5.4 for the concrete model, with genuine (tree) views.** For
a computable locality `T`, a finite output alphabet and a computable validity check: some
(possibly uncomputable) LOCAL algorithm without any information on `n` solves `P` with locality
`T` iff some *computable* LOCAL algorithm (on coded views) that is given an upper bound `N ≥ n`
does. -/
theorem concrete_uncomputable_iff_computable [Finite Out] {T : ℕ → ℕ} (hT : Computable T)
    {P : (concreteModelN Δ c k).Problem Out} (check : Net Δ c k → List Out → Bool)
    (hcheck : Computable₂ check) (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab) :
    (∃ A : Alg VTree Out, (concreteModel Δ c k).Solves P A T) ↔
      ∃ A : ℕ → Alg ℕ Out, Model.IsComputableFam A ∧
        (concreteModelN Δ c k).SolvesWith (concreteModelN Δ c k).UpperBound P A T :=
  (exists_solves_iff P T).trans ((concrete_classII hT check hcheck hP).out 1 3)

/-- **Table 1, class III (Theorem 5.3), for the concrete LOCAL model.** With the promise
`n ≤ N ≤ f(n)` for a computable `f : ℕ → ℕ∞`, uncomputable and computable LOCAL solve the same
problems with a computable locality `T` (the validity check being computable). -/
theorem concrete_classIII {T : ℕ → ℕ} (hT : Computable T) {f : ℕ → ℕ∞}
    (hf : Computable fun n => Model.enatToOption (f n))
    {P : (concreteModelN Δ c k).Problem Out} (check : Net Δ c k → List Out → Bool)
    (hcheck : Computable₂ check) (hP : ∀ G lab, check G (List.ofFn lab) = true ↔ P G lab) :
    (∃ A : ℕ → Alg ℕ Out,
        (concreteModelN Δ c k).SolvesWith ((concreteModelN Δ c k).Sandwich f) P A T) ↔
      ∃ A : ℕ → Alg ℕ Out, Model.IsComputableFam A ∧
        (concreteModelN Δ c k).SolvesWith ((concreteModelN Δ c k).Sandwich f) P A T :=
  (concreteModelN Δ c k).classIII_iff (computable_size Δ c k) (computable_view Δ c k) hT hf
    (netsN Δ c k) (primrec_netsN Δ c k).to_comp (fun _ _ => mem_netsN) check hcheck hP

/-- **Lemma 5.2 for the concrete LOCAL model.** For a computable non-decreasing locality `T`,
there is a computable test deciding, for every view that occurs in some network, whether it is
`T`-critical. -/
theorem concrete_critical_decidable {T : ℕ → ℕ} (hT : Computable T) (hmono : Monotone T) :
    ∃ p : ℕ → ℕ → Bool, Computable₂ p ∧
      ∀ (G : Net Δ c k) (v : Fin ((concreteModelN Δ c k).size G)) (t : ℕ),
        p ((concreteModelN Δ c k).view G v t) t = true ↔
          (concreteModelN Δ c k).Critical T ((concreteModelN Δ c k).view G v t) t :=
  (concreteModelN Δ c k).critical_decidable (computable_size Δ c k) (computable_view Δ c k) hT
    hmono (netsN Δ c k) (primrec_netsN Δ c k).to_comp (fun _ _ => mem_netsN)

/-- **Lemma 5.2 for the concrete LOCAL model, with tree views**: a computable test, applied to
the code of a view, decides whether the view is `T`-critical. -/
theorem concrete_critical_decidable' {T : ℕ → ℕ} (hT : Computable T) (hmono : Monotone T) :
    ∃ p : ℕ → ℕ → Bool, Computable₂ p ∧
      ∀ (G : Net Δ c k) (v : Fin G.1.n) (t : ℕ),
        p (fview G.1 v t).code t = true ↔ (concreteModel Δ c k).Critical T (fview G.1 v t) t := by
  obtain ⟨p, hp, hspec⟩ := concrete_critical_decidable (Δ := Δ) (c := c) (k := k) hT hmono
  exact ⟨p, hp, fun G v t => (hspec G v t).trans (critical_code_iff T _ t)⟩

end Corollaries

end LocalComputable
