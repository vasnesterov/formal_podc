import Papers.PODC2022.HybridApproxAgreement.OBC
import Podc.PartialSync.Sim
import Podc.PartialSync.Map

/-!
# `Π_rBC` and `Π_oBC` only compare values for equality

Both protocols are generic in the value type `V` and only test values for equality. Hence they
commute with every injective map `f : V → W` of values (`RBC.stepI_map`, `OBC.step_map`). With
`Run.st_map` this transfers a run computed (by `decide`) with Boolean values to the same run with
real values.
-/

open Cslib.Byzantine.PartialSync

namespace HybridApproxAgreement

set_option linter.unusedSectionVars false

variable {n : ℕ} {V W : Type} [DecidableEq V] [DecidableEq W] (f : V → W)

namespace RBC

/-- Mapping the values in a message. -/
def Msg.map : Msg n V → Msg n W
  | .propose v => .propose (f v)
  | .vote p v => .vote p (f v)
  | .cert v C => .cert (f v) C

/-- Mapping the values in a state. -/
def St.map (s : St n V) : St n W :=
  ⟨s.first.map f, s.conflict, s.fwd, s.voteDone, s.votes.map (Prod.map id f), s.out.map f⟩

variable {f} (hf : Function.Injective f)
include hf

theorem recv_map (s : St n V) (m : Msg n V) : recv (s.map f) (m.map f) = (recv s m).map f := by
  cases m with
  | propose v =>
    rcases h : s.first with _ | w
    · simp [recv, Msg.map, St.map, h]
    · by_cases hvw : v = w
      · simp [recv, Msg.map, St.map, h, hvw]
      · simp [recv, Msg.map, St.map, h, hvw, hf.ne hvw]
  | vote p v => simp [recv, Msg.map, St.map]
  | cert v C => simp [recv, Msg.map, St.map, Function.comp_def]

theorem foldl_recv_map (s : St n V) (ms : List (Msg n V)) :
    (ms.map (Msg.map f)).foldl recv (s.map f) = (ms.foldl recv s).map f := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => simp only [List.map_cons, List.foldl_cons, recv_map hf, ih]

theorem mem_votes_map (s : St n V) (p : Fin n) (v : V) :
    (p, f v) ∈ (s.map f).votes ↔ (p, v) ∈ s.votes := by
  simp only [St.map, List.mem_map, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, h, rfl, hb⟩; rwa [hf hb] at h
  · intro h; exact ⟨p, v, h, rfl, rfl⟩

theorem voters_map (s : St n V) (v : V) : voters (s.map f) (f v) = voters s v := by
  unfold voters
  congr 1
  funext p
  simp only [mem_votes_map hf]

theorem certified_map (q : ℕ) (s : St n V) : certified q (s.map f) = (certified q s).map f := by
  unfold certified
  have : (s.map f).votes.map Prod.snd = (s.votes.map Prod.snd).map f := by
    simp [St.map, Function.comp_def]
  rw [this, List.filter_map]
  congr 1
  apply List.filter_congr
  intro v _
  simp [voters_map hf]

theorem actFwd_map (Δ now : ℕ) (s : St n V) :
    actFwd Δ now (s.map f) = ((actFwd Δ now s).1.map f, (actFwd Δ now s).2.map (Msg.map f)) := by
  rcases h : s.first with _ | v
  · simp [actFwd, St.map, h]
  · by_cases hc : (!s.fwd && decide (Δ ≤ now)) = true
    · simp only [actFwd, St.map, h, Option.map_some] at hc ⊢
      simp [hc, Msg.map]
    · simp only [actFwd, St.map, h, Option.map_some] at hc ⊢
      simp [hc, h]

theorem actVote_map (Δ now : ℕ) (self : Fin n) (s : St n V) :
    actVote Δ now self (s.map f) =
      ((actVote Δ now self s).1.map f, (actVote Δ now self s).2.map (Msg.map f)) := by
  rcases h : s.first with _ | v
  · simp [actVote, St.map, h]
  · simp only [actVote, St.map, h, Option.map_some]
    split_ifs <;> simp_all [Msg.map]

theorem actOut_map (Δ q now : ℕ) (s : St n V) :
    actOut Δ q now (s.map f) =
      ((actOut Δ q now s).1.map f, (actOut Δ q now s).2.map (Msg.map f)) := by
  unfold actOut
  rw [certified_map hf]
  rcases h : certified q s with _ | ⟨v, vs⟩
  · simp [St.map]
  · simp only [List.map_cons]
    split_ifs
    · rw [voters_map hf]; simp [St.map, Msg.map]
    · simp [St.map]

theorem stepI_map (Δ q now : ℕ) (self : Fin n) (s : St n V) (ms : List (Msg n V)) :
    stepI Δ q now self (s.map f) (ms.map (Msg.map f)) =
      ((stepI Δ q now self s ms).1.map f, (stepI Δ q now self s ms).2.map (Msg.map f)) := by
  unfold stepI
  have hout : (s.map f).out.isSome = s.out.isSome := by simp [St.map]
  rw [hout]
  split_ifs
  · simp
  · simp only [foldl_recv_map hf, actFwd_map hf, actVote_map hf, actOut_map hf, List.map_append]

end RBC

namespace OBC

/-- Mapping the values in a message. -/
def Msg.map : Msg n V → Msg n W
  | .inst s m => .inst s (m.map f)
  | .report k v s => .report k (f v) s

/-- Mapping the values in a state. -/
def St.map (s : St n V) : St n W :=
  ⟨s.clock, fun x => (s.rbc x).map f, fun x => (s.O x).map f, s.nrep,
    fun x => (s.buf x).map (fun e => (e.1, f e.2.1, e.2.2)), s.phase, s.outbox.map (Msg.map f)⟩

variable {f} (hf : Function.Injective f)
include hf

omit hf in
theorem length_dedup_map {α β : Type} [DecidableEq α] [DecidableEq β] {g : α → β}
    (hg : Function.Injective g) (l : List α) : (l.map g).dedup.length = l.dedup.length := by
  cases l with
  | nil => simp
  | cons a l =>
    have : Nonempty α := ⟨a⟩
    rw [List.dedup_map_of_injective hg, List.length_map]

theorem fifoPrefix_go_map (b : List (ℕ × V × Fin n)) (k fuel : ℕ) :
    fifoPrefix.go (b.map (fun e => (e.1, f e.2.1, e.2.2))) k fuel =
      (fifoPrefix.go b k fuel).map (Prod.map f id) := by
  induction fuel generalizing k with
  | zero => rfl
  | succ fuel ih =>
    have : ((fun e : ℕ × W × Fin n => decide (e.1 = k)) ∘ fun e : ℕ × V × Fin n => (e.1, f e.2.1, e.2.2))
        = fun e => decide (e.1 = k) := rfl
    simp only [fifoPrefix.go, List.find?_map, this]
    rcases h : b.find? (fun e => decide (e.1 = k)) with _ | e
    · rw [h]; rfl
    · rw [h]; simp [ih, Prod.map]

theorem fifoPrefix_map (b : List (ℕ × V × Fin n)) :
    fifoPrefix (b.map (fun e => (e.1, f e.2.1, e.2.2))) = (fifoPrefix b).map (Prod.map f id) := by
  unfold fifoPrefix; rw [List.length_map, fifoPrefix_go_map hf]

theorem reportsOf_map (s : St n V) (p : Fin n) :
    reportsOf (s.map f) p = (reportsOf s p).map (Prod.map f id) := fifoPrefix_map hf _

theorem cardO_map (O : Fin n → Option V) : cardO (fun x => (O x).map f) = cardO O := by
  simp [cardO]

theorem isWitness_map (q : ℕ) (s : St n V) (p : Fin n) :
    isWitness q (s.map f) p = isWitness q s p := by
  unfold isWitness
  have hinj : Function.Injective (Prod.map f (id : Fin n → Fin n)) := by
    intro a b h; simp only [Prod.map, Prod.mk.injEq, id_eq] at h; exact Prod.ext (hf h.1) h.2
  rw [reportsOf_map hf, length_dedup_map hinj, List.all_map]
  have : ((fun e : W × Fin n => decide ((s.map f).O e.2 = some e.1)) ∘ Prod.map f id) =
      fun e => decide (s.O e.2 = some e.1) := by
    funext e
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, St.map]
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
    obtain ⟨a, ha, hfa⟩ := Option.map_eq_some_iff.mp h
    rw [ha, hf hfa]
  rw [this]

theorem witnesses_map (q : ℕ) (s : St n V) : witnesses q (s.map f) = witnesses q s := by
  unfold witnesses; congr 1; funext p; exact isWitness_map hf q s p

theorem instMsgs_map (ms : List (Msg n V)) (s : Fin n) :
    instMsgs (ms.map (Msg.map f)) s = (instMsgs ms s).map (RBC.Msg.map f) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    cases m with
    | inst s' m =>
      by_cases h : s' = s
      · simp [instMsgs, Msg.map, h] at ih ⊢; exact ih
      · simp [instMsgs, Msg.map, h] at ih ⊢; exact ih
    | report k v s' => simp [instMsgs, Msg.map] at ih ⊢; exact ih

omit hf in
theorem update_map {α β : Type} (g : α → β) (F : Fin n → α) (x : Fin n) (a : α) :
    (fun y => g (Function.update F x a y)) = Function.update (fun y => g (F y)) x (g a) := by
  funext y
  by_cases h : y = x
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem stepInstances_map (Δ q : ℕ) (self : Fin n) (s : St n V) (ms : List (Msg n V)) :
    stepInstances Δ q self (s.map f) (ms.map (Msg.map f)) =
      ((stepInstances Δ q self s ms).1.map f,
        (stepInstances Δ q self s ms).2.map (Msg.map f)) := by
  unfold stepInstances
  suffices H : ∀ (l : List (Fin n)) (acc : St n V × List (Msg n V)),
      l.foldl (fun (acc : St n W × List (Msg n W)) snd =>
        let st := acc.1
        let r := RBC.stepI Δ q st.clock self (st.rbc snd) (instMsgs (ms.map (Msg.map f)) snd)
        let st1 := { st with rbc := Function.update st.rbc snd r.1 }
        let msgs := r.2.map (.inst snd)
        match (st.rbc snd).out, r.1.out with
        | none, some v =>
          if st.phase = 1 then
            ({ st1 with O := Function.update st.O snd (some v), nrep := st.nrep + 1 },
              acc.2 ++ msgs ++ [.report st.nrep v snd])
          else ({ st1 with O := Function.update st.O snd (some v) }, acc.2 ++ msgs)
        | _, _ => (st1, acc.2 ++ msgs)) (acc.1.map f, acc.2.map (Msg.map f)) =
      let res := l.foldl (fun (acc : St n V × List (Msg n V)) snd =>
        let st := acc.1
        let r := RBC.stepI Δ q st.clock self (st.rbc snd) (instMsgs ms snd)
        let st1 := { st with rbc := Function.update st.rbc snd r.1 }
        let msgs := r.2.map (.inst snd)
        match (st.rbc snd).out, r.1.out with
        | none, some v =>
          if st.phase = 1 then
            ({ st1 with O := Function.update st.O snd (some v), nrep := st.nrep + 1 },
              acc.2 ++ msgs ++ [.report st.nrep v snd])
          else ({ st1 with O := Function.update st.O snd (some v) }, acc.2 ++ msgs)
        | _, _ => (st1, acc.2 ++ msgs)) acc
      (res.1.map f, res.2.map (Msg.map f)) by
    exact H _ (s, [])
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    obtain ⟨st, out⟩ := acc
    simp only
    have hst : (St.map f st).rbc x = (st.rbc x).map f := rfl
    rw [instMsgs_map hf, hst, show (St.map f st).clock = st.clock from rfl,
      RBC.stepI_map hf]
    set r := RBC.stepI Δ q st.clock self (st.rbc x) (instMsgs ms x)
    have ho1 : ((st.rbc x).map f).out = (st.rbc x).out.map f := rfl
    have ho2 : (r.1.map f).out = r.1.out.map f := rfl
    rw [ho1, ho2]
    have u1 := update_map (RBC.St.map f) st.rbc x r.1
    have u2 : ∀ b, (fun y => Option.map f (Function.update st.O x (some b) y)) =
        Function.update (fun y => Option.map f (st.O y)) x (some (f b)) :=
      fun b => update_map (Option.map f) st.O x (some b)
    rcases h1 : (st.rbc x).out with _ | a <;> rcases h2 : r.1.out with _ | b
    · simp [St.map, u1, List.map_append, Function.comp_def, Msg.map]
    · simp only [Option.map_none, Option.map_some]
      by_cases hp : st.phase = 1
      · simp [St.map, hp, u1, u2, List.map_append, Msg.map, Function.comp_def]
      · simp [St.map, hp, u1, u2, List.map_append, Function.comp_def, Msg.map]
    · simp [St.map, u1, List.map_append, Function.comp_def, Msg.map]
    · simp [St.map, u1, List.map_append, Function.comp_def, Msg.map]

theorem fileReports_map (s : St n V) (inbox : Fin n → List (Msg n V)) :
    fileReports (s.map f) (fun q => (inbox q).map (Msg.map f)) = (fileReports s inbox).map f := by
  simp only [fileReports, St.map, St.mk.injEq, true_and]
  refine ⟨?_, trivial⟩
  funext p
  simp only [List.map_append, List.map_reverse, List.filterMap_map]
  congr 2
  rw [List.map_filterMap]
  congr 1
  funext m
  cases m <;> simp [Msg.map]

theorem checkExit_map (Δ q : ℕ) (s : St n V) : checkExit Δ q (s.map f) = (checkExit Δ q s).map f := by
  unfold checkExit
  have h1 : (s.map f).phase = s.phase := rfl
  have h2 : (s.map f).clock = s.clock := rfl
  have h3 : cardO (s.map f).O = cardO s.O := cardO_map hf s.O
  rw [h1, h2, h3, witnesses_map hf]
  split_ifs <;> rfl

theorem step_map (Δ q : ℕ) (p : Fin n) (s : St n V) (ib : Fin n → List (Msg n V)) :
    (alg Δ q).step p (s.map f) (fun x => (ib x).map (Msg.map f)) = ((alg Δ q).step p s ib).map f := by
  simp only [alg]
  have h1 : (s.map f).phase = s.phase := rfl
  rw [h1]
  split_ifs
  · rfl
  · have hms : (List.finRange n).flatMap (fun x => (ib x).map (Msg.map f)) =
        ((List.finRange n).flatMap ib).map (Msg.map f) := by rw [List.map_flatMap]
    rw [hms, stepInstances_map hf, fileReports_map hf, checkExit_map hf]
    rfl

theorem init_map (Δ q : ℕ) (p : Fin n) (v : V) :
    (alg Δ q).init p (f v) = ((alg Δ q).init p v).map f := by
  simp only [alg, St.map, St.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

end OBC

end HybridApproxAgreement
