import Papers.PODC2022.RecoverableHarder.Fig2

/-!
# Figure 2: the invariant (Lemmas 9–13)

The correctness proof of Figure 2 (Lemmas 9–13 of the paper) is turned into an invariant of the
*abstract view* of a configuration — the program counters `pcf`, the registers `R X` and the
value `O` of the object — together with a ghost component (`Ghost`):

* `L` — the distinct processes that applied their operation to `O` in the current *epoch*, so
  that `O = apply u o L` (Lemmas 10 and 11: no process updates `O` twice per epoch);
* `ep2` — whether `O` returned to `q₀` after a first update by team `A` (the second phase in the
  proof of Lemma 11; then `|B| = 1`, the process of `B` has updated and never updates again, and
  only processes of `A` update afterwards);
* `dec` — the value decided so far.

The team that updated `O` first is `Ghost.fst` (`none` before the first update). Agreement and
validity (Lemmas 12, 13 and 9) are the fields `done` and `dec` of `InvV`.
-/

namespace Podc.RecoverableHarder

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable Cslib.SharedMemory.Recoverable.Ovens

/-- The ghost state of the invariant. -/
structure Ghost (k : ℕ) where
  /-- The processes that applied their operation to `O` in the current epoch, in order. -/
  L : List (Fin k)
  /-- Second epoch: `O` returned to `q₀` after a first update by team `A`. -/
  ep2 : Bool
  /-- The decided value. -/
  dec : Option Bool

section Inv

variable {S : ObjSpec} {k : ℕ} (u : S.State) (team : Fin k → Bool) (o : Fin k → S.Op)

/-- The team that updated `O` first (`none`: no update yet). -/
def Ghost.fst (g : Ghost k) : Option Bool := if g.ep2 then some false else g.L.head?.map team

/-- The invariant on abstract views (inputs `x`, program counters `pcf`, registers `R`, object
value `O`). -/
structure InvV (x : Fin k → Bool) (pcf : Fin k → PC) (R : Bool → Option Bool) (O : S.State)
    (g : Ghost k) : Prop where
  regv : ∀ X w, R X = some w → ∀ q, team q = X → x q = w
  wrote : ∀ q, pcf q ≠ .wr → R (team q) ≠ none
  obj : O = apply S u o g.L
  nodup : g.L.Nodup
  ep1 : g.ep2 = false → g.L ≠ [] → apply S u o g.L ≠ u
  ep2 : g.ep2 = true → (∃! q, team q = true) ∧ (∀ q ∈ g.L, team q = false) ∧
    (∀ q, team q = true → pcf q ≠ .upd) ∧ QX u team o false u
  notin : ∀ q, (pcf q = .upd ∨ pcf q = .chk) → q ∉ g.L
  chk : ∀ q, pcf q = .chk → team q = true ∧ ∃! q, team q = true
  rd2 : ∀ q, pcf q = .rd2 → g.fst team ≠ none
  rdR : ∀ q Y, pcf q = .rdR Y → g.fst team = some Y
  done : ∀ q w, pcf q = .done w → g.dec = some w
  dec : ∀ d, g.dec = some d → (∀ Y, g.fst team = some Y → ∀ q, team q = Y → x q = d) ∧
    (g.fst team = none → (∃! q, team q = true) ∧ R false ≠ none ∧
      (∀ q, team q = false → x q = d) ∧ ∀ q, team q = true → pcf q ≠ .upd)
  fstR : ∀ Y, g.fst team = some Y → R Y ≠ none

variable {u team o}

/-! ## Facts about the recording conditions -/

section Facts

variable (hrec : RecOn S Finset.univ u team o) (hB : ¬ QX u team o true u)
include hrec

lemma qx_disj {q : S.State} (hA : QX u team o false q) (hB' : QX u team o true q) : False := by
  obtain ⟨p, σ, hp, tp, rfl⟩ := hA
  obtain ⟨p', σ', hp', tp', he⟩ := hB'
  exact hrec.2.2.1 p σ p' σ' (by simp) (by simp) hp hp' tp tp' he.symm

lemma qx_cycle {X : Bool} (h : QX u team o X u) : ∃! q, team q = !X := by
  obtain ⟨p, σ, hp, rfl, he⟩ := h
  obtain ⟨q, ⟨-, hq⟩, huniq⟩ := hrec.2.2.2 p σ (by simp) hp he
  exact ⟨q, hq, fun q' hq' => huniq q' ⟨by simp, hq'⟩⟩

lemma exists_team (X : Bool) : ∃ q, team q = X := by
  obtain ⟨⟨a, -, ha⟩, ⟨b, -, hb⟩, -⟩ := hrec
  cases X
  · exact ⟨a, ha⟩
  · exact ⟨b, hb⟩

omit hrec in
lemma qx_of_list {L : List (Fin k)} (hL : L.Nodup) (hne : L ≠ []) :
    QX u team o (team (L.head hne)) (apply S u o L) := by
  obtain ⟨p, σ, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨p, σ, hL, rfl, rfl⟩

include hB in
/-- Lemma 7 for `X = B`: a cycle (from `q₀` back to `q₀`) contains every process of `B`. -/
lemma mem_of_cycle {L : List (Fin k)} (hL : L.Nodup) (hne : L ≠ [])
    (hcyc : apply S u o L = u) {j : Fin k} (hj : team j = true) : j ∈ L := by
  obtain ⟨p, σ, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact lemma7 hrec (x := true) (fun p' σ' _ hn ht he => hB ⟨p', σ', hn, ht, he⟩) p σ (by simp)
    hL hcyc j (by simp) hj

end Facts

lemma side_resp {rd : S.Op} (hinj : Function.Injective fun q => (S.δ q rd).2) (q : S.State) :
    side rd u team o (S.δ q rd).2 = false ↔ QX u team o false q := by
  classical
  unfold side
  have : (∃ q', (S.δ q' rd).2 = (S.δ q rd).2 ∧ QX u team o false q') ↔ QX u team o false q := by
    constructor
    · rintro ⟨q', hq', hA⟩; rwa [← hinj hq']
    · intro h; exact ⟨q, rfl, h⟩
  split_ifs with h
  · simpa using this.1 h
  · simpa using fun h' => h (this.2 h')

lemma side_list {rd : S.Op} (hinj : Function.Injective fun q => (S.δ q rd).2)
    (hrec : RecOn S Finset.univ u team o) {L : List (Fin k)} (hL : L.Nodup) (hne : L ≠ []) :
    side rd u team o (S.δ (apply S u o L) rd).2 = team (L.head hne) := by
  have hq := qx_of_list (u := u) (team := team) (o := o) hL hne
  cases ht : team (L.head hne)
  · rw [side_resp hinj]; rw [ht] at hq; exact hq
  · rw [ht] at hq
    cases hs : side rd u team o (S.δ (apply S u o L) rd).2
    · exact absurd hq (fun hq' => qx_disj hrec ((side_resp hinj _).1 hs) hq')
    · rfl

/-! ## Preservation, one program counter at a time -/

section Steps

variable {x : Fin k → Bool} {pcf : Fin k → PC} {R : Bool → Option Bool} {O : S.State}
  {g : Ghost k} {p : Fin k}

/-- Crash: back to `wr`. -/
lemma InvV.crash (hI : InvV u team o x pcf R O g) :
    InvV u team o x (Function.update pcf p .wr) R O g := by
  have hupd : ∀ q, Function.update pcf p .wr q = .wr ∨ Function.update pcf p .wr q = pcf q := by
    intro q; by_cases hq : q = p
    · subst hq; simp
    · simp [hq]
  refine ⟨hI.regv, fun q hq => ?_, hI.obj, hI.nodup, hI.ep1, fun h => ?_, fun q hq => ?_,
    fun q hq => ?_, fun q hq => ?_, fun q Y hq => ?_, fun q w hq => ?_, fun d hd => ?_, hI.fstR⟩
  · rcases hupd q with h | h
    · exact absurd h hq
    · rw [h] at hq; exact hI.wrote q hq
  · obtain ⟨h1, h2, h3, h4⟩ := hI.ep2 h
    refine ⟨h1, h2, fun q hq => ?_, h4⟩
    rcases hupd q with h | h <;> rw [h]
    · simp
    · exact h3 q hq
  · rcases hupd q with h | h <;> rw [h] at hq
    · simp at hq
    · exact hI.notin q hq
  · rcases hupd q with h | h <;> rw [h] at hq
    · simp at hq
    · exact hI.chk q hq
  · rcases hupd q with h | h <;> rw [h] at hq
    · simp at hq
    · exact hI.rd2 q hq
  · rcases hupd q with h | h <;> rw [h] at hq
    · simp at hq
    · exact hI.rdR q Y hq
  · rcases hupd q with h | h <;> rw [h] at hq
    · simp at hq
    · exact hI.done q w hq
  · refine ⟨(hI.dec d hd).1, fun h => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := (hI.dec d hd).2 h
    refine ⟨h1, h2, h3, fun q hq => ?_⟩
    rcases hupd q with h | h <;> rw [h]
    · simp
    · exact h4 q hq

/-- `wr`: write the input to the team's register. -/
lemma InvV.wr (hx : ∀ p q, team p = team q → x p = x q) (hI : InvV u team o x pcf R O g)
    (hp : pcf p = .wr) :
    InvV u team o x (Function.update pcf p .rd1) (Function.update R (team p) (some (x p))) O g := by
  have hR : ∀ Y, R Y ≠ none → Function.update R (team p) (some (x p)) Y ≠ none := by
    intro Y hY; by_cases h : Y = team p
    · subst h; simp
    · simp [h, hY]
  have hupd : ∀ q, q ≠ p → Function.update pcf p .rd1 q = pcf q := fun q hq => by simp [hq]
  refine ⟨fun X w hw q hq => ?_, fun q hq => ?_, hI.obj, hI.nodup, hI.ep1, fun h => ?_,
    fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q Y hq => ?_, fun q w hq => ?_,
    fun d hd => ?_, fun Y hY => hR Y (hI.fstR Y hY)⟩
  · by_cases hX : X = team p
    · subst hX; simp at hw; subst hw; exact hx q p hq
    · simp [hX] at hw; exact hI.regv X w hw q hq
  · by_cases hqp : q = p
    · subst hqp; simp
    · rw [hupd q hqp] at hq; exact hR _ (hI.wrote q hq)
  · obtain ⟨h1, h2, h3, h4⟩ := hI.ep2 h
    refine ⟨h1, h2, fun q hq => ?_, h4⟩
    by_cases hqp : q = p
    · subst hqp; simp
    · rw [hupd q hqp]; exact h3 q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.notin q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.chk q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rd2 q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rdR q Y hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.done q w hq
  · refine ⟨(hI.dec d hd).1, fun h => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := (hI.dec d hd).2 h
    refine ⟨h1, hR _ h2, h3, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp
    · rw [hupd q hqp]; exact h4 q hq

/-- Facts from the invariant: the current epoch is empty iff `O = q₀`. -/
lemma InvV.L_nil_of_eq (hrec : RecOn S Finset.univ u team o) (hB : ¬ QX u team o true u)
    (hI : InvV u team o x pcf R O g) (hO : O = u) : g.L = [] := by
  by_contra hne
  cases he : g.ep2
  · exact hI.ep1 he hne (hI.obj ▸ hO)
  · obtain ⟨-, h2, -, -⟩ := hI.ep2 he
    obtain ⟨j, hj⟩ := exists_team hrec true
    have := h2 j (mem_of_cycle hrec hB hI.nodup hne (hI.obj ▸ hO) hj)
    rw [hj] at this; cases this

lemma InvV.fst_ne_true (hI : InvV u team o x pcf R O g) (hp : pcf p = .chk) :
    g.fst team ≠ some true := by
  intro h
  obtain ⟨tp, q, hq, huniq⟩ := hI.chk p hp
  unfold Ghost.fst at h
  split_ifs at h with he
  · simp at h
  · rcases hL : g.L with _ | ⟨h₀, t⟩
    · simp [hL] at h
    · simp [hL] at h
      have : h₀ = p := (huniq h₀ h).trans (huniq p tp).symm
      subst this
      exact hI.notin h₀ (Or.inr hp) (by simp [hL])

/-- Changing the program counter of `p` only (ghost, registers and object unchanged). -/
lemma InvV.setpc (hI : InvV u team o x pcf R O g) (c : PC)
    (hwr : c ≠ .wr → R (team p) ≠ none) (hep2 : g.ep2 = true → team p = true → c ≠ .upd)
    (hnotin : c = .upd ∨ c = .chk → p ∉ g.L) (hchk : c = .chk → team p = true ∧ ∃! q, team q = true)
    (hrd2 : c = .rd2 → g.fst team ≠ none) (hrdR : ∀ Y, c = .rdR Y → g.fst team = some Y)
    (hdone : ∀ w, c = .done w → g.dec = some w)
    (hdec : ∀ d, g.dec = some d → g.fst team = none → team p = true → c ≠ .upd) :
    InvV u team o x (Function.update pcf p c) R O g := by
  have hupd : ∀ q, q ≠ p → Function.update pcf p c q = pcf q := fun q hq => by simp [hq]
  refine ⟨hI.regv, fun q hq => ?_, hI.obj, hI.nodup, hI.ep1, fun h => ?_,
    fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q Y hq => ?_, fun q w hq => ?_,
    fun d hd => ⟨(hI.dec d hd).1, fun h => ?_⟩, hI.fstR⟩
  · by_cases hqp : q = p
    · subst hqp; simp at hq; exact hwr hq
    · rw [hupd q hqp] at hq; exact hI.wrote q hq
  · obtain ⟨h1, h2, h3, h4⟩ := hI.ep2 h
    refine ⟨h1, h2, fun q hq => ?_, h4⟩
    by_cases hqp : q = p
    · subst hqp; simp; exact hep2 h hq
    · rw [hupd q hqp]; exact h3 q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; exact hnotin hq
    · rw [hupd q hqp] at hq; exact hI.notin q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; exact hchk hq
    · rw [hupd q hqp] at hq; exact hI.chk q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; exact hrd2 hq
    · rw [hupd q hqp] at hq; exact hI.rd2 q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; exact hrdR Y hq
    · rw [hupd q hqp] at hq; exact hI.rdR q Y hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; exact hdone w hq
    · rw [hupd q hqp] at hq; exact hI.done q w hq
  · obtain ⟨h1, h2, h3, h4⟩ := (hI.dec d hd).2 h
    refine ⟨h1, h2, h3, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp; exact hdec d hd h hq
    · rw [hupd q hqp]; exact h4 q hq

open Classical in
/-- `rd1` (lines 5–7 and 17–19): read `O`. -/
lemma InvV.rd1 {rd : S.Op} (hinj : Function.Injective fun q => (S.δ q rd).2)
    (hrec : RecOn S Finset.univ u team o) (hB : ¬ QX u team o true u)
    (hI : InvV u team o x pcf R O g) (hp : pcf p = .rd1) :
    InvV u team o x (Function.update pcf p
      (if (S.δ O rd).2 = (S.δ u rd).2 then
        (if team p = true ∧ (∃! q, team q = true) then .chk else .upd)
      else .rdR (side rd u team o (S.δ O rd).2))) R O g := by
  have hwr : R (team p) ≠ none := hI.wrote p (by rw [hp]; simp)
  by_cases hO : O = u
  · have hL := hI.L_nil_of_eq hrec hB hO
    rw [ite_eq_left (by rw [hO])]
    split_ifs with hc
    · refine hI.setpc _ (fun _ => hwr) (fun _ _ => by simp) (fun _ => by simp [hL])
        (fun _ => hc) (by simp) (by simp) (by simp) (fun _ _ _ _ => by simp)
    · refine hI.setpc _ (fun _ => hwr) (fun he ht => ?_) (fun _ => by simp [hL])
        (by simp) (by simp) (by simp) (by simp) (fun d hd hf ht => ?_)
      · exact absurd ⟨ht, (hI.ep2 he).1⟩ hc
      · exact absurd ⟨ht, ((hI.dec d hd).2 hf).1⟩ hc
  · rw [ite_eq_right (fun h => hO (hinj h))]
    have hne : g.L ≠ [] := by
      intro hL; apply hO; rw [hI.obj, hL]; rfl
    refine hI.setpc _ (fun _ => hwr) (fun _ _ => by simp) (by simp) (by simp) (by simp)
      (fun Y hY => ?_) (by simp) (fun _ _ _ _ => by simp)
    cases hY
    rw [hI.obj, side_list hinj hrec hI.nodup hne]
    unfold Ghost.fst
    split_ifs with he
    · obtain ⟨-, h2, -, -⟩ := hI.ep2 he
      rw [h2 _ (List.head_mem hne)]
    · obtain ⟨h₀, t, hL⟩ := List.exists_cons_of_ne_nil hne
      simp [hL]

/-- `rd2` (lines 9 and 23): read `O` after the update. -/
lemma InvV.step_rd2 {rd : S.Op} (hinj : Function.Injective fun q => (S.δ q rd).2)
    (hrec : RecOn S Finset.univ u team o) (hI : InvV u team o x pcf R O g) (hp : pcf p = .rd2) :
    InvV u team o x (Function.update pcf p (.rdR (side rd u team o (S.δ O rd).2))) R O g := by
  have hwr : R (team p) ≠ none := hI.wrote p (by rw [hp]; simp)
  have hf := hI.rd2 p hp
  refine hI.setpc _ (fun _ => hwr) (fun _ _ => by simp) (by simp) (by simp) (by simp)
    (fun Y hY => ?_) (by simp) (fun _ _ _ _ => by simp)
  cases hY
  unfold Ghost.fst at hf ⊢
  split_ifs with he
  · obtain ⟨-, h2, -, h4⟩ := hI.ep2 he
    by_cases hL : g.L = []
    · rw [hI.obj, hL]
      exact congrArg some ((side_resp hinj u).2 h4).symm
    · rw [hI.obj, side_list hinj hrec hI.nodup hL, h2 _ (List.head_mem hL)]
  · rw [ite_eq_right he] at hf
    have hL : g.L ≠ [] := by intro hL; simp [hL] at hf
    rw [hI.obj, side_list hinj hrec hI.nodup hL]
    obtain ⟨h₀, t, hL'⟩ := List.exists_cons_of_ne_nil hL
    simp [hL']

/-- `chk` (lines 19–20), `R_A = ⊥`: go on to update `O`. -/
lemma InvV.chk_none (hI : InvV u team o x pcf R O g) (hp : pcf p = .chk) (hR : R false = none) :
    InvV u team o x (Function.update pcf p .upd) R O g := by
  have hwr : R (team p) ≠ none := hI.wrote p (by rw [hp]; simp)
  refine hI.setpc _ (fun _ => hwr) (fun he _ => ?_) (fun _ => hI.notin p (Or.inr hp)) (by simp)
    (by simp) (by simp) (by simp) (fun d hd hf _ => ?_)
  · exact absurd hR (hI.fstR false (by simp [Ghost.fst, he]))
  · exact absurd hR ((hI.dec d hd).2 hf).2.1

/-- Changing the program counter of `p` to an output `done w` and recording the decision. -/
lemma InvV.setDone (hI : InvV u team o x pcf R O g) (w : Bool) (hwr : R (team p) ≠ none)
    (hw : ∀ d, g.dec = some d → d = w)
    (hfst : ∀ Y, g.fst team = some Y → ∀ q, team q = Y → x q = w)
    (hnone : g.fst team = none → (∃! q, team q = true) ∧ R false ≠ none ∧
      (∀ q, team q = false → x q = w) ∧ ∀ q, team q = true → q ≠ p → pcf q ≠ .upd) :
    InvV u team o x (Function.update pcf p (.done w)) R O ⟨g.L, g.ep2, some w⟩ := by
  have hupd : ∀ q, q ≠ p → Function.update pcf p (.done w) q = pcf q := fun q hq => by simp [hq]
  refine ⟨hI.regv, fun q hq => ?_, hI.obj, hI.nodup, hI.ep1, fun h => ?_,
    fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q Y hq => ?_, fun q w' hq => ?_,
    fun d hd => ?_, hI.fstR⟩
  · by_cases hqp : q = p
    · subst hqp; exact hwr
    · rw [hupd q hqp] at hq; exact hI.wrote q hq
  · obtain ⟨h1, h2, h3, h4⟩ := hI.ep2 h
    refine ⟨h1, h2, fun q hq => ?_, h4⟩
    by_cases hqp : q = p
    · subst hqp; simp
    · rw [hupd q hqp]; exact h3 q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.notin q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.chk q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rd2 q hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq; exact hI.rdR q Y hq
  · by_cases hqp : q = p
    · subst hqp; simp at hq; simp [hq]
    · rw [hupd q hqp] at hq; simp [hw w' (hI.done q w' hq)]
  · simp only [Option.some.injEq] at hd; subst hd
    refine ⟨hfst, fun hf => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hnone hf
    refine ⟨h1, h2, h3, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp
    · rw [hupd q hqp]; exact h4 q hq hqp

/-- `chk` (lines 19–20), `R_A = w ≠ ⊥`: yield to team `A`, output `w`. -/
lemma InvV.chk_some (hrec : RecOn S Finset.univ u team o) (hI : InvV u team o x pcf R O g)
    (hp : pcf p = .chk) {w : Bool} (hR : R false = some w) :
    InvV u team o x (Function.update pcf p (.done w)) R O ⟨g.L, g.ep2, some w⟩ ∧
      ∀ d, g.dec = some d → d = w := by
  have hwr : R (team p) ≠ none := hI.wrote p (by rw [hp]; simp)
  obtain ⟨tp, hsingle⟩ := hI.chk p hp
  have hnt := hI.fst_ne_true hp
  obtain ⟨a, ha⟩ := exists_team hrec false
  have hxa : x a = w := hI.regv false w hR a ha
  have hw : ∀ d, g.dec = some d → d = w := by
    intro d hd
    rcases hf : g.fst team with _ | Y
    · exact (((hI.dec d hd).2 hf).2.2.1 a ha).symm.trans hxa
    · cases Y
      · exact ((hI.dec d hd).1 false hf a ha).symm.trans hxa
      · exact absurd hf hnt
  refine ⟨hI.setDone w hwr hw (fun Y hY q hq => ?_) (fun _ => ⟨hsingle, by simp [hR],
    fun q hq => hI.regv false w hR q hq, fun q hq hqp => ?_⟩), hw⟩
  · cases Y
    · exact hI.regv false w hR q hq
    · exact absurd hY hnt
  · obtain ⟨q₀, -, huniq⟩ := hsingle
    exact absurd ((huniq q hq).trans (huniq p tp).symm) hqp

/-- `rdR Y` (lines 11–12, 26–27): read `R_Y` and output its value. -/
lemma InvV.step_rdR (hrec : RecOn S Finset.univ u team o) (hI : InvV u team o x pcf R O g) {Y : Bool}
    (hp : pcf p = .rdR Y) :
    ∃ w, R Y = some w ∧
      InvV u team o x (Function.update pcf p (.done w)) R O ⟨g.L, g.ep2, some w⟩ ∧
      ∀ d, g.dec = some d → d = w := by
  have hf := hI.rdR p Y hp
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (hI.fstR Y hf)
  have hwr : R (team p) ≠ none := hI.wrote p (by rw [hp]; simp)
  obtain ⟨a, ha⟩ := exists_team hrec Y
  have hxa : x a = w := hI.regv Y w hw a ha
  have hdec : ∀ d, g.dec = some d → d = w :=
    fun d hd => ((hI.dec d hd).1 Y hf a ha).symm.trans hxa
  refine ⟨w, hw, hI.setDone w hwr hdec (fun Y' hY' q hq => ?_) (fun h => by rw [hf] at h; cases h),
    hdec⟩
  rw [hf] at hY'; cases hY'
  exact hI.regv Y w hw q hq

/-- `upd` (lines 8 and 22): apply the operation of `p` to `O` (Lemmas 10, 11 and 7). -/
lemma InvV.upd (hrec : RecOn S Finset.univ u team o) (hB : ¬ QX u team o true u)
    (hI : InvV u team o x pcf R O g) (hp : pcf p = .upd) :
    ∃ g' : Ghost k, InvV u team o x (Function.update pcf p .rd2) R (S.δ O (o p)).1 g' ∧
      g'.dec = g.dec := by
  have hpL : p ∉ g.L := hI.notin p (Or.inl hp)
  have hwr : R (team p) ≠ none := hI.wrote p (by rw [hp]; simp)
  have hnd : (g.L ++ [p]).Nodup := by
    rw [List.nodup_append]
    exact ⟨hI.nodup, by simp, fun a ha b hb => by simp at hb; subst hb; rintro rfl; exact hpL ha⟩
  have hO' : (S.δ O (o p)).1 = apply S u o (g.L ++ [p]) := by
    rw [apply_append, ← hI.obj]; rfl
  have hne' : g.L ++ [p] ≠ [] := by simp
  have hupd : ∀ q, q ≠ p → Function.update pcf p .rd2 q = pcf q := fun q hq => by simp [hq]
  have hnotin' : ∀ q, (Function.update pcf p .rd2 q = .upd ∨ Function.update pcf p .rd2 q = .chk) →
      q ∉ g.L ++ [p] := by
    intro q hq
    by_cases hqp : q = p
    · subst hqp; simp at hq
    · rw [hupd q hqp] at hq
      simp [hI.notin q hq, hqp]
  -- the head of the new epoch list
  have hhead : (g.L ++ [p]).head hne' = if h : g.L = [] then p else g.L.head h := by
    split_ifs with h
    · simp [h]
    · obtain ⟨h₀, t, hL⟩ := List.exists_cons_of_ne_nil h; simp [hL]
  cases he : g.ep2
  · -- first epoch
    have hfst : g.fst team = g.L.head?.map team := by simp [Ghost.fst, he]
    by_cases hcyc : apply S u o (g.L ++ [p]) = u
    · -- `O` returns to `q₀`: start the second epoch
      have hQ := qx_of_list (u := u) (team := team) (o := o) hnd hne'
      rw [hcyc] at hQ
      have hh : team ((g.L ++ [p]).head hne') = false := by
        cases h : team ((g.L ++ [p]).head hne')
        · rfl
        · rw [h] at hQ; exact absurd hQ hB
      rw [hh] at hQ
      have hsingle := qx_cycle hrec hQ
      have hin : ∀ j, team j = true → j ∈ g.L ++ [p] :=
        fun j hj => mem_of_cycle hrec hB hnd hne' hcyc hj
      -- the old first team was `A` (or nobody)
      have hold : g.fst team = none ∨ g.fst team = some false := by
        rw [hfst]
        by_cases hL : g.L = []
        · simp [hL]
        · right
          rw [hhead, dite_eq_right hL] at hh
          simp [List.head?_eq_some_head hL, hh]
      have hRA : R false ≠ none := by
        rcases hold with h | h
        · have hL : g.L = [] := by rw [hfst] at h; simpa using h
          rw [hhead, dite_eq_left hL] at hh
          rw [← hh]; exact hwr
        · exact hI.fstR false h
      refine ⟨⟨[], true, g.dec⟩, ⟨hI.regv, fun q hq => ?_, ?_, by simp, by simp,
        fun _ => ⟨hsingle, by simp, fun q hq => ?_, hQ⟩, fun q _ => by simp, fun q hq => ?_,
        fun q _ => by simp [Ghost.fst], fun q Y hq => ?_, fun q w hq => ?_, fun d hd => ?_,
        fun Y hY => ?_⟩, rfl⟩
      · by_cases hqp : q = p
        · subst hqp; exact hwr
        · rw [hupd q hqp] at hq; exact hI.wrote q hq
      · rw [hO', hcyc]; rfl
      · by_cases hqp : q = p
        · subst hqp; simp
        · rw [hupd q hqp]
          have := hin q hq
          simp [hqp] at this
          exact fun h => hI.notin q (Or.inl h) this
      · by_cases hqp : q = p
        · subst hqp; simp at hq
        · rw [hupd q hqp] at hq; exact hI.chk q hq
      · by_cases hqp : q = p
        · subst hqp; simp at hq
        · rw [hupd q hqp] at hq
          have := hI.rdR q Y hq
          rcases hold with h | h
          · rw [h] at this; cases this
          · rw [h] at this; cases this; simp [Ghost.fst]
      · by_cases hqp : q = p
        · subst hqp; simp at hq
        · rw [hupd q hqp] at hq; exact hI.done q w hq
      · refine ⟨fun Y hY q hq => ?_, fun h => by simp [Ghost.fst] at h⟩
        simp [Ghost.fst] at hY; subst hY
        rcases hold with h | h
        · exact ((hI.dec d hd).2 h).2.2.1 q hq
        · exact (hI.dec d hd).1 false h q hq
      · simp [Ghost.fst] at hY; subst hY; exact hRA
    · -- stay in the first epoch
      have hfst' : (Ghost.mk (g.L ++ [p]) false g.dec).fst team =
          some (team ((g.L ++ [p]).head hne')) := by
        simp only [Ghost.fst, Bool.false_eq_true, ite_false]
        obtain ⟨h₀, t, hL⟩ := List.exists_cons_of_ne_nil hne'
        simp [hL]
      -- the new first team is the old one, if any
      have hsame : ∀ Y, g.fst team = some Y → team ((g.L ++ [p]).head hne') = Y := by
        intro Y hY
        rw [hfst] at hY
        by_cases hL : g.L = []
        · simp [hL] at hY
        · rw [hhead, dite_eq_right hL]; simpa [List.head?_eq_some_head hL] using hY
      refine ⟨⟨g.L ++ [p], false, g.dec⟩, ⟨hI.regv, fun q hq => ?_, hO', hnd,
        fun _ _ => hcyc, fun h => by simp at h, hnotin', fun q hq => ?_,
        fun q _ => by rw [hfst']; simp, fun q Y hq => ?_, fun q w hq => ?_, fun d hd => ?_,
        fun Y hY => ?_⟩, rfl⟩
      · by_cases hqp : q = p
        · subst hqp; exact hwr
        · rw [hupd q hqp] at hq; exact hI.wrote q hq
      · by_cases hqp : q = p
        · subst hqp; simp at hq
        · rw [hupd q hqp] at hq; exact hI.chk q hq
      · by_cases hqp : q = p
        · subst hqp; simp at hq
        · rw [hupd q hqp] at hq
          rw [hfst', hsame Y (hI.rdR q Y hq)]
      · by_cases hqp : q = p
        · subst hqp; simp at hq
        · rw [hupd q hqp] at hq; exact hI.done q w hq
      · refine ⟨fun Y hY q hq => ?_, fun h => by rw [hfst'] at h; cases h⟩
        rw [hfst'] at hY; cases hY
        rcases hf : g.fst team with _ | Y'
        · obtain ⟨-, -, h3, h4⟩ := (hI.dec d hd).2 hf
          have hL : g.L = [] := by rw [hfst] at hf; simpa using hf
          rw [hhead, dite_eq_left hL] at hq
          have tp : team p = false := by
            cases h : team p
            · rfl
            · exact absurd hp (h4 p h)
          exact h3 q (hq.trans tp)
        · rw [hsame Y' hf] at hq
          exact (hI.dec d hd).1 Y' hf q hq
      · rw [hfst'] at hY; cases hY
        rcases hf : g.fst team with _ | Y'
        · have hL : g.L = [] := by rw [hfst] at hf; simpa using hf
          rw [hhead, dite_eq_left hL]; exact hwr
        · rw [hsame Y' hf]; exact hI.fstR Y' hf
  · -- second epoch
    obtain ⟨h1, h2, h3, h4⟩ := hI.ep2 he
    have tp : team p = false := by
      cases h : team p
      · rfl
      · exact absurd hp (h3 p h)
    have hfst : ∀ g' : Ghost k, g'.ep2 = true → g'.fst team = some false := by
      intro g' h; simp [Ghost.fst, h]
    have hf0 := hfst g he
    refine ⟨⟨g.L ++ [p], true, g.dec⟩, ⟨hI.regv, fun q hq => ?_, hO', hnd, fun h => by simp at h,
      fun _ => ⟨h1, fun q hq => ?_, fun q hq => ?_, h4⟩, hnotin', fun q hq => ?_,
      fun q _ => by rw [hfst _ rfl]; simp, fun q Y hq => ?_, fun q w hq => ?_, fun d hd => ?_,
      fun Y hY => ?_⟩, rfl⟩
    · by_cases hqp : q = p
      · subst hqp; exact hwr
      · rw [hupd q hqp] at hq; exact hI.wrote q hq
    · simp at hq; rcases hq with hq | rfl
      · exact h2 q hq
      · exact tp
    · by_cases hqp : q = p
      · subst hqp; simp
      · rw [hupd q hqp]; exact h3 q hq
    · by_cases hqp : q = p
      · subst hqp; simp at hq
      · rw [hupd q hqp] at hq; exact hI.chk q hq
    · by_cases hqp : q = p
      · subst hqp; simp at hq
      · rw [hupd q hqp] at hq; rw [hfst _ rfl, ← hf0]; exact hI.rdR q Y hq
    · by_cases hqp : q = p
      · subst hqp; simp at hq
      · rw [hupd q hqp] at hq; exact hI.done q w hq
    · rw [hfst _ rfl, ← hf0]
      refine ⟨(hI.dec d hd).1, fun h => by rw [hf0] at h; cases h⟩
    · rw [hfst _ rfl, ← hf0] at hY; exact hI.fstR Y hY

end Steps

end Inv

end Podc.RecoverableHarder
