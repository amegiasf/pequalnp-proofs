import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.ReadersExport

namespace PEqualNP.Outside.L_meta_604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Helpers.Readers

def H (n : ℕ) (g : (Fin n → Bool) → Bool) (x : Fin (n + 1) → Bool) : Bool :=
  xor (x (Fin.last n)) (g (fun i : Fin n => x i.castSucc))

theorem xorForm (a b : Bool) : ((a || b) && !(a && b)) = xor a b := by
  cases a <;> cases b <;> rfl

theorem xnorForm (a b : Bool) : ((a && b) || !(a || b)) = xor a (!b) := by
  cases a <;> cases b <;> rfl

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

theorem fold_length (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_len, List.length_cons]
    omega

theorem fold_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by rw [step_len]; omega)]
    exact step_lt w g i hi

theorem wires_step (gs : List Gate) (w : List Bool) :
    wiresFrom gs w = gs.foldl step w := by
  simp [wiresFrom, step]

def xorTail (a o m : ℕ) : List Gate :=
  [⟨GateOp.and, [a, o]⟩, ⟨GateOp.or, [a, o]⟩, ⟨GateOp.not, [m]⟩, ⟨GateOp.and, [m + 1, m + 2]⟩]

def xnorTail (a o m : ℕ) : List Gate :=
  [⟨GateOp.and, [a, o]⟩, ⟨GateOp.or, [a, o]⟩, ⟨GateOp.not, [m + 1]⟩, ⟨GateOp.or, [m, m + 2]⟩]

theorem xorTail_ok (a o m : ℕ) : ∀ g ∈ xorTail a o m, Ok g := by
  intro g hg
  simp only [xorTail, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [Ok]

theorem xnorTail_ok (a o m : ℕ) : ∀ g ∈ xnorTail a o m, Ok g := by
  intro g hg
  simp only [xnorTail, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp [Ok]

theorem xorTail_eval (w : List Bool) (a o : ℕ) (ha : a < w.length) (ho : o < w.length) :
    ((xorTail a o w.length).foldl step w).getD (w.length + 3) false =
      xor (w.getD a false) (w.getD o false) := by
  let w1 := step w ⟨GateOp.and, [a, o]⟩
  let w2 := step w1 ⟨GateOp.or, [a, o]⟩
  let w3 := step w2 ⟨GateOp.not, [w.length]⟩
  let w4 := step w3 ⟨GateOp.and, [w.length + 1, w.length + 2]⟩
  have l1 : w1.length = w.length + 1 := step_len _ _
  have l2 : w2.length = w.length + 2 := by rw [step_len, l1]
  have l3 : w3.length = w.length + 3 := by rw [step_len, l2]
  have e1 : w1.getD w.length false = (w.getD a false && w.getD o false) := by
    rw [step_last _ _ _ rfl]
    simp [GateOp.eval]
  have e2 : w2.getD (w.length + 1) false = (w.getD a false || w.getD o false) := by
    rw [step_last _ _ _ l1.symm]
    have ha' : w1.getD a false = w.getD a false := step_lt _ _ _ ha
    have ho' : w1.getD o false = w.getD o false := step_lt _ _ _ ho
    simp [GateOp.eval, ha', ho']
  have e3 : w3.getD (w.length + 2) false = !(w.getD a false && w.getD o false) := by
    rw [step_last _ _ _ l2.symm]
    have h0 : w2.getD w.length false = (w.getD a false && w.getD o false) := by
      rw [step_lt _ _ _ (by omega), e1]
    simp [GateOp.eval, h0]
  have e4 : w4.getD (w.length + 3) false =
      ((w.getD a false || w.getD o false) && !(w.getD a false && w.getD o false)) := by
    rw [step_last _ _ _ l3.symm]
    have hOr : w3.getD (w.length + 1) false = (w.getD a false || w.getD o false) := by
      rw [step_lt _ _ _ (by omega), e2]
    have hNot : w3.getD (w.length + 2) false = !(w.getD a false && w.getD o false) := e3
    simp [GateOp.eval, hOr, hNot]
  have hfold : (xorTail a o w.length).foldl step w = w4 := by
    simp [xorTail, w1, w2, w3, w4, step]
  rw [hfold, e4, xorForm]

theorem xnorTail_eval (w : List Bool) (a o : ℕ) (ha : a < w.length) (ho : o < w.length) :
    ((xnorTail a o w.length).foldl step w).getD (w.length + 3) false =
      xor (w.getD a false) (!(w.getD o false)) := by
  let w1 := step w ⟨GateOp.and, [a, o]⟩
  let w2 := step w1 ⟨GateOp.or, [a, o]⟩
  let w3 := step w2 ⟨GateOp.not, [w.length + 1]⟩
  let w4 := step w3 ⟨GateOp.or, [w.length, w.length + 2]⟩
  have l1 : w1.length = w.length + 1 := step_len _ _
  have l2 : w2.length = w.length + 2 := by rw [step_len, l1]
  have l3 : w3.length = w.length + 3 := by rw [step_len, l2]
  have e1 : w1.getD w.length false = (w.getD a false && w.getD o false) := by
    rw [step_last _ _ _ rfl]
    simp [GateOp.eval]
  have e2 : w2.getD (w.length + 1) false = (w.getD a false || w.getD o false) := by
    rw [step_last _ _ _ l1.symm]
    simp [GateOp.eval, step_lt _ _ _ ha, step_lt _ _ _ ho]
  have e3 : w3.getD (w.length + 2) false = !(w.getD a false || w.getD o false) := by
    rw [step_last _ _ _ l2.symm]
    have h0 : w2.getD (w.length + 1) false = (w.getD a false || w.getD o false) := e2
    simp [GateOp.eval, h0]
  have e4 : w4.getD (w.length + 3) false =
      ((w.getD a false && w.getD o false) || !(w.getD a false || w.getD o false)) := by
    rw [step_last _ _ _ l3.symm]
    have hAnd : w3.getD w.length false = (w.getD a false && w.getD o false) := by
      rw [step_lt _ _ _ (by omega), step_lt _ _ _ (by omega), e1]
    have hNot : w3.getD (w.length + 2) false = !(w.getD a false || w.getD o false) := e3
    simp [GateOp.eval, hAnd, hNot]
  have hfold : (xnorTail a o w.length).foldl step w = w4 := by
    simp [xnorTail, w1, w2, w3, w4, step]
  rw [hfold, e4, xnorForm]

theorem output_lt {n : ℕ} (g : (Fin n → Bool) → Bool) (C : Circuit)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = g x)
    (hnc : ∃ y y' : Fin n → Bool, g y ≠ g y') : C.output < n + C.gates.length := by
  by_contra hge
  obtain ⟨y, y', hne⟩ := hnc
  apply hne
  have hfalse : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = false := by
    intro x
    rw [wires_eq]
    exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
  rw [← hev y, ← hev y', hfalse, hfalse]

theorem upperOf (n : ℕ) (g : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, g y ≠ g y') (hg : HasCircuitSize n g s) :
    HasCircuitSize (n + 1) (H n g) (s + 4) := by
  have hrel := relabel_size Fin.castSucc g s hg
  obtain ⟨C, hok, hsz, hev⟩ := hrel
  have hnc' : ∃ y y' : Fin (n + 1) → Bool,
      g (fun i : Fin n => y i.castSucc) ≠ g (fun i : Fin n => y' i.castSucc) := by
    obtain ⟨y, y', hne⟩ := hnc
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    simpa [Fin.snoc_castSucc] using hne
  have ho := output_lt (fun x => g (fun i => x i.castSucc)) C hev hnc'
  have hsz' : C.gates.length ≤ s := hsz
  let m := n + 1 + C.gates.length
  let tail := xorTail n C.output m
  refine ⟨⟨C.gates ++ tail, m + 3⟩, ?_, ?_, ?_⟩
  · intro gate hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hok gate hg
    · exact xorTail_ok _ _ _ _ hg
  · change (C.gates ++ tail).length ≤ s + 4
    simp only [List.length_append, tail, xorTail, List.length_cons, List.length_nil]
    omega
  · intro x
    rw [show ((C.gates ++ tail).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x)).getD (m + 3) false = ((C.gates ++ tail).foldl step (List.ofFn x)).getD (m + 3) false
      by rfl]
    rw [List.foldl_append]
    let w := C.gates.foldl step (List.ofFn x)
    have hlen : w.length = m := by
      rw [fold_length]
      simp [w, m]
    have ha : n < w.length := by rw [hlen]; omega
    have ho' : C.output < w.length := by rw [hlen]; exact ho
    have hlast : w.getD n false = x (Fin.last n) := by
      rw [fold_lt _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    have hbase : w.getD C.output false = g (fun i : Fin n => x i.castSucc) := by
      have : C.eval (List.ofFn x) = g (fun i => x i.castSucc) := hev x
      rw [← this, wires_eq, wires_step]
      rfl
    have htail := xorTail_eval w n C.output ha ho'
    have heq : (tail.foldl step w).getD (w.length + 3) false =
        xor (w.getD n false) (w.getD C.output false) := by
      simpa [tail, hlen] using htail
    rw [heq, hlast, hbase]
    rfl

theorem upperNot (n : ℕ) (g : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, g y ≠ g y')
    (hg : HasCircuitSize n (fun y : Fin n → Bool => !(g y)) s) :
    HasCircuitSize (n + 1) (H n g) (s + 4) := by
  have hrel := relabel_size Fin.castSucc (fun y : Fin n → Bool => !(g y)) s hg
  obtain ⟨C, hok, hsz, hev⟩ := hrel
  have hnc' : ∃ y y' : Fin (n + 1) → Bool,
      (!(g (fun i : Fin n => y i.castSucc))) ≠ (!(g (fun i : Fin n => y' i.castSucc))) := by
    obtain ⟨y, y', hne⟩ := hnc
    refine ⟨Fin.snoc y false, Fin.snoc y' false, ?_⟩
    simpa [Fin.snoc_castSucc] using hne
  have ho := output_lt (fun x => !(g (fun i => x i.castSucc))) C hev hnc'
  have hsz' : C.gates.length ≤ s := hsz
  let m := n + 1 + C.gates.length
  let tail := xnorTail n C.output m
  refine ⟨⟨C.gates ++ tail, m + 3⟩, ?_, ?_, ?_⟩
  · intro gate hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hok gate hg
    · exact xnorTail_ok _ _ _ _ hg
  · change (C.gates ++ tail).length ≤ s + 4
    simp only [List.length_append, tail, xnorTail, List.length_cons, List.length_nil]
    omega
  · intro x
    rw [List.foldl_append]
    let w := C.gates.foldl step (List.ofFn x)
    change (tail.foldl step w).getD (m + 3) false = H n g x
    have hlen : w.length = m := by
      rw [fold_length]
      simp [w, m]
    have ha : n < w.length := by rw [hlen]; omega
    have ho' : C.output < w.length := by rw [hlen]; exact ho
    have hlast : w.getD n false = x (Fin.last n) := by
      rw [fold_lt _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    have hbase : w.getD C.output false = !(g (fun i : Fin n => x i.castSucc)) := by
      have : C.eval (List.ofFn x) = !(g (fun i => x i.castSucc)) := hev x
      rw [← this, wires_eq, wires_step]
    have htail := xnorTail_eval w n C.output ha ho'
    have heq : (tail.foldl step w).getD (w.length + 3) false =
        xor (w.getD n false) (!(w.getD C.output false)) := by
      simpa [tail, hlen] using htail
    rw [heq, hlast, hbase]
    simp [H, Bool.not_not]

end PEqualNP.Outside.L_meta_604
