import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4245

open PEqualNP.CircuitLowerBounds

-- Map input indices to the new initial wires. All other indices keep their
-- offset from the initial wires, including indices past the last gate.
def wireMap {n k : ℕ} (σ : Fin n → Fin k) (i : ℕ) : ℕ :=
  if hi : i < n then (σ ⟨i, hi⟩).val else k + (i - n)

def mapGate (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

def runGate (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op.eval (g.inputs.map fun i => wires.getD i false)]

lemma inputValue {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

lemma wireValue {n k : ℕ} (σ : Fin n → Fin k) (old new tail : List Bool)
    (hold : old.length = n) (hnew : new.length = k)
    (hinput : ∀ i : Fin n, new.getD (σ i).val false = old.getD i.val false) (i : ℕ) :
    (new ++ tail).getD (wireMap σ i) false = (old ++ tail).getD i false := by
  by_cases hi : i < n
  · have hσ := (σ ⟨i, hi⟩).isLt
    simp only [wireMap, hi, dite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
    exact hinput ⟨i, hi⟩
  · simp only [wireMap, hi, dite_false]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    rw [hnew, hold, Nat.add_sub_cancel_left]

-- Evaluating either program appends the same list of gate values.
lemma evaluateGates {n k : ℕ} (σ : Fin n → Fin k) (old new : List Bool)
    (hold : old.length = n) (hnew : new.length = k)
    (hinput : ∀ i : Fin n, new.getD (σ i).val false = old.getD i.val false)
    (gates : List Gate) (tail : List Bool) :
    ∃ values : List Bool,
      (gates.map (mapGate (wireMap σ))).foldl runGate (new ++ tail) = new ++ values ∧
      gates.foldl runGate (old ++ tail) = old ++ values := by
  induction gates generalizing tail with
  | nil => exact ⟨tail, rfl, rfl⟩
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => (old ++ tail).getD i false)
    have hmap : ((g.inputs.map (wireMap σ)).map fun i => (new ++ tail).getD i false) =
        g.inputs.map (fun i => (old ++ tail).getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => wireValue σ old new tail hold hnew hinput i)
    have hstep : runGate (new ++ tail) (mapGate (wireMap σ) g) = new ++ (tail ++ [value]) := by
      simp only [runGate, mapGate, hmap, value, List.append_assoc]
    have hstepOld : runGate (old ++ tail) g = old ++ (tail ++ [value]) := by
      simp only [runGate, value, List.append_assoc]
    simpa only [List.map_cons, List.foldl_cons, hstep, hstepOld] using ih (tail ++ [value])

end PEqualNP.Outside.L_meta_4245

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4245 in
theorem PEqualNP.Outside.L_meta_4245 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1) (x4 x5 : Fin x2)
      (x6 : Fin x1 → Fin x2) (x7 : PEqualNP.CircuitLowerBounds.Circuit),
    PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x1 x7 →
    ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 x10 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x10 ∧
      x10.size ≤ x7.size + (1 : ℕ) ∧ ∀ (x11 : Fin x2 → Bool),
        PEqualNP.MetaComplexity.circuitFun x2 x10 x11 =
          PEqualNP.MetaComplexity.circuitFun x1 x7 fun (x12 : Fin x1) =>
            if x12 = x3 then x11 x4 || x11 x5 else x11 (x6 x12) := by
  intro n k hit left right σ C hmono hback
  let target : Fin n → Fin (k + 1) := fun i =>
    if i = hit then ⟨k, Nat.lt_succ_self k⟩ else (σ i).castSucc
  let first : Gate := ⟨GateOp.or, [left.val, right.val]⟩
  let D : Circuit := ⟨first :: C.gates.map (mapGate (wireMap target)), wireMap target C.output⟩
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hm
    · simp [first]
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hm
      simpa only [mapGate, List.length_map] using hmono g' hg'
  · intro j hj i hi
    cases j with
    | zero =>
      change i ∈ [left.val, right.val] at hi
      rcases List.mem_cons.mp hi with he | he
      · simp [he]
      · have he' : i = right.val := List.mem_singleton.mp he
        simp [he']
    | succ j =>
      have hj' : j < C.gates.length := by simpa [D] using hj
      have hg : NestedCover.gateAt D (j + 1) =
          mapGate (wireMap target) (NestedCover.gateAt C j) := by
        simp [NestedCover.gateAt, D, List.getD_eq_getElem?_getD, hj']
      rw [hg] at hi
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      have hu' := hback j hj' u hu
      by_cases hn : u < n
      · have htarget := (target ⟨u, hn⟩).isLt
        simp only [wireMap, hn, dite_true]
        omega
      · simp only [wireMap, hn, dite_false]
        omega
  · simp [D, Circuit.size]
  · intro x
    let y : Fin n → Bool := fun i => if i = hit then x left || x right else x (σ i)
    let initialWires := List.ofFn x ++ [x left || x right]
    have hinitial : initialWires.length = k + 1 := by simp [initialWires]
    have hinput : ∀ i : Fin n, initialWires.getD (target i).val false = (List.ofFn y).getD i.val false := by
      intro i
      rw [inputValue]
      by_cases hi : i = hit
      · simp only [target, y, hi, ite_true, initialWires]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
      · simp only [target, y, hi, ite_false, Fin.val_castSucc, initialWires]
        rw [List.getD_append _ _ _ _ (by simp), inputValue]
    have hfirst : runGate (List.ofFn x) first = initialWires := by
      simp [runGate, first, initialWires, GateOp.eval]
    obtain ⟨values, hD, hC⟩ := evaluateGates target (List.ofFn y) initialWires (by simp) hinitial hinput C.gates []
    simp only [List.append_nil] at hD hC
    change ((first :: C.gates.map (mapGate (wireMap target))).foldl runGate (List.ofFn x)).getD
      (wireMap target C.output) false = (C.gates.foldl runGate (List.ofFn y)).getD C.output false
    rw [List.foldl_cons, hfirst, hD, hC]
    exact wireValue target _ _ values (by simp) hinitial hinput C.output
