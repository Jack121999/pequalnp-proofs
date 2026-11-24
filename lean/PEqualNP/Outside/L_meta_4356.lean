import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Signal (n : ℕ) := (Fin n → Bool) → Bool

def inputs (n : ℕ) : List (Signal n) := List.ofFn fun i x => x i

def constant {n : ℕ} (f : Signal n) : Prop := ∃ b : Bool, f = fun _ => b

def readSignal {n : ℕ} (w : List (Signal n)) (i : ℕ) : Signal n := w.getD i (fun _ => false)

def gateSignal {n : ℕ} (w : List (Signal n)) (g : Gate) : Signal n :=
  fun x => g.op.eval (g.inputs.map fun i => readSignal w i x)

def wireSignals {n : ℕ} (gs : List Gate) (w : List (Signal n)) : List (Signal n) :=
  gs.foldl (fun a g => a ++ [gateSignal a g]) w

def gateSignals {n : ℕ} (gs : List Gate) (w : List (Signal n)) : List (Signal n) :=
  (wireSignals gs w).drop w.length

def allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

lemma read_map {n : ℕ} (w : List (Signal n)) (i : ℕ) (x : Fin n → Bool) :
    (w.map fun f => f x).getD i false = readSignal w i x := by
  simp only [readSignal, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

lemma wireSignals_eval {n : ℕ} (gs : List Gate) (w : List (Signal n)) (x : Fin n → Bool) :
    (wireSignals gs w).map (fun f => f x) = (Circuit.mk gs 0).wires (w.map fun f => f x) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wireSignals gs (w ++ [gateSignal w g])).map (fun f => f x) =
      (Circuit.mk gs 0).wires ((w.map fun f => f x) ++
        [g.op.eval (g.inputs.map fun i => (w.map fun f => f x).getD i false)])
    rw [ih]
    simp only [List.map_append, List.map_cons, List.map_nil, gateSignal, read_map]

lemma wireSignals_snoc {n : ℕ} (gs : List Gate) (g : Gate) (w : List (Signal n)) :
    wireSignals (gs ++ [g]) w = wireSignals gs w ++ [gateSignal (wireSignals gs w) g] := by
  simp [wireSignals, List.foldl_append]

lemma wire_parts {n : ℕ} (gs : List Gate) (w : List (Signal n)) :
    wireSignals gs w = w ++ gateSignals gs w ∧ (gateSignals gs w).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wireSignals, gateSignals]
  | append_singleton gs g ih =>
    have shape : wireSignals (gs ++ [g]) w =
        w ++ (gateSignals gs w ++ [gateSignal (wireSignals gs w) g]) := by
      rw [wireSignals_snoc, ← List.append_assoc, ← ih.1]
    have tail : gateSignals (gs ++ [g]) w = gateSignals gs w ++ [gateSignal (wireSignals gs w) g] := by
      rw [gateSignals, shape, List.drop_append_length]
    rw [shape, tail]
    simp [ih.2]

lemma gateSignals_snoc {n : ℕ} (gs : List Gate) (g : Gate) (w : List (Signal n)) :
    gateSignals (gs ++ [g]) w = gateSignals gs w ++ [gateSignal (wireSignals gs w) g] := by
  have shape : wireSignals (gs ++ [g]) w =
      w ++ (gateSignals gs w ++ [gateSignal (wireSignals gs w) g]) := by
    rw [wireSignals_snoc, ← List.append_assoc, ← (wire_parts gs w).1]
  rw [gateSignals, shape, List.drop_append_length]

lemma available_read {n : ℕ} (old new : List (Signal n))
    (represented : ∀ f ∈ old, constant f ∨ f ∈ new) (i : ℕ) :
    constant (readSignal old i) ∨ readSignal old i ∈ new := by
  by_cases hi : i < old.length
  · unfold readSignal
    rw [List.getD_eq_getElem _ _ hi]
    exact represented _ (List.getElem_mem hi)
  · left
    exact ⟨false, List.getD_eq_default _ _ (by omega)⟩

lemma available_index {n : ℕ} {w : List (Signal n)} {f : Signal n} (h : f ∈ w) :
    ∃ i : ℕ, readSignal w i = f := by
  obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, (List.getD_eq_getElem _ _ hi).trans hval⟩

def combine (b : Bool) (xs : List Bool) : Bool := if b then xs.all id else xs.any id

lemma combine_id (b : Bool) (xs : List Bool) : combine b (b :: xs) = combine b xs := by
  cases b <;> simp [combine]

lemma combine_absorb (b z : Bool) (xs : List Bool) (h : combine b xs = !b) :
    combine b (z :: xs) = !b := by
  cases b <;> simp_all [combine]

lemma combine_head (b : Bool) (xs : List Bool) : combine b ((!b) :: xs) = !b := by
  cases b <;> simp [combine]

lemma combine_congr (b z : Bool) (xs ys : List Bool) (h : combine b xs = combine b ys) :
    combine b (z :: xs) = combine b (z :: ys) := by
  cases b <;> simp_all [combine]

lemma compileArgs {n : ℕ} (old new : List (Signal n))
    (represented : ∀ f ∈ old, constant f ∨ f ∈ new) (b : Bool) (is : List ℕ) :
    (∀ x, combine b (is.map fun i => readSignal old i x) = !b) ∨
    ∃ js : List ℕ, js.length ≤ is.length ∧
      ∀ x, combine b (is.map fun i => readSignal old i x) = combine b (js.map fun j => readSignal new j x) := by
  induction is with
  | nil => exact Or.inr ⟨[], le_rfl, fun _ => rfl⟩
  | cons i is ih =>
    rcases ih with ha | ⟨js, hlen, heq⟩
    · exact Or.inl fun x => combine_absorb b _ _ (ha x)
    · rcases available_read old new represented i with ⟨c, hc⟩ | hm
      · by_cases h : c = b
        · refine Or.inr ⟨js, hlen.trans (Nat.le_succ _), ?_⟩
          intro x
          simpa only [List.map_cons, hc, h, combine_id] using heq x
        · have hc' : c = !b := by cases c <;> cases b <;> simp_all
          exact Or.inl (fun x => by simp only [List.map_cons, hc, hc', combine_head])
      · obtain ⟨j, hj⟩ := available_index hm
        refine Or.inr ⟨j :: js, by simpa using hlen, ?_⟩
        intro x
        exact combine_congr b (readSignal old i x) _ _ (heq x) |>.trans
          (by simp only [List.map_cons, hj])

lemma compileGate {n : ℕ} (old new : List (Signal n)) (g : Gate)
    (represented : ∀ f ∈ old, constant f ∨ f ∈ new) (hg : allowed g)
    (hn : ¬ constant (gateSignal old g)) :
    ∃ g' : Gate, allowed g' ∧ gateSignal new g' = gateSignal old g := by
  obtain ⟨op, is⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with hop | hop | hop <;> dsimp only at hop <;> subst op
  · rcases compileArgs old new represented true is with h | ⟨js, hj, heq⟩
    · exact (hn ⟨false, funext h⟩).elim
    · exact ⟨⟨.and, js⟩, ⟨Or.inl rfl, hj.trans hlen⟩, (funext heq).symm⟩
  · rcases compileArgs old new represented false is with h | ⟨js, hj, heq⟩
    · exact (hn ⟨true, funext h⟩).elim
    · exact ⟨⟨.or, js⟩, ⟨Or.inr (Or.inl rfl), hj.trans hlen⟩, (funext heq).symm⟩
  · cases is with
    | nil => exact (hn ⟨true, rfl⟩).elim
    | cons i is =>
      rcases available_read old new represented i with ⟨c, hc⟩ | hm
      · apply False.elim (hn ⟨!c, ?_⟩)
        funext x
        simp [gateSignal, GateOp.eval, hc]
      · obtain ⟨j, hj⟩ := available_index hm
        refine ⟨⟨.not, [j]⟩, by simp [allowed], ?_⟩
        funext x
        simp [gateSignal, GateOp.eval, hj]

-- Add a gate only when its function is neither a constant nor already available.
lemma replay {n : ℕ} (initial : List (Signal n)) (gs : List Gate)
    (hinit : ∀ f ∈ initial, constant f ∨ f ∈ inputs n)
    (hgs : ∀ g ∈ gs, allowed g) :
    ∃ ds : List Gate,
      (∀ g ∈ ds, allowed g) ∧
      (gateSignals ds (inputs n)).Nodup ∧
      (∀ f ∈ gateSignals ds (inputs n), ¬ constant f ∧ f ∉ inputs n) ∧
      (∀ f ∈ gateSignals ds (inputs n), f ∈ gateSignals gs initial) ∧
      ∀ f ∈ wireSignals gs initial, constant f ∨ f ∈ wireSignals ds (inputs n) := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], ?_, ?_, ?_, ?_, hinit⟩ <;> simp [gateSignals, wireSignals]
  | append_singleton gs g ih =>
    obtain ⟨ds, hd, hnd, hbase, hsub, havail⟩ := ih (fun gate hm => hgs gate (List.mem_append_left _ hm))
    let old := wireSignals gs initial
    let new := wireSignals ds (inputs n)
    let f := gateSignal old g
    by_cases hf : constant f ∨ f ∈ new
    · refine ⟨ds, hd, hnd, hbase, ?_, ?_⟩
      · intro a ha
        rw [gateSignals_snoc]
        exact List.mem_append_left _ (hsub a ha)
      · intro a ha
        rw [wireSignals_snoc, List.mem_append, List.mem_singleton] at ha
        rcases ha with h | rfl
        · exact havail _ h
        · exact hf
    · have hn : ¬ constant f := fun h => hf (Or.inl h)
      have hnot : f ∉ new := fun h => hf (Or.inr h)
      obtain ⟨g', hg', he⟩ := compileGate old new g havail (hgs g (by simp)) hn
      have wireEq : wireSignals (ds ++ [g']) (inputs n) = new ++ [f] := by
        rw [wireSignals_snoc]
        change new ++ [gateSignal new g'] = _
        rw [he]
      have gateEq : gateSignals (ds ++ [g']) (inputs n) = gateSignals ds (inputs n) ++ [f] := by
        rw [gateSignals_snoc]
        change gateSignals ds (inputs n) ++ [gateSignal new g'] = _
        rw [he]
      have hnew : new = inputs n ++ gateSignals ds (inputs n) := (wire_parts ds (inputs n)).1
      have fnotOld : f ∉ gateSignals ds (inputs n) := fun h => hnot (hnew ▸ List.mem_append_right _ h)
      have fnotInput : f ∉ inputs n := fun h => hnot (hnew ▸ List.mem_append_left _ h)
      refine ⟨ds ++ [g'], ?_, ?_, ?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hd a h
        · obtain rfl := List.mem_singleton.mp h
          exact hg'
      · rw [gateEq, List.nodup_append']
        exact ⟨hnd, by simp, fun a ha hb => fnotOld ((List.mem_singleton.mp hb).symm ▸ ha)⟩
      · intro a ha
        rw [gateEq, List.mem_append, List.mem_singleton] at ha
        rcases ha with h | rfl
        · exact hbase _ h
        · exact ⟨hn, fnotInput⟩
      · intro a ha
        rw [gateEq, List.mem_append, List.mem_singleton] at ha
        rw [gateSignals_snoc]
        rcases ha with h | rfl
        · exact List.mem_append_left _ (hsub _ h)
        · simp [f, old]
      · intro a ha
        rw [wireSignals_snoc, List.mem_append, List.mem_singleton] at ha
        rw [wireEq, List.mem_append, List.mem_singleton]
        rcases ha with h | rfl
        · rcases havail _ h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr rfl)

lemma circuitRead {n : ℕ} (C : Circuit) (w : List (Signal n)) (x : Fin n → Bool) (i : ℕ) :
    (C.wires (w.map fun f => f x)).getD i false = readSignal (wireSignals C.gates w) i x := by
  change ((Circuit.mk C.gates 0).wires (w.map fun f => f x)).getD i false = _
  rw [← wireSignals_eval]
  exact read_map _ _ _

lemma evaluateInputs {n : ℕ} (x : Fin n → Bool) : (inputs n).map (fun f => f x) = List.ofFn x := by
  rw [inputs, List.map_ofFn]
  rfl

end PEqualNP.Outside.L_meta_4356

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4356 in
theorem PEqualNP.Outside.L_meta_4356 :
    have x1 : (Fin (6 : ℕ) → Bool) → List Bool := fun (x1 : Fin (6 : ℕ) → Bool) =>
      [x1 (0 : Fin (6 : ℕ)), x1 (1 : Fin (6 : ℕ)), Bool.false, x1 (2 : Fin (6 : ℕ)),
        x1 (3 : Fin (6 : ℕ)), x1 (4 : Fin (6 : ℕ)), x1 (5 : Fin (6 : ℕ))];
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) →
        PEqualNP.MetaComplexity.HasCircuitSize (6 : ℕ)
          (fun (x5 : Fin (6 : ℕ) → Bool) => x2.eval (x1 x5)) (7 : ℕ) ∨
        have x5 : Fin (11 : ℕ) → (Fin (6 : ℕ) → Bool) → Bool :=
          fun (x5 : Fin (11 : ℕ)) (x6 : Fin (6 : ℕ) → Bool) =>
            (x2.wires (x1 x6)).getD ((7 : ℕ) + ↑x5) Bool.false;
        ∃ (x6 : Fin (8 : ℕ) → Fin (11 : ℕ)),
          (∀ (x7 x8 : Fin (8 : ℕ)), x7 ≠ x8 → ∃ (x10 : Fin (6 : ℕ) → Bool),
            x5 (x6 x7) x10 ≠ x5 (x6 x8) x10) ∧
          ∀ (x7 x8 : Fin (8 : ℕ)), ∃ (x9 : Fin (6 : ℕ) → Bool),
            x5 (x6 x7) x9 ≠ (Bool.false :: Bool.true :: List.ofFn x9).getD (↑x8) Bool.false := by
  dsimp only
  intro C hfan hsize
  let initial : List (Signal 6) := [fun x => x 0, fun x => x 1, fun _ => false,
    fun x => x 2, fun x => x 3, fun x => x 4, fun x => x 5]
  let row (x : Fin 6 → Bool) := [x 0, x 1, false, x 2, x 3, x 4, x 5]
  have hinit : ∀ f ∈ initial, constant f ∨ f ∈ inputs 6 := by
    intro f h
    simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (List.mem_ofFn.mpr ⟨0, rfl⟩)
    · exact Or.inr (List.mem_ofFn.mpr ⟨1, rfl⟩)
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inr (List.mem_ofFn.mpr ⟨2, rfl⟩)
    · exact Or.inr (List.mem_ofFn.mpr ⟨3, rfl⟩)
    · exact Or.inr (List.mem_ofFn.mpr ⟨4, rfl⟩)
    · exact Or.inr (List.mem_ofFn.mpr ⟨5, rfl⟩)
  have hAllowed : ∀ g ∈ C.gates, allowed g := by
    intro g hg
    simpa [allowed] using hfan g hg
  obtain ⟨ds, hd, hnodup, hnontrivial, hsub, havail⟩ := replay initial C.gates hinit hAllowed
  let values := gateSignals ds (inputs 6)
  let original := gateSignals C.gates initial
  have originalLen : original.length = 11 := (wire_parts C.gates initial).2.trans hsize
  have evalOriginal (x : Fin 6 → Bool) (i : ℕ) :
      (C.wires (row x)).getD i false = readSignal (wireSignals C.gates initial) i x :=
    circuitRead C initial x i
  change HasCircuitSize 6 (fun x => C.eval (row x)) 7 ∨ _
  by_cases few : ds.length ≤ 7
  · left
    rcases available_read (wireSignals C.gates initial) (wireSignals ds (inputs 6)) havail C.output with
      ⟨b, hb⟩ | hm
    · let out : Circuit := ⟨[⟨if b then GateOp.and else GateOp.or, []⟩], 6⟩
      refine ⟨out, ?_, by change 1 ≤ 7; decide, ?_⟩
      · cases b <;> simp [FanInTwo, out]
      · intro x
        change out.eval (List.ofFn x) = (C.wires (row x)).getD C.output false
        rw [evalOriginal, hb]
        cases b <;> rfl
    · obtain ⟨o, ho⟩ := available_index hm
      refine ⟨⟨ds, o⟩, ?_, few, ?_⟩
      · intro g hg
        simpa [allowed] using hd g hg
      · intro x
        change ((Circuit.mk ds o).wires (List.ofFn x)).getD o false =
          (C.wires (row x)).getD C.output false
        rw [← evaluateInputs x, circuitRead, ho, evalOriginal]
  · right
    have many : 8 ≤ values.length := by
      change 8 ≤ (gateSignals ds (inputs 6)).length
      rw [(wire_parts ds (inputs 6)).2]
      omega
    let pick (i : Fin 8) : Signal 6 := values[i.val]'(i.isLt.trans_le many)
    have pick_mem (i : Fin 8) : pick i ∈ values := List.getElem_mem _
    have index (i : Fin 8) : ∃ j : Fin 11, original[j.val]'(by omega) = pick i := by
      obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.mp (hsub (pick i) (pick_mem i))
      change j < original.length at hj
      exact ⟨⟨j, by simpa only [originalLen] using hj⟩, e⟩
    choose embed hembed using index
    have read_at (j : Fin 11) (x : Fin 6 → Bool) :
        (C.wires (row x)).getD (7 + j.val) false = (original[j.val]'(by omega)) x := by
      rw [evalOriginal, (wire_parts C.gates initial).1]
      unfold readSignal
      rw [List.getD_append_right _ _ _ _ (by simp [initial])]
      have h : initial.length = 7 := rfl
      rw [h, Nat.add_sub_cancel_left]
      have hj : j.val < (gateSignals C.gates initial).length := by
        change j.val < original.length
        rw [originalLen]
        exact j.isLt
      rw [List.getD_eq_getElem _ _ hj]
    have agreement (i : Fin 8) (x : Fin 6 → Bool) :
        (C.wires (row x)).getD (7 + (embed i).val) false = pick i x := by
      simp only [read_at, hembed]
    refine ⟨embed, ?_, ?_⟩
    · intro i j ne
      by_contra! h
      have eq : pick i = pick j := by
        funext x
        exact (agreement i x).symm.trans ((h x).trans (agreement j x))
      exact ne (Fin.ext (hnodup.getElem_inj.mp eq))
    · intro i r
      let literals : List (Signal 6) := (fun _ => false) :: (fun _ => true) :: inputs 6
      have hl : literals.length = 8 := by simp [literals, inputs]
      have lit (x : Fin 6 → Bool) :
          (false :: true :: List.ofFn x).getD r.val false = readSignal literals r.val x := by
        rw [← read_map, show (literals.map fun f => f x) = false :: true :: List.ofFn x by
          simp only [literals, List.map_cons, evaluateInputs]]
      have mem : readSignal literals r.val ∈ literals := by
        unfold readSignal
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      by_contra! h
      have eq : pick i = readSignal literals r.val := by
        funext x
        exact (agreement i x).symm.trans ((h x).trans (lit x))
      have bad := hnontrivial (pick i) (pick_mem i)
      rw [← eq] at mem
      simp only [literals, List.mem_cons] at mem
      rcases mem with h | h | h
      · exact bad.1 ⟨false, h⟩
      · exact bad.1 ⟨true, h⟩
      · exact bad.2 h
