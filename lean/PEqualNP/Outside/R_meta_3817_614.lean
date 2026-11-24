import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_3817_614
    (binary : ∀ (C : Circuit), FanInTwo C →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5)) →
      13 ≤ C.gates.countP (fun g => !(GateOp.rec false false true (fun _ => false) false g.op)))
    (monotone : ∀ (C : Circuit), Monotone2 C → 13 ≤ C.size → C.size ≤ 15 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5))
    (oneNegation : ∀ (C : Circuit), FanInTwo C →
      C.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) = 1 →
      14 ≤ C.size → C.size ≤ 15 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5))
    (twoNegations : ∀ (C : Circuit), FanInTwo C →
      C.gates.countP (fun g => GateOp.rec false false true (fun _ => false) false g.op) = 2 →
      C.size = 15 →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x) ≠ (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (15 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  intro C legal small
  classical
  by_contra noWitness
  have computes (x : Fin 9 → Bool) :
      C.eval (List.ofFn x) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
        x 6 && x 8 || x 8 && x 5) := by
    by_contra differs
    exact noWitness ⟨x, differs⟩
  let isNot (g : Gate) : Bool := GateOp.rec false false true (fun _ => false) false g.op
  have andOrCount : 13 ≤ C.gates.countP (fun g => !isNot g) := binary C legal computes
  have partition : C.size = C.gates.countP isNot + C.gates.countP (fun g => !isNot g) :=
    List.length_eq_countP_add_countP isNot
  have notCount : C.gates.countP isNot = 0 ∨ C.gates.countP isNot = 1 ∨ C.gates.countP isNot = 2 := by
    omega
  rcases notCount with zero | one | two
  · have monotoneC : Monotone2 C := by
      intro g hg
      obtain ⟨hop, hlength⟩ := legal g hg
      change (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
      refine ⟨?_, hlength⟩
      have choices : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        simpa using hop
      rcases choices with hand | hor | hnot
      · exact Or.inl hand
      · exact Or.inr hor
      · have excluded := List.countP_eq_zero.mp zero g hg
        have gate_is_not : isNot g = true := by
          change GateOp.rec false false true (fun _ => false) false g.op = true
          rw [hnot]
        exact (excluded gate_is_not).elim
    exact noWitness (monotone C monotoneC (by omega) small)
  · exact noWitness (oneNegation C legal one (by omega) small)
  · exact noWitness (twoNegations C legal two (by omega))
