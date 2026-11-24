import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4095_1
    (normalise : ∀ (n : ℕ) (C : Circuit), IsMinimalCircuit n C →
      (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
      ∃ D : Circuit,
        D.gates = C.gates.map (fun g => ⟨g.op, g.inputs.take (bif g.op.eval [false] then 1 else 2)⟩) ∧
        circuitFun n D = circuitFun n C ∧ ReadsBack n D ∧
        ∀ g ∈ D.gates, if g.op.eval [false] then g.inputs.length = 1
          else g.inputs.length = 2 ∧ g.inputs.Nodup)
    (clean : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let readers (v : Fin n) := C.gates.filter fun g => g.inputs.contains v.val
      let later (i : ℕ) := (C.gates.drop (i + 1)).filter fun g => g.inputs.contains (n + i)
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → IsMinimalCircuit n C → circuitFun n C = f →
      ReadsBack n C →
      (∀ g ∈ C.gates, if g.op.eval [false] then g.inputs.length = 1
        else g.inputs.length = 2 ∧ g.inputs.Nodup) →
      (∀ v ∉ A, 2 ≤ (readers v).length ∧ (readers v).length ≤ 3 ∧
        ((readers v).length = 3 → ∀ g ∈ readers v, g.op = .or)) →
      (∃ v ∉ A, (readers v).length = 2 ∧ ∃ g ∈ readers v, g.op = .and) →
      (∀ v ∉ A, ∀ i g, C.gates[i]? = some g → g.op = .and → g.inputs.contains v.val →
        (∃ h ∈ readers v, h.op = .or) ∧ (later i).length ≤ 1 ∧ ∀ h ∈ later i, h.op = .or) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs;   have x8 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x8 : Fin x1) => List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x9).contains ↑x8) x5.gates;   have x9 : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : ℕ) => List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x10).contains (x1 + x9)) (List.drop (x9 + (1 : ℕ)) x5.gates);   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (∀ (x11 : Fin x1) (x12 : x2.Walk x11 x11), x12.IsCycle → (7 : ℕ) ≤ x12.length) → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x16 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x16 → x5.size ≤ x16) → (∀ x17 ∉ x4, (2 : ℕ) ≤ (x8 x17).length ∧ (x8 x17).length ≤ (3 : ℕ) ∧ ((x8 x17).length = (3 : ℕ) → ∀ x20 ∈ x8 x17, x20.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x18 ∉ x4, (x8 x18).length = (2 : ℕ) ∧ ∃ x19 ∈ x8 x18, x19.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ x19 ∉ x4, ∀ (x21 : ℕ) (x22 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x21]? = Option.some x22 → x22.op = PEqualNP.CircuitLowerBounds.GateOp.and → (x7 x22).contains ↑x19 = Bool.true → (∃ x26 ∈ x8 x19, x26.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (x9 x21).length ≤ (1 : ℕ) ∧ ∀ x26 ∈ x9 x21, x26.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ x20 ∉ x4, ∃ (x21 : ℕ), x21 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => x6 (Function.update x22 x20 Bool.false)) x21 := by
  classical
  intro n G dec A C f eff readers later degree girth marked edge fan computes least reads andReader next
  have minimal : IsMinimalCircuit n C := by
    refine ⟨fan, ?_⟩
    intro E hE hEq
    exact least E.size ⟨E, hE, le_rfl, fun x => congrFun (hEq.trans computes) x⟩
  have varying : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
    obtain ⟨u, v, huv⟩ := edge
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [computes]
    change (decide (∃ a ∈ A, (false : Bool) = true) ||
      decide (∃ a b, G.Adj a b ∧ (false : Bool) = true ∧ (false : Bool) = true)) ≠
      (decide (∃ a ∈ A, (true : Bool) = true) ||
      decide (∃ a b, G.Adj a b ∧ (true : Bool) = true ∧ (true : Bool) = true))
    simp [show ∃ a b, G.Adj a b from ⟨u, v, huv⟩]
  obtain ⟨D, gates, eval, back, shape⟩ := normalise n C minimal varying
  let trim (g : Gate) : Gate := ⟨g.op, eff g⟩
  change D.gates = C.gates.map trim at gates
  have size : D.size = C.size := by
    change D.gates.length = C.gates.length
    rw [gates, List.length_map]
  have legal : FanInTwo D := by
    intro g hg
    rw [gates] at hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    refine ⟨(fan a ha).1, ?_⟩
    change (eff a).length ≤ 2
    cases h : a.op.eval [false] <;> simp [eff, h]
  have minimum : IsMinimalCircuit n D := by
    refine ⟨legal, ?_⟩
    intro E hE hEq
    rw [size]
    exact minimal.2 E hE (hEq.trans eval)
  let rd (v : Fin n) := D.gates.filter fun g => g.inputs.contains v.val
  let nxt (i : ℕ) := (D.gates.drop (i + 1)).filter fun g => g.inputs.contains (n + i)
  have mapFilter (l : List Gate) (w : ℕ) :
      (((l.map trim).filter (fun g => g.inputs.contains w)).map Gate.op) =
        ((l.filter (fun g => (eff g).contains w)).map Gate.op) := by
    simp only [List.filter_map, List.map_map]
    rfl
  have readerOps (v : Fin n) : (rd v).map Gate.op = (readers v).map Gate.op := by
    change (D.gates.filter _).map Gate.op = _
    rw [gates]
    exact mapFilter C.gates v.val
  have readerLen (v : Fin n) : (rd v).length = (readers v).length := by
    simpa only [List.length_map] using congrArg List.length (readerOps v)
  have laterOps (i : ℕ) : (nxt i).map Gate.op = (later i).map Gate.op := by
    change ((D.gates.drop (i + 1)).filter _).map Gate.op = _
    rw [gates, ← List.map_drop]
    exact mapFilter (C.gates.drop (i + 1)) (n + i)
  have laterLen (i : ℕ) : (nxt i).length = (later i).length := by
    simpa only [List.length_map] using congrArg List.length (laterOps i)
  have transfer {L L' : List Gate} (ops : L.map Gate.op = L'.map Gate.op) (op : GateOp) :
      (∃ g ∈ L, g.op = op) ↔ ∃ g ∈ L', g.op = op := by
    simpa only [List.mem_map] using (show op ∈ L.map Gate.op ↔ op ∈ L'.map Gate.op by rw [ops])
  have bound : ∀ v ∉ A, 2 ≤ (rd v).length ∧ (rd v).length ≤ 3 ∧
      ((rd v).length = 3 → ∀ g ∈ rd v, g.op = .or) := by
    intro v hv
    obtain ⟨lo, hi, hor⟩ := reads v hv
    refine ⟨by simpa only [readerLen] using lo, by simpa only [readerLen] using hi, ?_⟩
    intro h g hg
    obtain ⟨a, ha, hop⟩ := (transfer (readerOps v) g.op).mp ⟨g, hg, rfl⟩
    exact hop ▸ hor (by simpa only [readerLen] using h) a ha
  have andD : ∃ v ∉ A, (rd v).length = 2 ∧ ∃ g ∈ rd v, g.op = .and := by
    obtain ⟨v, hv, hlen, hw⟩ := andReader
    exact ⟨v, hv, by simpa only [readerLen] using hlen, (transfer (readerOps v) .and).mpr hw⟩
  have nextD : ∀ v ∉ A, ∀ i g, D.gates[i]? = some g → g.op = .and → g.inputs.contains v.val →
      (∃ h ∈ rd v, h.op = .or) ∧ (nxt i).length ≤ 1 ∧ ∀ h ∈ nxt i, h.op = .or := by
    intro v hv i g hg hop pin
    rw [gates, List.getElem?_map] at hg
    cases ha : C.gates[i]? with
    | none => simp [ha] at hg
    | some a =>
      have eq : trim a = g := by simpa [ha] using hg
      subst g
      obtain ⟨hor, hlen, hall⟩ := next v hv i a ha hop pin
      refine ⟨(transfer (readerOps v) .or).mpr hor, by simpa only [laterLen] using hlen, ?_⟩
      intro b hb
      obtain ⟨c, hc, hbc⟩ := (transfer (laterOps i) b.op).mp ⟨b, hb, rfl⟩
      exact hbc ▸ hall c hc
  obtain ⟨v, hv, s, hs, res⟩ := clean n G A D degree girth marked minimum
    (eval.trans computes) back shape bound andD nextD
  exact ⟨v, hv, s, by simpa only [size] using hs, res⟩
