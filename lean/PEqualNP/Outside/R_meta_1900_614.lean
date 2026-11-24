import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.BicliqueBlockCost

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_1900_614
    (normalize : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (D : Circuit),
      G.edgeFinset.Nonempty → Monotone2 D → circuitFun m D = graphFun G ∅ →
      ∃ C : Circuit, IsLeastAO G C ∧ TopForm G C ∧ C.size ≤ D.size)
    (account : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      G.edgeFinset.card + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1)
    (charge : ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      ∃ K : Finset (Fin m),
        (∀ u v : Fin m, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
        (Ustar G C).card + K.card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  intro n G D hedge hcycle hmono heval
  classical
  have no4 : NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    by_contra hab
    exact hcycle u a v b (G.ne_of_adj ha'.1) huv (G.ne_of_adj hb'.1)
      (G.ne_of_adj ha'.2.symm) hab (G.ne_of_adj hb'.2) ha'.1 ha'.2.symm hb'.2 hb'.1.symm
  have nonempty : G.edgeFinset.Nonempty := by
    obtain ⟨u, v, huv⟩ := hedge
    exact ⟨s(u, v), by simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using huv⟩
  have computes : circuitFun n D = graphFun G ∅ := by
    funext x
    change D.eval (List.ofFn x) = (decide (∃ a ∈ (∅ : Finset (Fin n)), x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.coe_iff_coe, decide_eq_true_iff] using heval x
  obtain ⟨C, least, top, size_le⟩ := normalize n G D nonempty hmono computes
  obtain ⟨K, covers, budget⟩ := charge n G C no4 nonempty least top
  have gate_count := account n G C no4 nonempty least top
  have size_budget : G.edgeFinset.card + K.card ≤ D.size + 1 := by omega
  let leaves (u : Fin n) := (G.neighborFinset u).filter (fun v => v ∉ K ∨ u < v)
  have leaf_iff {u v : Fin n} : v ∈ leaves u ↔ G.Adj u v ∧ (v ∉ K ∨ u < v) := by
    change v ∈ (G.neighborFinset u).filter _ ↔ _
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  let centers := K.filter (fun u => (leaves u).Nonempty)
  let block (u : Fin n) : Block n := ({u}, leaves u)
  let F := centers.image block
  have designated {u v : Fin n} (h : G.Adj u v) :
      (u ∈ K ∧ v ∈ leaves u) ∨ (v ∈ K ∧ u ∈ leaves v) := by
    by_cases hu : u ∈ K
    · by_cases hv : v ∈ K
      · rcases lt_or_gt_of_ne (G.ne_of_adj h) with huv | hvu
        · exact Or.inl ⟨hu, leaf_iff.mpr ⟨h, Or.inr huv⟩⟩
        · exact Or.inr ⟨hv, leaf_iff.mpr ⟨h.symm, Or.inr hvu⟩⟩
      · exact Or.inl ⟨hu, leaf_iff.mpr ⟨h, Or.inl hv⟩⟩
    · exact Or.inr ⟨(covers u v h).resolve_left hu, leaf_iff.mpr ⟨h.symm, Or.inl hu⟩⟩
  have active {u v : Fin n} (hu : u ∈ K) (hv : v ∈ leaves u) : u ∈ centers :=
    Finset.mem_filter.mpr ⟨hu, ⟨v, hv⟩⟩
  have block_cover : IsBlockCover G F := by
    constructor
    · intro B hB
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hB
      have hLeaves := (Finset.mem_filter.mp hu).2
      refine ⟨?_, ⟨u, Finset.mem_singleton_self u⟩, hLeaves, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro a ha hb
        have hau : a = u := Finset.mem_singleton.mp ha
        subst a
        exact (G.ne_of_adj (leaf_iff.mp hb).1) rfl
      · intro a ha b hb
        have hau : a = u := Finset.mem_singleton.mp ha
        subst a
        exact (leaf_iff.mp hb).1
    · intro u v h
      rcases designated h with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact ⟨block u, Finset.mem_image.mpr ⟨u, active hu hv, rfl⟩,
          Or.inl ⟨Finset.mem_singleton_self u, hv⟩⟩
      · exact ⟨block v, Finset.mem_image.mpr ⟨v, active hv hu, rfl⟩,
          Or.inr ⟨Finset.mem_singleton_self v, hu⟩⟩
  let edges (p : Σ _ : Fin n, Fin n) : Sym2 (Fin n) := s(p.1, p.2)
  have leaves_total : (∑ u ∈ centers, (leaves u).card) ≤ G.edgeFinset.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn edges
    · intro p hp
      have hp' := Finset.mem_sigma.mp hp
      have hadj := (leaf_iff.mp hp'.2).1
      change edges p ∈ G.edgeFinset
      simpa only [edges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hadj
    · intro p hp q hq hpq
      rcases p with ⟨u, v⟩
      rcases q with ⟨a, b⟩
      change s(u, v) = s(a, b) at hpq
      rcases Sym2.eq_iff.mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · have hp' := Finset.mem_sigma.mp hp
        have hq' := Finset.mem_sigma.mp hq
        have hu := (Finset.mem_filter.mp hp'.1).1
        have hv := (Finset.mem_filter.mp hq'.1).1
        have hvu := (leaf_iff.mp hp'.2).2.resolve_left (fun h => h hv)
        have huv := (leaf_iff.mp hq'.2).2.resolve_left (fun h => h hu)
        exact (lt_asymm hvu huv).elim
  have block_injective : Function.Injective block := by
    intro u v h
    have h' : ({u} : Finset (Fin n)) = {v} := congrArg Prod.fst h
    simpa only [Finset.singleton_inj] using h'
  have center_budget : centers.card ≤ K.card := Finset.card_le_card (Finset.filter_subset _ _)
  have center_pos : 0 < centers.card := by
    obtain ⟨u, v, huv⟩ := hedge
    apply Finset.card_pos.mpr
    rcases designated huv with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · exact ⟨u, active hu hv⟩
    · exact ⟨v, active hv hu⟩
  have leaf_cost (u : Fin n) : blockCost (block u) = (leaves u).card := by
    change ({u} : Finset (Fin n)).card + (leaves u).card - 1 = (leaves u).card
    rw [Finset.card_singleton]
    omega
  refine ⟨F, block_cover, ?_⟩
  change (∑ p ∈ centers.image block, blockCost p) + ((centers.image block).card - 1) ≤ D.size
  rw [Finset.card_image_of_injective _ block_injective,
    Finset.sum_image (fun u _ v _ h => block_injective h)]
  simp_rw [leaf_cost]
  omega
