import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import PEqualNP.Defs

-- The wire supports adapt the project's Shannon and Support helpers to arbitrary gate operations.

namespace PEqualNP.Outside.L_meta_4687

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

set_option maxHeartbeats 800000 in
theorem square_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (E : Finset (α × β))
    (endpoints : E ⊆ A ×ˢ B)
    (unique : ∀ a a' : α, a ≠ a' → ∀ b b' : β,
      (a,b) ∈ E → (a',b) ∈ E → (a,b') ∈ E → (a',b') ∈ E → b = b') :
    E.card * E.card ≤ B.card * (A.card * (A.card - 1) + E.card) := by
  let neighbors (b : β) := A.filter (fun a => (a,b) ∈ E)
  have edge_sum : E.card = ∑ b ∈ B, (neighbors b).card := by
    let flatten (p : Σ _ : β, α) : α × β := (p.2, p.1)
    have inj : Function.Injective flatten := by
      rintro ⟨b,a⟩ ⟨d,c⟩ h
      have h₁ : a = c := congrArg Prod.fst h
      have h₂ : b = d := congrArg Prod.snd h
      subst c
      subst d
      rfl
    have image_eq : (B.sigma neighbors).image flatten = E := by
      ext p
      rcases p with ⟨a,b⟩
      constructor
      · intro h
        obtain ⟨⟨d,c⟩, hd, he⟩ := Finset.mem_image.mp h
        have h₁ : c = a := congrArg Prod.fst he
        have h₂ : d = b := congrArg Prod.snd he
        subst c
        subst d
        exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hd).2).2
      · intro h
        obtain ⟨ha,hb⟩ := Finset.mem_product.mp (endpoints h)
        exact Finset.mem_image.mpr ⟨⟨b,a⟩, Finset.mem_sigma.mpr ⟨hb, Finset.mem_filter.mpr ⟨ha,h⟩⟩, rfl⟩
    rw [← image_eq, Finset.card_image_of_injective _ inj, Finset.card_sigma]
  have pairs_bound : (∑ b ∈ B, (neighbors b).offDiag.card) ≤ A.offDiag.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn (fun p : Σ _ : β, α × α => p.2)
    · intro p hp
      have pair := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hp).2
      exact Finset.mem_offDiag.mpr ⟨(Finset.mem_filter.mp pair.1).1,
        (Finset.mem_filter.mp pair.2.1).1, pair.2.2⟩
    · rintro ⟨b,p⟩ hp ⟨d,r⟩ hr eq
      change p = r at eq
      subst r
      have pair₁ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hp).2
      have pair₂ := Finset.mem_offDiag.mp (Finset.mem_sigma.mp hr).2
      have eqbd := unique p.1 p.2 pair₁.2.2 b d
        (Finset.mem_filter.mp pair₁.1).2 (Finset.mem_filter.mp pair₁.2.1).2
        (Finset.mem_filter.mp pair₂.1).2 (Finset.mem_filter.mp pair₂.2.1).2
      subst d
      rfl
  have offDiag_formula (S : Finset α) : S.offDiag.card = S.card * (S.card - 1) := by
    rw [Finset.offDiag_card, Nat.mul_sub_one]
  have sum_of_squares : (∑ b ∈ B, (neighbors b).card ^ 2)
      = (∑ b ∈ B, (neighbors b).offDiag.card) + E.card := by
    rw [edge_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.offDiag_card, pow_two]
    exact (Nat.sub_add_cancel (Nat.le_mul_self _)).symm
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul B
    (r := fun b => (neighbors b).card)
    (f := fun _ => 1)
    (g := fun b => (neighbors b).card ^ 2)
    (fun _ _ => by omega) (fun _ _ => Nat.zero_le _) (by intro b _; simp)
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one] at cauchy
  rw [← edge_sum, pow_two, sum_of_squares] at cauchy
  rw [← offDiag_formula]
  exact cauchy.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right pairs_bound _))

theorem output_support {n : ℕ} (C : Circuit) (fanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) → circuitFun n C x = circuitFun n C y := by
  refine ⟨(suppsFrom C.gates (inputSupps n)).getD C.output ∅, ?_, ?_⟩
  · have h := cnt_suppsFrom C.gates 0 (inputSupps n) fanin cnt_inputs {C.output}
    simpa only [zero_add, Finset.singleton_biUnion, Finset.card_singleton, Circuit.size] using h
  · intro x y h
    exact (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output h

end PEqualNP.Outside.L_meta_4687

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_4687

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_4687 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (1 : ℕ) ≤ x1 →     (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) →       have x7 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x2 × Fin x2) := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : Fin x2 × Fin x2 | x3 x8.1 x8.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x7 fun (x9 : Fin (x2 + x2)) => Decidable.decide (x9 = Fin.castAdd x2 x8.1 ∨ x9 = Fin.natAdd x2 x8.2)) = Bool.true};       have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x8 x9 = Bool.false;       ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),         (∀ x10 ∈ x9.gates, x10.inputs.length ≤ (2 : ℕ)) →           x8 x9 →             x9.size ≤ (4512 : ℕ) →               have x13 : ℕ := (x7 x9).card;               ∃ (x14 : ℕ) (x15 : ℕ), x14 + x15 ≤ x9.size + (1 : ℕ) ∧ x13 ≤ x14 * x15 ∧ x13 * x13 ≤ x15 * (x14 * (x14 - (1 : ℕ)) + x13) ∧ x13 * x13 ≤ x14 * (x15 * (x15 - (1 : ℕ)) + x13) := by
  intro q N I _ hq hlinear
  dsimp only
  intro C hfanin hsound _hsize
  classical
  let left : Fin N → Fin (N + N) := Fin.castAdd N
  let right : Fin N → Fin (N + N) := Fin.natAdd N
  let single (i : Fin (N + N)) (j : Fin (N + N)) : Bool := decide (j = i)
  let pairInput (p l : Fin N) (j : Fin (N + N)) : Bool := decide (j = left p ∨ j = right l)
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ circuitFun (N + N) C (pairInput e.1 e.2) = true)
  change ∃ a b : ℕ, a + b ≤ C.size + 1 ∧ E.card ≤ a * b ∧
    E.card * E.card ≤ b * (a * (a - 1) + E.card) ∧
    E.card * E.card ≤ a * (b * (b - 1) + E.card)
  have separated (p l : Fin N) : left p ≠ right l := by
    intro eq
    have eqval := congrArg Fin.val eq
    change p.val = N + l.val at eqval
    omega
  have left_injective : Function.Injective left := Fin.castAdd_injective N N
  have right_injective : Function.Injective right := by
    intro a b eq
    have eqval := congrArg Fin.val eq
    change N + a.val = N + b.val at eqval
    apply Fin.ext
    omega
  have singleton_rejected (i : Fin (N + N)) : circuitFun (N + N) C (single i) = false := by
    apply hsound (single i)
    · have le_one : Fintype.card {l : Fin N // single i (right l) = true} ≤ 1 := by
        apply Fintype.card_le_one_iff.mpr
        intro a b
        apply Subtype.ext
        apply right_injective
        have ha : right a.val = i := of_decide_eq_true a.property
        have hb : right b.val = i := of_decide_eq_true b.property
        exact ha.trans hb.symm
      exact le_one.trans hq
    · rintro ⟨p, l, _, hp, hl⟩
      exact separated p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
  obtain ⟨S, size_support, stable⟩ := output_support (n := N + N) C hfanin
  let P := Finset.univ.filter (fun p : Fin N => left p ∈ S)
  let L := Finset.univ.filter (fun l : Fin N => right l ∈ S)
  have endpoints : E ⊆ P ×ˢ L := by
    rintro ⟨p,l⟩ he
    have accepted : circuitFun (N + N) C (pairInput p l) = true := (Finset.mem_filter.mp he).2.2
    have point_live : left p ∈ S := by
      by_contra missing
      have agreement := stable (pairInput p l) (single (right l)) (by
        intro i hi
        have different : i ≠ left p := fun eq => missing (eq ▸ hi)
        simp [pairInput, single, different])
      rw [accepted, singleton_rejected] at agreement
      contradiction
    have line_live : right l ∈ S := by
      by_contra missing
      have agreement := stable (pairInput p l) (single (left p)) (by
        intro i hi
        have different : i ≠ right l := fun eq => missing (eq ▸ hi)
        simp [pairInput, single, different])
      rw [accepted, singleton_rejected] at agreement
      contradiction
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, point_live⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, line_live⟩⟩
  have disjoint_halves : Disjoint (P.image left) (L.image right) := by
    apply Finset.disjoint_left.mpr
    intro i hp hl
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨l, _, eq⟩ := Finset.mem_image.mp hl
    exact separated p l eq.symm
  have parts_support : P.image left ∪ L.image right ⊆ S := by
    intro i hi
    rcases Finset.mem_union.mp hi with hp | hl
    · obtain ⟨p, p_mem, eq⟩ := Finset.mem_image.mp hp
      exact eq ▸ (Finset.mem_filter.mp p_mem).2
    · obtain ⟨l, l_mem, eq⟩ := Finset.mem_image.mp hl
      exact eq ▸ (Finset.mem_filter.mp l_mem).2
  have size_bound : P.card + L.card ≤ C.size + 1 := by
    have card_bound := (Finset.card_le_card parts_support).trans size_support
    rwa [Finset.card_union_of_disjoint disjoint_halves,
      Finset.card_image_of_injective _ left_injective,
      Finset.card_image_of_injective _ right_injective] at card_bound
  have product_bound : E.card ≤ P.card * L.card := by
    simpa only [Finset.card_product] using Finset.card_le_card endpoints
  have incident {p l : Fin N} (h : (p,l) ∈ E) : I p l := (Finset.mem_filter.mp h).2.1
  have line_unique (p p' : Fin N) (hne : p ≠ p') (l l' : Fin N)
      (ha : (p,l) ∈ E) (hb : (p',l) ∈ E) (hc : (p,l') ∈ E) (hd : (p',l') ∈ E) :
      l = l' := by
    obtain ⟨w, _, hw⟩ := hlinear p p' hne
    exact (hw l ⟨incident ha, incident hb⟩).trans (hw l' ⟨incident hc, incident hd⟩).symm
  have line_bound := square_bound P L E endpoints line_unique
  let flipped := E.image (Prod.swap : Fin N × Fin N → Fin N × Fin N)
  have flip_mem {p l : Fin N} : (l,p) ∈ flipped ↔ (p,l) ∈ E := by
    constructor
    · intro h
      obtain ⟨e, he, eq⟩ := Finset.mem_image.mp h
      have swap_pair : (p,l).swap = (l,p) := rfl
      have e_eq : e = (p,l) := Prod.swap_injective (eq.trans swap_pair.symm)
      exact e_eq ▸ he
    · intro h
      exact Finset.mem_image.mpr ⟨(p,l), h, rfl⟩
  have flipped_card : flipped.card = E.card := by
    apply Finset.card_image_of_injective
    intro a b eq
    exact Prod.swap_injective eq
  have flipped_ends : flipped ⊆ L ×ˢ P := by
    rintro ⟨l,p⟩ h
    obtain ⟨hp, hl⟩ := Finset.mem_product.mp (endpoints (flip_mem.mp h))
    exact Finset.mem_product.mpr ⟨hl,hp⟩
  have point_unique (l l' : Fin N) (hne : l ≠ l') (p p' : Fin N)
      (ha : (l,p) ∈ flipped) (hb : (l',p) ∈ flipped)
      (hc : (l,p') ∈ flipped) (hd : (l',p') ∈ flipped) : p = p' := by
    by_contra unequal
    exact hne (line_unique p p' unequal l l'
      (flip_mem.mp ha) (flip_mem.mp hc) (flip_mem.mp hb) (flip_mem.mp hd))
  have point_bound := square_bound L P flipped flipped_ends point_unique
  rw [flipped_card] at point_bound
  exact ⟨P.card, L.card, size_bound, product_bound, line_bound, point_bound⟩
