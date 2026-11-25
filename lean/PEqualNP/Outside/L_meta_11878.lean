import PEqualNP.Defs

-- The generic bounded-circuit machinery adapts k-sandhu's L_meta_11064.
-- The two omitted variables leave two triangles sharing one vertex.
-- The circuit, test rows and finite checks below are for this graph.

namespace PEqualNP.Outside.L_meta_11878

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

end Generic

abbrev BF := (Fin 7 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 7) : BF := fun x => x i

def gM (k a b : ℕ) : ℕ :=
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def gN (k : Fin 4) (a b : ℕ) : ℕ := gM k.val a b

theorem gN_testBit (k : Fin 4) (a b i : ℕ) :
    (gN k a b).testBit i = zeroGate k (a.testBit i) (b.testBit i) := by
  fin_cases k <;>
    simp [gN, gM, zeroGate, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem gN_zero_left (k : Fin 4) (b : ℕ) : gN k 0 b = 0 ∨ gN k 0 b = b := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_right (k : Fin 4) (a : ℕ) : gN k a 0 = 0 ∨ gN k a 0 = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_self (k : Fin 4) (a : ℕ) : gN k a a = 0 ∨ gN k a a = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_lt (k : Fin 4) (a b : ℕ) (ha : a < 32768) (hb : b < 32768) : gN k a b < 32768 := by
  apply Nat.lt_pow_two_of_testBit (n := 15)
  intro i hi
  have hp : (32768 : ℕ) ≤ 2 ^ i :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi)
  rw [gN_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]
  fin_cases k <;> rfl

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_gate {ρ : Type} (k : Fin 4) (a b : ρ → Bool) (l : List ρ) :
    enc (fun r => zeroGate k (a r) (b r)) l = gN k (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [gN_testBit, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    fin_cases k <;> rfl

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 7 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := enc_gate k a b l

theorem TRN_det {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i j : ℕ) :
    (∀ t ∈ ws, t.testBit i = t.testBit j) → y.testBit i = y.testBit j := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = t.testBit j) →
    y.testBit i = y.testBit j) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, gN_testBit, hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

theorem TRN_zp {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i : ℕ) :
    (∀ t ∈ ws, t.testBit i = false) → y.testBit i = false := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = false) →
    y.testBit i = false) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, hz a (by simp), hz b (by simp)]
      fin_cases k <;> rfl
    · exact hz t (by simp [ht])

def sg (p t : ℕ) : ℕ := if t.testBit p then t ^^^ 32767 else t

def covB (f : ℕ → ℕ) (ws : List ℕ) : Bool :=
  ws.foldl (fun acc t => acc ||| f t) 0 &&& 31236 == 31236

def rejects : List ℕ := [0, 1, 3, 4, 5, 6, 7, 8, 10]

def cov (ws : List ℕ) : Bool :=
  covB id ws && rejects.all (fun p => covB (sg p) ws)

theorem fold_bit (f : ℕ → ℕ) (i : ℕ) : ∀ (ws : List ℕ) (a : ℕ),
    (ws.foldl (fun acc t => acc ||| f t) a).testBit i =
      (a.testBit i || ws.any fun t => (f t).testBit i)
  | [], a => by simp
  | t :: ws, a => by
    rw [List.foldl_cons, fold_bit f i ws, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem covB_iff (f : ℕ → ℕ) (ws : List ℕ) :
    covB f ws = true ↔
      ∀ i, (31236 : ℕ).testBit i = true → ∃ t ∈ ws, (f t).testBit i = true := by
  unfold covB
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    have h1 := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or,
      List.any_eq_true] at h1
    exact h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : (31236 : ℕ).testBit i
    · simp
    · rw [Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or, List.any_eq_true]
      exact h i hi

theorem sg_bit (p t i : ℕ) (hi : (31236 : ℕ).testBit i = true) :
    (sg p t).testBit i = (t.testBit i != t.testBit p) := by
  have h32767 : (32767 : ℕ).testBit i = true := by
    have hlt : i < 15 := by
      by_contra hc
      have h2 : (31236 : ℕ) < 2 ^ i :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hc))
      rw [Nat.testBit_lt_two_pow h2] at hi
      exact Bool.noConfusion hi
    interval_cases i <;> rfl
  have e : (sg p t).testBit i =
      if t.testBit p = true then (t.testBit i ^^ true) else t.testBit i := by
    unfold sg
    split_ifs with h
    · rw [Nat.testBit_xor, h32767]
    · rfl
  rw [e]
  cases t.testBit i <;> cases t.testBit p <;> rfl

theorem TRN_cov {C : Fin 4 → ℕ → ℕ → Prop} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [31236] s ws) : cov ws = true := by
  have hd := TRN_det h
  have hz := TRN_zp h
  have k1 : ∀ i, (31236 : ℕ).testBit i = true → ∃ t ∈ ws, (id t).testBit i = true := by
    intro i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = false := by
      intro t ht
      by_contra h2
      exact hc ⟨t, ht, by simpa using h2⟩
    rw [hz i h1] at hi
    exact Bool.noConfusion hi
  have k2 : ∀ p, (31236 : ℕ).testBit p = false → ∀ i, (31236 : ℕ).testBit i = true →
      ∃ t ∈ ws, (sg p t).testBit i = true := by
    intro p hp i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = t.testBit p := by
      intro t ht
      by_contra h2
      refine hc ⟨t, ht, ?_⟩
      rw [sg_bit p t i hi]
      simpa using h2
    rw [hd i p h1, hp] at hi
    exact Bool.noConfusion hi
  rw [cov, Bool.and_eq_true]
  refine ⟨(covB_iff _ _).2 k1, List.all_eq_true.2 ?_⟩
  intro p hp
  have negative : ∀ p ∈ rejects, (31236 : ℕ).testBit p = false := by decide
  exact (covB_iff _ _).2 (k2 p (negative p hp))

def tryG (g a b : ℕ) (f : ℕ → Bool) : Bool :=
  match g with
  | 0 => false
  | g' + 1 => g' + 1 != a && g' + 1 != b && f (g' + 1)

theorem tryG_iff (g a b : ℕ) (f : ℕ → Bool) :
    tryG g a b f = true ↔ g ≠ 0 ∧ g ≠ a ∧ g ≠ b ∧ f g = true := by
  cases g <;> simp [tryG, and_assoc]

def search : ℕ → List ℕ → Bool
  | 0, ws => decide (ws = [31236])
  | s + 1, ws =>
    decide (ws.length ≤ s + 2) && cov ws &&
      ws.dedup.any fun a => ws.dedup.any fun b => decide (a < b) &&
        [0, 1, 2, 3].any fun k =>
          tryG (gM k a b) a b fun g =>
            (List.range (s + 3 - ws.length)).any fun u =>
              search s (List.replicate (u + 1) g ++ (ws.erase a).erase b)

theorem search_succ (s : ℕ) (ws : List ℕ) :
    search (s + 1) ws = true ↔ ws.length ≤ s + 2 ∧ cov ws = true ∧
      ∃ a ∈ ws, ∃ b ∈ ws, a < b ∧ ∃ k, k < 4 ∧ gM k a b ≠ 0 ∧ gM k a b ≠ a ∧ gM k a b ≠ b ∧
        ∃ u, u < s + 3 - ws.length ∧
          search s (List.replicate (u + 1) (gM k a b) ++ (ws.erase a).erase b) = true := by
  simp only [search, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_dedup,
    tryG_iff, List.mem_range, and_assoc]
  constructor
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

theorem cov_perm {xs zs : List ℕ} (hp : xs.Perm zs) (h : cov xs = true) : cov zs = true := by
  have transfer (f : ℕ → ℕ) (hf : covB f xs = true) : covB f zs = true := by
    apply (covB_iff f zs).2
    intro i hi
    obtain ⟨t, ht, value⟩ := (covB_iff f xs).1 hf i hi
    exact ⟨t, hp.mem_iff.1 ht, value⟩
  simp only [cov, Bool.and_eq_true] at h ⊢
  obtain ⟨covered, separated⟩ := h
  exact ⟨transfer id covered, List.all_eq_true.2 fun p hp' =>
    transfer (sg p) ((List.all_eq_true.1 separated) p hp')⟩

theorem search_perm : ∀ (s : ℕ) (xs zs : List ℕ), xs.Perm zs → search s xs = true →
    search s zs = true
  | 0, xs, zs, hp, h => by
    simp only [search, decide_eq_true_eq] at h ⊢
    subst h
    exact List.perm_singleton.1 hp.symm
  | s + 1, xs, zs, hp, h => by
    rw [search_succ] at h ⊢
    obtain ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3, h4, h5, u, hu, h6⟩ := h
    refine ⟨hp.length_eq ▸ h1, cov_perm hp h2, a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, hab, k,
      hk, h3, h4, h5, u, hp.length_eq ▸ hu, ?_⟩
    exact search_perm s _ _ (List.Perm.append_left _ ((hp.erase a).erase b)) h6

theorem gM_swap (k a b : ℕ) (hk : k < 4) :
    ∃ k', k' < 4 ∧ gM k' b a = gM k a b := by
  interval_cases k
  · exact ⟨0, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨1, by omega, by simp [gM, Nat.or_comm]⟩
  · exact ⟨3, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨2, by omega, by simp [gM, Nat.and_comm]⟩

abbrev NR (s : ℕ) (ws : List ℕ) : Prop :=
  TR gN (strictC gN 0 (fun _ => True) fun t => t < 32768) [31236] s ws

theorem run_search {s : ℕ} {ws : List ℕ} (h : NR s ws) : search s ws = true := by
  refine TR.ind (P := fun s ws => search s ws = true) h (by simp [search]) ?_ ?_
  · intro s xs zs hp _ ih
    exact search_perm s xs zs hp ih
  · intro s a b r k u hc hr ih
    have hrun := TR.step k u hc hr
    obtain ⟨-, -, -, hab, hga, hgb, hgz⟩ := hc
    have hlen := TR.len hr
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen
    rw [search_succ]
    refine ⟨by have := TR.len hrun; simpa using this, TRN_cov hrun, ?_⟩
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨a, by simp, b, by simp, hlt, k.val, k.isLt, hgz, hga, hgb, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · have : ((a :: b :: r).erase a).erase b = r := by simp
        rw [this]
        exact ih
    · obtain ⟨k', hk', he⟩ := gM_swap k.val a b k.isLt
      have he' : gM k' b a = gN k a b := he
      refine ⟨b, by simp, a, by simp, hlt, k', hk', by rw [he']; exact hgz, by rw [he']; exact hgb,
        by rw [he']; exact hga, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [he']
        have : ((a :: b :: r).erase b).erase a = r := by
          rw [List.erase_cons_tail (by simpa using hab), List.erase_cons_head,
            List.erase_cons_head]
        rw [this]
        exact ih

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

def bperm (rho : List ℕ) (t : ℕ) : ℕ := enc (fun i => t.testBit i) rho

theorem bperm_gN (rho : List ℕ) (k : Fin 4) (a b : ℕ) :
    bperm rho (gN k a b) = gN k (bperm rho a) (bperm rho b) := by
  unfold bperm
  rw [← enc_gate]
  congr 1
  funext i
  exact gN_testBit k a b i

theorem NR_perm (rho : List ℕ) (hlen : rho.length = 15)
    (hinv : ∀ t, t < 32768 → bperm rho (bperm rho t) = t) (h0 : bperm rho 0 = 0)
    (h31236 : bperm rho 31236 = 31236) {s : ℕ} {ws : List ℕ} (h : NR s ws) :
    NR s (ws.map (bperm rho)) := by
  have hlt : ∀ t, bperm rho t < 32768 := fun t => by
    have := enc_lt (fun i => t.testBit i) rho
    rw [hlen] at this
    exact this
  have hinj : ∀ a b, a < 32768 → b < 32768 → bperm rho a = bperm rho b → a = b := by
    intro a b ha hb he
    rw [← hinv a ha, ← hinv b hb, he]
  have h1 := TR.map (C' := strictC gN 0 (fun _ => True) fun t => t < 32768) (bperm rho)
    (bperm_gN rho) (by
      rintro k a b ⟨hk, ha, hb, hab, hga, hgb, hgz⟩
      have hg := gN_lt k a b ha hb
      refine ⟨hk, hlt a, hlt b, fun e => hab (hinj a b ha hb e), ?_, ?_, ?_⟩
      · rw [← bperm_gN]; exact fun e => hga (hinj _ _ hg ha e)
      · rw [← bperm_gN]; exact fun e => hgb (hinj _ _ hg hb e)
      · rw [← bperm_gN, ← h0]; exact fun e => hgz (hinj _ _ hg (by norm_num) e)) h
  simp only [List.map_cons, List.map_nil, h31236] at h1
  exact h1

theorem bperm_bit (rho : List ℕ) (t i : ℕ) (hi : i < rho.length) :
    (bperm rho t).testBit i = t.testBit (rho.getD i 0) := by
  rw [bperm, enc_testBit]
  simp [List.getD, hi]

theorem bperm_involution {rho : List ℕ} (len : rho.length = 15)
    (permuted : ∀ i < 15, rho.getD i 0 < 15 ∧ rho.getD (rho.getD i 0) 0 = i)
    (t : ℕ) (short : t < 32768) : bperm rho (bperm rho t) = t := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 15
  · have step := permuted i hi
    rw [bperm_bit rho _ i (by simpa [len] using hi), bperm_bit rho _ _ (by simpa [len] using step.1), step.2]
  · have hbig : (32768 : ℕ) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) (show 15 ≤ i by omega)
    have hm : bperm rho (bperm rho t) < 32768 := by
      simpa [bperm, len] using enc_lt (fun i => (bperm rho t).testBit i) rho
    rw [Nat.testBit_lt_two_pow (hm.trans_le hbig), Nat.testBit_lt_two_pow (short.trans_le hbig)]

def pins : List ℕ := [2197, 4390, 8760, 17344, 31744]

def mk (a b c d e : ℕ) : List ℕ :=
  List.replicate a 2197 ++
  List.replicate b 4390 ++
  List.replicate c 8760 ++
  List.replicate d 17344 ++
  List.replicate e 31744

def rowsFirst : List ℕ := [1, 0, 2, 3, 5, 4, 6, 8, 7, 9, 10, 12, 11, 13, 14]

theorem swapFirst {s a b c d e : ℕ} (h : NR s (mk a b c d e)) :
    NR s (mk b a c d e) := by
  have mapped := NR_perm rowsFirst (by decide)
    (bperm_involution (by decide) (by decide)) (by decide) (by decide) h
  apply TR.perm _ mapped
  rw [List.perm_iff_count]
  intro x
  simp only [mk, List.map_append, List.map_replicate, List.count_append, List.count_replicate,
    (show bperm rowsFirst 2197 = 4390 from rfl), (show bperm rowsFirst 4390 = 2197 from rfl), (show bperm rowsFirst 8760 = 8760 from rfl), (show bperm rowsFirst 17344 = 17344 from rfl), (show bperm rowsFirst 31744 = 31744 from rfl)]
  omega

def rowsSecond : List ℕ := [0, 1, 2, 6, 7, 8, 3, 4, 5, 9, 10, 11, 12, 14, 13]

theorem swapSecond {s a b c d e : ℕ} (h : NR s (mk a b c d e)) :
    NR s (mk a b d c e) := by
  have mapped := NR_perm rowsSecond (by decide)
    (bperm_involution (by decide) (by decide)) (by decide) (by decide) h
  apply TR.perm _ mapped
  rw [List.perm_iff_count]
  intro x
  simp only [mk, List.map_append, List.map_replicate, List.count_append, List.count_replicate,
    (show bperm rowsSecond 2197 = 2197 from rfl), (show bperm rowsSecond 4390 = 4390 from rfl), (show bperm rowsSecond 8760 = 17344 from rfl), (show bperm rowsSecond 17344 = 8760 from rfl), (show bperm rowsSecond 31744 = 31744 from rfl)]
  omega

def searchCore (s : ℕ) : Bool :=
  (List.range (s + 2 - 5)).all fun a =>
    (List.range (s + 2 - 5 - a)).all fun b =>
      (List.range (s + 2 - 5 - a - b)).all fun c =>
        (List.range (s + 2 - 5 - a - b - c)).all fun d =>
          (List.range (s + 2 - 5 - a - b - c - d)).all fun e =>
            if a ≤ b ∧ c ≤ d then !search s (mk (a + 1) (b + 1) (c + 1) (d + 1) (e + 1)) else true

def candidateChildren (s : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if ws.length ≤ s + 2 ∧ cov ws = true then
    ws.dedup.flatMap fun a => ws.dedup.flatMap fun b =>
      if a < b then [0, 1, 2, 3].flatMap fun k =>
        let g := gM k a b
        if g ≠ 0 ∧ g ≠ a ∧ g ≠ b then
          (List.range (s + 3 - ws.length)).filterMap fun u =>
            let child := List.replicate (u + 1) g ++ (ws.erase a).erase b
            if cov child = true then some child else none
        else []
      else []
  else []

theorem search_child {s : ℕ} (hs : 0 < s) (ws : List ℕ) (found : search (s + 1) ws = true) :
    ∃ child ∈ candidateChildren s ws, search s child = true := by
  obtain ⟨len, cover, a, ha, b, hb, hab, k, hk, nonzero, neA, neB, u, hu, live⟩ :=
    (search_succ s ws).1 found
  let child := List.replicate (u + 1) (gM k a b) ++ (ws.erase a).erase b
  have good : cov child = true := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
    exact ((search_succ r child).1 live).2.1
  refine ⟨child, ?_, live⟩
  unfold candidateChildren
  rw [ite_eq_left ⟨len, cover⟩]
  apply List.mem_flatMap.2
  refine ⟨a, List.mem_dedup.2 ha, ?_⟩
  apply List.mem_flatMap.2
  refine ⟨b, List.mem_dedup.2 hb, ?_⟩
  rw [ite_eq_left hab]
  apply List.mem_flatMap.2
  refine ⟨k, ?_, ?_⟩
  · interval_cases k <;> decide
  rw [ite_eq_left ⟨nonzero, neA, neB⟩]
  exact List.mem_filterMap.2 ⟨u, List.mem_range.2 hu, by simp [child, good]⟩

theorem close_step {s : ℕ} (hs : 0 < s) (ws : List ℕ)
    (all : (candidateChildren s ws).all (fun child => !search s child) = true) :
    search (s + 1) ws = false := by
  cases h : search (s + 1) ws
  · rfl
  · obtain ⟨child, mem, found⟩ := search_child hs ws h
    have absent := List.all_eq_true.mp all child mem
    simp [found] at absent

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem searchCore4 : searchCore 4 = true := by
  have case11111 : search 4 (mk 1 1 1 1 1) = false := by decide +kernel
  simp only [searchCore, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
    (show List.range 1 = [0] from rfl),
    List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
    true_and, ite_true,
    case11111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem searchCore5 : searchCore 5 = true := by
  have case11111 : search 5 (mk 1 1 1 1 1) = false := by decide +kernel
  have case11112 : search 5 (mk 1 1 1 1 2) = false := by decide +kernel
  have case11121 : search 5 (mk 1 1 1 2 1) = false := by decide +kernel
  have case12111 : search 5 (mk 1 2 1 1 1) = false := by decide +kernel
  simp only [searchCore, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
    (show List.range 1 = [0] from rfl),
    (show List.range 2 = [0, 1] from rfl),
    List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
    true_and, false_and, ite_true, ite_false,
    case11111, case11112, case11121, case12111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem searchCore6 : searchCore 6 = true := by
  have case11111 : search 6 (mk 1 1 1 1 1) = false := by decide +kernel
  have case11112 : search 6 (mk 1 1 1 1 2) = false := by decide +kernel
  have case11113 : search 6 (mk 1 1 1 1 3) = false := by decide +kernel
  have case11121 : search 6 (mk 1 1 1 2 1) = false := by decide +kernel
  have case11122 : search 6 (mk 1 1 1 2 2) = false := by decide +kernel
  have case11131 : search 6 (mk 1 1 1 3 1) = false := by decide +kernel
  have case11221 : search 6 (mk 1 1 2 2 1) = false := by decide +kernel
  have case12111 : search 6 (mk 1 2 1 1 1) = false := by decide +kernel
  have case12112 : search 6 (mk 1 2 1 1 2) = false := by decide +kernel
  have case12121 : search 6 (mk 1 2 1 2 1) = false := by decide +kernel
  have case13111 : search 6 (mk 1 3 1 1 1) = false := by decide +kernel
  have case22111 : search 6 (mk 2 2 1 1 1) = false := by decide +kernel
  simp only [searchCore, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
    (show List.range 1 = [0] from rfl),
    (show List.range 2 = [0, 1] from rfl),
    (show List.range 3 = [0, 1, 2] from rfl),
    List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
    true_and, false_and, ite_true, ite_false,
    case11111, case11112, case11113, case11121, case11122, case11131, case11221, case12111, case12112, case12121, case13111, case22111]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem searchCore7 : searchCore 7 = true := by
  have case11111 : search 7 (mk 1 1 1 1 1) = false := by decide +kernel
  have case11112 : search 7 (mk 1 1 1 1 2) = false := by decide +kernel
  have case11113 : search 7 (mk 1 1 1 1 3) = false := by decide +kernel
  have case11114 : search 7 (mk 1 1 1 1 4) = false := by decide +kernel
  have case11121 : search 7 (mk 1 1 1 2 1) = false := by decide +kernel
  have case11122 : search 7 (mk 1 1 1 2 2) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 1 1 2 2) = [
      [19413, 4390, 8760, 17344, 31744, 31744],
      [19413, 19413, 4390, 8760, 17344, 31744, 31744],
      [2069, 4390, 8760, 17344, 31744, 31744],
      [2069, 2069, 4390, 8760, 17344, 31744, 31744],
      [21478, 2197, 8760, 17344, 31744, 31744],
      [21478, 21478, 2197, 8760, 17344, 31744, 31744],
      [4134, 2197, 8760, 17344, 31744, 31744],
      [4134, 4134, 2197, 8760, 17344, 31744, 31744],
      [16384, 2197, 4390, 8760, 17344, 31744],
      [16384, 16384, 2197, 4390, 8760, 17344, 31744],
      [32704, 2197, 4390, 8760, 17344, 31744],
      [32704, 32704, 2197, 4390, 8760, 17344, 31744],
      [960, 2197, 4390, 8760, 17344, 31744],
      [960, 960, 2197, 4390, 8760, 17344, 31744],
      [15360, 2197, 4390, 8760, 17344, 31744],
      [15360, 15360, 2197, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [19413, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked1 : search 6 [19413, 19413, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked2 : search 6 [2069, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked3 : search 6 [2069, 2069, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked4 : search 6 [21478, 2197, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked5 : search 6 [21478, 21478, 2197, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked6 : search 6 [4134, 2197, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked7 : search 6 [4134, 4134, 2197, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked8 : search 6 [16384, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [16384, 16384, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [32704, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [32704, 32704, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [960, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [960, 960, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [15360, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [15360, 15360, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15]
  have case11123 : search 7 (mk 1 1 1 2 3) = false := by decide +kernel
  have case11131 : search 7 (mk 1 1 1 3 1) = false := by decide +kernel
  have case11132 : search 7 (mk 1 1 1 3 2) = false := by decide +kernel
  have case11141 : search 7 (mk 1 1 1 4 1) = false := by decide +kernel
  have case11221 : search 7 (mk 1 1 2 2 1) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 1 2 2 1) = [
      [10941, 4390, 8760, 17344, 17344, 31744],
      [10941, 10941, 4390, 8760, 17344, 17344, 31744],
      [2181, 4390, 8760, 17344, 17344, 31744],
      [2181, 2181, 4390, 8760, 17344, 17344, 31744],
      [19413, 4390, 8760, 8760, 17344, 31744],
      [19413, 19413, 4390, 8760, 8760, 17344, 31744],
      [2069, 4390, 8760, 8760, 17344, 31744],
      [2069, 2069, 4390, 8760, 8760, 17344, 31744],
      [13118, 2197, 8760, 17344, 17344, 31744],
      [13118, 13118, 2197, 8760, 17344, 17344, 31744],
      [4358, 2197, 8760, 17344, 17344, 31744],
      [4358, 4358, 2197, 8760, 17344, 17344, 31744],
      [21478, 2197, 8760, 8760, 17344, 31744],
      [21478, 21478, 2197, 8760, 8760, 17344, 31744],
      [4134, 2197, 8760, 8760, 17344, 31744],
      [4134, 4134, 2197, 8760, 8760, 17344, 31744],
      [512, 2197, 4390, 8760, 17344, 31744],
      [512, 512, 2197, 4390, 8760, 17344, 31744],
      [25592, 2197, 4390, 8760, 17344, 31744],
      [25592, 25592, 2197, 4390, 8760, 17344, 31744],
      [8248, 2197, 4390, 8760, 17344, 31744],
      [8248, 8248, 2197, 4390, 8760, 17344, 31744],
      [16832, 2197, 4390, 8760, 17344, 31744],
      [16832, 16832, 2197, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [10941, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked1 : search 6 [10941, 10941, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked2 : search 6 [2181, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked3 : search 6 [2181, 2181, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked4 : search 6 [19413, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked5 : search 6 [19413, 19413, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked6 : search 6 [2069, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked7 : search 6 [2069, 2069, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked8 : search 6 [13118, 2197, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [13118, 13118, 2197, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [4358, 2197, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [4358, 4358, 2197, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [21478, 2197, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [21478, 21478, 2197, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [4134, 2197, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [4134, 4134, 2197, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked16 : search 6 [512, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked17 : search 6 [512, 512, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked18 : search 6 [25592, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked19 : search 6 [25592, 25592, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked20 : search 6 [8248, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked21 : search 6 [8248, 8248, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked22 : search 6 [16832, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked23 : search 6 [16832, 16832, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19, checked20, checked21, checked22, checked23]
  have case11222 : search 7 (mk 1 1 2 2 2) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 1 2 2 2) = [
      [10941, 4390, 8760, 17344, 17344, 31744, 31744],
      [2181, 4390, 8760, 17344, 17344, 31744, 31744],
      [19413, 4390, 8760, 8760, 17344, 31744, 31744],
      [2069, 4390, 8760, 8760, 17344, 31744, 31744],
      [13118, 2197, 8760, 17344, 17344, 31744, 31744],
      [4358, 2197, 8760, 17344, 17344, 31744, 31744],
      [21478, 2197, 8760, 8760, 17344, 31744, 31744],
      [4134, 2197, 8760, 8760, 17344, 31744, 31744],
      [512, 2197, 4390, 8760, 17344, 31744, 31744],
      [25592, 2197, 4390, 8760, 17344, 31744, 31744],
      [8248, 2197, 4390, 8760, 17344, 31744, 31744],
      [16832, 2197, 4390, 8760, 17344, 31744, 31744],
      [8192, 2197, 4390, 8760, 17344, 17344, 31744],
      [32312, 2197, 4390, 8760, 17344, 17344, 31744],
      [568, 2197, 4390, 8760, 17344, 17344, 31744],
      [23552, 2197, 4390, 8760, 17344, 17344, 31744],
      [16384, 2197, 4390, 8760, 8760, 17344, 31744],
      [32704, 2197, 4390, 8760, 8760, 17344, 31744],
      [960, 2197, 4390, 8760, 8760, 17344, 31744],
      [15360, 2197, 4390, 8760, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [10941, 4390, 8760, 17344, 17344, 31744, 31744] = false := by decide +kernel
    have checked1 : search 6 [2181, 4390, 8760, 17344, 17344, 31744, 31744] = false := by decide +kernel
    have checked2 : search 6 [19413, 4390, 8760, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked3 : search 6 [2069, 4390, 8760, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked4 : search 6 [13118, 2197, 8760, 17344, 17344, 31744, 31744] = false := by decide +kernel
    have checked5 : search 6 [4358, 2197, 8760, 17344, 17344, 31744, 31744] = false := by decide +kernel
    have checked6 : search 6 [21478, 2197, 8760, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked7 : search 6 [4134, 2197, 8760, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked8 : search 6 [512, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked9 : search 6 [25592, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked10 : search 6 [8248, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked11 : search 6 [16832, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked12 : search 6 [8192, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [32312, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [568, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [23552, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked16 : search 6 [16384, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked17 : search 6 [32704, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked18 : search 6 [960, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked19 : search 6 [15360, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19]
  have case11231 : search 7 (mk 1 1 2 3 1) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 1 2 3 1) = [
      [10941, 4390, 8760, 17344, 17344, 17344, 31744],
      [2181, 4390, 8760, 17344, 17344, 17344, 31744],
      [19413, 4390, 8760, 8760, 17344, 17344, 31744],
      [2069, 4390, 8760, 8760, 17344, 17344, 31744],
      [13118, 2197, 8760, 17344, 17344, 17344, 31744],
      [4358, 2197, 8760, 17344, 17344, 17344, 31744],
      [21478, 2197, 8760, 8760, 17344, 17344, 31744],
      [4134, 2197, 8760, 8760, 17344, 17344, 31744],
      [512, 2197, 4390, 8760, 17344, 17344, 31744],
      [25592, 2197, 4390, 8760, 17344, 17344, 31744],
      [8248, 2197, 4390, 8760, 17344, 17344, 31744],
      [16832, 2197, 4390, 8760, 17344, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [10941, 4390, 8760, 17344, 17344, 17344, 31744] = false := by decide +kernel
    have checked1 : search 6 [2181, 4390, 8760, 17344, 17344, 17344, 31744] = false := by decide +kernel
    have checked2 : search 6 [19413, 4390, 8760, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked3 : search 6 [2069, 4390, 8760, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked4 : search 6 [13118, 2197, 8760, 17344, 17344, 17344, 31744] = false := by decide +kernel
    have checked5 : search 6 [4358, 2197, 8760, 17344, 17344, 17344, 31744] = false := by decide +kernel
    have checked6 : search 6 [21478, 2197, 8760, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked7 : search 6 [4134, 2197, 8760, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked8 : search 6 [512, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [25592, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [8248, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [16832, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11]
  have case12111 : search 7 (mk 1 2 1 1 1) = false := by decide +kernel
  have case12112 : search 7 (mk 1 2 1 1 2) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 2 1 1 2) = [
      [13118, 2197, 4390, 17344, 31744, 31744],
      [13118, 13118, 2197, 4390, 17344, 31744, 31744],
      [8728, 2197, 4390, 17344, 31744, 31744],
      [8728, 8728, 2197, 4390, 17344, 31744, 31744],
      [21478, 2197, 4390, 8760, 31744, 31744],
      [21478, 21478, 2197, 4390, 8760, 31744, 31744],
      [17088, 2197, 4390, 8760, 31744, 31744],
      [17088, 17088, 2197, 4390, 8760, 31744, 31744],
      [4096, 2197, 4390, 8760, 17344, 31744],
      [4096, 4096, 2197, 4390, 8760, 17344, 31744],
      [32038, 2197, 4390, 8760, 17344, 31744],
      [32038, 32038, 2197, 4390, 8760, 17344, 31744],
      [294, 2197, 4390, 8760, 17344, 31744],
      [294, 294, 2197, 4390, 8760, 17344, 31744],
      [27648, 2197, 4390, 8760, 17344, 31744],
      [27648, 27648, 2197, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [13118, 2197, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked1 : search 6 [13118, 13118, 2197, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked2 : search 6 [8728, 2197, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked3 : search 6 [8728, 8728, 2197, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked4 : search 6 [21478, 2197, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked5 : search 6 [21478, 21478, 2197, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked6 : search 6 [17088, 2197, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked7 : search 6 [17088, 17088, 2197, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked8 : search 6 [4096, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [4096, 4096, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [32038, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [32038, 32038, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [294, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [294, 294, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [27648, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [27648, 27648, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15]
  have case12113 : search 7 (mk 1 2 1 1 3) = false := by decide +kernel
  have case12121 : search 7 (mk 1 2 1 2 1) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 2 1 2 1) = [
      [19413, 4390, 4390, 8760, 17344, 31744],
      [19413, 19413, 4390, 4390, 8760, 17344, 31744],
      [2069, 4390, 4390, 8760, 17344, 31744],
      [2069, 2069, 4390, 4390, 8760, 17344, 31744],
      [13118, 2197, 4390, 17344, 17344, 31744],
      [13118, 13118, 2197, 4390, 17344, 17344, 31744],
      [8728, 2197, 4390, 17344, 17344, 31744],
      [8728, 8728, 2197, 4390, 17344, 17344, 31744],
      [256, 2197, 4390, 8760, 17344, 31744],
      [256, 256, 2197, 4390, 8760, 17344, 31744],
      [21478, 2197, 4390, 8760, 17344, 31744],
      [21478, 21478, 2197, 4390, 8760, 17344, 31744],
      [4134, 2197, 4390, 8760, 17344, 31744],
      [4134, 4134, 2197, 4390, 8760, 17344, 31744],
      [17088, 2197, 4390, 8760, 17344, 31744],
      [17088, 17088, 2197, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [19413, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked1 : search 6 [19413, 19413, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked2 : search 6 [2069, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked3 : search 6 [2069, 2069, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked4 : search 6 [13118, 2197, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked5 : search 6 [13118, 13118, 2197, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked6 : search 6 [8728, 2197, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked7 : search 6 [8728, 8728, 2197, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked8 : search 6 [256, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [256, 256, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [21478, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [21478, 21478, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [4134, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [4134, 4134, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [17088, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [17088, 17088, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15]
  have case12122 : search 7 (mk 1 2 1 2 2) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 2 1 2 2) = [
      [19413, 4390, 4390, 8760, 17344, 31744, 31744],
      [2069, 4390, 4390, 8760, 17344, 31744, 31744],
      [13118, 2197, 4390, 17344, 17344, 31744, 31744],
      [8728, 2197, 4390, 17344, 17344, 31744, 31744],
      [256, 2197, 4390, 8760, 17344, 31744, 31744],
      [21478, 2197, 4390, 8760, 17344, 31744, 31744],
      [4134, 2197, 4390, 8760, 17344, 31744, 31744],
      [17088, 2197, 4390, 8760, 17344, 31744, 31744],
      [4096, 2197, 4390, 8760, 17344, 17344, 31744],
      [32038, 2197, 4390, 8760, 17344, 17344, 31744],
      [294, 2197, 4390, 8760, 17344, 17344, 31744],
      [27648, 2197, 4390, 8760, 17344, 17344, 31744],
      [16384, 2197, 4390, 4390, 8760, 17344, 31744],
      [32704, 2197, 4390, 4390, 8760, 17344, 31744],
      [960, 2197, 4390, 4390, 8760, 17344, 31744],
      [15360, 2197, 4390, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [19413, 4390, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked1 : search 6 [2069, 4390, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked2 : search 6 [13118, 2197, 4390, 17344, 17344, 31744, 31744] = false := by decide +kernel
    have checked3 : search 6 [8728, 2197, 4390, 17344, 17344, 31744, 31744] = false := by decide +kernel
    have checked4 : search 6 [256, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked5 : search 6 [21478, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked6 : search 6 [4134, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked7 : search 6 [17088, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked8 : search 6 [4096, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [32038, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [294, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [27648, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [16384, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [32704, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [960, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [15360, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15]
  have case12131 : search 7 (mk 1 2 1 3 1) = false := by decide +kernel
  have case12221 : search 7 (mk 1 2 2 2 1) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 1 2 2 2 1) = [
      [10941, 4390, 4390, 8760, 17344, 17344, 31744],
      [2181, 4390, 4390, 8760, 17344, 17344, 31744],
      [19413, 4390, 4390, 8760, 8760, 17344, 31744],
      [2069, 4390, 4390, 8760, 8760, 17344, 31744],
      [32, 2197, 4390, 8760, 17344, 17344, 31744],
      [13118, 2197, 4390, 8760, 17344, 17344, 31744],
      [4358, 2197, 4390, 8760, 17344, 17344, 31744],
      [8728, 2197, 4390, 8760, 17344, 17344, 31744],
      [256, 2197, 4390, 8760, 8760, 17344, 31744],
      [21478, 2197, 4390, 8760, 8760, 17344, 31744],
      [4134, 2197, 4390, 8760, 8760, 17344, 31744],
      [17088, 2197, 4390, 8760, 8760, 17344, 31744],
      [512, 2197, 4390, 4390, 8760, 17344, 31744],
      [25592, 2197, 4390, 4390, 8760, 17344, 31744],
      [8248, 2197, 4390, 4390, 8760, 17344, 31744],
      [16832, 2197, 4390, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [10941, 4390, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked1 : search 6 [2181, 4390, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked2 : search 6 [19413, 4390, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked3 : search 6 [2069, 4390, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked4 : search 6 [32, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked5 : search 6 [13118, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked6 : search 6 [4358, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked7 : search 6 [8728, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked8 : search 6 [256, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [21478, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [4134, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [17088, 2197, 4390, 8760, 8760, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [512, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [25592, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [8248, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [16832, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15]
  have case13111 : search 7 (mk 1 3 1 1 1) = false := by decide +kernel
  have case13112 : search 7 (mk 1 3 1 1 2) = false := by decide +kernel
  have case13121 : search 7 (mk 1 3 1 2 1) = false := by decide +kernel
  have case14111 : search 7 (mk 1 4 1 1 1) = false := by decide +kernel
  have case22111 : search 7 (mk 2 2 1 1 1) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 2 2 1 1 1) = [
      [4, 2197, 4390, 8760, 17344, 31744],
      [4, 4, 2197, 4390, 8760, 17344, 31744],
      [6583, 2197, 4390, 8760, 17344, 31744],
      [6583, 6583, 2197, 4390, 8760, 17344, 31744],
      [2193, 2197, 4390, 8760, 17344, 31744],
      [2193, 2193, 2197, 4390, 8760, 17344, 31744],
      [4386, 2197, 4390, 8760, 17344, 31744],
      [4386, 4386, 2197, 4390, 8760, 17344, 31744],
      [10941, 2197, 4390, 4390, 17344, 31744],
      [10941, 10941, 2197, 4390, 4390, 17344, 31744],
      [8744, 2197, 4390, 4390, 17344, 31744],
      [8744, 8744, 2197, 4390, 4390, 17344, 31744],
      [19413, 2197, 4390, 4390, 8760, 31744],
      [19413, 19413, 2197, 4390, 4390, 8760, 31744],
      [17216, 2197, 4390, 4390, 8760, 31744],
      [17216, 17216, 2197, 4390, 4390, 8760, 31744],
      [13118, 2197, 2197, 4390, 17344, 31744],
      [13118, 13118, 2197, 2197, 4390, 17344, 31744],
      [8728, 2197, 2197, 4390, 17344, 31744],
      [8728, 8728, 2197, 2197, 4390, 17344, 31744],
      [21478, 2197, 2197, 4390, 8760, 31744],
      [21478, 21478, 2197, 2197, 4390, 8760, 31744],
      [17088, 2197, 2197, 4390, 8760, 31744],
      [17088, 17088, 2197, 2197, 4390, 8760, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [4, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked1 : search 6 [4, 4, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked2 : search 6 [6583, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked3 : search 6 [6583, 6583, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked4 : search 6 [2193, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked5 : search 6 [2193, 2193, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked6 : search 6 [4386, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked7 : search 6 [4386, 4386, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked8 : search 6 [10941, 2197, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [10941, 10941, 2197, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [8744, 2197, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [8744, 8744, 2197, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [19413, 2197, 4390, 4390, 8760, 31744] = false := by decide +kernel
    have checked13 : search 6 [19413, 19413, 2197, 4390, 4390, 8760, 31744] = false := by decide +kernel
    have checked14 : search 6 [17216, 2197, 4390, 4390, 8760, 31744] = false := by decide +kernel
    have checked15 : search 6 [17216, 17216, 2197, 4390, 4390, 8760, 31744] = false := by decide +kernel
    have checked16 : search 6 [13118, 2197, 2197, 4390, 17344, 31744] = false := by decide +kernel
    have checked17 : search 6 [13118, 13118, 2197, 2197, 4390, 17344, 31744] = false := by decide +kernel
    have checked18 : search 6 [8728, 2197, 2197, 4390, 17344, 31744] = false := by decide +kernel
    have checked19 : search 6 [8728, 8728, 2197, 2197, 4390, 17344, 31744] = false := by decide +kernel
    have checked20 : search 6 [21478, 2197, 2197, 4390, 8760, 31744] = false := by decide +kernel
    have checked21 : search 6 [21478, 21478, 2197, 2197, 4390, 8760, 31744] = false := by decide +kernel
    have checked22 : search 6 [17088, 2197, 2197, 4390, 8760, 31744] = false := by decide +kernel
    have checked23 : search 6 [17088, 17088, 2197, 2197, 4390, 8760, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19, checked20, checked21, checked22, checked23]
  have case22112 : search 7 (mk 2 2 1 1 2) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 2 2 1 1 2) = [
      [4, 2197, 4390, 8760, 17344, 31744, 31744],
      [6583, 2197, 4390, 8760, 17344, 31744, 31744],
      [2193, 2197, 4390, 8760, 17344, 31744, 31744],
      [4386, 2197, 4390, 8760, 17344, 31744, 31744],
      [10941, 2197, 4390, 4390, 17344, 31744, 31744],
      [8744, 2197, 4390, 4390, 17344, 31744, 31744],
      [19413, 2197, 4390, 4390, 8760, 31744, 31744],
      [17216, 2197, 4390, 4390, 8760, 31744, 31744],
      [2048, 2197, 4390, 4390, 8760, 17344, 31744],
      [31893, 2197, 4390, 4390, 8760, 17344, 31744],
      [149, 2197, 4390, 4390, 8760, 17344, 31744],
      [29696, 2197, 4390, 4390, 8760, 17344, 31744],
      [13118, 2197, 2197, 4390, 17344, 31744, 31744],
      [8728, 2197, 2197, 4390, 17344, 31744, 31744],
      [21478, 2197, 2197, 4390, 8760, 31744, 31744],
      [17088, 2197, 2197, 4390, 8760, 31744, 31744],
      [4096, 2197, 2197, 4390, 8760, 17344, 31744],
      [32038, 2197, 2197, 4390, 8760, 17344, 31744],
      [294, 2197, 2197, 4390, 8760, 17344, 31744],
      [27648, 2197, 2197, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [4, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked1 : search 6 [6583, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked2 : search 6 [2193, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked3 : search 6 [4386, 2197, 4390, 8760, 17344, 31744, 31744] = false := by decide +kernel
    have checked4 : search 6 [10941, 2197, 4390, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked5 : search 6 [8744, 2197, 4390, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked6 : search 6 [19413, 2197, 4390, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked7 : search 6 [17216, 2197, 4390, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked8 : search 6 [2048, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [31893, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [149, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [29696, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [13118, 2197, 2197, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked13 : search 6 [8728, 2197, 2197, 4390, 17344, 31744, 31744] = false := by decide +kernel
    have checked14 : search 6 [21478, 2197, 2197, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked15 : search 6 [17088, 2197, 2197, 4390, 8760, 31744, 31744] = false := by decide +kernel
    have checked16 : search 6 [4096, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked17 : search 6 [32038, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked18 : search 6 [294, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked19 : search 6 [27648, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15, checked16, checked17, checked18, checked19]
  have case22121 : search 7 (mk 2 2 1 2 1) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 2 2 1 2 1) = [
      [4, 2197, 4390, 8760, 17344, 17344, 31744],
      [6583, 2197, 4390, 8760, 17344, 17344, 31744],
      [2193, 2197, 4390, 8760, 17344, 17344, 31744],
      [4386, 2197, 4390, 8760, 17344, 17344, 31744],
      [10941, 2197, 4390, 4390, 17344, 17344, 31744],
      [8744, 2197, 4390, 4390, 17344, 17344, 31744],
      [128, 2197, 4390, 4390, 8760, 17344, 31744],
      [19413, 2197, 4390, 4390, 8760, 17344, 31744],
      [2069, 2197, 4390, 4390, 8760, 17344, 31744],
      [17216, 2197, 4390, 4390, 8760, 17344, 31744],
      [13118, 2197, 2197, 4390, 17344, 17344, 31744],
      [8728, 2197, 2197, 4390, 17344, 17344, 31744],
      [256, 2197, 2197, 4390, 8760, 17344, 31744],
      [21478, 2197, 2197, 4390, 8760, 17344, 31744],
      [4134, 2197, 2197, 4390, 8760, 17344, 31744],
      [17088, 2197, 2197, 4390, 8760, 17344, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [4, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked1 : search 6 [6583, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked2 : search 6 [2193, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked3 : search 6 [4386, 2197, 4390, 8760, 17344, 17344, 31744] = false := by decide +kernel
    have checked4 : search 6 [10941, 2197, 4390, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked5 : search 6 [8744, 2197, 4390, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked6 : search 6 [128, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked7 : search 6 [19413, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked8 : search 6 [2069, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [17216, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [13118, 2197, 2197, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked11 : search 6 [8728, 2197, 2197, 4390, 17344, 17344, 31744] = false := by decide +kernel
    have checked12 : search 6 [256, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked13 : search 6 [21478, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked14 : search 6 [4134, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked15 : search 6 [17088, 2197, 2197, 4390, 8760, 17344, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11, checked12, checked13, checked14, checked15]
  have case23111 : search 7 (mk 2 3 1 1 1) = false := by
    apply close_step (by decide : 0 < 6)
    have frontier : candidateChildren 6 (mk 2 3 1 1 1) = [
      [4, 2197, 4390, 4390, 8760, 17344, 31744],
      [6583, 2197, 4390, 4390, 8760, 17344, 31744],
      [2193, 2197, 4390, 4390, 8760, 17344, 31744],
      [4386, 2197, 4390, 4390, 8760, 17344, 31744],
      [10941, 2197, 4390, 4390, 4390, 17344, 31744],
      [8744, 2197, 4390, 4390, 4390, 17344, 31744],
      [19413, 2197, 4390, 4390, 4390, 8760, 31744],
      [17216, 2197, 4390, 4390, 4390, 8760, 31744],
      [13118, 2197, 2197, 4390, 4390, 17344, 31744],
      [8728, 2197, 2197, 4390, 4390, 17344, 31744],
      [21478, 2197, 2197, 4390, 4390, 8760, 31744],
      [17088, 2197, 2197, 4390, 4390, 8760, 31744]] := by decide +kernel
    rw [frontier]
    have checked0 : search 6 [4, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked1 : search 6 [6583, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked2 : search 6 [2193, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked3 : search 6 [4386, 2197, 4390, 4390, 8760, 17344, 31744] = false := by decide +kernel
    have checked4 : search 6 [10941, 2197, 4390, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked5 : search 6 [8744, 2197, 4390, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked6 : search 6 [19413, 2197, 4390, 4390, 4390, 8760, 31744] = false := by decide +kernel
    have checked7 : search 6 [17216, 2197, 4390, 4390, 4390, 8760, 31744] = false := by decide +kernel
    have checked8 : search 6 [13118, 2197, 2197, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked9 : search 6 [8728, 2197, 2197, 4390, 4390, 17344, 31744] = false := by decide +kernel
    have checked10 : search 6 [21478, 2197, 2197, 4390, 4390, 8760, 31744] = false := by decide +kernel
    have checked11 : search 6 [17088, 2197, 2197, 4390, 4390, 8760, 31744] = false := by decide +kernel
    simp only [List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
      checked0, checked1, checked2, checked3, checked4, checked5, checked6, checked7, checked8, checked9, checked10, checked11]
  simp only [searchCore, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
    (show List.range 1 = [0] from rfl),
    (show List.range 2 = [0, 1] from rfl),
    (show List.range 3 = [0, 1, 2] from rfl),
    (show List.range 4 = [0, 1, 2, 3] from rfl),
    List.all_cons, List.all_nil, Bool.not_false, Bool.and_true,
    true_and, false_and, ite_true, ite_false,
    case11111, case11112, case11113, case11114, case11121, case11122, case11123, case11131, case11132, case11141, case11221, case11222, case11231, case12111, case12112, case12113, case12121, case12122, case12131, case12221, case13111, case13112, case13121, case14111, case22111, case22112, case22121, case23111]

theorem pin_required {s : ℕ} {ws : List ℕ} (h : NR s ws)
    (supported : ∀ w ∈ ws, w ∈ pins) (p : ℕ) (hp : p ∈ pins) : p ∈ ws := by
  have rows : ∀ p ∈ pins, ∃ i < 15, ∃ j < 15,
      (31236 : ℕ).testBit i ≠ (31236 : ℕ).testBit j ∧
      ∀ w ∈ pins, w ≠ p → w.testBit i = w.testBit j := by decide
  obtain ⟨i, -, j, -, difference, equal⟩ := rows p hp
  by_contra missing
  exact difference (TRN_det h i j fun w hw => equal w (supported w hw)
    (fun eq => missing (eq ▸ hw)))

theorem mk_perm (ws : List ℕ) (h : ∀ w ∈ ws, w ∈ pins) :
    ws.Perm (mk (ws.count 2197) (ws.count 4390) (ws.count 8760) (ws.count 17344) (ws.count 31744)) := by
  rw [List.perm_iff_count]
  intro a
  simp only [mk, List.count_append, List.count_replicate]
  by_cases h0 : a = 2197
  · subst h0; simp
  by_cases h1 : a = 4390
  · subst h1; simp
  by_cases h2 : a = 8760
  · subst h2; simp
  by_cases h3 : a = 17344
  · subst h3; simp
  by_cases h4 : a = 31744
  · subst h4; simp
  have : a ∉ ws := by
    intro ha
    simpa [pins, h0, h1, h2, h3, h4] using h a ha
  simp [List.count_eq_zero_of_not_mem this, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]

theorem closeCanonical {s a b c d e : ℕ} (top : s ≤ 7) (cap : a + b + c + d + e + 5 ≤ s + 1)
    (h1 : a ≤ b) (h2 : c ≤ d)
    (h : NR s (mk (a + 1) (b + 1) (c + 1) (d + 1) (e + 1))) : False := by
  have lo : 4 ≤ s := by omega
  have verification : searchCore s = true := by
    interval_cases s
    · exact searchCore4
    · exact searchCore5
    · exact searchCore6
    · exact searchCore7
  unfold searchCore at verification
  have va := List.all_eq_true.1 verification a (List.mem_range.2 (by omega))
  have vb := List.all_eq_true.1 va b (List.mem_range.2 (by omega))
  have vc := List.all_eq_true.1 vb c (List.mem_range.2 (by omega))
  have vd := List.all_eq_true.1 vc d (List.mem_range.2 (by omega))
  have ve := List.all_eq_true.1 vd e (List.mem_range.2 (by omega))
  have f := run_search h
  simp [h1, h2, f] at ve

theorem noCore {s : ℕ} {ws : List ℕ} (h : NR s ws) (size : s ≤ 7)
    (supported : ∀ w ∈ ws, w ∈ pins) : False := by
  have perm := mk_perm ws supported
  have cap := TR.len h
  rw [perm.length_eq] at cap
  simp only [mk, List.length_append, List.length_replicate, List.length_singleton] at cap
  have pa : 0 < ws.count 2197 := List.count_pos_iff.mpr (pin_required h supported 2197 (by decide))
  obtain ⟨a, eqa⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pa)
  have pb : 0 < ws.count 4390 := List.count_pos_iff.mpr (pin_required h supported 4390 (by decide))
  obtain ⟨b, eqb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pb)
  have pc : 0 < ws.count 8760 := List.count_pos_iff.mpr (pin_required h supported 8760 (by decide))
  obtain ⟨c, eqc⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pc)
  have pd : 0 < ws.count 17344 := List.count_pos_iff.mpr (pin_required h supported 17344 (by decide))
  obtain ⟨d, eqd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pd)
  have pe : 0 < ws.count 31744 := List.count_pos_iff.mpr (pin_required h supported 31744 (by decide))
  obtain ⟨e, eqe⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pe)

  rw [eqa, eqb, eqc, eqd, eqe] at cap perm
  have ordered := TR.perm perm h
  by_cases hab : a ≤ b <;> by_cases hcd : c ≤ d
  · exact closeCanonical size (by omega) hab hcd ordered
  · exact closeCanonical size (by omega) hab (by omega) (swapSecond ordered)
  · exact closeCanonical size (by omega) (by omega) hcd (swapFirst ordered)
  · exact closeCanonical size (by omega) (by omega) (by omega) (swapSecond (swapFirst ordered))

def zF : BF := fun _ => false

def rst (p : Fin 7) (a : BF) : BF := fun x => a (Function.update x p false)

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem rst_var_self (p : Fin 7) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 7} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 7 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 7) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 7) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 7) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 7) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

def MonoA : Fin 4 → Prop := fun k => k.val < 2

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 7 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 7 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

def graphTable (a : ℕ) (x : Fin 7 → Bool) : Bool := a.testBit (tableIndex x)

def assignment (a : ℕ) (i : Fin 7) : Bool := a.testBit i.val

theorem inputVector (x : Fin 7 → Bool) : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
  funext i
  fin_cases i <;> rfl

theorem equalSeven {f g : (Fin 7 → Bool) → Bool}
    (h : ∀ a b c d e v w : Bool, f ![a, b, c, d, e, v, w] = g ![a, b, c, d, e, v, w]) : f = g := by
  funext x
  rw [inputVector x]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)

def isNot : GateOp → Bool
  | .not => true
  | _ => false

theorem isNot_true (op : GateOp) : isNot op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNot]

def countBinary : List Gate → ℕ
  | [] => 0
  | g :: gs => countBinary gs + if isNot g.op then 0 else 1

theorem countBinary_le (gs : List Gate) : countBinary gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [countBinary, List.length_cons]
    split <;> omega

theorem countBinary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    countBinary gs < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, he⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · have hb := countBinary_le gs
      simp [countBinary, he, isNot, Nat.lt_succ_of_le hb]
    · have hb := ih ⟨a, ha, he⟩
      simp only [countBinary, List.length_cons]
      split <;> omega

theorem not_key (g : Gate) (W : List BF) (S : BF → Prop) (hop : g.op = GateOp.not)
    (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    ori (gv g W) = zF ∨ S (ori (gv g W)) := by
  obtain ⟨op, ins⟩ := g
  change op = GateOp.not at hop
  subst op
  cases ins with
  | nil => exact Or.inl ori_true
  | cons i rest =>
    have he : gv ⟨GateOp.not, i :: rest⟩ W = fun x => !(W.getD i zF) x := rfl
    rw [he, ori_not]
    rcases getD_mem W i with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero

theorem trans_binary : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) (countBinary gs) S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hw, o => by
    rcases getD_mem W o with h | h
    · exact hw _ h
    · rw [wiresF, h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hw, o => by
    have hg1 := hg g (by simp)
    have hg2 : GOK gs := fun g' h => hg g' (by simp [h])
    have free (h : ori (gv g W) = zF ∨ S (ori (gv g W))) :=
      trans_binary gs (W ++ [gv g W]) S hg2 (by
        intro w hm
        rcases List.mem_append.1 hm with hm | hm
        · exact hw w hm
        · rw [List.mem_singleton.1 hm]; exact h) o
    simp only [wiresF, countBinary]
    by_cases hn : g.op = GateOp.not
    · simpa [hn, isNot] using free (not_key g W S hn hw)
    · rw [ite_eq_right (fun ht => hn ((isNot_true g.op).1 ht))]
      rcases ori_key g W S hg1.1 hg1.2 hw with h | ⟨k, a, b, ha, hb, h⟩
      · exact (free h).imp id (UC_le (Nat.le_succ _))
      · have next := trans_binary gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hg2 (by
          intro w hm
          rcases List.mem_append.1 hm with hm | hm
          · exact (hw w hm).imp id Or.inr
          · rw [List.mem_singleton.1 hm]; exact Or.inr (Or.inl h)) o
        exact next.imp id (UC_gate k a b trivial ha hb)

def sourceVars (xs : Finset (Fin 7)) (f : BF) : Prop := ∃ i ∈ xs, f = var i

theorem remove_var (F : BF) (p : Fin 7) (xs : Finset (Fin 7)) (s : ℕ)
    (hd : ∃ x, rst p F x ≠ F x) (hn : rst p F ≠ zF)
    (h : UC gF (fun _ => True) s (sourceVars xs) F) :
    ∃ t, t + 1 ≤ s ∧ UC gF (fun _ => True) t (sourceVars (xs.erase p)) (rst p F) := by
  have hf : F ≠ zF := fun e => hn (by rw [e]; rfl)
  obtain ⟨k, hk, ws, hws, run⟩ := normalize gF zF (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ => trivial) gF_zero_left gF_zero_right gF_self
    s (sourceVars xs) F (fun _ _ => trivial) hf h
  have hp : var p ∈ ws := by
    by_contra hmiss
    obtain ⟨x, hx⟩ := hd
    apply hx
    exact TRF_det run (Function.update x p false) x (by
      intro w hw
      obtain ⟨i, _, rfl⟩ := (hws w hw).1
      have hi : i ≠ p := fun e => hmiss (e ▸ hw)
      exact Function.update_of_ne hi false x) F (by simp)
  have hc : 1 ≤ dcount p ws := by
    apply Nat.succ_le_of_lt
    unfold dcount
    exact List.countP_pos_iff.2 ⟨var p, hp, by simp [rst_var_self]⟩
  have dr := pot_dead p hn (TR.monoC (fun _ _ _ _ => trivial) run)
  refine ⟨k - dcount p ws, by omega, dr.2 (sourceVars (xs.erase p)) ?_⟩
  intro w hw hz
  obtain ⟨i, hi, rfl⟩ := (hws w hw).1
  have hne : i ≠ p := fun e => hz (e ▸ rst_var_self p)
  exact ⟨i, Finset.mem_erase.2 ⟨hne, hi⟩, rst_var_ne hne⟩

def projectRows : List (Fin 7 → Bool) :=
  [1, 8, 9, 2, 3, 10, 16, 17, 24, 18, 64, 65, 72, 66, 80].map assignment

theorem lower_with_not (gates : List Gate) (o : ℕ) (legal : GOK gates)
    (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (comp : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = (graphTable 340282366920938463149707618005867604480) x) :
    11 ≤ gates.length := by
  have hg : (wiresF gates (List.ofFn var)).getD o zF = graphTable 340282366920938463149707618005867604480 := by
    funext x
    rw [← comp x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have start := trans_binary gates (List.ofFn var) (sourceVars Finset.univ) legal (by
    intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    exact Or.inr ⟨i, Finset.mem_univ i, ori_zp rfl⟩) o
  rw [hg, ori_zp (by decide : (graphTable 340282366920938463149707618005867604480) (fun _ => false) = false)] at start
  have base : UC gF (fun _ => True) (countBinary gates) (sourceVars Finset.univ) (graphTable 340282366920938463149707618005867604480) := by
    rcases start with e | base
    · exact False.elim ((by decide : (graphTable 340282366920938463149707618005867604480) (assignment 9) ≠ false) (congrFun e (assignment 9)))
    · exact base
  obtain ⟨t, removed, restricted⟩ := remove_var (graphTable 340282366920938463149707618005867604480) 2 (Finset.univ : Finset (Fin 7))
    (countBinary gates) ⟨assignment 20, by decide⟩ (by
      intro h
      exact (by decide : rst 2 (graphTable 340282366920938463149707618005867604480) (assignment 9) ≠ false) (congrFun h (assignment 9))) base
  obtain ⟨u, removedAgain, core⟩ := remove_var (rst 2 (graphTable 340282366920938463149707618005867604480)) 5
    ((Finset.univ : Finset (Fin 7)).erase 2) t ⟨assignment 33, by decide⟩ (by
      intro h
      exact (by decide : rst 5 (rst 2 (graphTable 340282366920938463149707618005867604480)) (assignment 9) ≠ false) (congrFun h (assignment 9))) restricted
  have projected : enc (rst 5 (rst 2 (graphTable 340282366920938463149707618005867604480))) projectRows = 31236 := by decide
  have pinCodes : ∀ i : Fin 7, i ≠ 2 → i ≠ 5 → enc (var i) projectRows ∈ pins := by decide
  have abstract : UC gN (fun _ => True) u (fun w => w ∈ pins) 31236 := by
    rw [← projected]
    apply UC_map (fun w => enc w projectRows) (fun k a b => enc_gF k a b projectRows) u
      (sourceVars ((Finset.univ.erase 2).erase 5)) _ _ ?_ core
    rintro _ ⟨i, hi, rfl⟩
    have outer := Finset.mem_erase.mp hi
    exact pinCodes i (Finset.mem_erase.mp outer.2).1 outer.1
  have extra := countBinary_lt gates hnot
  by_contra! small
  obtain ⟨s, less, ws, supported, run⟩ := normalize gN 0 (fun _ => True) (fun w => w < 32768)
    gN_lt gN_zero_left gN_zero_right gN_self u _ 31236
    (by intro w hw; exact (by decide : ∀ n ∈ pins, n < 32768) w hw) (by decide) abstract
  exact noCore run (by omega) fun w hw => (supported w hw).1

def graph (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

def witness : List Gate := [⟨.or, [5, 3]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [8, 7]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [11, 10]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [13, 1]⟩, ⟨.and, [14, 6]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 9]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool,
    Circuit.eval ⟨witness, 17⟩ (List.ofFn x) = graph x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 7 → Bool, graph x = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_11878

open PEqualNP.Outside.L_meta_11878 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_11878 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have comp : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = graph x :=
      fun x => (computes x).trans (graph_correct x).symm
    have eq : graph = (graphTable 340282366920938463149707618005867604480) := equalSeven (by decide)
    have large := lower_with_not gates o legal hnot (fun x => (comp x).trans (congrFun eq x))
    have hw : witness.length = 11 := rfl
    exact ⟨witness, 17, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
  · refine ⟨gates, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨ops, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases ops with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hnot ⟨g, hg, h⟩)
