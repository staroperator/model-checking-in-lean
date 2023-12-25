import TemporalLogic.CTL.Logic

section
variable {α : Type u}

def iter (f : Set α → Set α) : Nat → Set α
| 0 => ∅
| n + 1 => f (iter f n)

def iter.decidable
  (h : ∀ s, DecidablePred s → DecidablePred (f s)) :
  ∀ n, DecidablePred (iter f n)
| 0, _ => isFalse not_false
| n + 1, s => h _ (decidable h n) s

theorem iter.monotone (h : Monotone f) : Monotone (iter f ·) := by
  intro n m h'
  induction' n with n ih generalizing m
  · exact bot_le
  · cases' m with m
    · contradiction
    · apply h; apply ih; exact Nat.le_of_succ_le_succ h'

variable [Fintype α]

noncomputable local instance {s : Set α} : Fintype s := by
  have := Classical.propDecidable
  apply Set.fintypeSubset (s := Set.univ)
  apply Set.subset_univ

def lfp (f : Set α → Set α) : Set α :=
  iter f (Fintype.card α)

variable {f : Set α → Set α}

def lfp.decidable (h : ∀ s, DecidablePred s → DecidablePred (f s)) :
  DecidablePred (lfp f) :=
  iter.decidable h _

variable (h : Monotone f)

lemma lfp.is_fixpoint : f (lfp f) = lfp f := by
  suffices h' : f (lfp f) ⊆ lfp f by
    apply Set.Subset.antisymm h'
    apply iter.monotone h (Nat.le_succ _)
  by_contra h₁
  have h₂ : ∀ n ≤ Fintype.card α, iter f n ⊂ iter f (n + 1) := by
    intro n h₂
    constructor
    · apply iter.monotone h; apply Nat.le_succ
    · intro h₃
      apply h₁; clear h₁
      simp [lfp]; generalize Fintype.card α = m at *
      induction' m with m ih
      · cases h₂; exact h₃
      · rcases Nat.of_le_succ h₂ with h₂ | h₂
        · apply h; exact ih h₂
        · rw [←h₂]; exact h₃
  have h₃ : ∀ n ≤ Fintype.card α, Finset.card (iter f n).toFinset ≥ n := by
    intro n h
    induction' n with n ih
    · apply Nat.zero_le
    · apply Nat.lt_of_le_of_lt
      · apply ih; exact Nat.le_trans (Nat.le_succ _) h
      · apply Finset.card_lt_card
        simp; apply h₂
        exact Nat.le_trans (Nat.le_succ _) h
  have h₄ : (lfp f).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    apply Nat.le_antisymm
    · apply Finset.card_le_univ
    · apply h₃; rfl
  apply h₁
  simp at h₄
  rw [h₄]
  apply Set.subset_univ 

theorem lfp.iff_union_iter : x ∈ lfp f ↔ ∃ n, x ∈ iter f n := by
  constructor
  · intro; exists Fintype.card α
  · intro ⟨n, h₁⟩
    by_cases h₂ : n < Fintype.card α
    · exact iter.monotone h (Nat.le_of_lt h₂) h₁
    · simp at h₂
      have h₃ : iter f n = lfp f := by
        clear h₁
        induction' h₂ with n _ ih
        · rfl
        · simp [iter, ih]; exact is_fixpoint h
      rw [←h₃]; exact h₁

end



variable {𝓢 : KripkeStructure α}

def allNext : Set 𝓢.S → Set 𝓢.S
| p, s => ∀ s', 𝓢.R s s' → p s'

instance allNext.decidable {p : Set 𝓢.S} [DecidablePred p] :
  DecidablePred (allNext p)
| _ => have := 𝓢.decR; Fintype.decidableForallFintype

theorem allNext.monotone {p q : Set 𝓢.S} : p ⊆ q → allNext p ⊆ allNext q
| h, _, h₁, _, h₂ => h (h₁ _ h₂)

def exNext : Set 𝓢.S → Set 𝓢.S
| p, s => ∃ s', 𝓢.R s s' ∧ p s'

instance exNext.decidable {p : Set 𝓢.S} [DecidablePred p] :
  DecidablePred (exNext p)
| _ => have := 𝓢.decR; Fintype.decidableExistsFintype

theorem exNext.monotone {p q : Set 𝓢.S} : p ⊆ q → exNext p ⊆ exNext q
| h, _, ⟨s', h₁, h₂⟩ => ⟨s', h₁, h h₂⟩

def iterAllUntil (p q s : Set 𝓢.S) := q ∪ (p ∩ allNext s)

theorem iterAllUntil.iff :
  s ∈ iter (iterAllUntil p q) n ↔
  ∀ (π : 𝓢.Trace), π 0 = s → ∃ k < n, (∀ k' < k, π k' ∈ p) ∧ π k ∈ q := by
  induction' n with n ih generalizing s
  · simp [iter]
    exact KripkeStructure.Trace.existence s
  · simp [iter, iterAllUntil]
    constructor
    · rintro (h₁ | ⟨h₁, h₂⟩) π h₃
      · exists 0; simp [h₃]; exact h₁
      · have h₄ : π 1 ∈ iter (iterAllUntil p q) n := by
          apply h₂; rw [←h₃]; apply π.pathR
        rw [ih] at h₄
        rcases h₄ (π.suffix 1) rfl with ⟨k, h₅, h₆, h₇⟩
        exists k + 1; constructor
        · exact Nat.succ_lt_succ h₅
        constructor
        · intro k' h
          cases' k' with k'
          · rw [h₃]; exact h₁
          · apply h₆; exact Nat.lt_of_succ_lt_succ h
        · exact h₇
    · intro h₁
      by_cases h₂ : s ∈ q
      · left; exact h₂
      · right; constructor
        · rcases KripkeStructure.Trace.existence s with ⟨π₀, h⟩
          rcases h₁ _ h with ⟨k, h₃, h₄, h₅⟩
          cases' k with k
          · rw [h] at h₅; contradiction
          · rw [←h]; apply h₄; apply Nat.zero_lt_succ
        · intro s' h₃
          apply ih.mpr
          intro π h₄
          let π' := KripkeStructure.Trace.cons s π (by rw [h₄]; exact h₃)
          rcases h₁ π' rfl with ⟨k, h₅, h₆, h₇⟩
          cases' k with k
          · contradiction
          · exists k; constructor
            · exact Nat.lt_of_succ_lt_succ h₅
            constructor
            · intro k' h; exact h₆ (k' + 1) (Nat.succ_lt_succ h)
            · exact h₇

theorem iterAllUntil.monotone : Monotone (iterAllUntil p q) := by
  intro p q h
  apply Set.union_subset_union_right
  apply Set.inter_subset_inter_right
  apply allNext.monotone
  exact h

def allUntil (p q : Set 𝓢.S) : Set 𝓢.S := lfp (iterAllUntil p q)

instance allUntil.decidable [DecidablePred p] [DecidablePred q] :
  DecidablePred (allUntil p q) := by
  apply lfp.decidable
  intro s _ x
  apply @Set.decidableUnion _ _ _ _ ?_ ?_
  · apply_assumption
  · apply @Set.decidableInter _ _ _ _ ?_ ?_
    · apply_assumption
    · apply allNext.decidable

theorem allUntil.iff : s ⊨ 𝓐 p 𝓤 q ↔ s ∈ allUntil (· ⊨ p) (· ⊨ q) := by
  simp [allUntil, lfp.iff_union_iter iterAllUntil.monotone, iterAllUntil.iff]
  constructor
  · intro h
    apply CTL.all_until_upper_bound at h
    rcases h with ⟨n, h⟩
    exists n + 1
    intro π h₁
    rcases h π h₁ with ⟨k, h₂, h₃⟩
    exists k, Nat.lt_succ_of_le h₂
  · intro ⟨n, h⟩ π h₁
    rcases h π h₁ with ⟨k, _, _⟩
    exists k

def iterExUntil (p q s : Set 𝓢.S) := q ∪ (p ∩ exNext s)

theorem iterExUntil.iff :
  s ∈ iter (iterExUntil p q) n ↔
  ∃ (π : 𝓢.Trace), π 0 = s ∧ ∃ k < n, (∀ k' < k, π k' ∈ p) ∧ π k ∈ q := by
  induction' n with n ih generalizing s
  · simp [iter]
  · simp [iter, iterExUntil]
    constructor
    · rintro (h₁ | ⟨h₁, s', h₂, h₃⟩)
      · rcases KripkeStructure.Trace.existence s with ⟨π₀, h⟩
        exists π₀, h, 0; constructor
        · apply Nat.zero_lt_succ
        constructor
        · intro _ h; contradiction
        · rw [h]; exact h₁
      · apply ih.mp at h₃
        rcases h₃ with ⟨π, h₃, k, h₄, h₅, h₆⟩
        let π' := KripkeStructure.Trace.cons s π (by rw [h₃]; exact h₂)
        exists π', rfl, k + 1; constructor
        · exact Nat.succ_lt_succ h₄
        constructor
        · intro k' h
          cases' k' with k'
          · exact h₁
          · apply h₅; exact Nat.lt_of_succ_lt_succ h
        · exact h₆
    · intro ⟨π, h₁, k, h₂, h₃, h₄⟩
      cases' k with k
      · left; rw [←h₁]; exact h₄
      · right; constructor
        · rw [←h₁]; apply h₃; apply Nat.zero_lt_succ
        · exists π 1; constructor
          · rw [←h₁]; apply π.pathR
          · apply ih.mpr
            exists π.suffix 1, rfl, k; constructor
            · exact Nat.lt_of_succ_lt_succ h₂
            constructor
            · intro k' h; apply h₃ (k' + 1); exact Nat.succ_lt_succ h
            · exact h₄

theorem iterExUntil.monotone : Monotone (iterExUntil p q) := by
  intro p q h
  apply Set.union_subset_union_right
  apply Set.inter_subset_inter_right
  apply exNext.monotone
  exact h

def exUntil (p q : Set 𝓢.S) := lfp (iterExUntil p q)

instance exUntil.decidable [DecidablePred p] [DecidablePred q] :
  DecidablePred (exUntil p q) := by
  apply lfp.decidable
  intro s _ x
  apply @Or.decidable _ _ ?_ ?_
  · apply_assumption
  · apply @And.decidable _ _ ?_ ?_
    · apply_assumption
    · apply exNext.decidable

theorem exUntil.iff : s ⊨ 𝓔 p 𝓤 q ↔ s ∈ exUntil (· ⊨ p) (· ⊨ q) := by
  simp [exUntil, lfp.iff_union_iter iterExUntil.monotone, iterExUntil.iff]
  constructor
  · intro ⟨π, h₁, k, h₂, h₃⟩
    exists k + 1, π, h₁, k, Nat.lt_succ_self _
  · intro ⟨_, π, h₁, k, _, h₃, h₄⟩
    exists π, h₁, k

instance CTL.decSatisfy :
  (s : 𝓢.S) → (p : CTL α) → Decidable (s ⊨ p)
  | s, atom a => 𝓢.decL s a
  | _, ⊤ => isTrue True.intro
  | s, ~ p => @Not.decidable _ (decSatisfy s p)
  | s, p ⋀ q => @And.decidable _ _ (decSatisfy s p) (decSatisfy s q)
  | s, 𝓐𝓧 p => @allNext.decidable _ _ _ (decSatisfy · p) s
  | s, 𝓔𝓧 p => @exNext.decidable _ _ _ (decSatisfy · p) s
  | s, 𝓐 p 𝓤 q => by
    rw [allUntil.iff]
    apply @allUntil.decidable _ _ _ _ (decSatisfy · p) (decSatisfy · q)
  | s, 𝓔 p 𝓤 q => by
    rw [exUntil.iff]
    apply @exUntil.decidable _ _ _ _ (decSatisfy · p) (decSatisfy · q)

instance CTL.decSatisfied : Decidable (CTL.satisfied 𝓢 p) :=
  have := 𝓢.decI
  Fintype.decidableForallFintype
