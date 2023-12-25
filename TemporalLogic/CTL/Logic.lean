import Mathlib.Data.Set.Finite
import TemporalLogic.KripkeStructure

inductive CTL (α : Type u)
| atom : α → CTL α
| true : CTL α
| not : CTL α → CTL α
| and : CTL α → CTL α → CTL α
| allNext : CTL α → CTL α
| exNext : CTL α → CTL α
| allUntil : CTL α → CTL α → CTL α
| exUntil : CTL α → CTL α → CTL α

notation "⊤" => CTL.true
prefix:80 "~ " => CTL.not
def CTL.false : CTL α := ~ ⊤
notation "⊥" => CTL.false
infix:74 "⋀" => CTL.and
def CTL.or (φ ψ : CTL α) := ~ (~ φ ⋀ ~ ψ)
infix:72 "⋁" => CTL.or
def CTL.imp (φ ψ : CTL α) := ~ φ ⋁ ψ
infix:70 "⇒" => CTL.imp
prefix:80 "𝓐𝓧" => CTL.allNext
prefix:80 "𝓔𝓧" => CTL.exNext
notation:80 "𝓐" φ "𝓤" ψ:80 => CTL.allUntil φ ψ
notation:80 "𝓔" φ "𝓤" ψ:80 => CTL.exUntil φ ψ
def CTL.allFinal (φ : CTL α) := 𝓐 ⊤ 𝓤 φ
prefix:80 "𝓐𝓕" => CTL.allFinal
def CTL.exFinal (φ : CTL α) := 𝓔 ⊤ 𝓤 φ
prefix:80 "𝓔𝓕" => CTL.exFinal
def CTL.allGlobal (φ : CTL α) := ~ 𝓔𝓕 ~ φ
prefix:80 "𝓐𝓖" => CTL.allGlobal
def CTL.exGlobal (φ : CTL α) := ~ 𝓐𝓕 ~ φ
prefix:80 "𝓔𝓖" => CTL.exGlobal

def CTL.satisfy {𝓢 : KripkeStructure α} (s : 𝓢.S) : CTL α → Prop
| CTL.atom a => 𝓢.L s a
| ⊤ => True
| ~ φ => ¬ satisfy s φ
| φ ⋀ ψ => satisfy s φ ∧ satisfy s ψ
| 𝓐𝓧 φ => ∀ s', 𝓢.R s s' → satisfy s' φ
| 𝓔𝓧 φ => ∃ s', 𝓢.R s s' ∧ satisfy s' φ
| 𝓐 φ 𝓤 ψ => ∀ (π : 𝓢.Trace), π 0 = s →
  ∃ k, (∀ k' < k, satisfy (π k') φ) ∧ satisfy (π k) ψ
| 𝓔 φ 𝓤 ψ => ∃ (π : 𝓢.Trace), π 0 = s ∧
  ∃ k, (∀ k' < k, satisfy (π k') φ) ∧ satisfy (π k) ψ

notation:40 s " ⊨ " φ:40 => CTL.satisfy s φ
notation:40 s " ⊭ " p:40 => ¬ s ⊨ p

def CTL.satisfied (𝓢 : KripkeStructure α) (φ : CTL α) :=
  ∀ s, 𝓢.I s → s ⊨ φ

variable {𝓢 : KripkeStructure α} {s : 𝓢.S}

theorem CTL.satisfy_false : ¬ (s ⊨ ⊥) := by
  simp [false, satisfy]

theorem CTL.satisfy_or : s ⊨ φ ⋁ ψ ↔ s ⊨ φ ∨ s ⊨ ψ := by
  simp [or, satisfy]
  tauto

theorem CTL.satisfy_imp : s ⊨ φ ⇒ ψ ↔ (s ⊨ φ → s ⊨ ψ) := by
  simp [imp, satisfy]

theorem CTL.satisfy_all_final :
  s ⊨ 𝓐𝓕 φ ↔ ∀ (π : 𝓢.Trace), π 0 = s → ∃ k, π k ⊨ φ := by
  simp [allFinal, satisfy]

theorem CTL.satisfy_exists_final :
  s ⊨ 𝓔𝓕 φ ↔ ∃ (π : 𝓢.Trace), π 0 = s ∧ ∃ k, π k ⊨ φ := by
  simp [exFinal, satisfy]

theorem CTL.satisfy_all_global :
  s ⊨ 𝓐𝓖 φ ↔ ∀ (π : 𝓢.Trace), π 0 = s → ∀ k, π k ⊨ φ := by
  simp [allGlobal, satisfy_exists_final, satisfy]

theorem CTL.satisfy_exists_global :
  s ⊨ 𝓔𝓖 φ ↔ ∃ (π : 𝓢.Trace), π 0 = s ∧ ∀ k, π k ⊨ φ := by
  simp [exGlobal, satisfy_all_final, satisfy]

theorem CTL.not_all_next :
  s ⊨ ~ 𝓐𝓧 φ ↔ s ⊨ 𝓔𝓧 ~ φ := by
  simp [satisfy]

theorem CTL.not_exists_next :
  s ⊨ ~ 𝓔𝓧 φ ↔ s ⊨ 𝓐𝓧 ~ φ := by
  simp [satisfy]

theorem CTL.expand_all_until :
  s ⊨ 𝓐 φ 𝓤 ψ ↔ s ⊨ ψ ⋁ φ ⋀ 𝓐𝓧 (𝓐 φ 𝓤 ψ) := by
  simp [satisfy_or]
  constructor
  · intro h₁
    by_cases h₂ : s ⊨ ψ
    · left; exact h₂
    · right; constructor
      · rcases KripkeStructure.Trace.existence s with ⟨π₀, h⟩
        rcases h₁ _ h with ⟨k, h₃, h₄⟩
        cases' k with k
        · rw [h] at h₄; contradiction
        · rw [←h]; apply h₃; apply Nat.zero_lt_succ
      · intro s' h₃ π h₄
        let π' := KripkeStructure.Trace.cons s π (by rw [h₄]; exact h₃)
        rcases h₁ π' rfl with ⟨k, h₅, h₆⟩
        cases' k with k
        · contradiction
        · exists k; constructor
          · intro k' h; exact h₅ (k' + 1) (Nat.succ_lt_succ h)
          · exact h₆
  · rintro (h₁ | ⟨h₁, h₁'⟩) π h₂
    · exists 0; constructor
      · intro _ h; contradiction
      · rw [h₂]; exact h₁
    · let π' := π.suffix 1
      rcases h₁' (π 1) (by rw [←h₂]; apply π.pathR) π' rfl with ⟨k, h₃, h₄⟩
      exists k + 1; constructor
      · intro k' h
        cases' k' with k'
        · rw [h₂]; exact h₁
        · apply h₃; exact Nat.lt_of_succ_lt_succ h
      · exact h₄

theorem CTL.expand_all_final :
  s ⊨ 𝓐𝓕 φ ↔ s ⊨ φ ⋁ 𝓐𝓧 𝓐𝓕 φ := by
  simp [allFinal, expand_all_until, satisfy_or]
  simp [satisfy]

theorem CTL.expand_exists_global :
  s ⊨ 𝓔𝓖 φ ↔ s ⊨ φ ⋀ 𝓔𝓧 𝓔𝓖 φ := by
  simp [exGlobal]
  unfold satisfy
  simp [expand_all_final, satisfy_or, not_or]
  apply and_congr
  · simp [satisfy]
  · exact not_all_next

theorem CTL.expand_exists_until :
  s ⊨ 𝓔 φ 𝓤 ψ ↔ s ⊨ ψ ⋁ φ ⋀ 𝓔𝓧 (𝓔 φ 𝓤 ψ) := by
  simp [satisfy_or]
  constructor
  · intro ⟨π, h₁, k, h₂, h₃⟩
    cases' k with k
    · left; rw [←h₁]; exact h₃
    · right; constructor
      · rw [←h₁]; apply h₂; apply Nat.zero_lt_succ
      · exists π 1; constructor
        · rw [←h₁]; apply π.pathR
        · exists π.suffix 1, rfl, k; constructor
          · intro k' h; apply h₂ (k' + 1); exact Nat.succ_lt_succ h
          · exact h₃
  · rintro (h₁ | ⟨h₁, s', h₂, π, h₃, k, h₄, h₅⟩)
    · rcases KripkeStructure.Trace.existence s with ⟨π₀, h⟩
      exists π₀, h, 0; constructor
      · intro _ h; contradiction
      · rw [h]; exact h₁
    · let π' := KripkeStructure.Trace.cons s π (by rw [h₃]; exact h₂)
      exists π', rfl, k + 1; constructor
      · intro k' h
        cases' k' with k'
        · exact h₁
        · apply h₄; exact Nat.lt_of_succ_lt_succ h
      · exact h₅

theorem CTL.expand_exists_final :
  s ⊨ 𝓔𝓕 φ ↔ s ⊨ φ ⋁ 𝓔𝓧 𝓔𝓕 φ := by
  simp [exFinal, expand_exists_until, satisfy_or]
  simp [satisfy]

theorem CTL.expand_all_global :
  s ⊨ 𝓐𝓖 φ ↔ s ⊨ φ ⋀ 𝓐𝓧 𝓐𝓖 φ := by
  simp [allGlobal]
  unfold satisfy
  simp [expand_exists_final, satisfy_or, not_or]
  apply and_congr
  · simp [satisfy]
  · exact not_exists_next



lemma Nat.succ_mod (h : m > 0):
  (k + 1) % m = if k % m = m - 1 then 0 else k % m + 1 := by
  rcases Nat.eq_or_lt_of_le (Nat.le_pred_of_lt (Nat.mod_lt k h))
    with (h₁ | h₁)
  · rw [←Nat.sub_one] at h₁
    simp [h₁]
    apply mod_eq_zero_of_dvd
    have h₂ := mod_add_div k m
    rw [h₁] at h₂
    rw [←h₂, add_right_comm, Nat.sub_add_cancel (one_le_of_lt h)]
    exists 1 + k / m
    rw [mul_add, mul_one]
  · rw [←Nat.sub_one] at h₁
    simp [ne_of_lt h₁]
    have h₂ : (k + 1) % m = (k % m + 1) % m := by
      apply add_mod_eq_add_mod_right
      rw [mod_mod]
    rw [h₂]
    apply mod_eq_of_lt
    exact succ_lt_of_lt_pred h₁

theorem CTL.all_until_upper_bound :
  s ⊨ 𝓐 p 𝓤 q → ∃ n, ∀ (π : 𝓢.Trace), π 0 = s →
  ∃ k ≤ n, (∀ k' < k, satisfy (π k') p) ∧ satisfy (π k) q := by
  intro h₁
  by_contra h₂
  push_neg at h₂
  have h₃ : ∀ n, ∃ (π : 𝓢.Trace), π 0 = s ∧ ∀ k ≤ n, π k ⊭ q := by
    intro n
    rcases h₂ n with ⟨π, h₃, h₄⟩
    have h₅ : ∀ k ≤ n, π k ⊨ p := by
      by_contra h₅
      push_neg at h₅
      rcases h₅ with ⟨k₁, h₅, h₆⟩
      rcases h₁ π h₃ with ⟨k₂, h₇, h₈⟩
      have h₉ : k₁ ≥ k₂ := by
        by_contra h₉
        simp at h₉
        apply h₇ at h₉
        contradiction
      apply h₄ k₂
      · exact Nat.le_trans h₉ h₅
      · exact h₇
      · exact h₈
    exists π, h₃
    intro k h
    apply h₄ k h
    intro k' h'
    apply h₅
    exact Nat.le_trans (Nat.le_of_lt h') h
  have h₄ : ∃ (π : 𝓢.Trace), π 0 = s ∧
    ∃ (i j : Nat), i < j ∧ π i = π j ∧ ∀ k ≤ j, π k ⊭ q := by
    rcases h₃ (Fintype.card 𝓢.S) with ⟨π, h₄, h₅⟩
    exists π, h₄
    let f : Fin (Fintype.card 𝓢.S + 1) → 𝓢.S := λ x => π x
    have h₆ : Fintype.card (Fin (Fintype.card 𝓢.S + 1)) > Fintype.card 𝓢.S := by simp
    rcases Fintype.exists_ne_map_eq_of_card_lt f h₆ with
      ⟨⟨i, h₁'⟩, ⟨j, h₂'⟩, h₃', h₄'⟩
    simp at h₃' h₄'
    rcases Nat.lt_or_gt_of_ne h₃' with (h | h)
    · exists i, j, h, h₄'
      intro k h'
      apply h₅
      exact Nat.le_trans h' (Nat.le_of_lt_succ h₂')
    · exists j, i, h, Eq.symm h₄'
      intro k h'
      apply h₅
      exact Nat.le_trans h' (Nat.le_of_lt_succ h₁')
  have h₅ : ∃ (π : 𝓢.Trace), π 0 = s ∧ ∀ k, π k ⊭ q := by
    rcases h₄ with ⟨π, h₄, i, j, h₅, h₆, h₇⟩
    let π' : Path 𝓢.S := λ k =>
      if k < i then π k else π (i + (k - i) % (j - i))
    have h₈ : ∀ k, 𝓢.R (π' k) (π' (k + 1)) := by
      intro k; simp
      rcases Nat.lt_trichotomy (k + 1) i with (h | h | h)
      · simp [h, Nat.lt_of_succ_lt h]; apply π.pathR
      · simp [←h]; apply π.pathR
      · apply Nat.le_of_lt_succ at h
        simp [Nat.not_lt_of_ge h, Nat.not_lt_of_ge (Nat.le_succ_of_le h)]
        rw [Nat.succ_sub h, ←Nat.add_one]
        rw [Nat.succ_mod (Nat.zero_lt_sub_of_lt h₅)]
        split
        next h' =>
          simp [h']
          rw [Nat.sub_right_comm, Nat.sub_one,
            Nat.add_sub_cancel' (Nat.le_pred_of_lt h₅)]
          conv => arg 3; rw [h₆, ←Nat.sub_add_cancel (Nat.one_le_of_lt h₅)]
          apply π.pathR
        next h' =>
          apply π.pathR
    exists ⟨π', h₈⟩
    constructor
    · simp; split
      next => exact h₄
      next h => simp at h; rw [h]; exact h₄
    · intro k
      simp; split <;> apply h₇
      next h => exact Nat.le_trans (Nat.le_of_lt h) (Nat.le_of_lt h₅)
      next h =>
        apply Nat.add_le_of_le_sub' (Nat.le_of_lt h₅)
        apply Nat.le_of_lt
        exact Nat.mod_lt _ (Nat.zero_lt_sub_of_lt h₅)
  rcases h₅ with ⟨π, h₅, h₆⟩
  rcases h₁ π h₅ with ⟨k, _, h₇⟩
  exact h₆ _ h₇
