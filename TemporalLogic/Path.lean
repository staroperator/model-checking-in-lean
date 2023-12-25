import Mathlib.Data.Set.Basic
import Mathlib.Tactic.ApplyAt

def Path (α : Type u) := Nat → α

def Path.map (π : Path α) (f : α → β) : Path β := f ∘ π

def Path.suffix (π : Path α) (n : Nat) : Path α := λ k => π (k + n)
notation π "^[" n "]" => Path.suffix π n

theorem Path.suffix_comp {π : Path α} {n m : Nat} :
  π^[n]^[m] = π^[n + m] := by
  funext; simp [Path.suffix, Nat.add_assoc, Nat.add_comm m]

def Path.prefix (π : Path α) : Nat → List α
| 0 => []
| k + 1 => π.prefix k ++ [π k]

theorem Path.prefix_length {π : Path α} : (π.prefix n).length = n := by
  induction n <;> simp [Path.prefix]; aesop

theorem Path.prefix_get {π : Path α} {k : Fin _} : (π.prefix n).get k = π k := by
  induction n with
  | zero => cases k.isLt
  | succ n ih =>
    cases' k with k h
    simp [Path.prefix]
    by_cases h' : k < (π.prefix n).length
    · trans
      · exact (List.get_append_left _ _ h')
      · exact ih
    · trans
      · exact (List.get_last h')
      · simp [prefix_length] at h h'
        rw [Nat.le_antisymm (Nat.le_of_lt_succ h) h']

def Path.cons (x : α) (π : Path α) : Path α
| 0 => x
| k + 1 => π k

theorem Path.cons_suffix {π : Path α} : (cons x π)^[1] = π := by
  funext k; rfl

def Path.concat : List α → Path α → Path α
| [], π => π
| x :: l, π => cons x (concat l π)

theorem Path.concat_apply :
  (concat l π) k =
  if h : k < l.length then l.get ⟨k, h⟩ else π (k - l.length) := by
  induction l generalizing k with
  | nil => rfl
  | cons x l ih =>
    simp [concat]
    cases' k with k <;> simp [cons]
    rw [ih]
    by_cases h : k < l.length
    · simp [h, Nat.succ_lt_succ h]
    · simp [h, mt Nat.lt_of_succ_lt_succ h]

theorem Path.concat_prefix : (concat l π).prefix l.length = l := by
  apply List.ext_get
  · simp [prefix_length]
  · intro k h₁ h₂
    simp [prefix_get, concat_apply, h₂]

theorem Path.concat_suffix {π : Path α} : (concat l π)^[l.length] = π := by
  funext k
  simp [suffix, concat_apply]
  intro h
  apply Nat.lt_of_le_of_lt (Nat.le_add_left _ _) at h
  exfalso; exact Nat.not_succ_le_self _ h

def Path.inf (π : Path α) : Set α :=
  λ s => ∀ k, ∃ k' ≥ k, π k' = s
