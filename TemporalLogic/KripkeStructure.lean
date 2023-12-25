import Mathlib.Data.Fintype.Basic
import TemporalLogic.Path

structure KripkeStructure (α : Type v) where
  S : Type u
  [finiteS : Fintype S]
  [decEqS : DecidableEq S]
  I : S → Prop
  [decI : DecidablePred I]
  R : S → S → Prop
  [decR : DecidableRel R]
  totalR : ∀ s, ∃ s', R s s'
  L : S → α → Prop
  [decL : ∀ s a, Decidable (L s a)]

instance {𝓢 : KripkeStructure α} : Fintype 𝓢.S := 𝓢.finiteS

structure KripkeStructure.Trace (𝓢 : KripkeStructure α) where
  path : Path 𝓢.S
  pathR : ∀ n, 𝓢.R (path n) (path (n + 1))

namespace KripkeStructure.Trace
variable {𝓢 : KripkeStructure α}
instance : Coe 𝓢.Trace (Path 𝓢.S) := ⟨KripkeStructure.Trace.path⟩
instance : CoeFun 𝓢.Trace (λ _ => Nat → 𝓢.S) :=
  ⟨KripkeStructure.Trace.path⟩

namespace existence

noncomputable def next (s : 𝓢.S) : 𝓢.S :=
  Classical.choose (𝓢.totalR s)

noncomputable def path (s : 𝓢.S) : Nat → 𝓢.S
| 0 => s
| n + 1 => next (path s n)

theorem pathR : ∀ n, 𝓢.R (path s n) (path s (n + 1)) := by
  intro
  exact Classical.choose_spec (h := 𝓢.totalR _)

end existence

theorem existence (s : 𝓢.S) :
  ∃ (π : 𝓢.Trace), π 0 = s := by
  exists ⟨existence.path s, existence.pathR⟩

def cons (s : 𝓢.S) (π : 𝓢.Trace) (h : 𝓢.R s (π 0)) : 𝓢.Trace where
  path := Path.cons s π
  pathR
  | 0 => h
  | n + 1 => π.pathR n

def suffix (π : 𝓢.Trace) (n : Nat) : 𝓢.Trace where
  path := Path.suffix π n
  pathR := by intro k; simp [Path.suffix, Nat.succ_add]; apply π.pathR

end KripkeStructure.Trace

structure KripkeStructure.Run (𝓢 : KripkeStructure α) extends 𝓢.Trace where
  pathI : 𝓢.I (path 0)
