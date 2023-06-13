import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Covering
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Topology.UnitInterval

open Topology Filter unitInterval Bundle

/-
Notation:
`E` : the covering space of `X` - otherwise denoted tilde X
`F` : the lift of the map `f`
`F₀` : the start of `F`, i.e. `F₀ = F(y, 0)`

`U : ι → Set α` : collection of (open) sets of α
`s ⊆ ⋃ i, U i` : a (possibly infinite) open cover 
`∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i` : existence of finite subcover

`Continuous f` : `f` is globally continuous
`ContinuousAt f a` : `f` is continuous at the point a

`IsCompact (s : Set α)` : the set s is compact in topological space `α`

`Trivialization F proj` : local trivialization of `proj : E → B` with fiber `F`
`IsEvenlyCovered x ι` : `DiscreteTopology ι ∧ ∃ t : Trivialization ι p, x ∈ t.baseSet`
                      : fiber over x has discrete topology & has a local trivialization
`IsCoveringMap p` : `∀ x, IsEvenlyCovered (f x) (f ⁻¹' {x})`

Theorems:
`toTrivialization` : gets local trivialization above a point from a covering map
`IsCompact.elim_finite_subcover` : reduces open cover to finite cover

`isCompact_singleton` : set of a single point is compact
`isCompact_prod` : product of compact sets is compact
-/

variable {α β ε : Type _}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace ε]
variable (X : Set α) (Y : Set β) (E : Set ε)
variable (x : X) (y : Y) (t : I)

theorem homotopy_lift (Continuous f : Y ×ˢ I → X) (IsCoveringMap p : E → X) (Continuous F₀ : Y → E) :
  ∃ Continuous F : Y ×ˢ I → E, p ∘ F = f ∧ (fun y ↦ F ⟨y, (0:I)⟩, _) = F₀ := by
    sorry