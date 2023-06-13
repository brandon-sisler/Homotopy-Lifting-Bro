import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Covering
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Topology.UnitInterval

open Topology Filter unitInterval Bundle

universe u
variable {X Y E : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
variable (Continuous f : Y × I → X) (IsCoveringMap p : E → X)
variable (x : X) (y : Y) (t : I)


/-
Notation:
`E` : the covering space of `X` - otherwise denoted tilde X
`F` : the lift of the map `f`
`F₀` : the start of `F`, i.e. `F₀ = F(y, 0)`

`Continuous f` : `f` is globally continuous
`ContinuousAt f a` : `f` is continuous at the point a

`Trivialization F proj` : local trivialization of `proj : E → B` with fiber `F`
`IsEvenlyCovered x ι` : `DiscreteTopology ι ∧ ∃ t : Trivialization ι p, x ∈ t.baseSet`
                      : fiber over x has discrete topology & has a local trivialization
`IsCoveringMap p` : `∀ x, IsEvenlyCovered (f x) (f ⁻¹' {x})`

Theorems:
`toTrivialization` : gets local trivialization above a point from a covering map
-/

theorem homotopy_lift (Continuous f : Y × I → X) (IsCoveringMap p : E → X) (Continuous F₀ : Y → E) :
  ∃ Continuous F : Y × I → E, p ∘ F = f ∧ (fun y => F (y, 0)) = F₀ := by 
    sorry
