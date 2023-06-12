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
Continuous f : f is globally continuous
ContinuousAt f a : f is continuous at the point a

Notation:
E is is the covering space of X - otherwise denoted tilde X
F is the lift of the map f
F₀ is the start of F, i.e. F₀ = F(y, 0)
-/

theorem homotopy_lift (Continuous F₀ : Y → E) : ∃ Continuous F : Y × I → E, 
  p ∘ F = f ∧ (fun y => F (y, t)) = F₀ := by 
    sorry