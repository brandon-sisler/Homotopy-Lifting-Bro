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
`IsCoveringMap (f : E → X)` : `∀ x, IsEvenlyCovered (f x) (f ⁻¹' {x})`

`∀ᶠ y ∈ 𝓝 x, P y` : exists a nbhd `U` of `x` such that `y ∈ U → P y`

Theorems:
`toTrivialization` : gets local trivialization above a point from a covering map
`IsCompact.elim_finite_subcover` : reduces open cover to finite cover

`isCompact_singleton` : set of a single point is compact
`isCompact_prod` : product of compact sets is compact
-/

variable {X Y E : Type _}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
variable (f : Y × I → X) (p : E → X) (F₀ : Y → E)
variable (hf : Continuous f) (hp : IsCoveringMap p)
variable (x : X) (y : Y) (t : I)

lemma nbhd_in_trivialization (y : Y) (t : I) :
  ∃ triv : Trivialization (p ⁻¹' {f (y, t)}) p, ∃ Nyt ∈ 𝓝 (y, t), f '' Nyt ⊆ triv.baseSet := by
    -- find the trivialization
    specialize hp <| f (y, t)
    let triv : Trivialization (p ⁻¹' {f (y, t)}) p := by
      apply IsEvenlyCovered.toTrivialization hp
    use triv
    -- let U : Set (X) := triv.baseSet
    use f ⁻¹' triv.baseSet
    constructor
    . rw [mem_nhds_iff]
      use f ⁻¹' triv.baseSet
      constructor
      . rfl
      . constructor
        . exact IsOpen.preimage hf triv.open_baseSet
        . rw [Set.mem_preimage]
          exact IsEvenlyCovered.mem_toTrivialization_baseSet hp
    . exact Set.image_preimage_subset f triv.baseSet

lemma lift_from_point (s : Set I) (hso : IsOpen s) (hsc : IsConnected s) (pt : s) (Fpt : E)
   : ∃ F : s → E, Continuous F ∧ (F pt = Fpt) := by
    sorry

theorem homotopy_lift (hf : Continuous f) (hp : IsCoveringMap p) (hF₀ : Continuous F₀) :
  ∃ F : Y × I → E, Continuous F ∧ p ∘ F = f ∧ (fun y ↦ F (y, 0)) = F₀ := sorry
