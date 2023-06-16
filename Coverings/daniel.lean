--import Mathlib.Topology.Basic
--import Mathlib.Topology.ContinuousOn
--import Mathlib.Topology.Covering
--import Mathlib.Topology.LocalHomeomorph
--import Mathlib.Topology.UnitInterval
import Coverings.tony
--import Coverings.lean3
import Coverings.Uniqueness
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
variable {p : E → X} 
variable (x : X) (y : Y) (t : I)

open Function Set

namespace IsCoveringMap

variable (Y)
structure LiftingSituation (hp : IsCoveringMap p) where
  f : Y × I → X
  hf : Continuous f
  F₀ : Y → E
  hF₀ : Continuous F₀
  -- `F₀` is a lift of `f (⬝, 0)`
  f_eq_p_F₀ : ∀ y, f (y, 0) = p (F₀ y)

variable {Y}
variable (hp : IsCoveringMap p) (Φ : hp.LiftingSituation Y)

lemma aux (y : Y) (hy : y ∈ U) : (y, 0) ∈ (U ×ˢ univ) := by
  apply mk_mem_prod hy
  apply mem_univ

-- rearrange the data of the theorem `test`
theorem test2 (y : Y) : 
    ∃ U ∈ 𝓝 y, ∃ Ft : ContinuousMap (U ×ˢ (univ : Set I)) E, 
    (∀ (y' : Y) (hy' : y' ∈ U), Ft ⟨(y', 0), aux y' hy'⟩ = Φ.F₀ y') 
    ∧ ∀ z : U ×ˢ (univ : Set I), Φ.f z = p (Ft z) :=
  sorry 

def tube (y : Y) : Set Y := (hp.test2 Φ y).choose

lemma tubes_nhds (y : Y) : hp.tube Φ y ∈ 𝓝 y := (hp.test2 Φ y).choose_spec.1

noncomputable def nhd_lift (y : Y) : ContinuousMap (hp.tube Φ y ×ˢ (univ : Set I)) E :=
  (hp.test2 Φ y).choose_spec.2.choose

lemma extends_F₀ (y : Y) (y' : Y) (hy' : y' ∈ hp.tube Φ y) :
    hp.nhd_lift Φ y ⟨(y', 0), aux y' hy'⟩ = Φ.F₀ y' :=
  (hp.test2 Φ y).choose_spec.2.choose_spec.1 y' hy'

lemma is_lift (y : Y) (z : hp.tube Φ y ×ˢ (univ : Set I)) :
    Φ.f z = p (hp.nhd_lift Φ y z) :=
  (hp.test2 Φ y).choose_spec.2.choose_spec.2 z

noncomputable def liftToCoveringSpace : ContinuousMap (Y × I) E :=
ContinuousMap.liftCover
  (fun y ↦ (hp.tube Φ y ×ˢ (univ : Set I)))
  (hp.nhd_lift Φ)
  sorry
  sorry

theorem homotopy_lift₁ : p ∘ (hp.liftToCoveringSpace Φ) = Φ.f := sorry

theorem homotopy_lift₂ (y : Y) : hp.liftToCoveringSpace Φ (y, 0) = Φ.F₀ y := sorry

-- repackage:
-- make a `LiftingSituation` inside this proof and then pull in the constructions above
theorem homotopy_lift (hf : Continuous f) (hp : IsCoveringMap p) (hF₀ : Continuous F₀) :
    ∃ F : Y × I → E, Continuous F ∧ p ∘ F = f ∧ (fun y ↦ F (y, 0)) = F₀ :=
  sorry


#exit -- probably don't need the rest

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

lemma lift_from_point (y : Y) (s : Set I) (hso : IsOpen s) (hsc : IsConnected s)
  (triv : Trivialization (p ⁻¹' {f (y, t)}) p) (htriv : f '' ({y} ×ˢ s) ⊆ triv.baseSet)
  (pt : s) (Fpt : E) : ∃ F : s → E, Continuous F ∧ (F pt = Fpt) := by sorry

