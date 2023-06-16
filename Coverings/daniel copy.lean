import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Covering
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Topology.UnitInterval
import Coverings.tony
import Coverings.lean3
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

variable {X Y Xt : Type _}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Xt]
variable {p : Xt → X} 
variable (x : X) (y : Y) (t : I)

open Function Set

namespace IsCoveringMap

variable (Y)
structure LiftingSituation (hp : IsCoveringMap p) where
  F : I × Y → X
  hF : Continuous F
  F0t : Y → Xt
  hF0t : Continuous F0t
  -- `F₀` is a lift of `f (⬝, 0)`
  f_eq_p_F0t : ∀ y, F (0, y) = p (F0t y)

variable {Y}
variable (hp : IsCoveringMap p) (Φ : hp.LiftingSituation Y)

lemma aux (y : Y) (hy : y ∈ U) : (0, y) ∈ (univ ×ˢ U) := by
  apply mk_mem_prod _ hy
  apply mem_univ

-- rearrange the data of the theorem `test`
theorem test2 (y : Y) : 
    ∃ U ∈ 𝓝 y, ∃ Ft : ContinuousMap ((univ : Set I) ×ˢ U) Xt, 
    (∀ (y' : Y) (hy' : y' ∈ U), Ft ⟨(0, y'), aux y' hy'⟩ = Φ.F0t y') 
    ∧ ∀ z : (univ : Set I) ×ˢ U, Φ.F z = p (Ft z) := by
  have data : ∀ y : Y, ∃ U ∈ 𝓝 y, ∃ Ft : I → Y → Xt,
  ContinuousOn (uncurry Ft) (univ ×ˢ U) 
  ∧ EqOn (Ft 0) Φ.F0t U 
  ∧ EqOn Φ.F (p ∘ uncurry Ft) (univ ×ˢ U) := by
    apply test Y X Xt p hp (curry Φ.F) Φ.hF Φ.F0t Φ.hF0t _
    ext y
    exact Φ.f_eq_p_F0t y
  specialize data y
  rcases data with ⟨U, hU, ⟨Ft, hFt, eq1, eq2⟩⟩
  use U
  constructor
  . exact hU
  . let Ft' : ContinuousMap ((univ : Set I) ×ˢ U) Xt := by
      let Ft' : (univ : Set I) ×ˢ U → Xt := restrict ((univ : Set I) ×ˢ U) (uncurry Ft)
      have hFt' : Continuous Ft' := by
        rw [continuousOn_iff_continuous_restrict] at hFt
        exact hFt
      exact ⟨Ft', hFt'⟩
    use Ft'
    constructor
    . rintro y' hy'
      rw [← restrict_eq_restrict_iff] at eq1
      rw [restrict_eq_iff] at eq1
      specialize eq1 y' hy'
      dsimp
      rw [eq1]
      rfl
    . intro z
      rw [← restrict_eq_restrict_iff] at eq2
      rw [restrict_eq_iff] at eq2
      specialize eq2 z (Subtype.mem z)
      rw [eq2]
      rfl

def tube (y : Y) : Set Y := (hp.test2 Φ y).choose

lemma tubes_nhds (y : Y) : hp.tube Φ y ∈ 𝓝 y := (hp.test2 Φ y).choose_spec.1

noncomputable def nhd_lift (y : Y) : ContinuousMap ((univ : Set I) ×ˢ hp.tube Φ y) Xt :=
  (hp.test2 Φ y).choose_spec.2.choose

lemma extends_F₀ (y : Y) (y' : Y) (hy' : y' ∈ hp.tube Φ y) :
    hp.nhd_lift Φ y ⟨(0, y'), aux y' hy'⟩ = Φ.F0t y' :=
  (hp.test2 Φ y).choose_spec.2.choose_spec.1 y' hy'

lemma is_lift (y : Y) (z : (univ : Set I) ×ˢ hp.tube Φ y) :
    Φ.F z = p (hp.nhd_lift Φ y z) :=
  (hp.test2 Φ y).choose_spec.2.choose_spec.2 z

noncomputable def liftToCoveringSpace : ContinuousMap (I × Y) Xt :=
ContinuousMap.liftCover
  (fun y ↦ ((univ : Set I) ×ˢ hp.tube Φ y))
  (hp.nhd_lift Φ)
  ( by
    rintro y₁ y₂ x hxi hxj
    let U := (univ : Set I) ×ˢ hp.tube Φ y₁ ∩ (univ : Set I) ×ˢ hp.tube Φ y₂
    sorry
    -- apply uniqueness_of_homotopy_lifting _ _ hp (hp.nhd_lift Φ y₁) (hp.nhd_lift Φ y₂) 
  )
  sorry

theorem homotopy_lift₁ : p ∘ (hp.liftToCoveringSpace Φ) = Φ.F := by
  sorry

theorem homotopy_lift₂ (y : Y) : hp.liftToCoveringSpace Φ (0, y) = Φ.F0t y := by
  sorry

-- repackage:
-- make a `LiftingSituation` inside this proof and then pull in the constructions above
theorem homotopy_lift (hf : Continuous f) (hp : IsCoveringMap p) (hF₀ : Continuous F₀)
  (h : ∀ (y : Y), f (0, y) = p (F₀ y))
    : ∃ F : I × Y → Xt, Continuous F ∧ p ∘ F = f ∧ (fun y ↦ F (0, y)) = F₀ := by
  let Φ : LiftingSituation Y hp := {
    F := f
    hF := hf
    F0t := F₀ 
    hF0t := hF₀
    f_eq_p_F0t := h      
  }
  use liftToCoveringSpace hp Φ
  exact ⟨(liftToCoveringSpace hp Φ).2, homotopy_lift₁ hp Φ, by
    ext y
    exact homotopy_lift₂ hp Φ y⟩ 

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

