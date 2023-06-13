import Mathlib.Topology.Covering
import Mathlib.Topology.Connected 
import Mathlib.Topology.Basic
import Mathlib.Topology.IsLocallyHomeomorph
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.SetTheory.Cardinal.Basic 
import Mathlib.Topology.LocallyConstant.Basic

open Cardinal Topology

set_option autoImplicit false

namespace IsCoveringMap

variable {E X : Type _} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s t: Set X)

-- If f is a bijective covering map then it is a homeomorphism
noncomputable def toHomeomorph (hf : IsCoveringMap f)
(h : Function.Bijective f) : Homeomorph E X := 
  Homeomorph.homeomorphOfContinuousOpen (Equiv.ofBijective f h ) (IsCoveringMap.continuous hf) (IsCoveringMap.isOpenMap hf)

-- homeomorph.homeomorph_of_continuous_open (equiv.of_bijective f h) hf.continuous hf.is_open_map
lemma is_locally_constant_card (hf : IsCoveringMap f) :
  IsLocallyConstant (fun x => #(f ⁻¹' {x})) := by sorry
-- (is_locally_constant.iff_exists_open _).2 $ λ x, let ⟨t, ht⟩ := (hf x).2 in
--   ⟨_, t.open_base_set, ht, λ y hy, (t.preimage_singleton_homeomorph hy).to_equiv.cardinal_eq⟩


lemma clopen_set_intersect_connected_components_whole_set (Y: Type _) [TopologicalSpace Y]
  (S : Set Y) (hS : IsClopen S) (w : ∀ x : Y, ∃ y ∈ connectedComponent x, y ∈ S) :
  S = Set.univ := by 
  apply Set.eq_univ_of_forall 
  intro x 
  specialize w x 
  cases' w with y h1
  have con_same : connectedComponent x = connectedComponent y := connectedComponent_eq (h1.1)
  have y_con: connectedComponent y ⊆ S := by 
    apply IsClopen.connectedComponent_subset
    exact hS
    exact h1.2
  have con_sub : connectedComponent x ⊆ S := by 
    rw[con_same] 
    exact y_con
  have x_in_con : x ∈ connectedComponent x := mem_connectedComponent 
  exact con_sub x_in_con 
-- set.eq_univ_of_forall $ λ x, let ⟨y, hy, h⟩ := w x in
--   hS.connected_component_subset h (connected_component_eq hy ▸ mem_connected_component)


theorem is_open_inter_of_coe_preim' (hs : IsOpen s)
  (h : IsOpen ((Subtype.val : s → X) ⁻¹' t)) : IsOpen (t ∩ s) := by sorry

lemma is_open_of_is_open_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
    (hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ 𝓝 x), IsOpen ((Subtype.val : U → Y) ⁻¹' A)) : IsOpen A := by
  sorry

lemma is_closed_of_is_closed_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ 𝓝 x), IsClosed ((Subtype.val : U → Y) ⁻¹' A)) : IsClosed A := by sorry

lemma is_clopen_of_is_clopen_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ 𝓝 x), IsClopen ((Subtype.val : U → Y) ⁻¹' A)) : IsClopen A := by sorry 


theorem clopen_equalizer_of_discrete (Y:Type _) [TopologicalSpace Y]
  [DiscreteTopology Y] {h g : X → Y} (hf : Continuous h) (hg : Continuous g) :
  IsClopen {x : X | h x = g x} := by sorry


lemma tautology : true := rfl

theorem uniqueness_of_homotopy_lifting (Y : Type _) [TopologicalSpace Y] (hf : IsCoveringMap f)
  (H₁ H₂ : ContinuousMap Y E) (h : f ∘ H₁ = f ∘ H₂)
  (hC : ∀ x : Y, ∃ y ∈ connectedComponent x, H₁ y = H₂ y) :
  H₁ = H₂ := by sorry 

-- begin
--   refine fun_like.ext H₁ H₂ (set.eq_univ_iff_forall.mp
--     (clopen_set_intersect_connected_components_whole_set _ _
--     (is_clopen_of_is_clopen_coe _ _ (λ x, _)) hC)),
--   let t := (hf (f (H₁ x))).to_trivialization,
--   let U := (f ∘ H₁) ⁻¹' t.base_set,
--   refine ⟨U, (t.open_base_set.preimage (hf.continuous.comp H₁.continuous)).mem_nhds
--     ((hf (f (H₁ x)))).mem_to_trivialization_base_set, _⟩,
--   change is_clopen {y : U | H₁ y = H₂ y},
--   have h0 : ∀ y : U, f (H₁ y) = f (H₂ y) := λ y, congr_fun h y,
--   have h1 : ∀ y : U, f (H₁ y) ∈ t.base_set := subtype.prop,
--   have h2 : ∀ y : U, f (H₂ y) ∈ t.base_set := λ y, h0 y ▸ h1 y,
--   have key : ∀ y : U, H₁ y = H₂ y ↔ (t (H₁ y)).2 = (t (H₂ y)).2,
--   { refine λ y, ⟨congr_arg (prod.snd ∘ t), λ m, _⟩,
--     have h0 : f (H₁ y) = f (H₂ y) := congr_fun h y,
--     rw [←t.coe_fst' (h1 y), ←t.coe_fst' (h2 y)] at h0,
--     refine t.inj_on (t.mem_source.mpr (h1 y)) (t.mem_source.mpr (h2 y)) (prod.ext h0 m) },
--   simp_rw [key],
--   haveI := (hf (f (H₁ x))).1,
--   simp only [←t.mem_source] at h1 h2,
--   refine clopen_equalizer_of_discrete
--     (continuous_snd.comp (t.continuous_to_fun.comp_continuous (H₁.2.comp continuous_subtype_coe) h1))