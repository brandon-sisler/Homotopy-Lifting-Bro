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

#check Inducing.isOpen_iff
#check Subtype.preimage_val_eq_preimage_val_iff

theorem is_open_inter_of_coe_preim (hs : IsOpen s)
  (h : IsOpen ((Subtype.val : s → X) ⁻¹' t)) : IsOpen (t ∩ s) := by sorry
-- let ⟨a, b, c⟩ := inducing_coe.is_open_iff.mp h in
--   subtype.preimage_coe_eq_preimage_coe_iff.mp c ▸ b.inter hs


#check mem_nhds_iff
#check Set.inter_subset_left
#check IsOpen.preimage
#check is_open_inter_of_coe_preim 
#check isOpen_iff_forall_mem_open
lemma is_open_of_is_open_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
    (hA : ∀ x : Y, ∃ (U : Set Y) (hU : U ∈ 𝓝 x), IsOpen ((Subtype.val : U → Y) ⁻¹' A)) : IsOpen A := by 

    rw[isOpen_iff_forall_mem_open] 
    intro x 
    specialize hA x 
    intro xa 
    

-- is_open_iff_forall_mem_open.mpr (λ x hx, let ⟨U, hU1, hU2⟩ := hA x,
    -- ⟨V, hV1, hV2, hV3⟩ := mem_nhds_iff.mp hU1 in ⟨A ∩ V, set.inter_subset_left A V,
    -- is_open_inter_of_coe_preim V A hV2 ((continuous_inclusion hV1).is_open_preimage _ hU2), hx, hV3⟩)

lemma is_closed_of_is_closed_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (_ : U ∈ 𝓝 x), IsClosed ((Subtype.val : U → Y) ⁻¹' A)) : IsClosed A := by 
  rw [← isOpen_compl_iff]
  apply is_open_of_is_open_coe 
  intro x 
  specialize hA x 
  cases' hA with hleft hright 
  cases' hright with h1 h2 
  use hleft 
  use h1 
  dsimp at h2 
  dsimp 
  rw [isOpen_compl_iff]
  exact h2   

lemma is_clopen_of_is_clopen_coe (Y:Type _) [TopologicalSpace Y] (A: Set Y)
(hA : ∀ x : Y, ∃ (U : Set Y) (_ : U ∈ 𝓝 x), IsClopen ((Subtype.val : U → Y) ⁻¹' A)) : IsClopen A := by
  have left : IsOpen A := by
    apply is_open_of_is_open_coe Y A 
    intro x 
    specialize hA x 
    cases' hA with hleft hright
    use hleft 
    cases' hright with hleft hright
    use hleft 
    exact hright.1 

  have right : IsClosed A := by
    apply is_closed_of_is_closed_coe Y A 
    intro x 
    specialize hA x 
    cases' hA with hleft hright
    use hleft 
    cases' hright with hleft hright
    use hleft 
    exact hright.2 

  exact ⟨left, right ⟩ 

theorem clopen_equalizer_of_discrete (Y:Type _) [TopologicalSpace Y]
  [DiscreteTopology Y] {h g : X → Y} (hf : Continuous h) (hg : Continuous g) :
  IsClopen {x : X | h x = g x} := by 
  have diag_cl : IsClopen (Set.diagonal Y) := by 
    apply isClopen_discrete
  have con_map : Continuous (fun x => (g x, h x)) := by
    apply continuous_prod_mk.mpr 
    constructor 
    exact hg 
    exact hf 
  have : IsClopen (((fun x => (g x, h x))) ⁻¹' (Set.diagonal Y)) := by
    apply IsClopen.preimage
    exact diag_cl
    exact con_map
  have re : (fun x => (g x, h x)) ⁻¹' Set.diagonal Y = {x |h x = g x} := by 
    ext n  
    simp
    tauto 
  rw[←re]
  exact this

lemma tautology : true := rfl

theorem uniqueness_of_homotopy_lifting (Y : Type _) [TopologicalSpace Y] (hf : IsCoveringMap f)
  (H₁ H₂ : ContinuousMap Y E) (h : f ∘ H₁ = f ∘ H₂)
  (hC : ∀ x : Y, ∃ y ∈ connectedComponent x, H₁ y = H₂ y) :
  H₁ = H₂ := by 


/- Define S := {y ∈ Y ∣ H₁(y) = H₂(y)} -/
  let S:= {y:Y | H₁ y = H₂ y}
  

/- S is clopen proof Part 1 : by Lemma 1 it suffices to prove that U_y ∩ S is
clopen in U_y (where for y ∈ Y, F(y) ∈ X has evenly covered nbhd V_y by defn
of covering and U_y := F^{-1}(V_y)) -/

  have fCont: Continuous f:= by
    exact IsCoveringMap.continuous hf 

  have H1cont: Continuous H₁:= by
    exact ContinuousMap.continuous H₁ 

  have ClopenS : IsClopen S := by
    apply is_clopen_of_is_clopen_coe
    intro y
    specialize hf (f (H₁ y))
    rcases hf with ⟨DT,TrivN,xTrivN ⟩   --- x=f(H₁ y)
    use ((f∘ H₁)⁻¹' TrivN.baseSet)  
    have h1: ((f∘ H₁)⁻¹' TrivN.baseSet)∈ 𝓝 y:= by
      rw [IsOpen.mem_nhds_iff]
      exact xTrivN
      apply  Continuous.isOpen_preimage 
      exact Continuous.comp fCont H1cont
      exact TrivN.open_baseSet
    use h1
    simp only [Set.preimage_setOf_eq]
    sorry
    

--IsOpen.mem_nhds_iff {a : α} {s : Set α} (hs : IsOpen s) : s ∈ 𝓝 a ↔ a ∈ s 


   sorry
   



/- S is clopen proof Part 2(a) : U_y ∩ S = {z ∈ U_y ∣ H₁(z) = H₂(z)} -/



/- S is clopen proof Part 2(b) : ∃ discrete topological space D such that 
f⁻¹(V_y) ≅ V_y × D := by defn of covering -/



/- S is clopen proof Part 2(c) : {z ∈ U_y ∣ (proj_D ∘ H₁)(z) = (proj_D ∘ H₂)(z)} is clopen in U_y := 
by Lemma 2 -/



/- S is clopen proof Part 2(d) : {z ∈ U_y ∣ (proj_D ∘ H₁)(z) = (proj_D ∘ H₂)(z)} 
= {z ∈ U_y ∣ H₁(z) = H₂(z)} and {z ∈ U_y ∣ H₁(z) = H₂(z)} clopen by 2(c) and 
 -/



/- S is clopen proof Part 2(e) : S is clopen by Part 1 and Part 2(a) -/



/- Proof that S = Y using Lemma 3 -/
















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