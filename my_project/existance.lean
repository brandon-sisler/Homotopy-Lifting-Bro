/-
File for the existence of homotopy lifts:

# Statement
Given - a (continuous) map `F : Y × I → X`
      - a map `F_tilde : Y × {0} → X_tilde` lifting `F|Y ×{0}`
      
Then  - there is a (unique) map `F_tilde : Y × I → X_tilde` 
      - lifting F, i.e. `p ∘ F_tilde = F`
      - restricting to `F_tilde on Y × {0}`
-/

/-
# Proof Outline
1.  Start by constructing the lift in the neighborhood of a point `y₀ ∈ Y`:

2.  Since `F` is continuous, each point `(y₀, t) ∈ Y × I` has a product neighborhood
    `N_t × (a_t, b_t)` so that `F( N_t × (a_t, b_t) )` is contained in an `evenly covered`
    nbhd of `(y₀, t)`

3.  By compactness of `{y₀} × I`, finitely many `N_t × (a_t, b_t)` cover `{y₀} × I`

4.  Then we can choose a single neighborhood `N` and a partition `0 = t_0 < t_1 < ⋯ < t_m = 1`
    of `I` such that `F( N × [t_i, t_{i+1}] )` is contained in an `evenly covered U_i` 

5.  Assume inductively that `F_tilde` has been constructed on `N × [0, t_i]`, starting with
    the given `F_tilde` on `N × {0}`

6.  Since `F( N × [t_i, t_{i+1}] ) ⊆ U_i` by the even covering of `U_i` there is an
    `open U_i_tilde ⊆ X_tilde` with `p: U_i_tilde ≅ U_i` and `F_tilde (y₀ × t_i) ∈ U_i_tilde`

7.  After replacing `N` with a smaller neighborhood, we can assume `F_tilde (N × t_i) ⊆ U_i_tilde`
    (Restrict into the set `(F_tilde)⁻¹ (U_i_tilde)`)

8.  Define `F_tilde` on `N × [t_i, t_{i+1}]` by `p⁻¹ ∘ F` with `p⁻¹: U_i → U_i_tilde`

9.  After a finite number of steps we obtain `F_tilde : N × I → X_tilde`

10. Use uniqueness on the nbhds `N × {y₀}` for each point `y₀ ∈ Y` these agree on intersections

11. `F_tilde` is continuous since it is continuous on each `N × I`

-/

/-
# Concepts 

`Covering Map:` 
Given a space `X` a `covering map` consists of a space `X_tilde` and a map `p: X_tilde → X`
which satisfies the condition:

(*) `∀ x ∈ X, ∃ open nbhs U of x` s.t. `p⁻¹(U) = ⨆ V` is a union of disjoint open sets in `X_tilde`
    for which `p : V ≅ U`

Such a set `U` is called `evenly covered`
-/