module

public import SphereSixComplex.Topology.StandardSpherePunctures
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Relative five-cube contraction in a punctured six-sphere

A generalized loop in `S⁶` whose image avoids one point can be contracted relative to the cube
boundary.  Stereographic projection identifies the punctured sphere with `ℝ⁶`; affine contraction
there to the loop basepoint fixes every boundary value throughout the homotopy.

This is the final topological step in the dimension-avoidance route to `π₅(S⁶) = 0`: it remains to
replace an arbitrary five-cube loop by a boundary-preserving approximation which omits a point.
-/

@[expose] public section

noncomputable section

open ContinuousMap Set Topology
open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

private abbrev SixSphereFiveCube := I^(Fin 5)

/-- A five-cube loop in the six-sphere which omits one point is nullhomotopic relative to the cube
boundary. -/
public theorem fiveCubeGenLoop_homotopic_const_of_avoids
    {x v : SixSphere} (p : Ω^ (Fin 5) SixSphere x)
    (hp : ∀ a, p a ≠ v) :
    GenLoop.Homotopic p
      (_root_.GenLoop.const : Ω^ (Fin 5) SixSphere x) := by
  let a₀ : SixSphereFiveCube := fun _ ↦ 0
  have ha₀ : a₀ ∈ Cube.boundary (Fin 5) := by
    exact ⟨0, Or.inl rfl⟩
  have hxv : x ≠ v := by
    intro hxv
    apply hp a₀
    rw [_root_.GenLoop.boundary p a₀ ha₀, hxv]
  let Xv : ({v}ᶜ : Set SixSphere) := ⟨x, by simpa using hxv⟩
  let q : C(SixSphereFiveCube, ({v}ᶜ : Set SixSphere)) :=
    ⟨fun a ↦ ⟨p a, by simpa using hp a⟩,
      continuous_induced_rng.mpr p.1.continuous⟩
  let e := puncturedStandardSphereHomeomorph 5 v
  let K : p.1.HomotopyRel
      (_root_.GenLoop.const : Ω^ (Fin 5) SixSphere x).1
      (Cube.boundary (Fin 5)) := {
    toFun := fun z ↦
      (e.symm (AffineMap.lineMap (e (q z.2)) (e Xv) (z.1 : ℝ))).1
    continuous_toFun := by
      dsimp [AffineMap.lineMap_apply]
      fun_prop
    map_zero_left := by
      intro a
      change (e.symm (AffineMap.lineMap (e (q a)) (e Xv) (0 : ℝ))).1 = p a
      simp [q]
    map_one_left := by
      intro a
      change (e.symm (AffineMap.lineMap (e (q a)) (e Xv) (1 : ℝ))).1 = x
      simp [Xv]
    prop' := by
      intro t a ha
      change (e.symm (AffineMap.lineMap (e (q a)) (e Xv) (t : ℝ))).1 = p a
      have hpa : p a = x := _root_.GenLoop.boundary p a ha
      have hq : q a = Xv := by
        apply Subtype.ext
        exact hpa
      rw [hq, AffineMap.lineMap_same]
      simp [Xv, hpa]
    }
  exact ⟨K⟩

end SphereSixComplex
