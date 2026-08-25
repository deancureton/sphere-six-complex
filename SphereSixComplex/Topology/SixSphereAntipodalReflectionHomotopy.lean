module

public import SphereSixComplex.Topology.OrientedSmoothHomotopySphere
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# An explicit reflection model for the six-sphere antipodal map

In seven ambient coordinates, the antipodal map is homotopic through orthogonal maps to the
reflection which negates only coordinate zero.  The other six signs are removed in three planar
rotation blocks.  This is a concrete geometric reduction of the antipodal degree calculation.
-/

@[expose] public section

noncomputable section

open ContinuousMap Set

namespace SphereSixComplex

/-- The ambient coordinate reflection which negates coordinate zero. -/
public noncomputable def sixSphereCoordinateReflectionAmbient
    (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 7) :=
  WithLp.toLp 2 ![-x 0, x 1, x 2, x 3, x 4, x 5, x 6]

/-- Simultaneously rotate the coordinate planes `(1,2)`, `(3,4)`, and `(5,6)`, while negating
coordinate zero.  At angle `π` this is the antipodal map; at angle zero it is coordinate
reflection. -/
public noncomputable def sixSphereAntipodalReflectionRotationAmbient
    (t : unitInterval) (x : EuclideanSpace ℝ (Fin 7)) :
    EuclideanSpace ℝ (Fin 7) := by
  let θ : ℝ := Real.pi * (1 - (t : ℝ))
  exact WithLp.toLp 2 ![
    -x 0,
    Real.cos θ * x 1 - Real.sin θ * x 2,
    Real.sin θ * x 1 + Real.cos θ * x 2,
    Real.cos θ * x 3 - Real.sin θ * x 4,
    Real.sin θ * x 3 + Real.cos θ * x 4,
    Real.cos θ * x 5 - Real.sin θ * x 6,
    Real.sin θ * x 5 + Real.cos θ * x 6]

public theorem sixSphereAntipodalReflectionRotationAmbient_norm
    (t : unitInterval) (x : EuclideanSpace ℝ (Fin 7)) :
    ‖sixSphereAntipodalReflectionRotationAmbient t x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ]
  simp [sixSphereAntipodalReflectionRotationAmbient]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi - Real.pi * (t : ℝ))]

@[simp]
public theorem sixSphereAntipodalReflectionRotationAmbient_zero
    (x : EuclideanSpace ℝ (Fin 7)) :
    sixSphereAntipodalReflectionRotationAmbient 0 x = -x := by
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [sixSphereAntipodalReflectionRotationAmbient]

@[simp]
public theorem sixSphereAntipodalReflectionRotationAmbient_one
    (x : EuclideanSpace ℝ (Fin 7)) :
    sixSphereAntipodalReflectionRotationAmbient 1 x =
      sixSphereCoordinateReflectionAmbient x := by
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [sixSphereAntipodalReflectionRotationAmbient,
    sixSphereCoordinateReflectionAmbient]

public theorem continuous_sixSphereAntipodalReflectionRotationAmbient :
    Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 7) ↦
      sixSphereAntipodalReflectionRotationAmbient p.1 p.2) := by
  rw [← (EuclideanSpace.equiv (Fin 7) ℝ).toHomeomorph.comp_continuous_iff]
  apply continuous_pi
  intro i
  fin_cases i <;> simp [sixSphereAntipodalReflectionRotationAmbient] <;> fun_prop

/-- Coordinate reflection restricted to the unit six-sphere. -/
public noncomputable def sixSphereCoordinateReflectionMap : C(SixSphere, SixSphere) where
  toFun x := ⟨sixSphereCoordinateReflectionAmbient x.1, by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [← sixSphereAntipodalReflectionRotationAmbient_one,
      sixSphereAntipodalReflectionRotationAmbient_norm]
    simpa only [Metric.mem_sphere, dist_zero_right] using x.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h : Continuous (fun x : SixSphere ↦
        sixSphereAntipodalReflectionRotationAmbient 1 x.1) :=
      continuous_sixSphereAntipodalReflectionRotationAmbient.comp
        ((continuous_const : Continuous (fun _ : SixSphere ↦ (1 : unitInterval))).prodMk
          continuous_subtype_val)
    exact h.congr fun x ↦
      sixSphereAntipodalReflectionRotationAmbient_one x.1

@[simp]
public theorem sixSphereCoordinateReflectionMap_apply (x : SixSphere) :
    (sixSphereCoordinateReflectionMap x : EuclideanSpace ℝ (Fin 7)) =
      sixSphereCoordinateReflectionAmbient x.1 :=
  rfl

public theorem sixSphereCoordinateReflectionAmbient_involutive :
    Function.Involutive sixSphereCoordinateReflectionAmbient := by
  intro x
  apply (EuclideanSpace.equiv (Fin 7) ℝ).injective
  funext i
  fin_cases i <;> simp [sixSphereCoordinateReflectionAmbient]

/-- Coordinate reflection is a self-homeomorphism of the unit six-sphere. -/
public noncomputable def sixSphereCoordinateReflectionHomeomorph :
    SixSphere ≃ₜ SixSphere where
  toFun := sixSphereCoordinateReflectionMap
  invFun := sixSphereCoordinateReflectionMap
  left_inv x := by
    apply Subtype.ext
    exact sixSphereCoordinateReflectionAmbient_involutive x.1
  right_inv x := by
    apply Subtype.ext
    exact sixSphereCoordinateReflectionAmbient_involutive x.1
  continuous_toFun := sixSphereCoordinateReflectionMap.continuous
  continuous_invFun := sixSphereCoordinateReflectionMap.continuous

@[simp]
public theorem sixSphereCoordinateReflectionHomeomorph_apply (x : SixSphere) :
    sixSphereCoordinateReflectionHomeomorph x =
      sixSphereCoordinateReflectionMap x :=
  rfl

/-- The analytic antipodal map is explicitly homotopic, through norm-preserving ambient
rotations, to reflection in coordinate zero. -/
public noncomputable def sixSphereAntipodalHomotopyToCoordinateReflection :
    ContinuousMap.Homotopy
      OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun
      sixSphereCoordinateReflectionMap where
  toFun p := ⟨sixSphereAntipodalReflectionRotationAmbient p.1 p.2.1, by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [sixSphereAntipodalReflectionRotationAmbient_norm]
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_sixSphereAntipodalReflectionRotationAmbient.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  map_zero_left x := by
    apply Subtype.ext
    simp
  map_one_left x := by
    apply Subtype.ext
    simp

/-- The corresponding proposition-level homotopy, ready for homology invariance. -/
public theorem sixSphere_antipodal_homotopic_coordinateReflection :
    OrientedMarkedSmoothHomotopySixSphere.antipodalMarking.toFun.Homotopic
      sixSphereCoordinateReflectionMap :=
  ⟨sixSphereAntipodalHomotopyToCoordinateReflection⟩

end SphereSixComplex
