module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalTop

@[expose] public section

section

noncomputable section

open CategoryTheory ContinuousMap Metric Module Set

universe u

namespace DifferentialGeometry.Topology

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def integralEuclideanLocalTopGenerator (n : ℕ) (hd : finrank ℝ E = n + 2) (x : E) :
    integralLocalHomology (n + 2) x :=
  (integralEuclideanLocalTopEquiv E n hd x).symm 1


theorem integralEuclideanLocalTopGenerator_coordinate (n : ℕ) (hd : finrank ℝ E = n + 2)
    (x : E) :
    integralEuclideanLocalTopEquiv E n hd x (integralEuclideanLocalTopGenerator E n hd x) = 1 :=
  (integralEuclideanLocalTopEquiv E n hd x).apply_symm_apply 1


theorem integralEuclideanLocalTopGenerator_zsmul_bijective (n : ℕ)
    (hd : finrank ℝ E = n + 2) (x : E) :
    Function.Bijective (fun z : ℤ => z • integralEuclideanLocalTopGenerator E n hd x) := by
  have hfun : (fun z : ℤ => z • integralEuclideanLocalTopGenerator E n hd x) =
      ⇑(integralEuclideanLocalTopEquiv E n hd x).symm := by
    funext z
    apply (integralEuclideanLocalTopEquiv E n hd x).injective
    rw [map_zsmul, integralEuclideanLocalTopGenerator_coordinate, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (integralEuclideanLocalTopEquiv E n hd x).symm.bijective


theorem integralEuclideanLocalTopGenerator_ne_zero (n : ℕ) (hd : finrank ℝ E = n + 2) (x : E) :
    integralEuclideanLocalTopGenerator E n hd x ≠ 0 := by
  intro h
  have hh := congrArg (integralEuclideanLocalTopEquiv E n hd x) h
  rw [integralEuclideanLocalTopGenerator_coordinate, map_zero] at hh
  exact one_ne_zero hh


def integralManifoldLocalTopGenerator (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralLocalHomology (n + 2) x :=
  (integralManifoldLocalTopEquiv E n hd M x).symm 1


theorem integralManifoldLocalTopGenerator_coordinate (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralManifoldLocalTopEquiv E n hd M x (integralManifoldLocalTopGenerator E n hd M x) = 1 :=
  (integralManifoldLocalTopEquiv E n hd M x).apply_symm_apply 1


theorem integralManifoldLocalTopGenerator_zsmul_bijective (n : ℕ)
    (hd : finrank ℝ E = n + 2) (M : Type u) [TopologicalSpace M] [T1Space M]
    [ChartedSpace E M] (x : M) :
    Function.Bijective (fun z : ℤ => z • integralManifoldLocalTopGenerator E n hd M x) := by
  have hfun : (fun z : ℤ => z • integralManifoldLocalTopGenerator E n hd M x) =
      ⇑(integralManifoldLocalTopEquiv E n hd M x).symm := by
    funext z
    apply (integralManifoldLocalTopEquiv E n hd M x).injective
    rw [map_zsmul, integralManifoldLocalTopGenerator_coordinate, smul_eq_mul, mul_one,
      LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact (integralManifoldLocalTopEquiv E n hd M x).symm.bijective


theorem integralManifoldLocalTopGenerator_ne_zero (n : ℕ) (hd : finrank ℝ E = n + 2)
    (M : Type u) [TopologicalSpace M] [T1Space M] [ChartedSpace E M] (x : M) :
    integralManifoldLocalTopGenerator E n hd M x ≠ 0 := by
  intro h
  have hh := congrArg (integralManifoldLocalTopEquiv E n hd M x) h
  rw [integralManifoldLocalTopGenerator_coordinate, map_zero] at hh
  exact one_ne_zero hh


end DifferentialGeometry.Topology

end

end
