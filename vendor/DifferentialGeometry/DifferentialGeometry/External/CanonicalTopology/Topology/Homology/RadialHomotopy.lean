module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

/-! # The original punctured normed space and its same unit sphere -/

noncomputable section

open CategoryTheory ContinuousMap Set Metric
open scoped Topology

universe u

namespace DifferentialGeometry.Topology

/-- Projection from a positive-radius product is a homotopy equivalence
whose section uses radius EXACTLY one. The same radius is interpolated
linearly, remaining positive throughout the homotopy. -/
def positiveRadiusProdHomotopyEquiv (X : Type u) [TopologicalSpace X] :
    (X × Ioi (0 : ℝ)) ≃ₕ X where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := ⟨fun x => (x, (⟨1, by norm_num⟩ : Ioi (0 : ℝ))), by fun_prop⟩
  left_inv := by
    refine ⟨⟨⟨fun p => (p.2.1, ⟨(1 - p.1.val) • (1 : ℝ) + p.1.val • p.2.2.val, ?_⟩), ?_⟩, ?_, ?_⟩⟩
    · exact (show Convex ℝ (Ioi (0 : ℝ)) from convex_Ioi 0) (by norm_num) p.2.2.property
        (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 _)
    · fun_prop
    · intro x
      refine Prod.ext ?_ ?_
      · rfl
      · apply Subtype.ext
        simp
    · intro x
      refine Prod.ext ?_ ?_
      · rfl
      · apply Subtype.ext
        simp
  right_inv := Homotopic.refl _

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The SAME actual radial normalization retracts the original punctured
space onto its unit sphere, with the unit-radius inclusion as inverse. -/
def puncturedSpaceSphereHomotopyEquiv : ({0}ᶜ : Set E) ≃ₕ sphere (0 : E) 1 :=
  (homeomorphUnitSphereProd E).toHomotopyEquiv.trans
    (positiveRadiusProdHomotopyEquiv (sphere (0 : E) 1))

/-- The forward map is the actual radial normalization of the original point. -/
theorem puncturedSpaceSphereHomotopyEquiv_apply (x : ({0}ᶜ : Set E)) :
    ((puncturedSpaceSphereHomotopyEquiv E).toFun x : E) = ‖x.val‖⁻¹ • x.val :=
  homeomorphUnitSphereProd_apply_fst_coe E x

/-- The inverse is the SAME original sphere inclusion into the punctured space. -/
theorem puncturedSpaceSphereHomotopyEquiv_inv_apply (x : sphere (0 : E) 1) :
    ((puncturedSpaceSphereHomotopyEquiv E).invFun x : E) = x.val := by
  change (1 : ℝ) • x.val = x.val
  exact one_smul ℝ x.val

/-- The resulting isomorphism concerns the ORIGINAL singular homology
groups, and is induced by the same radial normalization. -/
def integralPuncturedSpaceSphereHomologyEquiv (n : ℕ) :
    integralSingularHomology n ({0}ᶜ : Set E) ≃ₗ[ℤ] integralSingularHomology n (sphere (0 : E) 1) :=
  integralSingularHomologyHomotopyEquiv n (puncturedSpaceSphereHomotopyEquiv E)

end DifferentialGeometry.Topology
