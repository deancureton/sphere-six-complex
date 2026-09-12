module

public import SphereSixComplex.Prerequisites.Geometry.EllipticCayleyHomeomorph
public import Mathlib.Geometry.Manifold.Complex
public import Mathlib.Geometry.Manifold.Diffeomorph

/-! # The natural complex manifold structure on the unit disc and the Cayley diffeomorphism -/

open scoped Manifold ComplexConjugate ContDiff

namespace SphereSixComplex

open Complex

noncomputable section

namespace ComplexUnitDisc

/-- The open embedding that equips the unit disc with its natural complex manifold structure. -/
public theorem isOpenEmbedding_coe :
    Topology.IsOpenEmbedding ((↑) : ComplexUnitDisc → ℂ) :=
  (isOpen_lt continuous_norm continuous_const).isOpenEmbedding_subtypeVal

public instance nonempty : Nonempty ComplexUnitDisc := ⟨ComplexUnitDisc.center⟩

/-- The complex chart on the open unit disc induced by its inclusion into `ℂ`. -/
public noncomputable instance chartedSpace : ChartedSpace ℂ ComplexUnitDisc :=
  isOpenEmbedding_coe.singletonChartedSpace


end ComplexUnitDisc

namespace UpperHalfPlane

/-- A holomorphic scalar-valued function on the upper half-plane is complex smooth of every
finite or infinite order. -/
public theorem contMDiff_of_mdifferentiable {f : UpperHalfPlane → ℂ} (hf : MDiff f)
    (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n f := by
  intro z
  rw [UpperHalfPlane.contMDiffAt_iff]
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) _root_.UpperHalfPlane.upperHalfPlaneSet :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  exact (hd.contDiffOn _root_.UpperHalfPlane.isOpen_upperHalfPlaneSet).contDiffAt
    (_root_.UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

public theorem contMDiff_cayleyToDisc (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (UpperHalfPlane.cayleyToDisc a) := by
  have hcomp : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (((↑) : ComplexUnitDisc → ℂ) ∘ UpperHalfPlane.cayleyToDisc a) := by
    change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (UpperHalfPlane.cayley a)
    exact contMDiff_of_mdifferentiable (UpperHalfPlane.mdifferentiable_cayley a) n
  exact hcomp.of_comp_isOpenEmbedding ComplexUnitDisc.isOpenEmbedding_coe

public theorem contMDiff_cayleyFromDisc (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (UpperHalfPlane.cayleyFromDisc a) := by
  have hval : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      ((↑) : ComplexUnitDisc → ℂ) :=
    contMDiff_isOpenEmbedding ComplexUnitDisc.isOpenEmbedding_coe
  have hcomp : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (((↑) : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.cayleyFromDisc a) := by
    change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun w : ComplexUnitDisc ↦ ((a : ℂ) - w.1 * conj (a : ℂ)) / (1 - w.1))
    exact (contMDiff_const.sub (hval.mul contMDiff_const)).div₀
      (contMDiff_const.sub hval) (by
        intro w h
        have hw : w.1 = 1 := (sub_eq_zero.mp h).symm
        have := w.2
        rw [hw] at this
        norm_num at this)
  exact hcomp.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe

/-- The Cayley homeomorphism is an actual biholomorphism for the natural disc manifold. -/
@[expose] public noncomputable def cayleyDiffeomorph (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc where
  toEquiv := (UpperHalfPlane.cayleyHomeomorph a).toEquiv
  contMDiff_toFun := contMDiff_cayleyToDisc a n
  contMDiff_invFun := contMDiff_cayleyFromDisc a n

end UpperHalfPlane

end

end SphereSixComplex
