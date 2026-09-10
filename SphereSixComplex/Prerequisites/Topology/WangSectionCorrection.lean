module

public import SphereSixComplex.Prerequisites.Topology.GeometricWangSection

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge.UnnormalizedCuspRadialClutchingData

/-- Adjust a Wang section by its coinvariant component so that a given map kills its lift. -/
public noncomputable def geometricSectionInMapKernel
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L) :
    P.GeometricSection where
  lift := S.lift - P.coinvariantsToTotal.comp
    (c.symm.toLinearMap.comp (f.comp S.lift))
  rightInverse := by
    apply LinearMap.ext
    intro z
    change P.totalToInvariants
      (S.lift z - P.coinvariantsToTotal (c.symm (f (S.lift z)))) = z
    rw [map_sub, P.exact_coinvariantsToTotal_totalToInvariants.apply_apply_eq_zero, sub_zero]
    exact DFunLike.congr_fun S.rightInverse z

/-- The adjusted Wang section is killed by a map whose restriction to coinvariants is the
specified coordinate equivalence. -/
public theorem geometricSectionInMapKernel_lift
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L)
    (h : f.comp P.coinvariantsToTotal = c.toLinearMap) :
    f.comp (geometricSectionInMapKernel P S c f).lift = 0 := by
  apply LinearMap.ext
  intro z
  change f (S.lift z - P.coinvariantsToTotal (c.symm (f (S.lift z)))) = 0
  rw [map_sub]
  have hi := DFunLike.congr_fun h (c.symm (f (S.lift z)))
  simp only [LinearMap.coe_comp, Function.comp_apply] at hi
  rw [hi]
  change f (S.lift z) - c (c.symm (f (S.lift z))) = 0
  rw [c.apply_symm_apply, sub_self]

/-- In the splitting defined by the adjusted section, a map is exactly its coinvariant
coordinate. -/
public theorem geometricSectionInMapKernel_map_eq_coinvariant
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L)
    (h : f.comp P.coinvariantsToTotal = c.toLinearMap) (x : Total) :
    f x = c ((P.totalLinearEquivCoinvariantsProdInvariantsOfSection
      (geometricSectionInMapKernel P S c f) x).1) := by
  let K := geometricSectionInMapKernel P S c f
  let T := P.totalLinearEquivCoinvariantsProdInvariantsOfSection K
  let y := T x
  have hx : x = T.symm y := (T.symm_apply_apply x).symm
  rw [hx, T.apply_symm_apply]
  have hinv : T.symm y = P.coinvariantsToTotal y.1 + K.lift y.2 := by rfl
  rw [hinv]
  rw [map_add]
  have hi := DFunLike.congr_fun h y.1
  simp only [LinearMap.coe_comp, Function.comp_apply] at hi
  have hs := DFunLike.congr_fun
    (geometricSectionInMapKernel_lift P S c f h) y.2
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] at hs
  rw [hi, hs, add_zero]
  rfl

/-- Normalize against the actual fiber map when it is invertible. -/
public noncomputable def geometricSectionInMapKernelIfBijective
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L) :
    P.GeometricSection := by
  classical
  exact if h : Function.Bijective (f.comp P.coinvariantsToTotal) then
    geometricSectionInMapKernel P S (LinearEquiv.ofBijective (f.comp P.coinvariantsToTotal) h) f
  else geometricSectionInMapKernel P S c f

public theorem geometricSectionInMapKernelIfBijective_of_bijective
    {HighRelations High Total LowRelations Low L : Type*}
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] [AddCommGroup L]
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    (S : P.GeometricSection) (c : P.Coinvariants ≃ₗ[ℤ] L) (f : Total →ₗ[ℤ] L)
    (h : Function.Bijective (f.comp P.coinvariantsToTotal)) :
    geometricSectionInMapKernelIfBijective P S c f =
      geometricSectionInMapKernel P S (LinearEquiv.ofBijective (f.comp P.coinvariantsToTotal) h) f :=
  dite_eq_left h


end SphereSixComplex.Geometry.CuspPuncturedCollarBridge.UnnormalizedCuspRadialClutchingData
