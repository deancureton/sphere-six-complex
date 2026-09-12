module

public import SphereSixComplex.Prerequisites.Topology.CyclicPuncturedProductMappingTorus

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.CyclicAngularFundamentalDomain

public theorem realMappingTorusHomeomorph_symm_fiberInclusion {T : Type} [TopologicalSpace T]
    (phi : T ≃ₜ T) (y : T) :
    (realMappingTorusHomeomorph phi).symm
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) y) =
      Quotient.mk (realMappingTorusSetoid phi) ((0 : ℝ), y) := rfl

public theorem realMappingTorusHomeomorph_mk_zero {T : Type} [TopologicalSpace T]
    (phi : T ≃ₜ T) (y : T) :
    realMappingTorusHomeomorph phi (Quotient.mk (realMappingTorusSetoid phi) ((0 : ℝ), y)) =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) y := by
  rw [← realMappingTorusHomeomorph_symm_fiberInclusion, Homeomorph.apply_symm_apply]

public def realFiberSlice
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (a : ℝ) :
    C(F, CircleMappingTorus phi) :=
  ⟨fun y ↦ realMappingTorusHomeomorph phi
      (Quotient.mk
        (realMappingTorusSetoid phi) (a, y)),
    (realMappingTorusHomeomorph phi).continuous.comp
      (continuous_quot_mk.comp (continuous_const.prodMk continuous_id))⟩

public def realFiberSliceHomotopy
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (a : ℝ) :
    ContinuousMap.Homotopy (realFiberSlice phi a)
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) where
  toFun q :=
    realMappingTorusHomeomorph phi
      (Quotient.mk
        (realMappingTorusSetoid phi)
        ((1 - (q.1 : ℝ)) * a, q.2))
  continuous_toFun :=
    (realMappingTorusHomeomorph phi).continuous.comp
      (continuous_quot_mk.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          continuous_const).prodMk continuous_snd))
  map_zero_left x := by
    simp [realFiberSlice]
  map_one_left x := by
    simpa using
      realMappingTorusHomeomorph_mk_zero
        phi x

end SphereSixComplex.CyclicAngularFundamentalDomain

end

end
