/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCentralComponents

/-!
# Integral fan shears of the standard infinite `A₂` toric carrier

Translation of the affine-chart labels by `B₀ lambda` preserves every Laurent transition map.
It therefore descends to a biholomorphism of the glued carrier.  This file constructs the full
additive family and records its exact action on the dense torus, affine charts, and central
components.
-/

@[expose] public section

noncomputable section

open Matrix Set
open scoped ContDiff Manifold
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- Translation of a maximal-cone label by the fan shear. -/
public def translateChartIndex (lambda : ParameterLattice) (a : ChartIndex) : ChartIndex :=
  (a.1, a.2 + shearVector lambda)

private theorem shearVector_zero : shearVector (0 : ParameterLattice) = 0 := by
  ext i
  simp [shearVector, Matrix.mulVec]

private theorem shearVector_add (lambda mu : ParameterLattice) :
    shearVector (lambda + mu) = shearVector lambda + shearVector mu := by
  exact Matrix.mulVec_add _ _ _

private theorem shearVector_neg (lambda : ParameterLattice) :
    shearVector (-lambda) = -shearVector lambda := by
  exact Matrix.mulVec_neg _ _

@[simp]
private theorem translateChartIndex_zero (a : ChartIndex) :
    translateChartIndex 0 a = a := by
  rcases a with ⟨upper, v⟩
  simp [translateChartIndex, shearVector_zero]

private theorem translateChartIndex_add
    (lambda mu : ParameterLattice) (a : ChartIndex) :
    translateChartIndex lambda (translateChartIndex mu a) =
      translateChartIndex (lambda + mu) a := by
  rcases a with ⟨upper, v⟩
  simp only [translateChartIndex, shearVector_add]
  congr 1
  abel

private theorem translateChartIndex_neg
    (lambda : ParameterLattice) (a : ChartIndex) :
    translateChartIndex (-lambda) (translateChartIndex lambda a) = a := by
  rw [translateChartIndex_add]
  simp

/-- Simultaneous translation of two fan cones does not change their Laurent transition matrix. -/
public theorem transitionMatrix_translate
    (lambda : ParameterLattice) (a b : ChartIndex) :
    transitionMatrix (translateChartIndex lambda a) (translateChartIndex lambda b) =
      transitionMatrix a b := by
  rcases a with ⟨ua, va⟩
  rcases b with ⟨ub, vb⟩
  ext i j
  cases ua <;> cases ub <;> fin_cases i <;> fin_cases j <;>
    simp [translateChartIndex, transitionMatrix, dualMatrix, a2DualCharacter, a2ConeMatrix,
      heightOneRay, a2Triangle, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private theorem chartChange_translate_source
    (lambda : ParameterLattice) (a b : ChartIndex) :
    (chartChange (translateChartIndex lambda a) (translateChartIndex lambda b)).source =
      (chartChange a b).source := by
  simp only [chartChange_source, transitionMatrix_translate]

private theorem chartChange_translate_apply
    (lambda : ParameterLattice) (a b : ChartIndex) (z : RawCoordinates) :
    chartChange (translateChartIndex lambda a) (translateChartIndex lambda b) z =
      chartChange a b z := by
  change monomial
      (transitionMatrix (translateChartIndex lambda a) (translateChartIndex lambda b)) z =
    monomial (transitionMatrix a b) z
  rw [transitionMatrix_translate]

/-- Translation of the fan labels, descended through the Laurent gluing. -/
public noncomputable def carrierFanShearFun
    (lambda : ParameterLattice) (p : Carrier) : Carrier :=
  inclusion (translateChartIndex lambda (preferredChart p)) (preferredCoordinates p)

/-- The descended fan translation has the identity coordinate formula in every affine chart. -/
public theorem carrierFanShearFun_inclusion
    (lambda : ParameterLattice) (a : ChartIndex) (z : RawCoordinates) :
    carrierFanShearFun lambda (inclusion a z) =
      inclusion (translateChartIndex lambda a) z := by
  let b := preferredChart (inclusion a z)
  let w := preferredCoordinates (inclusion a z)
  have he : inclusion b w = inclusion a z := inclusion_preferredCoordinates _
  have hchange := (inclusion_eq_iff b a w z).mp he
  apply (inclusion_eq_iff (translateChartIndex lambda b)
    (translateChartIndex lambda a) w z).mpr
  constructor
  · rw [chartChange_translate_source]
    exact hchange.1
  · rw [chartChange_translate_apply]
    exact hchange.2

private theorem carrierFanShearFun_zero (p : Carrier) : carrierFanShearFun 0 p = p := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierFanShearFun_inclusion, translateChartIndex_zero]

private theorem carrierFanShearFun_add
    (lambda mu : ParameterLattice) (p : Carrier) :
    carrierFanShearFun (lambda + mu) p =
      carrierFanShearFun lambda (carrierFanShearFun mu p) := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierFanShearFun_inclusion, carrierFanShearFun_inclusion,
    carrierFanShearFun_inclusion, translateChartIndex_add]

/-- The permutation of the glued carrier induced by one integral fan translation. -/
public noncomputable def carrierFanShearEquiv
    (lambda : ParameterLattice) : Equiv.Perm Carrier where
  toFun := carrierFanShearFun lambda
  invFun := carrierFanShearFun (-lambda)
  left_inv p := by
    rw [← carrierFanShearFun_add]
    simpa using carrierFanShearFun_zero p
  right_inv p := by
    rw [← carrierFanShearFun_add]
    simpa using carrierFanShearFun_zero p

@[simp]
public theorem carrierFanShearEquiv_apply
    (lambda : ParameterLattice) (p : Carrier) :
    carrierFanShearEquiv lambda p = carrierFanShearFun lambda p :=
  rfl

/-- The integral fan translations form an additive family of carrier permutations. -/
public noncomputable def carrierFanShear :
    ParameterLattice →+ Additive (Equiv.Perm Carrier) where
  toFun lambda := Additive.ofMul (carrierFanShearEquiv lambda)
  map_zero' := by
    apply Additive.toMul.injective
    ext p
    change carrierFanShearFun 0 p = p
    exact carrierFanShearFun_zero p
  map_add' lambda mu := by
    apply Additive.toMul.injective
    ext p
    change carrierFanShearFun (lambda + mu) p =
      carrierFanShearFun lambda (carrierFanShearFun mu p)
    exact carrierFanShearFun_add lambda mu p

@[simp]
public theorem carrierFanShear_apply
    (lambda : ParameterLattice) (p : Carrier) :
    Additive.toMul (carrierFanShear lambda) p = carrierFanShearFun lambda p :=
  rfl

/-- A fan translation carries the affine piece indexed by `a` onto its translated piece. -/
public theorem carrierFanShear_mem_toricChart_iff
    (lambda : ParameterLattice) (a : ChartIndex) (p : Carrier) :
    letI := chartedSpace
    p ∈ (toricChart a).source ↔
      carrierFanShearFun lambda p ∈ (toricChart (translateChartIndex lambda a)).source := by
  let _ := chartedSpace
  rw [toricChart_source, toricChart_source]
  constructor
  · rintro ⟨z, rfl⟩
    rw [carrierFanShearFun_inclusion]
    exact Set.mem_range_self z
  · obtain ⟨b, w, rfl⟩ := inclusion_jointly_surjective p
    rw [carrierFanShearFun_inclusion]
    rintro ⟨z, he⟩
    refine ⟨z, ?_⟩
    have hchange := (inclusion_eq_iff (translateChartIndex lambda a)
      (translateChartIndex lambda b) z w).mp he
    apply (inclusion_eq_iff a b z w).mpr
    constructor
    · have hsource := hchange.1
      rwa [chartChange_translate_source] at hsource
    · have happly := hchange.2
      rwa [chartChange_translate_apply] at happly

/-- In translated affine charts the fan shear is literally the identity on coordinates. -/
public theorem toricChart_carrierFanShear
    (lambda : ParameterLattice) (a : ChartIndex) {p : Carrier}
    (hp : letI := chartedSpace; p ∈ (toricChart a).source) :
    letI := chartedSpace
    toricChart (translateChartIndex lambda a) (carrierFanShearFun lambda p) =
      toricChart a p := by
  let _ := chartedSpace
  rw [toricChart_source] at hp
  obtain ⟨z, rfl⟩ := hp
  rw [carrierFanShearFun_inclusion, toricChart_inclusion, toricChart_inclusion]

/-- Every integral fan translation is biholomorphic for the glued complex atlas. -/
public theorem carrierFanShear_contMDiff (lambda : ParameterLattice) :
    letI := chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (carrierFanShearFun lambda) := by
  let _ := chartedSpace
  intro p
  obtain ⟨a, hp⟩ := toricChart_cover p
  let b := translateChartIndex lambda a
  have hchart : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (toricChart a) p :=
    (toricChart a).contMDiffOn_toFun.contMDiffAt
      ((toricChart a).open_source.mem_nhds hp)
  have htarget : toricChart a p ∈ (toricChart b).target := by
    rw [toricChart_target]
    exact Set.mem_univ _
  have hinv : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (toricChart b).invFun (toricChart a p) :=
    (toricChart b).contMDiffOn_invFun.contMDiffAt
      ((toricChart b).open_target.mem_nhds htarget)
  have hcomp := hinv.comp p hchart
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(toricChart a).open_source.mem_nhds hp] with q hq
  have hshear : carrierFanShearFun lambda q ∈ (toricChart b).source :=
    (carrierFanShear_mem_toricChart_iff lambda a q).mp hq
  calc
    carrierFanShearFun lambda q =
        (toricChart b).invFun (toricChart b (carrierFanShearFun lambda q)) :=
      ((toricChart b).left_inv hshear).symm
    _ = (toricChart b).invFun (toricChart a q) := by
      rw [toricChart_carrierFanShear lambda a hq]

/-- Fan translations preserve the descended height character. -/
public theorem carrierFanShear_preserves_height
    (lambda : ParameterLattice) (p : Carrier) :
    carrierHeight (carrierFanShearFun lambda p) = carrierHeight p := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierFanShearFun_inclusion, carrierHeight_inclusion, carrierHeight_inclusion]

private theorem group_zpow_two {G : Type*} [CommGroup G] (z : G) (a b : ℤ) :
    z ^ a * z ^ b = z ^ (a + b) := by
  rw [zpow_add]

private theorem group_zpow_three {G : Type*} [CommGroup G] (z : G) (a b c : ℤ) :
    z ^ a * z ^ b * z ^ c = z ^ (a + b + c) := by
  rw [zpow_add, zpow_add]

private theorem evaluateCharacter_translate_denseTorusShear
    (lambda : ParameterLattice) (upper : Bool) (v : ToricLattice)
    (x : DenseTorus) (i : Fin 3) :
    evaluateCharacter (a2DualCharacter upper (v + shearVector lambda) i)
        (denseTorusShear lambda x) =
      evaluateCharacter (a2DualCharacter upper v i) x := by
  cases upper
  · fin_cases i
    · simp [evaluateCharacter, a2DualCharacter, denseTorusShear, Fin.prod_univ_succ]
      rw [← zpow_neg, ← zpow_neg]
      rw [show v 0 + shearVector lambda 0 + (v 1 + shearVector lambda 1) + 1 =
          1 + shearVector lambda 0 + shearVector lambda 1 + v 0 + v 1 by ring,
        show v 0 + v 1 + 1 = 1 + v 0 + v 1 by ring]
      have hpow :
          x 2 ^ (-shearVector lambda 0) *
              x 2 ^ (-shearVector lambda 1) *
              x 2 ^ (1 + shearVector lambda 0 + shearVector lambda 1 + v 0 + v 1) =
            x 2 ^ (1 + v 0 + v 1) := by
        rw [group_zpow_three]
        congr 1
        ring
      calc
        x 2 ^ (-shearVector lambda 0) * (x 0)⁻¹ *
            (x 2 ^ (-shearVector lambda 1) * (x 1)⁻¹ *
              x 2 ^ (1 + shearVector lambda 0 + shearVector lambda 1 + v 0 + v 1)) =
          (x 0)⁻¹ * (x 1)⁻¹ *
            (x 2 ^ (-shearVector lambda 0) *
              x 2 ^ (-shearVector lambda 1) *
              x 2 ^ (1 + shearVector lambda 0 + shearVector lambda 1 + v 0 + v 1)) := by
          ac_rfl
        _ = _ := by rw [hpow]; ac_rfl
    · simp [evaluateCharacter, a2DualCharacter, denseTorusShear, Fin.prod_univ_succ]
      rw [← zpow_neg]
      have hpow :
          x 2 ^ shearVector lambda 0 * x 2 ^ (-shearVector lambda 0 + -v 0) =
            x 2 ^ (-v 0) := by
        rw [group_zpow_two]
        congr 1
        ring
      calc
        x 0 * x 2 ^ shearVector lambda 0 * x 2 ^ (-shearVector lambda 0 + -v 0) =
          x 0 * (x 2 ^ shearVector lambda 0 *
            x 2 ^ (-shearVector lambda 0 + -v 0)) := by ac_rfl
        _ = _ := by rw [hpow]
    · simp [evaluateCharacter, a2DualCharacter, denseTorusShear, Fin.prod_univ_succ]
      rw [← zpow_neg]
      have hpow :
          x 2 ^ shearVector lambda 1 * x 2 ^ (-shearVector lambda 1 + -v 1) =
            x 2 ^ (-v 1) := by
        rw [group_zpow_two]
        congr 1
        ring
      calc
        x 1 * x 2 ^ shearVector lambda 1 * x 2 ^ (-shearVector lambda 1 + -v 1) =
          x 1 * (x 2 ^ shearVector lambda 1 *
            x 2 ^ (-shearVector lambda 1 + -v 1)) := by ac_rfl
        _ = _ := by rw [hpow]
  · fin_cases i
    · simp [evaluateCharacter, a2DualCharacter, denseTorusShear, Fin.prod_univ_succ]
      rw [← zpow_neg]
      have hpow :
          x 2 ^ (-shearVector lambda 1) * x 2 ^ (v 1 + shearVector lambda 1 + 1) =
            x 2 ^ (v 1 + 1) := by
        rw [group_zpow_two]
        congr 1
        ring
      calc
        x 2 ^ (-shearVector lambda 1) * (x 1)⁻¹ *
            x 2 ^ (v 1 + shearVector lambda 1 + 1) =
          (x 1)⁻¹ * (x 2 ^ (-shearVector lambda 1) *
            x 2 ^ (v 1 + shearVector lambda 1 + 1)) := by ac_rfl
        _ = _ := by rw [hpow]
    · simp [evaluateCharacter, a2DualCharacter, denseTorusShear, Fin.prod_univ_succ]
      rw [← zpow_neg]
      have hpow :
          x 2 ^ (-shearVector lambda 0) * x 2 ^ (v 0 + shearVector lambda 0 + 1) =
            x 2 ^ (v 0 + 1) := by
        rw [group_zpow_two]
        congr 1
        ring
      calc
        x 2 ^ (-shearVector lambda 0) * (x 0)⁻¹ *
            x 2 ^ (v 0 + shearVector lambda 0 + 1) =
          (x 0)⁻¹ * (x 2 ^ (-shearVector lambda 0) *
            x 2 ^ (v 0 + shearVector lambda 0 + 1)) := by ac_rfl
        _ = _ := by rw [hpow]
    · simp [evaluateCharacter, a2DualCharacter, denseTorusShear, Fin.prod_univ_succ]
      have hpow :
          x 2 ^ shearVector lambda 0 *
              x 2 ^ shearVector lambda 1 *
              x 2 ^ (-shearVector lambda 0 + -v 0 -
                (v 1 + shearVector lambda 1) - 1) =
            x 2 ^ (-v 0 - v 1 - 1) := by
        rw [group_zpow_three]
        congr 1
        ring
      calc
        x 0 * x 2 ^ shearVector lambda 0 *
            (x 1 * x 2 ^ shearVector lambda 1 *
              x 2 ^ (-shearVector lambda 0 + -v 0 -
                (v 1 + shearVector lambda 1) - 1)) =
          x 0 * x 1 * (x 2 ^ shearVector lambda 0 *
            x 2 ^ shearVector lambda 1 *
            x 2 ^ (-shearVector lambda 0 + -v 0 -
              (v 1 + shearVector lambda 1) - 1)) := by ac_rfl
        _ = _ := by rw [hpow]; ac_rfl

private theorem torusChartCoordinates_translate_denseTorusShear
    (lambda : ParameterLattice) (a : ChartIndex) (x : DenseTorus) :
    torusChartCoordinates (translateChartIndex lambda a) (denseTorusShear lambda x) =
      torusChartCoordinates a x := by
  funext i
  simpa [translateChartIndex, torusChartCoordinates, monomial, dualMatrix,
    evaluateCharacter, denseRawCoordinates] using
      congrArg Units.val (evaluateCharacter_translate_denseTorusShear lambda a.1 a.2 x i)

/-- On the common dense torus, fan translation is the prescribed integral monomial shear. -/
public theorem carrierFanShear_torus (lambda : ParameterLattice) (x : DenseTorus) :
    carrierFanShearFun lambda (carrierTorusEmbedding x) =
      carrierTorusEmbedding (denseTorusShear lambda x) := by
  rw [carrierTorusEmbedding_eq_inclusion_torusChartCoordinates baseChart,
    carrierFanShearFun_inclusion,
    carrierTorusEmbedding_eq_inclusion_torusChartCoordinates
      (translateChartIndex lambda baseChart),
    torusChartCoordinates_translate_denseTorusShear]

private theorem a2Triangle_translate
    (lambda : ParameterLattice) (upper : Bool) (v : ToricLattice) (i : Fin 3) :
    a2Triangle upper (v + shearVector lambda) i =
      a2Triangle upper v i + shearVector lambda := by
  cases upper <;> fin_cases i <;> simp [a2Triangle] <;> abel

private theorem carrierFanShear_mapsTo_centralComponent
    (lambda : ParameterLattice) (v : ToricLattice) :
    MapsTo (carrierFanShearFun lambda) (carrierCentralComponent v)
      (carrierCentralComponent (v + shearVector lambda)) := by
  intro p hp
  obtain ⟨a, i, z, hray, hi, rfl⟩ := hp
  rw [carrierFanShearFun_inclusion]
  refine ⟨translateChartIndex lambda a, i, z, ?_, hi, rfl⟩
  rw [show (translateChartIndex lambda a).1 = a.1 from rfl,
    show (translateChartIndex lambda a).2 = a.2 + shearVector lambda from rfl,
    a2Triangle_translate, hray]

/-- Fan translations carry each central ray component to the correspondingly translated one. -/
public theorem carrierFanShear_component
    (lambda : ParameterLattice) (v : ToricLattice) :
    carrierFanShearFun lambda '' carrierCentralComponent v =
      carrierCentralComponent (v + shearVector lambda) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact carrierFanShear_mapsTo_centralComponent lambda v hq
  · intro hp
    refine ⟨carrierFanShearFun (-lambda) p, ?_, ?_⟩
    · have hpre := carrierFanShear_mapsTo_centralComponent (-lambda)
        (v + shearVector lambda) hp
      rw [shearVector_neg] at hpre
      simpa only [add_neg_cancel_right] using hpre
    · exact (carrierFanShearEquiv lambda).right_inv p

/-- The holomorphicity field in the exact form used by `RemainingGeometry`. -/
public theorem carrierFanShear_holomorphic :
    letI := chartedSpace
    ∀ lambda, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun p ↦ Additive.toMul (carrierFanShear lambda) p) := by
  let _ := chartedSpace
  intro lambda
  simpa only [carrierFanShear_apply] using carrierFanShear_contMDiff lambda

/-- The height-invariance field in the exact form used by `RemainingGeometry`. -/
public theorem carrierFanShear_preserves_t
    (lambda : ParameterLattice) (p : Carrier) :
    carrierHeight (Additive.toMul (carrierFanShear lambda) p) = carrierHeight p := by
  simpa only [carrierFanShear_apply] using carrierFanShear_preserves_height lambda p

/-- The dense-torus field in the exact form used by `RemainingGeometry`. -/
public theorem carrierFanShear_on_torus
    (lambda : ParameterLattice) (x : DenseTorus) :
    Additive.toMul (carrierFanShear lambda) (carrierTorusEmbedding x) =
      carrierTorusEmbedding (denseTorusShear lambda x) := by
  simpa only [carrierFanShear_apply] using carrierFanShear_torus lambda x

/-- The chart-translation field in the exact form used by `RemainingGeometry`. -/
public theorem carrierFanShear_chart
    (lambda : ParameterLattice) (a : ChartIndex) (p : Carrier) :
    letI := chartedSpace
    p ∈ (toricChart a).source ↔
      Additive.toMul (carrierFanShear lambda) p ∈
        (toricChart (a.1, a.2 + shearVector lambda)).source := by
  let _ := chartedSpace
  simpa only [carrierFanShear_apply, translateChartIndex] using
    carrierFanShear_mem_toricChart_iff lambda a p

/-- The component-translation field in the exact form used by `RemainingGeometry`. -/
public theorem carrierFanShear_component_exact
    (lambda : ParameterLattice) (v : ToricLattice) :
    (fun p ↦ Additive.toMul (carrierFanShear lambda) p) '' carrierCentralComponent v =
      carrierCentralComponent (v + shearVector lambda) := by
  simpa only [carrierFanShear_apply] using carrierFanShear_component lambda v

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
