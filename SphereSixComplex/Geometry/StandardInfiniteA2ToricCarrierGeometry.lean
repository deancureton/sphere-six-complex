/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrier
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Geometry of the glued infinite `A₂` toric carrier

This module descends the height character and the common algebraic torus through the affine
Laurent gluing.  It records the exact chart formulas needed to assemble the standard toric model.
-/

@[expose] public section

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- The height monomial in raw affine coordinates. -/
public def rawHeight (z : RawCoordinates) : ℂ := z 0 * z 1 * z 2

public theorem rawHeight_eq_prod (z : RawCoordinates) : rawHeight z = ∏ i, z i := by
  simp [rawHeight, Fin.prod_univ_succ, mul_assoc]

private theorem prod_zpow_eq {a : ℂ} (ha : a ≠ 0) (k : Fin 3 → ℤ) :
    (∏ i, a ^ k i) = a ^ ∑ i, k i := by
  induction (Finset.univ : Finset (Fin 3)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

private theorem rawHeight_monomial_on_coordinateTorus
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : HeightOne A) {z : RawCoordinates}
    (hz : z ∈ coordinateTorus) : rawHeight (monomial A z) = rawHeight z := by
  rw [rawHeight_eq_prod, rawHeight_eq_prod]
  unfold monomial
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [prod_zpow_eq (hz j), hA j, zpow_one]

public theorem rawHeight_monomial_on_domain
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : HeightOne A) :
    EqOn (rawHeight ∘ monomial A) rawHeight (monomialDomain A) := by
  have h : EqOn (rawHeight ∘ monomial A) rawHeight
      (monomialDomain A ∩ coordinateTorus) :=
    fun _ hz ↦ rawHeight_monomial_on_coordinateTorus A hA hz.2
  have hraw : ContDiff ℂ 0 rawHeight :=
    ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).mul
      (contDiff_apply ℂ ℂ 2)
  refine h.of_subset_closure ?_ ?_ Set.inter_subset_left
    (coordinateTorus_isDense.open_subset_closure_inter (monomialDomain_isOpen A))
  · exact hraw.continuous.comp_continuousOn (monomial_contDiffOn A 0).continuousOn
  · exact hraw.continuous.continuousOn

public theorem rawHeight_chartChange (a b : ChartIndex) :
    EqOn (rawHeight ∘ chartChange a b) rawHeight (chartChange a b).source := by
  rw [chartChange_source]
  exact rawHeight_monomial_on_domain _ (transitionMatrix_heightOne a b)

/-- A selected affine representative of a point of the glued carrier. -/
public noncomputable def preferredCoordinates (x : Carrier) : RawCoordinates :=
  (inclusion_jointly_surjective x).choose_spec.choose

public theorem inclusion_preferredCoordinates (x : Carrier) :
    inclusion (preferredChart x) (preferredCoordinates x) = x :=
  (inclusion_jointly_surjective x).choose_spec.choose_spec

/-- The globally descended height character. -/
public noncomputable def carrierHeight (x : Carrier) : ℂ := rawHeight (preferredCoordinates x)

public theorem carrierHeight_inclusion (a : ChartIndex) (z : RawCoordinates) :
    carrierHeight (inclusion a z) = rawHeight z := by
  let b := preferredChart (inclusion a z)
  let w := preferredCoordinates (inclusion a z)
  have he : inclusion b w = inclusion a z := inclusion_preferredCoordinates _
  have hchange := (inclusion_eq_iff b a w z).mp he
  calc
    rawHeight w = rawHeight (chartChange b a w) :=
      (rawHeight_chartChange b a hchange.1).symm
    _ = rawHeight z := congrArg rawHeight hchange.2

/-- Raw coordinates of a point of the algebraic torus. -/
public def denseRawCoordinates (x : DenseTorus) : RawCoordinates := fun i ↦ (x i : ℂ)

public theorem denseRawCoordinates_mem_coordinateTorus (x : DenseTorus) :
    denseRawCoordinates x ∈ coordinateTorus := fun i ↦ Units.ne_zero (x i)

public theorem denseRawCoordinates_isOpenEmbedding :
    IsOpenEmbedding denseRawCoordinates := by
  exact Topology.IsOpenEmbedding.piMap fun _ ↦ IsOpenUnits.isOpenEmbedding_unitsVal

/-- Recover units from a raw point all of whose coordinates are nonzero. -/
public def denseTorusOfCoordinateTorus (z : RawCoordinates) (hz : z ∈ coordinateTorus) :
    DenseTorus := fun i ↦ Units.mk0 (z i) (hz i)

@[simp]
public theorem denseRawCoordinates_denseTorusOfCoordinateTorus
    (z : RawCoordinates) (hz : z ∈ coordinateTorus) :
    denseRawCoordinates (denseTorusOfCoordinateTorus z hz) = z := by
  funext i
  rfl

public def baseChart : ChartIndex := (false, 0)

/-- The monomial coordinate change from intrinsic torus coordinates to the base affine chart. -/
public def baseTorusEquiv : DenseTorus ≃ DenseTorus where
  toFun x := ![(x 0 * x 1)⁻¹ * x 2, x 0, x 1]
  invFun z := ![z 1, z 2, z 0 * z 1 * z 2]
  left_inv x := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change (x 0 * x 1)⁻¹ * x 2 * x 0 * x 1 = x 2
      calc
        (x 0 * x 1)⁻¹ * x 2 * x 0 * x 1 =
            x 2 * ((x 0 * x 1)⁻¹ * (x 0 * x 1)) := by ac_rfl
        _ = x 2 := by simp
  right_inv z := by
    funext i
    fin_cases i
    · change (z 1 * z 2)⁻¹ * (z 0 * z 1 * z 2) = z 0
      calc
        (z 1 * z 2)⁻¹ * (z 0 * z 1 * z 2) =
            z 0 * ((z 1 * z 2)⁻¹ * (z 1 * z 2)) := by ac_rfl
        _ = z 0 := by simp
    · rfl
    · rfl

/-- The base-chart monomial change is a homeomorphism of the algebraic torus. -/
public def baseTorusHomeomorph : DenseTorus ≃ₜ DenseTorus where
  toEquiv := baseTorusEquiv
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

/-- Affine coordinates of an intrinsic torus point in the base chart. -/
public def baseChartCoordinates (x : DenseTorus) : RawCoordinates :=
  denseRawCoordinates (baseTorusHomeomorph x)

/-- The common dense torus embedded through a fixed affine chart. -/
public def carrierTorusEmbedding (x : DenseTorus) : Carrier :=
  inclusion baseChart (baseChartCoordinates x)

public theorem carrierTorusEmbedding_isOpenEmbedding :
    IsOpenEmbedding carrierTorusEmbedding :=
  (inclusion_isOpenEmbedding baseChart).comp
    (denseRawCoordinates_isOpenEmbedding.comp baseTorusHomeomorph.isOpenEmbedding)

public theorem carrierHeight_torus (x : DenseTorus) :
    carrierHeight (carrierTorusEmbedding x) = (x 2 : ℂ) := by
  rw [carrierTorusEmbedding, carrierHeight_inclusion]
  simp [rawHeight, baseChartCoordinates, denseRawCoordinates, baseTorusHomeomorph,
    baseTorusEquiv]
  field_simp [Units.ne_zero]

/-- Affine coordinates of an intrinsic torus point in an arbitrary maximal-cone chart. -/
public def torusChartCoordinates (a : ChartIndex) (x : DenseTorus) : RawCoordinates :=
  monomial (dualMatrix a) (denseRawCoordinates x)

public theorem torusChartCoordinates_mem_coordinateTorus (a : ChartIndex) (x : DenseTorus) :
    torusChartCoordinates a x ∈ coordinateTorus :=
  monomial_mapsTo_coordinateTorus _ (denseRawCoordinates_mem_coordinateTorus x)

public theorem baseChartCoordinates_eq_torusChartCoordinates (x : DenseTorus) :
    baseChartCoordinates x = torusChartCoordinates baseChart x := by
  funext i
  fin_cases i
  all_goals simp [baseChartCoordinates, baseTorusHomeomorph, baseTorusEquiv,
    torusChartCoordinates, monomial, dualMatrix, baseChart, a2DualCharacter,
    denseRawCoordinates, Fin.prod_univ_succ]
  all_goals field_simp [Units.ne_zero]

private theorem transitionMatrix_mul_dualMatrix (a b : ChartIndex) :
    transitionMatrix a b * dualMatrix a = dualMatrix b := by
  rw [transitionMatrix, Matrix.mul_assoc, coneMatrix_mul_dualMatrix, Matrix.mul_one]

public theorem chartChange_torusChartCoordinates (a b : ChartIndex) (x : DenseTorus) :
    chartChange a b (torusChartCoordinates a x) = torusChartCoordinates b x := by
  have h := monomial_comp_on_coordinateTorus (transitionMatrix a b) (dualMatrix a)
    (denseRawCoordinates_mem_coordinateTorus x)
  change monomial (transitionMatrix a b)
      (monomial (dualMatrix a) (denseRawCoordinates x)) =
    monomial (dualMatrix b) (denseRawCoordinates x)
  simpa only [transitionMatrix_mul_dualMatrix] using h

public theorem torusChartCoordinates_mem_chartChange_source
    (a b : ChartIndex) (x : DenseTorus) :
    torusChartCoordinates a x ∈ (chartChange a b).source := by
  rw [chartChange_source]
  exact coordinateTorus_subset_monomialDomain _
    (torusChartCoordinates_mem_coordinateTorus a x)

/-- The common torus has the expected affine coordinates in every glued chart. -/
public theorem carrierTorusEmbedding_eq_inclusion_torusChartCoordinates
    (a : ChartIndex) (x : DenseTorus) :
    carrierTorusEmbedding x = inclusion a (torusChartCoordinates a x) := by
  rw [carrierTorusEmbedding, baseChartCoordinates_eq_torusChartCoordinates]
  exact (inclusion_eq_iff baseChart a _ _).mpr
    ⟨torusChartCoordinates_mem_chartChange_source baseChart a x,
      chartChange_torusChartCoordinates baseChart a x⟩

public theorem inclusion_coordinateTorus_mem_torus_range
    (a : ChartIndex) {z : RawCoordinates} (hz : z ∈ coordinateTorus) :
    inclusion a z ∈ Set.range carrierTorusEmbedding := by
  let rawIntrinsic := monomial (a2ConeMatrix a.1 a.2) z
  have hrawIntrinsic : rawIntrinsic ∈ coordinateTorus :=
    monomial_mapsTo_coordinateTorus _ hz
  let x := denseTorusOfCoordinateTorus rawIntrinsic hrawIntrinsic
  refine ⟨x, ?_⟩
  rw [carrierTorusEmbedding_eq_inclusion_torusChartCoordinates a x]
  congr 1
  have hx : denseRawCoordinates x = rawIntrinsic :=
    denseRawCoordinates_denseTorusOfCoordinateTorus rawIntrinsic hrawIntrinsic
  rw [torusChartCoordinates, hx]
  dsimp only [rawIntrinsic]
  rw [monomial_comp_on_coordinateTorus _ _ hz, dualMatrix_mul_coneMatrix, monomial_one]

/-- The common torus is dense because its intersection with every affine chart is the dense
coordinate torus. -/
public theorem carrierTorusEmbedding_denseRange : DenseRange carrierTorusEmbedding := by
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  apply map_mem_closure (inclusion_isOpenEmbedding a).continuous
    (coordinateTorus_isDense z)
  intro w hw
  exact inclusion_coordinateTorus_mem_torus_range a hw

private theorem mem_coordinateTorus_of_rawHeight_ne_zero {z : RawCoordinates}
    (hz : rawHeight z ≠ 0) : z ∈ coordinateTorus := by
  have hprod : z 0 * z 1 ≠ 0 ∧ z 2 ≠ 0 := by
    simpa [rawHeight] using (mul_ne_zero_iff.mp hz)
  have h01 : z 0 ≠ 0 ∧ z 1 ≠ 0 := mul_ne_zero_iff.mp hprod.1
  intro i
  fin_cases i
  · exact h01.1
  · exact h01.2
  · exact hprod.2

/-- The common torus is exactly the nonzero height fibre. -/
public theorem carrierTorusEmbedding_range :
    Set.range carrierTorusEmbedding = {p | carrierHeight p ≠ 0} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    change carrierHeight (carrierTorusEmbedding x) ≠ 0
    rw [carrierHeight_torus]
    exact Units.ne_zero (x 2)
  · intro hp
    obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
    change carrierHeight (inclusion a z) ≠ 0 at hp
    rw [carrierHeight_inclusion] at hp
    exact inclusion_coordinateTorus_mem_torus_range a
      (mem_coordinateTorus_of_rawHeight_ne_zero hp)

private theorem parametrization_symm_mem_rawAtlas (a : ChartIndex) :
    (parametrization a).symm ∈
      @atlas RawCoordinates inferInstance Carrier inferInstance rawChartedSpace :=
  Set.mem_range_self _

public theorem parametrization_contMDiffOn (a : ChartIndex) :
    letI := rawChartedSpace
    ContMDiffOn (modelWithCornersSelf ℂ RawCoordinates)
      (modelWithCornersSelf ℂ RawCoordinates) ∞
      (parametrization a) (parametrization a).source := by
  let _ := rawChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ RawCoordinates) ∞ Carrier := rawIsManifold
  have hmax : (parametrization a).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ RawCoordinates) ∞ Carrier :=
    IsManifold.subset_maximalAtlas (parametrization_symm_mem_rawAtlas a)
  exact contMDiffOn_symm_of_mem_maximalAtlas hmax

public theorem parametrization_symm_contMDiffOn (a : ChartIndex) :
    letI := rawChartedSpace
    ContMDiffOn (modelWithCornersSelf ℂ RawCoordinates)
      (modelWithCornersSelf ℂ RawCoordinates) ∞
      (parametrization a).symm (parametrization a).target := by
  let _ := rawChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ RawCoordinates) ∞ Carrier := rawIsManifold
  have hmax : (parametrization a).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ RawCoordinates) ∞ Carrier :=
    IsManifold.subset_maximalAtlas (parametrization_symm_mem_rawAtlas a)
  exact contMDiffOn_of_mem_maximalAtlas hmax

/-- The affine chart, re-expressed in the project's `ComplexModel`. -/
public def toricChartOpen (a : ChartIndex) :
    OpenPartialHomeomorph Carrier ComplexModel :=
  (parametrization a).symm.trans rawToComplexModel.toHomeomorph.toOpenPartialHomeomorph

@[simp]
public theorem parametrization_source (a : ChartIndex) :
    (parametrization a).source = Set.univ := by
  simp [parametrization]

@[simp]
public theorem toricChartOpen_source (a : ChartIndex) :
    (toricChartOpen a).source = Set.range (inclusion a) := by
  rw [toricChartOpen, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, parametrization_target]
  simp

@[simp]
public theorem toricChartOpen_target (a : ChartIndex) :
    (toricChartOpen a).target = Set.univ := by
  simp [toricChartOpen, parametrization]

public theorem toricChartOpen_inclusion (a : ChartIndex) (z : RawCoordinates) :
    toricChartOpen a (inclusion a z) = rawToComplexModel z := by
  change rawToComplexModel ((parametrization a).symm (inclusion a z)) = rawToComplexModel z
  rw [show (parametrization a).symm (inclusion a z) = z from
    (parametrization a).left_inv (by simp [parametrization])]

/-- Each affine parametrization is a complex partial diffeomorphism after linear recharting. -/
public noncomputable def toricChart (a : ChartIndex) :
    letI := chartedSpace
    PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) Carrier ComplexModel ∞ := by
  let _ : ChartedSpace RawCoordinates Carrier := rawChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ RawCoordinates) ∞ Carrier := rawIsManifold
  let _ : ChartedSpace ComplexModel Carrier := chartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ Carrier := isManifold
  let e := toricChartOpen a
  refine
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := ?_
      contMDiffOn_invFun := ?_ }
  · have hparamRaw := parametrization_symm_contMDiffOn a
    have hid := contMDiff_id_linearRechart_symm (M := Carrier) (n := ∞) rawToComplexModel
    have hparam : ContMDiffOn (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ RawCoordinates) ∞
        (parametrization a).symm (parametrization a).target :=
      hparamRaw.comp hid.contMDiffOn fun _ h ↦ h
    have hlinear : ContMDiff (modelWithCornersSelf ℂ RawCoordinates)
        (modelWithCornersSelf ℂ ComplexModel) ∞ rawToComplexModel :=
      contMDiff_iff_contDiff.mpr rawToComplexModel.contDiff
    simpa [e, toricChartOpen] using hlinear.comp_contMDiffOn hparam
  · have hlinear : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ RawCoordinates) ∞ rawToComplexModel.symm :=
      contMDiff_iff_contDiff.mpr rawToComplexModel.symm.contDiff
    have hparamRaw := parametrization_contMDiffOn a
    have hparam : ContMDiffOn (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ RawCoordinates) ∞
        ((parametrization a) ∘ rawToComplexModel.symm) Set.univ := by
      apply hparamRaw.comp hlinear.contMDiffOn
      intro z _
      simp [parametrization]
    have hid := contMDiff_id_linearRechart (M := Carrier) (n := ∞) rawToComplexModel
    rw [show chartedSpace = linearRechart rawToComplexModel from rfl]
    simpa [e, toricChartOpen] using hid.comp_contMDiffOn hparam

@[simp]
public theorem toricChart_source (a : ChartIndex) :
    letI := chartedSpace
    (toricChart a).source = Set.range (inclusion a) := by
  let _ := chartedSpace
  exact toricChartOpen_source a

@[simp]
public theorem toricChart_target (a : ChartIndex) :
    letI := chartedSpace
    (toricChart a).target = Set.univ := by
  let _ := chartedSpace
  exact toricChartOpen_target a

public theorem toricChart_inclusion (a : ChartIndex) (z : RawCoordinates) :
    letI := chartedSpace
    toricChart a (inclusion a z) = rawToComplexModel z := by
  let _ := chartedSpace
  exact toricChartOpen_inclusion a z

public theorem toricChart_cover (p : Carrier) :
    letI := chartedSpace
    ∃ a, p ∈ (toricChart a).source := by
  let _ := chartedSpace
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  exact ⟨a, by simp⟩

public theorem carrierTorusEmbedding_mem_toricChart (a : ChartIndex) (x : DenseTorus) :
    letI := chartedSpace
    carrierTorusEmbedding x ∈ (toricChart a).source := by
  let _ := chartedSpace
  rw [toricChart_source, carrierTorusEmbedding_eq_inclusion_torusChartCoordinates]
  exact Set.mem_range_self _

public theorem toricChart_torus_character (a : ChartIndex) (x : DenseTorus) (i : Fin 3) :
    letI := chartedSpace
    toricChart a (carrierTorusEmbedding x) i =
      ((evaluateCharacter (a2DualCharacter a.1 a.2 i) x : ℂˣ) : ℂ) := by
  let _ := chartedSpace
  rw [carrierTorusEmbedding_eq_inclusion_torusChartCoordinates a x,
    toricChart_inclusion]
  simp [torusChartCoordinates, rawToComplexModel, monomial, dualMatrix,
    evaluateCharacter, denseRawCoordinates]

/-- In every affine chart the descended height is the squarefree coordinate monomial. -/
public theorem carrierHeight_toricChart (a : ChartIndex) (p : Carrier) :
    letI := chartedSpace
    p ∈ (toricChart a).source →
      carrierHeight p = toricChart a p 0 * toricChart a p 1 * toricChart a p 2 := by
  let _ := chartedSpace
  intro hp
  rw [toricChart_source] at hp
  obtain ⟨z, rfl⟩ := hp
  rw [carrierHeight_inclusion, toricChart_inclusion]
  rfl

/-- The affine pieces form a connected gluing because their common coordinate torus is
nonempty. -/
public theorem carrierConnectedSpace : ConnectedSpace Carrier := by
  let _ : Nonempty gluing.J := ⟨baseChart⟩
  let _ (a : gluing.J) : ConnectedSpace (gluing.U a) := by
    change ConnectedSpace RawCoordinates
    infer_instance
  apply connectedSpace_gluedSpace gluing
  intro a b
  apply Relation.ReflTransGen.single
  let x : DenseTorus := 1
  exact ⟨carrierTorusEmbedding x,
    ⟨torusChartCoordinates a x,
      (carrierTorusEmbedding_eq_inclusion_torusChartCoordinates a x).symm⟩,
    ⟨torusChartCoordinates b x,
      (carrierTorusEmbedding_eq_inclusion_torusChartCoordinates b x).symm⟩⟩

/-- The descended height character is holomorphic in the glued complex atlas. -/
public theorem carrierHeight_contMDiff :
    letI := chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ carrierHeight := by
  let _ := chartedSpace
  intro p
  obtain ⟨a, hp⟩ := toricChart_cover p
  have hchart : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (toricChart a) p :=
    (toricChart a).contMDiffOn_toFun.contMDiffAt
      ((toricChart a).open_source.mem_nhds hp)
  have hproj (i : Fin 3) : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun z : ComplexModel ↦ z i) :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).contMDiff
  have hprod : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun z : ComplexModel ↦ z 0 * z 1 * z 2) :=
    ((hproj 0).mul (hproj 1)).mul (hproj 2)
  have hcomp := hprod.contMDiffAt.comp p hchart
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(toricChart a).open_source.mem_nhds hp] with q hq
  exact carrierHeight_toricChart a q hq

private theorem coordinateTorus_mul_mem_monomialDomain
    (A : Matrix (Fin 3) (Fin 3) ℤ) {u z : RawCoordinates}
    (hu : u ∈ coordinateTorus) (hz : z ∈ monomialDomain A) :
    u * z ∈ monomialDomain A := by
  intro i j hij hzero
  exact hz i j hij ((mul_eq_zero.mp hzero).resolve_left (hu j))

private theorem chartChange_mul_torusCoordinates
    (a b : ChartIndex) (g : DenseTorus) {z : RawCoordinates}
    (_hz : z ∈ (chartChange a b).source) :
    chartChange a b (torusChartCoordinates a g * z) =
      torusChartCoordinates b g * chartChange a b z := by
  change monomial (transitionMatrix a b) (torusChartCoordinates a g * z) = _
  rw [monomial_mul]
  have h := chartChange_torusChartCoordinates a b g
  change monomial (transitionMatrix a b) (torusChartCoordinates a g) =
    torusChartCoordinates b g at h
  rw [h]
  rfl

/-- Coordinatewise torus multiplication descended through the Laurent gluing. -/
public noncomputable def carrierTorusActionFun (g : DenseTorus) (p : Carrier) : Carrier :=
  inclusion (preferredChart p)
    (torusChartCoordinates (preferredChart p) g * preferredCoordinates p)

public theorem carrierTorusActionFun_inclusion
    (g : DenseTorus) (a : ChartIndex) (z : RawCoordinates) :
    carrierTorusActionFun g (inclusion a z) =
      inclusion a (torusChartCoordinates a g * z) := by
  let b := preferredChart (inclusion a z)
  let w := preferredCoordinates (inclusion a z)
  have he : inclusion b w = inclusion a z := inclusion_preferredCoordinates _
  have hchange := (inclusion_eq_iff b a w z).mp he
  apply (inclusion_eq_iff b a _ _).mpr
  constructor
  · rw [chartChange_source] at hchange ⊢
    exact coordinateTorus_mul_mem_monomialDomain _
      (torusChartCoordinates_mem_coordinateTorus b g) hchange.1
  · rw [chartChange_mul_torusCoordinates b a g hchange.1, hchange.2]

private theorem torusChartCoordinates_one (a : ChartIndex) :
    torusChartCoordinates a 1 = 1 := by
  funext i
  simp [torusChartCoordinates, monomial, denseRawCoordinates]

private theorem torusChartCoordinates_mul (a : ChartIndex) (g h : DenseTorus) :
    torusChartCoordinates a (g * h) =
      torusChartCoordinates a g * torusChartCoordinates a h := by
  change monomial (dualMatrix a) (denseRawCoordinates (g * h)) =
    monomial (dualMatrix a) (denseRawCoordinates g) *
      monomial (dualMatrix a) (denseRawCoordinates h)
  rw [show denseRawCoordinates (g * h) = denseRawCoordinates g * denseRawCoordinates h by rfl,
    monomial_mul]

public theorem carrierTorusActionFun_one (p : Carrier) : carrierTorusActionFun 1 p = p := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierTorusActionFun_inclusion, torusChartCoordinates_one, one_mul]

public theorem carrierTorusActionFun_mul (g h : DenseTorus) (p : Carrier) :
    carrierTorusActionFun (g * h) p =
      carrierTorusActionFun g (carrierTorusActionFun h p) := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  rw [carrierTorusActionFun_inclusion, carrierTorusActionFun_inclusion,
    carrierTorusActionFun_inclusion, torusChartCoordinates_mul]
  congr 1
  simp [mul_assoc]

/-- The algebraic torus action on the glued carrier. -/
public noncomputable def carrierTorusAction : DenseTorus →* Equiv.Perm Carrier where
  toFun g :=
    { toFun := carrierTorusActionFun g
      invFun := carrierTorusActionFun g⁻¹
      left_inv p := by
        rw [← carrierTorusActionFun_mul]
        simpa using carrierTorusActionFun_one p
      right_inv p := by
        rw [← carrierTorusActionFun_mul]
        simpa using carrierTorusActionFun_one p }
  map_one' := by
    ext p
    exact carrierTorusActionFun_one p
  map_mul' g h := by
    apply Equiv.ext
    exact carrierTorusActionFun_mul g h

public theorem carrierTorusAction_torus (g x : DenseTorus) :
    carrierTorusAction g (carrierTorusEmbedding x) = carrierTorusEmbedding (g * x) := by
  change carrierTorusActionFun g (carrierTorusEmbedding x) = _
  rw [carrierTorusEmbedding_eq_inclusion_torusChartCoordinates baseChart,
    carrierTorusActionFun_inclusion,
    carrierTorusEmbedding_eq_inclusion_torusChartCoordinates baseChart,
    torusChartCoordinates_mul]

public theorem carrierHeight_torusAction (g : DenseTorus) (p : Carrier) :
    carrierHeight (carrierTorusAction g p) = (g 2 : ℂ) * carrierHeight p := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective p
  change carrierHeight (carrierTorusActionFun g (inclusion a z)) = _
  rw [carrierTorusActionFun_inclusion, carrierHeight_inclusion, carrierHeight_inclusion,
    rawHeight]
  have hg := carrierHeight_torus g
  rw [carrierTorusEmbedding_eq_inclusion_torusChartCoordinates a g,
    carrierHeight_inclusion, rawHeight] at hg
  change
    (torusChartCoordinates a g 0 * z 0) *
        (torusChartCoordinates a g 1 * z 1) *
      (torusChartCoordinates a g 2 * z 2) = _
  rw [← hg]
  simp only [rawHeight]
  ring

/-- Coordinatewise multiplication in one affine chart. -/
public def torusScale (a : ChartIndex) (g : DenseTorus) (z : ComplexModel) : ComplexModel :=
  rawToComplexModel (torusChartCoordinates a g * rawToComplexModel.symm z)

public theorem torusScale_contMDiff (a : ChartIndex) (g : DenseTorus) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (torusScale a g) := by
  rw [contMDiff_iff_contDiff]
  unfold torusScale
  fun_prop

public theorem carrierTorusAction_mem_toricChart
    (g : DenseTorus) (a : ChartIndex) {p : Carrier} :
    letI := chartedSpace
    p ∈ (toricChart a).source → carrierTorusAction g p ∈ (toricChart a).source := by
  let _ := chartedSpace
  intro hp
  rw [toricChart_source] at hp ⊢
  obtain ⟨z, rfl⟩ := hp
  rw [show carrierTorusAction g (inclusion a z) =
    carrierTorusActionFun g (inclusion a z) from rfl, carrierTorusActionFun_inclusion]
  exact Set.mem_range_self _

public theorem toricChart_carrierTorusAction
    (g : DenseTorus) (a : ChartIndex) {p : Carrier} :
    letI := chartedSpace
    p ∈ (toricChart a).source →
      toricChart a (carrierTorusAction g p) = torusScale a g (toricChart a p) := by
  let _ := chartedSpace
  intro hp
  rw [toricChart_source] at hp
  obtain ⟨z, rfl⟩ := hp
  change toricChart a (carrierTorusActionFun g (inclusion a z)) = _
  rw [carrierTorusActionFun_inclusion, toricChart_inclusion, toricChart_inclusion]
  simp [torusScale]

/-- Every fixed torus element acts biholomorphically on the glued carrier. -/
public theorem carrierTorusAction_contMDiff (g : DenseTorus) :
    letI := chartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (carrierTorusAction g) := by
  let _ := chartedSpace
  intro p
  obtain ⟨a, hp⟩ := toricChart_cover p
  have hchart : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (toricChart a) p :=
    (toricChart a).contMDiffOn_toFun.contMDiffAt
      ((toricChart a).open_source.mem_nhds hp)
  have hscale := (torusScale_contMDiff a g).contMDiffAt.comp p hchart
  have htarget : torusScale a g (toricChart a p) ∈ (toricChart a).target := by
    rw [toricChart_target]
    exact Set.mem_univ _
  have hinv : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (toricChart a).invFun
      (torusScale a g (toricChart a p)) :=
    (toricChart a).contMDiffOn_invFun.contMDiffAt
      ((toricChart a).open_target.mem_nhds htarget)
  have hcomp := hinv.comp p hscale
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(toricChart a).open_source.mem_nhds hp] with q hq
  have haction := carrierTorusAction_mem_toricChart g a hq
  calc
    carrierTorusAction g q =
        (toricChart a).invFun (toricChart a (carrierTorusAction g q)) :=
      ((toricChart a).left_inv haction).symm
    _ = (toricChart a).invFun (torusScale a g (toricChart a q)) := by
      rw [toricChart_carrierTorusAction g a hq]

private theorem evaluateCharacter_comp_contMDiff
    {N : Type*} [TopologicalSpace N] [ChartedSpace ComplexModel N]
    (c : N → DenseTorus)
    (hc : ∀ i, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun p : N ↦ (c p i : ℂ)))
    (m : FanLattice) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞
      (fun p : N ↦ (evaluateCharacter m (c p) : ℂ)) := by
  have hi (i : Fin 3) : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun p : N ↦ (c p i : ℂ) ^ m i) := by
    intro p
    have hz : AnalyticAt ℂ (fun z : ℂ ↦ z ^ m i) (c p i : ℂ) :=
      analyticAt_id.zpow (Units.ne_zero (c p i))
    exact hz.contDiffAt.contMDiffAt.comp p ((hc i).contMDiffAt)
  convert contMDiff_finsetProd (t := Finset.univ)
    (f := fun i (p : N) ↦ (c p i : ℂ) ^ m i) (fun i _ ↦ hi i) using 1
  funext p
  simp [evaluateCharacter]

private theorem torusChartCoordinates_comp_contMDiff
    {N : Type*} [TopologicalSpace N] [ChartedSpace ComplexModel N]
    (c : N → DenseTorus)
    (hc : ∀ i, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun p : N ↦ (c p i : ℂ)))
    (a : ChartIndex) (i : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞
      (fun p : N ↦ torusChartCoordinates a (c p) i) := by
  convert evaluateCharacter_comp_contMDiff c hc (a2DualCharacter a.1 a.2 i) using 1
  funext p
  simp [torusChartCoordinates, monomial, dualMatrix, evaluateCharacter, denseRawCoordinates]

/-- A point-dependent torus action is holomorphic whenever its three intrinsic torus
coordinates are holomorphic. -/
public theorem carrierVariableTorusAction_contMDiff :
    letI := chartedSpace
    ∀ (U : TopologicalSpace.Opens Carrier) (c : U → DenseTorus),
      (∀ i, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ℂ) ∞ (fun p : U ↦ (c p i : ℂ))) →
      ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞
        (fun p : U ↦ carrierTorusAction (c p) (p : Carrier)) := by
  let _ := chartedSpace
  intro U c hc p
  obtain ⟨a, hp⟩ := toricChart_cover (p : Carrier)
  have hval : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (fun q : U ↦ (q : Carrier)) :=
    contMDiff_subtype_val
  have hchart : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun q : U ↦ toricChart a (q : Carrier)) p :=
    ((toricChart a).contMDiffOn_toFun.contMDiffAt
      ((toricChart a).open_source.mem_nhds hp)).comp p hval.contMDiffAt
  have hlinearSymm : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ RawCoordinates) ∞ rawToComplexModel.symm :=
    contMDiff_iff_contDiff.mpr rawToComplexModel.symm.contDiff
  have hrawChart : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ RawCoordinates) ∞
      (fun q : U ↦ rawToComplexModel.symm (toricChart a (q : Carrier))) p :=
    hlinearSymm.contMDiffAt.comp p hchart
  have hrawCoord (i : Fin 3) : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞
      (fun q : U ↦ rawToComplexModel.symm (toricChart a (q : Carrier)) i) p := by
    have happly : ContMDiff (modelWithCornersSelf ℂ RawCoordinates)
        (modelWithCornersSelf ℂ ℂ) ∞ (fun z : RawCoordinates ↦ z i) :=
      contMDiff_iff_contDiff.mpr (contDiff_apply ℂ ℂ i)
    exact happly.contMDiffAt.comp p hrawChart
  have hscaledRaw : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ RawCoordinates) ∞
      (fun q : U ↦ torusChartCoordinates a (c q) *
        rawToComplexModel.symm (toricChart a (q : Carrier))) p := by
    rw [contMDiffAt_pi_space]
    intro i
    exact ((torusChartCoordinates_comp_contMDiff c hc a i).contMDiffAt).mul (hrawCoord i)
  have hlinear : ContMDiff (modelWithCornersSelf ℂ RawCoordinates)
      (modelWithCornersSelf ℂ ComplexModel) ∞ rawToComplexModel :=
    contMDiff_iff_contDiff.mpr rawToComplexModel.contDiff
  have hscaled : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun q : U ↦ torusScale a (c q) (toricChart a (q : Carrier))) p :=
    hlinear.contMDiffAt.comp p hscaledRaw
  have htarget : torusScale a (c p) (toricChart a (p : Carrier)) ∈
      (toricChart a).target := by
    rw [toricChart_target]
    exact Set.mem_univ _
  have hinv : ContMDiffAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (toricChart a).invFun
      (torusScale a (c p) (toricChart a (p : Carrier))) :=
    (toricChart a).contMDiffOn_invFun.contMDiffAt
      ((toricChart a).open_target.mem_nhds htarget)
  have hcomp := hinv.comp p hscaled
  apply hcomp.congr_of_eventuallyEq
  have hopen : IsOpen {q : U | (q : Carrier) ∈ (toricChart a).source} :=
    (toricChart a).open_source.preimage continuous_subtype_val
  filter_upwards [hopen.mem_nhds hp] with q hq
  have haction := carrierTorusAction_mem_toricChart (c q) a hq
  calc
    carrierTorusAction (c q) (q : Carrier) =
        (toricChart a).invFun (toricChart a (carrierTorusAction (c q) (q : Carrier))) :=
      ((toricChart a).left_inv haction).symm
    _ = (toricChart a).invFun (torusScale a (c q) (toricChart a (q : Carrier))) := by
      rw [toricChart_carrierTorusAction (c q) a hq]

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
