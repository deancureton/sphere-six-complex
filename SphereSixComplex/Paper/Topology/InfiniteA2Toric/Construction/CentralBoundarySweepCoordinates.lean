module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryHomology
public import SphereSixComplex.Prerequisites.Topology.MappingTorusTwoSliceBoundary
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverBoundaryCoordinates
public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundaryPositiveGenerator
public import SphereSixComplex.Prerequisites.Topology.NormalizedCircleProductCross
public import SphereSixComplex.Prerequisites.Topology.PositiveCircleProductSwap
public import Mathlib.Analysis.Convex.PathConnected
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryAction
import all SphereSixComplex.Prerequisites.Topology.MappingTorusTwoSliceBoundary
import all SphereSixComplex.Prerequisites.Topology.IntervalClutchingQuotientCore
import all SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryCharts

@[expose] public section
noncomputable section
open Set Topology TopologicalSpace ContinuousMap CategoryTheory
open scoped OnePoint unitInterval ContinuousMap
open SphereSixComplex.Periods
open SphereSixComplex.BinaryOpenCover
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def lowerMeridian (i : Fin 3) : Path (mk 0 (0 : ℂ)) (mk i (1 : ℂ)) :=
  ((Path.segment (0 : ℂ) 1).map
    ((continuous_mk.comp (continuous_const.prodMk OnePoint.continuous_coe)) :
      Continuous (fun z : ℂ => mk i (z : OnePoint ℂ)))).cast (mk_zero i).symm rfl

def upperMeridian (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Path (mk i (1 : ℂ)) (mk 0 ∞) :=
  ((Path.segment (1 : ℂ) 0).map
    (continuous_subtype_val.comp ((isQuotientMap_reciprocalChart W).continuous.comp
      (continuous_const.prodMk continuous_id)))).cast
      (by simpa using (reciprocalChart_coe_of_ne_zero W i 1 one_ne_zero).symm)
      (reciprocalChart_zero W i).symm

/-- The positive-real meridian in the selected sphere, using its two affine charts. -/
def meridian (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Path (mk 0 (0 : ℂ)) (mk 0 ∞) :=
  (lowerMeridian i).trans (upperMeridian W i)


@[simp] theorem lowerMeridian_apply (i : Fin 3) (t : unitInterval) :
    lowerMeridian i t = mk i (((t : ℝ) : ℂ) : OnePoint ℂ) := by
  simp [lowerMeridian, Path.segment, AffineMap.lineMap_apply]

@[simp] theorem upperMeridian_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (t : unitInterval) :
    upperMeridian W i t = (reciprocalChart W (i, 1 - ((t : ℝ) : ℂ)) : Spheres) := by
  simp [upperMeridian, Path.segment, AffineMap.lineMap_apply, sub_eq_add_neg, add_comm]

theorem lowerMeridian_mem_finitePart (i : Fin 3) (t : unitInterval) :
    lowerMeridian i t ∈ finitePart := by
  rw [lowerMeridian_apply, mk_mem_finitePart]
  exact OnePoint.coe_ne_infty _

theorem upperMeridian_mem_reciprocalPart
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (t : unitInterval) :
    upperMeridian W i t ∈ reciprocalPart := by
  rw [upperMeridian_apply]
  exact (reciprocalChart W _).2


theorem reciprocalChart_mem_finitePart_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (z : ℂ) :
    (reciprocalChart W (i, z) : Spheres) ∈ finitePart ↔ z ≠ 0 := by
  change (reciprocalChart W (i, z) : Spheres) ≠ mk 0 ∞ ↔ z ≠ 0
  rw [← reciprocalChart_zero W 0]
  simp only [ne_eq, Subtype.coe_inj, reciprocalChart_eq_iff, Prod.mk.injEq, and_true]
  tauto

theorem lowerMeridian_mem_reciprocalPart_iff (i : Fin 3) (t : unitInterval) :
    lowerMeridian i t ∈ reciprocalPart ↔ t ≠ 0 := by
  rw [lowerMeridian_apply, mk_mem_reciprocalPart]
  simp

theorem upperMeridian_mem_finitePart_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (t : unitInterval) :
    upperMeridian W i t ∈ finitePart ↔ t ≠ 1 := by
  rw [upperMeridian_apply, reciprocalChart_mem_finitePart_iff]
  rw [sub_ne_zero]
  apply not_congr
  constructor
  · intro h
    apply Subtype.ext
    exact_mod_cast h.symm
  · rintro rfl
    rfl


theorem meridian_mem_finitePart_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (t : unitInterval) :
    meridian W i t ∈ finitePart ↔ t ≠ 1 := by
  rw [meridian, Path.trans_apply]
  split_ifs with ht
  · refine iff_of_true (lowerMeridian_mem_finitePart _ _) ?_
    intro h
    have he := congrArg (fun s : unitInterval => (s : ℝ)) h
    change (t : ℝ) = 1 at he
    linarith
  · rw [upperMeridian_mem_finitePart_iff]
    simp only [ne_eq, Subtype.ext_iff]
    change (2 * (t : ℝ) - 1 ≠ 1) ↔ (t : ℝ) ≠ 1
    constructor <;> intro h he <;> apply h <;> linarith

theorem meridian_mem_reciprocalPart_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (t : unitInterval) :
    meridian W i t ∈ reciprocalPart ↔ t ≠ 0 := by
  rw [meridian, Path.trans_apply]
  split_ifs with ht
  · rw [lowerMeridian_mem_reciprocalPart_iff]
    simp only [ne_eq, Subtype.ext_iff]
    change (2 * (t : ℝ) ≠ 0) ↔ (t : ℝ) ≠ 0
    constructor <;> intro h he <;> apply h <;> linarith
  · refine iff_of_true (upperMeridian_mem_reciprocalPart _ _ _) ?_
    intro h
    have he := congrArg (fun s : unitInterval => (s : ℝ)) h
    change (t : ℝ) = 0 at he
    linarith


/-- The effective torus action in the three-sphere model of the actual boundary. -/
def phaseMap (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C((Fin 2 → Circle) × Spheres, Spheres) :=
  (⟨(homeomorph W).symm, (homeomorph W).symm.continuous⟩ : C(_, _)).comp
    ((centralBoundaryPhaseMap W).comp
      ((ContinuousMap.id (Fin 2 → Circle)).prodMap ⟨fun x => homeomorph W x, (homeomorph W).continuous⟩))

theorem homeomorph_phaseMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (x : Spheres) :
    ((homeomorph W (phaseMap W (k,x))) : ActualLocalCuspCentralOrbitQuotient W) =
      centralCompactOrbitMap W k (homeomorph W x) := by
  change ((homeomorph W ((homeomorph W).symm
    (centralBoundaryPhaseMap W (k, homeomorph W x)))) : ActualLocalCuspCentralOrbitQuotient W) = _
  erw [(homeomorph W).apply_symm_apply]
  rfl

theorem phaseMap_mk_coe
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (i : Fin 3) (z : ℂ) :
    phaseMap W (k, mk i (z : OnePoint ℂ)) =
      mk i ((![((k 0 : ℂ)⁻¹ * (k 1 : ℂ)⁻¹), (k 0 : ℂ), (k 1 : ℂ)] i * z : ℂ) : OnePoint ℂ) := by
  apply (homeomorph W).injective
  apply Subtype.ext
  rw [homeomorph_phaseMap, homeomorph_mk_coe, homeomorph_mk_coe]
  change Quotient.mk _ (centralCompactMap W k (axisPoint W false i z)) =
    Quotient.mk _ (axisPoint W false i _)
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  change carrierTorusActionFun _ (inclusion (false,0) (singleAxis i z)) = _
  rw [carrierTorusActionFun_inclusion]
  have hw : torusChartCoordinates (false,0) (compactTorusEmbedding (effectivePhaseSection k)) =
      ![((k 0 : ℂ)⁻¹ * (k 1 : ℂ)⁻¹), (k 0 : ℂ), (k 1 : ℂ)] := by
    ext j
    fin_cases j <;>
      simp [torusChartCoordinates, monomial, dualMatrix, a2DualCharacter, denseRawCoordinates,
        compactTorusEmbedding, effectivePhaseSection, Fin.prod_univ_succ]
  rw [hw]
  apply congrArg (inclusion (false,0))
  ext j
  by_cases h : j = i
  · subst j
    simp [singleAxis]
  · simp [singleAxis, h]


@[simp] theorem phaseMap_mk_infty
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) : phaseMap W (k, mk 0 ∞) = mk 0 ∞ := by
  apply (homeomorph W).injective
  apply Subtype.ext
  rw [homeomorph_phaseMap, homeomorph_mk_infty,
    centralCompactOrbitMap_origin]

@[simp] theorem phaseMap_mk_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) : phaseMap W (k, mk 0 (0 : ℂ)) = mk 0 (0 : ℂ) := by
  rw [phaseMap_mk_coe, mul_zero]

theorem phaseMap_mem_finitePart_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (x : Spheres) : phaseMap W (k,x) ∈ finitePart ↔ x ∈ finitePart := by
  induction x using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨i,z⟩
    change phaseMap W (k,mk i z) ∈ finitePart ↔ mk i z ∈ finitePart
    induction z using OnePoint.rec with
    | infty => rw [mk_infty, phaseMap_mk_infty]
    | coe z => simp [phaseMap_mk_coe, mk_mem_finitePart]

theorem phaseMap_mem_reciprocalPart_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : Fin 2 → Circle) (x : Spheres) : phaseMap W (k,x) ∈ reciprocalPart ↔ x ∈ reciprocalPart := by
  induction x using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨i,z⟩
    change phaseMap W (k,mk i z) ∈ reciprocalPart ↔ mk i z ∈ reciprocalPart
    induction z using OnePoint.rec with
    | infty => rw [mk_infty, phaseMap_mk_infty]
    | coe z =>
      rw [phaseMap_mk_coe, mk_mem_reciprocalPart, mk_mem_reciprocalPart]
      fin_cases i <;> simp [Circle.coe_ne_zero]


variable {F : Type} [TopologicalSpace F]

def phaseOrbit (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) : C(Spheres, C(F, Spheres)) :=
  (⟨fun p : Spheres × F => phaseMap W (k p.2, p.1),
    (phaseMap W).continuous.comp
      ((k.continuous.comp continuous_snd).prodMk continuous_fst)⟩ : C(Spheres × F, Spheres)).curry

def phaseMeridian (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i : Fin 3) :
    Path (ContinuousMap.const F (mk 0 (0 : ℂ))) (ContinuousMap.const F (mk 0 ∞)) :=
  ((meridian W i).map (phaseOrbit W k).continuous).cast
    (by ext x; exact (phaseMap_mk_zero W (k x)).symm)
    (by ext x; exact (phaseMap_mk_infty W (k x)).symm)

def phaseMeridianLoop (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3) :
    Path (ContinuousMap.const F (mk 0 (0 : ℂ))) (ContinuousMap.const F (mk 0 (0 : ℂ))) :=
  (phaseMeridian W k i).trans (phaseMeridian W k j).symm

@[simp] theorem phaseMeridian_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i : Fin 3) (t : unitInterval) (x : F) :
    phaseMeridian W k i t x = phaseMap W (k x, meridian W i t) := rfl

@[simp] theorem meridian_half
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    meridian W i ⟨1 / 2, by norm_num⟩ = mk i (1 : ℂ) := by
  rw [meridian, Path.trans_apply]
  norm_num


@[simp] theorem phaseMeridianLoop_quarter
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3) (x : F) :
    phaseMeridianLoop W k i j uQuarter x = phaseMap W (k x, mk i (1 : ℂ)) := by
  rw [phaseMeridianLoop, Path.trans_apply]
  norm_num [uQuarter]

@[simp] theorem phaseMeridianLoop_threeQuarters
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3) (x : F) :
    phaseMeridianLoop W k i j uThreeQuarters x = phaseMap W (k x, mk j (1 : ℂ)) := by
  rw [phaseMeridianLoop, Path.trans_apply]
  norm_num [uThreeQuarters, Path.symm_apply, unitInterval.symm]


theorem phaseMeridianLoop_vertex
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3)
    (t : unitInterval) (ht : t ∈ vertexBand) (x : F) :
    phaseMeridianLoop W k i j t x ∈ finitePart := by
  have ht' : (t : ℝ) < 1 / 3 ∨ 2 / 3 < (t : ℝ) := ht
  rw [phaseMeridianLoop, Path.trans_apply]
  split_ifs with h
  · rw [phaseMeridian_apply, phaseMap_mem_finitePart_iff, meridian_mem_finitePart_iff]
    intro he
    have he' := congrArg (fun s : unitInterval => (s : ℝ)) he
    change 2 * (t : ℝ) = 1 at he'
    rcases ht' with ht' | ht' <;> linarith
  · erw [Path.symm_apply, Function.comp_apply, phaseMeridian_apply, phaseMap_mem_finitePart_iff,
      meridian_mem_finitePart_iff]
    intro he
    have he' := congrArg (fun s : unitInterval => (s : ℝ)) he
    change 1 - (2 * (t : ℝ) - 1) = 1 at he'
    rcases ht' with ht' | ht' <;> linarith

theorem phaseMeridianLoop_edge
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3)
    (t : unitInterval) (ht : t ∈ edgeBand) (x : F) :
    phaseMeridianLoop W k i j t x ∈ reciprocalPart := by
  have ht' : 1 / 6 < (t : ℝ) ∧ (t : ℝ) < 5 / 6 := ht
  rw [phaseMeridianLoop, Path.trans_apply]
  split_ifs with h
  · rw [phaseMeridian_apply, phaseMap_mem_reciprocalPart_iff, meridian_mem_reciprocalPart_iff]
    intro he
    have he' := congrArg (fun s : unitInterval => (s : ℝ)) he
    change 2 * (t : ℝ) = 0 at he'
    linarith [ht'.1]
  · erw [Path.symm_apply, Function.comp_apply, phaseMeridian_apply, phaseMap_mem_reciprocalPart_iff,
      meridian_mem_reciprocalPart_iff]
    intro he
    have he' := congrArg (fun s : unitInterval => (s : ℝ)) he
    change 1 - (2 * (t : ℝ) - 1) = 0 at he'
    linarith [ht'.2]


/-- The integral phase character on the selected lower affine axis. -/
def phaseCharacter (k : C(F, Fin 2 → Circle)) (i : Fin 3) : C(F, ℂˣ) where
  toFun x := Circle.toUnits (![(k x 0 * k x 1)⁻¹, k x 0, k x 1] i)
  continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr (by
    fin_cases i <;> fun_prop)

@[simp] theorem phaseCharacter_coe (k : C(F, Fin 2 → Circle)) (i : Fin 3) (x : F) :
    (phaseCharacter k i x : ℂ) =
      ![((k x 0 : ℂ)⁻¹ * (k x 1 : ℂ)⁻¹), (k x 0 : ℂ), (k x 1 : ℂ)] i := by
  fin_cases i <;> simp [phaseCharacter, mul_inv_rev, mul_comm]

theorem phaseMap_axisUnit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i : Fin 3) (x : F) :
    phaseMap W (k x, mk i (1 : ℂ)) =
      (overlapHomeomorph (i, phaseCharacter k i x) : Spheres) := by
  rw [phaseMap_mk_coe, mul_one, overlapHomeomorph_apply, phaseCharacter_coe]


theorem homologyEquiv_ambientBoundary
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (hn : n ≠ 0) (x : IntegralSingularHomology (n + 1) Spheres) :
    integralSingularHomologyEquiv n overlapHomeomorph (homologyEquiv W n hn x) =
      ConcreteCategory.hom
        ((openCoverHomologyComparisonOfCover finiteOpen_sup_reciprocalOpen).boundary n ≫
          (opensIntersectionHomologyIso finiteOpen reciprocalOpen n).inv) x := by
  rw [homologyEquiv_apply]
  exact ((openCoverHomologyComparisonOfCover finiteOpen_sup_reciprocalOpen).toIntegralMayerVietorisData
    finiteOpen_sup_reciprocalOpen).legacyBoundary_unionHomeomorph_symm n x


theorem homologyEquiv_phaseMeridianLoop [LocallyCompactSpace F]
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3) (n : ℕ) (hn : n ≠ 0)
    (x : IntegralSingularHomology (n + 1) (CircleMappingTorus (Homeomorph.refl F))) :
    homologyEquiv W n hn
      (integralSingularHomologyMap (n + 1)
        (identityMappingTorusMapOfLoop (phaseMeridianLoop W k i j)) x) =
      integralSingularHomologyMap n ((ContinuousMap.const F i).prodMk (phaseCharacter k i))
        ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x) -
      integralSingularHomologyMap n ((ContinuousMap.const F j).prodMk (phaseCharacter k j))
        ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x) := by
  let hU := phaseMeridianLoop_vertex W k i j
  let hV := phaseMeridianLoop_edge W k i j
  have hb := circleLoop_boundary_twoSlices (Y := TopCat.of Spheres)
    (phaseMeridianLoop W k i j) finiteOpen reciprocalOpen finiteOpen_sup_reciprocalOpen
    hU hV n x
  apply (integralSingularHomologyEquiv n overlapHomeomorph).injective
  rw [homologyEquiv_ambientBoundary, map_sub]
  change ConcreteCategory.hom (opensIntersectionHomologyIso finiteOpen reciprocalOpen n).inv
    (ConcreteCategory.hom ((openCoverHomologyComparisonOfCover finiteOpen_sup_reciprocalOpen).boundary n)
      (integralSingularHomologyMap (n + 1) _ x)) = _
  rw [hb, map_sub]
  congr 1
  · change integralSingularHomologyMap n
      ⟨(opensIntersectionHomeomorph finiteOpen reciprocalOpen).symm,
        (opensIntersectionHomeomorph finiteOpen reciprocalOpen).symm.continuous⟩
      (integralSingularHomologyMap n _ _) =
        integralSingularHomologyMap n ⟨overlapHomeomorph, overlapHomeomorph.continuous⟩
          (integralSingularHomologyMap n _ _)
    rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
    apply congrArg (fun f : C(F, ↥(finitePart ∩ reciprocalPart)) =>
      integralSingularHomologyMap n f
        ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x))
    ext y
    exact (phaseMeridianLoop_quarter W k i j y).trans (phaseMap_axisUnit W k i y)
  · change integralSingularHomologyMap n
      ⟨(opensIntersectionHomeomorph finiteOpen reciprocalOpen).symm,
        (opensIntersectionHomeomorph finiteOpen reciprocalOpen).symm.continuous⟩
      (integralSingularHomologyMap n _ _) =
        integralSingularHomologyMap n ⟨overlapHomeomorph, overlapHomeomorph.continuous⟩
          (integralSingularHomologyMap n _ _)
    rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang]
    apply congrArg (fun f : C(F, ↥(finitePart ∩ reciprocalPart)) =>
      integralSingularHomologyMap n f
        ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x))
    ext y
    exact (phaseMeridianLoop_threeQuarters W k i j y).trans (phaseMap_axisUnit W k j y)


theorem homologyTwoEquiv_phaseMeridianLoop [LocallyCompactSpace F]
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3)
    (x : IntegralSingularHomology 2 (CircleMappingTorus (Homeomorph.refl F))) :
    homologyTwoEquiv W
      (integralSingularHomologyMap 2 (identityMappingTorusMapOfLoop (phaseMeridianLoop W k i j)) x) =
      Pi.single i (Complex.unitsHomologyOneEquiv
        (integralSingularHomologyMap 1 (phaseCharacter k i)
          ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) 1).boundary x))) -
      Pi.single j (Complex.unitsHomologyOneEquiv
        (integralSingularHomologyMap 1 (phaseCharacter k j)
          ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) 1).boundary x))) := by
  let e := IntegralSingularHomology.discreteProductEquiv (Fin 3) ℂˣ 1
  let v := AddEquiv.piCongrRight (fun _ : Fin 3 => Complex.unitsHomologyOneEquiv)
  change v (e (homologyEquiv W 1 one_ne_zero _)) = _
  rw [homologyEquiv_phaseMeridianLoop, map_sub, map_sub]
  have h (l : Fin 3) (y : IntegralSingularHomology 1 F) :
      v (e (integralSingularHomologyMap 1 ((ContinuousMap.const F l).prodMk (phaseCharacter k l)) y)) =
        Pi.single l (Complex.unitsHomologyOneEquiv (integralSingularHomologyMap 1 (phaseCharacter k l) y)) := by
    have hf : (ContinuousMap.const F l).prodMk (phaseCharacter k l) =
        ((ContinuousMap.const ℂˣ l).prodMk (ContinuousMap.id ℂˣ)).comp (phaseCharacter k l) := rfl
    rw [hf, ← integralSingularHomologyMap_comp_wang]
    change v ((IntegralSingularHomology.discreteProductEquiv (Fin 3) ℂˣ 1) _) = _
    rw [IntegralSingularHomology.discreteProductEquiv_component]
    ext m
    change Complex.unitsHomologyOneEquiv
      ((Pi.single l (integralSingularHomologyMap 1 (phaseCharacter k l) y) :
        Fin 3 → IntegralSingularHomology 1 ℂˣ) m) =
      (Pi.single l (Complex.unitsHomologyOneEquiv
        (integralSingularHomologyMap 1 (phaseCharacter k l) y)) : Fin 3 → ℤ) m
    by_cases hm : m = l <;> simp [hm]
  rw [h, h]


def coordinatePhase (a : Fin 2) : C(UnitAddCircle, Fin 2 → Circle) where
  toFun t l := if l = a then AddCircle.toCircle t else 1
  continuous_toFun := by
    apply continuous_pi
    intro l
    by_cases h : l = a
    · simp only [h, ite_true]
      exact AddCircle.continuous_toCircle
    · simp only [h, ite_false]
      exact continuous_const

def phaseWeights (a : Fin 2) : Fin 3 → ℤ := ![![-1,1,0], ![-1,0,1]] a

theorem phaseCharacter_coordinatePhase (a : Fin 2) (i : Fin 3) :
    phaseCharacter (coordinatePhase a) i =
      CircleExponential.toUnits.comp (StandardCircleHomologyLiftDegree.unitCirclePowerMap (phaseWeights a i)) := by
  ext t
  fin_cases a <;> fin_cases i <;>
    simp [phaseCharacter, coordinatePhase, phaseWeights, CircleExponential.toUnits,
      StandardCircleHomologyLiftDegree.unitCirclePowerMap, AddCircle.toCircle_neg]

theorem phaseCharacter_winding (a : Fin 2) (i : Fin 3) :
    Complex.unitsHomologyOneEquiv
      (integralSingularHomologyMap 1 (phaseCharacter (coordinatePhase a) i)
        StandardCircleHomologyLiftDegree.unitCirclePositiveHomologyClass) = phaseWeights a i := by
  rw [phaseCharacter_coordinatePhase, ← integralSingularHomologyMap_comp_wang,
    Complex.unitsHomologyOneEquiv_toUnits,
    StandardCircleHomologyLiftDegree.unitCirclePowerMap_positiveHomologyClass,
    StandardCircleHomologyLiftDegree.unitCircleHomologyWinding_integerLoop]


open StandardTorusHomology StandardCircleHomologyLiftDegree
open SphereSixComplex.Topology CircleProductIdentityMappingTorus PositiveCircleCross

def meridianSweep (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Fin 2) (i j : Fin 3) : IntegralSingularHomology 2 Spheres :=
  integralSingularHomologyMap 2
    (identityMappingTorusMapOfLoop
      (phaseMeridianLoop W ((coordinatePhase a).comp
        ⟨stdTorusOneHomeomorph, stdTorusOneHomeomorph.continuous⟩) i j))
    (integralSingularHomologyMap 2
      ⟨circleProductIdentityMappingTorusHomeomorph,
        circleProductIdentityMappingTorusHomeomorph.continuous⟩ positiveCircleProductGenerator)

theorem homologyTwoEquiv_meridianSweep
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Fin 2) (i j : Fin 3) :
    homologyTwoEquiv W (meridianSweep W a i j) =
      Pi.single i (phaseWeights a i) - Pi.single j (phaseWeights a j) := by
  have hg : integralSingularHomologyMap 1
      ⟨stdTorusOneHomeomorph, stdTorusOneHomeomorph.continuous⟩ standardCircleHomologyGenerator =
      unitCirclePositiveHomologyClass := by
    apply unitCircleHomologyWinding_injective
    rw [standardCircleHomologyGenerator_winding, unitCircleHomologyWinding_positive]
  have hb : (circleMappingTorusWangPresentationOfCover (Homeomorph.refl (StdTorus 1)) 1).boundary
      (integralSingularHomologyMap 2
        ⟨circleProductIdentityMappingTorusHomeomorph,
          circleProductIdentityMappingTorusHomeomorph.continuous⟩ positiveCircleProductGenerator) =
      standardCircleHomologyGenerator :=
    CanonicalProductWangBoundarySlant.canonicalProductWangBoundary_positiveGenerator_core
  rw [meridianSweep, homologyTwoEquiv_phaseMeridianLoop, hb]
  have h (l : Fin 3) :
      Complex.unitsHomologyOneEquiv (integralSingularHomologyMap 1
        (phaseCharacter ((coordinatePhase a).comp
          ⟨stdTorusOneHomeomorph, stdTorusOneHomeomorph.continuous⟩) l)
        standardCircleHomologyGenerator) = phaseWeights a l := by
    change Complex.unitsHomologyOneEquiv (integralSingularHomologyMap 1
      ((phaseCharacter (coordinatePhase a) l).comp
        ⟨stdTorusOneHomeomorph, stdTorusOneHomeomorph.continuous⟩)
      standardCircleHomologyGenerator) = _
    rw [← integralSingularHomologyMap_comp_wang, hg, phaseCharacter_winding]
  rw [h, h]

def circleAction (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Fin 2) : C(UnitAddCircle × Spheres, Spheres) :=
  (phaseMap W).comp ((coordinatePhase a).prodMap (ContinuousMap.id Spheres))

theorem phaseMeridianLoop_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (k : C(F, Fin 2 → Circle)) (i j : Fin 3) (t : unitInterval) (x : F) :
    phaseMeridianLoop W k i j t x =
      phaseMap W (k x, ((meridian W i).trans (meridian W j).symm) t) := by
  simp only [phaseMeridianLoop, Path.trans_apply]
  split_ifs <;> rfl

theorem meridianSweep_map
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Fin 2) (i j : Fin 3) :
    (identityMappingTorusMapOfLoop
      (phaseMeridianLoop W ((coordinatePhase a).comp
        ⟨stdTorusOneHomeomorph, stdTorusOneHomeomorph.continuous⟩) i j)).comp
      ⟨circleProductIdentityMappingTorusHomeomorph,
        circleProductIdentityMappingTorusHomeomorph.continuous⟩ =
    ((circleAction W a).comp
      (circleProductMap (pathCircleMap ((meridian W i).trans (meridian W j).symm)))).comp
      positiveCircleProductSwap := by
  ext1 p
  let t : unitInterval := ⟨AddCircle.equivIco (1 : ℝ) 0 p.1,
    (AddCircle.equivIco (1 : ℝ) 0 p.1).2.1,
    le_of_lt (by simpa using (AddCircle.equivIco (1 : ℝ) 0 p.1).2.2)⟩
  have ht : ((t : ℝ) : UnitAddCircle) = p.1 := AddCircle.coe_equivIco
  have hp : p = (((t : ℝ) : UnitAddCircle), p.2) := Prod.ext ht.symm rfl
  rw [hp]
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    circleProductIdentityMappingTorusHomeomorph_interval]
  have hl : standardCirclePositiveLoop t = (fun _ ↦ ((t : ℝ) : UnitAddCircle)) := by
    ext l
    change (((t : ℝ) * ((1 : ℤ) : ℝ) : ℝ) : UnitAddCircle) = _
    simp only [Int.cast_one, mul_one]
  change phaseMeridianLoop W ((coordinatePhase a).comp
    ⟨stdTorusOneHomeomorph, stdTorusOneHomeomorph.continuous⟩) i j t p.2 =
    circleAction W a (p.2 0,
      pathCircleMap ((meridian W i).trans (meridian W j).symm)
        (fun _ ↦ ((t : ℝ) : UnitAddCircle)))
  rw [← hl, phaseMeridianLoop_apply, pathCircleMap_loop]
  rfl

theorem meridianSweep_eq_neg_circleSweepClass
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (a : Fin 2) (i j : Fin 3) :
    meridianSweep W a i j =
      -circleSweepClass (circleAction W a) ((meridian W i).trans (meridian W j).symm) := by
  rw [meridianSweep, integralSingularHomologyMap_comp_wang, meridianSweep_map,
    ← integralSingularHomologyMap_comp_wang, positiveCircleProductSwap_generator,
    map_neg, ← integralSingularHomologyMap_comp_wang]
  change -integralSingularHomologyMap 2 _ (positiveCircleCross _) = _
  rw [positiveCircleCross_eq_normalized, pathCircleMap_homology]
  rfl

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
