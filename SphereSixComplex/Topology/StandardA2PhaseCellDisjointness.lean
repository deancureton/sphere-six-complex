module

public import SphereSixComplex.Topology.StandardA2ToricCentralOrbitCellAtlasProof
public import SphereSixComplex.Topology.ConstructedA2HigherCellPartition

@[expose] public section
noncomputable section
open Set
namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

private theorem carrierOrigin_componentSupport (a : ChartIndex) :
    componentSupport constructedModel (inclusion a 0) =
      Set.range (a2Triangle a.1 a.2) := by
  let _ := chartedSpace
  have hchart : inclusion a 0 ∈ (toricChart a).source := by
    rw [toricChart_source]
    exact Set.mem_range_self _
  ext v
  change inclusion a 0 ∈ carrierCentralComponent v ↔ v ∈ Set.range (a2Triangle a.1 a.2)
  constructor
  · intro hp
    by_contra hn
    exact Set.disjoint_left.mp (otherCarrierCentralComponent_disjoint_chart a v hn) hp hchart
  · rintro ⟨i, rfl⟩
    apply (carrierCentralComponent_in_chart a i _ hchart).mpr
    rw [toricChart_inclusion]
    simp [rawToComplexModel]

private theorem a2Triangle_injective_for_origin (upper : Bool) (v : ToricLattice) :
    Function.Injective (a2Triangle upper v) := by
  intro i j h
  have hcone (k : Fin 3) :
      a2ConeMatrix upper v k i = a2ConeMatrix upper v k j := by
    exact congrFun (congrArg heightOneRay h) k
  have hmatrix := dualMatrix_mul_coneMatrix (upper, v)
  have hentry (k : Fin 3) :
      (1 : Matrix (Fin 3) (Fin 3) ℤ) k i = (1 : Matrix (Fin 3) (Fin 3) ℤ) k j := by
    rw [← hmatrix, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcone l]
  by_contra hij
  have hii := hentry i
  simp [hij] at hii

private theorem carrierOrigin_componentSupport_ncard (a : ChartIndex) :
    (componentSupport constructedModel (inclusion a 0)).ncard = 3 := by
  rw [carrierOrigin_componentSupport, Set.ncard_range_of_injective
    (a2Triangle_injective_for_origin a.1 a.2)]
  simp

public theorem actualCentralOrbit_support_eq_translate
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : actualLocalCuspCentralSubMulAction W)
    (h : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _) p =
      Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _) q) :
    ∃ k : ToricLattice, componentSupport constructedModel (p.1.1 : Carrier) =
      (fun v ↦ v + k) '' componentSupport constructedModel (q.1.1 : Carrier) := by
  have hr := Quotient.exact h
  change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at hr
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
  obtain ⟨g, rfl⟩ := hr
  exact ⟨shearVector g.toAdd, constructedA2ActualCentral_support_smul W g q⟩

public theorem actualCentralOrbit_eq_of_same_finite_support
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : actualLocalCuspCentralSubMulAction W)
    (T : Set ToricLattice) (hfin : T.Finite) (hne : T.Nonempty)
    (hp : componentSupport constructedModel (p.1.1 : Carrier) = T)
    (hq : componentSupport constructedModel (q.1.1 : Carrier) = T)
    (h : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _) p =
      Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _) q) : p = q := by
  have hr := Quotient.exact h
  change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at hr
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hr
  obtain ⟨g, hg⟩ := hr
  have hs := constructedA2ActualCentral_support_smul W g q
  rw [hg, hp, hq] at hs
  have hk : shearVector g.toAdd = 0 :=
    translation_eq_zero_of_finite_forward_invariant hfin hne (by
      intro v hv
      rw [hs]
      exact ⟨v, hv, rfl⟩)
  have hga : g.toAdd = 0 := by
    apply shearVector_injective
    rw [hk]
    ext i
    simp [shearVector, Matrix.mulVec]
  have hg1 : g = 1 := by exact hga
  simpa [hg1] using hg.symm

private theorem toricPair_eq_translate_imp
    {a b c d k : ToricLattice} (hab : a ≠ b)
    (h : ({a, b} : Set ToricLattice) = (fun v ↦ v + k) '' ({c, d} : Set ToricLattice)) :
    (a = c + k ∧ b = d + k) ∨ (a = d + k ∧ b = c + k) := by
  have ha : a ∈ (fun v ↦ v + k) '' ({c, d} : Set ToricLattice) := by
    rw [← h]
    simp
  have hb : b ∈ (fun v ↦ v + k) '' ({c, d} : Set ToricLattice) := by
    rw [← h]
    simp
  obtain ⟨u, hu, hua⟩ := ha
  obtain ⟨v, hv, hvb⟩ := hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (hab (hua.symm.trans hvb)).elim
  · exact Or.inl ⟨hua.symm, hvb.symm⟩
  · exact Or.inr ⟨hua.symm, hvb.symm⟩
  · exact (hab (hua.symm.trans hvb)).elim

private theorem edgeSupportZero_ne_translate_one (k : ToricLattice) :
    ({e₁, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₂} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := e₁) (b := e₂) (c := 0) (d := e₂)
      (by simp [e₁, e₂]) h with hcase | hcase
  · have h00 := congrFun hcase.1 0
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h10
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h01 h10
    omega

private theorem edgeSupportZero_ne_translate_two (k : ToricLattice) :
    ({e₁, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₁} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := e₁) (b := e₂) (c := 0) (d := e₁)
      (by simp [e₁, e₂]) h with hcase | hcase
  · have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h01 h11
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h00 h01 h11
    omega

private theorem edgeSupportOne_ne_translate_two (k : ToricLattice) :
    ({0, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₁} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := 0) (b := e₂) (c := 0) (d := e₁)
      (by
        intro heq
        have hcoord := congrFun heq 1
        simp [e₂] at hcoord) h with hcase | hcase
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h00 h01 h11
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h01 h10
    omega


public theorem constructedCentralPhaseFaceZeroOrbit_ne_oneOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1)
    (y : Fin 2 → ℝ) (hy : y ∈ Metric.ball 0 1) :
    constructedCentralPhaseFaceZeroOrbit W x ≠ constructedCentralPhaseFaceOneOrbit W y := by
  intro h
  obtain ⟨k, hk⟩ := actualCentralOrbit_support_eq_translate W
    (constructedCentralPhaseFaceZeroPoint W x) (constructedCentralPhaseFaceOnePoint W y) h
  change componentSupport constructedModel (constructedCentralPhaseFaceZeroCarrier x) =
    (fun v ↦ v + k) '' componentSupport constructedModel
      (constructedCentralPhaseFaceOneCarrier y) at hk
  rw [constructedCentralPhaseFaceZeroCarrier_componentSupport x hx,
    constructedCentralPhaseFaceOneCarrier_componentSupport y hy] at hk
  exact edgeSupportZero_ne_translate_one k hk

public theorem constructedCentralPhaseFaceZeroOrbit_ne_twoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1)
    (y : Fin 2 → ℝ) (hy : y ∈ Metric.ball 0 1) :
    constructedCentralPhaseFaceZeroOrbit W x ≠ constructedCentralPhaseFaceTwoOrbit W y := by
  intro h
  obtain ⟨k, hk⟩ := actualCentralOrbit_support_eq_translate W
    (constructedCentralPhaseFaceZeroPoint W x) (constructedCentralPhaseFaceTwoPoint W y) h
  change componentSupport constructedModel (constructedCentralPhaseFaceZeroCarrier x) =
    (fun v ↦ v + k) '' componentSupport constructedModel
      (constructedCentralPhaseFaceTwoCarrier y) at hk
  rw [constructedCentralPhaseFaceZeroCarrier_componentSupport x hx,
    constructedCentralPhaseFaceTwoCarrier_componentSupport y hy] at hk
  exact edgeSupportZero_ne_translate_two k hk

public theorem constructedCentralPhaseFaceOneOrbit_ne_twoOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1)
    (y : Fin 2 → ℝ) (hy : y ∈ Metric.ball 0 1) :
    constructedCentralPhaseFaceOneOrbit W x ≠ constructedCentralPhaseFaceTwoOrbit W y := by
  intro h
  obtain ⟨k, hk⟩ := actualCentralOrbit_support_eq_translate W
    (constructedCentralPhaseFaceOnePoint W x) (constructedCentralPhaseFaceTwoPoint W y) h
  change componentSupport constructedModel (constructedCentralPhaseFaceOneCarrier x) =
    (fun v ↦ v + k) '' componentSupport constructedModel
      (constructedCentralPhaseFaceTwoCarrier y) at hk
  rw [constructedCentralPhaseFaceOneCarrier_componentSupport x hx,
    constructedCentralPhaseFaceTwoCarrier_componentSupport y hy] at hk
  exact edgeSupportOne_ne_translate_two k hk

public theorem cayley_re_pos_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    0 < ((1 + z) / (1 - z)).re := by
  have hm : (1 : ℂ) - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp [he] at hz
  have hs : Complex.normSq z < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hd : 0 < Complex.normSq (1 - z) := Complex.normSq_pos.mpr hm
  have he : ((1 + z) / (1 - z)).re =
      (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    rw [Complex.div_re]
    field_simp [ne_of_gt hd]
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,
      Complex.sub_re, Complex.sub_im]
    ring
  rw [he]
  exact div_pos (sub_pos.mpr hs) hd

public theorem neg_sq_ne_nonnegReal {z : ℂ} (hz : 0 < z.re)
    {r : ℝ} (hr : 0 ≤ r) : -(z ^ 2) ≠ (r : ℂ) := by
  intro he
  have hi := congrArg Complex.im he
  have hre := congrArg Complex.re he
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hi hre
  have hzi : z.im = 0 := by nlinarith
  nlinarith [sq_pos_of_pos hz]

public theorem centralPhaseDiskLowerCoordinate_ne_nonnegReal
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) {r : ℝ} (hr : 0 ≤ r) :
    centralPhaseDiskLowerCoordinate x ≠ (r : ℂ) := by
  apply neg_sq_ne_nonnegReal _ hr
  apply cayley_re_pos_of_norm_lt_one
  rw [norm_centralPhaseDiskComplex]
  simpa [Metric.mem_ball, dist_zero_right] using hx

public theorem centralPhaseDiskUpperCoordinate_ne_nonnegReal
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1) {r : ℝ} (hr : 0 ≤ r) :
    centralPhaseDiskUpperCoordinate x ≠ (r : ℂ) := by
  apply neg_sq_ne_nonnegReal _ hr
  have h := cayley_re_pos_of_norm_lt_one (z := -centralPhaseDiskComplex x) (by
    rw [norm_neg, norm_centralPhaseDiskComplex]
    simpa [Metric.mem_ball, dist_zero_right] using hx)
  simpa [sub_eq_add_neg] using h

public theorem constructedCentralPhaseFaceZeroCarrier_ne_edgeZero
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1)
    {y : Fin 1 → ℝ} (hy : y ∈ Metric.closedBall 0 1) :
    constructedCentralPhaseFaceZeroCarrier x ≠ constructedCentralEdgeZeroCarrier y := by
  have hyabs : |y 0| ≤ 1 := by
    have h := (norm_le_pi_norm y 0).trans (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
    simpa only [Real.norm_eq_abs] using h
  have hp : 0 ≤ 1 + y 0 := by have := (abs_le.mp hyabs).1; linarith
  have hm : 0 ≤ 1 - y 0 := by have := (abs_le.mp hyabs).2; linarith
  intro h
  by_cases hx0 : x 0 ≤ 0 <;> by_cases hy0 : y 0 ≤ 0
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralEdgeZeroCarrier,
      hx0, hy0, ↓reduceIte, constructedCentralEdgeZeroLowerBranch] at h
    have he := congrFun ((inclusion_isOpenEmbedding (false, 0)).injective h) 0
    exact centralPhaseDiskLowerCoordinate_ne_nonnegReal hx hp he
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralEdgeZeroCarrier,
      hx0, hy0, ↓reduceIte, constructedCentralEdgeZeroUpperBranch] at h
    have he := ((inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp h).2
    have hi := congrArg Inv.inv he
    simp only [inv_inv, ← Complex.ofReal_inv] at hi
    exact centralPhaseDiskLowerCoordinate_ne_nonnegReal hx (inv_nonneg.mpr hm) hi.symm
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralEdgeZeroCarrier,
      hx0, hy0, ↓reduceIte, constructedCentralEdgeZeroLowerBranch] at h
    have he := ((inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 _ _).mp h.symm).2
    rw [← Complex.ofReal_inv] at he
    exact centralPhaseDiskUpperCoordinate_ne_nonnegReal hx (inv_nonneg.mpr hp) he
  · simp only [constructedCentralPhaseFaceZeroCarrier, constructedCentralEdgeZeroCarrier,
      hx0, hy0, ↓reduceIte, constructedCentralEdgeZeroUpperBranch] at h
    have he := congrFun ((inclusion_isOpenEmbedding (true, 0)).injective h) 2
    exact centralPhaseDiskUpperCoordinate_ne_nonnegReal hx hm he

public theorem constructedCentralPhaseFaceOneCarrier_ne_edgeOne
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1)
    {y : Fin 1 → ℝ} (hy : y ∈ Metric.closedBall 0 1) :
    constructedCentralPhaseFaceOneCarrier x ≠ constructedCentralEdgeOneCarrier y := by
  intro h
  rw [← a2CyclicCarrier_constructedCentralPhaseFaceZeroCarrier,
    ← a2CyclicCarrier_constructedCentralEdgeZeroCarrier] at h
  have hi : Function.Injective a2CyclicCarrier := a2CyclicCarrierHomeomorph.injective
  exact constructedCentralPhaseFaceZeroCarrier_ne_edgeZero hx hy (hi h)

public theorem constructedCentralPhaseFaceTwoCarrier_ne_edgeTwo
    {x : Fin 2 → ℝ} (hx : x ∈ Metric.ball 0 1)
    {y : Fin 1 → ℝ} (hy : y ∈ Metric.closedBall 0 1) :
    constructedCentralPhaseFaceTwoCarrier x ≠ constructedCentralEdgeTwoCarrier y := by
  intro h
  rw [← a2CyclicCarrier_sq_constructedCentralPhaseFaceZeroCarrier,
    ← a2CyclicCarrier_sq_constructedCentralEdgeZeroCarrier] at h
  have hi : Function.Injective a2CyclicCarrier := a2CyclicCarrierHomeomorph.injective
  exact constructedCentralPhaseFaceZeroCarrier_ne_edgeZero hx hy (hi (hi h))

public def constructedCentralPhaseTwoCell
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    PartialEquiv (Fin 2 → ℝ) (ActualLocalCuspCentralOrbitQuotient W) :=
  ![constructedCentralPhaseTwoCellZero W, constructedCentralPhaseTwoCellOne W,
    constructedCentralPhaseTwoCellTwo W] i

public theorem constructedCentralPhaseTwoCell_pairwiseDisjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Set.univ : Set (Fin 3)).PairwiseDisjoint
      (fun i ↦ constructedCentralPhaseTwoCell W i '' Metric.ball 0 1) := by
  have h01 : Disjoint (constructedCentralPhaseTwoCell W 0 '' Metric.ball 0 1)
      (constructedCentralPhaseTwoCell W 1 '' Metric.ball 0 1) := by
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, h⟩
    exact constructedCentralPhaseFaceZeroOrbit_ne_oneOrbit W x hx y hy h.symm
  have h02 : Disjoint (constructedCentralPhaseTwoCell W 0 '' Metric.ball 0 1)
      (constructedCentralPhaseTwoCell W 2 '' Metric.ball 0 1) := by
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, h⟩
    exact constructedCentralPhaseFaceZeroOrbit_ne_twoOrbit W x hx y hy h.symm
  have h12 : Disjoint (constructedCentralPhaseTwoCell W 1 '' Metric.ball 0 1)
      (constructedCentralPhaseTwoCell W 2 '' Metric.ball 0 1) := by
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, h⟩
    exact constructedCentralPhaseFaceOneOrbit_ne_twoOrbit W x hx y hy h.symm
  intro i _ j _ hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact h01 | exact h01.symm | exact h02 |
      exact h02.symm | exact h12 | exact h12.symm

public def constructedCentralEdgeSupport (i : Fin 3) : Set ToricLattice :=
  ![{e₁, e₂}, {0, e₂}, {0, e₁}] i

public theorem constructedCentralEdgeSupport_translate_injective
    (i j : Fin 3) (k : ToricLattice)
    (h : constructedCentralEdgeSupport i =
      (fun v ↦ v + k) '' constructedCentralEdgeSupport j) : i = j := by
  have hr : constructedCentralEdgeSupport j =
      (fun v ↦ v + -k) '' constructedCentralEdgeSupport i := by
    rw [h, Set.image_image]
    simp
  fin_cases i <;> fin_cases j
  · rfl
  · exact (edgeSupportZero_ne_translate_one k h).elim
  · exact (edgeSupportZero_ne_translate_two k h).elim
  · exact (edgeSupportZero_ne_translate_one (-k) hr).elim
  · rfl
  · exact (edgeSupportOne_ne_translate_two k h).elim
  · exact (edgeSupportZero_ne_translate_two (-k) hr).elim
  · exact (edgeSupportOne_ne_translate_two (-k) hr).elim
  · rfl

public def constructedCentralPhaseCellPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (x : Fin 2 → ℝ) :
    actualLocalCuspCentralSubMulAction W :=
  ![constructedCentralPhaseFaceZeroPoint W x, constructedCentralPhaseFaceOnePoint W x,
    constructedCentralPhaseFaceTwoPoint W x] i

public def constructedCentralEdgeCellPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (x : Fin 1 → ℝ) :
    actualLocalCuspCentralSubMulAction W :=
  ![constructedCentralEdgeZeroPoint W x,
    centralEdgePointOf W constructedCentralEdgeOneCarrier constructedCentralEdgeOneCarrier_height x,
    centralEdgePointOf W constructedCentralEdgeTwoCarrier constructedCentralEdgeTwoCarrier_height x] i

public theorem constructedCentralPhaseCellPoint_support
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3)
    (x : Fin 2 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel ((constructedCentralPhaseCellPoint W i x).1.1 : Carrier) =
      constructedCentralEdgeSupport i := by
  fin_cases i
  · exact constructedCentralPhaseFaceZeroCarrier_componentSupport x hx
  · exact constructedCentralPhaseFaceOneCarrier_componentSupport x hx
  · exact constructedCentralPhaseFaceTwoCarrier_componentSupport x hx

public theorem constructedCentralEdgeCellPoint_support
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3)
    (x : Fin 1 → ℝ) (hx : x ∈ Metric.ball 0 1) :
    componentSupport constructedModel ((constructedCentralEdgeCellPoint W i x).1.1 : Carrier) =
      constructedCentralEdgeSupport i := by
  fin_cases i
  · exact constructedCentralEdgeZeroCarrier_componentSupport x hx
  · exact constructedCentralEdgeOneCarrier_componentSupport x hx
  · exact constructedCentralEdgeTwoCarrier_componentSupport x hx

public theorem constructedCentralPhaseTwoCell_oneCell_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i j : Fin 3) :
    Disjoint (constructedCentralPhaseTwoCell W i '' Metric.ball 0 1)
      (constructedCentralOneCell W j '' Metric.ball 0 1) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  have h : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _)
      (constructedCentralPhaseCellPoint W i x) =
      Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _)
        (constructedCentralEdgeCellPoint W j y) := by
    fin_cases i <;> fin_cases j <;> exact he.symm
  obtain ⟨k, hk⟩ := actualCentralOrbit_support_eq_translate W _ _ h
  rw [constructedCentralPhaseCellPoint_support W i x hx,
    constructedCentralEdgeCellPoint_support W j y hy] at hk
  obtain rfl := constructedCentralEdgeSupport_translate_injective i j k hk
  have hf : (constructedCentralEdgeSupport i).Finite := by
    fin_cases i <;> simp [constructedCentralEdgeSupport]
  have hn : (constructedCentralEdgeSupport i).Nonempty := by
    fin_cases i <;> simp [constructedCentralEdgeSupport]
  have hp := actualCentralOrbit_eq_of_same_finite_support W _ _ _ hf hn
    (constructedCentralPhaseCellPoint_support W i x hx)
    (constructedCentralEdgeCellPoint_support W i y hy) h
  have hc := congrArg (fun p : actualLocalCuspCentralSubMulAction W ↦ (p.1.1 : Carrier)) hp
  fin_cases i
  · exact constructedCentralPhaseFaceZeroCarrier_ne_edgeZero hx (Metric.ball_subset_closedBall hy) hc
  · exact constructedCentralPhaseFaceOneCarrier_ne_edgeOne hx (Metric.ball_subset_closedBall hy) hc
  · exact constructedCentralPhaseFaceTwoCarrier_ne_edgeTwo hx (Metric.ball_subset_closedBall hy) hc

public theorem constructedCentralEdgeSupport_ncard (i : Fin 3) :
    (constructedCentralEdgeSupport i).ncard = 2 := by
  have h1 : (0 : ToricLattice) ≠ e₁ := by decide
  have h2 : (0 : ToricLattice) ≠ e₂ := by decide
  have h12 : e₁ ≠ e₂ := by decide
  fin_cases i <;> simp [constructedCentralEdgeSupport, h1, h2, h12]

public theorem constructedCentralPhaseTwoCell_zeroCell_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (j : Fin 2) :
    Disjoint (constructedCentralPhaseTwoCell W i '' Metric.ball 0 1)
      (constructedCentralZeroCell W j '' Metric.closedBall 0 1) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  have h : Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _)
      (constructedCentralPhaseCellPoint W i x) =
      Quotient.mk (MulAction.orbitRel (Multiplicative ParameterLattice) _)
        (constructedCentralOriginPoint W (![false, true] j)) := by
    fin_cases i <;> fin_cases j <;> exact he.symm
  have hr := Quotient.exact h
  have hn := constructedA2ActualCentralOrbitRel_componentSupport_ncard_eq W _ _ hr
  change (componentSupport constructedModel
      ((constructedCentralPhaseCellPoint W i x).1.1 : Carrier)).ncard =
    (componentSupport constructedModel (inclusion (![false, true] j, 0) 0)).ncard at hn
  rw [constructedCentralPhaseCellPoint_support W i x hx, constructedCentralEdgeSupport_ncard,
    carrierOrigin_componentSupport_ncard] at hn
  omega

public theorem constructedCentralPhaseTwoCell_oneSkeleton_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Disjoint (constructedCentralPhaseTwoCell W i '' Metric.ball 0 1)
      (constructedCentralOneSkeleton W) := by
  rw [Set.disjoint_left]
  intro z hz hs
  rcases hs with hs | hs
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hs
    exact Set.disjoint_left.mp (constructedCentralPhaseTwoCell_zeroCell_disjoint W i j) hz hj
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hs
    rw [constructedCentralOneCell_closedBall_image_eq] at hj
    rcases hj with hj | hj
    · exact Set.disjoint_left.mp (constructedCentralPhaseTwoCell_oneCell_disjoint W i j) hz hj
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hj
      exact Set.disjoint_left.mp (constructedCentralPhaseTwoCell_zeroCell_disjoint W i k) hz hk

public theorem constructedCentralPhaseTwoCell_singleton_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Disjoint (constructedCentralPhaseTwoCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ hz
  have hn := constructedA2ActualSingleton_not_of_support_ge_two W
    (constructedCentralPhaseCellPoint W i x) (by
      rw [constructedCentralPhaseCellPoint_support W i x hx, constructedCentralEdgeSupport_ncard])
  apply hn
  fin_cases i <;> exact hz

public theorem constructedCentralOneCell_singleton_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    Disjoint (constructedCentralOneCell W i '' Metric.ball 0 1)
      (constructedA2ActualSingletonStratum W) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ hz
  have hn := constructedA2ActualSingleton_not_of_support_ge_two W
    (constructedCentralEdgeCellPoint W i x) (by
      rw [constructedCentralEdgeCellPoint_support W i x hx, constructedCentralEdgeSupport_ncard])
  apply hn
  fin_cases i <;> exact hz

public theorem constructedCentralZeroCell_singleton_disjoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 2) :
    Disjoint (constructedCentralZeroCell W i '' Metric.closedBall 0 1)
      (constructedA2ActualSingletonStratum W) := by
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ hz
  have hn := constructedA2ActualSingleton_not_of_support_ge_two W
    (constructedCentralOriginPoint W (![false, true] i)) (by
      change 2 ≤ (componentSupport constructedModel (inclusion (![false, true] i, 0) 0)).ncard
      rw [carrierOrigin_componentSupport_ncard]
      omega)
  exact hn hz

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
