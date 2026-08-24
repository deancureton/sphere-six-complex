module

public import SphereSixComplex.Periods.Uniformization.ChamberCaratheodory
import all SphereSixComplex.Periods.Uniformization.ChamberCaratheodory
public import SphereSixComplex.Periods.Uniformization.DiscBoundaryTripleClosure
import all SphereSixComplex.Periods.Uniformization.DiscBoundaryTripleClosure

@[expose] public section

open Complex Metric Set Topology

noncomputable section

namespace SphereSixComplex.Periods.SourceChamberTopology

-- Pin the canonical complex normed-space instance.  `UpperHalfPlane.Basic`, imported by the
-- Cayley-coordinate file, also exposes the scalar-self module instance and otherwise leaves a
-- downstream instance diamond in `DifferentiableOn.comp`.
local instance : NormedSpace ℂ ℂ := RCLike.innerProductSpace.toNormedSpace

/-! ## Closed-disc Riemann-map seeds and their marked boundary preimages -/

/-- A Riemann map together with its Carathéodory homeomorphism of closures. -/
structure ChamberCaratheodorySeed (Ω : Set ℂ) where
  map : ℂ → ℂ
  closureEquiv : closedBall (0 : ℂ) 1 ≃ₜ closure Ω
  differentiableOn : DifferentiableOn ℂ map (ball 0 1)
  bijOn : BijOn map (ball 0 1) Ω
  closureEquiv_apply : ∀ z, (closureEquiv z : ℂ) = map z

theorem exists_sourceChamberCaratheodorySeed :
    Nonempty (ChamberCaratheodorySeed sourceBoundedChamber) := by
  obtain ⟨g, e, hgd, hgbij, he⟩ := exists_sourceChamber_closureHomeomorph
  exact ⟨⟨g, e, hgd, hgbij, he⟩⟩

theorem exists_targetChamberCaratheodorySeed :
    Nonempty (ChamberCaratheodorySeed targetBoundedChamber) := by
  obtain ⟨g, e, hgd, hgbij, he⟩ := exists_targetChamber_closureHomeomorph
  exact ⟨⟨g, e, hgd, hgbij, he⟩⟩

/-- The circle point at which a closed-disc Riemann-map seed takes a prescribed frontier value. -/
def ChamberCaratheodorySeed.boundaryPreimage {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω) (v : ℂ)
    (hv : v ∈ frontier Ω) : Circle := by
  let z : closedBall (0 : ℂ) 1 := S.closureEquiv.symm ⟨v, frontier_subset_closure hv⟩
  have hzle : ‖(z : ℂ)‖ ≤ 1 := by
    have hzdist : dist (z : ℂ) 0 ≤ 1 := mem_closedBall.mp z.2
    simpa only [dist_zero_right] using hzdist
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    apply le_antisymm hzle
    by_contra hnot
    have hzlt : ‖(z : ℂ)‖ < 1 := lt_of_not_ge hnot
    have hzball : (z : ℂ) ∈ ball (0 : ℂ) 1 := by
      exact mem_ball.mpr (by simpa only [dist_zero_right] using hzlt)
    have hmap : S.map z ∈ Ω := S.bijOn.mapsTo hzball
    have heq : S.map z = v := by
      rw [← S.closureEquiv_apply z]
      exact congrArg Subtype.val
        (S.closureEquiv.apply_symm_apply ⟨v, frontier_subset_closure hv⟩)
    exact (hΩo.frontier_eq.subset hv).2 (heq ▸ hmap)
  exact ⟨z, (show (z : ℂ) ∈ sphere 0 1 from mem_sphere_zero_iff_norm.mpr hnorm)⟩

theorem ChamberCaratheodorySeed.coe_boundaryPreimage {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω) (v : ℂ)
    (hv : v ∈ frontier Ω) :
    (S.boundaryPreimage hΩo v hv : ℂ) =
      (S.closureEquiv.symm ⟨v, frontier_subset_closure hv⟩ : ℂ) := by
  unfold boundaryPreimage
  rfl

theorem ChamberCaratheodorySeed.closureEquiv_boundaryPreimage {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω) (v : ℂ)
    (hv : v ∈ frontier Ω) :
    S.closureEquiv
      ⟨S.boundaryPreimage hΩo v hv,
        by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ =
      ⟨v, frontier_subset_closure hv⟩ := by
  apply Subtype.ext
  simp only [ChamberCaratheodorySeed.coe_boundaryPreimage]
  exact congrArg Subtype.val
    (S.closureEquiv.apply_symm_apply ⟨v, frontier_subset_closure hv⟩)

theorem ChamberCaratheodorySeed.boundaryPreimage_ne {Ω : Set ℂ}
    (S : ChamberCaratheodorySeed Ω) (hΩo : IsOpen Ω)
    {v w : ℂ} (hv : v ∈ frontier Ω) (hw : w ∈ frontier Ω) (hvw : v ≠ w) :
    S.boundaryPreimage hΩo v hv ≠ S.boundaryPreimage hΩo w hw := by
  intro h
  apply hvw
  have hcoe : (S.boundaryPreimage hΩo v hv : ℂ) =
      (S.boundaryPreimage hΩo w hw : ℂ) := congrArg (fun z : Circle ↦ (z : ℂ)) h
  have hclosed :
      (⟨S.boundaryPreimage hΩo v hv,
          by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ :
          closedBall (0 : ℂ) 1) =
        ⟨S.boundaryPreimage hΩo w hw,
          by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩ := Subtype.ext hcoe
  have he := congrArg S.closureEquiv hclosed
  rw [S.closureEquiv_boundaryPreimage hΩo v hv,
    S.closureEquiv_boundaryPreimage hΩo w hw] at he
  exact congrArg Subtype.val he

/-! ## The three distinguished vertices -/

def sourceCuspVertex : ℂ := 0

/-- The source order-three vertex, at the right endpoint of the circular side. -/
def sourceOrderThreeVertex : ℂ :=
  cuspPolar (1 + Real.sqrt 2) semicircleHeight ((1 / 2 : ℝ), 1)

/-- The source order-four vertex, at the left endpoint of the circular side. -/
def sourceOtherEllipticVertex : ℂ :=
  cuspPolar (1 + Real.sqrt 2) semicircleHeight (-Real.sqrt 2 / 2, 1)

def targetCuspVertex : ℂ := 0

/-- The target order-three vertex, at the right endpoint of the circular side. -/
def targetOrderThreeVertex : ℂ := cuspPolar 1 semicircleHeight ((1 / 2 : ℝ), 1)

/-- The target order-two vertex, at the left endpoint of the circular side. -/
def targetOtherEllipticVertex : ℂ := cuspPolar 1 semicircleHeight (0, 1)

theorem sourceCuspVertex_mem_frontier : sourceCuspVertex ∈ frontier sourceBoundedChamber := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨(-Real.sqrt 2 / 2, 0), ?_, by simp [sourceCuspVertex, cuspPolar]⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨le_rfl, by
    have hs := Real.sqrt_nonneg 2
    linarith⟩, le_rfl, zero_le_one⟩, Or.inl rfl⟩

theorem sourceOrderThreeVertex_mem_frontier :
    sourceOrderThreeVertex ∈ frontier sourceBoundedChamber := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨((1 / 2 : ℝ), 1), ?_, rfl⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨by
    have hs := Real.sqrt_nonneg 2
    linarith, le_rfl⟩, zero_le_one, le_rfl⟩, Or.inr (Or.inl rfl)⟩

theorem sourceOtherEllipticVertex_mem_frontier :
    sourceOtherEllipticVertex ∈ frontier sourceBoundedChamber := by
  rw [frontier_sourceBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨(-Real.sqrt 2 / 2, 1), ?_, rfl⟩
  apply (mem_cuspRectangleBoundary_iff
    (show -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) by
      have hs := Real.sqrt_nonneg 2
      linarith) _).2
  exact ⟨⟨⟨le_rfl, by
    have hs := Real.sqrt_nonneg 2
    linarith⟩, zero_le_one, le_rfl⟩, Or.inl rfl⟩

theorem targetCuspVertex_mem_frontier : targetCuspVertex ∈ frontier targetBoundedChamber := by
  rw [frontier_targetBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨((0 : ℝ), 0), ?_, by simp [targetCuspVertex, cuspPolar]⟩
  exact (mem_cuspRectangleBoundary_iff (by norm_num : (0 : ℝ) ≤ 1 / 2) _).2
    ⟨⟨⟨le_rfl, by norm_num⟩, le_rfl, zero_le_one⟩, Or.inl rfl⟩

theorem targetOrderThreeVertex_mem_frontier :
    targetOrderThreeVertex ∈ frontier targetBoundedChamber := by
  rw [frontier_targetBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨((1 / 2 : ℝ), 1), ?_, rfl⟩
  exact (mem_cuspRectangleBoundary_iff (by norm_num : (0 : ℝ) ≤ 1 / 2) _).2
    ⟨⟨⟨by norm_num, le_rfl⟩, zero_le_one, le_rfl⟩, Or.inr (Or.inl rfl)⟩

theorem targetOtherEllipticVertex_mem_frontier :
    targetOtherEllipticVertex ∈ frontier targetBoundedChamber := by
  rw [frontier_targetBoundedChamber_eq_cuspPolar_boundary]
  refine ⟨((0 : ℝ), 1), ?_, rfl⟩
  exact (mem_cuspRectangleBoundary_iff (by norm_num : (0 : ℝ) ≤ 1 / 2) _).2
    ⟨⟨⟨le_rfl, by norm_num⟩, zero_le_one, le_rfl⟩, Or.inl rfl⟩

theorem sourceCuspVertex_ne_orderThree : sourceCuspVertex ≠ sourceOrderThreeVertex := by
  rw [sourceCuspVertex, sourceOrderThreeVertex, cuspPolar]
  simpa only [Complex.ofReal_one, one_mul] using (cuspExponential_ne_zero
    (1 + Real.sqrt 2) ((1 / 2 : ℝ) + (semicircleHeight (1 / 2) : ℂ) * I)).symm

theorem sourceCuspVertex_ne_otherElliptic :
    sourceCuspVertex ≠ sourceOtherEllipticVertex := by
  rw [sourceCuspVertex, sourceOtherEllipticVertex, cuspPolar]
  simpa only [Complex.ofReal_one, one_mul] using (cuspExponential_ne_zero
    (1 + Real.sqrt 2)
      ((-Real.sqrt 2 / 2 : ℝ) + (semicircleHeight (-Real.sqrt 2 / 2) : ℂ) * I)).symm

theorem targetCuspVertex_ne_orderThree : targetCuspVertex ≠ targetOrderThreeVertex := by
  rw [targetCuspVertex, targetOrderThreeVertex, cuspPolar]
  simpa only [Complex.ofReal_one, one_mul] using (cuspExponential_ne_zero
    1 ((1 / 2 : ℝ) + (semicircleHeight (1 / 2) : ℂ) * I)).symm

theorem targetCuspVertex_ne_otherElliptic :
    targetCuspVertex ≠ targetOtherEllipticVertex := by
  rw [targetCuspVertex, targetOtherEllipticVertex, cuspPolar]
  simpa only [Complex.ofReal_one, one_mul] using (cuspExponential_ne_zero
    1 ((0 : ℝ) + (semicircleHeight 0 : ℂ) * I)).symm

theorem sourceOrderThreeVertex_ne_otherElliptic :
    sourceOrderThreeVertex ≠ sourceOtherEllipticVertex := by
  intro h
  have hlr : -Real.sqrt 2 / 2 ≤ (1 / 2 : ℝ) := by
    have hs := Real.sqrt_nonneg 2
    linarith
  have hp := cuspPolar_injOn_positiveClosedCuspStrip
    (show (1 + Real.sqrt 2 : ℝ) ≠ 0 by positivity) semicircleHeight
    source_cuspExponential_injOn_closedStrip
    (show ((1 / 2 : ℝ), 1) ∈
      positiveClosedCuspStrip (-Real.sqrt 2 / 2) (1 / 2) from
        ⟨hlr, le_rfl, one_pos⟩)
    (show (-Real.sqrt 2 / 2, (1 : ℝ)) ∈
      positiveClosedCuspStrip (-Real.sqrt 2 / 2) (1 / 2) from
        ⟨le_rfl, hlr, one_pos⟩)
    (by simpa only [sourceOrderThreeVertex, sourceOtherEllipticVertex] using h)
  have hx := congrArg Prod.fst hp
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  norm_num only [Prod.fst] at hx
  nlinarith

theorem targetOrderThreeVertex_ne_otherElliptic :
    targetOrderThreeVertex ≠ targetOtherEllipticVertex := by
  intro h
  have hp := cuspPolar_injOn_positiveClosedCuspStrip one_ne_zero semicircleHeight
    target_cuspExponential_injOn_closedStrip
    (show ((1 / 2 : ℝ), 1) ∈ positiveClosedCuspStrip 0 (1 / 2) from
      ⟨by norm_num, le_rfl, one_pos⟩)
    (show ((0 : ℝ), 1) ∈ positiveClosedCuspStrip 0 (1 / 2) from
      ⟨le_rfl, by norm_num, one_pos⟩)
    (by simpa only [targetOrderThreeVertex, targetOtherEllipticVertex] using h)
  have hx := congrArg Prod.fst hp
  norm_num at hx

/-! ## The marked triples selected by a pair of Carathéodory seeds -/

def sourceCuspCircle (S : ChamberCaratheodorySeed sourceBoundedChamber) : Circle :=
  S.boundaryPreimage sourceBoundedChamber_isOpen sourceCuspVertex
    sourceCuspVertex_mem_frontier

def sourceOrderThreeCircle (S : ChamberCaratheodorySeed sourceBoundedChamber) : Circle :=
  S.boundaryPreimage sourceBoundedChamber_isOpen sourceOrderThreeVertex
    sourceOrderThreeVertex_mem_frontier

def sourceOtherEllipticCircle (S : ChamberCaratheodorySeed sourceBoundedChamber) : Circle :=
  S.boundaryPreimage sourceBoundedChamber_isOpen sourceOtherEllipticVertex
    sourceOtherEllipticVertex_mem_frontier

def targetCuspCircle (T : ChamberCaratheodorySeed targetBoundedChamber) : Circle :=
  T.boundaryPreimage targetBoundedChamber_isOpen targetCuspVertex
    targetCuspVertex_mem_frontier

def targetOrderThreeCircle (T : ChamberCaratheodorySeed targetBoundedChamber) : Circle :=
  T.boundaryPreimage targetBoundedChamber_isOpen targetOrderThreeVertex
    targetOrderThreeVertex_mem_frontier

def targetOtherEllipticCircle (T : ChamberCaratheodorySeed targetBoundedChamber) : Circle :=
  T.boundaryPreimage targetBoundedChamber_isOpen targetOtherEllipticVertex
    targetOtherEllipticVertex_mem_frontier

theorem sourceOrderThreeCircle_ne_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceOrderThreeCircle S ≠ sourceCuspCircle S :=
  S.boundaryPreimage_ne sourceBoundedChamber_isOpen
    sourceOrderThreeVertex_mem_frontier sourceCuspVertex_mem_frontier
    sourceCuspVertex_ne_orderThree.symm

theorem sourceOtherEllipticCircle_ne_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceOtherEllipticCircle S ≠ sourceCuspCircle S :=
  S.boundaryPreimage_ne sourceBoundedChamber_isOpen
    sourceOtherEllipticVertex_mem_frontier sourceCuspVertex_mem_frontier
    sourceCuspVertex_ne_otherElliptic.symm

theorem targetOrderThreeCircle_ne_cusp
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    targetOrderThreeCircle T ≠ targetCuspCircle T :=
  T.boundaryPreimage_ne targetBoundedChamber_isOpen
    targetOrderThreeVertex_mem_frontier targetCuspVertex_mem_frontier
    targetCuspVertex_ne_orderThree.symm

theorem targetOtherEllipticCircle_ne_cusp
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    targetOtherEllipticCircle T ≠ targetCuspCircle T :=
  T.boundaryPreimage_ne targetBoundedChamber_isOpen
    targetOtherEllipticVertex_mem_frontier targetCuspVertex_mem_frontier
    targetCuspVertex_ne_otherElliptic.symm

theorem sourceOrderThreeCircle_ne_otherElliptic
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    sourceOrderThreeCircle S ≠ sourceOtherEllipticCircle S :=
  S.boundaryPreimage_ne sourceBoundedChamber_isOpen
    sourceOrderThreeVertex_mem_frontier sourceOtherEllipticVertex_mem_frontier
    sourceOrderThreeVertex_ne_otherElliptic

theorem targetOrderThreeCircle_ne_otherElliptic
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    targetOrderThreeCircle T ≠ targetOtherEllipticCircle T :=
  T.boundaryPreimage_ne targetBoundedChamber_isOpen
    targetOrderThreeVertex_mem_frontier targetOtherEllipticVertex_mem_frontier
    targetOrderThreeVertex_ne_otherElliptic

/-- The sole orientation condition needed to normalize two arbitrary Carathéodory seeds. -/
def SourceTargetSeedSameOrientation
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) : Prop :=
  SameCircleTripleOrientation
    (sourceCuspCircle S) (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
    (targetCuspCircle T) (targetOrderThreeCircle T) (targetOtherEllipticCircle T)

/-- The unique positive-Cayley-affine open-disc map carrying the three marked preimages in the
source seed to those in the target seed. -/
def sourceTargetMarkedDiscMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) : ℂ → ℂ :=
  orientedCircleTripleMap
    (sourceCuspCircle S) (sourceOrderThreeCircle S) (sourceOtherEllipticCircle S)
    (targetCuspCircle T) (targetOrderThreeCircle T) (targetOtherEllipticCircle T)

theorem sourceTargetMarkedDiscMap_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    sourceTargetMarkedDiscMap S T (sourceCuspCircle S) = targetCuspCircle T := by
  exact orientedCircleTripleMap_pole _ _ _ _ _ _

theorem sourceTargetMarkedDiscMap_orderThree
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    sourceTargetMarkedDiscMap S T (sourceOrderThreeCircle S) =
      targetOrderThreeCircle T := by
  exact orientedCircleTripleMap_first horient
    (sourceOrderThreeCircle_ne_cusp S) (targetOrderThreeCircle_ne_cusp T)

theorem sourceTargetMarkedDiscMap_otherElliptic
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    sourceTargetMarkedDiscMap S T (sourceOtherEllipticCircle S) =
      targetOtherEllipticCircle T := by
  exact orientedCircleTripleMap_second horient
    (sourceOtherEllipticCircle_ne_cusp S) (targetOtherEllipticCircle_ne_cusp T)

theorem sourceTargetMarkedDiscMap_bijOn_ball
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    BijOn (sourceTargetMarkedDiscMap S T) (ball (0 : ℂ) 1) (ball 0 1) :=
  orientedCircleTripleMap_bijOn_ball _ _ _ _ _ _ horient

theorem sourceTargetMarkedDiscMap_differentiableOn_ball
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    DifferentiableOn ℂ (sourceTargetMarkedDiscMap S T) (ball (0 : ℂ) 1) :=
  orientedCircleTripleMap_differentiableOn_ball _ _ _ _ _ _ horient

theorem sourceTargetMarkedDiscMap_continuousOn_closedBall
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    ContinuousOn (sourceTargetMarkedDiscMap S T) (closedBall (0 : ℂ) 1) :=
  orientedCircleTripleMap_continuousOn_closedBall horient

theorem sourceTargetMarkedDiscMap_bijOn_closedBall
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    BijOn (sourceTargetMarkedDiscMap S T)
      (closedBall (0 : ℂ) 1) (closedBall 0 1) :=
  orientedCircleTripleMap_bijOn_closedBall horient

/-! ## The induced marked biholomorphism of the open chambers -/

def sourceTargetMarkedChamberMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) : ℂ → ℂ :=
  T.map ∘ sourceTargetMarkedDiscMap S T ∘
    Function.invFunOn S.map (ball (0 : ℂ) 1)

private theorem sourceSeed_invFunOn_bijOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber) :
    BijOn (Function.invFunOn S.map (ball (0 : ℂ) 1))
      sourceBoundedChamber (ball 0 1) :=
  BijOn.symm S.bijOn.invOn_invFunOn.symm S.bijOn

theorem sourceTargetMarkedChamberMap_bijOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    BijOn (sourceTargetMarkedChamberMap S T)
      sourceBoundedChamber targetBoundedChamber := by
  have h := T.bijOn.comp
    ((sourceTargetMarkedDiscMap_bijOn_ball S T horient).comp
      (sourceSeed_invFunOn_bijOn S))
  exact h

theorem sourceTargetMarkedChamberMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    DifferentiableOn ℂ (sourceTargetMarkedChamberMap S T) sourceBoundedChamber := by
  have hSinv : DifferentiableOn ℂ
      (Function.invFunOn S.map (ball (0 : ℂ) 1)) sourceBoundedChamber := by
    have h := TauCeti.DifferentiableOn.invFunOn
      S.differentiableOn isOpen_ball S.bijOn.injOn
    rwa [S.bijOn.image_eq] at h
  have hdisc := (sourceTargetMarkedDiscMap_differentiableOn_ball S T horient).comp
    hSinv (sourceSeed_invFunOn_bijOn S).mapsTo
  have h := T.differentiableOn.comp hdisc
    ((sourceTargetMarkedDiscMap_bijOn_ball S T horient).mapsTo.comp
      (sourceSeed_invFunOn_bijOn S).mapsTo)
  exact h

theorem sourceTargetMarkedChamberMap_invFunOn_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    DifferentiableOn ℂ
      (Function.invFunOn (sourceTargetMarkedChamberMap S T) sourceBoundedChamber)
      targetBoundedChamber := by
  have h := TauCeti.DifferentiableOn.invFunOn
    (sourceTargetMarkedChamberMap_differentiableOn S T horient)
    sourceBoundedChamber_isOpen
    (sourceTargetMarkedChamberMap_bijOn S T horient).injOn
  rwa [(sourceTargetMarkedChamberMap_bijOn S T horient).image_eq] at h

/-- Kernel-checked reduction of the marked chamber biholomorphism to the orientation of the two
boundary triples selected by arbitrary Carathéodory seeds. -/
theorem exists_sourceTarget_marked_biholomorph_of_seed_orientation
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f sourceBoundedChamber ∧
      BijOn f sourceBoundedChamber targetBoundedChamber ∧
      DifferentiableOn ℂ (Function.invFunOn f sourceBoundedChamber)
        targetBoundedChamber :=
  ⟨sourceTargetMarkedChamberMap S T,
    sourceTargetMarkedChamberMap_differentiableOn S T horient,
    sourceTargetMarkedChamberMap_bijOn S T horient,
    sourceTargetMarkedChamberMap_invFunOn_differentiableOn S T horient⟩

/-! ## Lifting the bounded equivalence back to the original open chambers -/

private theorem source_cuspExponential_bijOn :
    BijOn (cuspExponential (1 + Real.sqrt 2)) sourceOpenChamber
      sourceBoundedChamber := by
  rw [sourceBoundedChamber]
  exact source_cuspExponential_injOn.bijOn_image

private theorem target_cuspExponential_bijOn :
    BijOn (cuspExponential 1) targetOpenChamber targetBoundedChamber := by
  rw [targetBoundedChamber]
  exact target_cuspExponential_injOn.bijOn_image

private theorem target_cuspExponential_invFunOn_bijOn :
    BijOn (Function.invFunOn (cuspExponential 1) targetOpenChamber)
      targetBoundedChamber targetOpenChamber :=
  BijOn.symm target_cuspExponential_bijOn.invOn_invFunOn.symm
    target_cuspExponential_bijOn

private theorem target_cuspExponential_invFunOn_differentiableOn :
    DifferentiableOn ℂ
      (Function.invFunOn (cuspExponential 1) targetOpenChamber)
      targetBoundedChamber := by
  have h := TauCeti.DifferentiableOn.invFunOn
    (cuspExponential_differentiable 1 one_ne_zero).differentiableOn
    targetOpenChamber_isOpen target_cuspExponential_injOn
  rwa [target_cuspExponential_bijOn.image_eq] at h

/-- The marked bounded-chamber equivalence lifted through the two cusp-exponential charts. -/
def sourceTargetMarkedOpenChamberMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) : ℂ → ℂ :=
  Function.invFunOn (cuspExponential 1) targetOpenChamber ∘
    sourceTargetMarkedChamberMap S T ∘ cuspExponential (1 + Real.sqrt 2)

theorem sourceTargetMarkedOpenChamberMap_bijOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    BijOn (sourceTargetMarkedOpenChamberMap S T)
      sourceOpenChamber targetOpenChamber := by
  exact target_cuspExponential_invFunOn_bijOn.comp
    ((sourceTargetMarkedChamberMap_bijOn S T horient).comp
      source_cuspExponential_bijOn)

theorem sourceTargetMarkedOpenChamberMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    DifferentiableOn ℂ (sourceTargetMarkedOpenChamberMap S T) sourceOpenChamber := by
  have hmiddle := (sourceTargetMarkedChamberMap_differentiableOn S T horient).comp
    (cuspExponential_differentiable (1 + Real.sqrt 2)
      (show (1 + Real.sqrt 2 : ℝ) ≠ 0 by positivity)).differentiableOn
    source_cuspExponential_bijOn.mapsTo
  exact target_cuspExponential_invFunOn_differentiableOn.comp hmiddle
    ((sourceTargetMarkedChamberMap_bijOn S T horient).mapsTo.comp
      source_cuspExponential_bijOn.mapsTo)

theorem sourceTargetMarkedOpenChamberMap_invFunOn_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    DifferentiableOn ℂ
      (Function.invFunOn (sourceTargetMarkedOpenChamberMap S T) sourceOpenChamber)
      targetOpenChamber := by
  have h := TauCeti.DifferentiableOn.invFunOn
    (sourceTargetMarkedOpenChamberMap_differentiableOn S T horient)
    sourceOpenChamber_isOpen
    (sourceTargetMarkedOpenChamberMap_bijOn S T horient).injOn
  rwa [(sourceTargetMarkedOpenChamberMap_bijOn S T horient).image_eq] at h

/-- Strongest current marked seed on the original unbounded chambers: a biholomorphism, reduced
only to the orientation of the two boundary triples. -/
theorem exists_sourceOpen_targetOpen_marked_biholomorph_of_seed_orientation
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f sourceOpenChamber ∧
      BijOn f sourceOpenChamber targetOpenChamber ∧
      DifferentiableOn ℂ (Function.invFunOn f sourceOpenChamber) targetOpenChamber :=
  ⟨sourceTargetMarkedOpenChamberMap S T,
    sourceTargetMarkedOpenChamberMap_differentiableOn S T horient,
    sourceTargetMarkedOpenChamberMap_bijOn S T horient,
    sourceTargetMarkedOpenChamberMap_invFunOn_differentiableOn S T horient⟩

/-! An orientation-free seed is also useful: it provides the biholomorphic open-chamber map while
deliberately making no claim about which elliptic vertex is reached. -/

def sourceTargetUnmarkedChamberMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) : ℂ → ℂ :=
  T.map ∘ Function.invFunOn S.map (ball (0 : ℂ) 1)

theorem sourceTargetUnmarkedChamberMap_bijOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    BijOn (sourceTargetUnmarkedChamberMap S T)
      sourceBoundedChamber targetBoundedChamber :=
  T.bijOn.comp (sourceSeed_invFunOn_bijOn S)

theorem sourceTargetUnmarkedChamberMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    DifferentiableOn ℂ (sourceTargetUnmarkedChamberMap S T) sourceBoundedChamber := by
  have hSinv : DifferentiableOn ℂ
      (Function.invFunOn S.map (ball (0 : ℂ) 1)) sourceBoundedChamber := by
    have h := TauCeti.DifferentiableOn.invFunOn
      S.differentiableOn isOpen_ball S.bijOn.injOn
    rwa [S.bijOn.image_eq] at h
  exact T.differentiableOn.comp hSinv (sourceSeed_invFunOn_bijOn S).mapsTo

def sourceTargetUnmarkedOpenChamberMap
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) : ℂ → ℂ :=
  Function.invFunOn (cuspExponential 1) targetOpenChamber ∘
    sourceTargetUnmarkedChamberMap S T ∘ cuspExponential (1 + Real.sqrt 2)

theorem sourceTargetUnmarkedOpenChamberMap_bijOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    BijOn (sourceTargetUnmarkedOpenChamberMap S T)
      sourceOpenChamber targetOpenChamber :=
  target_cuspExponential_invFunOn_bijOn.comp
    ((sourceTargetUnmarkedChamberMap_bijOn S T).comp source_cuspExponential_bijOn)

theorem sourceTargetUnmarkedOpenChamberMap_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    DifferentiableOn ℂ (sourceTargetUnmarkedOpenChamberMap S T) sourceOpenChamber := by
  have hmiddle := (sourceTargetUnmarkedChamberMap_differentiableOn S T).comp
    (cuspExponential_differentiable (1 + Real.sqrt 2)
      (show (1 + Real.sqrt 2 : ℝ) ≠ 0 by positivity)).differentiableOn
    source_cuspExponential_bijOn.mapsTo
  exact target_cuspExponential_invFunOn_differentiableOn.comp hmiddle
    ((sourceTargetUnmarkedChamberMap_bijOn S T).mapsTo.comp
      source_cuspExponential_bijOn.mapsTo)

theorem sourceTargetUnmarkedOpenChamberMap_invFunOn_differentiableOn
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber) :
    DifferentiableOn ℂ
      (Function.invFunOn (sourceTargetUnmarkedOpenChamberMap S T) sourceOpenChamber)
      targetOpenChamber := by
  have h := TauCeti.DifferentiableOn.invFunOn
    (sourceTargetUnmarkedOpenChamberMap_differentiableOn S T)
    sourceOpenChamber_isOpen
    (sourceTargetUnmarkedOpenChamberMap_bijOn S T).injOn
  rwa [(sourceTargetUnmarkedOpenChamberMap_bijOn S T).image_eq] at h

/-- Unconditional biholomorphic equivalence of the two original open chambers. -/
theorem exists_sourceOpen_targetOpen_biholomorph :
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f sourceOpenChamber ∧
      BijOn f sourceOpenChamber targetOpenChamber ∧
      DifferentiableOn ℂ (Function.invFunOn f sourceOpenChamber) targetOpenChamber := by
  let S := Classical.choice exists_sourceChamberCaratheodorySeed
  let T := Classical.choice exists_targetChamberCaratheodorySeed
  exact ⟨sourceTargetUnmarkedOpenChamberMap S T,
    sourceTargetUnmarkedOpenChamberMap_differentiableOn S T,
    sourceTargetUnmarkedOpenChamberMap_bijOn S T,
    sourceTargetUnmarkedOpenChamberMap_invFunOn_differentiableOn S T⟩

/-! ## Closure packaging -/

/-- A continuous bijection of the closed disc, packaged as a homeomorphism. -/
noncomputable def closedBallHomeomorphOf (A : ℂ → ℂ)
    (hAc : ContinuousOn A (closedBall (0 : ℂ) 1))
    (hAbij : BijOn A (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 := by
  letI : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  exact Continuous.homeoOfEquivCompactToT2 (f := hAbij.equiv A)
    (hAc.mapsToRestrict hAbij.mapsTo)

@[simp] theorem coe_closedBallHomeomorphOf_apply (A : ℂ → ℂ)
    (hAc : ContinuousOn A (closedBall (0 : ℂ) 1))
    (hAbij : BijOn A (closedBall (0 : ℂ) 1) (closedBall 0 1))
    (z : closedBall (0 : ℂ) 1) :
    (closedBallHomeomorphOf A hAc hAbij z : ℂ) = A z := rfl

/-- The marked homeomorphism of chamber closures, parameterized by its closed-disc facts.  The
canonical specialization below supplies these facts from the linear-fractional formula. -/
noncomputable def sourceTargetMarkedClosureEquiv
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T)
    (hAc : ContinuousOn (sourceTargetMarkedDiscMap S T) (closedBall (0 : ℂ) 1))
    (hAbij : BijOn (sourceTargetMarkedDiscMap S T)
      (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    closure sourceBoundedChamber ≃ₜ closure targetBoundedChamber :=
  S.closureEquiv.symm.trans
    ((closedBallHomeomorphOf (sourceTargetMarkedDiscMap S T) hAc hAbij).trans
      T.closureEquiv)

private theorem sourceTargetMarkedClosureEquiv_maps_boundaryValue
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T)
    (hAc : ContinuousOn (sourceTargetMarkedDiscMap S T) (closedBall (0 : ℂ) 1))
    (hAbij : BijOn (sourceTargetMarkedDiscMap S T)
      (closedBall (0 : ℂ) 1) (closedBall 0 1))
    {v w : ℂ} (hv : v ∈ frontier sourceBoundedChamber)
    (hw : w ∈ frontier targetBoundedChamber)
    (hmarked : sourceTargetMarkedDiscMap S T
      (S.boundaryPreimage sourceBoundedChamber_isOpen v hv) =
        T.boundaryPreimage targetBoundedChamber_isOpen w hw) :
    sourceTargetMarkedClosureEquiv S T horient hAc hAbij
      ⟨v, frontier_subset_closure hv⟩ =
        ⟨w, frontier_subset_closure hw⟩ := by
  let zs : closedBall (0 : ℂ) 1 :=
    ⟨S.boundaryPreimage sourceBoundedChamber_isOpen v hv,
      by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
  let zt : closedBall (0 : ℂ) 1 :=
    ⟨T.boundaryPreimage targetBoundedChamber_isOpen w hw,
      by rw [mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
  have hsource :
      S.closureEquiv.symm ⟨v, frontier_subset_closure hv⟩ = zs := by
    apply Subtype.ext
    exact (S.coe_boundaryPreimage sourceBoundedChamber_isOpen v hv).symm
  have hdisc :
      closedBallHomeomorphOf (sourceTargetMarkedDiscMap S T) hAc hAbij zs = zt := by
    apply Subtype.ext
    simpa only [coe_closedBallHomeomorphOf_apply, zs, zt] using hmarked
  rw [sourceTargetMarkedClosureEquiv, Homeomorph.trans_apply, Homeomorph.trans_apply,
    hsource, hdisc]
  exact T.closureEquiv_boundaryPreimage targetBoundedChamber_isOpen w hw

theorem sourceTargetMarkedClosureEquiv_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T)
    (hAc : ContinuousOn (sourceTargetMarkedDiscMap S T) (closedBall (0 : ℂ) 1))
    (hAbij : BijOn (sourceTargetMarkedDiscMap S T)
      (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    sourceTargetMarkedClosureEquiv S T horient hAc hAbij
      ⟨sourceCuspVertex, frontier_subset_closure sourceCuspVertex_mem_frontier⟩ =
      ⟨targetCuspVertex, frontier_subset_closure targetCuspVertex_mem_frontier⟩ :=
  sourceTargetMarkedClosureEquiv_maps_boundaryValue S T horient hAc hAbij
    sourceCuspVertex_mem_frontier targetCuspVertex_mem_frontier
    (sourceTargetMarkedDiscMap_cusp S T)

theorem sourceTargetMarkedClosureEquiv_orderThree
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T)
    (hAc : ContinuousOn (sourceTargetMarkedDiscMap S T) (closedBall (0 : ℂ) 1))
    (hAbij : BijOn (sourceTargetMarkedDiscMap S T)
      (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    sourceTargetMarkedClosureEquiv S T horient hAc hAbij
      ⟨sourceOrderThreeVertex,
        frontier_subset_closure sourceOrderThreeVertex_mem_frontier⟩ =
      ⟨targetOrderThreeVertex,
        frontier_subset_closure targetOrderThreeVertex_mem_frontier⟩ :=
  sourceTargetMarkedClosureEquiv_maps_boundaryValue S T horient hAc hAbij
    sourceOrderThreeVertex_mem_frontier targetOrderThreeVertex_mem_frontier
    (sourceTargetMarkedDiscMap_orderThree S T horient)

theorem sourceTargetMarkedClosureEquiv_otherElliptic
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T)
    (hAc : ContinuousOn (sourceTargetMarkedDiscMap S T) (closedBall (0 : ℂ) 1))
    (hAbij : BijOn (sourceTargetMarkedDiscMap S T)
      (closedBall (0 : ℂ) 1) (closedBall 0 1)) :
    sourceTargetMarkedClosureEquiv S T horient hAc hAbij
      ⟨sourceOtherEllipticVertex,
        frontier_subset_closure sourceOtherEllipticVertex_mem_frontier⟩ =
      ⟨targetOtherEllipticVertex,
        frontier_subset_closure targetOtherEllipticVertex_mem_frontier⟩ :=
  sourceTargetMarkedClosureEquiv_maps_boundaryValue S T horient hAc hAbij
    sourceOtherEllipticVertex_mem_frontier targetOtherEllipticVertex_mem_frontier
    (sourceTargetMarkedDiscMap_otherElliptic S T horient)

theorem sourceTargetMarkedClosureEquiv_apply_of_mem
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T)
    (hAc : ContinuousOn (sourceTargetMarkedDiscMap S T) (closedBall (0 : ℂ) 1))
    (hAbij : BijOn (sourceTargetMarkedDiscMap S T)
      (closedBall (0 : ℂ) 1) (closedBall 0 1))
    (q : closure sourceBoundedChamber) (hq : (q : ℂ) ∈ sourceBoundedChamber) :
    (sourceTargetMarkedClosureEquiv S T horient hAc hAbij q : ℂ) =
      sourceTargetMarkedChamberMap S T q := by
  let z : ℂ := Function.invFunOn S.map (ball (0 : ℂ) 1) q
  have hzball : z ∈ ball (0 : ℂ) 1 := (sourceSeed_invFunOn_bijOn S).mapsTo hq
  let zd : closedBall (0 : ℂ) 1 := ⟨z, ball_subset_closedBall hzball⟩
  have hSmap : S.map z = (q : ℂ) :=
    S.bijOn.surjOn.rightInvOn_invFunOn hq
  have hsource : S.closureEquiv.symm q = zd := by
    apply S.closureEquiv.injective
    rw [S.closureEquiv.apply_symm_apply]
    apply Subtype.ext
    simpa only [S.closureEquiv_apply, zd] using hSmap.symm
  rw [sourceTargetMarkedClosureEquiv, Homeomorph.trans_apply, Homeomorph.trans_apply,
    hsource]
  rw [T.closureEquiv_apply, coe_closedBallHomeomorphOf_apply]
  rfl

/-! The rational closed-disc theorem discharges the two auxiliary closure hypotheses. -/

/-- The canonical marked homeomorphism of chamber closures, conditional only on the orientation
of the two marked boundary triples. -/
noncomputable def sourceTargetMarkedClosureEquivOfOrientation
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    closure sourceBoundedChamber ≃ₜ closure targetBoundedChamber :=
  sourceTargetMarkedClosureEquiv S T horient
    (sourceTargetMarkedDiscMap_continuousOn_closedBall S T horient)
    (sourceTargetMarkedDiscMap_bijOn_closedBall S T horient)

theorem sourceTargetMarkedClosureEquivOfOrientation_cusp
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    sourceTargetMarkedClosureEquivOfOrientation S T horient
      ⟨sourceCuspVertex, frontier_subset_closure sourceCuspVertex_mem_frontier⟩ =
      ⟨targetCuspVertex, frontier_subset_closure targetCuspVertex_mem_frontier⟩ :=
  sourceTargetMarkedClosureEquiv_cusp S T horient
    (sourceTargetMarkedDiscMap_continuousOn_closedBall S T horient)
    (sourceTargetMarkedDiscMap_bijOn_closedBall S T horient)

theorem sourceTargetMarkedClosureEquivOfOrientation_orderThree
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    sourceTargetMarkedClosureEquivOfOrientation S T horient
      ⟨sourceOrderThreeVertex,
        frontier_subset_closure sourceOrderThreeVertex_mem_frontier⟩ =
      ⟨targetOrderThreeVertex,
        frontier_subset_closure targetOrderThreeVertex_mem_frontier⟩ :=
  sourceTargetMarkedClosureEquiv_orderThree S T horient
    (sourceTargetMarkedDiscMap_continuousOn_closedBall S T horient)
    (sourceTargetMarkedDiscMap_bijOn_closedBall S T horient)

theorem sourceTargetMarkedClosureEquivOfOrientation_otherElliptic
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T) :
    sourceTargetMarkedClosureEquivOfOrientation S T horient
      ⟨sourceOtherEllipticVertex,
        frontier_subset_closure sourceOtherEllipticVertex_mem_frontier⟩ =
      ⟨targetOtherEllipticVertex,
        frontier_subset_closure targetOtherEllipticVertex_mem_frontier⟩ :=
  sourceTargetMarkedClosureEquiv_otherElliptic S T horient
    (sourceTargetMarkedDiscMap_continuousOn_closedBall S T horient)
    (sourceTargetMarkedDiscMap_bijOn_closedBall S T horient)

theorem sourceTargetMarkedClosureEquivOfOrientation_apply_of_mem
    (S : ChamberCaratheodorySeed sourceBoundedChamber)
    (T : ChamberCaratheodorySeed targetBoundedChamber)
    (horient : SourceTargetSeedSameOrientation S T)
    (q : closure sourceBoundedChamber) (hq : (q : ℂ) ∈ sourceBoundedChamber) :
    (sourceTargetMarkedClosureEquivOfOrientation S T horient q : ℂ) =
      sourceTargetMarkedChamberMap S T q :=
  sourceTargetMarkedClosureEquiv_apply_of_mem S T horient
    (sourceTargetMarkedDiscMap_continuousOn_closedBall S T horient)
    (sourceTargetMarkedDiscMap_bijOn_closedBall S T horient) q hq


end SphereSixComplex.Periods.SourceChamberTopology
