module

public import SphereSixComplex.Topology.RelativeSingularHomology
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Collapsing the boundary of the seven-disk

This file constructs the topological quotient which collapses the boundary of a disk, identifies
its underlying point set with the one-point extension of the disk interior, and records the
standard homeomorphism from the one-point compactification of the open seven-ball to the
seven-sphere.

It also constructs the canonical chain map from relative singular chains of a pair to singular
chains of its collapse quotient modulo the collapsed basepoint.  The remaining comparison is the
excision assertion that this concrete map is a quasi-isomorphism; mathlib currently has no theorem
which proves it.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Function Metric Set Topology

namespace SphereSixComplex

section Collapse

variable {A X : TopCat} (i : A ⟶ X)

/-- The equivalence relation which identifies all points in the image of `i` and no others. -/
public def collapseSetoid : Setoid X where
  r x y := x = y ∨ (x ∈ Set.range i ∧ y ∈ Set.range i)
  iseqv := by
    refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
    · intro x y h
      exact h.elim (fun hxy ↦ Or.inl hxy.symm) fun hxy ↦ Or.inr ⟨hxy.2, hxy.1⟩
    · intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy⟩
      · exact hyz
      rcases hyz with rfl | ⟨_, hz⟩
      · exact Or.inr ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hz⟩

/-- The point-set quotient obtained by collapsing the image of `i`. -/
public abbrev CollapseQuotient := Quotient (collapseSetoid i)

/-- The collapse quotient as a categorical topological space, with the quotient topology. -/
public noncomputable def collapseQuotientObj : TopCat :=
  TopCat.of (CollapseQuotient i)

/-- The canonical quotient map which collapses the image of `i`. -/
public noncomputable def collapseQuotientMap : X ⟶ collapseQuotientObj i :=
  TopCat.ofHom ⟨@Quotient.mk' X (collapseSetoid i), continuous_quotient_mk'⟩

@[simp]
public theorem collapseQuotientMap_apply (x : X) :
    collapseQuotientMap i x = @Quotient.mk' X (collapseSetoid i) x :=
  rfl

/-- A chosen point of the collapsed subspace determines the distinguished quotient point. -/
public noncomputable def collapseQuotientBasepoint (a : A) :
    TopCat.of PUnit ⟶ collapseQuotientObj i :=
  TopCat.ofHom
    ⟨fun _ ↦ @Quotient.mk' X (collapseSetoid i) (i a), continuous_const⟩

/-- The unique map to the one-point space. -/
public noncomputable def collapseToPoint : A ⟶ TopCat.of PUnit :=
  TopCat.ofHom ⟨fun _ ↦ PUnit.unit, continuous_const⟩

/-- The quotient map is constant on the collapsed subspace. -/
public theorem collapseQuotientMap_comp_subspace (a : A) :
    i ≫ collapseQuotientMap i = collapseToPoint ≫ collapseQuotientBasepoint i a := by
  ext x
  change @Quotient.mk' X (collapseSetoid i) (i x) =
    @Quotient.mk' X (collapseSetoid i) (i a)
  apply Quotient.sound
  exact Or.inr ⟨⟨x, rfl⟩, ⟨a, rfl⟩⟩

/-- Points outside the collapsed image. -/
public abbrev CollapseComplement := {x : X // x ∉ Set.range i}

/-- The prequotient collapse map: points of the complement remain finite and points in the
collapsed image are sent to infinity. -/
public noncomputable def collapseToOnePointComplement : X →
    OnePoint (CollapseComplement i) := by
  classical
  exact fun x ↦ if hx : x ∈ Set.range i then OnePoint.infty
    else (↑(⟨x, hx⟩ : CollapseComplement i))

@[simp]
public theorem collapseToOnePointComplement_of_mem {x : X} (hx : x ∈ Set.range i) :
    collapseToOnePointComplement i x = OnePoint.infty := by
  simp [collapseToOnePointComplement, hx]

@[simp]
public theorem collapseToOnePointComplement_of_notMem {x : X} (hx : x ∉ Set.range i) :
    collapseToOnePointComplement i x = (↑(⟨x, hx⟩ : CollapseComplement i)) := by
  simp [collapseToOnePointComplement, hx]

/-- The underlying point-set quotient is the one-point extension of the complement. -/
public noncomputable def collapseQuotientEquivOnePointComplement (a : A) :
    CollapseQuotient i ≃ OnePoint (CollapseComplement i) := by
  classical
  let f := collapseToOnePointComplement i
  have hf : ∀ x y, collapseSetoid i x y → f x = f y := by
    intro x y hxy
    rcases hxy with rfl | ⟨hx, hy⟩
    · rfl
    · dsimp [f]
      rw [collapseToOnePointComplement_of_mem i hx,
        collapseToOnePointComplement_of_mem i hy]
  let g : OnePoint (CollapseComplement i) → CollapseQuotient i := fun p ↦
    p.elim (@Quotient.mk' X (collapseSetoid i) (i a))
      (fun x ↦ @Quotient.mk' X (collapseSetoid i) x.1)
  refine
    { toFun := Quotient.lift f hf
      invFun := g
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hx : x ∈ Set.range i
    · change g (f x) = @Quotient.mk' X (collapseSetoid i) x
      have hfx : f x = OnePoint.infty := by
        exact collapseToOnePointComplement_of_mem i hx
      rw [hfx]
      change @Quotient.mk' X (collapseSetoid i) (i a) =
        @Quotient.mk' X (collapseSetoid i) x
      apply Quotient.sound
      exact Or.inr ⟨⟨a, rfl⟩, hx⟩
    · change g (f x) = @Quotient.mk' X (collapseSetoid i) x
      have hfx : f x = (↑(⟨x, hx⟩ : CollapseComplement i) :
          OnePoint (CollapseComplement i)) := by
        exact collapseToOnePointComplement_of_notMem i hx
      rw [hfx]
      rfl
  · intro p
    induction p using OnePoint.rec with
    | infty =>
        change Quotient.lift f hf (@Quotient.mk' X (collapseSetoid i) (i a)) = _
        change f (i a) = _
        exact collapseToOnePointComplement_of_mem i ⟨a, rfl⟩
    | coe x =>
        change Quotient.lift f hf (@Quotient.mk' X (collapseSetoid i) x.1) = _
        change f x.1 = _
        exact collapseToOnePointComplement_of_notMem i x.2

@[simp]
public theorem collapseQuotientEquivOnePointComplement_mk (a : A) (x : X) :
    collapseQuotientEquivOnePointComplement i a
        (@Quotient.mk' X (collapseSetoid i) x) = collapseToOnePointComplement i x :=
  rfl

/-- If the uncollapsed complement is open in a Hausdorff ambient space, the prequotient collapse
map to its one-point compactification is continuous. -/
public theorem continuous_collapseToOnePointComplement [T2Space X]
    (hopen : IsOpen {x : X | x ∉ Set.range i}) :
    Continuous (collapseToOnePointComplement i) := by
  classical
  rw [continuous_def]
  intro s hs
  have hs' := OnePoint.isOpen_def.mp hs
  by_cases hinf : OnePoint.infty ∈ s
  · have hpre : collapseToOnePointComplement i ⁻¹' s =
        (((↑) : CollapseComplement i → X) ''
          (((↑) : CollapseComplement i → OnePoint (CollapseComplement i)) ⁻¹' s)ᶜ)ᶜ := by
      ext x
      by_cases hx : x ∈ Set.range i
      · constructor
        · intro _ hImage
          obtain ⟨z, _, hzx⟩ := hImage
          exact z.2 (by simpa [← hzx] using hx)
        · intro _
          change collapseToOnePointComplement i x ∈ s
          rw [collapseToOnePointComplement_of_mem i hx]
          exact hinf
      · change collapseToOnePointComplement i x ∈ s ↔ _
        rw [collapseToOnePointComplement_of_notMem i hx]
        constructor
        · intro hxs hImage
          obtain ⟨z, hz, hzx⟩ := hImage
          have hzEq : z = ⟨x, hx⟩ := Subtype.ext hzx
          subst z
          exact hz hxs
        · intro hnot
          by_contra hxs
          apply hnot
          exact ⟨⟨x, hx⟩, hxs, rfl⟩
    rw [hpre]
    exact ((hs'.1 hinf).image continuous_subtype_val).isClosed.isOpen_compl
  · have hpre : collapseToOnePointComplement i ⁻¹' s =
        ((↑) : CollapseComplement i → X) ''
          (((↑) : CollapseComplement i → OnePoint (CollapseComplement i)) ⁻¹' s) := by
      ext x
      by_cases hx : x ∈ Set.range i
      · constructor
        · intro hxs
          exact (hinf (by simpa [collapseToOnePointComplement_of_mem i hx] using hxs)).elim
        · rintro ⟨z, _, hzx⟩
          exact (z.2 (by simpa [← hzx] using hx)).elim
      · change collapseToOnePointComplement i x ∈ s ↔ _
        rw [collapseToOnePointComplement_of_notMem i hx]
        constructor
        · intro hxs
          exact ⟨⟨x, hx⟩, hxs, rfl⟩
        · rintro ⟨z, hzs, hzx⟩
          have hzEq : z = ⟨x, hx⟩ := Subtype.ext hzx
          simpa [hzEq] using hzs
    rw [hpre]
    exact hopen.isOpenMap_subtype_val _ hs'.2

/-- Reduced singular chains based at `b`, modeled as the cokernel of the singular chains of the
basepoint inclusion. -/
public noncomputable abbrev ReducedIntegralSingularChainComplex
    {Q : TopCat} (b : TopCat.of PUnit ⟶ Q) : ChainComplex AddCommGrpCat ℕ :=
  RelativeIntegralSingularChainComplex b

/-- The quotient singular-chain map followed by projection away from the collapsed basepoint. -/
public noncomputable def collapseAmbientToReducedChains (a : A) :
    IntegralSingularChainComplexObj X ⟶
      ReducedIntegralSingularChainComplex (collapseQuotientBasepoint i a) :=
  integralSingularChainMapObj (collapseQuotientMap i) ≫
    relativeIntegralSingularChainProjection (collapseQuotientBasepoint i a)

/-- The ambient-to-reduced map kills chains coming from the collapsed subspace. -/
public theorem collapseAmbientToReducedChains_comp_subspace (a : A) :
    integralSingularChainMapObj i ≫ collapseAmbientToReducedChains i a = 0 := by
  rw [collapseAmbientToReducedChains, ← Category.assoc]
  change
    (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map i ≫
      ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (collapseQuotientMap i)) ≫ _ = 0
  rw [← Functor.map_comp]
  rw [collapseQuotientMap_comp_subspace i a]
  rw [Functor.map_comp]
  change
    ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map collapseToPoint ≫
      (((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (collapseQuotientBasepoint i a) ≫
        cokernel.π (((singularChainComplexFunctor AddCommGrpCat).obj
          (AddCommGrpCat.of ℤ)).map (collapseQuotientBasepoint i a))) = 0
  rw [cokernel.condition]
  exact Limits.comp_zero

/-- The canonical chain map from relative chains to reduced chains of the collapse quotient. -/
public noncomputable def relativeChainsToReducedCollapseChains (a : A) :
    RelativeIntegralSingularChainComplex i ⟶
      ReducedIntegralSingularChainComplex (collapseQuotientBasepoint i a) :=
  cokernel.desc (integralSingularChainMapObj i)
    (collapseAmbientToReducedChains i a)
    (collapseAmbientToReducedChains_comp_subspace i a)

@[reassoc (attr := simp)]
public theorem relativeChainsToReducedCollapseChains_comp_projection (a : A) :
    relativeIntegralSingularChainProjection i ≫
      relativeChainsToReducedCollapseChains i a = collapseAmbientToReducedChains i a :=
  cokernel.π_desc _ _ _

end Collapse

section SevenDisk

/-- The quotient `D⁷/S⁶`. -/
public noncomputable abbrev DiskBoundaryQuotientSeven :=
  CollapseQuotient (TopCat.diskBoundaryInclusion.{0} 7)

/-- The topological quotient `D⁷/S⁶`. -/
public noncomputable abbrev DiskBoundaryQuotientSevenObj :=
  collapseQuotientObj (TopCat.diskBoundaryInclusion.{0} 7)

/-- The quotient map `D⁷ ⟶ D⁷/S⁶`. -/
public noncomputable abbrev diskBoundaryQuotientSevenMap :
    TopCat.disk.{0} 7 ⟶ DiskBoundaryQuotientSevenObj :=
  collapseQuotientMap (TopCat.diskBoundaryInclusion.{0} 7)

/-- The canonical disk-collapse map is a quotient map. -/
public theorem diskBoundaryQuotientSevenMap_isQuotientMap :
    IsQuotientMap diskBoundaryQuotientSevenMap :=
  isQuotientMap_quotient_mk'

/-- A concrete point on `S⁶ = ∂D⁷`. -/
public noncomputable def diskBoundarySevenBasepoint : TopCat.diskBoundary.{0} 7 := by
  let v : EuclideanSpace ℝ (Fin 7) := PiLp.single 2 (0 : Fin 7) 1
  exact ULift.up ⟨v, by simp [v]⟩

/-- The distinguished collapsed boundary point of `D⁷/S⁶`. -/
public noncomputable abbrev diskBoundaryQuotientSevenBasepoint :
    TopCat.of PUnit ⟶ DiskBoundaryQuotientSevenObj :=
  collapseQuotientBasepoint (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint

/-- Every boundary point maps to the distinguished collapsed point. -/
@[simp]
public theorem diskBoundaryQuotientSevenMap_boundary (x : TopCat.diskBoundary.{0} 7) :
    diskBoundaryQuotientSevenMap ((TopCat.diskBoundaryInclusion.{0} 7) x) =
      diskBoundaryQuotientSevenBasepoint PUnit.unit := by
  apply Quotient.sound
  exact Or.inr ⟨⟨x, rfl⟩, ⟨diskBoundarySevenBasepoint, rfl⟩⟩

/-- The complement of the collapsed boundary inside the closed disk is homeomorphic to the open
ball. -/
public noncomputable def diskSevenComplementBoundaryEquivBall :
    CollapseComplement (TopCat.diskBoundaryInclusion.{0} 7) ≃
      (TopCat.ball.{0} 7 : Type) :=
    { toFun := fun x ↦
        ⟨x.1.down.1, by
          have hxclosed := x.1.down.2
          simp only [Metric.mem_closedBall, dist_zero_right] at hxclosed
          simpa only [Metric.mem_ball, dist_zero_right] using
            (lt_of_le_of_ne hxclosed fun h ↦ x.2
              ⟨ULift.up ⟨x.1.down.1, by
                simpa only [Metric.mem_sphere, dist_zero_right] using h⟩, rfl⟩)⟩
      invFun := fun x ↦
        ⟨ULift.up ⟨x.down.1, Metric.ball_subset_closedBall x.down.2⟩, by
          intro hx
          obtain ⟨y, hy⟩ := hx
          have heq : y.down.1 = x.down.1 := by
            exact congrArg (fun z : TopCat.disk.{0} 7 => z.down.1) hy
          have hnorm : ‖x.down.1‖ = 1 := by
            simpa only [Metric.mem_sphere, dist_zero_right, heq] using y.down.2
          have hlt : ‖x.down.1‖ < 1 := by
            simpa only [Metric.mem_ball, dist_zero_right] using x.down.2
          exact hlt.ne hnorm⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply ULift.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply ULift.ext
        apply Subtype.ext
        rfl }

/-- The disk interior, viewed as the complement of the boundary image, is open in the closed
disk. -/
public theorem diskSevenCollapseComplement_isOpen :
    IsOpen {x : (TopCat.disk.{0} 7 : Type) |
      x ∉ Set.range (TopCat.diskBoundaryInclusion.{0} 7)} := by
  have hset : {x : (TopCat.disk.{0} 7 : Type) |
      x ∉ Set.range (TopCat.diskBoundaryInclusion.{0} 7)} =
      {x | ‖x.down.1‖ < 1} := by
    ext x
    constructor
    · intro hx
      have hle : ‖x.down.1‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using x.down.2
      exact lt_of_le_of_ne hle fun heq ↦ hx
        ⟨ULift.up ⟨x.down.1, by
          simpa only [Metric.mem_sphere, dist_zero_right] using heq⟩, rfl⟩
    · intro hlt hx
      obtain ⟨y, hy⟩ := hx
      have hxy : y.down.1 = x.down.1 :=
        congrArg (fun z : TopCat.disk.{0} 7 ↦ z.down.1) hy
      have hyNorm : ‖y.down.1‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using y.down.2
      exact hlt.ne (hxy ▸ hyNorm)
  rw [hset]
  exact isOpen_lt
    (continuous_norm.comp (continuous_subtype_val.comp continuous_uliftDown))
    continuous_const

/-- The preceding point-set equivalence is a homeomorphism. -/
public noncomputable def diskSevenComplementBoundaryHomeomorphBall :
    CollapseComplement (TopCat.diskBoundaryInclusion.{0} 7) ≃ₜ
      (TopCat.ball.{0} 7 : Type) where
  toEquiv := diskSevenComplementBoundaryEquivBall
  continuous_toFun := by
    dsimp only [diskSevenComplementBoundaryEquivBall]
    fun_prop
  continuous_invFun := by
    dsimp only [diskSevenComplementBoundaryEquivBall]
    fun_prop

/-- The one-point compactification of the open seven-ball is the standard seven-sphere. -/
public noncomputable def onePointBallSevenHomeomorphSphereSeven :
    OnePoint (TopCat.ball.{0} 7 : Type) ≃ₜ
      (TopCat.sphere.{0} 7 : Type) := by
  let euclideanToBall : EuclideanSpace ℝ (Fin 7) ≃ₜ (TopCat.ball.{0} 7 : Type) :=
    (Homeomorph.unitBall : EuclideanSpace ℝ (Fin 7) ≃ₜ
      Metric.ball (0 : EuclideanSpace ℝ (Fin 7)) 1) |>.trans Homeomorph.ulift.symm
  exact (euclideanToBall.symm.onePointCongr).trans <|
    (onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin 7)) (by simp)).trans
      Homeomorph.ulift.symm

/-- The explicit point-set equivalence `D⁷/S⁶ ≃ S⁷`. -/
public noncomputable def diskBoundaryQuotientSevenEquivSphereSeven :
    DiskBoundaryQuotientSeven ≃ (TopCat.sphere.{0} 7 : Type) :=
  (collapseQuotientEquivOnePointComplement
      (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint).trans
    ((diskSevenComplementBoundaryHomeomorphBall.onePointCongr.trans
      onePointBallSevenHomeomorphSphereSeven).toEquiv)

/-- The sphere point corresponding to the collapsed boundary. -/
public noncomputable def diskBoundaryQuotientSevenSphereBasepoint :
    TopCat.sphere.{0} 7 :=
  onePointBallSevenHomeomorphSphereSeven OnePoint.infty

/-- The geometric continuity statement that the explicit quotient-to-one-point-complement
equivalence respects the quotient topology. -/
public def DiskBoundaryCollapseToOnePointContinuous : Prop :=
  Continuous (collapseQuotientEquivOnePointComplement
    (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint)

/-- The explicit quotient-to-one-point-complement equivalence is continuous. -/
public theorem diskBoundaryCollapseToOnePointContinuous :
    DiskBoundaryCollapseToOnePointContinuous := by
  let _ : T2Space (TopCat.disk.{0} 7 : Type) := Homeomorph.ulift.symm.t2Space
  change Continuous (collapseQuotientEquivOnePointComplement
    (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint)
  rw [isQuotientMap_quotient_mk'.continuous_iff]
  have hfun :
      (collapseQuotientEquivOnePointComplement
        (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint) ∘
          (@Quotient.mk' (TopCat.disk.{0} 7 : Type)
            (collapseSetoid (TopCat.diskBoundaryInclusion.{0} 7))) =
        collapseToOnePointComplement (TopCat.diskBoundaryInclusion.{0} 7) := by
    funext x
    exact collapseQuotientEquivOnePointComplement_mk _ _ x
  rw [hfun]
  exact continuous_collapseToOnePointComplement (TopCat.diskBoundaryInclusion.{0} 7)
    diskSevenCollapseComplement_isOpen

/-- The quotient-topology statement promoting the point-set equivalence to a homeomorphism. -/
public def DiskBoundaryQuotientSevenTopologyComparison : Prop :=
  Continuous diskBoundaryQuotientSevenEquivSphereSeven

/-- The topology comparison follows from continuity of the sole non-library factor. -/
public theorem diskBoundaryQuotientSevenTopologyComparison_of_collapseContinuous
    (h : DiskBoundaryCollapseToOnePointContinuous) :
    DiskBoundaryQuotientSevenTopologyComparison :=
  (diskSevenComplementBoundaryHomeomorphBall.onePointCongr.trans
    onePointBallSevenHomeomorphSphereSeven).continuous.comp h

/-- The explicit point-set equivalence `D⁷/S⁶ ≃ S⁷` is continuous. -/
public theorem diskBoundaryQuotientSevenTopologyComparison :
    DiskBoundaryQuotientSevenTopologyComparison :=
  diskBoundaryQuotientSevenTopologyComparison_of_collapseContinuous
    diskBoundaryCollapseToOnePointContinuous

/-- Continuity of the explicit equivalence gives the expected homeomorphism.  Its inverse is
automatic because the quotient is compact and the sphere is Hausdorff. -/
public noncomputable def diskBoundaryQuotientSevenHomeomorphSphereSeven
    : DiskBoundaryQuotientSeven ≃ₜ (TopCat.sphere.{0} 7 : Type) := by
  letI : T2Space (TopCat.sphere.{0} 7 : Type) :=
    Homeomorph.ulift.symm.t2Space
  exact diskBoundaryQuotientSevenTopologyComparison.homeoOfEquivCompactToT2

/-- The collapse quotient as a categorical space is isomorphic to the standard seven-sphere. -/
public noncomputable def diskBoundaryQuotientSevenSphereIso :
    DiskBoundaryQuotientSevenObj ≅ TopCat.sphere.{0} 7 :=
  TopCat.isoOfHomeo diskBoundaryQuotientSevenHomeomorphSphereSeven

/-- The image on the sphere of the collapsed boundary basepoint. -/
public noncomputable def sphereSevenCollapsedBoundaryBasepoint :
    TopCat.of PUnit ⟶ TopCat.sphere.{0} 7 :=
  TopCat.ofHom ⟨fun _ ↦ diskBoundaryQuotientSevenHomeomorphSphereSeven
    (diskBoundaryQuotientSevenBasepoint PUnit.unit), continuous_const⟩

/-- The quotient-to-sphere isomorphism preserves the specified basepoint. -/
public theorem diskBoundaryQuotientSevenSphereIso_basepoint :
    diskBoundaryQuotientSevenBasepoint ≫ diskBoundaryQuotientSevenSphereIso.hom =
      sphereSevenCollapsedBoundaryBasepoint := by
  ext x
  cases x
  rfl

/-- Reduced singular chains of the quotient are isomorphic to reduced singular chains of the
standard seven-sphere, based at the image of the collapsed boundary. -/
public noncomputable def reducedDiskBoundaryQuotientChainsIsoReducedSphereSevenChains :
    ReducedIntegralSingularChainComplex diskBoundaryQuotientSevenBasepoint ≅
      ReducedIntegralSingularChainComplex sphereSevenCollapsedBoundaryBasepoint := by
  let F := (singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  exact cokernel.mapIso (integralSingularChainMapObj diskBoundaryQuotientSevenBasepoint)
    (integralSingularChainMapObj sphereSevenCollapsedBoundaryBasepoint)
    (Iso.refl (IntegralSingularChainComplexObj (TopCat.of PUnit)))
    (F.mapIso diskBoundaryQuotientSevenSphereIso) (by
      change F.map diskBoundaryQuotientSevenBasepoint ≫
          F.map diskBoundaryQuotientSevenSphereIso.hom =
        (Iso.refl _).hom ≫ F.map sphereSevenCollapsedBoundaryBasepoint
      rw [← F.map_comp, diskBoundaryQuotientSevenSphereIso_basepoint,
        Iso.refl_hom, Category.id_comp])

/-- The canonical relative-to-reduced chain comparison for the pair `(D⁷,S⁶)`. -/
public noncomputable abbrev diskSevenRelativeChainsToReducedQuotientChains :
    DiskSevenSphereSixRelativeIntegralSingularChainComplex ⟶
      ReducedIntegralSingularChainComplex diskBoundaryQuotientSevenBasepoint :=
  relativeChainsToReducedCollapseChains
    (TopCat.diskBoundaryInclusion.{0} 7) diskBoundarySevenBasepoint

/-- The canonical comparison transported along `D⁷/S⁶ ≃ₜ S⁷`, now landing in reduced
singular chains of the standard seven-sphere. -/
public noncomputable def diskSevenRelativeChainsToReducedSphereSevenChains :
    DiskSevenSphereSixRelativeIntegralSingularChainComplex ⟶
      ReducedIntegralSingularChainComplex sphereSevenCollapsedBoundaryBasepoint :=
  diskSevenRelativeChainsToReducedQuotientChains ≫
    reducedDiskBoundaryQuotientChainsIsoReducedSphereSevenChains.hom

/-- The exact missing excision statement: the canonical chain map from relative chains of
`(D⁷,S⁶)` to reduced chains of `D⁷/S⁶` induces homology isomorphisms. -/
public def DiskSevenRelativeQuotientExcision : Prop :=
  ∀ n : ℕ,
    IsIso (HomologicalComplex.homologyMap
      diskSevenRelativeChainsToReducedQuotientChains n)

/-- Excision would make the transported comparison to the standard sphere a homology
isomorphism in every degree. -/
public theorem diskSevenRelativeSphereComparison_isIso
    (h : DiskSevenRelativeQuotientExcision) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      diskSevenRelativeChainsToReducedSphereSevenChains n) := by
  let _ := h n
  dsimp [diskSevenRelativeChainsToReducedSphereSevenChains]
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

end SevenDisk

end SphereSixComplex
