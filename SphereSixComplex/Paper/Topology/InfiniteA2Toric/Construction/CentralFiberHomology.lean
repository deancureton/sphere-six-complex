module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralAttachingHomology
public import SphereSixComplex.Prerequisites.Topology.ExactSplitting
public import SphereSixComplex.Prerequisites.Topology.IntegralMayerVietorisTheorem

/-! # Mayer–Vietoris for the radial cover of the central fiber -/

@[expose] public section
noncomputable section
open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
open SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates
open IntegralMayerVietoris StandardTorusHomology

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

abbrev inner (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℝ) :=
  {x | centralRadius W x < s}
abbrev outer (W : ActualPuncturedCuspCollarWitness N constructedModel) (r : ℝ) :=
  {x | r < centralRadius W x}

theorem isOpen_inner (W : ActualPuncturedCuspCollarWitness N constructedModel) (s : ℝ) :
    IsOpen (inner W s) := isOpen_lt (centralRadius W).continuous continuous_const

theorem isOpen_outer (W : ActualPuncturedCuspCollarWitness N constructedModel) (r : ℝ) :
    IsOpen (outer W r) := isOpen_lt continuous_const (centralRadius W).continuous

theorem inner_union_outer (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hrs : r < s) : inner W s ∪ outer W r = univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (lt_or_ge (centralRadius W x) s).imp_right (fun h ↦ hrs.trans_le h)

def unionHomeomorph (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hrs : r < s) :
    (inner W s ∪ outer W r : Set _) ≃ₜ ActualLocalCuspCentralOrbitQuotient W :=
  (Homeomorph.setCongr (inner_union_outer W r s hrs)).trans (Homeomorph.Set.univ _)

def overlapHomeomorph (W : ActualPuncturedCuspCollarWitness N constructedModel) (r s : ℝ) :
    (inner W s ∩ outer W r : Set _) ≃ₜ {x | centralRadius W x ∈ Ioo r s} :=
  Homeomorph.setCongr (by ext x; exact and_comm)

def overlapHomologyEquiv (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) (n : ℕ) :
    IntegralSingularHomology n (inner W s ∩ outer W r : Set _) ≃+
      IntegralSingularHomology n (StdTorus 3) :=
  (integralSingularHomologyEquiv n (overlapHomeomorph W r s)).trans
    (integralSingularHomologyEquivOfHomotopyEquiv n
      (centralAnnulusTorusHomotopyEquiv W r s hr hrs hs1))

def piecesHomologyEquiv (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) (n : ℕ) :
    (IntegralSingularHomology n (inner W s) × IntegralSingularHomology n (outer W r)) ≃+
      (IntegralSingularHomology n (StdTorus 2) × IntegralSingularHomology n (centralBoundary W)) :=
  (integralSingularHomologyEquivOfHomotopyEquiv n
    (centralInnerTorusHomotopyEquiv W s (hr.trans hrs) hs1)).prodCongr
      (integralSingularHomologyEquivOfHomotopyEquiv n
        (centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1)))

theorem differenceMap_coordinates
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) (n : ℕ)
    (x : IntegralSingularHomology n (inner W s ∩ outer W r : Set _)) :
    piecesHomologyEquiv W r s hr hrs hs1 n (differenceMap (inner W s) (outer W r) n x) =
      (integralSingularHomologyMap n threeTorusTailProjection
          (overlapHomologyEquiv W r s hr hrs hs1 n x),
        -integralSingularHomologyMap n (centralTorusAttachingMap W)
          (overlapHomologyEquiv W r s hr hrs hs1 n x)) := by
  have hl : (interToLeft (inner W s) (outer W r)) =
      (centralAnnulusToInner W r s).comp (overlapHomeomorph W r s : C(_, _)) := rfl
  have hv : (interToRight (inner W s) (outer W r)) =
      (centralAnnulusToOuter W r s).comp (overlapHomeomorph W r s : C(_, _)) := rfl
  apply Prod.ext
  · change integralSingularHomologyMap n
      (centralInnerTorusHomotopyEquiv W s (hr.trans hrs) hs1).toFun
      (integralSingularHomologyMap n (interToLeft (inner W s) (outer W r)) x) = _
    rw [hl, ← integralSingularHomologyMap_comp_wang, centralAnnulusToInner_homology_coordinates]
    rfl
  · change integralSingularHomologyMap n
      (centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1)).toFun
      (-integralSingularHomologyMap n (interToRight (inner W s) (outer W r)) x) = _
    rw [map_neg, hv, ← integralSingularHomologyMap_comp_wang,
      centralAnnulusToOuter_homology_coordinates]
    rfl

theorem exists_union_homologyTwo_split
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    ∃ e : IntegralSingularHomology 2 (inner W s ∪ outer W r : Set _) ≃+
        (IntegralSingularHomology 2 (centralBoundary W) × ℤ),
      ∀ y, e (sumMap (inner W s) (outer W r) 2
        ((piecesHomologyEquiv W r s hr hrs hs1 2).symm (0, y))) = (y, 0) := by
  let A := overlapHomologyEquiv W r s hr hrs hs1
  let P := piecesHomologyEquiv W r s hr hrs hs1
  obtain ⟨δ, hex⟩ := exact_sequence_of_isOpen (inner W s) (outer W r)
    (isOpen_inner W s) (isOpen_outer W r)
  let b := (sumMap (inner W s) (outer W r) 2).comp (P 2).symm.toAddMonoidHom
  let c := (A 1).toAddMonoidHom.comp (δ 1)
  let j := b.comp (AddMonoidHom.inr (IntegralSingularHomology 2 (StdTorus 2))
    (IntegralSingularHomology 2 (centralBoundary W)))
  let head : IntegralSingularHomology 1 (StdTorus 3) →+ ℤ :=
    { toFun := fun x ↦ standardThreeTorusDegreeOneCoordinateHom x 0
      map_zero' := by simp
      map_add' := by intro x y; simp }
  let q := head.comp c
  have hd1 (z) : P 1 (differenceMap (inner W s) (outer W r) 1 z) =
      (integralSingularHomologyMap 1 threeTorusTailProjection (A 1 z), 0) := by
    simpa only [centralTorusAttachingMap_homologyOne_eq_zero W, AddMonoidHom.zero_apply, neg_zero] using
      differenceMap_coordinates W r s hr hrs hs1 1 z
  have hd2 (z) : P 2 (differenceMap (inner W s) (outer W r) 2 z) =
      (integralSingularHomologyMap 2 threeTorusTailProjection (A 2 z), 0) := by
    simpa only [centralTorusAttachingMap_homologyTwo_eq_zero W, AddMonoidHom.zero_apply, neg_zero] using
      differenceMap_coordinates W r s hr hrs hs1 2 z
  have hbzero (u : IntegralSingularHomology 2 (StdTorus 2)) : b (u, 0) = 0 := by
    obtain ⟨z, hz⟩ := threeTorusTailProjection_homology_surjective 2 u
    have hh := hd2 ((A 2).symm z)
    rw [(A 2).apply_symm_apply, hz] at hh
    have hh' : (P 2).symm (u, 0) =
        differenceMap (inner W s) (outer W r) 2 ((A 2).symm z) := by
      rw [← hh, (P 2).symm_apply_apply]
    change sumMap (inner W s) (outer W r) 2 ((P 2).symm (u, 0)) = 0
    rw [hh']
    exact (hex 2).2.2.apply_apply_eq_zero _
  have hcproj (x) : integralSingularHomologyMap 1 threeTorusTailProjection (c x) = 0 := by
    have hh := hd1 (δ 1 x)
    rw [(hex 1).2.1.apply_apply_eq_zero, map_zero] at hh
    exact (congrArg Prod.fst hh).symm
  have hj : Function.Injective j := by
    apply (injective_iff_map_eq_zero j).mpr
    intro y hy
    obtain ⟨z, hz⟩ := ((hex 2).2.2 ((P 2).symm (0, y))).mp hy
    have hh := hd2 z
    rw [hz, (P 2).apply_symm_apply] at hh
    exact congrArg Prod.snd hh
  have hqsurj : Function.Surjective q := by
    intro m
    let z := m • standardThreeTorusCoordinateHomologyClass 0
    have hp : integralSingularHomologyMap 1 threeTorusTailProjection z = 0 := by
      simp [z]
    have hd : differenceMap (inner W s) (outer W r) 1 ((A 1).symm z) = 0 := by
      apply (P 1).injective
      rw [hd1, (A 1).apply_symm_apply, hp, map_zero]
      rfl
    obtain ⟨x, hx⟩ := ((hex 1).2.1 ((A 1).symm z)).mp hd
    refine ⟨x, ?_⟩
    change head (A 1 (δ 1 x)) = m
    rw [hx, (A 1).apply_symm_apply]
    simp [head, z]
  have hjq : Function.Exact j q := by
    intro x
    constructor
    · intro hx
      have hc : c x = 0 := by
        have hh := (threeTorusTailProjection_homologyOne_eq_zero_iff (c x)).mp (hcproj x)
        change standardThreeTorusDegreeOneCoordinateHom (c x) 0 = 0 at hx
        simpa only [hx, zero_smul] using hh
      have hδ : δ 1 x = 0 := (A 1).injective (by exact hc.trans (map_zero _).symm)
      obtain ⟨v, hv⟩ := ((hex 1).1 x).mp hδ
      let u := P 2 v
      have hb : b u = x := by
        change sumMap (inner W s) (outer W r) 2 ((P 2).symm (P 2 v)) = x
        rw [(P 2).symm_apply_apply]
        exact hv
      refine ⟨u.2, ?_⟩
      have hh := b.map_add (u.1, 0) (0, u.2)
      simp only [Prod.mk_add_mk, add_zero, zero_add, hbzero] at hh
      exact hh.symm.trans hb
    · rintro ⟨y, rfl⟩
      have hh := (hex 1).1.apply_apply_eq_zero ((P 2).symm (0, y))
      change head (A 1 (δ 1 (sumMap (inner W s) (outer W r) 2
        ((P 2).symm (0, y))))) = 0
      rw [hh, map_zero, map_zero]
  obtain ⟨e, he, -⟩ := LinearMap.exists_equiv_prod_of_exact j.toIntLinearMap
    q.toIntLinearMap hj hjq hqsurj
  exact ⟨e.toAddEquiv, he⟩

def boundaryInclusion (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    C(centralBoundary W, ActualLocalCuspCentralOrbitQuotient W) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem boundaryInclusion_eq_outer_composite
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    (unionHomeomorph W r s hrs : C(_, _)).comp
      ((rightToUnion (inner W s) (outer W r)).comp
        (centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1)).invFun) =
      boundaryInclusion W := by
  ext b
  change centralAttachmentHomeomorph W
    (AdjunctionSpace.inr _ (centralAttachingMap W) b) = b.1
  exact centralAttachmentHomeomorph_inr W b

private theorem homologyEquiv_apply_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (e : X ≃ₜ Y) (x : IntegralSingularHomology n X) :
    integralSingularHomologyEquiv n e x = integralSingularHomologyMap n (e : C(_, _)) x := rfl

private theorem homotopyHomologyEquiv_symm_apply_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (e : X ≃ₕ Y) (x : IntegralSingularHomology n Y) :
    (integralSingularHomologyEquivOfHomotopyEquiv n e).symm x =
      integralSingularHomologyMap n e.invFun x := rfl

theorem unionHomologyEquiv_outer_summand
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) (n : ℕ)
    (y : IntegralSingularHomology n (centralBoundary W)) :
    integralSingularHomologyEquiv n (unionHomeomorph W r s hrs)
      (sumMap (inner W s) (outer W r) n
        ((piecesHomologyEquiv W r s hr hrs hs1 n).symm (0, y))) =
      integralSingularHomologyMap n (boundaryInclusion W) y := by
  have hp : (piecesHomologyEquiv W r s hr hrs hs1 n).symm (0, y) =
      ((integralSingularHomologyEquivOfHomotopyEquiv n
          (centralInnerTorusHomotopyEquiv W s (hr.trans hrs) hs1)).symm 0,
        (integralSingularHomologyEquivOfHomotopyEquiv n
          (centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1))).symm y) := rfl
  rw [hp, map_zero]
  change integralSingularHomologyEquiv n (unionHomeomorph W r s hrs)
    (integralSingularHomologyMap n (leftToUnion (inner W s) (outer W r)) 0 +
      integralSingularHomologyMap n (rightToUnion (inner W s) (outer W r))
        ((integralSingularHomologyEquivOfHomotopyEquiv n
          (centralOuterHomotopyEquiv W r hr (hrs.trans_le hs1))).symm y)) = _
  rw [map_zero, zero_add]
  rw [homologyEquiv_apply_map, homotopyHomologyEquiv_symm_apply_map]
  rw [integralSingularHomologyMap_comp_wang, integralSingularHomologyMap_comp_wang,
    ContinuousMap.comp_assoc, boundaryInclusion_eq_outer_composite W r s hr hrs hs1]

/-- The central fiber has one additional degree-two generator beyond its boundary.
The boundary inclusion is the first summand of the resulting integral splitting. -/
theorem exists_homologyTwo_split
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1) :
    ∃ e : IntegralSingularHomology 2 (ActualLocalCuspCentralOrbitQuotient W) ≃+
        (IntegralSingularHomology 2 (centralBoundary W) × ℤ),
      ∀ y, e (integralSingularHomologyMap 2 (boundaryInclusion W) y) = (y, 0) := by
  obtain ⟨e, he⟩ := exists_union_homologyTwo_split
    W r s hr hrs hs1
  let u := integralSingularHomologyEquiv 2 (unionHomeomorph W r s hrs)
  refine ⟨u.symm.trans e, ?_⟩
  intro y
  change e (u.symm (integralSingularHomologyMap 2 (boundaryInclusion W) y)) = _
  rw [← unionHomologyEquiv_outer_summand W r s hr hrs hs1 2 y]
  change e (u.symm (u _)) = _
  rw [u.symm_apply_apply]
  exact he y

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
