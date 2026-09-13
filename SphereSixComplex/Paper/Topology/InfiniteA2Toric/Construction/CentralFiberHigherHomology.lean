module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralFiberHomology
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryHomology
public import SphereSixComplex.Prerequisites.Topology.StandardFourTorusHomologicalModel

@[expose] public section
noncomputable section

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
open SphereSixComplex.Periods CuspCollar CuspPeriodExpansion
open IntegralMayerVietoris StandardTorusHomology

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}
  (W : ActualPuncturedCuspCollarWitness N constructedModel)
  (r s : ℝ) (hr : 0 < r) (hrs : r < s) (hs1 : s ≤ 1)

include hr hrs hs1

theorem subsingleton_piecesHomology (n : ℕ) (hn : 2 < n) :
    Subsingleton (IntegralSingularHomology n (inner W s) ×
      IntegralSingularHomology n (outer W r)) := by
  let _ := subsingleton_homology_stdTorus_of_lt 2 n hn
  let _ : Subsingleton (IntegralSingularHomology n (centralBoundary W)) :=
    CentralBoundary.subsingleton_actualHomology W n hn
  exact ⟨fun x y => (piecesHomologyEquiv W r s hr hrs hs1 n).injective
    (Subsingleton.elim _ _)⟩

theorem exists_higherHomologyEquiv (n : ℕ) (hn : 2 < n) :
    Nonempty (IntegralSingularHomology (n + 1) (ActualLocalCuspCentralOrbitQuotient W) ≃+
      IntegralSingularHomology n (StdTorus 3)) := by
  let _ := subsingleton_piecesHomology W r s hr hrs hs1 n hn
  let _ := subsingleton_piecesHomology W r s hr hrs hs1 (n + 1) (by omega)
  obtain ⟨δ, hδ⟩ := exact_sequence_of_isOpen (inner W s) (outer W r)
    (isOpen_inner W s) (isOpen_outer W r)
  have hi : Function.Injective (δ n) := by
    apply (injective_iff_map_eq_zero (δ n)).mpr
    intro x hx
    obtain ⟨y, hy⟩ := ((hδ n).1 x).mp hx
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa [hy0] using hy.symm
  have hs : Function.Surjective (δ n) := by
    intro x
    exact ((hδ n).2.1 x).mp (Subsingleton.elim _ _)
  exact ⟨(integralSingularHomologyEquiv (n + 1)
    (unionHomeomorph W r s hrs)).symm.trans
      ((AddEquiv.ofBijective (δ n) ⟨hi, hs⟩).trans
        (overlapHomologyEquiv W r s hr hrs hs1 n))⟩

theorem subsingleton_homology (n : ℕ) (hn : 4 < n) :
    Subsingleton (IntegralSingularHomology n (ActualLocalCuspCentralOrbitQuotient W)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨e⟩ := exists_higherHomologyEquiv W r s hr hrs hs1 k (by omega)
  let _ := subsingleton_homology_stdTorus_of_lt 3 k (by omega)
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

theorem exists_homologyThreeEquiv :
    Nonempty (IntegralSingularHomology 3 (ActualLocalCuspCentralOrbitQuotient W) ≃+
      (Fin 2 → ℤ)) := by
  let _ := subsingleton_piecesHomology W r s hr hrs hs1 3 (by omega)
  let A := overlapHomologyEquiv W r s hr hrs hs1 2
  let P := piecesHomologyEquiv W r s hr hrs hs1 2
  obtain ⟨δ, hex⟩ := exact_sequence_of_isOpen (inner W s) (outer W r)
    (isOpen_inner W s) (isOpen_outer W r)
  have hi : Function.Injective (δ 2) := by
    apply (injective_iff_map_eq_zero (δ 2)).mpr
    intro x hx
    obtain ⟨y, hy⟩ := ((hex 2).1 x).mp hx
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa [hy0] using hy.symm
  have hd (z) : P (differenceMap (inner W s) (outer W r) 2 z) =
      (integralSingularHomologyMap 2 threeTorusTailProjection (A z), 0) := by
    simpa only [centralTorusAttachingMap_homologyTwo_eq_zero W, AddMonoidHom.zero_apply, neg_zero] using
      differenceMap_coordinates W r s hr hrs hs1 2 z
  let f := standardThreeTorusDegreeTwoCoordinateHom.comp (A.toAddMonoidHom.comp (δ 2))
  have hf : Function.Injective f :=
    standardThreeTorusDegreeTwoCoordinateHom_injective.comp (A.injective.comp hi)
  have hf2 (x) : f x 2 = 0 := by
    have hz := congrArg Prod.fst (hd (δ 2 x))
    rw [(hex 2).2.1.apply_apply_eq_zero, map_zero] at hz
    have hz' : (f x 2) • standardTwoTorusHomologyGenerator = 0 :=
      (threeTorusTailProjection_homologyTwo (A (δ 2 x))).symm.trans hz.symm
    have he := congrArg (fun z => stdTorusHomologyTwo 2 z
      standardTwoTorusDegreeTwoIndex) hz'
    simpa [standardTwoTorusHomologyGenerator] using he
  let g : IntegralSingularHomology 3 (inner W s ∪ outer W r : Set _) →+ (Fin 2 → ℤ) :=
    { toFun := fun x i => f x i.castSucc
      map_zero' := by ext i; simp
      map_add' := by intros; ext i; simp }
  have hg : Function.Bijective g := by
    constructor
    · apply (injective_iff_map_eq_zero g).mpr
      intro x hx
      apply hf
      rw [map_zero]
      funext i
      fin_cases i
      · exact congrFun hx 0
      · exact congrFun hx 1
      · exact hf2 x
    · intro v
      let z := standardThreeTorusHomologyTwo.symm ![v 0, v 1, 0]
      have hz : standardThreeTorusDegreeTwoCoordinateHom z = ![v 0, v 1, 0] :=
        standardThreeTorusHomologyTwo.apply_symm_apply _
      have hp : integralSingularHomologyMap 2 threeTorusTailProjection z = 0 := by
        rw [threeTorusTailProjection_homologyTwo, hz]
        simp
      have hd0 : differenceMap (inner W s) (outer W r) 2 (A.symm z) = 0 := by
        apply P.injective
        rw [hd, A.apply_symm_apply, hp, map_zero]
        rfl
      obtain ⟨x, hx⟩ := ((hex 2).2.1 (A.symm z)).mp hd0
      refine ⟨x, ?_⟩
      change (fun i : Fin 2 => standardThreeTorusDegreeTwoCoordinateHom
        (A (δ 2 x)) i.castSucc) = v
      rw [hx, A.apply_symm_apply, hz]
      ext i
      fin_cases i <;> rfl
  exact ⟨(integralSingularHomologyEquiv 3 (unionHomeomorph W r s hrs)).symm.trans
    (AddEquiv.ofBijective g hg)⟩

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralFiberHomology
