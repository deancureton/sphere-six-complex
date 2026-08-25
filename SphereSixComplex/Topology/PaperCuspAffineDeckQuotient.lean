module

public import SphereSixComplex.Topology.PaperCuspBoundaryUniversalCover

/-!
# The cusp affine deck quotient

The actual boundary deck group is the semidirect product of lattice translations by the angular
meridian acting through `M₀`.  Since `M₀` fixes the first two coordinates, the cusp filling kills
the toric translation sublattice and the angular factor, leaving the parameter lattice.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology

open LatticeData
open SphereSixComplex.Geometry.CuspFilling

/-- The residual projection is invariant under the cusp monodromy. -/
public theorem paperCuspResidualProjection_monodromy (a : Lattice) :
    paperCuspResidualProjection (paperCuspMonodromy a) = paperCuspResidualProjection a := by
  rw [paperCuspMonodromy_apply]
  funext i
  fin_cases i
  · have h := congrFun (M₀_sub_mulVec a) (0 : Fin 4)
    simp at h
    change M₀.mulVec a 0 = a 0
    omega
  · have h := congrFun (M₀_sub_mulVec a) (1 : Fin 4)
    simp at h
    change M₀.mulVec a 1 = a 1
    omega

/-- The residual projection is invariant under inverse cusp monodromy. -/
public theorem paperCuspResidualProjection_monodromy_inv (a : Lattice) :
    paperCuspResidualProjection ((-paperCuspMonodromy) a) =
      paperCuspResidualProjection a := by
  have h := paperCuspResidualProjection_monodromy ((-paperCuspMonodromy) a)
  rw [AddAut.neg_apply, paperCuspMonodromy.apply_symm_apply] at h
  exact h.symm

/-- The residual projection is invariant under every integral power of cusp monodromy. -/
public theorem paperCuspResidualProjection_integerPower (n : ℤ) (a : Lattice) :
    paperCuspResidualProjection ((n • paperCuspMonodromy) a) =
      paperCuspResidualProjection a := by
  induction n using Int.induction_on generalizing a with
  | zero => simp
  | succ i hi =>
      rw [show ((i : ℤ) + 1) • paperCuspMonodromy =
          (i : ℤ) • paperCuspMonodromy + paperCuspMonodromy by
        rw [add_zsmul, one_zsmul],
        AddAut.add_apply, hi, paperCuspResidualProjection_monodromy]
  | pred i hi =>
      rw [show (- (i : ℤ) - 1) • paperCuspMonodromy =
          (- (i : ℤ)) • paperCuspMonodromy + (-paperCuspMonodromy) by
        rw [sub_eq_add_neg, add_zsmul, neg_one_zsmul],
        AddAut.add_apply, hi, paperCuspResidualProjection_monodromy_inv]

/-- The semidirect angular action is invisible after residual projection. -/
public theorem paperCuspResidualProjection_integerAffineMonodromy
    (n : Multiplicative ℤ) (a : Multiplicative Lattice) :
    paperCuspResidualProjection
        ((integerAffineMonodromy paperCuspMonodromy n a).toAdd) =
      paperCuspResidualProjection a.toAdd :=
  paperCuspResidualProjection_integerPower n.toAdd a.toAdd

/-- The residual cusp deck map keeps the first two translation coordinates and kills the angular
meridian. -/
public def paperCuspBoundaryDeckProjection :
    paperCuspBoundaryDeck →* Multiplicative ParameterLattice :=
  SemidirectProduct.lift paperCuspResidualProjection.toMultiplicative 1 (by
    intro n
    apply MonoidHom.ext
    intro a
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply]
    change Multiplicative.ofAdd
        (paperCuspResidualProjection
          ((integerAffineMonodromy paperCuspMonodromy n a).toAdd)) =
      1 * Multiplicative.ofAdd (paperCuspResidualProjection a.toAdd) * 1⁻¹
    simpa using congrArg Multiplicative.ofAdd
      (paperCuspResidualProjection_integerAffineMonodromy n a))

@[simp]
public theorem paperCuspBoundaryDeckProjection_apply
    (a : Multiplicative Lattice) (n : Multiplicative ℤ) :
    paperCuspBoundaryDeckProjection (⟨a, n⟩ : paperCuspBoundaryDeck) =
      Multiplicative.ofAdd (paperCuspResidualProjection a.toAdd) := by
  change Multiplicative.ofAdd (paperCuspResidualProjection a.toAdd) * 1 = _
  simp

/-- The residual cusp deck map is onto. -/
public theorem paperCuspBoundaryDeckProjection_surjective :
    Function.Surjective paperCuspBoundaryDeckProjection := by
  intro b
  obtain ⟨a, ha⟩ := paperCuspResidualProjection_surjective b.toAdd
  refine ⟨(⟨Multiplicative.ofAdd a, 1⟩ : paperCuspBoundaryDeck), ?_⟩
  rw [paperCuspBoundaryDeckProjection_apply]
  apply Multiplicative.toAdd.injective
  exact ha

/-- The residual cusp deck map kills exactly the toric filling relations. -/
public theorem paperCuspBoundaryDeckProjection_ker :
    paperCuspBoundaryDeckProjection.ker = paperCuspBoundaryDeckData.fillingKernel := by
  let D := paperCuspBoundaryDeckData
  apply le_antisymm
  · intro g hg
    rcases g with ⟨a, n⟩
    have ha0 : paperCuspResidualProjection a.toAdd = 0 := by
      change paperCuspBoundaryDeckProjection (⟨a, n⟩ : paperCuspBoundaryDeck) = 1 at hg
      rw [paperCuspBoundaryDeckProjection_apply] at hg
      apply Multiplicative.ofAdd.injective
      simpa using hg
    have ha : a.toAdd ∈ paperToricSubgroup := by
      rw [← paperCuspResidualProjection_ker]
      exact ha0
    obtain ⟨k, hk⟩ := paperCuspVanishing_onto a.toAdd ha
    have htranslation :
        SemidirectProduct.inl (φ := integerAffineMonodromy paperCuspMonodromy) a ∈
          D.fillingKernel := by
      apply Subgroup.subset_normalClosure
      refine Or.inl ⟨k, ?_⟩
      change SemidirectProduct.inl (Multiplicative.ofAdd (paperCuspVanishing k)) =
        SemidirectProduct.inl a
      rw [hk]
      rfl
    have hmeridian : paperCuspBoundaryMeridian ∈ D.fillingKernel := by
      apply Subgroup.subset_normalClosure
      exact Or.inr (Set.mem_singleton _)
    have hright :
        SemidirectProduct.inr (φ := integerAffineMonodromy paperCuspMonodromy) n ∈
          D.fillingKernel := by
      rw [show SemidirectProduct.inr n = paperCuspBoundaryMeridian ^ n.toAdd by
        change SemidirectProduct.inr n =
          (SemidirectProduct.inr (Multiplicative.ofAdd 1)) ^ n.toAdd
        rw [← map_zpow]
        congr 1
        apply Multiplicative.toAdd.injective
        simp]
      exact D.fillingKernel.zpow_mem hmeridian n.toAdd
    rw [← SemidirectProduct.inl_left_mul_inr_right
      (⟨a, n⟩ : paperCuspBoundaryDeck)]
    exact D.fillingKernel.mul_mem htranslation hright
  · rw [UnwrappedToricBoundaryDeckData.fillingKernel]
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    rcases hg with hg | hg
    · obtain ⟨k, rfl⟩ := hg
      have hgen :
          Additive.toMul
              (paperCuspBoundaryDeckData.translation
                (paperCuspBoundaryDeckData.vanishing k)) =
            (⟨Multiplicative.ofAdd (paperCuspVanishing k), 1⟩ :
              paperCuspBoundaryDeck) := by
        rfl
      change Additive.toMul
          (paperCuspBoundaryDeckData.translation
            (paperCuspBoundaryDeckData.vanishing k)) ∈
        paperCuspBoundaryDeckProjection.ker
      rw [hgen, MonoidHom.mem_ker, paperCuspBoundaryDeckProjection_apply]
      have hk : paperCuspResidualProjection (paperCuspVanishing k) = 0 := by
        rw [← AddMonoidHom.mem_ker, paperCuspResidualProjection_ker]
        exact k.property
      simpa using congrArg Multiplicative.ofAdd hk
    · rw [Set.mem_singleton_iff] at hg
      subst g
      have hmeridian : paperCuspBoundaryDeckData.meridian =
          (⟨1, Multiplicative.ofAdd 1⟩ : paperCuspBoundaryDeck) := by
        rfl
      change paperCuspBoundaryDeckData.meridian ∈ paperCuspBoundaryDeckProjection.ker
      rw [hmeridian, MonoidHom.mem_ker, paperCuspBoundaryDeckProjection_apply]
      simp

/-- The cusp filling deck group is canonically the multiplicative parameter lattice. -/
public noncomputable def paperCuspFillingDeckEquiv :
    paperCuspBoundaryDeckData.FillingDeck ≃* Multiplicative ParameterLattice :=
  QuotientGroup.liftEquiv paperCuspBoundaryDeckData.fillingKernel
    paperCuspBoundaryDeckProjection_surjective paperCuspBoundaryDeckProjection_ker.symm

/-- The canonical cusp filling quotient map agrees with the residual cusp deck projection. -/
@[simp]
public theorem paperCuspFillingDeckEquiv_fillingDeckMap (g : paperCuspBoundaryDeck) :
    paperCuspFillingDeckEquiv (paperCuspBoundaryDeckData.fillingDeckMap g) =
      paperCuspBoundaryDeckProjection g := by
  exact QuotientGroup.liftEquiv_mk paperCuspBoundaryDeckData.fillingKernel
    paperCuspBoundaryDeckProjection_surjective paperCuspBoundaryDeckProjection_ker.symm g

end SphereSixComplex.Topology

end
