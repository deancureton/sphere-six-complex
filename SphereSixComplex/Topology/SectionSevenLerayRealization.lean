module

public import SphereSixComplex.Topology.SectionSevenLerayHomologyDuality

/-!
# Coherent singular realization of the finite Leray model

A realization consists of one chain map from the finite Section 7 model to integral singular
chains, together with the assertion that this same map induces an isomorphism in every degree.
The algebraic duality datum fixes the remaining coefficient and supplies the model calculation.

Mathlib does not currently compute the singular homology of the standard six-sphere.  Consequently
one coherent realization gives the existing `SectionSevenHomologyRealization` contract, while two
coherent realizations through the same model (one for `X` and one for `SixSphere`) give
`HasIntegralHomologyOfSixSphere X`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- The unique additive equivalence between two subsingleton additive commutative groups. -/
public def sectionSevenSubsingletonAddEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    [Subsingleton A] [Subsingleton B] : A ≃+ B where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _

/-- The finite Leray model has zero homology in every degree above six. -/
public theorem sectionSevenLerayChainModel_homology_isZero_of_six_lt
    (top : ℤ) (k : ℕ) (hk : 6 < k) :
    IsZero ((sectionSevenLerayChainModel top).homology k) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.ExactAt.of_isZero
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 7 := by
    exact ⟨k - 7, by omega⟩
  change IsZero (AddCommGrpCat.of (SectionSevenLerayGroup (n + 7)))
  let _ : Subsingleton (SectionSevenLerayGroup (n + 7)) := by
    change Subsingleton (Fin (sectionSevenLerayRank (n + 7)) → ℤ)
    constructor
    intro f g
    funext i
    exact Fin.elim0 i
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The endpoint value of the computed graded group has its inherited integer addition. -/
public def sectionSevenComputedHomologyZeroEquivInteger :
    SectionSevenComputedHomology 0 ≃+ ℤ where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    change x + y = x + y
    rfl

/-- The top-degree value of the computed graded group has its inherited integer addition. -/
public def sectionSevenComputedHomologySixEquivInteger :
    SectionSevenComputedHomology 6 ≃+ ℤ where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' x y := by
    change x + y = x + y
    rfl

/-- The chain model's homology is the graded group recorded by the original Section 7 contract. -/
public noncomputable def SectionSevenLerayAlgebraicDuality.modelHomologyEquivComputed
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) (k : ℕ) :
    (sectionSevenLerayChainModel top).homology k ≃+ SectionSevenComputedHomology k := by
  rcases k with (_ | _ | _ | _ | _ | _ | _ | k)
  · exact (sectionSevenLerayChainModel_homology_zero_equiv top).trans
      sectionSevenComputedHomologyZeroEquivInteger.symm
  · letI : Subsingleton ((sectionSevenLerayChainModel top).homology 1) :=
      AddCommGrpCat.subsingleton_of_isZero (h.middle_homology_isZero 1 (by omega) (by omega))
    change (sectionSevenLerayChainModel top).homology 1 ≃+ ZMod 1
    exact sectionSevenSubsingletonAddEquiv _ _
  · letI : Subsingleton ((sectionSevenLerayChainModel top).homology 2) :=
      AddCommGrpCat.subsingleton_of_isZero (h.middle_homology_isZero 2 (by omega) (by omega))
    change (sectionSevenLerayChainModel top).homology 2 ≃+ ZMod 1
    exact sectionSevenSubsingletonAddEquiv _ _
  · letI : Subsingleton ((sectionSevenLerayChainModel top).homology 3) :=
      AddCommGrpCat.subsingleton_of_isZero (h.middle_homology_isZero 3 (by omega) (by omega))
    change (sectionSevenLerayChainModel top).homology 3 ≃+ ZMod 1
    exact sectionSevenSubsingletonAddEquiv _ _
  · letI : Subsingleton ((sectionSevenLerayChainModel top).homology 4) :=
      AddCommGrpCat.subsingleton_of_isZero (h.middle_homology_isZero 4 (by omega) (by omega))
    change (sectionSevenLerayChainModel top).homology 4 ≃+ ZMod 1
    exact sectionSevenSubsingletonAddEquiv _ _
  · letI : Subsingleton ((sectionSevenLerayChainModel top).homology 5) :=
      AddCommGrpCat.subsingleton_of_isZero (h.middle_homology_isZero 5 (by omega) (by omega))
    change (sectionSevenLerayChainModel top).homology 5 ≃+ ZMod 1
    exact sectionSevenSubsingletonAddEquiv _ _
  · exact (sectionSevenLerayChainModel_homology_six_equiv top).trans
      sectionSevenComputedHomologySixEquivInteger.symm
  · letI : Subsingleton ((sectionSevenLerayChainModel top).homology (k + 7)) :=
      AddCommGrpCat.subsingleton_of_isZero
        (sectionSevenLerayChainModel_homology_isZero_of_six_lt top (k + 7) (by omega))
    change (sectionSevenLerayChainModel top).homology (k + 7) ≃+ ZMod 1
    exact sectionSevenSubsingletonAddEquiv _ _

/-- A single coherent realization of the finite Leray calculation in integral singular chains. -/
public structure SectionSevenLerayCoherentRealization
    (X : Type) [TopologicalSpace X] where
  /-- The unresolved coefficient in the finite chain model. -/
  top : ℤ
  /-- The explicit algebraic duality data fixing that coefficient. -/
  duality : SectionSevenLerayAlgebraicDuality top
  /-- One chain map realizing the whole finite model. -/
  comparison : sectionSevenLerayChainModel top ⟶ IntegralSingularChainComplex X
  /-- The one comparison map induces an isomorphism in every degree. -/
  homologyMap_isIso : ∀ k : ℕ,
    IsIso ((sectionSevenLerayChainModel top).homologyMap comparison k)

/-- A coherent chain realization supplies the existing degreewise Section 7 realization contract;
all degrees use the homology maps of the same chain map. -/
public theorem SectionSevenLerayCoherentRealization.sectionSevenHomologyRealization
    {X : Type} [TopologicalSpace X] (h : SectionSevenLerayCoherentRealization X) :
    SectionSevenHomologyRealization X := by
  intro k
  let _ : IsIso ((sectionSevenLerayChainModel h.top).homologyMap h.comparison k) :=
    h.homologyMap_isIso k
  exact ⟨(asIso ((sectionSevenLerayChainModel h.top).homologyMap h.comparison k)).symm
    |>.addCommGroupIsoToAddEquiv.trans (h.duality.modelHomologyEquivComputed k)⟩

/-- Coherent realizations of `X` and the standard sphere through the verified finite model give the
project's actual integral-homology-sphere contract. -/
public theorem SectionSevenLerayCoherentRealization.hasIntegralHomologyOfSixSphere
    {X : Type} [TopologicalSpace X]
    (hX : SectionSevenLerayCoherentRealization X)
    (hSphere : SectionSevenLerayCoherentRealization SixSphere) :
    HasIntegralHomologyOfSixSphere X :=
  hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations
    hX.sectionSevenHomologyRealization hSphere.sectionSevenHomologyRealization

end SphereSixComplex
