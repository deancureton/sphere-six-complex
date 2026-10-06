module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.EuclideanLocalCapDuality
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeEmpty
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ConnectedZeroCohomology
public import DifferentialGeometry.External.CanonicalTopology.Topology.Algebra.Module.Pairing
public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.OneDimensionalLocalCapDuality

@[expose] public section
noncomputable section

open CategoryTheory Metric Module Set

universe u

namespace DifferentialGeometry.Topology

private theorem exists_innerProduct_local_top_cap_bijective
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ c : integralLocalHomology (finrank ℝ E) (0 : E),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (finrank ℝ E) 0 α c) := by
  by_cases hlarge : 2 ≤ finrank ℝ E
  · have hd : finrank ℝ E = (finrank ℝ E - 2) + 2 := by omega
    rw [hd]
    exact ⟨(integralEuclideanLocalTopZeroEquiv E (finrank ℝ E - 2) hd).symm 1,
      integralEuclideanLocalTopZeroEquiv_cap_bijective (finrank ℝ E - 2) E hd⟩
  by_cases hzero : finrank ℝ E = 0
  · have hempty : ({0}ᶜ : Set E) = ∅ := by
      ext x
      constructor
      · intro hx
        exact (hx (finrank_zero_iff_forall_zero.mp hzero x)).elim
      · intro hx
        exact hx.elim
    change ∃ c : integralRelativeHomology (finrank ℝ E) ({0}ᶜ : Set E),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (finrank ℝ E) 0 α c)
    rw [hzero, hempty]
    let e := integralSingularHomologyZeroEquiv (X := E)
    let c := e.symm 1
    have hc : Function.Bijective (fun z : ℤ => z • c) := by
      have hfun : (fun z : ℤ => z • c) = e.symm := by
        funext z
        change z • e.symm 1 = e.symm z
        rw [← map_zsmul]
        congr 1
        exact mul_one z
      rw [hfun]
      exact e.symm.bijective
    have hcap : Function.Bijective (fun α : integralSingularCohomology 0 E =>
        integralSingularCohomologyCapProduct 0 0 α c) :=
      (integralSingularCohomologyCapProduct_zero_bijective_iff 0 c).mpr hc
    refine ⟨integralAbsoluteToRelative 0 (∅ : Set E) c, ?_⟩
    have hfun : (fun α : integralRelativeCohomology 0 (∅ : Set E) =>
        integralRelativeCohomologyCapToAbsolute (∅ : Set E) 0 0 α
          (integralAbsoluteToRelative 0 (∅ : Set E) c)) =
        (fun α : integralSingularCohomology 0 E =>
          integralSingularCohomologyCapProduct 0 0 α c) ∘
            integralRelativeToAbsoluteCohomology 0 (∅ : Set E) := by
      funext α
      exact integralRelativeCohomologyCapToAbsolute_absoluteToRelative (∅ : Set E) 0 0 α c
    rw [hfun]
    exact hcap.comp (integralRelativeToAbsoluteCohomologyEmptyEquiv 0 E).bijective
  have hone : finrank ℝ E = 1 := by omega
  change ∃ c : integralRelativeHomology (finrank ℝ E) ({0}ᶜ : Set E),
    Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
        ({0}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set E) (finrank ℝ E) 0 α c)
  rw [hone]
  exact exists_integralLocalHomology_cap_bijective_of_finrank_one E hone

private theorem exists_normed_local_top_cap_bijective
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) :
    ∃ c : integralLocalHomology (finrank ℝ E) p,
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({p}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (finrank ℝ E) 0 α c) := by
  let ι := Module.Free.ChooseBasisIndex ℝ E
  let b : Basis ι ℝ E := Module.Free.chooseBasis ℝ E
  let e : E ≃L[ℝ] EuclideanSpace ℝ ι :=
    b.equivFunL.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let h := e.symm.toHomeomorph.trans (Homeomorph.addRight p)
  have hp : h 0 = p := by
    change e.symm 0 + p = p
    rw [map_zero, zero_add]
  have hex : ∃ c : integralLocalHomology (finrank ℝ E) (0 : EuclideanSpace ℝ ι),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({0}ᶜ : Set (EuclideanSpace ℝ ι)) =>
        integralRelativeCohomologyCapToAbsolute ({0}ᶜ : Set (EuclideanSpace ℝ ι))
          (finrank ℝ E) 0 α c) := by
    rw [e.toLinearEquiv.finrank_eq]
    exact exists_innerProduct_local_top_cap_bijective (EuclideanSpace ℝ ι)
  let f : ContinuousMap (EuclideanSpace ℝ ι) E := ⟨h, h.continuous⟩
  have hf : MapsTo f ({0}ᶜ : Set (EuclideanSpace ℝ ι)) ({h 0}ᶜ : Set E) :=
    fun _ hx => h.injective.ne hx
  let g := h.subtype (p := fun x : EuclideanSpace ℝ ι => x ∈ ({0}ᶜ : Set (EuclideanSpace ℝ ι)))
    (q := fun y : E => y ∈ ({h 0}ᶜ : Set E)) (fun x => h.injective.ne_iff.symm)
  have hcoh : Function.Bijective (integralRelativeCohomologyMap (finrank ℝ E) f hf) := by
    apply integralRelativeCohomologyMap_bijective_of_absolute_and_subspace
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv h.toHomotopyEquiv n
    · intro n
      exact integralSingularCohomologyMap_bijective_of_homotopyEquiv g.toHomotopyEquiv n
  obtain ⟨c, hc⟩ := hex
  have hcap := integralRelativeCohomologyCapToAbsolute_bijective_map (finrank ℝ E) 0 f hf
    (integralSingularHomologyZeroMapEquiv f).bijective hcoh c hc
  have hout : ∃ d : integralLocalHomology (finrank ℝ E) (h 0),
      Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E)
          ({h 0}ᶜ : Set E) =>
        integralRelativeCohomologyCapToAbsolute ({h 0}ᶜ : Set E) (finrank ℝ E) 0 α d) :=
    ⟨integralRelativeHomologyMap (finrank ℝ E) f hf c, hcap⟩
  rwa [hp] at hout

theorem integralLocalHomology_cap_bijective_of_generator
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : E) (c : integralLocalHomology (finrank ℝ E) p)
    (hc : Function.Bijective (fun z : ℤ => z • c)) :
    Function.Bijective (fun α : integralRelativeCohomology (finrank ℝ E) ({p}ᶜ : Set E) =>
      integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (finrank ℝ E) 0 α c) := by
  let f : ℤ →+ integralLocalHomology (finrank ℝ E) p :=
    { toFun := fun z => z • c
      map_zero' := zero_zsmul c
      map_add' := fun z w => add_zsmul c z w }
  let e := (AddEquiv.ofBijective f hc).symm
  have he : e.symm 1 = c := one_zsmul c
  obtain ⟨d, hd⟩ := exists_normed_local_top_cap_bijective p
  let B := fun α : integralRelativeCohomology (finrank ℝ E) ({p}ᶜ : Set E) =>
    integralZeroAugmentation.toAddMonoidHom.comp
      ((integralRelativeCohomologyCapToAbsolute ({p}ᶜ : Set E) (finrank ℝ E) 0 α).toAddMonoidHom)
  have hdB : Function.Bijective (fun α => B α d) :=
    integralConnectedZeroAugmentationEquiv.bijective.comp hd
  have h := additive_pairing_bijective_at_generator B e d hdB
  rw [he] at h
  exact (Function.Bijective.of_comp_iff' integralConnectedZeroAugmentationEquiv.bijective _).mp h

end DifferentialGeometry.Topology
