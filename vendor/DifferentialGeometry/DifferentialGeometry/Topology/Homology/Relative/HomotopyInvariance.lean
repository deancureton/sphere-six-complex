module

public import DifferentialGeometry.Topology.Homology.Relative.PairVanishing
public import DifferentialGeometry.Topology.Homology.Relative.SingularExcision

@[expose] public section

open CategoryTheory Limits HomologicalComplex
open scoped ContinuousMap

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

theorem isIso_relativeHomologyMap_of_isIso_singularHomologyMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f : X ⟶ Y)
    (hf : Set.MapsTo f A B) (h₁ : ∀ n, IsIso (singularHomologyMap R (restr f hf) n))
    (h₂ : ∀ n, IsIso (singularHomologyMap R f n)) (k : ℕ) : IsIso (relativeHomologyMap R f hf k) :=
  isIso_homologyMap_of_quasiIso R (pairMap f hf)
    ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).2 (h₁ n)⟩
    ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ n).2 (h₂ n)⟩ k

section inclusion

variable {X : Type u} [TopologicalSpace X] {A A' B B' : Set X}

theorem mapsTo_inclOfLE_preimage (hBB' : B ⊆ B') (hAA' : A ⊆ A') :
    Set.MapsTo (inclOfLE (X := TopCat.of X) hBB') (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' A') :=
  fun _ hx => hAA' hx

theorem isIso_singularHomologyMap_restr_inclOfLE (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hA : isHomotopyEquivInclusion A A') (n : ℕ) :
    IsIso (singularHomologyMap R (restr (inclOfLE (X := TopCat.of X) hBB')
      (mapsTo_inclOfLE_preimage hBB' hAA')) n) := by
  obtain ⟨eA, heA⟩ := hA
  let e' : (Subtype.val ⁻¹' A : Set B) ≃ₕ (Subtype.val ⁻¹' A' : Set B') :=
    (homeomorphPreimageVal hAB).toHomotopyEquiv.trans
      (eA.trans (homeomorphPreimageVal hA'B').symm.toHomotopyEquiv)
  have h : TopCat.ofHom e'.toFun =
      restr (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') := by
    ext x
    exact heA _
  rw [← h]
  exact isIso_singularHomologyMap_of_homotopyEquiv R e' n

theorem isIso_singularHomologyMap_inclOfLE (hBB' : B ⊆ B') (hB : isHomotopyEquivInclusion B B') (n : ℕ) :
    IsIso (singularHomologyMap R (inclOfLE (X := TopCat.of X) hBB') n) := by
  obtain ⟨eB, heB⟩ := hB
  have h : TopCat.ofHom eB.toFun = inclOfLE (X := TopCat.of X) hBB' := by
    ext x
    exact heB _
  rw [← h]
  exact isIso_singularHomologyMap_of_homotopyEquiv R eB n

theorem isIso_relativeHomologyMap_inclOfLE_of_homotopyEquiv (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hB : isHomotopyEquivInclusion B B') (hA : isHomotopyEquivInclusion A A')
    (k : ℕ) :
    IsIso (relativeHomologyMap R (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') k) :=
  isIso_relativeHomologyMap_of_isIso_singularHomologyMap R _ _ (isIso_singularHomologyMap_restr_inclOfLE R hAB hA'B' hBB' hAA' hA)
    (isIso_singularHomologyMap_inclOfLE R hBB' hB) k

def relativeHomologyIsoOfHomotopyEquivInclusion (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hB : isHomotopyEquivInclusion B B') (hA : isHomotopyEquivInclusion A A')
    (k : ℕ) :
    relativeHomology R (TopCat.of B) (Subtype.val ⁻¹' A) k ≅ relativeHomology R (TopCat.of B') (Subtype.val ⁻¹' A') k :=
  haveI := isIso_relativeHomologyMap_inclOfLE_of_homotopyEquiv R hAB hA'B' hBB' hAA' hB hA k
  asIso (relativeHomologyMap R (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') k)

lemma relativeHomologyIsoOfHomotopyEquivInclusion_hom (hAB : A ⊆ B) (hA'B' : A' ⊆ B') (hBB' : B ⊆ B')
    (hAA' : A ⊆ A') (hB : isHomotopyEquivInclusion B B') (hA : isHomotopyEquivInclusion A A')
    (k : ℕ) :
    (relativeHomologyIsoOfHomotopyEquivInclusion R hAB hA'B' hBB' hAA' hB hA k).hom =
      relativeHomologyMap R (inclOfLE (X := TopCat.of X) hBB') (mapsTo_inclOfLE_preimage hBB' hAA') k := rfl

end inclusion

theorem relHomologyVanishes_of_isIso_inclMap {X : Type u} [TopologicalSpace X] {A B : Set X}
    (h : ∀ k, IsIso (inclMap integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) k)) :
    relHomologyVanishes B (Subtype.val ⁻¹' A) := by
  have hπ : ∀ n, relπ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₂ integerCoefficients _ _ n).epi_f_iff.1 (haveI := h n; inferInstance)
  have hδ : ∀ n, δ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) n = 0 := fun n =>
    (les_exact₁ integerCoefficients _ _ n).mono_g_iff.1 (haveI := h n; inferInstance)
  intro n
  cases n with
  | zero =>
    let : HasCoproducts.{u} (ModuleCat.{u} ℤ) := fun _ => inferInstance
    have : Epi (relπ integerCoefficients (TopCat.of B) (Subtype.val ⁻¹' A) 0) :=
      inferInstanceAs (Epi ((pair (TopCat.of B) (Subtype.val ⁻¹' A)).homologyπ integerCoefficients 0))
    exact IsZero.of_epi_eq_zero _ (hπ 0)
  | succ n => exact (les_exact₃ integerCoefficients _ _ n).isZero_X₂ (hπ (n + 1)) (hδ n)

end DifferentialGeometry.Topology.SingularPair

end
