module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.Grp.Abelian

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SphereSixComplex

variable (S T : ShortComplex (ChainComplex AddCommGrpCat ℕ)) (hS : S.ShortExact)
  {F G : S.X₂ ⟶ T.X₂} (H : Homotopy F G)
  (hH : ∀ i j, S.f.f i ≫ H.hom i j ≫ T.g.f j = 0)

public def quotientChainHomotopyComponent (i j : ℕ) : S.X₃.X i ⟶ T.X₃.X j := by
  have := hS.mono_f
  have := hS.epi_g
  let hs := hS.map (eval AddCommGrpCat (ComplexShape.down ℕ) i)
  have := hs.epi_g
  exact hs.exact.desc (H.hom i j ≫ T.g.f j) (hH i j)

public theorem quotientChainHomotopyComponent_projection (i j : ℕ) :
    S.g.f i ≫ quotientChainHomotopyComponent S T hS H hH i j = H.hom i j ≫ T.g.f j := by
  have := hS.mono_f
  have := hS.epi_g
  let hs := hS.map (eval AddCommGrpCat (ComplexShape.down ℕ) i)
  have := hs.epi_g
  exact hs.exact.g_desc _ _

public def quotientChainHomotopy {f g : S.X₃ ⟶ T.X₃}
    (hf : S.g ≫ f = F ≫ T.g) (hg : S.g ≫ g = G ≫ T.g) : Homotopy f g where
  hom := quotientChainHomotopyComponent S T hS H hH
  zero i j hij := by
    have := hS.epi_g
    apply (cancel_epi (S.g.f i)).mp
    rw [quotientChainHomotopyComponent_projection, H.zero i j hij, zero_comp, comp_zero]
  comm i := by
    have := hS.epi_g
    apply (cancel_epi (S.g.f i)).mp
    have he : (fun i j ↦ S.g.f i ≫ quotientChainHomotopyComponent S T hS H hH i j) =
        (fun i j ↦ H.hom i j ≫ T.g.f j) := by
      funext i j
      exact quotientChainHomotopyComponent_projection S T hS H hH i j
    rw [Preadditive.comp_add, Preadditive.comp_add,
      ← dNext_comp_left, ← prevD_comp_left, he, dNext_comp_right, prevD_comp_right]
    have hf' := congrArg (fun k ↦ k.f i) hf
    have hg' := congrArg (fun k ↦ k.f i) hg
    change S.g.f i ≫ f.f i = F.f i ≫ T.g.f i at hf'
    change S.g.f i ≫ g.f i = G.f i ≫ T.g.f i at hg'
    rw [hf', hg', H.comm i, Preadditive.add_comp, Preadditive.add_comp]

end SphereSixComplex
