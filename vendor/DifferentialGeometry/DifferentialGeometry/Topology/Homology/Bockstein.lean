module

public import DifferentialGeometry.Topology.Homology.SingularPair
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Data.ZMod.Basic

@[expose] public section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

instance ab5_moduleCat_int : AB5 (ModuleCat.{u} ℤ) :=
  ⟨fun J _ _ => HasExactColimitsOfShape.domain_of_functor J (forget₂ _ AddCommGrpCat.{u})⟩

attribute [local instance] Abelian.hasFiniteBiproducts in
instance ab4_moduleCat_int : AB4 (ModuleCat.{u} ℤ) := AB4.of_AB5 _

abbrev sigmaFun (ι : Type u) : ModuleCat.{u} ℤ ⥤ ModuleCat.{u} ℤ := sigmaConst.flip.obj ι

lemma sigmaFun_map (ι : Type u) {R R' : ModuleCat.{u} ℤ} (φ : R ⟶ R') :
    (sigmaFun ι).map φ = Limits.Sigma.map (fun _ : ι => φ) := rfl

def sigmaFunIso (ι : Type u) :
    (Functor.const (Discrete ι) ⋙ colim : ModuleCat.{u} ℤ ⥤ _) ≅ sigmaFun ι :=
  NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso Discrete.natIsoFunctor) (by
    intro R R' φ
    apply colimit.hom_ext
    rintro ⟨j⟩
    simp)

instance (ι : Type u) : (sigmaFun ι).Additive where
  map_add {_ _ f g} := by
    apply Sigma.hom_ext
    intro i
    simp [Preadditive.comp_add]

instance (ι : Type u) : PreservesFiniteLimits (sigmaFun ι) :=
  preservesFiniteLimits_of_natIso (sigmaFunIso ι)

instance (ι : Type u) : PreservesFiniteColimits (sigmaFun ι) :=
  preservesFiniteColimits_of_natIso (sigmaFunIso ι)

abbrev modularCoefficients (d : ℕ) : ModuleCat.{u} ℤ := ModuleCat.of ℤ (ULift.{u} (ZMod d))

instance (d : ℕ) [NeZero d] : Finite (modularCoefficients.{u} d) := inferInstanceAs (Finite (ULift (ZMod d)))

def mulD (d : ℕ) : integerCoefficients.{u} ⟶ integerCoefficients.{u} := ModuleCat.ofHom ((d : ℤ) • LinearMap.id)

def redD (d : ℕ) : integerCoefficients.{u} ⟶ modularCoefficients.{u} d :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
    (Int.castAddHom (ZMod d)).toIntLinearMap ∘ₗ ULift.moduleEquiv.toLinearMap)

lemma mulD_eq (d : ℕ) : mulD.{u} d = (d : ℤ) • 𝟙 integerCoefficients.{u} := by
  ext x
  simp [mulD]

lemma mulD_hom_apply (d : ℕ) (x : integerCoefficients.{u}) : (mulD d).hom x = ULift.up ((d : ℤ) * x.down) := rfl

lemma redD_hom_apply (d : ℕ) (x : integerCoefficients.{u}) : (redD d).hom x = ULift.up (x.down : ZMod d) := rfl

lemma mulD_comp_redD (d : ℕ) : mulD.{u} d ≫ redD d = 0 := by
  ext x
  simp [mulD, redD]

def coefSC (d : ℕ) : ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.mk (mulD d) (redD d) (mulD_comp_redD d)

theorem coefSC_shortExact (d : ℕ) [NeZero d] : (coefSC.{u} d).ShortExact := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have : (d : ℤ) ∣ x.down := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact congrArg ULift.down hx
    obtain ⟨c, hc⟩ := this
    exact ⟨ULift.up c, ULift.ext (by change (d : ℤ) * c = x.down; rw [hc])⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have h : (d : ℤ) * x.down = (d : ℤ) * y.down := congrArg ULift.down hxy
    exact ULift.ext (mul_left_cancel₀ hd h)
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    exact ⟨ULift.up (y.down.cast : ℤ), ULift.ext (ZMod.intCast_zmod_cast y.down)⟩

variable (d : ℕ) (X : TopCat.{u})

abbrev chainsOf : ModuleCat.{u} ℤ ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (singularChainComplexFunctor (ModuleCat.{u} ℤ)).flip.obj X

lemma chainsOf_map_f {R R' : ModuleCat.{u} ℤ} (φ : R ⟶ R') (k : ℕ) :
    ((chainsOf X).map φ).f k =
      Limits.Sigma.map (fun _ : (TopCat.toSSet.obj X) _⦋k⦌ => φ) := rfl

def bocksteinSC : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (mulD d)).app X)
    (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (redD d)).app X)
    (by rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, mulD_comp_redD]; simp)

@[simp] lemma bocksteinSC_X₁ : (bocksteinSC d X).X₁ = singularChains integerCoefficients X := rfl
@[simp] lemma bocksteinSC_X₂ : (bocksteinSC d X).X₂ = singularChains integerCoefficients X := rfl
@[simp] lemma bocksteinSC_X₃ : (bocksteinSC d X).X₃ = singularChains (modularCoefficients d) X := rfl

@[simp] lemma bocksteinSC_f :
    (bocksteinSC d X).f = ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (mulD d)).app X :=
  rfl

@[simp] lemma bocksteinSC_g :
    (bocksteinSC d X).g = ((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (redD d)).app X :=
  rfl

lemma bocksteinSC_eq : bocksteinSC d X = (coefSC d).map (chainsOf X) := rfl

lemma bocksteinSC_map_eval (k : ℕ) :
    (bocksteinSC d X).map (eval _ _ k) =
      (coefSC d).map (sigmaFun ((TopCat.toSSet.obj X) _⦋k⦌)) := rfl

theorem bocksteinSC_shortExact [NeZero d] : (bocksteinSC d X).ShortExact := by
  rw [shortExact_iff_degreewise_shortExact]
  intro k
  rw [bocksteinSC_map_eval]
  exact (coefSC_shortExact d).map_of_exact _

def bocksteinδ [NeZero d] (k : ℕ) : singularHomology (modularCoefficients d) X (k + 1) ⟶ singularHomology integerCoefficients X k :=
  (bocksteinSC_shortExact d X).δ (k + 1) k rfl

theorem bockstein_exact₁ [NeZero d] (k : ℕ) :
    (ShortComplex.mk (bocksteinδ d X k) (homologyMap (bocksteinSC d X).f k)
      ((bocksteinSC_shortExact d X).δ_comp (k + 1) k rfl)).Exact :=
  (bocksteinSC_shortExact d X).homology_exact₁ (k + 1) k rfl

theorem bockstein_exact₂ [NeZero d] (k : ℕ) :
    (ShortComplex.mk (homologyMap (bocksteinSC d X).f k) (homologyMap (bocksteinSC d X).g k)
      (by rw [← homologyMap_comp, (bocksteinSC d X).zero, homologyMap_zero])).Exact :=
  (bocksteinSC_shortExact d X).homology_exact₂ k

theorem bockstein_exact₃ [NeZero d] (k : ℕ) :
    (ShortComplex.mk (homologyMap (bocksteinSC d X).g (k + 1)) (bocksteinδ d X k)
      ((bocksteinSC_shortExact d X).comp_δ (k + 1) k rfl)).Exact :=
  (bocksteinSC_shortExact d X).homology_exact₃ (k + 1) k rfl

theorem homologyMap_bockstein_f (k : ℕ) :
    homologyMap (bocksteinSC d X).f k = (d : ℤ) • 𝟙 (singularHomology integerCoefficients X k) := by
  change homologyMap (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).map (mulD d)).app X) k = _
  rw [mulD_eq, CategoryTheory.Functor.map_zsmul, NatTrans.app_zsmul,
    CategoryTheory.Functor.map_id, NatTrans.id_app]
  exact ((homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map_zsmul).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

theorem exists_smul_eq_of_isZero [NeZero d] (k : ℕ) (h : IsZero (singularHomology (modularCoefficients d) X k)) (g : singularHomology integerCoefficients X k) :
    ∃ g' : singularHomology integerCoefficients X k, (d : ℤ) • g' = g := by
  have hepi : Epi (homologyMap (bocksteinSC d X).f k) :=
    (bockstein_exact₂ d X k).epi_f (h.eq_zero_of_tgt _)
  obtain ⟨g', hg'⟩ := (ModuleCat.epi_iff_surjective _).1 hepi g
  refine ⟨g', ?_⟩
  rw [homologyMap_bockstein_f] at hg'
  rw [← hg']
  rfl

end DifferentialGeometry.Topology.SingularPair
