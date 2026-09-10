module

public import SphereSixComplex.Prerequisites.Topology.StandardFourTorusHomologicalModel
public import SphereSixComplex.Paper.Topology.PaperEllipticTorusHomologyBasisProof

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex

namespace EstablishedFiniteCWTopology

open Geometry Geometry.ComplexTorus Geometry.EllipticFamilySpecialization
open SphereSixComplex.Periods

/-- A full-rank complex two-torus has the four-torus homological model, proved from its explicit
homeomorphism with the iterated identity mapping torus. -/
public noncomputable def additiveTorusFourTorusHomologicalModel
    (p : Parameters) (h : FullRank p) : FourTorusHomologicalModel (AdditiveTorus p) where
  homologyEquiv k :=
    (integralSingularHomologyEquiv k
      (StandardTorusHomology.additiveTorusStdHomeomorph p h)).trans
        (StandardTorusHomology.stdTorusHomology 4 k)

public theorem additiveTorus_integralHomologyFiniteSix (p : Parameters) (h : FullRank p) :
    IntegralHomologyFiniteSix (AdditiveTorus p) :=
  (additiveTorusFourTorusHomologicalModel p h).integralHomologyFiniteSix

public theorem additiveTorus_subsingleton_homology_five (p : Parameters) (h : FullRank p) :
    Subsingleton (IntegralSingularHomology 5 (AdditiveTorus p)) :=
  (additiveTorusFourTorusHomologicalModel p h).subsingleton_homology_five

public theorem additiveTorus_subsingleton_homology_six (p : Parameters) (h : FullRank p) :
    Subsingleton (IntegralSingularHomology 6 (AdditiveTorus p)) :=
  (additiveTorusFourTorusHomologicalModel p h).subsingleton_homology_six

public theorem additiveTorus_euler_eq_zero (p : Parameters) (h : FullRank p) :
    integralHomologyEulerCharacteristicSix (AdditiveTorus p) = 0 :=
  (additiveTorusFourTorusHomologicalModel p h).euler_eq_zero

end EstablishedFiniteCWTopology

end SphereSixComplex

end

end
