# References for the declared axioms

Each `axiom` in `SphereSixComplex/` says what it stands for. Most name a classical result, and this
file resolves the citation keys used in those docstrings; the rest are boundaries specific to this
construction, listed at the end, and those name no source because there is none to name. Keys follow the source paper's bibliography where the
paper cites the same result, so a reader can check the two against each other.

`./scripts/axiom_inventory.py` lists every axiom with its location; `./scripts/check-axioms.sh`
enforces which of them the theorems actually depend on.

Numbered citations refer to the editions listed below -- in particular `[Hat02]` numbering is that
of the 2002 Cambridge edition, which is the one freely available from the author's page. Where a
result is standard but not stated as a numbered theorem in the cited source, the citation names the
section instead.

| Key | Reference |
| --- | --- |
| `[Bea83]` | A. F. Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer, 1983. |
| `[BHPV]` | W. Barth, K. Hulek, C. Peters, A. Van de Ven, *Compact Complex Surfaces*, 2nd ed., Ergeb. Math. Grenzgeb. (3) 4, Springer, 2004. |
| `[Ful93]` | W. Fulton, *Introduction to Toric Varieties*, Annals of Mathematics Studies 131, Princeton University Press, 1993. |
| `[GrRe]` | H. Grauert, R. Remmert, *Coherent Analytic Sheaves*, Grundlehren math. Wiss. 265, Springer, 1984. |
| `[Hat02]` | A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002. |
| `[KKMS]` | G. Kempf, F. Knudsen, D. Mumford, B. Saint-Donat, *Toroidal Embeddings I*, Lecture Notes in Mathematics 339, Springer, 1973. |
| `[KM63]` | M. Kervaire, J. Milnor, Groups of homotopy spheres I, *Ann. of Math.* (2) **77** (1963), 504–537. |
| `[Kod64]` | K. Kodaira, On the structure of compact complex analytic surfaces I, *Amer. J. Math.* **86** (1964), 751–798; II, ibid. **88** (1966), 682–721. |
| `[Mil65]` | J. Milnor, *Lectures on the h-Cobordism Theorem*, Princeton University Press, 1965. |
| `[Mum72]` | D. Mumford, An analytic construction of degenerating abelian varieties over complete rings, *Compositio Math.* **24** (1972), 239–272. |
| `[Oda88]` | T. Oda, *Convex Bodies and Algebraic Geometry*, Ergeb. Math. Grenzgeb. (3) 15, Springer, 1988. |
| `[Orl72]` | P. Orlik, *Seifert Manifolds*, Lecture Notes in Mathematics 291, Springer, 1972. |
| `[Sma61]` | S. Smale, Generalized Poincaré's conjecture in dimensions greater than four, *Ann. of Math.* (2) **74** (1961), 391–406. |
| `[Wang49]` | H.-C. Wang, The homology groups of the fibre bundles over a sphere, *Duke Math. J.* **16** (1949), 33–38. |

## Axioms that are not classical citations

Some declared boundaries are statements about *this construction* rather than results that can be
cited. They are marked as such in their own docstrings, and are listed here so the distinction is
not lost:

- `establishedActualAffineFillingCoverSquares` — the three regular cover squares of the star (§7.5).
- `centralFamilyBundleRealization`, `collarBundleRealization` — the torus-bundle realizations (§6–7).
- `establishedStandardA2ToricCentralFiberCWDecomposition` and
  `establishedStandardA2ToricCentralFiberCellularIncidence` — the CW decomposition of the `A₂`
  central fibre and its attaching data (§7.3). The orbit-cone correspondence gives the torus-orbit
  stratification but not cells: a positive-dimensional orbit is `(C*)^k`. Its consequences are checked against the paper: the recorded cell counts and
  incidences reproduce `H_*(W) = (Z, Z², Z⁴, Z², Z)` and `e(W) = 2`, which is the paper's
  Proposition 7.11.
- `EstablishedActualCuspRadialClutching.data`, `establishedActualCuspCentralNaturality`,
  `EstablishedStandardA2CuspSpecialization.degreeOne` / `degreeTwo` — the cusp collar's radial
  fundamental domain and its specialization maps (§4, §7.3).
- `polarHoneycombPhaseSpreadingPackage` — the honeycomb package chosen compatibly with the frozen
  deck action and the phase-spreading data (§4).
- `establishedPuncturedGlobalFamilyEquivariantUniversalCover` — the equivariant universal cover of
  the punctured global family (§7.5).
