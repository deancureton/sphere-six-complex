# Canonical topology vendor

Pinned source: `4ca15d0de4c41f22bccc635a15178dfac88336bf`, historical project path `canonical-topology/Poincare/`, restored from the Git object in the integration repository. The commit author is Ayush Khaitan <ak5556@della9.princeton.edu>. The original project is licensed under Apache-2.0; see LICENSE and the preserved upstream provenance, including the plby/HopfProblem derivative-homotopy attribution.

The active source keeps existing DifferentialGeometry declaration namespaces while living entirely below this vendor directory. Newly added native theorems stay in their mathematical topic directories and import this API. Mixed source files were split by declaration.

The unchanged pinned project is archived at `upstream/source-4ca15d0de.tar.gz`, with its original source and documentation. `SOURCE_MAP.json` records hashes, original and former paths, native extensions and every reconciliation patch. `MODIFICATIONS.md` describes local changes. Historical integration records remain in `../CanonicalTopologyProvenance/`.

Run `python3 DifferentialGeometry/External/CanonicalTopology/migrate.py --check` to verify this migration snapshot. `--apply` restores mapped sources and updates recorded consumers only after checking their pre-migration or post-migration hashes. It does not write build caches.
