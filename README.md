# Manuscripts and Lean proofs

Prepared by Erfan Oliaei · Independent researcher · Edition 8 · 26 November 2026

Ten manuscripts in mathematics, quantum information, and mathematical physics with matching LaTeX sources, Lean 4 formalizations, and verification logs.

## Citing qubit universality

Erfan Oliaei (2026), *Every finite joint measurability structure is realizable on one qubit*, Zenodo, 25 November 2026. [Archived version DOI](https://doi.org/10.5281/zenodo.24528781) · [All versions DOI](https://doi.org/10.5281/zenodo.24528780).

The repository PDF contains a later manuscript revision and links to the archived version.

## What Lean proves

| Manuscript | Formal result | Scope of the paper proof |
| --- | --- | --- |
| [Minimal compatibility-threshold tests for noiseless quantum codes](papers/three-binary-measurements.pdf) · [TeX](papers/three-binary-measurements.tex) | The two lifted commutators imply an actual diagonal block decomposition. The third-setting averaging equations then force the matrix to be \(I\otimes H\), including the unpaired line. Lean also checks the plane-parameter separation, explicit mixing weights, slack identities and the extraction of a noiseless code from an invertible lifted factor. | The manuscript verifies the hypotheses for its two explicit measurement families, assembles the supporting-functional argument and applies the CHSH obstruction to arbitrary binary pairs. |
| [A common parent for all noisy qutrit measurements](papers/qutrit-common-parent.pdf) · [TeX](papers/qutrit-common-parent.tex) | Lean computes the gate bias and every power coefficient directly from the finite angular and radial moment sums. It proves the higher coefficients vanish, identifies the resulting real polynomial, and proves its Bernstein bound, endpoint, thinning probability, visibility and gap. | The probabilistic response, Haar law and derivation of the finite moment formula are on paper. The two rational Python checks provide independent routes from the formulas. Renner's qubit parent is an external input. |
| [The exact loss threshold for two displaced on–off detectors](papers/optical-detector-threshold.pdf) · [TeX](papers/optical-detector-threshold.tex) | The Hilbert-space necessity and equality steps, the coherent cross ratio after the environmental overlap cancels, the normalized binary parent for the cutoff expansion with its stochastic response, and the estimate giving the constant 36. | The optical loss isometry, its action on Fock space, and the cutoff operator-norm estimate leading to the finite expansion are identified on paper. |
| [Finite-copy quantum lists](papers/finite-copy-quantum-lists.pdf) · [TeX](papers/finite-copy-quantum-lists.tex) | **The main if-and-only-if criterion** on an ordinary positive number of copies, with complex positive-semidefinite matrices and an actual normalized finite POVM. The proof includes the signed expansion, activation and a basis equivalence preserving Born probabilities. A separable trace obstruction is also checked. | The numerical bound on the number of copies, LOCC classification, and the separation examples are on paper. |
| [Qubit compatibility universality](papers/qubit-universality.pdf) · [TeX](papers/qubit-universality.tex) | **The main realization theorem** for every finite simplicial complex by genuine complex two-by-two POVMs. The library also proves the merged compatibility criterion, rational entries and the nonzero-outcome bound. For the noise witness it checks the selected Gram and frame inequalities and the sum of normalized traces over parent events with arbitrary intersections. Retaining a nonzero effect gives strictly positive normalized trace. | The application to the depolarized family, the complete independent-perturbation parent and the fixed-alphabet count are assembled on paper. |
| [Optimal pure-state exclusion](papers/pure-state-exclusion.pdf) · [TeX](papers/pure-state-exclusion.tex) | The constrained-frame extension for any finite set of continuous orthogonality constraints smaller than the complex dimension, and the final phase cancellation. The trace upper bound uses a genuine complex unitary change of basis and two Cauchy–Schwarz inequalities. Scalar spectral tests and witness normalization are also checked. | The assembly of those frame extensions with the SDP rank argument, full-rank perturbation of the minimizer, matrix differentiation and the final spectral formula are on paper. |
| [Regular-graph coupon collector](papers/graph-coupon-collector.pdf) · [TeX](papers/graph-coupon-collector.tex) | Poisson-tail inequalities, the product barrier for the specified backward system, neighborhood rigidity, and differentiation of the first-removal convolution into that backward differential equation. | The marked-clock probability law, equality characterization and expected-time gap are on paper. |
| [Lossy qubit measurements](papers/lossy-qubit-threshold.pdf) · [TeX](papers/lossy-qubit-threshold.tex) | Hermitian Bloch representation, branch capacity, the exact two-setting region, the uniform finite-menu clipping estimate including rank-one branches, and the minimax and Carathéodory step yielding at most N+1 generating efficiencies. | The spherical law, evaluation and maximization of the scalar integral, directional gap and geometric estimates for the finite-menu rates are on paper. |
| [Spin Wigner negativity](papers/spin-wigner-negativity.pdf) · [TeX](papers/spin-wigner-negativity.tex) | Existence of the continuous logarithm on a simply connected, locally path-connected space and its explicit local formula through the smooth logarithm near 1. The library also checks open negativity under the stated hypotheses and converts absolute overlap to a negative-volume bound. | The spin orbit, Wigner identities and spherical-harmonic overlap estimate are on paper. |
| [Uniform Carleman truncation](papers/uniform-carleman-truncation.pdf) · [TeX](papers/uniform-carleman-truncation.tex) | Marked-divisor separation, tree counting, the inverse-divisor product, uniqueness of the finite linear ODE on each forward interval, and the exact Riccati truncation error. | Analytic conjugacy, control of the flow coefficients and the general uniform estimate are on paper. |

## Reproduce the checks

All 36 proof modules passed separate kernel replays. The build and kernel reports apply to the same Lean sources and pinned dependencies in this distribution. Paths to compiled objects in the distributed object inventory are relative to the project root. Their compiled objects contain 808 declarations, including 582 theorem entries and 16 compiler-generated partial recursion helpers. The inventory flags those helpers with RUNTIME. Lean uses them for execution and skips them in its stock kernel replay. A separate audit traced the types and proof bodies of all 792 logical project declarations. Every partial or unsafe declaration was unreachable from those roots. The audit replayed all 59,958 reachable constants into an empty environment using the pinned Lean kernel and checked their presence afterward.

The project pins Lean 4.34.0-rc2 and Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`. Use a fresh checkout with Elan, Git and Python 3.11 or later. Python uses only its standard library.

```sh
lake exe cache get
python verification/replay.py
python certificates/check_qutrit.py
python certificates/check_direct_integral.py
```

The audit runs `lake build`, verifies the nine dependency revisions and their working trees, and fresh-imports the library. It prints the axiom dependencies of 100 named statements. An inventory matches all project declarations, including private and generated helpers, to the names in the compiled objects. Each proof-bearing module is then replayed by a separate invocation of the toolchain's `leanchecker`. The entry-point module has imports only. The last check traverses the actual types and proof bodies and replays their combined mathematical dependency closure into an empty Lean kernel environment. The audit driver and inspection files are outside the mathematical import graph. An optional `--fresh-imports` additionally asks the stock checker to replay the whole imported environment, including unrelated declarations.

| Evidence | File |
| --- | --- |
| Fresh source build and pinned dependencies | [Build](verification/build.txt) · [Dependency status](verification/dependencies.txt) · [Toolchain fingerprints](verification/toolchain.txt) |
| Human-selected theorem interfaces and printed axioms | [Interfaces](verification/interfaces.txt) · [Axioms](verification/axioms.txt) |
| All local declarations and source imports | [Inventory](verification/inventory.tsv) · [Object names](verification/object-names.tsv) · [Source hashes and imports](verification/source-imports.tsv) |
| Kernel replay | [Per-module results](verification/kernel-replay.tsv) · [Mathematical dependency closure](verification/kernel-closure.txt) |
| Qutrit supplement | [Finite moments in Lean](ManuscriptProofs/QutritMoments.lean) · [Bernstein proof in Lean](ManuscriptProofs/QutritCertificate.lean) · [Moment calculation](certificates/check_qutrit.py) · [Direct Haar integration](certificates/check_direct_integral.py) · [Exact outputs](verification/qutrit-checks.txt) |
| PDF checks | [Build and render results by manuscript](verification/pdf-checks.tsv) |

Each proof runs in Lean's standard classical foundation. The mathematical baseline includes the calculus of inductive constructions, its primitive inductive and quotient mechanisms, and the allowed axiom declarations `propext`, `Classical.choice` and `Quot.sound`. A kernel replay checks a formal statement against these foundations. The table above identifies the mathematical steps covered by each statement and its remaining paper-level inputs. Checksums for the release files are listed in [SHA256SUMS](SHA256SUMS).
