# Quartic SPR Proof

[简体中文](README.zh-CN.md)

A standalone Lean 4 / mathlib formalization of robust strictly positive-real (SPR) synthesis for real monic quartic interval polynomials.

## What this repository proves

For 4 independent finite closed coefficient intervals, including degenerate intervals, assume that **every denominator in the interval box is strictly Hurwitz** (all roots have negative real part). There exists **one fixed real numerator of exact degree 4**, which is also monic, such that

$$
\mathrm{Re}\left(\frac{b(i\omega)}{a(i\omega)}\right)>0
\quad\text{for every denominator }a\text{ in the box and every }\omega\in\mathbb R.
$$

The same numerator works for the entire box and all real frequencies, including zero. This is an existence theorem, not a numerical synthesis algorithm or a theorem for arbitrary orders.

- Public theorem: [`SPR.N4.Direct.robustSPR`](Lean/Main.lean).
- Exact definitions: [`Lean/SPR/N4/Basic.lean`](Lean/SPR/N4/Basic.lean).
- [Verification notes](VERIFICATION.md).

## Setup and build

Install Git and [elan](https://github.com/leanprover/elan), the Lean toolchain manager, and make sure `elan`, `lean`, and `lake` are on your PATH. The commands below work in a macOS, Linux, or Windows WSL shell and run from the repository root.

```sh
git clone https://github.com/dgjszy/quartic-spr-proof.git
cd quartic-spr-proof
lake exe cache get
lake build
```

`lean-toolchain` pins Lean **4.30.0**; mathlib is pinned to **v4.30.0**, with exact dependency commits in `lake-manifest.json`. The first run needs internet access to download the toolchain, dependencies, and compiled cache. Keep the lockfile; a normal build does not require `lake update`. The cache speeds up dependency builds; Lean checks the project proof sources.

This repository is used as a local proof library. No server or database deployment is needed. The formal build requires neither Python nor an external solver.

## Verify and use

```sh
lake env lean Lean/Verify.lean
lake env lean Lean/Audit.lean
```

The default build includes a transitive axiom audit that permits only `propext`, `Classical.choice`, and `Quot.sound`; any other axiom causes an error.

Within this project's Lean environment:

```lean
import SPR

#check SPR.N4.Direct.robustSPR
#print axioms SPR.N4.Direct.robustSPR
```

## Repository layout

- [`Lean/Main.lean`](Lean/Main.lean): public theorem and final proof assembly.
- [`Lean/SPR.lean`](Lean/SPR.lean): public import entry.
- [`Lean/SPR/N4/`](Lean/SPR/N4/): definitions and quartic proof modules.
- [`Lean/Audit.lean`](Lean/Audit.lean): axiom audit.
- [`Lean/Verify.lean`](Lean/Verify.lean): expanded statement type checks.
