# Verification and trust boundary

## Pinned environment

- Lean: `leanprover/lean4:v4.33.0-rc1`
- Mathlib: `9944fe2973b8dc0b86949101ed98232c07cd54a0`
- All transitive revisions: committed `lake-manifest.json`

Run `lake exe cache get` and `python3 scripts/verify.py` in a fresh checkout. The GitHub workflow performs the build and then runs the same audit and regression stages. Its current result is visible in the [Actions history](https://github.com/starkbbk/lean-multiset-descent/actions).

## Checks performed

1. `lake build` elaborates the complete library and builds the native executable.
2. `lake env lean Audit.lean` inspects every declaration whose name begins with `Descent`, including definitions with proof terms and generated declarations. It rejects project-defined axioms and dependencies outside `propext`, `Classical.choice`, and `Quot.sound`.
3. The verifier checks that every explicit theorem in all eight source modules appears in the imported audit and the theorem index. This guards against silently leaving a module out of the root import.
4. `lake exe descent-demo` compares the verified executor with an independently implemented FIFO reference simulation, the cost potential, reversed input order, and the empty normal form on 340 finite configurations. It also displays binary costs for ranks 0–8.
5. Three negative controls inject an unfinished theorem, an unfinished proof-valued definition, and a custom axiom into temporary audit inputs. Each must fail for the appropriate reason. Temporary files are removed afterward.

The successful local run inspected **137 project declarations**, including **88 theorem declarations with generated helpers**. The separately checked source inventory contains **60 explicit theorems**. The executable reported all 340 configurations passing. These counts are tied to this source revision; the CI logs report the live audit result.

## What is trusted

The Lean kernel and its implementation, Lean's ordinary foundational axioms, the pinned Mathlib proofs, and the compiler/runtime for executable behavior are within the trust boundary. Formal theorems do not rely on the finite sweep or a native decision procedure. The audit is a dependency check; it does not prove that English documentation perfectly specifies the intended application, nor independently reimplement Lean's kernel.

The native FIFO reference is a finite testing oracle with a 1,000-step guard, not a theorem for all inputs. The main normalizer and transition counter have no fuel parameter. Formal universal results establish their termination and the exact count; finite checks provide additional implementation regression coverage.
