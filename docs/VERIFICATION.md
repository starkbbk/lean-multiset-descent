# Verification and trust boundary

## Pinned environment

- Lean: `leanprover/lean4:v4.33.0-rc1`
- Mathlib: `9944fe2973b8dc0b86949101ed98232c07cd54a0`
- All transitive revisions: committed `lake-manifest.json`

Run `lake exe cache get` and `python3 scripts/verify.py` in a fresh checkout. The GitHub workflow performs the build and then runs the same audit and regression stages. Its current result is visible in the [Actions history](https://github.com/starkbbk/lean-multiset-descent/actions).

## Checks performed

1. `lake build` elaborates the complete library and builds the native executable.
2. `lake env lean Audit.lean` inspects every declaration whose name begins with `Descent`, including definitions with proof terms, instances, and generated declarations. It rejects project-defined axioms and dependencies outside `propext`, `Classical.choice`, and `Quot.sound`.
3. The verifier checks that every explicit theorem in all twelve source modules appears in the imported audit, resolving nested namespaces. It also checks that `docs/THEOREMS.md` is exactly the index generated from the sources (`--write-index` regenerates it). This guards against silently leaving a module out of the root import or publishing stale counts.
4. `lake exe descent-demo` compares the verified worklist executor with an independently implemented FIFO reference simulation, the cost potential, reversed input order, and the empty normal form on 340 finite configurations. It also displays binary costs for ranks 0–8.
5. The same executable runs ten Kirby–Paris battles. For each, the direct move counter and the generic normalizer must agree and the final hydra must be the bare root. The verifier parses each printed hydra and recomputes its battle length with an independent Python implementation of the strategy.
6. The executable computes Goodstein lengths for starts 0–3, checking that each is the first zero and that the next stages stay at zero, and prints ten-stage prefixes from 4 and 5. The verifier recomputes all of them with an independent Python implementation, which reads hereditary notation digit by digit from the least significant end instead of by leading terms.
7. The verifier runs the demo twice and requires identical output.
8. Three negative controls inject an unfinished theorem, an unfinished proof-valued definition, and a custom axiom into temporary audit inputs. Each must fail for the appropriate reason. Temporary files are removed afterward.

The successful local run inspected **461 project declarations**, including **271 theorem declarations with generated helpers**. The separately checked source inventory contains **135 explicit theorems**. The executable reported all 340 configurations, all ten battles, and all Goodstein checks passing. These counts are tied to this source revision; the CI logs report the live audit result.

## What is trusted

The Lean kernel and its implementation, Lean's ordinary foundational axioms, the pinned Mathlib proofs, and the compiler/runtime for executable behavior are within the trust boundary. Formal theorems do not rely on the finite sweep, the battle samples, the Goodstein samples, or a native decision procedure. The audit is a dependency check; it does not prove that English documentation perfectly specifies the intended application, nor independently reimplement Lean's kernel.

The native FIFO reference is a finite testing oracle with a 1,000-step guard. The Python battle model has a one-million-move guard, and the Python Goodstein model a 1,000-stage guard. None of them is a theorem for all inputs. The main normalizers, transition counter, battle counter, and Goodstein search have no fuel parameter. Formal universal results establish their termination, the exact worklist count, the legality of every computed battle, and the first-zero property of every Goodstein length; finite checks provide additional implementation regression coverage.
