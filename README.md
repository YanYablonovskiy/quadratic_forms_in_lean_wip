# Lean Quadratic Forms Project

Formalization of the theory of quadratic forms, their isometries, hyperbolic planes, Witt cancellation, and the construction of the Witt ring in Lean 4.

## Project Structure
- `Basic.lean`: Core definitions of quadratic forms and basic operations.
- `Constructors.lean`: Constructors for quadratic forms.
- `Examples.lean`: Concrete worked-out examples.
- `Isometry.lean`: Isometry relations and equivalence.
- `HilbertSymbol.lean`: Definition of the Hilbert norm residue symbol and its properties.
- `Hyperbolic.lean`: Definition of the hyperbolic plane and hyperbolic forms.
- `LocalTheory.lean`: Quadratic forms over local fields.
- `LocalGlobalHassePrinciple.lean`: Hasse–Minkowski theorem and related Hasse principles.
- `Invariants.lean`: Discriminants and Hasse invariants.

## Setup

```bash
lake build
```

Requires [Lean 4](https://leanprover-community.github.io/get_started.html) and [Mathlib4](https://github.com/leanprover-community/mathlib4).


## Refernces
- Cassels, "Rational Quadratic Forms", https://archive.org/details/rationalquadrati0000cass/page/n5/mode/2up