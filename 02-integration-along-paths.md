---
topic: cauchy-integral-formula
type: topic
section: "2"
---
# Integration along paths

The formula is an integral over a curve, so the curve, the integral and the one estimate that will bound it have to be in place first. Every integral in this network is pulled back to an interval by a parametrisation, which is why nothing below the last card here is complex analysis.

## Curves

![[def-piecewise-smooth-path]]

Piecewise is what admits the boundary of a square or a triangle, which a single smooth parametrisation would exclude.

![[def-circle-and-disks]]

![[lem-circle-parametrisation]]

That one lemma carries the derivative and the length together, because every computation later needs both at once.

## The integral

![[def-integral-over-real-interval]]

![[def-path-integral]]

![[def-length-of-path]]

## The only estimate

Two cards, and the first is the one that makes the second possible: for a complex integrand the two sides of the triangle inequality are no longer comparable term by term, and a rotation is what repairs it.

![[lem-modulus-of-integral]]

![[prop-integral-length-bound]]

This converts a bound on an integrand, which continuity supplies, into a bound on an integral, which is what has to be made small. It is the only estimate the argument for the formula uses.
