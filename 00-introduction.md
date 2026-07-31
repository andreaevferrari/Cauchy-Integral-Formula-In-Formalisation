---
topic: cauchy-integral-formula
type: topic
section: "0"
date: 2026-07-31
tags: [complex-analysis, contour-integration]
---
# The Cauchy Integral Formula

How the values of a holomorphic function on a closed curve determine its values everywhere inside, and why one hand-computed integral is the whole reason.

Take a smooth real function on a disc and write down its values on the boundary circle. You have written down almost nothing: push a bump up in the middle, flatten it before the edge, and the boundary is unmoved. The interior is free.

Ask the same of a complex-differentiable function and the answer inverts. The boundary values determine the function at every interior point, and they determine it by an explicit formula with a fixed kernel that knows nothing about the function. Everything that makes complex analysis unlike the real theory it appears to generalise descends from this.

## The result

![[thm-cauchy-integral-formula]]

## The mechanism

One integral is computed by hand — $\frac{1}{z-w}$ around a circle centred at $w$ — and its value is $2\pi i$ no matter how small the circle. That independence of the radius is the entire mechanism. Cauchy's theorem says a contour may be deformed without changing the integral of a holomorphic function, so the integral over a large circle may be evaluated over an arbitrarily small one; on a small circle the function is nearly constant, and a constant is exactly what the hand computation handles. The factor $\frac{1}{2\pi i}$ is not a choice: it undoes that one integral.

The general contour is reached from the circle by deformation, which is where plane topology enters and where this account takes on its debts.

## What it buys

Differentiating the formula under the integral sign costs nothing — the kernel is smooth in $w$ — so a function differentiable once is differentiable infinitely often, a statement with no real-variable analogue. Expanding the kernel as a geometric series makes every holomorphic function locally a power series. Letting the radius grow in the formula for the derivative of a bounded entire function forces that derivative to vanish, which is Liouville's theorem and with it a short proof that every non-constant polynomial has a root.

## What is established here

Three cards carry no proof: Cauchy's theorem itself, which the source states and declares beyond its scope [[ref-beck]], together with the two facts of plane topology that the deformation argument needs. Everything else is proved line by line, and what §5 establishes is a complete reduction of the general formula to the case of a circle.
