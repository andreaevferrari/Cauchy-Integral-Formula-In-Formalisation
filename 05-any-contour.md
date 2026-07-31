---
topic: cauchy-integral-formula
type: topic
section: "5"
---
# Any contour

Replace the circle by an arbitrary simple closed curve going counter-clockwise around $w$. The argument is the one from §4 with the deformation doing more work: shrink the contour onto a small circle about $w$, staying inside the contour and away from $w$, then apply the circle case.

Making that sentence mean anything costs two facts about the plane, and both are harder than they look. Neither is proved here.

## What "inside" means

![[thm-jordan-curve]]

![[def-inside-of-path]]

![[def-positively-oriented-path]]

Orientation is not a detail: reversing it replaces the value of the integral by its negative, so a formula giving $f(w)$ for one orientation gives $-f(w)$ for the other.

## The deformation

![[thm-annulus-homotopy]]

Insisting the homotopy stays in the annulus is the whole point. The integrand is holomorphic only away from $w$, so a deformation sweeping across $w$ would be worthless.

## Trading the hypothesis

The natural hypothesis is "the region contains the inside of the contour", which is not something one checks. It can be traded for contractibility, which is.

![[prop-interior-in-region-iff-contractible]]

The direction that does the work runs backwards through the usual traffic: a holomorphic function, $\frac{1}{z-w}$, is used to prove a statement of plane topology. It detects a puncture that no argument about connectedness was going to see.

## The formula

![[thm-cauchy-integral-formula]]

What this card establishes is the reduction of the general formula to the circle case, and that reduction is complete. What it stands on — Cauchy's theorem and the two topological facts above — is exactly the network's three unproved cards.
