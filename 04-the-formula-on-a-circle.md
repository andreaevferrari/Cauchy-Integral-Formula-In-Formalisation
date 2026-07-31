---
topic: cauchy-integral-formula
type: topic
section: "4"
---
# The formula on a circle

Everything the subject is famous for is already here, in the case where the contour is a circle centred at the point being evaluated. The general case, in §5, adds topology but no analysis.

## The one integral computed by hand

![[lem-circle-integral-inverse]]

Two features matter. The answer is not zero, unlike the integral of a function with an antiderivative around a loop. And the answer does not depend on the radius: every circle around $w$ feels the singularity equally, so shrinking the circle is free.

## The formula

![[thm-cauchy-integral-formula-circle]]

The mechanism is worth separating from the computation. Cauchy's theorem makes the integral the same on every circle about $w$, so it may be evaluated in the limit of small circles; on a small circle the function is nearly constant, and a constant is exactly what the hand computation above handles. Holomorphy enters only through that first step — the remainder of the proof uses nothing beyond continuity at the single point $w$.

Read the right-hand side and notice what appears in it: the values of $f$ on the circle, and the point $w$. Nothing else.

## The same statement, unparametrised

![[cor-mean-value-property-holomorphic]]

No weighting and no correction term: a holomorphic function equals its plain average over every circle centred where it is evaluated. Split into real and imaginary parts this is the mean value property of harmonic functions, which is the shortest bridge from this subject to potential theory.
