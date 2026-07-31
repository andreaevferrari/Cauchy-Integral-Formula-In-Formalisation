---
topic: cauchy-integral-formula
type: topic
section: "3"
---
# Cauchy's theorem

The central theorem of the subject, and the reason a contour may be moved before it is integrated over. Integration against a holomorphic function does not distinguish between curves that can be deformed into one another — which means a badly placed contour can always be traded for a convenient one.

## Deforming a loop

![[def-homotopic-paths]]

The last of the three conditions is what keeps every intermediate path closed; without it the deformation could open the loop up.

![[lem-homotopy-is-equivalence-relation]]

Transitivity is not decoration. Every argument later chains two deformations, and without it $\sim_G$ would relate ordered pairs rather than group paths.

![[def-contractible-path]]

Contractibility is the case that carries the weight: a loop that can be shrunk to a point inside $G$ encloses nothing that $G$ omits.

## The theorem

![[thm-cauchy]]

This card carries no proof. The source states it and declares a full proof beyond its scope, so it stands here as the largest debt in the network — everything downstream is conditional on it. It is often called the Cauchy–Goursat theorem: the original hypothesis included continuity of the derivative, and removing that is Goursat's contribution.

## The form that gets applied

![[cor-integral-zero-contractible-path]]

One path instead of two, and a conclusion that is a number rather than an equality of integrals. This is the version §5 actually cites.
