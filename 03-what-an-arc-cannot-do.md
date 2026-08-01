---
topic: jordan-curve-theorem
type: topic
section: "3"
---
# What an arc cannot do

Before the curve can be shown to separate the plane, the thing it is cut into has to be shown not to. This section is the contrast the whole proof is built on, together with the two easy clauses of the separation statement.

## An arc leaves the plane in one piece

![[thm-arc-does-not-separate-plane]]

The proof is [[thm-brouwer-fixed-point|Brouwer]] again, in a different disguise. Suppose the complement of an arc `A` were disconnected. An arc is homeomorphic to an interval, and an interval is an absolute retract, so the identity on `A` extends to a continuous map of the whole plane into `A`. Glue that retraction onto one bounded piece of the complement and the identity onto the rest: the result is a continuous map of a large disc into itself with no fixed point, which cannot exist.

Two ends are what makes this work. A curve with no ends admits no such retraction, and that is the entire difference between an arc and a [[def-jordan-curve|Jordan curve]].

## The far half of the statement

![[thm-unique-unbounded-component]]

This clause needs no geometry: a curve is [[def-compact|compact]], so it sits inside a disc, and the complement of that disc is [[def-connected|connected]] and unbounded. Every unbounded component has to meet it, so there is exactly one.

## The curve is the whole boundary

![[thm-component-boundary-is-curve]]

Once the complement is known to be disconnected, no proper part of the curve can be doing the separating: if some point of the curve were not on the boundary of a component, that boundary would fit inside a proper sub-[[def-arc|arc]], and the previous result would reconnect the complement.
