---
topic: jordan-curve-theorem
type: topic
section: "2"
---
# Brouwer, and the lemma that does the work

One topological input, and one consequence of it that the rest of the proof calls again and again. After this section no further topology is needed — everything is plane geometry with the crossing lemma as its engine.

## The input

![[thm-brouwer-fixed-point]]

Only the plane case is used, and only for convex compact sets. The route to it is through the disc.

![[thm-no-retraction-of-disc]]

A retraction of the disc onto its boundary would contract the once-around loop inside the circle, and that loop cannot be contracted. Given no retraction, Brouwer for the disc follows: a fixed-point-free self-map would let every point be pushed along the ray from its image to itself, out to the boundary, and that is a retraction. Brouwer for an arbitrary convex compact set follows by nearest-point projection from a disc containing it.

## The engine

![[thm-crossing-lemma]]

This is the form in which Brouwer is actually used. Every subsequent claim about which points lie in which component is established the same way: exhibit a path crossing the rectangle one way, observe that some arc of the curve crosses it the other way, and conclude that they meet — or, when the construction is arranged so that they provably do not meet, conclude that the situation is impossible.

The "transversal" in the name is only about which edges the two paths join. It says nothing about angles, and neither path need be anything but continuous.
