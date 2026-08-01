---
topic: jordan-curve-theorem
type: topic
section: "0"
date: 2026-07-31
tags: [topology, plane-topology, brouwer]
---
# The Jordan curve theorem

A loop in the plane that does not cross itself divides the plane into an inside and an outside — and why that is a theorem rather than an observation.

Draw a closed loop on paper without lifting the pen and without crossing your own line. It has an inside and an outside. Nothing looks less in need of proof.

The trouble is that "a loop that does not cross itself" is a much larger class of objects than the ones a pen draws. It includes curves of infinite length, curves with no tangent at any point, curves that wander into every neighbourhood of every one of their points. For those, the picture is no guide at all, and the statement is not obvious — it is one of the earliest hard theorems of topology, and every known proof is long out of proportion to how the statement reads.

## The result

![[thm-jordan-curve]]

## What is hard about it

Three things have to be produced: a bounded piece, an unbounded piece, and the fact that there is nothing else. The unbounded piece is easy — a curve is [[def-compact|compact]], so it sits inside some disc, and everything far away is connected. The other two are not.

The difficulty is that no hypothesis is available to work with. The curve is continuous and injective and that is all. There is no derivative to integrate, no length to measure, no polygon to approximate with — approximation is exactly what fails, since a nearby polygon can have a completely different inside.

## The route

This account follows Maehara's proof, which reduces everything to one topological input:

![[thm-brouwer-fixed-point]]

From Brouwer comes a lemma about rectangles — two paths crossing a rectangle in transverse directions must meet — and from that lemma, everything else. The proof is remarkable for how little it needs: no homology, no degree theory, no covering spaces beyond the one that establishes Brouwer itself.

## What the network carries

Every statement here has a machine-checked counterpart, and the cards name it in their `lean:` field. There are no proof debts: the argument is complete, and its foundations are the three standard axioms of Lean's logic and nothing else.
