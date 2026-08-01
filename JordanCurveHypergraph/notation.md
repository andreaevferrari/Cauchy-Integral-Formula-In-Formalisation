---
type: notation
---

# Notation

Every symbol this network uses, with the card that defines it. The table is
normative: one name and one symbol per concept, registered here when the card
is written.

A row with a plain-text term and a card links that term to that card
everywhere it appears in the pool, which is how a word like `arc` gets linked
at all: the automatic rule refuses single words, because linking every
occurrence of a common noun sends the reader somewhere it did not mean. Here
a person has decided, so it can.

Rows whose term is a formula are for reading only. Prose does not contain
formulas, and a link inside `$…$` renders as brackets.

**Written by hand.** Nothing generates this table.

## The cast — role letters

Recurring roles have fixed letters, pool-wide.

| Letter | Role |
|---|---|
| $J$ | the Jordan curve under study; $J_N$, $J_S$ its northern and southern arcs |
| $A$ | an arc — a curve with two ends, when it is not one of $J_N$, $J_S$ |
| $U$ | a connected component of the complement $\mathbb{C} \setminus J$ |
| $z$, $w$ | points of the plane |
| $l$, $m$, $p$, $q$ | the four distinguished points on the vertical axis, from highest to lowest |
| $z_0$ | the midpoint of $m$ and $p$ — the point shown to lie in a bounded component |
| $r$ | the parametrisation $S^1 \to \mathbb{C}$ whose image is $J$ |
| $R$ | the normalized rectangle $[-1,1] \times [-2,2]$ |
| $h$, $v$ | the horizontal and vertical paths of the crossing lemma |
| $\rho$ | a retraction |

## The table — notation with its defining card

| Notation | Meaning | Card |
|---|---|---|
| $\mathbb{C}$ | the plane, in its two readings — a field, and $\mathbb{R}^2$ | [[def-complex-numbers]] |
| $\lvert \cdot \rvert$, $\operatorname{Re}$, $\operatorname{Im}$ | modulus, real part, imaginary part | [[def-modulus-and-parts]] |
| $S^1$ | the unit circle, the domain of the parametrisation | [[def-jordan-curve]] |
| $C[a,r]$, $D[a,r]$, $\overline{D}[a,r]$ | circle, open disk, closed disk of centre $a$ and radius $r$ | [[def-circle-and-disks]] |
| Jordan curve | the image of a continuous injection $S^1 \to \mathbb{C}$ | [[def-jordan-curve]] |
| arc | a subset of the plane homeomorphic to $[0,1]$ | [[def-arc]] |
| open | every point has a disk around it inside the set | [[def-open-set]] |
| connected | not a union of two disjoint non-empty relatively open pieces | [[def-connected]] |
| connected component | a maximal connected subset | [[def-connected]] |
| compact | every open cover has a finite subcover | [[def-compact]] |
| continuous | the limit at each point is the value there | [[def-continuity]] |
| $\lim$ | a limit in $\mathbb{C}$ | [[def-limit-in-c]] |
| configuration | the four axis points and their midpoint, for a normalized curve | [[def-maehara-configuration]] |
| $\partial U$ | the boundary of a component | [[thm-component-boundary-is-curve]] |

## The floor

Nothing about the plane is a primitive here: every notion in the table above
has a card, down to $\mathbb{C}$ itself. What this network does not define is
the mathematics that is not its subject.

| Taken from | Used for |
|---|---|
| $\mathbb{R}$, its order and completeness | the coordinates of $\mathbb{C}$, and every $\varepsilon$–$\delta$ argument |
| sets, functions, finiteness | throughout |
| homeomorphism, path-connectedness, the unit interval | the shapes `arc` and `Jordan curve` are defined by |
| convexity, and the nearest-point projection onto a convex compact set | carrying [[thm-brouwer-fixed-point]] from the disk to a general convex compact set |
| covering spaces, for the covering $\mathbb{R} \to \mathbb{R}/\mathbb{Z}$ alone | [[thm-no-retraction-of-disc]] |

## Typography

Not mathematics — marks that structure a proof.

| Mark | Use |
|---|---|
| $\Rightarrow$, $\Leftarrow$ | the two directions of an equivalence, as proof headings |
| $\square$ | end of proof |
