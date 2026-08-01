---
topic: jordan-curve-theorem
type: topic
section: "5"
---
# The two steps

Everything is in place: a curve in a rectangle, cut into two arcs that each cross it from side to side, and a point `z₀` on the vertical axis that is off the curve. Two claims remain, and both are proved the same way — by building a path across the rectangle that provably misses one of the arcs, which [[thm-crossing-lemma|the crossing lemma]] says is impossible.

## Step A — something is enclosed

![[thm-exists-bounded-component]]

Suppose the component of `z₀` were unbounded. Then some path leaves `z₀` and escapes the rectangle, and it has a first exit point on the boundary — above the axis or below it.

Say below. Now concatenate five pieces: along the bottom boundary of the rectangle to the exit point, back along the escaping path to `z₀`, up the axis to `m`, on up to `l`, and out to the top edge. Every piece avoids the southern arc — the first because it runs along a boundary path built to avoid it, the second because it stays in the component of `z₀`, the last three because they lie on the axis above `p`, which is the highest point of the southern arc down there.

The result runs from the bottom edge of the rectangle to the top edge and misses the southern arc entirely. But the southern arc runs from the left edge to the right edge. They must cross, and they do not.

The case where the escape happens above the axis is the same argument reflected, missing the northern arc instead.

## Step B — nothing else is

![[thm-bounded-component-unique]]

The same construction, run against an arbitrary bounded component: it too must contain `z₀`, or a bottom-to-top path missing one of the arcs appears again. So there is only one bounded component.

## The theorem

![[thm-jordan-curve]]

Three facts assembled: exactly one unbounded component (§3), at least one bounded component (Step A), at most one (Step B). Two in total, with the curve as the boundary of each.

What the argument used, in the end, was one fixed point theorem and the observation that two paths crossing a rectangle in transverse directions have to meet.
