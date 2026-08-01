---
topic: jordan-curve-theorem
type: topic
section: "4"
---
# Normalization, and five points on a line

The remaining clause — that a bounded piece exists at all — is the hard one, and it is proved by putting the curve in a standard position and then looking at where the vertical axis meets it. This section sets that up; §5 uses it.

## Moving the curve into a box

![[prop-normalizing-similarity]]

Separation is unchanged by a similarity, so the curve may as well be moved first. The farthest pair exists because the curve is [[def-compact|compact]]; sending it to `-1` and `1` fixes the diameter at `2`, and the two distance conditions that follow pin the curve inside `[-1,1] × [-2,2]`.

Everything after this happens inside that rectangle, which is what makes [[thm-crossing-lemma|the crossing lemma]] applicable at all — it is a statement about rectangles.

## Cutting the curve in two

![[prop-arc-decomposition]]

The two ends of the diameter are on the curve, and removing them leaves two pieces. Each is an [[def-arc|arc]] joining `-1` to `1`, and by §3 neither of them separates anything. Whatever separating happens is a consequence of how the two are joined.

## The five points

![[def-maehara-configuration]]

The vertical axis meets each arc — that is already an application of [[thm-crossing-lemma|the crossing lemma]], since each arc runs from the left edge of the rectangle to the right edge. Compactness then supplies the extreme points, and the ordering `q ≤ p < z₀ < m ≤ l` follows.

The point of the construction is `z₀`. It is on the axis, strictly between the lowest point of the northern arc and the highest point of the southern arc below it, and therefore on neither arc: a point of the curve there would contradict the extremality of `m` or of `p`. So `z₀` is off the curve, and the next section shows its component is bounded.
