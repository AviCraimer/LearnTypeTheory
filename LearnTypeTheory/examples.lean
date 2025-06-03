

/-
Ranta Chapter 4

If John walks he talks.
If Bill walks he talks.

"He can be used for reffering to any man"
"She can be used for reffering to any woman"

Σ (x:Man), x walks

A value of this consists of a pair:
(Bill, Bill walks)

Recall the notation π₁ π₂   for first and second projections of a pair. A dependent pair has these too.

So we can understand the sentence:

"If x walks, he talks"

As a dependent function:

Π (pair: Σ (x:Man)(x walks)), ( π₁(pair) talks )

The pronoun 'he' in the sentence acts as the first projection on the sigma type.

We can further analyze specific cases like "If Bill walks, he talks"

Π (x: Man),[ Π (p: x walks), ( x talks )](Bill)

Actually, we can see by currying that

Π (pair: Σ (x:Man)(x walks)), ( π₁(pair) talks )\

is equivalent to:

Π (x: Man),[ Π (p: x walks), ( x talks )]




-/
