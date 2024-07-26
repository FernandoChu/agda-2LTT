# The field of rational numbers

```agda
module elementary-number-theory.field-of-rational-numbersᵉ where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.discrete-fieldsᵉ

open import elementary-number-theory.multiplicative-group-of-rational-numbersᵉ
open import elementary-number-theory.nonzero-rational-numbersᵉ
open import elementary-number-theory.ring-of-rational-numbersᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ

open import ring-theory.division-ringsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ [rationalᵉ numbers](elementary-number-theory.rational-numbers.mdᵉ)
equippedᵉ with [addition](elementary-number-theory.addition-rational-numbers.mdᵉ)
andᵉ
[multiplication](elementary-number-theory.multiplication-rational-numbers.mdᵉ) isᵉ
aᵉ [discreteᵉ field](commutative-algebra.discrete-fields.md),ᵉ i.e.,ᵉ aᵉ
[commutativeᵉ ring](commutative-algebra.commutative-rings.mdᵉ) whoseᵉ
[nonzero](elementary-number-theory.nonzero-rational-numbers.mdᵉ) elementsᵉ areᵉ
[invertible](ring-theory.invertible-elements-rings.md).ᵉ

## Definitions

### The ring of rational numbers is a division ring

```agda
is-division-ring-ℚᵉ : is-division-Ringᵉ ring-ℚᵉ
pr1ᵉ is-division-ring-ℚᵉ = is-nonzero-one-ℚᵉ ∘ᵉ invᵉ
pr2ᵉ is-division-ring-ℚᵉ xᵉ Hᵉ = is-invertible-element-ring-is-nonzero-ℚᵉ xᵉ (Hᵉ ∘ᵉ invᵉ)
```

### The rational numbers form a discrete field

```agda
is-discrete-field-ℚᵉ : is-discrete-field-Commutative-Ringᵉ commutative-ring-ℚᵉ
is-discrete-field-ℚᵉ = is-division-ring-ℚᵉ
```