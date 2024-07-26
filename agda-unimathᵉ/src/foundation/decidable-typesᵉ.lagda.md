# Decidable types

```agda
module foundation.decidable-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-negationᵉ
open import foundation.empty-typesᵉ
open import foundation.hilberts-epsilon-operatorsᵉ
open import foundation.negationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.retracts-of-typesᵉ
```

</details>

## Idea

Aᵉ typeᵉ isᵉ saidᵉ to beᵉ **decidable**ᵉ ifᵉ weᵉ canᵉ eitherᵉ constructᵉ anᵉ element,ᵉ orᵉ weᵉ
canᵉ proveᵉ thatᵉ itᵉ isᵉ [empty](foundation-core.empty-types.md).ᵉ Inᵉ otherᵉ words,ᵉ weᵉ
interpretᵉ decidabilityᵉ viaᵉ theᵉ
[Curry-Howardᵉ interpretation](https://en.wikipedia.org/wiki/Curry–Howard_correspondenceᵉ)
ofᵉ logicᵉ intoᵉ typeᵉ theory.ᵉ Aᵉ relatedᵉ conceptᵉ isᵉ thatᵉ aᵉ typeᵉ isᵉ eitherᵉ
[inhabited](foundation.inhabited-types.mdᵉ) orᵉ empty,ᵉ where inhabitednessᵉ ofᵉ aᵉ
typeᵉ isᵉ expressedᵉ using theᵉ
[propositionalᵉ truncation](foundation.propositional-truncations.md).ᵉ

## Definition

### The Curry–Howard interpretation of decidability

```agda
is-decidableᵉ : {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) → UUᵉ lᵉ
is-decidableᵉ Aᵉ = Aᵉ +ᵉ (¬ᵉ Aᵉ)

is-decidable-famᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-decidable-famᵉ {Aᵉ = Aᵉ} Pᵉ = (xᵉ : Aᵉ) → is-decidableᵉ (Pᵉ xᵉ)
```

### The predicate that a type is inhabited or empty

```agda
is-inhabited-or-emptyᵉ : {l1ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l1ᵉ
is-inhabited-or-emptyᵉ Aᵉ = type-trunc-Propᵉ Aᵉ +ᵉ is-emptyᵉ Aᵉ
```

### Merely decidable types

Aᵉ typeᵉ `A`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "merelyᵉ decidable"ᵉ Agda=is-merely-decidableᵉ}} ifᵉ itᵉ comesᵉ equippedᵉ
with anᵉ elementᵉ ofᵉ `║ᵉ is-decidableᵉ Aᵉ ║₋₁`,ᵉ orᵉ equivalently,ᵉ theᵉ
[disjunction](foundation.disjunction.mdᵉ) `Aᵉ ∨ᵉ ¬ᵉ A`ᵉ holds.ᵉ

```agda
is-merely-decidable-Propᵉ :
  {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
is-merely-decidable-Propᵉ Aᵉ = trunc-Propᵉ (is-decidableᵉ Aᵉ)

is-merely-decidableᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
is-merely-decidableᵉ Aᵉ = type-trunc-Propᵉ (is-decidableᵉ Aᵉ)
```

## Examples

### The unit type and the empty type are decidable

```agda
is-decidable-unitᵉ : is-decidableᵉ unitᵉ
is-decidable-unitᵉ = inlᵉ starᵉ

is-decidable-emptyᵉ : is-decidableᵉ emptyᵉ
is-decidable-emptyᵉ = inrᵉ idᵉ
```

## Properties

### Coproducts of decidable types are decidable

```agda
is-decidable-coproductᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ Aᵉ → is-decidableᵉ Bᵉ → is-decidableᵉ (Aᵉ +ᵉ Bᵉ)
is-decidable-coproductᵉ (inlᵉ aᵉ) yᵉ = inlᵉ (inlᵉ aᵉ)
is-decidable-coproductᵉ (inrᵉ naᵉ) (inlᵉ bᵉ) = inlᵉ (inrᵉ bᵉ)
is-decidable-coproductᵉ (inrᵉ naᵉ) (inrᵉ nbᵉ) = inrᵉ (rec-coproductᵉ naᵉ nbᵉ)
```

### Cartesian products of decidable types are decidable

```agda
is-decidable-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ Aᵉ → is-decidableᵉ Bᵉ → is-decidableᵉ (Aᵉ ×ᵉ Bᵉ)
is-decidable-productᵉ (inlᵉ aᵉ) (inlᵉ bᵉ) = inlᵉ (pairᵉ aᵉ bᵉ)
is-decidable-productᵉ (inlᵉ aᵉ) (inrᵉ gᵉ) = inrᵉ (gᵉ ∘ᵉ pr2ᵉ)
is-decidable-productᵉ (inrᵉ fᵉ) (inlᵉ bᵉ) = inrᵉ (fᵉ ∘ᵉ pr1ᵉ)
is-decidable-productᵉ (inrᵉ fᵉ) (inrᵉ gᵉ) = inrᵉ (fᵉ ∘ᵉ pr1ᵉ)

is-decidable-product'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ Aᵉ → (Aᵉ → is-decidableᵉ Bᵉ) → is-decidableᵉ (Aᵉ ×ᵉ Bᵉ)
is-decidable-product'ᵉ (inlᵉ aᵉ) dᵉ with dᵉ aᵉ
... | inlᵉ bᵉ = inlᵉ (pairᵉ aᵉ bᵉ)
... | inrᵉ nbᵉ = inrᵉ (nbᵉ ∘ᵉ pr2ᵉ)
is-decidable-product'ᵉ (inrᵉ naᵉ) dᵉ = inrᵉ (naᵉ ∘ᵉ pr1ᵉ)

is-decidable-left-factorᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ (Aᵉ ×ᵉ Bᵉ) → Bᵉ → is-decidableᵉ Aᵉ
is-decidable-left-factorᵉ (inlᵉ (pairᵉ xᵉ yᵉ)) bᵉ = inlᵉ xᵉ
is-decidable-left-factorᵉ (inrᵉ fᵉ) bᵉ = inrᵉ (λ aᵉ → fᵉ (pairᵉ aᵉ bᵉ))

is-decidable-right-factorᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ (Aᵉ ×ᵉ Bᵉ) → Aᵉ → is-decidableᵉ Bᵉ
is-decidable-right-factorᵉ (inlᵉ (pairᵉ xᵉ yᵉ)) aᵉ = inlᵉ yᵉ
is-decidable-right-factorᵉ (inrᵉ fᵉ) aᵉ = inrᵉ (λ bᵉ → fᵉ (pairᵉ aᵉ bᵉ))
```

### Function types of decidable types are decidable

```agda
is-decidable-function-typeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ Aᵉ → is-decidableᵉ Bᵉ → is-decidableᵉ (Aᵉ → Bᵉ)
is-decidable-function-typeᵉ (inlᵉ aᵉ) (inlᵉ bᵉ) = inlᵉ (λ xᵉ → bᵉ)
is-decidable-function-typeᵉ (inlᵉ aᵉ) (inrᵉ gᵉ) = inrᵉ (λ hᵉ → gᵉ (hᵉ aᵉ))
is-decidable-function-typeᵉ (inrᵉ fᵉ) (inlᵉ bᵉ) = inlᵉ (ex-falsoᵉ ∘ᵉ fᵉ)
is-decidable-function-typeᵉ (inrᵉ fᵉ) (inrᵉ gᵉ) = inlᵉ (ex-falsoᵉ ∘ᵉ fᵉ)

is-decidable-function-type'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-decidableᵉ Aᵉ → (Aᵉ → is-decidableᵉ Bᵉ) → is-decidableᵉ (Aᵉ → Bᵉ)
is-decidable-function-type'ᵉ (inlᵉ aᵉ) dᵉ with dᵉ aᵉ
... | inlᵉ bᵉ = inlᵉ (λ xᵉ → bᵉ)
... | inrᵉ nbᵉ = inrᵉ (λ fᵉ → nbᵉ (fᵉ aᵉ))
is-decidable-function-type'ᵉ (inrᵉ naᵉ) dᵉ = inlᵉ (ex-falsoᵉ ∘ᵉ naᵉ)
```

### The negation of a decidable type is decidable

```agda
is-decidable-negᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-decidableᵉ Aᵉ → is-decidableᵉ (¬ᵉ Aᵉ)
is-decidable-negᵉ dᵉ = is-decidable-function-typeᵉ dᵉ is-decidable-emptyᵉ
```

### Decidable types are closed under coinhabited types; retracts, and equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-decidable-iffᵉ :
    (Aᵉ → Bᵉ) → (Bᵉ → Aᵉ) → is-decidableᵉ Aᵉ → is-decidableᵉ Bᵉ
  is-decidable-iffᵉ fᵉ gᵉ (inlᵉ aᵉ) = inlᵉ (fᵉ aᵉ)
  is-decidable-iffᵉ fᵉ gᵉ (inrᵉ naᵉ) = inrᵉ (λ bᵉ → naᵉ (gᵉ bᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-decidable-retract-ofᵉ :
    Aᵉ retract-ofᵉ Bᵉ → is-decidableᵉ Bᵉ → is-decidableᵉ Aᵉ
  is-decidable-retract-ofᵉ (pairᵉ iᵉ (pairᵉ rᵉ Hᵉ)) (inlᵉ bᵉ) = inlᵉ (rᵉ bᵉ)
  is-decidable-retract-ofᵉ (pairᵉ iᵉ (pairᵉ rᵉ Hᵉ)) (inrᵉ fᵉ) = inrᵉ (fᵉ ∘ᵉ iᵉ)

  is-decidable-is-equivᵉ :
    {fᵉ : Aᵉ → Bᵉ} → is-equivᵉ fᵉ → is-decidableᵉ Bᵉ → is-decidableᵉ Aᵉ
  is-decidable-is-equivᵉ {fᵉ} (pairᵉ (pairᵉ gᵉ Gᵉ) (pairᵉ hᵉ Hᵉ)) =
    is-decidable-retract-ofᵉ (pairᵉ fᵉ (pairᵉ hᵉ Hᵉ))

  is-decidable-equivᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) → is-decidableᵉ Bᵉ → is-decidableᵉ Aᵉ
  is-decidable-equivᵉ eᵉ = is-decidable-iffᵉ (map-inv-equivᵉ eᵉ) (map-equivᵉ eᵉ)

is-decidable-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ) →
  is-decidableᵉ Aᵉ → is-decidableᵉ Bᵉ
is-decidable-equiv'ᵉ eᵉ = is-decidable-equivᵉ (inv-equivᵉ eᵉ)
```

### Decidability implies double negation elimination

```agda
double-negation-elim-is-decidableᵉ :
  {lᵉ : Level} {Pᵉ : UUᵉ lᵉ} → is-decidableᵉ Pᵉ → (¬¬ᵉ Pᵉ → Pᵉ)
double-negation-elim-is-decidableᵉ (inlᵉ xᵉ) pᵉ = xᵉ
double-negation-elim-is-decidableᵉ (inrᵉ xᵉ) pᵉ = ex-falsoᵉ (pᵉ xᵉ)
```

### The double negation of `is-decidable` is always provable

```agda
double-negation-is-decidableᵉ : {lᵉ : Level} {Pᵉ : UUᵉ lᵉ} → ¬¬ᵉ (is-decidableᵉ Pᵉ)
double-negation-is-decidableᵉ {Pᵉ = Pᵉ} fᵉ =
  map-negᵉ (inrᵉ {Aᵉ = Pᵉ} {Bᵉ = ¬ᵉ Pᵉ}) fᵉ (map-negᵉ (inlᵉ {Aᵉ = Pᵉ} {Bᵉ = ¬ᵉ Pᵉ}) fᵉ)
```

### Decidable types have ε-operators

```agda
elim-trunc-Prop-is-decidableᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-decidableᵉ Aᵉ → ε-operator-Hilbertᵉ Aᵉ
elim-trunc-Prop-is-decidableᵉ (inlᵉ aᵉ) xᵉ = aᵉ
elim-trunc-Prop-is-decidableᵉ (inrᵉ fᵉ) xᵉ =
  ex-falsoᵉ (apply-universal-property-trunc-Propᵉ xᵉ empty-Propᵉ fᵉ)
```

### `is-decidable` is an idempotent operation

```agda
idempotent-is-decidableᵉ :
  {lᵉ : Level} (Pᵉ : UUᵉ lᵉ) → is-decidableᵉ (is-decidableᵉ Pᵉ) → is-decidableᵉ Pᵉ
idempotent-is-decidableᵉ Pᵉ (inlᵉ (inlᵉ pᵉ)) = inlᵉ pᵉ
idempotent-is-decidableᵉ Pᵉ (inlᵉ (inrᵉ npᵉ)) = inrᵉ npᵉ
idempotent-is-decidableᵉ Pᵉ (inrᵉ npᵉ) = inrᵉ (λ pᵉ → npᵉ (inlᵉ pᵉ))
```

### Being inhabited or empty is a proposition

```agda
abstract
  is-property-is-inhabited-or-emptyᵉ :
    {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → is-propᵉ (is-inhabited-or-emptyᵉ Aᵉ)
  is-property-is-inhabited-or-emptyᵉ Aᵉ =
    is-prop-coproductᵉ
      ( λ tᵉ → apply-universal-property-trunc-Propᵉ tᵉ empty-Propᵉ)
      ( is-prop-type-trunc-Propᵉ)
      ( is-prop-negᵉ)

is-inhabited-or-empty-Propᵉ : {l1ᵉ : Level} → UUᵉ l1ᵉ → Propᵉ l1ᵉ
pr1ᵉ (is-inhabited-or-empty-Propᵉ Aᵉ) = is-inhabited-or-emptyᵉ Aᵉ
pr2ᵉ (is-inhabited-or-empty-Propᵉ Aᵉ) = is-property-is-inhabited-or-emptyᵉ Aᵉ
```

### Any inhabited type is a fixed point for `is-decidable`

```agda
is-fixed-point-is-decidable-is-inhabitedᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → type-trunc-Propᵉ Xᵉ → is-decidableᵉ Xᵉ ≃ᵉ Xᵉ
is-fixed-point-is-decidable-is-inhabitedᵉ {lᵉ} {Xᵉ} tᵉ =
  right-unit-law-coproduct-is-emptyᵉ Xᵉ (¬ᵉ Xᵉ) (is-nonempty-is-inhabitedᵉ tᵉ)
```

### Raising types converves decidability

```agda
module _
  (lᵉ : Level) {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ)
  where

  is-decidable-raiseᵉ : is-decidableᵉ Aᵉ → is-decidableᵉ (raiseᵉ lᵉ Aᵉ)
  is-decidable-raiseᵉ (inlᵉ pᵉ) = inlᵉ (map-raiseᵉ pᵉ)
  is-decidable-raiseᵉ (inrᵉ npᵉ) = inrᵉ (λ p'ᵉ → npᵉ (map-inv-raiseᵉ p'ᵉ))
```