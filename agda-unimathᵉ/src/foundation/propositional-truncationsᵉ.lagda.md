# Propositional truncations

```agda
module foundation.propositional-truncationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositionsᵉ
open import foundation.truncationsᵉ
open import foundation.universal-property-propositional-truncationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-dependent-functionsᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.sectionsᵉ
open import foundation-core.setsᵉ
open import foundation-core.transport-along-identificationsᵉ
open import foundation-core.truncated-typesᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Weᵉ haveᵉ specifiedᵉ whatᵉ itᵉ meansᵉ to beᵉ aᵉ propositionalᵉ truncationᵉ in theᵉ fileᵉ
`foundation.universal-property-propositional-truncation`.ᵉ Hereᵉ weᵉ useᵉ theᵉ
postulate ofᵉ theᵉ existenceᵉ ofᵉ truncationsᵉ atᵉ allᵉ levels,ᵉ foundᵉ in theᵉ fileᵉ
`foundation.truncations`,ᵉ to showᵉ thatᵉ propositionalᵉ truncationsᵉ exist.ᵉ

## Definition

```agda
type-trunc-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
type-trunc-Propᵉ = type-truncᵉ neg-one-𝕋ᵉ

unit-trunc-Propᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → type-trunc-Propᵉ Aᵉ
unit-trunc-Propᵉ = unit-truncᵉ

is-prop-type-trunc-Propᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-propᵉ (type-trunc-Propᵉ Aᵉ)
is-prop-type-trunc-Propᵉ = is-trunc-type-truncᵉ

all-elements-equal-type-trunc-Propᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → all-elements-equalᵉ (type-trunc-Propᵉ Aᵉ)
all-elements-equal-type-trunc-Propᵉ {lᵉ} {Aᵉ} =
  eq-is-prop'ᵉ (is-prop-type-trunc-Propᵉ {lᵉ} {Aᵉ})

trunc-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Propᵉ lᵉ
trunc-Propᵉ = truncᵉ neg-one-𝕋ᵉ

║_║₋₁ᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
║_║₋₁ᵉ = type-trunc-Propᵉ
```

**Notation.**ᵉ Theᵉ [boxᵉ drawingsᵉ doubleᵉ vertical](https://codepoints.net/U+2551ᵉ)
symbolᵉ `║`ᵉ in theᵉ propositionalᵉ truncationᵉ notationᵉ `║_║₋₁`ᵉ canᵉ beᵉ insertedᵉ with
`agda-input`ᵉ using theᵉ escapeᵉ sequenceᵉ `\--=`ᵉ andᵉ selectingᵉ theᵉ secondᵉ itemᵉ in
theᵉ list.ᵉ

## Properties

### The condition in the induction principle is a property

```agda
abstract
  is-prop-condition-ind-trunc-Prop'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : type-trunc-Propᵉ Aᵉ → UUᵉ l2ᵉ} →
    ( (xᵉ yᵉ : type-trunc-Propᵉ Aᵉ) (uᵉ : Pᵉ xᵉ) (vᵉ : Pᵉ yᵉ) →
      trᵉ Pᵉ (all-elements-equal-type-trunc-Propᵉ xᵉ yᵉ) uᵉ ＝ᵉ vᵉ) →
    (xᵉ : type-trunc-Propᵉ Aᵉ) → is-propᵉ (Pᵉ xᵉ)
  is-prop-condition-ind-trunc-Prop'ᵉ {Pᵉ = Pᵉ} Hᵉ xᵉ =
    is-prop-all-elements-equalᵉ
      ( λ uᵉ vᵉ →
        ( apᵉ
          ( λ γᵉ → trᵉ Pᵉ γᵉ uᵉ)
          ( eq-is-contrᵉ (is-prop-type-trunc-Propᵉ xᵉ xᵉ))) ∙ᵉ
        ( Hᵉ xᵉ xᵉ uᵉ vᵉ))
```

### The induction principle for propositional truncations

```agda
ind-trunc-Prop'ᵉ :
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : type-trunc-Propᵉ Aᵉ → UUᵉ lᵉ)
  (fᵉ : (xᵉ : Aᵉ) → Pᵉ (unit-trunc-Propᵉ xᵉ))
  (Hᵉ :
    (xᵉ yᵉ : type-trunc-Propᵉ Aᵉ) (uᵉ : Pᵉ xᵉ) (vᵉ : Pᵉ yᵉ) →
    trᵉ Pᵉ (all-elements-equal-type-trunc-Propᵉ xᵉ yᵉ) uᵉ ＝ᵉ vᵉ) →
  (xᵉ : type-trunc-Propᵉ Aᵉ) → Pᵉ xᵉ
ind-trunc-Prop'ᵉ Pᵉ fᵉ Hᵉ =
  function-dependent-universal-property-truncᵉ
    ( λ xᵉ → pairᵉ (Pᵉ xᵉ) (is-prop-condition-ind-trunc-Prop'ᵉ Hᵉ xᵉ))
    ( fᵉ)
```

### The propositional induction principle for propositional truncations

```agda
module _
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : type-trunc-Propᵉ Aᵉ → Propᵉ lᵉ)
  where

  abstract
    ind-trunc-Propᵉ :
      ((xᵉ : Aᵉ) → type-Propᵉ (Pᵉ (unit-trunc-Propᵉ xᵉ))) →
      (( yᵉ : type-trunc-Propᵉ Aᵉ) → type-Propᵉ (Pᵉ yᵉ))
    ind-trunc-Propᵉ fᵉ =
      ind-trunc-Prop'ᵉ (type-Propᵉ ∘ᵉ Pᵉ) fᵉ
        ( λ xᵉ yᵉ uᵉ vᵉ → eq-is-propᵉ (is-prop-type-Propᵉ (Pᵉ yᵉ)))

    compute-ind-trunc-Propᵉ :
        is-sectionᵉ (precomp-Πᵉ unit-trunc-Propᵉ (type-Propᵉ ∘ᵉ Pᵉ)) (ind-trunc-Propᵉ)
    compute-ind-trunc-Propᵉ hᵉ =
      eq-is-propᵉ (is-prop-Πᵉ (λ xᵉ → is-prop-type-Propᵉ (Pᵉ (unit-trunc-Propᵉ xᵉ))))
```

### The propositional recursion principle for propositional truncations

```agda
module _
  {lᵉ l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ lᵉ)
  where

  abstract
    rec-trunc-Propᵉ :
      (Aᵉ → type-Propᵉ Pᵉ) → (type-trunc-Propᵉ Aᵉ → type-Propᵉ Pᵉ)
    rec-trunc-Propᵉ = ind-trunc-Propᵉ (λ _ → Pᵉ)

    compute-rec-trunc-Propᵉ :
      is-sectionᵉ (precompᵉ unit-trunc-Propᵉ (type-Propᵉ Pᵉ)) (rec-trunc-Propᵉ)
    compute-rec-trunc-Propᵉ = compute-ind-trunc-Propᵉ (λ _ → Pᵉ)
```

### The defined propositional truncations are propositional truncations

```agda
abstract
  is-propositional-truncation-trunc-Propᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    is-propositional-truncationᵉ (trunc-Propᵉ Aᵉ) unit-trunc-Propᵉ
  is-propositional-truncation-trunc-Propᵉ Aᵉ =
    is-propositional-truncation-extension-propertyᵉ
      ( trunc-Propᵉ Aᵉ)
      ( unit-trunc-Propᵉ)
      ( λ Qᵉ → ind-trunc-Propᵉ (λ xᵉ → Qᵉ))
```

### The defined propositional truncations satisfy the universal property of propositional truncations

```agda
abstract
  universal-property-trunc-Propᵉ :
    {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
    universal-property-propositional-truncationᵉ
      ( trunc-Propᵉ Aᵉ)
      ( unit-trunc-Propᵉ)
  universal-property-trunc-Propᵉ Aᵉ =
    universal-property-is-propositional-truncationᵉ
      ( trunc-Propᵉ Aᵉ)
      ( unit-trunc-Propᵉ)
      ( is-propositional-truncation-trunc-Propᵉ Aᵉ)

abstract
  map-universal-property-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Propᵉ l2ᵉ) →
    (Aᵉ → type-Propᵉ Pᵉ) → type-hom-Propᵉ (trunc-Propᵉ Aᵉ) Pᵉ
  map-universal-property-trunc-Propᵉ {Aᵉ = Aᵉ} Pᵉ fᵉ =
    map-is-propositional-truncationᵉ
      ( trunc-Propᵉ Aᵉ)
      ( unit-trunc-Propᵉ)
      ( is-propositional-truncation-trunc-Propᵉ Aᵉ)
      ( Pᵉ)
      ( fᵉ)

abstract
  apply-universal-property-trunc-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (tᵉ : type-trunc-Propᵉ Aᵉ) (Pᵉ : Propᵉ l2ᵉ) →
    (Aᵉ → type-Propᵉ Pᵉ) → type-Propᵉ Pᵉ
  apply-universal-property-trunc-Propᵉ tᵉ Pᵉ fᵉ =
    map-universal-property-trunc-Propᵉ Pᵉ fᵉ tᵉ

abstract
  apply-twice-universal-property-trunc-Propᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (uᵉ : type-trunc-Propᵉ Aᵉ)
    (vᵉ : type-trunc-Propᵉ Bᵉ) (Pᵉ : Propᵉ l3ᵉ) →
    (Aᵉ → Bᵉ → type-Propᵉ Pᵉ) → type-Propᵉ Pᵉ
  apply-twice-universal-property-trunc-Propᵉ uᵉ vᵉ Pᵉ fᵉ =
    apply-universal-property-trunc-Propᵉ uᵉ Pᵉ
      ( λ xᵉ → apply-universal-property-trunc-Propᵉ vᵉ Pᵉ (fᵉ xᵉ))

abstract
  apply-three-times-universal-property-trunc-Propᵉ :
    {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
    (uᵉ : type-trunc-Propᵉ Aᵉ) (vᵉ : type-trunc-Propᵉ Bᵉ) (wᵉ : type-trunc-Propᵉ Cᵉ) →
    (Pᵉ : Propᵉ l4ᵉ) → (Aᵉ → Bᵉ → Cᵉ → type-Propᵉ Pᵉ) → type-Propᵉ Pᵉ
  apply-three-times-universal-property-trunc-Propᵉ uᵉ vᵉ wᵉ Pᵉ fᵉ =
    apply-universal-property-trunc-Propᵉ uᵉ Pᵉ
      ( λ xᵉ → apply-twice-universal-property-trunc-Propᵉ vᵉ wᵉ Pᵉ (fᵉ xᵉ))
```

### The propositional truncation of a type is `k+1`-truncated

```agda
is-trunc-trunc-Propᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} → is-truncᵉ (succ-𝕋ᵉ kᵉ) (type-trunc-Propᵉ Aᵉ)
is-trunc-trunc-Propᵉ kᵉ = is-trunc-is-propᵉ kᵉ is-prop-type-trunc-Propᵉ

truncated-type-trunc-Propᵉ :
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ lᵉ → Truncated-Typeᵉ lᵉ (succ-𝕋ᵉ kᵉ)
pr1ᵉ (truncated-type-trunc-Propᵉ kᵉ Aᵉ) = type-trunc-Propᵉ Aᵉ
pr2ᵉ (truncated-type-trunc-Propᵉ kᵉ Aᵉ) = is-trunc-trunc-Propᵉ kᵉ

set-trunc-Propᵉ : {lᵉ : Level} → UUᵉ lᵉ → Setᵉ lᵉ
set-trunc-Propᵉ = truncated-type-trunc-Propᵉ neg-one-𝕋ᵉ
```

### A proposition is equivalent to its propositional truncation

```agda
module _
  {lᵉ : Level} (Aᵉ : Propᵉ lᵉ)
  where

  equiv-unit-trunc-Propᵉ : type-Propᵉ Aᵉ ≃ᵉ type-trunc-Propᵉ (type-Propᵉ Aᵉ)
  equiv-unit-trunc-Propᵉ = equiv-unit-truncᵉ Aᵉ
```

### The propositional truncation is idempotent

```agda
module _
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ)
  where

  abstract
    map-idempotent-trunc-Propᵉ :
      type-trunc-Propᵉ (type-trunc-Propᵉ Aᵉ) → type-trunc-Propᵉ Aᵉ
    map-idempotent-trunc-Propᵉ =
      map-universal-property-trunc-Propᵉ (trunc-Propᵉ Aᵉ) idᵉ

  abstract
    is-equiv-map-idempotent-trunc-Propᵉ : is-equivᵉ map-idempotent-trunc-Propᵉ
    is-equiv-map-idempotent-trunc-Propᵉ =
      is-equiv-has-converse-is-propᵉ
        ( is-prop-type-trunc-Propᵉ)
        ( is-prop-type-trunc-Propᵉ)
        ( unit-trunc-Propᵉ)

  idempotent-trunc-Propᵉ :
    type-trunc-Propᵉ (type-trunc-Propᵉ Aᵉ) ≃ᵉ type-trunc-Propᵉ Aᵉ
  pr1ᵉ idempotent-trunc-Propᵉ = map-idempotent-trunc-Propᵉ
  pr2ᵉ idempotent-trunc-Propᵉ = is-equiv-map-idempotent-trunc-Propᵉ

  abstract
    is-equiv-map-inv-idempotent-trunc-Propᵉ :
      is-equivᵉ (unit-trunc-Propᵉ {Aᵉ = type-trunc-Propᵉ Aᵉ})
    is-equiv-map-inv-idempotent-trunc-Propᵉ =
      is-equiv-has-converse-is-propᵉ
        ( is-prop-type-trunc-Propᵉ)
        ( is-prop-type-trunc-Propᵉ)
        ( map-idempotent-trunc-Propᵉ)

  inv-idempotent-trunc-Propᵉ :
    type-trunc-Propᵉ Aᵉ ≃ᵉ type-trunc-Propᵉ (type-trunc-Propᵉ Aᵉ)
  pr1ᵉ inv-idempotent-trunc-Propᵉ = unit-trunc-Propᵉ
  pr2ᵉ inv-idempotent-trunc-Propᵉ = is-equiv-map-inv-idempotent-trunc-Propᵉ
```

### Propositional truncations satisfy the dependent universal property of the propositional truncation

```agda
abstract
  dependent-universal-property-trunc-Propᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
      dependent-universal-property-propositional-truncationᵉ
      ( trunc-Propᵉ Aᵉ)
      ( unit-trunc-Propᵉ)
  dependent-universal-property-trunc-Propᵉ {Aᵉ = Aᵉ} =
    dependent-universal-property-is-propositional-truncationᵉ
      ( trunc-Propᵉ Aᵉ)
      ( unit-trunc-Propᵉ)
      ( is-propositional-truncation-trunc-Propᵉ Aᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : type-trunc-Propᵉ Aᵉ → Propᵉ l2ᵉ)
  where

  equiv-dependent-universal-property-trunc-Propᵉ :
    ((yᵉ : type-trunc-Propᵉ Aᵉ) → type-Propᵉ (Pᵉ yᵉ)) ≃ᵉ
    ((xᵉ : Aᵉ) → type-Propᵉ (Pᵉ (unit-trunc-Propᵉ xᵉ)))
  pr1ᵉ equiv-dependent-universal-property-trunc-Propᵉ =
    precomp-Πᵉ unit-trunc-Propᵉ (type-Propᵉ ∘ᵉ Pᵉ)
  pr2ᵉ equiv-dependent-universal-property-trunc-Propᵉ =
    dependent-universal-property-trunc-Propᵉ Pᵉ

  apply-dependent-universal-property-trunc-Propᵉ :
    (yᵉ : type-trunc-Propᵉ Aᵉ) → ((xᵉ : Aᵉ) → type-Propᵉ (Pᵉ (unit-trunc-Propᵉ xᵉ))) →
    type-Propᵉ (Pᵉ yᵉ)
  apply-dependent-universal-property-trunc-Propᵉ yᵉ fᵉ =
    map-inv-equivᵉ equiv-dependent-universal-property-trunc-Propᵉ fᵉ yᵉ
```

### Propositional truncations distribute over cartesian products

```agda
equiv-product-trunc-Propᵉ :
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (A'ᵉ : UUᵉ l2ᵉ) →
  type-equiv-Propᵉ
    ( trunc-Propᵉ (Aᵉ ×ᵉ A'ᵉ))
    ( product-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ A'ᵉ))
equiv-product-trunc-Propᵉ Aᵉ A'ᵉ =
  pr1ᵉ
    ( centerᵉ
      ( is-uniquely-unique-propositional-truncationᵉ
        ( trunc-Propᵉ (Aᵉ ×ᵉ A'ᵉ))
        ( product-Propᵉ (trunc-Propᵉ Aᵉ) (trunc-Propᵉ A'ᵉ))
        ( unit-trunc-Propᵉ)
        ( map-productᵉ unit-trunc-Propᵉ unit-trunc-Propᵉ)
        ( is-propositional-truncation-trunc-Propᵉ (Aᵉ ×ᵉ A'ᵉ))
        ( is-propositional-truncation-productᵉ
          ( trunc-Propᵉ Aᵉ)
          ( unit-trunc-Propᵉ)
          ( trunc-Propᵉ A'ᵉ)
          ( unit-trunc-Propᵉ)
          ( is-propositional-truncation-trunc-Propᵉ Aᵉ)
          ( is-propositional-truncation-trunc-Propᵉ A'ᵉ))))

map-distributive-trunc-product-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  type-trunc-Propᵉ (Aᵉ ×ᵉ Bᵉ) → type-trunc-Propᵉ Aᵉ ×ᵉ type-trunc-Propᵉ Bᵉ
map-distributive-trunc-product-Propᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} =
  map-universal-property-trunc-Propᵉ
    ( pairᵉ
      ( type-trunc-Propᵉ Aᵉ ×ᵉ type-trunc-Propᵉ Bᵉ)
      ( is-prop-productᵉ is-prop-type-trunc-Propᵉ is-prop-type-trunc-Propᵉ))
    ( map-productᵉ unit-trunc-Propᵉ unit-trunc-Propᵉ)

map-inv-distributive-trunc-product-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  type-trunc-Propᵉ Aᵉ ×ᵉ type-trunc-Propᵉ Bᵉ → type-trunc-Propᵉ (Aᵉ ×ᵉ Bᵉ)
map-inv-distributive-trunc-product-Propᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} tᵉ =
  map-universal-property-trunc-Propᵉ
    ( trunc-Propᵉ (Aᵉ ×ᵉ Bᵉ))
    ( λ xᵉ →
      map-universal-property-trunc-Propᵉ
        ( trunc-Propᵉ (Aᵉ ×ᵉ Bᵉ))
        ( unit-trunc-Propᵉ ∘ᵉ (pairᵉ xᵉ))
        ( pr2ᵉ tᵉ))
    ( pr1ᵉ tᵉ)

abstract
  is-equiv-map-distributive-trunc-product-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-equivᵉ (map-distributive-trunc-product-Propᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
  is-equiv-map-distributive-trunc-product-Propᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-type-trunc-Propᵉ)
      ( is-prop-productᵉ is-prop-type-trunc-Propᵉ is-prop-type-trunc-Propᵉ)
      ( map-inv-distributive-trunc-product-Propᵉ)

distributive-trunc-product-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  type-trunc-Propᵉ (Aᵉ ×ᵉ Bᵉ) ≃ᵉ (type-trunc-Propᵉ Aᵉ ×ᵉ type-trunc-Propᵉ Bᵉ)
pr1ᵉ distributive-trunc-product-Propᵉ = map-distributive-trunc-product-Propᵉ
pr2ᵉ distributive-trunc-product-Propᵉ =
  is-equiv-map-distributive-trunc-product-Propᵉ

abstract
  is-equiv-map-inv-distributive-trunc-product-Propᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
    is-equivᵉ (map-inv-distributive-trunc-product-Propᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ})
  is-equiv-map-inv-distributive-trunc-product-Propᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-productᵉ is-prop-type-trunc-Propᵉ is-prop-type-trunc-Propᵉ)
      ( is-prop-type-trunc-Propᵉ)
      ( map-distributive-trunc-product-Propᵉ)

inv-distributive-trunc-product-Propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  ( type-trunc-Propᵉ Aᵉ ×ᵉ type-trunc-Propᵉ Bᵉ) ≃ᵉ type-trunc-Propᵉ (Aᵉ ×ᵉ Bᵉ)
pr1ᵉ inv-distributive-trunc-product-Propᵉ =
  map-inv-distributive-trunc-product-Propᵉ
pr2ᵉ inv-distributive-trunc-product-Propᵉ =
  is-equiv-map-inv-distributive-trunc-product-Propᵉ
```

### Propositional truncations of coproducts of types with themselves

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} where
  map-trunc-Prop-diagonal-coproductᵉ :
    type-trunc-Propᵉ (Aᵉ +ᵉ Aᵉ) → type-trunc-Propᵉ Aᵉ
  map-trunc-Prop-diagonal-coproductᵉ =
    map-universal-property-trunc-Propᵉ
      ( trunc-Propᵉ Aᵉ)
      ( unit-truncᵉ ∘ᵉ rec-coproductᵉ idᵉ idᵉ)

  map-inv-trunc-Prop-diagonal-coproductᵉ :
    type-trunc-Propᵉ Aᵉ → type-trunc-Propᵉ (Aᵉ +ᵉ Aᵉ)
  map-inv-trunc-Prop-diagonal-coproductᵉ =
    map-universal-property-trunc-Propᵉ
      ( trunc-Propᵉ (Aᵉ +ᵉ Aᵉ))
      ( unit-truncᵉ ∘ᵉ (inlᵉ ∘ᵉ idᵉ))

  abstract
    is-equiv-map-trunc-Prop-diagonal-coproductᵉ :
      is-equivᵉ map-trunc-Prop-diagonal-coproductᵉ
    is-equiv-map-trunc-Prop-diagonal-coproductᵉ =
      is-equiv-has-converse-is-propᵉ
        is-prop-type-trunc-Propᵉ
        is-prop-type-trunc-Propᵉ
        map-inv-trunc-Prop-diagonal-coproductᵉ

    is-equiv-map-inv-trunc-Prop-diagonal-coproductᵉ :
      is-equivᵉ map-inv-trunc-Prop-diagonal-coproductᵉ
    is-equiv-map-inv-trunc-Prop-diagonal-coproductᵉ =
      is-equiv-has-converse-is-propᵉ
        is-prop-type-trunc-Propᵉ
        is-prop-type-trunc-Propᵉ
        map-trunc-Prop-diagonal-coproductᵉ

  equiv-trunc-Prop-diagonal-coproductᵉ :
    type-trunc-Propᵉ (Aᵉ +ᵉ Aᵉ) ≃ᵉ type-trunc-Propᵉ Aᵉ
  pr1ᵉ equiv-trunc-Prop-diagonal-coproductᵉ = map-trunc-Prop-diagonal-coproductᵉ
  pr2ᵉ equiv-trunc-Prop-diagonal-coproductᵉ =
    is-equiv-map-trunc-Prop-diagonal-coproductᵉ

  inv-equiv-trunc-Prop-diagonal-coproductᵉ :
    type-trunc-Propᵉ Aᵉ ≃ᵉ type-trunc-Propᵉ (Aᵉ +ᵉ Aᵉ)
  pr1ᵉ inv-equiv-trunc-Prop-diagonal-coproductᵉ =
    map-inv-trunc-Prop-diagonal-coproductᵉ
  pr2ᵉ inv-equiv-trunc-Prop-diagonal-coproductᵉ =
    is-equiv-map-inv-trunc-Prop-diagonal-coproductᵉ
```

## Table of files about propositional logic

Theᵉ followingᵉ tableᵉ givesᵉ anᵉ overviewᵉ ofᵉ basicᵉ constructionsᵉ in propositionalᵉ
logicᵉ andᵉ relatedᵉ considerations.ᵉ

{{#includeᵉ tables/propositional-logic.mdᵉ}}

## External links

-ᵉ [bracketᵉ type](https://ncatlab.org/nlab/show/bracket+typeᵉ) atᵉ $n$Labᵉ