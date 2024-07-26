# Null families of types

```agda
module orthogonal-factorization-systems.null-families-of-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.propositionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.null-typesᵉ
open import orthogonal-factorization-systems.orthogonal-mapsᵉ
```

</details>

## Idea

Aᵉ familyᵉ ofᵉ typesᵉ `Bᵉ : Aᵉ → UUᵉ l`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "null"ᵉ Disambiguation="familyᵉ ofᵉ types"ᵉ Agda=is-null-familyᵉ}} atᵉ `Y`,ᵉ
orᵉ **`Y`-null**,ᵉ ifᵉ everyᵉ fiberᵉ is.ᵉ I.e.,ᵉ ifᵉ theᵉ
[diagonalᵉ map](foundation.diagonal-maps-of-types.mdᵉ)

```text
  Δᵉ : Bᵉ xᵉ → (Yᵉ → Bᵉ xᵉ)
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ everyᵉ `x`ᵉ in `A`.ᵉ

## Definitions

### `Y`-null families of types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Yᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} (Bᵉ : Aᵉ → UUᵉ l3ᵉ)
  where

  is-null-familyᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-null-familyᵉ = (xᵉ : Aᵉ) → is-nullᵉ Yᵉ (Bᵉ xᵉ)

  is-property-is-null-familyᵉ : is-propᵉ is-null-familyᵉ
  is-property-is-null-familyᵉ =
    is-prop-Πᵉ (λ xᵉ → is-prop-is-nullᵉ Yᵉ (Bᵉ xᵉ))

  is-null-family-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  is-null-family-Propᵉ = (is-null-familyᵉ ,ᵉ is-property-is-null-familyᵉ)
```

## Properties

### Closure under equivalences

Ifᵉ `C`ᵉ isᵉ `Y`-nullᵉ andᵉ weᵉ haveᵉ equivalencesᵉ `Xᵉ ≃ᵉ Y`ᵉ andᵉ `(xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Cᵉ x`,ᵉ
thenᵉ `B`ᵉ isᵉ `X`-null.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : Aᵉ → UUᵉ l4ᵉ}
  where

  is-null-family-equivᵉ :
    {l5ᵉ : Level} {Cᵉ : Aᵉ → UUᵉ l5ᵉ} →
    Xᵉ ≃ᵉ Yᵉ → ((xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ) →
    is-null-familyᵉ Yᵉ Cᵉ → is-null-familyᵉ Xᵉ Bᵉ
  is-null-family-equivᵉ eᵉ fᵉ Hᵉ xᵉ = is-null-equivᵉ eᵉ (fᵉ xᵉ) (Hᵉ xᵉ)

  is-null-family-equiv-exponentᵉ :
    (eᵉ : Xᵉ ≃ᵉ Yᵉ) → is-null-familyᵉ Yᵉ Bᵉ → is-null-familyᵉ Xᵉ Bᵉ
  is-null-family-equiv-exponentᵉ eᵉ Hᵉ xᵉ = is-null-equiv-exponentᵉ eᵉ (Hᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Yᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ} {Cᵉ : Aᵉ → UUᵉ l4ᵉ}
  where

  is-null-family-equiv-familyᵉ :
    ((xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ) → is-null-familyᵉ Yᵉ Cᵉ → is-null-familyᵉ Yᵉ Bᵉ
  is-null-family-equiv-familyᵉ fᵉ Hᵉ xᵉ = is-null-equiv-baseᵉ (fᵉ xᵉ) (Hᵉ xᵉ)
```

### Closure under retracts

Ifᵉ `C`ᵉ isᵉ `Y`-nullᵉ andᵉ `X`ᵉ isᵉ aᵉ retractᵉ ofᵉ `Y`ᵉ andᵉ `Bᵉ x`ᵉ isᵉ aᵉ retractᵉ ofᵉ `Cᵉ x`ᵉ
forᵉ allᵉ `x`,ᵉ thenᵉ `B`ᵉ isᵉ `X`-null.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level}
  {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : Aᵉ → UUᵉ l4ᵉ} {Cᵉ : Aᵉ → UUᵉ l5ᵉ}
  where

  is-null-family-retractᵉ :
    Xᵉ retract-ofᵉ Yᵉ → ((xᵉ : Aᵉ) → (Bᵉ xᵉ) retract-ofᵉ (Cᵉ xᵉ)) →
    is-null-familyᵉ Yᵉ Cᵉ → is-null-familyᵉ Xᵉ Bᵉ
  is-null-family-retractᵉ eᵉ fᵉ Hᵉ xᵉ = is-null-retractᵉ eᵉ (fᵉ xᵉ) (Hᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Yᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ} {Cᵉ : Aᵉ → UUᵉ l4ᵉ}
  where

  is-null-family-retract-familyᵉ :
    ((xᵉ : Aᵉ) → (Bᵉ xᵉ) retract-ofᵉ (Cᵉ xᵉ)) → is-null-familyᵉ Yᵉ Cᵉ → is-null-familyᵉ Yᵉ Bᵉ
  is-null-family-retract-familyᵉ fᵉ Hᵉ xᵉ = is-null-retract-baseᵉ (fᵉ xᵉ) (Hᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} {Bᵉ : Aᵉ → UUᵉ l4ᵉ}
  where

  is-null-family-retract-exponentᵉ :
    Xᵉ retract-ofᵉ Yᵉ → is-null-familyᵉ Yᵉ Bᵉ → is-null-familyᵉ Xᵉ Bᵉ
  is-null-family-retract-exponentᵉ eᵉ Hᵉ xᵉ = is-null-retract-exponentᵉ eᵉ (Hᵉ xᵉ)
```

## See also

-ᵉ Inᵉ [`null-maps`](orthogonal-factorization-systems.null-maps.mdᵉ) weᵉ showᵉ thatᵉ aᵉ
  typeᵉ familyᵉ isᵉ `Y`-nullᵉ ifᵉ andᵉ onlyᵉ ifᵉ itsᵉ totalᵉ spaceᵉ projectionᵉ is.ᵉ