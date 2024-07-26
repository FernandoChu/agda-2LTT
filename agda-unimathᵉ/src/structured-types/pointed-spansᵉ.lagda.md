# Pointed spans

```agda
module structured-types.pointed-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.spansᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [pointedᵉ types](structured-types.pointed-types.mdᵉ) `A`ᵉ andᵉ `B`.ᵉ Aᵉ
{{#conceptᵉ "(binaryᵉ) pointedᵉ span"ᵉ Agda=pointed-spanᵉ}} fromᵉ `A`ᵉ to `B`ᵉ consistsᵉ
ofᵉ aᵉ
{{#conceptᵉ "spanningᵉ pointedᵉ type"ᵉ Disambiguation="binaryᵉ pointedᵉ span"ᵉ Agda=spanning-pointed-type-pointed-spanᵉ}}
`S`ᵉ andᵉ aᵉ [pair](foundation.dependent-pair-types.mdᵉ) ofᵉ
[pointedᵉ maps](structured-types.pointed-maps.mdᵉ) `fᵉ : Sᵉ →∗ᵉ A`ᵉ andᵉ `gᵉ : Sᵉ →∗ᵉ B`.ᵉ
Theᵉ pointedᵉ typesᵉ `A`ᵉ andᵉ `B`ᵉ in theᵉ specificationᵉ ofᵉ aᵉ binaryᵉ spanᵉ ofᵉ pointedᵉ
typesᵉ areᵉ alsoᵉ referredᵉ to asᵉ theᵉ
{{#conceptᵉ "domain"ᵉ Disambiguation="binaryᵉ pointedᵉ span"ᵉ}} andᵉ
{{#conceptᵉ "codomain"ᵉ Disambiguation="binaryᵉ pointedᵉ span"ᵉ}} ofᵉ theᵉ pointedᵉ
span,ᵉ respectively.ᵉ

## Definitions

### (Binary) pointed spans

```agda
pointed-spanᵉ :
  {l1ᵉ l2ᵉ : Level} (lᵉ : Level) (Aᵉ : Pointed-Typeᵉ l1ᵉ) (Bᵉ : Pointed-Typeᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc lᵉ)
pointed-spanᵉ lᵉ Aᵉ Bᵉ = Σᵉ (Pointed-Typeᵉ lᵉ) (λ Sᵉ → (Sᵉ →∗ᵉ Aᵉ) ×ᵉ (Sᵉ →∗ᵉ Bᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  (𝒮ᵉ : pointed-spanᵉ l3ᵉ Aᵉ Bᵉ)
  where

  spanning-pointed-type-pointed-spanᵉ : Pointed-Typeᵉ l3ᵉ
  spanning-pointed-type-pointed-spanᵉ = pr1ᵉ 𝒮ᵉ

  spanning-type-pointed-spanᵉ : UUᵉ l3ᵉ
  spanning-type-pointed-spanᵉ =
    type-Pointed-Typeᵉ spanning-pointed-type-pointed-spanᵉ

  point-spanning-type-pointed-spanᵉ : spanning-type-pointed-spanᵉ
  point-spanning-type-pointed-spanᵉ =
    point-Pointed-Typeᵉ spanning-pointed-type-pointed-spanᵉ

  left-pointed-map-pointed-spanᵉ :
    spanning-pointed-type-pointed-spanᵉ →∗ᵉ Aᵉ
  left-pointed-map-pointed-spanᵉ = pr1ᵉ (pr2ᵉ 𝒮ᵉ)

  left-map-pointed-spanᵉ :
    spanning-type-pointed-spanᵉ → type-Pointed-Typeᵉ Aᵉ
  left-map-pointed-spanᵉ =
    map-pointed-mapᵉ left-pointed-map-pointed-spanᵉ

  preserves-point-left-map-pointed-spanᵉ :
    left-map-pointed-spanᵉ point-spanning-type-pointed-spanᵉ ＝ᵉ
    point-Pointed-Typeᵉ Aᵉ
  preserves-point-left-map-pointed-spanᵉ =
    preserves-point-pointed-mapᵉ left-pointed-map-pointed-spanᵉ

  right-pointed-map-pointed-spanᵉ :
    spanning-pointed-type-pointed-spanᵉ →∗ᵉ Bᵉ
  right-pointed-map-pointed-spanᵉ = pr2ᵉ (pr2ᵉ 𝒮ᵉ)

  right-map-pointed-spanᵉ :
    spanning-type-pointed-spanᵉ → type-Pointed-Typeᵉ Bᵉ
  right-map-pointed-spanᵉ =
    map-pointed-mapᵉ right-pointed-map-pointed-spanᵉ

  preserves-point-right-map-pointed-spanᵉ :
    right-map-pointed-spanᵉ point-spanning-type-pointed-spanᵉ ＝ᵉ
    point-Pointed-Typeᵉ Bᵉ
  preserves-point-right-map-pointed-spanᵉ =
    preserves-point-pointed-mapᵉ right-pointed-map-pointed-spanᵉ

  span-pointed-spanᵉ : spanᵉ l3ᵉ (type-Pointed-Typeᵉ Aᵉ) (type-Pointed-Typeᵉ Bᵉ)
  pr1ᵉ span-pointed-spanᵉ = spanning-type-pointed-spanᵉ
  pr1ᵉ (pr2ᵉ span-pointed-spanᵉ) = left-map-pointed-spanᵉ
  pr2ᵉ (pr2ᵉ span-pointed-spanᵉ) = right-map-pointed-spanᵉ
```

### Identity pointed spans

```agda
module _
  {l1ᵉ : Level} {Xᵉ : Pointed-Typeᵉ l1ᵉ}
  where

  id-pointed-spanᵉ : pointed-spanᵉ l1ᵉ Xᵉ Xᵉ
  pr1ᵉ id-pointed-spanᵉ = Xᵉ
  pr1ᵉ (pr2ᵉ id-pointed-spanᵉ) = id-pointed-mapᵉ
  pr2ᵉ (pr2ᵉ id-pointed-spanᵉ) = id-pointed-mapᵉ
```

## See also

-ᵉ [Oppositeᵉ pointedᵉ spans](structured-types.opposite-pointed-spans.mdᵉ)
-ᵉ [Pointedᵉ spanᵉ diagrams](structured-types.pointed-span-diagrams.mdᵉ)
-ᵉ [Spans](foundation.spans.mdᵉ)