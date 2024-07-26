# Set truncations

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.set-truncationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.equality-coproduct-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.mere-equalityᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.sliceᵉ
open import foundation.surjective-mapsᵉ
open import foundation.truncationsᵉ
open import foundation.uniqueness-set-truncationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universal-property-set-truncationᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Idea

Theᵉ {{#conceptᵉ "setᵉ truncation"ᵉ Agda=trunc-Setᵉ}} ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ mapᵉ
`ηᵉ : Aᵉ → trunc-Setᵉ A`ᵉ thatᵉ satisfiesᵉ
[theᵉ universalᵉ propertyᵉ ofᵉ setᵉ truncations](foundation.universal-property-set-truncation.md).ᵉ

## Definitions

```agda
trunc-Setᵉ : {lᵉ : Level} → UUᵉ lᵉ → Setᵉ lᵉ
trunc-Setᵉ = truncᵉ zero-𝕋ᵉ

type-trunc-Setᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
type-trunc-Setᵉ = type-truncᵉ zero-𝕋ᵉ

is-set-type-trunc-Setᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-setᵉ (type-trunc-Setᵉ Aᵉ)
is-set-type-trunc-Setᵉ = is-trunc-type-truncᵉ

unit-trunc-Setᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → type-trunc-Setᵉ Aᵉ
unit-trunc-Setᵉ = unit-truncᵉ

is-set-truncation-trunc-Setᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → is-set-truncationᵉ (trunc-Setᵉ Aᵉ) unit-trunc-Setᵉ
is-set-truncation-trunc-Setᵉ Aᵉ = is-truncation-truncᵉ

║_║₀ᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
║_║₀ᵉ = type-trunc-Setᵉ
```

**Notation.**ᵉ Theᵉ [boxᵉ drawingsᵉ doubleᵉ vertical](https://codepoints.net/U+2551ᵉ)
symbolᵉ `║`ᵉ in theᵉ setᵉ truncationᵉ notationᵉ `║_║₀`ᵉ canᵉ beᵉ insertedᵉ with
`agda-input`ᵉ using theᵉ escapeᵉ sequenceᵉ `\--=`ᵉ andᵉ selectingᵉ theᵉ secondᵉ itemᵉ in
theᵉ list.ᵉ

## Properties

### The dependent universal property of set truncations

```agda
dependent-universal-property-trunc-Setᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  dependent-universal-property-set-truncationᵉ (trunc-Setᵉ Aᵉ) unit-trunc-Setᵉ
dependent-universal-property-trunc-Setᵉ = dependent-universal-property-truncᵉ

equiv-dependent-universal-property-trunc-Setᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : type-trunc-Setᵉ Aᵉ → Setᵉ l2ᵉ) →
  ((xᵉ : type-trunc-Setᵉ Aᵉ) → type-Setᵉ (Bᵉ xᵉ)) ≃ᵉ
  ((aᵉ : Aᵉ) → type-Setᵉ (Bᵉ (unit-trunc-Setᵉ aᵉ)))
equiv-dependent-universal-property-trunc-Setᵉ =
  equiv-dependent-universal-property-truncᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : type-trunc-Setᵉ Aᵉ → Setᵉ l2ᵉ)
  (fᵉ : (xᵉ : Aᵉ) → type-Setᵉ (Bᵉ (unit-trunc-Setᵉ xᵉ)))
  where

  Π-trunc-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Π-trunc-Setᵉ =
    Σᵉ ( (xᵉ : type-trunc-Setᵉ Aᵉ) → type-Setᵉ (Bᵉ xᵉ))
      ( λ gᵉ → gᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ fᵉ)

  function-dependent-universal-property-trunc-Setᵉ :
    (xᵉ : type-trunc-Setᵉ Aᵉ) → type-Setᵉ (Bᵉ xᵉ)
  function-dependent-universal-property-trunc-Setᵉ =
    function-dependent-universal-property-truncᵉ Bᵉ fᵉ

  compute-dependent-universal-property-trunc-Setᵉ :
    function-dependent-universal-property-trunc-Setᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ fᵉ
  compute-dependent-universal-property-trunc-Setᵉ =
    htpy-dependent-universal-property-truncᵉ Bᵉ fᵉ

  apply-dependent-universal-property-trunc-Set'ᵉ :
    (xᵉ : type-trunc-Setᵉ Aᵉ) → type-Setᵉ (Bᵉ xᵉ)
  apply-dependent-universal-property-trunc-Set'ᵉ =
    map-inv-equivᵉ (equiv-dependent-universal-property-trunc-Setᵉ Bᵉ) fᵉ
```

### The universal property of set truncations

```agda
universal-property-trunc-Setᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  universal-property-set-truncationᵉ (trunc-Setᵉ Aᵉ) (unit-trunc-Setᵉ)
universal-property-trunc-Setᵉ Aᵉ = universal-property-truncᵉ zero-𝕋ᵉ Aᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ)
  where

  equiv-universal-property-trunc-Setᵉ :
    (type-trunc-Setᵉ Aᵉ → type-Setᵉ Bᵉ) ≃ᵉ (Aᵉ → type-Setᵉ Bᵉ)
  equiv-universal-property-trunc-Setᵉ = equiv-universal-property-truncᵉ Aᵉ Bᵉ

  apply-universal-property-trunc-Setᵉ :
    (tᵉ : type-trunc-Setᵉ Aᵉ) → (Aᵉ → type-Setᵉ Bᵉ) → type-Setᵉ Bᵉ
  apply-universal-property-trunc-Setᵉ tᵉ fᵉ = map-universal-property-truncᵉ Bᵉ fᵉ tᵉ

  map-universal-property-trunc-Setᵉ :
    (Aᵉ → type-Setᵉ Bᵉ) → hom-Setᵉ (trunc-Setᵉ Aᵉ) Bᵉ
  map-universal-property-trunc-Setᵉ = map-universal-property-truncᵉ Bᵉ

  triangle-universal-property-trunc-Setᵉ :
    (fᵉ : Aᵉ → type-Setᵉ Bᵉ) →
    map-universal-property-trunc-Setᵉ fᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ fᵉ
  triangle-universal-property-trunc-Setᵉ = triangle-universal-property-truncᵉ Bᵉ
  Map-trunc-Setᵉ : (fᵉ : Aᵉ → type-Setᵉ Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  Map-trunc-Setᵉ fᵉ =
    Σᵉ (type-trunc-Setᵉ Aᵉ → type-Setᵉ Bᵉ) (λ gᵉ → gᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ fᵉ)

apply-universal-property-trunc-Set'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (tᵉ : type-trunc-Setᵉ Aᵉ) (Bᵉ : Setᵉ l2ᵉ) →
  (Aᵉ → type-Setᵉ Bᵉ) → type-Setᵉ Bᵉ
apply-universal-property-trunc-Set'ᵉ tᵉ Bᵉ fᵉ =
  map-universal-property-trunc-Setᵉ Bᵉ fᵉ tᵉ
```

### The set truncation of `X` is the set quotient by the mere equality relation

```agda
reflecting-map-mere-eq-unit-trunc-Setᵉ :
  {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) →
  reflecting-map-equivalence-relationᵉ
    ( mere-eq-equivalence-relationᵉ Aᵉ)
    ( type-trunc-Setᵉ Aᵉ)
reflecting-map-mere-eq-unit-trunc-Setᵉ Aᵉ =
  pairᵉ unit-trunc-Setᵉ (reflects-mere-eqᵉ (trunc-Setᵉ Aᵉ) unit-trunc-Setᵉ)

abstract
  is-set-quotient-trunc-Setᵉ :
    {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
    is-set-quotientᵉ
      ( mere-eq-equivalence-relationᵉ Aᵉ)
      ( trunc-Setᵉ Aᵉ)
      ( reflecting-map-mere-eq-unit-trunc-Setᵉ Aᵉ)
  is-set-quotient-trunc-Setᵉ Aᵉ =
    is-set-quotient-is-set-truncationᵉ
      ( trunc-Setᵉ Aᵉ)
      ( unit-trunc-Setᵉ)
      ( λ {lᵉ} → is-set-truncation-trunc-Setᵉ Aᵉ)

module _
  {lᵉ : Level}
  where

  abstract
    is-surjective-and-effective-unit-trunc-Setᵉ :
      (Aᵉ : UUᵉ lᵉ) →
      is-surjective-and-effectiveᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( unit-trunc-Setᵉ)
    is-surjective-and-effective-unit-trunc-Setᵉ Aᵉ =
      is-surjective-and-effective-is-set-quotientᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( trunc-Setᵉ Aᵉ)
        ( unit-trunc-Setᵉ ,ᵉ
          reflects-mere-eqᵉ (trunc-Setᵉ Aᵉ) unit-trunc-Setᵉ)
        ( λ {lᵉ} → is-set-quotient-trunc-Setᵉ Aᵉ)

  abstract
    is-surjective-unit-trunc-Setᵉ :
      (Aᵉ : UUᵉ lᵉ) → is-surjectiveᵉ (unit-trunc-Setᵉ {Aᵉ = Aᵉ})
    is-surjective-unit-trunc-Setᵉ Aᵉ =
      pr1ᵉ (is-surjective-and-effective-unit-trunc-Setᵉ Aᵉ)

  abstract
    is-effective-unit-trunc-Setᵉ :
      (Aᵉ : UUᵉ lᵉ) →
      is-effectiveᵉ (mere-eq-equivalence-relationᵉ Aᵉ) (unit-trunc-Setᵉ {Aᵉ = Aᵉ})
    is-effective-unit-trunc-Setᵉ Aᵉ =
      pr2ᵉ (is-surjective-and-effective-unit-trunc-Setᵉ Aᵉ)

  abstract
    apply-effectiveness-unit-trunc-Setᵉ :
      {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} → unit-trunc-Setᵉ xᵉ ＝ᵉ unit-trunc-Setᵉ yᵉ → mere-eqᵉ xᵉ yᵉ
    apply-effectiveness-unit-trunc-Setᵉ {Aᵉ = Aᵉ} {xᵉ} {yᵉ} =
      map-equivᵉ (is-effective-unit-trunc-Setᵉ Aᵉ xᵉ yᵉ)

  abstract
    apply-effectiveness-unit-trunc-Set'ᵉ :
      {Aᵉ : UUᵉ lᵉ} {xᵉ yᵉ : Aᵉ} → mere-eqᵉ xᵉ yᵉ → unit-trunc-Setᵉ xᵉ ＝ᵉ unit-trunc-Setᵉ yᵉ
    apply-effectiveness-unit-trunc-Set'ᵉ {Aᵉ = Aᵉ} {xᵉ} {yᵉ} =
      map-inv-equivᵉ (is-effective-unit-trunc-Setᵉ Aᵉ xᵉ yᵉ)

  emb-trunc-Setᵉ : (Aᵉ : UUᵉ lᵉ) → type-trunc-Setᵉ Aᵉ ↪ᵉ (Aᵉ → Propᵉ lᵉ)
  emb-trunc-Setᵉ Aᵉ =
    emb-is-surjective-and-effectiveᵉ
      ( mere-eq-equivalence-relationᵉ Aᵉ)
      ( trunc-Setᵉ Aᵉ)
      ( unit-trunc-Setᵉ)
      ( is-surjective-and-effective-unit-trunc-Setᵉ Aᵉ)

  hom-slice-trunc-Setᵉ :
    (Aᵉ : UUᵉ lᵉ) → hom-sliceᵉ (mere-eq-Propᵉ {Aᵉ = Aᵉ}) (map-embᵉ (emb-trunc-Setᵉ Aᵉ))
  pr1ᵉ (hom-slice-trunc-Setᵉ Aᵉ) = unit-trunc-Setᵉ
  pr2ᵉ (hom-slice-trunc-Setᵉ Aᵉ) =
    triangle-emb-is-surjective-and-effectiveᵉ
      ( mere-eq-equivalence-relationᵉ Aᵉ)
      ( trunc-Setᵉ Aᵉ)
      ( unit-trunc-Setᵉ)
      ( is-surjective-and-effective-unit-trunc-Setᵉ Aᵉ)

  abstract
    is-image-trunc-Setᵉ :
      (Aᵉ : UUᵉ lᵉ) →
      is-imageᵉ
        ( mere-eq-Propᵉ {Aᵉ = Aᵉ})
        ( emb-trunc-Setᵉ Aᵉ)
        ( hom-slice-trunc-Setᵉ Aᵉ)
    is-image-trunc-Setᵉ Aᵉ =
      is-image-is-surjective-and-effectiveᵉ
        ( mere-eq-equivalence-relationᵉ Aᵉ)
        ( trunc-Setᵉ Aᵉ)
        ( unit-trunc-Setᵉ)
        ( is-surjective-and-effective-unit-trunc-Setᵉ Aᵉ)
```

### Uniqueness of `trunc-Set`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  {hᵉ : hom-Setᵉ Bᵉ (trunc-Setᵉ Aᵉ)} (Hᵉ : hᵉ ∘ᵉ fᵉ ~ᵉ unit-trunc-Setᵉ)
  where

  abstract
    is-equiv-is-set-truncation'ᵉ : is-set-truncationᵉ Bᵉ fᵉ → is-equivᵉ hᵉ
    is-equiv-is-set-truncation'ᵉ Sfᵉ =
      is-equiv-is-set-truncation-is-set-truncationᵉ
        ( Bᵉ)
        ( fᵉ)
        ( trunc-Setᵉ Aᵉ)
        ( unit-trunc-Setᵉ)
        ( Hᵉ)
        ( Sfᵉ)
        ( λ {hᵉ} → is-set-truncation-trunc-Setᵉ Aᵉ)

  abstract
    is-set-truncation-is-equiv'ᵉ :
      is-equivᵉ hᵉ → is-set-truncationᵉ Bᵉ fᵉ
    is-set-truncation-is-equiv'ᵉ Ehᵉ =
      is-set-truncation-is-equiv-is-set-truncationᵉ
        ( Bᵉ)
        ( fᵉ)
        ( trunc-Setᵉ Aᵉ)
        ( unit-trunc-Setᵉ)
        ( Hᵉ)
        ( λ {lᵉ} → is-set-truncation-trunc-Setᵉ Aᵉ)
        ( Ehᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  {hᵉ : hom-Setᵉ (trunc-Setᵉ Aᵉ) Bᵉ} (Hᵉ : hᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ fᵉ)
  where

  abstract
    is-equiv-is-set-truncationᵉ : is-set-truncationᵉ Bᵉ fᵉ → is-equivᵉ hᵉ
    is-equiv-is-set-truncationᵉ Sfᵉ =
      is-equiv-is-set-truncation-is-set-truncationᵉ
        ( trunc-Setᵉ Aᵉ)
        ( unit-trunc-Setᵉ)
        ( Bᵉ)
        ( fᵉ)
        ( Hᵉ)
        ( λ {lᵉ} → is-set-truncation-trunc-Setᵉ Aᵉ)
        ( Sfᵉ)

  abstract
    is-set-truncation-is-equivᵉ :
      is-equivᵉ hᵉ → is-set-truncationᵉ Bᵉ fᵉ
    is-set-truncation-is-equivᵉ Ehᵉ =
      is-set-truncation-is-set-truncation-is-equivᵉ
        ( trunc-Setᵉ Aᵉ)
        ( unit-trunc-Setᵉ)
        ( Bᵉ)
        ( fᵉ)
        ( Hᵉ)
        ( Ehᵉ)
        ( λ {lᵉ} → is-set-truncation-trunc-Setᵉ Aᵉ)

is-equiv-unit-trunc-Setᵉ :
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) → is-equivᵉ (unit-trunc-Setᵉ {Aᵉ = type-Setᵉ Aᵉ})
is-equiv-unit-trunc-Setᵉ = is-equiv-unit-truncᵉ

equiv-unit-trunc-Setᵉ :
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ) → type-Setᵉ Aᵉ ≃ᵉ type-trunc-Setᵉ (type-Setᵉ Aᵉ)
equiv-unit-trunc-Setᵉ = equiv-unit-truncᵉ

equiv-unit-trunc-empty-Setᵉ : emptyᵉ ≃ᵉ type-trunc-Setᵉ emptyᵉ
equiv-unit-trunc-empty-Setᵉ = equiv-unit-trunc-Setᵉ empty-Setᵉ

abstract
  is-empty-trunc-Setᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-emptyᵉ Aᵉ → is-emptyᵉ (type-trunc-Setᵉ Aᵉ)
  is-empty-trunc-Setᵉ fᵉ xᵉ = apply-universal-property-trunc-Set'ᵉ xᵉ empty-Setᵉ fᵉ

abstract
  is-empty-is-empty-trunc-Setᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-emptyᵉ (type-trunc-Setᵉ Aᵉ) → is-emptyᵉ Aᵉ
  is-empty-is-empty-trunc-Setᵉ fᵉ = fᵉ ∘ᵉ unit-trunc-Setᵉ

equiv-unit-trunc-unit-Setᵉ : unitᵉ ≃ᵉ type-trunc-Setᵉ unitᵉ
equiv-unit-trunc-unit-Setᵉ = equiv-unit-trunc-Setᵉ unit-Setᵉ

abstract
  is-contr-trunc-Setᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-contrᵉ Aᵉ → is-contrᵉ (type-trunc-Setᵉ Aᵉ)
  is-contr-trunc-Setᵉ {lᵉ} {Aᵉ} Hᵉ =
    is-contr-equiv'ᵉ
      ( Aᵉ)
      ( equiv-unit-trunc-Setᵉ (pairᵉ Aᵉ (is-set-is-contrᵉ Hᵉ)))
      ( Hᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  (Sfᵉ : is-set-truncationᵉ Bᵉ fᵉ)
  where

  abstract
    uniqueness-trunc-Setᵉ :
      is-contrᵉ
        ( Σᵉ (type-trunc-Setᵉ Aᵉ ≃ᵉ type-Setᵉ Bᵉ)
        ( λ eᵉ → map-equivᵉ eᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ fᵉ))
    uniqueness-trunc-Setᵉ =
      uniqueness-set-truncationᵉ (trunc-Setᵉ Aᵉ) unit-trunc-Setᵉ Bᵉ fᵉ
        ( λ {lᵉ} → is-set-truncation-trunc-Setᵉ Aᵉ)
        ( Sfᵉ)

  equiv-uniqueness-trunc-Setᵉ : type-trunc-Setᵉ Aᵉ ≃ᵉ type-Setᵉ Bᵉ
  equiv-uniqueness-trunc-Setᵉ = pr1ᵉ (centerᵉ uniqueness-trunc-Setᵉ)

  map-equiv-uniqueness-trunc-Setᵉ : type-trunc-Setᵉ Aᵉ → type-Setᵉ Bᵉ
  map-equiv-uniqueness-trunc-Setᵉ = map-equivᵉ equiv-uniqueness-trunc-Setᵉ

  triangle-uniqueness-trunc-Setᵉ :
    map-equiv-uniqueness-trunc-Setᵉ ∘ᵉ unit-trunc-Setᵉ ~ᵉ fᵉ
  triangle-uniqueness-trunc-Setᵉ = pr2ᵉ (centerᵉ uniqueness-trunc-Setᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Setᵉ l2ᵉ) (fᵉ : Aᵉ → type-Setᵉ Bᵉ)
  (Sfᵉ : is-set-truncationᵉ Bᵉ fᵉ)
  where

  abstract
    uniqueness-trunc-Set'ᵉ :
      is-contrᵉ
        ( Σᵉ ( type-Setᵉ Bᵉ ≃ᵉ type-trunc-Setᵉ Aᵉ)
            ( λ eᵉ → map-equivᵉ eᵉ ∘ᵉ fᵉ ~ᵉ unit-trunc-Setᵉ))
    uniqueness-trunc-Set'ᵉ =
      uniqueness-set-truncationᵉ Bᵉ fᵉ (trunc-Setᵉ Aᵉ) unit-trunc-Setᵉ Sfᵉ
        ( λ {lᵉ} → is-set-truncation-trunc-Setᵉ Aᵉ)

  equiv-uniqueness-trunc-Set'ᵉ : type-Setᵉ Bᵉ ≃ᵉ type-trunc-Setᵉ Aᵉ
  equiv-uniqueness-trunc-Set'ᵉ = pr1ᵉ (centerᵉ uniqueness-trunc-Set'ᵉ)

  map-equiv-uniqueness-trunc-Set'ᵉ : type-Setᵉ Bᵉ → type-trunc-Setᵉ Aᵉ
  map-equiv-uniqueness-trunc-Set'ᵉ =
    map-equivᵉ equiv-uniqueness-trunc-Set'ᵉ

  triangle-uniqueness-trunc-Set'ᵉ :
    map-equiv-uniqueness-trunc-Set'ᵉ ∘ᵉ fᵉ ~ᵉ unit-trunc-Setᵉ
  triangle-uniqueness-trunc-Set'ᵉ = pr2ᵉ (centerᵉ uniqueness-trunc-Set'ᵉ)
```

### The set truncation of a set is equivalent to the set

```agda
module _
  {lᵉ : Level} (Aᵉ : Setᵉ lᵉ)
  where

  equiv-unit-trunc-setᵉ : type-Setᵉ Aᵉ ≃ᵉ type-trunc-Setᵉ (type-Setᵉ Aᵉ)
  equiv-unit-trunc-setᵉ = equiv-unit-truncᵉ Aᵉ
```

### Distributive of set truncation over coproduct

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  abstract
    distributive-trunc-coproduct-Setᵉ :
      is-contrᵉ
        ( Σᵉ ( equiv-Setᵉ
              ( trunc-Setᵉ (Aᵉ +ᵉ Bᵉ))
              ( coproduct-Setᵉ (trunc-Setᵉ Aᵉ) (trunc-Setᵉ Bᵉ)))
            ( λ eᵉ →
              ( map-equivᵉ eᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
              ( map-coproductᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ)))
    distributive-trunc-coproduct-Setᵉ =
      uniqueness-trunc-Setᵉ
        ( coproduct-Setᵉ (trunc-Setᵉ Aᵉ) (trunc-Setᵉ Bᵉ))
        ( map-coproductᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ)
        ( λ {lᵉ} Cᵉ →
          is-equiv-right-factorᵉ
            ( ev-inl-inrᵉ (λ xᵉ → type-Setᵉ Cᵉ))
            ( precomp-Setᵉ (map-coproductᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ) Cᵉ)
            ( universal-property-coproductᵉ (type-Setᵉ Cᵉ))
            ( is-equiv-compᵉ
              ( map-productᵉ
                ( precomp-Setᵉ unit-trunc-Setᵉ Cᵉ)
                ( precomp-Setᵉ unit-trunc-Setᵉ Cᵉ))
              ( ev-inl-inrᵉ (λ xᵉ → type-Setᵉ Cᵉ))
              ( universal-property-coproductᵉ (type-Setᵉ Cᵉ))
              ( is-equiv-map-productᵉ
                ( precomp-Setᵉ unit-trunc-Setᵉ Cᵉ)
                ( precomp-Setᵉ unit-trunc-Setᵉ Cᵉ)
                ( is-set-truncation-trunc-Setᵉ Aᵉ Cᵉ)
                ( is-set-truncation-trunc-Setᵉ Bᵉ Cᵉ))))

  equiv-distributive-trunc-coproduct-Setᵉ :
    equiv-Setᵉ (trunc-Setᵉ (Aᵉ +ᵉ Bᵉ)) (coproduct-Setᵉ (trunc-Setᵉ Aᵉ) (trunc-Setᵉ Bᵉ))
  equiv-distributive-trunc-coproduct-Setᵉ =
    pr1ᵉ (centerᵉ distributive-trunc-coproduct-Setᵉ)

  map-equiv-distributive-trunc-coproduct-Setᵉ :
    hom-Setᵉ (trunc-Setᵉ (Aᵉ +ᵉ Bᵉ)) (coproduct-Setᵉ (trunc-Setᵉ Aᵉ) (trunc-Setᵉ Bᵉ))
  map-equiv-distributive-trunc-coproduct-Setᵉ =
    map-equivᵉ equiv-distributive-trunc-coproduct-Setᵉ

  triangle-distributive-trunc-coproduct-Setᵉ :
    ( map-equiv-distributive-trunc-coproduct-Setᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
    ( map-coproductᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ)
  triangle-distributive-trunc-coproduct-Setᵉ =
    pr2ᵉ (centerᵉ distributive-trunc-coproduct-Setᵉ)
```

### Set truncations of Σ-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  abstract
    trunc-Σ-Setᵉ :
      is-contrᵉ
        ( Σᵉ ( type-trunc-Setᵉ (Σᵉ Aᵉ Bᵉ) ≃ᵉ
              type-trunc-Setᵉ (Σᵉ Aᵉ (λ xᵉ → type-trunc-Setᵉ (Bᵉ xᵉ))))
            ( λ eᵉ →
              ( map-equivᵉ eᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
              ( unit-trunc-Setᵉ ∘ᵉ totᵉ (λ xᵉ → unit-trunc-Setᵉ))))
    trunc-Σ-Setᵉ =
      uniqueness-trunc-Setᵉ
        ( trunc-Setᵉ (Σᵉ Aᵉ (λ xᵉ → type-trunc-Setᵉ (Bᵉ xᵉ))))
        ( unit-trunc-Setᵉ ∘ᵉ totᵉ (λ xᵉ → unit-trunc-Setᵉ))
        ( λ {lᵉ} Cᵉ →
          is-equiv-right-factorᵉ
            ( ev-pairᵉ)
            ( precomp-Setᵉ (unit-trunc-Setᵉ ∘ᵉ totᵉ (λ xᵉ → unit-trunc-Setᵉ)) Cᵉ)
            ( is-equiv-ev-pairᵉ)
            ( is-equiv-htpy-equivᵉ
              ( ( equiv-Π-equiv-familyᵉ
                  ( λ xᵉ → equiv-universal-property-trunc-Setᵉ Cᵉ)) ∘eᵉ
                ( equiv-ev-pairᵉ) ∘eᵉ
                ( equiv-universal-property-trunc-Setᵉ Cᵉ))
              ( refl-htpyᵉ)))

  equiv-trunc-Σ-Setᵉ :
    type-trunc-Setᵉ (Σᵉ Aᵉ Bᵉ) ≃ᵉ type-trunc-Setᵉ (Σᵉ Aᵉ (λ xᵉ → type-trunc-Setᵉ (Bᵉ xᵉ)))
  equiv-trunc-Σ-Setᵉ = pr1ᵉ (centerᵉ trunc-Σ-Setᵉ)

  map-equiv-trunc-Σ-Setᵉ :
    type-trunc-Setᵉ (Σᵉ Aᵉ Bᵉ) → type-trunc-Setᵉ (Σᵉ Aᵉ (λ xᵉ → type-trunc-Setᵉ (Bᵉ xᵉ)))
  map-equiv-trunc-Σ-Setᵉ = map-equivᵉ equiv-trunc-Σ-Setᵉ
```

### `trunc-Set` distributes over products

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ)
  where

  abstract
    distributive-trunc-product-Setᵉ :
      is-contrᵉ
        ( Σᵉ ( type-trunc-Setᵉ (Aᵉ ×ᵉ Bᵉ) ≃ᵉ (type-trunc-Setᵉ Aᵉ ×ᵉ type-trunc-Setᵉ Bᵉ))
            ( λ eᵉ →
              ( map-equivᵉ eᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
              ( map-productᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ)))
    distributive-trunc-product-Setᵉ =
      uniqueness-trunc-Setᵉ
        ( product-Setᵉ (trunc-Setᵉ Aᵉ) (trunc-Setᵉ Bᵉ))
        ( map-productᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ)
        ( λ {lᵉ} Cᵉ →
          is-equiv-right-factorᵉ
            ( ev-pairᵉ)
            ( precomp-Setᵉ (map-productᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ) Cᵉ)
            ( is-equiv-ev-pairᵉ)
            ( is-equiv-htpy-equivᵉ
              ( ( equiv-universal-property-trunc-Setᵉ (Π-Set'ᵉ Bᵉ (λ yᵉ → Cᵉ))) ∘eᵉ
                ( equiv-postcompᵉ
                  ( type-trunc-Setᵉ Aᵉ)
                  ( equiv-universal-property-trunc-Setᵉ Cᵉ)) ∘eᵉ
                ( equiv-ev-pairᵉ))
              ( refl-htpyᵉ)))

  equiv-distributive-trunc-product-Setᵉ :
    type-trunc-Setᵉ (Aᵉ ×ᵉ Bᵉ) ≃ᵉ (type-trunc-Setᵉ Aᵉ ×ᵉ type-trunc-Setᵉ Bᵉ)
  equiv-distributive-trunc-product-Setᵉ =
    pr1ᵉ (centerᵉ distributive-trunc-product-Setᵉ)

  map-equiv-distributive-trunc-product-Setᵉ :
    type-trunc-Setᵉ (Aᵉ ×ᵉ Bᵉ) → type-trunc-Setᵉ Aᵉ ×ᵉ type-trunc-Setᵉ Bᵉ
  map-equiv-distributive-trunc-product-Setᵉ =
    map-equivᵉ equiv-distributive-trunc-product-Setᵉ

  map-inv-equiv-distributive-trunc-product-Setᵉ :
    type-trunc-Setᵉ Aᵉ ×ᵉ type-trunc-Setᵉ Bᵉ → type-trunc-Setᵉ (Aᵉ ×ᵉ Bᵉ)
  map-inv-equiv-distributive-trunc-product-Setᵉ =
    map-inv-equivᵉ equiv-distributive-trunc-product-Setᵉ

  triangle-distributive-trunc-product-Setᵉ :
    ( map-equiv-distributive-trunc-product-Setᵉ ∘ᵉ unit-trunc-Setᵉ) ~ᵉ
    ( map-productᵉ unit-trunc-Setᵉ unit-trunc-Setᵉ)
  triangle-distributive-trunc-product-Setᵉ =
    pr2ᵉ (centerᵉ distributive-trunc-product-Setᵉ)
```