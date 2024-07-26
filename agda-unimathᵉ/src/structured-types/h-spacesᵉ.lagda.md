# H-spaces

```agda
module structured-types.h-spacesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.evaluation-functionsᵉ
open import foundation.function-extensionalityᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unital-binary-operationsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.endomorphismsᵉ

open import structured-types.magmasᵉ
open import structured-types.noncoherent-h-spacesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-sectionsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Aᵉ **(coherentᵉ) H-space**ᵉ isᵉ aᵉ "wildᵉ unitalᵉ magma",ᵉ i.e.,ᵉ itᵉ isᵉ aᵉ
[pointedᵉ type](structured-types.pointed-types.mdᵉ)
[equipped](foundation.structure.mdᵉ) with aᵉ binaryᵉ operationᵉ forᵉ whichᵉ theᵉ baseᵉ
pointᵉ isᵉ aᵉ unit,ᵉ with aᵉ coherenceᵉ lawᵉ betweenᵉ theᵉ leftᵉ andᵉ theᵉ rightᵉ unitᵉ laws.ᵉ

## Definitions

### Unital binary operations on pointed types

```agda
coherent-unit-laws-mul-Pointed-Typeᵉ :
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  (μᵉ : (xᵉ yᵉ : type-Pointed-Typeᵉ Aᵉ) → type-Pointed-Typeᵉ Aᵉ) → UUᵉ lᵉ
coherent-unit-laws-mul-Pointed-Typeᵉ Aᵉ μᵉ =
  coherent-unit-lawsᵉ μᵉ (point-Pointed-Typeᵉ Aᵉ)

coherent-unital-mul-Pointed-Typeᵉ :
  {lᵉ : Level} → Pointed-Typeᵉ lᵉ → UUᵉ lᵉ
coherent-unital-mul-Pointed-Typeᵉ Aᵉ =
  Σᵉ ( type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Aᵉ)
    ( coherent-unit-laws-mul-Pointed-Typeᵉ Aᵉ)
```

### H-spaces

Anᵉ H-spaceᵉ consistsᵉ ofᵉ aᵉ pointedᵉ typeᵉ `X`ᵉ andᵉ aᵉ coherentᵉ unitalᵉ multiplicationᵉ
onᵉ `X`.ᵉ Theᵉ entryᵉ `make-H-Space`ᵉ isᵉ providedᵉ to breakᵉ upᵉ theᵉ constructionᵉ ofᵉ anᵉ
H-spaceᵉ intoᵉ twoᵉ componentsᵉ: theᵉ constructionᵉ ofᵉ itsᵉ underlyingᵉ pointedᵉ typeᵉ andᵉ
theᵉ constructionᵉ ofᵉ theᵉ coherentlyᵉ unitalᵉ multiplicationᵉ onᵉ thisᵉ pointedᵉ type.ᵉ
Furthermore,ᵉ thisᵉ definitionᵉ suggestsᵉ thatᵉ anyᵉ constructionᵉ ofᵉ anᵉ H-spaceᵉ shouldᵉ
beᵉ refactoredᵉ byᵉ firstᵉ definingᵉ itsᵉ underlyingᵉ pointedᵉ type,ᵉ thenᵉ definingᵉ itsᵉ
coherentlyᵉ unitalᵉ multiplication,ᵉ andᵉ finallyᵉ combiningᵉ thoseᵉ twoᵉ constructionsᵉ
using `make-H-Space`.ᵉ

```agda
H-Spaceᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
H-Spaceᵉ lᵉ =
  Σᵉ ( Pointed-Typeᵉ lᵉ) coherent-unital-mul-Pointed-Typeᵉ

make-H-Spaceᵉ :
  {lᵉ : Level} →
  (Xᵉ : Pointed-Typeᵉ lᵉ) → coherent-unital-mul-Pointed-Typeᵉ Xᵉ → H-Spaceᵉ lᵉ
make-H-Spaceᵉ Xᵉ μᵉ = (Xᵉ ,ᵉ μᵉ)

{-# INLINE make-H-Spaceᵉ #-}

module _
  {lᵉ : Level} (Mᵉ : H-Spaceᵉ lᵉ)
  where

  pointed-type-H-Spaceᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-H-Spaceᵉ = pr1ᵉ Mᵉ

  type-H-Spaceᵉ : UUᵉ lᵉ
  type-H-Spaceᵉ = type-Pointed-Typeᵉ pointed-type-H-Spaceᵉ

  unit-H-Spaceᵉ : type-H-Spaceᵉ
  unit-H-Spaceᵉ = point-Pointed-Typeᵉ pointed-type-H-Spaceᵉ

  coherent-unital-mul-H-Spaceᵉ :
    coherent-unital-mul-Pointed-Typeᵉ pointed-type-H-Spaceᵉ
  coherent-unital-mul-H-Spaceᵉ = pr2ᵉ Mᵉ

  mul-H-Spaceᵉ :
    type-H-Spaceᵉ → type-H-Spaceᵉ → type-H-Spaceᵉ
  mul-H-Spaceᵉ = pr1ᵉ coherent-unital-mul-H-Spaceᵉ

  mul-H-Space'ᵉ :
    type-H-Spaceᵉ → type-H-Spaceᵉ → type-H-Spaceᵉ
  mul-H-Space'ᵉ xᵉ yᵉ = mul-H-Spaceᵉ yᵉ xᵉ

  ap-mul-H-Spaceᵉ :
    {aᵉ bᵉ cᵉ dᵉ : type-H-Spaceᵉ} → Idᵉ aᵉ bᵉ → Idᵉ cᵉ dᵉ →
    Idᵉ (mul-H-Spaceᵉ aᵉ cᵉ) (mul-H-Spaceᵉ bᵉ dᵉ)
  ap-mul-H-Spaceᵉ pᵉ qᵉ = ap-binaryᵉ mul-H-Spaceᵉ pᵉ qᵉ

  magma-H-Spaceᵉ : Magmaᵉ lᵉ
  pr1ᵉ magma-H-Spaceᵉ = type-H-Spaceᵉ
  pr2ᵉ magma-H-Spaceᵉ = mul-H-Spaceᵉ

  coherent-unit-laws-mul-H-Spaceᵉ :
    coherent-unit-lawsᵉ mul-H-Spaceᵉ unit-H-Spaceᵉ
  coherent-unit-laws-mul-H-Spaceᵉ =
    pr2ᵉ coherent-unital-mul-H-Spaceᵉ

  left-unit-law-mul-H-Spaceᵉ :
    (xᵉ : type-H-Spaceᵉ) →
    Idᵉ (mul-H-Spaceᵉ unit-H-Spaceᵉ xᵉ) xᵉ
  left-unit-law-mul-H-Spaceᵉ =
    pr1ᵉ coherent-unit-laws-mul-H-Spaceᵉ

  right-unit-law-mul-H-Spaceᵉ :
    (xᵉ : type-H-Spaceᵉ) →
    Idᵉ (mul-H-Spaceᵉ xᵉ unit-H-Spaceᵉ) xᵉ
  right-unit-law-mul-H-Spaceᵉ =
    pr1ᵉ (pr2ᵉ coherent-unit-laws-mul-H-Spaceᵉ)

  coh-unit-laws-mul-H-Spaceᵉ :
    Idᵉ
      ( left-unit-law-mul-H-Spaceᵉ unit-H-Spaceᵉ)
      ( right-unit-law-mul-H-Spaceᵉ unit-H-Spaceᵉ)
  coh-unit-laws-mul-H-Spaceᵉ =
    pr2ᵉ (pr2ᵉ coherent-unit-laws-mul-H-Spaceᵉ)

  unit-laws-mul-H-Spaceᵉ :
    unit-lawsᵉ mul-H-Spaceᵉ unit-H-Spaceᵉ
  pr1ᵉ unit-laws-mul-H-Spaceᵉ = left-unit-law-mul-H-Spaceᵉ
  pr2ᵉ unit-laws-mul-H-Spaceᵉ = right-unit-law-mul-H-Spaceᵉ

  is-unital-mul-H-Spaceᵉ : is-unitalᵉ mul-H-Spaceᵉ
  pr1ᵉ is-unital-mul-H-Spaceᵉ = unit-H-Spaceᵉ
  pr2ᵉ is-unital-mul-H-Spaceᵉ = unit-laws-mul-H-Spaceᵉ

  is-coherently-unital-mul-H-Spaceᵉ :
    is-coherently-unitalᵉ mul-H-Spaceᵉ
  pr1ᵉ is-coherently-unital-mul-H-Spaceᵉ = unit-H-Spaceᵉ
  pr2ᵉ is-coherently-unital-mul-H-Spaceᵉ =
    coherent-unit-laws-mul-H-Spaceᵉ
```

## Properties

### Every noncoherent H-space can be upgraded to a coherent H-space

```agda
h-space-Noncoherent-H-Spaceᵉ :
  {lᵉ : Level} → Noncoherent-H-Spaceᵉ lᵉ → H-Spaceᵉ lᵉ
pr1ᵉ (h-space-Noncoherent-H-Spaceᵉ Aᵉ) = pointed-type-Noncoherent-H-Spaceᵉ Aᵉ
pr1ᵉ (pr2ᵉ (h-space-Noncoherent-H-Spaceᵉ Aᵉ)) = mul-Noncoherent-H-Spaceᵉ Aᵉ
pr2ᵉ (pr2ᵉ (h-space-Noncoherent-H-Spaceᵉ Aᵉ)) =
  coherent-unit-laws-unit-lawsᵉ
    ( mul-Noncoherent-H-Spaceᵉ Aᵉ)
    ( unit-laws-mul-Noncoherent-H-Spaceᵉ Aᵉ)
```

### The type of H-space structures on `A` is equivalent to the type of sections of `ev-point : (A → A) →∗ A`

```agda
module _
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ)
  where

  ev-endo-Pointed-Typeᵉ : endo-Pointed-Typeᵉ (type-Pointed-Typeᵉ Aᵉ) →∗ᵉ Aᵉ
  pr1ᵉ ev-endo-Pointed-Typeᵉ = ev-point-Pointed-Typeᵉ Aᵉ
  pr2ᵉ ev-endo-Pointed-Typeᵉ = reflᵉ

  pointed-section-ev-point-Pointed-Typeᵉ : UUᵉ lᵉ
  pointed-section-ev-point-Pointed-Typeᵉ =
    pointed-sectionᵉ ev-endo-Pointed-Typeᵉ

  compute-pointed-section-ev-point-Pointed-Typeᵉ :
    pointed-section-ev-point-Pointed-Typeᵉ ≃ᵉ coherent-unital-mul-Pointed-Typeᵉ Aᵉ
  compute-pointed-section-ev-point-Pointed-Typeᵉ =
    ( equiv-totᵉ
      ( λ _ →
        equiv-Σᵉ _
          ( equiv-funextᵉ)
          ( λ _ →
            equiv-totᵉ (λ _ → inv-equivᵉ (equiv-right-whisker-concatᵉ reflᵉ))))) ∘eᵉ
    ( associative-Σᵉ _ _ _)
```