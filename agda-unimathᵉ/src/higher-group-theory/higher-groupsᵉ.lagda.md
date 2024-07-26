# Higher groups

```agda
module higher-group-theory.higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.full-subtypesᵉ
open import foundation.identity-typesᵉ
open import foundation.imagesᵉ
open import foundation.mere-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.pointed-typesᵉ

open import synthetic-homotopy-theory.loop-spacesᵉ
```

</details>

## Idea

Anᵉ **∞-group**ᵉ isᵉ justᵉ aᵉ [pointed](structured-types.pointed-types.mdᵉ)
[connected](foundation.0-connected-types.mdᵉ) type.ᵉ Itsᵉ underlyingᵉ typeᵉ isᵉ itsᵉ
[loopᵉ space](synthetic-homotopy-theory.loop-spaces.md),ᵉ andᵉ theᵉ classifyingᵉ typeᵉ
isᵉ theᵉ pointedᵉ connectedᵉ typeᵉ itself.ᵉ

## Definition

```agda
∞-Groupᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
∞-Groupᵉ lᵉ = Σᵉ (Pointed-Typeᵉ lᵉ) (λ Xᵉ → is-0-connectedᵉ (type-Pointed-Typeᵉ Xᵉ))

module _
  {lᵉ : Level} (Gᵉ : ∞-Groupᵉ lᵉ)
  where

  classifying-pointed-type-∞-Groupᵉ : Pointed-Typeᵉ lᵉ
  classifying-pointed-type-∞-Groupᵉ = pr1ᵉ Gᵉ

  classifying-type-∞-Groupᵉ : UUᵉ lᵉ
  classifying-type-∞-Groupᵉ =
    type-Pointed-Typeᵉ classifying-pointed-type-∞-Groupᵉ

  shape-∞-Groupᵉ : classifying-type-∞-Groupᵉ
  shape-∞-Groupᵉ =
    point-Pointed-Typeᵉ classifying-pointed-type-∞-Groupᵉ

  point-∞-Groupᵉ : unitᵉ → classifying-type-∞-Groupᵉ
  point-∞-Groupᵉ = pointᵉ shape-∞-Groupᵉ

  abstract
    is-0-connected-classifying-type-∞-Groupᵉ :
      is-0-connectedᵉ classifying-type-∞-Groupᵉ
    is-0-connected-classifying-type-∞-Groupᵉ = pr2ᵉ Gᵉ

  abstract
    mere-eq-classifying-type-∞-Groupᵉ :
      (Xᵉ Yᵉ : classifying-type-∞-Groupᵉ) → mere-eqᵉ Xᵉ Yᵉ
    mere-eq-classifying-type-∞-Groupᵉ =
      mere-eq-is-0-connectedᵉ
        is-0-connected-classifying-type-∞-Groupᵉ

  abstract
    is-full-subtype-im-point-∞-Groupᵉ :
      is-full-subtypeᵉ (subtype-imᵉ point-∞-Groupᵉ)
    is-full-subtype-im-point-∞-Groupᵉ xᵉ =
      apply-universal-property-trunc-Propᵉ
        ( mere-eq-classifying-type-∞-Groupᵉ shape-∞-Groupᵉ xᵉ)
        ( subtype-imᵉ point-∞-Groupᵉ xᵉ)
        ( λ where reflᵉ → unit-trunc-Propᵉ (starᵉ ,ᵉ reflᵉ))

  compute-im-point-∞-Groupᵉ :
    imᵉ point-∞-Groupᵉ ≃ᵉ classifying-type-∞-Groupᵉ
  compute-im-point-∞-Groupᵉ =
    equiv-inclusion-is-full-subtypeᵉ
      ( subtype-imᵉ point-∞-Groupᵉ)
      ( is-full-subtype-im-point-∞-Groupᵉ)

  abstract
    elim-prop-classifying-type-∞-Groupᵉ :
      {l2ᵉ : Level} (Pᵉ : classifying-type-∞-Groupᵉ → Propᵉ l2ᵉ) →
      type-Propᵉ (Pᵉ shape-∞-Groupᵉ) →
      ((Xᵉ : classifying-type-∞-Groupᵉ) → type-Propᵉ (Pᵉ Xᵉ))
    elim-prop-classifying-type-∞-Groupᵉ =
      apply-dependent-universal-property-is-0-connectedᵉ
        shape-∞-Groupᵉ
        is-0-connected-classifying-type-∞-Groupᵉ

  h-space-∞-Groupᵉ : H-Spaceᵉ lᵉ
  h-space-∞-Groupᵉ = Ω-H-Spaceᵉ classifying-pointed-type-∞-Groupᵉ

  pointed-type-∞-Groupᵉ : Pointed-Typeᵉ lᵉ
  pointed-type-∞-Groupᵉ = Ωᵉ classifying-pointed-type-∞-Groupᵉ

  type-∞-Groupᵉ : UUᵉ lᵉ
  type-∞-Groupᵉ = type-Pointed-Typeᵉ pointed-type-∞-Groupᵉ

  unit-∞-Groupᵉ : type-∞-Groupᵉ
  unit-∞-Groupᵉ = point-Pointed-Typeᵉ pointed-type-∞-Groupᵉ

  mul-∞-Groupᵉ : (xᵉ yᵉ : type-∞-Groupᵉ) → type-∞-Groupᵉ
  mul-∞-Groupᵉ = mul-Ωᵉ classifying-pointed-type-∞-Groupᵉ

  associative-mul-∞-Groupᵉ :
    (xᵉ yᵉ zᵉ : type-∞-Groupᵉ) →
    Idᵉ
      ( mul-∞-Groupᵉ (mul-∞-Groupᵉ xᵉ yᵉ) zᵉ)
      ( mul-∞-Groupᵉ xᵉ (mul-∞-Groupᵉ yᵉ zᵉ))
  associative-mul-∞-Groupᵉ = associative-mul-Ωᵉ classifying-pointed-type-∞-Groupᵉ

  left-unit-law-mul-∞-Groupᵉ :
    (xᵉ : type-∞-Groupᵉ) → Idᵉ (mul-∞-Groupᵉ unit-∞-Groupᵉ xᵉ) xᵉ
  left-unit-law-mul-∞-Groupᵉ =
    left-unit-law-mul-Ωᵉ classifying-pointed-type-∞-Groupᵉ

  right-unit-law-mul-∞-Groupᵉ :
    (yᵉ : type-∞-Groupᵉ) → Idᵉ (mul-∞-Groupᵉ yᵉ unit-∞-Groupᵉ) yᵉ
  right-unit-law-mul-∞-Groupᵉ =
    right-unit-law-mul-Ωᵉ classifying-pointed-type-∞-Groupᵉ

  coherence-unit-laws-mul-∞-Groupᵉ :
    left-unit-law-mul-∞-Groupᵉ unit-∞-Groupᵉ ＝ᵉ
    right-unit-law-mul-∞-Groupᵉ unit-∞-Groupᵉ
  coherence-unit-laws-mul-∞-Groupᵉ =
    coherence-unit-laws-mul-Ωᵉ classifying-pointed-type-∞-Groupᵉ

  inv-∞-Groupᵉ : type-∞-Groupᵉ → type-∞-Groupᵉ
  inv-∞-Groupᵉ = inv-Ωᵉ classifying-pointed-type-∞-Groupᵉ

  left-inverse-law-mul-∞-Groupᵉ :
    (xᵉ : type-∞-Groupᵉ) → Idᵉ (mul-∞-Groupᵉ (inv-∞-Groupᵉ xᵉ) xᵉ) unit-∞-Groupᵉ
  left-inverse-law-mul-∞-Groupᵉ =
    left-inverse-law-mul-Ωᵉ classifying-pointed-type-∞-Groupᵉ

  right-inverse-law-mul-∞-Groupᵉ :
    (xᵉ : type-∞-Groupᵉ) → Idᵉ (mul-∞-Groupᵉ xᵉ (inv-∞-Groupᵉ xᵉ)) unit-∞-Groupᵉ
  right-inverse-law-mul-∞-Groupᵉ =
    right-inverse-law-mul-Ωᵉ classifying-pointed-type-∞-Groupᵉ
```