# Symmetric cores of binary relations

```agda
module foundation.symmetric-cores-binary-relationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.morphisms-binary-relationsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.symmetric-binary-relationsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-function-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ **symmetricᵉ core**ᵉ ofᵉ aᵉ [binaryᵉ relation](foundation.binary-relations.mdᵉ)
`Rᵉ : Aᵉ → Aᵉ → 𝒰`ᵉ onᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ
[symmetricᵉ binaryᵉ relation](foundation.symmetric-binary-relations.mdᵉ) `coreᵉ R`ᵉ
equippedᵉ with aᵉ counitᵉ

```text
  (xᵉ yᵉ : Aᵉ) → coreᵉ Rᵉ {xᵉ ,ᵉ yᵉ} → Rᵉ xᵉ yᵉ
```

thatᵉ satisfiesᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ symmetricᵉ core,ᵉ i.e.,ᵉ itᵉ satisfiesᵉ
theᵉ propertyᵉ thatᵉ forᵉ anyᵉ symmetricᵉ relationᵉ `Sᵉ : unordered-pairᵉ Aᵉ → 𝒰`,ᵉ theᵉ
precompositionᵉ functionᵉ

```text
  hom-Symmetric-Relationᵉ Sᵉ (coreᵉ Rᵉ) → hom-Relationᵉ (relᵉ Sᵉ) Rᵉ
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.md).ᵉ Theᵉ symmetricᵉ coreᵉ ofᵉ aᵉ
binaryᵉ relationᵉ `R`ᵉ isᵉ definedᵉ asᵉ theᵉ relationᵉ

```text
  coreᵉ Rᵉ (I,aᵉ) :=ᵉ (iᵉ : Iᵉ) → Rᵉ (aᵉ iᵉ) (aᵉ -iᵉ)
```

where `-i`ᵉ isᵉ theᵉ elementᵉ ofᵉ theᵉ
[2-elementᵉ type](univalent-combinatorics.2-element-types.mdᵉ) obtainedᵉ byᵉ
applyingᵉ theᵉ swapᵉ [involution](foundation.involutions.mdᵉ) to `i`.ᵉ Withᵉ thisᵉ
definitionᵉ itᵉ isᵉ easyᵉ to seeᵉ thatᵉ theᵉ universalᵉ propertyᵉ ofᵉ theᵉ adjunctionᵉ
shouldᵉ hold,ᵉ sinceᵉ weᵉ haveᵉ

```text
  ((I,aᵉ) → Sᵉ (I,aᵉ) → coreᵉ Rᵉ (I,aᵉ)) ≃ᵉ ((xᵉ yᵉ : Aᵉ) → Sᵉ {x,yᵉ} → Rᵉ xᵉ y).ᵉ
```

## Definitions

### The symmetric core of a binary relation

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  where

  symmetric-core-Relationᵉ : Symmetric-Relationᵉ l2ᵉ Aᵉ
  symmetric-core-Relationᵉ pᵉ =
    (iᵉ : type-unordered-pairᵉ pᵉ) →
    Rᵉ (element-unordered-pairᵉ pᵉ iᵉ) (other-element-unordered-pairᵉ pᵉ iᵉ)

  counit-symmetric-core-Relationᵉ :
    {xᵉ yᵉ : Aᵉ} →
    relation-Symmetric-Relationᵉ symmetric-core-Relationᵉ xᵉ yᵉ → Rᵉ xᵉ yᵉ
  counit-symmetric-core-Relationᵉ {xᵉ} {yᵉ} rᵉ =
    trᵉ
      ( Rᵉ xᵉ)
      ( compute-other-element-standard-unordered-pairᵉ xᵉ yᵉ (zero-Finᵉ 1ᵉ))
      ( rᵉ (zero-Finᵉ 1ᵉ))
```

## Properties

### The universal property of the symmetric core of a binary relation

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : Relationᵉ l2ᵉ Aᵉ)
  (Sᵉ : Symmetric-Relationᵉ l3ᵉ Aᵉ)
  where

  map-universal-property-symmetric-core-Relationᵉ :
    hom-Symmetric-Relationᵉ Sᵉ (symmetric-core-Relationᵉ Rᵉ) →
    hom-Relationᵉ (relation-Symmetric-Relationᵉ Sᵉ) Rᵉ
  map-universal-property-symmetric-core-Relationᵉ fᵉ xᵉ yᵉ sᵉ =
    counit-symmetric-core-Relationᵉ Rᵉ (fᵉ (standard-unordered-pairᵉ xᵉ yᵉ) sᵉ)

  equiv-universal-property-symmetric-core-Relationᵉ :
    hom-Symmetric-Relationᵉ Sᵉ (symmetric-core-Relationᵉ Rᵉ) ≃ᵉ
    hom-Relationᵉ (relation-Symmetric-Relationᵉ Sᵉ) Rᵉ
  equiv-universal-property-symmetric-core-Relationᵉ =
    ( equiv-Π-equiv-familyᵉ
      ( λ xᵉ →
        equiv-Π-equiv-familyᵉ
          ( λ yᵉ →
            equiv-postcompᵉ
              ( Sᵉ (standard-unordered-pairᵉ xᵉ yᵉ))
              ( equiv-trᵉ
                ( Rᵉ _)
                ( compute-other-element-standard-unordered-pairᵉ xᵉ yᵉ
                  ( zero-Finᵉ 1ᵉ)))))) ∘eᵉ
    ( equiv-dependent-universal-property-pointed-unordered-pairsᵉ
      ( λ pᵉ iᵉ →
        Sᵉ pᵉ →
        Rᵉ (element-unordered-pairᵉ pᵉ iᵉ) (other-element-unordered-pairᵉ pᵉ iᵉ))) ∘eᵉ
    ( equiv-Π-equiv-familyᵉ (λ pᵉ → equiv-swap-Πᵉ))

  universal-property-symmetric-core-Relationᵉ :
    is-equivᵉ map-universal-property-symmetric-core-Relationᵉ
  universal-property-symmetric-core-Relationᵉ =
    is-equiv-map-equivᵉ
      ( equiv-universal-property-symmetric-core-Relationᵉ)
```