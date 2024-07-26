# Ferrers diagrams (unlabeled partitions)

```agda
module univalent-combinatorics.ferrers-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

**Unlabeledᵉ partitions**,ᵉ alsoᵉ knownᵉ asᵉ **Ferrersᵉ diagrams**,ᵉ ofᵉ aᵉ typeᵉ `A`ᵉ
record theᵉ numberᵉ ofᵉ waysᵉ in whichᵉ `A`ᵉ canᵉ beᵉ decomposedᵉ asᵉ theᵉ
[dependentᵉ pairᵉ type](foundation.dependent-pair-types.mdᵉ) ofᵉ aᵉ familyᵉ ofᵉ
[inhabitedᵉ types](foundation.inhabited-types.md).ᵉ Moreᵉ precisely,ᵉ aᵉ Ferrersᵉ
diagramᵉ ofᵉ aᵉ typeᵉ `A`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ andᵉ aᵉ familyᵉ `Y`ᵉ ofᵉ inhabitedᵉ typesᵉ
overᵉ `X`ᵉ suchᵉ thatᵉ `Σᵉ Xᵉ Y`ᵉ isᵉ
[merelyᵉ equivalent](foundation.mere-equivalences.mdᵉ) to `A`.ᵉ Aᵉ finiteᵉ Finiteᵉ
ferrersᵉ diagramᵉ ofᵉ aᵉ [finiteᵉ type](univalent-combinatorics.finite-types.mdᵉ) `A`ᵉ
consistsᵉ ofᵉ aᵉ finiteᵉ typeᵉ `X`ᵉ andᵉ aᵉ familyᵉ `Y`ᵉ ofᵉ inhabitedᵉ finiteᵉ typesᵉ overᵉ
`X`ᵉ suchᵉ thatᵉ `Σᵉ Xᵉ Y`ᵉ isᵉ merelyᵉ equivalentᵉ to `A`.ᵉ Theᵉ numberᵉ ofᵉ finiteᵉ Ferrersᵉ
diagramsᵉ ofᵉ `A`ᵉ isᵉ theᵉ [partitionᵉ number](univalent-combinatorics.partitions.mdᵉ)
ofᵉ theᵉ [cardinality](set-theory.cardinalities.mdᵉ) ofᵉ `A`.ᵉ

## Definition

### Ferrers diagrams of arbitrary types

```agda
ferrers-diagramᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
ferrers-diagramᵉ l2ᵉ l3ᵉ Aᵉ =
  Σᵉ ( UUᵉ l2ᵉ)
    ( λ Xᵉ →
      Σᵉ ( Xᵉ → UUᵉ l3ᵉ)
        ( λ Yᵉ →
          ((xᵉ : Xᵉ) → type-trunc-Propᵉ (Yᵉ xᵉ)) ×ᵉ mere-equivᵉ Aᵉ (Σᵉ Xᵉ Yᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : ferrers-diagramᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  row-ferrers-diagramᵉ : UUᵉ l2ᵉ
  row-ferrers-diagramᵉ = pr1ᵉ Dᵉ

  dot-ferrers-diagramᵉ : row-ferrers-diagramᵉ → UUᵉ l3ᵉ
  dot-ferrers-diagramᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  is-inhabited-dot-ferrers-diagramᵉ :
    (xᵉ : row-ferrers-diagramᵉ) → type-trunc-Propᵉ (dot-ferrers-diagramᵉ xᵉ)
  is-inhabited-dot-ferrers-diagramᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))

  mere-equiv-ferrers-diagramᵉ :
    mere-equivᵉ Aᵉ (Σᵉ row-ferrers-diagramᵉ dot-ferrers-diagramᵉ)
  mere-equiv-ferrers-diagramᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))
```

### Finite Ferrers diagrams of finite types

```agda
ferrers-diagram-𝔽ᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) (Aᵉ : 𝔽ᵉ l1ᵉ) → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
ferrers-diagram-𝔽ᵉ {lᵉ} l2ᵉ l3ᵉ Aᵉ =
  Σᵉ ( 𝔽ᵉ l2ᵉ)
    ( λ Xᵉ →
      Σᵉ ( type-𝔽ᵉ Xᵉ → 𝔽ᵉ l3ᵉ)
        ( λ Yᵉ →
          ((xᵉ : type-𝔽ᵉ Xᵉ) → type-trunc-Propᵉ (type-𝔽ᵉ (Yᵉ xᵉ))) ×ᵉ
          mere-equivᵉ (type-𝔽ᵉ Aᵉ) (Σᵉ (type-𝔽ᵉ Xᵉ) (λ xᵉ → type-𝔽ᵉ (Yᵉ xᵉ)))))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) (Dᵉ : ferrers-diagram-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  row-ferrers-diagram-𝔽ᵉ : 𝔽ᵉ l2ᵉ
  row-ferrers-diagram-𝔽ᵉ = pr1ᵉ Dᵉ

  type-row-ferrers-diagram-𝔽ᵉ : UUᵉ l2ᵉ
  type-row-ferrers-diagram-𝔽ᵉ = type-𝔽ᵉ row-ferrers-diagram-𝔽ᵉ

  is-finite-type-row-ferrers-diagram-𝔽ᵉ : is-finiteᵉ type-row-ferrers-diagram-𝔽ᵉ
  is-finite-type-row-ferrers-diagram-𝔽ᵉ =
    is-finite-type-𝔽ᵉ row-ferrers-diagram-𝔽ᵉ

  dot-ferrers-diagram-𝔽ᵉ : type-row-ferrers-diagram-𝔽ᵉ → 𝔽ᵉ l3ᵉ
  dot-ferrers-diagram-𝔽ᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  type-dot-ferrers-diagram-𝔽ᵉ : type-row-ferrers-diagram-𝔽ᵉ → UUᵉ l3ᵉ
  type-dot-ferrers-diagram-𝔽ᵉ xᵉ = type-𝔽ᵉ (dot-ferrers-diagram-𝔽ᵉ xᵉ)

  is-finite-type-dot-ferrers-diagram-𝔽ᵉ :
    (xᵉ : type-row-ferrers-diagram-𝔽ᵉ) → is-finiteᵉ (type-dot-ferrers-diagram-𝔽ᵉ xᵉ)
  is-finite-type-dot-ferrers-diagram-𝔽ᵉ xᵉ =
    is-finite-type-𝔽ᵉ (dot-ferrers-diagram-𝔽ᵉ xᵉ)

  is-inhabited-dot-ferrers-diagram-𝔽ᵉ :
    (xᵉ : type-row-ferrers-diagram-𝔽ᵉ) →
    type-trunc-Propᵉ (type-dot-ferrers-diagram-𝔽ᵉ xᵉ)
  is-inhabited-dot-ferrers-diagram-𝔽ᵉ = pr1ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))

  mere-equiv-ferrers-diagram-𝔽ᵉ :
    mere-equivᵉ
      ( type-𝔽ᵉ Aᵉ)
      ( Σᵉ (type-row-ferrers-diagram-𝔽ᵉ) (type-dot-ferrers-diagram-𝔽ᵉ))
  mere-equiv-ferrers-diagram-𝔽ᵉ = pr2ᵉ (pr2ᵉ (pr2ᵉ Dᵉ))

  ferrers-diagram-ferrers-diagram-𝔽ᵉ : ferrers-diagramᵉ l2ᵉ l3ᵉ (type-𝔽ᵉ Aᵉ)
  pr1ᵉ ferrers-diagram-ferrers-diagram-𝔽ᵉ = type-row-ferrers-diagram-𝔽ᵉ
  pr1ᵉ (pr2ᵉ ferrers-diagram-ferrers-diagram-𝔽ᵉ) = type-dot-ferrers-diagram-𝔽ᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ ferrers-diagram-ferrers-diagram-𝔽ᵉ)) =
    is-inhabited-dot-ferrers-diagram-𝔽ᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ ferrers-diagram-ferrers-diagram-𝔽ᵉ)) =
    mere-equiv-ferrers-diagram-𝔽ᵉ
```

### Equivalences of Ferrers diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : ferrers-diagramᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  equiv-ferrers-diagramᵉ :
    {l4ᵉ l5ᵉ : Level} (Eᵉ : ferrers-diagramᵉ l4ᵉ l5ᵉ Aᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  equiv-ferrers-diagramᵉ Eᵉ =
    Σᵉ ( row-ferrers-diagramᵉ Dᵉ ≃ᵉ row-ferrers-diagramᵉ Eᵉ)
      ( λ eᵉ →
        (xᵉ : row-ferrers-diagramᵉ Dᵉ) →
        dot-ferrers-diagramᵉ Dᵉ xᵉ ≃ᵉ dot-ferrers-diagramᵉ Eᵉ (map-equivᵉ eᵉ xᵉ))

  id-equiv-ferrers-diagramᵉ : equiv-ferrers-diagramᵉ Dᵉ
  pr1ᵉ id-equiv-ferrers-diagramᵉ = id-equivᵉ
  pr2ᵉ id-equiv-ferrers-diagramᵉ xᵉ = id-equivᵉ

  equiv-eq-ferrers-diagramᵉ :
    (Eᵉ : ferrers-diagramᵉ l2ᵉ l3ᵉ Aᵉ) → Idᵉ Dᵉ Eᵉ → equiv-ferrers-diagramᵉ Eᵉ
  equiv-eq-ferrers-diagramᵉ .Dᵉ reflᵉ = id-equiv-ferrers-diagramᵉ

  is-torsorial-equiv-ferrers-diagramᵉ :
    is-torsorialᵉ equiv-ferrers-diagramᵉ
  is-torsorial-equiv-ferrers-diagramᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (row-ferrers-diagramᵉ Dᵉ))
      ( pairᵉ (row-ferrers-diagramᵉ Dᵉ) id-equivᵉ)
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-equiv-famᵉ (dot-ferrers-diagramᵉ Dᵉ))
        ( λ Yᵉ →
          is-prop-productᵉ
            ( is-prop-Πᵉ (λ xᵉ → is-prop-type-trunc-Propᵉ))
            ( is-prop-mere-equivᵉ Aᵉ (Σᵉ (row-ferrers-diagramᵉ Dᵉ) Yᵉ)))
        ( dot-ferrers-diagramᵉ Dᵉ)
        ( λ xᵉ → id-equivᵉ)
        ( pairᵉ
          ( is-inhabited-dot-ferrers-diagramᵉ Dᵉ)
          ( mere-equiv-ferrers-diagramᵉ Dᵉ)))

  is-equiv-equiv-eq-ferrers-diagramᵉ :
    (Eᵉ : ferrers-diagramᵉ l2ᵉ l3ᵉ Aᵉ) → is-equivᵉ (equiv-eq-ferrers-diagramᵉ Eᵉ)
  is-equiv-equiv-eq-ferrers-diagramᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-ferrers-diagramᵉ
      equiv-eq-ferrers-diagramᵉ

  eq-equiv-ferrers-diagramᵉ :
    (Eᵉ : ferrers-diagramᵉ l2ᵉ l3ᵉ Aᵉ) → equiv-ferrers-diagramᵉ Eᵉ → Idᵉ Dᵉ Eᵉ
  eq-equiv-ferrers-diagramᵉ Eᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-ferrers-diagramᵉ Eᵉ)
```

### Equivalences of finite ferrers diagrams of finite types

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) (Dᵉ : ferrers-diagram-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  equiv-ferrers-diagram-𝔽ᵉ :
    {l4ᵉ l5ᵉ : Level} → ferrers-diagram-𝔽ᵉ l4ᵉ l5ᵉ Aᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
  equiv-ferrers-diagram-𝔽ᵉ Eᵉ =
    equiv-ferrers-diagramᵉ
      ( ferrers-diagram-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ)
      ( ferrers-diagram-ferrers-diagram-𝔽ᵉ Aᵉ Eᵉ)

  id-equiv-ferrers-diagram-𝔽ᵉ : equiv-ferrers-diagram-𝔽ᵉ Dᵉ
  id-equiv-ferrers-diagram-𝔽ᵉ =
    id-equiv-ferrers-diagramᵉ (ferrers-diagram-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ)

  equiv-eq-ferrers-diagram-𝔽ᵉ :
    (Eᵉ : ferrers-diagram-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ) → Idᵉ Dᵉ Eᵉ → equiv-ferrers-diagram-𝔽ᵉ Eᵉ
  equiv-eq-ferrers-diagram-𝔽ᵉ .Dᵉ reflᵉ = id-equiv-ferrers-diagram-𝔽ᵉ

  is-torsorial-equiv-ferrers-diagram-𝔽ᵉ :
    is-torsorialᵉ equiv-ferrers-diagram-𝔽ᵉ
  is-torsorial-equiv-ferrers-diagram-𝔽ᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-equivᵉ (type-row-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ))
        ( is-prop-is-finiteᵉ)
        ( type-row-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ)
        ( id-equivᵉ)
        ( is-finite-type-row-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ))
      ( pairᵉ (row-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ) id-equivᵉ)
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-Eq-Πᵉ
          ( λ xᵉ →
            is-torsorial-Eq-subtypeᵉ
              ( is-torsorial-equivᵉ (type-dot-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ xᵉ))
              ( is-prop-is-finiteᵉ)
              ( type-dot-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ xᵉ)
              ( id-equivᵉ)
              ( is-finite-type-dot-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ xᵉ)))
        ( λ xᵉ →
          is-prop-productᵉ
            ( is-prop-Πᵉ (λ xᵉ → is-prop-type-trunc-Propᵉ))
            ( is-prop-mere-equivᵉ (type-𝔽ᵉ Aᵉ) _))
        ( dot-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ)
        ( λ xᵉ → id-equivᵉ)
        ( pairᵉ
          ( is-inhabited-dot-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ)
          ( mere-equiv-ferrers-diagram-𝔽ᵉ Aᵉ Dᵉ)))

  is-equiv-equiv-eq-ferrers-diagram-𝔽ᵉ :
    (Eᵉ : ferrers-diagram-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ) → is-equivᵉ (equiv-eq-ferrers-diagram-𝔽ᵉ Eᵉ)
  is-equiv-equiv-eq-ferrers-diagram-𝔽ᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-ferrers-diagram-𝔽ᵉ
      equiv-eq-ferrers-diagram-𝔽ᵉ

  eq-equiv-ferrers-diagram-𝔽ᵉ :
    (Eᵉ : ferrers-diagram-𝔽ᵉ l2ᵉ l3ᵉ Aᵉ) → equiv-ferrers-diagram-𝔽ᵉ Eᵉ → Idᵉ Dᵉ Eᵉ
  eq-equiv-ferrers-diagram-𝔽ᵉ Eᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-ferrers-diagram-𝔽ᵉ Eᵉ)
```

## Properties

### The type of Ferrers diagrams of any finite type is π-finite

Thisᵉ remainsᵉ to beᵉ shown.ᵉ
[#746](https://github.com/UniMath/agda-unimath/issues/746ᵉ)

## See also

-ᵉ Integerᵉ partitionsᵉ in
  [`elementary-number-theory.integer-partitions`](elementary-number-theory.integer-partitions.mdᵉ)