# Functional correspondences

```agda
module foundation.functional-correspondencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ functionalᵉ dependentᵉ correspondenceᵉ isᵉ aᵉ dependentᵉ binaryᵉ correspondenceᵉ
`Cᵉ : Πᵉ (aᵉ : Aᵉ) → Bᵉ aᵉ → 𝒰`ᵉ fromᵉ aᵉ typeᵉ `A`ᵉ to aᵉ typeᵉ familyᵉ `B`ᵉ overᵉ `A`ᵉ suchᵉ
thatᵉ forᵉ everyᵉ `aᵉ : A`ᵉ theᵉ typeᵉ `Σᵉ (bᵉ : Bᵉ a),ᵉ Cᵉ aᵉ b`ᵉ isᵉ contractible.ᵉ Theᵉ typeᵉ
ofᵉ dependentᵉ functionsᵉ fromᵉ `A`ᵉ to `B`ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ functionalᵉ
dependentᵉ correspondences.ᵉ

## Definition

```agda
is-functional-correspondence-Propᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ → UUᵉ l3ᵉ) →
  Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-functional-correspondence-Propᵉ {Aᵉ = Aᵉ} {Bᵉ} Cᵉ =
  Π-Propᵉ Aᵉ (λ xᵉ → is-contr-Propᵉ (Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ)))

is-functional-correspondenceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ → UUᵉ l3ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
is-functional-correspondenceᵉ Cᵉ =
  type-Propᵉ (is-functional-correspondence-Propᵉ Cᵉ)

is-prop-is-functional-correspondenceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (Cᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ → UUᵉ l3ᵉ) →
  is-propᵉ (is-functional-correspondenceᵉ Cᵉ)
is-prop-is-functional-correspondenceᵉ Cᵉ =
  is-prop-type-Propᵉ (is-functional-correspondence-Propᵉ Cᵉ)

functional-correspondenceᵉ :
  {l1ᵉ l2ᵉ : Level} (l3ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Aᵉ → UUᵉ l2ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ =
  type-subtypeᵉ (is-functional-correspondence-Propᵉ {l3ᵉ = l3ᵉ} {Aᵉ} {Bᵉ})

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Cᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ)
  where

  correspondence-functional-correspondenceᵉ :
    (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ
  correspondence-functional-correspondenceᵉ = pr1ᵉ Cᵉ

  is-functional-functional-correspondenceᵉ :
    is-functional-correspondenceᵉ
      correspondence-functional-correspondenceᵉ
  is-functional-functional-correspondenceᵉ =
    pr2ᵉ Cᵉ
```

## Properties

### Characterization of equality in the type of functional dependent correspondences

```agda
equiv-functional-correspondenceᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Cᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ)
  (Dᵉ : functional-correspondenceᵉ l4ᵉ Aᵉ Bᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
equiv-functional-correspondenceᵉ {Aᵉ = Aᵉ} {Bᵉ} Cᵉ Dᵉ =
  (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) →
  correspondence-functional-correspondenceᵉ Cᵉ xᵉ yᵉ ≃ᵉ
  correspondence-functional-correspondenceᵉ Dᵉ xᵉ yᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (Cᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ)
  where

  id-equiv-functional-correspondenceᵉ :
    equiv-functional-correspondenceᵉ Cᵉ Cᵉ
  id-equiv-functional-correspondenceᵉ xᵉ yᵉ = id-equivᵉ

  is-torsorial-equiv-functional-correspondenceᵉ :
    is-torsorialᵉ (equiv-functional-correspondenceᵉ Cᵉ)
  is-torsorial-equiv-functional-correspondenceᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-Eq-Πᵉ
        ( λ xᵉ →
          is-torsorial-equiv-famᵉ
            ( correspondence-functional-correspondenceᵉ
              Cᵉ xᵉ)))
      ( is-prop-is-functional-correspondenceᵉ)
      ( correspondence-functional-correspondenceᵉ Cᵉ)
      ( id-equiv-functional-correspondenceᵉ)
      ( is-functional-functional-correspondenceᵉ Cᵉ)

  equiv-eq-functional-correspondenceᵉ :
    (Dᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ) →
    (Cᵉ ＝ᵉ Dᵉ) → equiv-functional-correspondenceᵉ Cᵉ Dᵉ
  equiv-eq-functional-correspondenceᵉ .Cᵉ reflᵉ =
    id-equiv-functional-correspondenceᵉ

  is-equiv-equiv-eq-functional-correspondenceᵉ :
    (Dᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ) →
    is-equivᵉ (equiv-eq-functional-correspondenceᵉ Dᵉ)
  is-equiv-equiv-eq-functional-correspondenceᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-functional-correspondenceᵉ
      equiv-eq-functional-correspondenceᵉ

  extensionality-functional-correspondenceᵉ :
    (Dᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ) →
    (Cᵉ ＝ᵉ Dᵉ) ≃ᵉ equiv-functional-correspondenceᵉ Cᵉ Dᵉ
  pr1ᵉ (extensionality-functional-correspondenceᵉ Dᵉ) =
    equiv-eq-functional-correspondenceᵉ Dᵉ
  pr2ᵉ (extensionality-functional-correspondenceᵉ Dᵉ) =
    is-equiv-equiv-eq-functional-correspondenceᵉ Dᵉ

  eq-equiv-functional-correspondenceᵉ :
    (Dᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ) →
    equiv-functional-correspondenceᵉ Cᵉ Dᵉ → Cᵉ ＝ᵉ Dᵉ
  eq-equiv-functional-correspondenceᵉ Dᵉ =
    map-inv-equivᵉ (extensionality-functional-correspondenceᵉ Dᵉ)
```

### The type of dependent functions `(x : A) → B x` is equivalent to the type of functional dependent correspondences from `A` to `B`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  functional-correspondence-functionᵉ :
    ((xᵉ : Aᵉ) → Bᵉ xᵉ) → functional-correspondenceᵉ l2ᵉ Aᵉ Bᵉ
  pr1ᵉ (functional-correspondence-functionᵉ fᵉ) xᵉ yᵉ = fᵉ xᵉ ＝ᵉ yᵉ
  pr2ᵉ (functional-correspondence-functionᵉ fᵉ) xᵉ =
    is-torsorial-Idᵉ (fᵉ xᵉ)

  function-functional-correspondenceᵉ :
    {l3ᵉ : Level} → functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ → ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  function-functional-correspondenceᵉ Cᵉ xᵉ =
    pr1ᵉ (centerᵉ (is-functional-functional-correspondenceᵉ Cᵉ xᵉ))

  is-retraction-function-functional-correspondenceᵉ :
    (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    function-functional-correspondenceᵉ
      ( functional-correspondence-functionᵉ fᵉ) ＝ᵉ fᵉ
  is-retraction-function-functional-correspondenceᵉ fᵉ =
    eq-htpyᵉ
      ( λ xᵉ →
        apᵉ pr1ᵉ
          ( contractionᵉ
            ( is-functional-functional-correspondenceᵉ
              ( functional-correspondence-functionᵉ fᵉ)
              ( xᵉ))
            ( fᵉ xᵉ ,ᵉ reflᵉ)))

  module _
    {l3ᵉ : Level} (Cᵉ : functional-correspondenceᵉ l3ᵉ Aᵉ Bᵉ)
    where

    map-is-section-function-functional-correspondenceᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) →
      function-functional-correspondenceᵉ Cᵉ xᵉ ＝ᵉ yᵉ →
      correspondence-functional-correspondenceᵉ Cᵉ xᵉ yᵉ
    map-is-section-function-functional-correspondenceᵉ xᵉ ._ reflᵉ =
      pr2ᵉ ( centerᵉ (is-functional-functional-correspondenceᵉ Cᵉ xᵉ))

    is-equiv-map-is-section-function-functional-correspondenceᵉ :
      (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) →
      is-equivᵉ (map-is-section-function-functional-correspondenceᵉ xᵉ yᵉ)
    is-equiv-map-is-section-function-functional-correspondenceᵉ
      xᵉ =
      fundamental-theorem-idᵉ
        ( is-functional-functional-correspondenceᵉ Cᵉ xᵉ)
        ( map-is-section-function-functional-correspondenceᵉ xᵉ)

    equiv-is-section-function-functional-correspondenceᵉ :
      equiv-functional-correspondenceᵉ
        ( functional-correspondence-functionᵉ
          ( function-functional-correspondenceᵉ Cᵉ))
        ( Cᵉ)
    pr1ᵉ ( equiv-is-section-function-functional-correspondenceᵉ xᵉ yᵉ) =
      map-is-section-function-functional-correspondenceᵉ xᵉ yᵉ
    pr2ᵉ (equiv-is-section-function-functional-correspondenceᵉ xᵉ yᵉ) =
      is-equiv-map-is-section-function-functional-correspondenceᵉ xᵉ yᵉ

  is-section-function-functional-correspondenceᵉ :
    (Cᵉ : functional-correspondenceᵉ l2ᵉ Aᵉ Bᵉ) →
    functional-correspondence-functionᵉ (function-functional-correspondenceᵉ Cᵉ) ＝ᵉ
    Cᵉ
  is-section-function-functional-correspondenceᵉ Cᵉ =
    eq-equiv-functional-correspondenceᵉ
      ( functional-correspondence-functionᵉ
        ( function-functional-correspondenceᵉ Cᵉ))
      ( Cᵉ)
      ( equiv-is-section-function-functional-correspondenceᵉ Cᵉ)

  is-equiv-functional-correspondence-functionᵉ :
    is-equivᵉ functional-correspondence-functionᵉ
  is-equiv-functional-correspondence-functionᵉ =
    is-equiv-is-invertibleᵉ
      function-functional-correspondenceᵉ
      is-section-function-functional-correspondenceᵉ
      is-retraction-function-functional-correspondenceᵉ

  equiv-functional-correspondence-functionᵉ :
    ((xᵉ : Aᵉ) → Bᵉ xᵉ) ≃ᵉ functional-correspondenceᵉ l2ᵉ Aᵉ Bᵉ
  pr1ᵉ equiv-functional-correspondence-functionᵉ =
    functional-correspondence-functionᵉ
  pr2ᵉ equiv-functional-correspondence-functionᵉ =
    is-equiv-functional-correspondence-functionᵉ
```