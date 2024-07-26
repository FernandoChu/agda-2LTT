# Truncations

```agda
module foundation.truncationsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.truncated-typesᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.truncation-levelsᵉ
open import foundation-core.universal-property-truncationᵉ
```

</details>

## Idea

Weᵉ postulate theᵉ existenceᵉ ofᵉ truncations.ᵉ

## Postulates

```agda
postulate
  type-truncᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ lᵉ → UUᵉ lᵉ

postulate
  is-trunc-type-truncᵉ :
    {lᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ lᵉ} → is-truncᵉ kᵉ (type-truncᵉ kᵉ Aᵉ)

truncᵉ : {lᵉ : Level} (kᵉ : 𝕋ᵉ) → UUᵉ lᵉ → Truncated-Typeᵉ lᵉ kᵉ
pr1ᵉ (truncᵉ kᵉ Aᵉ) = type-truncᵉ kᵉ Aᵉ
pr2ᵉ (truncᵉ kᵉ Aᵉ) = is-trunc-type-truncᵉ

postulate
  unit-truncᵉ : {lᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ lᵉ} → Aᵉ → type-truncᵉ kᵉ Aᵉ

postulate
  is-truncation-truncᵉ :
    {lᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ lᵉ} →
    is-truncationᵉ (truncᵉ kᵉ Aᵉ) unit-truncᵉ

equiv-universal-property-truncᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) →
  (type-truncᵉ kᵉ Aᵉ → type-Truncated-Typeᵉ Bᵉ) ≃ᵉ (Aᵉ → type-Truncated-Typeᵉ Bᵉ)
pr1ᵉ (equiv-universal-property-truncᵉ Aᵉ Bᵉ) = precomp-Truncᵉ unit-truncᵉ Bᵉ
pr2ᵉ (equiv-universal-property-truncᵉ Aᵉ Bᵉ) = is-truncation-truncᵉ Bᵉ
```

## Properties

### The `n`-truncations satisfy the universal property of `n`-truncations

```agda
universal-property-truncᵉ :
  {l1ᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ l1ᵉ) →
  universal-property-truncationᵉ (truncᵉ kᵉ Aᵉ) unit-truncᵉ
universal-property-truncᵉ kᵉ Aᵉ =
  universal-property-truncation-is-truncationᵉ
    ( truncᵉ kᵉ Aᵉ)
    ( unit-truncᵉ)
    ( is-truncation-truncᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  where

  apply-universal-property-truncᵉ :
    (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ) →
    Σᵉ ( type-truncᵉ kᵉ Aᵉ → type-Truncated-Typeᵉ Bᵉ)
      ( λ hᵉ → hᵉ ∘ᵉ unit-truncᵉ ~ᵉ fᵉ)
  apply-universal-property-truncᵉ Bᵉ fᵉ =
    centerᵉ
      ( universal-property-truncation-is-truncationᵉ
        ( truncᵉ kᵉ Aᵉ)
        ( unit-truncᵉ)
        ( is-truncation-truncᵉ)
        ( Bᵉ)
        ( fᵉ))

  map-universal-property-truncᵉ :
    (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) → (Aᵉ → type-Truncated-Typeᵉ Bᵉ) →
    type-truncᵉ kᵉ Aᵉ → type-Truncated-Typeᵉ Bᵉ
  map-universal-property-truncᵉ Bᵉ fᵉ =
    pr1ᵉ (apply-universal-property-truncᵉ Bᵉ fᵉ)

  triangle-universal-property-truncᵉ :
    (Bᵉ : Truncated-Typeᵉ l2ᵉ kᵉ) (fᵉ : Aᵉ → type-Truncated-Typeᵉ Bᵉ) →
    map-universal-property-truncᵉ Bᵉ fᵉ ∘ᵉ unit-truncᵉ ~ᵉ fᵉ
  triangle-universal-property-truncᵉ Bᵉ fᵉ =
    pr2ᵉ (apply-universal-property-truncᵉ Bᵉ fᵉ)
```

### The `n`-truncations satisfy the dependent universal property of `n`-truncations

```agda
module _
  {l1ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ}
  where

  dependent-universal-property-truncᵉ :
    dependent-universal-property-truncationᵉ (truncᵉ kᵉ Aᵉ) unit-truncᵉ
  dependent-universal-property-truncᵉ =
    dependent-universal-property-truncation-is-truncationᵉ
      ( truncᵉ kᵉ Aᵉ)
      ( unit-truncᵉ)
      ( is-truncation-truncᵉ)

  equiv-dependent-universal-property-truncᵉ :
    {l2ᵉ : Level} (Bᵉ : type-truncᵉ kᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
    ((xᵉ : type-truncᵉ kᵉ Aᵉ) → type-Truncated-Typeᵉ (Bᵉ xᵉ)) ≃ᵉ
    ((aᵉ : Aᵉ) → type-Truncated-Typeᵉ (Bᵉ (unit-truncᵉ aᵉ)))
  pr1ᵉ (equiv-dependent-universal-property-truncᵉ Bᵉ) =
    precomp-Π-Truncated-Typeᵉ unit-truncᵉ Bᵉ
  pr2ᵉ (equiv-dependent-universal-property-truncᵉ Bᵉ) =
    dependent-universal-property-truncᵉ Bᵉ

  unique-dependent-function-truncᵉ :
    {l2ᵉ : Level} (Bᵉ : type-truncᵉ kᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ)
    (fᵉ : (xᵉ : Aᵉ) → type-Truncated-Typeᵉ (Bᵉ (unit-truncᵉ xᵉ))) →
    is-contrᵉ
      ( Σᵉ ( (xᵉ : type-truncᵉ kᵉ Aᵉ) → type-Truncated-Typeᵉ (Bᵉ xᵉ))
          ( λ hᵉ → (hᵉ ∘ᵉ unit-truncᵉ) ~ᵉ fᵉ))
  unique-dependent-function-truncᵉ Bᵉ fᵉ =
    is-contr-equiv'ᵉ
      ( fiberᵉ (precomp-Π-Truncated-Typeᵉ unit-truncᵉ Bᵉ) fᵉ)
      ( equiv-totᵉ
        ( λ hᵉ → equiv-funextᵉ))
      ( is-contr-map-is-equivᵉ
        ( dependent-universal-property-truncᵉ Bᵉ)
        ( fᵉ))

  apply-dependent-universal-property-truncᵉ :
    {l2ᵉ : Level} (Bᵉ : type-truncᵉ kᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
    (fᵉ : (xᵉ : Aᵉ) → type-Truncated-Typeᵉ (Bᵉ (unit-truncᵉ xᵉ))) →
    Σᵉ ( (xᵉ : type-truncᵉ kᵉ Aᵉ) → type-Truncated-Typeᵉ (Bᵉ xᵉ))
      ( λ hᵉ → (hᵉ ∘ᵉ unit-truncᵉ) ~ᵉ fᵉ)
  apply-dependent-universal-property-truncᵉ Bᵉ fᵉ =
    centerᵉ (unique-dependent-function-truncᵉ Bᵉ fᵉ)

  function-dependent-universal-property-truncᵉ :
    {l2ᵉ : Level} (Bᵉ : type-truncᵉ kᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
    (fᵉ : (xᵉ : Aᵉ) → type-Truncated-Typeᵉ (Bᵉ (unit-truncᵉ xᵉ))) →
    (xᵉ : type-truncᵉ kᵉ Aᵉ) → type-Truncated-Typeᵉ (Bᵉ xᵉ)
  function-dependent-universal-property-truncᵉ Bᵉ fᵉ =
    pr1ᵉ (apply-dependent-universal-property-truncᵉ Bᵉ fᵉ)

  htpy-dependent-universal-property-truncᵉ :
    {l2ᵉ : Level} (Bᵉ : type-truncᵉ kᵉ Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
    (fᵉ : (xᵉ : Aᵉ) → type-Truncated-Typeᵉ (Bᵉ (unit-truncᵉ xᵉ))) →
    ( function-dependent-universal-property-truncᵉ Bᵉ fᵉ ∘ᵉ unit-truncᵉ) ~ᵉ fᵉ
  htpy-dependent-universal-property-truncᵉ Bᵉ fᵉ =
    pr2ᵉ (apply-dependent-universal-property-truncᵉ Bᵉ fᵉ)
```

### Families of `k`-truncated-types over `k+1`-truncations of types

```agda
unique-truncated-fam-truncᵉ :
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} →
  (Bᵉ : Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ) →
  is-contrᵉ
    ( Σᵉ ( type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ)
        ( λ Cᵉ → (xᵉ : Aᵉ) → type-equiv-Truncated-Typeᵉ (Bᵉ xᵉ) (Cᵉ (unit-truncᵉ xᵉ))))
unique-truncated-fam-truncᵉ {l1ᵉ} {l2ᵉ} {kᵉ} {Aᵉ} Bᵉ =
  is-contr-equiv'ᵉ
    ( Σᵉ ( type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ)
        ( λ Cᵉ → (Cᵉ ∘ᵉ unit-truncᵉ) ~ᵉ Bᵉ))
    ( equiv-totᵉ
      ( λ Cᵉ →
        equiv-Π-equiv-familyᵉ
          ( λ xᵉ →
            ( extensionality-Truncated-Typeᵉ (Bᵉ xᵉ) (Cᵉ (unit-truncᵉ xᵉ))) ∘eᵉ
            ( equiv-invᵉ (Cᵉ (unit-truncᵉ xᵉ)) (Bᵉ xᵉ)))))
    ( universal-property-truncᵉ
      ( succ-𝕋ᵉ kᵉ)
      ( Aᵉ)
      ( Truncated-Type-Truncated-Typeᵉ l2ᵉ kᵉ)
      ( Bᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ)
  where

  truncated-fam-truncᵉ : type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ
  truncated-fam-truncᵉ =
    pr1ᵉ (centerᵉ (unique-truncated-fam-truncᵉ Bᵉ))

  fam-truncᵉ : type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → UUᵉ l2ᵉ
  fam-truncᵉ = type-Truncated-Typeᵉ ∘ᵉ truncated-fam-truncᵉ

  compute-truncated-fam-truncᵉ :
    (xᵉ : Aᵉ) →
    type-equiv-Truncated-Typeᵉ (Bᵉ xᵉ) (truncated-fam-truncᵉ (unit-truncᵉ xᵉ))
  compute-truncated-fam-truncᵉ =
    pr2ᵉ (centerᵉ (unique-truncated-fam-truncᵉ Bᵉ))

  map-compute-truncated-fam-truncᵉ :
    (xᵉ : Aᵉ) → type-Truncated-Typeᵉ (Bᵉ xᵉ) → (fam-truncᵉ (unit-truncᵉ xᵉ))
  map-compute-truncated-fam-truncᵉ xᵉ =
    map-equivᵉ (compute-truncated-fam-truncᵉ xᵉ)

  total-truncated-fam-truncᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  total-truncated-fam-truncᵉ = Σᵉ (type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ) fam-truncᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {kᵉ : 𝕋ᵉ} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → Truncated-Typeᵉ l2ᵉ kᵉ)
  ( Cᵉ : total-truncated-fam-truncᵉ Bᵉ → Truncated-Typeᵉ l3ᵉ kᵉ)
  ( fᵉ :
    ( xᵉ : Aᵉ)
    ( yᵉ : type-Truncated-Typeᵉ (Bᵉ xᵉ)) →
    type-Truncated-Typeᵉ
      ( Cᵉ (unit-truncᵉ xᵉ ,ᵉ map-equivᵉ (compute-truncated-fam-truncᵉ Bᵉ xᵉ) yᵉ)))
  where

  dependent-universal-property-total-truncated-fam-truncᵉ :
    is-contrᵉ
      ( Σᵉ ( (tᵉ : total-truncated-fam-truncᵉ Bᵉ) → type-Truncated-Typeᵉ (Cᵉ tᵉ))
          ( λ hᵉ →
            (xᵉ : Aᵉ) (yᵉ : type-Truncated-Typeᵉ (Bᵉ xᵉ)) →
            Idᵉ
              ( hᵉ (unit-truncᵉ xᵉ ,ᵉ map-compute-truncated-fam-truncᵉ Bᵉ xᵉ yᵉ))
              ( fᵉ xᵉ yᵉ)))
  dependent-universal-property-total-truncated-fam-truncᵉ =
    is-contr-equivᵉ _
      ( equiv-Σᵉ
        ( λ gᵉ →
          (xᵉ : Aᵉ) →
          Idᵉ
            ( gᵉ (unit-truncᵉ xᵉ))
            ( map-equiv-Πᵉ
              ( λ uᵉ → type-Truncated-Typeᵉ (Cᵉ (unit-truncᵉ xᵉ ,ᵉ uᵉ)))
              ( compute-truncated-fam-truncᵉ Bᵉ xᵉ)
              ( λ uᵉ → id-equivᵉ)
              ( fᵉ xᵉ)))
        ( equiv-ev-pairᵉ)
        ( λ gᵉ →
          equiv-Π-equiv-familyᵉ
            ( λ xᵉ →
              ( inv-equivᵉ equiv-funextᵉ) ∘eᵉ
              ( equiv-Πᵉ
                ( λ yᵉ →
                  Idᵉ
                    ( gᵉ (unit-truncᵉ xᵉ ,ᵉ yᵉ))
                    ( map-equiv-Πᵉ
                      ( λ uᵉ →
                        type-Truncated-Typeᵉ (Cᵉ (unit-truncᵉ xᵉ ,ᵉ uᵉ)))
                      ( compute-truncated-fam-truncᵉ Bᵉ xᵉ)
                      ( λ uᵉ → id-equivᵉ)
                      ( fᵉ xᵉ)
                      ( yᵉ)))
                ( compute-truncated-fam-truncᵉ Bᵉ xᵉ)
                ( λ yᵉ →
                  equiv-concat'ᵉ
                    ( gᵉ (unit-truncᵉ xᵉ ,ᵉ map-compute-truncated-fam-truncᵉ Bᵉ xᵉ yᵉ))
                    ( invᵉ
                      ( compute-map-equiv-Πᵉ
                        ( λ uᵉ → type-Truncated-Typeᵉ (Cᵉ (unit-truncᵉ xᵉ ,ᵉ uᵉ)))
                        ( compute-truncated-fam-truncᵉ Bᵉ xᵉ)
                        ( λ yᵉ → id-equivᵉ)
                        ( fᵉ xᵉ)
                        ( yᵉ))))))))
      ( unique-dependent-function-truncᵉ
        ( λ yᵉ →
          truncated-type-succ-Truncated-Typeᵉ kᵉ
            ( Π-Truncated-Typeᵉ kᵉ
              ( truncated-fam-truncᵉ Bᵉ yᵉ)
              ( λ uᵉ → Cᵉ (yᵉ ,ᵉ uᵉ))))
        ( λ yᵉ →
          map-equiv-Πᵉ
            ( λ uᵉ → type-Truncated-Typeᵉ (Cᵉ (unit-truncᵉ yᵉ ,ᵉ uᵉ)))
            ( compute-truncated-fam-truncᵉ Bᵉ yᵉ)
            ( λ uᵉ → id-equivᵉ)
            ( fᵉ yᵉ)))

  function-dependent-universal-property-total-truncated-fam-truncᵉ :
    (tᵉ : total-truncated-fam-truncᵉ Bᵉ) → type-Truncated-Typeᵉ (Cᵉ tᵉ)
  function-dependent-universal-property-total-truncated-fam-truncᵉ =
    pr1ᵉ (centerᵉ dependent-universal-property-total-truncated-fam-truncᵉ)

  htpy-dependent-universal-property-total-truncated-fam-truncᵉ :
    (xᵉ : Aᵉ) (yᵉ : type-Truncated-Typeᵉ (Bᵉ xᵉ)) →
    Idᵉ
      ( function-dependent-universal-property-total-truncated-fam-truncᵉ
        ( unit-truncᵉ xᵉ ,ᵉ map-compute-truncated-fam-truncᵉ Bᵉ xᵉ yᵉ))
      ( fᵉ xᵉ yᵉ)
  htpy-dependent-universal-property-total-truncated-fam-truncᵉ =
    pr2ᵉ (centerᵉ dependent-universal-property-total-truncated-fam-truncᵉ)
```

### An `n`-truncated type is equivalent to its `n`-truncation

```agda
module _
  {lᵉ : Level} {kᵉ : 𝕋ᵉ} (Aᵉ : Truncated-Typeᵉ lᵉ kᵉ)
  where

  map-inv-unit-truncᵉ :
    type-truncᵉ kᵉ (type-Truncated-Typeᵉ Aᵉ) → type-Truncated-Typeᵉ Aᵉ
  map-inv-unit-truncᵉ = map-universal-property-truncᵉ Aᵉ idᵉ

  is-retraction-map-inv-unit-truncᵉ :
    ( map-inv-unit-truncᵉ ∘ᵉ unit-truncᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-unit-truncᵉ = triangle-universal-property-truncᵉ Aᵉ idᵉ

  is-section-map-inv-unit-truncᵉ :
    ( unit-truncᵉ ∘ᵉ map-inv-unit-truncᵉ) ~ᵉ idᵉ
  is-section-map-inv-unit-truncᵉ =
    htpy-eqᵉ
      ( pr1ᵉ
        ( pair-eq-Σᵉ
          ( eq-is-prop'ᵉ
            ( is-trunc-succ-is-truncᵉ
              ( neg-two-𝕋ᵉ)
              ( universal-property-truncᵉ
                ( kᵉ)
                ( type-Truncated-Typeᵉ Aᵉ)
                ( truncᵉ kᵉ (type-Truncated-Typeᵉ Aᵉ))
                ( unit-truncᵉ)))
            ( unit-truncᵉ ∘ᵉ map-inv-unit-truncᵉ ,ᵉ
              unit-truncᵉ ·lᵉ is-retraction-map-inv-unit-truncᵉ)
            ( idᵉ ,ᵉ refl-htpyᵉ))))

  is-equiv-unit-truncᵉ : is-equivᵉ unit-truncᵉ
  is-equiv-unit-truncᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-unit-truncᵉ
      is-section-map-inv-unit-truncᵉ
      is-retraction-map-inv-unit-truncᵉ

  equiv-unit-truncᵉ :
    type-Truncated-Typeᵉ Aᵉ ≃ᵉ type-truncᵉ kᵉ (type-Truncated-Typeᵉ Aᵉ)
  pr1ᵉ equiv-unit-truncᵉ = unit-truncᵉ
  pr2ᵉ equiv-unit-truncᵉ = is-equiv-unit-truncᵉ
```

### A contractible type is equivalent to its `k`-truncation

```agda
module _
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ lᵉ)
  where

  is-equiv-unit-trunc-is-contrᵉ : is-contrᵉ Aᵉ → is-equivᵉ unit-truncᵉ
  is-equiv-unit-trunc-is-contrᵉ cᵉ =
    is-equiv-unit-truncᵉ (Aᵉ ,ᵉ is-trunc-is-contrᵉ kᵉ cᵉ)
```

### Truncation is idempotent

```agda
module _
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) (Aᵉ : UUᵉ lᵉ)
  where

  idempotent-truncᵉ : type-truncᵉ kᵉ (type-truncᵉ kᵉ Aᵉ) ≃ᵉ type-truncᵉ kᵉ Aᵉ
  idempotent-truncᵉ = inv-equivᵉ (equiv-unit-truncᵉ (truncᵉ kᵉ Aᵉ))
```

### Characterization of the identity types of truncations

```agda
module _
  {lᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ lᵉ} (aᵉ : Aᵉ)
  where

  Eq-trunc-Truncated-Typeᵉ : type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → Truncated-Typeᵉ lᵉ kᵉ
  Eq-trunc-Truncated-Typeᵉ = truncated-fam-truncᵉ (λ yᵉ → truncᵉ kᵉ (aᵉ ＝ᵉ yᵉ))

  Eq-truncᵉ : type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ → UUᵉ lᵉ
  Eq-truncᵉ xᵉ = type-Truncated-Typeᵉ (Eq-trunc-Truncated-Typeᵉ xᵉ)

  compute-Eq-truncᵉ : (xᵉ : Aᵉ) → type-truncᵉ kᵉ (aᵉ ＝ᵉ xᵉ) ≃ᵉ Eq-truncᵉ (unit-truncᵉ xᵉ)
  compute-Eq-truncᵉ = compute-truncated-fam-truncᵉ (λ yᵉ → truncᵉ kᵉ (aᵉ ＝ᵉ yᵉ))

  map-compute-Eq-truncᵉ :
    (xᵉ : Aᵉ) → type-truncᵉ kᵉ (aᵉ ＝ᵉ xᵉ) → Eq-truncᵉ (unit-truncᵉ xᵉ)
  map-compute-Eq-truncᵉ xᵉ = map-equivᵉ (compute-Eq-truncᵉ xᵉ)

  refl-Eq-truncᵉ : Eq-truncᵉ (unit-truncᵉ aᵉ)
  refl-Eq-truncᵉ = map-compute-Eq-truncᵉ aᵉ (unit-truncᵉ reflᵉ)

  refl-compute-Eq-truncᵉ :
    map-compute-Eq-truncᵉ aᵉ (unit-truncᵉ reflᵉ) ＝ᵉ refl-Eq-truncᵉ
  refl-compute-Eq-truncᵉ = reflᵉ

  is-torsorial-Eq-truncᵉ : is-torsorialᵉ Eq-truncᵉ
  pr1ᵉ (pr1ᵉ is-torsorial-Eq-truncᵉ) = unit-truncᵉ aᵉ
  pr2ᵉ (pr1ᵉ is-torsorial-Eq-truncᵉ) = refl-Eq-truncᵉ
  pr2ᵉ is-torsorial-Eq-truncᵉ =
    function-dependent-universal-property-total-truncated-fam-truncᵉ
      ( λ yᵉ → truncᵉ kᵉ (aᵉ ＝ᵉ yᵉ))
      ( Id-Truncated-Typeᵉ
          ( Σ-Truncated-Typeᵉ
            ( truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ)
            ( λ bᵉ →
              truncated-type-succ-Truncated-Typeᵉ kᵉ
                ( Eq-trunc-Truncated-Typeᵉ bᵉ)))
          ( unit-truncᵉ aᵉ ,ᵉ refl-Eq-truncᵉ))
      ( λ yᵉ →
        function-dependent-universal-property-truncᵉ
          ( λ qᵉ →
            Id-Truncated-Typeᵉ
              ( Σ-Truncated-Typeᵉ
                ( truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ)
                ( λ yᵉ →
                  truncated-type-succ-Truncated-Typeᵉ kᵉ
                    ( Eq-trunc-Truncated-Typeᵉ yᵉ)))
              ( unit-truncᵉ aᵉ ,ᵉ refl-Eq-truncᵉ)
              ( unit-truncᵉ yᵉ ,ᵉ map-compute-Eq-truncᵉ yᵉ qᵉ))
          ( rᵉ yᵉ))
    where
    rᵉ :
      (yᵉ : Aᵉ) (pᵉ : aᵉ ＝ᵉ yᵉ) →
      Idᵉ
        { Aᵉ = Σᵉ (type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ) Eq-truncᵉ}
        ( unit-truncᵉ aᵉ ,ᵉ refl-Eq-truncᵉ)
        ( unit-truncᵉ yᵉ ,ᵉ (map-compute-Eq-truncᵉ yᵉ (unit-truncᵉ pᵉ)))
    rᵉ .aᵉ reflᵉ = reflᵉ

  Eq-eq-truncᵉ : (xᵉ : type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ) → (unit-truncᵉ aᵉ ＝ᵉ xᵉ) → Eq-truncᵉ xᵉ
  Eq-eq-truncᵉ .(unit-truncᵉ aᵉ) reflᵉ = refl-Eq-truncᵉ

  is-equiv-Eq-eq-truncᵉ :
    (xᵉ : type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ) → is-equivᵉ (Eq-eq-truncᵉ xᵉ)
  is-equiv-Eq-eq-truncᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-Eq-truncᵉ)
      ( Eq-eq-truncᵉ)

  extensionality-truncᵉ :
    (xᵉ : type-truncᵉ (succ-𝕋ᵉ kᵉ) Aᵉ) → (unit-truncᵉ aᵉ ＝ᵉ xᵉ) ≃ᵉ Eq-truncᵉ xᵉ
  pr1ᵉ (extensionality-truncᵉ xᵉ) = Eq-eq-truncᵉ xᵉ
  pr2ᵉ (extensionality-truncᵉ xᵉ) = is-equiv-Eq-eq-truncᵉ xᵉ

  effectiveness-truncᵉ :
    (xᵉ : Aᵉ) →
    type-truncᵉ kᵉ (aᵉ ＝ᵉ xᵉ) ≃ᵉ (unit-truncᵉ {kᵉ = succ-𝕋ᵉ kᵉ} aᵉ ＝ᵉ unit-truncᵉ xᵉ)
  effectiveness-truncᵉ xᵉ =
    inv-equivᵉ (extensionality-truncᵉ (unit-truncᵉ xᵉ)) ∘eᵉ compute-Eq-truncᵉ xᵉ

  map-effectiveness-truncᵉ :
    (xᵉ : Aᵉ) →
    type-truncᵉ kᵉ (aᵉ ＝ᵉ xᵉ) → (unit-truncᵉ {kᵉ = succ-𝕋ᵉ kᵉ} aᵉ ＝ᵉ unit-truncᵉ xᵉ)
  map-effectiveness-truncᵉ xᵉ = map-equivᵉ (effectiveness-truncᵉ xᵉ)

  refl-effectiveness-truncᵉ :
    map-effectiveness-truncᵉ aᵉ (unit-truncᵉ reflᵉ) ＝ᵉ reflᵉ
  refl-effectiveness-truncᵉ =
    is-retraction-map-inv-equivᵉ (extensionality-truncᵉ (unit-truncᵉ aᵉ)) reflᵉ
```

### Truncations of Σ-types

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  map-trunc-Σᵉ :
    type-truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ) → type-truncᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → type-truncᵉ kᵉ (Bᵉ xᵉ)))
  map-trunc-Σᵉ =
    map-universal-property-truncᵉ
      ( truncᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → type-truncᵉ kᵉ (Bᵉ xᵉ))))
      ( λ (aᵉ ,ᵉ bᵉ) → unit-truncᵉ (aᵉ ,ᵉ unit-truncᵉ bᵉ))

  map-inv-trunc-Σᵉ :
    type-truncᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → type-truncᵉ kᵉ (Bᵉ xᵉ))) → type-truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ)
  map-inv-trunc-Σᵉ =
    map-universal-property-truncᵉ
      ( truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ))
      ( λ (aᵉ ,ᵉ |b|ᵉ) →
        map-universal-property-truncᵉ
          ( truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ))
          ( λ bᵉ → unit-truncᵉ (aᵉ ,ᵉ bᵉ))
          ( |b|ᵉ))

  is-retraction-map-inv-trunc-Σᵉ :
    ( map-inv-trunc-Σᵉ ∘ᵉ map-trunc-Σᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-trunc-Σᵉ =
    function-dependent-universal-property-truncᵉ
      ( λ |ab|ᵉ →
        Id-Truncated-Type'ᵉ
          ( truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ))
          ( map-inv-trunc-Σᵉ (map-trunc-Σᵉ |ab|ᵉ))
          ( |ab|ᵉ))
      ( λ (aᵉ ,ᵉ bᵉ) →
        ( apᵉ
          ( map-inv-trunc-Σᵉ)
          ( triangle-universal-property-truncᵉ _
            ( λ (a'ᵉ ,ᵉ b'ᵉ) → unit-truncᵉ (a'ᵉ ,ᵉ unit-truncᵉ b'ᵉ))
            ( aᵉ ,ᵉ bᵉ))) ∙ᵉ
        ( triangle-universal-property-truncᵉ _
          ( λ (a'ᵉ ,ᵉ |b'|ᵉ) →
            map-universal-property-truncᵉ
              ( truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ))
              ( λ b'ᵉ → unit-truncᵉ (a'ᵉ ,ᵉ b'ᵉ))
              ( |b'|ᵉ))
          ( aᵉ ,ᵉ unit-truncᵉ bᵉ) ∙ᵉ
        triangle-universal-property-truncᵉ _
          ( λ b'ᵉ → unit-truncᵉ (aᵉ ,ᵉ b'ᵉ))
          ( bᵉ)))

  is-section-map-inv-trunc-Σᵉ :
    ( map-trunc-Σᵉ ∘ᵉ map-inv-trunc-Σᵉ) ~ᵉ idᵉ
  is-section-map-inv-trunc-Σᵉ =
    function-dependent-universal-property-truncᵉ
      ( λ |a|b||ᵉ →
        Id-Truncated-Type'ᵉ
          ( truncᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → type-truncᵉ kᵉ (Bᵉ xᵉ))))
          ( map-trunc-Σᵉ (map-inv-trunc-Σᵉ |a|b||ᵉ))
          ( |a|b||ᵉ))
      ( λ (aᵉ ,ᵉ |b|ᵉ) →
        function-dependent-universal-property-truncᵉ
          (λ |b'|ᵉ →
            Id-Truncated-Type'ᵉ
              ( truncᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → type-truncᵉ kᵉ (Bᵉ xᵉ))))
              (map-trunc-Σᵉ (map-inv-trunc-Σᵉ (unit-truncᵉ (aᵉ ,ᵉ |b'|ᵉ))))
              (unit-truncᵉ (aᵉ ,ᵉ |b'|ᵉ)))
          (λ bᵉ →
            apᵉ map-trunc-Σᵉ
              (triangle-universal-property-truncᵉ _
                ( λ (a'ᵉ ,ᵉ |b'|ᵉ) →
                  map-universal-property-truncᵉ
                    ( truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ))
                    ( λ b'ᵉ → unit-truncᵉ (a'ᵉ ,ᵉ b'ᵉ))
                    ( |b'|ᵉ))
                ( aᵉ ,ᵉ unit-truncᵉ bᵉ)) ∙ᵉ
            (apᵉ map-trunc-Σᵉ
              (triangle-universal-property-truncᵉ
                ( truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ))
                ( λ b'ᵉ → unit-truncᵉ (aᵉ ,ᵉ b'ᵉ))
                ( bᵉ)) ∙ᵉ
            triangle-universal-property-truncᵉ _
              ( λ (a'ᵉ ,ᵉ b'ᵉ) → unit-truncᵉ (a'ᵉ ,ᵉ unit-truncᵉ b'ᵉ))
              ( aᵉ ,ᵉ bᵉ)))
          ( |b|ᵉ))

  equiv-trunc-Σᵉ :
      type-truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ) ≃ᵉ type-truncᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → type-truncᵉ kᵉ (Bᵉ xᵉ)))
  pr1ᵉ equiv-trunc-Σᵉ = map-trunc-Σᵉ
  pr2ᵉ equiv-trunc-Σᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-trunc-Σᵉ
      is-section-map-inv-trunc-Σᵉ
      is-retraction-map-inv-trunc-Σᵉ

  inv-equiv-trunc-Σᵉ :
    type-truncᵉ kᵉ (Σᵉ Aᵉ (λ xᵉ → type-truncᵉ kᵉ (Bᵉ xᵉ))) ≃ᵉ type-truncᵉ kᵉ (Σᵉ Aᵉ Bᵉ)
  pr1ᵉ inv-equiv-trunc-Σᵉ = map-inv-trunc-Σᵉ
  pr2ᵉ inv-equiv-trunc-Σᵉ =
    is-equiv-is-invertibleᵉ
      map-trunc-Σᵉ
      is-retraction-map-inv-trunc-Σᵉ
      is-section-map-inv-trunc-Σᵉ
```