# Equality on dependent function types

```agda
module foundation.equality-dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.implicit-function-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ typesᵉ `B`ᵉ overᵉ `A`,ᵉ ifᵉ weᵉ canᵉ characterizeᵉ theᵉ
[identityᵉ types](foundation-core.identity-types.mdᵉ) ofᵉ eachᵉ `Bᵉ x`,ᵉ thenᵉ weᵉ canᵉ
characterizeᵉ theᵉ identityᵉ typesᵉ ofᵉ `(xᵉ : Aᵉ) → Bᵉ x`.ᵉ

## Properties

### Torsoriality

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ}
  (is-torsorial-Cᵉ : (xᵉ : Aᵉ) → is-torsorialᵉ (Cᵉ xᵉ))
  where

  is-torsorial-Eq-Πᵉ : is-torsorialᵉ (λ gᵉ → (xᵉ : Aᵉ) → Cᵉ xᵉ (gᵉ xᵉ))
  is-torsorial-Eq-Πᵉ =
    is-contr-equiv'ᵉ
      ( (xᵉ : Aᵉ) → Σᵉ (Bᵉ xᵉ) (Cᵉ xᵉ))
      ( distributive-Π-Σᵉ)
      ( is-contr-Πᵉ is-torsorial-Cᵉ)

  is-torsorial-Eq-implicit-Πᵉ : is-torsorialᵉ (λ gᵉ → {xᵉ : Aᵉ} → Cᵉ xᵉ (gᵉ {xᵉ}))
  is-torsorial-Eq-implicit-Πᵉ =
    is-contr-equivᵉ
      ( Σᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) (λ gᵉ → (xᵉ : Aᵉ) → Cᵉ xᵉ (gᵉ xᵉ)))
      ( equiv-Σᵉ
        ( λ gᵉ → (xᵉ : Aᵉ) → Cᵉ xᵉ (gᵉ xᵉ))
        ( equiv-explicit-implicit-Πᵉ)
        ( λ _ → equiv-explicit-implicit-Πᵉ))
      ( is-torsorial-Eq-Πᵉ)
```

### Extensionality

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ)
  (Eq-Bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l3ᵉ)
  where

  map-extensionality-Πᵉ :
    ( (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-Bᵉ xᵉ yᵉ) →
    ( gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → fᵉ ＝ᵉ gᵉ → ((xᵉ : Aᵉ) → Eq-Bᵉ xᵉ (gᵉ xᵉ))
  map-extensionality-Πᵉ eᵉ .fᵉ reflᵉ xᵉ = map-equivᵉ (eᵉ xᵉ (fᵉ xᵉ)) reflᵉ

  abstract
    is-equiv-map-extensionality-Πᵉ :
      (eᵉ : (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-Bᵉ xᵉ yᵉ) →
      (gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → is-equivᵉ (map-extensionality-Πᵉ eᵉ gᵉ)
    is-equiv-map-extensionality-Πᵉ eᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-Πᵉ
          ( λ xᵉ →
            fundamental-theorem-id'ᵉ
              ( λ yᵉ → map-equivᵉ (eᵉ xᵉ yᵉ))
              ( λ yᵉ → is-equiv-map-equivᵉ (eᵉ xᵉ yᵉ))))
        ( map-extensionality-Πᵉ eᵉ)

  extensionality-Πᵉ :
    ( (xᵉ : Aᵉ) (yᵉ : Bᵉ xᵉ) → (fᵉ xᵉ ＝ᵉ yᵉ) ≃ᵉ Eq-Bᵉ xᵉ yᵉ) →
    ( gᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ ((xᵉ : Aᵉ) → Eq-Bᵉ xᵉ (gᵉ xᵉ))
  pr1ᵉ (extensionality-Πᵉ eᵉ gᵉ) = map-extensionality-Πᵉ eᵉ gᵉ
  pr2ᵉ (extensionality-Πᵉ eᵉ gᵉ) = is-equiv-map-extensionality-Πᵉ eᵉ gᵉ
```

## See also

-ᵉ Equalityᵉ proofsᵉ in theᵉ fiberᵉ ofᵉ aᵉ mapᵉ areᵉ characterizedᵉ in
  [`foundation.equality-fibers-of-maps`](foundation.equality-fibers-of-maps.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in cartesianᵉ productᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ pairᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).ᵉ
-ᵉ Functionᵉ extensionalityᵉ isᵉ postulatedᵉ in
  [`foundation.function-extensionality`](foundation.function-extensionality.md).ᵉ