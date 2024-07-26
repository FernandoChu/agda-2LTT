# Type arithmetic for cartesian product types

```agda
module foundation.type-arithmetic-cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Weᵉ proveᵉ lawsᵉ forᵉ theᵉ manipulationᵉ ofᵉ cartesianᵉ productsᵉ with respectᵉ to
themselvesᵉ andᵉ dependentᵉ pairᵉ types.ᵉ

## Laws

### Commutativity of cartesian products

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-commutative-productᵉ : Aᵉ ×ᵉ Bᵉ → Bᵉ ×ᵉ Aᵉ
  pr1ᵉ (map-commutative-productᵉ (pairᵉ aᵉ bᵉ)) = bᵉ
  pr2ᵉ (map-commutative-productᵉ (pairᵉ aᵉ bᵉ)) = aᵉ

  map-inv-commutative-productᵉ : Bᵉ ×ᵉ Aᵉ → Aᵉ ×ᵉ Bᵉ
  pr1ᵉ (map-inv-commutative-productᵉ (pairᵉ bᵉ aᵉ)) = aᵉ
  pr2ᵉ (map-inv-commutative-productᵉ (pairᵉ bᵉ aᵉ)) = bᵉ

  is-section-map-inv-commutative-productᵉ :
    (map-commutative-productᵉ ∘ᵉ map-inv-commutative-productᵉ) ~ᵉ idᵉ
  is-section-map-inv-commutative-productᵉ (pairᵉ bᵉ aᵉ) = reflᵉ

  is-retraction-map-inv-commutative-productᵉ :
    (map-inv-commutative-productᵉ ∘ᵉ map-commutative-productᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-commutative-productᵉ (pairᵉ aᵉ bᵉ) = reflᵉ

  is-equiv-map-commutative-productᵉ : is-equivᵉ map-commutative-productᵉ
  is-equiv-map-commutative-productᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-commutative-productᵉ
      is-section-map-inv-commutative-productᵉ
      is-retraction-map-inv-commutative-productᵉ

  commutative-productᵉ : (Aᵉ ×ᵉ Bᵉ) ≃ᵉ (Bᵉ ×ᵉ Aᵉ)
  pr1ᵉ commutative-productᵉ = map-commutative-productᵉ
  pr2ᵉ commutative-productᵉ = is-equiv-map-commutative-productᵉ
```

### Associativity of cartesian products

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) (Cᵉ : UUᵉ l3ᵉ)
  where

  map-associative-productᵉ : (Aᵉ ×ᵉ Bᵉ) ×ᵉ Cᵉ → Aᵉ ×ᵉ (Bᵉ ×ᵉ Cᵉ)
  map-associative-productᵉ = map-associative-Σᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  map-inv-associative-productᵉ : Aᵉ ×ᵉ (Bᵉ ×ᵉ Cᵉ) → (Aᵉ ×ᵉ Bᵉ) ×ᵉ Cᵉ
  map-inv-associative-productᵉ = map-inv-associative-Σᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  is-section-map-inv-associative-productᵉ :
    (map-associative-productᵉ ∘ᵉ map-inv-associative-productᵉ) ~ᵉ idᵉ
  is-section-map-inv-associative-productᵉ =
    is-section-map-inv-associative-Σᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  is-retraction-map-inv-associative-productᵉ :
    (map-inv-associative-productᵉ ∘ᵉ map-associative-productᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-associative-productᵉ =
    is-retraction-map-inv-associative-Σᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  is-equiv-map-associative-productᵉ : is-equivᵉ map-associative-productᵉ
  is-equiv-map-associative-productᵉ =
    is-equiv-map-associative-Σᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)

  associative-productᵉ : ((Aᵉ ×ᵉ Bᵉ) ×ᵉ Cᵉ) ≃ᵉ (Aᵉ ×ᵉ (Bᵉ ×ᵉ Cᵉ))
  associative-productᵉ = associative-Σᵉ Aᵉ (λ _ → Bᵉ) (λ _ → Cᵉ)
```

### The unit laws of cartesian product types with respect to contractible types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (is-contr-Bᵉ : is-contrᵉ Bᵉ)
  where

  right-unit-law-product-is-contrᵉ : Aᵉ ×ᵉ Bᵉ ≃ᵉ Aᵉ
  right-unit-law-product-is-contrᵉ = right-unit-law-Σ-is-contrᵉ (λ _ → is-contr-Bᵉ)

  inv-right-unit-law-product-is-contrᵉ : Aᵉ ≃ᵉ Aᵉ ×ᵉ Bᵉ
  inv-right-unit-law-product-is-contrᵉ =
    inv-equivᵉ right-unit-law-product-is-contrᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (is-contr-Aᵉ : is-contrᵉ Aᵉ)
  where

  left-unit-law-product-is-contrᵉ : Aᵉ ×ᵉ Bᵉ ≃ᵉ Bᵉ
  left-unit-law-product-is-contrᵉ =
    left-unit-law-Σ-is-contrᵉ is-contr-Aᵉ (centerᵉ is-contr-Aᵉ)

  inv-left-unit-law-product-is-contrᵉ : Bᵉ ≃ᵉ Aᵉ ×ᵉ Bᵉ
  inv-left-unit-law-product-is-contrᵉ = inv-equivᵉ left-unit-law-product-is-contrᵉ

  is-equiv-pr2-product-is-contrᵉ : is-equivᵉ (pr2ᵉ {Bᵉ = λ _ → Bᵉ})
  is-equiv-pr2-product-is-contrᵉ =
    is-equiv-compᵉ
      ( pr1ᵉ)
      ( map-commutative-productᵉ)
      ( is-equiv-map-commutative-productᵉ)
      ( is-equiv-pr1-is-contrᵉ (λ _ → is-contr-Aᵉ))

  equiv-pr2-product-is-contrᵉ : (Aᵉ ×ᵉ Bᵉ) ≃ᵉ Bᵉ
  pr1ᵉ equiv-pr2-product-is-contrᵉ = pr2ᵉ
  pr2ᵉ equiv-pr2-product-is-contrᵉ = is-equiv-pr2-product-is-contrᵉ
```

### Adding redundant properties

```agda
equiv-add-redundant-propᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  is-propᵉ Bᵉ → (fᵉ : Aᵉ → Bᵉ) → Aᵉ ≃ᵉ Aᵉ ×ᵉ Bᵉ
pr1ᵉ (equiv-add-redundant-propᵉ is-prop-Bᵉ fᵉ) aᵉ = aᵉ ,ᵉ fᵉ aᵉ
pr2ᵉ (equiv-add-redundant-propᵉ is-prop-Bᵉ fᵉ) =
  is-equiv-is-invertibleᵉ
    ( pr1ᵉ)
    ( λ pᵉ → eq-pairᵉ reflᵉ (eq-is-propᵉ is-prop-Bᵉ))
    ( refl-htpyᵉ)
```

## See also

-ᵉ Functorialᵉ propertiesᵉ ofᵉ cartesianᵉ productsᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in cartesianᵉ productᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).ᵉ
-ᵉ Theᵉ universalᵉ propertyᵉ ofᵉ cartesianᵉ productᵉ typesᵉ isᵉ treatedᵉ in
  [`foundation.universal-property-cartesian-product-types`](foundation.universal-property-cartesian-product-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).ᵉ
  -ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ productᵉ typesᵉ areᵉ recordedᵉ in
    [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ coproductᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-coproduct-types`](foundation.type-arithmetic-coproduct-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ unitᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-unit-type`](foundation.type-arithmetic-unit-type.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ theᵉ emptyᵉ typeᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-empty-type`](foundation.type-arithmetic-empty-type.md).ᵉ