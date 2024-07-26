# Functoriality of dependent function types

```agda
module foundation-core.functoriality-dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.implicit-function-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.families-of-equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Properties

### The operation `map-Π` preserves homotopies

```agda
htpy-map-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  {fᵉ f'ᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ} (Hᵉ : (iᵉ : Iᵉ) → (fᵉ iᵉ) ~ᵉ (f'ᵉ iᵉ)) →
  map-Πᵉ fᵉ ~ᵉ map-Πᵉ f'ᵉ
htpy-map-Πᵉ Hᵉ hᵉ = eq-htpyᵉ (λ iᵉ → Hᵉ iᵉ (hᵉ iᵉ))

htpy-map-Π'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  {Jᵉ : UUᵉ l4ᵉ} (αᵉ : Jᵉ → Iᵉ) {fᵉ f'ᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ} →
  ((iᵉ : Iᵉ) → (fᵉ iᵉ) ~ᵉ (f'ᵉ iᵉ)) → map-Π'ᵉ αᵉ fᵉ ~ᵉ map-Π'ᵉ αᵉ f'ᵉ
htpy-map-Π'ᵉ αᵉ Hᵉ = htpy-map-Πᵉ (Hᵉ ∘ᵉ αᵉ)
```

### The fibers of `map-Π`

```agda
compute-fiber-map-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) (hᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ) →
  ((iᵉ : Iᵉ) → fiberᵉ (fᵉ iᵉ) (hᵉ iᵉ)) ≃ᵉ fiberᵉ (map-Πᵉ fᵉ) hᵉ
compute-fiber-map-Πᵉ fᵉ hᵉ = equiv-totᵉ (λ _ → equiv-eq-htpyᵉ) ∘eᵉ distributive-Π-Σᵉ

compute-fiber-map-Π'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  {Jᵉ : UUᵉ l4ᵉ} (αᵉ : Jᵉ → Iᵉ) (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ)
  (hᵉ : (jᵉ : Jᵉ) → Bᵉ (αᵉ jᵉ)) →
  ((jᵉ : Jᵉ) → fiberᵉ (fᵉ (αᵉ jᵉ)) (hᵉ jᵉ)) ≃ᵉ fiberᵉ (map-Π'ᵉ αᵉ fᵉ) hᵉ
compute-fiber-map-Π'ᵉ αᵉ fᵉ = compute-fiber-map-Πᵉ (fᵉ ∘ᵉ αᵉ)
```

### Families of equivalences induce equivalences of dependent function types

```agda
abstract
  is-equiv-map-Π-is-fiberwise-equivᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
    {fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ} → is-fiberwise-equivᵉ fᵉ →
    is-equivᵉ (map-Πᵉ fᵉ)
  is-equiv-map-Π-is-fiberwise-equivᵉ is-equiv-fᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ gᵉ →
        is-contr-equiv'ᵉ _
          ( compute-fiber-map-Πᵉ _ gᵉ)
          ( is-contr-Πᵉ (λ iᵉ → is-contr-map-is-equivᵉ (is-equiv-fᵉ iᵉ) (gᵉ iᵉ))))

equiv-Π-equiv-familyᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (eᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ ≃ᵉ Bᵉ iᵉ) → ((iᵉ : Iᵉ) → Aᵉ iᵉ) ≃ᵉ ((iᵉ : Iᵉ) → Bᵉ iᵉ)
pr1ᵉ (equiv-Π-equiv-familyᵉ eᵉ) =
  map-Πᵉ (λ iᵉ → map-equivᵉ (eᵉ iᵉ))
pr2ᵉ (equiv-Π-equiv-familyᵉ eᵉ) =
  is-equiv-map-Π-is-fiberwise-equivᵉ (λ iᵉ → is-equiv-map-equivᵉ (eᵉ iᵉ))
```

### Families of equivalences induce equivalences of implicit dependent function types

```agda
is-equiv-map-implicit-Π-is-fiberwise-equivᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
    {fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ} → is-fiberwise-equivᵉ fᵉ →
    is-equivᵉ (map-implicit-Πᵉ fᵉ)
is-equiv-map-implicit-Π-is-fiberwise-equivᵉ is-equiv-fᵉ =
  is-equiv-compᵉ _ _
    ( is-equiv-explicit-implicit-Πᵉ)
    ( is-equiv-compᵉ _ _
      ( is-equiv-map-Π-is-fiberwise-equivᵉ is-equiv-fᵉ)
      ( is-equiv-implicit-explicit-Πᵉ))

equiv-implicit-Π-equiv-familyᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (eᵉ : (iᵉ : Iᵉ) → (Aᵉ iᵉ) ≃ᵉ (Bᵉ iᵉ)) → ({iᵉ : Iᵉ} → Aᵉ iᵉ) ≃ᵉ ({iᵉ : Iᵉ} → Bᵉ iᵉ)
equiv-implicit-Π-equiv-familyᵉ eᵉ =
  ( equiv-implicit-explicit-Πᵉ) ∘eᵉ
  ( equiv-Π-equiv-familyᵉ eᵉ) ∘eᵉ
  ( equiv-explicit-implicit-Πᵉ)
```

##### Computing the inverse of `equiv-Π-equiv-family`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  compute-inv-equiv-Π-equiv-familyᵉ :
    (eᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ ≃ᵉ Cᵉ xᵉ) →
    ( map-inv-equivᵉ (equiv-Π-equiv-familyᵉ eᵉ)) ~ᵉ
    ( map-equivᵉ (equiv-Π-equiv-familyᵉ (λ xᵉ → inv-equivᵉ (eᵉ xᵉ))))
  compute-inv-equiv-Π-equiv-familyᵉ eᵉ fᵉ =
    is-injective-equivᵉ
      ( equiv-Π-equiv-familyᵉ eᵉ)
      ( ( is-section-map-inv-equivᵉ (equiv-Π-equiv-familyᵉ eᵉ) fᵉ) ∙ᵉ
        ( eq-htpyᵉ (λ xᵉ → invᵉ (is-section-map-inv-equivᵉ (eᵉ xᵉ) (fᵉ xᵉ)))))
```

## See also

-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ functionᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ functionᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ functionᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-function-types`](foundation.functoriality-function-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ pairᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).ᵉ
-ᵉ Functorialᵉ propertiesᵉ ofᵉ cartesianᵉ productᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).ᵉ