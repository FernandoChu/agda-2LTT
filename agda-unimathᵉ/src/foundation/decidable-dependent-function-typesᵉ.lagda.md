# Decidability of dependent function types

```agda
module foundation.decidable-dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.maybeᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-maybeᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.coproduct-typesᵉ
open import foundation-core.equivalencesᵉ
```

</details>

## Idea

Weᵉ describeᵉ conditionsᵉ underᵉ whichᵉ dependentᵉ productsᵉ areᵉ decidable.ᵉ

### Decidablitilty of dependent products over coproducts

```agda
is-decidable-Π-coproductᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ +ᵉ Bᵉ → UUᵉ l3ᵉ} →
  is-decidableᵉ ((aᵉ : Aᵉ) → Cᵉ (inlᵉ aᵉ)) → is-decidableᵉ ((bᵉ : Bᵉ) → Cᵉ (inrᵉ bᵉ)) →
  is-decidableᵉ ((xᵉ : Aᵉ +ᵉ Bᵉ) → Cᵉ xᵉ)
is-decidable-Π-coproductᵉ {Cᵉ = Cᵉ} dAᵉ dBᵉ =
  is-decidable-equivᵉ
    ( equiv-dependent-universal-property-coproductᵉ Cᵉ)
    ( is-decidable-productᵉ dAᵉ dBᵉ)
```

### Decidability of dependent products over `Maybe`

```agda
is-decidable-Π-Maybeᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Maybeᵉ Aᵉ → UUᵉ l2ᵉ} →
  is-decidableᵉ ((xᵉ : Aᵉ) → Bᵉ (unit-Maybeᵉ xᵉ)) → is-decidableᵉ (Bᵉ exception-Maybeᵉ) →
  is-decidableᵉ ((xᵉ : Maybeᵉ Aᵉ) → Bᵉ xᵉ)
is-decidable-Π-Maybeᵉ {Bᵉ = Bᵉ} duᵉ deᵉ =
  is-decidable-equivᵉ
    ( equiv-dependent-universal-property-Maybeᵉ Bᵉ)
    ( is-decidable-productᵉ duᵉ deᵉ)
```

### Decidability of dependent products over an equivalence

```agda
is-decidable-Π-equivᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} {Dᵉ : Bᵉ → UUᵉ l4ᵉ}
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) (fᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ ≃ᵉ Dᵉ (map-equivᵉ eᵉ xᵉ)) →
  is-decidableᵉ ((xᵉ : Aᵉ) → Cᵉ xᵉ) → is-decidableᵉ ((yᵉ : Bᵉ) → Dᵉ yᵉ)
is-decidable-Π-equivᵉ {Dᵉ = Dᵉ} eᵉ fᵉ = is-decidable-equiv'ᵉ (equiv-Πᵉ Dᵉ eᵉ fᵉ)

is-decidable-Π-equiv'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ} {Dᵉ : Bᵉ → UUᵉ l4ᵉ}
  (eᵉ : Aᵉ ≃ᵉ Bᵉ) (fᵉ : (xᵉ : Aᵉ) → Cᵉ xᵉ ≃ᵉ Dᵉ (map-equivᵉ eᵉ xᵉ)) →
  is-decidableᵉ ((yᵉ : Bᵉ) → Dᵉ yᵉ) → is-decidableᵉ ((xᵉ : Aᵉ) → Cᵉ xᵉ)
is-decidable-Π-equiv'ᵉ {Dᵉ = Dᵉ} eᵉ fᵉ = is-decidable-equivᵉ (equiv-Πᵉ Dᵉ eᵉ fᵉ)
```