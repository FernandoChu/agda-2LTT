# Counting the elements of dependent function types

```agda
module univalent-combinatorics.dependent-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-empty-typeᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.cartesian-product-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-choiceᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Dependentᵉ productsᵉ ofᵉ finiteᵉ typesᵉ indexedᵉ byᵉ aᵉ finiteᵉ typeᵉ areᵉ finite.ᵉ

## Properties

### Counting dependent products indexed by standard finite types

Ifᵉ theᵉ elementsᵉ ofᵉ `A`ᵉ canᵉ beᵉ countedᵉ andᵉ ifᵉ forᵉ eachᵉ `xᵉ : A`ᵉ theᵉ elementsᵉ ofᵉ
`Bᵉ x`ᵉ canᵉ beᵉ counted,ᵉ thenᵉ theᵉ elementsᵉ ofᵉ `Πᵉ Aᵉ B`ᵉ canᵉ beᵉ counted.ᵉ

```agda
count-Π-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) {Bᵉ : Finᵉ kᵉ → UUᵉ l1ᵉ} →
  ((xᵉ : Finᵉ kᵉ) → countᵉ (Bᵉ xᵉ)) → countᵉ ((xᵉ : Finᵉ kᵉ) → Bᵉ xᵉ)
count-Π-Finᵉ {l1ᵉ} zero-ℕᵉ {Bᵉ} eᵉ =
  count-is-contrᵉ (dependent-universal-property-empty'ᵉ Bᵉ)
count-Π-Finᵉ {l1ᵉ} (succ-ℕᵉ kᵉ) {Bᵉ} eᵉ =
  count-equiv'ᵉ
    ( equiv-dependent-universal-property-coproductᵉ Bᵉ)
    ( count-productᵉ
      ( count-Π-Finᵉ kᵉ (λ xᵉ → eᵉ (inlᵉ xᵉ)))
      ( count-equiv'ᵉ
        ( equiv-dependent-universal-property-unitᵉ (Bᵉ ∘ᵉ inrᵉ))
        ( eᵉ (inrᵉ starᵉ))))
```

### Counting on dependent function types

```agda
count-Πᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  countᵉ Aᵉ → ((xᵉ : Aᵉ) → countᵉ (Bᵉ xᵉ)) → countᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
count-Πᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} eᵉ fᵉ =
  count-equiv'ᵉ
    ( equiv-precomp-Πᵉ (equiv-countᵉ eᵉ) Bᵉ)
    ( count-Π-Finᵉ (number-of-elements-countᵉ eᵉ) (λ xᵉ → fᵉ (map-equiv-countᵉ eᵉ xᵉ)))
```

### Finiteness of dependent function types

```agda
abstract
  is-finite-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-finiteᵉ Aᵉ → ((xᵉ : Aᵉ) → is-finiteᵉ (Bᵉ xᵉ)) → is-finiteᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  is-finite-Πᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ gᵉ =
    apply-universal-property-trunc-Propᵉ fᵉ
      ( is-finite-Propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ))
      ( λ eᵉ →
        apply-universal-property-trunc-Propᵉ
          ( finite-choiceᵉ fᵉ gᵉ)
          ( is-finite-Propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ))
          ( λ hᵉ → unit-trunc-Propᵉ (count-Πᵉ eᵉ hᵉ)))

  is-finite-Π'ᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-finiteᵉ Aᵉ → ((xᵉ : Aᵉ) → is-finiteᵉ (Bᵉ xᵉ)) → is-finiteᵉ ({xᵉ : Aᵉ} → Bᵉ xᵉ)
  is-finite-Π'ᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ gᵉ =
    is-finite-equivᵉ
      (( pairᵉ
        ( λ fᵉ {xᵉ} → fᵉ xᵉ)
        ( is-equiv-is-invertibleᵉ
          ( λ gᵉ xᵉ → gᵉ {xᵉ})
          ( refl-htpyᵉ)
          ( refl-htpyᵉ))))
      (is-finite-Πᵉ fᵉ gᵉ)

Π-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) (Bᵉ : type-𝔽ᵉ Aᵉ → 𝔽ᵉ l2ᵉ) → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Π-𝔽ᵉ Aᵉ Bᵉ) = (xᵉ : type-𝔽ᵉ Aᵉ) → type-𝔽ᵉ (Bᵉ xᵉ)
pr2ᵉ (Π-𝔽ᵉ Aᵉ Bᵉ) = is-finite-Πᵉ (is-finite-type-𝔽ᵉ Aᵉ) (λ xᵉ → is-finite-type-𝔽ᵉ (Bᵉ xᵉ))

Π-𝔽'ᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) (Bᵉ : type-𝔽ᵉ Aᵉ → 𝔽ᵉ l2ᵉ) → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Π-𝔽'ᵉ Aᵉ Bᵉ) = {xᵉ : type-𝔽ᵉ Aᵉ} → type-𝔽ᵉ (Bᵉ xᵉ)
pr2ᵉ (Π-𝔽'ᵉ Aᵉ Bᵉ) =
  is-finite-Π'ᵉ (is-finite-type-𝔽ᵉ Aᵉ) (λ xᵉ → is-finite-type-𝔽ᵉ (Bᵉ xᵉ))
```