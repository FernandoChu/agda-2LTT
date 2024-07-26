# Cartesian products of finite types

```agda
module univalent-combinatorics.cartesian-product-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbersᵉ
open import elementary-number-theory.natural-numbersᵉ

open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.decidable-equalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-arithmetic-empty-typeᵉ
open import foundation.type-arithmetic-unit-typeᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-dependent-pair-typesᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.double-countingᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ cartesianᵉ productᵉ ofᵉ finiteᵉ typesᵉ isᵉ finite.ᵉ Weᵉ obtainᵉ aᵉ cartesianᵉ productᵉ
operationᵉ onᵉ finiteᵉ types.ᵉ

### The standard finite types are closed under cartesian products

```agda
product-Finᵉ : (kᵉ lᵉ : ℕᵉ) → ((Finᵉ kᵉ) ×ᵉ (Finᵉ lᵉ)) ≃ᵉ Finᵉ (kᵉ *ℕᵉ lᵉ)
product-Finᵉ zero-ℕᵉ lᵉ = left-absorption-productᵉ (Finᵉ lᵉ)
product-Finᵉ (succ-ℕᵉ kᵉ) lᵉ =
  ( ( coproduct-Finᵉ (kᵉ *ℕᵉ lᵉ) lᵉ) ∘eᵉ
    ( equiv-coproductᵉ (product-Finᵉ kᵉ lᵉ) left-unit-law-productᵉ)) ∘eᵉ
  ( right-distributive-product-coproductᵉ (Finᵉ kᵉ) unitᵉ (Finᵉ lᵉ))

Fin-mul-ℕᵉ : (kᵉ lᵉ : ℕᵉ) → (Finᵉ (kᵉ *ℕᵉ lᵉ)) ≃ᵉ ((Finᵉ kᵉ) ×ᵉ (Finᵉ lᵉ))
Fin-mul-ℕᵉ kᵉ lᵉ = inv-equivᵉ (product-Finᵉ kᵉ lᵉ)
```

```agda
count-productᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → countᵉ Xᵉ → countᵉ Yᵉ → countᵉ (Xᵉ ×ᵉ Yᵉ)
pr1ᵉ (count-productᵉ (pairᵉ kᵉ eᵉ) (pairᵉ lᵉ fᵉ)) = kᵉ *ℕᵉ lᵉ
pr2ᵉ (count-productᵉ (pairᵉ kᵉ eᵉ) (pairᵉ lᵉ fᵉ)) =
  (equiv-productᵉ eᵉ fᵉ) ∘eᵉ (inv-equivᵉ (product-Finᵉ kᵉ lᵉ))

abstract
  number-of-elements-count-productᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (count-Aᵉ : countᵉ Aᵉ)
    (count-Bᵉ : countᵉ Bᵉ) →
    Idᵉ
      ( number-of-elements-countᵉ
        ( count-productᵉ count-Aᵉ count-Bᵉ))
      ( ( number-of-elements-countᵉ count-Aᵉ) *ℕᵉ
        ( number-of-elements-countᵉ count-Bᵉ))
  number-of-elements-count-productᵉ (pairᵉ kᵉ eᵉ) (pairᵉ lᵉ fᵉ) = reflᵉ

equiv-left-factorᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (yᵉ : Yᵉ) →
  (Σᵉ (Xᵉ ×ᵉ Yᵉ) (λ tᵉ → Idᵉ (pr2ᵉ tᵉ) yᵉ)) ≃ᵉ Xᵉ
equiv-left-factorᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} yᵉ =
  ( ( right-unit-law-productᵉ) ∘eᵉ
    ( equiv-totᵉ
      ( λ xᵉ → equiv-is-contrᵉ (is-torsorial-Id'ᵉ yᵉ) is-contr-unitᵉ))) ∘eᵉ
  ( associative-Σᵉ Xᵉ (λ xᵉ → Yᵉ) (λ tᵉ → Idᵉ (pr2ᵉ tᵉ) yᵉ))

count-left-factorᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → countᵉ (Xᵉ ×ᵉ Yᵉ) → Yᵉ → countᵉ Xᵉ
count-left-factorᵉ eᵉ yᵉ =
  count-equivᵉ
    ( equiv-left-factorᵉ yᵉ)
    ( count-Σᵉ eᵉ
      ( λ zᵉ →
        count-eqᵉ
          ( has-decidable-equality-right-factorᵉ
            ( has-decidable-equality-countᵉ eᵉ)
            ( pr1ᵉ zᵉ))
          ( pr2ᵉ zᵉ)
          ( yᵉ)))

count-right-factorᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → countᵉ (Xᵉ ×ᵉ Yᵉ) → Xᵉ → countᵉ Yᵉ
count-right-factorᵉ eᵉ xᵉ =
  count-left-factorᵉ (count-equivᵉ commutative-productᵉ eᵉ) xᵉ
```

```agda
abstract
  product-number-of-elements-productᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (count-ABᵉ : countᵉ (Aᵉ ×ᵉ Bᵉ)) →
    (aᵉ : Aᵉ) (bᵉ : Bᵉ) →
    Idᵉ
      ( ( number-of-elements-countᵉ (count-left-factorᵉ count-ABᵉ bᵉ)) *ℕᵉ
        ( number-of-elements-countᵉ (count-right-factorᵉ count-ABᵉ aᵉ)))
      ( number-of-elements-countᵉ count-ABᵉ)
  product-number-of-elements-productᵉ count-ABᵉ aᵉ bᵉ =
    ( invᵉ
      ( number-of-elements-count-productᵉ
        ( count-left-factorᵉ count-ABᵉ bᵉ)
        ( count-right-factorᵉ count-ABᵉ aᵉ))) ∙ᵉ
    ( double-countingᵉ
      ( count-productᵉ
        ( count-left-factorᵉ count-ABᵉ bᵉ)
        ( count-right-factorᵉ count-ABᵉ aᵉ))
      ( count-ABᵉ))
```

```agda
abstract
  is-finite-productᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
    is-finiteᵉ Xᵉ → is-finiteᵉ Yᵉ → is-finiteᵉ (Xᵉ ×ᵉ Yᵉ)
  is-finite-productᵉ {Xᵉ = Xᵉ} {Yᵉ} is-finite-Xᵉ is-finite-Yᵉ =
    apply-universal-property-trunc-Propᵉ is-finite-Xᵉ
      ( is-finite-Propᵉ (Xᵉ ×ᵉ Yᵉ))
      ( λ (eᵉ : countᵉ Xᵉ) →
        apply-universal-property-trunc-Propᵉ is-finite-Yᵉ
          ( is-finite-Propᵉ (Xᵉ ×ᵉ Yᵉ))
          ( is-finite-countᵉ ∘ᵉ (count-productᵉ eᵉ)))

product-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} → 𝔽ᵉ l1ᵉ → 𝔽ᵉ l2ᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (product-𝔽ᵉ Xᵉ Yᵉ) = (type-𝔽ᵉ Xᵉ) ×ᵉ (type-𝔽ᵉ Yᵉ)
pr2ᵉ (product-𝔽ᵉ Xᵉ Yᵉ) =
  is-finite-productᵉ (is-finite-type-𝔽ᵉ Xᵉ) (is-finite-type-𝔽ᵉ Yᵉ)

abstract
  is-finite-left-factorᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
    is-finiteᵉ (Xᵉ ×ᵉ Yᵉ) → Yᵉ → is-finiteᵉ Xᵉ
  is-finite-left-factorᵉ fᵉ yᵉ =
    map-trunc-Propᵉ (λ eᵉ → count-left-factorᵉ eᵉ yᵉ) fᵉ

abstract
  is-finite-right-factorᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} →
    is-finiteᵉ (Xᵉ ×ᵉ Yᵉ) → Xᵉ → is-finiteᵉ Yᵉ
  is-finite-right-factorᵉ fᵉ xᵉ =
    map-trunc-Propᵉ (λ eᵉ → count-right-factorᵉ eᵉ xᵉ) fᵉ

product-UU-Finᵉ :
  {l1ᵉ l2ᵉ : Level} (kᵉ lᵉ : ℕᵉ) → UU-Finᵉ l1ᵉ kᵉ → UU-Finᵉ l2ᵉ lᵉ →
  UU-Finᵉ (l1ᵉ ⊔ l2ᵉ) (kᵉ *ℕᵉ lᵉ)
pr1ᵉ (product-UU-Finᵉ kᵉ lᵉ (pairᵉ Xᵉ Hᵉ) (pairᵉ Yᵉ Kᵉ)) = Xᵉ ×ᵉ Yᵉ
pr2ᵉ (product-UU-Finᵉ kᵉ lᵉ (pairᵉ Xᵉ Hᵉ) (pairᵉ Yᵉ Kᵉ)) =
  apply-universal-property-trunc-Propᵉ Hᵉ
    ( mere-equiv-Propᵉ (Finᵉ (kᵉ *ℕᵉ lᵉ)) (Xᵉ ×ᵉ Yᵉ))
    ( λ e1ᵉ →
      apply-universal-property-trunc-Propᵉ Kᵉ
        ( mere-equiv-Propᵉ (Finᵉ (kᵉ *ℕᵉ lᵉ)) (Xᵉ ×ᵉ Yᵉ))
        ( λ e2ᵉ →
          unit-trunc-Propᵉ (equiv-productᵉ e1ᵉ e2ᵉ ∘eᵉ inv-equivᵉ (product-Finᵉ kᵉ lᵉ))))
```