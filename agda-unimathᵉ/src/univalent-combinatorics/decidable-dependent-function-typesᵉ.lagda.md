# Decidable dependent function types

```agda
module univalent-combinatorics.decidable-dependent-function-typesᵉ where

open import elementary-number-theory.decidable-dependent-function-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-propositionsᵉ
open import foundation.decidable-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.finite-choiceᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ describeᵉ conditionsᵉ underᵉ whichᵉ dependentᵉ productsᵉ areᵉ decidable.ᵉ

```agda
is-decidable-Π-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) {Bᵉ : Finᵉ kᵉ → UUᵉ l1ᵉ} →
  ((xᵉ : Finᵉ kᵉ) → is-decidableᵉ (Bᵉ xᵉ)) → is-decidableᵉ ((xᵉ : Finᵉ kᵉ) → Bᵉ xᵉ)
is-decidable-Π-Finᵉ zero-ℕᵉ {Bᵉ} dᵉ = inlᵉ ind-emptyᵉ
is-decidable-Π-Finᵉ (succ-ℕᵉ kᵉ) {Bᵉ} dᵉ =
  is-decidable-Π-Maybeᵉ
    ( is-decidable-Π-Finᵉ kᵉ (λ xᵉ → dᵉ (inlᵉ xᵉ)))
    ( dᵉ (inrᵉ starᵉ))
```

```agda
is-decidable-Π-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
  countᵉ Aᵉ → ((xᵉ : Aᵉ) → is-decidableᵉ (Bᵉ xᵉ)) → is-decidableᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
is-decidable-Π-countᵉ eᵉ dᵉ =
  is-decidable-Π-equivᵉ
    ( equiv-countᵉ eᵉ)
    ( λ xᵉ → id-equivᵉ)
    ( is-decidable-Π-Finᵉ
      ( number-of-elements-countᵉ eᵉ)
      ( λ xᵉ → dᵉ (map-equiv-countᵉ eᵉ xᵉ)))

is-decidable-Π-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → is-finiteᵉ Aᵉ →
  ((xᵉ : Aᵉ) → is-decidableᵉ (Bᵉ xᵉ)) → is-decidableᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
is-decidable-Π-is-finiteᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} Hᵉ dᵉ =
  is-decidable-iffᵉ
    ( map-Πᵉ (λ xᵉ → elim-trunc-Prop-is-decidableᵉ (dᵉ xᵉ)))
    ( map-Πᵉ (λ xᵉ → unit-trunc-Propᵉ))
    ( is-decidable-iffᵉ
      ( αᵉ)
      ( finite-choiceᵉ Hᵉ)
      ( apply-universal-property-trunc-Propᵉ Hᵉ
        ( is-decidable-Propᵉ (trunc-Propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)))
        ( λ eᵉ →
          is-decidable-iffᵉ
            ( finite-choiceᵉ Hᵉ)
            ( αᵉ)
            ( is-decidable-Π-countᵉ eᵉ
              ( λ xᵉ →
                is-decidable-iffᵉ
                  ( unit-trunc-Propᵉ)
                  ( elim-trunc-Prop-is-decidableᵉ (dᵉ xᵉ))
                  ( dᵉ xᵉ))))))
  where
  αᵉ : type-trunc-Propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ) → (xᵉ : Aᵉ) → type-trunc-Propᵉ (Bᵉ xᵉ)
  αᵉ = map-universal-property-trunc-Propᵉ
        ( Π-Propᵉ Aᵉ (λ xᵉ → trunc-Propᵉ (Bᵉ xᵉ)))
        ( λ (fᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) (xᵉ : Aᵉ) → unit-trunc-Propᵉ (fᵉ xᵉ))
```