# Finite choice

```agda
module univalent-combinatorics.finite-choiceᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.well-ordering-principle-standard-finite-typesᵉ

open import foundation.coproduct-typesᵉ
open import foundation.decidable-embeddingsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fiber-inclusionsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.hilberts-epsilon-operatorsᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-coproduct-typesᵉ
open import foundation.universal-property-unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-decidable-subtypesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Propositionalᵉ truncationsᵉ distributesᵉ overᵉ finiteᵉ products.ᵉ

## Theorems

```agda
abstract
  finite-choice-Finᵉ :
    {l1ᵉ : Level} (kᵉ : ℕᵉ) {Yᵉ : Finᵉ kᵉ → UUᵉ l1ᵉ} →
    ((xᵉ : Finᵉ kᵉ) → type-trunc-Propᵉ (Yᵉ xᵉ)) → type-trunc-Propᵉ ((xᵉ : Finᵉ kᵉ) → Yᵉ xᵉ)
  finite-choice-Finᵉ {l1ᵉ} zero-ℕᵉ {Yᵉ} Hᵉ = unit-trunc-Propᵉ ind-emptyᵉ
  finite-choice-Finᵉ {l1ᵉ} (succ-ℕᵉ kᵉ) {Yᵉ} Hᵉ =
    map-inv-equiv-trunc-Propᵉ
      ( equiv-dependent-universal-property-coproductᵉ Yᵉ)
      ( map-inv-distributive-trunc-product-Propᵉ
        ( pairᵉ
          ( finite-choice-Finᵉ kᵉ (λ xᵉ → Hᵉ (inlᵉ xᵉ)))
          ( map-inv-equiv-trunc-Propᵉ
            ( equiv-dependent-universal-property-unitᵉ (Yᵉ ∘ᵉ inrᵉ))
            ( Hᵉ (inrᵉ starᵉ)))))

abstract
  finite-choice-countᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : Xᵉ → UUᵉ l2ᵉ} → countᵉ Xᵉ →
    ((xᵉ : Xᵉ) → type-trunc-Propᵉ (Yᵉ xᵉ)) → type-trunc-Propᵉ ((xᵉ : Xᵉ) → Yᵉ xᵉ)
  finite-choice-countᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} (pairᵉ kᵉ eᵉ) Hᵉ =
    map-inv-equiv-trunc-Propᵉ
      ( equiv-precomp-Πᵉ eᵉ Yᵉ)
      ( finite-choice-Finᵉ kᵉ (λ xᵉ → Hᵉ (map-equivᵉ eᵉ xᵉ)))

abstract
  finite-choiceᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : Xᵉ → UUᵉ l2ᵉ} → is-finiteᵉ Xᵉ →
    ((xᵉ : Xᵉ) → type-trunc-Propᵉ (Yᵉ xᵉ)) → type-trunc-Propᵉ ((xᵉ : Xᵉ) → Yᵉ xᵉ)
  finite-choiceᵉ {l1ᵉ} {l2ᵉ} {Xᵉ} {Yᵉ} is-finite-Xᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ is-finite-Xᵉ
      ( trunc-Propᵉ ((xᵉ : Xᵉ) → Yᵉ xᵉ))
      ( λ eᵉ → finite-choice-countᵉ eᵉ Hᵉ)
```

```agda
abstract
  ε-operator-countᵉ :
    {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → countᵉ Aᵉ → ε-operator-Hilbertᵉ Aᵉ
  ε-operator-countᵉ (pairᵉ zero-ℕᵉ eᵉ) tᵉ =
    ex-falsoᵉ
      ( is-empty-type-trunc-Propᵉ
        ( is-empty-is-zero-number-of-elements-countᵉ (pairᵉ zero-ℕᵉ eᵉ) reflᵉ)
        ( tᵉ))
  ε-operator-countᵉ (pairᵉ (succ-ℕᵉ kᵉ) eᵉ) tᵉ = map-equivᵉ eᵉ (zero-Finᵉ kᵉ)

abstract
  ε-operator-decidable-subtype-countᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (eᵉ : countᵉ Aᵉ) (Pᵉ : decidable-subtypeᵉ l2ᵉ Aᵉ) →
    ε-operator-Hilbertᵉ (type-decidable-subtypeᵉ Pᵉ)
  ε-operator-decidable-subtype-countᵉ eᵉ Pᵉ =
    ε-operator-equivᵉ
      ( equiv-Σ-equiv-baseᵉ (is-in-decidable-subtypeᵉ Pᵉ) (equiv-countᵉ eᵉ))
      ( ε-operator-decidable-subtype-Finᵉ
        ( number-of-elements-countᵉ eᵉ)
        ( λ xᵉ → Pᵉ (map-equiv-countᵉ eᵉ xᵉ)))
```

```agda
abstract
  ε-operator-emb-countᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (eᵉ : countᵉ Aᵉ) {Bᵉ : UUᵉ l2ᵉ} →
    (fᵉ : Bᵉ ↪ᵈᵉ Aᵉ) → ε-operator-Hilbertᵉ Bᵉ
  ε-operator-emb-countᵉ eᵉ fᵉ tᵉ =
    map-equiv-total-fiberᵉ
      ( map-decidable-embᵉ fᵉ)
      ( ε-operator-decidable-subtype-countᵉ eᵉ
        ( decidable-subtype-decidable-embᵉ fᵉ)
        ( map-trunc-Propᵉ
          ( map-inv-equiv-total-fiberᵉ (map-decidable-embᵉ fᵉ))
          ( tᵉ)))
```

```agda
abstract
  choice-count-Σ-is-finite-fiberᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-setᵉ Aᵉ → countᵉ (Σᵉ Aᵉ Bᵉ) → ((xᵉ : Aᵉ) → is-finiteᵉ (Bᵉ xᵉ)) →
    ((xᵉ : Aᵉ) → type-trunc-Propᵉ (Bᵉ xᵉ)) → (xᵉ : Aᵉ) → Bᵉ xᵉ
  choice-count-Σ-is-finite-fiberᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} Kᵉ eᵉ gᵉ Hᵉ xᵉ =
    ε-operator-countᵉ
      ( count-domain-emb-is-finite-domain-embᵉ eᵉ
        ( fiber-inclusion-embᵉ (pairᵉ Aᵉ Kᵉ) Bᵉ xᵉ)
        ( gᵉ xᵉ))
      ( Hᵉ xᵉ)

abstract
  choice-is-finite-Σ-is-finite-fiberᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-setᵉ Aᵉ → is-finiteᵉ (Σᵉ Aᵉ Bᵉ) → ((xᵉ : Aᵉ) → is-finiteᵉ (Bᵉ xᵉ)) →
    ((xᵉ : Aᵉ) → type-trunc-Propᵉ (Bᵉ xᵉ)) → type-trunc-Propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ)
  choice-is-finite-Σ-is-finite-fiberᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} Kᵉ fᵉ gᵉ Hᵉ =
    apply-universal-property-trunc-Propᵉ fᵉ
      ( trunc-Propᵉ ((xᵉ : Aᵉ) → Bᵉ xᵉ))
      ( λ eᵉ → unit-trunc-Propᵉ (choice-count-Σ-is-finite-fiberᵉ Kᵉ eᵉ gᵉ Hᵉ))
```