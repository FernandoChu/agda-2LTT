# Dependent pair types of finite types

```agda
module univalent-combinatorics.dependent-pair-typesᵉ where

open import foundation.dependent-pair-typesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.complementsᵉ
open import foundation.contractible-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.identity-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.sectionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.coproduct-typesᵉ
open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-dependent-pair-typesᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-choiceᵉ
open import univalent-combinatorics.finite-typesᵉ
```

</details>

## Idea

Inᵉ thisᵉ fileᵉ weᵉ studyᵉ finitenessᵉ in relationᵉ to dependentᵉ pairᵉ types.ᵉ

## Properties

### A dependent sum of finite types indexed by a finite type is finite

```agda
abstract
  is-finite-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-finiteᵉ Aᵉ → ((aᵉ : Aᵉ) → is-finiteᵉ (Bᵉ aᵉ)) → is-finiteᵉ (Σᵉ Aᵉ Bᵉ)
  is-finite-Σᵉ {Aᵉ = Aᵉ} {Bᵉ} Hᵉ Kᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-finite-Propᵉ (Σᵉ Aᵉ Bᵉ))
      ( λ (eᵉ : countᵉ Aᵉ) →
        apply-universal-property-trunc-Propᵉ
          ( finite-choiceᵉ Hᵉ Kᵉ)
          ( is-finite-Propᵉ (Σᵉ Aᵉ Bᵉ))
          ( is-finite-countᵉ ∘ᵉ (count-Σᵉ eᵉ)))

Σ-𝔽ᵉ : {l1ᵉ l2ᵉ : Level} (Aᵉ : 𝔽ᵉ l1ᵉ) (Bᵉ : type-𝔽ᵉ Aᵉ → 𝔽ᵉ l2ᵉ) → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (Σ-𝔽ᵉ Aᵉ Bᵉ) = Σᵉ (type-𝔽ᵉ Aᵉ) (λ aᵉ → type-𝔽ᵉ (Bᵉ aᵉ))
pr2ᵉ (Σ-𝔽ᵉ Aᵉ Bᵉ) =
  is-finite-Σᵉ
    ( is-finite-type-𝔽ᵉ Aᵉ)
    ( λ aᵉ → is-finite-type-𝔽ᵉ (Bᵉ aᵉ))
```

### If `A` and `Σ A B` are finite, then eacy `B a` is finite

```agda
abstract
  is-finite-fiber-is-finite-Σᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-finiteᵉ Aᵉ → is-finiteᵉ (Σᵉ Aᵉ Bᵉ) → (aᵉ : Aᵉ) → is-finiteᵉ (Bᵉ aᵉ)
  is-finite-fiber-is-finite-Σᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} fᵉ gᵉ aᵉ =
    apply-universal-property-trunc-Propᵉ fᵉ
      ( is-finite-Propᵉ (Bᵉ aᵉ))
      ( λ eᵉ → map-trunc-Propᵉ (λ hᵉ → count-fiber-count-Σ-count-baseᵉ eᵉ hᵉ aᵉ) gᵉ)
```

### If `B` is a family of finite types over `A` equipped with a (mere) section and `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-Σ-sectionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ) →
    is-finiteᵉ (Σᵉ Aᵉ Bᵉ) → ((aᵉ : Aᵉ) → is-finiteᵉ (Bᵉ aᵉ)) → is-finiteᵉ Aᵉ
  is-finite-base-is-finite-Σ-sectionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} bᵉ fᵉ gᵉ =
    apply-universal-property-trunc-Propᵉ fᵉ
      ( is-finite-Propᵉ Aᵉ)
      ( λ eᵉ →
        is-finite-countᵉ
          ( count-equivᵉ
            ( ( equiv-total-fiberᵉ (map-section-familyᵉ bᵉ)) ∘eᵉ
              ( equiv-totᵉ
                ( λ tᵉ →
                  ( equiv-totᵉ
                    ( λ xᵉ → equiv-eq-pair-Σᵉ (map-section-familyᵉ bᵉ xᵉ) tᵉ)) ∘eᵉ
                  ( ( associative-Σᵉ Aᵉ
                      ( λ (xᵉ : Aᵉ) → Idᵉ xᵉ (pr1ᵉ tᵉ))
                      ( λ sᵉ → Idᵉ (trᵉ Bᵉ (pr2ᵉ sᵉ) (bᵉ (pr1ᵉ sᵉ))) (pr2ᵉ tᵉ))) ∘eᵉ
                    ( inv-left-unit-law-Σ-is-contrᵉ
                      ( is-torsorial-Id'ᵉ (pr1ᵉ tᵉ))
                      ( pairᵉ (pr1ᵉ tᵉ) reflᵉ))))))
            ( count-Σᵉ eᵉ
              ( λ tᵉ →
                count-eqᵉ
                  ( has-decidable-equality-is-finiteᵉ (gᵉ (pr1ᵉ tᵉ)))
                  ( bᵉ (pr1ᵉ tᵉ))
                  ( pr2ᵉ tᵉ)))))

abstract
  is-finite-base-is-finite-Σ-mere-sectionᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    type-trunc-Propᵉ ((aᵉ : Aᵉ) → Bᵉ aᵉ) →
    is-finiteᵉ (Σᵉ Aᵉ Bᵉ) → ((aᵉ : Aᵉ) → is-finiteᵉ (Bᵉ aᵉ)) → is-finiteᵉ Aᵉ
  is-finite-base-is-finite-Σ-mere-sectionᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} Hᵉ fᵉ gᵉ =
    apply-universal-property-trunc-Propᵉ Hᵉ
      ( is-finite-Propᵉ Aᵉ)
      ( λ bᵉ → is-finite-base-is-finite-Σ-sectionᵉ bᵉ fᵉ gᵉ)
```

### If `B` is a family of finite inhabited types over a set `A` and `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-Σ-merely-inhabitedᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} →
    is-setᵉ Aᵉ → (bᵉ : (aᵉ : Aᵉ) → type-trunc-Propᵉ (Bᵉ aᵉ)) →
    is-finiteᵉ (Σᵉ Aᵉ Bᵉ) → ((aᵉ : Aᵉ) → is-finiteᵉ (Bᵉ aᵉ)) → is-finiteᵉ Aᵉ
  is-finite-base-is-finite-Σ-merely-inhabitedᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} Kᵉ bᵉ fᵉ gᵉ =
    is-finite-base-is-finite-Σ-mere-sectionᵉ
      ( choice-is-finite-Σ-is-finite-fiberᵉ Kᵉ fᵉ gᵉ bᵉ)
      ( fᵉ)
      ( gᵉ)
```

### If `B` is a family of finite types over `A` with finite complement, and if `Σ A B` is finite, then `A` is finite

```agda
abstract
  is-finite-base-is-finite-complementᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} → is-setᵉ Aᵉ →
    is-finiteᵉ (Σᵉ Aᵉ Bᵉ) → (gᵉ : (aᵉ : Aᵉ) → is-finiteᵉ (Bᵉ aᵉ)) →
    is-finiteᵉ (complementᵉ Bᵉ) → is-finiteᵉ Aᵉ
  is-finite-base-is-finite-complementᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} Kᵉ fᵉ gᵉ hᵉ =
    is-finite-equivᵉ
      ( ( right-unit-law-Σ-is-contrᵉ
          ( λ xᵉ →
            is-proof-irrelevant-is-propᵉ
              ( is-property-is-inhabited-or-emptyᵉ (Bᵉ xᵉ))
              ( is-inhabited-or-empty-is-finiteᵉ (gᵉ xᵉ)))) ∘eᵉ
        ( inv-equivᵉ
          ( left-distributive-Σ-coproductᵉ Aᵉ
            ( λ xᵉ → type-trunc-Propᵉ (Bᵉ xᵉ))
            ( λ xᵉ → is-emptyᵉ (Bᵉ xᵉ)))))
      ( is-finite-coproductᵉ
        ( is-finite-base-is-finite-Σ-merely-inhabitedᵉ
          ( is-set-type-subtypeᵉ (λ xᵉ → trunc-Propᵉ _) Kᵉ)
          ( λ tᵉ → pr2ᵉ tᵉ)
          ( is-finite-equivᵉ
            ( equiv-right-swap-Σᵉ)
            ( is-finite-Σᵉ
              ( fᵉ)
              ( λ xᵉ → is-finite-type-trunc-Propᵉ (gᵉ (pr1ᵉ xᵉ)))))
          ( λ xᵉ → gᵉ (pr1ᵉ xᵉ)))
        ( hᵉ))
```