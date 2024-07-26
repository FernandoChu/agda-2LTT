# Fibers of maps between finite types

```agda
module univalent-combinatorics.fibers-of-mapsᵉ where

open import foundation.fibers-of-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ
open import elementary-number-theory.sums-of-natural-numbersᵉ

open import foundation.contractible-typesᵉ
open import foundation.decidable-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.sectionsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-dependent-pair-typesᵉ
open import univalent-combinatorics.decidable-propositionsᵉ
open import univalent-combinatorics.dependent-pair-typesᵉ
open import univalent-combinatorics.double-countingᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Theᵉ fibersᵉ ofᵉ mapsᵉ betweenᵉ finiteᵉ typesᵉ areᵉ finite.ᵉ

## Properties

### If `A` and `B` can be counted, then the fibers of a map `f : A → B` can be counted

```agda
count-fiberᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  countᵉ Aᵉ → countᵉ Bᵉ → (yᵉ : Bᵉ) → countᵉ (fiberᵉ fᵉ yᵉ)
count-fiberᵉ fᵉ count-Aᵉ count-Bᵉ =
  count-fiber-count-Σ-count-baseᵉ
    ( count-Bᵉ)
    ( count-equiv'ᵉ (equiv-total-fiberᵉ fᵉ) count-Aᵉ)

abstract
  sum-number-of-elements-count-fiberᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    (count-Aᵉ : countᵉ Aᵉ) (count-Bᵉ : countᵉ Bᵉ) →
    Idᵉ
      ( sum-count-ℕᵉ count-Bᵉ
        ( λ xᵉ → number-of-elements-countᵉ (count-fiberᵉ fᵉ count-Aᵉ count-Bᵉ xᵉ)))
      ( number-of-elements-countᵉ count-Aᵉ)
  sum-number-of-elements-count-fiberᵉ fᵉ count-Aᵉ count-Bᵉ =
    sum-number-of-elements-count-fiber-count-Σᵉ count-Bᵉ
      ( count-equiv'ᵉ (equiv-total-fiberᵉ fᵉ) count-Aᵉ)

abstract
  double-counting-fiberᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (count-Aᵉ : countᵉ Aᵉ) →
    (count-Bᵉ : countᵉ Bᵉ) (count-fiber-fᵉ : (yᵉ : Bᵉ) → countᵉ (fiberᵉ fᵉ yᵉ)) (yᵉ : Bᵉ) →
    Idᵉ
      ( number-of-elements-countᵉ (count-fiber-fᵉ yᵉ))
      ( number-of-elements-countᵉ (count-fiberᵉ fᵉ count-Aᵉ count-Bᵉ yᵉ))
  double-counting-fiberᵉ fᵉ count-Aᵉ count-Bᵉ count-fiber-fᵉ yᵉ =
    double-countingᵉ (count-fiber-fᵉ yᵉ) (count-fiberᵉ fᵉ count-Aᵉ count-Bᵉ yᵉ)
```

### Fibers of maps between finite types are finite

```agda
abstract
  is-finite-fiberᵉ :
    {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ) →
    is-finiteᵉ Xᵉ → is-finiteᵉ Yᵉ → (yᵉ : Yᵉ) → is-finiteᵉ (fiberᵉ fᵉ yᵉ)
  is-finite-fiberᵉ fᵉ is-finite-Xᵉ is-finite-Yᵉ yᵉ =
    apply-universal-property-trunc-Propᵉ
      ( is-finite-Xᵉ)
      ( is-finite-Propᵉ (fiberᵉ fᵉ yᵉ))
      ( λ Hᵉ →
        apply-universal-property-trunc-Propᵉ
          ( is-finite-Yᵉ)
          ( is-finite-Propᵉ (fiberᵉ fᵉ yᵉ))
          ( λ Kᵉ → unit-trunc-Propᵉ (count-fiberᵉ fᵉ Hᵉ Kᵉ yᵉ)))

fiber-𝔽ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝔽ᵉ l1ᵉ) (Yᵉ : 𝔽ᵉ l2ᵉ) (fᵉ : type-𝔽ᵉ Xᵉ → type-𝔽ᵉ Yᵉ) →
  type-𝔽ᵉ Yᵉ → 𝔽ᵉ (l1ᵉ ⊔ l2ᵉ)
pr1ᵉ (fiber-𝔽ᵉ Xᵉ Yᵉ fᵉ yᵉ) = fiberᵉ fᵉ yᵉ
pr2ᵉ (fiber-𝔽ᵉ Xᵉ Yᵉ fᵉ yᵉ) =
  is-finite-fiberᵉ fᵉ (is-finite-type-𝔽ᵉ Xᵉ) (is-finite-type-𝔽ᵉ Yᵉ) yᵉ
```

###

```agda
abstract
  is-finite-fiber-map-section-familyᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} (bᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ) →
    is-finiteᵉ (Σᵉ Aᵉ Bᵉ) → ((xᵉ : Aᵉ) → is-finiteᵉ (Bᵉ xᵉ)) →
    (tᵉ : Σᵉ Aᵉ Bᵉ) → is-finiteᵉ (fiberᵉ (map-section-familyᵉ bᵉ) tᵉ)
  is-finite-fiber-map-section-familyᵉ {l1ᵉ} {l2ᵉ} {Aᵉ} {Bᵉ} bᵉ fᵉ gᵉ (pairᵉ yᵉ zᵉ) =
    is-finite-equiv'ᵉ
      ( ( ( left-unit-law-Σ-is-contrᵉ
            ( is-torsorial-Id'ᵉ yᵉ)
            ( pairᵉ yᵉ reflᵉ)) ∘eᵉ
          ( inv-associative-Σᵉ Aᵉ
            ( λ xᵉ → Idᵉ xᵉ yᵉ)
            ( λ tᵉ → Idᵉ (trᵉ Bᵉ (pr2ᵉ tᵉ) (bᵉ (pr1ᵉ tᵉ))) zᵉ))) ∘eᵉ
        ( equiv-totᵉ (λ xᵉ → equiv-pair-eq-Σᵉ (pairᵉ xᵉ (bᵉ xᵉ)) (pairᵉ yᵉ zᵉ))))
      ( is-finite-eqᵉ (has-decidable-equality-is-finiteᵉ (gᵉ yᵉ)))
```

### The fibers of maps between finite types are decidable

```agda
is-decidable-fiber-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
  countᵉ Aᵉ → countᵉ Bᵉ → (yᵉ : Bᵉ) → is-decidableᵉ (fiberᵉ fᵉ yᵉ)
is-decidable-fiber-countᵉ fᵉ count-Aᵉ count-Bᵉ yᵉ =
  is-decidable-countᵉ (count-fiberᵉ fᵉ count-Aᵉ count-Bᵉ yᵉ)

is-decidable-fiber-Finᵉ :
  {kᵉ lᵉ : ℕᵉ} (fᵉ : Finᵉ kᵉ → Finᵉ lᵉ) → (yᵉ : Finᵉ lᵉ) → is-decidableᵉ (fiberᵉ fᵉ yᵉ)
is-decidable-fiber-Finᵉ {kᵉ} {lᵉ} fᵉ yᵉ =
  is-decidable-fiber-countᵉ fᵉ (count-Finᵉ kᵉ) (count-Finᵉ lᵉ) yᵉ
```

### If `f : A → B` and `B` is finite, then `A` is finite if and only if the fibers of `f` are finite

```agda
equiv-is-finite-domain-is-finite-fiberᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  (Bᵉ : 𝔽ᵉ l2ᵉ) (fᵉ : Aᵉ → (type-𝔽ᵉ Bᵉ)) →
  ((bᵉ : type-𝔽ᵉ Bᵉ) → is-finiteᵉ (fiberᵉ fᵉ bᵉ)) ≃ᵉ is-finiteᵉ Aᵉ
equiv-is-finite-domain-is-finite-fiberᵉ {Aᵉ = Aᵉ} Bᵉ fᵉ =
  equiv-iff-is-propᵉ
    ( is-prop-Πᵉ (λ bᵉ → is-prop-is-finiteᵉ (fiberᵉ fᵉ bᵉ)))
    ( is-prop-is-finiteᵉ Aᵉ)
    ( λ Pᵉ →
      is-finite-equivᵉ
        ( equiv-total-fiberᵉ fᵉ)
        ( is-finite-Σᵉ (is-finite-type-𝔽ᵉ Bᵉ) Pᵉ))
    ( λ Pᵉ → is-finite-fiberᵉ fᵉ Pᵉ (is-finite-type-𝔽ᵉ Bᵉ))
```