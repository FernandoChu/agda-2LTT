# Retracts of finite types

```agda
module univalent-combinatorics.retracts-of-finite-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-embeddingsᵉ
open import foundation.decidable-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.injective-mapsᵉ
open import foundation.retractionsᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.counting-decidable-subtypesᵉ
open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.equality-standard-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Properties

### If a map `i : A → Fin k` has a retraction, then it is a decidable map

```agda
is-decidable-map-retraction-Finᵉ :
  {l1ᵉ : Level} (kᵉ : ℕᵉ) {Aᵉ : UUᵉ l1ᵉ} (iᵉ : Aᵉ → Finᵉ kᵉ) →
  retractionᵉ iᵉ → is-decidable-mapᵉ iᵉ
is-decidable-map-retraction-Finᵉ kᵉ =
  is-decidable-map-retractionᵉ (has-decidable-equality-Finᵉ kᵉ)
```

### If a map `i : A → B` into a finite type `B` has a retraction, then `i` is decidable and `A` is finite

```agda
is-decidable-map-retraction-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : countᵉ Bᵉ) (iᵉ : Aᵉ → Bᵉ) →
  retractionᵉ iᵉ → is-decidable-mapᵉ iᵉ
is-decidable-map-retraction-countᵉ eᵉ =
  is-decidable-map-retractionᵉ (has-decidable-equality-countᵉ eᵉ)

is-decidable-map-retraction-is-finiteᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (Hᵉ : is-finiteᵉ Bᵉ) (iᵉ : Aᵉ → Bᵉ) →
  retractionᵉ iᵉ → is-decidable-mapᵉ iᵉ
is-decidable-map-retraction-is-finiteᵉ Hᵉ =
  is-decidable-map-retractionᵉ (has-decidable-equality-is-finiteᵉ Hᵉ)
```

```agda
abstract
  is-emb-retract-countᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : countᵉ Bᵉ) (iᵉ : Aᵉ → Bᵉ) →
    retractionᵉ iᵉ → is-embᵉ iᵉ
  is-emb-retract-countᵉ eᵉ iᵉ Rᵉ =
    is-emb-is-injectiveᵉ (is-set-countᵉ eᵉ) (is-injective-retractionᵉ iᵉ Rᵉ)

emb-retract-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : countᵉ Bᵉ) (iᵉ : Aᵉ → Bᵉ) →
  retractionᵉ iᵉ → Aᵉ ↪ᵉ Bᵉ
pr1ᵉ (emb-retract-countᵉ eᵉ iᵉ Rᵉ) = iᵉ
pr2ᵉ (emb-retract-countᵉ eᵉ iᵉ Rᵉ) = is-emb-retract-countᵉ eᵉ iᵉ Rᵉ

decidable-emb-retract-countᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : countᵉ Bᵉ) (iᵉ : Aᵉ → Bᵉ) →
  retractionᵉ iᵉ → Aᵉ ↪ᵈᵉ Bᵉ
pr1ᵉ (decidable-emb-retract-countᵉ eᵉ iᵉ Rᵉ) = iᵉ
pr1ᵉ (pr2ᵉ (decidable-emb-retract-countᵉ eᵉ iᵉ Rᵉ)) = is-emb-retract-countᵉ eᵉ iᵉ Rᵉ
pr2ᵉ (pr2ᵉ (decidable-emb-retract-countᵉ eᵉ iᵉ Rᵉ)) =
  is-decidable-map-retraction-countᵉ eᵉ iᵉ Rᵉ

count-retractᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} →
  Aᵉ retract-ofᵉ Bᵉ → countᵉ Bᵉ → countᵉ Aᵉ
count-retractᵉ (pairᵉ iᵉ Rᵉ) eᵉ =
  count-equivᵉ
    ( equiv-total-fiberᵉ iᵉ)
    ( count-decidable-subtypeᵉ
      ( decidable-subtype-decidable-embᵉ (decidable-emb-retract-countᵉ eᵉ iᵉ Rᵉ))
      ( eᵉ))

abstract
  is-finite-retractᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} → Aᵉ retract-ofᵉ Bᵉ →
    is-finiteᵉ Bᵉ → is-finiteᵉ Aᵉ
  is-finite-retractᵉ Rᵉ = map-trunc-Propᵉ (count-retractᵉ Rᵉ)
```