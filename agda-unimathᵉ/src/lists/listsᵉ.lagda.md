# Lists

```agda
module lists.listsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.maybeᵉ
open import foundation.negationᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.setsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.truncated-typesᵉ
open import foundation.truncation-levelsᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ listsᵉ ofᵉ elementsᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ definedᵉ inductively,ᵉ with anᵉ
emptyᵉ listᵉ andᵉ anᵉ operationᵉ thatᵉ extendsᵉ aᵉ listᵉ with oneᵉ elementᵉ fromᵉ `A`.ᵉ

## Definition

### The inductive definition of the type of lists

```agda
data listᵉ {lᵉ : Level} (Aᵉ : UUᵉ lᵉ) : UUᵉ lᵉ where
  nilᵉ : listᵉ Aᵉ
  consᵉ : Aᵉ → listᵉ Aᵉ → listᵉ Aᵉ

```

### Predicates on the type of lists

```agda
is-nil-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → UUᵉ lᵉ
is-nil-listᵉ lᵉ = (lᵉ ＝ᵉ nilᵉ)

is-nonnil-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → UUᵉ lᵉ
is-nonnil-listᵉ lᵉ = ¬ᵉ (is-nil-listᵉ lᵉ)

is-cons-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → UUᵉ lᵉ
is-cons-listᵉ {l1ᵉ} {Aᵉ} lᵉ = Σᵉ (Aᵉ ×ᵉ listᵉ Aᵉ) (λ (aᵉ ,ᵉ l'ᵉ) → lᵉ ＝ᵉ consᵉ aᵉ l'ᵉ)
```

## Operations

### Fold

```agda
fold-listᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (bᵉ : Bᵉ) (μᵉ : Aᵉ → (Bᵉ → Bᵉ)) →
  listᵉ Aᵉ → Bᵉ
fold-listᵉ bᵉ μᵉ nilᵉ = bᵉ
fold-listᵉ bᵉ μᵉ (consᵉ aᵉ lᵉ) = μᵉ aᵉ (fold-listᵉ bᵉ μᵉ lᵉ)
```

### The dual of `cons`

```agda
snocᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → Aᵉ → listᵉ Aᵉ
snocᵉ nilᵉ aᵉ = consᵉ aᵉ nilᵉ
snocᵉ (consᵉ bᵉ lᵉ) aᵉ = consᵉ bᵉ (snocᵉ lᵉ aᵉ)
```

### The unit list

```agda
unit-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → listᵉ Aᵉ
unit-listᵉ aᵉ = consᵉ aᵉ nilᵉ
```

### The length of a list

```agda
length-listᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → ℕᵉ
length-listᵉ = fold-listᵉ 0 (λ aᵉ → succ-ℕᵉ)
```

### The elementhood predicate on lists

```agda
infix 6 _∈-listᵉ_

data _∈-listᵉ_ {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} : Aᵉ → listᵉ Aᵉ → UUᵉ lᵉ where
  is-headᵉ : (aᵉ : Aᵉ) (lᵉ : listᵉ Aᵉ) → aᵉ ∈-listᵉ (consᵉ aᵉ lᵉ)
  is-in-tailᵉ : (aᵉ xᵉ : Aᵉ) (lᵉ : listᵉ Aᵉ) → aᵉ ∈-listᵉ lᵉ → aᵉ ∈-listᵉ (consᵉ xᵉ lᵉ)
```

## Properties

### A list that uses cons is not nil

```agda
is-nonnil-cons-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  (aᵉ : Aᵉ) → (lᵉ : listᵉ Aᵉ) → is-nonnil-listᵉ (consᵉ aᵉ lᵉ)
is-nonnil-cons-listᵉ aᵉ lᵉ ()

is-nonnil-is-cons-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  (lᵉ : listᵉ Aᵉ) → is-cons-listᵉ lᵉ → is-nonnil-listᵉ lᵉ
is-nonnil-is-cons-listᵉ lᵉ ((aᵉ ,ᵉ l'ᵉ) ,ᵉ reflᵉ) qᵉ =
  is-nonnil-cons-listᵉ aᵉ l'ᵉ qᵉ
```

### A list that uses cons is not nil

```agda
is-cons-is-nonnil-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  (lᵉ : listᵉ Aᵉ) → is-nonnil-listᵉ lᵉ → is-cons-listᵉ lᵉ
is-cons-is-nonnil-listᵉ nilᵉ pᵉ = ex-falsoᵉ (pᵉ reflᵉ)
is-cons-is-nonnil-listᵉ (consᵉ xᵉ lᵉ) pᵉ = ((xᵉ ,ᵉ lᵉ) ,ᵉ reflᵉ)

head-is-nonnil-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  (lᵉ : listᵉ Aᵉ) → is-nonnil-listᵉ lᵉ → Aᵉ
head-is-nonnil-listᵉ lᵉ pᵉ =
  pr1ᵉ (pr1ᵉ (is-cons-is-nonnil-listᵉ lᵉ pᵉ))

tail-is-nonnil-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} →
  (lᵉ : listᵉ Aᵉ) → is-nonnil-listᵉ lᵉ → listᵉ Aᵉ
tail-is-nonnil-listᵉ lᵉ pᵉ =
  pr2ᵉ (pr1ᵉ (is-cons-is-nonnil-listᵉ lᵉ pᵉ))
```

### Characterizing the identity type of lists

```agda
Eq-listᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → listᵉ Aᵉ → listᵉ Aᵉ → UUᵉ l1ᵉ
Eq-listᵉ {l1ᵉ} nilᵉ nilᵉ = raise-unitᵉ l1ᵉ
Eq-listᵉ {l1ᵉ} nilᵉ (consᵉ xᵉ l'ᵉ) = raise-emptyᵉ l1ᵉ
Eq-listᵉ {l1ᵉ} (consᵉ xᵉ lᵉ) nilᵉ = raise-emptyᵉ l1ᵉ
Eq-listᵉ {l1ᵉ} (consᵉ xᵉ lᵉ) (consᵉ x'ᵉ l'ᵉ) = (Idᵉ xᵉ x'ᵉ) ×ᵉ Eq-listᵉ lᵉ l'ᵉ

refl-Eq-listᵉ : {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ : listᵉ Aᵉ) → Eq-listᵉ lᵉ lᵉ
refl-Eq-listᵉ nilᵉ = raise-starᵉ
refl-Eq-listᵉ (consᵉ xᵉ lᵉ) = pairᵉ reflᵉ (refl-Eq-listᵉ lᵉ)

Eq-eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ l'ᵉ : listᵉ Aᵉ) → Idᵉ lᵉ l'ᵉ → Eq-listᵉ lᵉ l'ᵉ
Eq-eq-listᵉ lᵉ .lᵉ reflᵉ = refl-Eq-listᵉ lᵉ

eq-Eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ l'ᵉ : listᵉ Aᵉ) → Eq-listᵉ lᵉ l'ᵉ → Idᵉ lᵉ l'ᵉ
eq-Eq-listᵉ nilᵉ nilᵉ (map-raiseᵉ starᵉ) = reflᵉ
eq-Eq-listᵉ nilᵉ (consᵉ xᵉ l'ᵉ) (map-raiseᵉ fᵉ) = ex-falsoᵉ fᵉ
eq-Eq-listᵉ (consᵉ xᵉ lᵉ) nilᵉ (map-raiseᵉ fᵉ) = ex-falsoᵉ fᵉ
eq-Eq-listᵉ (consᵉ xᵉ lᵉ) (consᵉ .xᵉ l'ᵉ) (pairᵉ reflᵉ eᵉ) =
  apᵉ (consᵉ xᵉ) (eq-Eq-listᵉ lᵉ l'ᵉ eᵉ)

square-eq-Eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {xᵉ : Aᵉ} {lᵉ l'ᵉ : listᵉ Aᵉ} (pᵉ : Idᵉ lᵉ l'ᵉ) →
  Idᵉ
    ( Eq-eq-listᵉ (consᵉ xᵉ lᵉ) (consᵉ xᵉ l'ᵉ) (apᵉ (consᵉ xᵉ) pᵉ))
    ( pairᵉ reflᵉ (Eq-eq-listᵉ lᵉ l'ᵉ pᵉ))
square-eq-Eq-listᵉ reflᵉ = reflᵉ

is-section-eq-Eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ l'ᵉ : listᵉ Aᵉ) (eᵉ : Eq-listᵉ lᵉ l'ᵉ) →
  Idᵉ (Eq-eq-listᵉ lᵉ l'ᵉ (eq-Eq-listᵉ lᵉ l'ᵉ eᵉ)) eᵉ
is-section-eq-Eq-listᵉ nilᵉ nilᵉ eᵉ = eq-is-contrᵉ is-contr-raise-unitᵉ
is-section-eq-Eq-listᵉ nilᵉ (consᵉ xᵉ l'ᵉ) eᵉ = ex-falsoᵉ (is-empty-raise-emptyᵉ eᵉ)
is-section-eq-Eq-listᵉ (consᵉ xᵉ lᵉ) nilᵉ eᵉ = ex-falsoᵉ (is-empty-raise-emptyᵉ eᵉ)
is-section-eq-Eq-listᵉ (consᵉ xᵉ lᵉ) (consᵉ .xᵉ l'ᵉ) (pairᵉ reflᵉ eᵉ) =
  ( square-eq-Eq-listᵉ (eq-Eq-listᵉ lᵉ l'ᵉ eᵉ)) ∙ᵉ
  ( eq-pair-eq-fiberᵉ (is-section-eq-Eq-listᵉ lᵉ l'ᵉ eᵉ))

eq-Eq-refl-Eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ : listᵉ Aᵉ) →
  Idᵉ (eq-Eq-listᵉ lᵉ lᵉ (refl-Eq-listᵉ lᵉ)) reflᵉ
eq-Eq-refl-Eq-listᵉ nilᵉ = reflᵉ
eq-Eq-refl-Eq-listᵉ (consᵉ xᵉ lᵉ) = ap²ᵉ (consᵉ xᵉ) (eq-Eq-refl-Eq-listᵉ lᵉ)

is-retraction-eq-Eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ l'ᵉ : listᵉ Aᵉ) (pᵉ : Idᵉ lᵉ l'ᵉ) →
  Idᵉ (eq-Eq-listᵉ lᵉ l'ᵉ (Eq-eq-listᵉ lᵉ l'ᵉ pᵉ)) pᵉ
is-retraction-eq-Eq-listᵉ nilᵉ .nilᵉ reflᵉ = reflᵉ
is-retraction-eq-Eq-listᵉ (consᵉ xᵉ lᵉ) .(consᵉ xᵉ lᵉ) reflᵉ =
  eq-Eq-refl-Eq-listᵉ (consᵉ xᵉ lᵉ)

is-equiv-Eq-eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ l'ᵉ : listᵉ Aᵉ) → is-equivᵉ (Eq-eq-listᵉ lᵉ l'ᵉ)
is-equiv-Eq-eq-listᵉ lᵉ l'ᵉ =
  is-equiv-is-invertibleᵉ
    ( eq-Eq-listᵉ lᵉ l'ᵉ)
    ( is-section-eq-Eq-listᵉ lᵉ l'ᵉ)
    ( is-retraction-eq-Eq-listᵉ lᵉ l'ᵉ)

equiv-Eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ l'ᵉ : listᵉ Aᵉ) → Idᵉ lᵉ l'ᵉ ≃ᵉ Eq-listᵉ lᵉ l'ᵉ
equiv-Eq-listᵉ lᵉ l'ᵉ =
  pairᵉ (Eq-eq-listᵉ lᵉ l'ᵉ) (is-equiv-Eq-eq-listᵉ lᵉ l'ᵉ)

is-torsorial-Eq-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (lᵉ : listᵉ Aᵉ) →
  is-torsorialᵉ (Eq-listᵉ lᵉ)
is-torsorial-Eq-listᵉ {Aᵉ = Aᵉ} lᵉ =
  is-contr-equiv'ᵉ
    ( Σᵉ (listᵉ Aᵉ) (Idᵉ lᵉ))
    ( equiv-totᵉ (equiv-Eq-listᵉ lᵉ))
    ( is-torsorial-Idᵉ lᵉ)

is-trunc-Eq-listᵉ :
  (kᵉ : 𝕋ᵉ) {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) Aᵉ →
  (lᵉ l'ᵉ : listᵉ Aᵉ) → is-truncᵉ (succ-𝕋ᵉ kᵉ) (Eq-listᵉ lᵉ l'ᵉ)
is-trunc-Eq-listᵉ kᵉ Hᵉ nilᵉ nilᵉ =
  is-trunc-is-contrᵉ (succ-𝕋ᵉ kᵉ) is-contr-raise-unitᵉ
is-trunc-Eq-listᵉ kᵉ Hᵉ nilᵉ (consᵉ xᵉ l'ᵉ) =
  is-trunc-is-emptyᵉ kᵉ is-empty-raise-emptyᵉ
is-trunc-Eq-listᵉ kᵉ Hᵉ (consᵉ xᵉ lᵉ) nilᵉ =
  is-trunc-is-emptyᵉ kᵉ is-empty-raise-emptyᵉ
is-trunc-Eq-listᵉ kᵉ Hᵉ (consᵉ xᵉ lᵉ) (consᵉ yᵉ l'ᵉ) =
  is-trunc-productᵉ (succ-𝕋ᵉ kᵉ) (Hᵉ xᵉ yᵉ) (is-trunc-Eq-listᵉ kᵉ Hᵉ lᵉ l'ᵉ)

is-trunc-listᵉ :
  (kᵉ : 𝕋ᵉ) {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) Aᵉ →
  is-truncᵉ (succ-𝕋ᵉ (succ-𝕋ᵉ kᵉ)) (listᵉ Aᵉ)
is-trunc-listᵉ kᵉ Hᵉ lᵉ l'ᵉ =
  is-trunc-equivᵉ
    ( succ-𝕋ᵉ kᵉ)
    ( Eq-listᵉ lᵉ l'ᵉ)
    ( equiv-Eq-listᵉ lᵉ l'ᵉ)
    ( is-trunc-Eq-listᵉ kᵉ Hᵉ lᵉ l'ᵉ)

is-set-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → is-setᵉ Aᵉ → is-setᵉ (listᵉ Aᵉ)
is-set-listᵉ = is-trunc-listᵉ neg-two-𝕋ᵉ

list-Setᵉ : {lᵉ : Level} → Setᵉ lᵉ → Setᵉ lᵉ
list-Setᵉ Aᵉ = pairᵉ (listᵉ (type-Setᵉ Aᵉ)) (is-set-listᵉ (is-set-type-Setᵉ Aᵉ))
```

### The length operation behaves well with respect to the other list operations

```agda
length-nilᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} →
  Idᵉ (length-listᵉ {Aᵉ = Aᵉ} nilᵉ) zero-ℕᵉ
length-nilᵉ = reflᵉ

is-nil-is-zero-length-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (lᵉ : listᵉ Aᵉ) →
  is-zero-ℕᵉ (length-listᵉ lᵉ) →
  is-nil-listᵉ lᵉ
is-nil-is-zero-length-listᵉ nilᵉ pᵉ = reflᵉ

is-nonnil-is-nonzero-length-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (lᵉ : listᵉ Aᵉ) →
  is-nonzero-ℕᵉ (length-listᵉ lᵉ) →
  is-nonnil-listᵉ lᵉ
is-nonnil-is-nonzero-length-listᵉ nilᵉ pᵉ qᵉ = pᵉ reflᵉ
is-nonnil-is-nonzero-length-listᵉ (consᵉ xᵉ lᵉ) pᵉ ()

is-nonzero-length-is-nonnil-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (lᵉ : listᵉ Aᵉ) →
  is-nonnil-listᵉ lᵉ →
  is-nonzero-ℕᵉ (length-listᵉ lᵉ)
is-nonzero-length-is-nonnil-listᵉ nilᵉ pᵉ qᵉ = pᵉ reflᵉ

lenght-tail-is-nonnil-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (lᵉ : listᵉ Aᵉ) → (pᵉ : is-nonnil-listᵉ lᵉ) →
  succ-ℕᵉ (length-listᵉ (tail-is-nonnil-listᵉ lᵉ pᵉ)) ＝ᵉ
    length-listᵉ lᵉ
lenght-tail-is-nonnil-listᵉ nilᵉ pᵉ = ex-falsoᵉ (pᵉ reflᵉ)
lenght-tail-is-nonnil-listᵉ (consᵉ xᵉ lᵉ) pᵉ = reflᵉ
```

### Head and tail operations

Weᵉ defineᵉ theᵉ headᵉ andᵉ tailᵉ operations,ᵉ andᵉ weᵉ defineᵉ theᵉ operationsᵉ ofᵉ pickingᵉ
andᵉ removingᵉ theᵉ lastᵉ elementᵉ fromᵉ aᵉ list.ᵉ

```agda
head-snoc-listᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (lᵉ : listᵉ Aᵉ) → Aᵉ → Aᵉ
head-snoc-listᵉ nilᵉ aᵉ = aᵉ
head-snoc-listᵉ (consᵉ hᵉ lᵉ) aᵉ = hᵉ

head-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → listᵉ Aᵉ → listᵉ Aᵉ
head-listᵉ nilᵉ = nilᵉ
head-listᵉ (consᵉ aᵉ xᵉ) = unit-listᵉ aᵉ

tail-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → listᵉ Aᵉ → listᵉ Aᵉ
tail-listᵉ nilᵉ = nilᵉ
tail-listᵉ (consᵉ aᵉ xᵉ) = xᵉ

last-element-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → listᵉ Aᵉ → listᵉ Aᵉ
last-element-listᵉ nilᵉ = nilᵉ
last-element-listᵉ (consᵉ aᵉ nilᵉ) = unit-listᵉ aᵉ
last-element-listᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) = last-element-listᵉ (consᵉ bᵉ xᵉ)
```

### Removing the last element of a list

```agda
remove-last-element-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → listᵉ Aᵉ → listᵉ Aᵉ
remove-last-element-listᵉ nilᵉ = nilᵉ
remove-last-element-listᵉ (consᵉ aᵉ nilᵉ) = nilᵉ
remove-last-element-listᵉ (consᵉ aᵉ (consᵉ bᵉ xᵉ)) =
  consᵉ aᵉ (remove-last-element-listᵉ (consᵉ bᵉ xᵉ))
```

### Properties of heads and tails and their duals

```agda
head-snoc-snoc-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) (aᵉ : Aᵉ) (bᵉ : Aᵉ) →
  head-listᵉ (snocᵉ (snocᵉ xᵉ aᵉ) bᵉ) ＝ᵉ head-listᵉ (snocᵉ xᵉ aᵉ)
head-snoc-snoc-listᵉ nilᵉ aᵉ bᵉ = reflᵉ
head-snoc-snoc-listᵉ (consᵉ cᵉ xᵉ) aᵉ bᵉ = reflᵉ

tail-snoc-snoc-listᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) (aᵉ : Aᵉ) (bᵉ : Aᵉ) →
  tail-listᵉ (snocᵉ (snocᵉ xᵉ aᵉ) bᵉ) ＝ᵉ snocᵉ (tail-listᵉ (snocᵉ xᵉ aᵉ)) bᵉ
tail-snoc-snoc-listᵉ nilᵉ aᵉ bᵉ = reflᵉ
tail-snoc-snoc-listᵉ (consᵉ cᵉ xᵉ) aᵉ bᵉ = reflᵉ

last-element-snocᵉ :
  {l1ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (xᵉ : listᵉ Aᵉ) (aᵉ : Aᵉ) →
  Idᵉ (last-element-listᵉ (snocᵉ xᵉ aᵉ)) (unit-listᵉ aᵉ)
last-element-snocᵉ nilᵉ aᵉ = reflᵉ
last-element-snocᵉ (consᵉ bᵉ nilᵉ) aᵉ = reflᵉ
last-element-snocᵉ (consᵉ bᵉ (consᵉ cᵉ xᵉ)) aᵉ =
  last-element-snocᵉ (consᵉ cᵉ xᵉ) aᵉ
```

### Algebra structure on the type of lists of elements of `A`

```agda
map-algebra-listᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  Maybeᵉ (Aᵉ ×ᵉ listᵉ Aᵉ) → listᵉ Aᵉ
map-algebra-listᵉ Aᵉ (inlᵉ (aᵉ ,ᵉ xᵉ)) = consᵉ aᵉ xᵉ
map-algebra-listᵉ Aᵉ (inrᵉ starᵉ) = nilᵉ

map-inv-algebra-listᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  listᵉ Aᵉ → Maybeᵉ (Aᵉ ×ᵉ listᵉ Aᵉ)
map-inv-algebra-listᵉ Aᵉ nilᵉ = inrᵉ starᵉ
map-inv-algebra-listᵉ Aᵉ (consᵉ aᵉ xᵉ) = inlᵉ (pairᵉ aᵉ xᵉ)

is-section-map-inv-algebra-listᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  (map-algebra-listᵉ Aᵉ ∘ᵉ map-inv-algebra-listᵉ Aᵉ) ~ᵉ idᵉ
is-section-map-inv-algebra-listᵉ Aᵉ nilᵉ = reflᵉ
is-section-map-inv-algebra-listᵉ Aᵉ (consᵉ aᵉ xᵉ) = reflᵉ

is-retraction-map-inv-algebra-listᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) →
  (map-inv-algebra-listᵉ Aᵉ ∘ᵉ map-algebra-listᵉ Aᵉ) ~ᵉ idᵉ
is-retraction-map-inv-algebra-listᵉ Aᵉ (inlᵉ (aᵉ ,ᵉ xᵉ)) = reflᵉ
is-retraction-map-inv-algebra-listᵉ Aᵉ (inrᵉ starᵉ) = reflᵉ

is-equiv-map-algebra-listᵉ :
  {l1ᵉ : Level} (Aᵉ : UUᵉ l1ᵉ) → is-equivᵉ (map-algebra-listᵉ Aᵉ)
is-equiv-map-algebra-listᵉ Aᵉ =
  is-equiv-is-invertibleᵉ
    ( map-inv-algebra-listᵉ Aᵉ)
    ( is-section-map-inv-algebra-listᵉ Aᵉ)
    ( is-retraction-map-inv-algebra-listᵉ Aᵉ)
```