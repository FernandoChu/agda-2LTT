# Dependent identifications

```agda
module foundation.dependent-identificationsᵉ where

open import foundation-core.dependent-identificationsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.strictly-right-unital-concatenation-identificationsᵉ
open import foundation.transport-along-higher-identificationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.transport-along-identificationsᵉ
```

</details>

## Idea

Weᵉ characterizeᵉ dependentᵉ pathsᵉ in theᵉ familyᵉ ofᵉ depedentᵉ paths;ᵉ defineᵉ theᵉ
groupoidalᵉ operatorsᵉ onᵉ dependentᵉ paths;ᵉ defineᵉ theᵉ coherenceᵉ paths;ᵉ proveᵉ theᵉ
operatorsᵉ areᵉ equivalences.ᵉ

## Properites

### Computing twice iterated dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  map-compute-dependent-identification²ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ x'ᵉ y'ᵉ) →
    p'ᵉ ＝ᵉ tr²ᵉ Bᵉ αᵉ x'ᵉ ∙ᵉ q'ᵉ → dependent-identification²ᵉ Bᵉ αᵉ p'ᵉ q'ᵉ
  map-compute-dependent-identification²ᵉ reflᵉ ._ reflᵉ reflᵉ =
    reflᵉ

  map-inv-compute-dependent-identification²ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ x'ᵉ y'ᵉ) →
    dependent-identification²ᵉ Bᵉ αᵉ p'ᵉ q'ᵉ → p'ᵉ ＝ᵉ tr²ᵉ Bᵉ αᵉ x'ᵉ ∙ᵉ q'ᵉ
  map-inv-compute-dependent-identification²ᵉ reflᵉ reflᵉ ._ reflᵉ =
    reflᵉ

  is-section-map-inv-compute-dependent-identification²ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ x'ᵉ y'ᵉ) →
    ( map-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ ∘ᵉ
      map-inv-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-dependent-identification²ᵉ reflᵉ reflᵉ ._ reflᵉ =
    reflᵉ

  is-retraction-map-inv-compute-dependent-identification²ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ x'ᵉ y'ᵉ) →
    ( map-inv-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ ∘ᵉ
      map-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-dependent-identification²ᵉ reflᵉ ._ reflᵉ reflᵉ =
    reflᵉ

  is-equiv-map-compute-dependent-identification²ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ x'ᵉ y'ᵉ) →
    is-equivᵉ (map-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ)
  is-equiv-map-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ)
      ( is-section-map-inv-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ)
      ( is-retraction-map-inv-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ)

  compute-dependent-identification²ᵉ :
    {xᵉ yᵉ : Aᵉ} {pᵉ qᵉ : xᵉ ＝ᵉ yᵉ} (αᵉ : pᵉ ＝ᵉ qᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ x'ᵉ y'ᵉ) →
    (p'ᵉ ＝ᵉ tr²ᵉ Bᵉ αᵉ x'ᵉ ∙ᵉ q'ᵉ) ≃ᵉ dependent-identification²ᵉ Bᵉ αᵉ p'ᵉ q'ᵉ
  pr1ᵉ (compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ) =
    map-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ
  pr2ᵉ (compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ) =
    is-equiv-map-compute-dependent-identification²ᵉ αᵉ p'ᵉ q'ᵉ
```

### The groupoidal structure of dependent identifications

Weᵉ showᵉ thatᵉ thereᵉ isᵉ groupoidalᵉ structureᵉ onᵉ theᵉ dependentᵉ identifications.ᵉ Theᵉ
statementᵉ ofᵉ theᵉ groupoidᵉ lawsᵉ useᵉ dependentᵉ identifications,ᵉ dueᵉ to theᵉ
dependentᵉ natureᵉ ofᵉ dependentᵉ identifications.ᵉ

#### Concatenation of dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  concat-dependent-identificationᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ} {z'ᵉ : Bᵉ zᵉ} →
    dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ →
    dependent-identificationᵉ Bᵉ qᵉ y'ᵉ z'ᵉ →
    dependent-identificationᵉ Bᵉ (pᵉ ∙ᵉ qᵉ) x'ᵉ z'ᵉ
  concat-dependent-identificationᵉ reflᵉ qᵉ reflᵉ q'ᵉ = q'ᵉ

  compute-concat-dependent-identification-left-base-reflᵉ :
    { yᵉ zᵉ : Aᵉ} (qᵉ : yᵉ ＝ᵉ zᵉ) →
    { x'ᵉ y'ᵉ : Bᵉ yᵉ} {z'ᵉ : Bᵉ zᵉ} (p'ᵉ : x'ᵉ ＝ᵉ y'ᵉ) →
    ( q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ y'ᵉ z'ᵉ) →
    concat-dependent-identificationᵉ reflᵉ qᵉ p'ᵉ q'ᵉ ＝ᵉ apᵉ (trᵉ Bᵉ qᵉ) p'ᵉ ∙ᵉ q'ᵉ
  compute-concat-dependent-identification-left-base-reflᵉ qᵉ reflᵉ q'ᵉ = reflᵉ
```

#### Strictly right unital concatenation of dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  right-strict-concat-dependent-identificationᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ} {z'ᵉ : Bᵉ zᵉ} →
    dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ →
    dependent-identificationᵉ Bᵉ qᵉ y'ᵉ z'ᵉ →
    dependent-identificationᵉ Bᵉ (pᵉ ∙ᵣᵉ qᵉ) x'ᵉ z'ᵉ
  right-strict-concat-dependent-identificationᵉ pᵉ reflᵉ p'ᵉ q'ᵉ = p'ᵉ ∙ᵣᵉ q'ᵉ

  compute-right-strict-concat-dependent-identification-right-base-reflᵉ :
    { xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) →
    { x'ᵉ : Bᵉ xᵉ} {y'ᵉ z'ᵉ : Bᵉ yᵉ} (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ) →
    ( q'ᵉ : y'ᵉ ＝ᵉ z'ᵉ) →
    right-strict-concat-dependent-identificationᵉ pᵉ reflᵉ p'ᵉ q'ᵉ ＝ᵉ p'ᵉ ∙ᵣᵉ q'ᵉ
  compute-right-strict-concat-dependent-identification-right-base-reflᵉ qᵉ p'ᵉ q'ᵉ =
    reflᵉ
```

#### Inverses of dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  inv-dependent-identificationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ} →
    dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ →
    dependent-identificationᵉ Bᵉ (invᵉ pᵉ) y'ᵉ x'ᵉ
  inv-dependent-identificationᵉ reflᵉ reflᵉ = reflᵉ
```

#### Associativity of concatenation of dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  assoc-dependent-identificationᵉ :
    {xᵉ yᵉ zᵉ uᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) (rᵉ : zᵉ ＝ᵉ uᵉ)
    {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ} {z'ᵉ : Bᵉ zᵉ} {u'ᵉ : Bᵉ uᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ y'ᵉ z'ᵉ)
    (r'ᵉ : dependent-identificationᵉ Bᵉ rᵉ z'ᵉ u'ᵉ) →
    dependent-identification²ᵉ Bᵉ
      ( assocᵉ pᵉ qᵉ rᵉ)
      ( concat-dependent-identificationᵉ Bᵉ
        ( pᵉ ∙ᵉ qᵉ)
        ( rᵉ)
        ( concat-dependent-identificationᵉ Bᵉ pᵉ qᵉ p'ᵉ q'ᵉ)
        ( r'ᵉ))
      ( concat-dependent-identificationᵉ Bᵉ
        ( pᵉ)
        ( qᵉ ∙ᵉ rᵉ)
        ( p'ᵉ)
        ( concat-dependent-identificationᵉ Bᵉ qᵉ rᵉ q'ᵉ r'ᵉ))
  assoc-dependent-identificationᵉ reflᵉ qᵉ rᵉ reflᵉ q'ᵉ r'ᵉ = reflᵉ
```

### Unit laws for concatenation of dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  right-unit-dependent-identificationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (qᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ) →
    dependent-identification²ᵉ
      ( Bᵉ)
      ( right-unitᵉ {pᵉ = pᵉ})
      ( concat-dependent-identificationᵉ Bᵉ pᵉ reflᵉ qᵉ reflᵉ)
      ( qᵉ)
  right-unit-dependent-identificationᵉ reflᵉ reflᵉ = reflᵉ

  left-unit-dependent-identificationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (qᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ) →
    dependent-identification²ᵉ
      ( Bᵉ)
      ( left-unitᵉ {pᵉ = pᵉ})
      ( concat-dependent-identificationᵉ Bᵉ reflᵉ pᵉ
        ( refl-dependent-identificationᵉ Bᵉ)
        ( qᵉ))
      ( qᵉ)
  left-unit-dependent-identificationᵉ pᵉ qᵉ = reflᵉ
```

### Inverse laws for dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  right-inv-dependent-identificationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (qᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ) →
    dependent-identification²ᵉ Bᵉ
      ( right-invᵉ pᵉ)
      ( concat-dependent-identificationᵉ Bᵉ
        ( pᵉ)
        ( invᵉ pᵉ)
        ( qᵉ)
        ( inv-dependent-identificationᵉ Bᵉ pᵉ qᵉ))
      ( refl-dependent-identificationᵉ Bᵉ)
  right-inv-dependent-identificationᵉ reflᵉ reflᵉ = reflᵉ

  left-inv-dependent-identificationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (qᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ) →
    dependent-identification²ᵉ
      ( Bᵉ)
      ( left-invᵉ pᵉ)
      ( concat-dependent-identificationᵉ Bᵉ
        ( invᵉ pᵉ)
        ( pᵉ)
        ( inv-dependent-identificationᵉ Bᵉ pᵉ qᵉ)
        ( qᵉ))
      ( refl-dependent-identificationᵉ Bᵉ)
  left-inv-dependent-identificationᵉ reflᵉ reflᵉ = reflᵉ
```

### The inverse of dependent identifications is involutive

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  inv-inv-dependent-identificationᵉ :
    {xᵉ yᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ}
    (qᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ) →
    dependent-identification²ᵉ Bᵉ
      ( inv-invᵉ pᵉ)
      ( inv-dependent-identificationᵉ Bᵉ
        ( invᵉ pᵉ)
        ( inv-dependent-identificationᵉ Bᵉ pᵉ qᵉ))
      ( qᵉ)
  inv-inv-dependent-identificationᵉ reflᵉ reflᵉ = reflᵉ
```

### The inverse distributes over concatenation of dependent identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Bᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  distributive-inv-concat-dependent-identificationᵉ :
    {xᵉ yᵉ zᵉ : Aᵉ} (pᵉ : xᵉ ＝ᵉ yᵉ) (qᵉ : yᵉ ＝ᵉ zᵉ) {x'ᵉ : Bᵉ xᵉ} {y'ᵉ : Bᵉ yᵉ} {z'ᵉ : Bᵉ zᵉ}
    (p'ᵉ : dependent-identificationᵉ Bᵉ pᵉ x'ᵉ y'ᵉ)
    (q'ᵉ : dependent-identificationᵉ Bᵉ qᵉ y'ᵉ z'ᵉ) →
    dependent-identification²ᵉ Bᵉ
      ( distributive-inv-concatᵉ pᵉ qᵉ)
      ( inv-dependent-identificationᵉ Bᵉ
        ( pᵉ ∙ᵉ qᵉ)
        ( concat-dependent-identificationᵉ Bᵉ pᵉ qᵉ p'ᵉ q'ᵉ))
      ( concat-dependent-identificationᵉ Bᵉ
        ( invᵉ qᵉ)
        ( invᵉ pᵉ)
        ( inv-dependent-identificationᵉ Bᵉ qᵉ q'ᵉ)
        ( inv-dependent-identificationᵉ Bᵉ pᵉ p'ᵉ))
  distributive-inv-concat-dependent-identificationᵉ reflᵉ reflᵉ reflᵉ reflᵉ = reflᵉ
```