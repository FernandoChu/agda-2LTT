# Walks in directed graphs

```agda
module graph-theory.walks-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.negated-equalityᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.equivalences-directed-graphsᵉ
open import graph-theory.morphisms-directed-graphsᵉ
```

</details>

## Idea

Aᵉ **walk**ᵉ in aᵉ [directedᵉ graph](graph-theory.directed-graphs.mdᵉ) fromᵉ aᵉ vertexᵉ
`x`ᵉ to aᵉ vertexᵉ `y`ᵉ isᵉ aᵉ [list](lists.lists.mdᵉ) ofᵉ edgesᵉ thatᵉ connectᵉ `x`ᵉ to
`y`.ᵉ Sinceᵉ everyᵉ journeyᵉ beginsᵉ with aᵉ singleᵉ step,ᵉ weᵉ defineᵉ theᵉ `cons`ᵉ
operationᵉ onᵉ walksᵉ in directedᵉ graphsᵉ with anᵉ edgeᵉ fromᵉ theᵉ sourceᵉ in theᵉ firstᵉ
argument,ᵉ andᵉ aᵉ walkᵉ to theᵉ targetᵉ in theᵉ secondᵉ argument.ᵉ

## Definitions

### The type of walks from `x` to `y` in `G`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  data walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    refl-walk-Directed-Graphᵉ :
      {xᵉ : vertex-Directed-Graphᵉ Gᵉ} → walk-Directed-Graphᵉ xᵉ xᵉ
    cons-walk-Directed-Graphᵉ :
      {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} →
      edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
      walk-Directed-Graphᵉ yᵉ zᵉ → walk-Directed-Graphᵉ xᵉ zᵉ

  unit-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    walk-Directed-Graphᵉ xᵉ yᵉ
  unit-walk-Directed-Graphᵉ eᵉ =
    cons-walk-Directed-Graphᵉ eᵉ refl-walk-Directed-Graphᵉ

  snoc-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ xᵉ yᵉ →
    edge-Directed-Graphᵉ Gᵉ yᵉ zᵉ → walk-Directed-Graphᵉ xᵉ zᵉ
  snoc-walk-Directed-Graphᵉ refl-walk-Directed-Graphᵉ eᵉ =
    unit-walk-Directed-Graphᵉ eᵉ
  snoc-walk-Directed-Graphᵉ (cons-walk-Directed-Graphᵉ fᵉ wᵉ) eᵉ =
    cons-walk-Directed-Graphᵉ fᵉ (snoc-walk-Directed-Graphᵉ wᵉ eᵉ)
```

### The type of walks in a directed graph, defined dually

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  data walk-Directed-Graph'ᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    refl-walk-Directed-Graph'ᵉ :
      {xᵉ : vertex-Directed-Graphᵉ Gᵉ} → walk-Directed-Graph'ᵉ xᵉ xᵉ
    snoc-walk-Directed-Graph'ᵉ :
      {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} →
      walk-Directed-Graph'ᵉ xᵉ yᵉ → edge-Directed-Graphᵉ Gᵉ yᵉ zᵉ →
      walk-Directed-Graph'ᵉ xᵉ zᵉ

  unit-walk-Directed-Graph'ᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ → walk-Directed-Graph'ᵉ xᵉ yᵉ
  unit-walk-Directed-Graph'ᵉ eᵉ =
    snoc-walk-Directed-Graph'ᵉ refl-walk-Directed-Graph'ᵉ eᵉ

  cons-walk-Directed-Graph'ᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ → walk-Directed-Graph'ᵉ yᵉ zᵉ →
    walk-Directed-Graph'ᵉ xᵉ zᵉ
  cons-walk-Directed-Graph'ᵉ eᵉ refl-walk-Directed-Graph'ᵉ =
    unit-walk-Directed-Graph'ᵉ eᵉ
  cons-walk-Directed-Graph'ᵉ eᵉ (snoc-walk-Directed-Graph'ᵉ wᵉ fᵉ) =
    snoc-walk-Directed-Graph'ᵉ (cons-walk-Directed-Graph'ᵉ eᵉ wᵉ) fᵉ
```

### The length of a walk in `G`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  length-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ → ℕᵉ
  length-walk-Directed-Graphᵉ refl-walk-Directed-Graphᵉ = 0
  length-walk-Directed-Graphᵉ (cons-walk-Directed-Graphᵉ xᵉ wᵉ) =
    succ-ℕᵉ (length-walk-Directed-Graphᵉ wᵉ)
```

### The type of walks of length `n` from `x` to `y` in `G`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  walk-of-length-Directed-Graphᵉ :
    ℕᵉ → (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  walk-of-length-Directed-Graphᵉ zero-ℕᵉ xᵉ yᵉ = raiseᵉ l2ᵉ (yᵉ ＝ᵉ xᵉ)
  walk-of-length-Directed-Graphᵉ (succ-ℕᵉ nᵉ) xᵉ yᵉ =
    Σᵉ ( vertex-Directed-Graphᵉ Gᵉ)
      ( λ zᵉ → edge-Directed-Graphᵉ Gᵉ xᵉ zᵉ ×ᵉ walk-of-length-Directed-Graphᵉ nᵉ zᵉ yᵉ)

  map-compute-total-walk-of-length-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    Σᵉ ℕᵉ (λ nᵉ → walk-of-length-Directed-Graphᵉ nᵉ xᵉ yᵉ) → walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ
  map-compute-total-walk-of-length-Directed-Graphᵉ
    xᵉ .xᵉ (zero-ℕᵉ ,ᵉ map-raiseᵉ reflᵉ) =
    refl-walk-Directed-Graphᵉ
  map-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ (succ-ℕᵉ nᵉ ,ᵉ zᵉ ,ᵉ eᵉ ,ᵉ wᵉ) =
    cons-walk-Directed-Graphᵉ eᵉ
      ( map-compute-total-walk-of-length-Directed-Graphᵉ zᵉ yᵉ (nᵉ ,ᵉ wᵉ))

  map-inv-compute-total-walk-of-length-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ → Σᵉ ℕᵉ (λ nᵉ → walk-of-length-Directed-Graphᵉ nᵉ xᵉ yᵉ)
  map-inv-compute-total-walk-of-length-Directed-Graphᵉ
    xᵉ .xᵉ refl-walk-Directed-Graphᵉ =
    (0ᵉ ,ᵉ map-raiseᵉ reflᵉ)
  map-inv-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ
    ( cons-walk-Directed-Graphᵉ {yᵉ = zᵉ} eᵉ wᵉ) =
    map-Σᵉ
      ( λ nᵉ → walk-of-length-Directed-Graphᵉ nᵉ xᵉ yᵉ)
      ( succ-ℕᵉ)
      ( λ kᵉ uᵉ → (zᵉ ,ᵉ eᵉ ,ᵉ uᵉ))
      ( map-inv-compute-total-walk-of-length-Directed-Graphᵉ zᵉ yᵉ wᵉ)

  is-section-map-inv-compute-total-walk-of-length-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    ( map-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ ∘ᵉ
      map-inv-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-total-walk-of-length-Directed-Graphᵉ
    xᵉ .xᵉ refl-walk-Directed-Graphᵉ = reflᵉ
  is-section-map-inv-compute-total-walk-of-length-Directed-Graphᵉ
    xᵉ yᵉ (cons-walk-Directed-Graphᵉ {yᵉ = zᵉ} eᵉ wᵉ) =
    apᵉ
      ( cons-walk-Directed-Graphᵉ eᵉ)
      ( is-section-map-inv-compute-total-walk-of-length-Directed-Graphᵉ zᵉ yᵉ wᵉ)

  is-retraction-map-inv-compute-total-walk-of-length-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    ( map-inv-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ ∘ᵉ
      map-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-total-walk-of-length-Directed-Graphᵉ
    xᵉ .xᵉ (zero-ℕᵉ ,ᵉ map-raiseᵉ reflᵉ) =
    reflᵉ
  is-retraction-map-inv-compute-total-walk-of-length-Directed-Graphᵉ
    xᵉ yᵉ (succ-ℕᵉ nᵉ ,ᵉ (zᵉ ,ᵉ eᵉ ,ᵉ wᵉ)) =
    apᵉ
      ( map-Σᵉ
        ( λ nᵉ → walk-of-length-Directed-Graphᵉ nᵉ xᵉ yᵉ)
        ( succ-ℕᵉ)
        ( λ kᵉ uᵉ → (zᵉ ,ᵉ eᵉ ,ᵉ uᵉ)))
      ( is-retraction-map-inv-compute-total-walk-of-length-Directed-Graphᵉ zᵉ yᵉ
        ( nᵉ ,ᵉ wᵉ))

  is-equiv-map-compute-total-walk-of-length-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    is-equivᵉ (map-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ)
  is-equiv-map-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ)
      ( is-section-map-inv-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ)
      ( is-retraction-map-inv-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ)

  compute-total-walk-of-length-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    Σᵉ ℕᵉ (λ nᵉ → walk-of-length-Directed-Graphᵉ nᵉ xᵉ yᵉ) ≃ᵉ walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ
  pr1ᵉ (compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ) =
    map-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ
  pr2ᵉ (compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ) =
    is-equiv-map-compute-total-walk-of-length-Directed-Graphᵉ xᵉ yᵉ
```

### Concatenation of walks

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  concat-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ → walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ →
    walk-Directed-Graphᵉ Gᵉ xᵉ zᵉ
  concat-walk-Directed-Graphᵉ refl-walk-Directed-Graphᵉ vᵉ = vᵉ
  concat-walk-Directed-Graphᵉ (cons-walk-Directed-Graphᵉ eᵉ uᵉ) vᵉ =
    cons-walk-Directed-Graphᵉ eᵉ (concat-walk-Directed-Graphᵉ uᵉ vᵉ)
```

## Properties

### The two dual definitions of walks are equivalent

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  map-compute-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ → walk-Directed-Graph'ᵉ Gᵉ xᵉ yᵉ
  map-compute-walk-Directed-Graphᵉ refl-walk-Directed-Graphᵉ =
    refl-walk-Directed-Graph'ᵉ
  map-compute-walk-Directed-Graphᵉ (cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
    cons-walk-Directed-Graph'ᵉ Gᵉ eᵉ (map-compute-walk-Directed-Graphᵉ wᵉ)

  compute-snoc-map-compute-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (wᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (eᵉ : edge-Directed-Graphᵉ Gᵉ yᵉ zᵉ) →
    map-compute-walk-Directed-Graphᵉ (snoc-walk-Directed-Graphᵉ Gᵉ wᵉ eᵉ) ＝ᵉ
    snoc-walk-Directed-Graph'ᵉ (map-compute-walk-Directed-Graphᵉ wᵉ) eᵉ
  compute-snoc-map-compute-walk-Directed-Graphᵉ refl-walk-Directed-Graphᵉ eᵉ =
    reflᵉ
  compute-snoc-map-compute-walk-Directed-Graphᵉ
    ( cons-walk-Directed-Graphᵉ fᵉ wᵉ)
    ( eᵉ) =
    apᵉ
      ( cons-walk-Directed-Graph'ᵉ Gᵉ fᵉ)
      ( compute-snoc-map-compute-walk-Directed-Graphᵉ wᵉ eᵉ)

  map-inv-compute-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graph'ᵉ Gᵉ xᵉ yᵉ → walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ
  map-inv-compute-walk-Directed-Graphᵉ refl-walk-Directed-Graph'ᵉ =
    refl-walk-Directed-Graphᵉ
  map-inv-compute-walk-Directed-Graphᵉ (snoc-walk-Directed-Graph'ᵉ wᵉ eᵉ) =
    snoc-walk-Directed-Graphᵉ Gᵉ (map-inv-compute-walk-Directed-Graphᵉ wᵉ) eᵉ

  compute-cons-map-inv-compute-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (wᵉ : walk-Directed-Graph'ᵉ Gᵉ yᵉ zᵉ) →
    map-inv-compute-walk-Directed-Graphᵉ (cons-walk-Directed-Graph'ᵉ Gᵉ eᵉ wᵉ) ＝ᵉ
    cons-walk-Directed-Graphᵉ eᵉ (map-inv-compute-walk-Directed-Graphᵉ wᵉ)
  compute-cons-map-inv-compute-walk-Directed-Graphᵉ eᵉ refl-walk-Directed-Graph'ᵉ =
    reflᵉ
  compute-cons-map-inv-compute-walk-Directed-Graphᵉ eᵉ
    ( snoc-walk-Directed-Graph'ᵉ wᵉ fᵉ) =
    apᵉ
      ( λ vᵉ → snoc-walk-Directed-Graphᵉ Gᵉ vᵉ fᵉ)
      ( compute-cons-map-inv-compute-walk-Directed-Graphᵉ eᵉ wᵉ)

  is-section-map-inv-compute-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    ( map-compute-walk-Directed-Graphᵉ {xᵉ} {yᵉ} ∘ᵉ
      map-inv-compute-walk-Directed-Graphᵉ {xᵉ} {yᵉ}) ~ᵉ idᵉ
  is-section-map-inv-compute-walk-Directed-Graphᵉ refl-walk-Directed-Graph'ᵉ =
    reflᵉ
  is-section-map-inv-compute-walk-Directed-Graphᵉ
    ( snoc-walk-Directed-Graph'ᵉ wᵉ eᵉ) =
    ( compute-snoc-map-compute-walk-Directed-Graphᵉ
      ( map-inv-compute-walk-Directed-Graphᵉ wᵉ)
      ( eᵉ)) ∙ᵉ
    ( apᵉ
      ( λ vᵉ → snoc-walk-Directed-Graph'ᵉ vᵉ eᵉ)
      ( is-section-map-inv-compute-walk-Directed-Graphᵉ wᵉ))

  is-retraction-map-inv-compute-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    ( map-inv-compute-walk-Directed-Graphᵉ {xᵉ} {yᵉ} ∘ᵉ
      map-compute-walk-Directed-Graphᵉ {xᵉ} {yᵉ}) ~ᵉ idᵉ
  is-retraction-map-inv-compute-walk-Directed-Graphᵉ refl-walk-Directed-Graphᵉ =
    reflᵉ
  is-retraction-map-inv-compute-walk-Directed-Graphᵉ
    ( cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
    ( compute-cons-map-inv-compute-walk-Directed-Graphᵉ eᵉ
      ( map-compute-walk-Directed-Graphᵉ wᵉ)) ∙ᵉ
    ( apᵉ
      ( cons-walk-Directed-Graphᵉ eᵉ)
      ( is-retraction-map-inv-compute-walk-Directed-Graphᵉ wᵉ))

  is-equiv-map-compute-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    is-equivᵉ (map-compute-walk-Directed-Graphᵉ {xᵉ} {yᵉ})
  is-equiv-map-compute-walk-Directed-Graphᵉ =
    is-equiv-is-invertibleᵉ
      map-inv-compute-walk-Directed-Graphᵉ
      is-section-map-inv-compute-walk-Directed-Graphᵉ
      is-retraction-map-inv-compute-walk-Directed-Graphᵉ

  compute-walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ walk-Directed-Graph'ᵉ Gᵉ xᵉ yᵉ
  pr1ᵉ (compute-walk-Directed-Graphᵉ xᵉ yᵉ) = map-compute-walk-Directed-Graphᵉ
  pr2ᵉ (compute-walk-Directed-Graphᵉ xᵉ yᵉ) =
    is-equiv-map-compute-walk-Directed-Graphᵉ
```

### The type of walks from `x` to `y` is a coproduct

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  coproduct-walk-Directed-Graphᵉ : (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coproduct-walk-Directed-Graphᵉ xᵉ yᵉ =
    (yᵉ ＝ᵉ xᵉ) +ᵉ
    Σᵉ ( vertex-Directed-Graphᵉ Gᵉ)
      ( λ zᵉ → edge-Directed-Graphᵉ Gᵉ xᵉ zᵉ ×ᵉ walk-Directed-Graphᵉ Gᵉ zᵉ yᵉ)

  map-compute-coproduct-walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ → coproduct-walk-Directed-Graphᵉ xᵉ yᵉ
  map-compute-coproduct-walk-Directed-Graphᵉ xᵉ .xᵉ refl-walk-Directed-Graphᵉ =
    inlᵉ reflᵉ
  map-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ
    ( cons-walk-Directed-Graphᵉ {aᵉ} {bᵉ} {cᵉ} eᵉ wᵉ) =
    inrᵉ (bᵉ ,ᵉ eᵉ ,ᵉ wᵉ)

  map-inv-compute-coproduct-walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    coproduct-walk-Directed-Graphᵉ xᵉ yᵉ → walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ
  map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ .xᵉ (inlᵉ reflᵉ) =
    refl-walk-Directed-Graphᵉ
  map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ (inrᵉ (zᵉ ,ᵉ eᵉ ,ᵉ wᵉ)) =
    cons-walk-Directed-Graphᵉ eᵉ wᵉ

  is-section-map-inv-compute-coproduct-walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    ( map-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ ∘ᵉ
      map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ) ~ᵉ idᵉ
  is-section-map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ .xᵉ (inlᵉ reflᵉ) =
    reflᵉ
  is-section-map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ
    ( inrᵉ (zᵉ ,ᵉ eᵉ ,ᵉ wᵉ)) =
    reflᵉ

  is-retraction-map-inv-compute-coproduct-walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    ( map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ ∘ᵉ
      map-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ) ~ᵉ idᵉ
  is-retraction-map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ .xᵉ
    refl-walk-Directed-Graphᵉ =
    reflᵉ
  is-retraction-map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ
    ( cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
    reflᵉ

  is-equiv-map-compute-coproduct-walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    is-equivᵉ (map-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ)
  is-equiv-map-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ =
    is-equiv-is-invertibleᵉ
      ( map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ)
      ( is-section-map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ)
      ( is-retraction-map-inv-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ)

  compute-coproduct-walk-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ coproduct-walk-Directed-Graphᵉ xᵉ yᵉ
  pr1ᵉ (compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ) =
    map-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ
  pr2ᵉ (compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ) =
    is-equiv-map-compute-coproduct-walk-Directed-Graphᵉ xᵉ yᵉ
```

### Walks of length `0` are identifications

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Directed-Graphᵉ Gᵉ)
  where

  is-torsorial-walk-of-length-zero-Directed-Graphᵉ :
    is-torsorialᵉ (λ yᵉ → walk-of-length-Directed-Graphᵉ Gᵉ 0 xᵉ yᵉ)
  is-torsorial-walk-of-length-zero-Directed-Graphᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (λ yᵉ → yᵉ ＝ᵉ xᵉ))
      ( equiv-totᵉ (λ yᵉ → compute-raiseᵉ l2ᵉ (yᵉ ＝ᵉ xᵉ)))
      ( is-torsorial-Id'ᵉ xᵉ)
```

### `cons-walk e w ≠ refl-walk`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Directed-Graphᵉ Gᵉ)
  where

  neq-cons-refl-walk-Directed-Graphᵉ :
    (yᵉ : vertex-Directed-Graphᵉ Gᵉ) (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    (wᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ xᵉ) →
    cons-walk-Directed-Graphᵉ eᵉ wᵉ ≠ᵉ refl-walk-Directed-Graphᵉ
  neq-cons-refl-walk-Directed-Graphᵉ yᵉ eᵉ wᵉ ()
```

### If `cons-walk e w ＝ cons-walk e' w'`, then `(y , e) ＝ (y' , e')`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (xᵉ : vertex-Directed-Graphᵉ Gᵉ)
  where

  eq-direct-successor-eq-cons-walk-Directed-Graphᵉ :
    {yᵉ y'ᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (e'ᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ y'ᵉ)
    (wᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ) (w'ᵉ : walk-Directed-Graphᵉ Gᵉ y'ᵉ zᵉ) →
    cons-walk-Directed-Graphᵉ eᵉ wᵉ ＝ᵉ cons-walk-Directed-Graphᵉ e'ᵉ w'ᵉ →
    (yᵉ ,ᵉ eᵉ) ＝ᵉ (y'ᵉ ,ᵉ e'ᵉ)
  eq-direct-successor-eq-cons-walk-Directed-Graphᵉ {yᵉ} {.yᵉ} {zᵉ} eᵉ .eᵉ wᵉ .wᵉ reflᵉ =
    reflᵉ
```

### Vertices on a walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-vertex-on-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (wᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (vᵉ : vertex-Directed-Graphᵉ Gᵉ) → UUᵉ l1ᵉ
  is-vertex-on-walk-Directed-Graphᵉ {xᵉ} refl-walk-Directed-Graphᵉ vᵉ = vᵉ ＝ᵉ xᵉ
  is-vertex-on-walk-Directed-Graphᵉ {xᵉ} (cons-walk-Directed-Graphᵉ eᵉ wᵉ) vᵉ =
    ( vᵉ ＝ᵉ xᵉ) +ᵉ
    ( is-vertex-on-walk-Directed-Graphᵉ wᵉ vᵉ)

  vertex-on-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} (wᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) → UUᵉ l1ᵉ
  vertex-on-walk-Directed-Graphᵉ wᵉ =
    Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (is-vertex-on-walk-Directed-Graphᵉ wᵉ)

  vertex-vertex-on-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} (wᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    vertex-on-walk-Directed-Graphᵉ wᵉ → vertex-Directed-Graphᵉ Gᵉ
  vertex-vertex-on-walk-Directed-Graphᵉ wᵉ = pr1ᵉ
```

### Edges on a walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  data is-edge-on-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} (wᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
    {uᵉ vᵉ : vertex-Directed-Graphᵉ Gᵉ} → edge-Directed-Graphᵉ Gᵉ uᵉ vᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
    where
    edge-is-edge-on-walk-Directed-Graphᵉ :
      {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
      (wᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ) →
      is-edge-on-walk-Directed-Graphᵉ (cons-walk-Directed-Graphᵉ eᵉ wᵉ) eᵉ
    cons-is-edge-on-walk-Directed-Graphᵉ :
      {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
      (wᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ) →
      {uᵉ vᵉ : vertex-Directed-Graphᵉ Gᵉ} (fᵉ : edge-Directed-Graphᵉ Gᵉ uᵉ vᵉ) →
      is-edge-on-walk-Directed-Graphᵉ wᵉ fᵉ →
      is-edge-on-walk-Directed-Graphᵉ (cons-walk-Directed-Graphᵉ eᵉ wᵉ) fᵉ

  edge-on-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (wᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  edge-on-walk-Directed-Graphᵉ wᵉ =
    Σᵉ ( total-edge-Directed-Graphᵉ Gᵉ)
      ( λ eᵉ →
        is-edge-on-walk-Directed-Graphᵉ wᵉ (edge-total-edge-Directed-Graphᵉ Gᵉ eᵉ))

  module _
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (wᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
    (eᵉ : edge-on-walk-Directed-Graphᵉ wᵉ)
    where

    total-edge-edge-on-walk-Directed-Graphᵉ : total-edge-Directed-Graphᵉ Gᵉ
    total-edge-edge-on-walk-Directed-Graphᵉ = pr1ᵉ eᵉ

    source-edge-on-walk-Directed-Graphᵉ : vertex-Directed-Graphᵉ Gᵉ
    source-edge-on-walk-Directed-Graphᵉ =
      source-total-edge-Directed-Graphᵉ Gᵉ total-edge-edge-on-walk-Directed-Graphᵉ

    target-edge-on-walk-Directed-Graphᵉ : vertex-Directed-Graphᵉ Gᵉ
    target-edge-on-walk-Directed-Graphᵉ =
      target-total-edge-Directed-Graphᵉ Gᵉ total-edge-edge-on-walk-Directed-Graphᵉ

    edge-edge-on-walk-Directed-Graphᵉ :
      edge-Directed-Graphᵉ Gᵉ
        source-edge-on-walk-Directed-Graphᵉ
        target-edge-on-walk-Directed-Graphᵉ
    edge-edge-on-walk-Directed-Graphᵉ =
      edge-total-edge-Directed-Graphᵉ Gᵉ total-edge-edge-on-walk-Directed-Graphᵉ

    is-edge-on-walk-edge-on-walk-Directed-Graphᵉ :
      is-edge-on-walk-Directed-Graphᵉ wᵉ edge-edge-on-walk-Directed-Graphᵉ
    is-edge-on-walk-edge-on-walk-Directed-Graphᵉ = pr2ᵉ eᵉ
```

### The action on walks of graph homomorphisms

```agda
walk-hom-Directed-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
  walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
  walk-Directed-Graphᵉ Hᵉ
    ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ)
    ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ yᵉ)
walk-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ refl-walk-Directed-Graphᵉ =
  refl-walk-Directed-Graphᵉ
walk-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ (cons-walk-Directed-Graphᵉ eᵉ wᵉ) =
  cons-walk-Directed-Graphᵉ
    ( edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ eᵉ)
    ( walk-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ wᵉ)
```

### The action on walks of length `n` of graph homomorphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (fᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ)
  where

  walk-of-length-hom-Directed-Graphᵉ :
    (nᵉ : ℕᵉ) {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-of-length-Directed-Graphᵉ Gᵉ nᵉ xᵉ yᵉ →
    walk-of-length-Directed-Graphᵉ Hᵉ nᵉ
    ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ)
    ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ yᵉ)
  walk-of-length-hom-Directed-Graphᵉ zero-ℕᵉ {xᵉ} {yᵉ} (map-raiseᵉ pᵉ) =
    map-raiseᵉ (apᵉ (vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ) pᵉ)
  walk-of-length-hom-Directed-Graphᵉ (succ-ℕᵉ nᵉ) =
    map-Σᵉ
      ( λ zᵉ →
        ( edge-Directed-Graphᵉ Hᵉ (vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ _) zᵉ) ×ᵉ
        ( walk-of-length-Directed-Graphᵉ Hᵉ nᵉ zᵉ
          ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ _)))
      ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
      ( λ zᵉ →
        map-productᵉ
          ( edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
          ( walk-of-length-hom-Directed-Graphᵉ nᵉ))

  square-compute-total-walk-of-length-hom-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    coherence-square-mapsᵉ
      ( totᵉ (λ nᵉ → walk-of-length-hom-Directed-Graphᵉ nᵉ {xᵉ} {yᵉ}))
      ( map-compute-total-walk-of-length-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
      ( map-compute-total-walk-of-length-Directed-Graphᵉ Hᵉ
        ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ)
        ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ yᵉ))
      ( walk-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ {xᵉ} {yᵉ})
  square-compute-total-walk-of-length-hom-Directed-Graphᵉ
    xᵉ .xᵉ (zero-ℕᵉ ,ᵉ map-raiseᵉ reflᵉ) = reflᵉ
  square-compute-total-walk-of-length-hom-Directed-Graphᵉ
    xᵉ yᵉ (succ-ℕᵉ nᵉ ,ᵉ zᵉ ,ᵉ eᵉ ,ᵉ wᵉ) =
    apᵉ
      ( cons-walk-Directed-Graphᵉ (edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ eᵉ))
      ( square-compute-total-walk-of-length-hom-Directed-Graphᵉ zᵉ yᵉ (nᵉ ,ᵉ wᵉ))
```

### The action on walks of length `n` of equivalences of graphs

```agda
equiv-walk-of-length-equiv-Directed-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) (nᵉ : ℕᵉ) {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
  walk-of-length-Directed-Graphᵉ Gᵉ nᵉ xᵉ yᵉ ≃ᵉ
  walk-of-length-Directed-Graphᵉ Hᵉ nᵉ
    ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ)
    ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ yᵉ)
equiv-walk-of-length-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ zero-ℕᵉ =
  equiv-raiseᵉ _ _
    ( equiv-apᵉ (equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ) _ _)
equiv-walk-of-length-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ (succ-ℕᵉ nᵉ) =
  equiv-Σᵉ
    ( λ zᵉ →
      ( edge-Directed-Graphᵉ Hᵉ (vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ _) zᵉ) ×ᵉ
      ( walk-of-length-Directed-Graphᵉ Hᵉ nᵉ zᵉ
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ _)))
    ( equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
    ( λ zᵉ →
      equiv-productᵉ
        ( equiv-edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ _ _)
        ( equiv-walk-of-length-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ nᵉ))
```

### The action of equivalences on walks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ)
  where

  walk-equiv-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
    walk-Directed-Graphᵉ Hᵉ
      ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ)
      ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ yᵉ)
  walk-equiv-Directed-Graphᵉ =
    walk-hom-Directed-Graphᵉ Gᵉ Hᵉ (hom-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ)

  square-compute-total-walk-of-length-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    coherence-square-mapsᵉ
      ( totᵉ
        ( λ nᵉ →
          map-equivᵉ
            ( equiv-walk-of-length-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ nᵉ {xᵉ} {yᵉ})))
      ( map-compute-total-walk-of-length-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
      ( map-compute-total-walk-of-length-Directed-Graphᵉ Hᵉ
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ)
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ yᵉ))
      ( walk-equiv-Directed-Graphᵉ {xᵉ} {yᵉ})
  square-compute-total-walk-of-length-equiv-Directed-Graphᵉ
    xᵉ .xᵉ (zero-ℕᵉ ,ᵉ map-raiseᵉ reflᵉ) = reflᵉ
  square-compute-total-walk-of-length-equiv-Directed-Graphᵉ
    xᵉ yᵉ (succ-ℕᵉ nᵉ ,ᵉ zᵉ ,ᵉ fᵉ ,ᵉ wᵉ) =
    apᵉ
      ( cons-walk-Directed-Graphᵉ (edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ zᵉ fᵉ))
      ( square-compute-total-walk-of-length-equiv-Directed-Graphᵉ zᵉ yᵉ (nᵉ ,ᵉ wᵉ))

  is-equiv-walk-equiv-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    is-equivᵉ (walk-equiv-Directed-Graphᵉ {xᵉ} {yᵉ})
  is-equiv-walk-equiv-Directed-Graphᵉ {xᵉ} {yᵉ} =
    is-equiv-right-is-equiv-left-squareᵉ
      ( map-equivᵉ
        ( equiv-totᵉ
        ( λ nᵉ → equiv-walk-of-length-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ nᵉ {xᵉ} {yᵉ})))
      ( walk-equiv-Directed-Graphᵉ {xᵉ} {yᵉ})
      ( map-compute-total-walk-of-length-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
      ( map-compute-total-walk-of-length-Directed-Graphᵉ Hᵉ
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ)
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ yᵉ))
      ( inv-htpyᵉ
        ( square-compute-total-walk-of-length-equiv-Directed-Graphᵉ xᵉ yᵉ))
      ( is-equiv-map-compute-total-walk-of-length-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
      ( is-equiv-map-compute-total-walk-of-length-Directed-Graphᵉ Hᵉ
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ)
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ yᵉ))
      ( is-equiv-map-equivᵉ
        ( equiv-totᵉ
          ( λ nᵉ → equiv-walk-of-length-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ nᵉ)))

  equiv-walk-equiv-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ
    walk-Directed-Graphᵉ Hᵉ
      ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ)
      ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ yᵉ)
  pr1ᵉ (equiv-walk-equiv-Directed-Graphᵉ {xᵉ} {yᵉ}) =
    walk-equiv-Directed-Graphᵉ
  pr2ᵉ (equiv-walk-equiv-Directed-Graphᵉ {xᵉ} {yᵉ}) =
    is-equiv-walk-equiv-Directed-Graphᵉ
```

### If `concat-walk-Directed-Graph u v ＝ refl-walk-Directed-Graph` then both `u` and `v` are `refl-walk-Directed-Graph`

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  eq-is-refl-concat-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    (uᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (vᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ xᵉ) →
    ( concat-walk-Directed-Graphᵉ Gᵉ uᵉ vᵉ ＝ᵉ refl-walk-Directed-Graphᵉ) →
    xᵉ ＝ᵉ yᵉ
  eq-is-refl-concat-walk-Directed-Graphᵉ
    refl-walk-Directed-Graphᵉ .refl-walk-Directed-Graphᵉ reflᵉ =
    reflᵉ

  is-refl-left-is-refl-concat-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (uᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (vᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ xᵉ) →
    (pᵉ : concat-walk-Directed-Graphᵉ Gᵉ uᵉ vᵉ ＝ᵉ refl-walk-Directed-Graphᵉ) →
    trᵉ
      ( walk-Directed-Graphᵉ Gᵉ xᵉ)
      ( eq-is-refl-concat-walk-Directed-Graphᵉ uᵉ vᵉ pᵉ)
      ( refl-walk-Directed-Graphᵉ) ＝ᵉ uᵉ
  is-refl-left-is-refl-concat-walk-Directed-Graphᵉ
    refl-walk-Directed-Graphᵉ .refl-walk-Directed-Graphᵉ reflᵉ =
    reflᵉ

  is-refl-right-is-refl-concat-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ}
    (uᵉ : walk-Directed-Graphᵉ Gᵉ xᵉ yᵉ) (vᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ xᵉ) →
    (pᵉ : concat-walk-Directed-Graphᵉ Gᵉ uᵉ vᵉ ＝ᵉ refl-walk-Directed-Graphᵉ) →
    trᵉ
      ( walk-Directed-Graphᵉ Gᵉ yᵉ)
      ( invᵉ (eq-is-refl-concat-walk-Directed-Graphᵉ uᵉ vᵉ pᵉ))
      ( refl-walk-Directed-Graphᵉ) ＝ᵉ vᵉ
  is-refl-right-is-refl-concat-walk-Directed-Graphᵉ
    refl-walk-Directed-Graphᵉ .refl-walk-Directed-Graphᵉ reflᵉ =
    reflᵉ
```

### The function `unit-walk` is injective

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  is-injective-unit-walk-Directed-Graphᵉ :
    {xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ} →
    is-injectiveᵉ (unit-walk-Directed-Graphᵉ Gᵉ {xᵉ} {yᵉ})
  is-injective-unit-walk-Directed-Graphᵉ reflᵉ = reflᵉ
```

### The last edge on a walk

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  last-stage-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ →
    Σᵉ (vertex-Directed-Graphᵉ Gᵉ) (λ uᵉ → edge-Directed-Graphᵉ Gᵉ uᵉ zᵉ)
  last-stage-walk-Directed-Graphᵉ eᵉ refl-walk-Directed-Graphᵉ = (ᵉ_ ,ᵉ eᵉ)
  last-stage-walk-Directed-Graphᵉ eᵉ (cons-walk-Directed-Graphᵉ fᵉ wᵉ) =
    last-stage-walk-Directed-Graphᵉ fᵉ wᵉ

  vertex-last-stage-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ → vertex-Directed-Graphᵉ Gᵉ
  vertex-last-stage-walk-Directed-Graphᵉ eᵉ wᵉ =
    pr1ᵉ (last-stage-walk-Directed-Graphᵉ eᵉ wᵉ)

  edge-last-stage-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    (wᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ) →
    edge-Directed-Graphᵉ Gᵉ (vertex-last-stage-walk-Directed-Graphᵉ eᵉ wᵉ) zᵉ
  edge-last-stage-walk-Directed-Graphᵉ eᵉ wᵉ =
    pr2ᵉ (last-stage-walk-Directed-Graphᵉ eᵉ wᵉ)

  walk-last-stage-walk-Directed-Graphᵉ :
    {xᵉ yᵉ zᵉ : vertex-Directed-Graphᵉ Gᵉ} (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    (wᵉ : walk-Directed-Graphᵉ Gᵉ yᵉ zᵉ) →
    walk-Directed-Graphᵉ Gᵉ xᵉ (vertex-last-stage-walk-Directed-Graphᵉ eᵉ wᵉ)
  walk-last-stage-walk-Directed-Graphᵉ eᵉ refl-walk-Directed-Graphᵉ =
    refl-walk-Directed-Graphᵉ
  walk-last-stage-walk-Directed-Graphᵉ eᵉ (cons-walk-Directed-Graphᵉ fᵉ wᵉ) =
    cons-walk-Directed-Graphᵉ eᵉ (walk-last-stage-walk-Directed-Graphᵉ fᵉ wᵉ)
```

## External links

-ᵉ [Path](https://www.wikidata.org/entity/Q917421ᵉ) onᵉ Wikidataᵉ
-ᵉ [Pathᵉ (graphᵉ theory)](<https://en.wikipedia.org/wiki/Path_(graph_theory)>ᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Walk](https://mathworld.wolfram.com/Walk.htmlᵉ) atᵉ Wolframᵉ Mathworldᵉ