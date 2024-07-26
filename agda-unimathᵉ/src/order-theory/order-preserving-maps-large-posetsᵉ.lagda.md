# Order preserving maps between large posets

```agda
module order-theory.order-preserving-maps-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.order-preserving-maps-large-preordersᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ
```

</details>

## Idea

Anᵉ **orderᵉ preservingᵉ map**ᵉ betweenᵉ [largeᵉ posets](order-theory.large-posets.mdᵉ)
`P`ᵉ andᵉ `Q`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ

```text
  fᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ → type-Large-Posetᵉ Qᵉ (γᵉ l1ᵉ)
```

forᵉ eachᵉ [universeᵉ level](foundation.universe-levels.mdᵉ) `l1`,ᵉ suchᵉ thatᵉ `xᵉ ≤ᵉ y`ᵉ
impliesᵉ `fᵉ xᵉ ≤ᵉ fᵉ y`ᵉ forᵉ anyᵉ twoᵉ elementsᵉ `xᵉ yᵉ : P`.ᵉ Theᵉ functionᵉ
`γᵉ : Level → Level`ᵉ thatᵉ specifiesᵉ theᵉ universeᵉ levelᵉ ofᵉ `fᵉ x`ᵉ in termsᵉ ofᵉ theᵉ
universeᵉ levelᵉ ofᵉ `x`ᵉ isᵉ calledᵉ theᵉ **universeᵉ levelᵉ reindexingᵉ function**ᵉ ofᵉ
theᵉ orderᵉ preservingᵉ mapᵉ `f`.ᵉ

## Definitions

### The predicate that a map between large posets is order preserving

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  where

  preserves-order-map-Large-Posetᵉ :
    ({lᵉ : Level} → type-Large-Posetᵉ Pᵉ lᵉ → type-Large-Posetᵉ Qᵉ (γᵉ lᵉ)) →
    UUωᵉ
  preserves-order-map-Large-Posetᵉ =
    preserves-order-map-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
```

### The type of order preserving maps between large posets

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (γᵉ : Level → Level)
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  where

  hom-Large-Posetᵉ : UUωᵉ
  hom-Large-Posetᵉ =
    hom-Large-Preorderᵉ γᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)

module _
  {αPᵉ αQᵉ γᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ) (fᵉ : hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ)
  where

  map-hom-Large-Posetᵉ :
    {lᵉ : Level} → type-Large-Posetᵉ Pᵉ lᵉ → type-Large-Posetᵉ Qᵉ (γᵉ lᵉ)
  map-hom-Large-Posetᵉ =
    map-hom-Large-Preorderᵉ fᵉ

  preserves-order-hom-Large-Posetᵉ :
    preserves-order-map-Large-Posetᵉ Pᵉ Qᵉ map-hom-Large-Posetᵉ
  preserves-order-hom-Large-Posetᵉ =
    preserves-order-hom-Large-Preorderᵉ fᵉ
```

### The identity order preserving map on a large poset

```agda
module _
  {αPᵉ : Level → Level} {βPᵉ : Level → Level → Level} (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  where

  id-hom-Large-Posetᵉ : hom-Large-Posetᵉ (λ lᵉ → lᵉ) Pᵉ Pᵉ
  id-hom-Large-Posetᵉ = id-hom-Large-Preorderᵉ (large-preorder-Large-Posetᵉ Pᵉ)
```

### Composition of order preserving maps between large posets

```agda
module _
  {αPᵉ αQᵉ αRᵉ γgᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ βRᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Rᵉ : Large-Posetᵉ αRᵉ βRᵉ)
  (gᵉ : hom-Large-Posetᵉ γgᵉ Qᵉ Rᵉ)
  (fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Qᵉ)
  where

  map-comp-hom-Large-Posetᵉ :
    {l1ᵉ : Level} → type-Large-Posetᵉ Pᵉ l1ᵉ → type-Large-Posetᵉ Rᵉ (γgᵉ (γfᵉ l1ᵉ))
  map-comp-hom-Large-Posetᵉ =
    map-comp-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( large-preorder-Large-Posetᵉ Rᵉ)
      ( gᵉ)
      ( fᵉ)

  preserves-order-comp-hom-Large-Posetᵉ :
    preserves-order-map-Large-Posetᵉ Pᵉ Rᵉ map-comp-hom-Large-Posetᵉ
  preserves-order-comp-hom-Large-Posetᵉ =
    preserves-order-comp-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( large-preorder-Large-Posetᵉ Rᵉ)
      ( gᵉ)
      ( fᵉ)

  comp-hom-Large-Posetᵉ : hom-Large-Posetᵉ (λ lᵉ → γgᵉ (γfᵉ lᵉ)) Pᵉ Rᵉ
  comp-hom-Large-Posetᵉ =
    comp-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( large-preorder-Large-Posetᵉ Rᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Homotopies of order preserving maps between large posets

Givenᵉ twoᵉ orderᵉ preservingᵉ mapsᵉ `fᵉ gᵉ : hom-Large-Posetᵉ γᵉ Pᵉ Q`ᵉ with theᵉ sameᵉ
universeᵉ levelᵉ reindexingᵉ `γ`,ᵉ aᵉ **homotopyᵉ ofᵉ orderᵉ preservingᵉ maps**ᵉ fromᵉ `f`ᵉ
to `g`ᵉ isᵉ aᵉ pointwiseᵉ identificationᵉ ofᵉ theᵉ underlyingᵉ mapsᵉ ofᵉ `f`ᵉ andᵉ `g`.ᵉ

```agda
module _
  {αPᵉ αQᵉ γᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  where

  htpy-hom-Large-Posetᵉ : (fᵉ gᵉ : hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ) → UUωᵉ
  htpy-hom-Large-Posetᵉ =
    htpy-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)

  refl-htpy-hom-Large-Posetᵉ :
    (fᵉ : hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ) → htpy-hom-Large-Posetᵉ fᵉ fᵉ
  refl-htpy-hom-Large-Posetᵉ =
    refl-htpy-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
```

## Properties

### Composition of order preserving maps is associative

```agda
module _
  {αPᵉ αQᵉ αRᵉ αSᵉ γhᵉ γgᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ βRᵉ βSᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Rᵉ : Large-Posetᵉ αRᵉ βRᵉ)
  (Sᵉ : Large-Posetᵉ αSᵉ βSᵉ)
  (hᵉ : hom-Large-Posetᵉ γhᵉ Rᵉ Sᵉ)
  (gᵉ : hom-Large-Posetᵉ γgᵉ Qᵉ Rᵉ)
  (fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Qᵉ)
  where

  associative-comp-hom-Large-Posetᵉ :
    htpy-hom-Large-Posetᵉ Pᵉ Sᵉ
      ( comp-hom-Large-Posetᵉ Pᵉ Qᵉ Sᵉ (comp-hom-Large-Posetᵉ Qᵉ Rᵉ Sᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-Large-Posetᵉ Pᵉ Rᵉ Sᵉ hᵉ (comp-hom-Large-Posetᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ))
  associative-comp-hom-Large-Posetᵉ =
    associative-comp-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( large-preorder-Large-Posetᵉ Rᵉ)
      ( large-preorder-Large-Posetᵉ Sᵉ)
      ( hᵉ)
      ( gᵉ)
      ( fᵉ)
```

### Composition of order preserving maps satisfies left and right unit laws

```agda
module _
  {αPᵉ αQᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Qᵉ)
  where

  left-unit-law-comp-hom-Large-Posetᵉ :
    htpy-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( comp-hom-Large-Posetᵉ Pᵉ Qᵉ Qᵉ (id-hom-Large-Posetᵉ Qᵉ) fᵉ)
      ( fᵉ)
  left-unit-law-comp-hom-Large-Posetᵉ =
    left-unit-law-comp-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( fᵉ)

  right-unit-law-comp-hom-Large-Posetᵉ :
    htpy-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( comp-hom-Large-Posetᵉ Pᵉ Pᵉ Qᵉ fᵉ (id-hom-Large-Posetᵉ Pᵉ))
      ( fᵉ)
  right-unit-law-comp-hom-Large-Posetᵉ =
    right-unit-law-comp-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( fᵉ)
```

### Order preserving maps preserve similarity of elements

```agda
module _
  {αPᵉ αQᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Posetᵉ γfᵉ Pᵉ Qᵉ)
  where

  preserves-sim-hom-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    sim-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    sim-Large-Posetᵉ Qᵉ
      ( map-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ xᵉ)
      ( map-hom-Large-Posetᵉ Pᵉ Qᵉ fᵉ yᵉ)
  preserves-sim-hom-Large-Posetᵉ =
    preserves-sim-hom-Large-Preorderᵉ
      ( large-preorder-Large-Posetᵉ Pᵉ)
      ( large-preorder-Large-Posetᵉ Qᵉ)
      ( fᵉ)
```

## See also

-ᵉ [Orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-posets.mdᵉ)
  betweenᵉ largeᵉ posetsᵉ
-ᵉ [Similarity](order-theory.similarity-of-order-preserving-maps-large-posets.mdᵉ)
  ofᵉ orderᵉ preservingᵉ mapsᵉ betweenᵉ largeᵉ posetsᵉ