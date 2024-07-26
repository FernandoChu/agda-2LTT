# Order preserving maps between large preorders

```agda
module order-theory.order-preserving-maps-large-preordersᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ

open import order-theory.large-preordersᵉ
open import order-theory.similarity-of-elements-large-preordersᵉ
```

</details>

## Idea

Anᵉ **orderᵉ preservingᵉ map**ᵉ betweenᵉ
[largeᵉ preorders](order-theory.large-preorders.mdᵉ) `P`ᵉ andᵉ `Q`ᵉ consistsᵉ ofᵉ aᵉ mapᵉ

```text
  fᵉ : type-Large-Preorderᵉ Pᵉ l1ᵉ → type-Large-Preorderᵉ Qᵉ (γᵉ l1ᵉ)
```

forᵉ eachᵉ [universeᵉ level](foundation.universe-levels.mdᵉ) `l1`,ᵉ suchᵉ thatᵉ `xᵉ ≤ᵉ y`ᵉ
impliesᵉ `fᵉ xᵉ ≤ᵉ fᵉ y`ᵉ forᵉ anyᵉ twoᵉ elementsᵉ `xᵉ yᵉ : P`.ᵉ Theᵉ functionᵉ
`γᵉ : Level → Level`ᵉ thatᵉ specifiesᵉ theᵉ universeᵉ levelᵉ ofᵉ `fᵉ x`ᵉ in termsᵉ ofᵉ theᵉ
universeᵉ levelᵉ ofᵉ `x`ᵉ isᵉ calledᵉ theᵉ **universeᵉ levelᵉ reindexingᵉ function**ᵉ ofᵉ
theᵉ orderᵉ preservingᵉ mapᵉ `f`.ᵉ

## Definitions

### The predicate that a map between large preorders is order preserving

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level} {γᵉ : Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ) (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  where

  preserves-order-map-Large-Preorderᵉ :
    ({lᵉ : Level} → type-Large-Preorderᵉ Pᵉ lᵉ → type-Large-Preorderᵉ Qᵉ (γᵉ lᵉ)) →
    UUωᵉ
  preserves-order-map-Large-Preorderᵉ fᵉ =
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Preorderᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Preorderᵉ Pᵉ l2ᵉ) →
    leq-Large-Preorderᵉ Pᵉ xᵉ yᵉ → leq-Large-Preorderᵉ Qᵉ (fᵉ xᵉ) (fᵉ yᵉ)
```

### The type of order preserving maps between large preorders

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (γᵉ : Level → Level)
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ) (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  where

  record hom-Large-Preorderᵉ : UUωᵉ
    where
    constructor
      make-hom-Large-Preorderᵉ
    field
      map-hom-Large-Preorderᵉ :
        {l1ᵉ : Level} → type-Large-Preorderᵉ Pᵉ l1ᵉ → type-Large-Preorderᵉ Qᵉ (γᵉ l1ᵉ)
      preserves-order-hom-Large-Preorderᵉ :
        preserves-order-map-Large-Preorderᵉ Pᵉ Qᵉ map-hom-Large-Preorderᵉ

  open hom-Large-Preorderᵉ public
```

### The identity order preserving map on a large preorder

```agda
module _
  {αPᵉ : Level → Level} {βPᵉ : Level → Level → Level} (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  where

  id-hom-Large-Preorderᵉ : hom-Large-Preorderᵉ (λ lᵉ → lᵉ) Pᵉ Pᵉ
  map-hom-Large-Preorderᵉ id-hom-Large-Preorderᵉ = idᵉ
  preserves-order-hom-Large-Preorderᵉ id-hom-Large-Preorderᵉ xᵉ yᵉ = idᵉ
```

### Composition of order preserving maps between large preorders

```agda
module _
  {αPᵉ αQᵉ αRᵉ γgᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ βRᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  (Rᵉ : Large-Preorderᵉ αRᵉ βRᵉ)
  (gᵉ : hom-Large-Preorderᵉ γgᵉ Qᵉ Rᵉ)
  (fᵉ : hom-Large-Preorderᵉ γfᵉ Pᵉ Qᵉ)
  where

  map-comp-hom-Large-Preorderᵉ :
    {l1ᵉ : Level} → type-Large-Preorderᵉ Pᵉ l1ᵉ → type-Large-Preorderᵉ Rᵉ (γgᵉ (γfᵉ l1ᵉ))
  map-comp-hom-Large-Preorderᵉ =
    map-hom-Large-Preorderᵉ gᵉ ∘ᵉ map-hom-Large-Preorderᵉ fᵉ

  preserves-order-comp-hom-Large-Preorderᵉ :
    preserves-order-map-Large-Preorderᵉ Pᵉ Rᵉ map-comp-hom-Large-Preorderᵉ
  preserves-order-comp-hom-Large-Preorderᵉ xᵉ yᵉ =
    preserves-order-hom-Large-Preorderᵉ gᵉ _ _ ∘ᵉ
    preserves-order-hom-Large-Preorderᵉ fᵉ _ _

  comp-hom-Large-Preorderᵉ : hom-Large-Preorderᵉ (λ lᵉ → γgᵉ (γfᵉ lᵉ)) Pᵉ Rᵉ
  map-hom-Large-Preorderᵉ comp-hom-Large-Preorderᵉ =
    map-comp-hom-Large-Preorderᵉ
  preserves-order-hom-Large-Preorderᵉ comp-hom-Large-Preorderᵉ =
    preserves-order-comp-hom-Large-Preorderᵉ
```

### Homotopies of order preserving maps between large preorders

Givenᵉ twoᵉ orderᵉ preservingᵉ mapsᵉ `fᵉ gᵉ : hom-Large-Preorderᵉ γᵉ Pᵉ Q`ᵉ with theᵉ sameᵉ
universeᵉ levelᵉ reindexingᵉ `γ`,ᵉ aᵉ **homotopyᵉ ofᵉ orderᵉ preservingᵉ maps**ᵉ fromᵉ `f`ᵉ
to `g`ᵉ isᵉ aᵉ pointwiseᵉ identificationᵉ ofᵉ theᵉ underlyingᵉ mapsᵉ ofᵉ `f`ᵉ andᵉ `g`.ᵉ

```agda
module _
  {αPᵉ αQᵉ γᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ) (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  where

  htpy-hom-Large-Preorderᵉ : (fᵉ gᵉ : hom-Large-Preorderᵉ γᵉ Pᵉ Qᵉ) → UUωᵉ
  htpy-hom-Large-Preorderᵉ fᵉ gᵉ =
    {lᵉ : Level} → map-hom-Large-Preorderᵉ fᵉ {lᵉ} ~ᵉ map-hom-Large-Preorderᵉ gᵉ {lᵉ}

  refl-htpy-hom-Large-Preorderᵉ :
    (fᵉ : hom-Large-Preorderᵉ γᵉ Pᵉ Qᵉ) → htpy-hom-Large-Preorderᵉ fᵉ fᵉ
  refl-htpy-hom-Large-Preorderᵉ fᵉ = refl-htpyᵉ
```

## Properties

### Composition of order preserving maps is associative

```agda
module _
  {αPᵉ αQᵉ αRᵉ αSᵉ γhᵉ γgᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ βRᵉ βSᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  (Rᵉ : Large-Preorderᵉ αRᵉ βRᵉ)
  (Sᵉ : Large-Preorderᵉ αSᵉ βSᵉ)
  (hᵉ : hom-Large-Preorderᵉ γhᵉ Rᵉ Sᵉ)
  (gᵉ : hom-Large-Preorderᵉ γgᵉ Qᵉ Rᵉ)
  (fᵉ : hom-Large-Preorderᵉ γfᵉ Pᵉ Qᵉ)
  where

  associative-comp-hom-Large-Preorderᵉ :
    htpy-hom-Large-Preorderᵉ Pᵉ Sᵉ
      ( comp-hom-Large-Preorderᵉ Pᵉ Qᵉ Sᵉ (comp-hom-Large-Preorderᵉ Qᵉ Rᵉ Sᵉ hᵉ gᵉ) fᵉ)
      ( comp-hom-Large-Preorderᵉ Pᵉ Rᵉ Sᵉ hᵉ (comp-hom-Large-Preorderᵉ Pᵉ Qᵉ Rᵉ gᵉ fᵉ))
  associative-comp-hom-Large-Preorderᵉ = refl-htpyᵉ
```

### Composition of order preserving maps satisfies left and right unit laws

```agda
module _
  {αPᵉ αQᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Preorderᵉ γfᵉ Pᵉ Qᵉ)
  where

  left-unit-law-comp-hom-Large-Preorderᵉ :
    htpy-hom-Large-Preorderᵉ Pᵉ Qᵉ
      ( comp-hom-Large-Preorderᵉ Pᵉ Qᵉ Qᵉ (id-hom-Large-Preorderᵉ Qᵉ) fᵉ)
      ( fᵉ)
  left-unit-law-comp-hom-Large-Preorderᵉ = refl-htpyᵉ

  right-unit-law-comp-hom-Large-Preorderᵉ :
    htpy-hom-Large-Preorderᵉ Pᵉ Qᵉ
      ( comp-hom-Large-Preorderᵉ Pᵉ Pᵉ Qᵉ fᵉ (id-hom-Large-Preorderᵉ Pᵉ))
      ( fᵉ)
  right-unit-law-comp-hom-Large-Preorderᵉ = refl-htpyᵉ
```

### Order preserving maps preserve similarity of elements

```agda
module _
  {αPᵉ αQᵉ γfᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Preorderᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Preorderᵉ αQᵉ βQᵉ)
  (fᵉ : hom-Large-Preorderᵉ γfᵉ Pᵉ Qᵉ)
  where

  preserves-sim-hom-Large-Preorderᵉ :
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Preorderᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Preorderᵉ Pᵉ l2ᵉ) →
    sim-Large-Preorderᵉ Pᵉ xᵉ yᵉ →
    sim-Large-Preorderᵉ Qᵉ
      ( map-hom-Large-Preorderᵉ fᵉ xᵉ)
      ( map-hom-Large-Preorderᵉ fᵉ yᵉ)
  pr1ᵉ (preserves-sim-hom-Large-Preorderᵉ xᵉ yᵉ (sᵉ ,ᵉ tᵉ)) =
    preserves-order-hom-Large-Preorderᵉ fᵉ xᵉ yᵉ sᵉ
  pr2ᵉ (preserves-sim-hom-Large-Preorderᵉ xᵉ yᵉ (sᵉ ,ᵉ tᵉ)) =
    preserves-order-hom-Large-Preorderᵉ fᵉ yᵉ xᵉ tᵉ
```

## See also

-ᵉ [Orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-posets.mdᵉ)
  betweenᵉ largeᵉ posetsᵉ
-ᵉ [Similarity](order-theory.similarity-of-order-preserving-maps-large-preorders.mdᵉ)
  ofᵉ orderᵉ preservingᵉ mapsᵉ betweenᵉ largeᵉ preordersᵉ