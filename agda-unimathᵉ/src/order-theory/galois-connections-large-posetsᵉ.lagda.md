# Galois connections between large posets

```agda
module order-theory.galois-connections-large-posetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import order-theory.large-posetsᵉ
open import order-theory.least-upper-bounds-large-posetsᵉ
open import order-theory.order-preserving-maps-large-posetsᵉ
open import order-theory.principal-lower-sets-large-posetsᵉ
open import order-theory.principal-upper-sets-large-posetsᵉ
open import order-theory.similarity-of-elements-large-posetsᵉ
open import order-theory.similarity-of-order-preserving-maps-large-posetsᵉ
```

</details>

## Idea

Aᵉ **galoisᵉ connection**ᵉ betweenᵉ [largeᵉ posets](order-theory.large-posets.mdᵉ) `P`ᵉ
andᵉ `Q`ᵉ consistsᵉ ofᵉ
[orderᵉ preservingᵉ maps](order-theory.order-preserving-maps-large-posets.mdᵉ)
`fᵉ : hom-Large-Posetᵉ (λ lᵉ → lᵉ) Pᵉ Q`ᵉ andᵉ `hom-Large-Posetᵉ idᵉ Qᵉ P`ᵉ suchᵉ thatᵉ theᵉ
adjointᵉ relationᵉ

```text
  (fᵉ xᵉ ≤ᵉ yᵉ) ↔ᵉ (xᵉ ≤ᵉ gᵉ yᵉ)
```

holdsᵉ forᵉ everyᵉ twoᵉ elementsᵉ `xᵉ : P`ᵉ andᵉ `yᵉ : Q`.ᵉ

Theᵉ followingᵉ tableᵉ listsᵉ theᵉ Galoisᵉ connectionsᵉ thatᵉ haveᵉ beenᵉ formalizedᵉ in
theᵉ agda-unimathᵉ libraryᵉ

{{#includeᵉ tables/galois-connections.mdᵉ}}

## Definitions

### The adjoint relation between order preserving maps between large posets

```agda
module _
  {αPᵉ αQᵉ γᵉ δᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Fᵉ : hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ) (Gᵉ : hom-Large-Posetᵉ δᵉ Qᵉ Pᵉ)
  where

  forward-implication-adjoint-relation-hom-Large-Posetᵉ : UUωᵉ
  forward-implication-adjoint-relation-hom-Large-Posetᵉ =
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ} {yᵉ : type-Large-Posetᵉ Qᵉ l2ᵉ} →
    leq-Large-Posetᵉ Qᵉ (map-hom-Large-Posetᵉ Pᵉ Qᵉ Fᵉ xᵉ) yᵉ →
    leq-Large-Posetᵉ Pᵉ xᵉ (map-hom-Large-Posetᵉ Qᵉ Pᵉ Gᵉ yᵉ)

  backward-implication-adjoint-relation-hom-Large-Posetᵉ : UUωᵉ
  backward-implication-adjoint-relation-hom-Large-Posetᵉ =
    {l1ᵉ l2ᵉ : Level}
    {xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ} {yᵉ : type-Large-Posetᵉ Qᵉ l2ᵉ} →
    leq-Large-Posetᵉ Pᵉ xᵉ (map-hom-Large-Posetᵉ Qᵉ Pᵉ Gᵉ yᵉ) →
    leq-Large-Posetᵉ Qᵉ (map-hom-Large-Posetᵉ Pᵉ Qᵉ Fᵉ xᵉ) yᵉ

  adjoint-relation-hom-Large-Posetᵉ : UUωᵉ
  adjoint-relation-hom-Large-Posetᵉ =
    {l1ᵉ l2ᵉ : Level}
    (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Qᵉ l2ᵉ) →
    leq-Large-Posetᵉ Qᵉ (map-hom-Large-Posetᵉ Pᵉ Qᵉ Fᵉ xᵉ) yᵉ ↔ᵉ
    leq-Large-Posetᵉ Pᵉ xᵉ (map-hom-Large-Posetᵉ Qᵉ Pᵉ Gᵉ yᵉ)
```

### Galois connections between large posets

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (γᵉ : Level → Level) (δᵉ : Level → Level)
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  where

  record
    galois-connection-Large-Posetᵉ : UUωᵉ
    where
    constructor
      make-galois-connection-Large-Posetᵉ
    field
      lower-adjoint-galois-connection-Large-Posetᵉ :
        hom-Large-Posetᵉ γᵉ Pᵉ Qᵉ
      upper-adjoint-galois-connection-Large-Posetᵉ :
        hom-Large-Posetᵉ δᵉ Qᵉ Pᵉ
      adjoint-relation-galois-connection-Large-Posetᵉ :
        adjoint-relation-hom-Large-Posetᵉ Pᵉ Qᵉ
          lower-adjoint-galois-connection-Large-Posetᵉ
          upper-adjoint-galois-connection-Large-Posetᵉ

  open galois-connection-Large-Posetᵉ public

module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  {γᵉ : Level → Level} {δᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  where

  map-lower-adjoint-galois-connection-Large-Posetᵉ :
    {l1ᵉ : Level} → type-Large-Posetᵉ Pᵉ l1ᵉ → type-Large-Posetᵉ Qᵉ (γᵉ l1ᵉ)
  map-lower-adjoint-galois-connection-Large-Posetᵉ =
    map-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)

  preserves-order-lower-adjoint-galois-connection-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ) →
    leq-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    leq-Large-Posetᵉ Qᵉ
      ( map-lower-adjoint-galois-connection-Large-Posetᵉ xᵉ)
      ( map-lower-adjoint-galois-connection-Large-Posetᵉ yᵉ)
  preserves-order-lower-adjoint-galois-connection-Large-Posetᵉ =
    preserves-order-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)

  map-upper-adjoint-galois-connection-Large-Posetᵉ :
    {l1ᵉ : Level} → type-Large-Posetᵉ Qᵉ l1ᵉ → type-Large-Posetᵉ Pᵉ (δᵉ l1ᵉ)
  map-upper-adjoint-galois-connection-Large-Posetᵉ =
    map-hom-Large-Posetᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)

  preserves-order-upper-adjoint-galois-connection-Large-Posetᵉ :
    {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Qᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Qᵉ l2ᵉ) →
    leq-Large-Posetᵉ Qᵉ xᵉ yᵉ →
    leq-Large-Posetᵉ Pᵉ
      ( map-upper-adjoint-galois-connection-Large-Posetᵉ xᵉ)
      ( map-upper-adjoint-galois-connection-Large-Posetᵉ yᵉ)
  preserves-order-upper-adjoint-galois-connection-Large-Posetᵉ =
    preserves-order-hom-Large-Posetᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)

  forward-implication-adjoint-relation-galois-connection-Large-Posetᵉ :
    forward-implication-adjoint-relation-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
  forward-implication-adjoint-relation-galois-connection-Large-Posetᵉ =
    forward-implicationᵉ (adjoint-relation-galois-connection-Large-Posetᵉ Gᵉ _ _)

  backward-implication-adjoint-relation-galois-connection-Large-Posetᵉ :
    backward-implication-adjoint-relation-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
  backward-implication-adjoint-relation-galois-connection-Large-Posetᵉ =
    backward-implicationᵉ (adjoint-relation-galois-connection-Large-Posetᵉ Gᵉ _ _)
```

### Composition of Galois connections

```agda
module _
  {αPᵉ αQᵉ αRᵉ : Level → Level} {βPᵉ βQᵉ βRᵉ : Level → Level → Level}
  {γGᵉ γHᵉ : Level → Level} {δGᵉ δHᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ)
  (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Rᵉ : Large-Posetᵉ αRᵉ βRᵉ)
  (Hᵉ : galois-connection-Large-Posetᵉ γHᵉ δHᵉ Qᵉ Rᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γGᵉ δGᵉ Pᵉ Qᵉ)
  where

  lower-adjoint-comp-galois-connection-Large-Posetᵉ :
    hom-Large-Posetᵉ (λ lᵉ → γHᵉ (γGᵉ lᵉ)) Pᵉ Rᵉ
  lower-adjoint-comp-galois-connection-Large-Posetᵉ =
    comp-hom-Large-Posetᵉ Pᵉ Qᵉ Rᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)

  map-lower-adjoint-comp-galois-connection-Large-Posetᵉ :
    {lᵉ : Level} → type-Large-Posetᵉ Pᵉ lᵉ → type-Large-Posetᵉ Rᵉ (γHᵉ (γGᵉ lᵉ))
  map-lower-adjoint-comp-galois-connection-Large-Posetᵉ =
    map-comp-hom-Large-Posetᵉ Pᵉ Qᵉ Rᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)

  preserves-order-lower-adjoint-comp-galois-connection-Large-Posetᵉ :
    preserves-order-map-Large-Posetᵉ Pᵉ Rᵉ
      map-lower-adjoint-comp-galois-connection-Large-Posetᵉ
  preserves-order-lower-adjoint-comp-galois-connection-Large-Posetᵉ =
    preserves-order-comp-hom-Large-Posetᵉ Pᵉ Qᵉ Rᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)

  upper-adjoint-comp-galois-connection-Large-Posetᵉ :
    hom-Large-Posetᵉ (λ lᵉ → δGᵉ (δHᵉ lᵉ)) Rᵉ Pᵉ
  upper-adjoint-comp-galois-connection-Large-Posetᵉ =
    comp-hom-Large-Posetᵉ Rᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Hᵉ)

  map-upper-adjoint-comp-galois-connection-Large-Posetᵉ :
    {lᵉ : Level} → type-Large-Posetᵉ Rᵉ lᵉ → type-Large-Posetᵉ Pᵉ (δGᵉ (δHᵉ lᵉ))
  map-upper-adjoint-comp-galois-connection-Large-Posetᵉ =
    map-comp-hom-Large-Posetᵉ Rᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Hᵉ)

  preserves-order-upper-adjoint-comp-galois-connection-Large-Posetᵉ :
    preserves-order-map-Large-Posetᵉ Rᵉ Pᵉ
      map-upper-adjoint-comp-galois-connection-Large-Posetᵉ
  preserves-order-upper-adjoint-comp-galois-connection-Large-Posetᵉ =
    preserves-order-comp-hom-Large-Posetᵉ Rᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Hᵉ)

  forward-implication-adjoint-relation-comp-galois-connection-Large-Posetᵉ :
    forward-implication-adjoint-relation-hom-Large-Posetᵉ Pᵉ Rᵉ
      lower-adjoint-comp-galois-connection-Large-Posetᵉ
      upper-adjoint-comp-galois-connection-Large-Posetᵉ
  forward-implication-adjoint-relation-comp-galois-connection-Large-Posetᵉ =
    forward-implication-adjoint-relation-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ ∘ᵉ
    forward-implication-adjoint-relation-galois-connection-Large-Posetᵉ Qᵉ Rᵉ Hᵉ

  backward-implication-adjoint-relation-comp-galois-connection-Large-Posetᵉ :
    backward-implication-adjoint-relation-hom-Large-Posetᵉ Pᵉ Rᵉ
      lower-adjoint-comp-galois-connection-Large-Posetᵉ
      upper-adjoint-comp-galois-connection-Large-Posetᵉ
  backward-implication-adjoint-relation-comp-galois-connection-Large-Posetᵉ =
    backward-implication-adjoint-relation-galois-connection-Large-Posetᵉ Qᵉ Rᵉ Hᵉ ∘ᵉ
    backward-implication-adjoint-relation-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ

  adjoint-relation-comp-galois-connection-Large-Posetᵉ :
    adjoint-relation-hom-Large-Posetᵉ Pᵉ Rᵉ
      lower-adjoint-comp-galois-connection-Large-Posetᵉ
      upper-adjoint-comp-galois-connection-Large-Posetᵉ
  pr1ᵉ (adjoint-relation-comp-galois-connection-Large-Posetᵉ xᵉ yᵉ) =
    forward-implication-adjoint-relation-comp-galois-connection-Large-Posetᵉ
  pr2ᵉ (adjoint-relation-comp-galois-connection-Large-Posetᵉ xᵉ yᵉ) =
    backward-implication-adjoint-relation-comp-galois-connection-Large-Posetᵉ

  comp-galois-connection-Large-Posetᵉ :
    galois-connection-Large-Posetᵉ (λ lᵉ → γHᵉ (γGᵉ lᵉ)) (λ lᵉ → δGᵉ (δHᵉ lᵉ)) Pᵉ Rᵉ
  lower-adjoint-galois-connection-Large-Posetᵉ
    comp-galois-connection-Large-Posetᵉ =
    lower-adjoint-comp-galois-connection-Large-Posetᵉ
  upper-adjoint-galois-connection-Large-Posetᵉ
    comp-galois-connection-Large-Posetᵉ =
    upper-adjoint-comp-galois-connection-Large-Posetᵉ
  adjoint-relation-galois-connection-Large-Posetᵉ
    comp-galois-connection-Large-Posetᵉ =
    adjoint-relation-comp-galois-connection-Large-Posetᵉ
```

### Homotopies of Galois connections

**Homotopiesᵉ ofᵉ Galoisᵉ connections**ᵉ areᵉ pointwiseᵉ identificationsᵉ betweenᵉ
eitherᵉ theirᵉ lowerᵉ adjointsᵉ orᵉ theirᵉ upperᵉ adjoints.ᵉ Weᵉ willᵉ showᵉ belowᵉ thatᵉ
homotopiesᵉ betweenᵉ lowerᵉ adjointsᵉ induceᵉ homotopiesᵉ betweenᵉ upperᵉ adjointsᵉ andᵉ
viceᵉ versa.ᵉ

**Note:**ᵉ Weᵉ canᵉ onlyᵉ haveᵉ homotopiesᵉ betweenᵉ Galoisᵉ connectionsᵉ with theᵉ sameᵉ
universeᵉ levelᵉ reindexingᵉ functions.ᵉ

```agda
module _
  {αPᵉ αQᵉ γᵉ δᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ Hᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  where

  lower-htpy-galois-connection-Large-Posetᵉ : UUωᵉ
  lower-htpy-galois-connection-Large-Posetᵉ =
    htpy-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( lower-adjoint-galois-connection-Large-Posetᵉ Hᵉ)

  upper-htpy-galois-connection-Large-Posetᵉ : UUωᵉ
  upper-htpy-galois-connection-Large-Posetᵉ =
    htpy-hom-Large-Posetᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
```

### Similarity of Galois connections

**Similaritiesᵉ ofᵉ Galoisᵉ connections**ᵉ areᵉ pointwiseᵉ
[similarities](order-theory.similarity-of-elements-large-posets.mdᵉ) betweenᵉ
eitherᵉ theirᵉ lowerᵉ orᵉ theirᵉ upperᵉ adjoints.ᵉ Weᵉ willᵉ showᵉ belowᵉ thatᵉ similaritiesᵉ
betweenᵉ lowerᵉ adjointsᵉ induceᵉ similaritiesᵉ betweenᵉ upperᵉ adjointsᵉ andᵉ viceᵉ
versa.ᵉ

**Note:**ᵉ Sinceᵉ theᵉ notionᵉ ofᵉ similarityᵉ appliesᵉ to galoisᵉ connectionsᵉ with notᵉ
necessarilyᵉ theᵉ sameᵉ universeᵉ levelᵉ reindexingᵉ function,ᵉ itᵉ isᵉ slightlyᵉ moreᵉ
flexible.ᵉ Forᵉ thisᵉ reason,ᵉ itᵉ mayᵉ beᵉ easierᵉ to workᵉ with similarityᵉ ofᵉ galoisᵉ
connections.ᵉ

```agda
module _
  {αPᵉ αQᵉ γGᵉ γHᵉ δGᵉ δHᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γGᵉ δGᵉ Pᵉ Qᵉ)
  (Hᵉ : galois-connection-Large-Posetᵉ γHᵉ δHᵉ Pᵉ Qᵉ)
  where

  lower-sim-galois-connection-Large-Posetᵉ : UUωᵉ
  lower-sim-galois-connection-Large-Posetᵉ =
    sim-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( lower-adjoint-galois-connection-Large-Posetᵉ Hᵉ)

  upper-sim-galois-connection-Large-Posetᵉ : UUωᵉ
  upper-sim-galois-connection-Large-Posetᵉ =
    sim-hom-Large-Posetᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
```

### Lower universal objects of galois connections

Considerᵉ aᵉ Galoisᵉ connectionᵉ `Gᵉ : Pᵉ → Q`ᵉ andᵉ anᵉ elementᵉ `xᵉ : P`.ᵉ Anᵉ elementᵉ
`x'ᵉ : Q`ᵉ isᵉ thenᵉ saidᵉ to satisfyᵉ theᵉ **lowerᵉ universalᵉ property**ᵉ with respectᵉ
to `x`ᵉ ifᵉ theᵉ logicalᵉ equivalenceᵉ

```text
  (x'ᵉ ≤-Qᵉ yᵉ) ↔ᵉ (xᵉ ≤-Pᵉ UGᵉ yᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ `yᵉ : Q`.ᵉ

```agda
module _
  {αPᵉ αQᵉ γᵉ δᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ)
  (x'ᵉ : type-Large-Posetᵉ Qᵉ l2ᵉ)
  where

  is-lower-element-galois-connection-Large-Posetᵉ : UUωᵉ
  is-lower-element-galois-connection-Large-Posetᵉ =
    {lᵉ : Level} (yᵉ : type-Large-Posetᵉ Qᵉ lᵉ) →
    leq-Large-Posetᵉ Qᵉ x'ᵉ yᵉ ↔ᵉ
    leq-Large-Posetᵉ Pᵉ xᵉ
      ( map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ yᵉ)
```

### Upper universal objects of galois connections

Considerᵉ aᵉ Galoisᵉ connectionᵉ `Gᵉ : Pᵉ → Q`ᵉ andᵉ anᵉ elementᵉ `yᵉ : Q`.ᵉ Anᵉ elementᵉ
`y'ᵉ : P`ᵉ isᵉ thenᵉ saidᵉ to satisfyᵉ theᵉ **upperᵉ universalᵉ property**ᵉ with respectᵉ
to `y`ᵉ ifᵉ theᵉ logicalᵉ equivalenceᵉ

```text
  (LGᵉ xᵉ ≤-Qᵉ yᵉ) ↔ᵉ (xᵉ ≤-Pᵉ y'ᵉ)
```

holdsᵉ forᵉ everyᵉ elementᵉ `xᵉ : P`.ᵉ

```agda
module _
  {αPᵉ αQᵉ γᵉ δᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  {l1ᵉ l2ᵉ : Level} (yᵉ : type-Large-Posetᵉ Qᵉ l1ᵉ)
  (y'ᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-upper-element-galois-connection-Large-Posetᵉ : UUωᵉ
  is-upper-element-galois-connection-Large-Posetᵉ =
    {lᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ lᵉ) →
    leq-Large-Posetᵉ Qᵉ
      ( map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ xᵉ)
      ( yᵉ) ↔ᵉ
    leq-Large-Posetᵉ Pᵉ xᵉ y'ᵉ
```

## Properties

### A similarity between lower adjoints of a Galois connection induces a similarity between upper adjoints, and vice versa

**Proof:**ᵉ Considerᵉ twoᵉ Galoisᵉ connectionsᵉ `LGᵉ ⊣ᵉ UG`ᵉ andᵉ `LHᵉ ⊣ᵉ UH`ᵉ betweenᵉ `P`ᵉ
andᵉ `Q`,ᵉ andᵉ supposeᵉ thatᵉ `LG(xᵉ) ~ᵉ LH(x)`ᵉ forᵉ allᵉ elementsᵉ `xᵉ : P`.ᵉ Thenᵉ itᵉ
followsᵉ thatᵉ

```text
  (xᵉ ≤ᵉ UG(yᵉ)) ↔ᵉ (LG(xᵉ) ≤ᵉ yᵉ) ↔ᵉ (LH(xᵉ) ≤ᵉ yᵉ) ↔ᵉ (xᵉ ≤ᵉ UH(y)).ᵉ
```

Thereforeᵉ itᵉ followsᵉ thatᵉ `UG(y)`ᵉ andᵉ `UH(y)`ᵉ haveᵉ theᵉ sameᵉ lowerᵉ sets,ᵉ andᵉ
henceᵉ theyᵉ mustᵉ beᵉ equal.ᵉ

```agda
module _
  {αPᵉ αQᵉ γGᵉ γHᵉ δGᵉ δHᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γGᵉ δGᵉ Pᵉ Qᵉ)
  (Hᵉ : galois-connection-Large-Posetᵉ γHᵉ δHᵉ Pᵉ Qᵉ)
  where

  upper-sim-lower-sim-galois-connection-Large-Posetᵉ :
    lower-sim-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ Hᵉ →
    upper-sim-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ Gᵉ
  upper-sim-lower-sim-galois-connection-Large-Posetᵉ
    pᵉ xᵉ =
    sim-has-same-elements-principal-lower-set-element-Large-Posetᵉ Pᵉ
      ( λ yᵉ →
        logical-equivalence-reasoningᵉ
          leq-Large-Posetᵉ Pᵉ yᵉ
            ( map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ xᵉ)
          ↔ᵉ leq-Large-Posetᵉ Qᵉ
              ( map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ yᵉ)
              ( xᵉ)
            byᵉ inv-iffᵉ (adjoint-relation-galois-connection-Large-Posetᵉ Hᵉ yᵉ xᵉ)
          ↔ᵉ leq-Large-Posetᵉ Qᵉ
              ( map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ yᵉ)
              ( xᵉ)
            byᵉ
            inv-iffᵉ
              ( has-same-elements-principal-upper-set-element-sim-Large-Posetᵉ Qᵉ
                ( pᵉ yᵉ)
                ( xᵉ))
          ↔ᵉ leq-Large-Posetᵉ Pᵉ yᵉ
              ( map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ xᵉ)
            byᵉ adjoint-relation-galois-connection-Large-Posetᵉ Gᵉ yᵉ xᵉ)

  lower-sim-upper-sim-galois-connection-Large-Posetᵉ :
    upper-sim-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ Gᵉ →
    lower-sim-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ Hᵉ
  lower-sim-upper-sim-galois-connection-Large-Posetᵉ
    pᵉ yᵉ =
    sim-has-same-elements-principal-upper-set-element-Large-Posetᵉ Qᵉ
      ( λ xᵉ →
        logical-equivalence-reasoningᵉ
          leq-Large-Posetᵉ Qᵉ
            ( map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ yᵉ)
            ( xᵉ)
          ↔ᵉ leq-Large-Posetᵉ Pᵉ yᵉ
              ( map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ xᵉ)
            byᵉ adjoint-relation-galois-connection-Large-Posetᵉ Gᵉ yᵉ xᵉ
          ↔ᵉ leq-Large-Posetᵉ Pᵉ yᵉ
              ( map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ xᵉ)
            byᵉ
            inv-iffᵉ
              ( has-same-elements-principal-lower-set-element-sim-Large-Posetᵉ Pᵉ
                ( pᵉ xᵉ)
                ( yᵉ))
          ↔ᵉ leq-Large-Posetᵉ Qᵉ
              ( map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ yᵉ)
              ( xᵉ)
            byᵉ inv-iffᵉ (adjoint-relation-galois-connection-Large-Posetᵉ Hᵉ yᵉ xᵉ))
```

### A homotopy between lower adjoints of a Galois connection induces a homotopy between upper adjoints, and vice versa

**Proof:**ᵉ Considerᵉ twoᵉ Galoisᵉ connectionsᵉ `LGᵉ ⊣ᵉ UG`ᵉ andᵉ `LHᵉ ⊣ᵉ UH`ᵉ betweenᵉ `P`ᵉ
andᵉ `Q`,ᵉ andᵉ supposeᵉ thatᵉ `LGᵉ ~ᵉ LH`.ᵉ Thenᵉ thereᵉ isᵉ aᵉ similarityᵉ `LGᵉ ≈ᵉ LH`,ᵉ andᵉ
thisᵉ inducesᵉ aᵉ similarityᵉ `UGᵉ ≈ᵉ UH`.ᵉ Inᵉ otherᵉ words,ᵉ weᵉ obtainᵉ thatᵉ

```text
  UGᵉ yᵉ ~ᵉ UHᵉ yᵉ
```

forᵉ anyᵉ elementᵉ `yᵉ : Q`.ᵉ Sinceᵉ `UGᵉ y`ᵉ andᵉ `UHᵉ y`ᵉ areᵉ ofᵉ theᵉ sameᵉ universeᵉ level,ᵉ
itᵉ followsᵉ thatᵉ theyᵉ areᵉ equal.ᵉ

```agda
module _
  {αPᵉ αQᵉ γᵉ δᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ Hᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  where

  upper-htpy-lower-htpy-galois-connection-Large-Posetᵉ :
    lower-htpy-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ Hᵉ →
    upper-htpy-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ Hᵉ
  upper-htpy-lower-htpy-galois-connection-Large-Posetᵉ pᵉ =
    htpy-sim-hom-Large-Posetᵉ Qᵉ Pᵉ
      ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( upper-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
      ( upper-sim-lower-sim-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ Gᵉ
        ( sim-htpy-hom-Large-Posetᵉ Pᵉ Qᵉ
          ( lower-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
          ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
          ( inv-htpyᵉ pᵉ)))

  lower-htpy-upper-htpy-galois-connection-Large-Posetᵉ :
    upper-htpy-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Hᵉ Gᵉ →
    lower-htpy-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ Hᵉ
  lower-htpy-upper-htpy-galois-connection-Large-Posetᵉ pᵉ =
    htpy-sim-hom-Large-Posetᵉ Pᵉ Qᵉ
      ( lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
      ( lower-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
      ( lower-sim-upper-sim-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ Hᵉ
        ( sim-htpy-hom-Large-Posetᵉ Qᵉ Pᵉ
          ( upper-adjoint-galois-connection-Large-Posetᵉ Hᵉ)
          ( upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ)
          ( pᵉ)))
```

### An element `x' : Q` satisfies the lower universal property with respect to `x : P` if and only if it is similar to the element `LG x`

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  {γᵉ δᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  {l1ᵉ l2ᵉ : Level} (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (x'ᵉ : type-Large-Posetᵉ Qᵉ l2ᵉ)
  where

  is-lower-element-sim-galois-connection-Large-Posetᵉ :
    sim-Large-Posetᵉ Qᵉ
      ( map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ xᵉ)
      ( x'ᵉ) →
    is-lower-element-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ xᵉ x'ᵉ
  pr1ᵉ (is-lower-element-sim-galois-connection-Large-Posetᵉ sᵉ yᵉ) pᵉ =
    forward-implication-adjoint-relation-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ
      ( transitive-leq-Large-Posetᵉ Qᵉ _ x'ᵉ yᵉ pᵉ (pr1ᵉ sᵉ))
  pr2ᵉ (is-lower-element-sim-galois-connection-Large-Posetᵉ sᵉ yᵉ) pᵉ =
    transitive-leq-Large-Posetᵉ Qᵉ x'ᵉ _ yᵉ
      ( backward-implication-adjoint-relation-galois-connection-Large-Posetᵉ
        Pᵉ Qᵉ Gᵉ pᵉ)
      ( pr2ᵉ sᵉ)

  sim-is-lower-element-galois-connection-Large-Posetᵉ :
    is-lower-element-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ xᵉ x'ᵉ →
    sim-Large-Posetᵉ Qᵉ
      ( map-lower-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ xᵉ)
      ( x'ᵉ)
  sim-is-lower-element-galois-connection-Large-Posetᵉ lᵉ =
    sim-has-same-elements-principal-upper-set-element-Large-Posetᵉ Qᵉ
      ( λ yᵉ →
        logical-equivalence-reasoningᵉ
          leq-Large-Posetᵉ Qᵉ _ yᵉ
          ↔ᵉ leq-Large-Posetᵉ Pᵉ xᵉ _
            byᵉ adjoint-relation-galois-connection-Large-Posetᵉ Gᵉ xᵉ yᵉ
          ↔ᵉ leq-Large-Posetᵉ Qᵉ x'ᵉ yᵉ
            byᵉ inv-iffᵉ (lᵉ yᵉ))
```

### An element `y' : P` satisfies the upper universal property with respect to `y : Q` if and only if it is similar to the element `UG y`

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  {γᵉ δᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  {l1ᵉ l2ᵉ : Level} (yᵉ : type-Large-Posetᵉ Qᵉ l1ᵉ) (y'ᵉ : type-Large-Posetᵉ Pᵉ l2ᵉ)
  where

  is-upper-element-sim-galois-connection-Large-Posetᵉ :
    sim-Large-Posetᵉ Pᵉ
      ( map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ yᵉ)
      ( y'ᵉ) →
    is-upper-element-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ yᵉ y'ᵉ
  pr1ᵉ (is-upper-element-sim-galois-connection-Large-Posetᵉ sᵉ xᵉ) pᵉ =
    transitive-leq-Large-Posetᵉ Pᵉ xᵉ _ y'ᵉ
      ( pr1ᵉ sᵉ)
      ( forward-implication-adjoint-relation-galois-connection-Large-Posetᵉ
        Pᵉ Qᵉ Gᵉ pᵉ)
  pr2ᵉ (is-upper-element-sim-galois-connection-Large-Posetᵉ sᵉ xᵉ) pᵉ =
    backward-implication-adjoint-relation-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ
      ( transitive-leq-Large-Posetᵉ Pᵉ xᵉ y'ᵉ _ (pr2ᵉ sᵉ) pᵉ)

  sim-is-upper-element-galois-connection-Large-Posetᵉ :
    is-upper-element-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ yᵉ y'ᵉ →
    sim-Large-Posetᵉ Pᵉ
      ( map-upper-adjoint-galois-connection-Large-Posetᵉ Pᵉ Qᵉ Gᵉ yᵉ)
      ( y'ᵉ)
  sim-is-upper-element-galois-connection-Large-Posetᵉ uᵉ =
    sim-has-same-elements-principal-lower-set-element-Large-Posetᵉ Pᵉ
      ( λ xᵉ →
        logical-equivalence-reasoningᵉ
          leq-Large-Posetᵉ Pᵉ xᵉ _
          ↔ᵉ leq-Large-Posetᵉ Qᵉ _ yᵉ
            byᵉ inv-iffᵉ (adjoint-relation-galois-connection-Large-Posetᵉ Gᵉ xᵉ yᵉ)
          ↔ᵉ leq-Large-Posetᵉ Pᵉ xᵉ y'ᵉ
            byᵉ uᵉ xᵉ)
```

### The lower adjoint of a Galois connection preserves all existing joins

```agda
module _
  {αPᵉ αQᵉ : Level → Level} {βPᵉ βQᵉ : Level → Level → Level}
  {γᵉ δᵉ : Level → Level}
  (Pᵉ : Large-Posetᵉ αPᵉ βPᵉ) (Qᵉ : Large-Posetᵉ αQᵉ βQᵉ)
  (Gᵉ : galois-connection-Large-Posetᵉ γᵉ δᵉ Pᵉ Qᵉ)
  where

  private
    _≤-Pᵉ_ :
      {l1ᵉ l2ᵉ : Level} → type-Large-Posetᵉ Pᵉ l1ᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ →
      UUᵉ (βPᵉ l1ᵉ l2ᵉ)
    _≤-Pᵉ_ = leq-Large-Posetᵉ Pᵉ

    _≤-Qᵉ_ :
      {l1ᵉ l2ᵉ : Level} → type-Large-Posetᵉ Qᵉ l1ᵉ → type-Large-Posetᵉ Qᵉ l2ᵉ →
      UUᵉ (βQᵉ l1ᵉ l2ᵉ)
    _≤-Qᵉ_ = leq-Large-Posetᵉ Qᵉ

    hom-fᵉ : hom-Large-Posetᵉ _ Pᵉ Qᵉ
    hom-fᵉ = lower-adjoint-galois-connection-Large-Posetᵉ Gᵉ

    fᵉ : {lᵉ : Level} → type-Large-Posetᵉ Pᵉ lᵉ → type-Large-Posetᵉ Qᵉ (γᵉ lᵉ)
    fᵉ = map-hom-Large-Posetᵉ Pᵉ Qᵉ hom-fᵉ

    hom-gᵉ : hom-Large-Posetᵉ _ Qᵉ Pᵉ
    hom-gᵉ = upper-adjoint-galois-connection-Large-Posetᵉ Gᵉ

    gᵉ : {lᵉ : Level} → type-Large-Posetᵉ Qᵉ lᵉ → type-Large-Posetᵉ Pᵉ (δᵉ lᵉ)
    gᵉ = map-hom-Large-Posetᵉ Qᵉ Pᵉ hom-gᵉ

    adjoint-relation-Gᵉ :
      {l1ᵉ l2ᵉ : Level}
      (xᵉ : type-Large-Posetᵉ Pᵉ l1ᵉ) (yᵉ : type-Large-Posetᵉ Qᵉ l2ᵉ) →
      leq-Large-Posetᵉ Qᵉ (fᵉ xᵉ) yᵉ ↔ᵉ
      leq-Large-Posetᵉ Pᵉ xᵉ (gᵉ yᵉ)
    adjoint-relation-Gᵉ = adjoint-relation-galois-connection-Large-Posetᵉ Gᵉ

  preserves-join-lower-adjoint-galois-connection-Large-Posetᵉ :
    {l1ᵉ l2ᵉ l3ᵉ : Level} {Uᵉ : UUᵉ l1ᵉ} (xᵉ : Uᵉ → type-Large-Posetᵉ Pᵉ l2ᵉ)
    (yᵉ : type-Large-Posetᵉ Pᵉ l3ᵉ) →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ Pᵉ xᵉ yᵉ →
    is-least-upper-bound-family-of-elements-Large-Posetᵉ Qᵉ
      ( λ αᵉ → fᵉ (xᵉ αᵉ))
      ( fᵉ yᵉ)
  preserves-join-lower-adjoint-galois-connection-Large-Posetᵉ xᵉ yᵉ Hᵉ zᵉ =
    logical-equivalence-reasoningᵉ
      ((αᵉ : _) → fᵉ (xᵉ αᵉ) ≤-Qᵉ zᵉ)
      ↔ᵉ ((αᵉ : _) → (xᵉ αᵉ) ≤-Pᵉ gᵉ zᵉ)
        byᵉ iff-Π-iff-familyᵉ (λ αᵉ → adjoint-relation-Gᵉ (xᵉ αᵉ) zᵉ)
      ↔ᵉ yᵉ ≤-Pᵉ gᵉ zᵉ byᵉ Hᵉ (gᵉ zᵉ)
      ↔ᵉ fᵉ yᵉ ≤-Qᵉ zᵉ byᵉ inv-iffᵉ (adjoint-relation-Gᵉ yᵉ zᵉ)
```