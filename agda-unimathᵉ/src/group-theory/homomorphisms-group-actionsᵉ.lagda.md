# Homomorphisms of group actions

```agda
module group-theory.homomorphisms-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
```

</details>

## Idea

Aᵉ **morphismᵉ ofᵉ groupᵉ actions**ᵉ fromᵉ aᵉ [`G`-set](group-theory.group-actions.mdᵉ)
`X`ᵉ to aᵉ `G`-setᵉ `Y`ᵉ isᵉ aᵉ mapᵉ fromᵉ theᵉ underlyingᵉ [set](foundation-core.sets.mdᵉ)
ofᵉ `X`ᵉ to theᵉ underlyingᵉ setᵉ ofᵉ `Y`ᵉ **preservingᵉ theᵉ groupᵉ action**.ᵉ Thisᵉ meansᵉ
thatᵉ forᵉ anyᵉ elementᵉ `g`ᵉ ofᵉ theᵉ [group](group-theory.groups.mdᵉ) `G`ᵉ theᵉ squareᵉ

```text
          fᵉ
      Xᵉ ----->ᵉ Yᵉ
      |        |
  μᵉ gᵉ |        | μᵉ gᵉ
      ∨ᵉ        ∨ᵉ
      Xᵉ ----->ᵉ Yᵉ
          fᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md).ᵉ

## Definitions

### The predicate on maps between underlying types of group actions to preserve the group action

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (fᵉ : type-action-Groupᵉ Gᵉ Xᵉ → type-action-Groupᵉ Gᵉ Yᵉ)
  where

  preserves-action-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  preserves-action-Groupᵉ =
    (gᵉ : type-Groupᵉ Gᵉ) →
    coherence-square-mapsᵉ fᵉ (mul-action-Groupᵉ Gᵉ Xᵉ gᵉ) (mul-action-Groupᵉ Gᵉ Yᵉ gᵉ) fᵉ

  is-prop-preserves-action-Groupᵉ : is-propᵉ preserves-action-Groupᵉ
  is-prop-preserves-action-Groupᵉ =
    is-prop-iterated-Πᵉ 2
      ( λ gᵉ xᵉ →
        is-set-type-action-Groupᵉ Gᵉ Yᵉ
          ( fᵉ (mul-action-Groupᵉ Gᵉ Xᵉ gᵉ xᵉ))
          ( mul-action-Groupᵉ Gᵉ Yᵉ gᵉ (fᵉ xᵉ)))

  preserves-action-prop-Groupᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ preserves-action-prop-Groupᵉ = preserves-action-Groupᵉ
  pr2ᵉ preserves-action-prop-Groupᵉ = is-prop-preserves-action-Groupᵉ
```

### Morphisms of `G`-sets

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  hom-action-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-action-Groupᵉ =
    Σᵉ ( type-action-Groupᵉ Gᵉ Xᵉ → type-action-Groupᵉ Gᵉ Yᵉ)
      ( preserves-action-Groupᵉ Gᵉ Xᵉ Yᵉ)

  map-hom-action-Groupᵉ :
    hom-action-Groupᵉ → type-action-Groupᵉ Gᵉ Xᵉ → type-action-Groupᵉ Gᵉ Yᵉ
  map-hom-action-Groupᵉ = pr1ᵉ

  preserves-action-hom-action-Groupᵉ :
    (fᵉ : hom-action-Groupᵉ) →
    preserves-action-Groupᵉ Gᵉ Xᵉ Yᵉ (map-hom-action-Groupᵉ fᵉ)
  preserves-action-hom-action-Groupᵉ = pr2ᵉ
```

### The identity morphism

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  id-hom-action-Groupᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Xᵉ
  pr1ᵉ id-hom-action-Groupᵉ = idᵉ
  pr2ᵉ id-hom-action-Groupᵉ gᵉ = refl-htpyᵉ
```

### Composition of morphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ) (Zᵉ : action-Groupᵉ Gᵉ l4ᵉ)
  where

  map-comp-hom-action-Groupᵉ :
    hom-action-Groupᵉ Gᵉ Yᵉ Zᵉ → hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ →
    type-action-Groupᵉ Gᵉ Xᵉ → type-action-Groupᵉ Gᵉ Zᵉ
  map-comp-hom-action-Groupᵉ gᵉ fᵉ =
    map-hom-action-Groupᵉ Gᵉ Yᵉ Zᵉ gᵉ ∘ᵉ map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ

  preserves-action-comp-hom-action-Groupᵉ :
    (gᵉ : hom-action-Groupᵉ Gᵉ Yᵉ Zᵉ) (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    preserves-action-Groupᵉ Gᵉ Xᵉ Zᵉ (map-comp-hom-action-Groupᵉ gᵉ fᵉ)
  preserves-action-comp-hom-action-Groupᵉ gᵉ fᵉ xᵉ =
    pasting-horizontal-coherence-square-mapsᵉ
      ( map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
      ( map-hom-action-Groupᵉ Gᵉ Yᵉ Zᵉ gᵉ)
      ( mul-action-Groupᵉ Gᵉ Xᵉ xᵉ)
      ( mul-action-Groupᵉ Gᵉ Yᵉ xᵉ)
      ( mul-action-Groupᵉ Gᵉ Zᵉ xᵉ)
      ( map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
      ( map-hom-action-Groupᵉ Gᵉ Yᵉ Zᵉ gᵉ)
      ( preserves-action-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ xᵉ)
      ( preserves-action-hom-action-Groupᵉ Gᵉ Yᵉ Zᵉ gᵉ xᵉ)

  comp-hom-action-Groupᵉ :
    hom-action-Groupᵉ Gᵉ Yᵉ Zᵉ → hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ → hom-action-Groupᵉ Gᵉ Xᵉ Zᵉ
  pr1ᵉ (comp-hom-action-Groupᵉ gᵉ fᵉ) = map-comp-hom-action-Groupᵉ gᵉ fᵉ
  pr2ᵉ (comp-hom-action-Groupᵉ gᵉ fᵉ) = preserves-action-comp-hom-action-Groupᵉ gᵉ fᵉ
```

## Properties

### Equality of homomorphisms of group actions is equivalent to homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ) (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  htpy-hom-action-Groupᵉ :
    (gᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  htpy-hom-action-Groupᵉ gᵉ =
    map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ ~ᵉ map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ gᵉ

  refl-htpy-hom-action-Groupᵉ : htpy-hom-action-Groupᵉ fᵉ
  refl-htpy-hom-action-Groupᵉ = refl-htpyᵉ

  htpy-eq-hom-action-Groupᵉ :
    (gᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    fᵉ ＝ᵉ gᵉ → htpy-hom-action-Groupᵉ gᵉ
  htpy-eq-hom-action-Groupᵉ .fᵉ reflᵉ =
    refl-htpy-hom-action-Groupᵉ

  is-torsorial-htpy-hom-action-Groupᵉ :
    is-torsorialᵉ htpy-hom-action-Groupᵉ
  is-torsorial-htpy-hom-action-Groupᵉ =
    is-torsorial-Eq-subtypeᵉ
      ( is-torsorial-htpyᵉ (map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ))
      ( λ gᵉ →
        is-prop-Πᵉ
          ( λ xᵉ →
            is-prop-Πᵉ
              ( λ yᵉ →
                is-set-type-Setᵉ
                  ( set-action-Groupᵉ Gᵉ Yᵉ)
                  ( gᵉ (mul-action-Groupᵉ Gᵉ Xᵉ xᵉ yᵉ))
                  ( mul-action-Groupᵉ Gᵉ Yᵉ xᵉ (gᵉ yᵉ)))))
      ( map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
      ( refl-htpyᵉ)
      ( preserves-action-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)

  is-equiv-htpy-eq-hom-action-Groupᵉ :
    (gᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → is-equivᵉ (htpy-eq-hom-action-Groupᵉ gᵉ)
  is-equiv-htpy-eq-hom-action-Groupᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-hom-action-Groupᵉ
      htpy-eq-hom-action-Groupᵉ

  extensionality-hom-action-Groupᵉ :
    (gᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → (fᵉ ＝ᵉ gᵉ) ≃ᵉ htpy-hom-action-Groupᵉ gᵉ
  pr1ᵉ (extensionality-hom-action-Groupᵉ gᵉ) =
    htpy-eq-hom-action-Groupᵉ gᵉ
  pr2ᵉ (extensionality-hom-action-Groupᵉ gᵉ) =
    is-equiv-htpy-eq-hom-action-Groupᵉ gᵉ

  eq-htpy-hom-action-Groupᵉ :
    (gᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → htpy-hom-action-Groupᵉ gᵉ → fᵉ ＝ᵉ gᵉ
  eq-htpy-hom-action-Groupᵉ gᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-hom-action-Groupᵉ gᵉ)
```

### The type of morphisms of group actions is a set

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  is-set-hom-action-Groupᵉ :
    is-setᵉ (hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
  is-set-hom-action-Groupᵉ fᵉ gᵉ =
    is-prop-equivᵉ
      ( extensionality-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ gᵉ)
      ( is-prop-Πᵉ
        ( λ xᵉ →
          is-set-type-action-Groupᵉ Gᵉ Yᵉ
            ( map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ xᵉ)
            ( map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ gᵉ xᵉ)))

  hom-set-action-Groupᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  pr1ᵉ hom-set-action-Groupᵉ = hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  pr2ᵉ hom-set-action-Groupᵉ = is-set-hom-action-Groupᵉ
```

### Composition is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (X1ᵉ : action-Groupᵉ Gᵉ l2ᵉ) (X2ᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (X3ᵉ : action-Groupᵉ Gᵉ l4ᵉ) (X4ᵉ : action-Groupᵉ Gᵉ l5ᵉ)
  (hᵉ : hom-action-Groupᵉ Gᵉ X3ᵉ X4ᵉ)
  (gᵉ : hom-action-Groupᵉ Gᵉ X2ᵉ X3ᵉ)
  (fᵉ : hom-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ)
  where

  associative-comp-hom-action-Groupᵉ :
    comp-hom-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X4ᵉ (comp-hom-action-Groupᵉ Gᵉ X2ᵉ X3ᵉ X4ᵉ hᵉ gᵉ) fᵉ ＝ᵉ
    comp-hom-action-Groupᵉ Gᵉ X1ᵉ X3ᵉ X4ᵉ hᵉ (comp-hom-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X3ᵉ gᵉ fᵉ)
  associative-comp-hom-action-Groupᵉ =
    eq-htpy-hom-action-Groupᵉ Gᵉ X1ᵉ X4ᵉ
      ( comp-hom-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X4ᵉ
        ( comp-hom-action-Groupᵉ Gᵉ X2ᵉ X3ᵉ X4ᵉ hᵉ gᵉ)
        ( fᵉ))
      ( comp-hom-action-Groupᵉ Gᵉ X1ᵉ X3ᵉ X4ᵉ
        ( hᵉ)
        ( comp-hom-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X3ᵉ gᵉ fᵉ))
      ( refl-htpyᵉ)
```

### Composition satisfies the left and right unit laws

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  left-unit-law-comp-hom-action-Groupᵉ :
    (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ Yᵉ (id-hom-action-Groupᵉ Gᵉ Yᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-hom-action-Groupᵉ fᵉ =
    eq-htpy-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( comp-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ Yᵉ (id-hom-action-Groupᵉ Gᵉ Yᵉ) fᵉ)
      ( fᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-hom-action-Groupᵉ :
    (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    comp-hom-action-Groupᵉ Gᵉ Xᵉ Xᵉ Yᵉ fᵉ (id-hom-action-Groupᵉ Gᵉ Xᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-hom-action-Groupᵉ fᵉ =
    eq-htpy-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( comp-hom-action-Groupᵉ Gᵉ Xᵉ Xᵉ Yᵉ fᵉ (id-hom-action-Groupᵉ Gᵉ Xᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)
```