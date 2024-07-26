# Small ∞-groups

```agda
module higher-group-theory.small-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.imagesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.replacementᵉ
open import foundation.small-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.equivalences-higher-groupsᵉ
open import higher-group-theory.higher-groupsᵉ

open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.small-pointed-typesᵉ
```

</details>

## Idea

Anᵉ [∞-group](higher-group-theory.higher-groups.mdᵉ) `G`ᵉ isᵉ saidᵉ to beᵉ
{{#conceptᵉ "small"ᵉ Disambiguation="∞-group"ᵉ Agda=is-small-∞-Groupᵉ}} with respectᵉ
to aᵉ universeᵉ `𝒰`ᵉ ifᵉ itsᵉ underlyingᵉ typeᵉ isᵉ `𝒰`-small.ᵉ Byᵉ theᵉ
[typeᵉ theoreticᵉ replacementᵉ principle](foundation.replacement.mdᵉ) itᵉ followsᵉ
thatᵉ `G`ᵉ isᵉ smallᵉ ifᵉ andᵉ onlyᵉ ifᵉ itsᵉ classifyingᵉ typeᵉ `BG`ᵉ isᵉ small.ᵉ Thisᵉ
observationᵉ impliesᵉ thatᵉ anᵉ ∞-groupᵉ `G`ᵉ isᵉ smallᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ isᵉ
{{#conceptᵉ "structurallyᵉ small"ᵉ Disambiguation="∞-group"ᵉ Agda=is-structurally-small-∞-Groupᵉ}}
in theᵉ senseᵉ thatᵉ itᵉ comesᵉ equippedᵉ with anᵉ elementᵉ ofᵉ typeᵉ

```text
  Σᵉ (Hᵉ : ∞-Group),ᵉ Gᵉ ≃ᵉ H,ᵉ
```

where theᵉ typeᵉ `Gᵉ ≃ᵉ H`ᵉ isᵉ theᵉ typeᵉ ofᵉ
[equivalencesᵉ ofᵉ ∞-groups](higher-group-theory.equivalences-higher-groups.md).ᵉ

Finally,ᵉ weᵉ alsoᵉ introduceᵉ theᵉ notionᵉ ofᵉ _pointedᵉ smallᵉ ∞-group_.ᵉ Anᵉ ∞-groupᵉ `G`ᵉ
isᵉ saidᵉ to beᵉ
{{#conceptᵉ "pointedᵉ small"ᵉ Disambiguation="∞-group"ᵉ Agda=is-pointed-small-∞-Groupᵉ}}
ifᵉ itsᵉ classifyingᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `BG`ᵉ isᵉ
[pointedᵉ small](structured-types.small-pointed-types.md).ᵉ

## Definitions

### The predicate of being a small ∞-group

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ)
  where

  is-small-prop-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-small-prop-∞-Groupᵉ = is-small-Propᵉ l2ᵉ (type-∞-Groupᵉ Gᵉ)

  is-small-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-small-∞-Groupᵉ = is-smallᵉ l2ᵉ (type-∞-Groupᵉ Gᵉ)

  is-prop-is-small-∞-Groupᵉ : is-propᵉ is-small-∞-Groupᵉ
  is-prop-is-small-∞-Groupᵉ = is-prop-is-smallᵉ l2ᵉ (type-∞-Groupᵉ Gᵉ)
```

### The predicate of being a structurally small ∞-group

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ)
  where

  is-structurally-small-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-structurally-small-∞-Groupᵉ =
    Σᵉ (∞-Groupᵉ l2ᵉ) (equiv-∞-Groupᵉ Gᵉ)

  abstract
    is-prop-is-structurally-small-∞-Groupᵉ :
      is-propᵉ is-structurally-small-∞-Groupᵉ
    is-prop-is-structurally-small-∞-Groupᵉ =
      is-prop-equivᵉ
        ( equiv-right-swap-Σᵉ)
        ( is-prop-Σᵉ
          ( is-prop-is-pointed-small-Pointed-Typeᵉ
            ( classifying-pointed-type-∞-Groupᵉ Gᵉ))
          ( λ Hᵉ → is-prop-is-0-connectedᵉ _))

  is-structurally-small-prop-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  pr1ᵉ is-structurally-small-prop-∞-Groupᵉ = is-structurally-small-∞-Groupᵉ
  pr2ᵉ is-structurally-small-prop-∞-Groupᵉ = is-prop-is-structurally-small-∞-Groupᵉ

module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : is-structurally-small-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  ∞-group-is-structurally-small-∞-Groupᵉ : ∞-Groupᵉ l2ᵉ
  ∞-group-is-structurally-small-∞-Groupᵉ = pr1ᵉ Hᵉ

  type-∞-group-is-structurally-small-∞-Groupᵉ : UUᵉ l2ᵉ
  type-∞-group-is-structurally-small-∞-Groupᵉ =
    type-∞-Groupᵉ ∞-group-is-structurally-small-∞-Groupᵉ

  equiv-∞-group-is-structurally-small-∞-Groupᵉ :
    equiv-∞-Groupᵉ Gᵉ ∞-group-is-structurally-small-∞-Groupᵉ
  equiv-∞-group-is-structurally-small-∞-Groupᵉ = pr2ᵉ Hᵉ

  equiv-is-structurally-small-∞-Groupᵉ :
    type-∞-Groupᵉ Gᵉ ≃ᵉ type-∞-group-is-structurally-small-∞-Groupᵉ
  equiv-is-structurally-small-∞-Groupᵉ =
    equiv-equiv-∞-Groupᵉ Gᵉ
      ( ∞-group-is-structurally-small-∞-Groupᵉ)
      ( equiv-∞-group-is-structurally-small-∞-Groupᵉ)
```

### The predicate of being a pointed small ∞-group

```agda
module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ)
  where

  is-pointed-small-prop-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-pointed-small-prop-∞-Groupᵉ =
    is-pointed-small-prop-Pointed-Typeᵉ l2ᵉ (classifying-pointed-type-∞-Groupᵉ Gᵉ)

  is-pointed-small-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-pointed-small-∞-Groupᵉ =
    is-pointed-small-Pointed-Typeᵉ l2ᵉ (classifying-pointed-type-∞-Groupᵉ Gᵉ)

  is-prop-is-pointed-small-∞-Groupᵉ : is-propᵉ is-pointed-small-∞-Groupᵉ
  is-prop-is-pointed-small-∞-Groupᵉ =
    is-prop-is-pointed-small-Pointed-Typeᵉ (classifying-pointed-type-∞-Groupᵉ Gᵉ)
```

## Properties

### The classifying type of any small ∞-group is locally small

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ)
  where

  abstract
    is-locally-small-classifying-type-is-small-∞-Group'ᵉ :
      (xᵉ yᵉ : classifying-type-∞-Groupᵉ Gᵉ) →
      shape-∞-Groupᵉ Gᵉ ＝ᵉ xᵉ → shape-∞-Groupᵉ Gᵉ ＝ᵉ yᵉ →
      is-smallᵉ l2ᵉ (xᵉ ＝ᵉ yᵉ)
    is-locally-small-classifying-type-is-small-∞-Group'ᵉ ._ ._ reflᵉ reflᵉ = Hᵉ

  abstract
    is-locally-small-classifying-type-is-small-∞-Groupᵉ :
      is-locally-smallᵉ l2ᵉ (classifying-type-∞-Groupᵉ Gᵉ)
    is-locally-small-classifying-type-is-small-∞-Groupᵉ xᵉ yᵉ =
      apply-twice-universal-property-trunc-Propᵉ
        ( mere-eq-classifying-type-∞-Groupᵉ Gᵉ (shape-∞-Groupᵉ Gᵉ) xᵉ)
        ( mere-eq-classifying-type-∞-Groupᵉ Gᵉ (shape-∞-Groupᵉ Gᵉ) yᵉ)
        ( is-small-Propᵉ l2ᵉ (xᵉ ＝ᵉ yᵉ))
        ( is-locally-small-classifying-type-is-small-∞-Group'ᵉ xᵉ yᵉ)
```

### An ∞-group is small if and only if its classifying type is small

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ)
  where

  abstract
    is-small-classifying-type-is-small-∞-Groupᵉ :
      is-small-∞-Groupᵉ l2ᵉ Gᵉ → is-smallᵉ l2ᵉ (classifying-type-∞-Groupᵉ Gᵉ)
    is-small-classifying-type-is-small-∞-Groupᵉ Hᵉ =
      is-small-equiv'ᵉ
        ( imᵉ (point-∞-Groupᵉ Gᵉ))
        ( compute-im-point-∞-Groupᵉ Gᵉ)
        ( replacementᵉ
          ( point-∞-Groupᵉ Gᵉ)
          ( is-small-unitᵉ)
          ( is-locally-small-classifying-type-is-small-∞-Groupᵉ Gᵉ Hᵉ))

  abstract
    is-small-is-small-classifying-type-∞-Groupᵉ :
      is-smallᵉ l2ᵉ (classifying-type-∞-Groupᵉ Gᵉ) → is-small-∞-Groupᵉ l2ᵉ Gᵉ
    is-small-is-small-classifying-type-∞-Groupᵉ Hᵉ =
      is-locally-small-is-smallᵉ Hᵉ (shape-∞-Groupᵉ Gᵉ) (shape-∞-Groupᵉ Gᵉ)
```

### An ∞-group is small if and only if it is pointed small

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ)
  where

  abstract
    is-pointed-small-is-small-∞-Groupᵉ :
      is-small-∞-Groupᵉ l2ᵉ Gᵉ → is-pointed-small-∞-Groupᵉ l2ᵉ Gᵉ
    is-pointed-small-is-small-∞-Groupᵉ Hᵉ =
      is-pointed-small-is-small-Pointed-Typeᵉ
        ( classifying-pointed-type-∞-Groupᵉ Gᵉ)
        ( is-small-classifying-type-is-small-∞-Groupᵉ Gᵉ Hᵉ)
```

### An ∞-group is small if and only if it is structurally small

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ)
  where

  classifying-pointed-type-is-small-∞-Groupᵉ :
    is-small-∞-Groupᵉ l2ᵉ Gᵉ → Pointed-Typeᵉ l2ᵉ
  classifying-pointed-type-is-small-∞-Groupᵉ Hᵉ =
    pointed-type-is-pointed-small-Pointed-Typeᵉ
      ( classifying-pointed-type-∞-Groupᵉ Gᵉ)
      ( is-pointed-small-is-small-∞-Groupᵉ Gᵉ Hᵉ)

  classifying-type-is-small-∞-Groupᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ → UUᵉ l2ᵉ
  classifying-type-is-small-∞-Groupᵉ Hᵉ =
    type-is-pointed-small-Pointed-Typeᵉ
      ( classifying-pointed-type-∞-Groupᵉ Gᵉ)
      ( is-pointed-small-is-small-∞-Groupᵉ Gᵉ Hᵉ)

  abstract
    is-0-connected-classifying-type-is-small-∞-Groupᵉ :
      (Hᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ) →
      is-0-connectedᵉ (classifying-type-is-small-∞-Groupᵉ Hᵉ)
    is-0-connected-classifying-type-is-small-∞-Groupᵉ Hᵉ =
      is-0-connected-equiv'ᵉ
        ( equiv-is-pointed-small-Pointed-Typeᵉ
          ( classifying-pointed-type-∞-Groupᵉ Gᵉ)
          ( is-pointed-small-is-small-∞-Groupᵉ Gᵉ Hᵉ))
        ( is-0-connected-classifying-type-∞-Groupᵉ Gᵉ)

  ∞-group-is-small-∞-Groupᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ → ∞-Groupᵉ l2ᵉ
  pr1ᵉ (∞-group-is-small-∞-Groupᵉ Hᵉ) =
    classifying-pointed-type-is-small-∞-Groupᵉ Hᵉ
  pr2ᵉ (∞-group-is-small-∞-Groupᵉ Hᵉ) =
    is-0-connected-classifying-type-is-small-∞-Groupᵉ Hᵉ

  pointed-type-∞-group-is-small-∞-Groupᵉ :
    is-small-∞-Groupᵉ l2ᵉ Gᵉ → Pointed-Typeᵉ l2ᵉ
  pointed-type-∞-group-is-small-∞-Groupᵉ Hᵉ =
    pointed-type-∞-Groupᵉ (∞-group-is-small-∞-Groupᵉ Hᵉ)

  type-∞-group-is-small-∞-Groupᵉ :
    is-small-∞-Groupᵉ l2ᵉ Gᵉ → UUᵉ l2ᵉ
  type-∞-group-is-small-∞-Groupᵉ Hᵉ =
    type-∞-Groupᵉ (∞-group-is-small-∞-Groupᵉ Hᵉ)

  equiv-∞-group-is-small-∞-Groupᵉ :
    (Hᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ) → equiv-∞-Groupᵉ Gᵉ (∞-group-is-small-∞-Groupᵉ Hᵉ)
  equiv-∞-group-is-small-∞-Groupᵉ Hᵉ =
    pointed-equiv-is-pointed-small-Pointed-Typeᵉ
      ( classifying-pointed-type-∞-Groupᵉ Gᵉ)
      ( is-pointed-small-is-small-∞-Groupᵉ Gᵉ Hᵉ)

  pointed-equiv-equiv-∞-group-is-small-∞-Groupᵉ :
    (Hᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ) →
    pointed-type-∞-Groupᵉ Gᵉ ≃∗ᵉ pointed-type-∞-group-is-small-∞-Groupᵉ Hᵉ
  pointed-equiv-equiv-∞-group-is-small-∞-Groupᵉ Hᵉ =
    pointed-equiv-equiv-∞-Groupᵉ Gᵉ
      ( ∞-group-is-small-∞-Groupᵉ Hᵉ)
      ( equiv-∞-group-is-small-∞-Groupᵉ Hᵉ)

  equiv-equiv-∞-group-is-small-∞-Groupᵉ :
    (Hᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ) →
    type-∞-Groupᵉ Gᵉ ≃ᵉ type-∞-group-is-small-∞-Groupᵉ Hᵉ
  equiv-equiv-∞-group-is-small-∞-Groupᵉ Hᵉ =
    equiv-equiv-∞-Groupᵉ Gᵉ
      ( ∞-group-is-small-∞-Groupᵉ Hᵉ)
      ( equiv-∞-group-is-small-∞-Groupᵉ Hᵉ)

  abstract
    is-structurally-small-is-small-∞-Groupᵉ :
      is-small-∞-Groupᵉ l2ᵉ Gᵉ → is-structurally-small-∞-Groupᵉ l2ᵉ Gᵉ
    pr1ᵉ (is-structurally-small-is-small-∞-Groupᵉ Hᵉ) =
      ∞-group-is-small-∞-Groupᵉ Hᵉ
    pr2ᵉ (is-structurally-small-is-small-∞-Groupᵉ Hᵉ) =
      equiv-∞-group-is-small-∞-Groupᵉ Hᵉ

  abstract
    is-small-is-structurally-small-∞-Groupᵉ :
      is-structurally-small-∞-Groupᵉ l2ᵉ Gᵉ → is-small-∞-Groupᵉ l2ᵉ Gᵉ
    pr1ᵉ (is-small-is-structurally-small-∞-Groupᵉ Hᵉ) =
      type-∞-group-is-structurally-small-∞-Groupᵉ Gᵉ Hᵉ
    pr2ᵉ (is-small-is-structurally-small-∞-Groupᵉ Hᵉ) =
      equiv-is-structurally-small-∞-Groupᵉ Gᵉ Hᵉ

  abstract
    is-small-∞-group-is-small-∞-Groupᵉ :
      (Hᵉ : is-small-∞-Groupᵉ l2ᵉ Gᵉ) →
      is-small-∞-Groupᵉ l1ᵉ (∞-group-is-small-∞-Groupᵉ Hᵉ)
    pr1ᵉ (is-small-∞-group-is-small-∞-Groupᵉ Hᵉ) = type-∞-Groupᵉ Gᵉ
    pr2ᵉ (is-small-∞-group-is-small-∞-Groupᵉ Hᵉ) =
      inv-equivᵉ (equiv-equiv-∞-group-is-small-∞-Groupᵉ Hᵉ)
```