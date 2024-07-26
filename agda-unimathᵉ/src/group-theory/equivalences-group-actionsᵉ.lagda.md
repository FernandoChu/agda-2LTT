# Equivalences of group actions

```agda
module group-theory.equivalences-group-actionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.subtype-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import group-theory.group-actionsᵉ
open import group-theory.groupsᵉ
open import group-theory.homomorphisms-group-actionsᵉ
open import group-theory.homomorphisms-groupsᵉ
open import group-theory.symmetric-groupsᵉ
```

</details>

## Idea

Aᵉ [morphismᵉ ofᵉ `G`-sets](group-theory.group-actions.mdᵉ) isᵉ saidᵉ to beᵉ anᵉ
**equivalence**ᵉ ifᵉ itsᵉ underlyingᵉ mapᵉ isᵉ anᵉ
[equivalence](foundation-core.equivalences.md).ᵉ

## Definitions

### The predicate of being an equivalence of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  is-equiv-hom-action-Groupᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  is-equiv-hom-action-Groupᵉ fᵉ = is-equivᵉ (map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
```

### The type of equivalences of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  equiv-action-Groupᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-action-Groupᵉ =
    Σᵉ ( type-action-Groupᵉ Gᵉ Xᵉ ≃ᵉ type-action-Groupᵉ Gᵉ Yᵉ)
      ( λ eᵉ →
        ( gᵉ : type-Groupᵉ Gᵉ) →
        coherence-square-mapsᵉ
          ( map-equivᵉ eᵉ)
          ( mul-action-Groupᵉ Gᵉ Xᵉ gᵉ)
          ( mul-action-Groupᵉ Gᵉ Yᵉ gᵉ)
          ( map-equivᵉ eᵉ))

  equiv-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ → type-action-Groupᵉ Gᵉ Xᵉ ≃ᵉ type-action-Groupᵉ Gᵉ Yᵉ
  equiv-equiv-action-Groupᵉ = pr1ᵉ

  map-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ → type-action-Groupᵉ Gᵉ Xᵉ → type-action-Groupᵉ Gᵉ Yᵉ
  map-equiv-action-Groupᵉ eᵉ =
    map-equivᵉ (equiv-equiv-action-Groupᵉ eᵉ)

  is-equiv-map-equiv-action-Groupᵉ :
    (eᵉ : equiv-action-Groupᵉ) → is-equivᵉ (map-equiv-action-Groupᵉ eᵉ)
  is-equiv-map-equiv-action-Groupᵉ eᵉ =
    is-equiv-map-equivᵉ (equiv-equiv-action-Groupᵉ eᵉ)

  coherence-square-equiv-action-Groupᵉ :
    (eᵉ : equiv-action-Groupᵉ) (gᵉ : type-Groupᵉ Gᵉ) →
    coherence-square-mapsᵉ
      ( map-equiv-action-Groupᵉ eᵉ)
      ( mul-action-Groupᵉ Gᵉ Xᵉ gᵉ)
      ( mul-action-Groupᵉ Gᵉ Yᵉ gᵉ)
      ( map-equiv-action-Groupᵉ eᵉ)
  coherence-square-equiv-action-Groupᵉ = pr2ᵉ

  hom-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ → hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  pr1ᵉ (hom-equiv-action-Groupᵉ eᵉ) = map-equiv-action-Groupᵉ eᵉ
  pr2ᵉ (hom-equiv-action-Groupᵉ eᵉ) = coherence-square-equiv-action-Groupᵉ eᵉ

  is-equiv-hom-equiv-action-Groupᵉ :
    (eᵉ : equiv-action-Groupᵉ) →
    is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ (hom-equiv-action-Groupᵉ eᵉ)
  is-equiv-hom-equiv-action-Groupᵉ =
    is-equiv-map-equiv-action-Groupᵉ

  equiv-is-equiv-hom-action-Groupᵉ :
    (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ →
    equiv-action-Groupᵉ
  pr1ᵉ (pr1ᵉ (equiv-is-equiv-hom-action-Groupᵉ fᵉ is-equiv-fᵉ)) =
    map-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ
  pr2ᵉ (pr1ᵉ (equiv-is-equiv-hom-action-Groupᵉ fᵉ is-equiv-fᵉ)) = is-equiv-fᵉ
  pr2ᵉ (equiv-is-equiv-hom-action-Groupᵉ fᵉ is-equiv-fᵉ) =
    preserves-action-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ
```

### Equality of equivalences of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (eᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
  where

  htpy-equiv-action-Groupᵉ : (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → UUᵉ (l2ᵉ ⊔ l3ᵉ)
  htpy-equiv-action-Groupᵉ fᵉ =
    htpy-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( hom-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ)
      ( hom-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)

  refl-htpy-equiv-action-Groupᵉ : htpy-equiv-action-Groupᵉ eᵉ
  refl-htpy-equiv-action-Groupᵉ =
    refl-htpy-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ (hom-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ)

  htpy-eq-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → eᵉ ＝ᵉ fᵉ → htpy-equiv-action-Groupᵉ fᵉ
  htpy-eq-equiv-action-Groupᵉ .eᵉ reflᵉ = refl-htpy-equiv-action-Groupᵉ

  is-torsorial-htpy-equiv-action-Groupᵉ : is-torsorialᵉ htpy-equiv-action-Groupᵉ
  is-torsorial-htpy-equiv-action-Groupᵉ =
    is-contr-equivᵉ
      ( Σᵉ ( Σᵉ ( hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) (λ fᵉ → is-equivᵉ (pr1ᵉ fᵉ)))
          ( λ fᵉ →
            htpy-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
              ( hom-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ)
              ( pr1ᵉ fᵉ)))
      ( equiv-Σᵉ
        ( λ fᵉ →
          htpy-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
            ( hom-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ)
            ( pr1ᵉ fᵉ))
        ( equiv-right-swap-Σᵉ)
        ( λ ((fᵉ ,ᵉ Eᵉ) ,ᵉ Hᵉ) → id-equivᵉ))
      ( is-torsorial-Eq-subtypeᵉ
        ( is-torsorial-htpy-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ
          ( hom-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ))
        ( λ fᵉ → is-property-is-equivᵉ (pr1ᵉ fᵉ))
        ( hom-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ)
        ( refl-htpyᵉ)
        ( is-equiv-map-equivᵉ (pr1ᵉ eᵉ)))

  is-equiv-htpy-eq-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → is-equivᵉ (htpy-eq-equiv-action-Groupᵉ fᵉ)
  is-equiv-htpy-eq-equiv-action-Groupᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-equiv-action-Groupᵉ
      htpy-eq-equiv-action-Groupᵉ

  extensionality-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-action-Groupᵉ fᵉ
  pr1ᵉ (extensionality-equiv-action-Groupᵉ fᵉ) =
    htpy-eq-equiv-action-Groupᵉ fᵉ
  pr2ᵉ (extensionality-equiv-action-Groupᵉ fᵉ) =
    is-equiv-htpy-eq-equiv-action-Groupᵉ fᵉ

  eq-htpy-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) → htpy-equiv-action-Groupᵉ fᵉ → eᵉ ＝ᵉ fᵉ
  eq-htpy-equiv-action-Groupᵉ fᵉ =
    map-inv-is-equivᵉ (is-equiv-htpy-eq-equiv-action-Groupᵉ fᵉ)
```

### The inverse equivalence of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  map-inv-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ → type-action-Groupᵉ Gᵉ Yᵉ → type-action-Groupᵉ Gᵉ Xᵉ
  map-inv-equiv-action-Groupᵉ eᵉ =
    map-inv-equivᵉ (equiv-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ eᵉ)

  preserves-action-map-inv-equiv-action-Groupᵉ :
    (eᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    preserves-action-Groupᵉ Gᵉ Yᵉ Xᵉ (map-inv-equiv-action-Groupᵉ eᵉ)
  preserves-action-map-inv-equiv-action-Groupᵉ (eᵉ ,ᵉ Hᵉ) gᵉ =
    horizontal-inv-equiv-coherence-square-mapsᵉ
      ( eᵉ)
      ( mul-action-Groupᵉ Gᵉ Xᵉ gᵉ)
      ( mul-action-Groupᵉ Gᵉ Yᵉ gᵉ)
      ( eᵉ)
      ( Hᵉ gᵉ)

  inv-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ → equiv-action-Groupᵉ Gᵉ Yᵉ Xᵉ
  pr1ᵉ (inv-equiv-action-Groupᵉ (eᵉ ,ᵉ Hᵉ)) = inv-equivᵉ eᵉ
  pr2ᵉ (inv-equiv-action-Groupᵉ eᵉ) =
    preserves-action-map-inv-equiv-action-Groupᵉ eᵉ

  hom-inv-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ → hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ
  hom-inv-equiv-action-Groupᵉ eᵉ =
    hom-equiv-action-Groupᵉ Gᵉ Yᵉ Xᵉ (inv-equiv-action-Groupᵉ eᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (fᵉ : hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ) (is-equiv-fᵉ : is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ)
  where

  map-inv-is-equiv-hom-action-Groupᵉ :
    type-action-Groupᵉ Gᵉ Yᵉ → type-action-Groupᵉ Gᵉ Xᵉ
  map-inv-is-equiv-hom-action-Groupᵉ =
    map-inv-is-equivᵉ is-equiv-fᵉ

  preserves-action-map-inv-is-equiv-hom-action-Groupᵉ :
    preserves-action-Groupᵉ Gᵉ Yᵉ Xᵉ (map-inv-is-equiv-hom-action-Groupᵉ)
  preserves-action-map-inv-is-equiv-hom-action-Groupᵉ =
    preserves-action-map-inv-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( equiv-is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-equiv-fᵉ)

  hom-inv-is-equiv-hom-action-Groupᵉ : hom-action-Groupᵉ Gᵉ Yᵉ Xᵉ
  hom-inv-is-equiv-hom-action-Groupᵉ =
    hom-inv-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( equiv-is-equiv-hom-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ is-equiv-fᵉ)
```

### The composite of equivalences of group actions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ) (Zᵉ : action-Groupᵉ Gᵉ l4ᵉ)
  where

  comp-equiv-action-Groupᵉ :
    equiv-action-Groupᵉ Gᵉ Yᵉ Zᵉ → equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ →
    equiv-action-Groupᵉ Gᵉ Xᵉ Zᵉ
  pr1ᵉ (comp-equiv-action-Groupᵉ (fᵉ ,ᵉ Kᵉ) (eᵉ ,ᵉ Hᵉ)) = fᵉ ∘eᵉ eᵉ
  pr2ᵉ (comp-equiv-action-Groupᵉ (fᵉ ,ᵉ Kᵉ) (eᵉ ,ᵉ Hᵉ)) gᵉ =
    pasting-horizontal-coherence-square-mapsᵉ
      ( map-equivᵉ eᵉ)
      ( map-equivᵉ fᵉ)
      ( mul-action-Groupᵉ Gᵉ Xᵉ gᵉ)
      ( mul-action-Groupᵉ Gᵉ Yᵉ gᵉ)
      ( mul-action-Groupᵉ Gᵉ Zᵉ gᵉ)
      ( map-equivᵉ eᵉ)
      ( map-equivᵉ fᵉ)
      ( Hᵉ gᵉ)
      ( Kᵉ gᵉ)
```

### The identity equivalence on group actions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  id-equiv-action-Groupᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-action-Groupᵉ = id-equivᵉ
  pr2ᵉ id-equiv-action-Groupᵉ gᵉ = refl-htpyᵉ
```

## Properties

### Equivalences of group actions characterize equality of group actions

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ) (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ)
  where

  equiv-eq-action-Groupᵉ :
    (Yᵉ : action-Groupᵉ Gᵉ l2ᵉ) → Xᵉ ＝ᵉ Yᵉ → equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  equiv-eq-action-Groupᵉ .Xᵉ reflᵉ = id-equiv-action-Groupᵉ Gᵉ Xᵉ

  abstract
    is-torsorial-equiv-action-Groupᵉ :
      is-torsorialᵉ (λ (Yᵉ : action-Groupᵉ Gᵉ l2ᵉ) → equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ)
    is-torsorial-equiv-action-Groupᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-equiv-Setᵉ (pr1ᵉ Xᵉ))
        ( pr1ᵉ Xᵉ ,ᵉ id-equivᵉ)
        ( is-contr-equivᵉ
          ( Σᵉ ( hom-Groupᵉ Gᵉ (symmetric-Groupᵉ (pr1ᵉ Xᵉ)))
              ( htpy-hom-Groupᵉ Gᵉ (symmetric-Groupᵉ (pr1ᵉ Xᵉ)) (pr2ᵉ Xᵉ)))
          ( equiv-totᵉ
            ( λ fᵉ →
              equiv-Π-equiv-familyᵉ
                ( λ gᵉ →
                  inv-equivᵉ
                    ( extensionality-equivᵉ
                      ( map-hom-Groupᵉ Gᵉ (symmetric-Groupᵉ (pr1ᵉ Xᵉ)) (pr2ᵉ Xᵉ) gᵉ)
                      ( map-hom-Groupᵉ Gᵉ (symmetric-Groupᵉ (pr1ᵉ Xᵉ)) fᵉ gᵉ)))))
          ( is-torsorial-htpy-hom-Groupᵉ Gᵉ
            ( symmetric-Groupᵉ (pr1ᵉ Xᵉ))
            ( pr2ᵉ Xᵉ)))

  abstract
    is-equiv-equiv-eq-action-Groupᵉ :
      (Yᵉ : action-Groupᵉ Gᵉ l2ᵉ) → is-equivᵉ (equiv-eq-action-Groupᵉ Yᵉ)
    is-equiv-equiv-eq-action-Groupᵉ =
      fundamental-theorem-idᵉ
        is-torsorial-equiv-action-Groupᵉ
        equiv-eq-action-Groupᵉ

  eq-equiv-action-Groupᵉ :
    (Yᵉ : action-Groupᵉ Gᵉ l2ᵉ) → equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ → Xᵉ ＝ᵉ Yᵉ
  eq-equiv-action-Groupᵉ Yᵉ =
    map-inv-is-equivᵉ (is-equiv-equiv-eq-action-Groupᵉ Yᵉ)

  extensionality-action-Groupᵉ :
    (Yᵉ : action-Groupᵉ Gᵉ l2ᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-action-Groupᵉ Yᵉ) =
    equiv-eq-action-Groupᵉ Yᵉ
  pr2ᵉ (extensionality-action-Groupᵉ Yᵉ) =
    is-equiv-equiv-eq-action-Groupᵉ Yᵉ
```

### Composition of equivalences of group actions is associative

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (X1ᵉ : action-Groupᵉ Gᵉ l2ᵉ) (X2ᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  (X3ᵉ : action-Groupᵉ Gᵉ l4ᵉ) (X4ᵉ : action-Groupᵉ Gᵉ l5ᵉ)
  where

  associative-comp-equiv-action-Groupᵉ :
    (hᵉ : equiv-action-Groupᵉ Gᵉ X3ᵉ X4ᵉ)
    (gᵉ : equiv-action-Groupᵉ Gᵉ X2ᵉ X3ᵉ)
    (fᵉ : equiv-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ) →
    comp-equiv-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X4ᵉ
      ( comp-equiv-action-Groupᵉ Gᵉ X2ᵉ X3ᵉ X4ᵉ hᵉ gᵉ)
      ( fᵉ) ＝ᵉ
    comp-equiv-action-Groupᵉ Gᵉ X1ᵉ X3ᵉ X4ᵉ hᵉ
      ( comp-equiv-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X3ᵉ gᵉ fᵉ)
  associative-comp-equiv-action-Groupᵉ hᵉ gᵉ fᵉ =
    eq-htpy-equiv-action-Groupᵉ Gᵉ X1ᵉ X4ᵉ
      ( comp-equiv-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X4ᵉ
        ( comp-equiv-action-Groupᵉ Gᵉ X2ᵉ X3ᵉ X4ᵉ hᵉ gᵉ)
        ( fᵉ))
      ( comp-equiv-action-Groupᵉ Gᵉ X1ᵉ X3ᵉ X4ᵉ hᵉ
        ( comp-equiv-action-Groupᵉ Gᵉ X1ᵉ X2ᵉ X3ᵉ gᵉ fᵉ))
      ( refl-htpyᵉ)
```

### The identity equivalence on group actions is a unit of composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Gᵉ : Groupᵉ l1ᵉ)
  (Xᵉ : action-Groupᵉ Gᵉ l2ᵉ) (Yᵉ : action-Groupᵉ Gᵉ l3ᵉ)
  where

  left-unit-law-comp-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    comp-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ Yᵉ (id-equiv-action-Groupᵉ Gᵉ Yᵉ) fᵉ ＝ᵉ fᵉ
  left-unit-law-comp-equiv-action-Groupᵉ fᵉ =
    eq-htpy-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( comp-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ Yᵉ (id-equiv-action-Groupᵉ Gᵉ Yᵉ) fᵉ)
      ( fᵉ)
      ( refl-htpyᵉ)

  right-unit-law-comp-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    comp-equiv-action-Groupᵉ Gᵉ Xᵉ Xᵉ Yᵉ fᵉ (id-equiv-action-Groupᵉ Gᵉ Xᵉ) ＝ᵉ fᵉ
  right-unit-law-comp-equiv-action-Groupᵉ fᵉ =
    eq-htpy-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ
      ( comp-equiv-action-Groupᵉ Gᵉ Xᵉ Xᵉ Yᵉ fᵉ (id-equiv-action-Groupᵉ Gᵉ Xᵉ))
      ( fᵉ)
      ( refl-htpyᵉ)

  left-inverse-law-comp-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    comp-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ Xᵉ (inv-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ) fᵉ ＝ᵉ
    id-equiv-action-Groupᵉ Gᵉ Xᵉ
  left-inverse-law-comp-equiv-action-Groupᵉ fᵉ =
    eq-htpy-equiv-action-Groupᵉ Gᵉ Xᵉ Xᵉ
      ( comp-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ Xᵉ (inv-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ) fᵉ)
      ( id-equiv-action-Groupᵉ Gᵉ Xᵉ)
      ( is-retraction-map-inv-equivᵉ (pr1ᵉ fᵉ))

  right-inverse-law-comp-equiv-action-Groupᵉ :
    (fᵉ : equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ) →
    comp-equiv-action-Groupᵉ Gᵉ Yᵉ Xᵉ Yᵉ fᵉ (inv-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ) ＝ᵉ
    id-equiv-action-Groupᵉ Gᵉ Yᵉ
  right-inverse-law-comp-equiv-action-Groupᵉ fᵉ =
    eq-htpy-equiv-action-Groupᵉ Gᵉ Yᵉ Yᵉ
      ( comp-equiv-action-Groupᵉ Gᵉ Yᵉ Xᵉ Yᵉ fᵉ (inv-equiv-action-Groupᵉ Gᵉ Xᵉ Yᵉ fᵉ))
      ( id-equiv-action-Groupᵉ Gᵉ Yᵉ)
      ( is-section-map-inv-equivᵉ (pr1ᵉ fᵉ))
```

## See also

-ᵉ [Isomorphismsᵉ ofᵉ groupᵉ actions](group-theory.isomorphisms-group-actions.mdᵉ)