# Factorizations of maps

```agda
module orthogonal-factorization-systems.factorizations-of-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-algebraᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.retracts-of-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
```

</details>

## Idea

Aᵉ **factorization**ᵉ ofᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`ᵉ isᵉ aᵉ pairᵉ ofᵉ mapsᵉ `gᵉ : Xᵉ → B`ᵉ andᵉ
`hᵉ : Aᵉ → X`ᵉ suchᵉ thatᵉ theirᵉ compositeᵉ `gᵉ ∘ᵉ h`ᵉ isᵉ `f`.ᵉ

```text
       Xᵉ
      ∧ᵉ \ᵉ
   hᵉ /ᵉ   \ᵉ gᵉ
    /ᵉ     ∨ᵉ
  Aᵉ ----->ᵉ Bᵉ
      fᵉ
```

Weᵉ useᵉ diagrammaticᵉ orderᵉ andᵉ sayᵉ theᵉ mapᵉ `h`ᵉ isᵉ theᵉ _leftᵉ_ andᵉ `g`ᵉ theᵉ _rightᵉ_
mapᵉ ofᵉ theᵉ factorization.ᵉ

## Definitions

### The predicate on triangles of maps of being a factorization

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  is-factorizationᵉ :
    {l3ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} →
    (gᵉ : Xᵉ → Bᵉ) (hᵉ : Aᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-factorizationᵉ gᵉ hᵉ = gᵉ ∘ᵉ hᵉ ~ᵉ fᵉ
```

### The type of factorizations of a map through a specified image/type

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  factorization-throughᵉ : (fᵉ : Aᵉ → Bᵉ) (Xᵉ : UUᵉ l3ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  factorization-throughᵉ fᵉ Xᵉ =
    Σᵉ ( Xᵉ → Bᵉ)
      ( λ gᵉ →
        Σᵉ ( Aᵉ → Xᵉ)
          ( is-factorizationᵉ fᵉ gᵉ))

  right-map-factorization-throughᵉ :
    {fᵉ : Aᵉ → Bᵉ} {Xᵉ : UUᵉ l3ᵉ} → factorization-throughᵉ fᵉ Xᵉ → Xᵉ → Bᵉ
  right-map-factorization-throughᵉ = pr1ᵉ

  left-map-factorization-throughᵉ :
    {fᵉ : Aᵉ → Bᵉ} {Xᵉ : UUᵉ l3ᵉ} → factorization-throughᵉ fᵉ Xᵉ → Aᵉ → Xᵉ
  left-map-factorization-throughᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  is-factorization-factorization-throughᵉ :
    {fᵉ : Aᵉ → Bᵉ} {Xᵉ : UUᵉ l3ᵉ}
    (Fᵉ : factorization-throughᵉ fᵉ Xᵉ) →
      is-factorizationᵉ fᵉ
        ( right-map-factorization-throughᵉ Fᵉ)
        ( left-map-factorization-throughᵉ Fᵉ)
  is-factorization-factorization-throughᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```

### The type of factorizations of a map through images in a universe

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  factorizationᵉ : (l3ᵉ : Level) (fᵉ : Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ lsuc l3ᵉ)
  factorizationᵉ l3ᵉ fᵉ = Σᵉ (UUᵉ l3ᵉ) (factorization-throughᵉ fᵉ)

  image-factorizationᵉ : {l3ᵉ : Level} {fᵉ : Aᵉ → Bᵉ} → factorizationᵉ l3ᵉ fᵉ → UUᵉ l3ᵉ
  image-factorizationᵉ = pr1ᵉ

  factorization-through-factorizationᵉ :
    {l3ᵉ : Level} {fᵉ : Aᵉ → Bᵉ} (Fᵉ : factorizationᵉ l3ᵉ fᵉ) →
    factorization-throughᵉ fᵉ (image-factorizationᵉ Fᵉ)
  factorization-through-factorizationᵉ = pr2ᵉ

  right-map-factorizationᵉ :
    {l3ᵉ : Level} {fᵉ : Aᵉ → Bᵉ} (Fᵉ : factorizationᵉ l3ᵉ fᵉ) →
    image-factorizationᵉ Fᵉ → Bᵉ
  right-map-factorizationᵉ Fᵉ =
    right-map-factorization-throughᵉ (factorization-through-factorizationᵉ Fᵉ)

  left-map-factorizationᵉ :
    {l3ᵉ : Level} {fᵉ : Aᵉ → Bᵉ} (Fᵉ : factorizationᵉ l3ᵉ fᵉ) →
    Aᵉ → image-factorizationᵉ Fᵉ
  left-map-factorizationᵉ Fᵉ =
    left-map-factorization-throughᵉ (factorization-through-factorizationᵉ Fᵉ)

  is-factorization-factorizationᵉ :
    {l3ᵉ : Level} {fᵉ : Aᵉ → Bᵉ} (Fᵉ : factorizationᵉ l3ᵉ fᵉ) →
    is-factorizationᵉ fᵉ (right-map-factorizationᵉ Fᵉ) (left-map-factorizationᵉ Fᵉ)
  is-factorization-factorizationᵉ Fᵉ =
    is-factorization-factorization-throughᵉ
      ( factorization-through-factorizationᵉ Fᵉ)
```

## Properties

### Whiskering of factorizations by retracts

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  whisker-image-factorization-throughᵉ :
    {l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} →
    Xᵉ retract-ofᵉ Yᵉ → factorization-throughᵉ fᵉ Xᵉ → factorization-throughᵉ fᵉ Yᵉ
  pr1ᵉ (whisker-image-factorization-throughᵉ (sᵉ ,ᵉ rᵉ ,ᵉ hᵉ) (frᵉ ,ᵉ flᵉ ,ᵉ fHᵉ)) =
    frᵉ ∘ᵉ rᵉ
  pr1ᵉ (pr2ᵉ (whisker-image-factorization-throughᵉ (sᵉ ,ᵉ rᵉ ,ᵉ hᵉ) (frᵉ ,ᵉ flᵉ ,ᵉ fHᵉ))) =
    sᵉ ∘ᵉ flᵉ
  pr2ᵉ (pr2ᵉ (whisker-image-factorization-throughᵉ (sᵉ ,ᵉ rᵉ ,ᵉ hᵉ) (frᵉ ,ᵉ flᵉ ,ᵉ fHᵉ))) =
    (frᵉ ·lᵉ (hᵉ ·rᵉ flᵉ)) ∙hᵉ fHᵉ
```

### Characterization of identifications of factorizations through a type

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  {Xᵉ : UUᵉ l3ᵉ}
  where

  coherence-htpy-factorization-throughᵉ :
    (Fᵉ Eᵉ : factorization-throughᵉ fᵉ Xᵉ) →
    right-map-factorization-throughᵉ Fᵉ ~ᵉ right-map-factorization-throughᵉ Eᵉ →
    left-map-factorization-throughᵉ Fᵉ ~ᵉ left-map-factorization-throughᵉ Eᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ)
  coherence-htpy-factorization-throughᵉ Fᵉ Eᵉ Rᵉ Lᵉ =
    ( is-factorization-factorization-throughᵉ Fᵉ) ~ᵉ
    ( horizontal-concat-htpyᵉ Rᵉ Lᵉ ∙hᵉ is-factorization-factorization-throughᵉ Eᵉ)

  htpy-factorization-throughᵉ :
    (Fᵉ Eᵉ : factorization-throughᵉ fᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-factorization-throughᵉ Fᵉ Eᵉ =
    Σᵉ ( right-map-factorization-throughᵉ Fᵉ ~ᵉ
        right-map-factorization-throughᵉ Eᵉ)
      ( λ Rᵉ →
        Σᵉ ( left-map-factorization-throughᵉ Fᵉ ~ᵉ
            left-map-factorization-throughᵉ Eᵉ)
          ( coherence-htpy-factorization-throughᵉ Fᵉ Eᵉ Rᵉ))

  refl-htpy-factorization-throughᵉ :
    (Fᵉ : factorization-throughᵉ fᵉ Xᵉ) → htpy-factorization-throughᵉ Fᵉ Fᵉ
  pr1ᵉ (refl-htpy-factorization-throughᵉ Fᵉ) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-htpy-factorization-throughᵉ Fᵉ)) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (refl-htpy-factorization-throughᵉ Fᵉ)) = refl-htpyᵉ

  htpy-eq-factorization-throughᵉ :
    (Fᵉ Eᵉ : factorization-throughᵉ fᵉ Xᵉ) →
    Fᵉ ＝ᵉ Eᵉ → htpy-factorization-throughᵉ Fᵉ Eᵉ
  htpy-eq-factorization-throughᵉ Fᵉ .Fᵉ reflᵉ = refl-htpy-factorization-throughᵉ Fᵉ

  is-torsorial-htpy-factorization-throughᵉ :
    (Fᵉ : factorization-throughᵉ fᵉ Xᵉ) →
    is-torsorialᵉ (htpy-factorization-throughᵉ Fᵉ)
  is-torsorial-htpy-factorization-throughᵉ Fᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (right-map-factorization-throughᵉ Fᵉ))
      ( right-map-factorization-throughᵉ Fᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (left-map-factorization-throughᵉ Fᵉ))
        ( left-map-factorization-throughᵉ Fᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ (is-factorization-factorization-throughᵉ Fᵉ)))

  is-equiv-htpy-eq-factorization-throughᵉ :
    (Fᵉ Eᵉ : factorization-throughᵉ fᵉ Xᵉ) →
    is-equivᵉ (htpy-eq-factorization-throughᵉ Fᵉ Eᵉ)
  is-equiv-htpy-eq-factorization-throughᵉ Fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-factorization-throughᵉ Fᵉ)
      ( htpy-eq-factorization-throughᵉ Fᵉ)

  extensionality-factorization-throughᵉ :
    (Fᵉ Eᵉ : factorization-throughᵉ fᵉ Xᵉ) →
    (Fᵉ ＝ᵉ Eᵉ) ≃ᵉ (htpy-factorization-throughᵉ Fᵉ Eᵉ)
  pr1ᵉ (extensionality-factorization-throughᵉ Fᵉ Eᵉ) =
    htpy-eq-factorization-throughᵉ Fᵉ Eᵉ
  pr2ᵉ (extensionality-factorization-throughᵉ Fᵉ Eᵉ) =
    is-equiv-htpy-eq-factorization-throughᵉ Fᵉ Eᵉ

  eq-htpy-factorization-throughᵉ :
    (Fᵉ Eᵉ : factorization-throughᵉ fᵉ Xᵉ) →
    htpy-factorization-throughᵉ Fᵉ Eᵉ → Fᵉ ＝ᵉ Eᵉ
  eq-htpy-factorization-throughᵉ Fᵉ Eᵉ =
    map-inv-equivᵉ (extensionality-factorization-throughᵉ Fᵉ Eᵉ)
```

### Characterization of identifications of factorizations of a map in a universe level

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  equiv-factorizationᵉ :
    (Fᵉ Eᵉ : factorizationᵉ l3ᵉ fᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equiv-factorizationᵉ Fᵉ Eᵉ =
    Σᵉ ( image-factorizationᵉ Fᵉ ≃ᵉ image-factorizationᵉ Eᵉ)
      ( λ eᵉ →
        htpy-factorization-throughᵉ fᵉ
          ( whisker-image-factorization-throughᵉ fᵉ
            ( map-equivᵉ eᵉ ,ᵉ retraction-map-equivᵉ eᵉ)
            ( factorization-through-factorizationᵉ Fᵉ))
          ( factorization-through-factorizationᵉ Eᵉ))

  id-equiv-factorizationᵉ :
    (Fᵉ : factorizationᵉ l3ᵉ fᵉ) → equiv-factorizationᵉ Fᵉ Fᵉ
  pr1ᵉ (id-equiv-factorizationᵉ Fᵉ) = id-equivᵉ
  pr2ᵉ (id-equiv-factorizationᵉ Fᵉ) =
    refl-htpy-factorization-throughᵉ fᵉ (factorization-through-factorizationᵉ Fᵉ)

  equiv-eq-factorizationᵉ :
    (Fᵉ Eᵉ : factorizationᵉ l3ᵉ fᵉ) →
    Fᵉ ＝ᵉ Eᵉ → equiv-factorizationᵉ Fᵉ Eᵉ
  equiv-eq-factorizationᵉ Fᵉ .Fᵉ reflᵉ = id-equiv-factorizationᵉ Fᵉ

  is-torsorial-equiv-factorizationᵉ :
    (Fᵉ : factorizationᵉ l3ᵉ fᵉ) →
    is-torsorialᵉ (equiv-factorizationᵉ Fᵉ)
  is-torsorial-equiv-factorizationᵉ Fᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (image-factorizationᵉ Fᵉ))
      ( image-factorizationᵉ Fᵉ ,ᵉ id-equivᵉ)
      ( is-torsorial-htpy-factorization-throughᵉ fᵉ
        ( factorization-through-factorizationᵉ Fᵉ))

  is-equiv-equiv-eq-factorizationᵉ :
    (Fᵉ Eᵉ : factorizationᵉ l3ᵉ fᵉ) → is-equivᵉ (equiv-eq-factorizationᵉ Fᵉ Eᵉ)
  is-equiv-equiv-eq-factorizationᵉ Fᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-equiv-factorizationᵉ Fᵉ)
      ( equiv-eq-factorizationᵉ Fᵉ)

  extensionality-factorizationᵉ :
    (Fᵉ Eᵉ : factorizationᵉ l3ᵉ fᵉ) → (Fᵉ ＝ᵉ Eᵉ) ≃ᵉ (equiv-factorizationᵉ Fᵉ Eᵉ)
  pr1ᵉ (extensionality-factorizationᵉ Fᵉ Eᵉ) = equiv-eq-factorizationᵉ Fᵉ Eᵉ
  pr2ᵉ (extensionality-factorizationᵉ Fᵉ Eᵉ) = is-equiv-equiv-eq-factorizationᵉ Fᵉ Eᵉ

  eq-equiv-factorizationᵉ :
    (Fᵉ Eᵉ : factorizationᵉ l3ᵉ fᵉ) → equiv-factorizationᵉ Fᵉ Eᵉ → Fᵉ ＝ᵉ Eᵉ
  eq-equiv-factorizationᵉ Fᵉ Eᵉ = map-inv-equivᵉ (extensionality-factorizationᵉ Fᵉ Eᵉ)
```

## See also

-ᵉ [Factorizationsᵉ ofᵉ mapsᵉ intoᵉ functionᵉ classes](orthogonal-factorization-systems.factorizations-of-maps-function-classes.mdᵉ)