# Π-decompositions of types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.pi-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
```

</details>

## Idea

Aᵉ Π-decompositionᵉ ofᵉ aᵉ typeᵉ `A`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ andᵉ aᵉ familyᵉ ofᵉ typesᵉ
`Yᵉ x`ᵉ indexedᵉ byᵉ `xᵉ : X`ᵉ equippedᵉ with anᵉ equivalenceᵉ `Aᵉ ≃ᵉ Πᵉ Xᵉ Y`.ᵉ Theᵉ typeᵉ `X`ᵉ
isᵉ calledᵉ theᵉ indexingᵉ typeᵉ ofᵉ theᵉ Π-decomposition,ᵉ theᵉ elementsᵉ ofᵉ `Yᵉ x`ᵉ areᵉ
calledᵉ theᵉ cotypesᵉ ofᵉ theᵉ Π-decomposition,ᵉ andᵉ theᵉ equivalenceᵉ `Aᵉ ≃ᵉ Πᵉ Xᵉ Y`ᵉ isᵉ
theᵉ matchingᵉ correspondenceᵉ ofᵉ theᵉ Π-decompositionᵉ

## Definitions

### Π type

```agda
Πᵉ : {l1ᵉ l2ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) (Yᵉ : Xᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Πᵉ Xᵉ Yᵉ = (xᵉ : Xᵉ) → Yᵉ xᵉ
```

### General Π-decompositions

```agda
Π-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ =
  Σᵉ ( UUᵉ l2ᵉ)
    ( λ Xᵉ →
      Σᵉ ( Xᵉ → UUᵉ l3ᵉ)
        ( λ Yᵉ → Aᵉ ≃ᵉ Πᵉ Xᵉ Yᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  indexing-type-Π-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-Π-Decompositionᵉ = pr1ᵉ Dᵉ

  cotype-Π-Decompositionᵉ : indexing-type-Π-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-Π-Decompositionᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  matching-correspondence-Π-Decompositionᵉ :
    Aᵉ ≃ᵉ Πᵉ indexing-type-Π-Decompositionᵉ cotype-Π-Decompositionᵉ
  matching-correspondence-Π-Decompositionᵉ = pr2ᵉ (pr2ᵉ Dᵉ)

  map-matching-correspondence-Π-Decompositionᵉ :
    Aᵉ → Πᵉ indexing-type-Π-Decompositionᵉ cotype-Π-Decompositionᵉ
  map-matching-correspondence-Π-Decompositionᵉ =
    map-equivᵉ matching-correspondence-Π-Decompositionᵉ
```

### Fibered Π-decompositions

```agda
fibered-Π-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  Σᵉ ( Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
    ( Π-Decompositionᵉ l4ᵉ l5ᵉ ∘ᵉ indexing-type-Π-Decompositionᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  fst-fibered-Π-Decompositionᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ
  fst-fibered-Π-Decompositionᵉ = pr1ᵉ Xᵉ

  indexing-type-fst-fibered-Π-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-fst-fibered-Π-Decompositionᵉ =
    indexing-type-Π-Decompositionᵉ fst-fibered-Π-Decompositionᵉ

  cotype-fst-fibered-Π-Decompositionᵉ :
    indexing-type-fst-fibered-Π-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-fst-fibered-Π-Decompositionᵉ =
    cotype-Π-Decompositionᵉ fst-fibered-Π-Decompositionᵉ

  matching-correspondence-fst-fibered-Π-Decompositionᵉ :
    Aᵉ ≃ᵉ
    Πᵉ ( indexing-type-Π-Decompositionᵉ
        ( fst-fibered-Π-Decompositionᵉ))
      ( cotype-Π-Decompositionᵉ fst-fibered-Π-Decompositionᵉ)
  matching-correspondence-fst-fibered-Π-Decompositionᵉ =
    matching-correspondence-Π-Decompositionᵉ
      ( fst-fibered-Π-Decompositionᵉ)

  map-matching-correspondence-fst-fibered-Π-Decompositionᵉ :
    Aᵉ →
    Πᵉ ( indexing-type-Π-Decompositionᵉ
        ( fst-fibered-Π-Decompositionᵉ))
      ( cotype-Π-Decompositionᵉ fst-fibered-Π-Decompositionᵉ)
  map-matching-correspondence-fst-fibered-Π-Decompositionᵉ =
    map-matching-correspondence-Π-Decompositionᵉ
      fst-fibered-Π-Decompositionᵉ

  snd-fibered-Π-Decompositionᵉ :
      Π-Decompositionᵉ l4ᵉ l5ᵉ
        ( indexing-type-fst-fibered-Π-Decompositionᵉ)
  snd-fibered-Π-Decompositionᵉ = pr2ᵉ Xᵉ

  indexing-type-snd-fibered-Π-Decompositionᵉ : UUᵉ l4ᵉ
  indexing-type-snd-fibered-Π-Decompositionᵉ =
    indexing-type-Π-Decompositionᵉ snd-fibered-Π-Decompositionᵉ

  cotype-snd-fibered-Π-Decompositionᵉ :
    indexing-type-snd-fibered-Π-Decompositionᵉ → UUᵉ l5ᵉ
  cotype-snd-fibered-Π-Decompositionᵉ =
    cotype-Π-Decompositionᵉ snd-fibered-Π-Decompositionᵉ

  matching-correspondence-snd-fibered-Π-Decompositionᵉ :
    indexing-type-fst-fibered-Π-Decompositionᵉ ≃ᵉ
    Πᵉ ( indexing-type-Π-Decompositionᵉ
        ( snd-fibered-Π-Decompositionᵉ))
      ( cotype-Π-Decompositionᵉ snd-fibered-Π-Decompositionᵉ)
  matching-correspondence-snd-fibered-Π-Decompositionᵉ =
    matching-correspondence-Π-Decompositionᵉ
      ( snd-fibered-Π-Decompositionᵉ)

  map-matching-correspondence-snd-fibered-Π-Decompositionᵉ :
    indexing-type-fst-fibered-Π-Decompositionᵉ →
    Πᵉ ( indexing-type-Π-Decompositionᵉ
        ( snd-fibered-Π-Decompositionᵉ))
      ( cotype-Π-Decompositionᵉ snd-fibered-Π-Decompositionᵉ)
  map-matching-correspondence-snd-fibered-Π-Decompositionᵉ =
    map-matching-correspondence-Π-Decompositionᵉ
      ( snd-fibered-Π-Decompositionᵉ)
```

#### Displayed double Π-decompositions

```agda
displayed-Π-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  ( Σᵉ (Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  ( λ Dᵉ →
    (uᵉ : indexing-type-Π-Decompositionᵉ Dᵉ) →
    Π-Decompositionᵉ l4ᵉ l5ᵉ (cotype-Π-Decompositionᵉ Dᵉ uᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  fst-displayed-Π-Decompositionᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ
  fst-displayed-Π-Decompositionᵉ = pr1ᵉ Xᵉ

  indexing-type-fst-displayed-Π-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-fst-displayed-Π-Decompositionᵉ =
    indexing-type-Π-Decompositionᵉ fst-displayed-Π-Decompositionᵉ

  cotype-fst-displayed-Π-Decompositionᵉ :
    indexing-type-fst-displayed-Π-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-fst-displayed-Π-Decompositionᵉ =
    cotype-Π-Decompositionᵉ fst-displayed-Π-Decompositionᵉ

  matching-correspondence-fst-displayed-Π-Decompositionᵉ :
    Aᵉ ≃ᵉ
    Πᵉ ( indexing-type-Π-Decompositionᵉ
        fst-displayed-Π-Decompositionᵉ)
      ( cotype-Π-Decompositionᵉ fst-displayed-Π-Decompositionᵉ)
  matching-correspondence-fst-displayed-Π-Decompositionᵉ =
    matching-correspondence-Π-Decompositionᵉ
      fst-displayed-Π-Decompositionᵉ

  map-matching-correspondence-fst-displayed-Π-Decompositionᵉ :
    Aᵉ →
    Πᵉ ( indexing-type-Π-Decompositionᵉ
        fst-displayed-Π-Decompositionᵉ)
      ( cotype-Π-Decompositionᵉ fst-displayed-Π-Decompositionᵉ)
  map-matching-correspondence-fst-displayed-Π-Decompositionᵉ =
    map-matching-correspondence-Π-Decompositionᵉ
      fst-displayed-Π-Decompositionᵉ

  snd-displayed-Π-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Π-Decompositionᵉ) →
    Π-Decompositionᵉ l4ᵉ l5ᵉ
      ( cotype-fst-displayed-Π-Decompositionᵉ xᵉ)
  snd-displayed-Π-Decompositionᵉ = pr2ᵉ Xᵉ

  indexing-type-snd-displayed-Π-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Π-Decompositionᵉ) →
    UUᵉ l4ᵉ
  indexing-type-snd-displayed-Π-Decompositionᵉ xᵉ =
    indexing-type-Π-Decompositionᵉ
      ( snd-displayed-Π-Decompositionᵉ xᵉ)

  cotype-snd-displayed-Π-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Π-Decompositionᵉ) →
    indexing-type-snd-displayed-Π-Decompositionᵉ xᵉ →
    UUᵉ l5ᵉ
  cotype-snd-displayed-Π-Decompositionᵉ xᵉ =
    cotype-Π-Decompositionᵉ (snd-displayed-Π-Decompositionᵉ xᵉ)

  matching-correspondence-snd-displayed-Π-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Π-Decompositionᵉ) →
    ( cotype-fst-displayed-Π-Decompositionᵉ xᵉ ≃ᵉ
      Πᵉ ( indexing-type-snd-displayed-Π-Decompositionᵉ xᵉ)
        ( cotype-snd-displayed-Π-Decompositionᵉ xᵉ))
  matching-correspondence-snd-displayed-Π-Decompositionᵉ xᵉ =
    matching-correspondence-Π-Decompositionᵉ
      ( snd-displayed-Π-Decompositionᵉ xᵉ)

  map-matching-correspondence-snd-displayed-Π-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Π-Decompositionᵉ) →
    cotype-fst-displayed-Π-Decompositionᵉ xᵉ →
    Πᵉ ( indexing-type-snd-displayed-Π-Decompositionᵉ xᵉ)
      ( cotype-snd-displayed-Π-Decompositionᵉ xᵉ)
  map-matching-correspondence-snd-displayed-Π-Decompositionᵉ xᵉ =
    map-matching-correspondence-Π-Decompositionᵉ
      ( snd-displayed-Π-Decompositionᵉ xᵉ)
```

## Properties

### Characterization of equality of Π-decompositions

```agda
equiv-Π-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  (Yᵉ : Π-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
equiv-Π-Decompositionᵉ Xᵉ Yᵉ =
  Σᵉ ( indexing-type-Π-Decompositionᵉ Xᵉ ≃ᵉ
      indexing-type-Π-Decompositionᵉ Yᵉ)
    ( λ eᵉ →
      Σᵉ ( (xᵉ : indexing-type-Π-Decompositionᵉ Xᵉ) →
          cotype-Π-Decompositionᵉ Xᵉ xᵉ ≃ᵉ
          cotype-Π-Decompositionᵉ Yᵉ (map-equivᵉ eᵉ xᵉ))
        ( λ fᵉ →
          ( map-equiv-Πᵉ (λ zᵉ → cotype-Π-Decompositionᵉ Yᵉ zᵉ) eᵉ fᵉ ∘ᵉ
            ( map-matching-correspondence-Π-Decompositionᵉ Xᵉ)) ~ᵉ
          ( map-matching-correspondence-Π-Decompositionᵉ Yᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) (Yᵉ : Π-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ)
  (eᵉ : equiv-Π-Decompositionᵉ Xᵉ Yᵉ)
  where

  equiv-indexing-type-equiv-Π-Decompositionᵉ :
    indexing-type-Π-Decompositionᵉ Xᵉ ≃ᵉ
    indexing-type-Π-Decompositionᵉ Yᵉ
  equiv-indexing-type-equiv-Π-Decompositionᵉ = pr1ᵉ eᵉ

  map-equiv-indexing-type-equiv-Π-Decompositionᵉ :
    indexing-type-Π-Decompositionᵉ Xᵉ →
    indexing-type-Π-Decompositionᵉ Yᵉ
  map-equiv-indexing-type-equiv-Π-Decompositionᵉ =
    map-equivᵉ equiv-indexing-type-equiv-Π-Decompositionᵉ

  equiv-cotype-equiv-Π-Decompositionᵉ :
    (xᵉ : indexing-type-Π-Decompositionᵉ Xᵉ) →
    cotype-Π-Decompositionᵉ Xᵉ xᵉ ≃ᵉ
    cotype-Π-Decompositionᵉ Yᵉ
      ( map-equiv-indexing-type-equiv-Π-Decompositionᵉ xᵉ)
  equiv-cotype-equiv-Π-Decompositionᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  map-equiv-cotype-equiv-Π-Decompositionᵉ :
    (xᵉ : indexing-type-Π-Decompositionᵉ Xᵉ) →
    cotype-Π-Decompositionᵉ Xᵉ xᵉ →
    cotype-Π-Decompositionᵉ Yᵉ
      ( map-equiv-indexing-type-equiv-Π-Decompositionᵉ xᵉ)
  map-equiv-cotype-equiv-Π-Decompositionᵉ xᵉ =
    map-equivᵉ (equiv-cotype-equiv-Π-Decompositionᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  id-equiv-Π-Decompositionᵉ : equiv-Π-Decompositionᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-Π-Decompositionᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-Π-Decompositionᵉ) xᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-Π-Decompositionᵉ) =
    id-map-equiv-Πᵉ (λ xᵉ → cotype-Π-Decompositionᵉ Xᵉ xᵉ) ·rᵉ
    map-matching-correspondence-Π-Decompositionᵉ Xᵉ

  is-torsorial-equiv-Π-Decompositionᵉ :
    is-torsorialᵉ (equiv-Π-Decompositionᵉ Xᵉ)
  is-torsorial-equiv-Π-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (indexing-type-Π-Decompositionᵉ Xᵉ))
      ( pairᵉ (indexing-type-Π-Decompositionᵉ Xᵉ) id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equiv-famᵉ
          ( cotype-Π-Decompositionᵉ Xᵉ))
        ( pairᵉ
          ( cotype-Π-Decompositionᵉ Xᵉ)
          ( id-equiv-famᵉ (cotype-Π-Decompositionᵉ Xᵉ)))
        ( is-torsorial-htpy-equivᵉ
          ( ( equiv-Πᵉ
              ( cotype-Π-Decompositionᵉ Xᵉ)
              ( id-equivᵉ)
              ( λ _ → id-equivᵉ)) ∘eᵉ
            ( matching-correspondence-Π-Decompositionᵉ Xᵉ))))

  equiv-eq-Π-Decompositionᵉ :
    (Yᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → equiv-Π-Decompositionᵉ Xᵉ Yᵉ
  equiv-eq-Π-Decompositionᵉ .Xᵉ reflᵉ = id-equiv-Π-Decompositionᵉ

  is-equiv-equiv-eq-Π-Decompositionᵉ :
    (Yᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-Π-Decompositionᵉ Yᵉ)
  is-equiv-equiv-eq-Π-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Π-Decompositionᵉ
      equiv-eq-Π-Decompositionᵉ

  extensionality-Π-Decompositionᵉ :
    (Yᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Π-Decompositionᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Π-Decompositionᵉ Yᵉ) =
    equiv-eq-Π-Decompositionᵉ Yᵉ
  pr2ᵉ (extensionality-Π-Decompositionᵉ Yᵉ) =
    is-equiv-equiv-eq-Π-Decompositionᵉ Yᵉ

  eq-equiv-Π-Decompositionᵉ :
    (Yᵉ : Π-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    equiv-Π-Decompositionᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-Π-Decompositionᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-Π-Decompositionᵉ Yᵉ)
```

### Invariance of Π-decompositions under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  equiv-tr-Π-Decompositionᵉ :
    {l3ᵉ l4ᵉ : Level} →
    Π-Decompositionᵉ l3ᵉ l4ᵉ Aᵉ ≃ᵉ Π-Decompositionᵉ l3ᵉ l4ᵉ Bᵉ
  equiv-tr-Π-Decompositionᵉ =
    equiv-totᵉ
      ( λ Xᵉ →
        equiv-totᵉ
          ( λ Yᵉ → equiv-precomp-equivᵉ (inv-equivᵉ eᵉ) (Πᵉ Xᵉ Yᵉ)))

  map-equiv-tr-Π-Decompositionᵉ :
    {l3ᵉ l4ᵉ : Level} →
    Π-Decompositionᵉ l3ᵉ l4ᵉ Aᵉ → Π-Decompositionᵉ l3ᵉ l4ᵉ Bᵉ
  map-equiv-tr-Π-Decompositionᵉ =
    map-equivᵉ equiv-tr-Π-Decompositionᵉ
```

### Iterated Π-decompositions

#### Characterization of identity type for fibered double Π-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  (Yᵉ : fibered-Π-Decompositionᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ Aᵉ)
  where

  equiv-fst-fibered-Π-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ ⊔ l7ᵉ)
  equiv-fst-fibered-Π-Decompositionᵉ =
    equiv-Π-Decompositionᵉ
    ( fst-fibered-Π-Decompositionᵉ Xᵉ)
    ( fst-fibered-Π-Decompositionᵉ Yᵉ)

  equiv-snd-fibered-Π-Decompositionᵉ :
    (eᵉ : equiv-fst-fibered-Π-Decompositionᵉ) →
    UUᵉ (l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-snd-fibered-Π-Decompositionᵉ eᵉ =
    equiv-Π-Decompositionᵉ
      ( map-equiv-tr-Π-Decompositionᵉ
        ( equiv-indexing-type-equiv-Π-Decompositionᵉ
          ( fst-fibered-Π-Decompositionᵉ Xᵉ)
          ( fst-fibered-Π-Decompositionᵉ Yᵉ)
          ( eᵉ))
        ( snd-fibered-Π-Decompositionᵉ Xᵉ))
      ( snd-fibered-Π-Decompositionᵉ Yᵉ)

  equiv-fibered-Π-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-fibered-Π-Decompositionᵉ =
    Σᵉ ( equiv-fst-fibered-Π-Decompositionᵉ)
      ( equiv-snd-fibered-Π-Decompositionᵉ)

  fst-equiv-fibered-Π-Decompositionᵉ :
    (eᵉ : equiv-fibered-Π-Decompositionᵉ) →
    equiv-fst-fibered-Π-Decompositionᵉ
  fst-equiv-fibered-Π-Decompositionᵉ = pr1ᵉ

  snd-equiv-fibered-Π-Decompositionᵉ :
    (eᵉ : equiv-fibered-Π-Decompositionᵉ) →
    equiv-snd-fibered-Π-Decompositionᵉ
      (fst-equiv-fibered-Π-Decompositionᵉ eᵉ)
  snd-equiv-fibered-Π-Decompositionᵉ = pr2ᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  ( Dᵉ : fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = fst-fibered-Π-Decompositionᵉ Dᵉ
    Yᵉ = snd-fibered-Π-Decompositionᵉ Dᵉ

  is-torsorial-equiv-fibered-Π-Decompositionᵉ :
    is-torsorialᵉ (equiv-fibered-Π-Decompositionᵉ Dᵉ)
  is-torsorial-equiv-fibered-Π-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Π-Decompositionᵉ Xᵉ)
      ( Xᵉ ,ᵉ id-equiv-Π-Decompositionᵉ Xᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (indexing-type-Π-Decompositionᵉ Yᵉ))
        ( pairᵉ (indexing-type-Π-Decompositionᵉ Yᵉ) id-equivᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-equiv-famᵉ
            ( cotype-Π-Decompositionᵉ Yᵉ))
          ( pairᵉ
            ( cotype-Π-Decompositionᵉ Yᵉ)
            ( id-equiv-famᵉ
              ( cotype-Π-Decompositionᵉ Yᵉ)))
            ( is-torsorial-htpy-equivᵉ
              ( ( equiv-Πᵉ
                  ( cotype-Π-Decompositionᵉ Yᵉ)
                  ( id-equivᵉ)
                  ( λ _ → id-equivᵉ)) ∘eᵉ
                ( matching-correspondence-Π-Decompositionᵉ Yᵉ)))))

  id-equiv-fibered-Π-Decompositionᵉ :
    equiv-fibered-Π-Decompositionᵉ Dᵉ Dᵉ
  pr1ᵉ id-equiv-fibered-Π-Decompositionᵉ =
    id-equiv-Π-Decompositionᵉ Xᵉ
  pr1ᵉ (pr2ᵉ id-equiv-fibered-Π-Decompositionᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ id-equiv-fibered-Π-Decompositionᵉ)) xᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ id-equiv-fibered-Π-Decompositionᵉ)) =
    id-map-equiv-Πᵉ (cotype-snd-fibered-Π-Decompositionᵉ Dᵉ) ·rᵉ
    map-matching-correspondence-snd-fibered-Π-Decompositionᵉ Dᵉ

  equiv-eq-fibered-Π-Decompositionᵉ :
    (D'ᵉ : fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (Dᵉ ＝ᵉ D'ᵉ) → equiv-fibered-Π-Decompositionᵉ Dᵉ D'ᵉ
  equiv-eq-fibered-Π-Decompositionᵉ .Dᵉ reflᵉ =
    id-equiv-fibered-Π-Decompositionᵉ

  is-equiv-equiv-eq-fibered-Π-Decompositionᵉ :
    (D'ᵉ : fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-fibered-Π-Decompositionᵉ D'ᵉ)
  is-equiv-equiv-eq-fibered-Π-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-fibered-Π-Decompositionᵉ
      equiv-eq-fibered-Π-Decompositionᵉ

  extensionality-fibered-Π-Decompositionᵉ :
    (D'ᵉ : fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (Dᵉ ＝ᵉ D'ᵉ) ≃ᵉ equiv-fibered-Π-Decompositionᵉ Dᵉ D'ᵉ
  pr1ᵉ (extensionality-fibered-Π-Decompositionᵉ D'ᵉ) =
    equiv-eq-fibered-Π-Decompositionᵉ D'ᵉ
  pr2ᵉ (extensionality-fibered-Π-Decompositionᵉ D'ᵉ) =
    is-equiv-equiv-eq-fibered-Π-Decompositionᵉ D'ᵉ

  eq-equiv-fibered-Π-Decompositionᵉ :
    (D'ᵉ : fibered-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (equiv-fibered-Π-Decompositionᵉ Dᵉ D'ᵉ) → (Dᵉ ＝ᵉ D'ᵉ)
  eq-equiv-fibered-Π-Decompositionᵉ D'ᵉ =
    map-inv-equivᵉ (extensionality-fibered-Π-Decompositionᵉ D'ᵉ)
```

#### Characterization of identity type for displayed double Π-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  (Yᵉ : displayed-Π-Decompositionᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ Aᵉ)
  where

  equiv-fst-displayed-Π-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ ⊔ l7ᵉ)
  equiv-fst-displayed-Π-Decompositionᵉ =
    equiv-Π-Decompositionᵉ
    ( fst-displayed-Π-Decompositionᵉ Xᵉ)
    ( fst-displayed-Π-Decompositionᵉ Yᵉ)

  equiv-snd-displayed-Π-Decompositionᵉ :
    (eᵉ : equiv-fst-displayed-Π-Decompositionᵉ) →
    UUᵉ (l2ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-snd-displayed-Π-Decompositionᵉ eᵉ =
    ( xᵉ : indexing-type-fst-displayed-Π-Decompositionᵉ Xᵉ) →
    equiv-Π-Decompositionᵉ
      ( map-equiv-tr-Π-Decompositionᵉ
        ( equiv-cotype-equiv-Π-Decompositionᵉ
          ( fst-displayed-Π-Decompositionᵉ Xᵉ)
          ( fst-displayed-Π-Decompositionᵉ Yᵉ)
          ( eᵉ)
          ( xᵉ))
        ( snd-displayed-Π-Decompositionᵉ Xᵉ xᵉ))
      ( snd-displayed-Π-Decompositionᵉ Yᵉ
        ( map-equiv-indexing-type-equiv-Π-Decompositionᵉ
          ( fst-displayed-Π-Decompositionᵉ Xᵉ)
          ( fst-displayed-Π-Decompositionᵉ Yᵉ)
          ( eᵉ)
          ( xᵉ)))

  equiv-displayed-Π-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-displayed-Π-Decompositionᵉ =
    Σᵉ ( equiv-fst-displayed-Π-Decompositionᵉ)
      ( equiv-snd-displayed-Π-Decompositionᵉ)

  fst-equiv-displayed-Π-Decompositionᵉ :
    (eᵉ : equiv-displayed-Π-Decompositionᵉ) →
    equiv-fst-displayed-Π-Decompositionᵉ
  fst-equiv-displayed-Π-Decompositionᵉ = pr1ᵉ

  snd-equiv-displayed-Π-Decompositionᵉ :
    (eᵉ : equiv-displayed-Π-Decompositionᵉ) →
    equiv-snd-displayed-Π-Decompositionᵉ
      ( fst-equiv-displayed-Π-Decompositionᵉ eᵉ)
  snd-equiv-displayed-Π-Decompositionᵉ = pr2ᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  ( disp-Dᵉ : displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = fst-displayed-Π-Decompositionᵉ disp-Dᵉ
    f-Yᵉ = snd-displayed-Π-Decompositionᵉ disp-Dᵉ

  is-torsorial-equiv-displayed-Π-Decompositionᵉ :
    is-torsorialᵉ (equiv-displayed-Π-Decompositionᵉ disp-Dᵉ)
  is-torsorial-equiv-displayed-Π-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Π-Decompositionᵉ Xᵉ)
      ( pairᵉ Xᵉ (id-equiv-Π-Decompositionᵉ Xᵉ))
      ( is-contr-equivᵉ
        ( Π-total-famᵉ (λ xᵉ → _))
        ( inv-distributive-Π-Σᵉ)
        ( is-contr-Πᵉ
          ( λ xᵉ → is-torsorial-equiv-Π-Decompositionᵉ (f-Yᵉ xᵉ))))

  id-equiv-displayed-Π-Decompositionᵉ :
    equiv-displayed-Π-Decompositionᵉ disp-Dᵉ disp-Dᵉ
  pr1ᵉ id-equiv-displayed-Π-Decompositionᵉ =
    id-equiv-Π-Decompositionᵉ Xᵉ
  pr1ᵉ (pr2ᵉ id-equiv-displayed-Π-Decompositionᵉ xᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ id-equiv-displayed-Π-Decompositionᵉ xᵉ)) yᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ id-equiv-displayed-Π-Decompositionᵉ xᵉ)) =
    id-map-equiv-Πᵉ
      ( cotype-snd-displayed-Π-Decompositionᵉ disp-Dᵉ xᵉ) ·rᵉ
    map-matching-correspondence-snd-displayed-Π-Decompositionᵉ disp-Dᵉ xᵉ

  equiv-eq-displayed-Π-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ) → equiv-displayed-Π-Decompositionᵉ disp-Dᵉ disp-D'ᵉ
  equiv-eq-displayed-Π-Decompositionᵉ .disp-Dᵉ reflᵉ =
    id-equiv-displayed-Π-Decompositionᵉ

  is-equiv-equiv-eq-displayed-Π-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-displayed-Π-Decompositionᵉ disp-D'ᵉ)
  is-equiv-equiv-eq-displayed-Π-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-displayed-Π-Decompositionᵉ
      equiv-eq-displayed-Π-Decompositionᵉ

  extensionality-displayed-Π-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ) ≃ᵉ equiv-displayed-Π-Decompositionᵉ disp-Dᵉ disp-D'ᵉ
  pr1ᵉ (extensionality-displayed-Π-Decompositionᵉ Dᵉ) =
    equiv-eq-displayed-Π-Decompositionᵉ Dᵉ
  pr2ᵉ (extensionality-displayed-Π-Decompositionᵉ Dᵉ) =
    is-equiv-equiv-eq-displayed-Π-Decompositionᵉ Dᵉ

  eq-equiv-displayed-Π-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Π-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (equiv-displayed-Π-Decompositionᵉ disp-Dᵉ disp-D'ᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ)
  eq-equiv-displayed-Π-Decompositionᵉ Dᵉ =
    map-inv-equivᵉ
      (extensionality-displayed-Π-Decompositionᵉ Dᵉ)
```