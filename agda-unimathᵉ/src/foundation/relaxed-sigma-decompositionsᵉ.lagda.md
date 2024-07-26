# Relaxed Σ-decompositions of types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.relaxed-sigma-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

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

Aᵉ relaxedᵉ Σ-decompositionᵉ isᵉ justᵉ aᵉ Σ-Decompositionᵉ where theᵉ conditionᵉ thatᵉ theᵉ
cotypeᵉ mustᵉ beᵉ inhabitedᵉ isᵉ relaxed.ᵉ

## Definitions

### General Σ-decompositions

```agda
Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ =
  Σᵉ ( UUᵉ l2ᵉ)
    ( λ Xᵉ →
      Σᵉ ( Xᵉ → UUᵉ l3ᵉ)
        ( λ Yᵉ → Aᵉ ≃ᵉ Σᵉ Xᵉ Yᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  indexing-type-Relaxed-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-Relaxed-Σ-Decompositionᵉ = pr1ᵉ Dᵉ

  cotype-Relaxed-Σ-Decompositionᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-Relaxed-Σ-Decompositionᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  matching-correspondence-Relaxed-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ Σᵉ indexing-type-Relaxed-Σ-Decompositionᵉ cotype-Relaxed-Σ-Decompositionᵉ
  matching-correspondence-Relaxed-Σ-Decompositionᵉ = pr2ᵉ (pr2ᵉ Dᵉ)

  map-matching-correspondence-Relaxed-Σ-Decompositionᵉ :
    Aᵉ → Σᵉ indexing-type-Relaxed-Σ-Decompositionᵉ cotype-Relaxed-Σ-Decompositionᵉ
  map-matching-correspondence-Relaxed-Σ-Decompositionᵉ =
    map-equivᵉ matching-correspondence-Relaxed-Σ-Decompositionᵉ
```

### Fibered relaxed Σ-decompositions

```agda
fibered-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  Σᵉ ( Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
    ( Relaxed-Σ-Decompositionᵉ l4ᵉ l5ᵉ ∘ᵉ indexing-type-Relaxed-Σ-Decompositionᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  fst-fibered-Relaxed-Σ-Decompositionᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ
  fst-fibered-Relaxed-Σ-Decompositionᵉ = pr1ᵉ Xᵉ

  indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ =
    indexing-type-Relaxed-Σ-Decompositionᵉ fst-fibered-Relaxed-Σ-Decompositionᵉ

  cotype-fst-fibered-Relaxed-Σ-Decompositionᵉ :
    indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-fst-fibered-Relaxed-Σ-Decompositionᵉ =
    cotype-Relaxed-Σ-Decompositionᵉ fst-fibered-Relaxed-Σ-Decompositionᵉ

  matching-correspondence-fst-fibered-Relaxed-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ
    Σᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ
        ( fst-fibered-Relaxed-Σ-Decompositionᵉ))
      ( cotype-Relaxed-Σ-Decompositionᵉ fst-fibered-Relaxed-Σ-Decompositionᵉ)
  matching-correspondence-fst-fibered-Relaxed-Σ-Decompositionᵉ =
    matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( fst-fibered-Relaxed-Σ-Decompositionᵉ)

  map-matching-correspondence-fst-fibered-Relaxed-Σ-Decompositionᵉ :
    Aᵉ →
    Σᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ
        ( fst-fibered-Relaxed-Σ-Decompositionᵉ))
      ( cotype-Relaxed-Σ-Decompositionᵉ fst-fibered-Relaxed-Σ-Decompositionᵉ)
  map-matching-correspondence-fst-fibered-Relaxed-Σ-Decompositionᵉ =
    map-matching-correspondence-Relaxed-Σ-Decompositionᵉ
      fst-fibered-Relaxed-Σ-Decompositionᵉ

  snd-fibered-Relaxed-Σ-Decompositionᵉ :
      Relaxed-Σ-Decompositionᵉ l4ᵉ l5ᵉ
        ( indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ)
  snd-fibered-Relaxed-Σ-Decompositionᵉ = pr2ᵉ Xᵉ

  indexing-type-snd-fibered-Relaxed-Σ-Decompositionᵉ : UUᵉ l4ᵉ
  indexing-type-snd-fibered-Relaxed-Σ-Decompositionᵉ =
    indexing-type-Relaxed-Σ-Decompositionᵉ snd-fibered-Relaxed-Σ-Decompositionᵉ

  cotype-snd-fibered-Relaxed-Σ-Decompositionᵉ :
    indexing-type-snd-fibered-Relaxed-Σ-Decompositionᵉ → UUᵉ l5ᵉ
  cotype-snd-fibered-Relaxed-Σ-Decompositionᵉ =
    cotype-Relaxed-Σ-Decompositionᵉ snd-fibered-Relaxed-Σ-Decompositionᵉ

  matching-correspondence-snd-fibered-Relaxed-Σ-Decompositionᵉ :
    indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ ≃ᵉ
    Σᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ
        ( snd-fibered-Relaxed-Σ-Decompositionᵉ))
      ( cotype-Relaxed-Σ-Decompositionᵉ snd-fibered-Relaxed-Σ-Decompositionᵉ)
  matching-correspondence-snd-fibered-Relaxed-Σ-Decompositionᵉ =
    matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( snd-fibered-Relaxed-Σ-Decompositionᵉ)

  map-matching-correspondence-snd-fibered-Relaxed-Σ-Decompositionᵉ :
    indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ →
    Σᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ
        ( snd-fibered-Relaxed-Σ-Decompositionᵉ))
      ( cotype-Relaxed-Σ-Decompositionᵉ snd-fibered-Relaxed-Σ-Decompositionᵉ)
  map-matching-correspondence-snd-fibered-Relaxed-Σ-Decompositionᵉ =
    map-matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( snd-fibered-Relaxed-Σ-Decompositionᵉ)
```

#### Displayed double Σ-decompositions

```agda
displayed-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  ( Σᵉ (Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  ( λ Dᵉ →
    (uᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Dᵉ) →
    Relaxed-Σ-Decompositionᵉ l4ᵉ l5ᵉ (cotype-Relaxed-Σ-Decompositionᵉ Dᵉ uᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  fst-displayed-Relaxed-Σ-Decompositionᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ
  fst-displayed-Relaxed-Σ-Decompositionᵉ = pr1ᵉ Xᵉ

  indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ =
    indexing-type-Relaxed-Σ-Decompositionᵉ fst-displayed-Relaxed-Σ-Decompositionᵉ

  cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ :
    indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ =
    cotype-Relaxed-Σ-Decompositionᵉ fst-displayed-Relaxed-Σ-Decompositionᵉ

  matching-correspondence-fst-displayed-Relaxed-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ
    Σᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ
        fst-displayed-Relaxed-Σ-Decompositionᵉ)
      ( cotype-Relaxed-Σ-Decompositionᵉ fst-displayed-Relaxed-Σ-Decompositionᵉ)
  matching-correspondence-fst-displayed-Relaxed-Σ-Decompositionᵉ =
    matching-correspondence-Relaxed-Σ-Decompositionᵉ
      fst-displayed-Relaxed-Σ-Decompositionᵉ

  map-matching-correspondence-fst-displayed-Relaxed-Σ-Decompositionᵉ :
    Aᵉ →
    Σᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ
        fst-displayed-Relaxed-Σ-Decompositionᵉ)
      ( cotype-Relaxed-Σ-Decompositionᵉ fst-displayed-Relaxed-Σ-Decompositionᵉ)
  map-matching-correspondence-fst-displayed-Relaxed-Σ-Decompositionᵉ =
    map-matching-correspondence-Relaxed-Σ-Decompositionᵉ
      fst-displayed-Relaxed-Σ-Decompositionᵉ

  snd-displayed-Relaxed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ) →
    Relaxed-Σ-Decompositionᵉ l4ᵉ l5ᵉ
      ( cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)
  snd-displayed-Relaxed-Σ-Decompositionᵉ = pr2ᵉ Xᵉ

  indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ) →
    UUᵉ l4ᵉ
  indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ =
    indexing-type-Relaxed-Σ-Decompositionᵉ
      ( snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)

  cotype-snd-displayed-Relaxed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ) →
    indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ →
    UUᵉ l5ᵉ
  cotype-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ =
    cotype-Relaxed-Σ-Decompositionᵉ (snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)

  matching-correspondence-snd-displayed-Relaxed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ) →
    ( cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ xᵉ ≃ᵉ
      Σᵉ ( indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)
        ( cotype-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ))
  matching-correspondence-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ =
    matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)

  map-matching-correspondence-snd-displayed-Relaxed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ) →
    cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ xᵉ →
    Σᵉ ( indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)
      ( cotype-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)
  map-matching-correspondence-snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ =
    map-matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( snd-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)
```

## Properties

### Characterization of equality of relaxed-Σ-decompositions

```agda
equiv-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  (Yᵉ : Relaxed-Σ-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
equiv-Relaxed-Σ-Decompositionᵉ Xᵉ Yᵉ =
  Σᵉ ( indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ ≃ᵉ
      indexing-type-Relaxed-Σ-Decompositionᵉ Yᵉ)
    ( λ eᵉ →
      Σᵉ ( (xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ) →
          cotype-Relaxed-Σ-Decompositionᵉ Xᵉ xᵉ ≃ᵉ
          cotype-Relaxed-Σ-Decompositionᵉ Yᵉ (map-equivᵉ eᵉ xᵉ))
        ( λ fᵉ →
          ( ( map-equivᵉ (equiv-Σᵉ (cotype-Relaxed-Σ-Decompositionᵉ Yᵉ) eᵉ fᵉ)) ∘ᵉ
            ( map-matching-correspondence-Relaxed-Σ-Decompositionᵉ Xᵉ)) ~ᵉ
          ( map-matching-correspondence-Relaxed-Σ-Decompositionᵉ Yᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) (Yᵉ : Relaxed-Σ-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ)
  (eᵉ : equiv-Relaxed-Σ-Decompositionᵉ Xᵉ Yᵉ)
  where

  equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ :
    indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ ≃ᵉ
    indexing-type-Relaxed-Σ-Decompositionᵉ Yᵉ
  equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ = pr1ᵉ eᵉ

  map-equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ :
    indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ →
    indexing-type-Relaxed-Σ-Decompositionᵉ Yᵉ
  map-equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ =
    map-equivᵉ equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ

  equiv-cotype-equiv-Relaxed-Σ-Decompositionᵉ :
    (xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ) →
    cotype-Relaxed-Σ-Decompositionᵉ Xᵉ xᵉ ≃ᵉ
    cotype-Relaxed-Σ-Decompositionᵉ Yᵉ
      ( map-equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ xᵉ)
  equiv-cotype-equiv-Relaxed-Σ-Decompositionᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  map-equiv-cotype-equiv-Relaxed-Σ-Decompositionᵉ :
    (xᵉ : indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ) →
    cotype-Relaxed-Σ-Decompositionᵉ Xᵉ xᵉ →
    cotype-Relaxed-Σ-Decompositionᵉ Yᵉ
      ( map-equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ xᵉ)
  map-equiv-cotype-equiv-Relaxed-Σ-Decompositionᵉ xᵉ =
    map-equivᵉ (equiv-cotype-equiv-Relaxed-Σ-Decompositionᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  id-equiv-Relaxed-Σ-Decompositionᵉ : equiv-Relaxed-Σ-Decompositionᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-Relaxed-Σ-Decompositionᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-Relaxed-Σ-Decompositionᵉ) xᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-Relaxed-Σ-Decompositionᵉ) = refl-htpyᵉ

  is-torsorial-equiv-Relaxed-Σ-Decompositionᵉ :
    is-torsorialᵉ (equiv-Relaxed-Σ-Decompositionᵉ Xᵉ)
  is-torsorial-equiv-Relaxed-Σ-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ))
      ( pairᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Xᵉ) id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equiv-famᵉ
          ( cotype-Relaxed-Σ-Decompositionᵉ Xᵉ))
        ( pairᵉ
          ( cotype-Relaxed-Σ-Decompositionᵉ Xᵉ)
          ( id-equiv-famᵉ (cotype-Relaxed-Σ-Decompositionᵉ Xᵉ)))
        ( is-torsorial-htpy-equivᵉ
          ( matching-correspondence-Relaxed-Σ-Decompositionᵉ Xᵉ)))

  equiv-eq-Relaxed-Σ-Decompositionᵉ :
    (Yᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → equiv-Relaxed-Σ-Decompositionᵉ Xᵉ Yᵉ
  equiv-eq-Relaxed-Σ-Decompositionᵉ .Xᵉ reflᵉ = id-equiv-Relaxed-Σ-Decompositionᵉ

  is-equiv-equiv-eq-Relaxed-Σ-Decompositionᵉ :
    (Yᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-Relaxed-Σ-Decompositionᵉ Yᵉ)
  is-equiv-equiv-eq-Relaxed-Σ-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Relaxed-Σ-Decompositionᵉ
      equiv-eq-Relaxed-Σ-Decompositionᵉ

  extensionality-Relaxed-Σ-Decompositionᵉ :
    (Yᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Relaxed-Σ-Decompositionᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Relaxed-Σ-Decompositionᵉ Yᵉ) =
    equiv-eq-Relaxed-Σ-Decompositionᵉ Yᵉ
  pr2ᵉ (extensionality-Relaxed-Σ-Decompositionᵉ Yᵉ) =
    is-equiv-equiv-eq-Relaxed-Σ-Decompositionᵉ Yᵉ

  eq-equiv-Relaxed-Σ-Decompositionᵉ :
    (Yᵉ : Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    equiv-Relaxed-Σ-Decompositionᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-Relaxed-Σ-Decompositionᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-Relaxed-Σ-Decompositionᵉ Yᵉ)
```

### Invariance of Σ-decompositions under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  equiv-tr-Relaxed-Σ-Decompositionᵉ :
    {l3ᵉ l4ᵉ : Level} →
    Relaxed-Σ-Decompositionᵉ l3ᵉ l4ᵉ Aᵉ ≃ᵉ Relaxed-Σ-Decompositionᵉ l3ᵉ l4ᵉ Bᵉ
  equiv-tr-Relaxed-Σ-Decompositionᵉ =
    equiv-totᵉ
      ( λ Xᵉ →
        equiv-totᵉ
          ( λ Yᵉ →
            equiv-precomp-equivᵉ (inv-equivᵉ eᵉ) (Σᵉ Xᵉ Yᵉ)))

  map-equiv-tr-Relaxed-Σ-Decompositionᵉ :
    {l3ᵉ l4ᵉ : Level} →
    Relaxed-Σ-Decompositionᵉ l3ᵉ l4ᵉ Aᵉ → Relaxed-Σ-Decompositionᵉ l3ᵉ l4ᵉ Bᵉ
  map-equiv-tr-Relaxed-Σ-Decompositionᵉ =
    map-equivᵉ equiv-tr-Relaxed-Σ-Decompositionᵉ
```

### Iterated Σ-decompositions

#### Characterization of identity type for fibered double Σ-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  (Yᵉ : fibered-Relaxed-Σ-Decompositionᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ Aᵉ)
  where

  equiv-fst-fibered-Relaxed-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ ⊔ l7ᵉ)
  equiv-fst-fibered-Relaxed-Σ-Decompositionᵉ =
    equiv-Relaxed-Σ-Decompositionᵉ
    ( fst-fibered-Relaxed-Σ-Decompositionᵉ Xᵉ)
    ( fst-fibered-Relaxed-Σ-Decompositionᵉ Yᵉ)

  equiv-snd-fibered-Relaxed-Σ-Decompositionᵉ :
    (eᵉ : equiv-fst-fibered-Relaxed-Σ-Decompositionᵉ) →
    UUᵉ (l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-snd-fibered-Relaxed-Σ-Decompositionᵉ eᵉ =
    equiv-Relaxed-Σ-Decompositionᵉ
      ( map-equiv-tr-Relaxed-Σ-Decompositionᵉ
        ( equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ
          ( fst-fibered-Relaxed-Σ-Decompositionᵉ Xᵉ)
          ( fst-fibered-Relaxed-Σ-Decompositionᵉ Yᵉ)
          ( eᵉ))
        ( snd-fibered-Relaxed-Σ-Decompositionᵉ Xᵉ))
      ( snd-fibered-Relaxed-Σ-Decompositionᵉ Yᵉ)

  equiv-fibered-Relaxed-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-fibered-Relaxed-Σ-Decompositionᵉ =
    Σᵉ ( equiv-fst-fibered-Relaxed-Σ-Decompositionᵉ)
      ( equiv-snd-fibered-Relaxed-Σ-Decompositionᵉ)

  fst-equiv-fibered-Relaxed-Σ-Decompositionᵉ :
    (eᵉ : equiv-fibered-Relaxed-Σ-Decompositionᵉ) →
    equiv-fst-fibered-Relaxed-Σ-Decompositionᵉ
  fst-equiv-fibered-Relaxed-Σ-Decompositionᵉ = pr1ᵉ

  snd-equiv-fibered-Relaxed-Σ-Decompositionᵉ :
    (eᵉ : equiv-fibered-Relaxed-Σ-Decompositionᵉ) →
    equiv-snd-fibered-Relaxed-Σ-Decompositionᵉ
      (fst-equiv-fibered-Relaxed-Σ-Decompositionᵉ eᵉ)
  snd-equiv-fibered-Relaxed-Σ-Decompositionᵉ = pr2ᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  ( Dᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = fst-fibered-Relaxed-Σ-Decompositionᵉ Dᵉ
    Yᵉ = snd-fibered-Relaxed-Σ-Decompositionᵉ Dᵉ

  is-torsorial-equiv-fibered-Relaxed-Σ-Decompositionᵉ :
    is-torsorialᵉ (equiv-fibered-Relaxed-Σ-Decompositionᵉ Dᵉ)
  is-torsorial-equiv-fibered-Relaxed-Σ-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Relaxed-Σ-Decompositionᵉ Xᵉ)
      ( Xᵉ ,ᵉ id-equiv-Relaxed-Σ-Decompositionᵉ Xᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Yᵉ))
        ( pairᵉ (indexing-type-Relaxed-Σ-Decompositionᵉ Yᵉ) id-equivᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-equiv-famᵉ
            ( cotype-Relaxed-Σ-Decompositionᵉ Yᵉ))
          ( pairᵉ
            ( cotype-Relaxed-Σ-Decompositionᵉ Yᵉ)
            ( id-equiv-famᵉ
              ( cotype-Relaxed-Σ-Decompositionᵉ Yᵉ)))
            ( is-torsorial-htpy-equivᵉ
              ( matching-correspondence-Relaxed-Σ-Decompositionᵉ Yᵉ))))

  id-equiv-fibered-Relaxed-Σ-Decompositionᵉ :
    equiv-fibered-Relaxed-Σ-Decompositionᵉ Dᵉ Dᵉ
  pr1ᵉ id-equiv-fibered-Relaxed-Σ-Decompositionᵉ =
    id-equiv-Relaxed-Σ-Decompositionᵉ Xᵉ
  pr1ᵉ (pr2ᵉ id-equiv-fibered-Relaxed-Σ-Decompositionᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ id-equiv-fibered-Relaxed-Σ-Decompositionᵉ)) xᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ id-equiv-fibered-Relaxed-Σ-Decompositionᵉ)) = refl-htpyᵉ

  equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (Dᵉ ＝ᵉ D'ᵉ) → equiv-fibered-Relaxed-Σ-Decompositionᵉ Dᵉ D'ᵉ
  equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ .Dᵉ reflᵉ =
    id-equiv-fibered-Relaxed-Σ-Decompositionᵉ

  is-equiv-equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ D'ᵉ)
  is-equiv-equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-fibered-Relaxed-Σ-Decompositionᵉ
      equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ

  extensionality-fibered-Relaxed-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (Dᵉ ＝ᵉ D'ᵉ) ≃ᵉ equiv-fibered-Relaxed-Σ-Decompositionᵉ Dᵉ D'ᵉ
  pr1ᵉ (extensionality-fibered-Relaxed-Σ-Decompositionᵉ D'ᵉ) =
    equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ D'ᵉ
  pr2ᵉ (extensionality-fibered-Relaxed-Σ-Decompositionᵉ D'ᵉ) =
    is-equiv-equiv-eq-fibered-Relaxed-Σ-Decompositionᵉ D'ᵉ

  eq-equiv-fibered-Relaxed-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (equiv-fibered-Relaxed-Σ-Decompositionᵉ Dᵉ D'ᵉ) → (Dᵉ ＝ᵉ D'ᵉ)
  eq-equiv-fibered-Relaxed-Σ-Decompositionᵉ D'ᵉ =
    map-inv-equivᵉ (extensionality-fibered-Relaxed-Σ-Decompositionᵉ D'ᵉ)
```

#### Characterization of identity type for displayed double Σ-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  (Yᵉ : displayed-Relaxed-Σ-Decompositionᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ Aᵉ)
  where

  equiv-fst-displayed-Relaxed-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ ⊔ l7ᵉ)
  equiv-fst-displayed-Relaxed-Σ-Decompositionᵉ =
    equiv-Relaxed-Σ-Decompositionᵉ
    ( fst-displayed-Relaxed-Σ-Decompositionᵉ Xᵉ)
    ( fst-displayed-Relaxed-Σ-Decompositionᵉ Yᵉ)

  equiv-snd-displayed-Relaxed-Σ-Decompositionᵉ :
    (eᵉ : equiv-fst-displayed-Relaxed-Σ-Decompositionᵉ) →
    UUᵉ (l2ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-snd-displayed-Relaxed-Σ-Decompositionᵉ eᵉ =
    ( xᵉ : indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ Xᵉ) →
    equiv-Relaxed-Σ-Decompositionᵉ
      ( map-equiv-tr-Relaxed-Σ-Decompositionᵉ
        ( equiv-cotype-equiv-Relaxed-Σ-Decompositionᵉ
          ( fst-displayed-Relaxed-Σ-Decompositionᵉ Xᵉ)
          ( fst-displayed-Relaxed-Σ-Decompositionᵉ Yᵉ)
          ( eᵉ)
          ( xᵉ))
        ( snd-displayed-Relaxed-Σ-Decompositionᵉ Xᵉ xᵉ))
      ( snd-displayed-Relaxed-Σ-Decompositionᵉ Yᵉ
        ( map-equiv-indexing-type-equiv-Relaxed-Σ-Decompositionᵉ
          ( fst-displayed-Relaxed-Σ-Decompositionᵉ Xᵉ)
          ( fst-displayed-Relaxed-Σ-Decompositionᵉ Yᵉ)
          ( eᵉ)
          ( xᵉ)))

  equiv-displayed-Relaxed-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-displayed-Relaxed-Σ-Decompositionᵉ =
    Σᵉ ( equiv-fst-displayed-Relaxed-Σ-Decompositionᵉ)
      ( equiv-snd-displayed-Relaxed-Σ-Decompositionᵉ)

  fst-equiv-displayed-Relaxed-Σ-Decompositionᵉ :
    (eᵉ : equiv-displayed-Relaxed-Σ-Decompositionᵉ) →
    equiv-fst-displayed-Relaxed-Σ-Decompositionᵉ
  fst-equiv-displayed-Relaxed-Σ-Decompositionᵉ = pr1ᵉ

  snd-equiv-displayed-Relaxed-Σ-Decompositionᵉ :
    (eᵉ : equiv-displayed-Relaxed-Σ-Decompositionᵉ) →
    equiv-snd-displayed-Relaxed-Σ-Decompositionᵉ
      ( fst-equiv-displayed-Relaxed-Σ-Decompositionᵉ eᵉ)
  snd-equiv-displayed-Relaxed-Σ-Decompositionᵉ = pr2ᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  ( disp-Dᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    f-Yᵉ = snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ

  is-torsorial-equiv-displayed-Relaxed-Σ-Decompositionᵉ :
    is-torsorialᵉ (equiv-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ)
  is-torsorial-equiv-displayed-Relaxed-Σ-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Relaxed-Σ-Decompositionᵉ Xᵉ)
      ( pairᵉ Xᵉ (id-equiv-Relaxed-Σ-Decompositionᵉ Xᵉ))
      ( is-contr-equivᵉ
        ( Π-total-famᵉ (λ xᵉ → _))
        ( inv-distributive-Π-Σᵉ)
        ( is-contr-Πᵉ
          ( λ xᵉ → is-torsorial-equiv-Relaxed-Σ-Decompositionᵉ (f-Yᵉ xᵉ))))

  id-equiv-displayed-Relaxed-Σ-Decompositionᵉ :
    equiv-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ disp-Dᵉ
  pr1ᵉ id-equiv-displayed-Relaxed-Σ-Decompositionᵉ =
    id-equiv-Relaxed-Σ-Decompositionᵉ Xᵉ
  pr1ᵉ (pr2ᵉ id-equiv-displayed-Relaxed-Σ-Decompositionᵉ xᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ id-equiv-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)) yᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ id-equiv-displayed-Relaxed-Σ-Decompositionᵉ xᵉ)) = refl-htpyᵉ

  equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ) → equiv-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ disp-D'ᵉ
  equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ .disp-Dᵉ reflᵉ =
    id-equiv-displayed-Relaxed-Σ-Decompositionᵉ

  is-equiv-equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ disp-D'ᵉ)
  is-equiv-equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-displayed-Relaxed-Σ-Decompositionᵉ
      equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ

  extensionality-displayed-Relaxed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ) ≃ᵉ equiv-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ disp-D'ᵉ
  pr1ᵉ (extensionality-displayed-Relaxed-Σ-Decompositionᵉ Dᵉ) =
    equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ Dᵉ
  pr2ᵉ (extensionality-displayed-Relaxed-Σ-Decompositionᵉ Dᵉ) =
    is-equiv-equiv-eq-displayed-Relaxed-Σ-Decompositionᵉ Dᵉ

  eq-equiv-displayed-Relaxed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (equiv-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ disp-D'ᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ)
  eq-equiv-displayed-Relaxed-Σ-Decompositionᵉ Dᵉ =
    map-inv-equivᵉ
      (extensionality-displayed-Relaxed-Σ-Decompositionᵉ Dᵉ)
```

#### Equivalence between fibered double relaxed Σ-recompositions and displayed double relaxed Σ-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (fib-Dᵉ : fibered-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    Yᵉ = cotype-fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    eᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ)
    Uᵉ = indexing-type-snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    Vᵉ = cotype-snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    fᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ)

  matching-correspondence-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ Σᵉ Uᵉ (λ uᵉ → Σᵉ (Vᵉ uᵉ) (λ vᵉ → Yᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ))))
  matching-correspondence-displayed-fibered-Relaxed-Σ-Decompositionᵉ =
    equivalence-reasoningᵉ
    Aᵉ ≃ᵉ Σᵉ Xᵉ Yᵉ byᵉ eᵉ
      ≃ᵉ Σᵉ ( Σᵉ Uᵉ Vᵉ) (λ uvᵉ → Yᵉ ((map-inv-equivᵉ fᵉ) uvᵉ))
        byᵉ inv-equivᵉ ( equiv-Σ-equiv-baseᵉ Yᵉ (inv-equivᵉ fᵉ))
      ≃ᵉ Σᵉ Uᵉ ( λ uᵉ → Σᵉ (Vᵉ uᵉ) (λ vᵉ → Yᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ))))
        byᵉ associative-Σᵉ Uᵉ Vᵉ (λ uvᵉ → Yᵉ (map-inv-equivᵉ fᵉ uvᵉ))

  map-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
    displayed-Relaxed-Σ-Decompositionᵉ l4ᵉ (l3ᵉ ⊔ l5ᵉ) l5ᵉ l3ᵉ Aᵉ
  pr1ᵉ (pr1ᵉ map-displayed-fibered-Relaxed-Σ-Decompositionᵉ) = Uᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ map-displayed-fibered-Relaxed-Σ-Decompositionᵉ)) uᵉ =
    Σᵉ ( Vᵉ uᵉ) ( λ vᵉ → Yᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ)))
  pr2ᵉ (pr2ᵉ (pr1ᵉ map-displayed-fibered-Relaxed-Σ-Decompositionᵉ)) =
    matching-correspondence-displayed-fibered-Relaxed-Σ-Decompositionᵉ
  pr1ᵉ (pr2ᵉ map-displayed-fibered-Relaxed-Σ-Decompositionᵉ uᵉ) = Vᵉ uᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ map-displayed-fibered-Relaxed-Σ-Decompositionᵉ uᵉ)) vᵉ =
    Yᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ))
  pr2ᵉ (pr2ᵉ (pr2ᵉ map-displayed-fibered-Relaxed-Σ-Decompositionᵉ uᵉ)) = id-equivᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (disp-Dᵉ : displayed-Relaxed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Mᵉ = indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    Nᵉ = cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    sᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ)
    Pᵉ = indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    Qᵉ = cotype-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    tᵉ = matching-correspondence-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ

  matching-correspondence-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ Σᵉ (Σᵉ Mᵉ Pᵉ) (λ (mᵉ ,ᵉ pᵉ) → Qᵉ mᵉ pᵉ)
  matching-correspondence-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ =
    equivalence-reasoningᵉ
    Aᵉ ≃ᵉ Σᵉ Mᵉ Nᵉ byᵉ sᵉ
      ≃ᵉ Σᵉ Mᵉ (λ mᵉ → Σᵉ (Pᵉ mᵉ) (Qᵉ mᵉ)) byᵉ equiv-Σᵉ (λ mᵉ → Σᵉ (Pᵉ mᵉ) (Qᵉ mᵉ)) id-equivᵉ tᵉ
      ≃ᵉ Σᵉ (Σᵉ Mᵉ Pᵉ) (λ (mᵉ ,ᵉ pᵉ) → Qᵉ mᵉ pᵉ)
      byᵉ inv-associative-Σᵉ
        ( Mᵉ)
        ( λ zᵉ → Pᵉ zᵉ)
        ( λ zᵉ → Qᵉ (pr1ᵉ zᵉ) (pr2ᵉ zᵉ))

  map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
    fibered-Relaxed-Σ-Decompositionᵉ (l2ᵉ ⊔ l4ᵉ) l5ᵉ l2ᵉ l4ᵉ Aᵉ
  pr1ᵉ (pr1ᵉ map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ) = Σᵉ Mᵉ Pᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ)) (mᵉ ,ᵉ pᵉ) =
    Qᵉ mᵉ pᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ)) =
    matching-correspondence-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ
  pr1ᵉ (pr2ᵉ map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ) = Mᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ)) = Pᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ)) = id-equivᵉ

module _
  {l1ᵉ lᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (fib-Dᵉ : fibered-Relaxed-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ)
  where

  private
    Xᵉ = indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    Yᵉ = cotype-fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    eᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ)
    Uᵉ = indexing-type-snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    Vᵉ = cotype-snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    fᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ)
    disp-Dᵉ = map-displayed-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    Mᵉ = indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    Nᵉ = cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    sᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ)
    Pᵉ = indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    Qᵉ = cotype-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    tᵉ = matching-correspondence-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ

    htpy-matching-correspondenceᵉ :
      map-equivᵉ
        ( equiv-Σᵉ Yᵉ (inv-equivᵉ fᵉ) (λ _ → id-equivᵉ) ∘eᵉ
          matching-correspondence-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ
            ( disp-Dᵉ)) ~ᵉ
      ( map-equivᵉ eᵉ)
    htpy-matching-correspondenceᵉ aᵉ =
      htpy-eq-equivᵉ
        ( right-inverse-law-equivᵉ (equiv-Σ-equiv-baseᵉ Yᵉ (inv-equivᵉ fᵉ)))
        ( map-equivᵉ eᵉ aᵉ)

  is-retraction-map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
    map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ
      ( map-displayed-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ) ＝ᵉ fib-Dᵉ
  is-retraction-map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ =
    eq-equiv-fibered-Relaxed-Σ-Decompositionᵉ
      ( map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ
        ( map-displayed-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ))
      ( fib-Dᵉ)
      ( ( ( inv-equivᵉ fᵉ) ,ᵉ
          ( ( λ xᵉ → id-equivᵉ) ,ᵉ
            ( htpy-matching-correspondenceᵉ))) ,ᵉ
        ( ( id-equivᵉ) ,ᵉ
          ( ( λ uᵉ → id-equivᵉ) ,ᵉ
            ( λ aᵉ → reflᵉ))))

module _
  {l1ᵉ lᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (disp-Dᵉ : displayed-Relaxed-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ)
  where

  private
    Mᵉ = indexing-type-fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    Nᵉ = cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    sᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ)
    Pᵉ = indexing-type-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    Qᵉ = cotype-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    tᵉ = matching-correspondence-snd-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    fib-Dᵉ = map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ disp-Dᵉ
    Xᵉ = indexing-type-fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    Yᵉ = cotype-fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    eᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( fst-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ)
    Uᵉ = indexing-type-snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    Vᵉ = cotype-snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ
    fᵉ = matching-correspondence-Relaxed-Σ-Decompositionᵉ
      ( snd-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ)

    htpy-matching-correspondenceᵉ :
      map-equivᵉ
        ( equiv-Σᵉ Nᵉ id-equivᵉ (inv-equivᵉ ∘ᵉ tᵉ) ∘eᵉ
          matching-correspondence-displayed-fibered-Relaxed-Σ-Decompositionᵉ
          (fib-Dᵉ)) ~ᵉ
      map-equivᵉ sᵉ
    htpy-matching-correspondenceᵉ xᵉ =
      ( apᵉ
        ( λ fᵉ → map-equivᵉ (equiv-totᵉ (inv-equivᵉ ∘ᵉ tᵉ)) fᵉ)
        ( map-inv-eq-transpose-equivᵉ
          ( associative-Σᵉ Mᵉ Pᵉ Yᵉ)
          ( invᵉ
            ( map-eq-transpose-equivᵉ
              ( equiv-Σ-equiv-baseᵉ Yᵉ (inv-equivᵉ id-equivᵉ))
              ( invᵉ
                ( map-eq-transpose-equivᵉ
                  ( associative-Σᵉ Mᵉ Pᵉ Yᵉ)
                  ( is-section-map-inv-associative-Σᵉ Mᵉ Pᵉ Yᵉ
                    ( map-equivᵉ (equiv-totᵉ tᵉ ∘eᵉ sᵉ) xᵉ)))))))) ∙ᵉ
      ( invᵉ
        ( preserves-comp-totᵉ
          ( map-equivᵉ ∘ᵉ tᵉ)
          ( map-inv-equivᵉ ∘ᵉ tᵉ)
          ( map-equivᵉ sᵉ xᵉ)) ∙ᵉ
        ( ( tot-htpyᵉ
            ( λ zᵉ → is-retraction-map-inv-equivᵉ (tᵉ zᵉ))
            ( map-equivᵉ sᵉ xᵉ)) ∙ᵉ
          ( tot-idᵉ
            ( λ zᵉ → cotype-fst-displayed-Relaxed-Σ-Decompositionᵉ disp-Dᵉ zᵉ)
            ( map-equivᵉ sᵉ xᵉ))))

  is-section-map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
    ( map-displayed-fibered-Relaxed-Σ-Decompositionᵉ
      {l1ᵉ} {lᵉ} {lᵉ} {lᵉ} {lᵉ} {Aᵉ} fib-Dᵉ) ＝ᵉ
    disp-Dᵉ
  is-section-map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ =
    eq-equiv-displayed-Relaxed-Σ-Decompositionᵉ
      ( map-displayed-fibered-Relaxed-Σ-Decompositionᵉ fib-Dᵉ)
      ( disp-Dᵉ)
      ( ( ( id-equivᵉ) ,ᵉ
          ( ( inv-equivᵉ ∘ᵉ tᵉ) ,ᵉ
            ( htpy-matching-correspondenceᵉ))) ,ᵉ
        ( λ (mᵉ : Mᵉ) →
          ( ( id-equivᵉ) ,ᵉ
            ( ( λ (pᵉ : Pᵉ mᵉ) → id-equivᵉ) ,ᵉ
              ( refl-htpyᵉ)))))

is-equiv-map-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ lᵉ : Level} → {Aᵉ : UUᵉ l1ᵉ} →
  is-equivᵉ
    ( map-displayed-fibered-Relaxed-Σ-Decompositionᵉ {l1ᵉ} {lᵉ} {lᵉ} {lᵉ} {lᵉ} {Aᵉ})
is-equiv-map-displayed-fibered-Relaxed-Σ-Decompositionᵉ =
  is-equiv-is-invertibleᵉ
    ( map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ)
    ( is-section-map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ)
    ( is-retraction-map-inv-displayed-fibered-Relaxed-Σ-Decompositionᵉ)

equiv-displayed-fibered-Relaxed-Σ-Decompositionᵉ :
  {l1ᵉ lᵉ : Level} → {Aᵉ : UUᵉ l1ᵉ} →
  fibered-Relaxed-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ ≃ᵉ
  displayed-Relaxed-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ
pr1ᵉ equiv-displayed-fibered-Relaxed-Σ-Decompositionᵉ =
  map-displayed-fibered-Relaxed-Σ-Decompositionᵉ
pr2ᵉ equiv-displayed-fibered-Relaxed-Σ-Decompositionᵉ =
  is-equiv-map-displayed-fibered-Relaxed-Σ-Decompositionᵉ
```