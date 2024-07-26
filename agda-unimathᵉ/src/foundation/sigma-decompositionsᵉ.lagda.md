# Σ-decompositions of types

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.sigma-decompositionsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.inhabited-typesᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.setsᵉ
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

Aᵉ **Σ-decomposition**ᵉ ofᵉ aᵉ typeᵉ `A`ᵉ consistsᵉ ofᵉ aᵉ typeᵉ `X`ᵉ andᵉ aᵉ familyᵉ ofᵉ
inhabitedᵉ typesᵉ `Yᵉ x`ᵉ indexedᵉ byᵉ `xᵉ : A`ᵉ equippedᵉ with anᵉ equivalenceᵉ
`Aᵉ ≃ᵉ Σᵉ Xᵉ Y`.ᵉ Theᵉ typeᵉ `X`ᵉ isᵉ calledᵉ theᵉ indexingᵉ typeᵉ ofᵉ theᵉ Σ-decomposition,ᵉ
theᵉ elementsᵉ ofᵉ `Yᵉ x`ᵉ areᵉ calledᵉ theᵉ cotypesᵉ ofᵉ theᵉ Σ-decomposition,ᵉ andᵉ theᵉ
equivalenceᵉ `Aᵉ ≃ᵉ Σᵉ Xᵉ Y`ᵉ isᵉ theᵉ matchingᵉ correspondenceᵉ ofᵉ theᵉ Σ-decomposition.ᵉ

Noteᵉ thatᵉ typesᵉ mayᵉ haveᵉ manyᵉ Σ-decompositions.ᵉ Theᵉ typeᵉ ofᵉ Σ-decompositionsᵉ ofᵉ
theᵉ unitᵉ type,ᵉ forᵉ instance,ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ ofᵉ allᵉ pointedᵉ connectedᵉ
types.ᵉ Alternatively,ᵉ weᵉ mayᵉ thinkᵉ ofᵉ theᵉ typeᵉ ofᵉ Σ-decompositionsᵉ ofᵉ theᵉ unitᵉ
typeᵉ asᵉ theᵉ typeᵉ ofᵉ higherᵉ groupoidᵉ structuresᵉ onᵉ aᵉ point,ᵉ i.e.,ᵉ theᵉ typeᵉ ofᵉ
higherᵉ groupᵉ structures.ᵉ

Weᵉ mayᵉ restrictᵉ to Σ-decompositionsᵉ where theᵉ indexingᵉ typeᵉ isᵉ in aᵉ givenᵉ
subuniverse,ᵉ suchᵉ asᵉ theᵉ subuniverseᵉ ofᵉ setsᵉ orᵉ theᵉ subuniverseᵉ ofᵉ finiteᵉ sets.ᵉ
Forᵉ instance,ᵉ theᵉ typeᵉ ofᵉ set-indexedᵉ Σ-decompositionsᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ
equivalentᵉ to theᵉ typeᵉ ofᵉ equivalenceᵉ relationsᵉ onᵉ `A`.ᵉ

## Definitions

### General Σ-decompositions

```agda
Σ-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ =
  Σᵉ ( UUᵉ l2ᵉ)
    ( λ Xᵉ →
      Σᵉ ( Fam-Inhabited-Typesᵉ l3ᵉ Xᵉ)
        ( λ Yᵉ → Aᵉ ≃ᵉ total-Fam-Inhabited-Typesᵉ Yᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  indexing-type-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-Σ-Decompositionᵉ = pr1ᵉ Dᵉ

  inhabited-cotype-Σ-Decompositionᵉ :
    Fam-Inhabited-Typesᵉ l3ᵉ indexing-type-Σ-Decompositionᵉ
  inhabited-cotype-Σ-Decompositionᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  cotype-Σ-Decompositionᵉ : indexing-type-Σ-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-Σ-Decompositionᵉ =
    type-Fam-Inhabited-Typesᵉ inhabited-cotype-Σ-Decompositionᵉ

  is-inhabited-cotype-Σ-Decompositionᵉ :
    (xᵉ : indexing-type-Σ-Decompositionᵉ) →
    is-inhabitedᵉ (cotype-Σ-Decompositionᵉ xᵉ)
  is-inhabited-cotype-Σ-Decompositionᵉ xᵉ =
    is-inhabited-type-Inhabited-Typeᵉ (inhabited-cotype-Σ-Decompositionᵉ xᵉ)

  matching-correspondence-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ Σᵉ indexing-type-Σ-Decompositionᵉ cotype-Σ-Decompositionᵉ
  matching-correspondence-Σ-Decompositionᵉ = pr2ᵉ (pr2ᵉ Dᵉ)

  map-matching-correspondence-Σ-Decompositionᵉ :
    Aᵉ → Σᵉ indexing-type-Σ-Decompositionᵉ cotype-Σ-Decompositionᵉ
  map-matching-correspondence-Σ-Decompositionᵉ =
    map-equivᵉ matching-correspondence-Σ-Decompositionᵉ

  is-inhabited-indexing-type-inhabited-Σ-Decompositionᵉ :
    (pᵉ : is-inhabitedᵉ Aᵉ) → (is-inhabitedᵉ (indexing-type-Σ-Decompositionᵉ))
  is-inhabited-indexing-type-inhabited-Σ-Decompositionᵉ pᵉ =
    map-is-inhabitedᵉ (pr1ᵉ ∘ᵉ map-matching-correspondence-Σ-Decompositionᵉ) pᵉ

  inhabited-indexing-type-inhabited-Σ-Decompositionᵉ :
    (pᵉ : is-inhabitedᵉ Aᵉ) → (Inhabited-Typeᵉ l2ᵉ)
  pr1ᵉ (inhabited-indexing-type-inhabited-Σ-Decompositionᵉ pᵉ) =
    indexing-type-Σ-Decompositionᵉ
  pr2ᵉ (inhabited-indexing-type-inhabited-Σ-Decompositionᵉ pᵉ) =
    is-inhabited-indexing-type-inhabited-Σ-Decompositionᵉ pᵉ

  is-inhabited-base-is-inhabited-indexing-type-Σ-Decompositionᵉ :
    (is-inhabitedᵉ (indexing-type-Σ-Decompositionᵉ)) → (is-inhabitedᵉ Aᵉ)
  is-inhabited-base-is-inhabited-indexing-type-Σ-Decompositionᵉ pᵉ =
    map-is-inhabitedᵉ
      ( map-inv-equivᵉ matching-correspondence-Σ-Decompositionᵉ)
      ( is-inhabited-Σᵉ pᵉ is-inhabited-cotype-Σ-Decompositionᵉ)
```

### Set-indexed Σ-decompositions

```agda
Set-Indexed-Σ-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ)
Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ =
  Σᵉ ( Setᵉ l2ᵉ)
    ( λ Xᵉ →
      Σᵉ ( Fam-Inhabited-Typesᵉ l3ᵉ (type-Setᵉ Xᵉ))
        ( λ Yᵉ → Aᵉ ≃ᵉ total-Fam-Inhabited-Typesᵉ Yᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Dᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  indexing-set-Set-Indexed-Σ-Decompositionᵉ : Setᵉ l2ᵉ
  indexing-set-Set-Indexed-Σ-Decompositionᵉ = pr1ᵉ Dᵉ

  indexing-type-Set-Indexed-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-Set-Indexed-Σ-Decompositionᵉ =
    type-Setᵉ indexing-set-Set-Indexed-Σ-Decompositionᵉ

  inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ :
    indexing-type-Set-Indexed-Σ-Decompositionᵉ → Inhabited-Typeᵉ l3ᵉ
  inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ = pr1ᵉ (pr2ᵉ Dᵉ)

  cotype-Set-Indexed-Σ-Decompositionᵉ :
    indexing-type-Set-Indexed-Σ-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-Set-Indexed-Σ-Decompositionᵉ xᵉ =
    type-Inhabited-Typeᵉ (inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ xᵉ)

  is-inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ :
    (xᵉ : indexing-type-Set-Indexed-Σ-Decompositionᵉ) →
    is-inhabitedᵉ (cotype-Set-Indexed-Σ-Decompositionᵉ xᵉ)
  is-inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ xᵉ =
    is-inhabited-type-Inhabited-Typeᵉ
      ( inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ xᵉ)

  matching-correspondence-Set-Indexed-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ
    Σᵉ indexing-type-Set-Indexed-Σ-Decompositionᵉ
      cotype-Set-Indexed-Σ-Decompositionᵉ
  matching-correspondence-Set-Indexed-Σ-Decompositionᵉ = pr2ᵉ (pr2ᵉ Dᵉ)

  map-matching-correspondence-Set-Indexed-Σ-Decompositionᵉ :
    Aᵉ →
    Σᵉ indexing-type-Set-Indexed-Σ-Decompositionᵉ
      cotype-Set-Indexed-Σ-Decompositionᵉ
  map-matching-correspondence-Set-Indexed-Σ-Decompositionᵉ =
    map-equivᵉ matching-correspondence-Set-Indexed-Σ-Decompositionᵉ

  index-Set-Indexed-Σ-Decompositionᵉ :
    Aᵉ → indexing-type-Set-Indexed-Σ-Decompositionᵉ
  index-Set-Indexed-Σ-Decompositionᵉ aᵉ =
    pr1ᵉ (map-matching-correspondence-Set-Indexed-Σ-Decompositionᵉ aᵉ)
```

### Fibered double Σ-decompositions

```agda
fibered-Σ-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  Σᵉ (Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
    ( λ Dᵉ → Σ-Decompositionᵉ l4ᵉ l5ᵉ (indexing-type-Σ-Decompositionᵉ Dᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  fst-fibered-Σ-Decompositionᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ
  fst-fibered-Σ-Decompositionᵉ = pr1ᵉ Xᵉ

  indexing-type-fst-fibered-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-fst-fibered-Σ-Decompositionᵉ =
    indexing-type-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ

  inhabited-cotype-fst-fibered-Σ-Decompositionᵉ :
    indexing-type-fst-fibered-Σ-Decompositionᵉ → Inhabited-Typeᵉ l3ᵉ
  inhabited-cotype-fst-fibered-Σ-Decompositionᵉ =
    inhabited-cotype-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ

  cotype-fst-fibered-Σ-Decompositionᵉ :
    indexing-type-fst-fibered-Σ-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-fst-fibered-Σ-Decompositionᵉ =
    cotype-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ

  matching-correspondence-fst-fibered-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ
    Σᵉ (indexing-type-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ)
      (cotype-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ)
  matching-correspondence-fst-fibered-Σ-Decompositionᵉ =
    matching-correspondence-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ

  map-matching-correspondence-fst-fibered-Σ-Decompositionᵉ :
    Aᵉ →
    Σᵉ (indexing-type-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ)
      (cotype-Σ-Decompositionᵉ fst-fibered-Σ-Decompositionᵉ)
  map-matching-correspondence-fst-fibered-Σ-Decompositionᵉ =
    map-matching-correspondence-Σ-Decompositionᵉ
      fst-fibered-Σ-Decompositionᵉ

  snd-fibered-Σ-Decompositionᵉ :
      Σ-Decompositionᵉ l4ᵉ l5ᵉ indexing-type-fst-fibered-Σ-Decompositionᵉ
  snd-fibered-Σ-Decompositionᵉ = pr2ᵉ Xᵉ

  indexing-type-snd-fibered-Σ-Decompositionᵉ : UUᵉ l4ᵉ
  indexing-type-snd-fibered-Σ-Decompositionᵉ =
    indexing-type-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ

  inhabited-cotype-snd-fibered-Σ-Decompositionᵉ :
    indexing-type-snd-fibered-Σ-Decompositionᵉ → Inhabited-Typeᵉ l5ᵉ
  inhabited-cotype-snd-fibered-Σ-Decompositionᵉ =
    inhabited-cotype-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ

  cotype-snd-fibered-Σ-Decompositionᵉ :
    indexing-type-snd-fibered-Σ-Decompositionᵉ → UUᵉ l5ᵉ
  cotype-snd-fibered-Σ-Decompositionᵉ =
    cotype-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ

  matching-correspondence-snd-fibered-Σ-Decompositionᵉ :
    indexing-type-fst-fibered-Σ-Decompositionᵉ ≃ᵉ
    Σᵉ (indexing-type-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ)
      (cotype-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ)
  matching-correspondence-snd-fibered-Σ-Decompositionᵉ =
    matching-correspondence-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ

  map-matching-correspondence-snd-fibered-Σ-Decompositionᵉ :
    indexing-type-fst-fibered-Σ-Decompositionᵉ →
    Σᵉ (indexing-type-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ)
      (cotype-Σ-Decompositionᵉ snd-fibered-Σ-Decompositionᵉ)
  map-matching-correspondence-snd-fibered-Σ-Decompositionᵉ =
    map-matching-correspondence-Σ-Decompositionᵉ
      snd-fibered-Σ-Decompositionᵉ
```

#### Displayed double Σ-decompositions

```agda
displayed-Σ-Decompositionᵉ :
  {l1ᵉ : Level} (l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level) (Aᵉ : UUᵉ l1ᵉ) →
  UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ ⊔ lsuc l3ᵉ ⊔ lsuc l4ᵉ ⊔ lsuc l5ᵉ)
displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ =
  ( Σᵉ (Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  ( λ Dᵉ →
    (uᵉ : indexing-type-Σ-Decompositionᵉ Dᵉ) →
    Σ-Decompositionᵉ l4ᵉ l5ᵉ (cotype-Σ-Decompositionᵉ Dᵉ uᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  fst-displayed-Σ-Decompositionᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ
  fst-displayed-Σ-Decompositionᵉ = pr1ᵉ Xᵉ

  indexing-type-fst-displayed-Σ-Decompositionᵉ : UUᵉ l2ᵉ
  indexing-type-fst-displayed-Σ-Decompositionᵉ =
    indexing-type-Σ-Decompositionᵉ fst-displayed-Σ-Decompositionᵉ

  inhabited-cotype-fst-displayed-Σ-Decompositionᵉ :
    indexing-type-fst-displayed-Σ-Decompositionᵉ → Inhabited-Typeᵉ l3ᵉ
  inhabited-cotype-fst-displayed-Σ-Decompositionᵉ =
    inhabited-cotype-Σ-Decompositionᵉ fst-displayed-Σ-Decompositionᵉ

  cotype-fst-displayed-Σ-Decompositionᵉ :
    indexing-type-fst-displayed-Σ-Decompositionᵉ → UUᵉ l3ᵉ
  cotype-fst-displayed-Σ-Decompositionᵉ =
    cotype-Σ-Decompositionᵉ fst-displayed-Σ-Decompositionᵉ

  matching-correspondence-fst-displayed-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ
    Σᵉ (indexing-type-Σ-Decompositionᵉ fst-displayed-Σ-Decompositionᵉ)
      (cotype-Σ-Decompositionᵉ fst-displayed-Σ-Decompositionᵉ)
  matching-correspondence-fst-displayed-Σ-Decompositionᵉ =
    matching-correspondence-Σ-Decompositionᵉ
      fst-displayed-Σ-Decompositionᵉ

  map-matching-correspondence-fst-displayed-Σ-Decompositionᵉ :
    Aᵉ →
    Σᵉ (indexing-type-Σ-Decompositionᵉ fst-displayed-Σ-Decompositionᵉ)
      (cotype-Σ-Decompositionᵉ fst-displayed-Σ-Decompositionᵉ)
  map-matching-correspondence-fst-displayed-Σ-Decompositionᵉ =
    map-matching-correspondence-Σ-Decompositionᵉ
      fst-displayed-Σ-Decompositionᵉ

  snd-displayed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Σ-Decompositionᵉ) →
    Σ-Decompositionᵉ l4ᵉ l5ᵉ (cotype-fst-displayed-Σ-Decompositionᵉ xᵉ)
  snd-displayed-Σ-Decompositionᵉ = pr2ᵉ Xᵉ

  indexing-type-snd-displayed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Σ-Decompositionᵉ) →
    UUᵉ l4ᵉ
  indexing-type-snd-displayed-Σ-Decompositionᵉ xᵉ =
    indexing-type-Σ-Decompositionᵉ (snd-displayed-Σ-Decompositionᵉ xᵉ)

  inhabited-cotype-snd-displayed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Σ-Decompositionᵉ) →
    indexing-type-snd-displayed-Σ-Decompositionᵉ xᵉ → Inhabited-Typeᵉ l5ᵉ
  inhabited-cotype-snd-displayed-Σ-Decompositionᵉ xᵉ =
    inhabited-cotype-Σ-Decompositionᵉ (snd-displayed-Σ-Decompositionᵉ xᵉ)

  cotype-snd-displayed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Σ-Decompositionᵉ) →
    indexing-type-snd-displayed-Σ-Decompositionᵉ xᵉ →
    UUᵉ l5ᵉ
  cotype-snd-displayed-Σ-Decompositionᵉ xᵉ =
    cotype-Σ-Decompositionᵉ (snd-displayed-Σ-Decompositionᵉ xᵉ)

  matching-correspondence-snd-displayed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Σ-Decompositionᵉ) →
    ( cotype-fst-displayed-Σ-Decompositionᵉ xᵉ ≃ᵉ
      Σᵉ ( indexing-type-snd-displayed-Σ-Decompositionᵉ xᵉ)
        ( cotype-snd-displayed-Σ-Decompositionᵉ xᵉ))
  matching-correspondence-snd-displayed-Σ-Decompositionᵉ xᵉ =
    matching-correspondence-Σ-Decompositionᵉ
      ( snd-displayed-Σ-Decompositionᵉ xᵉ)

  map-matching-correspondence-snd-displayed-Σ-Decompositionᵉ :
    ( xᵉ : indexing-type-fst-displayed-Σ-Decompositionᵉ) →
    cotype-fst-displayed-Σ-Decompositionᵉ xᵉ →
    Σᵉ ( indexing-type-snd-displayed-Σ-Decompositionᵉ xᵉ)
      ( cotype-snd-displayed-Σ-Decompositionᵉ xᵉ)
  map-matching-correspondence-snd-displayed-Σ-Decompositionᵉ xᵉ =
    map-matching-correspondence-Σ-Decompositionᵉ
      ( snd-displayed-Σ-Decompositionᵉ xᵉ)
```

## Properties

### Characterization of equality of Σ-decompositions

```agda
equiv-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) (Yᵉ : Σ-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
equiv-Σ-Decompositionᵉ Xᵉ Yᵉ =
  Σᵉ ( indexing-type-Σ-Decompositionᵉ Xᵉ ≃ᵉ indexing-type-Σ-Decompositionᵉ Yᵉ)
    ( λ eᵉ →
      Σᵉ ( (xᵉ : indexing-type-Σ-Decompositionᵉ Xᵉ) →
          cotype-Σ-Decompositionᵉ Xᵉ xᵉ ≃ᵉ cotype-Σ-Decompositionᵉ Yᵉ (map-equivᵉ eᵉ xᵉ))
        ( λ fᵉ →
          ( ( map-equivᵉ (equiv-Σᵉ (cotype-Σ-Decompositionᵉ Yᵉ) eᵉ fᵉ)) ∘ᵉ
            ( map-matching-correspondence-Σ-Decompositionᵉ Xᵉ)) ~ᵉ
          ( map-matching-correspondence-Σ-Decompositionᵉ Yᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) (Yᵉ : Σ-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ)
  (eᵉ : equiv-Σ-Decompositionᵉ Xᵉ Yᵉ)
  where

  equiv-indexing-type-equiv-Σ-Decompositionᵉ :
    indexing-type-Σ-Decompositionᵉ Xᵉ ≃ᵉ indexing-type-Σ-Decompositionᵉ Yᵉ
  equiv-indexing-type-equiv-Σ-Decompositionᵉ = pr1ᵉ eᵉ

  map-equiv-indexing-type-equiv-Σ-Decompositionᵉ :
    indexing-type-Σ-Decompositionᵉ Xᵉ → indexing-type-Σ-Decompositionᵉ Yᵉ
  map-equiv-indexing-type-equiv-Σ-Decompositionᵉ =
    map-equivᵉ equiv-indexing-type-equiv-Σ-Decompositionᵉ

  equiv-cotype-equiv-Σ-Decompositionᵉ :
    (xᵉ : indexing-type-Σ-Decompositionᵉ Xᵉ) →
    cotype-Σ-Decompositionᵉ Xᵉ xᵉ ≃ᵉ
    cotype-Σ-Decompositionᵉ Yᵉ (map-equiv-indexing-type-equiv-Σ-Decompositionᵉ xᵉ)
  equiv-cotype-equiv-Σ-Decompositionᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  map-equiv-cotype-equiv-Σ-Decompositionᵉ :
    (xᵉ : indexing-type-Σ-Decompositionᵉ Xᵉ) →
    cotype-Σ-Decompositionᵉ Xᵉ xᵉ →
    cotype-Σ-Decompositionᵉ Yᵉ (map-equiv-indexing-type-equiv-Σ-Decompositionᵉ xᵉ)
  map-equiv-cotype-equiv-Σ-Decompositionᵉ xᵉ =
    map-equivᵉ (equiv-cotype-equiv-Σ-Decompositionᵉ xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  id-equiv-Σ-Decompositionᵉ : equiv-Σ-Decompositionᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-Σ-Decompositionᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-Σ-Decompositionᵉ) xᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-Σ-Decompositionᵉ) = refl-htpyᵉ

  is-torsorial-equiv-Σ-Decompositionᵉ :
    is-torsorialᵉ (equiv-Σ-Decompositionᵉ Xᵉ)
  is-torsorial-equiv-Σ-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equivᵉ (indexing-type-Σ-Decompositionᵉ Xᵉ))
      ( pairᵉ (indexing-type-Σ-Decompositionᵉ Xᵉ) id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equiv-Fam-Inhabited-Typesᵉ
          ( inhabited-cotype-Σ-Decompositionᵉ Xᵉ))
        ( pairᵉ
          ( inhabited-cotype-Σ-Decompositionᵉ Xᵉ)
          ( id-equiv-Fam-Inhabited-Typesᵉ (inhabited-cotype-Σ-Decompositionᵉ Xᵉ)))
        ( is-torsorial-htpy-equivᵉ
          ( matching-correspondence-Σ-Decompositionᵉ Xᵉ)))

  equiv-eq-Σ-Decompositionᵉ :
    (Yᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) → (Xᵉ ＝ᵉ Yᵉ) → equiv-Σ-Decompositionᵉ Xᵉ Yᵉ
  equiv-eq-Σ-Decompositionᵉ .Xᵉ reflᵉ = id-equiv-Σ-Decompositionᵉ

  is-equiv-equiv-eq-Σ-Decompositionᵉ :
    (Yᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) → is-equivᵉ (equiv-eq-Σ-Decompositionᵉ Yᵉ)
  is-equiv-equiv-eq-Σ-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Σ-Decompositionᵉ
      equiv-eq-Σ-Decompositionᵉ

  extensionality-Σ-Decompositionᵉ :
    (Yᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) → (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Σ-Decompositionᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Σ-Decompositionᵉ Yᵉ) = equiv-eq-Σ-Decompositionᵉ Yᵉ
  pr2ᵉ (extensionality-Σ-Decompositionᵉ Yᵉ) = is-equiv-equiv-eq-Σ-Decompositionᵉ Yᵉ

  eq-equiv-Σ-Decompositionᵉ :
    (Yᵉ : Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) → equiv-Σ-Decompositionᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-Σ-Decompositionᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-Σ-Decompositionᵉ Yᵉ)
```

### Invariance of Σ-decompositions under equivalences

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  equiv-tr-Σ-Decompositionᵉ :
    {l3ᵉ l4ᵉ : Level} → Σ-Decompositionᵉ l3ᵉ l4ᵉ Aᵉ ≃ᵉ Σ-Decompositionᵉ l3ᵉ l4ᵉ Bᵉ
  equiv-tr-Σ-Decompositionᵉ =
    equiv-totᵉ
      ( λ Xᵉ →
        equiv-totᵉ
          ( λ Yᵉ →
            equiv-precomp-equivᵉ (inv-equivᵉ eᵉ) (total-Fam-Inhabited-Typesᵉ Yᵉ)))

  map-equiv-tr-Σ-Decompositionᵉ :
    {l3ᵉ l4ᵉ : Level} → Σ-Decompositionᵉ l3ᵉ l4ᵉ Aᵉ → Σ-Decompositionᵉ l3ᵉ l4ᵉ Bᵉ
  map-equiv-tr-Σ-Decompositionᵉ = map-equivᵉ equiv-tr-Σ-Decompositionᵉ
```

### Characterization of equality of set-indexed Σ-decompositions

```agda
equiv-Set-Indexed-Σ-Decompositionᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (Xᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  (Yᵉ : Set-Indexed-Σ-Decompositionᵉ l4ᵉ l5ᵉ Aᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ)
equiv-Set-Indexed-Σ-Decompositionᵉ Xᵉ Yᵉ =
  Σᵉ ( indexing-type-Set-Indexed-Σ-Decompositionᵉ Xᵉ ≃ᵉ
      indexing-type-Set-Indexed-Σ-Decompositionᵉ Yᵉ)
    ( λ eᵉ →
      Σᵉ ( (xᵉ : indexing-type-Set-Indexed-Σ-Decompositionᵉ Xᵉ) →
          cotype-Set-Indexed-Σ-Decompositionᵉ Xᵉ xᵉ ≃ᵉ
          cotype-Set-Indexed-Σ-Decompositionᵉ Yᵉ (map-equivᵉ eᵉ xᵉ))
        ( λ fᵉ →
          ( ( map-equivᵉ (equiv-Σᵉ (cotype-Set-Indexed-Σ-Decompositionᵉ Yᵉ) eᵉ fᵉ)) ∘ᵉ
            ( map-matching-correspondence-Set-Indexed-Σ-Decompositionᵉ Xᵉ)) ~ᵉ
          ( map-matching-correspondence-Set-Indexed-Σ-Decompositionᵉ Yᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ)
  where

  id-equiv-Set-Indexed-Σ-Decompositionᵉ : equiv-Set-Indexed-Σ-Decompositionᵉ Xᵉ Xᵉ
  pr1ᵉ id-equiv-Set-Indexed-Σ-Decompositionᵉ = id-equivᵉ
  pr1ᵉ (pr2ᵉ id-equiv-Set-Indexed-Σ-Decompositionᵉ) xᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ id-equiv-Set-Indexed-Σ-Decompositionᵉ) = refl-htpyᵉ

  is-torsorial-equiv-Set-Indexed-Σ-Decompositionᵉ :
    is-torsorialᵉ (equiv-Set-Indexed-Σ-Decompositionᵉ Xᵉ)
  is-torsorial-equiv-Set-Indexed-Σ-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Setᵉ (indexing-set-Set-Indexed-Σ-Decompositionᵉ Xᵉ))
      ( pairᵉ (indexing-set-Set-Indexed-Σ-Decompositionᵉ Xᵉ) id-equivᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equiv-Fam-Inhabited-Typesᵉ
          ( inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ Xᵉ))
        ( pairᵉ
          ( inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ Xᵉ)
          ( id-equiv-Fam-Inhabited-Typesᵉ
            ( inhabited-cotype-Set-Indexed-Σ-Decompositionᵉ Xᵉ)))
        ( is-torsorial-htpy-equivᵉ
          ( matching-correspondence-Set-Indexed-Σ-Decompositionᵉ Xᵉ)))

  equiv-eq-Set-Indexed-Σ-Decompositionᵉ :
    (Yᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) → equiv-Set-Indexed-Σ-Decompositionᵉ Xᵉ Yᵉ
  equiv-eq-Set-Indexed-Σ-Decompositionᵉ .Xᵉ reflᵉ =
    id-equiv-Set-Indexed-Σ-Decompositionᵉ

  is-equiv-equiv-eq-Set-Indexed-Σ-Decompositionᵉ :
    (Yᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-Set-Indexed-Σ-Decompositionᵉ Yᵉ)
  is-equiv-equiv-eq-Set-Indexed-Σ-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-Set-Indexed-Σ-Decompositionᵉ
      equiv-eq-Set-Indexed-Σ-Decompositionᵉ

  extensionality-Set-Indexed-Σ-Decompositionᵉ :
    (Yᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    (Xᵉ ＝ᵉ Yᵉ) ≃ᵉ equiv-Set-Indexed-Σ-Decompositionᵉ Xᵉ Yᵉ
  pr1ᵉ (extensionality-Set-Indexed-Σ-Decompositionᵉ Yᵉ) =
    equiv-eq-Set-Indexed-Σ-Decompositionᵉ Yᵉ
  pr2ᵉ (extensionality-Set-Indexed-Σ-Decompositionᵉ Yᵉ) =
    is-equiv-equiv-eq-Set-Indexed-Σ-Decompositionᵉ Yᵉ

  eq-equiv-Set-Indexed-Σ-Decompositionᵉ :
    (Yᵉ : Set-Indexed-Σ-Decompositionᵉ l2ᵉ l3ᵉ Aᵉ) →
    equiv-Set-Indexed-Σ-Decompositionᵉ Xᵉ Yᵉ → (Xᵉ ＝ᵉ Yᵉ)
  eq-equiv-Set-Indexed-Σ-Decompositionᵉ Yᵉ =
    map-inv-equivᵉ (extensionality-Set-Indexed-Σ-Decompositionᵉ Yᵉ)
```

### Iterated Σ-decompositions

#### Characterization of identity type for fibered double Σ-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  (Yᵉ : fibered-Σ-Decompositionᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ Aᵉ)
  where

  equiv-fst-fibered-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ ⊔ l7ᵉ)
  equiv-fst-fibered-Σ-Decompositionᵉ =
    equiv-Σ-Decompositionᵉ
    ( fst-fibered-Σ-Decompositionᵉ Xᵉ)
    ( fst-fibered-Σ-Decompositionᵉ Yᵉ)

  equiv-snd-fibered-Σ-Decompositionᵉ :
    (eᵉ : equiv-fst-fibered-Σ-Decompositionᵉ) →
    UUᵉ (l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-snd-fibered-Σ-Decompositionᵉ eᵉ =
    equiv-Σ-Decompositionᵉ
      ( map-equiv-tr-Σ-Decompositionᵉ
        ( equiv-indexing-type-equiv-Σ-Decompositionᵉ
          ( fst-fibered-Σ-Decompositionᵉ Xᵉ)
          ( fst-fibered-Σ-Decompositionᵉ Yᵉ)
          ( eᵉ))
        ( snd-fibered-Σ-Decompositionᵉ Xᵉ))
      ( snd-fibered-Σ-Decompositionᵉ Yᵉ)

  equiv-fibered-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-fibered-Σ-Decompositionᵉ =
    Σᵉ ( equiv-fst-fibered-Σ-Decompositionᵉ)
      ( equiv-snd-fibered-Σ-Decompositionᵉ)

  fst-equiv-fibered-Σ-Decompositionᵉ :
    (eᵉ : equiv-fibered-Σ-Decompositionᵉ) →
    equiv-fst-fibered-Σ-Decompositionᵉ
  fst-equiv-fibered-Σ-Decompositionᵉ = pr1ᵉ

  snd-equiv-fibered-Σ-Decompositionᵉ :
    (eᵉ : equiv-fibered-Σ-Decompositionᵉ) →
    equiv-snd-fibered-Σ-Decompositionᵉ
      (fst-equiv-fibered-Σ-Decompositionᵉ eᵉ)
  snd-equiv-fibered-Σ-Decompositionᵉ = pr2ᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  ( Dᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = fst-fibered-Σ-Decompositionᵉ Dᵉ
    Yᵉ = snd-fibered-Σ-Decompositionᵉ Dᵉ

  is-torsorial-equiv-fibered-Σ-Decompositionᵉ :
    is-torsorialᵉ (equiv-fibered-Σ-Decompositionᵉ Dᵉ)
  is-torsorial-equiv-fibered-Σ-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Σ-Decompositionᵉ Xᵉ)
      ( Xᵉ ,ᵉ id-equiv-Σ-Decompositionᵉ Xᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-equivᵉ (indexing-type-Σ-Decompositionᵉ Yᵉ))
        ( pairᵉ (indexing-type-Σ-Decompositionᵉ Yᵉ) id-equivᵉ)
        ( is-torsorial-Eq-structureᵉ
          ( is-torsorial-equiv-Fam-Inhabited-Typesᵉ
            ( inhabited-cotype-Σ-Decompositionᵉ Yᵉ))
          ( pairᵉ
            ( inhabited-cotype-Σ-Decompositionᵉ Yᵉ)
            ( id-equiv-Fam-Inhabited-Typesᵉ
              ( inhabited-cotype-Σ-Decompositionᵉ Yᵉ)))
            ( is-torsorial-htpy-equivᵉ
              ( matching-correspondence-Σ-Decompositionᵉ Yᵉ))))

  id-equiv-fibered-Σ-Decompositionᵉ :
    equiv-fibered-Σ-Decompositionᵉ Dᵉ Dᵉ
  pr1ᵉ id-equiv-fibered-Σ-Decompositionᵉ = id-equiv-Σ-Decompositionᵉ Xᵉ
  pr1ᵉ (pr2ᵉ id-equiv-fibered-Σ-Decompositionᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ id-equiv-fibered-Σ-Decompositionᵉ)) xᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ id-equiv-fibered-Σ-Decompositionᵉ)) = refl-htpyᵉ

  equiv-eq-fibered-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (Dᵉ ＝ᵉ D'ᵉ) → equiv-fibered-Σ-Decompositionᵉ Dᵉ D'ᵉ
  equiv-eq-fibered-Σ-Decompositionᵉ .Dᵉ reflᵉ =
    id-equiv-fibered-Σ-Decompositionᵉ

  is-equiv-equiv-eq-fibered-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-fibered-Σ-Decompositionᵉ D'ᵉ)
  is-equiv-equiv-eq-fibered-Σ-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-fibered-Σ-Decompositionᵉ
      equiv-eq-fibered-Σ-Decompositionᵉ

  extensionality-fibered-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (Dᵉ ＝ᵉ D'ᵉ) ≃ᵉ equiv-fibered-Σ-Decompositionᵉ Dᵉ D'ᵉ
  pr1ᵉ (extensionality-fibered-Σ-Decompositionᵉ D'ᵉ) =
    equiv-eq-fibered-Σ-Decompositionᵉ D'ᵉ
  pr2ᵉ (extensionality-fibered-Σ-Decompositionᵉ D'ᵉ) =
    is-equiv-equiv-eq-fibered-Σ-Decompositionᵉ D'ᵉ

  eq-equiv-fibered-Σ-Decompositionᵉ :
    (D'ᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (equiv-fibered-Σ-Decompositionᵉ Dᵉ D'ᵉ) → (Dᵉ ＝ᵉ D'ᵉ)
  eq-equiv-fibered-Σ-Decompositionᵉ D'ᵉ =
    map-inv-equivᵉ (extensionality-fibered-Σ-Decompositionᵉ D'ᵉ)
```

#### Characterization of identity type for displayed double Σ-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Xᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  (Yᵉ : displayed-Σ-Decompositionᵉ l6ᵉ l7ᵉ l8ᵉ l9ᵉ Aᵉ)
  where

  equiv-fst-displayed-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ ⊔ l7ᵉ)
  equiv-fst-displayed-Σ-Decompositionᵉ =
    equiv-Σ-Decompositionᵉ
    ( fst-displayed-Σ-Decompositionᵉ Xᵉ)
    ( fst-displayed-Σ-Decompositionᵉ Yᵉ)

  equiv-snd-displayed-Σ-Decompositionᵉ :
    (eᵉ : equiv-fst-displayed-Σ-Decompositionᵉ) →
    UUᵉ (l2ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-snd-displayed-Σ-Decompositionᵉ eᵉ =
    ( xᵉ : indexing-type-fst-displayed-Σ-Decompositionᵉ Xᵉ) →
    equiv-Σ-Decompositionᵉ
      ( map-equiv-tr-Σ-Decompositionᵉ
        ( equiv-cotype-equiv-Σ-Decompositionᵉ
          ( fst-displayed-Σ-Decompositionᵉ Xᵉ)
          ( fst-displayed-Σ-Decompositionᵉ Yᵉ)
          ( eᵉ)
          ( xᵉ))
        ( snd-displayed-Σ-Decompositionᵉ Xᵉ xᵉ))
      ( snd-displayed-Σ-Decompositionᵉ Yᵉ
        ( map-equiv-indexing-type-equiv-Σ-Decompositionᵉ
          ( fst-displayed-Σ-Decompositionᵉ Xᵉ)
          ( fst-displayed-Σ-Decompositionᵉ Yᵉ)
          ( eᵉ)
          ( xᵉ)))

  equiv-displayed-Σ-Decompositionᵉ :
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ ⊔ l7ᵉ ⊔ l8ᵉ ⊔ l9ᵉ)
  equiv-displayed-Σ-Decompositionᵉ =
    Σᵉ ( equiv-fst-displayed-Σ-Decompositionᵉ)
      ( equiv-snd-displayed-Σ-Decompositionᵉ)

  fst-equiv-displayed-Σ-Decompositionᵉ :
    (eᵉ : equiv-displayed-Σ-Decompositionᵉ) →
    equiv-fst-displayed-Σ-Decompositionᵉ
  fst-equiv-displayed-Σ-Decompositionᵉ = pr1ᵉ

  snd-equiv-displayed-Σ-Decompositionᵉ :
    (eᵉ : equiv-displayed-Σ-Decompositionᵉ) →
    equiv-snd-displayed-Σ-Decompositionᵉ
      ( fst-equiv-displayed-Σ-Decompositionᵉ eᵉ)
  snd-equiv-displayed-Σ-Decompositionᵉ = pr2ᵉ

module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  ( disp-Dᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = fst-displayed-Σ-Decompositionᵉ disp-Dᵉ
    f-Yᵉ = snd-displayed-Σ-Decompositionᵉ disp-Dᵉ

  is-torsorial-equiv-displayed-Σ-Decompositionᵉ :
    is-torsorialᵉ (equiv-displayed-Σ-Decompositionᵉ disp-Dᵉ)
  is-torsorial-equiv-displayed-Σ-Decompositionᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-equiv-Σ-Decompositionᵉ Xᵉ)
      ( pairᵉ Xᵉ (id-equiv-Σ-Decompositionᵉ Xᵉ))
      ( is-contr-equivᵉ
        ( Π-total-famᵉ (λ xᵉ → _))
        ( inv-distributive-Π-Σᵉ)
        ( is-contr-Πᵉ (λ xᵉ → is-torsorial-equiv-Σ-Decompositionᵉ (f-Yᵉ xᵉ))))

  id-equiv-displayed-Σ-Decompositionᵉ :
    equiv-displayed-Σ-Decompositionᵉ disp-Dᵉ disp-Dᵉ
  pr1ᵉ id-equiv-displayed-Σ-Decompositionᵉ = id-equiv-Σ-Decompositionᵉ Xᵉ
  pr1ᵉ (pr2ᵉ id-equiv-displayed-Σ-Decompositionᵉ xᵉ) = id-equivᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ id-equiv-displayed-Σ-Decompositionᵉ xᵉ)) yᵉ = id-equivᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ id-equiv-displayed-Σ-Decompositionᵉ xᵉ)) = refl-htpyᵉ

  equiv-eq-displayed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ) → equiv-displayed-Σ-Decompositionᵉ disp-Dᵉ disp-D'ᵉ
  equiv-eq-displayed-Σ-Decompositionᵉ .disp-Dᵉ reflᵉ =
    id-equiv-displayed-Σ-Decompositionᵉ

  is-equiv-equiv-eq-displayed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    is-equivᵉ (equiv-eq-displayed-Σ-Decompositionᵉ disp-D'ᵉ)
  is-equiv-equiv-eq-displayed-Σ-Decompositionᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-equiv-displayed-Σ-Decompositionᵉ
      equiv-eq-displayed-Σ-Decompositionᵉ

  extensionality-displayed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (disp-Dᵉ ＝ᵉ disp-D'ᵉ) ≃ᵉ equiv-displayed-Σ-Decompositionᵉ disp-Dᵉ disp-D'ᵉ
  pr1ᵉ (extensionality-displayed-Σ-Decompositionᵉ Dᵉ) =
    equiv-eq-displayed-Σ-Decompositionᵉ Dᵉ
  pr2ᵉ (extensionality-displayed-Σ-Decompositionᵉ Dᵉ) =
    is-equiv-equiv-eq-displayed-Σ-Decompositionᵉ Dᵉ

  eq-equiv-displayed-Σ-Decompositionᵉ :
    (disp-D'ᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ) →
    (equiv-displayed-Σ-Decompositionᵉ disp-Dᵉ disp-D'ᵉ) → (disp-Dᵉ ＝ᵉ disp-D'ᵉ)
  eq-equiv-displayed-Σ-Decompositionᵉ Dᵉ =
    map-inv-equivᵉ
      (extensionality-displayed-Σ-Decompositionᵉ Dᵉ)
```

#### Equivalence between fibered double Σ-decompositions and displayed double Σ-decompositions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (fib-Dᵉ : fibered-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Xᵉ = indexing-type-fst-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Yᵉ = cotype-fst-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Y-Inhabited-Typeᵉ = inhabited-cotype-fst-fibered-Σ-Decompositionᵉ fib-Dᵉ
    eᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( fst-fibered-Σ-Decompositionᵉ fib-Dᵉ)
    Uᵉ = indexing-type-snd-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Vᵉ = cotype-snd-fibered-Σ-Decompositionᵉ fib-Dᵉ
    V-Inhabited-Typeᵉ = inhabited-cotype-snd-fibered-Σ-Decompositionᵉ fib-Dᵉ
    fᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( snd-fibered-Σ-Decompositionᵉ fib-Dᵉ)

  matching-correspondence-displayed-fibered-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ Σᵉ Uᵉ (λ uᵉ → Σᵉ (Vᵉ uᵉ) (λ vᵉ → Yᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ))))
  matching-correspondence-displayed-fibered-Σ-Decompositionᵉ =
    equivalence-reasoningᵉ
    Aᵉ ≃ᵉ Σᵉ Xᵉ Yᵉ byᵉ eᵉ
      ≃ᵉ Σᵉ ( Σᵉ Uᵉ Vᵉ) (λ uvᵉ → Yᵉ ((map-inv-equivᵉ fᵉ) uvᵉ))
        byᵉ inv-equivᵉ ( equiv-Σ-equiv-baseᵉ Yᵉ (inv-equivᵉ fᵉ))
      ≃ᵉ Σᵉ Uᵉ ( λ uᵉ → Σᵉ (Vᵉ uᵉ) (λ vᵉ → Yᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ))))
        byᵉ associative-Σᵉ Uᵉ Vᵉ (λ uvᵉ → Yᵉ (map-inv-equivᵉ fᵉ uvᵉ))

  map-displayed-fibered-Σ-Decompositionᵉ :
    displayed-Σ-Decompositionᵉ l4ᵉ (l3ᵉ ⊔ l5ᵉ) l5ᵉ l3ᵉ Aᵉ
  pr1ᵉ (pr1ᵉ map-displayed-fibered-Σ-Decompositionᵉ) = Uᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ map-displayed-fibered-Σ-Decompositionᵉ)) uᵉ =
    Σ-Inhabited-Typeᵉ
      ( V-Inhabited-Typeᵉ uᵉ)
      ( λ vᵉ → Y-Inhabited-Typeᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ)))
  pr2ᵉ (pr2ᵉ (pr1ᵉ map-displayed-fibered-Σ-Decompositionᵉ)) =
    matching-correspondence-displayed-fibered-Σ-Decompositionᵉ
  pr1ᵉ (pr2ᵉ map-displayed-fibered-Σ-Decompositionᵉ uᵉ) = Vᵉ uᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ map-displayed-fibered-Σ-Decompositionᵉ uᵉ)) vᵉ =
    Y-Inhabited-Typeᵉ (map-inv-equivᵉ fᵉ (uᵉ ,ᵉ vᵉ))
  pr2ᵉ (pr2ᵉ (pr2ᵉ map-displayed-fibered-Σ-Decompositionᵉ uᵉ)) = id-equivᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (disp-Dᵉ : displayed-Σ-Decompositionᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ Aᵉ)
  where

  private
    Mᵉ = indexing-type-fst-displayed-Σ-Decompositionᵉ disp-Dᵉ
    Nᵉ = cotype-fst-displayed-Σ-Decompositionᵉ disp-Dᵉ
    sᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( fst-displayed-Σ-Decompositionᵉ disp-Dᵉ)
    Pᵉ = indexing-type-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    Q-Inhabited-Typeᵉ =
      inhabited-cotype-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    Qᵉ = cotype-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    tᵉ = matching-correspondence-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ

  matching-correspondence-inv-displayed-fibered-Σ-Decompositionᵉ :
    Aᵉ ≃ᵉ Σᵉ (Σᵉ Mᵉ Pᵉ) (λ (mᵉ ,ᵉ pᵉ) → Qᵉ mᵉ pᵉ)
  matching-correspondence-inv-displayed-fibered-Σ-Decompositionᵉ =
    equivalence-reasoningᵉ
    Aᵉ ≃ᵉ Σᵉ Mᵉ Nᵉ byᵉ sᵉ
      ≃ᵉ Σᵉ Mᵉ (λ mᵉ → Σᵉ (Pᵉ mᵉ) (Qᵉ mᵉ)) byᵉ equiv-Σᵉ (λ mᵉ → Σᵉ (Pᵉ mᵉ) (Qᵉ mᵉ)) id-equivᵉ tᵉ
      ≃ᵉ Σᵉ (Σᵉ Mᵉ Pᵉ) (λ (mᵉ ,ᵉ pᵉ) → Qᵉ mᵉ pᵉ)
      byᵉ inv-associative-Σᵉ
        ( Mᵉ)
        ( λ zᵉ → Pᵉ zᵉ)
        ( λ zᵉ → Qᵉ (pr1ᵉ zᵉ) (pr2ᵉ zᵉ))

  map-inv-displayed-fibered-Σ-Decompositionᵉ :
    fibered-Σ-Decompositionᵉ (l2ᵉ ⊔ l4ᵉ) l5ᵉ l2ᵉ l4ᵉ Aᵉ
  pr1ᵉ (pr1ᵉ map-inv-displayed-fibered-Σ-Decompositionᵉ) = Σᵉ Mᵉ Pᵉ
  pr1ᵉ (pr2ᵉ (pr1ᵉ map-inv-displayed-fibered-Σ-Decompositionᵉ)) (mᵉ ,ᵉ pᵉ) =
    Q-Inhabited-Typeᵉ mᵉ pᵉ
  pr2ᵉ (pr2ᵉ (pr1ᵉ map-inv-displayed-fibered-Σ-Decompositionᵉ)) =
    matching-correspondence-inv-displayed-fibered-Σ-Decompositionᵉ
  pr1ᵉ (pr2ᵉ map-inv-displayed-fibered-Σ-Decompositionᵉ) = Mᵉ
  pr1ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ map-inv-displayed-fibered-Σ-Decompositionᵉ)) mᵉ) = Pᵉ mᵉ
  pr2ᵉ (pr1ᵉ (pr2ᵉ (pr2ᵉ map-inv-displayed-fibered-Σ-Decompositionᵉ)) mᵉ) =
    ind-trunc-Propᵉ
      ( λ nᵉ → trunc-Propᵉ (Pᵉ mᵉ))
      ( λ nᵉ → unit-trunc-Propᵉ (pr1ᵉ (map-equivᵉ (tᵉ mᵉ) nᵉ)))
      ( is-inhabited-cotype-Σ-Decompositionᵉ
        ( fst-displayed-Σ-Decompositionᵉ disp-Dᵉ)
        ( mᵉ))
  pr2ᵉ (pr2ᵉ (pr2ᵉ map-inv-displayed-fibered-Σ-Decompositionᵉ)) = id-equivᵉ

module _
  {l1ᵉ lᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (fib-Dᵉ : fibered-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ)
  where

  private
    Xᵉ = indexing-type-fst-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Yᵉ = cotype-fst-fibered-Σ-Decompositionᵉ fib-Dᵉ
    eᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( fst-fibered-Σ-Decompositionᵉ fib-Dᵉ)
    Uᵉ = indexing-type-snd-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Vᵉ = cotype-snd-fibered-Σ-Decompositionᵉ fib-Dᵉ
    fᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( snd-fibered-Σ-Decompositionᵉ fib-Dᵉ)
    disp-Dᵉ = map-displayed-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Mᵉ = indexing-type-fst-displayed-Σ-Decompositionᵉ disp-Dᵉ
    Nᵉ = cotype-fst-displayed-Σ-Decompositionᵉ disp-Dᵉ
    sᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( fst-displayed-Σ-Decompositionᵉ disp-Dᵉ)
    Pᵉ = indexing-type-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    Qᵉ = cotype-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    tᵉ = matching-correspondence-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ

    htpy-matching-correspondenceᵉ :
      ( map-equivᵉ
        ( ( equiv-Σᵉ Yᵉ (inv-equivᵉ fᵉ) (λ (mᵉ ,ᵉ pᵉ) → id-equivᵉ)) ∘eᵉ
          ( matching-correspondence-inv-displayed-fibered-Σ-Decompositionᵉ
            ( disp-Dᵉ)))) ~ᵉ
      ( map-equivᵉ eᵉ)
    htpy-matching-correspondenceᵉ aᵉ =
      htpy-eq-equivᵉ
        ( right-inverse-law-equivᵉ (equiv-Σ-equiv-baseᵉ Yᵉ (inv-equivᵉ fᵉ)))
        ( map-equivᵉ eᵉ aᵉ)

  is-retraction-map-inv-displayed-fibered-Σ-Decompositionᵉ :
    map-inv-displayed-fibered-Σ-Decompositionᵉ
      ( map-displayed-fibered-Σ-Decompositionᵉ fib-Dᵉ) ＝ᵉ fib-Dᵉ
  is-retraction-map-inv-displayed-fibered-Σ-Decompositionᵉ =
    eq-equiv-fibered-Σ-Decompositionᵉ
      ( map-inv-displayed-fibered-Σ-Decompositionᵉ
        ( map-displayed-fibered-Σ-Decompositionᵉ fib-Dᵉ))
      ( fib-Dᵉ)
      ( ( ( inv-equivᵉ fᵉ) ,ᵉ
          ( ( λ xᵉ → id-equivᵉ) ,ᵉ
            ( htpy-matching-correspondenceᵉ))) ,ᵉ
        ( ( id-equivᵉ) ,ᵉ
          ( ( λ uᵉ → id-equivᵉ) ,ᵉ
            ( λ aᵉ → reflᵉ))))

module _
  {l1ᵉ lᵉ : Level} {Aᵉ : UUᵉ l1ᵉ}
  (disp-Dᵉ : displayed-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ)
  where

  private
    Mᵉ = indexing-type-fst-displayed-Σ-Decompositionᵉ disp-Dᵉ
    Nᵉ = cotype-fst-displayed-Σ-Decompositionᵉ disp-Dᵉ
    sᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( fst-displayed-Σ-Decompositionᵉ disp-Dᵉ)
    Pᵉ = indexing-type-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    Qᵉ = cotype-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    tᵉ = matching-correspondence-snd-displayed-Σ-Decompositionᵉ disp-Dᵉ
    fib-Dᵉ = map-inv-displayed-fibered-Σ-Decompositionᵉ disp-Dᵉ
    Xᵉ = indexing-type-fst-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Yᵉ = cotype-fst-fibered-Σ-Decompositionᵉ fib-Dᵉ
    eᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( fst-fibered-Σ-Decompositionᵉ fib-Dᵉ)
    Uᵉ = indexing-type-snd-fibered-Σ-Decompositionᵉ fib-Dᵉ
    Vᵉ = cotype-snd-fibered-Σ-Decompositionᵉ fib-Dᵉ
    fᵉ = matching-correspondence-Σ-Decompositionᵉ
      ( snd-fibered-Σ-Decompositionᵉ fib-Dᵉ)

    htpy-matching-correspondenceᵉ :
      map-equivᵉ
        ( equiv-Σᵉ Nᵉ id-equivᵉ (inv-equivᵉ ∘ᵉ tᵉ) ∘eᵉ
          matching-correspondence-displayed-fibered-Σ-Decompositionᵉ
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
      ( tot-htpyᵉ (λ zᵉ → is-retraction-map-inv-equivᵉ (tᵉ zᵉ)) (map-equivᵉ sᵉ xᵉ) ∙ᵉ
      ( tot-idᵉ
        ( λ zᵉ → cotype-fst-displayed-Σ-Decompositionᵉ disp-Dᵉ zᵉ)
        ( map-equivᵉ sᵉ xᵉ))))

  is-section-map-inv-displayed-fibered-Σ-Decompositionᵉ :
    ( map-displayed-fibered-Σ-Decompositionᵉ
      {l1ᵉ} {lᵉ} {lᵉ} {lᵉ} {lᵉ} {Aᵉ} fib-Dᵉ) ＝ᵉ
    disp-Dᵉ
  is-section-map-inv-displayed-fibered-Σ-Decompositionᵉ =
    eq-equiv-displayed-Σ-Decompositionᵉ
      ( map-displayed-fibered-Σ-Decompositionᵉ fib-Dᵉ)
      ( disp-Dᵉ)
      ( ( ( id-equivᵉ) ,ᵉ
          ( ( inv-equivᵉ ∘ᵉ tᵉ) ,ᵉ
            ( htpy-matching-correspondenceᵉ))) ,ᵉ
        ( λ (mᵉ : Mᵉ) →
          ( ( id-equivᵉ) ,ᵉ
            ( ( λ (pᵉ : Pᵉ mᵉ) → id-equivᵉ) ,ᵉ
              ( refl-htpyᵉ)))))

is-equiv-map-displayed-fibered-Σ-Decompositionᵉ :
  {l1ᵉ lᵉ : Level} → {Aᵉ : UUᵉ l1ᵉ} →
  is-equivᵉ
    ( map-displayed-fibered-Σ-Decompositionᵉ {l1ᵉ} {lᵉ} {lᵉ} {lᵉ} {lᵉ} {Aᵉ})
is-equiv-map-displayed-fibered-Σ-Decompositionᵉ =
  is-equiv-is-invertibleᵉ
    ( map-inv-displayed-fibered-Σ-Decompositionᵉ)
    ( is-section-map-inv-displayed-fibered-Σ-Decompositionᵉ)
    ( is-retraction-map-inv-displayed-fibered-Σ-Decompositionᵉ)

equiv-displayed-fibered-Σ-Decompositionᵉ :
  {l1ᵉ lᵉ : Level} → {Aᵉ : UUᵉ l1ᵉ} →
  fibered-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ ≃ᵉ
  displayed-Σ-Decompositionᵉ lᵉ lᵉ lᵉ lᵉ Aᵉ
pr1ᵉ equiv-displayed-fibered-Σ-Decompositionᵉ =
  map-displayed-fibered-Σ-Decompositionᵉ
pr2ᵉ equiv-displayed-fibered-Σ-Decompositionᵉ =
  is-equiv-map-displayed-fibered-Σ-Decompositionᵉ
```