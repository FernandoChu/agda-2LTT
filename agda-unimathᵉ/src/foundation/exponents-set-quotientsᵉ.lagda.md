# Exponents of set quotients

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.exponents-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-set-quotientsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.set-quotientsᵉ
open import foundation.setsᵉ
open import foundation.universal-property-set-quotientsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Givenᵉ aᵉ typeᵉ `A`ᵉ equippedᵉ with anᵉ equivalenceᵉ relationᵉ `R`ᵉ andᵉ aᵉ typeᵉ `X`,ᵉ theᵉ
setᵉ quotientᵉ

```text
  (Xᵉ → Aᵉ) /ᵉ ~ᵉ
```

where `fᵉ ~ᵉ gᵉ :=ᵉ (xᵉ : Aᵉ) → Rᵉ (fᵉ xᵉ) (gᵉ x)`,ᵉ embedsᵉ intoᵉ theᵉ typeᵉ `Xᵉ → A/R`.ᵉ Thisᵉ
embeddingᵉ forᵉ everyᵉ `X`,ᵉ `A`,ᵉ andᵉ `R`ᵉ ifᵉ andᵉ onlyᵉ ifᵉ theᵉ axiomᵉ ofᵉ choiceᵉ holds.ᵉ

Consequently,ᵉ weᵉ getᵉ embeddingsᵉ

```text
  ((hom-equivalence-relationᵉ Rᵉ Sᵉ) /ᵉ ~ᵉ) ↪ᵉ ((A/Rᵉ) → (B/Sᵉ))
```

forᵉ anyᵉ twoᵉ equivalenceᵉ relationsᵉ `R`ᵉ onᵉ `A`ᵉ andᵉ `S`ᵉ onᵉ `B`.ᵉ

## Definitions

### The canonical equivalence relation on `X → A`

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ) {Aᵉ : UUᵉ l2ᵉ} (Rᵉ : equivalence-relationᵉ l3ᵉ Aᵉ)
  where

  rel-function-typeᵉ : Relation-Propᵉ (l1ᵉ ⊔ l3ᵉ) (Xᵉ → Aᵉ)
  rel-function-typeᵉ fᵉ gᵉ =
    Π-Propᵉ Xᵉ (λ xᵉ → prop-equivalence-relationᵉ Rᵉ (fᵉ xᵉ) (gᵉ xᵉ))

  sim-function-typeᵉ : (fᵉ gᵉ : Xᵉ → Aᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  sim-function-typeᵉ = type-Relation-Propᵉ rel-function-typeᵉ

  refl-sim-function-typeᵉ : is-reflexiveᵉ sim-function-typeᵉ
  refl-sim-function-typeᵉ fᵉ xᵉ = refl-equivalence-relationᵉ Rᵉ (fᵉ xᵉ)

  symmetric-sim-function-typeᵉ : is-symmetricᵉ sim-function-typeᵉ
  symmetric-sim-function-typeᵉ fᵉ gᵉ rᵉ xᵉ =
    symmetric-equivalence-relationᵉ Rᵉ (fᵉ xᵉ) (gᵉ xᵉ) (rᵉ xᵉ)

  transitive-sim-function-typeᵉ : is-transitiveᵉ sim-function-typeᵉ
  transitive-sim-function-typeᵉ fᵉ gᵉ hᵉ rᵉ sᵉ xᵉ =
    transitive-equivalence-relationᵉ Rᵉ (fᵉ xᵉ) (gᵉ xᵉ) (hᵉ xᵉ) (rᵉ xᵉ) (sᵉ xᵉ)

  equivalence-relation-function-typeᵉ : equivalence-relationᵉ (l1ᵉ ⊔ l3ᵉ) (Xᵉ → Aᵉ)
  pr1ᵉ equivalence-relation-function-typeᵉ = rel-function-typeᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-function-typeᵉ) = refl-sim-function-typeᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-function-typeᵉ)) =
    symmetric-sim-function-typeᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-function-typeᵉ)) =
    transitive-sim-function-typeᵉ

  map-exponent-reflecting-map-equivalence-relationᵉ :
    {l4ᵉ : Level} {Bᵉ : UUᵉ l4ᵉ} →
    reflecting-map-equivalence-relationᵉ Rᵉ Bᵉ → (Xᵉ → Aᵉ) → (Xᵉ → Bᵉ)
  map-exponent-reflecting-map-equivalence-relationᵉ qᵉ =
    postcompᵉ Xᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)

  reflects-exponent-reflecting-map-equivalence-relationᵉ :
    {l4ᵉ : Level} {Bᵉ : UUᵉ l4ᵉ} (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ Bᵉ) →
    reflects-equivalence-relationᵉ equivalence-relation-function-typeᵉ
      ( map-exponent-reflecting-map-equivalence-relationᵉ qᵉ)
  reflects-exponent-reflecting-map-equivalence-relationᵉ qᵉ {fᵉ} {gᵉ} Hᵉ =
    eq-htpyᵉ (λ xᵉ → reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ (Hᵉ xᵉ))

  exponent-reflecting-map-equivalence-relationᵉ :
    {l4ᵉ : Level} {Bᵉ : UUᵉ l4ᵉ} →
    reflecting-map-equivalence-relationᵉ Rᵉ Bᵉ →
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-function-typeᵉ)
      ( Xᵉ → Bᵉ)
  pr1ᵉ (exponent-reflecting-map-equivalence-relationᵉ qᵉ) =
    map-exponent-reflecting-map-equivalence-relationᵉ qᵉ
  pr2ᵉ (exponent-reflecting-map-equivalence-relationᵉ qᵉ) =
    reflects-exponent-reflecting-map-equivalence-relationᵉ qᵉ

  module _
    {l4ᵉ l5ᵉ : Level}
    (Qᵉ : Setᵉ l4ᵉ)
    (qᵉ :
      reflecting-map-equivalence-relationᵉ
        ( equivalence-relation-function-typeᵉ)
        ( type-Setᵉ Qᵉ))
    (Uqᵉ : is-set-quotientᵉ equivalence-relation-function-typeᵉ Qᵉ qᵉ)
    (QRᵉ : Setᵉ l5ᵉ) (qRᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
    (UqRᵉ : is-set-quotientᵉ Rᵉ QRᵉ qRᵉ)
    where

    unique-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ :
      is-contrᵉ
        ( Σᵉ ( type-Setᵉ Qᵉ → (Xᵉ → type-Setᵉ QRᵉ))
            ( λ hᵉ →
              ( hᵉ) ∘ᵉ
              ( map-reflecting-map-equivalence-relationᵉ
                ( equivalence-relation-function-typeᵉ)
                ( qᵉ))
              ~ᵉ
              ( map-exponent-reflecting-map-equivalence-relationᵉ qRᵉ)))
    unique-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ =
      universal-property-set-quotient-is-set-quotientᵉ
        ( equivalence-relation-function-typeᵉ)
        ( Qᵉ)
        ( qᵉ)
        ( Uqᵉ)
        ( function-Setᵉ Xᵉ QRᵉ)
        ( exponent-reflecting-map-equivalence-relationᵉ qRᵉ)

    map-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ :
      type-Setᵉ Qᵉ → (Xᵉ → type-Setᵉ QRᵉ)
    map-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ =
      map-universal-property-set-quotient-is-set-quotientᵉ
        ( equivalence-relation-function-typeᵉ)
        ( Qᵉ)
        ( qᵉ)
        ( Uqᵉ)
        ( function-Setᵉ Xᵉ QRᵉ)
        ( exponent-reflecting-map-equivalence-relationᵉ qRᵉ)

    triangle-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ :
      ( ( map-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ) ∘ᵉ
        ( map-reflecting-map-equivalence-relationᵉ
          ( equivalence-relation-function-typeᵉ)
          ( qᵉ))) ~ᵉ
      ( map-exponent-reflecting-map-equivalence-relationᵉ qRᵉ)
    triangle-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ =
      triangle-universal-property-set-quotient-is-set-quotientᵉ
        ( equivalence-relation-function-typeᵉ)
        ( Qᵉ)
        ( qᵉ)
        ( Uqᵉ)
        ( function-Setᵉ Xᵉ QRᵉ)
        ( exponent-reflecting-map-equivalence-relationᵉ qRᵉ)
```

### An equivalence relation on relation preserving maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  rel-hom-equivalence-relationᵉ :
    Relation-Propᵉ (l1ᵉ ⊔ l4ᵉ) (hom-equivalence-relationᵉ Rᵉ Sᵉ)
  rel-hom-equivalence-relationᵉ fᵉ gᵉ =
    rel-function-typeᵉ Aᵉ Sᵉ
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ gᵉ)

  sim-hom-equivalence-relationᵉ :
    (fᵉ gᵉ : hom-equivalence-relationᵉ Rᵉ Sᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  sim-hom-equivalence-relationᵉ fᵉ gᵉ =
    sim-function-typeᵉ Aᵉ Sᵉ
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ gᵉ)

  refl-sim-hom-equivalence-relationᵉ : is-reflexiveᵉ sim-hom-equivalence-relationᵉ
  refl-sim-hom-equivalence-relationᵉ fᵉ =
    refl-sim-function-typeᵉ Aᵉ Sᵉ (map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)

  symmetric-sim-hom-equivalence-relationᵉ :
    is-symmetricᵉ sim-hom-equivalence-relationᵉ
  symmetric-sim-hom-equivalence-relationᵉ fᵉ gᵉ =
    symmetric-sim-function-typeᵉ Aᵉ Sᵉ
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ gᵉ)

  transitive-sim-hom-equivalence-relationᵉ :
    is-transitiveᵉ sim-hom-equivalence-relationᵉ
  transitive-sim-hom-equivalence-relationᵉ fᵉ gᵉ hᵉ =
    transitive-sim-function-typeᵉ Aᵉ Sᵉ
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ fᵉ)
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ gᵉ)
      ( map-hom-equivalence-relationᵉ Rᵉ Sᵉ hᵉ)

  equivalence-relation-hom-equivalence-relationᵉ :
    equivalence-relationᵉ (l1ᵉ ⊔ l4ᵉ) (hom-equivalence-relationᵉ Rᵉ Sᵉ)
  pr1ᵉ equivalence-relation-hom-equivalence-relationᵉ =
    rel-hom-equivalence-relationᵉ
  pr1ᵉ (pr2ᵉ equivalence-relation-hom-equivalence-relationᵉ) =
    refl-sim-hom-equivalence-relationᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-hom-equivalence-relationᵉ)) =
    symmetric-sim-hom-equivalence-relationᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ equivalence-relation-hom-equivalence-relationᵉ)) =
    transitive-sim-hom-equivalence-relationᵉ
```

### The universal reflecting map from `hom-equivalence-relation R S` to `A/R → B/S`

#### First variant using only the universal property of set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (QRᵉ : Setᵉ l3ᵉ) (qRᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  (UqRᵉ : is-set-quotientᵉ Rᵉ QRᵉ qRᵉ)
  {Bᵉ : UUᵉ l4ᵉ} (Sᵉ : equivalence-relationᵉ l5ᵉ Bᵉ)
  (QSᵉ : Setᵉ l6ᵉ) (qSᵉ : reflecting-map-equivalence-relationᵉ Sᵉ (type-Setᵉ QSᵉ))
  (UqSᵉ : is-set-quotientᵉ Sᵉ QSᵉ qSᵉ)
  where

  universal-map-is-set-quotient-hom-equivalence-relationᵉ :
    hom-equivalence-relationᵉ Rᵉ Sᵉ → hom-Setᵉ QRᵉ QSᵉ
  universal-map-is-set-quotient-hom-equivalence-relationᵉ =
    map-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ Sᵉ QSᵉ qSᵉ UqRᵉ UqSᵉ

  reflects-universal-map-is-set-quotient-hom-equivalence-relationᵉ :
    reflects-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( universal-map-is-set-quotient-hom-equivalence-relationᵉ)
  reflects-universal-map-is-set-quotient-hom-equivalence-relationᵉ {fᵉ} {gᵉ} sᵉ =
    eq-htpyᵉ
      ( ind-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ UqRᵉ
        ( λ xᵉ →
          Id-Propᵉ QSᵉ
            ( map-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ Sᵉ QSᵉ qSᵉ UqRᵉ UqSᵉ fᵉ xᵉ)
            ( map-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ Sᵉ QSᵉ qSᵉ UqRᵉ UqSᵉ gᵉ xᵉ))
        ( λ aᵉ →
          ( coherence-square-map-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ Sᵉ QSᵉ qSᵉ UqRᵉ UqSᵉ fᵉ aᵉ) ∙ᵉ
          ( apply-effectiveness-is-set-quotient'ᵉ Sᵉ QSᵉ qSᵉ UqSᵉ (sᵉ aᵉ)) ∙ᵉ
          ( invᵉ
            ( coherence-square-map-is-set-quotientᵉ
              Rᵉ QRᵉ qRᵉ Sᵉ QSᵉ qSᵉ UqRᵉ UqSᵉ gᵉ aᵉ))))

  universal-reflecting-map-is-set-quotient-hom-equivalence-relationᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( hom-Setᵉ QRᵉ QSᵉ)
  pr1ᵉ universal-reflecting-map-is-set-quotient-hom-equivalence-relationᵉ =
    universal-map-is-set-quotient-hom-equivalence-relationᵉ
  pr2ᵉ universal-reflecting-map-is-set-quotient-hom-equivalence-relationᵉ =
    reflects-universal-map-is-set-quotient-hom-equivalence-relationᵉ
```

#### Second variant using the designated set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  universal-reflecting-map-set-quotient-hom-equivalence-relationᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ)
  universal-reflecting-map-set-quotient-hom-equivalence-relationᵉ =
    universal-reflecting-map-is-set-quotient-hom-equivalence-relationᵉ
      ( Rᵉ)
      ( quotient-Setᵉ Rᵉ)
      ( reflecting-map-quotient-mapᵉ Rᵉ)
      ( λ {lᵉ} → is-set-quotient-set-quotientᵉ Rᵉ {lᵉ})
      ( Sᵉ)
      ( quotient-Setᵉ Sᵉ)
      ( reflecting-map-quotient-mapᵉ Sᵉ)
      ( λ {lᵉ} → is-set-quotient-set-quotientᵉ Sᵉ {lᵉ})

  universal-map-set-quotient-hom-equivalence-relationᵉ :
    hom-equivalence-relationᵉ Rᵉ Sᵉ → set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ
  universal-map-set-quotient-hom-equivalence-relationᵉ =
    map-reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( universal-reflecting-map-set-quotient-hom-equivalence-relationᵉ)

  reflects-universal-map-set-quotient-hom-equivalence-relationᵉ :
    reflects-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( universal-map-set-quotient-hom-equivalence-relationᵉ)
  reflects-universal-map-set-quotient-hom-equivalence-relationᵉ =
    reflects-map-reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( universal-reflecting-map-set-quotient-hom-equivalence-relationᵉ)
```

## Properties

### The inclusion of the quotient `(X → A)/~` into `X → A/R` is an embedding

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (Xᵉ : UUᵉ l1ᵉ)
  {Aᵉ : UUᵉ l2ᵉ} (Rᵉ : equivalence-relationᵉ l3ᵉ Aᵉ)
  (Qᵉ : Setᵉ l4ᵉ)
  (qᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-function-typeᵉ Xᵉ Rᵉ)
      ( type-Setᵉ Qᵉ))
  (Uqᵉ : is-set-quotientᵉ (equivalence-relation-function-typeᵉ Xᵉ Rᵉ) Qᵉ qᵉ)
  (QRᵉ : Setᵉ l5ᵉ) (qRᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  (UqRᵉ : is-set-quotientᵉ Rᵉ QRᵉ qRᵉ)
  where

  is-emb-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ :
    is-embᵉ
      ( map-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ
        Xᵉ Rᵉ Qᵉ qᵉ Uqᵉ QRᵉ qRᵉ UqRᵉ)
  is-emb-inclusion-is-set-quotient-equivalence-relation-function-typeᵉ =
    is-emb-map-universal-property-set-quotient-is-set-quotientᵉ
      ( equivalence-relation-function-typeᵉ Xᵉ Rᵉ)
      ( Qᵉ)
      ( qᵉ)
      ( Uqᵉ)
      ( function-Setᵉ Xᵉ QRᵉ)
      ( exponent-reflecting-map-equivalence-relationᵉ Xᵉ Rᵉ qRᵉ)
      ( λ gᵉ hᵉ pᵉ xᵉ →
        apply-effectiveness-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ UqRᵉ (htpy-eqᵉ pᵉ xᵉ))
```

### The extension of the universal map from `hom-equivalence-relation R S` to `A/R → B/S` to the quotient is an embedding

#### First variant using only the universal property of the set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (QRᵉ : Setᵉ l3ᵉ) (qRᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ QRᵉ))
  (URᵉ : is-set-quotientᵉ Rᵉ QRᵉ qRᵉ)
  {Bᵉ : UUᵉ l4ᵉ} (Sᵉ : equivalence-relationᵉ l5ᵉ Bᵉ)
  (QSᵉ : Setᵉ l6ᵉ) (qSᵉ : reflecting-map-equivalence-relationᵉ Sᵉ (type-Setᵉ QSᵉ))
  (USᵉ : is-set-quotientᵉ Sᵉ QSᵉ qSᵉ)
  (QHᵉ : Setᵉ l7ᵉ)
  (qHᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( type-Setᵉ QHᵉ))
  (UHᵉ :
    is-set-quotientᵉ (equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ) QHᵉ qHᵉ)
  where

  unique-inclusion-is-set-quotient-hom-equivalence-relationᵉ :
    is-contrᵉ
      ( Σᵉ ( hom-Setᵉ QHᵉ (hom-set-Setᵉ QRᵉ QSᵉ))
          ( λ μᵉ →
            ( μᵉ ∘ᵉ
              map-reflecting-map-equivalence-relationᵉ
                ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
                ( qHᵉ)) ~ᵉ
            ( universal-map-is-set-quotient-hom-equivalence-relationᵉ
                Rᵉ QRᵉ qRᵉ URᵉ Sᵉ QSᵉ qSᵉ USᵉ)))
  unique-inclusion-is-set-quotient-hom-equivalence-relationᵉ =
    universal-property-set-quotient-is-set-quotientᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( QHᵉ)
      ( qHᵉ)
      ( UHᵉ)
      ( hom-set-Setᵉ QRᵉ QSᵉ)
      ( universal-reflecting-map-is-set-quotient-hom-equivalence-relationᵉ
        Rᵉ QRᵉ qRᵉ URᵉ Sᵉ QSᵉ qSᵉ USᵉ)

  inclusion-is-set-quotient-hom-equivalence-relationᵉ :
    hom-Setᵉ QHᵉ (hom-set-Setᵉ QRᵉ QSᵉ)
  inclusion-is-set-quotient-hom-equivalence-relationᵉ =
    pr1ᵉ (centerᵉ (unique-inclusion-is-set-quotient-hom-equivalence-relationᵉ))

  triangle-inclusion-is-set-quotient-hom-equivalence-relationᵉ :
    ( inclusion-is-set-quotient-hom-equivalence-relationᵉ ∘ᵉ
      map-reflecting-map-equivalence-relationᵉ
        ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
        ( qHᵉ)) ~ᵉ
    ( universal-map-is-set-quotient-hom-equivalence-relationᵉ
        Rᵉ QRᵉ qRᵉ URᵉ Sᵉ QSᵉ qSᵉ USᵉ)
  triangle-inclusion-is-set-quotient-hom-equivalence-relationᵉ =
    pr2ᵉ (centerᵉ (unique-inclusion-is-set-quotient-hom-equivalence-relationᵉ))

  is-emb-inclusion-is-set-quotient-hom-equivalence-relationᵉ :
    is-embᵉ inclusion-is-set-quotient-hom-equivalence-relationᵉ
  is-emb-inclusion-is-set-quotient-hom-equivalence-relationᵉ =
    is-emb-map-universal-property-set-quotient-is-set-quotientᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( QHᵉ)
      ( qHᵉ)
      ( UHᵉ)
      ( hom-set-Setᵉ QRᵉ QSᵉ)
      ( universal-reflecting-map-is-set-quotient-hom-equivalence-relationᵉ
        Rᵉ QRᵉ qRᵉ URᵉ Sᵉ QSᵉ qSᵉ USᵉ)
      ( λ gᵉ hᵉ pᵉ aᵉ →
        apply-effectiveness-is-set-quotientᵉ Sᵉ QSᵉ qSᵉ USᵉ
          ( ( inv-htpyᵉ
              ( coherence-square-map-is-set-quotientᵉ Rᵉ QRᵉ qRᵉ Sᵉ QSᵉ qSᵉ URᵉ USᵉ gᵉ) ∙hᵉ
              ( ( htpy-eqᵉ pᵉ ·rᵉ map-reflecting-map-equivalence-relationᵉ Rᵉ qRᵉ) ∙hᵉ
                ( coherence-square-map-is-set-quotientᵉ
                  Rᵉ QRᵉ qRᵉ Sᵉ QSᵉ qSᵉ URᵉ USᵉ hᵉ)))
            ( aᵉ)))

  emb-inclusion-is-set-quotient-hom-equivalence-relationᵉ :
    type-Setᵉ QHᵉ ↪ᵉ hom-Setᵉ QRᵉ QSᵉ
  pr1ᵉ emb-inclusion-is-set-quotient-hom-equivalence-relationᵉ =
    inclusion-is-set-quotient-hom-equivalence-relationᵉ
  pr2ᵉ emb-inclusion-is-set-quotient-hom-equivalence-relationᵉ =
    is-emb-inclusion-is-set-quotient-hom-equivalence-relationᵉ
```

#### Second variant using the official set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (Sᵉ : equivalence-relationᵉ l4ᵉ Bᵉ)
  where

  quotient-hom-equivalence-relation-Setᵉ : Setᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  quotient-hom-equivalence-relation-Setᵉ =
    quotient-Setᵉ (equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)

  set-quotient-hom-equivalence-relationᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  set-quotient-hom-equivalence-relationᵉ =
    type-Setᵉ quotient-hom-equivalence-relation-Setᵉ

  is-set-set-quotient-hom-equivalence-relationᵉ :
    is-setᵉ set-quotient-hom-equivalence-relationᵉ
  is-set-set-quotient-hom-equivalence-relationᵉ =
    is-set-type-Setᵉ quotient-hom-equivalence-relation-Setᵉ

  reflecting-map-quotient-map-hom-equivalence-relationᵉ :
    reflecting-map-equivalence-relationᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( set-quotient-hom-equivalence-relationᵉ)
  reflecting-map-quotient-map-hom-equivalence-relationᵉ =
    reflecting-map-quotient-mapᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)

  quotient-map-hom-equivalence-relationᵉ :
    hom-equivalence-relationᵉ Rᵉ Sᵉ → set-quotient-hom-equivalence-relationᵉ
  quotient-map-hom-equivalence-relationᵉ =
    quotient-mapᵉ (equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)

  is-set-quotient-set-quotient-hom-equivalence-relationᵉ :
    is-set-quotientᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( quotient-hom-equivalence-relation-Setᵉ)
      ( reflecting-map-quotient-map-hom-equivalence-relationᵉ)
  is-set-quotient-set-quotient-hom-equivalence-relationᵉ =
    is-set-quotient-set-quotientᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)

  unique-inclusion-set-quotient-hom-equivalence-relationᵉ :
    is-contrᵉ
      ( Σᵉ ( set-quotient-hom-equivalence-relationᵉ →
            set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ)
          ( λ μᵉ →
            μᵉ ∘ᵉ
            quotient-mapᵉ (equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ) ~ᵉ
            universal-map-set-quotient-hom-equivalence-relationᵉ Rᵉ Sᵉ))
  unique-inclusion-set-quotient-hom-equivalence-relationᵉ =
    universal-property-set-quotient-is-set-quotientᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( quotient-hom-equivalence-relation-Setᵉ)
      ( reflecting-map-quotient-map-hom-equivalence-relationᵉ)
      ( is-set-quotient-set-quotient-hom-equivalence-relationᵉ)
      ( hom-set-Setᵉ (quotient-Setᵉ Rᵉ) (quotient-Setᵉ Sᵉ))
      ( universal-reflecting-map-set-quotient-hom-equivalence-relationᵉ Rᵉ Sᵉ)

  inclusion-set-quotient-hom-equivalence-relationᵉ :
    set-quotientᵉ (equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ) →
    set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ
  inclusion-set-quotient-hom-equivalence-relationᵉ =
    pr1ᵉ (centerᵉ (unique-inclusion-set-quotient-hom-equivalence-relationᵉ))

  triangle-inclusion-set-quotient-hom-equivalence-relationᵉ :
    ( inclusion-set-quotient-hom-equivalence-relationᵉ ∘ᵉ
      quotient-mapᵉ (equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)) ~ᵉ
    ( universal-map-set-quotient-hom-equivalence-relationᵉ Rᵉ Sᵉ)
  triangle-inclusion-set-quotient-hom-equivalence-relationᵉ =
    pr2ᵉ (centerᵉ (unique-inclusion-set-quotient-hom-equivalence-relationᵉ))

  is-emb-inclusion-set-quotient-hom-equivalence-relationᵉ :
    is-embᵉ inclusion-set-quotient-hom-equivalence-relationᵉ
  is-emb-inclusion-set-quotient-hom-equivalence-relationᵉ =
    is-emb-map-universal-property-set-quotient-is-set-quotientᵉ
      ( equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( quotient-hom-equivalence-relation-Setᵉ)
      ( reflecting-map-quotient-map-hom-equivalence-relationᵉ)
      ( is-set-quotient-set-quotient-hom-equivalence-relationᵉ)
      ( hom-set-Setᵉ (quotient-Setᵉ Rᵉ) (quotient-Setᵉ Sᵉ))
      ( universal-reflecting-map-set-quotient-hom-equivalence-relationᵉ Rᵉ Sᵉ)
      ( λ gᵉ hᵉ pᵉ aᵉ →
        apply-effectiveness-quotient-mapᵉ Sᵉ
          ( ( inv-htpyᵉ
              ( coherence-square-map-set-quotientᵉ Rᵉ Sᵉ gᵉ) ∙hᵉ
              ( ( htpy-eqᵉ pᵉ ·rᵉ quotient-mapᵉ Rᵉ) ∙hᵉ
                ( coherence-square-map-set-quotientᵉ
                  Rᵉ Sᵉ hᵉ)))
            ( aᵉ)))

  emb-inclusion-set-quotient-hom-equivalence-relationᵉ :
    set-quotientᵉ (equivalence-relation-hom-equivalence-relationᵉ Rᵉ Sᵉ) ↪ᵉ
    ( set-quotientᵉ Rᵉ → set-quotientᵉ Sᵉ)
  pr1ᵉ emb-inclusion-set-quotient-hom-equivalence-relationᵉ =
    inclusion-set-quotient-hom-equivalence-relationᵉ
  pr2ᵉ emb-inclusion-set-quotient-hom-equivalence-relationᵉ =
    is-emb-inclusion-set-quotient-hom-equivalence-relationᵉ
```