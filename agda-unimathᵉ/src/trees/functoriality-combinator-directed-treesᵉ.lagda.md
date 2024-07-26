# Functoriality of the combinator of directed trees

```agda
module trees.functoriality-combinator-directed-treesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-transportᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.combinator-directed-treesᵉ
open import trees.directed-treesᵉ
open import trees.equivalences-directed-treesᵉ
open import trees.morphisms-directed-treesᵉ
open import trees.rooted-morphisms-directed-treesᵉ
```

</details>

## Idea

Givenᵉ aᵉ familyᵉ ofᵉ rootedᵉ morphismsᵉ `fᵢᵉ : Sᵢᵉ → Tᵢ`ᵉ ofᵉ directedᵉ trees,ᵉ weᵉ obtainᵉ aᵉ
morphismᵉ

```text
  combinatorᵉ fᵉ : combinatorᵉ Sᵉ → combinatorᵉ Tᵉ
```

ofᵉ directedᵉ trees.ᵉ Furthermore,ᵉ `f`ᵉ isᵉ aᵉ familyᵉ ofᵉ equivalencesᵉ ofᵉ directedᵉ
treesᵉ ifᵉ andᵉ onlyᵉ ifᵉ `combinatorᵉ f`ᵉ isᵉ anᵉ equivalence.ᵉ

## Definitions

### The action of the combinator on families of rooted morphisms of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  (Sᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ) (Tᵉ : Iᵉ → Directed-Treeᵉ l4ᵉ l5ᵉ)
  (fᵉ : (iᵉ : Iᵉ) → rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ))
  where

  node-rooted-hom-combinator-Directed-Treeᵉ :
    node-combinator-Directed-Treeᵉ Sᵉ → node-combinator-Directed-Treeᵉ Tᵉ
  node-rooted-hom-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    root-combinator-Directed-Treeᵉ
  node-rooted-hom-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    node-inclusion-combinator-Directed-Treeᵉ iᵉ
      ( node-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) xᵉ)

  edge-rooted-hom-combinator-Directed-Treeᵉ :
    (xᵉ yᵉ : node-combinator-Directed-Treeᵉ Sᵉ) →
    edge-combinator-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
    edge-combinator-Directed-Treeᵉ Tᵉ
      ( node-rooted-hom-combinator-Directed-Treeᵉ xᵉ)
      ( node-rooted-hom-combinator-Directed-Treeᵉ yᵉ)
  edge-rooted-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-to-root-combinator-Directed-Treeᵉ iᵉ) =
    trᵉ
      ( λ uᵉ → edge-combinator-Directed-Treeᵉ Tᵉ uᵉ root-combinator-Directed-Treeᵉ)
      ( apᵉ
        ( node-inclusion-combinator-Directed-Treeᵉ iᵉ)
        ( preserves-root-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ)))
      ( edge-to-root-combinator-Directed-Treeᵉ iᵉ)
  edge-rooted-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ) =
    edge-inclusion-combinator-Directed-Treeᵉ iᵉ
      ( node-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) xᵉ)
      ( node-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) yᵉ)
      ( edge-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) eᵉ)

  hom-combinator-Directed-Treeᵉ :
    hom-Directed-Treeᵉ (combinator-Directed-Treeᵉ Sᵉ) (combinator-Directed-Treeᵉ Tᵉ)
  pr1ᵉ hom-combinator-Directed-Treeᵉ = node-rooted-hom-combinator-Directed-Treeᵉ
  pr2ᵉ hom-combinator-Directed-Treeᵉ = edge-rooted-hom-combinator-Directed-Treeᵉ

  preserves-root-rooted-hom-combinator-Directed-Treeᵉ :
    node-rooted-hom-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ ＝ᵉ
    root-combinator-Directed-Treeᵉ
  preserves-root-rooted-hom-combinator-Directed-Treeᵉ = reflᵉ

  rooted-hom-combinator-Directed-Treeᵉ :
    rooted-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Sᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
  pr1ᵉ rooted-hom-combinator-Directed-Treeᵉ = hom-combinator-Directed-Treeᵉ
  pr2ᵉ rooted-hom-combinator-Directed-Treeᵉ =
    preserves-root-rooted-hom-combinator-Directed-Treeᵉ
```

### The action of the combinator is functorial

#### The action of the combinator preserves identity morphisms

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} (Tᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ)
  where

  node-id-rooted-hom-combinator-Directed-Treeᵉ :
    node-rooted-hom-combinator-Directed-Treeᵉ Tᵉ Tᵉ
      ( λ iᵉ → id-rooted-hom-Directed-Treeᵉ (Tᵉ iᵉ)) ~ᵉ idᵉ
  node-id-rooted-hom-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    reflᵉ
  node-id-rooted-hom-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    reflᵉ

  edge-id-rooted-hom-combinator-Directed-Treeᵉ :
    (xᵉ yᵉ : node-combinator-Directed-Treeᵉ Tᵉ) →
    (eᵉ : edge-combinator-Directed-Treeᵉ Tᵉ xᵉ yᵉ) →
    binary-trᵉ
      ( edge-combinator-Directed-Treeᵉ Tᵉ)
      ( node-id-rooted-hom-combinator-Directed-Treeᵉ xᵉ)
      ( node-id-rooted-hom-combinator-Directed-Treeᵉ yᵉ)
      ( edge-rooted-hom-combinator-Directed-Treeᵉ Tᵉ Tᵉ
        ( λ iᵉ → id-rooted-hom-Directed-Treeᵉ (Tᵉ iᵉ))
        ( xᵉ)
        ( yᵉ)
        ( eᵉ)) ＝ᵉ eᵉ
  edge-id-rooted-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-to-root-combinator-Directed-Treeᵉ iᵉ) = reflᵉ
  edge-id-rooted-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ) = reflᵉ

  id-rooted-hom-combinator-Directed-Treeᵉ :
    htpy-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( hom-combinator-Directed-Treeᵉ Tᵉ Tᵉ
        ( λ iᵉ → id-rooted-hom-Directed-Treeᵉ (Tᵉ iᵉ)))
      ( id-hom-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ))
  pr1ᵉ id-rooted-hom-combinator-Directed-Treeᵉ =
    node-id-rooted-hom-combinator-Directed-Treeᵉ
  pr2ᵉ id-rooted-hom-combinator-Directed-Treeᵉ =
    edge-id-rooted-hom-combinator-Directed-Treeᵉ
```

#### The action of the combinator on morphisms preserves composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  (Rᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ) (Sᵉ : Iᵉ → Directed-Treeᵉ l4ᵉ l5ᵉ)
  (Tᵉ : Iᵉ → Directed-Treeᵉ l6ᵉ l7ᵉ)
  (gᵉ : (iᵉ : Iᵉ) → rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ))
  (fᵉ : (iᵉ : Iᵉ) → rooted-hom-Directed-Treeᵉ (Rᵉ iᵉ) (Sᵉ iᵉ))
  where

  comp-rooted-hom-combinator-Directed-Treeᵉ :
    htpy-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Rᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( hom-combinator-Directed-Treeᵉ Rᵉ Tᵉ
        ( λ iᵉ → comp-rooted-hom-Directed-Treeᵉ (Rᵉ iᵉ) (Sᵉ iᵉ) (Tᵉ iᵉ) (gᵉ iᵉ) (fᵉ iᵉ)))
      ( comp-hom-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Rᵉ)
        ( combinator-Directed-Treeᵉ Sᵉ)
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
        ( hom-combinator-Directed-Treeᵉ Rᵉ Sᵉ fᵉ))
  pr1ᵉ comp-rooted-hom-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ =
    reflᵉ
  pr1ᵉ comp-rooted-hom-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    reflᵉ
  pr2ᵉ comp-rooted-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-to-root-combinator-Directed-Treeᵉ iᵉ) =
    eq-is-contrᵉ
      ( is-proof-irrelevant-edge-to-root-Directed-Treeᵉ
        ( combinator-Directed-Treeᵉ Tᵉ)
        ( node-comp-hom-Directed-Treeᵉ
          ( combinator-Directed-Treeᵉ Rᵉ)
          ( combinator-Directed-Treeᵉ Sᵉ)
          ( combinator-Directed-Treeᵉ Tᵉ)
          ( hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
          ( hom-combinator-Directed-Treeᵉ Rᵉ Sᵉ fᵉ)
          ( node-inclusion-combinator-Directed-Treeᵉ iᵉ
            ( root-Directed-Treeᵉ (Rᵉ iᵉ))))
        ( trᵉ
          ( λ uᵉ →
            edge-combinator-Directed-Treeᵉ Tᵉ uᵉ root-combinator-Directed-Treeᵉ)
          ( apᵉ
            ( node-inclusion-combinator-Directed-Treeᵉ iᵉ)
            ( ( preserves-root-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (gᵉ iᵉ)) ∙ᵉ
              ( apᵉ
                ( node-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (gᵉ iᵉ))
                ( preserves-root-rooted-hom-Directed-Treeᵉ (Rᵉ iᵉ) (Sᵉ iᵉ) (fᵉ iᵉ)))))
          ( edge-to-root-combinator-Directed-Treeᵉ iᵉ)))
  pr2ᵉ comp-rooted-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ) =
    reflᵉ
```

#### The action of the combinator on morphisms preserves homotopies

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  (Sᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ) (Tᵉ : Iᵉ → Directed-Treeᵉ l4ᵉ l5ᵉ)
  (fᵉ gᵉ : (iᵉ : Iᵉ) → rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ))
  (Hᵉ : (iᵉ : Iᵉ) → htpy-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ))
  where

  node-htpy-hom-combinator-Directed-Treeᵉ :
    node-rooted-hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ fᵉ ~ᵉ
    node-rooted-hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ gᵉ
  node-htpy-hom-combinator-Directed-Treeᵉ root-combinator-Directed-Treeᵉ = reflᵉ
  node-htpy-hom-combinator-Directed-Treeᵉ
    ( node-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ) =
    apᵉ
      ( node-inclusion-combinator-Directed-Treeᵉ iᵉ)
      ( node-htpy-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (Hᵉ iᵉ) xᵉ)

  edge-htpy-hom-combinator-Directed-Treeᵉ :
    ( xᵉ yᵉ : node-combinator-Directed-Treeᵉ Sᵉ)
    ( eᵉ : edge-combinator-Directed-Treeᵉ Sᵉ xᵉ yᵉ) →
    binary-trᵉ
      ( edge-combinator-Directed-Treeᵉ Tᵉ)
      ( node-htpy-hom-combinator-Directed-Treeᵉ xᵉ)
      ( node-htpy-hom-combinator-Directed-Treeᵉ yᵉ)
      ( edge-rooted-hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ fᵉ xᵉ yᵉ eᵉ) ＝ᵉ
    edge-rooted-hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ gᵉ xᵉ yᵉ eᵉ
  edge-htpy-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-to-root-combinator-Directed-Treeᵉ iᵉ) =
    eq-edge-to-root-Directed-Treeᵉ (combinator-Directed-Treeᵉ Tᵉ) _ _ _
  edge-htpy-hom-combinator-Directed-Treeᵉ ._ ._
    ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ xᵉ yᵉ eᵉ) =
    binary-tr-apᵉ
      ( edge-combinator-Directed-Treeᵉ Tᵉ)
      ( edge-inclusion-combinator-Directed-Treeᵉ iᵉ)
      ( node-htpy-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (Hᵉ iᵉ) xᵉ)
      ( node-htpy-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (Hᵉ iᵉ) yᵉ)
      ( edge-htpy-rooted-hom-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ) (gᵉ iᵉ) (Hᵉ iᵉ) xᵉ yᵉ eᵉ)

  htpy-hom-combinator-Directed-Treeᵉ :
    htpy-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Sᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ fᵉ)
      ( hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ gᵉ)
  pr1ᵉ htpy-hom-combinator-Directed-Treeᵉ =
    node-htpy-hom-combinator-Directed-Treeᵉ
  pr2ᵉ htpy-hom-combinator-Directed-Treeᵉ =
    edge-htpy-hom-combinator-Directed-Treeᵉ
```

### The action of the combinator on families of equivalences of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ}
  (Sᵉ : Iᵉ → Directed-Treeᵉ l2ᵉ l3ᵉ) (Tᵉ : Iᵉ → Directed-Treeᵉ l4ᵉ l5ᵉ)
  (fᵉ : (iᵉ : Iᵉ) → equiv-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ))
  where

  rooted-hom-equiv-combinator-Directed-Treeᵉ :
    rooted-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Sᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
  rooted-hom-equiv-combinator-Directed-Treeᵉ =
    rooted-hom-combinator-Directed-Treeᵉ Sᵉ Tᵉ
      ( λ iᵉ → rooted-hom-equiv-Directed-Treeᵉ (Sᵉ iᵉ) (Tᵉ iᵉ) (fᵉ iᵉ))

  hom-equiv-combinator-Directed-Treeᵉ :
    hom-Directed-Treeᵉ (combinator-Directed-Treeᵉ Sᵉ) (combinator-Directed-Treeᵉ Tᵉ)
  hom-equiv-combinator-Directed-Treeᵉ =
    hom-rooted-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Sᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( rooted-hom-equiv-combinator-Directed-Treeᵉ)

  node-equiv-combinator-Directed-Treeᵉ :
    node-combinator-Directed-Treeᵉ Sᵉ → node-combinator-Directed-Treeᵉ Tᵉ
  node-equiv-combinator-Directed-Treeᵉ =
    node-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Sᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( hom-equiv-combinator-Directed-Treeᵉ)

  edge-equiv-combinator-Directed-Treeᵉ :
    {xᵉ yᵉ : node-combinator-Directed-Treeᵉ Sᵉ} →
    edge-combinator-Directed-Treeᵉ Sᵉ xᵉ yᵉ →
    edge-combinator-Directed-Treeᵉ Tᵉ
      ( node-equiv-combinator-Directed-Treeᵉ xᵉ)
      ( node-equiv-combinator-Directed-Treeᵉ yᵉ)
  edge-equiv-combinator-Directed-Treeᵉ =
    edge-hom-Directed-Treeᵉ
      ( combinator-Directed-Treeᵉ Sᵉ)
      ( combinator-Directed-Treeᵉ Tᵉ)
      ( hom-equiv-combinator-Directed-Treeᵉ)
```