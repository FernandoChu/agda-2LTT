# Equivalences of directed graphs

```agda
module graph-theory.equivalences-directed-graphsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.binary-transportᵉ
open import foundation.cartesian-product-typesᵉ
open import foundation.contractible-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-function-typesᵉ
open import foundation.equivalence-extensionalityᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transposition-identifications-along-equivalencesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.type-theoretic-principle-of-choiceᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import graph-theory.directed-graphsᵉ
open import graph-theory.morphisms-directed-graphsᵉ
```

</details>

## Idea

Anᵉ **equivalenceᵉ ofᵉ directedᵉ graphs**ᵉ fromᵉ aᵉ
[directedᵉ graph](graph-theory.directed-graphs.mdᵉ) `(V,E)`ᵉ to aᵉ directedᵉ graphᵉ
`(V',E')`ᵉ consistsᵉ ofᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ)
`eᵉ : Vᵉ ≃ᵉ V'`ᵉ ofᵉ vertices,ᵉ andᵉ aᵉ familyᵉ ofᵉ equivalencesᵉ `Eᵉ xᵉ yᵉ ≃ᵉ E'ᵉ (eᵉ xᵉ) (eᵉ y)`ᵉ
ofᵉ edgesᵉ indexedᵉ byᵉ `xᵉ yᵉ : V`.ᵉ

## Definitions

### Equivalences of directed graphs

```agda
equiv-Directed-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ) →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
equiv-Directed-Graphᵉ Gᵉ Hᵉ =
  Σᵉ ( vertex-Directed-Graphᵉ Gᵉ ≃ᵉ vertex-Directed-Graphᵉ Hᵉ)
    ( λ eᵉ →
      (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
      edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ
      edge-Directed-Graphᵉ Hᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ)
  where

  equiv-vertex-equiv-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Gᵉ ≃ᵉ vertex-Directed-Graphᵉ Hᵉ
  equiv-vertex-equiv-Directed-Graphᵉ = pr1ᵉ eᵉ

  vertex-equiv-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Gᵉ → vertex-Directed-Graphᵉ Hᵉ
  vertex-equiv-Directed-Graphᵉ = map-equivᵉ equiv-vertex-equiv-Directed-Graphᵉ

  is-equiv-vertex-equiv-Directed-Graphᵉ :
    is-equivᵉ vertex-equiv-Directed-Graphᵉ
  is-equiv-vertex-equiv-Directed-Graphᵉ =
    is-equiv-map-equivᵉ equiv-vertex-equiv-Directed-Graphᵉ

  inv-vertex-equiv-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Hᵉ → vertex-Directed-Graphᵉ Gᵉ
  inv-vertex-equiv-Directed-Graphᵉ =
    map-inv-equivᵉ equiv-vertex-equiv-Directed-Graphᵉ

  is-section-inv-vertex-equiv-Directed-Graphᵉ :
    ( vertex-equiv-Directed-Graphᵉ ∘ᵉ inv-vertex-equiv-Directed-Graphᵉ) ~ᵉ idᵉ
  is-section-inv-vertex-equiv-Directed-Graphᵉ =
    is-section-map-inv-equivᵉ equiv-vertex-equiv-Directed-Graphᵉ

  is-retraction-inv-vertex-equiv-Directed-Graphᵉ :
    ( inv-vertex-equiv-Directed-Graphᵉ ∘ᵉ vertex-equiv-Directed-Graphᵉ) ~ᵉ idᵉ
  is-retraction-inv-vertex-equiv-Directed-Graphᵉ =
    is-retraction-map-inv-equivᵉ equiv-vertex-equiv-Directed-Graphᵉ

  equiv-edge-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ
    edge-Directed-Graphᵉ Hᵉ
      ( vertex-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-equiv-Directed-Graphᵉ yᵉ)
  equiv-edge-equiv-Directed-Graphᵉ = pr2ᵉ eᵉ

  edge-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
    edge-Directed-Graphᵉ Hᵉ
      ( vertex-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-equiv-Directed-Graphᵉ yᵉ)
  edge-equiv-Directed-Graphᵉ xᵉ yᵉ =
    map-equivᵉ (equiv-edge-equiv-Directed-Graphᵉ xᵉ yᵉ)

  is-equiv-edge-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) → is-equivᵉ (edge-equiv-Directed-Graphᵉ xᵉ yᵉ)
  is-equiv-edge-equiv-Directed-Graphᵉ xᵉ yᵉ =
    is-equiv-map-equivᵉ (equiv-edge-equiv-Directed-Graphᵉ xᵉ yᵉ)
```

### The condition on a morphism of directed graphs to be an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  where

  is-equiv-hom-Directed-Graphᵉ :
    hom-Directed-Graphᵉ Gᵉ Hᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-equiv-hom-Directed-Graphᵉ fᵉ =
    ( is-equivᵉ (vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)) ×ᵉ
    ( (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
      is-equivᵉ (edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ {xᵉ} {yᵉ}))

  equiv-is-equiv-hom-Directed-Graphᵉ :
    (fᵉ : hom-Directed-Graphᵉ Gᵉ Hᵉ) →
    is-equiv-hom-Directed-Graphᵉ fᵉ → equiv-Directed-Graphᵉ Gᵉ Hᵉ
  pr1ᵉ (equiv-is-equiv-hom-Directed-Graphᵉ fᵉ (Kᵉ ,ᵉ Lᵉ)) =
    ( vertex-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ ,ᵉ Kᵉ)
  pr2ᵉ (equiv-is-equiv-hom-Directed-Graphᵉ fᵉ (Kᵉ ,ᵉ Lᵉ)) xᵉ yᵉ =
    ( edge-hom-Directed-Graphᵉ Gᵉ Hᵉ fᵉ ,ᵉ Lᵉ xᵉ yᵉ)

  compute-equiv-Directed-Graphᵉ :
    equiv-Directed-Graphᵉ Gᵉ Hᵉ ≃ᵉ
    Σᵉ (hom-Directed-Graphᵉ Gᵉ Hᵉ) is-equiv-hom-Directed-Graphᵉ
  compute-equiv-Directed-Graphᵉ =
    interchange-Σ-Σᵉ
      ( λ fVᵉ Hᵉ fEᵉ → (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) → is-equivᵉ (fEᵉ xᵉ yᵉ)) ∘eᵉ
      ( equiv-totᵉ
        ( λ fVᵉ →
          distributive-Π-Σᵉ ∘eᵉ equiv-Π-equiv-familyᵉ (λ xᵉ → distributive-Π-Σᵉ)))

  hom-equiv-Directed-Graphᵉ :
    equiv-Directed-Graphᵉ Gᵉ Hᵉ → hom-Directed-Graphᵉ Gᵉ Hᵉ
  hom-equiv-Directed-Graphᵉ eᵉ =
    pr1ᵉ (map-equivᵉ compute-equiv-Directed-Graphᵉ eᵉ)

  compute-hom-equiv-Directed-Graphᵉ :
    (eᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) →
    hom-equiv-Directed-Graphᵉ eᵉ ＝ᵉ
    ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ ,ᵉ edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ)
  compute-hom-equiv-Directed-Graphᵉ eᵉ = reflᵉ

  is-equiv-equiv-Directed-Graphᵉ :
    (eᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) →
    is-equiv-hom-Directed-Graphᵉ (hom-equiv-Directed-Graphᵉ eᵉ)
  is-equiv-equiv-Directed-Graphᵉ eᵉ =
    pr2ᵉ (map-equivᵉ compute-equiv-Directed-Graphᵉ eᵉ)
```

### Identity equivalences of directed graphs

```agda
id-equiv-Directed-Graphᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) → equiv-Directed-Graphᵉ Gᵉ Gᵉ
pr1ᵉ (id-equiv-Directed-Graphᵉ Gᵉ) = id-equivᵉ
pr2ᵉ (id-equiv-Directed-Graphᵉ Gᵉ) xᵉ yᵉ = id-equivᵉ
```

### Composition of equivalences of directed graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (Kᵉ : Directed-Graphᵉ l5ᵉ l6ᵉ)
  (gᵉ : equiv-Directed-Graphᵉ Hᵉ Kᵉ) (fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ)
  where

  equiv-vertex-comp-equiv-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Gᵉ ≃ᵉ vertex-Directed-Graphᵉ Kᵉ
  equiv-vertex-comp-equiv-Directed-Graphᵉ =
    ( equiv-vertex-equiv-Directed-Graphᵉ Hᵉ Kᵉ gᵉ) ∘eᵉ
    ( equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)

  vertex-comp-equiv-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Gᵉ → vertex-Directed-Graphᵉ Kᵉ
  vertex-comp-equiv-Directed-Graphᵉ =
    map-equivᵉ equiv-vertex-comp-equiv-Directed-Graphᵉ

  equiv-edge-comp-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ
    edge-Directed-Graphᵉ Kᵉ
      ( vertex-comp-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-comp-equiv-Directed-Graphᵉ yᵉ)
  equiv-edge-comp-equiv-Directed-Graphᵉ xᵉ yᵉ =
    ( equiv-edge-equiv-Directed-Graphᵉ Hᵉ Kᵉ gᵉ
      ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ)
      ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ yᵉ)) ∘eᵉ
    ( equiv-edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ yᵉ)

  edge-comp-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
    edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ →
    edge-Directed-Graphᵉ Kᵉ
      ( vertex-comp-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-comp-equiv-Directed-Graphᵉ yᵉ)
  edge-comp-equiv-Directed-Graphᵉ xᵉ yᵉ =
    map-equivᵉ (equiv-edge-comp-equiv-Directed-Graphᵉ xᵉ yᵉ)

  comp-equiv-Directed-Graphᵉ :
    equiv-Directed-Graphᵉ Gᵉ Kᵉ
  pr1ᵉ comp-equiv-Directed-Graphᵉ =
    equiv-vertex-comp-equiv-Directed-Graphᵉ
  pr2ᵉ comp-equiv-Directed-Graphᵉ =
    equiv-edge-comp-equiv-Directed-Graphᵉ
```

### Homotopies of equivalences of directed graphs

```agda
htpy-equiv-Directed-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (eᵉ fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ fᵉ =
  htpy-hom-Directed-Graphᵉ Gᵉ Hᵉ
    ( hom-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ)
    ( hom-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
```

### The reflexivity homotopy of equivalences of directed graphs

```agda
refl-htpy-equiv-Directed-Graphᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) → htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ eᵉ
refl-htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ =
  refl-htpy-hom-Directed-Graphᵉ Gᵉ Hᵉ (hom-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ)
```

## Properties

### Homotopies characterize identifications of equivalences of directed graphs

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ)
  where

  is-torsorial-htpy-equiv-Directed-Graphᵉ :
    is-torsorialᵉ (htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ)
  is-torsorial-htpy-equiv-Directed-Graphᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpy-equivᵉ (equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ))
      ( equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-Πᵉ
        ( λ xᵉ →
          is-torsorial-Eq-Πᵉ
            ( λ yᵉ →
              is-torsorial-htpy-equivᵉ
                ( equiv-edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ xᵉ yᵉ))))

  htpy-eq-equiv-Directed-Graphᵉ :
    (fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) → eᵉ ＝ᵉ fᵉ → htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ fᵉ
  htpy-eq-equiv-Directed-Graphᵉ .eᵉ reflᵉ = refl-htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ

  is-equiv-htpy-eq-equiv-Directed-Graphᵉ :
    (fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) →
    is-equivᵉ (htpy-eq-equiv-Directed-Graphᵉ fᵉ)
  is-equiv-htpy-eq-equiv-Directed-Graphᵉ =
    fundamental-theorem-idᵉ
      is-torsorial-htpy-equiv-Directed-Graphᵉ
      htpy-eq-equiv-Directed-Graphᵉ

  extensionality-equiv-Directed-Graphᵉ :
    (fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) →
    (eᵉ ＝ᵉ fᵉ) ≃ᵉ htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ fᵉ
  pr1ᵉ (extensionality-equiv-Directed-Graphᵉ fᵉ) = htpy-eq-equiv-Directed-Graphᵉ fᵉ
  pr2ᵉ (extensionality-equiv-Directed-Graphᵉ fᵉ) =
    is-equiv-htpy-eq-equiv-Directed-Graphᵉ fᵉ

  eq-htpy-equiv-Directed-Graphᵉ :
    (fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ) →
    htpy-equiv-Directed-Graphᵉ Gᵉ Hᵉ eᵉ fᵉ → eᵉ ＝ᵉ fᵉ
  eq-htpy-equiv-Directed-Graphᵉ fᵉ =
    map-inv-equivᵉ (extensionality-equiv-Directed-Graphᵉ fᵉ)
```

### Equivalences of directed graphs characterize identifications of directed graphs

```agda
module _
  {l1ᵉ l2ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ)
  where

  extensionality-Directed-Graphᵉ :
    (Hᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) → (Gᵉ ＝ᵉ Hᵉ) ≃ᵉ equiv-Directed-Graphᵉ Gᵉ Hᵉ
  extensionality-Directed-Graphᵉ =
    extensionality-Σᵉ
      ( λ {Vᵉ} Eᵉ eᵉ →
        ( xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) →
        edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ Eᵉ (map-equivᵉ eᵉ xᵉ) (map-equivᵉ eᵉ yᵉ))
      ( id-equivᵉ)
      ( λ xᵉ yᵉ → id-equivᵉ)
      ( λ Xᵉ → equiv-univalenceᵉ)
      ( extensionality-Πᵉ
          ( λ xᵉ yᵉ → edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
          ( λ xᵉ Fᵉ →
            (yᵉ : vertex-Directed-Graphᵉ Gᵉ) → edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ Fᵉ yᵉ)
          ( λ xᵉ →
            extensionality-Πᵉ
              ( λ yᵉ → edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ)
              ( λ yᵉ Xᵉ → edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ ≃ᵉ Xᵉ)
              ( λ yᵉ Xᵉ → equiv-univalenceᵉ)))

  equiv-eq-Directed-Graphᵉ :
    (Hᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) → (Gᵉ ＝ᵉ Hᵉ) → equiv-Directed-Graphᵉ Gᵉ Hᵉ
  equiv-eq-Directed-Graphᵉ Hᵉ = map-equivᵉ (extensionality-Directed-Graphᵉ Hᵉ)

  eq-equiv-Directed-Graphᵉ :
    (Hᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) → equiv-Directed-Graphᵉ Gᵉ Hᵉ → (Gᵉ ＝ᵉ Hᵉ)
  eq-equiv-Directed-Graphᵉ Hᵉ = map-inv-equivᵉ (extensionality-Directed-Graphᵉ Hᵉ)

  is-torsorial-equiv-Directed-Graphᵉ :
    is-torsorialᵉ (equiv-Directed-Graphᵉ Gᵉ)
  is-torsorial-equiv-Directed-Graphᵉ =
    is-contr-equiv'ᵉ
      ( Σᵉ (Directed-Graphᵉ l1ᵉ l2ᵉ) (λ Hᵉ → Gᵉ ＝ᵉ Hᵉ))
      ( equiv-totᵉ extensionality-Directed-Graphᵉ)
      ( is-torsorial-Idᵉ Gᵉ)
```

### The inverse of an equivalence of directed trees

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (Gᵉ : Directed-Graphᵉ l1ᵉ l2ᵉ) (Hᵉ : Directed-Graphᵉ l3ᵉ l4ᵉ)
  (fᵉ : equiv-Directed-Graphᵉ Gᵉ Hᵉ)
  where

  equiv-vertex-inv-equiv-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Hᵉ ≃ᵉ vertex-Directed-Graphᵉ Gᵉ
  equiv-vertex-inv-equiv-Directed-Graphᵉ =
    inv-equivᵉ (equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)

  vertex-inv-equiv-Directed-Graphᵉ :
    vertex-Directed-Graphᵉ Hᵉ → vertex-Directed-Graphᵉ Gᵉ
  vertex-inv-equiv-Directed-Graphᵉ =
    map-inv-equivᵉ (equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)

  is-section-vertex-inv-equiv-Directed-Graphᵉ :
    ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ ∘ᵉ
      vertex-inv-equiv-Directed-Graphᵉ) ~ᵉ idᵉ
  is-section-vertex-inv-equiv-Directed-Graphᵉ =
    is-section-map-inv-equivᵉ (equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)

  is-retraction-vertex-inv-equiv-Directed-Graphᵉ :
    ( vertex-inv-equiv-Directed-Graphᵉ ∘ᵉ
      vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ) ~ᵉ idᵉ
  is-retraction-vertex-inv-equiv-Directed-Graphᵉ =
    is-retraction-map-inv-equivᵉ (equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)

  is-equiv-vertex-inv-equiv-Directed-Graphᵉ :
    is-equivᵉ vertex-inv-equiv-Directed-Graphᵉ
  is-equiv-vertex-inv-equiv-Directed-Graphᵉ =
    is-equiv-map-inv-equivᵉ (equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)

  equiv-edge-inv-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Hᵉ) →
    edge-Directed-Graphᵉ Hᵉ xᵉ yᵉ ≃ᵉ
    edge-Directed-Graphᵉ Gᵉ
      ( vertex-inv-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-inv-equiv-Directed-Graphᵉ yᵉ)
  equiv-edge-inv-equiv-Directed-Graphᵉ xᵉ yᵉ =
    ( inv-equivᵉ
      ( equiv-edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ
        ( vertex-inv-equiv-Directed-Graphᵉ xᵉ)
        ( vertex-inv-equiv-Directed-Graphᵉ yᵉ))) ∘eᵉ
    ( equiv-binary-trᵉ
      ( edge-Directed-Graphᵉ Hᵉ)
      ( invᵉ (is-section-vertex-inv-equiv-Directed-Graphᵉ xᵉ))
      ( invᵉ (is-section-vertex-inv-equiv-Directed-Graphᵉ yᵉ)))

  edge-inv-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Hᵉ) →
    edge-Directed-Graphᵉ Hᵉ xᵉ yᵉ →
    edge-Directed-Graphᵉ Gᵉ
      ( vertex-inv-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-inv-equiv-Directed-Graphᵉ yᵉ)
  edge-inv-equiv-Directed-Graphᵉ xᵉ yᵉ =
    map-equivᵉ (equiv-edge-inv-equiv-Directed-Graphᵉ xᵉ yᵉ)

  hom-inv-equiv-Directed-Graphᵉ : hom-Directed-Graphᵉ Hᵉ Gᵉ
  pr1ᵉ hom-inv-equiv-Directed-Graphᵉ = vertex-inv-equiv-Directed-Graphᵉ
  pr2ᵉ hom-inv-equiv-Directed-Graphᵉ = edge-inv-equiv-Directed-Graphᵉ

  inv-equiv-Directed-Graphᵉ : equiv-Directed-Graphᵉ Hᵉ Gᵉ
  pr1ᵉ inv-equiv-Directed-Graphᵉ = equiv-vertex-inv-equiv-Directed-Graphᵉ
  pr2ᵉ inv-equiv-Directed-Graphᵉ = equiv-edge-inv-equiv-Directed-Graphᵉ

  vertex-is-section-inv-equiv-Directed-Graphᵉ :
    ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ ∘ᵉ vertex-inv-equiv-Directed-Graphᵉ) ~ᵉ idᵉ
  vertex-is-section-inv-equiv-Directed-Graphᵉ =
    is-section-vertex-inv-equiv-Directed-Graphᵉ

  edge-is-section-inv-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Hᵉ) (eᵉ : edge-Directed-Graphᵉ Hᵉ xᵉ yᵉ) →
    binary-trᵉ
      ( edge-Directed-Graphᵉ Hᵉ)
      ( vertex-is-section-inv-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-is-section-inv-equiv-Directed-Graphᵉ yᵉ)
      ( edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ
        ( vertex-inv-equiv-Directed-Graphᵉ xᵉ)
        ( vertex-inv-equiv-Directed-Graphᵉ yᵉ)
        ( edge-inv-equiv-Directed-Graphᵉ xᵉ yᵉ eᵉ)) ＝ᵉ eᵉ
  edge-is-section-inv-equiv-Directed-Graphᵉ xᵉ yᵉ eᵉ =
    ( apᵉ
      ( binary-trᵉ
        ( edge-Directed-Graphᵉ Hᵉ)
        ( vertex-is-section-inv-equiv-Directed-Graphᵉ xᵉ)
        ( vertex-is-section-inv-equiv-Directed-Graphᵉ yᵉ))
        ( is-section-map-inv-equivᵉ
          ( equiv-edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ
            ( vertex-inv-equiv-Directed-Graphᵉ xᵉ)
            ( vertex-inv-equiv-Directed-Graphᵉ yᵉ))
          ( binary-trᵉ
            ( edge-Directed-Graphᵉ Hᵉ)
            ( invᵉ (is-section-map-inv-equivᵉ (pr1ᵉ fᵉ) xᵉ))
            ( invᵉ (is-section-map-inv-equivᵉ (pr1ᵉ fᵉ) yᵉ))
            ( eᵉ)))) ∙ᵉ
    ( ( invᵉ
        ( binary-tr-concatᵉ
          ( edge-Directed-Graphᵉ Hᵉ)
          ( invᵉ (vertex-is-section-inv-equiv-Directed-Graphᵉ xᵉ))
          ( vertex-is-section-inv-equiv-Directed-Graphᵉ xᵉ)
          ( invᵉ (vertex-is-section-inv-equiv-Directed-Graphᵉ yᵉ))
          ( vertex-is-section-inv-equiv-Directed-Graphᵉ yᵉ)
          ( eᵉ))) ∙ᵉ
      ( ap-binaryᵉ
        ( λ pᵉ qᵉ → binary-trᵉ (edge-Directed-Graphᵉ Hᵉ) pᵉ qᵉ eᵉ)
        ( left-invᵉ (vertex-is-section-inv-equiv-Directed-Graphᵉ xᵉ))
        ( left-invᵉ (vertex-is-section-inv-equiv-Directed-Graphᵉ yᵉ))))

  is-section-inv-equiv-Directed-Graphᵉ :
    htpy-equiv-Directed-Graphᵉ Hᵉ Hᵉ
      ( comp-equiv-Directed-Graphᵉ Hᵉ Gᵉ Hᵉ fᵉ (inv-equiv-Directed-Graphᵉ))
      ( id-equiv-Directed-Graphᵉ Hᵉ)
  pr1ᵉ is-section-inv-equiv-Directed-Graphᵉ =
    vertex-is-section-inv-equiv-Directed-Graphᵉ
  pr2ᵉ is-section-inv-equiv-Directed-Graphᵉ =
    edge-is-section-inv-equiv-Directed-Graphᵉ

  vertex-is-retraction-inv-equiv-Directed-Graphᵉ :
    ( vertex-inv-equiv-Directed-Graphᵉ ∘ᵉ vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ) ~ᵉ idᵉ
  vertex-is-retraction-inv-equiv-Directed-Graphᵉ =
    is-retraction-vertex-inv-equiv-Directed-Graphᵉ

  edge-is-retraction-inv-equiv-Directed-Graphᵉ :
    (xᵉ yᵉ : vertex-Directed-Graphᵉ Gᵉ) (eᵉ : edge-Directed-Graphᵉ Gᵉ xᵉ yᵉ) →
    binary-trᵉ
      ( edge-Directed-Graphᵉ Gᵉ)
      ( vertex-is-retraction-inv-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-is-retraction-inv-equiv-Directed-Graphᵉ yᵉ)
      ( edge-inv-equiv-Directed-Graphᵉ
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ)
        ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ yᵉ)
        ( edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ yᵉ eᵉ)) ＝ᵉ eᵉ
  edge-is-retraction-inv-equiv-Directed-Graphᵉ xᵉ yᵉ eᵉ =
    transpose-binary-path-over'ᵉ
      ( edge-Directed-Graphᵉ Gᵉ)
      ( vertex-is-retraction-inv-equiv-Directed-Graphᵉ xᵉ)
      ( vertex-is-retraction-inv-equiv-Directed-Graphᵉ yᵉ)
      ( map-eq-transpose-equiv-invᵉ
        ( equiv-edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ
          ( vertex-inv-equiv-Directed-Graphᵉ
            ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ))
          ( vertex-inv-equiv-Directed-Graphᵉ
            ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ yᵉ)))
        ( ( ap-binaryᵉ
            ( λ uᵉ vᵉ →
              binary-trᵉ
                ( edge-Directed-Graphᵉ Hᵉ)
                ( uᵉ)
                ( vᵉ)
                ( edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ xᵉ yᵉ eᵉ))
            ( ( apᵉ
                ( invᵉ)
                ( coherence-map-inv-equivᵉ
                  ( equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
                  ( xᵉ))) ∙ᵉ
              ( invᵉ
                ( ap-invᵉ
                  ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
                  ( vertex-is-retraction-inv-equiv-Directed-Graphᵉ xᵉ))))
            ( ( apᵉ
                ( invᵉ)
                ( coherence-map-inv-equivᵉ
                  ( equiv-vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
                  ( yᵉ))) ∙ᵉ
              ( invᵉ
                ( ap-invᵉ
                  ( vertex-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
                  ( vertex-is-retraction-inv-equiv-Directed-Graphᵉ yᵉ))))) ∙ᵉ
          ( binary-tr-apᵉ
            ( edge-Directed-Graphᵉ Hᵉ)
            ( edge-equiv-Directed-Graphᵉ Gᵉ Hᵉ fᵉ)
            ( invᵉ (vertex-is-retraction-inv-equiv-Directed-Graphᵉ xᵉ))
            ( invᵉ (vertex-is-retraction-inv-equiv-Directed-Graphᵉ yᵉ))
            ( reflᵉ))))

  is-retraction-inv-equiv-Directed-Graphᵉ :
    htpy-equiv-Directed-Graphᵉ Gᵉ Gᵉ
      ( comp-equiv-Directed-Graphᵉ Gᵉ Hᵉ Gᵉ (inv-equiv-Directed-Graphᵉ) fᵉ)
      ( id-equiv-Directed-Graphᵉ Gᵉ)
  pr1ᵉ is-retraction-inv-equiv-Directed-Graphᵉ =
    vertex-is-retraction-inv-equiv-Directed-Graphᵉ
  pr2ᵉ is-retraction-inv-equiv-Directed-Graphᵉ =
    edge-is-retraction-inv-equiv-Directed-Graphᵉ
```

## External links

-ᵉ [Graphᵉ isomoprhism](https://www.wikidata.org/entity/Q303100ᵉ) atᵉ Wikidataᵉ
-ᵉ [Graphᵉ isomorphism](https://en.wikipedia.org/wiki/Graph_isomorphismᵉ) atᵉ
  Wikipediaᵉ
-ᵉ [Graphᵉ isomorphism](https://mathworld.wolfram.com/GraphIsomorphism.htmlᵉ) atᵉ
  Wolframᵉ Mathworldᵉ
-ᵉ [Isomorphism](https://ncatlab.org/nlab/show/isomorphismᵉ) atᵉ $n$Labᵉ