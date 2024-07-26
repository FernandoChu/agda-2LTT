# Lifting structures on commuting squares of maps

```agda
module orthogonal-factorization-systems.lifting-structures-on-squaresᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-homotopiesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-tetrahedra-of-homotopiesᵉ
open import foundation.commuting-triangles-of-homotopiesᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.fibers-of-mapsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.higher-homotopies-morphisms-arrowsᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.path-algebraᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import orthogonal-factorization-systems.extensions-of-mapsᵉ
open import orthogonal-factorization-systems.lifts-of-mapsᵉ
open import orthogonal-factorization-systems.pullback-homᵉ
```

</details>

## Idea

Aᵉ
{{#conceptᵉ "liftingᵉ structure"ᵉ Disambiguation="commutingᵉ squareᵉ ofᵉ maps"ᵉ Agda=lifting-structure-squareᵉ}}
ofᵉ aᵉ commutingᵉ squareᵉ

```text
       hᵉ
  Aᵉ ------>ᵉ Xᵉ
  |         |
 f|ᵉ         |gᵉ
  |         |
  ∨ᵉ         ∨ᵉ
  Bᵉ ------>ᵉ Yᵉ
       iᵉ
```

consistsᵉ ofᵉ aᵉ
{{#conceptᵉ "diagonalᵉ lift"ᵉ Disambiguation="commutingᵉ squareᵉ ofᵉ maps"ᵉ Agda=is-diagonal-lift-squareᵉ}}
`jᵉ : Bᵉ → X`ᵉ suchᵉ thatᵉ theᵉ completeᵉ diagramᵉ

```text
         hᵉ
   Aᵉ -------->ᵉ Xᵉ
   |        ∧ᵉ  |
 fᵉ |   jᵉ  /ᵉ    | gᵉ
   |    /ᵉ      |
   ∨ᵉ  /ᵉ        ∨ᵉ
   Bᵉ -------->ᵉ Yᵉ
         iᵉ
```

commutes.ᵉ Weᵉ referᵉ to aᵉ squareᵉ equippedᵉ with aᵉ liftingᵉ structureᵉ asᵉ aᵉ
{{#conceptᵉ "liftingᵉ square"}}.ᵉ Observeᵉ thatᵉ thereᵉ isᵉ aᵉ canonicalᵉ mapᵉ

```text
  pullback-homᵉ fᵉ gᵉ : (Bᵉ → Xᵉ) → hom-arrowᵉ fᵉ g.ᵉ
```

Thereforeᵉ weᵉ seeᵉ thatᵉ aᵉ liftingᵉ squareᵉ consistsᵉ ofᵉ aᵉ
[morphismᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `αᵉ : hom-arrowᵉ fᵉ g`ᵉ fromᵉ
`f`ᵉ to `g`,ᵉ aᵉ mapᵉ `jᵉ : Bᵉ → X`,ᵉ andᵉ aᵉ
[homotopyᵉ ofᵉ morphismsᵉ ofᵉ arrows](foundation.homotopies-morphisms-arrows.mdᵉ)
`pullback-homᵉ fᵉ gᵉ jᵉ ~ᵉ α`.ᵉ

**Terminology.**ᵉ Inᵉ theᵉ literature,ᵉ aᵉ liftingᵉ structureᵉ onᵉ aᵉ squareᵉ isᵉ commonlyᵉ
referredᵉ to asᵉ aᵉ _solutionᵉ to theᵉ liftingᵉ problemᵉ_ `α`.ᵉ

## Definitions

### The predicate of being a diagonal lift of a square

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ) (jᵉ : Bᵉ → Xᵉ)
  where

  is-diagonal-lift-squareᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  is-diagonal-lift-squareᵉ = htpy-hom-arrowᵉ fᵉ gᵉ αᵉ (pullback-homᵉ fᵉ gᵉ jᵉ)

  is-extension-is-diagonal-lift-squareᵉ :
    is-diagonal-lift-squareᵉ →
    is-extensionᵉ fᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ) jᵉ
  is-extension-is-diagonal-lift-squareᵉ = pr1ᵉ

  is-lift-is-diagonal-lift-squareᵉ :
    is-diagonal-lift-squareᵉ → is-liftᵉ gᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ) jᵉ
  is-lift-is-diagonal-lift-squareᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  coherence-is-diagonal-lift-squareᵉ :
    (lᵉ : is-diagonal-lift-squareᵉ) →
    coherence-square-homotopiesᵉ
      ( is-lift-is-diagonal-lift-squareᵉ lᵉ ·rᵉ fᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-pullback-homᵉ fᵉ gᵉ jᵉ)
      ( gᵉ ·lᵉ is-extension-is-diagonal-lift-squareᵉ lᵉ)
  coherence-is-diagonal-lift-squareᵉ = pr2ᵉ ∘ᵉ pr2ᵉ
```

### Lifting structures on squares

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  lifting-structure-squareᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  lifting-structure-squareᵉ = Σᵉ (Bᵉ → Xᵉ) (is-diagonal-lift-squareᵉ fᵉ gᵉ αᵉ)

  diagonal-map-lifting-structure-squareᵉ : lifting-structure-squareᵉ → (Bᵉ → Xᵉ)
  diagonal-map-lifting-structure-squareᵉ = pr1ᵉ

  is-lifting-diagonal-map-lifting-structure-squareᵉ :
    (lᵉ : lifting-structure-squareᵉ) →
    is-diagonal-lift-squareᵉ fᵉ gᵉ αᵉ (diagonal-map-lifting-structure-squareᵉ lᵉ)
  is-lifting-diagonal-map-lifting-structure-squareᵉ = pr2ᵉ

  is-extension-diagonal-map-lifting-structure-squareᵉ :
    (lᵉ : lifting-structure-squareᵉ) →
    is-extensionᵉ fᵉ
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( diagonal-map-lifting-structure-squareᵉ lᵉ)
  is-extension-diagonal-map-lifting-structure-squareᵉ = pr1ᵉ ∘ᵉ pr2ᵉ

  extension-lifting-structure-squareᵉ :
    lifting-structure-squareᵉ → extensionᵉ fᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
  pr1ᵉ (extension-lifting-structure-squareᵉ Lᵉ) =
    diagonal-map-lifting-structure-squareᵉ Lᵉ
  pr2ᵉ (extension-lifting-structure-squareᵉ Lᵉ) =
    is-extension-diagonal-map-lifting-structure-squareᵉ Lᵉ

  is-lift-diagonal-map-lifting-structure-squareᵉ :
    (lᵉ : lifting-structure-squareᵉ) →
    is-liftᵉ gᵉ
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( diagonal-map-lifting-structure-squareᵉ lᵉ)
  is-lift-diagonal-map-lifting-structure-squareᵉ = pr1ᵉ ∘ᵉ (pr2ᵉ ∘ᵉ pr2ᵉ)

  lift-lifting-structure-squareᵉ :
    lifting-structure-squareᵉ → liftᵉ gᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
  pr1ᵉ (lift-lifting-structure-squareᵉ Lᵉ) =
    diagonal-map-lifting-structure-squareᵉ Lᵉ
  pr2ᵉ (lift-lifting-structure-squareᵉ Lᵉ) =
    is-lift-diagonal-map-lifting-structure-squareᵉ Lᵉ

  coherence-lifting-structure-squareᵉ :
    (lᵉ : lifting-structure-squareᵉ) →
    coherence-square-homotopiesᵉ
      ( is-lift-diagonal-map-lifting-structure-squareᵉ lᵉ ·rᵉ fᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-pullback-homᵉ fᵉ gᵉ (diagonal-map-lifting-structure-squareᵉ lᵉ))
      ( gᵉ ·lᵉ is-extension-diagonal-map-lifting-structure-squareᵉ lᵉ)
  coherence-lifting-structure-squareᵉ = pr2ᵉ ∘ᵉ (pr2ᵉ ∘ᵉ pr2ᵉ)
```

### Homotopies of lifting squares

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  (kᵉ lᵉ : lifting-structure-squareᵉ fᵉ gᵉ αᵉ)
  where

  coherence-htpy-lifting-structure-squareᵉ :
    diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ ~ᵉ
    diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ →
    UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  coherence-htpy-lifting-structure-squareᵉ Hᵉ =
    htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ
      ( pullback-homᵉ fᵉ gᵉ (diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ))
      ( concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ
        ( pullback-homᵉ fᵉ gᵉ (diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ))
        ( pullback-homᵉ fᵉ gᵉ (diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ))
        ( is-lifting-diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ)
        ( htpy-hom-arrow-htpyᵉ fᵉ gᵉ Hᵉ))
      ( is-lifting-diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ)

  htpy-lifting-structure-squareᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-lifting-structure-squareᵉ =
    Σᵉ ( diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ ~ᵉ
        diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ)
      ( coherence-htpy-lifting-structure-squareᵉ)

  module _
    (Hᵉ : htpy-lifting-structure-squareᵉ)
    where

    htpy-diagonal-map-htpy-lifting-structure-squareᵉ :
      diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ ~ᵉ
      diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ
    htpy-diagonal-map-htpy-lifting-structure-squareᵉ = pr1ᵉ Hᵉ

    coh-htpy-lifting-structure-squareᵉ :
      coherence-htpy-lifting-structure-squareᵉ
        ( htpy-diagonal-map-htpy-lifting-structure-squareᵉ)
    coh-htpy-lifting-structure-squareᵉ = pr2ᵉ Hᵉ
```

### The reflexivity homotopy of a lifting square

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  (kᵉ : lifting-structure-squareᵉ fᵉ gᵉ αᵉ)
  where

  htpy-diagonal-map-refl-htpy-lifting-structure-squareᵉ :
    diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ ~ᵉ
    diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ
  htpy-diagonal-map-refl-htpy-lifting-structure-squareᵉ = refl-htpyᵉ

  coh-refl-htpy-lifting-structure-squareᵉ :
    coherence-htpy-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ kᵉ
      ( htpy-diagonal-map-refl-htpy-lifting-structure-squareᵉ)
  coh-refl-htpy-lifting-structure-squareᵉ =
    right-unit-law-concat-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ
      ( pullback-homᵉ fᵉ gᵉ (diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ))
      ( is-lifting-diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ)

  refl-htpy-lifting-structure-squareᵉ : htpy-lifting-structure-squareᵉ fᵉ gᵉ αᵉ kᵉ kᵉ
  pr1ᵉ refl-htpy-lifting-structure-squareᵉ =
    htpy-diagonal-map-refl-htpy-lifting-structure-squareᵉ
  pr2ᵉ refl-htpy-lifting-structure-squareᵉ =
    coh-refl-htpy-lifting-structure-squareᵉ
```

### Trivial lifting squares

Theᵉ diagramᵉ

```text
   Aᵉ          Xᵉ
   |        ∧ᵉ |
 fᵉ |   jᵉ  /ᵉ   |gᵉ
   |    /ᵉ     |
   ∨ᵉ  /ᵉ       ∨ᵉ
   Bᵉ          Yᵉ
```

givesᵉ riseᵉ to aᵉ liftingᵉ squareᵉ

```text
       jᵉ ∘ᵉ fᵉ
    Aᵉ ------->ᵉ Xᵉ
    |        ∧ᵉ |
  fᵉ |   jᵉ  /ᵉ   | gᵉ
    |    /ᵉ     |
    ∨ᵉ  /ᵉ       ∨ᵉ
    Bᵉ ------->ᵉ Yᵉ
       gᵉ ∘ᵉ jᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
  where

  is-diagonal-lift-square-pullback-homᵉ :
    (jᵉ : Bᵉ → Xᵉ) → is-diagonal-lift-squareᵉ fᵉ gᵉ (pullback-homᵉ fᵉ gᵉ jᵉ) jᵉ
  is-diagonal-lift-square-pullback-homᵉ jᵉ =
    refl-htpy-hom-arrowᵉ fᵉ gᵉ (pullback-homᵉ fᵉ gᵉ jᵉ)
```

## Properties

### The types of lifting squares are equivalent to the fibers of the pullback-hom

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  inv-compute-fiber-pullback-homᵉ :
    fiberᵉ (pullback-homᵉ fᵉ gᵉ) hᵉ ≃ᵉ lifting-structure-squareᵉ fᵉ gᵉ hᵉ
  inv-compute-fiber-pullback-homᵉ =
    equiv-totᵉ
      ( λ jᵉ →
        extensionality-hom-arrowᵉ fᵉ gᵉ _ _ ∘eᵉ
        equiv-invᵉ (pullback-homᵉ fᵉ gᵉ jᵉ) hᵉ)

  compute-fiber-pullback-homᵉ :
    lifting-structure-squareᵉ fᵉ gᵉ hᵉ ≃ᵉ fiberᵉ (pullback-homᵉ fᵉ gᵉ) hᵉ
  compute-fiber-pullback-homᵉ = inv-equivᵉ inv-compute-fiber-pullback-homᵉ
```

### Characterization of identifications of lifting squares

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  (lᵉ : lifting-structure-squareᵉ fᵉ gᵉ αᵉ)
  where

  htpy-eq-lifting-structure-squareᵉ :
    (kᵉ : lifting-structure-squareᵉ fᵉ gᵉ αᵉ) →
    lᵉ ＝ᵉ kᵉ → htpy-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ kᵉ
  htpy-eq-lifting-structure-squareᵉ .lᵉ reflᵉ =
    refl-htpy-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ

  is-torsorial-htpy-lifting-structure-squareᵉ :
    is-torsorialᵉ (htpy-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ)
  is-torsorial-htpy-lifting-structure-squareᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ _)
      ( diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-htpy-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ
        ( pullback-homᵉ fᵉ gᵉ (diagonal-map-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ))
        ( _))

  is-equiv-htpy-eq-lifting-structure-squareᵉ :
    (kᵉ : lifting-structure-squareᵉ fᵉ gᵉ αᵉ) →
    is-equivᵉ (htpy-eq-lifting-structure-squareᵉ kᵉ)
  is-equiv-htpy-eq-lifting-structure-squareᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-lifting-structure-squareᵉ)
      ( htpy-eq-lifting-structure-squareᵉ)

  extensionality-lifting-structure-squareᵉ :
    (kᵉ : lifting-structure-squareᵉ fᵉ gᵉ αᵉ) →
    (lᵉ ＝ᵉ kᵉ) ≃ᵉ htpy-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ kᵉ
  pr1ᵉ (extensionality-lifting-structure-squareᵉ kᵉ) =
    htpy-eq-lifting-structure-squareᵉ kᵉ
  pr2ᵉ (extensionality-lifting-structure-squareᵉ kᵉ) =
    is-equiv-htpy-eq-lifting-structure-squareᵉ kᵉ

  eq-htpy-lifting-structure-squareᵉ :
    (kᵉ : lifting-structure-squareᵉ fᵉ gᵉ αᵉ) →
    htpy-lifting-structure-squareᵉ fᵉ gᵉ αᵉ lᵉ kᵉ → lᵉ ＝ᵉ kᵉ
  eq-htpy-lifting-structure-squareᵉ kᵉ =
    map-inv-equivᵉ (extensionality-lifting-structure-squareᵉ kᵉ)
```

## External links

-ᵉ [lift](https://ncatlab.org/nlab/show/liftᵉ) atᵉ $n$Lab.ᵉ