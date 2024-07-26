# Homotopies of morphisms of arrows

```agda
module foundation.homotopies-morphisms-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-identificationsᵉ
open import foundation.commuting-triangles-of-identificationsᵉ
open import foundation.cones-over-cospan-diagramsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import foundation-core.commuting-squares-of-homotopiesᵉ
open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ) `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ
andᵉ `(i'ᵉ ,ᵉ j'ᵉ ,ᵉ H')`ᵉ fromᵉ `f`ᵉ to `g`,ᵉ asᵉ in theᵉ diagramsᵉ

```text
        iᵉ                   i'ᵉ
    Aᵉ ----->ᵉ Xᵉ          Aᵉ ----->ᵉ Xᵉ
    |        |          |        |
  fᵉ |        | gᵉ      fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ          ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ          Bᵉ ----->ᵉ Y.ᵉ
        jᵉ                   j'ᵉ
```

Aᵉ {{#conceptᵉ "homotopyᵉ ofᵉ morphismsᵉ ofᵉ arrows"ᵉ}} fromᵉ `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ to
`(i'ᵉ ,ᵉ j'ᵉ ,ᵉ H')`ᵉ isᵉ aᵉ tripleᵉ `(Iᵉ ,ᵉ Jᵉ ,ᵉ K)`ᵉ consistingᵉ ofᵉ homotopiesᵉ `Iᵉ : iᵉ ~ᵉ i'`ᵉ
andᵉ `Jᵉ : jᵉ ~ᵉ j'`ᵉ andᵉ aᵉ homotopyᵉ `K`ᵉ witnessingᵉ thatᵉ theᵉ
[squareᵉ ofᵉ homotopies](foundation.commuting-squares-of-homotopies.mdᵉ)

```text
           Jᵉ ·rᵉ fᵉ
  (jᵉ ∘ᵉ fᵉ) -------->ᵉ (j'ᵉ ∘ᵉ fᵉ)
     |                 |
   Hᵉ |                 | H'ᵉ
     ∨ᵉ                 ∨ᵉ
  (gᵉ ∘ᵉ iᵉ) -------->ᵉ (gᵉ ∘ᵉ i'ᵉ)
           gᵉ ·lᵉ Iᵉ
```

commutes.ᵉ

## Definitions

### Homotopies of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  coherence-htpy-hom-arrowᵉ :
    (βᵉ : hom-arrowᵉ fᵉ gᵉ)
    (Iᵉ : map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ βᵉ)
    (Jᵉ : map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ βᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-htpy-hom-arrowᵉ βᵉ Iᵉ Jᵉ =
    coherence-square-homotopiesᵉ
      ( Jᵉ ·rᵉ fᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ βᵉ)
      ( gᵉ ·lᵉ Iᵉ)

  htpy-hom-arrowᵉ :
    (βᵉ : hom-arrowᵉ fᵉ gᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-hom-arrowᵉ βᵉ =
    Σᵉ ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ βᵉ)
      ( λ Iᵉ →
        Σᵉ ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ βᵉ)
          ( coherence-htpy-hom-arrowᵉ βᵉ Iᵉ))

  module _
    (βᵉ : hom-arrowᵉ fᵉ gᵉ) (ηᵉ : htpy-hom-arrowᵉ βᵉ)
    where

    htpy-domain-htpy-hom-arrowᵉ :
      map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ βᵉ
    htpy-domain-htpy-hom-arrowᵉ = pr1ᵉ ηᵉ

    htpy-codomain-htpy-hom-arrowᵉ :
      map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ βᵉ
    htpy-codomain-htpy-hom-arrowᵉ = pr1ᵉ (pr2ᵉ ηᵉ)

    coh-htpy-hom-arrowᵉ :
      coherence-square-homotopiesᵉ
        ( htpy-codomain-htpy-hom-arrowᵉ ·rᵉ fᵉ)
        ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( coh-hom-arrowᵉ fᵉ gᵉ βᵉ)
        ( gᵉ ·lᵉ htpy-domain-htpy-hom-arrowᵉ)
    coh-htpy-hom-arrowᵉ = pr2ᵉ (pr2ᵉ ηᵉ)
```

### The reflexivity homotopy of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  htpy-domain-refl-htpy-hom-arrowᵉ :
    map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ
  htpy-domain-refl-htpy-hom-arrowᵉ = refl-htpyᵉ

  htpy-codomain-refl-htpy-hom-arrowᵉ :
    map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ
  htpy-codomain-refl-htpy-hom-arrowᵉ = refl-htpyᵉ

  coh-refl-htpy-hom-arrowᵉ :
    coherence-square-homotopiesᵉ
      ( htpy-codomain-refl-htpy-hom-arrowᵉ ·rᵉ fᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( gᵉ ·lᵉ htpy-domain-refl-htpy-hom-arrowᵉ)
  coh-refl-htpy-hom-arrowᵉ = right-unit-htpyᵉ

  refl-htpy-hom-arrowᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ αᵉ
  pr1ᵉ refl-htpy-hom-arrowᵉ = htpy-domain-refl-htpy-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ refl-htpy-hom-arrowᵉ) = htpy-codomain-refl-htpy-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ refl-htpy-hom-arrowᵉ) = coh-refl-htpy-hom-arrowᵉ
```

## Operations

### Concatenation of homotopies of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ βᵉ γᵉ : hom-arrowᵉ fᵉ gᵉ)
  (Hᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ) (Kᵉ : htpy-hom-arrowᵉ fᵉ gᵉ βᵉ γᵉ)
  where

  htpy-domain-concat-htpy-hom-arrowᵉ :
    map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ γᵉ
  htpy-domain-concat-htpy-hom-arrowᵉ =
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ ∙hᵉ
    htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ γᵉ Kᵉ

  htpy-codomain-concat-htpy-hom-arrowᵉ :
    map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ~ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ γᵉ
  htpy-codomain-concat-htpy-hom-arrowᵉ =
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ ∙hᵉ
    htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ γᵉ Kᵉ

  coh-concat-htpy-hom-arrowᵉ :
    coherence-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ γᵉ
      ( htpy-domain-concat-htpy-hom-arrowᵉ)
      ( htpy-codomain-concat-htpy-hom-arrowᵉ)
  coh-concat-htpy-hom-arrowᵉ aᵉ =
    ( left-whisker-concatᵉ
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
      ( ap-concatᵉ gᵉ
        ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ)
        ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ γᵉ Kᵉ aᵉ))) ∙ᵉ
    ( horizontal-pasting-coherence-square-identificationsᵉ
      ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ (fᵉ aᵉ))
      ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ γᵉ Kᵉ (fᵉ aᵉ))
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ βᵉ aᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ γᵉ aᵉ)
      ( (gᵉ ·lᵉ htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ) aᵉ)
      ( (gᵉ ·lᵉ htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ γᵉ Kᵉ) aᵉ)
      ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ)
      ( coh-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ γᵉ Kᵉ aᵉ))

  concat-htpy-hom-arrowᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ γᵉ
  pr1ᵉ concat-htpy-hom-arrowᵉ = htpy-domain-concat-htpy-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ concat-htpy-hom-arrowᵉ) = htpy-codomain-concat-htpy-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ concat-htpy-hom-arrowᵉ) = coh-concat-htpy-hom-arrowᵉ
```

### Inverses of homotopies of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ βᵉ : hom-arrowᵉ fᵉ gᵉ) (Hᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ)
  where

  htpy-domain-inv-htpy-hom-arrowᵉ :
    map-domain-hom-arrowᵉ fᵉ gᵉ βᵉ ~ᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ
  htpy-domain-inv-htpy-hom-arrowᵉ =
    inv-htpyᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ)

  htpy-codomain-inv-htpy-hom-arrowᵉ :
    map-codomain-hom-arrowᵉ fᵉ gᵉ βᵉ ~ᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ
  htpy-codomain-inv-htpy-hom-arrowᵉ =
    inv-htpyᵉ (htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ)

  coh-inv-htpy-hom-arrowᵉ :
    coherence-htpy-hom-arrowᵉ fᵉ gᵉ βᵉ αᵉ
      ( htpy-domain-inv-htpy-hom-arrowᵉ)
      ( htpy-codomain-inv-htpy-hom-arrowᵉ)
  coh-inv-htpy-hom-arrowᵉ aᵉ =
    ( left-whisker-concatᵉ
      ( coh-hom-arrowᵉ fᵉ gᵉ βᵉ aᵉ)
      ( ap-invᵉ gᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ))) ∙ᵉ
    ( double-transpose-eq-concat'ᵉ
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
      ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ (fᵉ aᵉ))
      ( apᵉ gᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ))
      ( coh-hom-arrowᵉ fᵉ gᵉ βᵉ aᵉ)
      ( invᵉ (coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ)))

  inv-htpy-hom-arrowᵉ : htpy-hom-arrowᵉ fᵉ gᵉ βᵉ αᵉ
  pr1ᵉ inv-htpy-hom-arrowᵉ = htpy-domain-inv-htpy-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ inv-htpy-hom-arrowᵉ) = htpy-codomain-inv-htpy-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ inv-htpy-hom-arrowᵉ) = coh-inv-htpy-hom-arrowᵉ
```

### Whiskering of homotopies of morphisms of arrows with respect to composition

#### Left whiskering of homotopies of morphisms of arrows with respect to composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (γᵉ : hom-arrowᵉ gᵉ hᵉ) (αᵉ βᵉ : hom-arrowᵉ fᵉ gᵉ) (Hᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ)
  where

  htpy-domain-left-whisker-comp-hom-arrowᵉ :
    map-domain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ ~ᵉ map-domain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ βᵉ
  htpy-domain-left-whisker-comp-hom-arrowᵉ =
    map-domain-hom-arrowᵉ gᵉ hᵉ γᵉ ·lᵉ htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ

  htpy-codomain-left-whisker-comp-hom-arrowᵉ :
    map-codomain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ ~ᵉ
    map-codomain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ βᵉ
  htpy-codomain-left-whisker-comp-hom-arrowᵉ =
    map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ ·lᵉ htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ

  coh-left-whisker-comp-hom-arrowᵉ :
    coherence-htpy-hom-arrowᵉ fᵉ hᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ)
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ βᵉ)
      ( htpy-domain-left-whisker-comp-hom-arrowᵉ)
      ( htpy-codomain-left-whisker-comp-hom-arrowᵉ)
  coh-left-whisker-comp-hom-arrowᵉ aᵉ =
    ( left-whisker-concat-coherence-triangle-identifications'ᵉ
      ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
      ( _)
      ( _)
      ( _)
      ( ( apᵉ
          ( coh-hom-arrowᵉ gᵉ hᵉ γᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ) ∙ᵉ_)
          ( invᵉ
            ( ap-compᵉ hᵉ
              ( map-domain-hom-arrowᵉ gᵉ hᵉ γᵉ)
              ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ)))) ∙ᵉ
        ( nat-htpyᵉ
          ( coh-hom-arrowᵉ gᵉ hᵉ γᵉ)
          ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ)))) ∙ᵉ
    ( right-whisker-concat-coherence-square-identificationsᵉ
      ( apᵉ
        ( map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ)
        ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ (fᵉ aᵉ)))
      ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
      ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ) (coh-hom-arrowᵉ fᵉ gᵉ βᵉ aᵉ))
      ( apᵉ
        ( map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ ∘ᵉ gᵉ)
        ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ))
      ( ( apᵉ
          ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ) ∙ᵉ_)
          ( ap-compᵉ
            ( map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ)
            ( gᵉ)
            ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ))) ∙ᵉ
        ( map-coherence-square-identificationsᵉ
          ( map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ)
          ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ (fᵉ aᵉ))
          ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)
          ( coh-hom-arrowᵉ fᵉ gᵉ βᵉ aᵉ)
          ( apᵉ gᵉ (htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ))
          ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ aᵉ)))
      ( coh-hom-arrowᵉ gᵉ hᵉ γᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ βᵉ aᵉ)))

  left-whisker-comp-hom-arrowᵉ :
    htpy-hom-arrowᵉ fᵉ hᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ)
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ βᵉ)
  pr1ᵉ left-whisker-comp-hom-arrowᵉ =
    htpy-domain-left-whisker-comp-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ left-whisker-comp-hom-arrowᵉ) =
    htpy-codomain-left-whisker-comp-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ left-whisker-comp-hom-arrowᵉ) =
    coh-left-whisker-comp-hom-arrowᵉ
```

#### Right whiskering of homotopies of morphisms of arrows with respect to composition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ)
  (βᵉ γᵉ : hom-arrowᵉ gᵉ hᵉ) (Hᵉ : htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  htpy-domain-right-whisker-comp-hom-arrowᵉ :
    map-domain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ ~ᵉ map-domain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ
  htpy-domain-right-whisker-comp-hom-arrowᵉ =
    htpy-domain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ ·rᵉ map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ

  htpy-codomain-right-whisker-comp-hom-arrowᵉ :
    map-codomain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ ~ᵉ
    map-codomain-comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ
  htpy-codomain-right-whisker-comp-hom-arrowᵉ =
    htpy-codomain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ ·rᵉ map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ

  coh-right-whisker-comp-hom-arrowᵉ :
    coherence-htpy-hom-arrowᵉ fᵉ hᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ)
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ)
      ( htpy-domain-right-whisker-comp-hom-arrowᵉ)
      ( htpy-codomain-right-whisker-comp-hom-arrowᵉ)
  coh-right-whisker-comp-hom-arrowᵉ aᵉ =
    ( left-whisker-concat-coherence-square-identificationsᵉ
      ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
      ( htpy-codomain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ
        ( gᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)))
      ( coh-hom-arrowᵉ gᵉ hᵉ βᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
      ( coh-hom-arrowᵉ gᵉ hᵉ γᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
      ( apᵉ hᵉ
        ( htpy-domain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ
          ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)))
      ( coh-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))) ∙ᵉ
    ( ( assocᵉ
        ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
        ( htpy-codomain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ
          ( gᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)))
        ( coh-hom-arrowᵉ gᵉ hᵉ γᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))) ∙ᵉ
      ( right-whisker-concat-coherence-square-identificationsᵉ
        ( htpy-codomain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ
          ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ (fᵉ aᵉ)))
        ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
        ( apᵉ (map-codomain-hom-arrowᵉ gᵉ hᵉ γᵉ) (coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))
        ( htpy-codomain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ
          ( gᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)))
        ( invᵉ
          ( nat-htpyᵉ
            ( htpy-codomain-htpy-hom-arrowᵉ gᵉ hᵉ βᵉ γᵉ Hᵉ)
            ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ)))
        ( coh-hom-arrowᵉ gᵉ hᵉ γᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ aᵉ))))

  right-whisker-comp-hom-arrowᵉ :
    htpy-hom-arrowᵉ fᵉ hᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ)
      ( comp-hom-arrowᵉ fᵉ gᵉ hᵉ γᵉ αᵉ)
  pr1ᵉ right-whisker-comp-hom-arrowᵉ =
    htpy-domain-right-whisker-comp-hom-arrowᵉ
  pr1ᵉ (pr2ᵉ right-whisker-comp-hom-arrowᵉ) =
    htpy-codomain-right-whisker-comp-hom-arrowᵉ
  pr2ᵉ (pr2ᵉ right-whisker-comp-hom-arrowᵉ) =
    coh-right-whisker-comp-hom-arrowᵉ
```

## Properties

### Homotopies of morphisms of arrows characterize equality of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  is-torsorial-htpy-hom-arrowᵉ :
    is-torsorialᵉ (htpy-hom-arrowᵉ fᵉ gᵉ αᵉ)
  is-torsorial-htpy-hom-arrowᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ))
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ))
        ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ ,ᵉ refl-htpyᵉ)
        ( is-torsorial-htpyᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ ∙hᵉ refl-htpyᵉ)))

  htpy-eq-hom-arrowᵉ : (βᵉ : hom-arrowᵉ fᵉ gᵉ) → (αᵉ ＝ᵉ βᵉ) → htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ
  htpy-eq-hom-arrowᵉ βᵉ reflᵉ = refl-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ

  is-equiv-htpy-eq-hom-arrowᵉ :
    (βᵉ : hom-arrowᵉ fᵉ gᵉ) → is-equivᵉ (htpy-eq-hom-arrowᵉ βᵉ)
  is-equiv-htpy-eq-hom-arrowᵉ =
    fundamental-theorem-idᵉ is-torsorial-htpy-hom-arrowᵉ htpy-eq-hom-arrowᵉ

  extensionality-hom-arrowᵉ :
    (βᵉ : hom-arrowᵉ fᵉ gᵉ) → (αᵉ ＝ᵉ βᵉ) ≃ᵉ htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ
  pr1ᵉ (extensionality-hom-arrowᵉ βᵉ) = htpy-eq-hom-arrowᵉ βᵉ
  pr2ᵉ (extensionality-hom-arrowᵉ βᵉ) = is-equiv-htpy-eq-hom-arrowᵉ βᵉ

  eq-htpy-hom-arrowᵉ :
    (βᵉ : hom-arrowᵉ fᵉ gᵉ) → htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ → αᵉ ＝ᵉ βᵉ
  eq-htpy-hom-arrowᵉ βᵉ = map-inv-equivᵉ (extensionality-hom-arrowᵉ βᵉ)
```

### Homotopies of morphisms of arrows give homotopies of their associated cones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ)
      (αᵉ βᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  coh-htpy-parallell-cone-htpy-hom-arrowᵉ :
    (Hᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ) →
    coherence-htpy-parallel-coneᵉ
      ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ)
      ( refl-htpy'ᵉ gᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ βᵉ)
      ( refl-htpyᵉ)
      ( htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ)
  coh-htpy-parallell-cone-htpy-hom-arrowᵉ Hᵉ =
    ( ap-concat-htpyᵉ (coh-hom-arrowᵉ fᵉ gᵉ αᵉ) right-unit-htpyᵉ) ∙hᵉ
    ( coh-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ)

  htpy-parallell-cone-htpy-hom-arrowᵉ :
    (Hᵉ : htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ) →
    htpy-parallel-coneᵉ
      ( htpy-codomain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ)
      ( refl-htpy'ᵉ gᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( cone-hom-arrowᵉ fᵉ gᵉ βᵉ)
  htpy-parallell-cone-htpy-hom-arrowᵉ Hᵉ =
    ( refl-htpyᵉ ,ᵉ
      htpy-domain-htpy-hom-arrowᵉ fᵉ gᵉ αᵉ βᵉ Hᵉ ,ᵉ
      coh-htpy-parallell-cone-htpy-hom-arrowᵉ Hᵉ)
```

### Associativity of composition of morphisms of arrows

Considerᵉ aᵉ commutingᵉ diagramᵉ ofᵉ theᵉ formᵉ

```text
        α₀ᵉ       β₀ᵉ       γ₀ᵉ
    Aᵉ ----->ᵉ Xᵉ ----->ᵉ Uᵉ ----->ᵉ Kᵉ
    |        |        |        |
  fᵉ |   αᵉ  gᵉ |   βᵉ  hᵉ |   γᵉ    | iᵉ
    ∨ᵉ        ∨ᵉ        ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ ----->ᵉ Vᵉ ----->ᵉ Lᵉ
        α₁ᵉ       β₁ᵉ       γ₁ᵉ
```

Thenᵉ associativityᵉ ofᵉ compositionᵉ ofᵉ morphismsᵉ ofᵉ arrowsᵉ followsᵉ directlyᵉ fromᵉ
associativityᵉ ofᵉ horizontalᵉ pastingᵉ ofᵉ commutativeᵉ squaresᵉ ofᵉ maps.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ l8ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Uᵉ : UUᵉ l5ᵉ} {Vᵉ : UUᵉ l6ᵉ}
  {Kᵉ : UUᵉ l7ᵉ} {Lᵉ : UUᵉ l8ᵉ} (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : Uᵉ → Vᵉ) (iᵉ : Kᵉ → Lᵉ)
  (γᵉ : hom-arrowᵉ hᵉ iᵉ) (βᵉ : hom-arrowᵉ gᵉ hᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  assoc-comp-hom-arrowᵉ :
    htpy-hom-arrowᵉ fᵉ iᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ iᵉ (comp-hom-arrowᵉ gᵉ hᵉ iᵉ γᵉ βᵉ) αᵉ)
      ( comp-hom-arrowᵉ fᵉ hᵉ iᵉ γᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ))
  pr1ᵉ assoc-comp-hom-arrowᵉ = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ assoc-comp-hom-arrowᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ assoc-comp-hom-arrowᵉ) =
    ( right-unit-htpyᵉ) ∙hᵉ
    ( inv-htpyᵉ
      ( assoc-pasting-horizontal-coherence-square-mapsᵉ
        ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( map-domain-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( map-domain-hom-arrowᵉ hᵉ iᵉ γᵉ)
        ( fᵉ)
        ( gᵉ)
        ( hᵉ)
        ( iᵉ)
        ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( map-codomain-hom-arrowᵉ hᵉ iᵉ γᵉ)
        ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
        ( coh-hom-arrowᵉ gᵉ hᵉ βᵉ)
        ( coh-hom-arrowᵉ hᵉ iᵉ γᵉ)))

  inv-assoc-comp-hom-arrowᵉ :
    htpy-hom-arrowᵉ fᵉ iᵉ
      ( comp-hom-arrowᵉ fᵉ hᵉ iᵉ γᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ βᵉ αᵉ))
      ( comp-hom-arrowᵉ fᵉ gᵉ iᵉ (comp-hom-arrowᵉ gᵉ hᵉ iᵉ γᵉ βᵉ) αᵉ)
  pr1ᵉ inv-assoc-comp-hom-arrowᵉ = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ inv-assoc-comp-hom-arrowᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ inv-assoc-comp-hom-arrowᵉ) =
    ( right-unit-htpyᵉ) ∙hᵉ
    ( assoc-pasting-horizontal-coherence-square-mapsᵉ
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-domain-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( map-domain-hom-arrowᵉ hᵉ iᵉ γᵉ)
      ( fᵉ)
      ( gᵉ)
      ( hᵉ)
      ( iᵉ)
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( map-codomain-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( map-codomain-hom-arrowᵉ hᵉ iᵉ γᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-hom-arrowᵉ gᵉ hᵉ βᵉ)
      ( coh-hom-arrowᵉ hᵉ iᵉ γᵉ))
```

### The left unit law for composition of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  left-unit-law-comp-hom-arrowᵉ :
    htpy-hom-arrowᵉ fᵉ gᵉ
      ( comp-hom-arrowᵉ fᵉ gᵉ gᵉ id-hom-arrowᵉ αᵉ)
      ( αᵉ)
  pr1ᵉ left-unit-law-comp-hom-arrowᵉ = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ left-unit-law-comp-hom-arrowᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ left-unit-law-comp-hom-arrowᵉ) =
    ( right-unit-htpyᵉ) ∙hᵉ
    ( right-unit-law-pasting-horizontal-coherence-square-mapsᵉ
      ( map-domain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( fᵉ)
      ( gᵉ)
      ( map-codomain-hom-arrowᵉ fᵉ gᵉ αᵉ)
      ( coh-hom-arrowᵉ fᵉ gᵉ αᵉ))
```

### The right unit law for composition of morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (αᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  right-unit-law-comp-hom-arrowᵉ :
    htpy-hom-arrowᵉ fᵉ gᵉ
      ( comp-hom-arrowᵉ fᵉ fᵉ gᵉ αᵉ id-hom-arrowᵉ)
      ( αᵉ)
  pr1ᵉ right-unit-law-comp-hom-arrowᵉ = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ right-unit-law-comp-hom-arrowᵉ) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ right-unit-law-comp-hom-arrowᵉ) = right-unit-htpyᵉ
```