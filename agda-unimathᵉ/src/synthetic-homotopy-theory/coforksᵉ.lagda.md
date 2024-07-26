# Coforks

```agda
module synthetic-homotopy-theory.coforksᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.codiagonal-maps-of-typesᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-double-arrowsᵉ
open import foundation.equivalences-span-diagramsᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-double-arrowsᵉ
open import foundation.morphisms-span-diagramsᵉ
open import foundation.span-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.cocones-under-spansᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "cofork"ᵉ Disambiguation="ofᵉ types"ᵉ Agda=coforkᵉ}} ofᵉ aᵉ
[doubleᵉ arrow](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`ᵉ with vertextᵉ `X`ᵉ isᵉ aᵉ
mapᵉ `eᵉ : Bᵉ → X`ᵉ togetherᵉ with aᵉ [homotopy](foundation.homotopies.mdᵉ)
`Hᵉ : eᵉ ∘ᵉ fᵉ ~ᵉ eᵉ ∘ᵉ g`.ᵉ Theᵉ nameᵉ comesᵉ fromᵉ theᵉ diagramᵉ

```text
     gᵉ
   ----->ᵉ     eᵉ
 Aᵉ ----->ᵉ Bᵉ ----->ᵉ Xᵉ
     fᵉ
```

whichᵉ looksᵉ likeᵉ aᵉ forkᵉ ifᵉ youᵉ flipᵉ theᵉ arrows,ᵉ henceᵉ aᵉ cofork.ᵉ

Coforksᵉ areᵉ anᵉ analogueᵉ ofᵉ
[coconesᵉ underᵉ spans](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) forᵉ
doubleᵉ arrows.ᵉ Theᵉ universalᵉ coforkᵉ ofᵉ aᵉ doubleᵉ arrowᵉ isᵉ theirᵉ
[coequalizer](synthetic-homotopy-theory.coequalizers.md).ᵉ

## Definitions

### Coforks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ)
  where

  coherence-coforkᵉ : {Xᵉ : UUᵉ l3ᵉ} → (codomain-double-arrowᵉ aᵉ → Xᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ)
  coherence-coforkᵉ eᵉ =
    eᵉ ∘ᵉ left-map-double-arrowᵉ aᵉ ~ᵉ
    eᵉ ∘ᵉ right-map-double-arrowᵉ aᵉ

  coforkᵉ : UUᵉ l3ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  coforkᵉ Xᵉ =
    Σᵉ (codomain-double-arrowᵉ aᵉ → Xᵉ) (coherence-coforkᵉ)

  module _
    {Xᵉ : UUᵉ l3ᵉ} (eᵉ : coforkᵉ Xᵉ)
    where

    map-coforkᵉ : codomain-double-arrowᵉ aᵉ → Xᵉ
    map-coforkᵉ = pr1ᵉ eᵉ

    coh-coforkᵉ : coherence-coforkᵉ map-coforkᵉ
    coh-coforkᵉ = pr2ᵉ eᵉ
```

### Homotopies of coforks

Aᵉ homotopyᵉ betweenᵉ coforksᵉ with theᵉ sameᵉ vertexᵉ isᵉ givenᵉ byᵉ aᵉ homotopyᵉ betweenᵉ
theᵉ twoᵉ maps,ᵉ togetherᵉ with aᵉ coherenceᵉ datumᵉ assertingᵉ thatᵉ weᵉ mayᵉ applyᵉ theᵉ
givenᵉ homotopyᵉ andᵉ theᵉ appropriateᵉ coforkᵉ homotopyᵉ in eitherᵉ order.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  where

  coherence-htpy-coforkᵉ :
    (eᵉ e'ᵉ : coforkᵉ aᵉ Xᵉ) →
    (Kᵉ : map-coforkᵉ aᵉ eᵉ ~ᵉ map-coforkᵉ aᵉ e'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l3ᵉ)
  coherence-htpy-coforkᵉ eᵉ e'ᵉ Kᵉ =
    ( (coh-coforkᵉ aᵉ eᵉ) ∙hᵉ (Kᵉ ·rᵉ right-map-double-arrowᵉ aᵉ)) ~ᵉ
    ( (Kᵉ ·rᵉ left-map-double-arrowᵉ aᵉ) ∙hᵉ (coh-coforkᵉ aᵉ e'ᵉ))

  htpy-coforkᵉ : coforkᵉ aᵉ Xᵉ → coforkᵉ aᵉ Xᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  htpy-coforkᵉ eᵉ e'ᵉ =
    Σᵉ ( map-coforkᵉ aᵉ eᵉ ~ᵉ map-coforkᵉ aᵉ e'ᵉ)
      ( coherence-htpy-coforkᵉ eᵉ e'ᵉ)
```

### Postcomposing coforks

Givenᵉ aᵉ coforkᵉ `eᵉ : Bᵉ → X`ᵉ andᵉ aᵉ mapᵉ `hᵉ : Xᵉ → Y`,ᵉ weᵉ mayᵉ composeᵉ theᵉ twoᵉ to getᵉ
aᵉ newᵉ coforkᵉ `hᵉ ∘ᵉ e`.ᵉ

```text
     gᵉ
   ----->ᵉ     eᵉ        hᵉ
 Aᵉ ----->ᵉ Bᵉ ----->ᵉ Xᵉ ----->ᵉ Yᵉ
     fᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  cofork-mapᵉ : {lᵉ : Level} {Yᵉ : UUᵉ lᵉ} → (Xᵉ → Yᵉ) → coforkᵉ aᵉ Yᵉ
  pr1ᵉ (cofork-mapᵉ hᵉ) = hᵉ ∘ᵉ map-coforkᵉ aᵉ eᵉ
  pr2ᵉ (cofork-mapᵉ hᵉ) = hᵉ ·lᵉ (coh-coforkᵉ aᵉ eᵉ)
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  where

  refl-htpy-coforkᵉ : (eᵉ : coforkᵉ aᵉ Xᵉ) → htpy-coforkᵉ aᵉ eᵉ eᵉ
  pr1ᵉ (refl-htpy-coforkᵉ eᵉ) = refl-htpyᵉ
  pr2ᵉ (refl-htpy-coforkᵉ eᵉ) = right-unit-htpyᵉ

  htpy-cofork-eqᵉ :
    (eᵉ e'ᵉ : coforkᵉ aᵉ Xᵉ) → (eᵉ ＝ᵉ e'ᵉ) → htpy-coforkᵉ aᵉ eᵉ e'ᵉ
  htpy-cofork-eqᵉ eᵉ .eᵉ reflᵉ = refl-htpy-coforkᵉ eᵉ

  abstract
    is-torsorial-htpy-coforkᵉ :
      (eᵉ : coforkᵉ aᵉ Xᵉ) → is-torsorialᵉ (htpy-coforkᵉ aᵉ eᵉ)
    is-torsorial-htpy-coforkᵉ eᵉ =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (map-coforkᵉ aᵉ eᵉ))
        ( map-coforkᵉ aᵉ eᵉ ,ᵉ refl-htpyᵉ)
        ( is-contr-is-equiv'ᵉ
          ( Σᵉ ( coherence-coforkᵉ aᵉ (map-coforkᵉ aᵉ eᵉ))
              ( λ Kᵉ → coh-coforkᵉ aᵉ eᵉ ~ᵉ Kᵉ))
          ( totᵉ (λ Kᵉ Mᵉ → right-unit-htpyᵉ ∙hᵉ Mᵉ))
          ( is-equiv-tot-is-fiberwise-equivᵉ
            ( is-equiv-concat-htpyᵉ right-unit-htpyᵉ))
          ( is-torsorial-htpyᵉ (coh-coforkᵉ aᵉ eᵉ)))

    is-equiv-htpy-cofork-eqᵉ :
      (eᵉ e'ᵉ : coforkᵉ aᵉ Xᵉ) → is-equivᵉ (htpy-cofork-eqᵉ eᵉ e'ᵉ)
    is-equiv-htpy-cofork-eqᵉ eᵉ =
      fundamental-theorem-idᵉ (is-torsorial-htpy-coforkᵉ eᵉ) (htpy-cofork-eqᵉ eᵉ)

  eq-htpy-coforkᵉ : (eᵉ e'ᵉ : coforkᵉ aᵉ Xᵉ) → htpy-coforkᵉ aᵉ eᵉ e'ᵉ → eᵉ ＝ᵉ e'ᵉ
  eq-htpy-coforkᵉ eᵉ e'ᵉ = map-inv-is-equivᵉ (is-equiv-htpy-cofork-eqᵉ eᵉ e'ᵉ)
```

### Postcomposing a cofork by identity is the identity

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) {Xᵉ : UUᵉ l3ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  cofork-map-idᵉ : cofork-mapᵉ aᵉ eᵉ idᵉ ＝ᵉ eᵉ
  cofork-map-idᵉ =
    eq-htpy-coforkᵉ aᵉ
      ( cofork-mapᵉ aᵉ eᵉ idᵉ)
      ( eᵉ)
      ( ( refl-htpyᵉ) ,ᵉ
        ( right-unit-htpyᵉ ∙hᵉ left-unit-law-left-whisker-compᵉ (coh-coforkᵉ aᵉ eᵉ)))
```

### Postcomposing coforks distributes over function composition

```text
     gᵉ
   ----->ᵉ     eᵉ        hᵉ        kᵉ
 Aᵉ ----->ᵉ Bᵉ ----->ᵉ Xᵉ ----->ᵉ Yᵉ ----->ᵉ Zᵉ
     fᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ)
  {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} {Zᵉ : UUᵉ l5ᵉ}
  (eᵉ : coforkᵉ aᵉ Xᵉ)
  where

  cofork-map-compᵉ :
    (hᵉ : Xᵉ → Yᵉ) (kᵉ : Yᵉ → Zᵉ) →
    cofork-mapᵉ aᵉ eᵉ (kᵉ ∘ᵉ hᵉ) ＝ᵉ cofork-mapᵉ aᵉ (cofork-mapᵉ aᵉ eᵉ hᵉ) kᵉ
  cofork-map-compᵉ hᵉ kᵉ =
    eq-htpy-coforkᵉ aᵉ
      ( cofork-mapᵉ aᵉ eᵉ (kᵉ ∘ᵉ hᵉ))
      ( cofork-mapᵉ aᵉ (cofork-mapᵉ aᵉ eᵉ hᵉ) kᵉ)
      ( ( refl-htpyᵉ) ,ᵉ
        ( ( right-unit-htpyᵉ) ∙hᵉ
          ( inv-preserves-comp-left-whisker-compᵉ kᵉ hᵉ (coh-coforkᵉ aᵉ eᵉ))))
```

### Coforks are special cases of cocones under spans

Theᵉ typeᵉ ofᵉ coforksᵉ ofᵉ aᵉ doubleᵉ arrowᵉ `f,ᵉ gᵉ : Aᵉ → B`ᵉ isᵉ equivalentᵉ to theᵉ typeᵉ
ofᵉ [cocones](synthetic-homotopy-theory.cocones-under-spans.mdᵉ) underᵉ theᵉ spanᵉ

```text
     ∇ᵉ         [f,gᵉ]
Aᵉ <-----ᵉ Aᵉ +ᵉ Aᵉ ----->ᵉ B.ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ)
  where

  vertical-map-span-cocone-coforkᵉ :
    domain-double-arrowᵉ aᵉ +ᵉ domain-double-arrowᵉ aᵉ → domain-double-arrowᵉ aᵉ
  vertical-map-span-cocone-coforkᵉ = codiagonalᵉ (domain-double-arrowᵉ aᵉ)

  horizontal-map-span-cocone-coforkᵉ :
    domain-double-arrowᵉ aᵉ +ᵉ domain-double-arrowᵉ aᵉ → codomain-double-arrowᵉ aᵉ
  horizontal-map-span-cocone-coforkᵉ (inlᵉ xᵉ) = left-map-double-arrowᵉ aᵉ xᵉ
  horizontal-map-span-cocone-coforkᵉ (inrᵉ xᵉ) = right-map-double-arrowᵉ aᵉ xᵉ

  span-diagram-coforkᵉ : span-diagramᵉ l1ᵉ l2ᵉ l1ᵉ
  span-diagram-coforkᵉ =
    make-span-diagramᵉ
      ( vertical-map-span-cocone-coforkᵉ)
      ( horizontal-map-span-cocone-coforkᵉ)

  module _
    {l3ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ}
    where

    cofork-cocone-codiagonalᵉ :
      coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ)
        ( horizontal-map-span-cocone-coforkᵉ)
        ( Xᵉ) →
      coforkᵉ aᵉ Xᵉ
    pr1ᵉ (cofork-cocone-codiagonalᵉ cᵉ) =
      vertical-map-coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ)
        ( horizontal-map-span-cocone-coforkᵉ)
        ( cᵉ)
    pr2ᵉ (cofork-cocone-codiagonalᵉ cᵉ) =
      ( ( inv-htpyᵉ
          ( coherence-square-coconeᵉ
            ( vertical-map-span-cocone-coforkᵉ)
            ( horizontal-map-span-cocone-coforkᵉ)
            ( cᵉ))) ·rᵉ
        ( inlᵉ)) ∙hᵉ
      ( ( coherence-square-coconeᵉ
          ( vertical-map-span-cocone-coforkᵉ)
          ( horizontal-map-span-cocone-coforkᵉ)
          ( cᵉ)) ·rᵉ
        ( inrᵉ))

    horizontal-map-cocone-coforkᵉ : coforkᵉ aᵉ Xᵉ → domain-double-arrowᵉ aᵉ → Xᵉ
    horizontal-map-cocone-coforkᵉ eᵉ = map-coforkᵉ aᵉ eᵉ ∘ᵉ left-map-double-arrowᵉ aᵉ

    vertical-map-cocone-coforkᵉ : coforkᵉ aᵉ Xᵉ → codomain-double-arrowᵉ aᵉ → Xᵉ
    vertical-map-cocone-coforkᵉ eᵉ = map-coforkᵉ aᵉ eᵉ

    coherence-square-cocone-coforkᵉ :
      (eᵉ : coforkᵉ aᵉ Xᵉ) →
      coherence-square-mapsᵉ
        ( horizontal-map-span-cocone-coforkᵉ)
        ( vertical-map-span-cocone-coforkᵉ)
        ( vertical-map-cocone-coforkᵉ eᵉ)
        ( horizontal-map-cocone-coforkᵉ eᵉ)
    coherence-square-cocone-coforkᵉ eᵉ (inlᵉ xᵉ) = reflᵉ
    coherence-square-cocone-coforkᵉ eᵉ (inrᵉ xᵉ) = coh-coforkᵉ aᵉ eᵉ xᵉ

    cocone-codiagonal-coforkᵉ :
      coforkᵉ aᵉ Xᵉ →
      coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ)
        ( horizontal-map-span-cocone-coforkᵉ)
        ( Xᵉ)
    pr1ᵉ (cocone-codiagonal-coforkᵉ eᵉ) = horizontal-map-cocone-coforkᵉ eᵉ
    pr1ᵉ (pr2ᵉ (cocone-codiagonal-coforkᵉ eᵉ)) = vertical-map-cocone-coforkᵉ eᵉ
    pr2ᵉ (pr2ᵉ (cocone-codiagonal-coforkᵉ eᵉ)) = coherence-square-cocone-coforkᵉ eᵉ

    abstract
      is-section-cocone-codiagonal-coforkᵉ :
        cofork-cocone-codiagonalᵉ ∘ᵉ cocone-codiagonal-coforkᵉ ~ᵉ idᵉ
      is-section-cocone-codiagonal-coforkᵉ eᵉ =
        eq-htpy-coforkᵉ aᵉ
          ( cofork-cocone-codiagonalᵉ (cocone-codiagonal-coforkᵉ eᵉ))
          ( eᵉ)
          ( refl-htpyᵉ ,ᵉ right-unit-htpyᵉ)

      is-retraction-cocone-codiagonal-forkᵉ :
        cocone-codiagonal-coforkᵉ ∘ᵉ cofork-cocone-codiagonalᵉ ~ᵉ idᵉ
      is-retraction-cocone-codiagonal-forkᵉ cᵉ =
        eq-htpy-coconeᵉ
          ( vertical-map-span-cocone-coforkᵉ)
          ( horizontal-map-span-cocone-coforkᵉ)
          ( cocone-codiagonal-coforkᵉ (cofork-cocone-codiagonalᵉ cᵉ))
          ( cᵉ)
          ( ( ( inv-htpyᵉ
                ( coherence-square-coconeᵉ
                  ( vertical-map-span-cocone-coforkᵉ)
                  ( horizontal-map-span-cocone-coforkᵉ)
                  ( cᵉ))) ·rᵉ
              ( inlᵉ)) ,ᵉ
            ( refl-htpyᵉ) ,ᵉ
            ( ind-coproductᵉ _
              ( inv-htpy-left-inv-htpyᵉ
                ( ( coherence-square-coconeᵉ
                    ( vertical-map-span-cocone-coforkᵉ)
                    ( horizontal-map-span-cocone-coforkᵉ)
                    ( cᵉ)) ·rᵉ
                  ( inlᵉ)))
              ( right-unit-htpyᵉ)))

    is-equiv-cofork-cocone-codiagonalᵉ :
      is-equivᵉ cofork-cocone-codiagonalᵉ
    is-equiv-cofork-cocone-codiagonalᵉ =
      is-equiv-is-invertibleᵉ
        ( cocone-codiagonal-coforkᵉ)
        ( is-section-cocone-codiagonal-coforkᵉ)
        ( is-retraction-cocone-codiagonal-forkᵉ)

    equiv-cocone-codiagonal-coforkᵉ :
      coconeᵉ
        ( vertical-map-span-cocone-coforkᵉ)
        ( horizontal-map-span-cocone-coforkᵉ)
        ( Xᵉ) ≃ᵉ
      coforkᵉ aᵉ Xᵉ
    pr1ᵉ equiv-cocone-codiagonal-coforkᵉ = cofork-cocone-codiagonalᵉ
    pr2ᵉ equiv-cocone-codiagonal-coforkᵉ = is-equiv-cofork-cocone-codiagonalᵉ

  triangle-cofork-coconeᵉ :
    {l3ᵉ l4ᵉ : Level} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} →
    (eᵉ : coforkᵉ aᵉ Xᵉ) →
    coherence-triangle-mapsᵉ
      ( cofork-mapᵉ aᵉ eᵉ {Yᵉ = Yᵉ})
      ( cofork-cocone-codiagonalᵉ)
      ( cocone-mapᵉ
        ( vertical-map-span-cocone-coforkᵉ)
        ( horizontal-map-span-cocone-coforkᵉ)
        ( cocone-codiagonal-coforkᵉ eᵉ))
  triangle-cofork-coconeᵉ eᵉ hᵉ =
    eq-htpy-coforkᵉ aᵉ
      ( cofork-mapᵉ aᵉ eᵉ hᵉ)
      ( cofork-cocone-codiagonalᵉ
        ( cocone-mapᵉ
          ( vertical-map-span-cocone-coforkᵉ)
          ( horizontal-map-span-cocone-coforkᵉ)
          ( cocone-codiagonal-coforkᵉ eᵉ)
          ( hᵉ)))
      ( refl-htpyᵉ ,ᵉ
        right-unit-htpyᵉ)
```

### Morphisms between double arrows induce morphisms between cofork span diagrams

Aᵉ [morphismᵉ ofᵉ doubleᵉ arrows](foundation.morphisms-double-arrows.mdᵉ)

```text
           iᵉ
     Aᵉ -------->ᵉ Xᵉ
    | |         | |
  fᵉ | | gᵉ     hᵉ | | kᵉ
    | |         | |
    ∨ᵉ ∨ᵉ         ∨ᵉ ∨ᵉ
     Bᵉ -------->ᵉ Yᵉ
           jᵉ
```

inducesᵉ aᵉ [morphismᵉ ofᵉ spanᵉ diagrams](foundation.morphisms-span-diagrams.mdᵉ)

```text
          ∇ᵉ           [f,gᵉ]
    Aᵉ <-------ᵉ Aᵉ +ᵉ Aᵉ ------->ᵉ Bᵉ
    |            |            |
  iᵉ |            | iᵉ +ᵉ iᵉ      | jᵉ
    ∨ᵉ            ∨ᵉ            ∨ᵉ
    Xᵉ <-------ᵉ Xᵉ +ᵉ Xᵉ ------->ᵉ Yᵉ
          ∇ᵉ           [h,kᵉ]
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (a'ᵉ : double-arrowᵉ l3ᵉ l4ᵉ)
  (hᵉ : hom-double-arrowᵉ aᵉ a'ᵉ)
  where

  spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ :
    domain-double-arrowᵉ aᵉ +ᵉ domain-double-arrowᵉ aᵉ →
    domain-double-arrowᵉ a'ᵉ +ᵉ domain-double-arrowᵉ a'ᵉ
  spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ =
    map-coproductᵉ
      ( domain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)
      ( domain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)

  left-square-hom-span-diagram-cofork-hom-double-arrowᵉ :
    coherence-square-maps'ᵉ
      ( vertical-map-span-cocone-coforkᵉ aᵉ)
      ( spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ)
      ( domain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)
      ( vertical-map-span-cocone-coforkᵉ a'ᵉ)
  left-square-hom-span-diagram-cofork-hom-double-arrowᵉ =
    ind-coproductᵉ _ refl-htpyᵉ refl-htpyᵉ

  right-square-hom-span-diagram-cofork-hom-double-arrowᵉ :
    coherence-square-maps'ᵉ
      ( horizontal-map-span-cocone-coforkᵉ aᵉ)
      ( spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ)
      ( codomain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)
      ( horizontal-map-span-cocone-coforkᵉ a'ᵉ)
  right-square-hom-span-diagram-cofork-hom-double-arrowᵉ =
    ind-coproductᵉ _
      ( left-square-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)
      ( right-square-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)

  hom-span-diagram-cofork-hom-double-arrowᵉ :
    hom-span-diagramᵉ
      ( span-diagram-coforkᵉ aᵉ)
      ( span-diagram-coforkᵉ a'ᵉ)
  pr1ᵉ (hom-span-diagram-cofork-hom-double-arrowᵉ) =
    domain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ
  pr1ᵉ (pr2ᵉ (hom-span-diagram-cofork-hom-double-arrowᵉ)) =
    codomain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (hom-span-diagram-cofork-hom-double-arrowᵉ))) =
    spanning-map-hom-span-diagram-cofork-hom-double-arrowᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (hom-span-diagram-cofork-hom-double-arrowᵉ)))) =
    left-square-hom-span-diagram-cofork-hom-double-arrowᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (hom-span-diagram-cofork-hom-double-arrowᵉ)))) =
    right-square-hom-span-diagram-cofork-hom-double-arrowᵉ
```

### Equivalences between double arrows induce equivalences between cofork span diagrams

Anᵉ [equivalenceᵉ ofᵉ doubleᵉ arrows](foundation.equivalences-double-arrows.mdᵉ)

```text
           iᵉ
     Aᵉ -------->ᵉ Xᵉ
    | |    ≃ᵉ    | |
  fᵉ | | gᵉ     hᵉ | | kᵉ
    | |         | |
    ∨ᵉ ∨ᵉ    ≃ᵉ    ∨ᵉ ∨ᵉ
     Bᵉ -------->ᵉ Yᵉ
           jᵉ
```

inducesᵉ anᵉ
[equivalenceᵉ ofᵉ spanᵉ diagrams](foundation.equivalences-span-diagrams.mdᵉ)

```text
          ∇ᵉ           [f,gᵉ]
    Aᵉ <-------ᵉ Aᵉ +ᵉ Aᵉ ------->ᵉ Bᵉ
    |            |            |
  iᵉ | ≃ᵉ        ≃ᵉ | iᵉ +ᵉ iᵉ    ≃ᵉ | jᵉ
    ∨ᵉ            ∨ᵉ            ∨ᵉ
    Xᵉ <-------ᵉ Xᵉ +ᵉ Xᵉ ------->ᵉ Yᵉ
          ∇ᵉ           [h,kᵉ]
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} (aᵉ : double-arrowᵉ l1ᵉ l2ᵉ) (a'ᵉ : double-arrowᵉ l3ᵉ l4ᵉ)
  (eᵉ : equiv-double-arrowᵉ aᵉ a'ᵉ)
  where

  spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrowᵉ :
    domain-double-arrowᵉ aᵉ +ᵉ domain-double-arrowᵉ aᵉ ≃ᵉ
    domain-double-arrowᵉ a'ᵉ +ᵉ domain-double-arrowᵉ a'ᵉ
  spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrowᵉ =
    equiv-coproductᵉ
      ( domain-equiv-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
      ( domain-equiv-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)

  left-square-equiv-span-diagram-cofork-equiv-double-arrowᵉ :
    coherence-square-maps'ᵉ
      ( vertical-map-span-cocone-coforkᵉ aᵉ)
      ( map-equivᵉ spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrowᵉ)
      ( domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
      ( vertical-map-span-cocone-coforkᵉ a'ᵉ)
  left-square-equiv-span-diagram-cofork-equiv-double-arrowᵉ =
    ind-coproductᵉ _ refl-htpyᵉ refl-htpyᵉ

  right-square-equiv-span-diagram-cofork-equiv-double-arrowᵉ :
    coherence-square-maps'ᵉ
      ( horizontal-map-span-cocone-coforkᵉ aᵉ)
      ( map-equivᵉ spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrowᵉ)
      ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
      ( horizontal-map-span-cocone-coforkᵉ a'ᵉ)
  right-square-equiv-span-diagram-cofork-equiv-double-arrowᵉ =
    ind-coproductᵉ _
      ( left-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
      ( right-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)

  equiv-span-diagram-cofork-equiv-double-arrowᵉ :
    equiv-span-diagramᵉ
      ( span-diagram-coforkᵉ aᵉ)
      ( span-diagram-coforkᵉ a'ᵉ)
  pr1ᵉ (equiv-span-diagram-cofork-equiv-double-arrowᵉ) =
    domain-equiv-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ
  pr1ᵉ (pr2ᵉ (equiv-span-diagram-cofork-equiv-double-arrowᵉ)) =
    codomain-equiv-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (equiv-span-diagram-cofork-equiv-double-arrowᵉ))) =
    spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrowᵉ
  pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (equiv-span-diagram-cofork-equiv-double-arrowᵉ)))) =
    left-square-equiv-span-diagram-cofork-equiv-double-arrowᵉ
  pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (equiv-span-diagram-cofork-equiv-double-arrowᵉ)))) =
    right-square-equiv-span-diagram-cofork-equiv-double-arrowᵉ
```