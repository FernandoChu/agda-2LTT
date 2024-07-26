# Cocones under spans

```agda
module synthetic-homotopy-theory.cocones-under-spansᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.span-diagramsᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Aᵉ **coconeᵉ underᵉ aᵉ [span](foundation.spans.md)**ᵉ `Aᵉ <-f-ᵉ Sᵉ -g->ᵉ B`ᵉ with codomainᵉ
`X`ᵉ consistsᵉ ofᵉ twoᵉ mapsᵉ `iᵉ : Aᵉ → X`ᵉ andᵉ `jᵉ : Bᵉ → X`ᵉ equippedᵉ with aᵉ
[homotopy](foundation.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ squareᵉ

```text
        gᵉ
    Sᵉ ----->ᵉ Bᵉ
    |        |
  fᵉ |        | jᵉ
    ∨ᵉ        ∨ᵉ
    Aᵉ ----->ᵉ Xᵉ
        iᵉ
```

[commutes](foundation.commuting-squares-of-maps.md).ᵉ

## Definitions

### Cocones

```agda
coconeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) → UUᵉ l4ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
coconeᵉ {Aᵉ = Aᵉ} {Bᵉ = Bᵉ} fᵉ gᵉ Xᵉ =
  Σᵉ (Aᵉ → Xᵉ) (λ iᵉ → Σᵉ (Bᵉ → Xᵉ) (λ jᵉ → coherence-square-mapsᵉ gᵉ fᵉ jᵉ iᵉ))

cocone-span-diagramᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} →
  span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ → UUᵉ l4ᵉ →
  UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
cocone-span-diagramᵉ 𝒮ᵉ Xᵉ =
  coconeᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒮ᵉ) Xᵉ

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  where

  horizontal-map-coconeᵉ : Aᵉ → Xᵉ
  horizontal-map-coconeᵉ = pr1ᵉ cᵉ

  vertical-map-coconeᵉ : Bᵉ → Xᵉ
  vertical-map-coconeᵉ = pr1ᵉ (pr2ᵉ cᵉ)

  coherence-square-coconeᵉ :
    coherence-square-mapsᵉ gᵉ fᵉ vertical-map-coconeᵉ horizontal-map-coconeᵉ
  coherence-square-coconeᵉ = pr2ᵉ (pr2ᵉ cᵉ)
```

### Homotopies of cocones

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ}
  where

  statement-coherence-htpy-coconeᵉ :
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
    (Kᵉ : horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coconeᵉ fᵉ gᵉ c'ᵉ)
    (Lᵉ : vertical-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coconeᵉ fᵉ gᵉ c'ᵉ) →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  statement-coherence-htpy-coconeᵉ cᵉ c'ᵉ Kᵉ Lᵉ =
    (coherence-square-coconeᵉ fᵉ gᵉ cᵉ ∙hᵉ (Lᵉ ·rᵉ gᵉ)) ~ᵉ
    ((Kᵉ ·rᵉ fᵉ) ∙hᵉ coherence-square-coconeᵉ fᵉ gᵉ c'ᵉ)

  htpy-coconeᵉ : (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  htpy-coconeᵉ cᵉ c'ᵉ =
    Σᵉ ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coconeᵉ fᵉ gᵉ c'ᵉ)
      ( λ Kᵉ →
        Σᵉ ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coconeᵉ fᵉ gᵉ c'ᵉ)
          ( statement-coherence-htpy-coconeᵉ cᵉ c'ᵉ Kᵉ))

  module _
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) (Hᵉ : htpy-coconeᵉ cᵉ c'ᵉ)
    where

    horizontal-htpy-coconeᵉ :
      horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ horizontal-map-coconeᵉ fᵉ gᵉ c'ᵉ
    horizontal-htpy-coconeᵉ = pr1ᵉ Hᵉ

    vertical-htpy-coconeᵉ :
      vertical-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ vertical-map-coconeᵉ fᵉ gᵉ c'ᵉ
    vertical-htpy-coconeᵉ = pr1ᵉ (pr2ᵉ Hᵉ)

    coherence-htpy-coconeᵉ :
      statement-coherence-htpy-coconeᵉ cᵉ c'ᵉ
        ( horizontal-htpy-coconeᵉ)
        ( vertical-htpy-coconeᵉ)
    coherence-htpy-coconeᵉ = pr2ᵉ (pr2ᵉ Hᵉ)

  refl-htpy-coconeᵉ :
    (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) → htpy-coconeᵉ cᵉ cᵉ
  pr1ᵉ (refl-htpy-coconeᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ)) = refl-htpyᵉ
  pr1ᵉ (pr2ᵉ (refl-htpy-coconeᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ))) = refl-htpyᵉ
  pr2ᵉ (pr2ᵉ (refl-htpy-coconeᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ))) = right-unit-htpyᵉ

  htpy-eq-coconeᵉ :
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) → cᵉ ＝ᵉ c'ᵉ → htpy-coconeᵉ cᵉ c'ᵉ
  htpy-eq-coconeᵉ cᵉ .cᵉ reflᵉ = refl-htpy-coconeᵉ cᵉ

  module _
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
    (pᵉ : cᵉ ＝ᵉ c'ᵉ)
    where

    horizontal-htpy-eq-coconeᵉ :
      horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ
      horizontal-map-coconeᵉ fᵉ gᵉ c'ᵉ
    horizontal-htpy-eq-coconeᵉ =
      horizontal-htpy-coconeᵉ cᵉ c'ᵉ (htpy-eq-coconeᵉ cᵉ c'ᵉ pᵉ)

    vertical-htpy-eq-coconeᵉ :
      vertical-map-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ
      vertical-map-coconeᵉ fᵉ gᵉ c'ᵉ
    vertical-htpy-eq-coconeᵉ =
      vertical-htpy-coconeᵉ cᵉ c'ᵉ (htpy-eq-coconeᵉ cᵉ c'ᵉ pᵉ)

    coherence-square-htpy-eq-coconeᵉ :
      statement-coherence-htpy-coconeᵉ cᵉ c'ᵉ
        ( horizontal-htpy-eq-coconeᵉ)
        ( vertical-htpy-eq-coconeᵉ)
    coherence-square-htpy-eq-coconeᵉ =
      coherence-htpy-coconeᵉ cᵉ c'ᵉ (htpy-eq-coconeᵉ cᵉ c'ᵉ pᵉ)

  is-torsorial-htpy-coconeᵉ :
    (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) → is-torsorialᵉ (htpy-coconeᵉ cᵉ)
  is-torsorial-htpy-coconeᵉ cᵉ =
    is-torsorial-Eq-structureᵉ
      ( is-torsorial-htpyᵉ (horizontal-map-coconeᵉ fᵉ gᵉ cᵉ))
      ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ,ᵉ refl-htpyᵉ)
      ( is-torsorial-Eq-structureᵉ
        ( is-torsorial-htpyᵉ (vertical-map-coconeᵉ fᵉ gᵉ cᵉ))
        ( vertical-map-coconeᵉ fᵉ gᵉ cᵉ ,ᵉ refl-htpyᵉ)
        ( is-contr-is-equiv'ᵉ
          ( Σᵉ ( horizontal-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ fᵉ ~ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ ∘ᵉ gᵉ)
              ( λ H'ᵉ → coherence-square-coconeᵉ fᵉ gᵉ cᵉ ~ᵉ H'ᵉ))
          ( totᵉ (λ H'ᵉ Mᵉ → right-unit-htpyᵉ ∙hᵉ Mᵉ))
          ( is-equiv-tot-is-fiberwise-equivᵉ (λ H'ᵉ → is-equiv-concat-htpyᵉ _ _))
          ( is-torsorial-htpyᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ))))

  is-equiv-htpy-eq-coconeᵉ :
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) → is-equivᵉ (htpy-eq-coconeᵉ cᵉ c'ᵉ)
  is-equiv-htpy-eq-coconeᵉ cᵉ =
    fundamental-theorem-idᵉ
      ( is-torsorial-htpy-coconeᵉ cᵉ)
      ( htpy-eq-coconeᵉ cᵉ)

  extensionality-coconeᵉ :
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) → (cᵉ ＝ᵉ c'ᵉ) ≃ᵉ htpy-coconeᵉ cᵉ c'ᵉ
  pr1ᵉ (extensionality-coconeᵉ cᵉ c'ᵉ) = htpy-eq-coconeᵉ cᵉ c'ᵉ
  pr2ᵉ (extensionality-coconeᵉ cᵉ c'ᵉ) = is-equiv-htpy-eq-coconeᵉ cᵉ c'ᵉ

  eq-htpy-coconeᵉ :
    (cᵉ c'ᵉ : coconeᵉ fᵉ gᵉ Xᵉ) → htpy-coconeᵉ cᵉ c'ᵉ → cᵉ ＝ᵉ c'ᵉ
  eq-htpy-coconeᵉ cᵉ c'ᵉ = map-inv-is-equivᵉ (is-equiv-htpy-eq-coconeᵉ cᵉ c'ᵉ)
```

### Postcomposing cocones under spans with maps

```agda
cocone-mapᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} →
  coconeᵉ fᵉ gᵉ Xᵉ → (Xᵉ → Yᵉ) → coconeᵉ fᵉ gᵉ Yᵉ
pr1ᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ) = hᵉ ∘ᵉ horizontal-map-coconeᵉ fᵉ gᵉ cᵉ
pr1ᵉ (pr2ᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ)) = hᵉ ∘ᵉ vertical-map-coconeᵉ fᵉ gᵉ cᵉ
pr2ᵉ (pr2ᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ)) = hᵉ ·lᵉ coherence-square-coconeᵉ fᵉ gᵉ cᵉ

cocone-map-span-diagramᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ}
  {Xᵉ : UUᵉ l4ᵉ} (cᵉ : cocone-span-diagramᵉ 𝒮ᵉ Xᵉ) →
  {l5ᵉ : Level} {Yᵉ : UUᵉ l5ᵉ} →
  (Xᵉ → Yᵉ) → cocone-span-diagramᵉ 𝒮ᵉ Yᵉ
cocone-map-span-diagramᵉ {𝒮ᵉ = 𝒮ᵉ} cᵉ =
  cocone-mapᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒮ᵉ) cᵉ

cocone-map-idᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ) →
  Idᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ idᵉ) cᵉ
cocone-map-idᵉ fᵉ gᵉ cᵉ =
  eq-pair-eq-fiberᵉ
    ( eq-pair-eq-fiberᵉ (eq-htpyᵉ (ap-idᵉ ∘ᵉ coherence-square-coconeᵉ fᵉ gᵉ cᵉ)))

cocone-map-compᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) {Xᵉ : UUᵉ l4ᵉ} (cᵉ : coconeᵉ fᵉ gᵉ Xᵉ)
  {Yᵉ : UUᵉ l5ᵉ} (hᵉ : Xᵉ → Yᵉ) {Zᵉ : UUᵉ l6ᵉ} (kᵉ : Yᵉ → Zᵉ) →
  cocone-mapᵉ fᵉ gᵉ cᵉ (kᵉ ∘ᵉ hᵉ) ＝ᵉ cocone-mapᵉ fᵉ gᵉ (cocone-mapᵉ fᵉ gᵉ cᵉ hᵉ) kᵉ
cocone-map-compᵉ fᵉ gᵉ (iᵉ ,ᵉ jᵉ ,ᵉ Hᵉ) hᵉ kᵉ =
  eq-pair-eq-fiberᵉ (eq-pair-eq-fiberᵉ (eq-htpyᵉ (ap-compᵉ kᵉ hᵉ ∘ᵉ Hᵉ)))
```

### Horizontal composition of cocones

```text
        iᵉ       kᵉ
    Aᵉ ---->ᵉ Bᵉ ---->ᵉ Cᵉ
    |       |       |
  fᵉ |       |       |
    ∨ᵉ       ∨ᵉ       ∨ᵉ
    Xᵉ ---->ᵉ Yᵉ ---->ᵉ Zᵉ
```

```agda
cocone-comp-horizontalᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Aᵉ → Xᵉ) (iᵉ : Aᵉ → Bᵉ) (kᵉ : Bᵉ → Cᵉ) ( cᵉ : coconeᵉ fᵉ iᵉ Yᵉ) →
  coconeᵉ (vertical-map-coconeᵉ fᵉ iᵉ cᵉ) kᵉ Zᵉ → coconeᵉ fᵉ (kᵉ ∘ᵉ iᵉ) Zᵉ
pr1ᵉ (cocone-comp-horizontalᵉ fᵉ iᵉ kᵉ cᵉ dᵉ) =
  ( horizontal-map-coconeᵉ (vertical-map-coconeᵉ fᵉ iᵉ cᵉ) kᵉ dᵉ) ∘ᵉ
  ( horizontal-map-coconeᵉ fᵉ iᵉ cᵉ)
pr1ᵉ (pr2ᵉ (cocone-comp-horizontalᵉ fᵉ iᵉ kᵉ cᵉ dᵉ)) =
  vertical-map-coconeᵉ (vertical-map-coconeᵉ fᵉ iᵉ cᵉ) kᵉ dᵉ
pr2ᵉ (pr2ᵉ (cocone-comp-horizontalᵉ fᵉ iᵉ kᵉ cᵉ dᵉ)) =
  pasting-horizontal-coherence-square-mapsᵉ
    ( iᵉ)
    ( kᵉ)
    ( fᵉ)
    ( vertical-map-coconeᵉ fᵉ iᵉ cᵉ)
    ( vertical-map-coconeᵉ (vertical-map-coconeᵉ fᵉ iᵉ cᵉ) kᵉ dᵉ)
    ( horizontal-map-coconeᵉ fᵉ iᵉ cᵉ)
    ( horizontal-map-coconeᵉ (vertical-map-coconeᵉ fᵉ iᵉ cᵉ) kᵉ dᵉ)
    ( coherence-square-coconeᵉ fᵉ iᵉ cᵉ)
    ( coherence-square-coconeᵉ (vertical-map-coconeᵉ fᵉ iᵉ cᵉ) kᵉ dᵉ)
```

Aᵉ variationᵉ onᵉ theᵉ aboveᵉ:

```text
        iᵉ       kᵉ
    Aᵉ ---->ᵉ Bᵉ ---->ᵉ Cᵉ
    |       |       |
  fᵉ |     gᵉ |       |
    ∨ᵉ       ∨ᵉ       ∨ᵉ
    Xᵉ ---->ᵉ Yᵉ ---->ᵉ Zᵉ
        jᵉ
```

```agda
cocone-comp-horizontal'ᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Aᵉ → Xᵉ) (iᵉ : Aᵉ → Bᵉ) (kᵉ : Bᵉ → Cᵉ) (gᵉ : Bᵉ → Yᵉ) (jᵉ : Xᵉ → Yᵉ) →
  coconeᵉ gᵉ kᵉ Zᵉ → coherence-square-mapsᵉ iᵉ fᵉ gᵉ jᵉ →
  coconeᵉ fᵉ (kᵉ ∘ᵉ iᵉ) Zᵉ
cocone-comp-horizontal'ᵉ fᵉ iᵉ kᵉ gᵉ jᵉ cᵉ cohᵉ =
  cocone-comp-horizontalᵉ fᵉ iᵉ kᵉ (jᵉ ,ᵉ gᵉ ,ᵉ cohᵉ) cᵉ
```

### Vertical composition of cocones

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        |
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
    |        |
  kᵉ |        |
    ∨ᵉ        ∨ᵉ
    Cᵉ ----->ᵉ Zᵉ
```

```agda
cocone-comp-verticalᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Aᵉ → Bᵉ) (iᵉ : Aᵉ → Xᵉ) (kᵉ : Bᵉ → Cᵉ) ( cᵉ : coconeᵉ fᵉ iᵉ Yᵉ) →
  coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ iᵉ cᵉ) Zᵉ → coconeᵉ (kᵉ ∘ᵉ fᵉ) iᵉ Zᵉ
pr1ᵉ (cocone-comp-verticalᵉ fᵉ iᵉ kᵉ cᵉ dᵉ) =
  horizontal-map-coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ iᵉ cᵉ) dᵉ
pr1ᵉ (pr2ᵉ (cocone-comp-verticalᵉ fᵉ iᵉ kᵉ cᵉ dᵉ)) =
  vertical-map-coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ iᵉ cᵉ) dᵉ ∘ᵉ
  vertical-map-coconeᵉ fᵉ iᵉ cᵉ
pr2ᵉ (pr2ᵉ (cocone-comp-verticalᵉ fᵉ iᵉ kᵉ cᵉ dᵉ)) =
  pasting-vertical-coherence-square-mapsᵉ
    ( iᵉ)
    ( fᵉ)
    ( vertical-map-coconeᵉ fᵉ iᵉ cᵉ)
    ( horizontal-map-coconeᵉ fᵉ iᵉ cᵉ)
    ( kᵉ)
    ( vertical-map-coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ iᵉ cᵉ) dᵉ)
    ( horizontal-map-coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ iᵉ cᵉ) dᵉ)
    ( coherence-square-coconeᵉ fᵉ iᵉ cᵉ)
    ( coherence-square-coconeᵉ kᵉ (horizontal-map-coconeᵉ fᵉ iᵉ cᵉ) dᵉ)
```

Aᵉ variationᵉ onᵉ theᵉ aboveᵉ:

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ   jᵉ    ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
    |        |
  kᵉ |        |
    ∨ᵉ        ∨ᵉ
    Cᵉ ----->ᵉ Zᵉ
```

```agda
cocone-comp-vertical'ᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ} {Yᵉ : UUᵉ l5ᵉ} {Zᵉ : UUᵉ l6ᵉ}
  ( fᵉ : Aᵉ → Bᵉ) (iᵉ : Aᵉ → Xᵉ) (gᵉ : Xᵉ → Yᵉ) (jᵉ : Bᵉ → Yᵉ) (kᵉ : Bᵉ → Cᵉ) →
  coconeᵉ kᵉ jᵉ Zᵉ → coherence-square-mapsᵉ iᵉ fᵉ gᵉ jᵉ →
  coconeᵉ (kᵉ ∘ᵉ fᵉ) iᵉ Zᵉ
cocone-comp-vertical'ᵉ fᵉ iᵉ gᵉ jᵉ kᵉ cᵉ cohᵉ =
  cocone-comp-verticalᵉ fᵉ iᵉ kᵉ (jᵉ ,ᵉ gᵉ ,ᵉ cohᵉ) cᵉ
```

Givenᵉ aᵉ commutativeᵉ diagramᵉ likeᵉ this,ᵉ

```text
           g'ᵉ
       S'ᵉ --->ᵉ B'ᵉ
      /ᵉ \ᵉ       \ᵉ
  f'ᵉ /ᵉ   \ᵉ kᵉ     \ᵉ jᵉ
    /ᵉ     ∨ᵉ   gᵉ   ∨ᵉ
   A'ᵉ     Sᵉ ---->ᵉ Bᵉ
     \ᵉ    |       |
    iᵉ \ᵉ   | fᵉ     |
       \ᵉ  ∨ᵉ       ∨ᵉ
        >ᵉ Aᵉ ---->ᵉ Xᵉ
```

weᵉ canᵉ composeᵉ bothᵉ verticallyᵉ andᵉ horizontallyᵉ to getᵉ theᵉ followingᵉ coconeᵉ:

```text
  S'ᵉ --->ᵉ B'ᵉ
  |       |
  |       |
  ∨ᵉ       ∨ᵉ
  A'ᵉ --->ᵉ Xᵉ
```

Noticeᵉ thatᵉ theᵉ tripleᵉ `(i,j,k)`ᵉ isᵉ reallyᵉ aᵉ morphismᵉ ofᵉ spans.ᵉ Soᵉ theᵉ resultingᵉ
coconeᵉ arisesᵉ asᵉ aᵉ compositionᵉ ofᵉ theᵉ originalᵉ coconeᵉ with thisᵉ morphismᵉ ofᵉ
spans.ᵉ

```agda
comp-cocone-hom-spanᵉ :
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ l7ᵉ : Level}
  { Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {Xᵉ : UUᵉ l4ᵉ}
  { S'ᵉ : UUᵉ l5ᵉ} {A'ᵉ : UUᵉ l6ᵉ} {B'ᵉ : UUᵉ l7ᵉ}
  ( fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (f'ᵉ : S'ᵉ → A'ᵉ) (g'ᵉ : S'ᵉ → B'ᵉ)
  ( iᵉ : A'ᵉ → Aᵉ) (jᵉ : B'ᵉ → Bᵉ) (kᵉ : S'ᵉ → Sᵉ) →
  coconeᵉ fᵉ gᵉ Xᵉ →
  coherence-square-mapsᵉ kᵉ f'ᵉ fᵉ iᵉ → coherence-square-mapsᵉ g'ᵉ kᵉ jᵉ gᵉ →
  coconeᵉ f'ᵉ g'ᵉ Xᵉ
comp-cocone-hom-spanᵉ fᵉ gᵉ f'ᵉ g'ᵉ iᵉ jᵉ kᵉ cᵉ coh-lᵉ coh-rᵉ =
  cocone-comp-verticalᵉ
    ( idᵉ)
    ( g'ᵉ)
    ( f'ᵉ)
    ( (gᵉ ∘ᵉ kᵉ ,ᵉ jᵉ ,ᵉ coh-rᵉ))
    ( cocone-comp-horizontalᵉ f'ᵉ kᵉ gᵉ (iᵉ ,ᵉ fᵉ ,ᵉ coh-lᵉ) cᵉ)
```

### The diagonal cocone on a span of identical maps

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) (Xᵉ : UUᵉ l3ᵉ)
  where

  diagonal-into-coconeᵉ :
    (Bᵉ → Xᵉ) → coconeᵉ fᵉ fᵉ Xᵉ
  pr1ᵉ (diagonal-into-coconeᵉ gᵉ) = gᵉ
  pr1ᵉ (pr2ᵉ (diagonal-into-coconeᵉ gᵉ)) = gᵉ
  pr2ᵉ (pr2ᵉ (diagonal-into-coconeᵉ gᵉ)) = refl-htpyᵉ
```

### Cocones obtained from morphisms of arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ}
  (fᵉ : Aᵉ → Bᵉ) (gᵉ : Xᵉ → Yᵉ) (hᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  cocone-hom-arrowᵉ : coconeᵉ fᵉ (map-domain-hom-arrowᵉ fᵉ gᵉ hᵉ) Yᵉ
  pr1ᵉ cocone-hom-arrowᵉ = map-codomain-hom-arrowᵉ fᵉ gᵉ hᵉ
  pr1ᵉ (pr2ᵉ cocone-hom-arrowᵉ) = gᵉ
  pr2ᵉ (pr2ᵉ cocone-hom-arrowᵉ) = coh-hom-arrowᵉ fᵉ gᵉ hᵉ
```

### The swapping function on cocones over spans

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (Xᵉ : UUᵉ l4ᵉ)
  where

  swap-coconeᵉ : coconeᵉ fᵉ gᵉ Xᵉ → coconeᵉ gᵉ fᵉ Xᵉ
  pr1ᵉ (swap-coconeᵉ cᵉ) = vertical-map-coconeᵉ fᵉ gᵉ cᵉ
  pr1ᵉ (pr2ᵉ (swap-coconeᵉ cᵉ)) = horizontal-map-coconeᵉ fᵉ gᵉ cᵉ
  pr2ᵉ (pr2ᵉ (swap-coconeᵉ cᵉ)) = inv-htpyᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (Xᵉ : UUᵉ l4ᵉ)
  where

  is-involution-swap-coconeᵉ : swap-coconeᵉ gᵉ fᵉ Xᵉ ∘ᵉ swap-coconeᵉ fᵉ gᵉ Xᵉ ~ᵉ idᵉ
  is-involution-swap-coconeᵉ cᵉ =
    eq-htpy-coconeᵉ fᵉ gᵉ
      ( swap-coconeᵉ gᵉ fᵉ Xᵉ (swap-coconeᵉ fᵉ gᵉ Xᵉ cᵉ))
      ( cᵉ)
      ( ( refl-htpyᵉ) ,ᵉ
        ( refl-htpyᵉ) ,ᵉ
        ( λ sᵉ →
          concatᵉ
            ( right-unitᵉ)
            ( coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ)
            ( inv-invᵉ (coherence-square-coconeᵉ fᵉ gᵉ cᵉ sᵉ))))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Sᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ}
  (fᵉ : Sᵉ → Aᵉ) (gᵉ : Sᵉ → Bᵉ) (Xᵉ : UUᵉ l4ᵉ)
  where

  is-equiv-swap-coconeᵉ : is-equivᵉ (swap-coconeᵉ fᵉ gᵉ Xᵉ)
  is-equiv-swap-coconeᵉ =
    is-equiv-is-invertibleᵉ
      ( swap-coconeᵉ gᵉ fᵉ Xᵉ)
      ( is-involution-swap-coconeᵉ gᵉ fᵉ Xᵉ)
      ( is-involution-swap-coconeᵉ fᵉ gᵉ Xᵉ)

  equiv-swap-coconeᵉ : coconeᵉ fᵉ gᵉ Xᵉ ≃ᵉ coconeᵉ gᵉ fᵉ Xᵉ
  pr1ᵉ equiv-swap-coconeᵉ = swap-coconeᵉ fᵉ gᵉ Xᵉ
  pr2ᵉ equiv-swap-coconeᵉ = is-equiv-swap-coconeᵉ
```