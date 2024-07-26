# Commuting triangles of morphisms of arrows

```agda
module foundation.commuting-triangles-of-morphisms-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopies-morphisms-arrowsᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Considerᵉ aᵉ triangleᵉ ofᵉ [morphismsᵉ ofᵉ arrows](foundation.morphisms-arrows.mdᵉ)

```text
        topᵉ
     fᵉ ---->ᵉ gᵉ
      \ᵉ     /ᵉ
  leftᵉ \ᵉ   /ᵉ rightᵉ
        ∨ᵉ ∨ᵉ
         hᵉ
```

thenᵉ weᵉ canᵉ askᵉ thatᵉ theᵉ triangleᵉ
{{#conceptᵉ "commutes"ᵉ Disambiguation="triangleᵉ ofᵉ morphismsᵉ ofᵉ arrows"ᵉ}}

byᵉ askingᵉ forᵉ aᵉ [homotopy](foundation.homotopies-morphisms-arrows.mdᵉ) ofᵉ
morphismsᵉ ofᵉ arrowsᵉ

```text
  leftᵉ ~ᵉ rightᵉ ∘ᵉ top.ᵉ
```

Thisᵉ isᵉ [equivalent](foundation-core.equivalences.mdᵉ) to askingᵉ forᵉ aᵉ
[commutingᵉ prismᵉ ofᵉ maps](foundation-core.commuting-prisms-of-maps.md),ᵉ givenᵉ
theᵉ squareᵉ facesᵉ in theᵉ diagramᵉ

```text
        fᵉ
  ∙ᵉ --------->ᵉ ∙ᵉ
  |\ᵉ           |\ᵉ
  | \ᵉ          | \ᵉ
  |  \ᵉ         |  \ᵉ
  |   ∨ᵉ        |   ∨ᵉ
  |    ∙ᵉ ---ᵉ gᵉ --->ᵉ ∙ᵉ
  |   /ᵉ        |   /ᵉ
  |  /ᵉ         |  /ᵉ
  | /ᵉ          | /ᵉ
  ∨∨ᵉ           ∨∨ᵉ
  ∙ᵉ --------->ᵉ ∙.ᵉ
        hᵉ
```

## Definition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {Aᵉ : UUᵉ l1ᵉ} {A'ᵉ : UUᵉ l2ᵉ} {Bᵉ : UUᵉ l3ᵉ} {B'ᵉ : UUᵉ l4ᵉ} {Cᵉ : UUᵉ l5ᵉ} {C'ᵉ : UUᵉ l6ᵉ}
  (fᵉ : Aᵉ → A'ᵉ) (gᵉ : Bᵉ → B'ᵉ) (hᵉ : Cᵉ → C'ᵉ)
  (leftᵉ : hom-arrowᵉ fᵉ hᵉ) (rightᵉ : hom-arrowᵉ gᵉ hᵉ) (topᵉ : hom-arrowᵉ fᵉ gᵉ)
  where

  coherence-triangle-hom-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  coherence-triangle-hom-arrowᵉ =
    htpy-hom-arrowᵉ fᵉ hᵉ leftᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ rightᵉ topᵉ)

  coherence-triangle-hom-arrow'ᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  coherence-triangle-hom-arrow'ᵉ =
    htpy-hom-arrowᵉ fᵉ hᵉ (comp-hom-arrowᵉ fᵉ gᵉ hᵉ rightᵉ topᵉ) leftᵉ
```