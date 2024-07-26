# Commuting prisms of maps

```agda
module foundation.commuting-prisms-of-mapsᵉ where

open import foundation-core.commuting-prisms-of-mapsᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.commuting-triangles-of-mapsᵉ
open import foundation.composition-algebraᵉ
open import foundation.function-extensionalityᵉ
open import foundation.identity-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.precomposition-functionsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.commuting-squares-of-homotopiesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-function-typesᵉ
open import foundation-core.homotopiesᵉ
```

</details>

## Definitions

### Vertical pasting of vertical prisms of maps

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ l1''ᵉ l2''ᵉ l3''ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( f'ᵉ : A'ᵉ → C'ᵉ) (g'ᵉ : B'ᵉ → C'ᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hAᵉ : Aᵉ → A'ᵉ) (hBᵉ : Bᵉ → B'ᵉ) (hCᵉ : Cᵉ → C'ᵉ)
  { A''ᵉ : UUᵉ l1''ᵉ} {B''ᵉ : UUᵉ l2''ᵉ} {C''ᵉ : UUᵉ l3''ᵉ}
  ( f''ᵉ : A''ᵉ → C''ᵉ) (g''ᵉ : B''ᵉ → C''ᵉ) (h''ᵉ : A''ᵉ → B''ᵉ)
  ( hA'ᵉ : A'ᵉ → A''ᵉ) (hB'ᵉ : B'ᵉ → B''ᵉ) (hC'ᵉ : C'ᵉ → C''ᵉ)
  ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
  ( front-topᵉ : coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
  ( right-topᵉ : coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
  ( left-topᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
  ( midᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
  ( front-bottomᵉ : coherence-square-mapsᵉ f'ᵉ hA'ᵉ hC'ᵉ f''ᵉ)
  ( right-bottomᵉ : coherence-square-mapsᵉ g'ᵉ hB'ᵉ hC'ᵉ g''ᵉ)
  ( left-bottomᵉ : coherence-square-mapsᵉ h'ᵉ hA'ᵉ hB'ᵉ h''ᵉ)
  ( bottomᵉ : coherence-triangle-mapsᵉ f''ᵉ g''ᵉ h''ᵉ)
  where

  pasting-vertical-coherence-prism-mapsᵉ :
    vertical-coherence-prism-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( topᵉ)
      ( front-topᵉ)
      ( right-topᵉ)
      ( left-topᵉ)
      ( midᵉ) →
    vertical-coherence-prism-mapsᵉ f'ᵉ g'ᵉ h'ᵉ f''ᵉ g''ᵉ h''ᵉ hA'ᵉ hB'ᵉ hC'ᵉ
      ( midᵉ)
      ( front-bottomᵉ)
      ( right-bottomᵉ)
      ( left-bottomᵉ)
      ( bottomᵉ) →
    vertical-coherence-prism-mapsᵉ fᵉ gᵉ hᵉ f''ᵉ g''ᵉ h''ᵉ
      ( hA'ᵉ ∘ᵉ hAᵉ)
      ( hB'ᵉ ∘ᵉ hBᵉ)
      ( hC'ᵉ ∘ᵉ hCᵉ)
      ( topᵉ)
      ( pasting-vertical-coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ hA'ᵉ hC'ᵉ f''ᵉ
        ( front-topᵉ)
        ( front-bottomᵉ))
      ( pasting-vertical-coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ hB'ᵉ hC'ᵉ g''ᵉ
        ( right-topᵉ)
        ( right-bottomᵉ))
      ( pasting-vertical-coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ hA'ᵉ hB'ᵉ h''ᵉ
        ( left-topᵉ)
        ( left-bottomᵉ))
      ( bottomᵉ)
  pasting-vertical-coherence-prism-mapsᵉ prism-topᵉ prism-bottomᵉ =
    ( ap-concat-htpyᵉ
      ( bottomᵉ ·rᵉ hA'ᵉ ·rᵉ hAᵉ)
      ( commutative-pasting-vertical-pasting-horizontal-coherence-square-mapsᵉ
        hᵉ gᵉ hAᵉ hBᵉ hCᵉ h'ᵉ g'ᵉ hA'ᵉ hB'ᵉ hC'ᵉ h''ᵉ g''ᵉ
        ( left-topᵉ)
        ( right-topᵉ)
        ( left-bottomᵉ)
        ( right-bottomᵉ))) ∙hᵉ
    ( right-whisker-concat-coherence-square-homotopiesᵉ
      ( front-bottomᵉ ·rᵉ hAᵉ)
      ( bottomᵉ ·rᵉ hA'ᵉ ·rᵉ hAᵉ)
      ( hC'ᵉ ·lᵉ midᵉ ·rᵉ hAᵉ)
      ( ( pasting-horizontal-coherence-square-mapsᵉ
            h'ᵉ g'ᵉ hA'ᵉ hB'ᵉ hC'ᵉ h''ᵉ g''ᵉ left-bottomᵉ right-bottomᵉ) ·rᵉ
        ( hAᵉ))
      ( prism-bottomᵉ ·rᵉ hAᵉ)
      ( hC'ᵉ ·lᵉ ((g'ᵉ ·lᵉ left-topᵉ) ∙hᵉ (right-topᵉ ·rᵉ hᵉ)))
      ) ∙hᵉ
    ( ap-concat-htpyᵉ
      ( front-bottomᵉ ·rᵉ hAᵉ)
      ( ( map-coherence-square-homotopiesᵉ hC'ᵉ
          ( front-topᵉ)
          ( midᵉ ·rᵉ hAᵉ)
          (hCᵉ ·lᵉ topᵉ)
          ( pasting-horizontal-coherence-square-mapsᵉ hᵉ gᵉ hAᵉ hBᵉ hCᵉ h'ᵉ g'ᵉ
            ( left-topᵉ)
            ( right-topᵉ))
          ( prism-topᵉ)) ∙hᵉ
        ( ap-concat-htpyᵉ
          ( hC'ᵉ ·lᵉ front-topᵉ)
          ( preserves-comp-left-whisker-compᵉ hC'ᵉ hCᵉ topᵉ)))) ∙hᵉ
    ( inv-htpy-assoc-htpyᵉ
      ( front-bottomᵉ ·rᵉ hAᵉ)
      ( hC'ᵉ ·lᵉ front-topᵉ)
      ( ( hC'ᵉ ∘ᵉ hCᵉ) ·lᵉ topᵉ))
```

## Properties

### The two definitions of vertical prisms are equivalent

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( f'ᵉ : A'ᵉ → C'ᵉ) (g'ᵉ : B'ᵉ → C'ᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hAᵉ : Aᵉ → A'ᵉ) (hBᵉ : Bᵉ → B'ᵉ) (hCᵉ : Cᵉ → C'ᵉ)
  ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
  ( inv-frontᵉ : coherence-square-maps'ᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
  ( inv-rightᵉ : coherence-square-maps'ᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
  ( leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
  ( bottomᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
  where

  equiv-rotate-vertical-coherence-prism-mapsᵉ :
    vertical-coherence-prism-maps'ᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( topᵉ)
      ( inv-frontᵉ)
      ( inv-rightᵉ)
      ( leftᵉ)
      ( bottomᵉ) ≃ᵉ
    vertical-coherence-prism-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( topᵉ)
      ( inv-htpyᵉ inv-frontᵉ)
      ( inv-htpyᵉ inv-rightᵉ)
      ( leftᵉ)
      ( bottomᵉ)
  equiv-rotate-vertical-coherence-prism-mapsᵉ =
    equiv-Π-equiv-familyᵉ
      ( λ aᵉ →
        ( equiv-concat-assocᵉ
          ( bottomᵉ (hAᵉ aᵉ))
          ( apᵉ g'ᵉ (leftᵉ aᵉ))
          ( invᵉ (inv-rightᵉ (hᵉ aᵉ))) _) ∘eᵉ
        ( equiv-right-transpose-eq-concat'ᵉ _
          ( invᵉ (inv-frontᵉ aᵉ) ∙ᵉ apᵉ hCᵉ (topᵉ aᵉ))
          ( inv-rightᵉ (hᵉ aᵉ))) ∘eᵉ
        ( inv-equivᵉ
          ( equiv-concat-assoc'ᵉ _
            ( invᵉ (inv-frontᵉ aᵉ))
            ( apᵉ hCᵉ (topᵉ aᵉ))
            ( inv-rightᵉ (hᵉ aᵉ)))) ∘eᵉ
        ( equiv-left-transpose-eq-concatᵉ
          ( inv-frontᵉ aᵉ)
          ( bottomᵉ (hAᵉ aᵉ) ∙ᵉ apᵉ g'ᵉ (leftᵉ aᵉ))
          ( _)))

  rotate-vertical-coherence-prism-mapsᵉ :
    vertical-coherence-prism-maps'ᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( topᵉ)
      ( inv-frontᵉ)
      ( inv-rightᵉ)
      ( leftᵉ)
      ( bottomᵉ) →
    vertical-coherence-prism-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( topᵉ)
      ( inv-htpyᵉ inv-frontᵉ)
      ( inv-htpyᵉ inv-rightᵉ)
      ( leftᵉ)
      ( bottomᵉ)
  rotate-vertical-coherence-prism-mapsᵉ =
    map-equivᵉ equiv-rotate-vertical-coherence-prism-mapsᵉ
```

### Commuting prisms of maps induce commuting prisms of precomposition maps

Weᵉ proveᵉ thisᵉ forᵉ aᵉ fewᵉ differentᵉ formulationsᵉ ofᵉ commutingᵉ prismsᵉ ofᵉ maps.ᵉ

Theᵉ basicᵉ set-upᵉ isᵉ that,ᵉ givenᵉ aᵉ commutingᵉ prismᵉ ofᵉ mapsᵉ

```text
          Bᵉ
      hᵉ  ∧|ᵉ \ᵉ  gᵉ
       /ᵉ  |   \ᵉ
     /ᵉ  fᵉ | ⇑ᵉ   ∨ᵉ
    Aᵉ --------->ᵉ Cᵉ
    |     | hBᵉ   |
    | ⇗ᵉ   ∨ᵉ   ⇗ᵉ  |
 hAᵉ |     B'ᵉ     | hCᵉ
    | h'ᵉ ∧ᵉ  \ᵉ g'ᵉ |
    |  /ᵉ  ⇑ᵉ   \ᵉ  |
    ∨/ᵉ          ∨∨ᵉ
    A'ᵉ -------->ᵉ C'ᵉ
          f'ᵉ
```

weᵉ haveᵉ commutingᵉ prismsᵉ ofᵉ
[precompositionᵉ maps](foundation-core.precomposition-functions.mdᵉ)

```text
                    (B'ᵉ → Sᵉ)
         (-ᵉ ∘ᵉ g'ᵉ) ∧ᵉ     |     \ᵉ (-ᵉ ∘ᵉ h'ᵉ)
                /ᵉ       |       \ᵉ
              /ᵉ (-ᵉ ∘ᵉ f')|ᵉ ⇑ᵉ       ∨ᵉ
       (C'ᵉ → Sᵉ) --------------->ᵉ (A'ᵉ → Sᵉ)
           |            |            |
           |            | (-ᵉ ∘ᵉ hBᵉ)   |
           |     ⇙ᵉ      ∨ᵉ      ⇙ᵉ     |
  (-ᵉ ∘ᵉ hCᵉ) |         (Bᵉ → Sᵉ)         | (-ᵉ ∘ᵉ hAᵉ)
           |  (-ᵉ ∘ᵉ gᵉ) ∧ᵉ   \ᵉ (-ᵉ ∘ᵉ hᵉ)  |
           |       /ᵉ    ⇑ᵉ    \ᵉ       |
           ∨ᵉ    /ᵉ               ∨ᵉ    ∨ᵉ
        (Cᵉ → Sᵉ) ---------------->ᵉ (Aᵉ → S).ᵉ
                     (-ᵉ ∘ᵉ fᵉ)
```

Observeᵉ thatᵉ theᵉ bottomᵉ andᵉ topᵉ trianglesᵉ haveᵉ switchedᵉ positions,ᵉ theᵉ diagramᵉ
isᵉ mirroredᵉ alongᵉ theᵉ verticalᵉ axisᵉ comparedᵉ to theᵉ underlyingᵉ commutingᵉ prism,ᵉ
andᵉ thatᵉ theᵉ directionᵉ ofᵉ theᵉ homotopiesᵉ ofᵉ theᵉ verticalᵉ squaresᵉ areᵉ flipped.ᵉ

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ lᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( f'ᵉ : A'ᵉ → C'ᵉ) (g'ᵉ : B'ᵉ → C'ᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hAᵉ : Aᵉ → A'ᵉ) (hBᵉ : Bᵉ → B'ᵉ) (hCᵉ : Cᵉ → C'ᵉ)
  ( topᵉ : coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ)
  ( frontᵉ : coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
  ( rightᵉ : coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
  ( leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
  ( bottomᵉ : coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ)
  ( Hᵉ :
    vertical-coherence-prism-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( topᵉ)
      ( frontᵉ)
      ( rightᵉ)
      ( leftᵉ)
      ( bottomᵉ))
  ( Sᵉ : UUᵉ lᵉ)
  where

  precomp-vertical-coherence-prism-inv-squares-mapsᵉ :
    vertical-coherence-prism-inv-squares-mapsᵉ
      ( precompᵉ f'ᵉ Sᵉ)
      ( precompᵉ h'ᵉ Sᵉ)
      ( precompᵉ g'ᵉ Sᵉ)
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ hᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( precompᵉ hCᵉ Sᵉ)
      ( precompᵉ hBᵉ Sᵉ)
      ( precompᵉ hAᵉ Sᵉ)
      ( precomp-coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ bottomᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ frontᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ leftᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ rightᵉ Sᵉ)
      ( precomp-coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ topᵉ Sᵉ)
  precomp-vertical-coherence-prism-inv-squares-mapsᵉ =
    ( ap-concat-htpyᵉ
      ( htpy-precompᵉ frontᵉ Sᵉ)
      ( inv-distributive-htpy-precomp-left-whiskerᵉ hCᵉ topᵉ Sᵉ)) ∙hᵉ
    ( inv-htpyᵉ
      ( distributive-htpy-precomp-concat-htpyᵉ frontᵉ (hCᵉ ·lᵉ topᵉ) Sᵉ)) ∙hᵉ
    ( λ iᵉ → apᵉ eq-htpyᵉ (apᵉ (iᵉ ·lᵉ_) (eq-htpyᵉ (inv-htpyᵉ Hᵉ)))) ∙hᵉ
    ( distributive-htpy-precomp-concat-htpyᵉ
      ( bottomᵉ ·rᵉ hAᵉ)
      ( pasting-horizontal-coherence-square-mapsᵉ hᵉ gᵉ hAᵉ hBᵉ hCᵉ h'ᵉ g'ᵉ leftᵉ rightᵉ)
      ( Sᵉ)) ∙hᵉ
    ( ap-binary-concat-htpyᵉ
      ( distributive-htpy-precomp-right-whiskerᵉ hAᵉ bottomᵉ Sᵉ)
      ( ( distributive-htpy-precomp-concat-htpyᵉ (g'ᵉ ·lᵉ leftᵉ) (rightᵉ ·rᵉ hᵉ) Sᵉ) ∙hᵉ
        ( ap-binary-concat-htpyᵉ
          ( distributive-htpy-precomp-left-whiskerᵉ g'ᵉ leftᵉ Sᵉ)
          ( distributive-htpy-precomp-right-whiskerᵉ hᵉ rightᵉ Sᵉ))))

  precomp-vertical-coherence-prism-mapsᵉ :
    vertical-coherence-prism-mapsᵉ
      ( precompᵉ f'ᵉ Sᵉ)
      ( precompᵉ h'ᵉ Sᵉ)
      ( precompᵉ g'ᵉ Sᵉ)
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ hᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( precompᵉ hCᵉ Sᵉ)
      ( precompᵉ hBᵉ Sᵉ)
      ( precompᵉ hAᵉ Sᵉ)
      ( precomp-coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ bottomᵉ Sᵉ)
      ( inv-htpyᵉ (precomp-coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ frontᵉ Sᵉ))
      ( inv-htpyᵉ (precomp-coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ leftᵉ Sᵉ))
      ( inv-htpyᵉ (precomp-coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ rightᵉ Sᵉ))
      ( precomp-coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ topᵉ Sᵉ)
  precomp-vertical-coherence-prism-mapsᵉ =
    vertical-coherence-prism-maps-vertical-coherence-prism-inv-squares-mapsᵉ
      ( precompᵉ f'ᵉ Sᵉ)
      ( precompᵉ h'ᵉ Sᵉ)
      ( precompᵉ g'ᵉ Sᵉ)
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ hᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( precompᵉ hCᵉ Sᵉ)
      ( precompᵉ hBᵉ Sᵉ)
      ( precompᵉ hAᵉ Sᵉ)
      ( precomp-coherence-triangle-mapsᵉ f'ᵉ g'ᵉ h'ᵉ bottomᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ frontᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ leftᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ rightᵉ Sᵉ)
      ( precomp-coherence-triangle-mapsᵉ fᵉ gᵉ hᵉ topᵉ Sᵉ)
      ( precomp-vertical-coherence-prism-inv-squares-mapsᵉ)

module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ lᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( f'ᵉ : A'ᵉ → C'ᵉ) (g'ᵉ : B'ᵉ → C'ᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hAᵉ : Aᵉ → A'ᵉ) (hBᵉ : Bᵉ → B'ᵉ) (hCᵉ : Cᵉ → C'ᵉ)
  ( inv-topᵉ : coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ)
  ( frontᵉ : coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
  ( rightᵉ : coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
  ( leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
  ( inv-bottomᵉ : coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ)
  ( Hᵉ :
    vertical-coherence-prism-inv-triangles-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( inv-topᵉ)
      ( frontᵉ)
      ( rightᵉ)
      ( leftᵉ)
      ( inv-bottomᵉ))
  (Sᵉ : UUᵉ lᵉ)
  where

  precomp-vertical-inv-boundary-vertical-coherence-inv-triangles-prism-mapsᵉ :
    vertical-coherence-prism-inv-boundary-mapsᵉ
      ( precompᵉ f'ᵉ Sᵉ)
      ( precompᵉ h'ᵉ Sᵉ)
      ( precompᵉ g'ᵉ Sᵉ)
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ hᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( precompᵉ hCᵉ Sᵉ)
      ( precompᵉ hBᵉ Sᵉ)
      ( precompᵉ hAᵉ Sᵉ)
      ( precomp-coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ inv-bottomᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ frontᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ leftᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ rightᵉ Sᵉ)
      ( precomp-coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ inv-topᵉ Sᵉ)
  precomp-vertical-inv-boundary-vertical-coherence-inv-triangles-prism-mapsᵉ =
    ( inv-htpyᵉ
      ( ( compute-concat-htpy-precompᵉ
          ( (g'ᵉ ·lᵉ leftᵉ) ∙hᵉ (rightᵉ ·rᵉ hᵉ))
          ( hCᵉ ·lᵉ inv-topᵉ)
          ( Sᵉ)) ∙hᵉ
        ( ap-binary-concat-htpyᵉ
          ( ( compute-concat-htpy-precompᵉ (g'ᵉ ·lᵉ leftᵉ) (rightᵉ ·rᵉ hᵉ) Sᵉ) ∙hᵉ
            ( ap-binary-concat-htpyᵉ
              ( distributive-htpy-precomp-left-whiskerᵉ g'ᵉ leftᵉ Sᵉ)
              ( distributive-htpy-precomp-right-whiskerᵉ hᵉ rightᵉ Sᵉ)))
          ( distributive-htpy-precomp-left-whiskerᵉ hCᵉ inv-topᵉ Sᵉ)))) ∙hᵉ
    ( λ iᵉ → apᵉ (λ pᵉ → htpy-precompᵉ pᵉ Sᵉ iᵉ) (eq-htpyᵉ Hᵉ)) ∙hᵉ
    ( compute-concat-htpy-precompᵉ (inv-bottomᵉ ·rᵉ hAᵉ) frontᵉ Sᵉ) ∙hᵉ
    ( ap-concat-htpy'ᵉ
      ( htpy-precompᵉ frontᵉ Sᵉ)
      ( distributive-htpy-precomp-right-whiskerᵉ hAᵉ inv-bottomᵉ Sᵉ))

  precomp-vertical-coherence-prism-inv-triangles-mapsᵉ :
    vertical-coherence-prism-inv-triangles-mapsᵉ
      ( precompᵉ f'ᵉ Sᵉ)
      ( precompᵉ h'ᵉ Sᵉ)
      ( precompᵉ g'ᵉ Sᵉ)
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ hᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( precompᵉ hCᵉ Sᵉ)
      ( precompᵉ hBᵉ Sᵉ)
      ( precompᵉ hAᵉ Sᵉ)
      ( precomp-coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ inv-bottomᵉ Sᵉ)
      ( inv-htpyᵉ (precomp-coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ frontᵉ Sᵉ))
      ( inv-htpyᵉ (precomp-coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ leftᵉ Sᵉ))
      ( inv-htpyᵉ (precomp-coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ rightᵉ Sᵉ))
      ( precomp-coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ inv-topᵉ Sᵉ)
  precomp-vertical-coherence-prism-inv-triangles-mapsᵉ =
    vertical-coherence-prism-inv-triangles-maps-vertical-coherence-prism-inv-boundary-mapsᵉ
      ( precompᵉ f'ᵉ Sᵉ)
      ( precompᵉ h'ᵉ Sᵉ)
      ( precompᵉ g'ᵉ Sᵉ)
      ( precompᵉ fᵉ Sᵉ)
      ( precompᵉ hᵉ Sᵉ)
      ( precompᵉ gᵉ Sᵉ)
      ( precompᵉ hCᵉ Sᵉ)
      ( precompᵉ hBᵉ Sᵉ)
      ( precompᵉ hAᵉ Sᵉ)
      ( precomp-coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ inv-bottomᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ frontᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ leftᵉ Sᵉ)
      ( precomp-coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ rightᵉ Sᵉ)
      ( precomp-coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ inv-topᵉ Sᵉ)
      ( precomp-vertical-inv-boundary-vertical-coherence-inv-triangles-prism-mapsᵉ)
```

### Commuting prisms of maps induce commuting prisms of postcomposition maps

Givenᵉ aᵉ commutingᵉ prismᵉ ofᵉ mapsᵉ

```text
          Bᵉ
      hᵉ  ∧|ᵉ \ᵉ  gᵉ
       /ᵉ  |   \ᵉ
     /ᵉ  fᵉ | ⇑ᵉ   ∨ᵉ
    Aᵉ --------->ᵉ Cᵉ
    |     | hBᵉ   |
    | ⇗ᵉ   ∨ᵉ   ⇗ᵉ  |
 hAᵉ |     B'ᵉ     | hCᵉ
    | h'ᵉ ∧ᵉ  \ᵉ g'ᵉ |
    |  /ᵉ  ⇑ᵉ   \ᵉ  |
    ∨/ᵉ          ∨∨ᵉ
    A'ᵉ -------->ᵉ C'ᵉ
          f'ᵉ
```

weᵉ haveᵉ commutingᵉ prismsᵉ ofᵉ
[postcompositionᵉ maps](foundation-core.postcomposition-functions.md)sᵉ

```text
                     (Sᵉ → Bᵉ)
          (hᵉ ∘ᵉ -ᵉ) ∧ᵉ     |     \ᵉ (gᵉ ∘ᵉ -ᵉ)
                /ᵉ       |       \ᵉ
              /ᵉ  (fᵉ ∘ᵉ -)|ᵉ ⇑ᵉ       ∨ᵉ
        (Sᵉ → Aᵉ) ---------------->ᵉ (Sᵉ → Cᵉ)
           |            |            |
           |            | (hBᵉ ∘ᵉ -ᵉ)   |
           |     ⇗ᵉ      ∨ᵉ      ⇗ᵉ     |
  (hAᵉ ∘ᵉ -ᵉ) |         (Sᵉ → B'ᵉ)        | (hCᵉ ∘ᵉ -ᵉ)
           | (h'ᵉ ∘ᵉ -ᵉ) ∧ᵉ   \ᵉ (g'ᵉ ∘ᵉ -ᵉ) |
           |       /ᵉ    ⇑ᵉ    \ᵉ       |
           ∨ᵉ    /ᵉ               ∨ᵉ    ∨ᵉ
        (Sᵉ → A'ᵉ) --------------->ᵉ (Sᵉ → C').ᵉ
                     (f'ᵉ ∘ᵉ -ᵉ)
```

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l1'ᵉ l2'ᵉ l3'ᵉ lᵉ : Level}
  { Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {Cᵉ : UUᵉ l3ᵉ}
  ( fᵉ : Aᵉ → Cᵉ) (gᵉ : Bᵉ → Cᵉ) (hᵉ : Aᵉ → Bᵉ)
  { A'ᵉ : UUᵉ l1'ᵉ} {B'ᵉ : UUᵉ l2'ᵉ} {C'ᵉ : UUᵉ l3'ᵉ}
  ( f'ᵉ : A'ᵉ → C'ᵉ) (g'ᵉ : B'ᵉ → C'ᵉ) (h'ᵉ : A'ᵉ → B'ᵉ)
  ( hAᵉ : Aᵉ → A'ᵉ) (hBᵉ : Bᵉ → B'ᵉ) (hCᵉ : Cᵉ → C'ᵉ)
  ( inv-topᵉ : coherence-triangle-maps'ᵉ fᵉ gᵉ hᵉ)
  ( frontᵉ : coherence-square-mapsᵉ fᵉ hAᵉ hCᵉ f'ᵉ)
  ( rightᵉ : coherence-square-mapsᵉ gᵉ hBᵉ hCᵉ g'ᵉ)
  ( leftᵉ : coherence-square-mapsᵉ hᵉ hAᵉ hBᵉ h'ᵉ)
  ( inv-bottomᵉ : coherence-triangle-maps'ᵉ f'ᵉ g'ᵉ h'ᵉ)
  ( Hᵉ :
    vertical-coherence-prism-inv-triangles-mapsᵉ fᵉ gᵉ hᵉ f'ᵉ g'ᵉ h'ᵉ hAᵉ hBᵉ hCᵉ
      ( inv-topᵉ)
      ( frontᵉ)
      ( rightᵉ)
      ( leftᵉ)
      ( inv-bottomᵉ))
  (Sᵉ : UUᵉ lᵉ)
  where

  postcomp-vertical-coherence-prism-inv-triangles-mapsᵉ :
    vertical-coherence-prism-inv-triangles-mapsᵉ
      ( postcompᵉ Sᵉ fᵉ)
      ( postcompᵉ Sᵉ gᵉ)
      ( postcompᵉ Sᵉ hᵉ)
      ( postcompᵉ Sᵉ f'ᵉ)
      ( postcompᵉ Sᵉ g'ᵉ)
      ( postcompᵉ Sᵉ h'ᵉ)
      ( postcompᵉ Sᵉ hAᵉ)
      ( postcompᵉ Sᵉ hBᵉ)
      ( postcompᵉ Sᵉ hCᵉ)
      ( htpy-postcompᵉ Sᵉ inv-topᵉ)
      ( htpy-postcompᵉ Sᵉ frontᵉ)
      ( htpy-postcompᵉ Sᵉ rightᵉ)
      ( htpy-postcompᵉ Sᵉ leftᵉ)
      ( htpy-postcompᵉ Sᵉ inv-bottomᵉ)
  postcomp-vertical-coherence-prism-inv-triangles-mapsᵉ =
    ( inv-htpyᵉ
      ( ( distributive-htpy-postcomp-concat-htpyᵉ
          ( g'ᵉ ·lᵉ leftᵉ ∙hᵉ rightᵉ ·rᵉ hᵉ)
          ( hCᵉ ·lᵉ inv-topᵉ)
          ( Sᵉ)) ∙hᵉ
        ( ap-binary-concat-htpyᵉ
          ( ( distributive-htpy-postcomp-concat-htpyᵉ
              ( g'ᵉ ·lᵉ leftᵉ)
              ( rightᵉ ·rᵉ hᵉ) Sᵉ) ∙hᵉ
            ( ap-binary-concat-htpyᵉ
              ( distributive-htpy-postcomp-left-whiskerᵉ g'ᵉ leftᵉ Sᵉ)
              ( distributive-htpy-postcomp-right-whiskerᵉ hᵉ rightᵉ Sᵉ)))
          ( distributive-htpy-postcomp-left-whiskerᵉ hCᵉ inv-topᵉ Sᵉ)))) ∙hᵉ
    ( λ iᵉ → apᵉ (λ pᵉ → htpy-postcompᵉ Sᵉ pᵉ iᵉ) (eq-htpyᵉ Hᵉ)) ∙hᵉ
    ( distributive-htpy-postcomp-concat-htpyᵉ (inv-bottomᵉ ·rᵉ hAᵉ) frontᵉ Sᵉ)
```