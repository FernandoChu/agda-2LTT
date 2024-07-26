# The universal property of lists with respect to wild monoids

```agda
module lists.universal-property-lists-wild-monoidsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-higher-homotopies-compositionᵉ

open import group-theory.homomorphisms-semigroupsᵉ

open import lists.concatenation-listsᵉ
open import lists.listsᵉ

open import structured-types.h-spacesᵉ
open import structured-types.morphisms-h-spacesᵉ
open import structured-types.morphisms-wild-monoidsᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
open import structured-types.wild-monoidsᵉ
```

</details>

## Idea

Theᵉ typeᵉ ofᵉ listsᵉ ofᵉ elementsᵉ ofᵉ `X`ᵉ isᵉ theᵉ initialᵉ wildᵉ monoidᵉ equippedᵉ with aᵉ
mapᵉ fromᵉ `X`ᵉ intoᵉ it.ᵉ

## Definition

### The pointed type of lists of elements of `X`

```agda
list-pointed-typeᵉ : {lᵉ : Level} → UUᵉ lᵉ → Pointed-Typeᵉ lᵉ
pr1ᵉ (list-pointed-typeᵉ Xᵉ) = listᵉ Xᵉ
pr2ᵉ (list-pointed-typeᵉ Xᵉ) = nilᵉ
```

### The H-space of lists of elements of `X`

```agda
list-H-Spaceᵉ :
  {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → H-Spaceᵉ lᵉ
pr1ᵉ (list-H-Spaceᵉ Xᵉ) = list-pointed-typeᵉ Xᵉ
pr1ᵉ (pr2ᵉ (list-H-Spaceᵉ Xᵉ)) = concat-listᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (list-H-Spaceᵉ Xᵉ))) = left-unit-law-concat-listᵉ
pr1ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (list-H-Spaceᵉ Xᵉ)))) = right-unit-law-concat-listᵉ
pr2ᵉ (pr2ᵉ (pr2ᵉ (pr2ᵉ (list-H-Spaceᵉ Xᵉ)))) = reflᵉ
```

### The wild monoid of lists of elements of `X`

```agda
unit-law-011-associative-concat-listᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (yᵉ zᵉ : listᵉ Xᵉ) →
  Idᵉ
    ( ( associative-concat-listᵉ nilᵉ yᵉ zᵉ) ∙ᵉ
      ( left-unit-law-concat-listᵉ (concat-listᵉ yᵉ zᵉ)))
    ( apᵉ (λ tᵉ → concat-listᵉ tᵉ zᵉ) (left-unit-law-concat-listᵉ yᵉ))
unit-law-011-associative-concat-listᵉ yᵉ zᵉ = reflᵉ

concat-list'ᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → listᵉ Aᵉ → listᵉ Aᵉ → listᵉ Aᵉ
concat-list'ᵉ xᵉ yᵉ = concat-listᵉ yᵉ xᵉ

unit-law-101-associative-concat-listᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ zᵉ : listᵉ Xᵉ) →
  Idᵉ
    ( ( associative-concat-listᵉ xᵉ nilᵉ zᵉ) ∙ᵉ
      ( apᵉ (concat-listᵉ xᵉ) (left-unit-law-concat-listᵉ zᵉ)))
    ( apᵉ (λ tᵉ → concat-listᵉ tᵉ zᵉ) (right-unit-law-concat-listᵉ xᵉ))
unit-law-101-associative-concat-listᵉ nilᵉ zᵉ = reflᵉ
unit-law-101-associative-concat-listᵉ (consᵉ xᵉ lᵉ) zᵉ =
  ( ( ( invᵉ
        ( ap-concatᵉ
          ( consᵉ xᵉ)
          ( associative-concat-listᵉ lᵉ nilᵉ zᵉ)
          ( apᵉ (concat-listᵉ lᵉ) (left-unit-law-concat-listᵉ zᵉ)))) ∙ᵉ
      ( left-whisker-comp²ᵉ
        ( consᵉ xᵉ)
        ( unit-law-101-associative-concat-listᵉ lᵉ)
        ( zᵉ))) ∙ᵉ
    ( invᵉ
      ( ap-compᵉ (consᵉ xᵉ) (concat-list'ᵉ zᵉ) (right-unit-law-concat-listᵉ lᵉ)))) ∙ᵉ
  ( ap-compᵉ (concat-list'ᵉ zᵉ) (consᵉ xᵉ) (right-unit-law-concat-listᵉ lᵉ))

unit-law-110-associative-concat-listᵉ :
  {l1ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (xᵉ yᵉ : listᵉ Xᵉ) →
  Idᵉ
    ( ( associative-concat-listᵉ xᵉ yᵉ nilᵉ) ∙ᵉ
      ( apᵉ (concat-listᵉ xᵉ) (right-unit-law-concat-listᵉ yᵉ)))
    ( right-unit-law-concat-listᵉ (concat-listᵉ xᵉ yᵉ))
unit-law-110-associative-concat-listᵉ nilᵉ yᵉ =
  ap-idᵉ (right-unit-law-concat-listᵉ yᵉ)
unit-law-110-associative-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ =
  ( apᵉ
    ( concatᵉ
      ( associative-concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ nilᵉ)
      ( concat-listᵉ (consᵉ aᵉ xᵉ) yᵉ))
    ( ap-compᵉ (consᵉ aᵉ) (concat-listᵉ xᵉ) (right-unit-law-concat-listᵉ yᵉ))) ∙ᵉ
  ( ( invᵉ
      ( ap-concatᵉ
        ( consᵉ aᵉ)
        ( associative-concat-listᵉ xᵉ yᵉ nilᵉ)
        ( apᵉ (concat-listᵉ xᵉ) (right-unit-law-concat-listᵉ yᵉ)))) ∙ᵉ
    ( left-whisker-comp²ᵉ
      ( consᵉ aᵉ)
      ( unit-law-110-associative-concat-listᵉ xᵉ)
      ( yᵉ)))

list-Wild-Monoidᵉ : {lᵉ : Level} → UUᵉ lᵉ → Wild-Monoidᵉ lᵉ
list-Wild-Monoidᵉ Xᵉ =
  pairᵉ
    ( list-H-Spaceᵉ Xᵉ)
    ( pairᵉ
      ( associative-concat-listᵉ)
      ( pairᵉ
        ( unit-law-011-associative-concat-listᵉ)
        ( pairᵉ
          ( unit-law-101-associative-concat-listᵉ)
          ( pairᵉ unit-law-110-associative-concat-listᵉ starᵉ))))
```

## Properties

### For any wild monoid `M` with a map `X → M` there is a morphism of wild monoids `list X → M`

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Mᵉ : Wild-Monoidᵉ l2ᵉ) (fᵉ : Xᵉ → type-Wild-Monoidᵉ Mᵉ)
  where

  map-elim-list-Wild-Monoidᵉ :
    listᵉ Xᵉ → type-Wild-Monoidᵉ Mᵉ
  map-elim-list-Wild-Monoidᵉ nilᵉ = unit-Wild-Monoidᵉ Mᵉ
  map-elim-list-Wild-Monoidᵉ (consᵉ uᵉ xᵉ) =
    mul-Wild-Monoidᵉ Mᵉ (fᵉ uᵉ) (map-elim-list-Wild-Monoidᵉ xᵉ)

  preserves-unit-map-elim-list-Wild-Monoidᵉ :
    Idᵉ (map-elim-list-Wild-Monoidᵉ nilᵉ) (unit-Wild-Monoidᵉ Mᵉ)
  preserves-unit-map-elim-list-Wild-Monoidᵉ = reflᵉ

  pointed-map-elim-list-Wild-Monoidᵉ :
    list-pointed-typeᵉ Xᵉ →∗ᵉ pointed-type-Wild-Monoidᵉ Mᵉ
  pr1ᵉ pointed-map-elim-list-Wild-Monoidᵉ =
    map-elim-list-Wild-Monoidᵉ
  pr2ᵉ pointed-map-elim-list-Wild-Monoidᵉ =
    preserves-unit-map-elim-list-Wild-Monoidᵉ

  preserves-mul-map-elim-list-Wild-Monoidᵉ :
    preserves-mul'ᵉ
      ( concat-listᵉ)
      ( mul-Wild-Monoidᵉ Mᵉ)
      ( map-elim-list-Wild-Monoidᵉ)
  preserves-mul-map-elim-list-Wild-Monoidᵉ nilᵉ yᵉ =
    invᵉ (left-unit-law-mul-Wild-Monoidᵉ Mᵉ (map-elim-list-Wild-Monoidᵉ yᵉ))
  preserves-mul-map-elim-list-Wild-Monoidᵉ (consᵉ uᵉ xᵉ) yᵉ =
    ( apᵉ (mul-Wild-Monoidᵉ Mᵉ (fᵉ uᵉ))
      ( preserves-mul-map-elim-list-Wild-Monoidᵉ xᵉ yᵉ)) ∙ᵉ
    ( invᵉ
      ( associative-mul-Wild-Monoidᵉ Mᵉ
        ( fᵉ uᵉ)
        ( map-elim-list-Wild-Monoidᵉ xᵉ)
        ( map-elim-list-Wild-Monoidᵉ yᵉ)))

  preserves-left-unit-law-map-elim-list-Wild-Monoidᵉ :
    preserves-left-unit-law-mul-pointed-map-H-Spaceᵉ
      ( list-H-Spaceᵉ Xᵉ)
      ( h-space-Wild-Monoidᵉ Mᵉ)
      ( pointed-map-elim-list-Wild-Monoidᵉ)
      ( λ {xᵉ} {yᵉ} → preserves-mul-map-elim-list-Wild-Monoidᵉ xᵉ yᵉ)
  preserves-left-unit-law-map-elim-list-Wild-Monoidᵉ xᵉ =
    invᵉ
      ( left-invᵉ
        ( left-unit-law-mul-Wild-Monoidᵉ Mᵉ (map-elim-list-Wild-Monoidᵉ xᵉ)))

  preserves-right-unit-law-map-elim-list-Wild-Monoidᵉ :
    preserves-right-unit-law-mul-pointed-map-H-Spaceᵉ
      ( list-H-Spaceᵉ Xᵉ)
      ( h-space-Wild-Monoidᵉ Mᵉ)
      ( pointed-map-elim-list-Wild-Monoidᵉ)
      ( λ {xᵉ} {yᵉ} → preserves-mul-map-elim-list-Wild-Monoidᵉ xᵉ yᵉ)
  preserves-right-unit-law-map-elim-list-Wild-Monoidᵉ nilᵉ =
    ( invᵉ (left-invᵉ (left-unit-law-mul-Wild-Monoidᵉ Mᵉ (unit-Wild-Monoidᵉ Mᵉ)))) ∙ᵉ
    ( apᵉ
      ( concatᵉ
        ( invᵉ (left-unit-law-mul-Wild-Monoidᵉ Mᵉ (unit-Wild-Monoidᵉ Mᵉ)))
        ( unit-Wild-Monoidᵉ Mᵉ))
      ( coh-unit-laws-mul-Wild-Monoidᵉ Mᵉ))
  preserves-right-unit-law-map-elim-list-Wild-Monoidᵉ (consᵉ aᵉ xᵉ) =
    ( invᵉ
      ( ap-compᵉ
        ( map-elim-list-Wild-Monoidᵉ)
        ( consᵉ aᵉ)
        ( right-unit-law-concat-listᵉ xᵉ))) ∙ᵉ
    ( ( ap-compᵉ
        ( mul-Wild-Monoidᵉ Mᵉ (fᵉ aᵉ))
        ( map-elim-list-Wild-Monoidᵉ)
        ( right-unit-law-concat-listᵉ xᵉ)) ∙ᵉ
      ( ( apᵉ
          ( apᵉ (mul-Wild-Monoidᵉ Mᵉ (fᵉ aᵉ)))
          ( preserves-right-unit-law-map-elim-list-Wild-Monoidᵉ xᵉ)) ∙ᵉ
        ( ( ap-concatᵉ
            ( mul-Wild-Monoidᵉ Mᵉ (fᵉ aᵉ))
            ( preserves-mul-map-elim-list-Wild-Monoidᵉ xᵉ nilᵉ)
            ( right-unit-law-mul-Wild-Monoidᵉ Mᵉ
              ( map-elim-list-Wild-Monoidᵉ xᵉ))) ∙ᵉ
          ( ( apᵉ
              ( concatᵉ
                ( apᵉ
                  ( mul-Wild-Monoidᵉ Mᵉ (fᵉ aᵉ))
                  ( preserves-mul-map-elim-list-Wild-Monoidᵉ xᵉ nilᵉ))
                ( map-elim-list-Wild-Monoidᵉ (consᵉ aᵉ xᵉ)))
              ( ( apᵉ
                  ( concat'ᵉ
                    ( mul-Wild-Monoidᵉ Mᵉ
                      ( fᵉ aᵉ)
                      ( mul-Wild-Monoidᵉ Mᵉ
                        ( map-elim-list-Wild-Monoidᵉ xᵉ)
                        ( unit-Wild-Monoidᵉ Mᵉ)))
                    ( apᵉ
                      ( mul-Wild-Monoidᵉ Mᵉ (fᵉ aᵉ))
                      ( right-unit-law-mul-Wild-Monoidᵉ Mᵉ
                        ( map-elim-list-Wild-Monoidᵉ xᵉ))))
                  ( invᵉ
                    ( left-invᵉ
                      ( associative-mul-Wild-Monoidᵉ Mᵉ
                        ( fᵉ aᵉ)
                        ( map-elim-list-Wild-Monoidᵉ xᵉ)
                        ( unit-Wild-Monoidᵉ Mᵉ))))) ∙ᵉ
                ( ( assocᵉ
                    ( invᵉ
                      ( associative-mul-Wild-Monoidᵉ Mᵉ
                        ( fᵉ aᵉ)
                        ( map-elim-list-Wild-Monoidᵉ xᵉ)
                        ( unit-Wild-Monoidᵉ Mᵉ)))
                    ( associative-mul-Wild-Monoidᵉ Mᵉ
                      ( fᵉ aᵉ)
                      ( map-elim-list-Wild-Monoidᵉ xᵉ)
                      ( unit-Wild-Monoidᵉ Mᵉ))
                    ( apᵉ
                      ( mul-Wild-Monoidᵉ Mᵉ (fᵉ aᵉ))
                      ( right-unit-law-mul-Wild-Monoidᵉ Mᵉ
                        ( map-elim-list-Wild-Monoidᵉ xᵉ)))) ∙ᵉ
                  ( apᵉ
                    ( concatᵉ
                      ( invᵉ
                        ( associative-mul-Wild-Monoidᵉ Mᵉ
                          ( fᵉ aᵉ)
                          ( map-elim-list-Wild-Monoidᵉ xᵉ)
                          ( unit-Wild-Monoidᵉ Mᵉ)))
                      ( map-elim-list-Wild-Monoidᵉ (consᵉ aᵉ xᵉ)))
                    ( unit-law-110-associative-Wild-Monoidᵉ Mᵉ
                      ( fᵉ aᵉ)
                      ( map-elim-list-Wild-Monoidᵉ xᵉ)))))) ∙ᵉ
            ( invᵉ
              ( assocᵉ
                ( apᵉ
                  ( mul-Wild-Monoidᵉ Mᵉ (fᵉ aᵉ))
                  ( preserves-mul-map-elim-list-Wild-Monoidᵉ xᵉ nilᵉ))
                ( invᵉ
                  ( associative-mul-Wild-Monoidᵉ Mᵉ
                    ( fᵉ aᵉ)
                    ( map-elim-list-Wild-Monoidᵉ xᵉ)
                    ( unit-Wild-Monoidᵉ Mᵉ)))
                ( right-unit-law-mul-Wild-Monoidᵉ Mᵉ
                  ( map-elim-list-Wild-Monoidᵉ (consᵉ aᵉ xᵉ)))))))))

preserves-coh-unit-laws-map-elim-list-Wild-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Mᵉ : Wild-Monoidᵉ l2ᵉ)
  (fᵉ : Xᵉ → type-Wild-Monoidᵉ Mᵉ) →
  preserves-coherence-unit-laws-mul-pointed-map-H-Spaceᵉ
    ( list-H-Spaceᵉ Xᵉ)
    ( h-space-Wild-Monoidᵉ Mᵉ)
    ( pointed-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ)
    ( λ {xᵉ} {yᵉ} → preserves-mul-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ xᵉ yᵉ)
    ( preserves-left-unit-law-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ)
    ( preserves-right-unit-law-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ)
preserves-coh-unit-laws-map-elim-list-Wild-Monoidᵉ
  (pairᵉ (pairᵉ (pairᵉ Mᵉ eMᵉ) (pairᵉ μᵉ (pairᵉ lMᵉ (pairᵉ rMᵉ cMᵉ)))) αMᵉ) fᵉ = reflᵉ

elim-list-Wild-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Mᵉ : Wild-Monoidᵉ l2ᵉ)
  (fᵉ : Xᵉ → type-Wild-Monoidᵉ Mᵉ) →
  hom-Wild-Monoidᵉ (list-Wild-Monoidᵉ Xᵉ) Mᵉ
elim-list-Wild-Monoidᵉ Mᵉ fᵉ =
  pairᵉ
    ( pairᵉ (map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ) reflᵉ)
    ( pairᵉ
      ( λ {xᵉ} {yᵉ} → preserves-mul-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ xᵉ yᵉ)
      ( pairᵉ (preserves-left-unit-law-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ)
        ( pairᵉ
          ( preserves-right-unit-law-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ)
          ( preserves-coh-unit-laws-map-elim-list-Wild-Monoidᵉ Mᵉ fᵉ))))
```

### Contractibility of the type `hom (list X) M` of morphisms of wild monoids

Thisᵉ remainsᵉ to beᵉ formalized.ᵉ Theᵉ followingᵉ blockᵉ containsᵉ someᵉ abandonedᵉ oldᵉ
codeᵉ towardsᵉ thisᵉ goalᵉ:

```text
htpy-elim-list-Wild-Monoidᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Mᵉ : Wild-Monoidᵉ l2ᵉ)
  (gᵉ hᵉ : hom-Wild-Monoidᵉ (list-Wild-Monoidᵉ Xᵉ) Mᵉ)
  ( Hᵉ : ( map-hom-Wild-Monoidᵉ (list-Wild-Monoidᵉ Xᵉ) Mᵉ gᵉ ∘ᵉ unit-listᵉ) ~ᵉ
        ( map-hom-Wild-Monoidᵉ (list-Wild-Monoidᵉ Xᵉ) Mᵉ hᵉ ∘ᵉ unit-listᵉ)) →
  htpy-hom-Wild-Monoidᵉ (list-Wild-Monoidᵉ Xᵉ) Mᵉ gᵉ hᵉ
htpy-elim-list-Wild-Monoidᵉ {Xᵉ = Xᵉ} Mᵉ gᵉ hᵉ Hᵉ =
  pairᵉ (pairᵉ αᵉ βᵉ) γᵉ
  where
  αᵉ : pr1ᵉ (pr1ᵉ gᵉ) ~ᵉ pr1ᵉ (pr1ᵉ hᵉ)
  αᵉ nilᵉ =
    ( preserves-unit-map-hom-Wild-Monoidᵉ (list-Wild-Monoidᵉ Xᵉ) Mᵉ gᵉ) ∙ᵉ
    ( invᵉ (preserves-unit-map-hom-Wild-Monoidᵉ (list-Wild-Monoidᵉ Xᵉ) Mᵉ hᵉ))
  αᵉ (consᵉ xᵉ lᵉ) =
    ( preserves-mul-map-hom-Wild-Monoidᵉ
      ( list-Wild-Monoidᵉ Xᵉ)
      ( Mᵉ)
      ( gᵉ)
      ( unit-listᵉ xᵉ)
      ( lᵉ)) ∙ᵉ
    ( ( ap-mul-Wild-Monoidᵉ Mᵉ (Hᵉ xᵉ) (αᵉ lᵉ)) ∙ᵉ
      ( invᵉ
        ( preserves-mul-map-hom-Wild-Monoidᵉ
          ( list-Wild-Monoidᵉ Xᵉ)
          ( Mᵉ)
          ( hᵉ)
          ( unit-listᵉ xᵉ)
          ( lᵉ))))
  βᵉ : (xᵉ yᵉ : pr1ᵉ (pr1ᵉ (list-Wild-Monoidᵉ Xᵉ))) →
      Idᵉ ( pr2ᵉ (pr1ᵉ gᵉ) xᵉ yᵉ ∙ᵉ ap-mul-Wild-Monoidᵉ Mᵉ (αᵉ xᵉ) (αᵉ yᵉ))
         ( αᵉ (concat-listᵉ xᵉ yᵉ) ∙ᵉ pr2ᵉ (pr1ᵉ hᵉ) xᵉ yᵉ)
  βᵉ nilᵉ yᵉ = {!!ᵉ}
  βᵉ (consᵉ xᵉ x₁ᵉ) yᵉ = {!!ᵉ}
  γᵉ : Idᵉ (pr2ᵉ gᵉ) (αᵉ nilᵉ ∙ᵉ pr2ᵉ hᵉ)
  γᵉ =
    ( invᵉ right-unitᵉ) ∙ᵉ
    ( ( left-whisker-concatᵉ (pr2ᵉ gᵉ) (invᵉ (left-invᵉ (pr2ᵉ hᵉ)))) ∙ᵉ
      ( invᵉ (assocᵉ (pr2ᵉ gᵉ) (invᵉ (pr2ᵉ hᵉ)) (pr2ᵉ hᵉ))))
```