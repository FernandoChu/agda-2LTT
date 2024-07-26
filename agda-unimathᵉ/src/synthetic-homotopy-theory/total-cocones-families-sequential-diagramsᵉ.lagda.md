# Total cocones of type families over cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.total-cocones-families-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equality-dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-identifications-concatenationᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.families-descent-data-sequential-colimitsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
open import synthetic-homotopy-theory.total-sequential-diagramsᵉ
```

</details>

## Idea

Givenᵉ aᵉ sequentialᵉ diagramᵉ `(A,ᵉ a)`ᵉ andᵉ aᵉ coconeᵉ `c`ᵉ underᵉ itᵉ with vertexᵉ `X`,ᵉ aᵉ
typeᵉ familyᵉ `Pᵉ : Xᵉ → 𝒰`ᵉ inducesᵉ aᵉ dependentᵉ sequentialᵉ diagramᵉ overᵉ `A`,ᵉ asᵉ
shownᵉ in
[`cocones-under-sequential-diagrams`](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md).ᵉ

Hereᵉ weᵉ showᵉ thatᵉ whenᵉ `P`ᵉ isᵉ additionallyᵉ equippedᵉ with correspondingᵉ
[descentᵉ data](synthetic-homotopy-theory.families-descent-data-sequential-colimits.mdᵉ)
`B`,ᵉ itᵉ inducesᵉ aᵉ coconeᵉ onᵉ theᵉ totalᵉ sequentialᵉ diagramᵉ

```text
  Σᵉ A₀ᵉ B₀ᵉ ---->ᵉ Σᵉ A₁ᵉ B₁ᵉ ---->ᵉ ⋯ᵉ ---->ᵉ Σᵉ Xᵉ Pᵉ .ᵉ
```

Specializingᵉ theᵉ aboveᵉ to theᵉ caseᵉ whenᵉ theᵉ descentᵉ data isᵉ theᵉ oneᵉ inducedᵉ byᵉ
theᵉ family,ᵉ weᵉ getᵉ aᵉ coconeᵉ ofᵉ theᵉ formᵉ

```text
                tot₍₊₁₎ᵉ (trᵉ Pᵉ Hₙᵉ)
  Σᵉ Aₙᵉ (Pᵉ ∘ᵉ iₙᵉ) ---------------->ᵉ Σᵉ Aₙ₊₁ᵉ (Pᵉ ∘ᵉ iₙ₊₁ᵉ)
                \ᵉ               /ᵉ
                  \ᵉ           /ᵉ
  map-Σ-map-baseᵉ iₙᵉ \ᵉ       /ᵉ map-Σ-map-baseᵉ iₙ₊₁ᵉ
                      \ᵉ   /ᵉ
                       ∨ᵉ ∨ᵉ
                      Σᵉ Xᵉ Pᵉ .ᵉ
```

Furthermore,ᵉ theᵉ twoᵉ totalᵉ diagramsᵉ areᵉ
[equivalent](synthetic-homotopy-theory.equivalences-sequential-diagrams.md),ᵉ andᵉ
theᵉ twoᵉ inducedᵉ coconesᵉ areᵉ alsoᵉ
[equivalent](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.mdᵉ)
underᵉ thisᵉ equivalence.ᵉ

## Definitions

### Cocones under total sequential diagrams induced by type families with descent data

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-sequential-colimitᵉ cᵉ l3ᵉ)
  where

  total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ :
    sequential-diagramᵉ (l1ᵉ ⊔ l3ᵉ)
  total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ =
    total-sequential-diagramᵉ
      ( dependent-sequential-diagram-family-with-descent-data-sequential-colimitᵉ
        ( Pᵉ))

  total-cocone-family-with-descent-data-sequential-colimitᵉ :
    cocone-sequential-diagramᵉ
      ( total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ)
      ( Σᵉ Xᵉ (family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ))
  pr1ᵉ total-cocone-family-with-descent-data-sequential-colimitᵉ nᵉ =
    map-Σᵉ
      ( family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ Pᵉ nᵉ)
  pr2ᵉ total-cocone-family-with-descent-data-sequential-colimitᵉ nᵉ =
    coherence-triangle-maps-Σᵉ
      ( family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ)
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ Pᵉ nᵉ)
      ( map-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ Pᵉ
        ( succ-ℕᵉ nᵉ))
      ( map-family-family-with-descent-data-sequential-colimitᵉ Pᵉ nᵉ)
      ( λ aᵉ →
        inv-htpyᵉ
          ( coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimitᵉ
            ( Pᵉ)
            ( nᵉ)
            ( aᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  (Pᵉ : Xᵉ → UUᵉ l3ᵉ)
  where

  total-sequential-diagram-family-cocone-sequential-diagramᵉ :
    sequential-diagramᵉ (l1ᵉ ⊔ l3ᵉ)
  total-sequential-diagram-family-cocone-sequential-diagramᵉ =
    total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ
      ( family-with-descent-data-family-cocone-sequential-diagramᵉ cᵉ Pᵉ)

  total-cocone-family-cocone-sequential-diagramᵉ :
    cocone-sequential-diagramᵉ
      ( total-sequential-diagram-family-cocone-sequential-diagramᵉ)
      ( Σᵉ Xᵉ Pᵉ)
  total-cocone-family-cocone-sequential-diagramᵉ =
    total-cocone-family-with-descent-data-sequential-colimitᵉ
      ( family-with-descent-data-family-cocone-sequential-diagramᵉ cᵉ Pᵉ)
```

### Type families with descent data for sequential colimits induce an equivalence between the cocone induced by descent data and the cocone induced by the family

Inᵉ otherᵉ words,ᵉ thereᵉ isᵉ anᵉ
[equivalenceᵉ ofᵉ cocones](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.mdᵉ)
underᵉ theᵉ inducedᵉ equivalenceᵉ ofᵉ sequentialᵉ diagramsᵉ

```text
     Σᵉ A₀ᵉ B₀ᵉ --------->ᵉ Σᵉ A₁ᵉ B₁ᵉ ------>ᵉ ⋯ᵉ ----->ᵉ Σᵉ Xᵉ Pᵉ
        |                  |                       |
        | ≃ᵉ                | ≃ᵉ                     | ≃ᵉ
        ∨ᵉ                  ∨ᵉ                       ∨ᵉ
  Σᵉ A₀ᵉ (Pᵉ ∘ᵉ i₀ᵉ) --->ᵉ Σᵉ A₁ᵉ (Pᵉ ∘ᵉ i₁ᵉ) --->ᵉ ⋯ᵉ ----->ᵉ Σᵉ Xᵉ Pᵉ .ᵉ
```

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : sequential-diagramᵉ l1ᵉ}
  {Xᵉ : UUᵉ l2ᵉ} {cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ}
  (Pᵉ : family-with-descent-data-sequential-colimitᵉ cᵉ l3ᵉ)
  where

  equiv-total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ :
    equiv-sequential-diagramᵉ
      ( total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ Pᵉ)
      ( total-sequential-diagram-family-cocone-sequential-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ))
  equiv-total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ =
    equiv-total-sequential-diagram-equiv-dependent-sequential-diagramᵉ _
      ( dependent-sequential-diagram-family-coconeᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ))
      ( equiv-descent-data-family-with-descent-data-sequential-colimitᵉ Pᵉ)

  equiv-total-cocone-family-with-descent-data-sequential-colimitᵉ :
    equiv-cocone-equiv-sequential-diagramᵉ
      ( total-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ)
      ( total-cocone-family-cocone-sequential-diagramᵉ cᵉ
        ( family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ))
      ( equiv-total-sequential-diagram-family-with-descent-data-sequential-colimitᵉ)
  pr1ᵉ equiv-total-cocone-family-with-descent-data-sequential-colimitᵉ =
    id-equivᵉ
  pr1ᵉ (pr2ᵉ equiv-total-cocone-family-with-descent-data-sequential-colimitᵉ) nᵉ =
    refl-htpyᵉ
  pr2ᵉ (pr2ᵉ equiv-total-cocone-family-with-descent-data-sequential-colimitᵉ)
    nᵉ (aᵉ ,ᵉ bᵉ) =
    ( left-whisker-concatᵉ
      ( eq-pair-Σᵉ (coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ) reflᵉ)
      ( ( right-unitᵉ) ∙ᵉ
        ( compute-ap-map-Σ-map-base-eq-pair-Σᵉ _ _ _ _))) ∙ᵉ
    ( invᵉ
      ( ( ap-idᵉ _) ∙ᵉ
        ( triangle-eq-pair-Σᵉ
          ( family-cocone-family-with-descent-data-sequential-colimitᵉ Pᵉ)
          ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ aᵉ)
          ( _))))
```