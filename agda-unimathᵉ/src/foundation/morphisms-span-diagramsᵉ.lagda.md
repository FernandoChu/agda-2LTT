# Morphisms of span diagrams

```agda
module foundation.morphisms-span-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.morphisms-spansᵉ
open import foundation.operations-spansᵉ
open import foundation.span-diagramsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
```

</details>

## Idea

Aᵉ {{#conceptᵉ "morphismᵉ ofᵉ spanᵉ diagrams"ᵉ Agda=hom-span-diagramᵉ}} fromᵉ aᵉ
[spanᵉ diagram](foundation.span-diagrams.mdᵉ) `Aᵉ <-f-ᵉ Sᵉ -g->ᵉ B`ᵉ to aᵉ spanᵉ diagramᵉ
`Cᵉ <-h-ᵉ Tᵉ -k->ᵉ D`ᵉ consistsᵉ ofᵉ mapsᵉ `uᵉ : Aᵉ → C`,ᵉ `vᵉ : Bᵉ → D`,ᵉ andᵉ `wᵉ : Sᵉ → T`ᵉ
[equipped](foundation.structure.mdᵉ) with twoᵉ
[homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ diagramᵉ

```text
         fᵉ       gᵉ
    Aᵉ <-----ᵉ Sᵉ ----->ᵉ Bᵉ
    |        |        |
  uᵉ |        | wᵉ      | vᵉ
    ∨ᵉ        ∨ᵉ        ∨ᵉ
    Cᵉ <-----ᵉ Tᵉ ----->ᵉ Dᵉ
         hᵉ       kᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md).ᵉ

Theᵉ definitionᵉ ofᵉ morphismsᵉ ofᵉ spanᵉ diagramsᵉ isᵉ givenᵉ conciselyᵉ in termsᵉ ofᵉ theᵉ
notionᵉ ofᵉ morphismsᵉ ofᵉ spans.ᵉ Inᵉ theᵉ resultingᵉ definitions,ᵉ theᵉ commutingᵉ
squaresᵉ ofᵉ morphismsᵉ ofᵉ spansᵉ areᵉ orientedᵉ in theᵉ followingᵉ wayᵉ:

-ᵉ Aᵉ homotopyᵉ
  `map-domain-hom-spanᵉ ∘ᵉ left-map-spanᵉ sᵉ ~ᵉ left-map-spanᵉ tᵉ ∘ᵉ spanning-map-hom-span`ᵉ
  witnessingᵉ thatᵉ theᵉ squareᵉ

  ```text
                       spanning-map-hom-spanᵉ
                    Sᵉ ---------------------->ᵉ Tᵉ
                    |                         |
    left-map-spanᵉ sᵉ |                         | left-map-spanᵉ tᵉ
                    ∨ᵉ                         ∨ᵉ
                    Aᵉ ---------------------->ᵉ Cᵉ
                        map-domain-hom-spanᵉ
  ```

  commutes.ᵉ

-ᵉ Aᵉ homotopyᵉ
  `map-domain-hom-spanᵉ ∘ᵉ right-map-spanᵉ sᵉ ~ᵉ right-map-spanᵉ tᵉ ∘ᵉ spanning-map-hom-span`ᵉ
  witnessingᵉ thatᵉ theᵉ squareᵉ

  ```text
                        spanning-map-hom-spanᵉ
                     Sᵉ ---------------------->ᵉ Tᵉ
                     |                         |
    right-map-spanᵉ sᵉ |                         | right-map-spanᵉ tᵉ
                     ∨ᵉ                         ∨ᵉ
                     Bᵉ ---------------------->ᵉ Dᵉ
                        map-codomain-hom-spanᵉ
  ```

  commutes.ᵉ

## Definitions

### Morphisms of span diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ)
  where

  hom-span-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ ⊔ l5ᵉ ⊔ l6ᵉ)
  hom-span-diagramᵉ =
    Σᵉ ( domain-span-diagramᵉ 𝒮ᵉ → domain-span-diagramᵉ 𝒯ᵉ)
      ( λ fᵉ →
        Σᵉ ( codomain-span-diagramᵉ 𝒮ᵉ → codomain-span-diagramᵉ 𝒯ᵉ)
          ( λ gᵉ →
            hom-spanᵉ
              ( concat-spanᵉ
                ( span-span-diagramᵉ 𝒮ᵉ)
                ( fᵉ)
                ( gᵉ))
              ( span-span-diagramᵉ 𝒯ᵉ)))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  (𝒮ᵉ : span-diagramᵉ l1ᵉ l2ᵉ l3ᵉ) (𝒯ᵉ : span-diagramᵉ l4ᵉ l5ᵉ l6ᵉ)
  (fᵉ : hom-span-diagramᵉ 𝒮ᵉ 𝒯ᵉ)
  where

  map-domain-hom-span-diagramᵉ :
    domain-span-diagramᵉ 𝒮ᵉ → domain-span-diagramᵉ 𝒯ᵉ
  map-domain-hom-span-diagramᵉ = pr1ᵉ fᵉ

  map-codomain-hom-span-diagramᵉ :
    codomain-span-diagramᵉ 𝒮ᵉ → codomain-span-diagramᵉ 𝒯ᵉ
  map-codomain-hom-span-diagramᵉ = pr1ᵉ (pr2ᵉ fᵉ)

  hom-span-hom-span-diagramᵉ :
    hom-spanᵉ
      ( concat-spanᵉ
        ( span-span-diagramᵉ 𝒮ᵉ)
        ( map-domain-hom-span-diagramᵉ)
        ( map-codomain-hom-span-diagramᵉ))
      ( span-span-diagramᵉ 𝒯ᵉ)
  hom-span-hom-span-diagramᵉ = pr2ᵉ (pr2ᵉ fᵉ)

  spanning-map-hom-span-diagramᵉ :
    spanning-type-span-diagramᵉ 𝒮ᵉ → spanning-type-span-diagramᵉ 𝒯ᵉ
  spanning-map-hom-span-diagramᵉ =
    map-hom-spanᵉ
      ( concat-spanᵉ
        ( span-span-diagramᵉ 𝒮ᵉ)
        ( map-domain-hom-span-diagramᵉ)
        ( map-codomain-hom-span-diagramᵉ))
      ( span-span-diagramᵉ 𝒯ᵉ)
      ( hom-span-hom-span-diagramᵉ)

  left-square-hom-span-diagramᵉ :
    coherence-square-mapsᵉ
      ( spanning-map-hom-span-diagramᵉ)
      ( left-map-span-diagramᵉ 𝒮ᵉ)
      ( left-map-span-diagramᵉ 𝒯ᵉ)
      ( map-domain-hom-span-diagramᵉ)
  left-square-hom-span-diagramᵉ =
    left-triangle-hom-spanᵉ
      ( concat-spanᵉ
        ( span-span-diagramᵉ 𝒮ᵉ)
        ( map-domain-hom-span-diagramᵉ)
        ( map-codomain-hom-span-diagramᵉ))
      ( span-span-diagramᵉ 𝒯ᵉ)
      ( hom-span-hom-span-diagramᵉ)

  left-hom-arrow-hom-span-diagramᵉ :
    hom-arrowᵉ (left-map-span-diagramᵉ 𝒮ᵉ) (left-map-span-diagramᵉ 𝒯ᵉ)
  pr1ᵉ left-hom-arrow-hom-span-diagramᵉ =
    spanning-map-hom-span-diagramᵉ
  pr1ᵉ (pr2ᵉ left-hom-arrow-hom-span-diagramᵉ) =
    map-domain-hom-span-diagramᵉ
  pr2ᵉ (pr2ᵉ left-hom-arrow-hom-span-diagramᵉ) =
    left-square-hom-span-diagramᵉ

  right-square-hom-span-diagramᵉ :
    coherence-square-mapsᵉ
      ( spanning-map-hom-span-diagramᵉ)
      ( right-map-span-diagramᵉ 𝒮ᵉ)
      ( right-map-span-diagramᵉ 𝒯ᵉ)
      ( map-codomain-hom-span-diagramᵉ)
  right-square-hom-span-diagramᵉ =
    right-triangle-hom-spanᵉ
      ( concat-spanᵉ
        ( span-span-diagramᵉ 𝒮ᵉ)
        ( map-domain-hom-span-diagramᵉ)
        ( map-codomain-hom-span-diagramᵉ))
      ( span-span-diagramᵉ 𝒯ᵉ)
      ( hom-span-hom-span-diagramᵉ)

  right-hom-arrow-hom-span-diagramᵉ :
    hom-arrowᵉ (right-map-span-diagramᵉ 𝒮ᵉ) (right-map-span-diagramᵉ 𝒯ᵉ)
  pr1ᵉ right-hom-arrow-hom-span-diagramᵉ =
    spanning-map-hom-span-diagramᵉ
  pr1ᵉ (pr2ᵉ right-hom-arrow-hom-span-diagramᵉ) =
    map-codomain-hom-span-diagramᵉ
  pr2ᵉ (pr2ᵉ right-hom-arrow-hom-span-diagramᵉ) =
    right-square-hom-span-diagramᵉ
```