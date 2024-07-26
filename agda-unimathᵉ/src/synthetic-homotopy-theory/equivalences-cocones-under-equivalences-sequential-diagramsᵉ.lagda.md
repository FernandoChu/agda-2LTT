# Equivalences of cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagramsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.commuting-prisms-of-mapsᵉ
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import synthetic-homotopy-theory.cocones-under-sequential-diagramsᵉ
open import synthetic-homotopy-theory.equivalences-sequential-diagramsᵉ
open import synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagramsᵉ
open import synthetic-homotopy-theory.sequential-diagramsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ
[sequentialᵉ diagrams](synthetic-homotopy-theory.sequential-diagrams.mdᵉ) `(A,ᵉ a)`ᵉ
andᵉ `(B,ᵉ b)`,ᵉ equippedᵉ with
[cocones](synthetic-homotopy-theory.cocones-under-sequential-diagrams.mdᵉ)
`cᵉ : Aᵉ → X`ᵉ andᵉ `c'ᵉ : Bᵉ → Y`,ᵉ respectively,ᵉ andᵉ anᵉ
[equivalenceᵉ ofᵉ sequentialᵉ diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.mdᵉ)
`eᵉ : Aᵉ ≃ᵉ B`.ᵉ Thenᵉ anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ cocones"ᵉ Disambiguation="underᵉ anᵉ equivalenceᵉ ofᵉ sequentialᵉ diagrams"ᵉ Agda=equiv-cocone-equiv-sequential-diagramᵉ}}
underᵉ `e`ᵉ isᵉ aᵉ tripleᵉ `(u,ᵉ H,ᵉ K)`,ᵉ with `uᵉ : Xᵉ ≃ᵉ Y`ᵉ aᵉ mapᵉ ofᵉ verticesᵉ ofᵉ theᵉ
coforks,ᵉ `H`ᵉ aᵉ familyᵉ ofᵉ [homotopies](foundation-core.homotopies.mdᵉ) witnessingᵉ
thatᵉ theᵉ squareᵉ

```text
           iₙᵉ
     Aₙᵉ ------->ᵉ Xᵉ
     |           |
  hₙᵉ | ≃ᵉ       ≃ᵉ | uᵉ
     |           |
     ∨ᵉ           ∨ᵉ
     Bₙᵉ ------->ᵉ Yᵉ
           i'ₙᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.mdᵉ) forᵉ everyᵉ `n`,ᵉ andᵉ `K`ᵉ
aᵉ familyᵉ ofᵉ coherenceᵉ data fillingᵉ theᵉ insidesᵉ ofᵉ theᵉ resultingᵉ
[prism](foundation.commuting-prisms-of-maps.mdᵉ) boundariesᵉ

```text
            Aₙ₊₁ᵉ
       aₙᵉ  ∧ᵉ |  \ᵉ  iₙ₊₁ᵉ
         /ᵉ   |    \ᵉ
       /ᵉ     |      ∨ᵉ
     Aₙᵉ ----------->ᵉ Xᵉ
     |   iₙᵉ  |       |
     |       | hₙ₊₁ᵉ  |
  hₙᵉ |       ∨ᵉ       | uᵉ
     |      Bₙ₊₁ᵉ     |
     |  bₙᵉ ∧ᵉ   \i'ₙ₊₁|ᵉ
     |   /ᵉ       \ᵉ   |
     ∨ᵉ /ᵉ           ∨ᵉ ∨ᵉ
     Bₙᵉ ----------->ᵉ Yᵉ
            i'ₙᵉ
```

forᵉ everyᵉ `n`.ᵉ

## Definition

### Equivalences of cocones under equivalences of sequential diagrams

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  (eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  coherence-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ :
    (Xᵉ ≃ᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ uᵉ =
    (nᵉ : ℕᵉ) →
    coherence-square-mapsᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
      ( map-equivᵉ uᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)

  coherence-equiv-cocone-equiv-sequential-diagramᵉ :
    (uᵉ : Xᵉ ≃ᵉ Yᵉ) →
    coherence-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ uᵉ →
    UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-equiv-cocone-equiv-sequential-diagramᵉ uᵉ Hᵉ =
    (nᵉ : ℕᵉ) →
    vertical-coherence-prism-mapsᵉ
      ( map-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ cᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Aᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ nᵉ)
      ( map-cocone-sequential-diagramᵉ c'ᵉ (succ-ℕᵉ nᵉ))
      ( map-sequential-diagramᵉ Bᵉ nᵉ)
      ( map-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
      ( map-equiv-sequential-diagramᵉ Bᵉ eᵉ (succ-ℕᵉ nᵉ))
      ( map-equivᵉ uᵉ)
      ( coherence-cocone-sequential-diagramᵉ cᵉ nᵉ)
      ( Hᵉ nᵉ)
      ( Hᵉ (succ-ℕᵉ nᵉ))
      ( naturality-equiv-sequential-diagramᵉ Bᵉ eᵉ nᵉ)
      ( coherence-cocone-sequential-diagramᵉ c'ᵉ nᵉ)

  equiv-cocone-equiv-sequential-diagramᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l4ᵉ)
  equiv-cocone-equiv-sequential-diagramᵉ =
    Σᵉ ( Xᵉ ≃ᵉ Yᵉ)
      ( λ uᵉ →
        Σᵉ ( coherence-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ uᵉ)
          ( coherence-equiv-cocone-equiv-sequential-diagramᵉ uᵉ))

  module _
    (e'ᵉ : equiv-cocone-equiv-sequential-diagramᵉ)
    where

    equiv-equiv-cocone-equiv-sequential-diagramᵉ : Xᵉ ≃ᵉ Yᵉ
    equiv-equiv-cocone-equiv-sequential-diagramᵉ = pr1ᵉ e'ᵉ

    map-equiv-cocone-equiv-sequential-diagramᵉ : Xᵉ → Yᵉ
    map-equiv-cocone-equiv-sequential-diagramᵉ =
      map-equivᵉ equiv-equiv-cocone-equiv-sequential-diagramᵉ

    is-equiv-map-equiv-cocone-equiv-sequential-diagramᵉ :
      is-equivᵉ map-equiv-cocone-equiv-sequential-diagramᵉ
    is-equiv-map-equiv-cocone-equiv-sequential-diagramᵉ =
      is-equiv-map-equivᵉ equiv-equiv-cocone-equiv-sequential-diagramᵉ

    coh-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ :
      coherence-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ
        ( equiv-equiv-cocone-equiv-sequential-diagramᵉ)
    coh-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ = pr1ᵉ (pr2ᵉ e'ᵉ)

    coh-equiv-cocone-equiv-sequential-diagramᵉ :
      coherence-equiv-cocone-equiv-sequential-diagramᵉ
        ( equiv-equiv-cocone-equiv-sequential-diagramᵉ)
        ( coh-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ)
    coh-equiv-cocone-equiv-sequential-diagramᵉ = pr2ᵉ (pr2ᵉ e'ᵉ)

    hom-equiv-cocone-equiv-sequential-diagramᵉ :
      hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ
        ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)
    pr1ᵉ hom-equiv-cocone-equiv-sequential-diagramᵉ =
      map-equiv-cocone-equiv-sequential-diagramᵉ
    pr1ᵉ (pr2ᵉ hom-equiv-cocone-equiv-sequential-diagramᵉ) =
      coh-map-cocone-equiv-cocone-equiv-sequential-diagramᵉ
    pr2ᵉ (pr2ᵉ hom-equiv-cocone-equiv-sequential-diagramᵉ) =
      coh-equiv-cocone-equiv-sequential-diagramᵉ
```

### The predicate on morphisms of cocones under equivalences of sequential diagrams of being an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  (eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  is-equiv-hom-cocone-equiv-sequential-diagramᵉ :
    hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ (hom-equiv-sequential-diagramᵉ Bᵉ eᵉ) →
    UUᵉ (l2ᵉ ⊔ l4ᵉ)
  is-equiv-hom-cocone-equiv-sequential-diagramᵉ hᵉ =
    is-equivᵉ (map-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ)

  is-equiv-hom-equiv-cocone-equiv-sequential-diagramᵉ :
    (e'ᵉ : equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ) →
    is-equiv-hom-cocone-equiv-sequential-diagramᵉ
      ( hom-equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
  is-equiv-hom-equiv-cocone-equiv-sequential-diagramᵉ e'ᵉ =
    is-equiv-map-equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ e'ᵉ
```

## Properties

### Morphisms of cocones under equivalences of arrows which are equivalences are equivalences of cocones

Toᵉ constructᵉ anᵉ equivalenceᵉ ofᵉ coconesᵉ underᵉ anᵉ equivalenceᵉ `e`ᵉ ofᵉ sequentialᵉ
diagrams,ᵉ itᵉ sufficesᵉ to constructᵉ aᵉ morphismᵉ ofᵉ coconesᵉ underᵉ theᵉ underlyingᵉ
morphismᵉ ofᵉ sequentialᵉ diagramsᵉ ofᵉ `e`,ᵉ andᵉ showᵉ thatᵉ theᵉ mapᵉ `Xᵉ → Y`ᵉ isᵉ anᵉ
equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Aᵉ : sequential-diagramᵉ l1ᵉ} {Xᵉ : UUᵉ l2ᵉ} (cᵉ : cocone-sequential-diagramᵉ Aᵉ Xᵉ)
  {Bᵉ : sequential-diagramᵉ l3ᵉ} {Yᵉ : UUᵉ l4ᵉ} (c'ᵉ : cocone-sequential-diagramᵉ Bᵉ Yᵉ)
  (eᵉ : equiv-sequential-diagramᵉ Aᵉ Bᵉ)
  where

  equiv-hom-cocone-equiv-sequential-diagramᵉ :
    (hᵉ :
      hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ
        ( hom-equiv-sequential-diagramᵉ Bᵉ eᵉ)) →
    is-equiv-hom-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ hᵉ →
    equiv-cocone-equiv-sequential-diagramᵉ cᵉ c'ᵉ eᵉ
  pr1ᵉ (equiv-hom-cocone-equiv-sequential-diagramᵉ hᵉ is-equiv-map-coconeᵉ) =
    (map-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ ,ᵉ is-equiv-map-coconeᵉ)
  pr1ᵉ (pr2ᵉ (equiv-hom-cocone-equiv-sequential-diagramᵉ hᵉ _)) =
    coh-map-cocone-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ
  pr2ᵉ (pr2ᵉ (equiv-hom-cocone-equiv-sequential-diagramᵉ hᵉ _)) =
    coh-hom-cocone-hom-sequential-diagramᵉ cᵉ c'ᵉ hᵉ
```