# Morphisms of coforks

```agda
module synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.morphisms-double-arrowsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.coforksᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [doubleᵉ arrows](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`ᵉ andᵉ
`h,ᵉ kᵉ : Uᵉ → V`,ᵉ equippedᵉ with [coforks](synthetic-homotopy-theory.coforks.mdᵉ)
`cᵉ : Bᵉ → X`ᵉ andᵉ `c'ᵉ : Vᵉ → Y`,ᵉ respectively,ᵉ andᵉ aᵉ
[morphismᵉ ofᵉ doubleᵉ arrows](foundation.morphisms-double-arrows.mdᵉ)
`eᵉ : (f,ᵉ gᵉ) → (h,ᵉ k)`.ᵉ

Thenᵉ aᵉ
{{#conceptᵉ "morphismᵉ ofᵉ coforks"ᵉ Disambiguation="underᵉ aᵉ morphismᵉ ofᵉ doubleᵉ arrows"ᵉ Agda=hom-cofork-hom-double-arrowᵉ}}
underᵉ `e`ᵉ isᵉ aᵉ tripleᵉ `(m,ᵉ H,ᵉ K)`,ᵉ with `mᵉ : Xᵉ → Y`ᵉ aᵉ mapᵉ ofᵉ verticesᵉ ofᵉ theᵉ
coforks,ᵉ `H`ᵉ aᵉ [homotopy](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ
bottomᵉ squareᵉ in theᵉ diagramᵉ

```text
           iᵉ
     Aᵉ -------->ᵉ Uᵉ
    | |         | |
  fᵉ | | gᵉ     hᵉ | | kᵉ
    | |         | |
    ∨ᵉ ∨ᵉ         ∨ᵉ ∨ᵉ
     Bᵉ -------->ᵉ Vᵉ
     |     jᵉ     |
   cᵉ |           | c'ᵉ
     |           |
     ∨ᵉ           ∨ᵉ
     Xᵉ -------->ᵉ Yᵉ
           mᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md),ᵉ andᵉ `K`ᵉ aᵉ coherenceᵉ
datumᵉ "fillingᵉ theᵉ inside"ᵉ ---ᵉ weᵉ haveᵉ twoᵉ stacksᵉ ofᵉ squaresᵉ

```text
           iᵉ                        iᵉ
     Aᵉ -------->ᵉ Uᵉ            Aᵉ -------->ᵉ Uᵉ
     |           |            |           |
   fᵉ |           | hᵉ        gᵉ |           | kᵉ
     |           |            |           |
     ∨ᵉ           ∨ᵉ            ∨ᵉ           ∨ᵉ
     Bᵉ -------->ᵉ Vᵉ            Bᵉ -------->ᵉ Vᵉ
     |     jᵉ     |            |     jᵉ     |
   cᵉ |           | c'ᵉ       cᵉ |           | c'ᵉ
     |           |            |           |
     ∨ᵉ           ∨ᵉ            ∨ᵉ           ∨ᵉ
     Xᵉ -------->ᵉ Yᵉ            Xᵉ -------->ᵉ Yᵉ
           mᵉ                        mᵉ
```

whichᵉ shareᵉ theᵉ topᵉ mapᵉ `i`ᵉ andᵉ theᵉ bottomᵉ square,ᵉ andᵉ theᵉ coherencesᵉ ofᵉ `c`ᵉ andᵉ
`c'`ᵉ fillingᵉ theᵉ sides;ᵉ thatᵉ givesᵉ theᵉ homotopiesᵉ

```text
                                                iᵉ                 iᵉ
     Aᵉ                  Aᵉ                 Aᵉ -------->ᵉ Uᵉ     Aᵉ -------->ᵉ Uᵉ
     |                  |                             |                 |
   fᵉ |                fᵉ |                             | hᵉ               | kᵉ
     |                  |                             |                 |
     ∨ᵉ                  ∨ᵉ     jᵉ                       ∨ᵉ                 ∨ᵉ
     Bᵉ         ~ᵉ        Bᵉ -------->ᵉ Vᵉ       ~ᵉ         Vᵉ        ~ᵉ        Vᵉ
     |                              |                 |                 |
   cᵉ |                              | c'ᵉ              | c'ᵉ              | c'ᵉ
     |                              |                 |                 |
     ∨ᵉ                              ∨ᵉ                 ∨ᵉ                 ∨ᵉ
     Xᵉ -------->ᵉ Yᵉ                  Yᵉ                 Yᵉ                 Yᵉ
           mᵉ
```

andᵉ

```text
                                                                  iᵉ
     Aᵉ                 Aᵉ               Aᵉ                    Aᵉ -------->ᵉ Uᵉ
     |                 |               |                                |
   fᵉ |               gᵉ |             gᵉ |                                | kᵉ
     |                 |               |                                |
     ∨ᵉ                 ∨ᵉ               ∨ᵉ     jᵉ                          ∨ᵉ
     Bᵉ         ~ᵉ       Bᵉ       ~ᵉ       Bᵉ -------->ᵉ Vᵉ           ~ᵉ        Vᵉ
     |                 |                           |                    |
   cᵉ |               cᵉ |                           | c'ᵉ                 | c'ᵉ
     |                 |                           |                    |
     ∨ᵉ                 ∨ᵉ                           ∨ᵉ                    ∨ᵉ
     Xᵉ -------->ᵉ Yᵉ     Xᵉ -------->ᵉ Yᵉ               Yᵉ                    Yᵉ ,ᵉ
           mᵉ                 mᵉ
```

whichᵉ areᵉ requiredᵉ to beᵉ homotopic.ᵉ

## Definitions

### Morphisms of coforks under morphisms of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {aᵉ : double-arrowᵉ l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coforkᵉ aᵉ Xᵉ)
  {a'ᵉ : double-arrowᵉ l4ᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} (c'ᵉ : coforkᵉ a'ᵉ Yᵉ)
  (hᵉ : hom-double-arrowᵉ aᵉ a'ᵉ)
  where

  coherence-map-cofork-hom-cofork-hom-double-arrowᵉ : (Xᵉ → Yᵉ) → UUᵉ (l2ᵉ ⊔ l6ᵉ)
  coherence-map-cofork-hom-cofork-hom-double-arrowᵉ uᵉ =
    coherence-square-mapsᵉ
      ( codomain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)
      ( map-coforkᵉ aᵉ cᵉ)
      ( map-coforkᵉ a'ᵉ c'ᵉ)
      ( uᵉ)

  coherence-hom-cofork-hom-double-arrowᵉ :
    (uᵉ : Xᵉ → Yᵉ) → coherence-map-cofork-hom-cofork-hom-double-arrowᵉ uᵉ →
    UUᵉ (l1ᵉ ⊔ l6ᵉ)
  coherence-hom-cofork-hom-double-arrowᵉ uᵉ Hᵉ =
    ( ( Hᵉ ·rᵉ (left-map-double-arrowᵉ aᵉ)) ∙hᵉ
      ( ( map-coforkᵉ a'ᵉ c'ᵉ) ·lᵉ
        ( left-square-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)) ∙hᵉ
      ( (coh-coforkᵉ a'ᵉ c'ᵉ) ·rᵉ (domain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ))) ~ᵉ
    ( ( uᵉ ·lᵉ (coh-coforkᵉ aᵉ cᵉ)) ∙hᵉ
      ( Hᵉ ·rᵉ (right-map-double-arrowᵉ aᵉ)) ∙hᵉ
      ( (map-coforkᵉ a'ᵉ c'ᵉ) ·lᵉ (right-square-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ)))

  hom-cofork-hom-double-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ)
  hom-cofork-hom-double-arrowᵉ =
    Σᵉ ( Xᵉ → Yᵉ)
      ( λ uᵉ →
        Σᵉ ( coherence-map-cofork-hom-cofork-hom-double-arrowᵉ uᵉ)
          ( coherence-hom-cofork-hom-double-arrowᵉ uᵉ))
```

### Components of a morphism of coforks under a morphism of double arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {aᵉ : double-arrowᵉ l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coforkᵉ aᵉ Xᵉ)
  {a'ᵉ : double-arrowᵉ l4ᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} (c'ᵉ : coforkᵉ a'ᵉ Yᵉ)
  {hᵉ : hom-double-arrowᵉ aᵉ a'ᵉ} (mᵉ : hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ hᵉ)
  where

  map-hom-cofork-hom-double-arrowᵉ : Xᵉ → Yᵉ
  map-hom-cofork-hom-double-arrowᵉ = pr1ᵉ mᵉ

  coh-map-cofork-hom-cofork-hom-double-arrowᵉ :
    coherence-map-cofork-hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ hᵉ
      ( map-hom-cofork-hom-double-arrowᵉ)
  coh-map-cofork-hom-cofork-hom-double-arrowᵉ = pr1ᵉ (pr2ᵉ mᵉ)

  hom-map-cofork-hom-cofork-hom-double-arrowᵉ :
    hom-arrowᵉ (map-coforkᵉ aᵉ cᵉ) (map-coforkᵉ a'ᵉ c'ᵉ)
  pr1ᵉ hom-map-cofork-hom-cofork-hom-double-arrowᵉ =
    codomain-map-hom-double-arrowᵉ aᵉ a'ᵉ hᵉ
  pr1ᵉ (pr2ᵉ hom-map-cofork-hom-cofork-hom-double-arrowᵉ) =
    map-hom-cofork-hom-double-arrowᵉ
  pr2ᵉ (pr2ᵉ hom-map-cofork-hom-cofork-hom-double-arrowᵉ) =
    coh-map-cofork-hom-cofork-hom-double-arrowᵉ

  coh-hom-cofork-hom-double-arrowᵉ :
    coherence-hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ hᵉ
      ( map-hom-cofork-hom-double-arrowᵉ)
      ( coh-map-cofork-hom-cofork-hom-double-arrowᵉ)
  coh-hom-cofork-hom-double-arrowᵉ = pr2ᵉ (pr2ᵉ mᵉ)
```