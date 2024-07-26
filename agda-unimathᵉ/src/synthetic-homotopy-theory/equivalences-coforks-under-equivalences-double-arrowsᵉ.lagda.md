# Equivalences of coforks

```agda
module synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-mapsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.double-arrowsᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.equivalences-double-arrowsᵉ
open import foundation.homotopiesᵉ
open import foundation.morphisms-arrowsᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import synthetic-homotopy-theory.coforksᵉ
open import synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrowsᵉ
```

</details>

## Idea

Considerᵉ twoᵉ [doubleᵉ arrows](foundation.double-arrows.mdᵉ) `f,ᵉ gᵉ : Aᵉ → B`ᵉ andᵉ
`h,ᵉ kᵉ : Uᵉ → V`,ᵉ equippedᵉ with [coforks](synthetic-homotopy-theory.coforks.mdᵉ)
`cᵉ : Bᵉ → X`ᵉ andᵉ `c'ᵉ : Vᵉ → Y`,ᵉ respectively,ᵉ andᵉ anᵉ
[equivalenceᵉ ofᵉ doubleᵉ arrows](foundation.equivalences-double-arrows.mdᵉ)
`eᵉ : (f,ᵉ gᵉ) ≃ᵉ (h,ᵉ k)`.ᵉ

Thenᵉ anᵉ
{{#conceptᵉ "equivalenceᵉ ofᵉ coforks"ᵉ Disambiguation="underᵉ anᵉ equivalenceᵉ ofᵉ doubleᵉ arrows"ᵉ Agda=equiv-cofork-equiv-double-arrowᵉ}}
underᵉ `e`ᵉ isᵉ aᵉ tripleᵉ `(m,ᵉ H,ᵉ K)`,ᵉ with `mᵉ : Xᵉ ≃ᵉ Y`ᵉ anᵉ
[equivalence](foundation-core.equivalences.mdᵉ) ofᵉ verticesᵉ ofᵉ theᵉ coforks,ᵉ `H`ᵉ aᵉ
[homotopy](foundation-core.homotopies.mdᵉ) witnessingᵉ thatᵉ theᵉ bottomᵉ squareᵉ in
theᵉ diagramᵉ

```text
           iᵉ
     Aᵉ -------->ᵉ Uᵉ
    | |    ≃ᵉ    | |
  fᵉ | | gᵉ     hᵉ | | kᵉ
    | |         | |
    ∨ᵉ ∨ᵉ    ≃ᵉ    ∨ᵉ ∨ᵉ
     Bᵉ -------->ᵉ Vᵉ
     |     jᵉ     |
   cᵉ |           | c'ᵉ
     |           |
     ∨ᵉ     ≃ᵉ     ∨ᵉ
     Xᵉ -------->ᵉ Yᵉ
           mᵉ
```

[commutes](foundation-core.commuting-squares-of-maps.md),ᵉ andᵉ `K`ᵉ aᵉ coherenceᵉ
datumᵉ "fillingᵉ theᵉ inside"ᵉ ---ᵉ weᵉ haveᵉ twoᵉ stacksᵉ ofᵉ squaresᵉ

```text
           iᵉ                        iᵉ
     Aᵉ -------->ᵉ Uᵉ            Aᵉ -------->ᵉ Uᵉ
     |     ≃ᵉ     |            |     ≃ᵉ     |
   fᵉ |           | hᵉ        gᵉ |           | kᵉ
     |           |            |           |
     ∨ᵉ     ≃ᵉ     ∨ᵉ            ∨ᵉ     ≃ᵉ     ∨ᵉ
     Bᵉ -------->ᵉ Vᵉ            Bᵉ -------->ᵉ Vᵉ
     |     jᵉ     |            |     jᵉ     |
   cᵉ |           | c'ᵉ       cᵉ |           | c'ᵉ
     |           |            |           |
     ∨ᵉ     ≃ᵉ     ∨ᵉ            ∨ᵉ     ≃ᵉ     ∨ᵉ
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

### Equivalences of coforks

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {aᵉ : double-arrowᵉ l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coforkᵉ aᵉ Xᵉ)
  {a'ᵉ : double-arrowᵉ l4ᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} (c'ᵉ : coforkᵉ a'ᵉ Yᵉ)
  (eᵉ : equiv-double-arrowᵉ aᵉ a'ᵉ)
  where

  coherence-map-cofork-equiv-cofork-equiv-double-arrowᵉ : (Xᵉ ≃ᵉ Yᵉ) → UUᵉ (l2ᵉ ⊔ l6ᵉ)
  coherence-map-cofork-equiv-cofork-equiv-double-arrowᵉ mᵉ =
    coherence-square-mapsᵉ
      ( codomain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
      ( map-coforkᵉ aᵉ cᵉ)
      ( map-coforkᵉ a'ᵉ c'ᵉ)
      ( map-equivᵉ mᵉ)

  coherence-equiv-cofork-equiv-double-arrowᵉ :
    (mᵉ : Xᵉ ≃ᵉ Yᵉ) → coherence-map-cofork-equiv-cofork-equiv-double-arrowᵉ mᵉ →
    UUᵉ (l1ᵉ ⊔ l6ᵉ)
  coherence-equiv-cofork-equiv-double-arrowᵉ mᵉ Hᵉ =
    ( ( Hᵉ ·rᵉ (left-map-double-arrowᵉ aᵉ)) ∙hᵉ
      ( ( map-coforkᵉ a'ᵉ c'ᵉ) ·lᵉ
        ( left-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)) ∙hᵉ
      ( (coh-coforkᵉ a'ᵉ c'ᵉ) ·rᵉ (domain-map-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ))) ~ᵉ
    ( ( (map-equivᵉ mᵉ) ·lᵉ (coh-coforkᵉ aᵉ cᵉ)) ∙hᵉ
      ( Hᵉ ·rᵉ (right-map-double-arrowᵉ aᵉ)) ∙hᵉ
      ( (map-coforkᵉ a'ᵉ c'ᵉ) ·lᵉ (right-square-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)))

  equiv-cofork-equiv-double-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l6ᵉ)
  equiv-cofork-equiv-double-arrowᵉ =
    Σᵉ ( Xᵉ ≃ᵉ Yᵉ)
      ( λ mᵉ →
        Σᵉ ( coherence-map-cofork-equiv-cofork-equiv-double-arrowᵉ mᵉ)
          ( coherence-equiv-cofork-equiv-double-arrowᵉ mᵉ))

  module _
    (e'ᵉ : equiv-cofork-equiv-double-arrowᵉ)
    where

    equiv-equiv-cofork-equiv-double-arrowᵉ : Xᵉ ≃ᵉ Yᵉ
    equiv-equiv-cofork-equiv-double-arrowᵉ = pr1ᵉ e'ᵉ

    map-equiv-cofork-equiv-double-arrowᵉ : Xᵉ → Yᵉ
    map-equiv-cofork-equiv-double-arrowᵉ =
      map-equivᵉ equiv-equiv-cofork-equiv-double-arrowᵉ

    is-equiv-map-equiv-cofork-equiv-double-arrowᵉ :
      is-equivᵉ map-equiv-cofork-equiv-double-arrowᵉ
    is-equiv-map-equiv-cofork-equiv-double-arrowᵉ =
      is-equiv-map-equivᵉ equiv-equiv-cofork-equiv-double-arrowᵉ

    coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ :
      coherence-map-cofork-equiv-cofork-equiv-double-arrowᵉ
        ( equiv-equiv-cofork-equiv-double-arrowᵉ)
    coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ = pr1ᵉ (pr2ᵉ e'ᵉ)

    equiv-map-cofork-equiv-cofork-equiv-double-arrowᵉ :
      equiv-arrowᵉ (map-coforkᵉ aᵉ cᵉ) (map-coforkᵉ a'ᵉ c'ᵉ)
    pr1ᵉ equiv-map-cofork-equiv-cofork-equiv-double-arrowᵉ =
      codomain-equiv-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ
    pr1ᵉ (pr2ᵉ equiv-map-cofork-equiv-cofork-equiv-double-arrowᵉ) =
      equiv-equiv-cofork-equiv-double-arrowᵉ
    pr2ᵉ (pr2ᵉ equiv-map-cofork-equiv-cofork-equiv-double-arrowᵉ) =
      coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ

    hom-map-cofork-equiv-cofork-equiv-double-arrowᵉ :
      hom-arrowᵉ (map-coforkᵉ aᵉ cᵉ) (map-coforkᵉ a'ᵉ c'ᵉ)
    hom-map-cofork-equiv-cofork-equiv-double-arrowᵉ =
      hom-equiv-arrowᵉ
        ( map-coforkᵉ aᵉ cᵉ)
        ( map-coforkᵉ a'ᵉ c'ᵉ)
        ( equiv-map-cofork-equiv-cofork-equiv-double-arrowᵉ)

    coh-equiv-cofork-equiv-double-arrowᵉ :
      coherence-equiv-cofork-equiv-double-arrowᵉ
        ( equiv-equiv-cofork-equiv-double-arrowᵉ)
        ( coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ)
    coh-equiv-cofork-equiv-double-arrowᵉ = pr2ᵉ (pr2ᵉ e'ᵉ)

    hom-equiv-cofork-equiv-double-arrowᵉ :
      hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ (hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)
    pr1ᵉ hom-equiv-cofork-equiv-double-arrowᵉ =
      map-equiv-cofork-equiv-double-arrowᵉ
    pr1ᵉ (pr2ᵉ hom-equiv-cofork-equiv-double-arrowᵉ) =
      coh-map-cofork-equiv-cofork-equiv-double-arrowᵉ
    pr2ᵉ (pr2ᵉ hom-equiv-cofork-equiv-double-arrowᵉ) =
      coh-equiv-cofork-equiv-double-arrowᵉ
```

### The predicate on morphisms of coforks under equivalences of double arrows of being an equivalence

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {aᵉ : double-arrowᵉ l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coforkᵉ aᵉ Xᵉ)
  {a'ᵉ : double-arrowᵉ l4ᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} (c'ᵉ : coforkᵉ a'ᵉ Yᵉ)
  (eᵉ : equiv-double-arrowᵉ aᵉ a'ᵉ)
  where

  is-equiv-hom-cofork-equiv-double-arrowᵉ :
    hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ (hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ) →
    UUᵉ (l3ᵉ ⊔ l6ᵉ)
  is-equiv-hom-cofork-equiv-double-arrowᵉ hᵉ =
    is-equivᵉ
      ( map-hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ hᵉ)

  is-equiv-hom-equiv-cofork-equiv-double-arrowᵉ :
    (e'ᵉ : equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ) →
    is-equiv-hom-cofork-equiv-double-arrowᵉ
      ( hom-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ)
  is-equiv-hom-equiv-cofork-equiv-double-arrowᵉ e'ᵉ =
    is-equiv-map-equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ e'ᵉ
```

## Properties

### Morphisms of coforks under equivalences of arrows which are equivalences are equivalences of coforks

Toᵉ constructᵉ anᵉ equivalenceᵉ ofᵉ coforksᵉ underᵉ anᵉ equivalenceᵉ `e`ᵉ ofᵉ doubleᵉ
arrows,ᵉ itᵉ sufficesᵉ to constructᵉ aᵉ morphismᵉ ofᵉ coforksᵉ underᵉ theᵉ underlyingᵉ
morphismᵉ ofᵉ doubleᵉ arrowsᵉ ofᵉ `e`,ᵉ andᵉ showᵉ thatᵉ theᵉ mapᵉ `Xᵉ → Y`ᵉ isᵉ anᵉ
equivalence.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ l5ᵉ l6ᵉ : Level}
  {aᵉ : double-arrowᵉ l1ᵉ l2ᵉ} {Xᵉ : UUᵉ l3ᵉ} (cᵉ : coforkᵉ aᵉ Xᵉ)
  {a'ᵉ : double-arrowᵉ l4ᵉ l5ᵉ} {Yᵉ : UUᵉ l6ᵉ} (c'ᵉ : coforkᵉ a'ᵉ Yᵉ)
  (eᵉ : equiv-double-arrowᵉ aᵉ a'ᵉ)
  where

  equiv-hom-cofork-equiv-double-arrowᵉ :
    (hᵉ : hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ (hom-equiv-double-arrowᵉ aᵉ a'ᵉ eᵉ)) →
    is-equiv-hom-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ hᵉ →
    equiv-cofork-equiv-double-arrowᵉ cᵉ c'ᵉ eᵉ
  pr1ᵉ (equiv-hom-cofork-equiv-double-arrowᵉ hᵉ is-equiv-map-coforkᵉ) =
    (map-hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ hᵉ ,ᵉ is-equiv-map-coforkᵉ)
  pr1ᵉ (pr2ᵉ (equiv-hom-cofork-equiv-double-arrowᵉ hᵉ _)) =
    coh-map-cofork-hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ hᵉ
  pr2ᵉ (pr2ᵉ (equiv-hom-cofork-equiv-double-arrowᵉ hᵉ _)) =
    coh-hom-cofork-hom-double-arrowᵉ cᵉ c'ᵉ hᵉ
```