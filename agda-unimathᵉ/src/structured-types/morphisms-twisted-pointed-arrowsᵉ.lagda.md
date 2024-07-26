# Morphisms of twisted pointed arrows

```agda
module structured-types.morphisms-twisted-pointed-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.morphisms-twisted-arrowsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

Aᵉ
{{#conceptᵉ "morphismᵉ ofᵉ twistedᵉ pointedᵉ arrows"ᵉ Agda=hom-twisted-pointed-arrowᵉ}}
fromᵉ aᵉ [pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Aᵉ →∗ᵉ B`ᵉ to aᵉ pointedᵉ
mapᵉ `gᵉ : Xᵉ →∗ᵉ Y`ᵉ isᵉ aᵉ [triple](foundation.dependent-pair-types.mdᵉ) `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ
consistingᵉ ofᵉ pointedᵉ mapsᵉ `iᵉ : Xᵉ →∗ᵉ A`ᵉ andᵉ `jᵉ : Bᵉ →∗ᵉ Y`ᵉ andᵉ aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ)
`Hᵉ : jᵉ ∘∗ᵉ fᵉ ~∗ᵉ gᵉ ∘∗ᵉ i`ᵉ witnessingᵉ thatᵉ theᵉ diagramᵉ

```text
         iᵉ
    Aᵉ <-----ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

commutes.ᵉ

## Definitions

### Morphisms of twisted pointed arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ)
  where

  coherence-hom-twisted-pointed-arrowᵉ :
    (Xᵉ →∗ᵉ Aᵉ) → (Bᵉ →∗ᵉ Yᵉ) → UUᵉ (l3ᵉ ⊔ l4ᵉ)
  coherence-hom-twisted-pointed-arrowᵉ iᵉ jᵉ = ((jᵉ ∘∗ᵉ fᵉ) ∘∗ᵉ iᵉ) ~∗ᵉ gᵉ

  hom-twisted-pointed-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  hom-twisted-pointed-arrowᵉ =
    Σᵉ (Xᵉ →∗ᵉ Aᵉ) (λ iᵉ → Σᵉ (Bᵉ →∗ᵉ Yᵉ) (coherence-hom-twisted-pointed-arrowᵉ iᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  {fᵉ : Aᵉ →∗ᵉ Bᵉ} {gᵉ : Xᵉ →∗ᵉ Yᵉ} (hᵉ : hom-twisted-pointed-arrowᵉ fᵉ gᵉ)
  where

  pointed-map-domain-hom-twisted-pointed-arrowᵉ : Xᵉ →∗ᵉ Aᵉ
  pointed-map-domain-hom-twisted-pointed-arrowᵉ = pr1ᵉ hᵉ

  map-domain-hom-twisted-pointed-arrowᵉ :
    type-Pointed-Typeᵉ Xᵉ → type-Pointed-Typeᵉ Aᵉ
  map-domain-hom-twisted-pointed-arrowᵉ =
    map-pointed-mapᵉ pointed-map-domain-hom-twisted-pointed-arrowᵉ

  preserves-point-map-domain-hom-twisted-pointed-arrowᵉ :
    map-domain-hom-twisted-pointed-arrowᵉ (point-Pointed-Typeᵉ Xᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Aᵉ
  preserves-point-map-domain-hom-twisted-pointed-arrowᵉ =
    preserves-point-pointed-mapᵉ pointed-map-domain-hom-twisted-pointed-arrowᵉ

  pointed-map-codomain-hom-twisted-pointed-arrowᵉ : Bᵉ →∗ᵉ Yᵉ
  pointed-map-codomain-hom-twisted-pointed-arrowᵉ = pr1ᵉ (pr2ᵉ hᵉ)

  map-codomain-hom-twisted-pointed-arrowᵉ :
    type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Yᵉ
  map-codomain-hom-twisted-pointed-arrowᵉ =
    map-pointed-mapᵉ pointed-map-codomain-hom-twisted-pointed-arrowᵉ

  preserves-point-map-codomain-hom-twisted-pointed-arrowᵉ :
    map-codomain-hom-twisted-pointed-arrowᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Yᵉ
  preserves-point-map-codomain-hom-twisted-pointed-arrowᵉ =
    preserves-point-pointed-mapᵉ
      ( pointed-map-codomain-hom-twisted-pointed-arrowᵉ)

  coh-hom-twisted-pointed-arrowᵉ :
    coherence-hom-twisted-pointed-arrowᵉ
      ( fᵉ)
      ( gᵉ)
      ( pointed-map-domain-hom-twisted-pointed-arrowᵉ)
      ( pointed-map-codomain-hom-twisted-pointed-arrowᵉ)
  coh-hom-twisted-pointed-arrowᵉ = pr2ᵉ (pr2ᵉ hᵉ)

  htpy-coh-hom-twisted-pointed-arrowᵉ :
    coherence-hom-twisted-arrowᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( map-domain-hom-twisted-pointed-arrowᵉ)
      ( map-codomain-hom-twisted-pointed-arrowᵉ)
  htpy-coh-hom-twisted-pointed-arrowᵉ =
    htpy-pointed-htpyᵉ coh-hom-twisted-pointed-arrowᵉ
```