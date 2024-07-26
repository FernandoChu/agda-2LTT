# Equivalences of pointed arrows

```agda
module structured-types.equivalences-pointed-arrowsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.equivalences-arrowsᵉ
open import foundation.function-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import structured-types.commuting-squares-of-pointed-mapsᵉ
open import structured-types.pointed-equivalencesᵉ
open import structured-types.pointed-homotopiesᵉ
open import structured-types.pointed-mapsᵉ
open import structured-types.pointed-typesᵉ
```

</details>

## Idea

Anᵉ {{#conceptᵉ "equivalenceᵉ ofᵉ pointedᵉ arrows"ᵉ Agda=equiv-pointed-arrowᵉ}} fromᵉ aᵉ
[pointedᵉ map](structured-types.pointed-maps.mdᵉ) `fᵉ : Aᵉ →∗ᵉ B`ᵉ to aᵉ pointedᵉ mapᵉ
`gᵉ : Xᵉ →∗ᵉ Y`ᵉ isᵉ aᵉ [triple](foundation.dependent-pair-types.mdᵉ) `(iᵉ ,ᵉ jᵉ ,ᵉ H)`ᵉ
consistingᵉ ofᵉ [pointedᵉ equivalences](structured-types.pointed-equivalences.mdᵉ)
`iᵉ : Aᵉ ≃∗ᵉ X`ᵉ andᵉ `jᵉ : Bᵉ ≃∗ᵉ Y`ᵉ andᵉ aᵉ
[pointedᵉ homotopy](structured-types.pointed-homotopies.mdᵉ)
`Hᵉ : jᵉ ∘∗ᵉ fᵉ ~∗ᵉ gᵉ ∘∗ᵉ i`ᵉ witnessingᵉ thatᵉ theᵉ squareᵉ

```text
        iᵉ
    Aᵉ ----->ᵉ Xᵉ
    |        |
  fᵉ |        | gᵉ
    ∨ᵉ        ∨ᵉ
    Bᵉ ----->ᵉ Yᵉ
        jᵉ
```

[commutes](structured-types.commuting-squares-of-pointed-maps.md).ᵉ

## Definitions

### Equivalences of pointed arrows

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  (fᵉ : Aᵉ →∗ᵉ Bᵉ) (gᵉ : Xᵉ →∗ᵉ Yᵉ)
  where

  coherence-equiv-pointed-arrowᵉ :
    (Aᵉ ≃∗ᵉ Xᵉ) → (Bᵉ ≃∗ᵉ Yᵉ) → UUᵉ (l1ᵉ ⊔ l4ᵉ)
  coherence-equiv-pointed-arrowᵉ iᵉ jᵉ =
    coherence-square-pointed-mapsᵉ
      ( pointed-map-pointed-equivᵉ iᵉ)
      ( fᵉ)
      ( gᵉ)
      ( pointed-map-pointed-equivᵉ jᵉ)

  equiv-pointed-arrowᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ ⊔ l4ᵉ)
  equiv-pointed-arrowᵉ =
    Σᵉ (Aᵉ ≃∗ᵉ Xᵉ) (λ iᵉ → Σᵉ (Bᵉ ≃∗ᵉ Yᵉ) (coherence-equiv-pointed-arrowᵉ iᵉ))

module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Aᵉ : Pointed-Typeᵉ l1ᵉ} {Bᵉ : Pointed-Typeᵉ l2ᵉ}
  {Xᵉ : Pointed-Typeᵉ l3ᵉ} {Yᵉ : Pointed-Typeᵉ l4ᵉ}
  {fᵉ : Aᵉ →∗ᵉ Bᵉ} {gᵉ : Xᵉ →∗ᵉ Yᵉ} (eᵉ : equiv-pointed-arrowᵉ fᵉ gᵉ)
  where

  pointed-equiv-domain-equiv-pointed-arrowᵉ : Aᵉ ≃∗ᵉ Xᵉ
  pointed-equiv-domain-equiv-pointed-arrowᵉ = pr1ᵉ eᵉ

  equiv-domain-equiv-pointed-arrowᵉ : type-Pointed-Typeᵉ Aᵉ ≃ᵉ type-Pointed-Typeᵉ Xᵉ
  equiv-domain-equiv-pointed-arrowᵉ =
    equiv-pointed-equivᵉ pointed-equiv-domain-equiv-pointed-arrowᵉ

  pointed-map-domain-equiv-pointed-arrowᵉ : Aᵉ →∗ᵉ Xᵉ
  pointed-map-domain-equiv-pointed-arrowᵉ =
    pointed-map-pointed-equivᵉ pointed-equiv-domain-equiv-pointed-arrowᵉ

  map-domain-equiv-pointed-arrowᵉ : type-Pointed-Typeᵉ Aᵉ → type-Pointed-Typeᵉ Xᵉ
  map-domain-equiv-pointed-arrowᵉ =
    map-pointed-equivᵉ pointed-equiv-domain-equiv-pointed-arrowᵉ

  preserves-point-map-domain-equiv-pointed-arrowᵉ :
    map-domain-equiv-pointed-arrowᵉ (point-Pointed-Typeᵉ Aᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Xᵉ
  preserves-point-map-domain-equiv-pointed-arrowᵉ =
    preserves-point-pointed-equivᵉ pointed-equiv-domain-equiv-pointed-arrowᵉ

  pointed-equiv-codomain-equiv-pointed-arrowᵉ : Bᵉ ≃∗ᵉ Yᵉ
  pointed-equiv-codomain-equiv-pointed-arrowᵉ = pr1ᵉ (pr2ᵉ eᵉ)

  equiv-codomain-equiv-pointed-arrowᵉ : type-Pointed-Typeᵉ Bᵉ ≃ᵉ type-Pointed-Typeᵉ Yᵉ
  equiv-codomain-equiv-pointed-arrowᵉ =
    equiv-pointed-equivᵉ pointed-equiv-codomain-equiv-pointed-arrowᵉ

  map-codomain-equiv-pointed-arrowᵉ : type-Pointed-Typeᵉ Bᵉ → type-Pointed-Typeᵉ Yᵉ
  map-codomain-equiv-pointed-arrowᵉ =
    map-pointed-equivᵉ pointed-equiv-codomain-equiv-pointed-arrowᵉ

  preserves-point-map-codomain-equiv-pointed-arrowᵉ :
    map-codomain-equiv-pointed-arrowᵉ (point-Pointed-Typeᵉ Bᵉ) ＝ᵉ
    point-Pointed-Typeᵉ Yᵉ
  preserves-point-map-codomain-equiv-pointed-arrowᵉ =
    preserves-point-pointed-equivᵉ pointed-equiv-codomain-equiv-pointed-arrowᵉ

  coh-equiv-pointed-arrowᵉ :
    coherence-equiv-pointed-arrowᵉ
      ( fᵉ)
      ( gᵉ)
      ( pointed-equiv-domain-equiv-pointed-arrowᵉ)
      ( pointed-equiv-codomain-equiv-pointed-arrowᵉ)
  coh-equiv-pointed-arrowᵉ = pr2ᵉ (pr2ᵉ eᵉ)

  htpy-coh-equiv-pointed-arrowᵉ :
    coherence-equiv-arrowᵉ
      ( map-pointed-mapᵉ fᵉ)
      ( map-pointed-mapᵉ gᵉ)
      ( equiv-domain-equiv-pointed-arrowᵉ)
      ( equiv-codomain-equiv-pointed-arrowᵉ)
  htpy-coh-equiv-pointed-arrowᵉ = htpy-pointed-htpyᵉ coh-equiv-pointed-arrowᵉ
```