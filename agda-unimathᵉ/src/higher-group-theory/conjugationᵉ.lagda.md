# Conjugation in higher groups

```agda
module higher-group-theory.conjugationᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ
open import higher-group-theory.homomorphisms-higher-groupsᵉ

open import structured-types.conjugation-pointed-typesᵉ

open import synthetic-homotopy-theory.conjugation-loopsᵉ
```

</details>

## Idea

Theᵉ **conjugationᵉ homomorphism**ᵉ onᵉ anᵉ
[∞-group](higher-group-theory.higher-groups.mdᵉ) `G`ᵉ isᵉ theᵉ
[conjugationᵉ map](structured-types.conjugation-pointed-types.mdᵉ) ofᵉ itsᵉ
classifyingᵉ [pointedᵉ type](structured-types.pointed-types.mdᵉ) `BG`.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} (Gᵉ : ∞-Groupᵉ lᵉ) (gᵉ : type-∞-Groupᵉ Gᵉ)
  where

  conjugation-∞-Groupᵉ : hom-∞-Groupᵉ Gᵉ Gᵉ
  conjugation-∞-Groupᵉ =
    conjugation-Pointed-Typeᵉ (classifying-pointed-type-∞-Groupᵉ Gᵉ) gᵉ

  classifying-map-conjugation-∞-Groupᵉ :
    classifying-type-∞-Groupᵉ Gᵉ → classifying-type-∞-Groupᵉ Gᵉ
  classifying-map-conjugation-∞-Groupᵉ =
    classifying-map-hom-∞-Groupᵉ Gᵉ Gᵉ conjugation-∞-Groupᵉ

  preserves-point-classifying-map-conjugation-∞-Groupᵉ :
    classifying-map-conjugation-∞-Groupᵉ (shape-∞-Groupᵉ Gᵉ) ＝ᵉ shape-∞-Groupᵉ Gᵉ
  preserves-point-classifying-map-conjugation-∞-Groupᵉ =
    preserves-point-classifying-map-hom-∞-Groupᵉ Gᵉ Gᵉ conjugation-∞-Groupᵉ

  map-conjugation-∞-Groupᵉ : type-∞-Groupᵉ Gᵉ → type-∞-Groupᵉ Gᵉ
  map-conjugation-∞-Groupᵉ = map-hom-∞-Groupᵉ Gᵉ Gᵉ conjugation-∞-Groupᵉ

  compute-map-conjugation-∞-Groupᵉ :
    map-conjugation-Ωᵉ gᵉ ~ᵉ map-conjugation-∞-Groupᵉ
  compute-map-conjugation-∞-Groupᵉ =
    htpy-compute-action-on-loops-conjugation-Pointed-Typeᵉ
      ( gᵉ)
```