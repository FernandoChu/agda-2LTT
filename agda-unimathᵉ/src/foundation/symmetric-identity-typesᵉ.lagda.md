# The symmetric identity types

```agda
module foundation.symmetric-identity-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.function-extensionalityᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.homotopy-inductionᵉ
open import foundation.identity-typesᵉ
open import foundation.structure-identity-principleᵉ
open import foundation.universe-levelsᵉ
open import foundation.unordered-pairsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.coproduct-typesᵉ
open import foundation-core.equality-dependent-pair-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.torsorial-type-familiesᵉ

open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Weᵉ constructᵉ aᵉ variantᵉ ofᵉ theᵉ identityᵉ typeᵉ equippedᵉ with aᵉ naturalᵉ
`ℤ/2`-action.ᵉ

## Definition

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  symmetric-Idᵉ :
    (aᵉ : unordered-pairᵉ Aᵉ) → UUᵉ lᵉ
  symmetric-Idᵉ aᵉ =
    Σᵉ Aᵉ (λ xᵉ → (iᵉ : type-unordered-pairᵉ aᵉ) → xᵉ ＝ᵉ element-unordered-pairᵉ aᵉ iᵉ)

  module _
    (aᵉ : unordered-pairᵉ Aᵉ)
    where

    Eq-symmetric-Idᵉ :
      (pᵉ qᵉ : symmetric-Idᵉ aᵉ) → UUᵉ lᵉ
    Eq-symmetric-Idᵉ (xᵉ ,ᵉ Hᵉ) qᵉ =
      Σᵉ (xᵉ ＝ᵉ pr1ᵉ qᵉ) (λ pᵉ → (iᵉ : type-unordered-pairᵉ aᵉ) → Hᵉ iᵉ ＝ᵉ (pᵉ ∙ᵉ pr2ᵉ qᵉ iᵉ))

    refl-Eq-symmetric-Idᵉ :
      (pᵉ : symmetric-Idᵉ aᵉ) → Eq-symmetric-Idᵉ pᵉ pᵉ
    pr1ᵉ (refl-Eq-symmetric-Idᵉ (xᵉ ,ᵉ Hᵉ)) = reflᵉ
    pr2ᵉ (refl-Eq-symmetric-Idᵉ (xᵉ ,ᵉ Hᵉ)) iᵉ = reflᵉ

    is-torsorial-Eq-symmetric-Idᵉ :
      (pᵉ : symmetric-Idᵉ aᵉ) → is-torsorialᵉ (Eq-symmetric-Idᵉ pᵉ)
    is-torsorial-Eq-symmetric-Idᵉ (xᵉ ,ᵉ Hᵉ) =
      is-torsorial-Eq-structureᵉ
        ( is-torsorial-Idᵉ xᵉ)
        ( xᵉ ,ᵉ reflᵉ)
        ( is-torsorial-htpyᵉ Hᵉ)

    Eq-eq-symmetric-Idᵉ :
      (pᵉ qᵉ : symmetric-Idᵉ aᵉ) → pᵉ ＝ᵉ qᵉ → Eq-symmetric-Idᵉ pᵉ qᵉ
    Eq-eq-symmetric-Idᵉ pᵉ .pᵉ reflᵉ = refl-Eq-symmetric-Idᵉ pᵉ

    is-equiv-Eq-eq-symmetric-Idᵉ :
      (pᵉ qᵉ : symmetric-Idᵉ aᵉ) → is-equivᵉ (Eq-eq-symmetric-Idᵉ pᵉ qᵉ)
    is-equiv-Eq-eq-symmetric-Idᵉ pᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-symmetric-Idᵉ pᵉ)
        ( Eq-eq-symmetric-Idᵉ pᵉ)

    extensionality-symmetric-Idᵉ :
      (pᵉ qᵉ : symmetric-Idᵉ aᵉ) → (pᵉ ＝ᵉ qᵉ) ≃ᵉ Eq-symmetric-Idᵉ pᵉ qᵉ
    pr1ᵉ (extensionality-symmetric-Idᵉ pᵉ qᵉ) = Eq-eq-symmetric-Idᵉ pᵉ qᵉ
    pr2ᵉ (extensionality-symmetric-Idᵉ pᵉ qᵉ) = is-equiv-Eq-eq-symmetric-Idᵉ pᵉ qᵉ

    eq-Eq-symmetric-Idᵉ :
      (pᵉ qᵉ : symmetric-Idᵉ aᵉ) → Eq-symmetric-Idᵉ pᵉ qᵉ → pᵉ ＝ᵉ qᵉ
    eq-Eq-symmetric-Idᵉ pᵉ qᵉ = map-inv-equivᵉ (extensionality-symmetric-Idᵉ pᵉ qᵉ)

  module _
    (aᵉ bᵉ : Aᵉ)
    where

    map-compute-symmetric-Idᵉ :
      symmetric-Idᵉ (standard-unordered-pairᵉ aᵉ bᵉ) → aᵉ ＝ᵉ bᵉ
    map-compute-symmetric-Idᵉ (xᵉ ,ᵉ fᵉ) = invᵉ (fᵉ (zero-Finᵉ 1ᵉ)) ∙ᵉ fᵉ (one-Finᵉ 1ᵉ)

    map-inv-compute-symmetric-Idᵉ :
      aᵉ ＝ᵉ bᵉ → symmetric-Idᵉ (standard-unordered-pairᵉ aᵉ bᵉ)
    pr1ᵉ (map-inv-compute-symmetric-Idᵉ pᵉ) = aᵉ
    pr2ᵉ (map-inv-compute-symmetric-Idᵉ pᵉ) (inlᵉ (inrᵉ _)) = reflᵉ
    pr2ᵉ (map-inv-compute-symmetric-Idᵉ pᵉ) (inrᵉ _) = pᵉ

    is-section-map-inv-compute-symmetric-Idᵉ :
      ( map-compute-symmetric-Idᵉ ∘ᵉ map-inv-compute-symmetric-Idᵉ) ~ᵉ idᵉ
    is-section-map-inv-compute-symmetric-Idᵉ reflᵉ = reflᵉ

    abstract
      is-retraction-map-inv-compute-symmetric-Idᵉ :
        ( map-inv-compute-symmetric-Idᵉ ∘ᵉ map-compute-symmetric-Idᵉ) ~ᵉ idᵉ
      is-retraction-map-inv-compute-symmetric-Idᵉ (xᵉ ,ᵉ fᵉ) =
        eq-Eq-symmetric-Idᵉ
          ( standard-unordered-pairᵉ aᵉ bᵉ)
          ( map-inv-compute-symmetric-Idᵉ (map-compute-symmetric-Idᵉ (xᵉ ,ᵉ fᵉ)))
          ( xᵉ ,ᵉ fᵉ)
          ( ( invᵉ (fᵉ (zero-Finᵉ 1ᵉ))) ,ᵉ
            ( λ where
              ( inlᵉ (inrᵉ _)) → invᵉ (left-invᵉ (fᵉ (zero-Finᵉ 1ᵉ)))
              ( inrᵉ _) → reflᵉ))

    is-equiv-map-compute-symmetric-Idᵉ :
      is-equivᵉ (map-compute-symmetric-Idᵉ)
    is-equiv-map-compute-symmetric-Idᵉ =
      is-equiv-is-invertibleᵉ
        ( map-inv-compute-symmetric-Idᵉ)
        ( is-section-map-inv-compute-symmetric-Idᵉ)
        ( is-retraction-map-inv-compute-symmetric-Idᵉ)

    compute-symmetric-Idᵉ :
      symmetric-Idᵉ (standard-unordered-pairᵉ aᵉ bᵉ) ≃ᵉ (aᵉ ＝ᵉ bᵉ)
    pr1ᵉ (compute-symmetric-Idᵉ) = map-compute-symmetric-Idᵉ
    pr2ᵉ (compute-symmetric-Idᵉ) = is-equiv-map-compute-symmetric-Idᵉ
```

## Properties

### The action of functions on symmetric identity types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-symmetric-Idᵉ :
    (fᵉ : Aᵉ → Bᵉ) (aᵉ : unordered-pairᵉ Aᵉ) →
    symmetric-Idᵉ aᵉ → symmetric-Idᵉ (map-unordered-pairᵉ fᵉ aᵉ)
  map-symmetric-Idᵉ fᵉ aᵉ =
    map-Σᵉ
      ( λ bᵉ → (xᵉ : type-unordered-pairᵉ aᵉ) → bᵉ ＝ᵉ fᵉ (element-unordered-pairᵉ aᵉ xᵉ))
      ( fᵉ)
      ( λ xᵉ → map-Πᵉ (λ iᵉ → apᵉ fᵉ))
```

### The action of equivalences on symmetric identity types

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  equiv-symmetric-Idᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (aᵉ : unordered-pairᵉ Aᵉ) →
    symmetric-Idᵉ aᵉ ≃ᵉ symmetric-Idᵉ (map-equiv-unordered-pairᵉ eᵉ aᵉ)
  equiv-symmetric-Idᵉ eᵉ aᵉ =
    equiv-Σᵉ
      ( λ bᵉ →
        (xᵉ : type-unordered-pairᵉ aᵉ) →
        bᵉ ＝ᵉ map-equivᵉ eᵉ (element-unordered-pairᵉ aᵉ xᵉ))
      ( eᵉ)
      ( λ xᵉ →
        equiv-Π-equiv-familyᵉ (λ iᵉ → equiv-apᵉ eᵉ xᵉ (element-unordered-pairᵉ aᵉ iᵉ)))

  map-equiv-symmetric-Idᵉ :
    (eᵉ : Aᵉ ≃ᵉ Bᵉ) (aᵉ : unordered-pairᵉ Aᵉ) →
    symmetric-Idᵉ aᵉ → symmetric-Idᵉ (map-equiv-unordered-pairᵉ eᵉ aᵉ)
  map-equiv-symmetric-Idᵉ eᵉ aᵉ = map-equivᵉ (equiv-symmetric-Idᵉ eᵉ aᵉ)

id-equiv-symmetric-Idᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (aᵉ : unordered-pairᵉ Aᵉ) →
  map-equiv-symmetric-Idᵉ id-equivᵉ aᵉ ~ᵉ idᵉ
id-equiv-symmetric-Idᵉ aᵉ (xᵉ ,ᵉ Hᵉ) =
  eq-pair-eq-fiberᵉ (eq-htpyᵉ (λ uᵉ → ap-idᵉ (Hᵉ uᵉ)))
```

### Transport in the symmetric identity type along observational equality of unordered pairs

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  equiv-tr-symmetric-Idᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ) → Eq-unordered-pairᵉ pᵉ qᵉ →
    symmetric-Idᵉ pᵉ ≃ᵉ symmetric-Idᵉ qᵉ
  equiv-tr-symmetric-Idᵉ (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ) (eᵉ ,ᵉ Hᵉ) =
    equiv-totᵉ (λ aᵉ → equiv-Πᵉ (λ xᵉ → aᵉ ＝ᵉ gᵉ xᵉ) eᵉ (λ xᵉ → equiv-concat'ᵉ aᵉ (Hᵉ xᵉ)))

  tr-symmetric-Idᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ)
    (eᵉ : type-unordered-pairᵉ pᵉ ≃ᵉ type-unordered-pairᵉ qᵉ) →
    (element-unordered-pairᵉ pᵉ ~ᵉ (element-unordered-pairᵉ qᵉ ∘ᵉ map-equivᵉ eᵉ)) →
    symmetric-Idᵉ pᵉ → symmetric-Idᵉ qᵉ
  tr-symmetric-Idᵉ pᵉ qᵉ eᵉ Hᵉ = map-equivᵉ (equiv-tr-symmetric-Idᵉ pᵉ qᵉ (pairᵉ eᵉ Hᵉ))

  compute-pr2-tr-symmetric-Idᵉ :
    (pᵉ qᵉ : unordered-pairᵉ Aᵉ)
    (eᵉ : type-unordered-pairᵉ pᵉ ≃ᵉ type-unordered-pairᵉ qᵉ) →
    (Hᵉ : element-unordered-pairᵉ pᵉ ~ᵉ (element-unordered-pairᵉ qᵉ ∘ᵉ map-equivᵉ eᵉ)) →
    {aᵉ : Aᵉ}
    (Kᵉ : (xᵉ : type-unordered-pairᵉ pᵉ) → aᵉ ＝ᵉ element-unordered-pairᵉ pᵉ xᵉ) →
    (xᵉ : type-unordered-pairᵉ pᵉ) →
    pr2ᵉ (tr-symmetric-Idᵉ pᵉ qᵉ eᵉ Hᵉ (aᵉ ,ᵉ Kᵉ)) (map-equivᵉ eᵉ xᵉ) ＝ᵉ (Kᵉ xᵉ ∙ᵉ Hᵉ xᵉ)
  compute-pr2-tr-symmetric-Idᵉ (Xᵉ ,ᵉ fᵉ) (Yᵉ ,ᵉ gᵉ) eᵉ Hᵉ {aᵉ} =
    compute-map-equiv-Πᵉ (λ xᵉ → aᵉ ＝ᵉ gᵉ xᵉ) eᵉ (λ xᵉ → equiv-concat'ᵉ aᵉ (Hᵉ xᵉ))

  refl-Eq-unordered-pair-tr-symmetric-Idᵉ :
    (pᵉ : unordered-pairᵉ Aᵉ) →
    tr-symmetric-Idᵉ pᵉ pᵉ id-equivᵉ refl-htpyᵉ ~ᵉ idᵉ
  refl-Eq-unordered-pair-tr-symmetric-Idᵉ pᵉ (aᵉ ,ᵉ Kᵉ) =
    eq-pair-eq-fiberᵉ
      ( eq-htpyᵉ
        ( ( compute-pr2-tr-symmetric-Idᵉ pᵉ pᵉ id-equivᵉ refl-htpyᵉ Kᵉ) ∙hᵉ
          ( right-unit-htpyᵉ)))
```