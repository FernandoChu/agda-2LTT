# The universal property of set quotients

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.universal-property-set-quotientsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.effective-maps-equivalence-relationsᵉ
open import foundation.epimorphisms-with-respect-to-setsᵉ
open import foundation.equivalence-classesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.function-extensionalityᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.imagesᵉ
open import foundation.injective-mapsᵉ
open import foundation.locally-small-typesᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.propositional-extensionalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.reflecting-maps-equivalence-relationsᵉ
open import foundation.setsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universal-property-dependent-pair-typesᵉ
open import foundation.universal-property-imageᵉ
open import foundation.universe-levelsᵉ
open import foundation.whiskering-homotopies-compositionᵉ

open import foundation-core.cartesian-product-typesᵉ
open import foundation-core.commuting-triangles-of-mapsᵉ
open import foundation-core.contractible-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.equivalence-relationsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ
open import foundation-core.homotopiesᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.small-typesᵉ
open import foundation-core.subtypesᵉ
open import foundation-core.torsorial-type-familiesᵉ
open import foundation-core.type-theoretic-principle-of-choiceᵉ
open import foundation-core.univalenceᵉ
```

</details>

## Idea

Theᵉ universalᵉ propertyᵉ ofᵉ setᵉ quotientsᵉ characterizesᵉ mapsᵉ outᵉ ofᵉ setᵉ quotients.ᵉ

## Definitions

### The universal property of set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  where

  precomp-Set-Quotientᵉ :
    {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) →
    (hom-Setᵉ Bᵉ Xᵉ) → reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Xᵉ)
  pr1ᵉ (precomp-Set-Quotientᵉ Xᵉ gᵉ) =
    gᵉ ∘ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)
  pr2ᵉ (precomp-Set-Quotientᵉ Xᵉ gᵉ) rᵉ =
    apᵉ gᵉ (reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ rᵉ)

is-set-quotientᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  (Bᵉ : Setᵉ l3ᵉ) (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) → UUωᵉ
is-set-quotientᵉ Rᵉ Bᵉ fᵉ =
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) → is-equivᵉ (precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  where

  universal-property-set-quotientᵉ : UUωᵉ
  universal-property-set-quotientᵉ =
    {lᵉ : Level} (Xᵉ : Setᵉ lᵉ)
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Xᵉ)) →
    is-contrᵉ
      ( Σᵉ ( hom-Setᵉ Bᵉ Xᵉ)
          ( λ hᵉ →
            ( hᵉ ∘ᵉ map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ) ~ᵉ
            ( map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ)))
```

## Properties

### Precomposing the identity function by a reflecting map yields the original reflecting map

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  where

  precomp-id-Set-Quotientᵉ : precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Bᵉ idᵉ ＝ᵉ fᵉ
  precomp-id-Set-Quotientᵉ =
    eq-htpy-reflecting-map-equivalence-relationᵉ Rᵉ Bᵉ
      ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Bᵉ idᵉ)
      ( fᵉ)
      ( refl-htpyᵉ)
```

### If a reflecting map is a set quotient, then it satisfies the universal property of the set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  where

  universal-property-set-quotient-is-set-quotientᵉ :
    is-set-quotientᵉ Rᵉ Bᵉ fᵉ → universal-property-set-quotientᵉ Rᵉ Bᵉ fᵉ
  universal-property-set-quotient-is-set-quotientᵉ Qᵉ Xᵉ gᵉ =
    is-contr-equiv'ᵉ
      ( fiberᵉ (precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ) gᵉ)
      ( equiv-totᵉ
        ( λ hᵉ →
          extensionality-reflecting-map-equivalence-relationᵉ Rᵉ Xᵉ
            ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ hᵉ)
            ( gᵉ)))
      ( is-contr-map-is-equivᵉ (Qᵉ Xᵉ) gᵉ)

  map-universal-property-set-quotient-is-set-quotientᵉ :
    {l4ᵉ : Level} (Ufᵉ : is-set-quotientᵉ Rᵉ Bᵉ fᵉ)
    (Cᵉ : Setᵉ l4ᵉ) (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Cᵉ)) →
    type-Setᵉ Bᵉ → type-Setᵉ Cᵉ
  map-universal-property-set-quotient-is-set-quotientᵉ Ufᵉ Cᵉ gᵉ =
    pr1ᵉ (centerᵉ (universal-property-set-quotient-is-set-quotientᵉ Ufᵉ Cᵉ gᵉ))

  triangle-universal-property-set-quotient-is-set-quotientᵉ :
    {l4ᵉ : Level} (Ufᵉ : is-set-quotientᵉ Rᵉ Bᵉ fᵉ)
    (Cᵉ : Setᵉ l4ᵉ) (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Cᵉ)) →
    ( ( map-universal-property-set-quotient-is-set-quotientᵉ Ufᵉ Cᵉ gᵉ) ∘ᵉ
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ)) ~ᵉ
    ( map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ)
  triangle-universal-property-set-quotient-is-set-quotientᵉ Ufᵉ Cᵉ gᵉ =
    ( pr2ᵉ (centerᵉ (universal-property-set-quotient-is-set-quotientᵉ Ufᵉ Cᵉ gᵉ)))
```

### If a reflecting map satisfies the universal property of the set quotient, then it is a set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  where

  is-set-quotient-universal-property-set-quotientᵉ :
    universal-property-set-quotientᵉ Rᵉ Bᵉ fᵉ → is-set-quotientᵉ Rᵉ Bᵉ fᵉ
  is-set-quotient-universal-property-set-quotientᵉ Ufᵉ Xᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ gᵉ →
        is-contr-equivᵉ
          ( Σᵉ ( hom-Setᵉ Bᵉ Xᵉ)
              ( λ hᵉ →
                ( hᵉ ∘ᵉ map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ) ~ᵉ
                ( map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ)))
          ( equiv-totᵉ
            ( λ hᵉ →
              extensionality-reflecting-map-equivalence-relationᵉ Rᵉ Xᵉ
                ( precomp-Set-Quotientᵉ Rᵉ Bᵉ fᵉ Xᵉ hᵉ)
                ( gᵉ)))
          ( Ufᵉ Xᵉ gᵉ))
```

### A map out of a type equipped with an equivalence relation is effective if and only if it is an image factorization

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (qᵉ : Aᵉ → type-Setᵉ Bᵉ)
  where

  is-effective-is-imageᵉ :
    (iᵉ : type-Setᵉ Bᵉ ↪ᵉ (Aᵉ → Propᵉ l2ᵉ)) →
    (Tᵉ : (prop-equivalence-relationᵉ Rᵉ) ~ᵉ ((map-embᵉ iᵉ) ∘ᵉ qᵉ)) →
    is-imageᵉ (prop-equivalence-relationᵉ Rᵉ) iᵉ (pairᵉ qᵉ Tᵉ) →
    is-effectiveᵉ Rᵉ qᵉ
  is-effective-is-imageᵉ iᵉ Tᵉ Hᵉ xᵉ yᵉ =
    ( is-effective-classᵉ Rᵉ xᵉ yᵉ) ∘eᵉ
    ( ( inv-equivᵉ (equiv-ap-embᵉ (emb-equivalence-classᵉ Rᵉ))) ∘eᵉ
      ( ( inv-equivᵉ (convert-eq-valuesᵉ Tᵉ xᵉ yᵉ)) ∘eᵉ
        ( equiv-ap-embᵉ iᵉ)))

  is-surjective-and-effective-is-imageᵉ :
    (iᵉ : type-Setᵉ Bᵉ ↪ᵉ (Aᵉ → Propᵉ l2ᵉ)) →
    (Tᵉ : (prop-equivalence-relationᵉ Rᵉ) ~ᵉ ((map-embᵉ iᵉ) ∘ᵉ qᵉ)) →
    is-imageᵉ (prop-equivalence-relationᵉ Rᵉ) iᵉ (pairᵉ qᵉ Tᵉ) →
    is-surjective-and-effectiveᵉ Rᵉ qᵉ
  pr1ᵉ (is-surjective-and-effective-is-imageᵉ iᵉ Tᵉ Hᵉ) =
    is-surjective-is-imageᵉ (prop-equivalence-relationᵉ Rᵉ) iᵉ (pairᵉ qᵉ Tᵉ) Hᵉ
  pr2ᵉ (is-surjective-and-effective-is-imageᵉ iᵉ Tᵉ Hᵉ) =
    is-effective-is-imageᵉ iᵉ Tᵉ Hᵉ

  is-locally-small-is-surjective-and-effectiveᵉ :
    is-surjective-and-effectiveᵉ Rᵉ qᵉ → is-locally-smallᵉ l2ᵉ (type-Setᵉ Bᵉ)
  is-locally-small-is-surjective-and-effectiveᵉ eᵉ xᵉ yᵉ =
    apply-universal-property-trunc-Propᵉ
      ( pr1ᵉ eᵉ xᵉ)
      ( is-small-Propᵉ l2ᵉ (xᵉ ＝ᵉ yᵉ))
      ( λ uᵉ →
        apply-universal-property-trunc-Propᵉ
          ( pr1ᵉ eᵉ yᵉ)
          ( is-small-Propᵉ l2ᵉ (xᵉ ＝ᵉ yᵉ))
          ( αᵉ uᵉ))
    where
    αᵉ : fiberᵉ qᵉ xᵉ → fiberᵉ qᵉ yᵉ → is-smallᵉ l2ᵉ (xᵉ ＝ᵉ yᵉ)
    pr1ᵉ (αᵉ (pairᵉ aᵉ reflᵉ) (pairᵉ bᵉ reflᵉ)) = sim-equivalence-relationᵉ Rᵉ aᵉ bᵉ
    pr2ᵉ (αᵉ (pairᵉ aᵉ reflᵉ) (pairᵉ bᵉ reflᵉ)) = pr2ᵉ eᵉ aᵉ bᵉ

  large-map-emb-is-surjective-and-effectiveᵉ :
    is-surjective-and-effectiveᵉ Rᵉ qᵉ → type-Setᵉ Bᵉ → Aᵉ → Propᵉ l3ᵉ
  large-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ = Id-Propᵉ Bᵉ bᵉ (qᵉ aᵉ)

  small-map-emb-is-surjective-and-effectiveᵉ :
    is-surjective-and-effectiveᵉ Rᵉ qᵉ → type-Setᵉ Bᵉ → Aᵉ →
    Σᵉ (Propᵉ l3ᵉ) (λ Pᵉ → is-smallᵉ l2ᵉ (type-Propᵉ Pᵉ))
  pr1ᵉ (small-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ) =
    large-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ
  pr2ᵉ (small-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ) =
    is-locally-small-is-surjective-and-effectiveᵉ Hᵉ bᵉ (qᵉ aᵉ)

  map-emb-is-surjective-and-effectiveᵉ :
    is-surjective-and-effectiveᵉ Rᵉ qᵉ → type-Setᵉ Bᵉ → Aᵉ → Propᵉ l2ᵉ
  pr1ᵉ (map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ) =
    pr1ᵉ (pr2ᵉ (small-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ))
  pr2ᵉ (map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ) =
    is-prop-equiv'ᵉ
      ( pr2ᵉ (pr2ᵉ (small-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ)))
      ( is-prop-type-Propᵉ
        ( large-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ))

  compute-map-emb-is-surjective-and-effectiveᵉ :
    (Hᵉ : is-surjective-and-effectiveᵉ Rᵉ qᵉ) (bᵉ : type-Setᵉ Bᵉ) (aᵉ : Aᵉ) →
    type-Propᵉ (large-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ) ≃ᵉ
    type-Propᵉ (map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ)
  compute-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ =
    pr2ᵉ (pr2ᵉ (small-map-emb-is-surjective-and-effectiveᵉ Hᵉ bᵉ aᵉ))

  triangle-emb-is-surjective-and-effectiveᵉ :
    (Hᵉ : is-surjective-and-effectiveᵉ Rᵉ qᵉ) →
    prop-equivalence-relationᵉ Rᵉ ~ᵉ (map-emb-is-surjective-and-effectiveᵉ Hᵉ ∘ᵉ qᵉ)
  triangle-emb-is-surjective-and-effectiveᵉ Hᵉ aᵉ =
    eq-htpyᵉ
      ( λ xᵉ →
        eq-equiv-Propᵉ
          ( ( compute-map-emb-is-surjective-and-effectiveᵉ Hᵉ (qᵉ aᵉ) xᵉ) ∘eᵉ
            ( inv-equivᵉ (pr2ᵉ Hᵉ aᵉ xᵉ))))

  is-emb-map-emb-is-surjective-and-effectiveᵉ :
    (Hᵉ : is-surjective-and-effectiveᵉ Rᵉ qᵉ) →
    is-embᵉ (map-emb-is-surjective-and-effectiveᵉ Hᵉ)
  is-emb-map-emb-is-surjective-and-effectiveᵉ Hᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-function-typeᵉ is-set-type-Propᵉ)
      ( λ {xᵉ} {yᵉ} pᵉ →
        apply-universal-property-trunc-Propᵉ
          ( pr1ᵉ Hᵉ yᵉ)
          ( Id-Propᵉ Bᵉ xᵉ yᵉ)
          ( αᵉ pᵉ))
    where
    αᵉ :
      {xᵉ yᵉ : type-Setᵉ Bᵉ}
      (pᵉ :
        ( map-emb-is-surjective-and-effectiveᵉ Hᵉ xᵉ) ＝ᵉ
        ( map-emb-is-surjective-and-effectiveᵉ Hᵉ yᵉ)) →
      fiberᵉ qᵉ yᵉ →
      type-Propᵉ (Id-Propᵉ Bᵉ xᵉ yᵉ)
    αᵉ {xᵉ} pᵉ (pairᵉ aᵉ reflᵉ) =
      map-inv-equivᵉ
        ( ( inv-equivᵉ
            ( pr2ᵉ
              ( is-locally-small-is-surjective-and-effectiveᵉ
                Hᵉ (qᵉ aᵉ) (qᵉ aᵉ)))) ∘eᵉ
          ( ( equiv-eqᵉ (apᵉ pr1ᵉ (htpy-eqᵉ pᵉ aᵉ))) ∘eᵉ
            ( pr2ᵉ
              ( is-locally-small-is-surjective-and-effectiveᵉ Hᵉ xᵉ (qᵉ aᵉ)))))
        ( reflᵉ)

  emb-is-surjective-and-effectiveᵉ :
    (Hᵉ : is-surjective-and-effectiveᵉ Rᵉ qᵉ) →
    type-Setᵉ Bᵉ ↪ᵉ (Aᵉ → Propᵉ l2ᵉ)
  pr1ᵉ (emb-is-surjective-and-effectiveᵉ Hᵉ) =
    map-emb-is-surjective-and-effectiveᵉ Hᵉ
  pr2ᵉ (emb-is-surjective-and-effectiveᵉ Hᵉ) =
    is-emb-map-emb-is-surjective-and-effectiveᵉ Hᵉ

  is-emb-large-map-emb-is-surjective-and-effectiveᵉ :
    (eᵉ : is-surjective-and-effectiveᵉ Rᵉ qᵉ) →
    is-embᵉ (large-map-emb-is-surjective-and-effectiveᵉ eᵉ)
  is-emb-large-map-emb-is-surjective-and-effectiveᵉ eᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-function-typeᵉ is-set-type-Propᵉ)
      ( λ {xᵉ} {yᵉ} pᵉ →
        apply-universal-property-trunc-Propᵉ
          ( pr1ᵉ eᵉ yᵉ)
          ( Id-Propᵉ Bᵉ xᵉ yᵉ)
          ( αᵉ pᵉ))
    where
    αᵉ :
      {xᵉ yᵉ : type-Setᵉ Bᵉ}
      (pᵉ :
        ( large-map-emb-is-surjective-and-effectiveᵉ eᵉ xᵉ) ＝ᵉ
        ( large-map-emb-is-surjective-and-effectiveᵉ eᵉ yᵉ)) →
      fiberᵉ qᵉ yᵉ →
      type-Propᵉ (Id-Propᵉ Bᵉ xᵉ yᵉ)
    αᵉ pᵉ (pairᵉ aᵉ reflᵉ) = map-inv-equivᵉ (equiv-eqᵉ (apᵉ pr1ᵉ (htpy-eqᵉ pᵉ aᵉ))) reflᵉ

  large-emb-is-surjective-and-effectiveᵉ :
    is-surjective-and-effectiveᵉ Rᵉ qᵉ → type-Setᵉ Bᵉ ↪ᵉ (Aᵉ → Propᵉ l3ᵉ)
  pr1ᵉ (large-emb-is-surjective-and-effectiveᵉ eᵉ) =
    large-map-emb-is-surjective-and-effectiveᵉ eᵉ
  pr2ᵉ (large-emb-is-surjective-and-effectiveᵉ eᵉ) =
    is-emb-large-map-emb-is-surjective-and-effectiveᵉ eᵉ

  is-image-is-surjective-and-effectiveᵉ :
    ( Hᵉ : is-surjective-and-effectiveᵉ Rᵉ qᵉ) →
    is-imageᵉ
      ( prop-equivalence-relationᵉ Rᵉ)
      ( emb-is-surjective-and-effectiveᵉ Hᵉ)
      ( pairᵉ qᵉ (triangle-emb-is-surjective-and-effectiveᵉ Hᵉ))
  is-image-is-surjective-and-effectiveᵉ Hᵉ =
    is-image-is-surjectiveᵉ
      ( prop-equivalence-relationᵉ Rᵉ)
      ( emb-is-surjective-and-effectiveᵉ Hᵉ)
      ( pairᵉ qᵉ (triangle-emb-is-surjective-and-effectiveᵉ Hᵉ))
      ( pr1ᵉ Hᵉ)
```

### Any set quotient `q : A → B` of an equivalence relation `R` on `A` is surjective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  where

  is-surjective-is-set-quotientᵉ :
    (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    is-set-quotientᵉ Rᵉ Bᵉ qᵉ →
    is-surjectiveᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
  is-surjective-is-set-quotientᵉ qᵉ Qᵉ bᵉ =
    trᵉ
      ( λ yᵉ →
        type-trunc-Propᵉ (fiberᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ) yᵉ))
      ( htpy-eqᵉ
        ( apᵉ pr1ᵉ
          ( eq-is-contrᵉ
            ( universal-property-set-quotient-is-set-quotientᵉ Rᵉ Bᵉ qᵉ Qᵉ Bᵉ qᵉ)
            { inclusion-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ) ∘ᵉ βᵉ ,ᵉ
              δᵉ}
            { idᵉ ,ᵉ refl-htpyᵉ}))
        ( bᵉ))
      ( pr2ᵉ (βᵉ bᵉ))
    where
    αᵉ :
      reflects-equivalence-relationᵉ Rᵉ
        ( map-unit-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
    αᵉ {xᵉ} {yᵉ} rᵉ =
      is-injective-is-embᵉ
        ( is-emb-inclusion-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
        ( map-equivᵉ
          ( convert-eq-valuesᵉ
            ( triangle-unit-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
            ( xᵉ)
            ( yᵉ))
          ( reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ rᵉ))
    βᵉ : type-Setᵉ Bᵉ → imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
    βᵉ = map-inv-is-equivᵉ
        ( Qᵉ ( pairᵉ
              ( imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
                ( is-set-imᵉ
                  ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
                  ( is-set-type-Setᵉ Bᵉ))))
          ( pairᵉ (map-unit-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)) αᵉ)
    γᵉ :
      ( βᵉ ∘ᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)) ~ᵉ
      ( map-unit-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
    γᵉ =
      htpy-eqᵉ
        ( apᵉ
            ( pr1ᵉ)
            ( is-section-map-inv-is-equivᵉ
              ( Qᵉ ( pairᵉ
                    ( imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
                    ( is-set-imᵉ
                      ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
                      ( is-set-type-Setᵉ Bᵉ))))
              ( map-unit-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ) ,ᵉ αᵉ)))
    δᵉ :
      ( ( inclusion-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ) ∘ᵉ βᵉ) ∘ᵉ
        ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)) ~ᵉ
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
    δᵉ =
      ( inclusion-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ) ·lᵉ γᵉ) ∙hᵉ
      ( triangle-unit-imᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
```

### Any set quotient `q : A → B` of an equivalence relation `R` on `A` is effective

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  where

  is-effective-is-set-quotientᵉ :
    (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    is-set-quotientᵉ Rᵉ Bᵉ qᵉ →
    is-effectiveᵉ Rᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
  is-effective-is-set-quotientᵉ qᵉ Qᵉ xᵉ yᵉ =
    inv-equivᵉ (compute-Pᵉ yᵉ) ∘eᵉ δᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ yᵉ)
    where
    αᵉ : Σᵉ (Aᵉ → Propᵉ l2ᵉ) (reflects-equivalence-relationᵉ Rᵉ)
    αᵉ = pairᵉ
        ( prop-equivalence-relationᵉ Rᵉ xᵉ)
        ( λ rᵉ →
          eq-iffᵉ
            ( transitive-equivalence-relationᵉ Rᵉ _ _ _ rᵉ)
            ( transitive-equivalence-relationᵉ Rᵉ _ _ _
              ( symmetric-equivalence-relationᵉ Rᵉ _ _ rᵉ)))
    Pᵉ : type-Setᵉ Bᵉ → Propᵉ l2ᵉ
    Pᵉ = map-inv-is-equivᵉ (Qᵉ (Prop-Setᵉ l2ᵉ)) αᵉ
    compute-Pᵉ :
      (aᵉ : Aᵉ) →
      sim-equivalence-relationᵉ Rᵉ xᵉ aᵉ ≃ᵉ
      type-Propᵉ (Pᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ aᵉ))
    compute-Pᵉ aᵉ =
      equiv-eqᵉ
        ( apᵉ pr1ᵉ
          ( htpy-eqᵉ
            ( apᵉ pr1ᵉ
              ( invᵉ (is-section-map-inv-is-equivᵉ (Qᵉ (Prop-Setᵉ l2ᵉ)) αᵉ)))
            ( aᵉ)))
    point-Pᵉ : type-Propᵉ (Pᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ))
    point-Pᵉ = map-equivᵉ (compute-Pᵉ xᵉ) (refl-equivalence-relationᵉ Rᵉ xᵉ)
    center-total-Pᵉ : Σᵉ (type-Setᵉ Bᵉ) (λ bᵉ → type-Propᵉ (Pᵉ bᵉ))
    center-total-Pᵉ =
      pairᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ) point-Pᵉ
    contraction-total-Pᵉ :
      (uᵉ : Σᵉ (type-Setᵉ Bᵉ) (λ bᵉ → type-Propᵉ (Pᵉ bᵉ))) → center-total-Pᵉ ＝ᵉ uᵉ
    contraction-total-Pᵉ (pairᵉ bᵉ pᵉ) =
      eq-type-subtypeᵉ Pᵉ
        ( apply-universal-property-trunc-Propᵉ
          ( is-surjective-is-set-quotientᵉ Rᵉ Bᵉ qᵉ Qᵉ bᵉ)
          ( Id-Propᵉ Bᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ) bᵉ)
          ( λ vᵉ →
            ( reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ
              ( map-inv-equivᵉ
                ( compute-Pᵉ (pr1ᵉ vᵉ))
                ( inv-trᵉ (type-Propᵉ ∘ᵉ Pᵉ) (pr2ᵉ vᵉ) pᵉ))) ∙ᵉ
            ( pr2ᵉ vᵉ)))
    is-torsorial-Pᵉ : is-torsorialᵉ (λ bᵉ → type-Propᵉ (Pᵉ bᵉ))
    is-torsorial-Pᵉ = pairᵉ center-total-Pᵉ contraction-total-Pᵉ
    βᵉ :
      (bᵉ : type-Setᵉ Bᵉ) →
      map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ ＝ᵉ bᵉ → type-Propᵉ (Pᵉ bᵉ)
    βᵉ .(map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ) reflᵉ = point-Pᵉ
    γᵉ : (bᵉ : type-Setᵉ Bᵉ) → is-equivᵉ (βᵉ bᵉ)
    γᵉ = fundamental-theorem-idᵉ is-torsorial-Pᵉ βᵉ
    δᵉ :
      (bᵉ : type-Setᵉ Bᵉ) →
      (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ ＝ᵉ bᵉ) ≃ᵉ type-Propᵉ (Pᵉ bᵉ)
    δᵉ bᵉ = pairᵉ (βᵉ bᵉ) (γᵉ bᵉ)

  apply-effectiveness-is-set-quotientᵉ :
    (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    is-set-quotientᵉ Rᵉ Bᵉ qᵉ →
    {xᵉ yᵉ : Aᵉ} →
    ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ ＝ᵉ
      map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ yᵉ) →
    sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ
  apply-effectiveness-is-set-quotientᵉ qᵉ Hᵉ {xᵉ} {yᵉ} =
    map-equivᵉ (is-effective-is-set-quotientᵉ qᵉ Hᵉ xᵉ yᵉ)

  apply-effectiveness-is-set-quotient'ᵉ :
    (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    is-set-quotientᵉ Rᵉ Bᵉ qᵉ →
    {xᵉ yᵉ : Aᵉ} → sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ →
    map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ xᵉ ＝ᵉ
    map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ yᵉ
  apply-effectiveness-is-set-quotient'ᵉ qᵉ Hᵉ {xᵉ} {yᵉ} =
    map-inv-equivᵉ (is-effective-is-set-quotientᵉ qᵉ Hᵉ xᵉ yᵉ)

  is-surjective-and-effective-is-set-quotientᵉ :
    (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ)) →
    is-set-quotientᵉ Rᵉ Bᵉ qᵉ →
    is-surjective-and-effectiveᵉ Rᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
  pr1ᵉ (is-surjective-and-effective-is-set-quotientᵉ qᵉ Qᵉ) =
    is-surjective-is-set-quotientᵉ Rᵉ Bᵉ qᵉ Qᵉ
  pr2ᵉ (is-surjective-and-effective-is-set-quotientᵉ qᵉ Qᵉ) =
    is-effective-is-set-quotientᵉ qᵉ Qᵉ
```

### Any surjective and effective map is a set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Bᵉ : Setᵉ l3ᵉ)
  (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
  where

  private
    module _
      ( Eᵉ :
        is-surjective-and-effectiveᵉ Rᵉ
          ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ))
      { lᵉ : Level}
      ( Xᵉ : Setᵉ lᵉ)
      ( fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Xᵉ))
      where

      P-Propᵉ : (bᵉ : type-Setᵉ Bᵉ) (xᵉ : type-Setᵉ Xᵉ) → Propᵉ (l1ᵉ ⊔ l3ᵉ ⊔ lᵉ)
      P-Propᵉ bᵉ xᵉ =
        exists-structure-Propᵉ Aᵉ
          ( λ aᵉ →
            ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ aᵉ ＝ᵉ xᵉ) ×ᵉ
            ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ aᵉ ＝ᵉ bᵉ))

      Pᵉ : (bᵉ : type-Setᵉ Bᵉ) (xᵉ : type-Setᵉ Xᵉ) → UUᵉ (l1ᵉ ⊔ l3ᵉ ⊔ lᵉ)
      Pᵉ bᵉ xᵉ = type-Propᵉ (P-Propᵉ bᵉ xᵉ)

      all-elements-equal-total-Pᵉ :
        (bᵉ : type-Setᵉ Bᵉ) → all-elements-equalᵉ (Σᵉ (type-Setᵉ Xᵉ) (Pᵉ bᵉ))
      all-elements-equal-total-Pᵉ bᵉ xᵉ yᵉ =
        eq-type-subtypeᵉ
          ( P-Propᵉ bᵉ)
          ( apply-universal-property-trunc-Propᵉ
            ( pr2ᵉ xᵉ)
            ( Id-Propᵉ Xᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ))
            ( λ uᵉ →
              apply-universal-property-trunc-Propᵉ
                ( pr2ᵉ yᵉ)
                ( Id-Propᵉ Xᵉ (pr1ᵉ xᵉ) (pr1ᵉ yᵉ))
                ( λ vᵉ →
                  ( invᵉ (pr1ᵉ (pr2ᵉ uᵉ))) ∙ᵉ
                  ( ( pr2ᵉ fᵉ
                      ( map-equivᵉ
                        ( pr2ᵉ Eᵉ (pr1ᵉ uᵉ) (pr1ᵉ vᵉ))
                        ( (pr2ᵉ (pr2ᵉ uᵉ)) ∙ᵉ (invᵉ (pr2ᵉ (pr2ᵉ vᵉ)))))) ∙ᵉ
                    ( pr1ᵉ (pr2ᵉ vᵉ))))))

      is-prop-total-Pᵉ : (bᵉ : type-Setᵉ Bᵉ) → is-propᵉ (Σᵉ (type-Setᵉ Xᵉ) (Pᵉ bᵉ))
      is-prop-total-Pᵉ bᵉ =
        is-prop-all-elements-equalᵉ (all-elements-equal-total-Pᵉ bᵉ)

      αᵉ : (bᵉ : type-Setᵉ Bᵉ) → Σᵉ (type-Setᵉ Xᵉ) (Pᵉ bᵉ)
      αᵉ =
        map-inv-is-equivᵉ
          ( dependent-universal-property-surjection-is-surjectiveᵉ
            ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
            ( pr1ᵉ Eᵉ)
            ( λ bᵉ →
              pairᵉ
                ( Σᵉ (type-Setᵉ Xᵉ) (Pᵉ bᵉ))
                ( is-prop-total-Pᵉ bᵉ)))
          ( λ aᵉ → pairᵉ (pr1ᵉ fᵉ aᵉ) (unit-trunc-Propᵉ (pairᵉ aᵉ (pairᵉ reflᵉ reflᵉ))))

      βᵉ :
        (aᵉ : Aᵉ) →
        ( αᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ aᵉ)) ＝ᵉ
        ( pairᵉ (pr1ᵉ fᵉ aᵉ) (unit-trunc-Propᵉ (pairᵉ aᵉ (pairᵉ reflᵉ reflᵉ))))
      βᵉ = htpy-eqᵉ
            ( is-section-map-inv-is-equivᵉ
              ( dependent-universal-property-surjection-is-surjectiveᵉ
                ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
                ( pr1ᵉ Eᵉ)
                ( λ bᵉ → pairᵉ (Σᵉ (type-Setᵉ Xᵉ) (Pᵉ bᵉ)) (is-prop-total-Pᵉ bᵉ)))
              ( λ aᵉ →
                pairᵉ (pr1ᵉ fᵉ aᵉ) (unit-trunc-Propᵉ (pairᵉ aᵉ (pairᵉ reflᵉ reflᵉ)))))

  is-set-quotient-is-surjective-and-effectiveᵉ :
    ( Eᵉ :
      is-surjective-and-effectiveᵉ Rᵉ
        ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)) →
    is-set-quotientᵉ Rᵉ Bᵉ qᵉ
  is-set-quotient-is-surjective-and-effectiveᵉ Eᵉ Xᵉ =
    is-equiv-is-contr-mapᵉ
      ( λ fᵉ →
        is-proof-irrelevant-is-propᵉ
        ( is-prop-equivᵉ
          ( equiv-totᵉ
            ( λ _ →
              equiv-ap-inclusion-subtypeᵉ
                ( reflects-prop-equivalence-relationᵉ Rᵉ Xᵉ)))
          ( is-prop-map-is-embᵉ
            ( is-epimorphism-is-surjective-Setᵉ (pr1ᵉ Eᵉ) Xᵉ)
            ( pr1ᵉ fᵉ)))
        ( pairᵉ
          ( λ bᵉ → pr1ᵉ (αᵉ Eᵉ Xᵉ fᵉ bᵉ))
          ( eq-type-subtypeᵉ
            ( reflects-prop-equivalence-relationᵉ Rᵉ Xᵉ)
            ( eq-htpyᵉ (λ aᵉ → apᵉ pr1ᵉ (βᵉ Eᵉ Xᵉ fᵉ aᵉ))))))

  universal-property-set-quotient-is-surjective-and-effectiveᵉ :
    ( Eᵉ :
      is-surjective-and-effectiveᵉ Rᵉ
        ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)) →
    universal-property-set-quotientᵉ Rᵉ Bᵉ qᵉ
  universal-property-set-quotient-is-surjective-and-effectiveᵉ Eᵉ =
    universal-property-set-quotient-is-set-quotientᵉ Rᵉ Bᵉ qᵉ
      ( is-set-quotient-is-surjective-and-effectiveᵉ Eᵉ)
```

### The large set quotient satisfies the universal property of set quotients

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ)
  where

  universal-property-equivalence-classᵉ :
    universal-property-set-quotientᵉ Rᵉ
      ( equivalence-class-Setᵉ Rᵉ)
      ( quotient-reflecting-map-equivalence-classᵉ Rᵉ)
  universal-property-equivalence-classᵉ =
    universal-property-set-quotient-is-surjective-and-effectiveᵉ Rᵉ
      ( equivalence-class-Setᵉ Rᵉ)
      ( quotient-reflecting-map-equivalence-classᵉ Rᵉ)
      ( is-surjective-and-effective-classᵉ Rᵉ)

  is-set-quotient-equivalence-classᵉ :
    is-set-quotientᵉ Rᵉ
      ( equivalence-class-Setᵉ Rᵉ)
      ( quotient-reflecting-map-equivalence-classᵉ Rᵉ)
  is-set-quotient-equivalence-classᵉ =
    is-set-quotient-universal-property-set-quotientᵉ Rᵉ
      ( equivalence-class-Setᵉ Rᵉ)
      ( quotient-reflecting-map-equivalence-classᵉ Rᵉ)
      ( universal-property-equivalence-classᵉ)

  map-universal-property-equivalence-classᵉ :
    {l4ᵉ : Level} (Cᵉ : Setᵉ l4ᵉ)
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Cᵉ)) →
    equivalence-classᵉ Rᵉ → type-Setᵉ Cᵉ
  map-universal-property-equivalence-classᵉ Cᵉ gᵉ =
    pr1ᵉ (centerᵉ (universal-property-equivalence-classᵉ Cᵉ gᵉ))

  triangle-universal-property-equivalence-classᵉ :
    {l4ᵉ : Level} (Cᵉ : Setᵉ l4ᵉ)
    (gᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Cᵉ)) →
    ( ( map-universal-property-equivalence-classᵉ Cᵉ gᵉ) ∘ᵉ
      ( classᵉ Rᵉ)) ~ᵉ
    ( map-reflecting-map-equivalence-relationᵉ Rᵉ gᵉ)
  triangle-universal-property-equivalence-classᵉ Cᵉ gᵉ =
    pr2ᵉ (centerᵉ (universal-property-equivalence-classᵉ Cᵉ gᵉ))
```

### The induction property of set quotients

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Qᵉ : Setᵉ l3ᵉ)
  (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Qᵉ))
  (Uᵉ : is-set-quotientᵉ Rᵉ Qᵉ qᵉ)
  where

  ind-is-set-quotientᵉ :
    {lᵉ : Level} (Pᵉ : type-Setᵉ Qᵉ → Propᵉ lᵉ) →
    ((aᵉ : Aᵉ) → type-Propᵉ (Pᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ aᵉ))) →
    ((xᵉ : type-Setᵉ Qᵉ) → type-Propᵉ (Pᵉ xᵉ))
  ind-is-set-quotientᵉ =
    apply-dependent-universal-property-surjection-is-surjectiveᵉ
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ)
      ( is-surjective-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ)
```

### Injectiveness of maps defined by the universal property of the set quotient

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Rᵉ : equivalence-relationᵉ l2ᵉ Aᵉ) (Qᵉ : Setᵉ l3ᵉ)
  (qᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Qᵉ))
  (Uᵉ : is-set-quotientᵉ Rᵉ Qᵉ qᵉ)
  where

  is-injective-map-universal-property-set-quotient-is-set-quotientᵉ :
    {l4ᵉ : Level} (Bᵉ : Setᵉ l4ᵉ)
    (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
    ( Hᵉ :
      (xᵉ yᵉ : Aᵉ) →
      ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ xᵉ ＝ᵉ
        map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ yᵉ) →
      sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ) →
    is-injectiveᵉ
      ( map-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ)
  is-injective-map-universal-property-set-quotient-is-set-quotientᵉ
    Bᵉ fᵉ Hᵉ {xᵉ} {yᵉ} =
    ind-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ
      ( λ uᵉ →
        function-Propᵉ
          ( map-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ uᵉ ＝ᵉ
            map-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ yᵉ)
          ( Id-Propᵉ Qᵉ uᵉ yᵉ))
      ( λ aᵉ →
        ( ind-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ
          ( λ vᵉ →
            function-Propᵉ
              ( ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ aᵉ) ＝ᵉ
                ( map-universal-property-set-quotient-is-set-quotientᵉ
                  Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ vᵉ))
              ( Id-Propᵉ Qᵉ (map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ aᵉ) vᵉ))
          ( λ bᵉ pᵉ →
            reflects-map-reflecting-map-equivalence-relationᵉ Rᵉ qᵉ
              ( Hᵉ aᵉ bᵉ
                ( ( pᵉ) ∙ᵉ
                  ( triangle-universal-property-set-quotient-is-set-quotientᵉ
                    Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ bᵉ))))
          ( yᵉ)) ∘ᵉ
        ( concatᵉ
          ( invᵉ
            ( triangle-universal-property-set-quotient-is-set-quotientᵉ
              Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ aᵉ))
          ( map-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ yᵉ)))
      ( xᵉ)

  is-emb-map-universal-property-set-quotient-is-set-quotientᵉ :
    {l4ᵉ : Level} (Bᵉ : Setᵉ l4ᵉ)
    (fᵉ : reflecting-map-equivalence-relationᵉ Rᵉ (type-Setᵉ Bᵉ))
    ( Hᵉ : (xᵉ yᵉ : Aᵉ) →
          ( map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ xᵉ ＝ᵉ
            map-reflecting-map-equivalence-relationᵉ Rᵉ fᵉ yᵉ) →
          sim-equivalence-relationᵉ Rᵉ xᵉ yᵉ) →
    is-embᵉ
      ( map-universal-property-set-quotient-is-set-quotientᵉ Rᵉ Qᵉ qᵉ Uᵉ Bᵉ fᵉ)
  is-emb-map-universal-property-set-quotient-is-set-quotientᵉ Bᵉ fᵉ Hᵉ =
    is-emb-is-injectiveᵉ
      ( is-set-type-Setᵉ Bᵉ)
      ( is-injective-map-universal-property-set-quotient-is-set-quotientᵉ Bᵉ fᵉ Hᵉ)
```

### The type of extensions of maps into a set along a surjection is equivalent to the proposition that that map equalizes the values that the surjection equalizes

Considerᵉ aᵉ surjectiveᵉ mapᵉ `fᵉ : Aᵉ ↠ᵉ B`ᵉ andᵉ aᵉ mapᵉ `gᵉ : Aᵉ → C`ᵉ intoᵉ aᵉ setᵉ `C`.ᵉ
Recallᵉ fromᵉ
[Epimorphismsᵉ with respectᵉ to sets](foundation.epimorphisms-with-respect-to-sets.mdᵉ)
thatᵉ theᵉ typeᵉ

```text
  Σᵉ (Bᵉ → Cᵉ) (λ hᵉ → gᵉ ~ᵉ hᵉ ∘ᵉ fᵉ)
```

ofᵉ extensionsᵉ ofᵉ `g`ᵉ alongᵉ `f`ᵉ isᵉ aᵉ proposition.ᵉ Thisᵉ propositionᵉ isᵉ equivalentᵉ
to theᵉ propositionᵉ

```text
  (aᵉ a'ᵉ : Aᵉ) → fᵉ aᵉ ＝ᵉ fᵉ a'ᵉ → gᵉ aᵉ ＝ᵉ gᵉ a'.ᵉ
```

**Proof:**ᵉ Theᵉ trickyᵉ directionᵉ isᵉ to constructᵉ anᵉ extensionᵉ ofᵉ `g`ᵉ alongᵉ `f`ᵉ
wheneverᵉ theᵉ aboveᵉ propositionᵉ holds.ᵉ Noteᵉ thatᵉ weᵉ mayᵉ composeᵉ `f`ᵉ with theᵉ
[setᵉ truncation](foundation.set-truncations.mdᵉ) ofᵉ `B`,ᵉ thisᵉ resultsᵉ in aᵉ mapᵉ

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ ↠ᵉ Bᵉ)
  (Cᵉ : Setᵉ l3ᵉ) (gᵉ : Aᵉ → type-Setᵉ Cᵉ)
  where

  equalizes-equal-values-prop-surjection-Setᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equalizes-equal-values-prop-surjection-Setᵉ =
    Π-Propᵉ Aᵉ
      ( λ aᵉ →
        Π-Propᵉ Aᵉ
          ( λ a'ᵉ →
            function-Propᵉ
              ( map-surjectionᵉ fᵉ aᵉ ＝ᵉ map-surjectionᵉ fᵉ a'ᵉ)
              ( Id-Propᵉ Cᵉ (gᵉ aᵉ) (gᵉ a'ᵉ))))

  equalizes-equal-values-surjection-Setᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  equalizes-equal-values-surjection-Setᵉ =
    type-Propᵉ equalizes-equal-values-prop-surjection-Setᵉ

  is-prop-equalizes-equal-values-surjection-Setᵉ :
    is-propᵉ equalizes-equal-values-surjection-Setᵉ
  is-prop-equalizes-equal-values-surjection-Setᵉ =
    is-prop-type-Propᵉ equalizes-equal-values-prop-surjection-Setᵉ

  equalizes-equal-values-extension-along-surjection-Setᵉ :
    extension-along-surjection-Setᵉ fᵉ Cᵉ gᵉ → equalizes-equal-values-surjection-Setᵉ
  equalizes-equal-values-extension-along-surjection-Setᵉ (hᵉ ,ᵉ qᵉ) aᵉ a'ᵉ pᵉ =
    qᵉ aᵉ ∙ᵉ (apᵉ hᵉ pᵉ ∙ᵉ invᵉ (qᵉ a'ᵉ))

  extension-equalizes-equal-values-surjection-Setᵉ :
    equalizes-equal-values-surjection-Setᵉ → extension-along-surjection-Setᵉ fᵉ Cᵉ gᵉ
  extension-equalizes-equal-values-surjection-Setᵉ Hᵉ =
    map-equivᵉ
      ( eᵉ)
      ( apply-dependent-universal-property-surjectionᵉ
        ( fᵉ)
        ( λ bᵉ → Pᵉ bᵉ ,ᵉ is-prop-Pᵉ bᵉ)
        ( λ aᵉ → (gᵉ aᵉ ,ᵉ λ (a'ᵉ ,ᵉ p'ᵉ) → Hᵉ a'ᵉ aᵉ p'ᵉ)))
    where
      Pᵉ : Bᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
      Pᵉ bᵉ =
        Σᵉ (type-Setᵉ Cᵉ) (λ cᵉ → (sᵉ : fiberᵉ (map-surjectionᵉ fᵉ) bᵉ) → gᵉ (pr1ᵉ sᵉ) ＝ᵉ cᵉ)

      eᵉ : ((bᵉ : Bᵉ) → Pᵉ bᵉ) ≃ᵉ
          Σᵉ (Bᵉ → type-Setᵉ Cᵉ) (λ hᵉ → gᵉ ~ᵉ (hᵉ ∘ᵉ map-surjectionᵉ fᵉ))
      eᵉ =
        ( equiv-totᵉ
          ( λ hᵉ →
            equiv-precomp-Πᵉ (inv-equiv-total-fiberᵉ (map-surjectionᵉ fᵉ)) _)) ∘eᵉ
        ( equiv-totᵉ (λ hᵉ → inv-equivᵉ equiv-ev-pairᵉ)) ∘eᵉ
        ( distributive-Π-Σᵉ)

      is-prop-Pᵉ : (bᵉ : Bᵉ) → is-propᵉ (Pᵉ bᵉ)
      is-prop-Pᵉ bᵉ =
        is-prop-all-elements-equalᵉ
          ( λ (pairᵉ cᵉ qᵉ) (pairᵉ c'ᵉ q'ᵉ) →
            eq-type-subtypeᵉ
              ( λ c''ᵉ →
                Π-Propᵉ
                  (fiberᵉ (map-surjectionᵉ fᵉ) bᵉ)
                  (λ sᵉ → Id-Propᵉ Cᵉ (gᵉ (pr1ᵉ sᵉ)) c''ᵉ))
              ( map-universal-property-trunc-Propᵉ
                ( Id-Propᵉ Cᵉ cᵉ c'ᵉ)
                ( λ sᵉ → invᵉ (qᵉ sᵉ) ∙ᵉ q'ᵉ sᵉ)
                ( is-surjective-map-surjectionᵉ fᵉ bᵉ)))

  equiv-equalizes-equal-values-extension-along-surjection-Setᵉ :
    extension-along-surjection-Setᵉ fᵉ Cᵉ gᵉ ≃ᵉ equalizes-equal-values-surjection-Setᵉ
  pr1ᵉ equiv-equalizes-equal-values-extension-along-surjection-Setᵉ =
    equalizes-equal-values-extension-along-surjection-Setᵉ
  pr2ᵉ equiv-equalizes-equal-values-extension-along-surjection-Setᵉ =
    is-equiv-has-converse-is-propᵉ
      ( is-prop-extension-along-surjection-Setᵉ fᵉ Cᵉ gᵉ)
      ( is-prop-equalizes-equal-values-surjection-Setᵉ)
      ( extension-equalizes-equal-values-surjection-Setᵉ)

  function-extension-equalizes-equal-values-surjection-Setᵉ :
    equalizes-equal-values-surjection-Setᵉ → Bᵉ → type-Setᵉ Cᵉ
  function-extension-equalizes-equal-values-surjection-Setᵉ =
    pr1ᵉ ∘ᵉ
    map-inv-equivᵉ equiv-equalizes-equal-values-extension-along-surjection-Setᵉ

  coherence-triangle-extension-equalizes-equal-values-surjection-Setᵉ :
    (Hᵉ : equalizes-equal-values-surjection-Setᵉ) →
    coherence-triangle-mapsᵉ
      ( gᵉ)
      ( function-extension-equalizes-equal-values-surjection-Setᵉ Hᵉ)
      ( map-surjectionᵉ fᵉ)
  coherence-triangle-extension-equalizes-equal-values-surjection-Setᵉ =
    pr2ᵉ ∘ᵉ
    map-inv-equivᵉ equiv-equalizes-equal-values-extension-along-surjection-Setᵉ
```