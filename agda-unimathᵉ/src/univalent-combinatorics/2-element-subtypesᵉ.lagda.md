# `2`-element subtypes

```agda
module univalent-combinatorics.2-element-subtypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphismsᵉ
open import foundation.contractible-typesᵉ
open import foundation.coproduct-typesᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.embeddingsᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-coproduct-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.logical-equivalencesᵉ
open import foundation.mere-equivalencesᵉ
open import foundation.negated-equalityᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.subtypesᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.type-arithmetic-coproduct-typesᵉ
open import foundation.unit-typeᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.2-element-typesᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ 2-elementᵉ subtypeᵉ ofᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ subtypeᵉ `P`ᵉ ofᵉ `A`ᵉ ofᵉ whichᵉ itsᵉ
underlyingᵉ typeᵉ `Σᵉ Aᵉ P`ᵉ hasᵉ cardinalityᵉ 2.ᵉ Suchᵉ aᵉ subtypeᵉ isᵉ saidᵉ to beᵉ
decidableᵉ ifᵉ theᵉ propositionᵉ `Pᵉ x`ᵉ isᵉ decidableᵉ forᵉ everyᵉ `xᵉ : A`.ᵉ

## Definitions

### The type of 2-element subtypes of a type

```agda
2-Element-Subtypeᵉ : {l1ᵉ : Level} (l2ᵉ : Level) → UUᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
2-Element-Subtypeᵉ l2ᵉ Xᵉ =
  Σᵉ (subtypeᵉ l2ᵉ Xᵉ) (λ Pᵉ → has-two-elementsᵉ (type-subtypeᵉ Pᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : 2-Element-Subtypeᵉ l2ᵉ Xᵉ)
  where

  subtype-2-Element-Subtypeᵉ : subtypeᵉ l2ᵉ Xᵉ
  subtype-2-Element-Subtypeᵉ = pr1ᵉ Pᵉ

  type-prop-2-Element-Subtypeᵉ : Xᵉ → UUᵉ l2ᵉ
  type-prop-2-Element-Subtypeᵉ xᵉ = type-Propᵉ (subtype-2-Element-Subtypeᵉ xᵉ)

  is-prop-type-prop-2-Element-Subtypeᵉ :
    (xᵉ : Xᵉ) → is-propᵉ (type-prop-2-Element-Subtypeᵉ xᵉ)
  is-prop-type-prop-2-Element-Subtypeᵉ xᵉ =
    is-prop-type-Propᵉ (subtype-2-Element-Subtypeᵉ xᵉ)

  type-2-Element-Subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ)
  type-2-Element-Subtypeᵉ = type-subtypeᵉ subtype-2-Element-Subtypeᵉ

  inclusion-2-Element-Subtypeᵉ : type-2-Element-Subtypeᵉ → Xᵉ
  inclusion-2-Element-Subtypeᵉ = inclusion-subtypeᵉ subtype-2-Element-Subtypeᵉ

  is-emb-inclusion-2-Element-Subtypeᵉ : is-embᵉ inclusion-2-Element-Subtypeᵉ
  is-emb-inclusion-2-Element-Subtypeᵉ =
    is-emb-inclusion-subtypeᵉ subtype-2-Element-Subtypeᵉ

  is-injective-inclusion-2-Element-Subtypeᵉ :
    is-injectiveᵉ inclusion-2-Element-Subtypeᵉ
  is-injective-inclusion-2-Element-Subtypeᵉ =
    is-injective-inclusion-subtypeᵉ subtype-2-Element-Subtypeᵉ

  has-two-elements-type-2-Element-Subtypeᵉ :
    has-two-elementsᵉ type-2-Element-Subtypeᵉ
  has-two-elements-type-2-Element-Subtypeᵉ = pr2ᵉ Pᵉ

  2-element-type-2-Element-Subtypeᵉ : 2-Element-Typeᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ 2-element-type-2-Element-Subtypeᵉ = type-2-Element-Subtypeᵉ
  pr2ᵉ 2-element-type-2-Element-Subtypeᵉ = has-two-elements-type-2-Element-Subtypeᵉ

  is-inhabited-type-2-Element-Subtypeᵉ : type-trunc-Propᵉ type-2-Element-Subtypeᵉ
  is-inhabited-type-2-Element-Subtypeᵉ =
    is-inhabited-2-Element-Typeᵉ 2-element-type-2-Element-Subtypeᵉ
```

### The standard 2-element subtype of a pair of distinct elements in a set

```agda
module _
  {lᵉ : Level} (Xᵉ : Setᵉ lᵉ) {xᵉ yᵉ : type-Setᵉ Xᵉ} (npᵉ : xᵉ ≠ᵉ yᵉ)
  where

  type-prop-standard-2-Element-Subtypeᵉ : type-Setᵉ Xᵉ → UUᵉ lᵉ
  type-prop-standard-2-Element-Subtypeᵉ zᵉ = (xᵉ ＝ᵉ zᵉ) +ᵉ (yᵉ ＝ᵉ zᵉ)

  is-prop-type-prop-standard-2-Element-Subtypeᵉ :
    (zᵉ : type-Setᵉ Xᵉ) → is-propᵉ (type-prop-standard-2-Element-Subtypeᵉ zᵉ)
  is-prop-type-prop-standard-2-Element-Subtypeᵉ zᵉ =
    is-prop-coproductᵉ
      ( λ pᵉ qᵉ → npᵉ (pᵉ ∙ᵉ invᵉ qᵉ))
      ( is-set-type-Setᵉ Xᵉ xᵉ zᵉ)
      ( is-set-type-Setᵉ Xᵉ yᵉ zᵉ)

  subtype-standard-2-Element-Subtypeᵉ : subtypeᵉ lᵉ (type-Setᵉ Xᵉ)
  pr1ᵉ (subtype-standard-2-Element-Subtypeᵉ zᵉ) =
    type-prop-standard-2-Element-Subtypeᵉ zᵉ
  pr2ᵉ (subtype-standard-2-Element-Subtypeᵉ zᵉ) =
    is-prop-type-prop-standard-2-Element-Subtypeᵉ zᵉ

  type-standard-2-Element-Subtypeᵉ : UUᵉ lᵉ
  type-standard-2-Element-Subtypeᵉ =
    type-subtypeᵉ subtype-standard-2-Element-Subtypeᵉ

  equiv-type-standard-2-Element-Subtypeᵉ :
    Finᵉ 2 ≃ᵉ type-standard-2-Element-Subtypeᵉ
  equiv-type-standard-2-Element-Subtypeᵉ =
    ( inv-equivᵉ
      ( left-distributive-Σ-coproductᵉ (type-Setᵉ Xᵉ) (Idᵉ xᵉ) (Idᵉ yᵉ))) ∘eᵉ
    ( equiv-coproductᵉ
      ( equiv-is-contrᵉ
        ( is-contr-Fin-one-ℕᵉ)
        ( is-torsorial-Idᵉ xᵉ))
      ( equiv-is-contrᵉ
        ( is-contr-unitᵉ)
        ( is-torsorial-Idᵉ yᵉ)))

  has-two-elements-type-standard-2-Element-Subtypeᵉ :
    has-two-elementsᵉ type-standard-2-Element-Subtypeᵉ
  has-two-elements-type-standard-2-Element-Subtypeᵉ =
    unit-trunc-Propᵉ equiv-type-standard-2-Element-Subtypeᵉ
```

### Morphisms of 2-element-subtypes

Aᵉ moprhismᵉ ofᵉ 2-elementᵉ subtypesᵉ `P`ᵉ andᵉ `Q`ᵉ isᵉ justᵉ aᵉ familyᵉ ofᵉ mapsᵉ
`Pᵉ xᵉ → Qᵉ x`.ᵉ

```agda
{-ᵉ
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ}
  (Pᵉ : 2-Element-Subtypeᵉ l2ᵉ Xᵉ) (Qᵉ : 2-Element-Subtypeᵉ l3ᵉ Xᵉ)
  where

  hom-2-Element-Subtypeᵉ : UUᵉ (l1ᵉ ⊔ l2ᵉ ⊔ l3ᵉ)
  hom-2-Element-Subtypeᵉ =
    (xᵉ : Xᵉ) → type-prop-2-Element-Subtypeᵉ Pᵉ xᵉ → type-prop-2-Element-Subtypeᵉ Qᵉ xᵉ

  map-hom-2-Element-Subtypeᵉ :
    hom-2-Element-Subtypeᵉ → type-2-Element-Subtypeᵉ Pᵉ → type-2-Element-Subtypeᵉ Qᵉ
  map-hom-2-Element-Subtypeᵉ fᵉ = totᵉ fᵉ

  is-emb-map-hom-2-Element-Subtypeᵉ :
    (fᵉ : hom-2-Element-Subtypeᵉ) → is-embᵉ (map-hom-2-Element-Subtypeᵉ fᵉ)
  is-emb-map-hom-2-Element-Subtypeᵉ fᵉ =
    is-emb-totᵉ
      ( λ xᵉ →
        is-emb-is-propᵉ
          ( is-prop-type-prop-2-Element-Subtypeᵉ Pᵉ xᵉ)
          ( is-prop-type-prop-2-Element-Subtypeᵉ Qᵉ xᵉ))

  is-surjective-map-hom-2-Element-Subtypeᵉ :
    (fᵉ : hom-2-Element-Subtypeᵉ) → is-surjectiveᵉ (map-hom-2-Element-Subtypeᵉ fᵉ)
  is-surjective-map-hom-2-Element-Subtypeᵉ fᵉ (pairᵉ xᵉ qᵉ) = {!ᵉ type-subtypeᵉ (Pᵉ ∘ᵉ map-inv-equivᵉ eᵉ) !ᵉ}

  is-equiv-map-hom-2-Element-Subtypeᵉ :
    (fᵉ : hom-2-Element-Subtypeᵉ) → is-equivᵉ (map-hom-2-Element-Subtypeᵉ fᵉ)
  is-equiv-map-hom-2-Element-Subtypeᵉ fᵉ = {!!ᵉ}
-ᵉ}
```

### Swapping the elements in a 2-element subtype

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} (Pᵉ : 2-Element-Subtypeᵉ l2ᵉ Xᵉ)
  where

  swap-2-Element-Subtypeᵉ : Autᵉ (type-2-Element-Subtypeᵉ Pᵉ)
  swap-2-Element-Subtypeᵉ =
    swap-2-Element-Typeᵉ (2-element-type-2-Element-Subtypeᵉ Pᵉ)

  map-swap-2-Element-Subtypeᵉ :
    type-2-Element-Subtypeᵉ Pᵉ → type-2-Element-Subtypeᵉ Pᵉ
  map-swap-2-Element-Subtypeᵉ =
    map-swap-2-Element-Typeᵉ (2-element-type-2-Element-Subtypeᵉ Pᵉ)

  compute-swap-2-Element-Subtypeᵉ :
    (xᵉ yᵉ : type-2-Element-Subtypeᵉ Pᵉ) → xᵉ ≠ᵉ yᵉ →
    map-swap-2-Element-Subtypeᵉ xᵉ ＝ᵉ yᵉ
  compute-swap-2-Element-Subtypeᵉ =
    compute-swap-2-Element-Typeᵉ (2-element-type-2-Element-Subtypeᵉ Pᵉ)
```

### 2-element subtypes are closed under precomposition with an equivalence

```agda
precomp-equiv-2-Element-Subtypeᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} → Xᵉ ≃ᵉ Yᵉ →
    2-Element-Subtypeᵉ l3ᵉ Xᵉ → 2-Element-Subtypeᵉ l3ᵉ Yᵉ
pr1ᵉ (precomp-equiv-2-Element-Subtypeᵉ eᵉ (pairᵉ Pᵉ Hᵉ)) =
  Pᵉ ∘ᵉ (map-inv-equivᵉ eᵉ)
pr2ᵉ (precomp-equiv-2-Element-Subtypeᵉ eᵉ (pairᵉ Pᵉ Hᵉ)) =
  transitive-mere-equivᵉ _ _ _
    ( unit-trunc-Propᵉ
      ( equiv-subtype-equivᵉ
        ( eᵉ)
        ( Pᵉ)
        ( Pᵉ ∘ᵉ (map-inv-equivᵉ eᵉ))
        ( λ xᵉ →
          iff-equivᵉ
            ( trᵉ
              ( λ gᵉ → (type-Propᵉ (Pᵉ xᵉ)) ≃ᵉ (type-Propᵉ (Pᵉ (map-equivᵉ gᵉ xᵉ))))
              ( invᵉ (left-inverse-law-equivᵉ eᵉ))
              ( id-equivᵉ)))))
    ( Hᵉ)

{-ᵉ
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-injective-map-Fin-two-ℕᵉ :
    (fᵉ : Finᵉ 2 → Aᵉ) → fᵉ zero-Finᵉ ≠ᵉ fᵉ one-Finᵉ → is-injectiveᵉ fᵉ
  is-injective-map-Fin-two-ℕᵉ fᵉ Hᵉ {inlᵉ (inrᵉ starᵉ)} {inlᵉ (inrᵉ starᵉ)} pᵉ = reflᵉ
  is-injective-map-Fin-two-ℕᵉ fᵉ Hᵉ {inlᵉ (inrᵉ starᵉ)} {inrᵉ starᵉ} pᵉ = ex-falsoᵉ (Hᵉ pᵉ)
  is-injective-map-Fin-two-ℕᵉ fᵉ Hᵉ {inrᵉ starᵉ} {inlᵉ (inrᵉ starᵉ)} pᵉ =
    ex-falsoᵉ (Hᵉ (invᵉ pᵉ))
  is-injective-map-Fin-two-ℕᵉ fᵉ Hᵉ {inrᵉ starᵉ} {inrᵉ starᵉ} pᵉ = reflᵉ

  is-injective-element-unordered-pairᵉ :
    (pᵉ : unordered-pairᵉ Aᵉ) →
    ¬ᵉ ( (xᵉ yᵉ : type-unordered-pairᵉ pᵉ) →
        Idᵉ (element-unordered-pairᵉ pᵉ xᵉ) (element-unordered-pairᵉ pᵉ yᵉ)) →
    is-injectiveᵉ (element-unordered-pairᵉ pᵉ)
  is-injective-element-unordered-pairᵉ (pairᵉ Xᵉ fᵉ) Hᵉ {xᵉ} {yᵉ} pᵉ =
    apply-universal-property-trunc-Propᵉ
      ( has-two-elements-type-unordered-pairᵉ (pairᵉ Xᵉ fᵉ))
      ( Id-Propᵉ (set-UU-Finᵉ Xᵉ) xᵉ yᵉ)
      ( λ hᵉ → {!!ᵉ})
    where
    first-elementᵉ : (Finᵉ 2 ≃ᵉ (type-2-Element-Typeᵉ Xᵉ)) →
      Σᵉ ( type-2-Element-Typeᵉ Xᵉ)
        ( λ xᵉ → ¬ᵉ ((yᵉ : type-2-Element-Typeᵉ Xᵉ) → Idᵉ (fᵉ xᵉ) (fᵉ yᵉ)))
    first-elementᵉ hᵉ =
      exists-not-not-for-all-countᵉ (λ zᵉ → (wᵉ : type-2-Element-Typeᵉ Xᵉ) →
      Idᵉ (fᵉ zᵉ) (fᵉ wᵉ)) (λ zᵉ → {!!ᵉ})
        {!!ᵉ} {!!ᵉ}
    two-elements-different-imageᵉ :
      Σᵉ ( type-2-Element-Typeᵉ Xᵉ)
        ( λ xᵉ → Σᵉ (type-2-Element-Typeᵉ Xᵉ) (λ yᵉ → fᵉ xᵉ ≠ᵉ fᵉ yᵉ))
    two-elements-different-imageᵉ = {!!ᵉ}
-ᵉ}
```