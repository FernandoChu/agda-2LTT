# Functoriality of function types

```agda
module foundation.functoriality-function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.postcomposition-functionsᵉ
open import foundation.unit-typeᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.embeddingsᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.precomposition-functionsᵉ
open import foundation-core.propositional-mapsᵉ
open import foundation-core.truncated-mapsᵉ
open import foundation-core.truncation-levelsᵉ
```

</details>

## Properties

### Equivalent types have equivalent function types

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  { A'ᵉ : UUᵉ l1ᵉ} {B'ᵉ : UUᵉ l2ᵉ} {Aᵉ : UUᵉ l3ᵉ} (Bᵉ : UUᵉ l4ᵉ)
  ( eᵉ : A'ᵉ ≃ᵉ Aᵉ) (fᵉ : B'ᵉ ≃ᵉ Bᵉ)
  where

  map-equiv-function-typeᵉ : (A'ᵉ → B'ᵉ) → (Aᵉ → Bᵉ)
  map-equiv-function-typeᵉ hᵉ = map-equivᵉ fᵉ ∘ᵉ (hᵉ ∘ᵉ map-inv-equivᵉ eᵉ)

  compute-map-equiv-function-typeᵉ :
    (hᵉ : A'ᵉ → B'ᵉ) (xᵉ : A'ᵉ) →
    map-equiv-function-typeᵉ hᵉ (map-equivᵉ eᵉ xᵉ) ＝ᵉ map-equivᵉ fᵉ (hᵉ xᵉ)
  compute-map-equiv-function-typeᵉ hᵉ xᵉ =
    apᵉ (map-equivᵉ fᵉ ∘ᵉ hᵉ) (is-retraction-map-inv-equivᵉ eᵉ xᵉ)

  is-equiv-map-equiv-function-typeᵉ : is-equivᵉ map-equiv-function-typeᵉ
  is-equiv-map-equiv-function-typeᵉ =
    is-equiv-compᵉ
      ( precompᵉ (map-equivᵉ (inv-equivᵉ eᵉ)) Bᵉ)
      ( postcompᵉ A'ᵉ (map-equivᵉ fᵉ))
      ( is-equiv-postcomp-equivᵉ fᵉ A'ᵉ)
      ( is-equiv-precomp-equivᵉ (inv-equivᵉ eᵉ) Bᵉ)

  equiv-function-typeᵉ : (A'ᵉ → B'ᵉ) ≃ᵉ (Aᵉ → Bᵉ)
  pr1ᵉ equiv-function-typeᵉ = map-equiv-function-typeᵉ
  pr2ᵉ equiv-function-typeᵉ = is-equiv-map-equiv-function-typeᵉ
```

### A map is truncated iff postcomposition by it is truncated

```agda
module _
  {l1ᵉ l2ᵉ : Level} (kᵉ : 𝕋ᵉ) {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  is-trunc-map-postcomp-is-trunc-mapᵉ :
    is-trunc-mapᵉ kᵉ fᵉ →
    {l3ᵉ : Level} (Aᵉ : UUᵉ l3ᵉ) → is-trunc-mapᵉ kᵉ (postcompᵉ Aᵉ fᵉ)
  is-trunc-map-postcomp-is-trunc-mapᵉ is-trunc-fᵉ Aᵉ =
    is-trunc-map-map-Π-is-trunc-map'ᵉ kᵉ
      ( terminal-mapᵉ Aᵉ)
      ( pointᵉ fᵉ)
      ( pointᵉ is-trunc-fᵉ)

  is-trunc-map-is-trunc-map-postcompᵉ :
    ({l3ᵉ : Level} (Aᵉ : UUᵉ l3ᵉ) → is-trunc-mapᵉ kᵉ (postcompᵉ Aᵉ fᵉ)) →
    is-trunc-mapᵉ kᵉ fᵉ
  is-trunc-map-is-trunc-map-postcompᵉ is-trunc-postcomp-fᵉ =
    is-trunc-map-is-trunc-map-map-Π'ᵉ kᵉ
      ( pointᵉ fᵉ)
      ( λ {lᵉ} {Jᵉ} αᵉ → is-trunc-postcomp-fᵉ {lᵉ} Jᵉ)
      ( starᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ → Yᵉ)
  where

  is-emb-postcomp-is-embᵉ :
    is-embᵉ fᵉ →
    {l3ᵉ : Level} (Aᵉ : UUᵉ l3ᵉ) → is-embᵉ (postcompᵉ Aᵉ fᵉ)
  is-emb-postcomp-is-embᵉ is-emb-fᵉ Aᵉ =
    is-emb-is-prop-mapᵉ
      ( is-trunc-map-postcomp-is-trunc-mapᵉ neg-one-𝕋ᵉ fᵉ
        ( is-prop-map-is-embᵉ is-emb-fᵉ)
        ( Aᵉ))

  is-emb-is-emb-postcompᵉ :
    ({l3ᵉ : Level} (Aᵉ : UUᵉ l3ᵉ) → is-embᵉ (postcompᵉ Aᵉ fᵉ)) →
    is-embᵉ fᵉ
  is-emb-is-emb-postcompᵉ is-emb-postcomp-fᵉ =
    is-emb-is-prop-mapᵉ
      ( is-trunc-map-is-trunc-map-postcompᵉ neg-one-𝕋ᵉ fᵉ
        ( is-prop-map-is-embᵉ ∘ᵉ is-emb-postcomp-fᵉ))

emb-postcompᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (fᵉ : Xᵉ ↪ᵉ Yᵉ) (Aᵉ : UUᵉ l3ᵉ) →
  (Aᵉ → Xᵉ) ↪ᵉ (Aᵉ → Yᵉ)
pr1ᵉ (emb-postcompᵉ fᵉ Aᵉ) = postcompᵉ Aᵉ (map-embᵉ fᵉ)
pr2ᵉ (emb-postcompᵉ fᵉ Aᵉ) = is-emb-postcomp-is-embᵉ (map-embᵉ fᵉ) (is-emb-map-embᵉ fᵉ) Aᵉ
```

## See also

-ᵉ Functorialᵉ propertiesᵉ ofᵉ dependentᵉ functionᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).ᵉ
-ᵉ Arithmeticalᵉ lawsᵉ involvingᵉ dependentᵉ functionᵉ typesᵉ areᵉ recordedᵉ in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).ᵉ
-ᵉ Equalityᵉ proofsᵉ in dependentᵉ functionᵉ typesᵉ areᵉ characterizedᵉ in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).ᵉ