# The universal multiset

```agda
module trees.universal-multisetᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.raising-universe-levelsᵉ
open import foundation.small-typesᵉ
open import foundation.small-universesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.universe-levelsᵉ

open import trees.functoriality-w-typesᵉ
open import trees.multisetsᵉ
open import trees.small-multisetsᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Theᵉ **universalᵉ multiset**ᵉ ofᵉ universeᵉ levelᵉ `l`ᵉ isᵉ theᵉ multisetᵉ ofᵉ levelᵉ
`lsucᵉ l`ᵉ builtᵉ outᵉ ofᵉ `𝕍ᵉ l`ᵉ andᵉ resizingsᵉ ofᵉ theᵉ multisetsᵉ itᵉ containsᵉ

## Definition

```agda
universal-multiset-𝕍ᵉ : (lᵉ : Level) → 𝕍ᵉ (lsuc lᵉ)
universal-multiset-𝕍ᵉ lᵉ =
  tree-𝕎ᵉ
    ( 𝕍ᵉ lᵉ)
    ( λ Xᵉ → resize-𝕍ᵉ Xᵉ (is-small-multiset-𝕍ᵉ is-small-lsucᵉ Xᵉ))
```

## Properties

### If `UU l1` is `UU l`-small, then the universal multiset of level `l1` is `UU l`-small

```agda
is-small-universal-multiset-𝕍ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} →
  is-small-universeᵉ lᵉ l1ᵉ → is-small-𝕍ᵉ lᵉ (universal-multiset-𝕍ᵉ l1ᵉ)
is-small-universal-multiset-𝕍ᵉ lᵉ {l1ᵉ} (pairᵉ (pairᵉ Uᵉ eᵉ) Hᵉ) =
  pairᵉ
    ( pairᵉ
      ( 𝕎ᵉ Uᵉ (λ xᵉ → pr1ᵉ (Hᵉ (map-inv-equivᵉ eᵉ xᵉ))))
      ( equiv-𝕎ᵉ
        ( λ uᵉ → type-is-smallᵉ (Hᵉ (map-inv-equivᵉ eᵉ uᵉ)))
        ( eᵉ)
        ( λ Xᵉ →
          trᵉ
            ( λ tᵉ → Xᵉ ≃ᵉ pr1ᵉ (Hᵉ tᵉ))
            ( invᵉ (is-retraction-map-inv-equivᵉ eᵉ Xᵉ))
            ( pr2ᵉ (Hᵉ Xᵉ)))))
    ( fᵉ)
    where
    fᵉ :
      (Xᵉ : 𝕍ᵉ l1ᵉ) →
      is-small-𝕍ᵉ lᵉ (resize-𝕍ᵉ Xᵉ (is-small-multiset-𝕍ᵉ is-small-lsucᵉ Xᵉ))
    fᵉ (tree-𝕎ᵉ Aᵉ αᵉ) =
      pairᵉ
        ( pairᵉ
          ( type-is-smallᵉ (Hᵉ Aᵉ))
          ( equiv-is-smallᵉ (Hᵉ Aᵉ) ∘eᵉ inv-equivᵉ (compute-raiseᵉ (lsuc l1ᵉ) Aᵉ)))
        ( λ xᵉ → fᵉ (αᵉ (map-inv-raiseᵉ xᵉ)))
```