# Small multisets

```agda
module trees.small-multisetsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.empty-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.function-typesᵉ
open import foundation.functoriality-dependent-pair-typesᵉ
open import foundation.homotopiesᵉ
open import foundation.identity-typesᵉ
open import foundation.propositionsᵉ
open import foundation.small-typesᵉ
open import foundation.subtypesᵉ
open import foundation.transport-along-identificationsᵉ
open import foundation.univalenceᵉ
open import foundation.universe-levelsᵉ

open import trees.multisetsᵉ
open import trees.w-typesᵉ
```

</details>

## Idea

Aᵉ multisetᵉ `Xᵉ :=ᵉ tree-𝕎ᵉ Aᵉ α`ᵉ isᵉ saidᵉ to beᵉ **small**ᵉ with respectᵉ to aᵉ universeᵉ
`UUᵉ l`ᵉ ifᵉ itsᵉ symbolᵉ `A`ᵉ isᵉ aᵉ smallᵉ typeᵉ with respectᵉ to `UUᵉ l`,ᵉ andᵉ ifᵉ eachᵉ
`αᵉ x`ᵉ isᵉ aᵉ smallᵉ multisetᵉ with respectᵉ to `UUᵉ l`.ᵉ

## Definition

### Small multisets

```agda
is-small-𝕍-Propᵉ : (lᵉ : Level) {l1ᵉ : Level} → 𝕍ᵉ l1ᵉ → Propᵉ (l1ᵉ ⊔ lsuc lᵉ)
is-small-𝕍-Propᵉ lᵉ (tree-𝕎ᵉ Aᵉ αᵉ) =
  product-Propᵉ (is-small-Propᵉ lᵉ Aᵉ) (Π-Propᵉ Aᵉ (λ xᵉ → is-small-𝕍-Propᵉ lᵉ (αᵉ xᵉ)))

is-small-𝕍ᵉ : (lᵉ : Level) {l1ᵉ : Level} → 𝕍ᵉ l1ᵉ → UUᵉ (l1ᵉ ⊔ lsuc lᵉ)
is-small-𝕍ᵉ lᵉ Xᵉ = type-Propᵉ (is-small-𝕍-Propᵉ lᵉ Xᵉ)

is-prop-is-small-𝕍ᵉ : {lᵉ l1ᵉ : Level} (Xᵉ : 𝕍ᵉ l1ᵉ) → is-propᵉ (is-small-𝕍ᵉ lᵉ Xᵉ)
is-prop-is-small-𝕍ᵉ {lᵉ} Xᵉ = is-prop-type-Propᵉ (is-small-𝕍-Propᵉ lᵉ Xᵉ)
```

### Resizing small multisets

```agda
resize-𝕍ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝕍ᵉ l1ᵉ) → is-small-𝕍ᵉ l2ᵉ Xᵉ → 𝕍ᵉ l2ᵉ
resize-𝕍ᵉ (tree-𝕎ᵉ Aᵉ αᵉ) (pairᵉ (pairᵉ A'ᵉ eᵉ) H2ᵉ) =
  tree-𝕎ᵉ A'ᵉ
    ( λ x'ᵉ → resize-𝕍ᵉ (αᵉ (map-inv-equivᵉ eᵉ x'ᵉ)) (H2ᵉ (map-inv-equivᵉ eᵉ x'ᵉ)))
```

## Properties

### The comprehension of a small multiset equipped with a small predicate is small

```agda
is-small-comprehension-𝕍ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} {Xᵉ : 𝕍ᵉ l1ᵉ} {Pᵉ : shape-𝕎ᵉ Xᵉ → UUᵉ l1ᵉ} →
  is-small-𝕍ᵉ lᵉ Xᵉ → ((xᵉ : shape-𝕎ᵉ Xᵉ) → is-smallᵉ lᵉ (Pᵉ xᵉ)) →
  is-small-𝕍ᵉ lᵉ (comprehension-𝕍ᵉ Xᵉ Pᵉ)
is-small-comprehension-𝕍ᵉ lᵉ {l1ᵉ} {tree-𝕎ᵉ Aᵉ αᵉ} {Pᵉ} (pairᵉ (pairᵉ Xᵉ eᵉ) Hᵉ) Kᵉ =
  pairᵉ
    ( is-small-Σᵉ (pairᵉ Xᵉ eᵉ) Kᵉ)
    ( λ tᵉ → Hᵉ (pr1ᵉ tᵉ))
```

### The identity type between small multisets is small

```agda
is-small-eq-𝕍ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} {Xᵉ Yᵉ : 𝕍ᵉ l1ᵉ} →
  is-small-𝕍ᵉ lᵉ Xᵉ → is-small-𝕍ᵉ lᵉ Yᵉ → is-smallᵉ lᵉ (Xᵉ ＝ᵉ Yᵉ)
is-small-eq-𝕍ᵉ lᵉ
  {l1ᵉ} {tree-𝕎ᵉ Aᵉ αᵉ} {tree-𝕎ᵉ Bᵉ βᵉ} (pairᵉ (pairᵉ Xᵉ eᵉ) Hᵉ) (pairᵉ (pairᵉ Yᵉ fᵉ) Kᵉ) =
  is-small-equivᵉ
    ( Eq-𝕎ᵉ (tree-𝕎ᵉ Aᵉ αᵉ) (tree-𝕎ᵉ Bᵉ βᵉ))
    ( equiv-Eq-𝕎-eqᵉ (tree-𝕎ᵉ Aᵉ αᵉ) (tree-𝕎ᵉ Bᵉ βᵉ))
    ( is-small-Σᵉ
      ( is-small-equivᵉ
        ( Aᵉ ≃ᵉ Bᵉ)
        ( equiv-univalenceᵉ)
        ( pairᵉ
          ( Xᵉ ≃ᵉ Yᵉ)
          ( equiv-precomp-equivᵉ (inv-equivᵉ eᵉ) Yᵉ ∘eᵉ equiv-postcomp-equivᵉ fᵉ Aᵉ)))
      ( σᵉ))
  where
  σᵉ : (xᵉ : Aᵉ ＝ᵉ Bᵉ) → is-smallᵉ lᵉ ((zᵉ : Aᵉ) → Eq-𝕎ᵉ (αᵉ zᵉ) (βᵉ (trᵉ idᵉ xᵉ zᵉ)))
  σᵉ reflᵉ =
    is-small-Πᵉ
      ( pairᵉ Xᵉ eᵉ)
      ( λ xᵉ →
        is-small-equivᵉ
          ( αᵉ xᵉ ＝ᵉ βᵉ xᵉ)
          ( inv-equivᵉ (equiv-Eq-𝕎-eqᵉ (αᵉ xᵉ) (βᵉ xᵉ)))
          ( is-small-eq-𝕍ᵉ lᵉ (Hᵉ xᵉ) (Kᵉ xᵉ)))
```

### The elementhood relation between small multisets is small

```agda
is-small-∈-𝕍ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} {Xᵉ Yᵉ : 𝕍ᵉ l1ᵉ} →
  is-small-𝕍ᵉ lᵉ Xᵉ → is-small-𝕍ᵉ lᵉ Yᵉ → is-smallᵉ lᵉ (Xᵉ ∈-𝕍ᵉ Yᵉ)
is-small-∈-𝕍ᵉ lᵉ {l1ᵉ} {tree-𝕎ᵉ Aᵉ αᵉ} {tree-𝕎ᵉ Bᵉ βᵉ} Hᵉ (pairᵉ (pairᵉ Yᵉ fᵉ) Kᵉ) =
  is-small-Σᵉ
    ( pairᵉ Yᵉ fᵉ)
    ( λ bᵉ → is-small-eq-𝕍ᵉ lᵉ (Kᵉ bᵉ) Hᵉ)

is-small-∉-𝕍ᵉ :
  (lᵉ : Level) {l1ᵉ : Level} {Xᵉ Yᵉ : 𝕍ᵉ l1ᵉ} →
  is-small-𝕍ᵉ lᵉ Xᵉ → is-small-𝕍ᵉ lᵉ Yᵉ → is-smallᵉ lᵉ (Xᵉ ∉-𝕍ᵉ Yᵉ)
is-small-∉-𝕍ᵉ lᵉ {l1ᵉ} {Xᵉ} {Yᵉ} Hᵉ Kᵉ =
  is-small-Πᵉ
    ( is-small-∈-𝕍ᵉ lᵉ {l1ᵉ} {Xᵉ} {Yᵉ} Hᵉ Kᵉ)
    ( λ xᵉ → pairᵉ (raise-emptyᵉ lᵉ) (compute-raise-emptyᵉ lᵉ))
```

### The resizing of a small multiset is small

```agda
is-small-resize-𝕍ᵉ :
  {l1ᵉ l2ᵉ : Level} (Xᵉ : 𝕍ᵉ l1ᵉ) (Hᵉ : is-small-𝕍ᵉ l2ᵉ Xᵉ) →
  is-small-𝕍ᵉ l1ᵉ (resize-𝕍ᵉ Xᵉ Hᵉ)
is-small-resize-𝕍ᵉ (tree-𝕎ᵉ Aᵉ αᵉ) (pairᵉ (pairᵉ A'ᵉ eᵉ) H2ᵉ) =
  pairᵉ
    ( pairᵉ Aᵉ (inv-equivᵉ eᵉ))
    ( λ a'ᵉ →
      is-small-resize-𝕍ᵉ
        ( αᵉ (map-inv-equivᵉ eᵉ a'ᵉ))
        ( H2ᵉ (map-inv-equivᵉ eᵉ a'ᵉ)))
```

### The type of `UU l2`-small multisets in `𝕍 l1` is equivalent to the type of `UU l1`-small multisets in `𝕍 l2`

```agda
resize-𝕍'ᵉ :
  {l1ᵉ l2ᵉ : Level} →
  Σᵉ (𝕍ᵉ l1ᵉ) (is-small-𝕍ᵉ l2ᵉ) → Σᵉ (𝕍ᵉ l2ᵉ) (is-small-𝕍ᵉ l1ᵉ)
resize-𝕍'ᵉ (pairᵉ Xᵉ Hᵉ) = pairᵉ (resize-𝕍ᵉ Xᵉ Hᵉ) (is-small-resize-𝕍ᵉ Xᵉ Hᵉ)

abstract
  resize-resize-𝕍ᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ : 𝕍ᵉ l1ᵉ} (Hᵉ : is-small-𝕍ᵉ l2ᵉ xᵉ) →
    resize-𝕍ᵉ (resize-𝕍ᵉ xᵉ Hᵉ) (is-small-resize-𝕍ᵉ xᵉ Hᵉ) ＝ᵉ xᵉ
  resize-resize-𝕍ᵉ {xᵉ = tree-𝕎ᵉ Aᵉ αᵉ} (pairᵉ (pairᵉ A'ᵉ eᵉ) Hᵉ) =
    eq-Eq-𝕎ᵉ
      ( resize-𝕍ᵉ
        ( resize-𝕍ᵉ (tree-𝕎ᵉ Aᵉ αᵉ) (pairᵉ (pairᵉ A'ᵉ eᵉ) Hᵉ))
        ( is-small-resize-𝕍ᵉ (tree-𝕎ᵉ Aᵉ αᵉ) (pairᵉ (pairᵉ A'ᵉ eᵉ) Hᵉ)))
      ( tree-𝕎ᵉ Aᵉ αᵉ)
      ( pairᵉ
        ( reflᵉ)
        ( λ zᵉ →
          Eq-𝕎-eqᵉ
            ( resize-𝕍ᵉ
              ( resize-𝕍ᵉ
                ( αᵉ (map-inv-equivᵉ eᵉ (map-inv-equivᵉ (inv-equivᵉ eᵉ) zᵉ)))
                ( Hᵉ (map-inv-equivᵉ eᵉ (map-inv-equivᵉ (inv-equivᵉ eᵉ) zᵉ))))
              ( is-small-resize-𝕍ᵉ
                ( αᵉ (map-inv-equivᵉ eᵉ (map-inv-equivᵉ (inv-equivᵉ eᵉ) zᵉ)))
                ( Hᵉ (map-inv-equivᵉ eᵉ (map-inv-equivᵉ (inv-equivᵉ eᵉ) zᵉ)))))
            ( αᵉ zᵉ)
            ( ( apᵉ
                ( λ tᵉ →
                  resize-𝕍ᵉ
                    ( resize-𝕍ᵉ (αᵉ tᵉ) (Hᵉ tᵉ))
                    ( is-small-resize-𝕍ᵉ (αᵉ tᵉ) (Hᵉ tᵉ)))
                ( is-retraction-map-inv-equivᵉ eᵉ zᵉ)) ∙ᵉ
              ( resize-resize-𝕍ᵉ (Hᵉ zᵉ)))))

abstract
  resize-resize-𝕍'ᵉ :
    {l1ᵉ l2ᵉ : Level} → (resize-𝕍'ᵉ {l2ᵉ} {l1ᵉ} ∘ᵉ resize-𝕍'ᵉ {l1ᵉ} {l2ᵉ}) ~ᵉ idᵉ
  resize-resize-𝕍'ᵉ {l1ᵉ} {l2ᵉ} (pairᵉ Xᵉ Hᵉ) =
    eq-type-subtypeᵉ
      ( is-small-𝕍-Propᵉ l2ᵉ)
      ( resize-resize-𝕍ᵉ Hᵉ)

is-equiv-resize-𝕍'ᵉ :
  {l1ᵉ l2ᵉ : Level} → is-equivᵉ (resize-𝕍'ᵉ {l1ᵉ} {l2ᵉ})
is-equiv-resize-𝕍'ᵉ {l1ᵉ} {l2ᵉ} =
  is-equiv-is-invertibleᵉ
    ( resize-𝕍'ᵉ {l2ᵉ} {l1ᵉ})
    ( resize-resize-𝕍'ᵉ)
    ( resize-resize-𝕍'ᵉ)

equiv-resize-𝕍'ᵉ :
  {l1ᵉ l2ᵉ : Level} → Σᵉ (𝕍ᵉ l1ᵉ) (is-small-𝕍ᵉ l2ᵉ) ≃ᵉ Σᵉ (𝕍ᵉ l2ᵉ) (is-small-𝕍ᵉ l1ᵉ)
equiv-resize-𝕍'ᵉ {l1ᵉ} {l2ᵉ} = pairᵉ resize-𝕍'ᵉ is-equiv-resize-𝕍'ᵉ
```

Theᵉ resizingᵉ operationᵉ onᵉ smallᵉ multisetsᵉ isᵉ anᵉ embeddingᵉ

```agda
eq-resize-𝕍ᵉ :
  {l1ᵉ l2ᵉ : Level} {xᵉ yᵉ : 𝕍ᵉ l1ᵉ} (Hᵉ : is-small-𝕍ᵉ l2ᵉ xᵉ) (Kᵉ : is-small-𝕍ᵉ l2ᵉ yᵉ) →
  (xᵉ ＝ᵉ yᵉ) ≃ᵉ (resize-𝕍ᵉ xᵉ Hᵉ ＝ᵉ resize-𝕍ᵉ yᵉ Kᵉ)
eq-resize-𝕍ᵉ {l1ᵉ} {l2ᵉ} Hᵉ Kᵉ =
  ( extensionality-type-subtype'ᵉ
    ( is-small-𝕍-Propᵉ l1ᵉ)
    ( resize-𝕍'ᵉ (pairᵉ _ Hᵉ))
    ( resize-𝕍'ᵉ (pairᵉ _ Kᵉ))) ∘eᵉ
  ( ( equiv-apᵉ (equiv-resize-𝕍'ᵉ) (pairᵉ _ Hᵉ) (pairᵉ _ Kᵉ)) ∘eᵉ
    ( inv-equivᵉ
      ( extensionality-type-subtype'ᵉ
        ( is-small-𝕍-Propᵉ l2ᵉ)
        ( pairᵉ _ Hᵉ)
        ( pairᵉ _ Kᵉ))))
```

### The resizing operation on small multisets respects the elementhood relation

```agda
abstract
  equiv-elementhood-resize-𝕍ᵉ :
    {l1ᵉ l2ᵉ : Level} {xᵉ yᵉ : 𝕍ᵉ l1ᵉ} (Hᵉ : is-small-𝕍ᵉ l2ᵉ xᵉ) (Kᵉ : is-small-𝕍ᵉ l2ᵉ yᵉ) →
    (xᵉ ∈-𝕍ᵉ yᵉ) ≃ᵉ (resize-𝕍ᵉ xᵉ Hᵉ ∈-𝕍ᵉ resize-𝕍ᵉ yᵉ Kᵉ)
  equiv-elementhood-resize-𝕍ᵉ {xᵉ = Xᵉ} {tree-𝕎ᵉ Bᵉ βᵉ} Hᵉ (pairᵉ (pairᵉ B'ᵉ eᵉ) Kᵉ) =
    equiv-Σᵉ
      ( λ y'ᵉ →
        ( component-𝕎ᵉ (resize-𝕍ᵉ (tree-𝕎ᵉ Bᵉ βᵉ) (pairᵉ (pairᵉ B'ᵉ eᵉ) Kᵉ)) y'ᵉ) ＝ᵉ
        ( resize-𝕍ᵉ Xᵉ Hᵉ))
      ( eᵉ)
      ( λ bᵉ →
        ( equiv-concatᵉ
          ( apᵉ
            ( λ tᵉ → resize-𝕍ᵉ (βᵉ tᵉ) (Kᵉ tᵉ))
            ( is-retraction-map-inv-equivᵉ eᵉ bᵉ))
          ( resize-𝕍ᵉ Xᵉ Hᵉ)) ∘eᵉ
        ( eq-resize-𝕍ᵉ (Kᵉ bᵉ) Hᵉ))
```

### The type of all multisets of universe level `l1` is `UU l2`-small if each type in `UU l1` is `UU l2`-small

```agda
is-small-multiset-𝕍ᵉ :
  {l1ᵉ l2ᵉ : Level} →
  ((Aᵉ : UUᵉ l1ᵉ) → is-smallᵉ l2ᵉ Aᵉ) → (Xᵉ : 𝕍ᵉ l1ᵉ) → is-small-𝕍ᵉ l2ᵉ Xᵉ
is-small-multiset-𝕍ᵉ {l1ᵉ} {l2ᵉ} Hᵉ (tree-𝕎ᵉ Aᵉ αᵉ) =
  pairᵉ (Hᵉ Aᵉ) (λ xᵉ → is-small-multiset-𝕍ᵉ Hᵉ (αᵉ xᵉ))
```