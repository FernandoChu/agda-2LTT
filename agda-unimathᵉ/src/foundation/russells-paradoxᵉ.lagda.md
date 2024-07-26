# Russell's paradox

```agda
{-# OPTIONSᵉ --lossy-unificationᵉ #-}

module foundation.russells-paradoxᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-cartesian-product-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.locally-small-typesᵉ
open import foundation.negationᵉ
open import foundation.small-typesᵉ
open import foundation.small-universesᵉ
open import foundation.surjective-mapsᵉ
open import foundation.torsorial-type-familiesᵉ
open import foundation.type-arithmetic-cartesian-product-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.empty-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.functoriality-dependent-pair-typesᵉ

open import trees.multisetsᵉ
open import trees.small-multisetsᵉ
open import trees.universal-multisetᵉ
```

</details>

## Idea

Russell'sᵉ paradoxᵉ arisesᵉ whenᵉ aᵉ setᵉ ofᵉ allᵉ setsᵉ isᵉ assumedᵉ to exist.ᵉ Inᵉ
Russell'sᵉ paradoxᵉ itᵉ isᵉ ofᵉ noᵉ importanceᵉ thatᵉ theᵉ elementhoodᵉ relationᵉ takesᵉ
valuesᵉ in propositions.ᵉ Inᵉ otherᵉ words,ᵉ Russell'sᵉ paradoxᵉ arisesᵉ similarlyᵉ ifᵉ
thereᵉ isᵉ aᵉ multisetᵉ ofᵉ allᵉ multisets.ᵉ Weᵉ willᵉ constructᵉ Russell'sᵉ paradoxᵉ fromᵉ
theᵉ assumptionᵉ thatᵉ aᵉ universeᵉ `U`ᵉ isᵉ equivalentᵉ to aᵉ typeᵉ `Aᵉ : U`.ᵉ Weᵉ concludeᵉ
thatᵉ thereᵉ canᵉ beᵉ noᵉ universeᵉ thatᵉ isᵉ containedᵉ in itself.ᵉ Furthermore,ᵉ using
replacementᵉ weᵉ showᵉ thatᵉ forᵉ anyᵉ typeᵉ `Aᵉ : U`,ᵉ thereᵉ isᵉ noᵉ surjectiveᵉ mapᵉ
`Aᵉ → U`.ᵉ

## Definition

### Russell's multiset

```agda
Russellᵉ : (lᵉ : Level) → 𝕍ᵉ (lsuc lᵉ)
Russellᵉ lᵉ =
  comprehension-𝕍ᵉ
    ( universal-multiset-𝕍ᵉ lᵉ)
    ( λ Xᵉ → Xᵉ ∉-𝕍ᵉ Xᵉ)
```

## Properties

### If a universe is small with respect to another universe, then Russells multiset is also small

```agda
is-small-Russellᵉ :
  {l1ᵉ l2ᵉ : Level} → is-small-universeᵉ l2ᵉ l1ᵉ → is-small-𝕍ᵉ l2ᵉ (Russellᵉ l1ᵉ)
is-small-Russellᵉ {l1ᵉ} {l2ᵉ} Hᵉ =
  is-small-comprehension-𝕍ᵉ l2ᵉ
    { lsuc l1ᵉ}
    { universal-multiset-𝕍ᵉ l1ᵉ}
    { λ zᵉ → zᵉ ∉-𝕍ᵉ zᵉ}
    ( is-small-universal-multiset-𝕍ᵉ l2ᵉ Hᵉ)
    ( λ Xᵉ → is-small-∉-𝕍ᵉ l2ᵉ {l1ᵉ} {Xᵉ} {Xᵉ} (Kᵉ Xᵉ) (Kᵉ Xᵉ))
  where
  Kᵉ = is-small-multiset-𝕍ᵉ (λ Aᵉ → pr2ᵉ Hᵉ Aᵉ)

resize-Russellᵉ :
  {l1ᵉ l2ᵉ : Level} → is-small-universeᵉ l2ᵉ l1ᵉ → 𝕍ᵉ l2ᵉ
resize-Russellᵉ {l1ᵉ} {l2ᵉ} Hᵉ =
  resize-𝕍ᵉ (Russellᵉ l1ᵉ) (is-small-Russellᵉ Hᵉ)

is-small-resize-Russellᵉ :
  {l1ᵉ l2ᵉ : Level} (Hᵉ : is-small-universeᵉ l2ᵉ l1ᵉ) →
  is-small-𝕍ᵉ (lsuc l1ᵉ) (resize-Russellᵉ Hᵉ)
is-small-resize-Russellᵉ {l1ᵉ} {l2ᵉ} Hᵉ =
  is-small-resize-𝕍ᵉ (Russellᵉ l1ᵉ) (is-small-Russellᵉ Hᵉ)

equiv-Russell-in-Russellᵉ :
  {l1ᵉ l2ᵉ : Level} (Hᵉ : is-small-universeᵉ l2ᵉ l1ᵉ) →
  (Russellᵉ l1ᵉ ∈-𝕍ᵉ Russellᵉ l1ᵉ) ≃ᵉ (resize-Russellᵉ Hᵉ ∈-𝕍ᵉ resize-Russellᵉ Hᵉ)
equiv-Russell-in-Russellᵉ Hᵉ =
  equiv-elementhood-resize-𝕍ᵉ (is-small-Russellᵉ Hᵉ) (is-small-Russellᵉ Hᵉ)
```

### Russell's paradox obtained from the assumption that `U` is `U`-small

```agda
paradox-Russellᵉ : {lᵉ : Level} → ¬ᵉ (is-smallᵉ lᵉ (UUᵉ lᵉ))
paradox-Russellᵉ {lᵉ} Hᵉ =
  no-fixed-points-negᵉ
    ( Rᵉ ∈-𝕍ᵉ Rᵉ)
    ( pairᵉ (map-equivᵉ βᵉ) (map-inv-equivᵉ βᵉ))
  where

  Kᵉ : is-small-universeᵉ lᵉ lᵉ
  Kᵉ = pairᵉ Hᵉ (λ Xᵉ → pairᵉ Xᵉ id-equivᵉ)

  Rᵉ : 𝕍ᵉ (lsuc lᵉ)
  Rᵉ = Russellᵉ lᵉ

  is-small-Rᵉ : is-small-𝕍ᵉ lᵉ Rᵉ
  is-small-Rᵉ = is-small-Russellᵉ Kᵉ

  R'ᵉ : 𝕍ᵉ lᵉ
  R'ᵉ = resize-Russellᵉ Kᵉ

  is-small-R'ᵉ : is-small-𝕍ᵉ (lsuc lᵉ) R'ᵉ
  is-small-R'ᵉ = is-small-resize-Russellᵉ Kᵉ

  abstract
    pᵉ : resize-𝕍ᵉ R'ᵉ is-small-R'ᵉ ＝ᵉ Rᵉ
    pᵉ = resize-resize-𝕍ᵉ is-small-Rᵉ

  αᵉ : (Rᵉ ∈-𝕍ᵉ Rᵉ) ≃ᵉ (R'ᵉ ∈-𝕍ᵉ R'ᵉ)
  αᵉ = equiv-Russell-in-Russellᵉ Kᵉ

  abstract
    βᵉ : (Rᵉ ∈-𝕍ᵉ Rᵉ) ≃ᵉ (Rᵉ ∉-𝕍ᵉ Rᵉ)
    βᵉ = ( equiv-precompᵉ αᵉ emptyᵉ) ∘eᵉ
        ( ( left-unit-law-Σ-is-contrᵉ
            { Bᵉ = λ tᵉ → (pr1ᵉ tᵉ) ∉-𝕍ᵉ (pr1ᵉ tᵉ)}
            ( is-torsorial-Id'ᵉ R'ᵉ)
            ( pairᵉ R'ᵉ reflᵉ)) ∘eᵉ
          ( ( inv-associative-Σᵉ (𝕍ᵉ lᵉ) (_＝ᵉ R'ᵉ) (λ tᵉ → (pr1ᵉ tᵉ) ∉-𝕍ᵉ (pr1ᵉ tᵉ))) ∘eᵉ
            ( ( equiv-totᵉ
                ( λ tᵉ →
                  ( commutative-productᵉ) ∘eᵉ
                  ( equiv-productᵉ
                    ( id-equivᵉ)
                    ( inv-equivᵉ
                      ( ( equiv-concat'ᵉ
                          _ ( pᵉ)) ∘eᵉ
                        ( eq-resize-𝕍ᵉ
                          ( is-small-multiset-𝕍ᵉ is-small-lsucᵉ tᵉ)
                          ( is-small-R'ᵉ))))))) ∘eᵉ
              ( associative-Σᵉ
                ( 𝕍ᵉ lᵉ)
                ( λ tᵉ → tᵉ ∉-𝕍ᵉ tᵉ)
                ( λ tᵉ → ( resize-𝕍ᵉ
                          ( pr1ᵉ tᵉ)
                          ( is-small-multiset-𝕍ᵉ is-small-lsucᵉ (pr1ᵉ tᵉ))) ＝ᵉ
                        ( Rᵉ))))))
```

### There can be no surjective map `f : A → U` for any `A : U`

```agda
no-surjection-onto-universeᵉ :
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} (fᵉ : Aᵉ → UUᵉ lᵉ) → ¬ᵉ (is-surjectiveᵉ fᵉ)
no-surjection-onto-universeᵉ fᵉ Hᵉ =
  paradox-Russellᵉ
    ( is-small-is-surjectiveᵉ Hᵉ
      ( is-small'ᵉ)
      ( is-locally-small-UUᵉ))
```