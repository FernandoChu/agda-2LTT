# The universal property of equivalences

```agda
module foundation.universal-property-equivalencesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.dependent-universal-property-equivalencesᵉ
open import foundation.precomposition-functions-into-subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.precomposition-functionsᵉ
```

</details>

## Idea

Considerᵉ aᵉ mapᵉ `fᵉ : Aᵉ → B`.ᵉ Weᵉ sayᵉ thatᵉ `f`ᵉ satisfiesᵉ theᵉ **universalᵉ propertyᵉ
ofᵉ equivalences**ᵉ ifᵉ
[precomposition](foundation-core.precomposition-functions.mdᵉ) byᵉ `f`ᵉ

```text
  -ᵉ ∘ᵉ fᵉ : (Bᵉ → Xᵉ) → (Aᵉ → Xᵉ)
```

isᵉ anᵉ [equivalence](foundation-core.equivalences.mdᵉ) forᵉ everyᵉ typeᵉ `X`.ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  universal-property-equivᵉ : UUωᵉ
  universal-property-equivᵉ = {lᵉ : Level} (Xᵉ : UUᵉ lᵉ) → is-equivᵉ (precompᵉ fᵉ Xᵉ)
```

## Properties

### Precomposition and equivalences

#### If dependent precomposition by `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-is-equiv-precomp-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    dependent-universal-property-equivᵉ fᵉ →
    universal-property-equivᵉ fᵉ
  is-equiv-precomp-is-equiv-precomp-Πᵉ fᵉ Hᵉ Cᵉ = Hᵉ (λ _ → Cᵉ)
```

#### If `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-equiv-precomp-is-equivᵉ :
      is-equivᵉ fᵉ → universal-property-equivᵉ fᵉ
    is-equiv-precomp-is-equivᵉ Hᵉ =
      is-equiv-precomp-is-equiv-precomp-Πᵉ fᵉ
        ( is-equiv-precomp-Π-is-equivᵉ Hᵉ)

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (eᵉ : Aᵉ ≃ᵉ Bᵉ)
  where

  abstract
    is-equiv-precomp-equivᵉ :
      universal-property-equivᵉ (map-equivᵉ eᵉ)
    is-equiv-precomp-equivᵉ =
      is-equiv-precomp-is-equivᵉ (map-equivᵉ eᵉ) (is-equiv-map-equivᵉ eᵉ)

  equiv-precompᵉ : {l3ᵉ : Level} (Cᵉ : UUᵉ l3ᵉ) → (Bᵉ → Cᵉ) ≃ᵉ (Aᵉ → Cᵉ)
  pr1ᵉ (equiv-precompᵉ Cᵉ) = precompᵉ (map-equivᵉ eᵉ) Cᵉ
  pr2ᵉ (equiv-precompᵉ Cᵉ) = is-equiv-precomp-equivᵉ Cᵉ
```

#### If precomposing by `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ)
  where

  abstract
    is-equiv-is-equiv-precompᵉ :
      universal-property-equivᵉ fᵉ → is-equivᵉ fᵉ
    is-equiv-is-equiv-precompᵉ Hᵉ =
      is-equiv-is-equiv-precomp-structured-typeᵉ
        ( λ lᵉ → l1ᵉ ⊔ l2ᵉ)
        ( λ Xᵉ → Aᵉ → Bᵉ)
        ( Aᵉ ,ᵉ fᵉ)
        ( Bᵉ ,ᵉ fᵉ)
        ( fᵉ)
        ( λ Cᵉ → Hᵉ (pr1ᵉ Cᵉ))
```

#### If dependent precomposition by `f` is an equivalence, then `f` is an equivalence

```agda
abstract
  is-equiv-is-equiv-precomp-Πᵉ :
    {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : Aᵉ → Bᵉ) →
    dependent-universal-property-equivᵉ fᵉ →
    is-equivᵉ fᵉ
  is-equiv-is-equiv-precomp-Πᵉ fᵉ Hᵉ =
    is-equiv-is-equiv-precompᵉ fᵉ (is-equiv-precomp-is-equiv-precomp-Πᵉ fᵉ Hᵉ)
```