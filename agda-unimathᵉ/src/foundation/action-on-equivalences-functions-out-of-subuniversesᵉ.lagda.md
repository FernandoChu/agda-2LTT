# The action on equivalences of functions out of subuniverses

```agda
module foundation.action-on-equivalences-functions-out-of-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functionsᵉ
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Considerᵉ aᵉ [subuniverse](foundation.subuniverses.mdᵉ) `P`ᵉ ofᵉ `𝒰`ᵉ andᵉ aᵉ mapᵉ
`fᵉ : Pᵉ → B`ᵉ fromᵉ theᵉ subuniverseᵉ `P`ᵉ intoᵉ someᵉ typeᵉ `B`.ᵉ Thenᵉ `f`ᵉ hasᵉ anᵉ
**actionᵉ onᵉ equivalences**ᵉ

```text
  (Xᵉ ≃ᵉ Yᵉ) → (fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ)
```

whichᵉ isᵉ uniquelyᵉ determinedᵉ byᵉ theᵉ
[identification](foundation-core.identity-types.mdᵉ)
`action-equivᵉ fᵉ id-equivᵉ ＝ᵉ refl`.ᵉ Theᵉ actionᵉ onᵉ equivalencesᵉ fitsᵉ in aᵉ
[commutingᵉ square](foundation.commuting-squares-of-maps.mdᵉ) ofᵉ mapsᵉ

```text
                     apᵉ fᵉ
       (Xᵉ = Yᵉ) --------------->ᵉ (fᵉ Xᵉ = fᵉ Yᵉ)
          |                          |
 equiv-eqᵉ |                          | idᵉ
          ∨ᵉ                          ∨ᵉ
       (Xᵉ ≃ᵉ Yᵉ) --------------->ᵉ (fᵉ Xᵉ = fᵉ Yᵉ)
                action-equivᵉ fᵉ
```

## Definitions

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ)
  {Bᵉ : UUᵉ l3ᵉ} (fᵉ : type-subuniverseᵉ Pᵉ → Bᵉ)
  where

  abstract
    unique-action-equiv-function-subuniverseᵉ :
      (Xᵉ : type-subuniverseᵉ Pᵉ) →
      is-contrᵉ
        ( Σᵉ ( (Yᵉ : type-subuniverseᵉ Pᵉ) → equiv-subuniverseᵉ Pᵉ Xᵉ Yᵉ → fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ)
            ( λ hᵉ → hᵉ Xᵉ id-equivᵉ ＝ᵉ reflᵉ))
    unique-action-equiv-function-subuniverseᵉ Xᵉ =
      is-contr-map-ev-id-equiv-subuniverseᵉ Pᵉ Xᵉ
        ( λ Yᵉ eᵉ → fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ)
        ( reflᵉ)

  action-equiv-function-subuniverseᵉ :
    (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) → equiv-subuniverseᵉ Pᵉ Xᵉ Yᵉ → fᵉ Xᵉ ＝ᵉ fᵉ Yᵉ
  action-equiv-function-subuniverseᵉ Xᵉ Yᵉ =
    apᵉ fᵉ ∘ᵉ eq-equiv-subuniverseᵉ Pᵉ

  compute-action-equiv-function-subuniverse-id-equivᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    action-equiv-function-subuniverseᵉ Xᵉ Xᵉ id-equivᵉ ＝ᵉ reflᵉ
  compute-action-equiv-function-subuniverse-id-equivᵉ Xᵉ =
    ap²ᵉ fᵉ (compute-eq-equiv-id-equiv-subuniverseᵉ Pᵉ)
```