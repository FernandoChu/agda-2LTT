# Action on equivalences in type families over subuniverses

```agda
module foundation.action-on-equivalences-type-families-over-subuniversesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.equivalence-inductionᵉ
open import foundation.subuniversesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.commuting-squares-of-mapsᵉ
open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.univalenceᵉ
```

</details>

## Ideas

Givenᵉ aᵉ [subuniverse](foundation.subuniverses.mdᵉ) `P`,ᵉ anyᵉ familyᵉ ofᵉ typesᵉ `B`ᵉ
indexedᵉ byᵉ typesᵉ ofᵉ `P`ᵉ hasᵉ anᵉ
[actionᵉ onᵉ equivalences](foundation.action-on-equivalences-functions.mdᵉ)
obtainedᵉ byᵉ using theᵉ [univalenceᵉ axiom](foundation.univalence.md).ᵉ

## Definitions

### The action on equivalences of a family of types over a subuniverse

```agda
module _
  { l1ᵉ l2ᵉ l3ᵉ : Level}
  ( Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Bᵉ : type-subuniverseᵉ Pᵉ → UUᵉ l3ᵉ)
  where

  abstract
    unique-action-equiv-family-over-subuniverseᵉ :
      (Xᵉ : type-subuniverseᵉ Pᵉ) →
      is-contrᵉ
        ( fiberᵉ (ev-id-equiv-subuniverseᵉ Pᵉ Xᵉ {λ Yᵉ eᵉ → Bᵉ Xᵉ ≃ᵉ Bᵉ Yᵉ}) id-equivᵉ)
    unique-action-equiv-family-over-subuniverseᵉ Xᵉ =
      is-contr-map-ev-id-equiv-subuniverseᵉ Pᵉ Xᵉ (λ Yᵉ eᵉ → Bᵉ Xᵉ ≃ᵉ Bᵉ Yᵉ) id-equivᵉ

  action-equiv-family-over-subuniverseᵉ :
    (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) → pr1ᵉ Xᵉ ≃ᵉ pr1ᵉ Yᵉ → Bᵉ Xᵉ ≃ᵉ Bᵉ Yᵉ
  action-equiv-family-over-subuniverseᵉ Xᵉ Yᵉ =
    equiv-eqᵉ ∘ᵉ apᵉ Bᵉ ∘ᵉ eq-equiv-subuniverseᵉ Pᵉ

  compute-id-equiv-action-equiv-family-over-subuniverseᵉ :
    (Xᵉ : type-subuniverseᵉ Pᵉ) →
    action-equiv-family-over-subuniverseᵉ Xᵉ Xᵉ id-equivᵉ ＝ᵉ id-equivᵉ
  compute-id-equiv-action-equiv-family-over-subuniverseᵉ Xᵉ =
    apᵉ (equiv-eqᵉ ∘ᵉ apᵉ Bᵉ) (compute-eq-equiv-id-equiv-subuniverseᵉ Pᵉ)
```

## Properties

### The action on equivalences of a family of types over a subuniverse fits in a commuting square with `equiv-eq`

Weᵉ claimᵉ thatᵉ theᵉ squareᵉ

```text
                   apᵉ Bᵉ
        (Xᵉ ＝ᵉ Yᵉ) -------->ᵉ (Bᵉ Xᵉ ＝ᵉ Bᵉ Yᵉ)
           |                    |
  equiv-eqᵉ |                    | equiv-eqᵉ
           ∨ᵉ                    ∨ᵉ
        (Xᵉ ≃ᵉ Yᵉ) --------->ᵉ (Bᵉ Xᵉ ≃ᵉ Bᵉ Y).ᵉ
                     Bᵉ
```

commutesᵉ forᵉ anyᵉ twoᵉ typesᵉ `Xᵉ Yᵉ : type-subuniverseᵉ P`ᵉ andᵉ anyᵉ familyᵉ ofᵉ typesᵉ
`B`ᵉ overᵉ theᵉ subuniverseᵉ `P`.ᵉ

```agda
coherence-square-action-equiv-family-over-subuniverseᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} (Pᵉ : subuniverseᵉ l1ᵉ l2ᵉ) (Bᵉ : type-subuniverseᵉ Pᵉ → UUᵉ l3ᵉ) →
  (Xᵉ Yᵉ : type-subuniverseᵉ Pᵉ) →
  coherence-square-mapsᵉ
    ( apᵉ Bᵉ {Xᵉ} {Yᵉ})
    ( equiv-eq-subuniverseᵉ Pᵉ Xᵉ Yᵉ)
    ( equiv-eqᵉ)
    ( action-equiv-family-over-subuniverseᵉ Pᵉ Bᵉ Xᵉ Yᵉ)
coherence-square-action-equiv-family-over-subuniverseᵉ
  Pᵉ Bᵉ Xᵉ .Xᵉ reflᵉ =
  compute-id-equiv-action-equiv-family-over-subuniverseᵉ Pᵉ Bᵉ Xᵉ
```