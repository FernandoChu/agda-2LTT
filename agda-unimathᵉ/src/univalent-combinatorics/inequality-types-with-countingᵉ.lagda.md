# Inequality on types equipped with a counting

```agda
module univalent-combinatorics.inequality-types-with-countingᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-standard-finite-typesᵉ

open import foundation.dependent-pair-typesᵉ
open import foundation.equivalencesᵉ
open import foundation.identity-typesᵉ
open import foundation.injective-mapsᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.countingᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Ifᵉ aᵉ typeᵉ comesᵉ equippedᵉ with aᵉ countingᵉ ofᵉ itsᵉ elements,ᵉ thenᵉ itᵉ inheritsᵉ theᵉ
inequalityᵉ relationsᵉ fromᵉ theᵉ standardᵉ finiteᵉ types.ᵉ

## Definition

```agda
leq-countᵉ : {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} → countᵉ Xᵉ → Xᵉ → Xᵉ → UUᵉ lzero
leq-countᵉ eᵉ xᵉ yᵉ =
  leq-Finᵉ
    ( number-of-elements-countᵉ eᵉ)
    ( map-inv-equiv-countᵉ eᵉ xᵉ)
    ( map-inv-equiv-countᵉ eᵉ yᵉ)
```

## Properties

```agda
refl-leq-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) (xᵉ : Xᵉ) → leq-countᵉ eᵉ xᵉ xᵉ
refl-leq-countᵉ eᵉ xᵉ =
  refl-leq-Finᵉ (number-of-elements-countᵉ eᵉ) (map-inv-equiv-countᵉ eᵉ xᵉ)

antisymmetric-leq-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) {xᵉ yᵉ : Xᵉ} →
  leq-countᵉ eᵉ xᵉ yᵉ → leq-countᵉ eᵉ yᵉ xᵉ → Idᵉ xᵉ yᵉ
antisymmetric-leq-countᵉ eᵉ Hᵉ Kᵉ =
  is-injective-map-inv-equivᵉ
    ( equiv-countᵉ eᵉ)
    ( antisymmetric-leq-Finᵉ (number-of-elements-countᵉ eᵉ) _ _ Hᵉ Kᵉ)

transitive-leq-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) {xᵉ yᵉ zᵉ : Xᵉ} →
  leq-countᵉ eᵉ yᵉ zᵉ → leq-countᵉ eᵉ xᵉ yᵉ → leq-countᵉ eᵉ xᵉ zᵉ
transitive-leq-countᵉ (pairᵉ kᵉ eᵉ) {xᵉ} {yᵉ} {zᵉ} =
  transitive-leq-Finᵉ kᵉ
    ( map-inv-equivᵉ eᵉ xᵉ)
    ( map-inv-equivᵉ eᵉ yᵉ)
    ( map-inv-equiv-countᵉ (pairᵉ kᵉ eᵉ) zᵉ)

preserves-leq-equiv-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ)
  {xᵉ yᵉ : Finᵉ (number-of-elements-countᵉ eᵉ)} →
  leq-Finᵉ (number-of-elements-countᵉ eᵉ) xᵉ yᵉ →
  leq-countᵉ eᵉ (map-equiv-countᵉ eᵉ xᵉ) (map-equiv-countᵉ eᵉ yᵉ)
preserves-leq-equiv-countᵉ eᵉ {xᵉ} {yᵉ} Hᵉ =
  concatenate-eq-leq-eq-Finᵉ
    ( number-of-elements-countᵉ eᵉ)
    ( is-retraction-map-inv-equivᵉ (equiv-countᵉ eᵉ) xᵉ)
    ( Hᵉ)
    ( invᵉ (is-retraction-map-inv-equivᵉ (equiv-countᵉ eᵉ) yᵉ))

reflects-leq-equiv-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ)
  {xᵉ yᵉ : Finᵉ (number-of-elements-countᵉ eᵉ)} →
  leq-countᵉ eᵉ (map-equiv-countᵉ eᵉ xᵉ) (map-equiv-countᵉ eᵉ yᵉ) →
  leq-Finᵉ (number-of-elements-countᵉ eᵉ) xᵉ yᵉ
reflects-leq-equiv-countᵉ eᵉ {xᵉ} {yᵉ} Hᵉ =
  concatenate-eq-leq-eq-Finᵉ
    ( number-of-elements-countᵉ eᵉ)
    ( invᵉ (is-retraction-map-inv-equivᵉ (equiv-countᵉ eᵉ) xᵉ))
    ( Hᵉ)
    ( is-retraction-map-inv-equivᵉ (equiv-countᵉ eᵉ) yᵉ)

transpose-leq-equiv-countᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) →
  {xᵉ : Finᵉ (number-of-elements-countᵉ eᵉ)} {yᵉ : Xᵉ} →
  leq-Finᵉ
    ( number-of-elements-countᵉ eᵉ) xᵉ (map-inv-equiv-countᵉ eᵉ yᵉ) →
  leq-countᵉ eᵉ (map-equiv-countᵉ eᵉ xᵉ) yᵉ
transpose-leq-equiv-countᵉ eᵉ {xᵉ} {yᵉ} Hᵉ =
  concatenate-eq-leq-eq-Finᵉ
    ( number-of-elements-countᵉ eᵉ)
    ( is-retraction-map-inv-equivᵉ (equiv-countᵉ eᵉ) xᵉ)
    ( Hᵉ)
    ( reflᵉ)

transpose-leq-equiv-count'ᵉ :
  {lᵉ : Level} {Xᵉ : UUᵉ lᵉ} (eᵉ : countᵉ Xᵉ) →
  {xᵉ : Xᵉ} {yᵉ : Finᵉ (number-of-elements-countᵉ eᵉ)} →
  leq-Finᵉ (number-of-elements-countᵉ eᵉ) (map-inv-equiv-countᵉ eᵉ xᵉ) yᵉ →
  leq-countᵉ eᵉ xᵉ (map-equiv-countᵉ eᵉ yᵉ)
transpose-leq-equiv-count'ᵉ eᵉ {xᵉ} {yᵉ} Hᵉ =
  concatenate-eq-leq-eq-Finᵉ
    ( number-of-elements-countᵉ eᵉ)
    ( reflᵉ)
    ( Hᵉ)
    ( invᵉ (is-retraction-map-inv-equivᵉ (equiv-countᵉ eᵉ) yᵉ))
```