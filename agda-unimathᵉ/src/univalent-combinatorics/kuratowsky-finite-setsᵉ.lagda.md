# Kuratowsky finite sets

```agda
module univalent-combinatorics.kuratowsky-finite-setsᵉ where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbersᵉ

open import foundation.decidable-equalityᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.existential-quantificationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.propositionsᵉ
open import foundation.setsᵉ
open import foundation.surjective-mapsᵉ
open import foundation.universe-levelsᵉ

open import univalent-combinatorics.equality-finite-typesᵉ
open import univalent-combinatorics.finite-typesᵉ
open import univalent-combinatorics.image-of-mapsᵉ
open import univalent-combinatorics.standard-finite-typesᵉ
```

</details>

## Idea

Aᵉ Kuratowskyᵉ finiteᵉ typeᵉ isᵉ aᵉ setᵉ `X`ᵉ forᵉ whichᵉ thereᵉ existsᵉ aᵉ surjectionᵉ intoᵉ
`X`ᵉ fromᵉ aᵉ standardᵉ finiteᵉ type.ᵉ Inᵉ otherᵉ words,ᵉ theᵉ Kuratowskyᵉ finiteᵉ typesᵉ areᵉ
theᵉ set-quotientᵉ ofᵉ aᵉ standardᵉ finiteᵉ type.ᵉ

## Definition

```agda
is-kuratowsky-finite-set-Propᵉ : {lᵉ : Level} → Setᵉ lᵉ → Propᵉ lᵉ
is-kuratowsky-finite-set-Propᵉ Xᵉ =
  exists-structure-Propᵉ ℕᵉ (λ nᵉ → Finᵉ nᵉ ↠ᵉ type-Setᵉ Xᵉ)

is-kuratowsky-finite-setᵉ : {lᵉ : Level} → Setᵉ lᵉ → UUᵉ lᵉ
is-kuratowsky-finite-setᵉ Xᵉ = type-Propᵉ (is-kuratowsky-finite-set-Propᵉ Xᵉ)

𝔽-Kuratowskyᵉ : (lᵉ : Level) → UUᵉ (lsuc lᵉ)
𝔽-Kuratowskyᵉ lᵉ = Σᵉ (Setᵉ lᵉ) is-kuratowsky-finite-setᵉ

module _
  {lᵉ : Level} (Xᵉ : 𝔽-Kuratowskyᵉ lᵉ)
  where

  set-𝔽-Kuratowskyᵉ : Setᵉ lᵉ
  set-𝔽-Kuratowskyᵉ = pr1ᵉ Xᵉ

  type-𝔽-Kuratowskyᵉ : UUᵉ lᵉ
  type-𝔽-Kuratowskyᵉ = type-Setᵉ set-𝔽-Kuratowskyᵉ

  is-set-type-𝔽-Kuratowskyᵉ : is-setᵉ type-𝔽-Kuratowskyᵉ
  is-set-type-𝔽-Kuratowskyᵉ = is-set-type-Setᵉ set-𝔽-Kuratowskyᵉ

  is-kuratowsky-finite-set-𝔽-Kuratowskyᵉ :
    is-kuratowsky-finite-setᵉ set-𝔽-Kuratowskyᵉ
  is-kuratowsky-finite-set-𝔽-Kuratowskyᵉ = pr2ᵉ Xᵉ
```

## Properties

### A Kuratowsky finite set is finite if and only if it has decidable equality

```agda
is-finite-has-decidable-equality-type-𝔽-Kuratowskyᵉ :
  {lᵉ : Level} (Xᵉ : 𝔽-Kuratowskyᵉ lᵉ) →
  has-decidable-equalityᵉ (type-𝔽-Kuratowskyᵉ Xᵉ) →
  is-finiteᵉ (type-𝔽-Kuratowskyᵉ Xᵉ)
is-finite-has-decidable-equality-type-𝔽-Kuratowskyᵉ Xᵉ Hᵉ =
  apply-universal-property-trunc-Propᵉ
    ( is-kuratowsky-finite-set-𝔽-Kuratowskyᵉ Xᵉ)
    ( is-finite-Propᵉ (type-𝔽-Kuratowskyᵉ Xᵉ))
    ( λ (nᵉ ,ᵉ fᵉ ,ᵉ sᵉ) → is-finite-codomainᵉ (is-finite-Finᵉ nᵉ) sᵉ Hᵉ)

has-decidable-equality-is-finite-type-𝔽-Kuratowskyᵉ :
  {lᵉ : Level} (Xᵉ : 𝔽-Kuratowskyᵉ lᵉ) →
  is-finiteᵉ (type-𝔽-Kuratowskyᵉ Xᵉ) →
  has-decidable-equalityᵉ (type-𝔽-Kuratowskyᵉ Xᵉ)
has-decidable-equality-is-finite-type-𝔽-Kuratowskyᵉ Xᵉ Hᵉ =
  has-decidable-equality-is-finiteᵉ Hᵉ
```