# The subtype identity principle

```agda
module foundation.subtype-identity-principleᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.type-arithmetic-dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.torsorial-type-familiesᵉ
```

</details>

## Idea

Theᵉ **subtypeᵉ identityᵉ principle**ᵉ allowsᵉ usᵉ to efficientlyᵉ characterizeᵉ theᵉ
[identityᵉ type](foundation-core.identity-types.mdᵉ) ofᵉ aᵉ
[subtype](foundation-core.subtypes.md),ᵉ using aᵉ characterizationᵉ ofᵉ theᵉ identityᵉ
typeᵉ ofᵉ theᵉ baseᵉ type.ᵉ

## Lemma

Theᵉ followingᵉ isᵉ aᵉ generalᵉ constructionᵉ thatᵉ willᵉ helpᵉ usᵉ showᵉ thatᵉ theᵉ identityᵉ
typeᵉ ofᵉ aᵉ subtypeᵉ agreesᵉ with theᵉ identityᵉ typeᵉ ofᵉ theᵉ originalᵉ type.ᵉ Weᵉ alreadyᵉ
knowᵉ thatᵉ theᵉ firstᵉ projectionᵉ ofᵉ aᵉ familyᵉ ofᵉ
[propositions](foundation-core.propositions.mdᵉ) isᵉ anᵉ
[embedding](foundation-core.embeddings.md),ᵉ butᵉ theᵉ followingᵉ lemmaᵉ stillᵉ hasᵉ
itsᵉ uses.ᵉ

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  abstract
    is-torsorial-Eq-subtypeᵉ :
      {l3ᵉ : Level} {Pᵉ : Aᵉ → UUᵉ l3ᵉ} →
      is-torsorialᵉ Bᵉ → ((xᵉ : Aᵉ) → is-propᵉ (Pᵉ xᵉ)) →
      (aᵉ : Aᵉ) (bᵉ : Bᵉ aᵉ) (pᵉ : Pᵉ aᵉ) →
      is-torsorialᵉ (λ (tᵉ : Σᵉ Aᵉ Pᵉ) → Bᵉ (pr1ᵉ tᵉ))
    is-torsorial-Eq-subtypeᵉ {Pᵉ = Pᵉ} is-torsorial-Bᵉ is-subtype-Pᵉ aᵉ bᵉ pᵉ =
      is-contr-equivᵉ
        ( Σᵉ (Σᵉ Aᵉ Bᵉ) (Pᵉ ∘ᵉ pr1ᵉ))
        ( equiv-right-swap-Σᵉ)
        ( is-contr-equivᵉ
          ( Pᵉ aᵉ)
          ( left-unit-law-Σ-is-contrᵉ is-torsorial-Bᵉ (aᵉ ,ᵉ bᵉ))
          ( is-proof-irrelevant-is-propᵉ (is-subtype-Pᵉ aᵉ) pᵉ))
```

## Theorem

### The subtype identity principle

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ}
  (is-prop-Pᵉ : (xᵉ : Aᵉ) → is-propᵉ (Pᵉ xᵉ)) {Eq-Aᵉ : Aᵉ → UUᵉ l3ᵉ}
  {aᵉ : Aᵉ} (pᵉ : Pᵉ aᵉ) (refl-Aᵉ : Eq-Aᵉ aᵉ)
  where

  abstract
    subtype-identity-principleᵉ :
      {fᵉ : (xᵉ : Aᵉ) → aᵉ ＝ᵉ xᵉ → Eq-Aᵉ xᵉ}
      (hᵉ : (zᵉ : (Σᵉ Aᵉ Pᵉ)) → (aᵉ ,ᵉ pᵉ) ＝ᵉ zᵉ → Eq-Aᵉ (pr1ᵉ zᵉ)) →
      ((xᵉ : Aᵉ) → is-equivᵉ (fᵉ xᵉ)) → (zᵉ : Σᵉ Aᵉ Pᵉ) → is-equivᵉ (hᵉ zᵉ)
    subtype-identity-principleᵉ {fᵉ} hᵉ Hᵉ =
      fundamental-theorem-idᵉ
        ( is-torsorial-Eq-subtypeᵉ
          ( fundamental-theorem-id'ᵉ fᵉ Hᵉ)
          ( is-prop-Pᵉ)
          ( aᵉ)
          ( refl-Aᵉ)
          ( pᵉ))
        ( hᵉ)

module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (Pᵉ : Aᵉ → Propᵉ l2ᵉ) {Eq-Aᵉ : Aᵉ → UUᵉ l3ᵉ}
  {aᵉ : Aᵉ} (pᵉ : type-Propᵉ (Pᵉ aᵉ)) (refl-Aᵉ : Eq-Aᵉ aᵉ)
  where

  map-extensionality-type-subtypeᵉ :
    (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Eq-Aᵉ xᵉ) →
    (zᵉ : Σᵉ Aᵉ (type-Propᵉ ∘ᵉ Pᵉ)) → (aᵉ ,ᵉ pᵉ) ＝ᵉ zᵉ → Eq-Aᵉ (pr1ᵉ zᵉ)
  map-extensionality-type-subtypeᵉ fᵉ .(aᵉ ,ᵉ pᵉ) reflᵉ = refl-Aᵉ

  extensionality-type-subtypeᵉ :
    (fᵉ : (xᵉ : Aᵉ) → (aᵉ ＝ᵉ xᵉ) ≃ᵉ Eq-Aᵉ xᵉ) →
    (zᵉ : Σᵉ Aᵉ (type-Propᵉ ∘ᵉ Pᵉ)) → ((aᵉ ,ᵉ pᵉ) ＝ᵉ zᵉ) ≃ᵉ Eq-Aᵉ (pr1ᵉ zᵉ)
  pr1ᵉ (extensionality-type-subtypeᵉ fᵉ zᵉ) = map-extensionality-type-subtypeᵉ fᵉ zᵉ
  pr2ᵉ (extensionality-type-subtypeᵉ fᵉ zᵉ) =
    subtype-identity-principleᵉ
      ( is-prop-type-Propᵉ ∘ᵉ Pᵉ)
      ( pᵉ)
      ( refl-Aᵉ)
      ( map-extensionality-type-subtypeᵉ fᵉ)
      ( is-equiv-map-equivᵉ ∘ᵉ fᵉ)
      ( zᵉ)
```