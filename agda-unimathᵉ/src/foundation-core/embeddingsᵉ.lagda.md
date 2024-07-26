# Embeddings

```agda
module foundation-core.embeddingsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
```

</details>

## Idea

Anᵉ **embedding**ᵉ fromᵉ oneᵉ typeᵉ intoᵉ anotherᵉ isᵉ aᵉ mapᵉ thatᵉ inducesᵉ
[equivalences](foundation-core.equivalences.mdᵉ) onᵉ
[identityᵉ types](foundation-core.identity-types.md).ᵉ Inᵉ otherᵉ words,ᵉ theᵉ
identitificationsᵉ `(fᵉ xᵉ) ＝ᵉ (fᵉ y)`ᵉ forᵉ anᵉ embeddingᵉ `fᵉ : Aᵉ → B`ᵉ areᵉ in
one-to-oneᵉ correspondenceᵉ with theᵉ identitificationsᵉ `xᵉ ＝ᵉ y`.ᵉ Embeddingsᵉ areᵉ
betterᵉ behavedᵉ homotopicallyᵉ thanᵉ
[injectiveᵉ maps](foundation-core.injective-maps.md),ᵉ becauseᵉ theᵉ conditionᵉ ofᵉ
beingᵉ anᵉ equivalenceᵉ isᵉ aᵉ [property](foundation-core.propositions.mdᵉ) underᵉ
[functionᵉ extensionality](foundation.function-extensionality.md).ᵉ

## Definition

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-embᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-embᵉ fᵉ = (xᵉ yᵉ : Aᵉ) → is-equivᵉ (apᵉ fᵉ {xᵉ} {yᵉ})

  equiv-ap-is-embᵉ :
    {fᵉ : Aᵉ → Bᵉ} (eᵉ : is-embᵉ fᵉ) {xᵉ yᵉ : Aᵉ} → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (fᵉ xᵉ ＝ᵉ fᵉ yᵉ)
  pr1ᵉ (equiv-ap-is-embᵉ {fᵉ} eᵉ) = apᵉ fᵉ
  pr2ᵉ (equiv-ap-is-embᵉ {fᵉ} eᵉ {xᵉ} {yᵉ}) = eᵉ xᵉ yᵉ

  inv-equiv-ap-is-embᵉ :
    {fᵉ : Aᵉ → Bᵉ} (eᵉ : is-embᵉ fᵉ) {xᵉ yᵉ : Aᵉ} → (fᵉ xᵉ ＝ᵉ fᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
  inv-equiv-ap-is-embᵉ eᵉ = inv-equivᵉ (equiv-ap-is-embᵉ eᵉ)

infix 5 _↪ᵉ_
_↪ᵉ_ :
  {l1ᵉ l2ᵉ : Level} → UUᵉ l1ᵉ → UUᵉ l2ᵉ → UUᵉ (l1ᵉ ⊔ l2ᵉ)
Aᵉ ↪ᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) is-embᵉ

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  map-embᵉ : Aᵉ ↪ᵉ Bᵉ → Aᵉ → Bᵉ
  map-embᵉ = pr1ᵉ

  is-emb-map-embᵉ : (fᵉ : Aᵉ ↪ᵉ Bᵉ) → is-embᵉ (map-embᵉ fᵉ)
  is-emb-map-embᵉ = pr2ᵉ

  equiv-ap-embᵉ :
    (eᵉ : Aᵉ ↪ᵉ Bᵉ) {xᵉ yᵉ : Aᵉ} → (xᵉ ＝ᵉ yᵉ) ≃ᵉ (map-embᵉ eᵉ xᵉ ＝ᵉ map-embᵉ eᵉ yᵉ)
  equiv-ap-embᵉ eᵉ = equiv-ap-is-embᵉ (is-emb-map-embᵉ eᵉ)

  inv-equiv-ap-embᵉ :
    (eᵉ : Aᵉ ↪ᵉ Bᵉ) {xᵉ yᵉ : Aᵉ} → (map-embᵉ eᵉ xᵉ ＝ᵉ map-embᵉ eᵉ yᵉ) ≃ᵉ (xᵉ ＝ᵉ yᵉ)
  inv-equiv-ap-embᵉ eᵉ = inv-equivᵉ (equiv-ap-embᵉ eᵉ)
```

## Examples

### The identity map is an embedding

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ}
  where

  is-emb-idᵉ : is-embᵉ (idᵉ {Aᵉ = Aᵉ})
  is-emb-idᵉ xᵉ yᵉ = is-equiv-htpyᵉ idᵉ ap-idᵉ is-equiv-idᵉ

  id-embᵉ : Aᵉ ↪ᵉ Aᵉ
  pr1ᵉ id-embᵉ = idᵉ
  pr2ᵉ id-embᵉ = is-emb-idᵉ
```

### To prove that a map is an embedding, a point in the domain may be assumed

```agda
module _
  {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} {l2ᵉ : Level} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  abstract
    is-emb-is-embᵉ : (Aᵉ → is-embᵉ fᵉ) → is-embᵉ fᵉ
    is-emb-is-embᵉ Hᵉ xᵉ yᵉ = Hᵉ xᵉ xᵉ yᵉ
```