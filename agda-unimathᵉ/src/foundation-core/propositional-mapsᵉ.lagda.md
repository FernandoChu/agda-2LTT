# Propositional maps

```agda
module foundation-core.propositional-mapsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functionsᵉ
open import foundation.dependent-pair-typesᵉ
open import foundation.fundamental-theorem-of-identity-typesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.contractible-typesᵉ
open import foundation-core.embeddingsᵉ
open import foundation-core.fibers-of-mapsᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ mapᵉ isᵉ saidᵉ to beᵉ **propositional**ᵉ ifᵉ itsᵉ
[fibers](foundation-core.fibers-of-maps.mdᵉ) areᵉ
[propositions](foundation-core.propositions.md).ᵉ Thisᵉ conditionᵉ isᵉ theᵉ sameᵉ asᵉ
theᵉ conditionᵉ ofᵉ beingᵉ aᵉ
[`-1`-truncatedᵉ map](foundation-core.truncated-maps.md),ᵉ andᵉ itᵉ isᵉ
[equivalent](foundation-core.equivalences.mdᵉ) to beingᵉ anᵉ
[embedding](foundation-core.embeddings.md).ᵉ

**Note:**ᵉ Ofᵉ theᵉ threeᵉ equivalentᵉ conditionsᵉ mentionedᵉ above,ᵉ propositionalᵉ
maps,ᵉ `-1`-truncatedᵉ maps,ᵉ andᵉ embeddings,ᵉ theᵉ centralᵉ notionᵉ ofᵉ in theᵉ
agda-unimathᵉ libraryᵉ isᵉ thatᵉ ofᵉ embedding.ᵉ Thisᵉ meansᵉ thatᵉ mostᵉ infrastructureᵉ
isᵉ availableᵉ forᵉ embeddings,ᵉ andᵉ thatᵉ itᵉ isᵉ easyᵉ to convertᵉ fromᵉ anyᵉ ofᵉ theᵉ
otherᵉ twoᵉ notionsᵉ to theᵉ notionᵉ ofᵉ embedding.ᵉ

## Definitions

### The predicate of being a propositional map

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  is-prop-mapᵉ : (Aᵉ → Bᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  is-prop-mapᵉ fᵉ = (bᵉ : Bᵉ) → is-propᵉ (fiberᵉ fᵉ bᵉ)
```

### The type of propositional maps

```agda
module _
  {l1ᵉ l2ᵉ : Level}
  where

  prop-mapᵉ : (Aᵉ : UUᵉ l1ᵉ) (Bᵉ : UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
  prop-mapᵉ Aᵉ Bᵉ = Σᵉ (Aᵉ → Bᵉ) is-prop-mapᵉ

  module _
    {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} (fᵉ : prop-mapᵉ Aᵉ Bᵉ)
    where

    map-prop-mapᵉ : Aᵉ → Bᵉ
    map-prop-mapᵉ = pr1ᵉ fᵉ

    is-prop-map-prop-mapᵉ : is-prop-mapᵉ map-prop-mapᵉ
    is-prop-map-prop-mapᵉ = pr2ᵉ fᵉ
```

## Properties

### The fibers of a map are propositions if and only if it is an embedding

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ} {fᵉ : Aᵉ → Bᵉ}
  where

  abstract
    is-emb-is-prop-mapᵉ : is-prop-mapᵉ fᵉ → is-embᵉ fᵉ
    is-emb-is-prop-mapᵉ is-prop-map-fᵉ xᵉ =
      fundamental-theorem-idᵉ
        ( is-contr-equiv'ᵉ
          ( fiberᵉ fᵉ (fᵉ xᵉ))
          ( equiv-fiberᵉ fᵉ (fᵉ xᵉ))
          ( is-proof-irrelevant-is-propᵉ (is-prop-map-fᵉ (fᵉ xᵉ)) (xᵉ ,ᵉ reflᵉ)))
        ( λ _ → apᵉ fᵉ)

  abstract
    is-prop-map-is-embᵉ : is-embᵉ fᵉ → is-prop-mapᵉ fᵉ
    is-prop-map-is-embᵉ is-emb-fᵉ yᵉ =
      is-prop-is-proof-irrelevantᵉ αᵉ
      where
      αᵉ : (tᵉ : fiberᵉ fᵉ yᵉ) → is-contrᵉ (fiberᵉ fᵉ yᵉ)
      αᵉ (xᵉ ,ᵉ reflᵉ) =
        is-contr-equivᵉ
          ( fiber'ᵉ fᵉ (fᵉ xᵉ))
          ( equiv-fiberᵉ fᵉ (fᵉ xᵉ))
          ( fundamental-theorem-id'ᵉ (λ _ → apᵉ fᵉ) (is-emb-fᵉ xᵉ))

module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : UUᵉ l2ᵉ}
  where

  emb-prop-mapᵉ : prop-mapᵉ Aᵉ Bᵉ → Aᵉ ↪ᵉ Bᵉ
  pr1ᵉ (emb-prop-mapᵉ (fᵉ ,ᵉ pᵉ)) = fᵉ
  pr2ᵉ (emb-prop-mapᵉ (fᵉ ,ᵉ pᵉ)) = is-emb-is-prop-mapᵉ pᵉ

  prop-map-embᵉ : Aᵉ ↪ᵉ Bᵉ → prop-mapᵉ Aᵉ Bᵉ
  pr1ᵉ (prop-map-embᵉ (fᵉ ,ᵉ pᵉ)) = fᵉ
  pr2ᵉ (prop-map-embᵉ (fᵉ ,ᵉ pᵉ)) = is-prop-map-is-embᵉ pᵉ

  is-prop-map-embᵉ : (fᵉ : Aᵉ ↪ᵉ Bᵉ) → is-prop-mapᵉ (map-embᵉ fᵉ)
  is-prop-map-embᵉ fᵉ = is-prop-map-is-embᵉ (is-emb-map-embᵉ fᵉ)

  is-prop-map-emb'ᵉ : (fᵉ : Aᵉ ↪ᵉ Bᵉ) → (bᵉ : Bᵉ) → is-propᵉ (fiber'ᵉ (map-embᵉ fᵉ) bᵉ)
  is-prop-map-emb'ᵉ fᵉ yᵉ =
    is-prop-equiv'ᵉ (equiv-fiberᵉ (map-embᵉ fᵉ) yᵉ) (is-prop-map-embᵉ fᵉ yᵉ)

  fiber-emb-Propᵉ : Aᵉ ↪ᵉ Bᵉ → Bᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (fiber-emb-Propᵉ fᵉ yᵉ) = fiberᵉ (map-embᵉ fᵉ) yᵉ
  pr2ᵉ (fiber-emb-Propᵉ fᵉ yᵉ) = is-prop-map-embᵉ fᵉ yᵉ

  fiber-emb-Prop'ᵉ : Aᵉ ↪ᵉ Bᵉ → Bᵉ → Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ (fiber-emb-Prop'ᵉ fᵉ yᵉ) = fiber'ᵉ (map-embᵉ fᵉ) yᵉ
  pr2ᵉ (fiber-emb-Prop'ᵉ fᵉ yᵉ) = is-prop-map-emb'ᵉ fᵉ yᵉ
```