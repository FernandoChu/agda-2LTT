# Cyclic higher groups

```agda
module higher-group-theory.cyclic-higher-groupsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddingsᵉ
open import foundation.existential-quantificationᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import higher-group-theory.higher-groupsᵉ
open import higher-group-theory.homomorphisms-higher-groupsᵉ
```

</details>

## Idea

Oneᵉ mayᵉ wonderᵉ ifᵉ theᵉ notionᵉ ofᵉ [cyclicᵉ group](group-theory.cyclic-groups.mdᵉ)
generalizesᵉ to [higherᵉ groups](higher-group-theory.higher-groups.md).ᵉ Aᵉ naiveᵉ
wayᵉ ofᵉ definingᵉ cyclicᵉ higherᵉ groupsᵉ isᵉ to extendᵉ theᵉ universalᵉ propertyᵉ ofᵉ
cyclicᵉ groupsᵉ to allᵉ higherᵉ groups.ᵉ Followingᵉ thisᵉ idea,ᵉ weᵉ sayᵉ thatᵉ aᵉ higherᵉ
groupᵉ `G`ᵉ isᵉ **cyclic**ᵉ ifᵉ thereᵉ
[exists](foundation.existential-quantification.mdᵉ) anᵉ elementᵉ `g`ᵉ ofᵉ `G`ᵉ suchᵉ
thatᵉ theᵉ evaluationᵉ mapᵉ

```text
  hom-∞-Groupᵉ Gᵉ Hᵉ → type-∞-Groupᵉ Hᵉ
```

givenᵉ byᵉ `fᵉ ↦ᵉ map-hom-∞-Groupᵉ Gᵉ Hᵉ fᵉ g`ᵉ isᵉ anᵉ
[embedding](foundation.embeddings.mdᵉ) forᵉ everyᵉ higherᵉ groupᵉ `H`.ᵉ Inᵉ otherᵉ
words,ᵉ aᵉ higherᵉ groupᵉ isᵉ cyclicᵉ ifᵉ itᵉ isᵉ generatedᵉ byᵉ aᵉ singleᵉ element.ᵉ

However,ᵉ byᵉ Miller'sᵉ theoremᵉ {{#citeᵉ Mil84ᵉ}} weᵉ don'tᵉ expectᵉ thereᵉ to beᵉ manyᵉ
higherᵉ groupsᵉ thatᵉ areᵉ cyclicᵉ in thisᵉ sense.ᵉ Forᵉ example,ᵉ theᵉ finiteᵉ cyclicᵉ
groupsᵉ `Bℤ/n`ᵉ areᵉ coherentᵉ spaces,ᵉ whereasᵉ theᵉ 2-sphereᵉ `S²`ᵉ isᵉ aᵉ finiteᵉ
CW-complex.ᵉ Miller'sᵉ theoremᵉ impliesᵉ thatᵉ theᵉ pointedᵉ mappingᵉ spaceᵉ
`Map∗(Bℤ/n,S²)`ᵉ isᵉ contractible.ᵉ However,ᵉ thisᵉ impliesᵉ thatᵉ theᵉ evaluationᵉ mapᵉ
`Map∗(Bℤ/n,S²ᵉ) → ΩS²`ᵉ atᵉ theᵉ generatorᵉ ofᵉ `ℤ/n`ᵉ isᵉ aᵉ pointᵉ inclusionᵉ intoᵉ aᵉ
nondiscreteᵉ type,ᵉ soᵉ itᵉ can'tᵉ beᵉ anᵉ embedding.ᵉ

## Definitions

### Cyclic higher groups

```agda
ev-element-∞-Groupᵉ :
  {l1ᵉ l2ᵉ : Level} (Gᵉ : ∞-Groupᵉ l1ᵉ) (Hᵉ : ∞-Groupᵉ l2ᵉ) (gᵉ : type-∞-Groupᵉ Gᵉ) →
  hom-∞-Groupᵉ Gᵉ Hᵉ → type-∞-Groupᵉ Hᵉ
ev-element-∞-Groupᵉ Gᵉ Hᵉ gᵉ fᵉ = map-hom-∞-Groupᵉ Gᵉ Hᵉ fᵉ gᵉ

module _
  {l1ᵉ : Level} (l2ᵉ : Level) (Gᵉ : ∞-Groupᵉ l1ᵉ)
  where

  is-cyclic-prop-∞-Groupᵉ : Propᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-cyclic-prop-∞-Groupᵉ =
    exists-structure-Propᵉ
      ( type-∞-Groupᵉ Gᵉ)
      ( λ gᵉ → (Hᵉ : ∞-Groupᵉ l2ᵉ) → is-embᵉ (ev-element-∞-Groupᵉ Gᵉ Hᵉ gᵉ))

  is-cyclic-∞-Groupᵉ : UUᵉ (l1ᵉ ⊔ lsuc l2ᵉ)
  is-cyclic-∞-Groupᵉ = type-Propᵉ is-cyclic-prop-∞-Groupᵉ

  is-prop-is-cyclic-∞-Groupᵉ : is-propᵉ is-cyclic-∞-Groupᵉ
  is-prop-is-cyclic-∞-Groupᵉ = is-prop-type-Propᵉ is-cyclic-prop-∞-Groupᵉ
```

## See also

### Table of files related to cyclic types, groups, and rings

{{#includeᵉ tables/cyclic-types.mdᵉ}}

## References

{{#bibliographyᵉ}}