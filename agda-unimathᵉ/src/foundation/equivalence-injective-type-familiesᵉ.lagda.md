# Equivalence injective type families

```agda
module foundation.equivalence-injective-type-familiesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.functoriality-dependent-function-typesᵉ
open import foundation.iterated-dependent-product-typesᵉ
open import foundation.univalenceᵉ
open import foundation.universal-property-equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
open import foundation-core.identity-typesᵉ
open import foundation-core.injective-mapsᵉ
open import foundation-core.propositionsᵉ
open import foundation-core.setsᵉ
```

</details>

## Idea

Weᵉ sayᵉ aᵉ typeᵉ familyᵉ `P`ᵉ isᵉ
{{#conceptᵉ "equivalenceᵉ injective"ᵉ Disambiguation="typeᵉ family"ᵉ Agda=is-equivalence-injectiveᵉ}}
ifᵉ forᵉ everyᵉ [equivalenceᵉ ofᵉ types](foundation-core.equivalences.mdᵉ) `Pᵉ xᵉ ≃ᵉ Pᵉ y`ᵉ
weᵉ haveᵉ `xᵉ ＝ᵉ yᵉ `.ᵉ Byᵉ [univalence](foundation-core.univalence.md),ᵉ theᵉ
[structure](foundation.structure.mdᵉ) ofᵉ beingᵉ equivalenceᵉ injectiveᵉ isᵉ
equivalentᵉ to beingᵉ [injectiveᵉ asᵉ aᵉ map](foundation-core.injective-maps.md),ᵉ butᵉ
moreᵉ generallyᵉ everyᵉ equivalenceᵉ injectiveᵉ typeᵉ familyᵉ mustᵉ alwaysᵉ beᵉ injectiveᵉ
asᵉ aᵉ map.ᵉ

**Note.**ᵉ Theᵉ conceptᵉ ofᵉ equivalenceᵉ injectiveᵉ typeᵉ familyᵉ asᵉ consideredᵉ hereᵉ isᵉ
unrelatedᵉ to theᵉ conceptᵉ ofᵉ "injectiveᵉ type"ᵉ asᵉ studiedᵉ byᵉ Martínᵉ Escardóᵉ in
_Injectiveᵉ typesᵉ in univalentᵉ mathematicsᵉ_
([arXiv:1903.01211](https://arxiv.org/abs/1903.01211),ᵉ
[TypeTopology](https://www.cs.bham.ac.uk/~mhe/TypeTopology/InjectiveTypes.index.html)).ᵉ

## Definition

### Equivalence injective type families

```agda
is-equivalence-injectiveᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} → (Aᵉ → UUᵉ l2ᵉ) → UUᵉ (l1ᵉ ⊔ l2ᵉ)
is-equivalence-injectiveᵉ {Aᵉ = Aᵉ} Pᵉ = {xᵉ yᵉ : Aᵉ} → Pᵉ xᵉ ≃ᵉ Pᵉ yᵉ → xᵉ ＝ᵉ yᵉ
```

## Properties

### Equivalence injective type families are injective as maps

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Pᵉ : Aᵉ → UUᵉ l2ᵉ}
  where

  is-injective-is-equivalence-injectiveᵉ :
    is-equivalence-injectiveᵉ Pᵉ → is-injectiveᵉ Pᵉ
  is-injective-is-equivalence-injectiveᵉ Hᵉ = Hᵉ ∘ᵉ equiv-eqᵉ

  is-equivalence-injective-is-injectiveᵉ :
    is-injectiveᵉ Pᵉ → is-equivalence-injectiveᵉ Pᵉ
  is-equivalence-injective-is-injectiveᵉ Hᵉ = Hᵉ ∘ᵉ eq-equivᵉ

  is-equiv-is-injective-is-equivalence-injectiveᵉ :
    is-equivᵉ is-injective-is-equivalence-injectiveᵉ
  is-equiv-is-injective-is-equivalence-injectiveᵉ =
    is-equiv-map-implicit-Π-is-fiberwise-equivᵉ
      ( λ xᵉ →
        is-equiv-map-implicit-Π-is-fiberwise-equivᵉ
          ( λ yᵉ →
            is-equiv-precomp-is-equivᵉ
              ( equiv-eqᵉ)
              ( univalenceᵉ (Pᵉ xᵉ) (Pᵉ yᵉ))
              ( xᵉ ＝ᵉ yᵉ)))

  equiv-is-injective-is-equivalence-injectiveᵉ :
    is-equivalence-injectiveᵉ Pᵉ ≃ᵉ is-injectiveᵉ Pᵉ
  pr1ᵉ equiv-is-injective-is-equivalence-injectiveᵉ =
    is-injective-is-equivalence-injectiveᵉ
  pr2ᵉ equiv-is-injective-is-equivalence-injectiveᵉ =
    is-equiv-is-injective-is-equivalence-injectiveᵉ

  equiv-is-equivalence-injective-is-injectiveᵉ :
    is-injectiveᵉ Pᵉ ≃ᵉ is-equivalence-injectiveᵉ Pᵉ
  equiv-is-equivalence-injective-is-injectiveᵉ =
    inv-equivᵉ equiv-is-injective-is-equivalence-injectiveᵉ
```

### For a type family over a set, being equivalence injective is a property

```agda
module _
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (is-set-Aᵉ : is-setᵉ Aᵉ) (Pᵉ : Aᵉ → UUᵉ l2ᵉ)
  where

  is-prop-is-equivalence-injectiveᵉ : is-propᵉ (is-equivalence-injectiveᵉ Pᵉ)
  is-prop-is-equivalence-injectiveᵉ =
    is-prop-iterated-implicit-Πᵉ 2 (λ xᵉ yᵉ → is-prop-function-typeᵉ (is-set-Aᵉ xᵉ yᵉ))

  is-equivalence-injective-Propᵉ : Propᵉ (l1ᵉ ⊔ l2ᵉ)
  pr1ᵉ is-equivalence-injective-Propᵉ = is-equivalence-injectiveᵉ Pᵉ
  pr2ᵉ is-equivalence-injective-Propᵉ = is-prop-is-equivalence-injectiveᵉ
```