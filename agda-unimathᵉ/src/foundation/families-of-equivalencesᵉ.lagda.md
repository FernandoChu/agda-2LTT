# Families of equivalences

```agda
module foundation.families-of-equivalencesᵉ where

open import foundation-core.families-of-equivalencesᵉ public
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalencesᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.propositionsᵉ
```

</details>

## Idea

Aᵉ **familyᵉ ofᵉ equivalences**ᵉ isᵉ aᵉ familyᵉ

```text
  eᵢᵉ : Aᵉ iᵉ ≃ᵉ Bᵉ iᵉ
```

ofᵉ [equivalences](foundation-core.equivalences.md).ᵉ Familiesᵉ ofᵉ equivalencesᵉ areᵉ
alsoᵉ calledᵉ **fiberwiseᵉ equivalences**.ᵉ

## Properties

### Being a fiberwise equivalence is a proposition

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : Aᵉ → UUᵉ l3ᵉ}
  where

  is-property-is-fiberwise-equivᵉ :
    (fᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ → Cᵉ aᵉ) → is-propᵉ (is-fiberwise-equivᵉ fᵉ)
  is-property-is-fiberwise-equivᵉ fᵉ =
    is-prop-Πᵉ (λ aᵉ → is-property-is-equivᵉ (fᵉ aᵉ))
```

## See also

-ᵉ Inᵉ
  [Functorialityᵉ ofᵉ dependentᵉ pairᵉ types](foundation-core.functoriality-dependent-pair-types.mdᵉ)
  weᵉ showᵉ thatᵉ aᵉ familyᵉ ofᵉ mapsᵉ isᵉ aᵉ fiberwiseᵉ equivalenceᵉ ifᵉ andᵉ onlyᵉ ifᵉ itᵉ
  inducesᵉ anᵉ equivalenceᵉ onᵉ [totalᵉ spaces](foundation.dependent-pair-types.md).ᵉ