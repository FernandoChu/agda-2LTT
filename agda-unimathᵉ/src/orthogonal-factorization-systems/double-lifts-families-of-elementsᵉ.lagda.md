# Double lifts of families of elements

```agda
module orthogonal-factorization-systems.double-lifts-families-of-elementsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ

open import orthogonal-factorization-systems.lifts-families-of-elementsᵉ
```

</details>

## Idea

Considerᵉ aᵉ familyᵉ ofᵉ elementsᵉ `bᵉ : (iᵉ : Iᵉ) → Bᵉ iᵉ (aᵉ i)`ᵉ overᵉ aᵉ familyᵉ ofᵉ
elementsᵉ `aᵉ : (iᵉ : Iᵉ) → Aᵉ i`ᵉ andᵉ considerᵉ aᵉ familyᵉ ofᵉ typesᵉ

```text
  Cᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ → 𝒰.ᵉ
```

Recallᵉ thatᵉ `b`ᵉ isᵉ alsoᵉ aᵉ
[dependentᵉ lift](orthogonal-factorization-systems.lifts-families-of-elements.mdᵉ)
ofᵉ theᵉ familyᵉ ofᵉ elementsᵉ `a`.ᵉ Theᵉ typeᵉ ofᵉ
{{#conceptᵉ "dependentᵉ doubleᵉ lifts"ᵉ Disambiguation="familyᵉ ofᵉ elements"ᵉ Agda=dependent-double-lift-family-of-elementsᵉ}}
ofᵉ `b`ᵉ andᵉ `a`ᵉ to `C`ᵉ isᵉ definedᵉ to beᵉ theᵉ typeᵉ

```text
  (iᵉ : Iᵉ) → Cᵉ iᵉ (aᵉ iᵉ) (bᵉ i).ᵉ
```

Noteᵉ thatᵉ thisᵉ isᵉ theᵉ typeᵉ ofᵉ doubleᵉ liftsᵉ in theᵉ senseᵉ thatᵉ itᵉ simultaneouslyᵉ
liftsᵉ `a`ᵉ andᵉ `b`ᵉ to theᵉ typeᵉ familyᵉ `C`.ᵉ

Theᵉ definitionᵉ ofᵉ (ordinaryᵉ) doubleᵉ liftsᵉ isᵉ somewhatᵉ simplerᵉ: Givenᵉ aᵉ liftᵉ `b`ᵉ
ofᵉ `aᵉ : Iᵉ → A`ᵉ to aᵉ typeᵉ familyᵉ `Bᵉ : Aᵉ → 𝒰`,ᵉ aᵉ
{{#conceptᵉ "doubleᵉ lift"ᵉ Disambiguation="familiesᵉ ofᵉ elements"ᵉ Agda=double-lift-family-of-elementsᵉ}}
ofᵉ `a`ᵉ andᵉ `b`ᵉ to aᵉ typeᵉ familyᵉ

```text
  Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → 𝒰ᵉ
```

isᵉ aᵉ familyᵉ ofᵉ elementsᵉ

```text
  (iᵉ : Iᵉ) → Cᵉ (aᵉ iᵉ) (bᵉ i).ᵉ
```

Noteᵉ thatᵉ thisᵉ isᵉ theᵉ typeᵉ ofᵉ doubleᵉ liftsᵉ in theᵉ senseᵉ thatᵉ itᵉ simultaneouslyᵉ
liftsᵉ `a`ᵉ andᵉ `b`ᵉ to theᵉ typeᵉ familyᵉ `C`.ᵉ

Theᵉ typeᵉ ofᵉ doubleᵉ liftsᵉ playsᵉ aᵉ roleᵉ in theᵉ
[universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ aᵉ map](foundation.universal-property-family-of-fibers-of-maps.md).ᵉ

## Definitions

### Dependent double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → UUᵉ l3ᵉ}
  (Cᵉ : (iᵉ : Iᵉ) (xᵉ : Aᵉ iᵉ) → Bᵉ iᵉ xᵉ → UUᵉ l4ᵉ)
  {aᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ} (bᵉ : dependent-lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  dependent-double-lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  dependent-double-lift-family-of-elementsᵉ =
    dependent-lift-family-of-elementsᵉ (λ iᵉ → Cᵉ iᵉ (aᵉ iᵉ)) bᵉ
```

### Double lifts of families of elements

```agda
module _
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level} {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : UUᵉ l2ᵉ} {Bᵉ : Aᵉ → UUᵉ l3ᵉ}
  (Cᵉ : (xᵉ : Aᵉ) → Bᵉ xᵉ → UUᵉ l4ᵉ)
  {aᵉ : Iᵉ → Aᵉ} (bᵉ : lift-family-of-elementsᵉ Bᵉ aᵉ)
  where

  double-lift-family-of-elementsᵉ : UUᵉ (l1ᵉ ⊔ l4ᵉ)
  double-lift-family-of-elementsᵉ =
    dependent-lift-family-of-elementsᵉ (λ iᵉ → Cᵉ (aᵉ iᵉ)) bᵉ
```

## See also

-ᵉ [Liftsᵉ ofᵉ familiesᵉ ofᵉ elements](orthogonal-factorization-systems.lifts-families-of-elements.mdᵉ)
-ᵉ [Liftsᵉ ofᵉ maps](orthogonal-factorization-systems.lifts-of-maps.mdᵉ)
-ᵉ [Theᵉ universalᵉ propertyᵉ ofᵉ theᵉ familyᵉ ofᵉ fibersᵉ ofᵉ aᵉ map](foundation.universal-property-family-of-fibers-of-maps.mdᵉ)