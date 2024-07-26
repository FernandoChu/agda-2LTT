# Hilbert's `ε`-operators

```agda
module foundation.hilberts-epsilon-operatorsᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.functoriality-propositional-truncationᵉ
open import foundation.propositional-truncationsᵉ
open import foundation.universe-levelsᵉ

open import foundation-core.equivalencesᵉ
open import foundation-core.function-typesᵉ
```

</details>

## Idea

Hilbert'sᵉ $ε$-operatorᵉ atᵉ aᵉ typeᵉ `A`ᵉ isᵉ aᵉ mapᵉ `type-trunc-Propᵉ Aᵉ → A`.ᵉ Contraryᵉ
to Hilbert,ᵉ weᵉ willᵉ notᵉ assumeᵉ thatᵉ suchᵉ anᵉ operatorᵉ existsᵉ forᵉ eachᵉ typeᵉ `A`.ᵉ

## Definition

```agda
ε-operator-Hilbertᵉ : {lᵉ : Level} → UUᵉ lᵉ → UUᵉ lᵉ
ε-operator-Hilbertᵉ Aᵉ = type-trunc-Propᵉ Aᵉ → Aᵉ
```

## Properties

### The existence of Hilbert's `ε`-operators is invariant under equivalences

```agda
ε-operator-equivᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) →
  ε-operator-Hilbertᵉ Xᵉ → ε-operator-Hilbertᵉ Yᵉ
ε-operator-equivᵉ eᵉ fᵉ =
  (map-equivᵉ eᵉ ∘ᵉ fᵉ) ∘ᵉ (map-trunc-Propᵉ (map-inv-equivᵉ eᵉ))

ε-operator-equiv'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Xᵉ : UUᵉ l1ᵉ} {Yᵉ : UUᵉ l2ᵉ} (eᵉ : Xᵉ ≃ᵉ Yᵉ) →
  ε-operator-Hilbertᵉ Yᵉ → ε-operator-Hilbertᵉ Xᵉ
ε-operator-equiv'ᵉ eᵉ fᵉ =
  (map-inv-equivᵉ eᵉ ∘ᵉ fᵉ) ∘ᵉ (map-trunc-Propᵉ (map-equivᵉ eᵉ))
```