# Function types

```agda
module foundation-core.function-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levelsᵉ
```

</details>

## Idea

Functionsᵉ areᵉ primitive in Agda.ᵉ Hereᵉ weᵉ constructᵉ someᵉ basicᵉ functionsᵉ

## Examples

### The identity function

```agda
idᵉ : {lᵉ : Level} {Aᵉ : UUᵉ lᵉ} → Aᵉ → Aᵉ
idᵉ aᵉ = aᵉ

idωᵉ : {Aᵉ : UUωᵉ} → Aᵉ → Aᵉ
idωᵉ aᵉ = aᵉ
```

### Dependent composition of functions

```agda
infixr 15 _∘ᵉ_

_∘ᵉ_ :
  {l1ᵉ l2ᵉ l3ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} {Bᵉ : Aᵉ → UUᵉ l2ᵉ} {Cᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ → UUᵉ l3ᵉ} →
  ({aᵉ : Aᵉ} → (bᵉ : Bᵉ aᵉ) → Cᵉ aᵉ bᵉ) → (fᵉ : (aᵉ : Aᵉ) → Bᵉ aᵉ) → (aᵉ : Aᵉ) → Cᵉ aᵉ (fᵉ aᵉ)
(gᵉ ∘ᵉ fᵉ) aᵉ = gᵉ (fᵉ aᵉ)
```

### Evaluation at a point

```agda
ev-pointᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Pᵉ : Aᵉ → UUᵉ l2ᵉ} → ((xᵉ : Aᵉ) → Pᵉ xᵉ) → Pᵉ aᵉ
ev-pointᵉ aᵉ fᵉ = fᵉ aᵉ

ev-point'ᵉ :
  {l1ᵉ l2ᵉ : Level} {Aᵉ : UUᵉ l1ᵉ} (aᵉ : Aᵉ) {Xᵉ : UUᵉ l2ᵉ} → (Aᵉ → Xᵉ) → Xᵉ
ev-point'ᵉ aᵉ fᵉ = fᵉ aᵉ
```

### Postcomposition functions

```agda
map-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) →
  ((iᵉ : Iᵉ) → Aᵉ iᵉ) →
  ((iᵉ : Iᵉ) → Bᵉ iᵉ)
map-Πᵉ fᵉ hᵉ iᵉ = fᵉ iᵉ (hᵉ iᵉ)

map-Π'ᵉ :
  {l1ᵉ l2ᵉ l3ᵉ l4ᵉ : Level}
  {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  {Jᵉ : UUᵉ l4ᵉ} (αᵉ : Jᵉ → Iᵉ) →
  ((iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) →
  ((jᵉ : Jᵉ) → Aᵉ (αᵉ jᵉ)) →
  ((jᵉ : Jᵉ) → Bᵉ (αᵉ jᵉ))
map-Π'ᵉ αᵉ fᵉ = map-Πᵉ (fᵉ ∘ᵉ αᵉ)

map-implicit-Πᵉ :
  {l1ᵉ l2ᵉ l3ᵉ : Level}
  {Iᵉ : UUᵉ l1ᵉ} {Aᵉ : Iᵉ → UUᵉ l2ᵉ} {Bᵉ : Iᵉ → UUᵉ l3ᵉ}
  (fᵉ : (iᵉ : Iᵉ) → Aᵉ iᵉ → Bᵉ iᵉ) →
  ({iᵉ : Iᵉ} → Aᵉ iᵉ) →
  ({iᵉ : Iᵉ} → Bᵉ iᵉ)
map-implicit-Πᵉ fᵉ hᵉ {iᵉ} = map-Πᵉ fᵉ (λ iᵉ → hᵉ {iᵉ}) iᵉ
```

## See also

-ᵉ [Postcomposition](foundation.postcomposition-functions.mdᵉ)
-ᵉ [Precomposition](foundation.precomposition-functions.mdᵉ)

### Table of files about function types, composition, and equivalences

{{#includeᵉ tables/composition.mdᵉ}}