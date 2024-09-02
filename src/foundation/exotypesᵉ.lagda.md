# Exotypes

```agda
module foundation.exotypesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-typesᵉ
open import foundation.identity-typesᵉ
open import foundation.setsᵉ
open import foundation.universe-levelsᵉ
```

</details>

```agda
is-setᵉ-exotype : {l : Level} (X : UUᵉ l) → is-setᵉ X
pr1ᵉ (is-setᵉ-exotype X x .x reflᵉ reflᵉ) = reflᵉ
pr2ᵉ (is-setᵉ-exotype X x .x reflᵉ reflᵉ) reflᵉ = reflᵉ

exotype-Setᵉ : {l : Level} (X : UUᵉ l) → Setᵉ l
pr1ᵉ (exotype-Setᵉ X) = X
pr2ᵉ (exotype-Setᵉ X) = is-setᵉ-exotype X
```
