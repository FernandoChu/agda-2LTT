# Constant maps

```agda
module foundation.exo-constant-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.exo-universes
```

</details>

## Definition

```agda
const : {l1 l2 : Level} (A : UUᵉ l1) (B : UUᵉ l2) → B → A → B
const A B b x = b
```
