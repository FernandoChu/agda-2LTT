# Contractible pointed types

```agda
module structured-types.contractible-pointed-typesᵉ where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-typesᵉ
open import foundation.propositionsᵉ
open import foundation.universe-levelsᵉ

open import structured-types.pointed-typesᵉ
```

</details>

## Definition

```agda
is-contr-pointed-type-Propᵉ : {lᵉ : Level} → Pointed-Typeᵉ lᵉ → Propᵉ lᵉ
is-contr-pointed-type-Propᵉ Aᵉ = is-contr-Propᵉ (type-Pointed-Typeᵉ Aᵉ)

is-contr-Pointed-Typeᵉ : {lᵉ : Level} → Pointed-Typeᵉ lᵉ → UUᵉ lᵉ
is-contr-Pointed-Typeᵉ Aᵉ = type-Propᵉ (is-contr-pointed-type-Propᵉ Aᵉ)

is-prop-is-contr-Pointed-Typeᵉ :
  {lᵉ : Level} (Aᵉ : Pointed-Typeᵉ lᵉ) → is-propᵉ (is-contr-Pointed-Typeᵉ Aᵉ)
is-prop-is-contr-Pointed-Typeᵉ Aᵉ =
  is-prop-type-Propᵉ (is-contr-pointed-type-Propᵉ Aᵉ)
```